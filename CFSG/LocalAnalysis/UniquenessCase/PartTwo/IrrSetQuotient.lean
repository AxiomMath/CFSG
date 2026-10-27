module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3
public import CFSG.Quasithin.Background.RonanF918Nat
public import CFSG.Quasithin.Background.F918Z1Quot
public import CFSG.Quasithin.Background.F918M0
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
public import CFSG.Quasithin.Background.FFC4Tr1
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Quasithin

variable {W : Type} [CommGroup W]

abbrev supConjSet (K Mbar : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  ⨆ X ∈ conjSet K Mbar, X

abbrev fixSupConjSet (K Mbar : Subgroup (MulAut W)) : Subgroup W := fixV (supConjSet K Mbar)

theorem autQuot_le_stabSub_map {K : Subgroup (MulAut W)} {Z I : Subgroup W}
    (hI : StableUnder K I) : autQuot K Z ≤ stabSub (I.map (QuotientGroup.mk' Z)) := by
  refine B1.le_stabSub_of_invariant fun φ hφ x hx => ?_
  obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hφ
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map.mpr ⟨g.1 u, hI g.1 hg u hu, rfl⟩

theorem map_subtype_fixV_autSub_autQuot {K : Subgroup (MulAut W)} {Z I : Subgroup W}
    (hKZ : K ≤ stabSub Z) (hZK : Z ≤ fixV K) (hI : I ∈ irrSet K) :
    (fixV (autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z)))).map
        (I.map (QuotientGroup.mk' Z)).subtype = (I ⊓ fixV K).map (QuotientGroup.mk' Z) := by
  obtain ⟨hcomm, hlt, hIst, hNst, hirr⟩ := hI
  rw [map_subtype_fixV_autSub (autQuot_le_stabSub_map hIst)]
  let J : Subgroup W :=
    { carrier := {u | u ∈ I ∧ ∀ g ∈ K, g u * u⁻¹ ∈ Z}
      one_mem' := ⟨I.one_mem, fun g _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨I.mul_mem ha.1 hb.1, fun g hg => by
        rw [map_mul, mul_inv, mul_mul_mul_comm]; exact Z.mul_mem (ha.2 g hg) (hb.2 g hg)⟩
      inv_mem' := fun {a} ha => ⟨I.inv_mem ha.1, fun g hg => by
        have := Z.inv_mem (ha.2 g hg); rw [map_inv, inv_inv, mul_comm]; simpa using this⟩ }
  have hJst : StableUnder K J := by
    intro k hk u hu
    refine ⟨hIst k hk u hu.1, fun g hg => ?_⟩
    have hz := hu.2 (k⁻¹ * g * k) (K.mul_mem (K.mul_mem (K.inv_mem hk) hg) hk)
    have heq : k ((k⁻¹ * g * k) u * u⁻¹) = g (k u) * (k u)⁻¹ := by
      simp [map_mul, map_inv]
    rw [← heq, hZK hz k hk]
    exact hz
  have hNJ : I ⊓ fixV K ≤ J := fun u hu =>
    ⟨hu.1, fun g hg => by rw [hu.2 g hg, mul_inv_cancel]; exact Z.one_mem⟩
  ext x
  constructor
  · rintro ⟨hxI, hxfix⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hxI
    have hu' : ∀ g ∈ K, g u * u⁻¹ ∈ Z := fun g hg =>
      (mk_mem_fixV_autQuot.mp hxfix) g hg (hKZ hg)
    rcases hirr J hJst hNJ (fun u hu => hu.1) with hJ | hJ
    · have huJ : u ∈ J := ⟨hu, hu'⟩
      rw [hJ] at huJ
      exact Subgroup.mem_map.mpr ⟨u, huJ, rfl⟩
    · exfalso
      have hle : commSub I K ≤ I ⊓ fixV K := (Subgroup.closure_le _).mpr <| by
        rintro c ⟨g, hg, w, hw, rfl⟩
        have hwJ : w ∈ J := hJ ▸ hw
        exact ⟨I.mul_mem (hIst g hg w hw) (I.inv_mem hw), hZK (hwJ.2 g hg)⟩
      have hIle : I ≤ I ⊓ fixV K := by
        conv_lhs => rw [← hcomm]
        exact hle
      exact (not_lt_of_ge hIle) hlt
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨Subgroup.mem_map.mpr ⟨u, hu.1, rfl⟩, mk_mem_fixV_autQuot.mpr fun g hg _ => by
      rw [hu.2 g hg, mul_inv_cancel]; exact Z.one_mem⟩

theorem eq_fixV_or_eq_top_of_stableUnder_autSub_autQuot {K : Subgroup (MulAut W)}
    {Z I : Subgroup W} (hKZ : K ≤ stabSub Z) (hZK : Z ≤ fixV K) (hI : I ∈ irrSet K)
    (U : Subgroup ↥(I.map (QuotientGroup.mk' Z)))
    (hU : StableUnder (autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z))) U)
    (hfixU : fixV (autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z))) ≤ U) :
    U = fixV (autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z))) ∨ U = ⊤ := by
  have hfix := map_subtype_fixV_autSub_autQuot hKZ hZK hI
  obtain ⟨-, -, hIst, -, hirr⟩ := hI
  set J : Subgroup W :=
    I ⊓ (U.map (I.map (QuotientGroup.mk' Z)).subtype).comap (QuotientGroup.mk' Z) with hJdef
  have hmapJ : J.map (QuotientGroup.mk' Z) = U.map (I.map (QuotientGroup.mk' Z)).subtype := by
    apply le_antisymm
    · rintro x ⟨u, hu, rfl⟩
      exact hu.2
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨u, huI, hu⟩ := Subgroup.mem_map.mp y.2
      refine ⟨u, ⟨huI, ?_⟩, hu⟩
      show QuotientGroup.mk' Z u ∈ U.map (I.map (QuotientGroup.mk' Z)).subtype
      rw [hu]
      exact ⟨y, hy, rfl⟩
  have hfixJ : I ⊓ fixV K ≤ J := by
    intro u hu
    refine ⟨hu.1, ?_⟩
    have hmem : QuotientGroup.mk' Z u ∈ (I ⊓ fixV K).map (QuotientGroup.mk' Z) :=
      Subgroup.mem_map_of_mem _ hu
    rw [← hfix] at hmem
    obtain ⟨w, hwfix, hw⟩ := Subgroup.mem_map.mp hmem
    show QuotientGroup.mk' Z u ∈ U.map (I.map (QuotientGroup.mk' Z)).subtype
    rw [← hw]
    exact Subgroup.mem_map_of_mem _ (hfixU hwfix)
  have hJst : StableUnder K J := by
    intro k hk u hu
    refine ⟨hIst k hk u hu.1, ?_⟩
    have hφ : quotHom Z ⟨k, hKZ hk⟩ ∈ autQuot K Z :=
      mem_autQuot.mpr ⟨⟨k, hKZ hk⟩, hk, rfl⟩
    have hφs : quotHom Z ⟨k, hKZ hk⟩ ∈ stabSub (I.map (QuotientGroup.mk' Z)) :=
      autQuot_le_stabSub_map hIst hφ
    have hl : resHom (I.map (QuotientGroup.mk' Z)) ⟨_, hφs⟩ ∈
        autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z)) :=
      mem_autSub.mpr ⟨⟨_, hφs⟩, hφ, rfl⟩
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp hu.2
    have hyU := hU _ hl y hy
    show QuotientGroup.mk' Z (k u) ∈ U.map (I.map (QuotientGroup.mk' Z)).subtype
    refine ⟨_, hyU, ?_⟩
    show ((resHom (I.map (QuotientGroup.mk' Z)) ⟨_, hφs⟩ y :
        ↥(I.map (QuotientGroup.mk' Z))) : W ⧸ Z) = QuotientGroup.mk' Z (k u)
    rw [resHom_apply]
    show quotHom Z ⟨k, hKZ hk⟩ (y : W ⧸ Z) = QuotientGroup.mk' Z (k u)
    have hy' : (y : W ⧸ Z) = QuotientGroup.mk u := hyu
    rw [hy', quotHom_mk]
    rfl
  rcases hirr J hJst hfixJ inf_le_left with hJ | hJ
  · left
    apply Subgroup.map_injective (I.map (QuotientGroup.mk' Z)).subtype_injective
    rw [hfix, ← hmapJ, hJ]
  · right
    rw [eq_top_iff]
    intro x _
    have hx : (x : W ⧸ Z) ∈ U.map (I.map (QuotientGroup.mk' Z)).subtype := by
      rw [← hmapJ, hJ]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyx' : y = x := Subtype.ext hyx
    exact hyx' ▸ hy

theorem isIrrOn_autQuot_fixV_autSub
    {K : Subgroup (MulAut W)} {Z I : Subgroup W}
    (hKZ : K ≤ stabSub Z) (hZK : Z ≤ fixV K) (hI : I ∈ irrSet K) :
    CFSG.LocalAnalysis.RankThreeUC.IsIrrOn
      (autQuot (autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z)))
        (fixV (autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z))))) := by
  let Istar : Subgroup (W ⧸ Z) := I.map (QuotientGroup.mk' Z)
  let Lstar : Subgroup (MulAut ↥Istar) := autSub (autQuot K Z) Istar
  have hLfix : Lstar ≤ stabSub (fixV Lstar) := CFSG.Quasithin.RonanF918.le_stabSub_fixV Lstar
  have hirr : ∀ U : Subgroup ↥Istar,
      (∀ g ∈ Lstar ⊔ Lstar, ∀ u ∈ U, g u ∈ U) → fixV Lstar ≤ U →
      U = fixV Lstar ∨ U = ⊤ := by
    intro U hU hfixU
    have hU' : StableUnder Lstar U := by
      intro g hg u hu
      exact hU g (by simpa using hg) u hu
    exact eq_fixV_or_eq_top_of_stableUnder_autSub_autQuot hKZ hZK hI U hU' hfixU
  have h := CFSG.Quasithin.D37Lift.irr_autQuot (C := fixV Lstar) (D := Lstar) (X := Lstar)
    hLfix hLfix hirr
  intro U' hU'
  exact h U' (by simpa [sup_idem] using hU')

theorem commSub_top_autSub_eq_top
    {X : Subgroup (MulAut W)} {U : Subgroup W}
    (hXU : X ≤ stabSub U) (hcomm : commSub U X = U) :
    commSub (⊤ : Subgroup ↥U) (autSub X U) = ⊤ := by
  have h := CFSG.Quasithin.FFC.map_commSub_autSub (V₂ := U) hXU (⊤ : Subgroup ↥U)
  rw [Subgroup.map_top, Subgroup.range_subtype, hcomm] at h
  apply Subgroup.map_injective U.subtype_injective
  rw [h, Subgroup.map_top, Subgroup.range_subtype]

theorem map_commSub_eq_commSub_autQuot {K : Subgroup (MulAut W)} {Z I : Subgroup W}
    (hKZ : K ≤ stabSub Z) :
    (commSub I K).map (QuotientGroup.mk' Z) =
      commSub (I.map (QuotientGroup.mk' Z)) (autQuot K Z) := by
  apply le_antisymm
  · rw [commSub, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, hk, u, hu, rfl⟩, rfl⟩
    exact Subgroup.subset_closure
      ⟨quotHom Z ⟨k, hKZ hk⟩, mem_autQuot.mpr ⟨⟨k, hKZ hk⟩, hk, rfl⟩,
        QuotientGroup.mk u, Subgroup.mem_map_of_mem _ hu, rfl⟩
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, w, hw, rfl⟩
    obtain ⟨g, hg, hgl⟩ := mem_autQuot.mp hl
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
    refine Subgroup.mem_map.mpr ⟨(g : MulAut W) u * u⁻¹, ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨g, hg, u, hu, rfl⟩
    · show (QuotientGroup.mk' Z ((g : MulAut W) u * u⁻¹)) =
          l ((QuotientGroup.mk' Z) u) * ((QuotientGroup.mk' Z) u)⁻¹
      rw [map_mul, map_inv, ← hgl]
      rfl

theorem map_commV_eq_commV_autQuot (K : Subgroup (MulAut W)) (Z : Subgroup W)
    (hKZ : K ≤ stabSub Z) :
    (commV K).map (QuotientGroup.mk' Z) = commV (autQuot K Z) := by
  rw [commV_eq_commSub, commV_eq_commSub, map_commSub_eq_commSub_autQuot hKZ,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)]

theorem map_commV_autQuot_conj (K : Subgroup (MulAut W)) (Z : Subgroup W)
    (hKZ : K ≤ stabSub Z) (m : MulAut W) (hmZ : m ∈ stabSub Z) :
    (commV (autQuot K Z)).map (quotHom Z ⟨m, hmZ⟩).toMonoidHom =
      commV (autQuot (conjAutSub m K) Z) := by
  have hKmZ : conjAutSub m K ≤ stabSub Z := by
    rintro _ ⟨k, hk, rfl⟩
    exact (stabSub Z).mul_mem ((stabSub Z).mul_mem hmZ (hKZ hk)) ((stabSub Z).inv_mem hmZ)
  calc
    (commV (autQuot K Z)).map (quotHom Z ⟨m, hmZ⟩).toMonoidHom =
        ((commV K).map (QuotientGroup.mk' Z)).map
          (quotHom Z ⟨m, hmZ⟩).toMonoidHom := by
      rw [map_commV_eq_commV_autQuot K Z hKZ]
    _ = (commV K).map
          ((quotHom Z ⟨m, hmZ⟩).toMonoidHom.comp (QuotientGroup.mk' Z)) := by
      rw [Subgroup.map_map]
    _ = (commV K).map ((QuotientGroup.mk' Z).comp m.toMonoidHom) := by rfl
    _ = ((commV K).map m.toMonoidHom).map (QuotientGroup.mk' Z) := by
      rw [Subgroup.map_map]
    _ = (commV (conjAutSub m K)).map (QuotientGroup.mk' Z) := by
      rw [← commV_map_conj_eq K m]
      rfl
    _ = commV (autQuot (conjAutSub m K) Z) :=
      map_commV_eq_commV_autQuot _ _ hKmZ

theorem conjAutSub_eq_self_of_isDirSumOver
    {Mbar K : Subgroup (MulAut W)} {Z I : Subgroup W}
    (hKZ : K ≤ stabSub Z) (hZK : Z ≤ fixV K) (hI : I ∈ irrSet K)
    (hsum : IsDirSumOver (conjSet K Mbar) (fun X => commV (autQuot X Z)))
    {m : MulAut W} (hmM : m ∈ Mbar) (hmZ : m ∈ stabSub Z)
    (hstab : quotHom Z ⟨m, hmZ⟩ ∈ stabSub (I.map (QuotientGroup.mk' Z))) :
    conjAutSub m K = K := by
  classical
  obtain ⟨hcommI, hIrrI⟩ := hI
  have hIstar_ne : I.map (QuotientGroup.mk' Z) ≠ ⊥ := by
    intro hbot
    have hIZ : I ≤ Z := by
      rw [Subgroup.map_eq_bot_iff] at hbot
      simpa [QuotientGroup.ker_mk'] using hbot
    exact CFSG.LocalAnalysis.WeakClosure81.not_le_fixV_of_mem_irrSet (X := K) (I := I)
      ⟨hcommI, hIrrI⟩ (hIZ.trans hZK)
  have hI_le_commV : I ≤ commV K := by
    rw [← hcommI, commV_eq_commSub]
    exact commSub_mono le_top le_rfl
  have hIstar_le : I.map (QuotientGroup.mk' Z) ≤ commV (autQuot K Z) := by
    rw [← map_commV_eq_commV_autQuot K Z hKZ]
    exact Subgroup.map_mono hI_le_commV
  have hmap : (I.map (QuotientGroup.mk' Z)).map (quotHom Z ⟨m, hmZ⟩).toMonoidHom =
      I.map (QuotientGroup.mk' Z) := mem_stabSub_iff_map_eq.mp hstab
  have hIstar_le_Km : I.map (QuotientGroup.mk' Z) ≤
      commV (autQuot (conjAutSub m K) Z) := by
    calc I.map (QuotientGroup.mk' Z) =
        (I.map (QuotientGroup.mk' Z)).map (quotHom Z ⟨m, hmZ⟩).toMonoidHom := hmap.symm
      _ ≤ (commV (autQuot K Z)).map (quotHom Z ⟨m, hmZ⟩).toMonoidHom :=
        Subgroup.map_mono hIstar_le
      _ = commV (autQuot (conjAutSub m K) Z) :=
        map_commV_autQuot_conj K Z hKZ m hmZ
  by_contra hKm_ne
  have hK_mem : K ∈ conjSet K Mbar := ⟨1, Mbar.one_mem, by ext x; simp [MulAut.conj_apply]⟩
  have hKm_mem : conjAutSub m K ∈ conjSet K Mbar := ⟨m, hmM, rfl⟩
  let XK : {X // X ∈ conjSet K Mbar} := ⟨K, hK_mem⟩
  let Xm : {X // X ∈ conjSet K Mbar} := ⟨conjAutSub m K, hKm_mem⟩
  have hXne : Xm ≠ XK := by
    intro h
    apply hKm_ne
    have := congrArg Subtype.val h
    simpa [Xm, XK] using this
  have hind := (iSupIndep_def.mp hsum.1) XK
  have hle : (fun X : {X // X ∈ conjSet K Mbar} => commV (autQuot X.1 Z)) Xm ≤
      ⨆ j, ⨆ (_ : j ≠ XK), (fun X : {X // X ∈ conjSet K Mbar} => commV (autQuot X.1 Z)) j :=
    le_iSup_of_le Xm (le_iSup_of_le hXne le_rfl)
  have hdisj : Disjoint (commV (autQuot K Z)) (commV (autQuot (conjAutSub m K) Z)) :=
    hind.mono_right hle
  have hbot : I.map (QuotientGroup.mk' Z) = ⊥ := by
    have hleinf : I.map (QuotientGroup.mk' Z) ≤
        commV (autQuot K Z) ⊓ commV (autQuot (conjAutSub m K) Z) :=
      le_inf hIstar_le hIstar_le_Km
    rw [disjoint_iff.mp hdisj] at hleinf
    exact le_bot_iff.mp hleinf
  exact hIstar_ne hbot

theorem autSub_autQuot_subgroupOf_normal_of_isDirSumOver
    {Mbar K : Subgroup (MulAut W)} {Z I : Subgroup W}
    (hKZ : K ≤ stabSub Z) (hZK : Z ≤ fixV K) (hI : I ∈ irrSet K)
    (hsum : IsDirSumOver (conjSet K Mbar) (fun X => commV (autQuot X Z)))
    (hKM : K ≤ Mbar) :
    ((autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z))).subgroupOf
      (autSub (autQuot Mbar Z) (I.map (QuotientGroup.mk' Z)))).Normal := by
  classical
  refine Subgroup.Normal.mk ?_
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨kn, hknMem, hknEq⟩ := mem_autSub.mp hn
  obtain ⟨kg, hkgMem, hkgEq⟩ := mem_autSub.mp g.2
  obtain ⟨m, hmMem, hmEq⟩ := mem_autQuot.mp hkgMem
  obtain ⟨k, hkMem, hkEq⟩ := mem_autQuot.mp hknMem
  have hmM : (m : MulAut W) ∈ Mbar := hmMem
  have hmZ : (m : MulAut W) ∈ stabSub Z := m.2
  have hkK : (k : MulAut W) ∈ K := hkMem
  have hkZ : (k : MulAut W) ∈ stabSub Z := k.2
  have hstabI : quotHom Z m ∈ stabSub (I.map (QuotientGroup.mk' Z)) := by
    simpa [hmEq] using kg.2
  have hN1 := conjAutSub_eq_self_of_isDirSumOver hKZ hZK hI hsum hmM hmZ hstabI
  have hmkmK : (m : MulAut W) * (k : MulAut W) * (m : MulAut W)⁻¹ ∈ K := by
    have h1 : (m : MulAut W) * (k : MulAut W) * (m : MulAut W)⁻¹ ∈
        conjAutSub (m : MulAut W) K :=
      Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩
    rwa [hN1] at h1
  have hmkmZ : (m : MulAut W) * (k : MulAut W) * (m : MulAut W)⁻¹ ∈ stabSub Z :=
    (stabSub Z).mul_mem ((stabSub Z).mul_mem hmZ hkZ) ((stabSub Z).inv_mem hmZ)
  have hstab : ((kg : MulAut (W ⧸ Z)) * (kn : MulAut (W ⧸ Z)) *
      (kg : MulAut (W ⧸ Z))⁻¹) ∈ stabSub (I.map (QuotientGroup.mk' Z)) :=
    (stabSub (I.map (QuotientGroup.mk' Z))).mul_mem
      ((stabSub (I.map (QuotientGroup.mk' Z))).mul_mem kg.2 kn.2)
      ((stabSub (I.map (QuotientGroup.mk' Z))).inv_mem kg.2)
  have hconj : (kg : MulAut (W ⧸ Z)) * (kn : MulAut (W ⧸ Z)) *
      (kg : MulAut (W ⧸ Z))⁻¹ =
      quotHom Z ⟨(m : MulAut W) * (k : MulAut W) * (m : MulAut W)⁻¹, hmkmZ⟩ := by
    rw [← hmEq, ← hkEq]
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  have hmem : (kg : MulAut (W ⧸ Z)) * (kn : MulAut (W ⧸ Z)) *
      (kg : MulAut (W ⧸ Z))⁻¹ ∈ autQuot K Z := by
    rw [hconj]
    exact mem_autQuot.mpr ⟨⟨_, hmkmZ⟩, hmkmK, rfl⟩
  refine mem_autSub.mpr ⟨⟨_, hstab⟩, hmem, ?_⟩
  change (resHom (I.map (QuotientGroup.mk' Z)) kg) *
      (resHom (I.map (QuotientGroup.mk' Z)) kn) *
      (resHom (I.map (QuotientGroup.mk' Z)) kg)⁻¹ = g * n * g⁻¹
  rw [hkgEq, hknEq]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
