module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  intro x y hxy
  exact IntMod.val_injective
    (mul_inv_eq_one.1 (Subgroup.mem_bot.1 ((mkTil_eq_iff ⊥ V hV x y).1 hxy)))

private theorem s16c167_imgTil_inj {V U U' : Subgroup G} (hV : IsElemAbelian 2 V)
    (hU : U ≤ V) (hU' : U' ≤ V) (h : imgTil ⊥ V hV U = imgTil ⊥ V hV U') : U = U' := by
  have hmkTil_inj : Function.Injective (mkTil (⊥ : Subgroup G) V hV) :=
    s16c167_mkTil_bot_injective hV
  have hmain : (intSub V hV U).map (mkTil (⊥ : Subgroup G) V hV) =
      (intSub V hV U').map (mkTil (⊥ : Subgroup G) V hV) := h
  have h1 : intSub V hV U = intSub V hV U' := by
    have hc := congrArg (Subgroup.comap (mkTil (⊥ : Subgroup G) V hV)) hmain
    rw [Subgroup.comap_map_eq_self_of_injective hmkTil_inj,
      Subgroup.comap_map_eq_self_of_injective hmkTil_inj] at hc
    exact hc
  have h2 : (U.subgroupOf V).map V.subtype = (U'.subgroupOf V).map V.subtype := by
    simpa only [intSub] using congrArg (Subgroup.map V.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hU, Subgroup.map_subgroupOf_eq_of_le hU'] at h2

private theorem s16c167_imgTil_le_iff {V U U' : Subgroup G} (hV : IsElemAbelian 2 V)
    (hU : U ≤ V) (hU' : U' ≤ V) :
    imgTil ⊥ V hV U ≤ imgTil ⊥ V hV U' ↔ U ≤ U' := by
  constructor
  · intro h
    have h1 : imgTil ⊥ V hV (U ⊓ U') = imgTil ⊥ V hV U := by
      rw [s16c167_imgTil_inf_bot hV, inf_eq_left.2 h]
    exact inf_eq_left.1 (s16c167_imgTil_inj hV (le_trans inf_le_left hU) hU h1)
  · intro h
    have hUU' : U ⊓ U' = U := inf_eq_left.2 h
    rw [← hUU', s16c167_imgTil_inf_bot hV]
    exact inf_le_right

private theorem s16c167_conjSubgroup_inj {A B : Subgroup G} {g : G}
    (h : conjSubgroup A g = conjSubgroup B g) : A = B := by
  have hc := congrArg (fun C : Subgroup G => conjSubgroup C g⁻¹) h
  rwa [E3.conjSubgroup_conj_inv, E3.conjSubgroup_conj_inv] at hc

private theorem s16c167_conj_conj {g u m : G} (hm : m = g * u * g⁻¹) (I : Subgroup G) :
    conjSubgroup (conjSubgroup I g) u = conjSubgroup (conjSubgroup I m) g := by
  rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, hm]
  congr 1
  group

private theorem s16c167_conjSubgroup_centralizer_singleton {g u m : G}
    (hm : m = g * u * g⁻¹) :
    conjSubgroup (Subgroup.centralizer ({m} : Set G)) g =
      Subgroup.centralizer ({u} : Set G) := by
  ext x
  rw [mem_conjSubgroup_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h2 : g * (x * u) * g⁻¹ = g * (u * x) * g⁻¹ := by
      calc g * (x * u) * g⁻¹ = (g * x * g⁻¹) * (g * u * g⁻¹) := by group
        _ = (g * u * g⁻¹) * (g * x * g⁻¹) := by rw [← hm]; exact h
        _ = g * (u * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  · intro h
    rw [hm]
    calc (g * x * g⁻¹) * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [h]
      _ = (g * u * g⁻¹) * (g * x * g⁻¹) := by group

private theorem s16c167_imgTil_bot_bot {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    imgTil (⊥ : Subgroup G) V hV (⊥ : Subgroup G) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨x, hx, rfl⟩ := (mem_imgTil ⊥ V hV (⊥ : Subgroup G) q).1 hq
  have h1 : x = 1 :=
    IntMod.val_injective (by rw [IntMod.val_one]; exact Subgroup.mem_bot.1 hx)
  rw [h1, map_one]
  exact Subgroup.one_mem _

theorem s16c167_disj_of_perm {g u : G} {Δ : Set (Subgroup G)} (hn : Δ.ncard = 2)
    (hind : sSupIndep Δ)
    (hperm : ∀ J ∈ deltaConj Δ g, conjSubgroup J u ∈ deltaConj Δ g) :
    ∀ J ∈ deltaConj Δ g, conjSubgroup J u = J ∨ J ⊓ conjSubgroup J u = ⊥ := by
  obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.1 hn
  have hbot : a ⊓ b = ⊥ := disjoint_iff.1 ((sSupIndep_pair hab).1 hind)
  have hbotg : conjSubgroup a g ⊓ conjSubgroup b g = ⊥ := by
    rw [← E3.conjSubgroup_inf, hbot, E3.conjSubgroup_bot]
  have hbotg' : conjSubgroup b g ⊓ conjSubgroup a g = ⊥ := by
    rw [inf_comm]; exact hbotg
  have hmem : deltaConj ({a, b} : Set (Subgroup G)) g =
      {conjSubgroup a g, conjSubgroup b g} := by
    unfold deltaConj
    rw [Set.image_pair]
  intro J hJ
  have hp := hperm J hJ
  rw [hmem] at hJ hp
  rcases Set.mem_insert_iff.1 hJ with rfl | hJ
  · rcases Set.mem_insert_iff.1 hp with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; exact hbotg)
  · rw [Set.mem_singleton_iff] at hJ
    subst hJ
    rcases Set.mem_insert_iff.1 hp with h | h
    · exact Or.inr (by rw [h]; exact hbotg')
    · exact Or.inl h

theorem s16c167_disj_of_tilde {D : Data G} {V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ normalizer (V : Set G)) {g : G} {Δ : Set (Subgroup G)}
    (hΔV : ∀ I ∈ Δ, I ≤ V)
    (hdoe : ∀ t ∈ Mbar D.M ⊥ V hV, ∀ I ∈ Δ,
      (imgTil ⊥ V hV I).map t.toMonoidHom = imgTil ⊥ V hV I ∨
        imgTil ⊥ V hV I ⊓ (imgTil ⊥ V hV I).map t.toMonoidHom = ⊥) :
    ∀ u ∈ V ⊓ conjSubgroup D.M g, ∀ J ∈ deltaConj Δ g,
      conjSubgroup J u = J ∨ J ⊓ conjSubgroup J u = ⊥ := by
  intro u hu J hJ
  obtain ⟨I, hI, rfl⟩ := hJ
  set m : G := g * u * g⁻¹ with hm
  have hmM : m ∈ D.M := by rw [hm]; exact mem_conjSubgroup_iff.1 hu.2
  have hmV : m ∈ normalizer (V : Set G) := hM hmM
  have hm_stab : m ∈ stabTil (⊥ : Subgroup G) V := s16c167_mem_stabTil_bot hmV
  have hm2 : m ^ 2 = 1 := by
    rw [pow_two, hm]
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [← pow_two, hV.2 u hu.1]; group
  set tbar : MulAut (Vtil (⊥ : Subgroup G) V hV) :=
    actTil (⊥ : Subgroup G) V hV ⟨m, hm_stab⟩ with htbar
  have htbar_mem : tbar ∈ Mbar D.M (⊥ : Subgroup G) V hV := by
    rw [htbar]; exact actTil_mem_barSub (⊥ : Subgroup G) V hV hmM hm_stab
  have hconj : conjSubgroup (conjSubgroup I g) u = conjSubgroup (conjSubgroup I m) g :=
    s16c167_conj_conj hm I
  have hconjI : imgTil (⊥ : Subgroup G) V hV (conjSubgroup I m) =
      (imgTil (⊥ : Subgroup G) V hV I).map tbar.toMonoidHom := by
    rw [htbar]; exact s16c167_imgTil_conjSubgroup hV hm_stab hm2 I
  have hIV : I ≤ V := hΔV I hI
  have hImV : conjSubgroup I m ≤ V := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hxV : m * x * m⁻¹ ∈ V := hIV hx
    have hx' : m⁻¹ * (m * x * m⁻¹) * m = x := by group
    have hmem := (Subgroup.mem_normalizer_iff''.1 hmV (m * x * m⁻¹)).1 hxV
    rwa [hx'] at hmem
  rcases hdoe tbar htbar_mem I hI with h | h
  · left
    have hcm : conjSubgroup I m = I := by
      apply s16c167_imgTil_inj hV hImV hIV
      rw [hconjI]; exact h
    rw [hconj, hcm]
  · right
    have hcm : I ⊓ conjSubgroup I m = ⊥ := by
      apply s16c167_imgTil_inj hV (le_trans inf_le_left hIV) bot_le
      have hbot : imgTil (⊥ : Subgroup G) V hV (I ⊓ conjSubgroup I m) = ⊥ := by
        rw [s16c167_imgTil_inf_bot hV, hconjI, h]
      rw [hbot, s16c167_imgTil_bot_bot hV]
    rw [hconj, ← E3.conjSubgroup_inf, hcm, E3.conjSubgroup_bot]

theorem s16c167_insp18_of_tilde (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ normalizer (V : Set G)) {g : G} {Δ : Set (Subgroup G)}
    (hΔV : ∀ I ∈ Δ, I ≤ V)
    (hge : D.k + 1 ≤ mBar D.M ⊥ V hV)
    (hbig : ∀ I ∈ Δ, D.k + 1 < rk ↥(imgTil ⊥ V hV I))
    (hdisj : ∀ u ∈ V ⊓ conjSubgroup D.M g, ∀ J ∈ deltaConj Δ g,
      conjSubgroup J u = J ∨ J ⊓ conjSubgroup J u = ⊥)
    (hk2 : Case168_2 D ⊥ V hV L → D.k = 1)
    (hnc : Case168_2 D ⊥ V hV L → ∀ t ∈ Mbar D.M ⊥ V hV, t * t = 1 →
      rkIdx (fixV (Subgroup.zpowers t)) = D.k + 1 →
      (∀ I ∈ Δ, (imgTil ⊥ V hV I).map t.toMonoidHom = imgTil ⊥ V hV I) →
      ∀ I ∈ Δ, ¬ imgTil ⊥ V hV I ≤ fixV (Subgroup.zpowers t))
    (hnt : ¬ Case168_2 D ⊥ V hV L → ∀ t ∈ Mbar D.M ⊥ V hV, t * t = 1 →
      ∀ I ∈ Δ, (imgTil ⊥ V hV I).map t.toMonoidHom = imgTil ⊥ V hV I →
      imgTil ⊥ V hV I ≤ fixV (Subgroup.zpowers t) ∨
        D.k + 1 ≤ E3.mQuot (imgTil ⊥ V hV I) (imgTil ⊥ V hV I ⊓ fixV (Subgroup.zpowers t))) :
    Insp18 D ⊥ V hV L g Δ := by
  refine { ge := hge, big := ?_, disj := ?_, k_eq_one := hk2, dist₂ := ?_, dist := ?_ }
  · intro J hJ
    obtain ⟨I, hI, rfl⟩ := hJ
    have hrk : rk ↥(conjSubgroup I g) = rk ↥(imgTil (⊥ : Subgroup G) V hV I) := by
      unfold rk
      rw [E3.card_conjSubgroup, s16c167_card_imgTil_bot hV (hΔV I hI)]
    rw [hrk]
    exact hbig I hI
  · intro u hu _ J hJ
    exact hdisj u hu J hJ
  · intro hc2 u hu hfixJ hmq J hJ
    obtain ⟨I, hI, rfl⟩ := hJ
    set m : G := g * u * g⁻¹ with hm
    have hmM : m ∈ D.M := by rw [hm]; exact mem_conjSubgroup_iff.1 hu.2
    have hmV : m ∈ normalizer (V : Set G) := hM hmM
    have hm_stab : m ∈ stabTil (⊥ : Subgroup G) V := s16c167_mem_stabTil_bot hmV
    have hm2 : m ^ 2 = 1 := by
      rw [pow_two, hm]
      calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
        _ = 1 := by rw [← pow_two, hV.2 u hu.1]; group
    set tbar : MulAut (Vtil (⊥ : Subgroup G) V hV) :=
      actTil (⊥ : Subgroup G) V hV ⟨m, hm_stab⟩ with htbar
    have htbar_mem : tbar ∈ Mbar D.M (⊥ : Subgroup G) V hV := by
      rw [htbar]; exact actTil_mem_barSub (⊥ : Subgroup G) V hV hmM hm_stab
    have htbar2 : tbar * tbar = 1 := by
      have hmul : (⟨m, hm_stab⟩ : stabTil (⊥ : Subgroup G) V) * ⟨m, hm_stab⟩ = 1 := by
        ext
        show m * m = 1
        rw [← pow_two]; exact hm2
      rw [htbar, ← map_mul, hmul, map_one]
    have hfixV : fixV (Subgroup.zpowers tbar) =
        imgTil (⊥ : Subgroup G) V hV (V ⊓ Subgroup.centralizer ({m} : Set G)) := by
      rw [htbar]; exact s16c167_fixV_actTil hV hm_stab
    have hrkIdx : rkIdx (fixV (Subgroup.zpowers tbar)) =
        E3.mQuot V (V ⊓ Subgroup.centralizer ({m} : Set G)) := by
      rw [htbar]; exact s16c167_rkIdx_fixV_actTil hV hm_stab
    have hCm : conjSubgroup (Subgroup.centralizer ({m} : Set G)) g =
        Subgroup.centralizer ({u} : Set G) := s16c167_conjSubgroup_centralizer_singleton hm
    have hVin : conjSubgroup V g ⊓ Subgroup.centralizer ({u} : Set G) =
        conjSubgroup (V ⊓ Subgroup.centralizer ({m} : Set G)) g := by
      rw [← hCm, ← E3.conjSubgroup_inf]
    have hrk : rkIdx (fixV (Subgroup.zpowers tbar)) = D.k + 1 := by
      rw [hrkIdx, ← E3.mQuot_conjSubgroup V (V ⊓ Subgroup.centralizer ({m} : Set G)) g,
        ← hVin]
      exact hmq
    have hmapAll : ∀ J ∈ Δ, (imgTil (⊥ : Subgroup G) V hV J).map tbar.toMonoidHom =
        imgTil (⊥ : Subgroup G) V hV J := by
      intro J hJ
      have hconjJ : conjSubgroup (conjSubgroup J g) u = conjSubgroup (conjSubgroup J m) g :=
        s16c167_conj_conj hm J
      have hcmJ : conjSubgroup J m = J := by
        apply s16c167_conjSubgroup_inj
        rw [← hconjJ]
        exact hfixJ _ (Set.mem_image_of_mem _ hJ)
      have himgJ : imgTil (⊥ : Subgroup G) V hV (conjSubgroup J m) =
          (imgTil (⊥ : Subgroup G) V hV J).map tbar.toMonoidHom := by
        rw [htbar]; exact s16c167_imgTil_conjSubgroup hV hm_stab hm2 J
      rw [← himgJ, hcmJ]
    have hfixI : imgTil (⊥ : Subgroup G) V hV I ≤ fixV (Subgroup.zpowers tbar) ↔
        I ≤ Subgroup.centralizer ({m} : Set G) := by
      rw [hfixV, s16c167_imgTil_le_iff hV (hΔV I hI) inf_le_left]
      exact ⟨fun h => h.trans inf_le_right, fun h => le_inf (hΔV I hI) h⟩
    have hleC : conjSubgroup I g ≤ Subgroup.centralizer ({u} : Set G) ↔
        I ≤ Subgroup.centralizer ({m} : Set G) := by
      rw [← hCm, E3.conjSubgroup_le_conjSubgroup_iff]
    have hncI : ¬ imgTil (⊥ : Subgroup G) V hV I ≤ fixV (Subgroup.zpowers tbar) :=
      hnc hc2 tbar htbar_mem htbar2 hrk hmapAll I hI
    intro hle
    exact hncI (hfixI.2 (hleC.1 hle))
  · intro hnt2 u hu hfixJ hmq J hJ
    obtain ⟨I, hI, rfl⟩ := hJ
    set m : G := g * u * g⁻¹ with hm
    have hmM : m ∈ D.M := by rw [hm]; exact mem_conjSubgroup_iff.1 hu.2
    have hmV : m ∈ normalizer (V : Set G) := hM hmM
    have hm_stab : m ∈ stabTil (⊥ : Subgroup G) V := s16c167_mem_stabTil_bot hmV
    have hm2 : m ^ 2 = 1 := by
      rw [pow_two, hm]
      calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
        _ = 1 := by rw [← pow_two, hV.2 u hu.1]; group
    set tbar : MulAut (Vtil (⊥ : Subgroup G) V hV) :=
      actTil (⊥ : Subgroup G) V hV ⟨m, hm_stab⟩ with htbar
    have htbar_mem : tbar ∈ Mbar D.M (⊥ : Subgroup G) V hV := by
      rw [htbar]; exact actTil_mem_barSub (⊥ : Subgroup G) V hV hmM hm_stab
    have htbar2 : tbar * tbar = 1 := by
      have hmul : (⟨m, hm_stab⟩ : stabTil (⊥ : Subgroup G) V) * ⟨m, hm_stab⟩ = 1 := by
        ext
        show m * m = 1
        rw [← pow_two]; exact hm2
      rw [htbar, ← map_mul, hmul, map_one]
    have hfixV : fixV (Subgroup.zpowers tbar) =
        imgTil (⊥ : Subgroup G) V hV (V ⊓ Subgroup.centralizer ({m} : Set G)) := by
      rw [htbar]; exact s16c167_fixV_actTil hV hm_stab
    have hCm : conjSubgroup (Subgroup.centralizer ({m} : Set G)) g =
        Subgroup.centralizer ({u} : Set G) := s16c167_conjSubgroup_centralizer_singleton hm
    have hmapAll : ∀ J ∈ Δ, (imgTil (⊥ : Subgroup G) V hV J).map tbar.toMonoidHom =
        imgTil (⊥ : Subgroup G) V hV J := by
      intro J hJ
      have hconjJ : conjSubgroup (conjSubgroup J g) u = conjSubgroup (conjSubgroup J m) g :=
        s16c167_conj_conj hm J
      have hcmJ : conjSubgroup J m = J := by
        apply s16c167_conjSubgroup_inj
        rw [← hconjJ]
        exact hfixJ _ (Set.mem_image_of_mem _ hJ)
      have himgJ : imgTil (⊥ : Subgroup G) V hV (conjSubgroup J m) =
          (imgTil (⊥ : Subgroup G) V hV J).map tbar.toMonoidHom := by
        rw [htbar]; exact s16c167_imgTil_conjSubgroup hV hm_stab hm2 J
      rw [← himgJ, hcmJ]
    have hfixI : imgTil (⊥ : Subgroup G) V hV I ≤ fixV (Subgroup.zpowers tbar) ↔
        I ≤ Subgroup.centralizer ({m} : Set G) := by
      rw [hfixV, s16c167_imgTil_le_iff hV (hΔV I hI) inf_le_left]
      exact ⟨fun h => h.trans inf_le_right, fun h => le_inf (hΔV I hI) h⟩
    have hleC : conjSubgroup I g ≤ Subgroup.centralizer ({u} : Set G) ↔
        I ≤ Subgroup.centralizer ({m} : Set G) := by
      rw [← hCm, E3.conjSubgroup_le_conjSubgroup_iff]
    have hJinf : conjSubgroup I g ⊓ Subgroup.centralizer ({u} : Set G) =
        conjSubgroup (I ⊓ Subgroup.centralizer ({m} : Set G)) g := by
      rw [← hCm, ← E3.conjSubgroup_inf]
    have hIeq : I ⊓ Subgroup.centralizer ({m} : Set G) =
        I ⊓ (V ⊓ Subgroup.centralizer ({m} : Set G)) := by
      rw [← inf_assoc, inf_eq_left.2 (hΔV I hI)]
    have hmqJ : E3.mQuot (conjSubgroup I g)
          (conjSubgroup I g ⊓ Subgroup.centralizer ({u} : Set G)) =
        E3.mQuot (imgTil (⊥ : Subgroup G) V hV I)
          (imgTil (⊥ : Subgroup G) V hV I ⊓ fixV (Subgroup.zpowers tbar)) := by
      rw [hJinf, E3.mQuot_conjSubgroup I (I ⊓ Subgroup.centralizer ({m} : Set G)) g,
        ← s16c167_mQuot_imgTil hV (hΔV I hI) inf_le_left, hIeq,
        s16c167_imgTil_inf_bot, hfixV]
    rcases hnt hnt2 tbar htbar_mem htbar2 I hI (hmapAll I hI) with h | h
    · exact Or.inl (hleC.2 (hfixI.1 h))
    · exact Or.inr (by rw [hmqJ]; exact h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
