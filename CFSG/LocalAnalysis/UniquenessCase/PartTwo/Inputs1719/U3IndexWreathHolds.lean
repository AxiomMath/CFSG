module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFourBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFourFour
public import CFSG.LocalAnalysis.WeakClosure81.OrbitClosureCentreQuot
public import CFSG.LocalAnalysis.WeakClosure81.CFAutAlmostSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {Q : Type} [Group Q] [Finite Q]

theorem cfAutInFGroup_of_component_U3 (hF : K_U3IndexF) {K S : Subgroup Q}
    (hK : CFSG.IsComponent K) (hS2 : IsPGroup 2 S)
    (hKT : orbitClosure K S ⊔ S = ⊤)
    {n : ℕ} (hU3 : IsU3 (↥K ⧸ Subgroup.center ↥K) n) :
    CFAutInFGroup n Q S := by
  classical
  intro X hXn hXne hXmin hXnc L hL
  let F : Subgroup Q := orbitClosure K S
  have hFnorm : F.Normal := orbitClosure_normal hKT
  have hQF2 : IsPGroup 2 (Q ⧸ F) := by
    have : F.Normal := hFnorm
    have : (F.subgroupOf (⊤ : Subgroup Q)).Normal := hFnorm.subgroupOf ⊤
    have htop : IsPGroup 2 ((⊤ : Subgroup Q) ⧸ F.subgroupOf ⊤) :=
      CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq (p := 2) (G := Q)
        (L := F) (Q := S) (K := ⊤) hS2 le_top
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hFnorm]; exact le_top) hKT
    have he : (F.subgroupOf (⊤ : Subgroup Q)).map
        (Subgroup.topEquiv (G := Q)).toMonoidHom = F := by
      ext x
      simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact IsPGroup.of_equiv htop
      (QuotientGroup.congr (F.subgroupOf ⊤) F Subgroup.topEquiv he)
  have hLcomp : CFSG.IsComponent L := by
    have hsub : CFSG.Open.IsSubnormal L ⊤ :=
      CFSG.Open.IsSubnormal.trans hL.2.1
        (CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal hXn))
    exact ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL.2.2,
      CFSG.Quasithin.A3.subnormal_top_iff.mp hsub⟩
  have hLleF : L ≤ F := by
    by_contra hnot
    let π : Q →* Q ⧸ F := QuotientGroup.mk' F
    have hmapne : L.map π ≠ ⊥ := fun hbot =>
      hnot (by simpa [π, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff L).mp hbot)
    have : Nontrivial ↥(L.map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hmapne
    have hsol : Group.IsSolvable ↥(L.map π) :=
      @IsNilpotent.to_isSolvable _ _ (hQF2.to_subgroup (L.map π)).isNilpotent
    have hperf : Group.IsPerfect ↥(L.map π) := by
      have : Group.IsPerfect ↥L := hLcomp.1.1
      exact Group.IsPerfect.map π
    exact Group.IsPerfect.not_isSolvable ↥(L.map π) hsol
  have hconj : ∃ s ∈ S, L = K.map (MulAut.conj s).toMonoidHom := by
    by_contra hnot
    push Not at hnot
    have hcomm : ∀ s ∈ S, ⁅K.map (MulAut.conj s).toMonoidHom, L⁆ = ⊥ := by
      intro s hs
      rcases CFSG.LocalCores.distinct_components_commute (isComponent_map_conjAut hK s)
        hLcomp with h | h
      · exact absurd h.symm (hnot s hs)
      · exact h
    have hFleC : F ≤ Subgroup.centralizer (L : Set Q) :=
      orbitClosure_le fun s hs =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm s hs)
    have hLleCF : L ≤ Subgroup.centralizer (F : Set Q) := by
      rw [Subgroup.le_centralizer_iff]
      exact hFleC
    have hLcomm : IsMulCommutative ↥L :=
      ⟨⟨fun a b => Subtype.ext
        ((Subgroup.mem_centralizer_iff.mp (hLleCF a.2) (b : Q) (hLleF b.2)).symm)⟩⟩
    have : Group.IsPerfect ↥L := hLcomp.1.1
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hLcomp.1
    exact Group.IsPerfect.not_isMulCommutative L hLcomm
  obtain ⟨s, hs, hsL⟩ := hconj
  have hU3L : IsU3 (↥L ⧸ Subgroup.center ↥L) n := by
    rw [hsL]
    exact LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center ↥K)
        (Subgroup.center ↥(K.map (MulAut.conj s).toMonoidHom))
        (Subgroup.equivMapOfInjective K (MulAut.conj s).toMonoidHom
          (MulAut.conj s).injective)
        (Subgroup.map_center_eq _)) hU3
  let N : Subgroup Q := F12.autNL S L
  let Lq : Subgroup ↥N := L.subgroupOf N
  let Kq : Subgroup ↥N := (S ⊓ Subgroup.normalizer (L : Set Q)).subgroupOf N
  have hKN : S ⊓ Subgroup.normalizer (L : Set Q) ≤ N := by
    show _ ≤ (S ⊓ Subgroup.normalizer (L : Set Q)) ⊔ L
    exact le_sup_left
  have hNL : N ≤ Subgroup.normalizer (L : Set Q) := by
    show (S ⊓ Subgroup.normalizer (L : Set Q)) ⊔ L ≤ _
    exact sup_le inf_le_right Subgroup.le_normalizer
  have hLq : Lq.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (show L ≤ N from le_sup_right)).mpr hNL
  have : Lq.Normal := hLq
  have hKq2 : IsPGroup 2 Kq := by
    have h1 : IsPGroup 2 ↥(S ⊓ Subgroup.normalizer (L : Set Q)) := hS2.to_le inf_le_left
    let e : ↥Kq ≃* ↥(S ⊓ Subgroup.normalizer (L : Set Q)) :=
      Subgroup.subgroupOfEquivOfLe hKN
    exact IsPGroup.of_equiv h1 e.symm
  have hsup : Lq ⊔ Kq = ⊤ := by
    have hN : L ⊔ (S ⊓ Subgroup.normalizer (L : Set Q)) = N := by
      show L ⊔ (S ⊓ Subgroup.normalizer (L : Set Q)) =
        (S ⊓ Subgroup.normalizer (L : Set Q)) ⊔ L
      exact sup_comm ..
    have h1 : (L ⊔ (S ⊓ Subgroup.normalizer (L : Set Q))).subgroupOf N = Lq ⊔ Kq :=
      Subgroup.subgroupOf_sup (A := L) (A' := S ⊓ Subgroup.normalizer (L : Set Q))
        (B := N) le_sup_right le_sup_left
    rw [hN] at h1
    rw [← h1, Subgroup.subgroupOf_self]
  have hLq_quasi : CFSG.Open.IsQuasisimple ↥Lq :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_right) hL.2.2
  have hU3q : IsU3 (↥Lq ⧸ Subgroup.center ↥Lq) n :=
    LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center ↥Lq) (Subgroup.center ↥L)
        (Subgroup.subgroupOfEquivOfLe le_sup_right) (Subgroup.map_center_eq _)).symm hU3L
  have hCeq : (F12.autC S L).subgroupOf N =
      Subgroup.centralizer (Lq : Set ↥N) := by
    ext x
    show (x : Q) ∈ F12.autC S L ↔ x ∈ Subgroup.centralizer (Lq : Set ↥N)
    simp only [F12.autC, F12.autNL, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, hc⟩ y hy
      exact Subtype.ext (hc (y : Q) hy)
    · intro hc
      refine ⟨x.2, fun y hy => ?_⟩
      have hyN : y ∈ N := by
        show y ∈ (S ⊓ Subgroup.normalizer (L : Set Q)) ⊔ L
        exact Subgroup.mem_sup_right hy
      let yN : ↥N := ⟨y, hyN⟩
      have hyLq : yN ∈ Lq := Subgroup.mem_subgroupOf.mpr hy
      exact congrArg Subtype.val (hc yN hyLq)
  have hCn : ((F12.autC S L).subgroupOf N).Normal :=
    hCeq ▸ Subgroup.normal_centralizer
  have : ((F12.autC S L).subgroupOf N).Normal := hCn
  have hres := hF N Lq Kq ((F12.autC S L).subgroupOf N) n hCeq hLq_quasi hU3q hKq2 hsup
  exact ⟨hCn, hres⟩

theorem compFactorAutInF_of_orbitClosure_U3 (hF : K_U3IndexF)
    (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) {K T : Subgroup Q} (hK : CFSG.IsComponent K)
    (hT : IsSylowIn 2 T ⊤) (hKT : orbitClosure K T ⊔ T = ⊤) {n : ℕ}
    (hU3 : IsU3 (↥K ⧸ Subgroup.center ↥K) n) :
    ∀ T' : Subgroup Q, CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ → CompFactorAutInF n ⊤ T' := by
  classical
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hFnorm : (orbitClosure K T).Normal := orbitClosure_normal hKT
  have hQF2 : IsPGroup 2 (Q ⧸ orbitClosure K T) := by
    have : (orbitClosure K T).Normal := hFnorm
    have : ((orbitClosure K T).subgroupOf (⊤ : Subgroup Q)).Normal :=
      hFnorm.subgroupOf ⊤
    have htop : IsPGroup 2 ((⊤ : Subgroup Q) ⧸ (orbitClosure K T).subgroupOf ⊤) :=
      CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq (p := 2) (G := Q)
        (L := orbitClosure K T) (Q := T) (K := ⊤) hT2 le_top
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hFnorm]; exact le_top) hKT
    have he : ((orbitClosure K T).subgroupOf (⊤ : Subgroup Q)).map
        (Subgroup.topEquiv (G := Q)).toMonoidHom = orbitClosure K T := by
      ext x
      simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact IsPGroup.of_equiv htop
      (QuotientGroup.congr ((orbitClosure K T).subgroupOf ⊤) (orbitClosure K T)
        Subgroup.topEquiv he)
  intro T' hT'
  have hT'in : IsSylowIn 2 T' ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT'
  obtain ⟨q, -, hq⟩ := CFSG.Quasithin.Ch1Sec3.exists_conj_of_isSylowIn hT hT'in
  have hT'eq : T' = T.map (MulAut.conj q).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨q⁻¹ * x * q, (hq x).mp hx, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨y, hy, rfl⟩
      exact (hq (q * y * q⁻¹)).mpr (by
        rw [show q⁻¹ * (q * y * q⁻¹) * q = y from by group]
        exact hy)
  set K' : Subgroup Q := K.map (MulAut.conj q).toMonoidHom with hK'def
  have hK' : CFSG.IsComponent K' := isComponent_map_conjAut hK q
  have hFconj : orbitClosure K' T' = orbitClosure K T := by
    rw [hK'def, hT'eq]
    exact (orbitClosure_map (MulAut.conj q).toMonoidHom K T).symm.trans
      (Subgroup.Normal.map_conj_eq (orbitClosure K T) q)
  have hFT' : orbitClosure K T ⊔ T' = ⊤ := by
    have : (orbitClosure K T).Normal := hFnorm
    let P : Sylow 2 Q := hT'in.isPGroup.toSylow (by simpa using hT'in.not_dvd_relIndex)
    have h := CFSG.section10_sylow_sup_normal_of_p_quotient_eq_top
      (N := orbitClosure K T) hQF2 P
    rw [IsPGroup.toSylow_coe] at h
    rw [sup_comm]
    exact h
  have hU3' : IsU3 (↥K' ⧸ Subgroup.center ↥K') n := by
    rw [hK'def]
    exact LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center ↥K)
        (Subgroup.center ↥(K.map (MulAut.conj q).toMonoidHom))
        (Subgroup.equivMapOfInjective K (MulAut.conj q).toMonoidHom
          (MulAut.conj q).injective)
        (Subgroup.map_center_eq _)) hU3
  intro Y hY hYn
  have hYnorm : Y.Normal := by
    have h := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : Y ≤ ⊤)).mp hYn
    exact Subgroup.normalizer_eq_top_iff.mp (le_antisymm le_top h)
  let NQ := ↥(⊤ : Subgroup Q) ⧸ Y.subgroupOf ⊤
  let π : Q →* NQ :=
    (QuotientGroup.mk' (Y.subgroupOf ⊤)).comp (Subgroup.topEquiv (G := Q)).symm.toMonoidHom
  have hπsurj : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := Q)).symm.surjective
  have hπker : π.ker = Y := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' : (Subgroup.topEquiv (G := Q)).symm x ∈ Y.subgroupOf ⊤ :=
        (QuotientGroup.eq_one_iff _).mp hx
      simpa [Subgroup.mem_subgroupOf] using hx'
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mpr (by
        simpa [Subgroup.mem_subgroupOf] using hx)
  by_cases hFY : orbitClosure K T ≤ Y
  · have hN2 : IsPGroup 2 NQ := by
      have hFYker : orbitClosure K T ≤ π.ker := by rw [hπker]; exact hFY
      refine IsPGroup.of_surjective hQF2
        (QuotientGroup.lift (orbitClosure K T) π hFYker) ?_
      exact QuotientGroup.lift_surjective_of_surjective _ π hπsurj hFYker
    exact cfAutInFGroup_of_isPGroup Nat.prime_two hN2 n _
  · have hYleZ : Y ≤ orbitClosure K T ⊓
        Subgroup.centralizer (orbitClosure K T : Set Q) :=
      (orbitClosure_le_or_le_inf_centralizer hO2 hK hT2 hKT hYnorm).resolve_left hFY
    by_cases hZY : orbitClosure K T ⊓
        Subgroup.centralizer (orbitClosure K T : Set Q) ≤ Y
    · have hYZ : Y = orbitClosure K T ⊓
          Subgroup.centralizer (orbitClosure K T : Set Q) := le_antisymm hYleZ hZY
      have hZeq : (orbitClosure K T ⊓ Subgroup.centralizer (orbitClosure K T : Set Q)) =
          (Subgroup.center ↥(CFSG.layer Q)).map (CFSG.layer Q).subtype := by
        have hFeq : orbitClosure K T = CFSG.layer Q :=
          le_antisymm (orbitClosure_le_layer hK) (layer_le_orbitClosure hO2 hT2 hKT)
        rw [hFeq]
        ext x
        rw [Subgroup.mem_inf, CFSG.LocalCores.mem_map_center_iff]
      have hK'Z : K' ⊓ Y = (Subgroup.center ↥K').map K'.subtype := by
        rw [hYZ, hZeq]
        exact (CFSG.LocalCores.layer_center (G := Q)).2 K' hK'
      have hK'leF : K' ≤ orbitClosure K T := by
        rw [hK'def]
        calc K.map (MulAut.conj q).toMonoidHom ≤
              (orbitClosure K T).map (MulAut.conj q).toMonoidHom :=
              Subgroup.map_mono (le_orbitClosure K T)
          _ = orbitClosure K T := Subgroup.Normal.map_conj_eq (orbitClosure K T) q
      have hZcent : Y ≤ Subgroup.centralizer (K' : Set Q) := by
        rw [hYZ]
        exact inf_le_right.trans (Subgroup.centralizer_le hK'leF)
      obtain ⟨hKbar, ⟨eKbar⟩⟩ :=
        isComponent_map_of_inf_eq_center π hπsurj hK' hπker hK'Z
      have hU3bar : IsU3 (↥(K'.map π) ⧸ Subgroup.center ↥(K'.map π)) n := by
        have hcent : Subgroup.center (↥K' ⧸ Subgroup.center ↥K') = ⊥ :=
          center_eq_bot_of_isU3 hU3'
        refine LieModel.of_mulEquiv ?_ hU3'
        exact ((QuotientGroup.congr (Subgroup.center ↥(K'.map π))
            (Subgroup.center (↥K' ⧸ Subgroup.center ↥K')) eKbar
            (Subgroup.map_center_eq eKbar)).trans
          ((QuotientGroup.quotientMulEquivOfEq hcent).trans QuotientGroup.quotientBot)).symm
      have hS2bar : IsPGroup 2 (T'.map π) := IsPGroup.map hT'in.isPGroup π
      have hKTbar : orbitClosure (K'.map π) (T'.map π) ⊔ T'.map π = ⊤ := by
        have h1 : orbitClosure (K'.map π) (T'.map π) = (orbitClosure K' T').map π :=
          (orbitClosure_map π K' T').symm
        rw [h1, hFconj, ← Subgroup.map_sup, hFT',
          Subgroup.map_top_of_surjective π hπsurj]
      have hres := cfAutInFGroup_of_component_U3 hF hKbar hS2bar hKTbar hU3bar
      have hSbarEq : T'.map π =
          (T'.subgroupOf ⊤).map (QuotientGroup.mk' (Y.subgroupOf ⊤)) := by
        rw [show π = (QuotientGroup.mk' (Y.subgroupOf ⊤)).comp
          (Subgroup.topEquiv (G := Q)).symm.toMonoidHom from rfl, ← Subgroup.map_map]
        congr 1
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          simpa [Subgroup.mem_subgroupOf] using hy
        · intro hx
          exact ⟨(x : Q), hx, Subtype.ext rfl⟩
      rwa [hSbarEq] at hres
    · intro X hXn hXne hXmin hXnc L hL
      exfalso
      have hXtil_norm : (X.comap π).Normal := hXn.comap π
      have hXtil_ne : X.comap π ≠ ⊥ := by
        intro hbot
        apply hXne
        have hmap : (X.comap π).map π = X :=
          Subgroup.map_comap_eq_self_of_surjective hπsurj X
        rw [hbot, Subgroup.map_bot] at hmap
        exact hmap.symm
      have hZcomm : IsMulCommutative ↥(orbitClosure K T ⊓
          Subgroup.centralizer (orbitClosure K T : Set Q)) := by
        refine ⟨⟨fun a b => ?_⟩⟩
        exact Subtype.ext
          (Subgroup.mem_centralizer_iff.mp a.2.2 (b : Q) b.2.1).symm
      have hZmap_comm : IsMulCommutative ↥((orbitClosure K T ⊓
          Subgroup.centralizer (orbitClosure K T : Set Q)).map π) := by
        refine ⟨⟨fun a b => ?_⟩⟩
        obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
        obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
        have h := congrArg (fun z : ↥(orbitClosure K T ⊓
            Subgroup.centralizer (orbitClosure K T : Set Q)) => π (z : Q))
          (hZcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
        apply Subtype.ext
        show (a : NQ) * (b : NQ) = (b : NQ) * (a : NQ)
        rw [← hxa, ← hyb]
        simpa using h
      rcases orbitClosure_le_or_le_inf_centralizer hO2 hK hT2 hKT hXtil_norm with
        hFX | hXZ
      · have hZle : orbitClosure K T ⊓
            Subgroup.centralizer (orbitClosure K T : Set Q) ≤ X.comap π :=
          inf_le_left.trans hFX
        have hZmap_le : (orbitClosure K T ⊓
            Subgroup.centralizer (orbitClosure K T : Set Q)).map π ≤ X := by
          rw [← Subgroup.map_comap_eq_self_of_surjective hπsurj X]
          exact Subgroup.map_mono hZle
        have hZmap_ne : (orbitClosure K T ⊓
            Subgroup.centralizer (orbitClosure K T : Set Q)).map π ≠ ⊥ := by
          intro hbot
          apply hZY
          intro z hz
          have hzπ : π z ∈ (orbitClosure K T ⊓
              Subgroup.centralizer (orbitClosure K T : Set Q)).map π :=
            Subgroup.mem_map_of_mem π hz
          rw [hbot] at hzπ
          rw [← hπker, MonoidHom.mem_ker]
          exact Subgroup.mem_bot.mp hzπ
        have hZmap_norm : ((orbitClosure K T ⊓
            Subgroup.centralizer (orbitClosure K T : Set Q)).map π).Normal := by
          have : (orbitClosure K T).Normal := hFnorm
          exact (Subgroup.normal_inf_normal _ _).map π hπsurj
        rcases hXmin _ hZmap_norm hZmap_le with hbot | htop
        · exact hZmap_ne hbot
        · exact hXnc (htop ▸ hZmap_comm)
      · have hXle : X ≤ (orbitClosure K T ⊓
            Subgroup.centralizer (orbitClosure K T : Set Q)).map π := by
          rw [← Subgroup.map_comap_eq_self_of_surjective hπsurj X]
          exact Subgroup.map_mono hXZ
        refine hXnc ⟨⟨fun a b => ?_⟩⟩
        have hcomm := congrArg Subtype.val (hZmap_comm.is_comm.comm
          ⟨a, hXle a.2⟩ ⟨b, hXle b.2⟩)
        exact Subtype.ext (by simpa using hcomm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

theorem k_U3IndexWreath_of_F (hF : K_U3IndexF) (h45 : W3Lem45_2Chief) :
    K_U3IndexWreath := by
  intro X _ _ K T H n hsub hnotnorm hperf hq hSU3 hTsyl hsup
  have hKH : K ≤ H := hsup ▸ le_sup_left
  have hTH : T ≤ H := hsup ▸ le_sup_right
  let Kbar : Subgroup (Bar2 H) :=
    (K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
  let Tbar : Subgroup (Bar2 H) :=
    (T.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
  have hKbar : CFSG.IsComponent Kbar :=
    s13_barImage_isComponent (M := H) (L := K) ⟨hsub, hperf, hq⟩
  have hTbar : IsSylowIn 2 Tbar ⊤ := isSylowIn_barImage hTsyl
  have hgen : Kbar ⊔ Tbar = ⊤ := by
    have h := s13_barImage_sup (M := H) (A := K) (B := T) hKH hTH
    rw [hsup, s13_barImage_self] at h
    exact h.symm
  have hKT : orbitClosure Kbar Tbar ⊔ Tbar = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le ((le_orbitClosure Kbar Tbar).trans le_sup_left) le_sup_right
  have hO2 : pCoreOf 2 (⊤ : Subgroup (Bar2 H)) = ⊥ := by
    rw [CFSG.CGT.PushingUpLit.Glue.pCoreOf_top_eq, pCore_two_bar2_eq_bot]
  have hKbarU3 : IsU3 (↥Kbar ⧸ Subgroup.center ↥Kbar) n := by
    obtain ⟨e, -⟩ := UC22.uc22p20d_bar2Equiv hKH hsub
    exact LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center (Bar2 K)) (Subgroup.center ↥Kbar) e
        (Subgroup.map_center_eq e)) hSU3.2
  have hn2 : 2 ≤ n := UC22.uc22p22a_two_le_of_isU3 hSU3.2
  have hcf : ∀ T' : Subgroup (Bar2 H), CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ →
      CompFactorAutInF n ⊤ T' :=
    compFactorAutInF_of_orbitClosure_U3 hF hO2 hKbar hTbar hKT hKbarU3
  exact inFSq_of_components h45 (by omega) hKbar hTbar hKT hcf

theorem k_U3Index_of_normal_and_F (hN : K_U3IndexNormal) (hF : K_U3IndexF)
    (h45 : W3Lem45_2Chief) : K_U3Index :=
  k_U3Index_of_normal_and_wreath hN (k_U3IndexWreath_of_F hF h45)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
