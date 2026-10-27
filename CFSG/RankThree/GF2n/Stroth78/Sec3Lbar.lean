module


import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen
public import CFSG.RankThree.GF2n.Stroth78.Sec2Fifteen

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

noncomputable abbrev aVec (S : Setting z E F) {a : G} (haQ : a ∈ Q z) :
    Additive (QbarOf S) :=
  Additive.ofMul (mkQbar S ⟨a, haQ⟩)

theorem exists_mem_L0_of_mem_Lbar (S : Setting z E F) {a : G} {ℓ : Hbar z}
    (hℓ : ℓ ∈ Lbar S a) :
    ∃ c : ↥(H z), (c : G) ∈ L0 S a ∧ (QuotientGroup.mk c : Hbar z) = ℓ := by
  rw [← map_L0_eq_Lbar S a] at hℓ
  obtain ⟨c, hc, hcℓ⟩ := Subgroup.mem_map.mp hℓ
  exact ⟨c, Subgroup.mem_subgroupOf.mp hc, by simpa [QuotientGroup.mk'_apply] using hcℓ⟩

theorem commutator_mem_zpowers_of_mem_L0 (S : Setting z E F) {a : G} (hconj : IsConj z a)
    {c c' : G} (hc : c ∈ L0 S a) (hc' : c' ∈ L0 S a) :
    ⁅c, c'⁆ ∈ Subgroup.zpowers a := by
  have h1 : c ∈ QaOf a := (Subgroup.mem_inf.mp hc).1
  have h2 : c' ∈ QaOf a := (Subgroup.mem_inf.mp hc').1
  have hmem : ⁅c, c'⁆ ∈ ⁅QaOf a, QaOf a⁆ := Subgroup.commutator_mem_commutator h1 h2
  rwa [QaOf_deriv_eq_zpowers S hconj] at hmem

theorem sq_mem_zpowers_of_mem_L0 (S : Setting z E F) {a : G} (hconj : IsConj z a)
    {c : G} (hc : c ∈ L0 S a) : c ^ 2 ∈ Subgroup.zpowers a := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hcQa : c ∈ QaOf a := (Subgroup.mem_inf.mp hc).1
  rw [QaOf_eq_map_conj S hg] at hcQa
  obtain ⟨q, hqQ, hq⟩ := Subgroup.mem_map.mp hcQa
  have hq2 : q ^ 2 ∈ Subgroup.zpowers z := sq_mem_zpowers_of_mem_Q S hqQ
  have hgz : (MulAut.conj g).toMonoidHom z = a := by
    change g * z * g⁻¹ = a
    exact hg
  have hmap : (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers a := by
    rw [MonoidHom.map_zpowers, hgz]
  have hmem : c ^ 2 ∈ (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom := by
    rw [← hq, ← map_pow]
    exact Subgroup.mem_map_of_mem _ hq2
  rwa [hmap] at hmem

theorem commute_of_mem_Lbar (S : Setting z E F) {a : G} (haQ : a ∈ Q z) (hconj : IsConj z a)
    {ℓ ℓ' : Hbar z} (hℓ : ℓ ∈ Lbar S a) (hℓ' : ℓ' ∈ Lbar S a) : ℓ * ℓ' = ℓ' * ℓ := by
  obtain ⟨c, hcL, rfl⟩ := exists_mem_L0_of_mem_Lbar S hℓ
  obtain ⟨c', hc'L, rfl⟩ := exists_mem_L0_of_mem_Lbar S hℓ'
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
  have hcomm : ⁅(c : G), (c' : G)⁆ ∈ Q z :=
    Subgroup.zpowers_le.mpr haQ (commutator_mem_zpowers_of_mem_L0 S hconj hcL hc'L)
  have hcommH : ⁅c, c'⁆ ∈ (Q z).subgroupOf (H z) := by
    rw [Subgroup.mem_subgroupOf]
    show ⁅(c : G), (c' : G)⁆ ∈ Q z
    exact hcomm
  have hdiv : c * c' / (c' * c) = ⁅c, c'⁆ := by
    rw [div_eq_mul_inv, commutatorElement_def]
    group
  rwa [hdiv]

theorem sq_eq_one_of_mem_Lbar (S : Setting z E F) {a : G} (haQ : a ∈ Q z) (hconj : IsConj z a)
    {ℓ : Hbar z} (hℓ : ℓ ∈ Lbar S a) : ℓ ^ 2 = 1 := by
  obtain ⟨c, hcL, rfl⟩ := exists_mem_L0_of_mem_Lbar S hℓ
  rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hsq : (c : G) ^ 2 ∈ Q z :=
    Subgroup.zpowers_le.mpr haQ (sq_mem_zpowers_of_mem_L0 S hconj hcL)
  simpa [pow_two] using hsq

theorem rhoBar_apply_aVec_of_mem_Lbar (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    (hconj : IsConj z a) {ℓ : Hbar z} (hℓ : ℓ ∈ Lbar S a) :
    (rhoBar S ℓ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) (aVec S haQ) =
      aVec S haQ := by
  obtain ⟨h, hhL, rfl⟩ := exists_mem_L0_of_mem_Lbar S hℓ
  have hhQa : (h : G) ∈ QaOf a := (Subgroup.mem_inf.mp hhL).1
  have haCent : a ∈ Subgroup.centralizer (QaOf a : Set G) :=
    (Subgroup.mem_inf.mp (mem_centerIn_QaOf_of_isConj S hconj)).2
  have hcomm : (h : G) * a = a * (h : G) :=
    Subgroup.mem_centralizer_iff.mp haCent (h : G) hhQa
  have hfix : conjAutQ S h ⟨a, haQ⟩ = ⟨a, haQ⟩ := by
    apply Subtype.ext
    rw [conjAutQ_apply]
    calc
      (h : G) * a * (h : G)⁻¹ = a * (h : G) * (h : G)⁻¹ := by rw [hcomm]
      _ = a := by group
  rw [rhoBar_apply_mk, rho_apply_mk]
  change conjQbar S h (Additive.ofMul (mkQbar S ⟨a, haQ⟩)) =
    Additive.ofMul (mkQbar S ⟨a, haQ⟩)
  simp only [mkQbar, QuotientGroup.mk'_apply]
  rw [conjQbar_apply_mk, hfix]

theorem qS_aVec_eq_zero (S : Setting z E F) {a : G} (haQ : a ∈ Q z) (hconj : IsConj z a) :
    qS S (aVec S haQ) = 0 := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  exact (q_eq_zero_iff S ⟨a, haQ⟩).mpr (sq_eq_one_of_isConj S hconj)

theorem mem_QaInterImage_CQ_of_polar_aVec_eq_zero (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) {v : Additive (QbarOf S)}
    (hv : QuadraticMap.polar (qS S) v (aVec S haQ) = 0) :
    v ∈ QaInterImage S (Q z ⊓ Subgroup.centralizer ({a} : Set G)) := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  have hB : (qS S).polarBilin (aVec S haQ) v = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply]
    exact (QuadraticMap.polar_comm (qS S) (aVec S haQ) v).trans hv
  rw [QaInterImage_CQ_eq_orthogonal S haQ, LinearMap.BilinForm.mem_orthogonal_iff]
  intro x hx
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl
  · simp
  · simpa [aVec] using hB

theorem rhoBar_sub_mem_QaInterImage (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    {ℓ : Hbar z} (hℓ : ℓ ∈ Lbar S a) {v : Additive (QbarOf S)}
    (hv : QuadraticMap.polar (qS S) v (aVec S haQ) = 0) :
    (rhoBar S ℓ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) v - v ∈
      QaInterImage S (Q z ⊓ QaOf a) :=
  commutator_Lbar_CQ_le S ℓ hℓ v (mem_QaInterImage_CQ_of_polar_aVec_eq_zero S haQ hv)

theorem rhoBar_apply_eq_of_invariant (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    (hconj : IsConj z a) (hza : z ∈ QaOf a)
    {U : Submodule (ZMod 2) (Additive (QbarOf S))}
    (hUa : ∀ u ∈ U, QuadraticMap.polar (qS S) u (aVec S haQ) = 0) (haU : aVec S haQ ∉ U)
    (hinv : ∀ ℓ ∈ Lbar S a, ∀ u ∈ U,
      (rhoBar S ℓ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) u ∈ U) :
    ∀ ℓ ∈ Lbar S a, ∀ u ∈ U,
      (rhoBar S ℓ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) u = u := by
  intro ℓ hℓ u hu
  let ρℓ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S) := rhoBar S ℓ
  let d : Additive (QbarOf S) := ρℓ u - u
  have hdU : d ∈ U := Submodule.sub_mem U (hinv ℓ hℓ u hu) hu
  have hdQ : d ∈ QaInterImage S (Q z ⊓ QaOf a) := by
    have h := rhoBar_sub_mem_QaInterImage S haQ hℓ (hUa u hu)
    simpa [d, ρℓ] using h
  by_contra hne
  have hd_ne : d ≠ 0 := sub_ne_zero.mpr hne
  have hdspan : d ∉ (ZMod 2) ∙ aVec S haQ := by
    intro hmem
    rw [CFSG.LargeExtraspecial.OrthoF2.mem_span_singleton_iff] at hmem
    rcases hmem with h | h
    · exact hd_ne h
    · exact haU (h ▸ hdU)
  obtain ⟨y, hyA, hyv⟩ := (mem_QaInterImage_iff S).mp hdQ
  have hbv : Additive.ofMul (mkQbar S ⟨(y : G), y.2⟩) = d := by
    simpa using congrArg Additive.ofMul hyv
  have hb_not : Additive.ofMul (mkQbar S ⟨(y : G), y.2⟩) ∉ (ZMod 2) ∙ aVec S haQ := by
    rw [hbv]
    exact hdspan
  obtain ⟨l, hl, hsub⟩ :=
    exists_lbar_apply_sub_eq S haQ hconj hza y.2 (Subgroup.mem_inf.mp hyA).2 hb_not
  have hsub' : (rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) d - d =
      aVec S haQ := by
    rw [← hbv]
    exact hsub
  have hmemU : (rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) d - d ∈ U :=
    Submodule.sub_mem U (hinv l hl d hdU) hdU
  exact haU (by rw [← hsub']; exact hmemU)

theorem rhoBar_sub_mem_span_of_mem_Rbar (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a) {r : Hbar z}
    (hr : r ∈ Rbar S a) {v : Additive (QbarOf S)}
    (hv : QuadraticMap.polar (qS S) v (aVec S haQ) = 0) :
    (rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) v - v ∈
      (ZMod 2) ∙ aVec S haQ := by
  by_cases hr1 : r = 1
  · subst r
    simp
  · obtain ⟨s, hsZ, hsH, -, hsr⟩ := exists_mem_centerIn_inf_H_of_mem_Rbar S hr hr1
    have hzaZ : z ∉ centerIn (QaOf a) :=
      z_not_mem_centerIn_Qa S haQ hconj haZ hza
    have hvW := mem_QaInterImage_CQ_of_polar_aVec_eq_zero S haQ hv
    have hmap := map_sub_QaInterImage_CQ_le_span S haQ hconj hzaZ hsZ hsH
    have hmem : ((conjQbar S ⟨s, hsH⟩ :
        Additive (QbarOf S) →ₗ[ZMod 2] Additive (QbarOf S)) - 1) v ∈
        Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S ⟨a, haQ⟩)} :=
      hmap (Submodule.mem_map.mpr ⟨v, hvW, rfl⟩)
    rw [← hsr, rhoBar_apply_mk, rho_apply_mk]
    simpa [aVec] using hmem

end CFSG.RankThree.GF2n.Stroth78
