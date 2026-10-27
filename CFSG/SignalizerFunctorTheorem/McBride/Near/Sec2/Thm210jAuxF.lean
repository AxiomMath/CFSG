module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210SetupGlobal

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

section Abstract

variable {p : ℕ} {X : Type*} [Group X] [Finite X]

theorem NearSimple.mem_fitting_of_commute
    (h : NearSimple p X) {f : MulAut X}
    (hf : orderOf f = p) {m z : X} (hm : m ∈ fixedNormalizer f)
    (hz : z ∈ CFSG.fittingSubgroupOf (fixedNormalizer f)) (hz1 : z ≠ 1) (hmz : m * z = z * m) :
    m ∈ CFSG.fittingSubgroupOf (fixedNormalizer f) := by
  obtain ⟨ℓ, hFr⟩ := frame_of_nearSimple h hf
  have hFZ := (near_fitting_eq_centralizer h hf).1
  have hzZ : z ∈ Subgroup.centralizer (fixedFitting f : Set X) := hFZ ▸ hz
  obtain ⟨z₀, hz₀, c, hc, rfl⟩ := hFr.normalizer_le m hm
  have hZcomm := hFr.centralizer_comm
  have hzz₀ : z₀ * z = z * z₀ := by
    have := mul_comm' (⟨z₀, hz₀⟩ : Subgroup.centralizer (fixedFitting f : Set X)) ⟨z, hzZ⟩
    exact congrArg Subtype.val this
  have hcz : c * z = z * c := by
    have h1 : z₀ * (c * z) = z₀ * (z * c) := by
      calc z₀ * (c * z) = z₀ * c * z := by group
        _ = z * (z₀ * c) := hmz
        _ = z₀ * z * c := by rw [hzz₀]; group
        _ = z₀ * (z * c) := by group
    exact mul_left_cancel h1
  have hcC0 : c ∈ fixedFitting f := by
    by_contra hcn
    exact hz1 (hFr.fpf c hc hcn z hzZ hcz)
  have hcZ : c ∈ Subgroup.centralizer (fixedFitting f : Set X) := by
    have := hFr.C0_comm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 := mul_comm' (⟨y, hy⟩ : fixedFitting f) ⟨c, hcC0⟩
    exact congrArg Subtype.val h2
  rw [hFZ]
  exact mul_mem hz₀ hcZ

theorem NearSimple.mem_fixedFitting_of_forall_commute
    (h : NearSimple p X) {f : MulAut X}
    (hf : orderOf f = p) {c : X} (hc : c ∈ signalizerFixedSubgroup f)
    (hcc : ∀ y ∈ fixedFitting f, c * y = y * c) : c ∈ fixedFitting f := by
  obtain ⟨ℓ, hFr⟩ := frame_of_nearSimple h hf
  by_contra hcn
  have hcZ : c ∈ Subgroup.centralizer (fixedFitting f : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    exact fun y hy => (hcc y hy).symm
  have h1 : c = 1 := hFr.fpf c hc hcn c hcZ rfl
  exact hcn (by rw [h1]; exact one_mem _)

theorem NearSimple.fixedFitting_ne
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    fixedFitting f ≠ signalizerFixedSubgroup f := by
  obtain ⟨ℓ, hFr⟩ := frame_of_nearSimple h hf
  exact hFr.C0_ne

theorem NearSimple.mem_fixedFitting_of_pow_eq_one
    (h : NearSimple p X) {f : MulAut X}
    (hf : orderOf f = p) {ℓ k : ℕ} (hℓ : ℓ.Prime) {y c : X} (hy : y ∈ fixedNormalizer f)
    (hyk : y ^ (ℓ ^ k) = 1) (hc : c ∈ fixedFitting f) (hc1 : c ≠ 1) (hcℓ : c ^ ℓ = 1) :
    y ∈ fixedFitting f := by
  obtain ⟨ℓ', hFr⟩ := frame_of_nearSimple h hf
  have hordc : orderOf c = ℓ := by
    have := Fact.mk hℓ
    exact orderOf_eq_prime hcℓ hc1
  obtain ⟨j, hj⟩ := hFr.C0_pgroup ⟨c, hc⟩
  have hcj : c ^ (ℓ' ^ j) = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hℓℓ' : ℓ = ℓ' := by
    have h1 : ℓ ∣ ℓ' ^ j := hordc ▸ orderOf_dvd_of_pow_eq_one hcj
    exact (Nat.prime_dvd_prime_iff_eq hℓ hFr.prime_ℓ).mp (hℓ.dvd_of_dvd_pow h1)
  subst hℓℓ'
  have hyN : y ∈ Subgroup.normalizer (fixedFitting f : Set X) := hy
  have hyP : IsPGroup ℓ (Subgroup.zpowers y) :=
    IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hyk)
  have hQ : IsPGroup ℓ (Subgroup.zpowers y ⊔ fixedFitting f : Subgroup X) :=
    hyP.to_sup_of_normal_right' hFr.C0_pgroup (Subgroup.zpowers_le.mpr hyN)
  have := hFr.C0_sylow _ hQ le_sup_right
  rw [← this]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)

end Abstract

end CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

section Component

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G J : Subgroup Γ}

theorem SemisimpleAction.mem_fittingSubgroupOf_kJ_of_commute
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) {m z : Γ} (hm : m ∈ kJ A J) (hz : z ∈ CFSG.fittingSubgroupOf (kJ A J))
    (hz1 : z ≠ 1) (hmz : m * z = z * m) : m ∈ CFSG.fittingSubgroupOf (kJ A J) := by
  obtain ⟨f, hf, -, -, hM, hFM⟩ := h.exists_frame_data hJ
  rw [← hM] at hm
  rw [← hFM] at hz ⊢
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  have hz₁ : z₀ ≠ 1 := fun e => hz1 (by rw [e, map_one])
  have hcomm : m₀ * z₀ = z₀ * m₀ := Subtype.ext hmz
  exact ⟨m₀, (h.nearSimple hJ).mem_fitting_of_commute hf hm₀ hz₀ hz₁ hcomm, rfl⟩

theorem SemisimpleAction.mem_fittingSubgroupOf_cenIn_of_forall_commute
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) {c : Γ} (hc : c ∈ cenIn J (norIn A J))
    (hcc : ∀ z ∈ CFSG.fittingSubgroupOf (cenIn J (norIn A J)), c * z = z * c) :
    c ∈ CFSG.fittingSubgroupOf (cenIn J (norIn A J)) := by
  obtain ⟨f, hf, hC, hC₀, -, -⟩ := h.exists_frame_data hJ
  rw [← hC] at hc
  rw [← hC₀] at hcc ⊢
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  refine ⟨c₀, (h.nearSimple hJ).mem_fixedFitting_of_forall_commute hf hc₀ fun y hy => ?_, rfl⟩
  exact Subtype.ext (hcc y ⟨y, hy, rfl⟩)

theorem SemisimpleAction.fittingSubgroupOf_cenIn_ne
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) :
    CFSG.fittingSubgroupOf (cenIn J (norIn A J)) ≠ cenIn J (norIn A J) := by
  obtain ⟨f, hf, hC, hC₀, -, -⟩ := h.exists_frame_data hJ
  rw [← hC₀, ← hC]
  exact fun he => (h.nearSimple hJ).fixedFitting_ne hf
    (Subgroup.map_injective J.subtype_injective he)

theorem SemisimpleAction.mem_fittingSubgroupOf_cenIn_of_pow_eq_one
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) {ℓ k : ℕ} (hℓ : ℓ.Prime) {y c : Γ} (hy : y ∈ kJ A J)
    (hyk : y ^ (ℓ ^ k) = 1) (hc : c ∈ CFSG.fittingSubgroupOf (cenIn J (norIn A J))) (hc1 : c ≠ 1)
    (hcℓ : c ^ ℓ = 1) : y ∈ CFSG.fittingSubgroupOf (cenIn J (norIn A J)) := by
  obtain ⟨f, hf, -, hC₀, hM, -⟩ := h.exists_frame_data hJ
  rw [← hM] at hy
  rw [← hC₀] at hc ⊢
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  have hy₁ : y₀ ^ (ℓ ^ k) = 1 := Subtype.ext (by simpa using hyk)
  have hc₁ : c₀ ≠ 1 := fun e => hc1 (by rw [e, map_one])
  have hc₂ : c₀ ^ ℓ = 1 := Subtype.ext (by simpa using hcℓ)
  exact ⟨y₀, (h.nearSimple hJ).mem_fixedFitting_of_pow_eq_one hf hℓ hy₀ hy₁ hc₀ hc₁ hc₂, rfl⟩

theorem SemisimpleAction.mem_fittingSubgroupOf_smear_of_commute
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) {d : Γ} (hd : d ∈ smear J A)
    (hdc : ∀ v ∈ CFSG.fittingSubgroupOf (smear J A), d * v = v * d) :
    d ∈ CFSG.fittingSubgroupOf (smear J A) := by
  have hG := h.isDirectProduct_lcal
  have hdG : d ∈ G := (Subgroup.mem_inf.mp (h.smear_le_cenIn hJ hd)).1
  have hmem : ((hG.coord hJ ⟨d, hdG⟩ : J) : Γ) ∈ cenIn J (norIn A J) := by
    rw [← h.projIn_smear hJ]
    exact (hG.mem_projIn_iff hJ).mpr ⟨⟨d, hdG⟩, hd, rfl⟩
  have hcF : ((hG.coord hJ ⟨d, hdG⟩ : J) : Γ) ∈
      CFSG.fittingSubgroupOf (cenIn J (norIn A J)) := by
    refine h.mem_fittingSubgroupOf_cenIn_of_forall_commute hJ hmem fun z hz => ?_
    rw [← h.projIn_fittingSubgroupOf_smear hJ] at hz
    obtain ⟨v, hv, rfl⟩ := (hG.mem_projIn_iff hJ).mp hz
    have hvS : (v : Γ) ∈ smear J A := Subgroup.map_subtype_le _ hv
    have hcomm : (⟨d, hdG⟩ : ↥G) * v = v * ⟨d, hdG⟩ := Subtype.ext (hdc _ hv)
    have := congrArg (hG.coord hJ) hcomm
    rw [map_mul, map_mul] at this
    exact congrArg Subtype.val this
  rw [← h.projIn_fittingSubgroupOf_smear hJ] at hcF
  obtain ⟨v, hv, hvc⟩ := (hG.mem_projIn_iff hJ).mp hcF
  have hvS : (v : Γ) ∈ smear J A := Subgroup.map_subtype_le _ hv
  have hdv : d * (v : Γ)⁻¹ ∈ smear J A ⊓ sSup (lcal G \ {J}) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem hd (inv_mem hvS), ?_⟩
    have : hG.coord hJ (⟨d, hdG⟩ * v⁻¹) = 1 := by
      rw [map_mul, map_inv, ← Subtype.ext hvc, mul_inv_cancel]
    exact (hG.coord_eq_one_iff hJ _).mp this
  rw [h.smear_inf_sSup hJ, Subgroup.mem_bot, mul_inv_eq_one] at hdv
  rw [hdv]
  exact hv

theorem SemisimpleAction.fittingSubgroupOf_smear_ne
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) : CFSG.fittingSubgroupOf (smear J A) ≠ smear J A := by
  intro he
  apply h.fittingSubgroupOf_cenIn_ne hJ
  rw [← h.projIn_fittingSubgroupOf_smear hJ, he, h.projIn_smear hJ]

end Component

end CFSG.SignalizerFunctorTheorem.McBride.Near
