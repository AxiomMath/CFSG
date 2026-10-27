module

public import CFSG.RankThree.PartTwo.KFacts.AutSz

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)
open Pointwise

section Coset

variable {X : Type*} [Group X] [Finite X]

theorem not_three_dvd_relIndex_sup {I : Subgroup X} [I.Normal] (hI : ¬ 3 ∣ Nat.card I) {φ : X}
    (hφ : orderOf φ = 3) {H : Subgroup X} (hH : H ≤ I ⊔ Subgroup.zpowers φ)
    (hH3 : Nat.card H = 3) : ¬ 3 ∣ H.relIndex (I ⊔ Subgroup.zpowers φ) := by
  have h1 := Subgroup.relIndex_mul_index hH
  have h2 := Subgroup.relIndex_mul_index (le_sup_left : I ≤ I ⊔ Subgroup.zpowers φ)
  have h3 := Subgroup.card_mul_index H
  have h4 := Subgroup.card_mul_index I
  have h0 : (I ⊔ Subgroup.zpowers φ).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hd : I.relIndex (I ⊔ Subgroup.zpowers φ) ∣ 3 := by
    have h := Subgroup.relIndex_dvd_card I (Subgroup.zpowers φ)
    rwa [Nat.card_zpowers, hφ, ← Subgroup.relIndex_sup_left] at h
  have key : 3 * H.relIndex (I ⊔ Subgroup.zpowers φ) =
      Nat.card I * I.relIndex (I ⊔ Subgroup.zpowers φ) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h0)
    rw [mul_assoc, h1, ← hH3, h3, mul_assoc, h2, h4]
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hd1 | hd3
  · rw [hd1] at key
    omega
  · rw [hd3] at key
    omega

theorem exists_mem_eq_mul_mul_inv_of_not_dvd {I : Subgroup X} [hIn : I.Normal]
    (hI : ¬ 3 ∣ Nat.card I) {φ α : X} (hφ : orderOf φ = 3) (hα : α ^ 3 = 1)
    (hαφ : α * φ⁻¹ ∈ I) : ∃ i ∈ I, α = i * φ * i⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime (Nat.card I) (Nat.card (Subgroup.zpowers φ)) := by
    rw [Nat.card_zpowers, hφ, Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hI
  have hdisj := Subgroup.disjoint_of_coprime_natCard hcop
  have hα1 : α ≠ 1 := by
    rintro rfl
    have hφI : φ ∈ I := by simpa using inv_mem hαφ
    have h1 : φ = 1 := Subgroup.disjoint_def.mp hdisj hφI (Subgroup.mem_zpowers φ)
    rw [h1, orderOf_one] at hφ
    omega
  have hαo : orderOf α = 3 := orderOf_eq_prime hα hα1
  set Y := I ⊔ Subgroup.zpowers φ with hY
  have hφY : φ ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers φ)
  have hαY : α ∈ Y := by
    have h1 : α = (α * φ⁻¹) * φ := by group
    rw [h1]
    exact mul_mem (Subgroup.mem_sup_left hαφ) hφY
  have hPY : Subgroup.zpowers φ ≤ Y := le_sup_right
  have hQY : Subgroup.zpowers α ≤ Y := (Subgroup.zpowers_le).mpr hαY
  have hP3 : Nat.card (Subgroup.zpowers φ) = 3 := by rw [Nat.card_zpowers, hφ]
  have hQ3 : Nat.card (Subgroup.zpowers α) = 3 := by rw [Nat.card_zpowers, hαo]
  have hPp : IsPGroup 3 ((Subgroup.zpowers φ).subgroupOf Y) :=
    (IsPGroup.of_card (n := 1) (by rw [hP3, pow_one])).comap_of_injective Y.subtype
      Y.subtype_injective
  have hQp : IsPGroup 3 ((Subgroup.zpowers α).subgroupOf Y) :=
    (IsPGroup.of_card (n := 1) (by rw [hQ3, pow_one])).comap_of_injective Y.subtype
      Y.subtype_injective
  let SP : Sylow 3 Y := hPp.toSylow (not_three_dvd_relIndex_sup hI hφ hPY hP3)
  let SQ : Sylow 3 Y := hQp.toSylow (not_three_dvd_relIndex_sup hI hφ hQY hQ3)
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y SP SQ
  have hyS := congrArg (fun S : Sylow 3 Y => (S : Subgroup Y)) hy
  simp only [Sylow.coe_subgroup_smul] at hyS
  have hαmem : (⟨α, hαY⟩ : Y) ∈ (SQ : Subgroup Y) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers α)
  rw [← hyS, Subgroup.mem_smul_pointwise_iff_exists] at hαmem
  obtain ⟨z, hz, hzα⟩ := hαmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hz)
  have hαy : α = (y : X) * φ ^ m * (y : X)⁻¹ := by
    have h1 := congrArg Subtype.val hzα
    rw [MulAut.smul_def, MulAut.conj_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [← h1, hm]
  have hyY : (y : X) ∈ ((I ⊔ Subgroup.zpowers φ : Subgroup X) : Set X) := y.2
  rw [Subgroup.normal_mul, Set.mem_mul] at hyY
  obtain ⟨i, hi, w, hw, hiw⟩ := hyY
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hαi : α = i * φ ^ m * i⁻¹ := by
    rw [hαy, ← hiw]
    group
  have h1 : i⁻¹ * (α * φ⁻¹) ∈ I := mul_mem (inv_mem hi) hαφ
  have h2 : φ ^ m * i⁻¹ * (φ ^ m)⁻¹ ∈ I := hIn.conj_mem _ (inv_mem hi) _
  have h3 : φ ^ m * φ⁻¹ = (φ ^ m * i⁻¹ * (φ ^ m)⁻¹)⁻¹ * (i⁻¹ * (α * φ⁻¹)) := by
    rw [hαi]
    group
  have h4 : φ ^ m * φ⁻¹ ∈ I := h3 ▸ mul_mem (inv_mem h2) h1
  have h5 : φ ^ m * φ⁻¹ ∈ Subgroup.zpowers φ :=
    mul_mem (zpow_mem (Subgroup.mem_zpowers φ) m) (inv_mem (Subgroup.mem_zpowers φ))
  have h6 : φ ^ m = φ := mul_inv_eq_one.mp (Subgroup.disjoint_def.mp hdisj h4 h5)
  exact ⟨i, hi, by rw [hαi, h6]⟩

end Coset

variable {a : ℕ} {K : Type} [Field K]

theorem not_three_dvd_card_suzukiGroup [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ 3 ∣ Nat.card (suzukiGroup a K) := by
  rw [CFSG.LieType.Ree.suzuki_order hK]
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  generalize q ^ 2 = q2 at hq2 ⊢
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h <;> omega
  · omega

theorem isField_sz_of_pow_three_eq_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {α : MulAut (suzukiGroup a K)} (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    (stdPinnedSz a K).IsField α := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, hinf, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  obtain ⟨g, σ, rfl⟩ := exists_conj_mul_szFieldAut ha hK α
  set I := (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)).range with hI
  have hIn : I.Normal := ⟨fun d hd β => by
    obtain ⟨y, rfl⟩ := hd
    exact ⟨β y, (mul_mulAutConj_mul_inv β y).symm⟩⟩
  have hgI : MulAut.conj g ∈ I := ⟨g, rfl⟩
  have hφI : szFieldAut a K σ ∉ I := fun h => hout (mul_mem hgI h)
  have hφ3I : szFieldAut a K σ ^ 3 ∈ I := by
    have hmk : ((MulAut.conj g * szFieldAut a K σ : MulAut (suzukiGroup a K)) :
        MulAut (suzukiGroup a K) ⧸ I) = (szFieldAut a K σ : MulAut (suzukiGroup a K) ⧸ I) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hgI, one_mul]
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hmk, ← QuotientGroup.mk_pow, hα,
      QuotientGroup.mk_one]
  have hφ3 : szFieldAut a K σ ^ 3 = 1 := by
    have h : szFieldAut a K σ ^ 3 ∈ (szFieldAut a K).range ⊓
        CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) :=
      ⟨⟨σ ^ 3, map_pow _ _ _⟩, hφ3I⟩
    rw [hinf] at h
    exact h
  have hφo : orderOf (szFieldAut a K σ) = 3 :=
    orderOf_eq_prime hφ3 fun h => hφI (h ▸ one_mem _)
  have hI3 : ¬ 3 ∣ Nat.card I := fun h =>
    not_three_dvd_card_suzukiGroup hK (h.trans (Subgroup.card_range_dvd _))
  obtain ⟨i, hi, heq⟩ := exists_mem_eq_mul_mul_inv_of_not_dvd hI3 hφo hα
    (by rw [mul_inv_cancel_right]; exact hgI)
  exact ⟨_, ⟨σ, rfl⟩, fun h => hφI (h ▸ one_mem _), i, hi, heq⟩

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

theorem inducesKindSz_field (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : G}
    (hx3 : x ^ 3 = 1) (hout : InducesOuterTheta x L)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* suzukiGroup a K) : InducesKindSz a K L x .field := by
  obtain ⟨hx, -⟩ := id hout
  exact ⟨e, hx, isField_sz_of_pow_three_eq_one ha hK (inducedAutHom_pow_eq_one L e hx hx3)
    ((not_isInnerAut_inducedAutHom_iff L e hx).mpr hout)⟩

end Induced

end CFSG.RankThree.PartTwo.KFacts
