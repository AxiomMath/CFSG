module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofSubfield
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofCent

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts (psuConj psuField)

theorem ringEquiv_eq_or_eq_mul_self_of_orderOf_eq_three {K : Type*} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {σ τ : K ≃+* K}
    (hσ : orderOf σ = 3) (hτ : orderOf τ = 3) : τ = σ ∨ τ = σ * σ := by
  obtain ⟨h3, hσ'⟩ := KFacts.eq_frobenius_pow_of_orderOf_eq_three hp hf hK hσ
  obtain ⟨-, hτ'⟩ := KFacts.eq_frobenius_pow_of_orderOf_eq_three hp hf hK hτ
  obtain ⟨m, rfl⟩ := h3
  have hm1 : 3 * m / 3 = m := by omega
  have hm2 : 2 * (3 * m) / 3 = 2 * m := by omega
  rw [hm1, hm2] at hσ' hτ'
  have hcard : ∀ x : K, x ^ p ^ (3 * m) = x := by
    intro x
    have := Fintype.ofFinite K
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hsq : ∀ x : K, (σ * σ) x = σ (σ x) := fun x => rfl
  rcases hσ' with hσ' | hσ' <;> rcases hτ' with hτ' | hτ'
  · left
    ext x
    rw [hτ', hσ']
  · right
    ext x
    rw [hτ', hsq, hσ', hσ', ← pow_mul, ← pow_add, two_mul]
  · right
    ext x
    rw [hτ', hsq, hσ', hσ', ← pow_mul, ← pow_add,
      show 2 * m + 2 * m = 3 * m + m by ring, pow_add, pow_mul, hcard]
  · left
    ext x
    rw [hτ', hσ']

section Twist


theorem normalizerMonoidHom_mul_of_mem {Γ : Type} [Group Γ] {X : Subgroup Γ} {σ z : Γ}
    (hσN : σ ∈ Subgroup.normalizer (X : Set Γ)) (hzX : z ∈ X) :
    X.normalizerMonoidHom ⟨σ * z, mul_mem hσN (Subgroup.le_normalizer hzX)⟩ =
      X.normalizerMonoidHom ⟨σ, hσN⟩ * MulAut.conj (⟨z, hzX⟩ : ↥X) := by
  ext x
  rw [MulAut.mul_apply, MulAut.conj_apply, Sec4.normalizerMonoidHom_apply_coe,
    Sec4.normalizerMonoidHom_apply_coe]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem exists_mulAut_twist_linear {Γ : Type} [Group Γ] [Finite Γ]
    {X K : Subgroup Γ} {σ z : Γ} {n : ℕ} (hn : 1 ≤ n) (hX : Sec4.IsoLThreePi ↥X 2 (3 * n))
    (hq : 2 ^ (3 * n) % 3 = 1) (hind : KFacts.InducesStdKind X σ .field) (hσ3 : σ ^ 3 = 1)
    (hσN : σ ∈ Subgroup.normalizer (X : Set Γ)) (hKX : K ≤ X)
    (hKC : K ≤ Subgroup.centralizer ({σ} : Set Γ)) (hK : Sec4.IsoLThreePi ↥K 2 n)
    (hzX : z ∈ X) (hz3 : z ^ 3 = 1) (hzσ : z * σ = σ * z) :
    ∃ δ : MulAut ↥X, ∀ x : ↥X, (x : Γ) ∈ K →
      (σ * z) * ((δ x : ↥X) : Γ) * (σ * z)⁻¹ = ((δ x : ↥X) : Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hX with ⟨-, ⟨e⟩⟩ | ⟨hq', -⟩
  swap
  · omega
  set F := GaloisField 2 (3 * n) with hFdef
  have hcardF : Nat.card F = 2 ^ (3 * n) := GaloisField.card 2 (3 * n) (by omega)
  obtain ⟨φ⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_projSL_mulEquiv 3 F
  set τ : ↥X ≃* projectiveSL 3 F := e.trans φ with hτ
  set α := X.normalizerMonoidHom ⟨σ, hσN⟩ with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨σ, hσN⟩ : Subgroup.normalizer (X : Set Γ)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hσ3)
    rw [this, map_one]
  have hout := not_isInnerAut_of_inducesStdKind_field148 hind hσN
  have hαk : ∀ k : ↥X, (k : Γ) ∈ K → α k = k := by
    intro k hk
    apply Subtype.ext
    show σ * (k : Γ) * σ⁻¹ = k
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)).symm, mul_inv_cancel_right]
  have h2K : 2 ∣ Nat.card K := Item148Res5.two_dvd_card_of_isoLThreePi hn hK
  obtain ⟨k₀, hk₀⟩ := exists_prime_orderOf_dvd_card' 2 h2K
  set t : ↥X := ⟨k₀, hKX k₀.2⟩ with ht
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have : (k₀ : Γ) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hk₀, pow_orderOf_eq_one, Subgroup.coe_one]
    exact this
  have ht1 : t ≠ 1 := by
    intro h1
    have h2 : ((t : ↥X) : Γ) = 1 := congrArg Subtype.val h1
    have hk1 : k₀ = 1 := Subtype.ext h2
    rw [hk1, orderOf_one] at hk₀
    norm_num at hk₀
  have hαt : α t = t := hαk t k₀.2
  set β := MulAut.congr τ α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : ¬ KFacts.IsInnerAut β := fun hb =>
    hout ((KFacts.isInnerAut_congr τ α).mp hb)
  have hβt : β (τ t) = τ t := by
    change τ (α (τ.symm (τ t))) = τ t
    rw [MulEquiv.symm_apply_apply, hαt]
  have hτt2 : (τ t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hτt1 : τ t ≠ 1 := fun h1 => ht1 (τ.injective (h1.trans (map_one τ).symm))
  have hlin : β ∉ linearAutGroup 3 F := by
    intro hl
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hl
    apply hβout
    rw [← hA]
    have h9 : 9 ∣ Nat.card F - 1 := by
      rw [hcardF]
      exact (Item148Res5.nine_dvd_of_two_pow_three_mul n).1 hq
    exact Sec19.Item19Res2Proof.isInnerAut_of_conjAut_fix_involution h9 (by rw [hA]; exact hβ3)
      hτt2 hτt1 (by rw [hA]; exact hβt)
  have hzN : z ∈ Subgroup.normalizer (X : Set Γ) := Subgroup.le_normalizer hzX
  set α' := X.normalizerMonoidHom ⟨σ * z, mul_mem hσN hzN⟩ with hα'
  have hα'eq : α' = α * MulAut.conj (⟨z, hzX⟩ : ↥X) := normalizerMonoidHom_mul_of_mem hσN hzX
  have hα'3 : α' ^ 3 = 1 := by
    rw [hα', ← map_pow]
    have h3 : (σ * z) ^ 3 = 1 := by
      have hc : Commute σ z := hzσ.symm
      rw [hc.mul_pow, hσ3, hz3, one_mul]
    have : (⟨σ * z, mul_mem hσN hzN⟩ : Subgroup.normalizer (X : Set Γ)) ^ 3 = 1 :=
      Subtype.ext (by simpa using h3)
    rw [this, map_one]
  set β' := MulAut.congr τ α' with hβ'
  have hβ'eq : β' = β * MulAut.conj (τ ⟨z, hzX⟩) := by
    rw [hβ', hα'eq, map_mul, KFacts.congr_mulAutConj]
  have hβ'3 : β' ^ 3 = 1 := by rw [hβ', ← map_pow, hα'3, map_one]
  have hlin' : β' ∉ linearAutGroup 3 F := by
    intro h
    apply hlin
    have hc : MulAut.conj (τ ⟨z, hzX⟩) ∈ linearAutGroup 3 F :=
      KFacts.innAut_le_linearAutGroup 3 F ⟨_, rfl⟩
    have : β = β' * (MulAut.conj (τ ⟨z, hzX⟩))⁻¹ := by rw [hβ'eq]; group
    rw [this]
    exact mul_mem h (inv_mem hc)
  obtain ⟨σ₀, hσ₀, H₀, hβH₀⟩ :=
    CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent le_rfl β hβ3 hlin
  obtain ⟨σ₁, hσ₁, H₁, hβH₁⟩ :=
    CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent le_rfl β' hβ'3 hlin'
  set δ₀ : MulAut (projectiveSL 3 F) := conjAut 3 F H₁ * (conjAut 3 F H₀)⁻¹ with hδ₀
  have hfix : ∀ y, β y = y → β' (δ₀ y) = δ₀ y := by
    intro y hy
    rcases ringEquiv_eq_or_eq_mul_self_of_orderOf_eq_three Nat.prime_two (by omega) hcardF hσ₀
      hσ₁ with h | h
    · have hconj : β' = δ₀ * β * δ₀⁻¹ := by rw [hβH₁, hβH₀, hδ₀, h]; group
      rw [hconj, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hy]
    · have hconj : β' = δ₀ * β * β * δ₀⁻¹ := by
        rw [hβH₁, hβH₀, hδ₀, h, map_mul]; group
      rw [hconj, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hy,
        hy]
  refine ⟨MulAut.congr τ.symm δ₀, fun x hx => ?_⟩
  have hβx : β (τ x) = τ x := by
    change τ (α (τ.symm (τ x))) = τ x
    rw [MulEquiv.symm_apply_apply, hαk x hx]
  have h1 : β' (δ₀ (τ x)) = δ₀ (τ x) := hfix _ hβx
  have hδx : MulAut.congr τ.symm δ₀ x = τ.symm (δ₀ (τ x)) := rfl
  have h2 : α' (MulAut.congr τ.symm δ₀ x) = MulAut.congr τ.symm δ₀ x := by
    have h3 : β' (τ (MulAut.congr τ.symm δ₀ x)) = τ (α' (MulAut.congr τ.symm δ₀ x)) := by
      change τ (α' (τ.symm (τ _))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [hδx, MulEquiv.apply_symm_apply] at h3
    rw [hδx]
    apply τ.injective
    rw [MulEquiv.apply_symm_apply]
    exact h3.symm.trans h1
  have h4 := congrArg Subtype.val h2
  rw [hα', Sec4.normalizerMonoidHom_apply_coe] at h4
  exact h4

theorem exists_mulAut_twist_unitary {Γ : Type} [Group Γ] [Finite Γ]
    {X K : Subgroup Γ} {σ z : Γ} {n : ℕ} (hn : 1 ≤ n) (hX : Sec4.IsoLThreePi ↥X 2 (3 * n))
    (hq : 2 ^ (3 * n) % 3 = 2) (hind : KFacts.InducesStdKind X σ .field) (hσ3 : σ ^ 3 = 1)
    (hσN : σ ∈ Subgroup.normalizer (X : Set Γ)) (hKX : K ≤ X)
    (hKC : K ≤ Subgroup.centralizer ({σ} : Set Γ)) (hK : Sec4.IsoLThreePi ↥K 2 n)
    (hzX : z ∈ X) (hz3 : z ^ 3 = 1) (hzσ : z * σ = σ * z) :
    ∃ δ : MulAut ↥X, ∀ x : ↥X, (x : Γ) ∈ K →
      (σ * z) * ((δ x : ↥X) : Γ) * (σ * z)⁻¹ = ((δ x : ↥X) : Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hX with ⟨hq', -⟩ | ⟨-, ⟨e⟩⟩
  · omega
  set F := GaloisField 2 (2 * (3 * n)) with hFdef
  have hcardF : Nat.card F = 2 ^ (2 * (3 * n)) := GaloisField.card 2 _ (by omega)
  have hU : UnitaryFieldData 2 (3 * n) F := ⟨Nat.prime_two, by omega, hcardF⟩
  obtain ⟨φ⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_unitaryPSU_mulEquiv_projSU hU
  set τ : ↥X ≃* unitaryPSU hU 3 := e.trans φ.symm with hτ
  set α := X.normalizerMonoidHom ⟨σ, hσN⟩ with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨σ, hσN⟩ : Subgroup.normalizer (X : Set Γ)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hσ3)
    rw [this, map_one]
  have hout := not_isInnerAut_of_inducesStdKind_field148 hind hσN
  have hαk : ∀ k : ↥X, (k : Γ) ∈ K → α k = k := by
    intro k hk
    apply Subtype.ext
    show σ * (k : Γ) * σ⁻¹ = k
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)).symm, mul_inv_cancel_right]
  have h2K : 2 ∣ Nat.card K := Item148Res5.two_dvd_card_of_isoLThreePi hn hK
  obtain ⟨k₀, hk₀⟩ := exists_prime_orderOf_dvd_card' 2 h2K
  set t : ↥X := ⟨k₀, hKX k₀.2⟩ with ht
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have : (k₀ : Γ) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hk₀, pow_orderOf_eq_one, Subgroup.coe_one]
    exact this
  have ht1 : t ≠ 1 := by
    intro h1
    have h2 : ((t : ↥X) : Γ) = 1 := congrArg Subtype.val h1
    have hk1 : k₀ = 1 := Subtype.ext h2
    rw [hk1, orderOf_one] at hk₀
    norm_num at hk₀
  have hαt : α t = t := hαk t k₀.2
  set β := MulAut.congr τ α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : ¬ KFacts.IsInnerAut β := fun hb =>
    hout ((KFacts.isInnerAut_congr τ α).mp hb)
  have hβt : β (τ t) = τ t := by
    change τ (α (τ.symm (τ t))) = τ t
    rw [MulEquiv.symm_apply_apply, hαt]
  have hτt2 : (τ t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hτt1 : τ t ≠ 1 := fun h1 => ht1 (τ.injective (h1.trans (map_one τ).symm))
  have hD : β ∉ (psuConj hU).range := by
    rintro ⟨A, hA⟩
    apply hβout
    rw [← hA]
    exact Item148Res5.isInnerAut_of_psuConj_fix_involution hU
      ((Item148Res5.nine_dvd_of_two_pow_three_mul n).2 hq) (by rw [hA]; exact hβ3) hτt2 hτt1
      (by rw [hA]; exact hβt)
  have hq2 : 2 < 2 ^ (3 * n) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
  have hzN : z ∈ Subgroup.normalizer (X : Set Γ) := Subgroup.le_normalizer hzX
  set α' := X.normalizerMonoidHom ⟨σ * z, mul_mem hσN hzN⟩ with hα'
  have hα'eq : α' = α * MulAut.conj (⟨z, hzX⟩ : ↥X) := normalizerMonoidHom_mul_of_mem hσN hzX
  have hα'3 : α' ^ 3 = 1 := by
    rw [hα', ← map_pow]
    have h3 : (σ * z) ^ 3 = 1 := by
      have hc : Commute σ z := hzσ.symm
      rw [hc.mul_pow, hσ3, hz3, one_mul]
    have : (⟨σ * z, mul_mem hσN hzN⟩ : Subgroup.normalizer (X : Set Γ)) ^ 3 = 1 :=
      Subtype.ext (by simpa using h3)
    rw [this, map_one]
  set β' := MulAut.congr τ α' with hβ'
  have hβ'eq : β' = β * MulAut.conj (τ ⟨z, hzX⟩) := by
    rw [hβ', hα'eq, map_mul, KFacts.congr_mulAutConj]
  have hβ'3 : β' ^ 3 = 1 := by rw [hβ', ← map_pow, hα'3, map_one]
  have hD' : β' ∉ (psuConj hU).range := by
    intro h
    apply hD
    have hc : MulAut.conj (τ ⟨z, hzX⟩) ∈ (psuConj hU).range :=
      (CFSG.RankThree.PartTwo.KFacts.stdPinnedPSU3 hU).inn_le ⟨_, rfl⟩
    have : β = β' * (MulAut.conj (τ ⟨z, hzX⟩))⁻¹ := by rw [hβ'eq]; group
    rw [this]
    exact mul_mem h (inv_mem hc)
  obtain ⟨σ₀, hσ₀, H₀, hβH₀⟩ :=
    CFSG.RankThree.PartTwo.KFacts.unitary_order_three_field_descent hq2 β hβ3 hD
  obtain ⟨σ₁, hσ₁, H₁, hβH₁⟩ :=
    CFSG.RankThree.PartTwo.KFacts.unitary_order_three_field_descent hq2 β' hβ'3 hD'
  set δ₀ : MulAut (unitaryPSU hU 3) := psuConj hU H₁ * (psuConj hU H₀)⁻¹ with hδ₀
  have hfix : ∀ y, β y = y → β' (δ₀ y) = δ₀ y := by
    intro y hy
    rcases ringEquiv_eq_or_eq_mul_self_of_orderOf_eq_three Nat.prime_two (by omega) hcardF hσ₀
      hσ₁ with h | h
    · have hconj : β' = δ₀ * β * δ₀⁻¹ := by rw [hβH₁, hβH₀, hδ₀, h]; group
      rw [hconj, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hy]
    · have hconj : β' = δ₀ * β * β * δ₀⁻¹ := by
        rw [hβH₁, hβH₀, hδ₀, h, map_mul]; group
      rw [hconj, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hy,
        hy]
  refine ⟨MulAut.congr τ.symm δ₀, fun x hx => ?_⟩
  have hβx : β (τ x) = τ x := by
    change τ (α (τ.symm (τ x))) = τ x
    rw [MulEquiv.symm_apply_apply, hαk x hx]
  have h1 : β' (δ₀ (τ x)) = δ₀ (τ x) := hfix _ hβx
  have hδx : MulAut.congr τ.symm δ₀ x = τ.symm (δ₀ (τ x)) := rfl
  have h2 : α' (MulAut.congr τ.symm δ₀ x) = MulAut.congr τ.symm δ₀ x := by
    have h3 : β' (τ (MulAut.congr τ.symm δ₀ x)) = τ (α' (MulAut.congr τ.symm δ₀ x)) := by
      change τ (α' (τ.symm (τ _))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [hδx, MulEquiv.apply_symm_apply] at h3
    rw [hδx]
    apply τ.injective
    rw [MulEquiv.apply_symm_apply]
    exact h3.symm.trans h1
  have h4 := congrArg Subtype.val h2
  rw [hα', Sec4.normalizerMonoidHom_apply_coe] at h4
  exact h4

theorem eq_bot_of_field_twist {Γ : Type} [Group Γ] [Finite Γ]
    {X K N : Subgroup Γ} {σ z : Γ} {n : ℕ} (hn : 1 ≤ n) (hX : Sec4.IsoLThreePi ↥X 2 (3 * n))
    (hXs : IsSimpleGroup ↥X) (hind : KFacts.InducesStdKind X σ .field) (hσ3 : σ ^ 3 = 1)
    (hσN : σ ∈ Subgroup.normalizer (X : Set Γ)) (hKX : K ≤ X)
    (hKC : K ≤ Subgroup.centralizer ({σ} : Set Γ)) (hKs : IsSimpleGroup ↥K)
    (hK : Sec4.IsoLThreePi ↥K 2 n) (hzX : z ∈ X) (hz3 : z ^ 3 = 1) (hzσ : z * σ = σ * z)
    (hNX : N ≤ X) (hN3 : ¬ 3 ∣ Nat.card N)
    (hNn : X ⊓ Subgroup.centralizer ({σ * z} : Set Γ) ≤ Subgroup.normalizer (N : Set Γ)) :
    N = ⊥ := by
  have h0 : 2 ^ (3 * n) % 3 ≠ 0 := by
    intro h0
    have h3 : 3 ∣ 2 ^ (3 * n) := Nat.dvd_of_mod_eq_zero h0
    have := Nat.prime_three.dvd_of_dvd_pow h3
    norm_num at this
  obtain ⟨δ, hδ⟩ : ∃ δ : MulAut ↥X, ∀ x : ↥X, (x : Γ) ∈ K →
      (σ * z) * ((δ x : ↥X) : Γ) * (σ * z)⁻¹ = ((δ x : ↥X) : Γ) := by
    rcases (by omega : 2 ^ (3 * n) % 3 = 1 ∨ 2 ^ (3 * n) % 3 = 2) with hq | hq
    · exact exists_mulAut_twist_linear hn hX hq hind hσ3 hσN hKX hKC hK hzX hz3 hzσ
    · exact exists_mulAut_twist_unitary hn hX hq hind hσ3 hσN hKX hKC hK hzX hz3 hzσ
  set N₀ : Subgroup Γ := ((N.subgroupOf X).map (δ⁻¹ : MulAut ↥X).toMonoidHom).map X.subtype
    with hN₀
  have hN₀X : N₀ ≤ X := Subgroup.map_subtype_le _
  have hmemN₀ : ∀ y : ↥X, (y : Γ) ∈ N₀ ↔ ((δ y : ↥X) : Γ) ∈ N := by
    intro y
    constructor
    · rintro ⟨w, ⟨v, hv, hvw⟩, hwy⟩
      have hwy' : w = y := Subtype.ext hwy
      subst hwy'
      have : δ w = v := by
        rw [← hvw]
        simp
      rw [this]
      exact Subgroup.mem_subgroupOf.mp hv
    · intro hy
      refine ⟨y, ⟨δ y, Subgroup.mem_subgroupOf.mpr hy, ?_⟩, rfl⟩
      simp
  have hcardN₀ : Nat.card N₀ = Nat.card N := by
    rw [hN₀, Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.card_map_of_injective (δ⁻¹ : MulAut ↥X).injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
  have hN₀3 : ¬ 3 ∣ Nat.card N₀ := hcardN₀ ▸ hN3
  have hKN₀ : K ≤ Subgroup.normalizer (N₀ : Set Γ) := by
    intro k hk
    set k' : ↥X := ⟨k, hKX hk⟩ with hk'
    have hdk : ((δ k' : ↥X) : Γ) ∈ Subgroup.normalizer (N : Set Γ) := by
      refine hNn (Subgroup.mem_inf.mpr ⟨(δ k').2, ?_⟩)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hδ k' hk
      calc ((δ k' : ↥X) : Γ) * (σ * z)
          = (σ * z) * ((δ k' : ↥X) : Γ) * (σ * z)⁻¹ * (σ * z) := by rw [h]
        _ = (σ * z) * ((δ k' : ↥X) : Γ) := by group
    rw [Subgroup.mem_normalizer_iff]
    intro g
    by_cases hg : g ∈ X
    · have hkg : k * g * k⁻¹ ∈ X := X.mul_mem (X.mul_mem (hKX hk) hg) (X.inv_mem (hKX hk))
      have e1 := hmemN₀ ⟨g, hg⟩
      have e2 := hmemN₀ ⟨k * g * k⁻¹, hkg⟩
      have e3 : (⟨k * g * k⁻¹, hkg⟩ : ↥X) = k' * ⟨g, hg⟩ * k'⁻¹ := rfl
      rw [e3, map_mul, map_mul, map_inv] at e2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e2
      change ((⟨g, hg⟩ : ↥X) : Γ) ∈ N₀ ↔ ((⟨k * g * k⁻¹, hkg⟩ : ↥X) : Γ) ∈ N₀
      rw [e1, e2]
      exact Subgroup.mem_normalizer_iff.mp hdk _
    · constructor
      · intro h
        exact absurd (hN₀X h) hg
      · intro h
        exfalso
        apply hg
        have h1 := hN₀X h
        have h2 : g = k⁻¹ * (k * g * k⁻¹) * k := by group
        rw [h2]
        exact X.mul_mem (X.mul_mem (X.inv_mem (hKX hk)) h1) (hKX hk)
  have h3K : 3 ∣ Nat.card K := Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi hn hK
  have hKH : K ≤ N₀ ⊔ K := le_sup_right
  have hHX : N₀ ⊔ K ≤ X := sup_le hN₀X hKX
  have hNK : N₀ ⊔ K ≠ X := by
    intro hHeq
    have hXN : X ≤ Subgroup.normalizer (N₀ : Set Γ) :=
      hHeq ▸ sup_le Subgroup.le_normalizer hKN₀
    have hnorm : (N₀.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀X).mpr hXN
    haveI := hXs
    rcases hnorm.eq_bot_or_eq_top with hb | ht
    · have hN₀b : N₀ = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have h1 : (⟨x, hN₀X hx⟩ : ↥X) ∈ N₀.subgroupOf X := Subgroup.mem_subgroupOf.mpr hx
        rw [hb] at h1
        exact (Subgroup.mem_bot).mpr (congrArg Subtype.val ((Subgroup.mem_bot).mp h1))
      rw [hN₀b, bot_sup_eq] at hHeq
      apply not_isInnerAut_of_inducesStdKind_field148 hind hσN
      refine ⟨1, ?_⟩
      ext x
      rw [map_one, MulAut.one_apply, Sec4.normalizerMonoidHom_apply_coe]
      have hxK : (x : Γ) ∈ K := hHeq ▸ x.2
      rw [(Subgroup.mem_centralizer_singleton_iff.mp (hKC hxK)).symm, mul_inv_cancel_right]
    · apply hN₀3
      have hXN₀ : X ≤ N₀ := fun x hx => by
        have h1 : (⟨x, hx⟩ : ↥X) ∈ N₀.subgroupOf X := ht ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp h1
      exact (Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi (by omega) hX).trans
        (Subgroup.card_dvd_of_le hXN₀)
  rcases Item148Res8.kf148SubfieldOver_holds Γ X K (N₀ ⊔ K) σ n hn hX hind hσ3 hσN hKX hKC hKs
      hK hKH hHX with hHeq | ⟨hHN, hHd⟩
  · exact absurd hHeq hNK
  have hN₀K : N₀ ≤ K := by
    intro x hx
    have hx3 : ¬ 3 ∣ orderOf x := by
      intro h3
      apply hN₀3
      have h1 : orderOf (⟨x, hx⟩ : ↥N₀) ∣ Nat.card N₀ := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact h3.trans h1
    exact Item148Res6.mem_of_dvd_three_mul_card hKH hHN hHd (le_sup_left (a := N₀) hx) hx3
  have hnormK : (N₀.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀K).mpr hKN₀
  haveI := hKs
  rcases hnormK.eq_bot_or_eq_top with hb | ht
  · have hN₀b : N₀ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hN₀K hx⟩ : ↥K) ∈ N₀.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
      rw [hb] at h1
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val ((Subgroup.mem_bot).mp h1))
    have h1 : Nat.card N = 1 := by rw [← hcardN₀, hN₀b, Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq N h1
  · exfalso
    apply hN₀3
    have hKN : K ≤ N₀ := fun x hx => by
      have h1 : (⟨x, hx⟩ : ↥K) ∈ N₀.subgroupOf K := ht ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h1
    exact h3K.trans (Subgroup.card_dvd_of_le hKN)

end Twist

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
