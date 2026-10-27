module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGNsq2QuotHyp
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

@[expose] def GGU62OuterDiagInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = (2 ^ 1) ^ 2 →
  ∀ (X Y : Type) [Group X] [Finite X] [Group Y] [Finite Y] (π : X →* Y) (ψ₀ : Su K 2 1 6 →* Y)
    (σ : MulAut X) (τ : MulAut Y) (g : GL (Fin 6) K),
    Group.IsPerfect X → Function.Surjective π → (∀ x ∈ π.ker, ∀ x' : X, x' * x = x * x') →
    (∀ x ∈ π.ker, ∃ k : ℕ, x ^ (2 ^ k) = 1) → Function.Surjective ψ₀ →
    ψ₀.ker ≤ Subgroup.center (Su K 2 1 6) → (∀ x, π (σ x) = τ (π x)) →
    ggIsUnitaryMat (p := 2) (f := 1) g → Matrix.GeneralLinearGroup.det g ≠ 1 →
    (∀ s : Su K 2 1 6, ∃ y : Su K 2 1 6,
      (y : GL (Fin 6) K) = g * (s : GL (Fin 6) K) * g⁻¹ ∧ τ (ψ₀ s) = ψ₀ y) →
    ∀ x ∈ π.ker, σ x = x → x = 1

section TwoCentral

variable {G : Type} [Group G]

@[expose] def twoCentral (L : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ L ∧ (∀ l ∈ L, l * z = z * l) ∧ ∃ k : ℕ, z ^ (2 ^ k) = 1}
  mul_mem' := by
    rintro a b ⟨haL, hac, ka, hka⟩ ⟨hbL, hbc, kb, hkb⟩
    refine ⟨L.mul_mem haL hbL, fun l hl => ?_, ka + kb, ?_⟩
    · calc l * (a * b) = (l * a) * b := by rw [mul_assoc]
        _ = (a * l) * b := by rw [hac l hl]
        _ = a * (l * b) := by rw [mul_assoc]
        _ = a * (b * l) := by rw [hbc l hl]
        _ = (a * b) * l := by rw [mul_assoc]
    · have hcomm : Commute a b := hbc a haL
      have ha : a ^ (2 ^ (ka + kb)) = 1 := by
        rw [pow_add, pow_mul, hka, one_pow]
      have hb : b ^ (2 ^ (ka + kb)) = 1 := by
        rw [add_comm, pow_add, pow_mul, hkb, one_pow]
      rw [hcomm.mul_pow, ha, hb, one_mul]
  one_mem' := ⟨L.one_mem, fun l _ => by rw [mul_one, one_mul], 0, by simp⟩
  inv_mem' := by
    rintro a ⟨haL, hac, k, hk⟩
    refine ⟨L.inv_mem haL, fun l hl => ?_, k, ?_⟩
    · have h1 := hac l hl
      calc l * a⁻¹ = a⁻¹ * (a * l) * a⁻¹ := by group
        _ = a⁻¹ * (l * a) * a⁻¹ := by rw [← h1]
        _ = a⁻¹ * l := by group
    · rw [inv_pow, hk, inv_one]

theorem twoCentral_le (L : Subgroup G) : twoCentral L ≤ L := fun _ hz => hz.1

theorem twoCentral_central {L : Subgroup G} {z : G} (hz : z ∈ twoCentral L) :
    ∀ l ∈ L, l * z = z * l := hz.2.1

theorem twoCentral_two {L : Subgroup G} {z : G} (hz : z ∈ twoCentral L) :
    ∃ k : ℕ, z ^ (2 ^ k) = 1 := hz.2.2

theorem mem_twoCentral_of_center {L : Subgroup G} {l : ↥L} (hc : l ∈ Subgroup.center ↥L)
    (hk : ∃ k : ℕ, l ^ (2 ^ k) = 1) : (l : G) ∈ twoCentral L := by
  obtain ⟨k, hk⟩ := hk
  refine ⟨l.2, fun l' hl' => ?_, k, ?_⟩
  · have := Subgroup.mem_center_iff.1 hc ⟨l', hl'⟩
    exact congrArg Subtype.val this
  · have := congrArg Subtype.val hk
    simpa using this

theorem conj_mem_twoCentral {L : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (L : Set G))
    {z : G} (hz : z ∈ twoCentral L) : n * z * n⁻¹ ∈ twoCentral L := by
  obtain ⟨hzL, hzc, k, hk⟩ := hz
  refine ⟨(Subgroup.mem_normalizer_iff.1 hn z).1 hzL, fun l hl => ?_, k, ?_⟩
  · have hl' : n⁻¹ * l * n ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) l).1 hl
      simpa using this
    have h1 := hzc _ hl'
    calc l * (n * z * n⁻¹) = n * ((n⁻¹ * l * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * l * n)) * n⁻¹ := by rw [h1]
      _ = (n * z * n⁻¹) * l := by group
  · rw [conj_pow, hk]
    simp

end TwoCentral

section Quotient

variable {G : Type} [Group G] [Finite G]

theorem exists_quotient_datum {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs L : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hBsp : ∀ b ∈ Bs, b ^ p = 1) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (f : ↥(Subgroup.normalizer (L : Set G)) →* Q),
      NsQuot.Datum p (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L) := by
  set N := Subgroup.normalizer (L : Set G) with hN
  haveI hnorm : ((twoCentral L).subgroupOf N).Normal :=
    ⟨fun a ha n => conj_mem_twoCentral n.2 ha⟩
  exact ⟨↥N ⧸ (twoCentral L).subgroupOf N, inferInstance, inferInstance, QuotientGroup.mk' _,
    { prime := hp
      odd := hp2
      surj := QuotientGroup.mk'_surjective _
      ker_eq := QuotientGroup.ker_mk' _
      ZL := twoCentral_le L
      LN := Subgroup.le_normalizer
      BsN := hBsN
      Zcent := fun z hz l hl => twoCentral_central hz l hl
      Z2 := fun z hz => twoCentral_two hz
      Bsp := hBsp }⟩

end Quotient

end CFSG.StandardType

end
