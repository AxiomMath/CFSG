module

public import CFSG.RankThree.PartTwo.Sec11.WreathSupplement

public section

namespace CFSG.RankThree.PartTwo.Sec11

open scoped commutatorElement

theorem commute_wreathZ :
    ∀ (f : Multiplicative (ZMod 3) → Multiplicative (ZMod 3)) (q : Multiplicative (ZMod 3)),
      ((⟨f, q⟩ : W33) * wreathZ).left = (wreathZ * ⟨f, q⟩).left ∧
        ((⟨f, q⟩ : W33) * wreathZ).right = (wreathZ * ⟨f, q⟩).right := by
  decide

theorem wreathZ_mem_center : wreathZ ∈ Subgroup.center W33 := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨h1, h2⟩ := commute_wreathZ y.left y.right
  exact RegularWreathProduct.ext h1 h2

theorem wreathZ_left_ne : wreathZ.left ≠ (1 : W33).left := by
  decide

theorem wreathZ_ne_one : wreathZ ≠ 1 := fun h => wreathZ_left_ne (congrArg _ h)

theorem center_eq_zpowers_wreathZ : Subgroup.center W33 = Subgroup.zpowers wreathZ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Subgroup.zpowers wreathZ ≤ Subgroup.center W33 :=
    Subgroup.zpowers_le.mpr wreathZ_mem_center
  have hZ3 : wreathZ ^ 3 = 1 := pow_three_eq_one_of_right_eq_one wreathZ_right
  have hord : orderOf wreathZ = 3 := orderOf_eq_prime hZ3 wreathZ_ne_one
  have hcard : Nat.card (Subgroup.zpowers wreathZ) = 3 := by
    rw [Nat.card_zpowers, hord]
  symm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact card_center_wreath_le)

theorem not_commute_commutator :
    ∀ (f : Multiplicative (ZMod 3) → Multiplicative (ZMod 3)) (q : Multiplicative (ZMod 3)),
      q ≠ 1 →
        (⁅(⟨fun x => if x = 1 then wreathT else 1, 1⟩ : W33), (⟨f, q⟩ : W33)⁆ *
            (⟨f, q⟩ : W33)).left ≠
          ((⟨f, q⟩ : W33) *
            ⁅(⟨fun x => if x = 1 then wreathT else 1, 1⟩ : W33), (⟨f, q⟩ : W33)⁆).left := by
  decide

theorem right_eq_one_of_abelian_normal {N : Subgroup W33} (hN : N.Normal)
    (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) : ∀ y ∈ N, y.right = 1 := by
  intro y hy
  by_contra hq
  set w : W33 := ⟨fun x => if x = 1 then wreathT else 1, 1⟩
  have hk : ⁅w, y⁆ ∈ N := by
    rw [commutatorElement_def]
    exact N.mul_mem (hN.conj_mem y hy w) (N.inv_mem hy)
  have h := hab _ hk y hy
  exact not_commute_commutator y.left y.right hq (congrArg RegularWreathProduct.left h)

theorem pow_three_eq_one_of_abelian_normal {N : Subgroup W33} (hN : N.Normal)
    (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) : ∀ y ∈ N, y ^ 3 = 1 := fun y hy =>
  pow_three_eq_one_of_right_eq_one (right_eq_one_of_abelian_normal hN hab y hy)

theorem inv_eq_wreathT_of_ne :
    ∀ q : Multiplicative (ZMod 3), q ≠ 1 → q ≠ wreathT → q⁻¹ = wreathT := by
  decide

theorem card_le_nine_of_abelian_of_not_le_base {S : Subgroup W33}
    (hab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {y : W33} (hy : y ∈ S) (hyq : y.right ≠ 1) :
    Nat.card S ≤ 9 := by
  obtain ⟨y₁, hy₁, hy₁t⟩ : ∃ y₁ ∈ S, y₁.right = wreathT := by
    by_cases ht : y.right = wreathT
    · exact ⟨y, hy, ht⟩
    · exact ⟨y⁻¹, S.inv_mem hy, inv_eq_wreathT_of_ne _ hyq ht⟩
  have hSB : ∀ s ∈ S, s.right = 1 → s ∈ Subgroup.zpowers wreathZ := by
    intro s hs hs1
    have hc := hab s hs y₁ hy₁
    obtain ⟨f, q⟩ := s
    obtain ⟨f₁, q₁⟩ := y₁
    change q = 1 at hs1
    change q₁ = wreathT at hy₁t
    subst hs1 hy₁t
    rcases eq_of_commute_base f f₁ (congrArg RegularWreathProduct.left hc) with h | h | h
    · have e : (⟨f, 1⟩ : W33) = 1 := RegularWreathProduct.ext h rfl
      rw [e]
      exact Subgroup.one_mem _
    · have e : (⟨f, 1⟩ : W33) = wreathZ := RegularWreathProduct.ext h wreathZ_right.symm
      rw [e]
      exact Subgroup.mem_zpowers _
    · have e : (⟨f, 1⟩ : W33) = wreathZ⁻¹ :=
        RegularWreathProduct.ext h wreathZ_inv_right.symm
      rw [e]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  let ρ : S →* Multiplicative (ZMod 3) := RegularWreathProduct.rightHom.comp S.subtype
  have hker : Nat.card ρ.ker ≤ 3 := by
    have hinj : Function.Injective (fun k : ρ.ker => (⟨((k : S) : W33),
        hSB _ (k : S).2 (MonoidHom.mem_ker.mp k.2)⟩ : Subgroup.zpowers wreathZ)) := by
      intro k k' h
      have h' := congrArg Subtype.val h
      simp only at h'
      exact Subtype.ext (Subtype.ext h')
    have h1 := Nat.card_le_card_of_injective _ hinj
    have hord : orderOf wreathZ = 3 :=
      orderOf_eq_prime (pow_three_eq_one_of_right_eq_one wreathZ_right) wreathZ_ne_one
    rwa [Nat.card_zpowers, hord] at h1
  have hrange : Nat.card ρ.range ≤ 3 := by
    calc Nat.card ρ.range ≤ Nat.card (Multiplicative (ZMod 3)) := Subgroup.card_le_card_group _
      _ = 3 := by simp
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv] at hcard
  rw [hcard]
  calc Nat.card ρ.range * Nat.card ρ.ker ≤ 3 * 3 := Nat.mul_le_mul hrange hker
    _ = 9 := by norm_num

theorem right_eq_one_of_abelian_of_card {S : Subgroup W33}
    (hab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (h27 : 27 ≤ Nat.card S) : ∀ y ∈ S, y.right = 1 := by
  intro y hy
  by_contra hq
  have := card_le_nine_of_abelian_of_not_le_base hab hy hq
  omega

variable {P : Type*} [Group P]

end CFSG.RankThree.PartTwo.Sec11
