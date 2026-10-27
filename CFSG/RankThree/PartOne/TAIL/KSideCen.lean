module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartOne.TAIL

open Matrix

theorem center_sl_eq_bot {F : Type} [Field F] [Finite F] {m : ℕ} (hm0 : m ≠ 0)
    (hg : Nat.gcd m (Nat.card F - 1) = 1) :
    Subgroup.center (SpecialLinearGroup (Fin m) F) = ⊥ := by
  have := Fintype.ofFinite F
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp [zero_pow hm0] at hr
  have hq : r ^ (Nat.card F - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one r hr0
    rwa [Fintype.card_eq_nat_card] at h
  have hr1 : r = 1 := by
    have h : r ^ Nat.gcd m (Nat.card F - 1) = 1 := pow_gcd_eq_one.2 ⟨hr, hq⟩
    rwa [hg, pow_one] at h
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

theorem inf_centralizer_eq_bot_of_mulEquiv {G : Type} [Group G] {K : Subgroup G} {X : Type*}
    [Group X] (e : ↥K ≃* X) (hX : Subgroup.center X = ⊥) :
    K ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxC⟩
  have hc : e ⟨x, hxK⟩ ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨k, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC k k.2)
  rw [hX, Subgroup.mem_bot] at hc
  have : (⟨x, hxK⟩ : ↥K) = 1 := e.injective (hc.trans (map_one e).symm)
  have := congrArg Subtype.val this
  simpa using this

end CFSG.RankThree.PartOne.TAIL
