module

public import CFSG.GroupTheory.CommutatorProductCard
public import CFSG.RankThree.GF2n.Smith81.Sec115Dim
public import CFSG.RankThree.GF2n.Stroth80.SectionActRank
public import CFSG.RankThree.GF2n.Smith81.LinSetup

public section

namespace CFSG.RankThree.GF2n.Smith81

open scoped Matrix
open CFSG.RankThree.GF2n.Stroth80

private theorem commutator_le_of_strothHyp {G : Type} [Group G] [Finite G]
    {M Q Z : Subgroup G} (H : StrothHyp M Q Z) :
    ⁅Q, Q⁆ ≤ Z :=
  Subgroup.commutator_le.mpr fun _ ha _ hb => comm_mem_Z H ha hb

private theorem half_eq_of_card_eq {q c r n : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n)
    (hA : c * q = q * q ^ r * (q * q ^ r))
    (hc : c = q ^ (n + 1) ∨ (Odd n ∧ c = q ^ (n - 1 + 1))) : n / 2 = r := by
  have key : ∀ m : ℕ, q ^ m = q ^ (2 * r + 2) → m = 2 * r + 2 := fun m h =>
    Nat.pow_right_injective hq h
  rcases hc with h | ⟨-, h⟩
  · subst h
    have e : q ^ (n + 1 + 1) = q ^ (2 * r + 2) := by
      calc q ^ (n + 1 + 1) = q ^ (n + 1) * q := by ring
        _ = q * q ^ r * (q * q ^ r) := hA
        _ = q ^ (2 * r + 2) := by ring
    have := key _ e
    omega
  · have e0 : n - 1 + 1 = n := by omega
    rw [e0] at h
    subst h
    have e : q ^ (n + 1) = q ^ (2 * r + 2) := by
      calc q ^ (n + 1) = q ^ n * q := by ring
        _ = q * q ^ r * (q * q ^ r) := hA
        _ = q ^ (2 * r + 2) := by ring
    have := key _ e
    omega

theorem lin115RankStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B X : Subgroup G) (x : G) (n : ℕ) (V₁ V₂ : Subgroup G),
      Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n → Sit M Q Z X x →
        x ∈ Lgen M (LB M Q B) → Q ⊓ QB X = ⊥ →
          HasDimOn V₁ Z (n / 2) x ∧ HasDimOn V₂ Z (n / 2) x :=
  fun G _ _ M Q Z B X x n V₁ V₂ hc hS hn hs hx hQ => by
    have hW := LinSetup.width hc.hyp hS
    have hsm := smith115Statement_holds G M Q Z X x hs n hW hQ
    have hdisj : Nat.card ↥(⁅Q, Subgroup.zpowers x⁆ ⊔ Z) = Nat.card Z ^ (n + 1) ∨
        (Odd n ∧ Nat.card ↥(⁅Q, Subgroup.zpowers x⁆ ⊔ Z) = Nat.card Z ^ (n - 1 + 1)) :=
      hsm.2.2.2
    obtain ⟨K, _, _, hcard, φ, -, -, hZV₁, -, hZV₂, -, hint, hsup, hs₁, hs₂, -, -⟩ := hS
    have hq2 : 2 ≤ Nat.card Z := by
      have := hc.hyp.q4
      omega
    have hxN₁ : x ∈ Subgroup.normalizer (V₁ : Set G) := hs₁.1 hx
    have hxN₂ : x ∈ Subgroup.normalizer (V₂ : Set G) := hs₂.1 hx
    have h1 : Nat.card ↥(⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) =
        Nat.card Z * Nat.card K ^
          (((φ ⟨x, hx⟩ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1).rank :=
      CFSG.RankThree.GF2n.Stroth80.card_comm_zpowers_sup_of_sectionAct hs₁ hZV₁ ⟨x, hx⟩
    have h2 : Nat.card ↥(⁅V₂, Subgroup.zpowers x⁆ ⊔ Z) =
        Nat.card Z * Nat.card K ^
          ((((φ ⟨x, hx⟩)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ - 1).rank :=
      CFSG.RankThree.GF2n.Stroth80.card_comm_zpowers_sup_of_sectionAct hs₂ hZV₂ ⟨x, hx⟩
    have hrk := CFSG.RankThree.GF2n.Stroth80.rank_inv_transpose_sub_one (φ ⟨x, hx⟩)
    rw [hrk] at h2
    have hmul := CFSG.GroupTheory.card_comm_zpowers_sup_mul_card hsup hint hZV₁ hZV₂
      (commutator_le_of_strothHyp hc.hyp) hxN₁ hxN₂
    rw [h1, h2, hcard] at hmul
    have hhalf := half_eq_of_card_eq hq2 (by omega) hmul hdisj
    refine ⟨?_, ?_⟩
    · show Nat.card ↥(⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) = Nat.card Z ^ (n / 2 + 1)
      rw [h1, hcard, hhalf]
      ring
    · show Nat.card ↥(⁅V₂, Subgroup.zpowers x⁆ ⊔ Z) = Nat.card Z ^ (n / 2 + 1)
      rw [h2, hcard, hhalf]
      ring

end CFSG.RankThree.GF2n.Smith81
