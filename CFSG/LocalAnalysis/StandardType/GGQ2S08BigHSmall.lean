module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigNumeric
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigCardStab
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigCardStabRed

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_hsmall_irr {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {x : G}
    (hx : x ∈ Bs) {N : ℕ} (hN : 10 ≤ N) (hBs : Nat.card ↥Bs = 3 ^ N) {W : ℕ}
    (hW : W ≤ 2 ^ (N - 1) * (N - 1).factorial)
    (hstab : Nat.card ↥(ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) ≤
      4 * W)
    {A : Subgroup (MulAut ↥Bs)} (hA : A ≤ ggAutomizer ⊤ Bs) :
    8 * Nat.card ↥A < 3 ^ (N * (N - 1) / 2) := by
  classical
  have h1 := ggQ2s08_card_le_of_stab hx hstab hA
  rw [hBs] at h1
  calc 8 * Nat.card ↥A ≤ 8 * (3 ^ N * (4 * W)) := Nat.mul_le_mul_left 8 h1
    _ ≤ 8 * (3 ^ N * (4 * (2 ^ (N - 1) * (N - 1).factorial))) :=
        Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 4 hW))
    _ < 3 ^ (N * (N - 1) / 2) := ggQ2s08_count_irr hN

theorem ggQ2s08_hsmall_red {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {x : G}
    (hx : x ∈ Bs) (hab : ∀ a b : ↥Bs, a * b = b * a) {r : ℕ} (hr : 9 ≤ r)
    (hBs : Nat.card ↥Bs = 3 ^ (r + 1)) {W : ℕ} (hW : W ≤ 2 ^ r * r.factorial)
    (hstab : Nat.card ↥(ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) ≤
      4 * W)
    {A : Subgroup (MulAut ↥Bs)} (hA : A ≤ ggAutomizer ⊤ Bs) {H : Subgroup ↥Bs}
    (hxH : (⟨x, hx⟩ : ↥Bs) ∉ H) (hidx : H.index = 3) (hinv : ∀ φ ∈ A, ∀ b ∈ H, φ b ∈ H) :
    8 * Nat.card ↥A < 3 ^ (r * (r - 1) / 2) := by
  classical
  have h1 := ggQ2s08_card_le_of_stab_red hx hab hstab hA hxH hidx hinv
  have hH : Nat.card ↥H = 3 ^ r := by
    have h2 := Subgroup.card_mul_index H
    rw [hidx, hBs] at h2
    have h3 : Nat.card ↥H * 3 = 3 ^ r * 3 := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3
  rw [hH] at h1
  calc 8 * Nat.card ↥A ≤ 8 * (2 * 3 ^ r * (4 * W)) := Nat.mul_le_mul_left 8 (by linarith)
    _ ≤ 8 * (2 * 3 ^ r * (4 * (2 ^ r * r.factorial))) :=
        Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 4 hW))
    _ < 3 ^ (r * (r - 1) / 2) := ggQ2s08_count_red hr

end CFSG.StandardType

end
