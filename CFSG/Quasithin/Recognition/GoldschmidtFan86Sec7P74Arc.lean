module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Tr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Arc

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_arc_offset (F : FanTree Γ G) {j : ℕ} (Q : Arc Γ j) (i : ℕ) :
    ∃ Q' : Arc Γ (j + i), ∀ m, m ≤ j → Q'.vert (i + m) = Q.vert m := by
  induction i with
  | zero => exact ⟨Q, fun m _ => by rw [zero_add]⟩
  | succ i ih =>
    obtain ⟨Q', hQ'⟩ := ih
    obtain ⟨Q'', -, hQ''⟩ := P71.exists_prepend F Q'
    refine ⟨Q'', fun m hm => ?_⟩
    rw [show i + 1 + m = (i + m) + 1 by omega, hQ'' (i + m) (by omega), hQ' m hm]

theorem exists_arc8_through (F : FanTree Γ G) {j : ℕ} (Q : Arc Γ j) {i : ℕ} (hij : i + j ≤ 8) :
    ∃ P : Arc Γ 8, ∀ m, m ≤ j → P.vert (i + m) = Q.vert m := by
  obtain ⟨Q', hQ'⟩ := exists_arc_offset F Q i
  obtain ⟨P, hP⟩ := P71.exists_extend F Q' 8 (by omega)
  exact ⟨P, fun m hm => by rw [hP (i + m) (by omega), hQ' m hm]⟩

theorem exists_arc8_between (F : FanTree Γ G) {a w : V} {k : ℕ} (hk : Γ.dist a w = k) {i : ℕ}
    (hik : i + k ≤ 8) : ∃ P : Arc Γ 8, P.vert i = a ∧ P.vert (i + k) = w := by
  have key : ∀ n : ℕ, Γ.dist a w = n → ∃ A : Arc Γ n, A.vert 0 = a ∧ A.vert n = w := by
    rintro n rfl
    exact IsTree.exists_arc_between F.isTree a w
  obtain ⟨A, hA0, hAk⟩ := key k hk
  obtain ⟨P, hP⟩ := exists_arc8_through F A hik
  exact ⟨P, by simpa [hA0] using hP 0 (Nat.zero_le _), by rw [hP k le_rfl, hAk]⟩

end P74

end CFSG.Quasithin.Fan86
