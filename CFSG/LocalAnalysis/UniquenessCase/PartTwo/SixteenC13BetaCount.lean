module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4Aut
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {T : Type} [CommGroup T] [Finite T]

theorem s16c13beta_exists_fix_card {p : ℕ} (hp : p = 3 ∨ p = 7) (hT : ∀ t : T, t ^ 2 = 1)
    {F : Subgroup (MulAut T)} (hF : IsElemAbelian p F) {ι : Type} (Y : ι → Subgroup T)
    (S : Finset ι) (hY : ∀ i ∈ S, rk ↥(Y i) = dParam p)
    (hFY : ∀ i ∈ S, ∀ f ∈ F, (Y i).map f.toMonoidHom = Y i) :
    ∃ F' : Subgroup (MulAut T), F' ≤ F ∧ (∀ i ∈ S, ∀ f ∈ F', ∀ y ∈ Y i, f y = y) ∧
      Nat.card F ≤ p ^ S.card * Nat.card F' := by
  classical
  have claim : ∀ (S : Finset ι), (∀ i ∈ S, rk ↥(Y i) = dParam p) →
      (∀ i ∈ S, ∀ f ∈ F, (Y i).map f.toMonoidHom = Y i) →
      ∃ F' : Subgroup (MulAut T), F' ≤ F ∧
        (∀ i ∈ S, ∀ f ∈ F', ∀ y ∈ Y i, f y = y) ∧
        Nat.card F ≤ p ^ S.card * Nat.card F' := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _ _
      exact ⟨F, le_rfl, by simp, by simp⟩
    · intro j S hj ih hY' hFY'
      obtain ⟨F', hF'le, hF'fix, hF'card⟩ := ih
        (fun i hi => hY' i (Finset.mem_insert_of_mem hi))
        (fun i hi => hFY' i (Finset.mem_insert_of_mem hi))
      have hYj : rk ↥(Y j) = dParam p := hY' j (Finset.mem_insert_self j S)
      have hF'ea : IsElemAbelian p F' := IsElemAbelian.mono hF hF'le
      have hF'Yj : ∀ f ∈ F', (Y j).map f.toMonoidHom = Y j :=
        fun f hf => hFY' j (Finset.mem_insert_self j S) f (hF'le hf)
      have hidx := s16n9b_case4_aut_index_le hp hT hYj hF'ea hF'Yj
      refine ⟨F' ⊓ centSub (Y j), inf_le_left.trans hF'le, ?_, ?_⟩
      · intro i hi f hf y hy
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact (mem_centSub.mp hf.2) y hy
        · exact hF'fix i hi f hf.1 y hy
      · rw [Finset.card_insert_of_notMem hj]
        calc Nat.card F ≤ p ^ S.card * Nat.card F' := hF'card
          _ ≤ p ^ S.card * (p * Nat.card ↥(F' ⊓ centSub (Y j))) :=
              Nat.mul_le_mul_left _ hidx
          _ = p ^ (S.card + 1) * Nat.card ↥(F' ⊓ centSub (Y j)) := by ring
  exact claim S hY hFY

theorem s16c13beta_exists_noncyclic_fix {p : ℕ} (hp : p = 3 ∨ p = 7) (hT : ∀ t : T, t ^ 2 = 1)
    {F : Subgroup (MulAut T)} (hF : IsElemAbelian p F) {n : ℕ} (hn : p ^ n ≤ Nat.card F)
    {ι : Type} (Y : ι → Subgroup T) (S : Finset ι) (hY : ∀ i ∈ S, rk ↥(Y i) = dParam p)
    (hFY : ∀ i ∈ S, ∀ f ∈ F, (Y i).map f.toMonoidHom = Y i) (hS : S.card + 2 ≤ n) :
    ∃ E : Subgroup (MulAut T), E ≤ F ∧ IsPGroup p ↥E ∧ ¬ IsCyclic ↥E ∧
      ∀ i ∈ S, ∀ e ∈ E, ∀ y ∈ Y i, e y = y := by
  classical
  obtain ⟨F', hF'le, hF'fix, hF'card⟩ :=
    s16c13beta_exists_fix_card hp hT hF Y S hY hFY
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hpos : 0 < p := hprime.pos
  have hcard : p ^ 2 ≤ Nat.card F' := by
    have hchain : p ^ (S.card + 2) ≤ p ^ S.card * Nat.card F' :=
      (Nat.pow_le_pow_right hpos hS).trans (hn.trans hF'card)
    rw [pow_add] at hchain
    exact Nat.le_of_mul_le_mul_left hchain (pow_pos hpos _)
  exact ⟨F', hF'le, (IsElemAbelian.mono hF hF'le).isPGroup,
    s16c7_not_isCyclic_of_elemAbelian hprime (IsElemAbelian.mono hF hF'le) hcard, hF'fix⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
