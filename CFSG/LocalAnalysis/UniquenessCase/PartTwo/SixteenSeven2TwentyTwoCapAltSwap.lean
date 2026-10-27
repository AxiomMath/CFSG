module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.RankThree.PartTwo (altHeart evenWeightPerm)
open CFSG.QuasithinUnique (evenWeight)
open CFSG.HardMathSupport.Cooperstein.Coordinator
  (altAct altAct_mk apply_inv_eq_of_mk_eq evenWeightPerm_apply)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (pairEW pairEW_apply exists_ne_four)

private theorem s16c167_altAct_swap_mk_eq_iff {n : ℕ} (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (x : evenWeight n) :
    altAct (Equiv.swap a b) (x : altHeart n) = (x : altHeart n) ↔
      (x : Fin n → ZMod 2) a = (x : Fin n → ZMod 2) b := by
  constructor
  · intro h
    obtain ⟨p, hpa, hpb, -, -⟩ := exists_ne_four hn a b a b
    have hp : Equiv.swap a b p = p := Equiv.swap_apply_of_ne_of_ne hpa hpb
    have hx := apply_inv_eq_of_mk_eq (σ := Equiv.swap a b) (a := p) hp h a
    rw [Equiv.swap_inv, Equiv.swap_apply_left] at hx
    exact hx.symm
  · intro h
    have hx : evenWeightPerm (Equiv.swap a b) x = x := by
      refine Subtype.ext (funext fun i => ?_)
      rw [evenWeightPerm_apply, Equiv.swap_inv]
      by_cases hia : i = a
      · subst hia
        rw [Equiv.swap_apply_left, h]
      · by_cases hib : i = b
        · subst hib
          rw [Equiv.swap_apply_right, h]
        · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
    rw [altAct_mk, hx]

private theorem s16c167_swap_eq_of_mem_pair {n : ℕ} {a b c d : Fin n} (hab : a ≠ b)
    (ha : a ∈ ({c, d} : Finset (Fin n))) (hb : b ∈ ({c, d} : Finset (Fin n))) :
    Equiv.swap a b = Equiv.swap c d := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with hac | had <;> rcases hb with hbc | hbd
  · exact absurd (hac.trans hbc.symm) hab
  · rw [hac, hbd]
  · rw [had, hbc]; exact (Equiv.swap_comm c d).symm
  · exact absurd (had.trans hbd.symm) hab

theorem s16c167_swap_eq_of_altAct_fixed_iff {n : ℕ} (hn : 5 ≤ n) {σ τ : Equiv.Perm (Fin n)}
    (hσ : σ.IsSwap) (hτ : τ.IsSwap) (h : ∀ v : altHeart n, altAct σ v = v ↔ altAct τ v = v) :
    σ = τ := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨c, d, hcd, rfl⟩ := hτ
  have hiff : ∀ x : evenWeight n,
      (x : Fin n → ZMod 2) a = (x : Fin n → ZMod 2) b ↔
        (x : Fin n → ZMod 2) c = (x : Fin n → ZMod 2) d := by
    intro x
    have hx := h (x : altHeart n)
    rw [s16c167_altAct_swap_mk_eq_iff hn hab x,
      s16c167_altAct_swap_mk_eq_iff hn hcd x] at hx
    exact hx
  by_contra hne
  have hnotboth : ¬ (a ∈ ({c, d} : Finset (Fin n)) ∧ b ∈ ({c, d} : Finset (Fin n))) := by
    rintro ⟨ha, hb⟩
    exact hne (s16c167_swap_eq_of_mem_pair hab ha hb)
  rcases not_and_or.mp hnotboth with haT | hbT
  · have hac : a ≠ c := fun h => haT (by simp [h])
    have had : a ≠ d := fun h => haT (by simp [h])
    obtain ⟨m, hma, hmb, hmc, hmd⟩ := exists_ne_four hn a b c d
    have h1 : ((pairEW a m : evenWeight n) : Fin n → ZMod 2) a = 1 := by
      rw [pairEW_apply, if_pos rfl, if_neg (Ne.symm hma)]
      decide
    have h2 : ((pairEW a m : evenWeight n) : Fin n → ZMod 2) b = 0 := by
      rw [pairEW_apply, if_neg (Ne.symm hab), if_neg (Ne.symm hmb)]
      decide
    have h3 : ((pairEW a m : evenWeight n) : Fin n → ZMod 2) c = 0 := by
      rw [pairEW_apply, if_neg hac.symm, if_neg (Ne.symm hmc)]
      decide
    have h4 : ((pairEW a m : evenWeight n) : Fin n → ZMod 2) d = 0 := by
      rw [pairEW_apply, if_neg had.symm, if_neg (Ne.symm hmd)]
      decide
    have hx := hiff (pairEW a m)
    rw [h1, h2, h3, h4] at hx
    exact absurd (hx.mpr rfl) (by decide)
  · have hbc : b ≠ c := fun h => hbT (by simp [h])
    have hbd : b ≠ d := fun h => hbT (by simp [h])
    obtain ⟨m, hma, hmb, hmc, hmd⟩ := exists_ne_four hn a b c d
    have h1 : ((pairEW b m : evenWeight n) : Fin n → ZMod 2) b = 1 := by
      rw [pairEW_apply, if_pos rfl, if_neg (Ne.symm hmb)]
      decide
    have h2 : ((pairEW b m : evenWeight n) : Fin n → ZMod 2) a = 0 := by
      rw [pairEW_apply, if_neg hab, if_neg (Ne.symm hma)]
      decide
    have h3 : ((pairEW b m : evenWeight n) : Fin n → ZMod 2) c = 0 := by
      rw [pairEW_apply, if_neg hbc.symm, if_neg (Ne.symm hmc)]
      decide
    have h4 : ((pairEW b m : evenWeight n) : Fin n → ZMod 2) d = 0 := by
      rw [pairEW_apply, if_neg hbd.symm, if_neg (Ne.symm hmd)]
      decide
    have hx := hiff (pairEW b m)
    rw [h1, h2, h3, h4] at hx
    exact absurd (hx.mpr rfl) (by decide)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
