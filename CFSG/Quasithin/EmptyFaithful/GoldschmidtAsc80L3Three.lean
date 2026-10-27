module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3ThreeFin
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3ThreeFix
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Solv

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15
open scoped MatrixGroups

theorem card_sl3_three : Nat.card SL(3, ZMod 3) = 5616 := by
  have hSL := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := ZMod 3) (n := 3)
    (by norm_num)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num), Nat.card_zmod] at hSL
  norm_num at hSL
  rw [Nat.card_eq_fintype_card, hSL]

theorem prime_dvd_card_sl3_three {r : ℕ} (hr : r.Prime) (h : r ∣ Nat.card SL(3, ZMod 3)) :
    r = 2 ∨ r = 3 ∨ r = 13 := by
  rw [card_sl3_three, show (5616 : ℕ) = 2 ^ 4 * 3 ^ 3 * 13 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hr).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
        (hr.dvd_of_dvd_pow h)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h))

variable {p : ℕ} [Fact p.Prime]

theorem mem_linePar_of_commute_zt (hp2 : p ≠ 2) {y : SL(3, ZMod p)}
    (h : y * zt p = zt p * y) : y ∈ linePar p := by
  have hm := congrArg (fun g : SL(3, ZMod p) => (g : Matrix (Fin 3) (Fin 3) (ZMod p))) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_zt] at hm
  have e02 := congrFun (congrFun hm 0) 2
  have e12 := congrFun (congrFun hm 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e02 e12
  refine ⟨?_, ?_⟩
  · have : (2 : ZMod p) * (y : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 := by
      linear_combination e02
    exact (mul_eq_zero.mp this).resolve_left (two_ne_zero_zmod hp2)
  · have : (2 : ZMod p) * (y : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0 := by
      linear_combination e12
    exact (mul_eq_zero.mp this).resolve_left (two_ne_zero_zmod hp2)

theorem not_irreducible_of_le_linePar {Y : Subgroup SL(3, ZMod p)} (hY : Y ≤ linePar p) :
    ¬ IsIrreducibleSL3 Y := by
  intro hirr
  let W : Submodule (ZMod p) (Fin 3 → ZMod p) := Submodule.span (ZMod p) {![0, 0, 1]}
  have hinv : ∀ g ∈ Y, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ W := by
    intro g hg w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    obtain ⟨h0, h1⟩ := hY hg
    refine Submodule.mem_span_singleton.mpr ⟨c * (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 2, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1]
    ring
  rcases hirr W hinv with hbot | htop
  · have : (![0, 0, 1] : Fin 3 → ZMod p) ∈ W := Submodule.mem_span_singleton_self _
    rw [hbot] at this
    have h2 := congrFun (Submodule.mem_bot _ |>.mp this) 2
    simp at h2
  · have : (![1, 0, 0] : Fin 3 → ZMod p) ∈ W := by rw [htop]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    have h0 := congrFun hc 0
    simp at h0

theorem false_of_normal_two {Y N : Subgroup SL(3, ZMod 3)}
    (hB : leviBlock 3 ≤ Y) (hirr : IsIrreducibleSL3 Y)
    (hnorm : ∀ y ∈ Y, ∀ a ∈ N, y * a * y⁻¹ ∈ N) (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hexp : ∀ a ∈ N, a ^ 2 = 1) (hne : N ≠ ⊥) : False := by
  have key : ∀ x ∈ N, x ≠ 1 → x = zt 3 := fun x hx hx1 =>
    eq_zt_of_sq_eq_one (by simpa [pow_two] using hexp x hx) hx1
      (hcomm x hx _ (hnorm _ (hB upperUni_mem) x hx))
      (hcomm x hx _ (hnorm _ (hB lowerUni_mem) x hx))
  obtain ⟨x, hxN, hx1⟩ : ∃ x ∈ N, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr (h a ha))
  have hz : zt 3 ∈ N := key x hxN hx1 ▸ hxN
  have hz1 : zt 3 ≠ 1 := fun h => by
    have := congrArg (fun g : SL(3, ZMod 3) => (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 0) h
    simp [coe_zt] at this
    exact absurd (by linear_combination -this : (2 : ZMod 3) = 0) (by decide)
  have hcz : ∀ y ∈ Y, y * zt 3 = zt 3 * y := fun y hy => by
    have h1 : y * zt 3 * y⁻¹ ∈ N := hnorm y hy _ hz
    have h2 : y * zt 3 * y⁻¹ ≠ 1 := fun h => hz1 (by
      have := congrArg (fun g => y⁻¹ * g * y) h
      simpa [mul_assoc] using this)
    have h3 := key _ h1 h2
    calc y * zt 3 = (y * zt 3 * y⁻¹) * y := by group
      _ = zt 3 * y := by rw [h3]
  exact not_irreducible_of_le_linePar (fun y hy => mem_linePar_of_commute_zt (by decide) (hcz y hy))
    hirr

theorem false_of_normal_thirteen {Y N : Subgroup SL(3, ZMod 3)}
    (hB : leviBlock 3 ≤ Y) (hnorm : ∀ y ∈ Y, ∀ a ∈ N, y * a * y⁻¹ ∈ N)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hexp : ∀ a ∈ N, a ^ 13 = 1) (hne : N ≠ ⊥) :
    False := by
  obtain ⟨x, hxN, hx1⟩ : ∃ x ∈ N, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr (h a ha))
  exact hx1 (eq_one_of_pow_thirteen (hexp x hxN)
    (hcomm x hxN _ (hnorm _ (hB upperUni_mem) x hxN)))

theorem no_solvable_irreducible_three (hp3 : p = 3)
    {Y : Subgroup SL(3, ZMod p)} (hB : leviBlock p ≤ Y) (hirr : IsIrreducibleSL3 Y) :
    ¬ Group.IsSolvable ↥Y := by
  subst hp3
  intro hsolv
  have hYne : Y ≠ ⊥ := fun h => by
    have hl : lowerUni 3 ∈ Y := hB lowerUni_mem
    rw [h] at hl
    have h1 : lowerUni 3 = 1 := Subgroup.mem_bot.mp hl
    have := congrArg (fun g : SL(3, ZMod 3) => (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 0) h1
    simp [lowerUni] at this
  obtain ⟨r, N, hr, hrd, hNY, hNne, hcomm, hexp, hnorm⟩ := exists_primary_normal hsolv hYne
  rcases prime_dvd_card_sl3_three hr hrd with rfl | rfl | rfl
  · exact false_of_normal_two hB hirr hnorm hcomm hexp hNne
  · refine false_of_normal_three_group hirr (U := N) (fun g => ⟨1, ?_⟩) hnorm hNne
    exact Subtype.ext (by simpa using hexp g.1 g.2)
  · exact false_of_normal_thirteen hB hnorm hcomm hexp hNne

end CFSG.Quasithin.E2P.Asc80
