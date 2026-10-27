module

public import CFSG.RankThree.PartTwo.KFacts.K71OddChar
public import CFSG.ClassicalInvolution.Orders.Symplectic
public import CFSG.RankThree.PartTwo.Sec4.HeringK419PinNum

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringPin

open Finset CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)

theorem exists_prime_pow_of_not_prime {F : Type} [Field F] [Finite F]
    (h : ¬ (Nat.card F).Prime) : ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ Nat.card F = p ^ e ∧
      p = ringChar F := by
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hn' : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  refine ⟨ringChar F, n, hp, ?_, hn', rfl⟩
  by_contra hlt
  have h1 : (n : ℕ) = 1 := by have := n.pos; omega
  rw [h1, pow_one] at hn'
  exact h (hn' ▸ hp)

theorem xord_projectiveSL {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] {p e : ℕ}
    (hq : Nat.card F = p ^ e) : XOrd (Nat.card (LinearFlag.projectiveSL n F)) p e := by
  have h := CFSG.RankThree.PartTwo.KFacts.card_projectiveSL_mul_card_scalars (K := F) (n := n)
    (by omega)
  have hg := LinearFlag.card_scalars_dvd (K := F) (n := n) (by omega)
  rw [hq] at h hg
  exact XOrd.sl n _ hn hg h

theorem xord_SL {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] {p e : ℕ}
    (hq : Nat.card F = p ^ e) : XOrd (Nat.card (Matrix.SpecialLinearGroup (Fin n) F)) p e :=
  XOrd.sl n 1 hn (one_dvd _) (by rw [mul_one, LinearFlag.card_SL_eq (by omega), hq])

theorem xord_PSp {r : ℕ} {F : Type} [Field F] [Finite F] (hr : 3 ≤ r ∨ (r = 2 ∧ ringChar F ≠ 2))
    {p e : ℕ} (hp : p = ringChar F) (hq : Nat.card F = p ^ e) :
    XOrd (Nat.card (StatedProj (StatedSp r F))) p e := by
  by_cases h2 : ringChar F = 2
  · haveI : CharP F 2 := h2 ▸ ringChar.charP F
    have hr3 : 3 ≤ r := by
      rcases hr with h | ⟨-, h⟩
      · exact h
      · exact absurd h2 h
    have hc := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo (K := F) r
    rw [hq] at hc
    exact XOrd.spEven r hr3 (hp.trans h2) hc
  · have h2' : (2 : F) ≠ 0 := Ring.two_ne_zero h2
    have hr2 : 2 ≤ r := by rcases hr with h | ⟨h, -⟩ <;> omega
    have hc := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero h2' (n := r)
      (by omega)
    rw [hq] at hc
    exact XOrd.spOdd r hr2 (hp ▸ h2) hc

instance finite_projectiveSL {n : ℕ} {F : Type} [Field F] [Finite F] :
    Finite (LinearFlag.projectiveSL n F) :=
  haveI : Finite (Matrix.SpecialLinearGroup (Fin n) F) :=
    Finite.of_injective (fun g => (g : Matrix (Fin n) (Fin n) F)) Subtype.val_injective
  inferInstance

instance finite_SL {n : ℕ} {F : Type} [Field F] [Finite F] :
    Finite (Matrix.SpecialLinearGroup (Fin n) F) :=
  Finite.of_injective (fun g => (g : Matrix (Fin n) (Fin n) F)) Subtype.val_injective

instance finite_statedProj_statedSp {r : ℕ} {F : Type} [Field F] [Finite F] :
    Finite (StatedProj (StatedSp r F)) :=
  haveI : Finite (CFSG.Assembly.LowTwoRank.StatedSp r F) :=
    Finite.of_injective (fun g => ((g : Matrix.GeneralLinearGroup (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) fun a b h =>
        Subtype.ext (Units.ext h)
  inferInstance

end CFSG.RankThree.PartTwo.Sec4.HeringPin
