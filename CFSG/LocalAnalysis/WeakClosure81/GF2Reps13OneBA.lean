module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem w16g_isElemAbelianOfRank_one_of_card {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] (hcard : Nat.card X = p) : IsElemAbelianOfRank p 1 X := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨mulEquivOfPrimeCardEq hcard ?_⟩
  simp [Nat.card_eq_fintype_card]

theorem w16g_isElemAbelianOfRank_one_iff {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] : IsElemAbelianOfRank p 1 X ↔ Nat.card X = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨e⟩
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card]
  · exact w16g_isElemAbelianOfRank_one_of_card hp

theorem w16g_conj_pow_inv {A : Type*} [Group A] {t x : A} (h : t * x * t⁻¹ = x⁻¹) (n : ℕ) :
    t * x ^ n * t⁻¹ = (x ^ n)⁻¹ := by
  have hc : MulAut.conj t x = x⁻¹ := by rw [MulAut.conj_apply, h]
  calc t * x ^ n * t⁻¹ = MulAut.conj t (x ^ n) := (MulAut.conj_apply t _).symm
    _ = (MulAut.conj t x) ^ n := map_pow (MulAut.conj t) x n
    _ = (x⁻¹) ^ n := by rw [hc]
    _ = (x ^ n)⁻¹ := by rw [inv_pow]

theorem w16g_isElemAbelianOfRank_of_card {p n : ℕ} [hp : Fact p.Prime] {X : Type*} [Group X]
    [Finite X] (hcomm : ∀ a b : X, a * b = b * a) (hpow : ∀ a : X, a ^ p = 1)
    (hcard : Nat.card X = p ^ n) : IsElemAbelianOfRank p n X := by
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hcomm }
  let _ : Module (ZMod p) (Additive X) := AddCommGroup.zmodModule (n := p) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hpow, ofMul_one]
  have hF : Module.Finite (ZMod p) (Additive X) := Module.Finite.of_finite
  have hFr : Module.Free (ZMod p) (Additive X) := Module.Free.of_divisionRing _ _
  have h := @Module.natCard_eq_pow_finrank (ZMod p) (Additive X) _ _ _ hF
  have hfin : Module.finrank (ZMod p) (Additive X) =
      Module.finrank (ZMod p) (Fin n → ZMod p) := by
    rw [Nat.card_zmod] at h
    rw [Module.finrank_fin_fun]
    exact Nat.pow_right_injective hp.out.two_le (h.symm.trans hcard)
  exact ⟨AddEquiv.toMultiplicativeRight
    (@LinearEquiv.ofFinrankEq (ZMod p) (Additive X) (Fin n → ZMod p) _ _ _ hFr _ _ _ _ hF _
      hfin).toAddEquiv⟩

end CFSG.LocalAnalysis.WeakClosure81
