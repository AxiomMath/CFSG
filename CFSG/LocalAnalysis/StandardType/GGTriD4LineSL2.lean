module

public import Mathlib
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType

open scoped MatrixGroups

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

private lemma zmodMultiplicative_pow_self {r : ℕ} (u : Multiplicative (ZMod r)) : u ^ r = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem triD4Line_not_injective_mulAut_SL2 (F : Type) [Field F] [Finite F] (N : ℕ)
    (hF : Nat.card F = 2 ^ N) (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) (hrN : ¬ r ∣ N)
    (φ : Multiplicative (ZMod r) × Multiplicative (ZMod r) →*
      MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) :
    ¬ Function.Injective φ := by
  classical
  intro hinj
  haveI : NeZero r := ⟨hr.pos.ne'⟩
  haveI : CharP F 2 := char_two_of_card hF
  let A : Subgroup (MulAut SL(2, F)) := φ.range
  have hdom_pow : ∀ g : Multiplicative (ZMod r) × Multiplicative (ZMod r), g ^ r = 1 := by
    rintro ⟨u, v⟩
    exact Prod.ext (by simpa using zmodMultiplicative_pow_self u)
      (by simpa using zmodMultiplicative_pow_self v)
  have hAexp : ∀ a ∈ A, a ^ r = 1 := by
    rintro a ⟨x, rfl⟩
    rw [← map_pow, hdom_pow x, map_one]
  have hcardAut : Nat.card (RingAut F) = N :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic (p := 2) (n := N)
      Nat.prime_two F hF).1
  have hcop : Nat.Coprime r N := (Nat.Prime.coprime_iff_not_dvd hr).mpr hrN
  have hAinner : A ≤ inner SL(2, F) := by
    intro a ha
    rw [inner_eq_ker_mulAutToRingAut hF, MonoidHom.mem_ker]
    have hr1 : (mulAutToRingAut hF a) ^ r = 1 := by
      rw [← map_pow, hAexp a ha, map_one]
    have hN1 : (mulAutToRingAut hF a) ^ N = 1 := by
      have := pow_card_eq_one' (x := mulAutToRingAut hF a)
      rwa [hcardAut] at this
    have hg := (pow_gcd_eq_one).mpr ⟨hr1, hN1⟩
    rw [hcop.gcd_eq_one, pow_one] at hg
    exact hg
  let f : SL(2, F) →* MulAut SL(2, F) := MulAut.conj
  have hfker : f.ker = Subgroup.center SL(2, F) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h x
      have hx : g * x * g⁻¹ = x := by
        have := congrArg (fun e : MulAut SL(2, F) => e x) h
        simpa [f, MulAut.conj_apply] using this
      have hx' : g * x = x * g := by
        calc g * x = g * x * g⁻¹ * g := by group
          _ = x * g := by rw [hx]
      exact hx'.symm
    · intro h
      apply MulEquiv.ext
      intro x
      show (MulAut.conj g) x = x
      rw [MulAut.conj_apply, ← h x]
      simp
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, hfker, sl2_center_eq_bot]
  let P : Subgroup SL(2, F) := A.comap f
  have hPpow : ∀ g ∈ P, g ^ r = 1 := by
    intro g hg
    exact hf (by rw [map_pow, hAexp (f g) hg, map_one])
  have hP : IsPGroup r P := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one, orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (by simpa using hPpow (g : SL(2, F)) g.2)
  haveI : Fact r.Prime := ⟨hr⟩
  have hPcyc : IsCyclic P := CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic hr2 P hP
  have hPmap : P.map f = A := Subgroup.map_comap_eq_self (f := f) hAinner
  let ePA : P ≃* A := hPmap ▸ Subgroup.equivMapOfInjective P f hf
  let eA : Multiplicative (ZMod r) × Multiplicative (ZMod r) ≃* A := MonoidHom.ofInjective hinj
  let ePD : P ≃* Multiplicative (ZMod r) × Multiplicative (ZMod r) := ePA.trans eA.symm
  have hDcyc : IsCyclic (Multiplicative (ZMod r) × Multiplicative (ZMod r)) :=
    ePD.isCyclic.mp hPcyc
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_natCard_le_orderOf.mp hDcyc
  have hcard_dom : Nat.card (Multiplicative (ZMod r) × Multiplicative (ZMod r)) = r ^ 2 := by
    rw [Nat.card_prod]
    have : Nat.card (Multiplicative (ZMod r)) = r := Nat.card_zmod r
    rw [this, pow_two]
  have hdiv : orderOf g ∣ r := orderOf_dvd_of_pow_eq_one (hdom_pow g)
  have hle : orderOf g ≤ r := Nat.le_of_dvd hr.pos hdiv
  have hle2 : r ^ 2 ≤ r := by
    rw [← hcard_dom]
    exact le_trans hg hle
  have hmul : r * r ≤ r * 1 := by simpa [pow_two, mul_one] using hle2
  have hrle1 : r ≤ 1 := Nat.le_of_mul_le_mul_left hmul hr.pos
  exact (not_le_of_gt hr.one_lt) hrle1

end CFSG.StandardType
