module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

namespace CFSG.RankThree.PartOne.TCP

open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.Assembly.LowTwoRank

section Generic

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem pow_apply_mem_of_invariant {T : Module.End K V} {W : Submodule K V}
    (hW : ∀ w ∈ W, T w ∈ W) (n : ℕ) : ∀ w ∈ W, (T ^ n) w ∈ W := by
  induction n with
  | zero => intro w hw; simpa using hw
  | succ n ih =>
    intro w hw
    rw [pow_succ', Module.End.mul_apply]
    exact hW _ (ih w hw)

theorem aeval_apply_mem_of_invariant {T : Module.End K V} {W : Submodule K V}
    (hW : ∀ w ∈ W, T w ∈ W) (f : K[X]) : ∀ w ∈ W, aeval T f w ∈ W := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    intro w hw
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (hp w hw) (hq w hw)
  | monomial n c =>
    intro w hw
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact W.smul_mem _ (pow_apply_mem_of_invariant hW n w hw)

variable [FiniteDimensional K V]

theorem exists_inf_primaryComponent_ne_bot {T : Module.End K V}
    (hsq : Squarefree (minpoly K T)) {W : Submodule K V} (hW0 : W ≠ ⊥)
    (hW : ∀ w ∈ W, T w ∈ W) : ∃ a ∈ primaryFactors T, W ⊓ primaryComponent T a ≠ ⊥ := by
  classical
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hsum : ∑ a ∈ primaryFactors T, primaryProjection T a w = w := by
    have := LinearMap.congr_fun (sum_primaryProjection hsq) w
    rw [LinearMap.sum_apply] at this
    simpa using this
  by_contra hcon
  push Not at hcon
  have hzero : ∀ a ∈ primaryFactors T, primaryProjection T a w = 0 := by
    intro a ha
    have hmemW : primaryProjection T a w ∈ W :=
      aeval_apply_mem_of_invariant hW (primaryIdempotent T a) w hwW
    have hmemV : primaryProjection T a w ∈ primaryComponent T a := primaryProjection_mem hsq ha w
    have h1 : primaryProjection T a w ∈ W ⊓ primaryComponent T a := ⟨hmemW, hmemV⟩
    rw [hcon a ha] at h1
    exact (Submodule.mem_bot K).mp h1
  rw [Finset.sum_eq_zero hzero] at hsum
  exact hw0 hsum.symm

theorem le_of_primaryMultiplicity_eq_one {T : Module.End K V} {a : K[X]}
    [Fact (Irreducible a)] (hm : primaryMultiplicity T a = 1) {U : Submodule K V}
    (hUa : U ≤ primaryComponent T a) (hU : ∀ w ∈ U, T w ∈ U) (hU0 : U ≠ ⊥) :
    primaryComponent T a ≤ U := by
  let U' : Submodule (AdjoinRoot a) (primaryComponent T a) :=
    { carrier := {v | (v : V) ∈ U}
      add_mem' := fun {u v} hu hv => U.add_mem hu hv
      zero_mem' := U.zero_mem
      smul_mem' := fun e v hv => by
        induction e using AdjoinRoot.induction_on with
        | _ f =>
          show ((AdjoinRoot.mk a f • v : primaryComponent T a) : V) ∈ U
          rw [coe_mk_smul_primaryComponent]
          exact aeval_apply_mem_of_invariant hU f v hv }
  have hU'0 : U' ≠ ⊥ := by
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    intro hbot
    have : (⟨u, hUa huU⟩ : primaryComponent T a) ∈ U' := huU
    rw [hbot, Submodule.mem_bot] at this
    exact hu0 (congrArg Subtype.val this)
  have hU'top : U' = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 : 1 ≤ finrank (AdjoinRoot a) U' := Submodule.one_le_finrank_iff.mpr hU'0
    have h2 : finrank (AdjoinRoot a) U' ≤ finrank (AdjoinRoot a) (primaryComponent T a) :=
      Submodule.finrank_le U'
    have h3 : finrank (AdjoinRoot a) (primaryComponent T a) = 1 := hm
    omega
  intro v hv
  have : (⟨v, hv⟩ : primaryComponent T a) ∈ U' := hU'top ▸ Submodule.mem_top
  exact this

end Generic

section Symplectic

variable {r : ℕ} {K : Type} [Field K]

theorem false_of_invariant_isotropic_block {x : StatedSp r K}
    (H : AltPrimaryData (spForm r K) (spLin r K x)) {a : K[X]}
    (ha : a ∈ primaryFactors (spEnd x)) (hself : reciprocalPolynomial a = a)
    (hm : primaryMultiplicity (spEnd x) a = 1) {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hWiso : ∀ u ∈ W, ∀ v ∈ W, spForm r K u v = 0) (hWx : ∀ w ∈ W, spEnd x w ∈ W)
    (hne : W ⊓ primaryComponent (spEnd x) a ≠ ⊥) : False := by
  have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have hsub := le_of_primaryMultiplicity_eq_one (T := spEnd x) hm
    (U := W ⊓ primaryComponent (spEnd x) a) inf_le_right
    (fun w hw => ⟨hWx w hw.1, apply_mem_primaryComponent (Commute.refl _) hw.2⟩) hne
  have hne0 := primaryComponent_ne_bot H.squarefree ha
  apply hne0
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  refine H.eq_zero_of_perfect_left ha hv fun w hw => ?_
  rw [hself] at hw
  exact hWiso v (hsub hv).1 w (hsub hw).1

end Symplectic

end CFSG.RankThree.PartOne.TCP
