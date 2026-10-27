module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLComp
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockTorus
public import Mathlib.Tactic.ComputeDegree

public section

namespace CFSG.StandardType.GGHalf

open CFSG.StandardType CFSG.StandardType.CoordSL Matrix

@[expose] noncomputable def phi3 : Polynomial F2 := Polynomial.X ^ 2 + Polynomial.X + 1

private theorem centFrame_f2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  let φ : F2 ≃+* ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv
  have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h (φ x) with h0 | h1
  · left
    calc x = φ.symm (φ x) := (φ.symm_apply_apply x).symm
      _ = φ.symm 0 := by rw [h0]
      _ = 0 := map_zero φ.symm
  · right
    calc x = φ.symm (φ x) := (φ.symm_apply_apply x).symm
      _ = φ.symm 1 := by rw [h1]
      _ = 1 := map_one φ.symm

private theorem centFrame_one_add_one : (1 : F2) + 1 = 0 := by
  have h : (2 : F2) = 1 + 1 := by norm_num
  rw [← h, gf2_two]

private theorem centFrame_card_f2 : Nat.card F2 = 2 := by
  rw [GaloisField.card 2 1 (by omega)]
  norm_num

theorem phi3_irreducible : Irreducible phi3 := by
  change Irreducible (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2)
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).natDegree = 2 := by
      compute_degree!
    rw [hdeg]; decide
  · intro x hx
    rw [Polynomial.IsRoot.def] at hx
    rcases centFrame_f2_eq_zero_or_one x with rfl | rfl
    · have h1 : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).eval 0 = 1 := by simp
      rw [h1] at hx; exact one_ne_zero hx
    · have h1 : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).eval 1 = 1 := by
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one, one_pow]
        rw [centFrame_one_add_one, zero_add]
      rw [h1] at hx; exact one_ne_zero hx

instance phi3_fact : Fact (Irreducible phi3) := ⟨phi3_irreducible⟩

theorem phi3_dvd_cyclotomic : phi3 ∣ Polynomial.cyclotomic 3 F2 := by
  unfold phi3
  rw [Polynomial.cyclotomic_three]

theorem natCast_three_ne_zero : ((3 : ℕ) : F2) ≠ 0 := by
  have h : ((3 : ℕ) : F2) = 1 := by
    have h31 : ((3 : ℕ) : F2) = 2 + 1 := by norm_num
    rw [h31, gf2_two, zero_add]
  rw [h]
  exact one_ne_zero

theorem det_rootMat_phi3 : (rootMat phi3).det = 1 := by
  refine CoordSL.det_rootMat (g := phi3) Nat.prime_three ?_ natCast_three_ne_zero
    phi3_dvd_cyclotomic
  rw [centFrame_card_f2]
  intro h
  obtain ⟨k, hk⟩ := h
  omega

theorem rootMat_phi3_pow_three : rootMat phi3 ^ 3 = 1 :=
  CoordSL.rootMat_pow_eq_one (g := phi3) Nat.prime_three natCast_three_ne_zero
    phi3_dvd_cyclotomic

theorem root_phi3_pow_three : AdjoinRoot.root phi3 ^ 3 = 1 :=
  (CoordSL.root_isPrimitiveRoot (g := phi3) Nat.prime_three natCast_three_ne_zero
    phi3_dvd_cyclotomic).pow_eq_one

theorem rootPB_phi3_dim : (rootPB phi3).dim = 2 := by
  rw [CoordSL.rootPB, AdjoinRoot.powerBasis_dim]
  change (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).natDegree = 2
  compute_degree!

theorem galExp_phi3 (u : (ZMod 3)ˣ) : u ∈ galExp phi3 root_phi3_pow_three := by
  haveI : Module.Finite F2 (AdjoinRoot phi3) := (CoordSL.rootPB phi3).finite
  haveI : Algebra.IsAlgebraic F2 (AdjoinRoot phi3) := Algebra.IsAlgebraic.of_finite F2 _
  haveI : Fintype F2 := Fintype.ofFinite F2
  have hcases : ∀ v : (ZMod 3)ˣ, v = 1 ∨ (v : ZMod 3) = 2 := by decide
  rcases hcases u with rfl | h2
  · exact (galExp phi3 root_phi3_pow_three).one_mem
  · refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic F2 (AdjoinRoot phi3), ?_⟩
    rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply]
    have hcardF : Fintype.card F2 = 2 := by
      rw [← Nat.card_eq_fintype_card, centFrame_card_f2]
    have hval : (u : ZMod 3).val = 2 := by
      rw [h2]
      exact ZMod.val_natCast_of_lt (by norm_num : 2 < 3)
    rw [hcardF, hval]

theorem natCard_adjoinRoot_phi3 : Nat.card (AdjoinRoot phi3) = 4 := by
  haveI : Module.Finite F2 (AdjoinRoot phi3) := (CoordSL.rootPB phi3).finite
  rw [Module.natCard_eq_pow_finrank (K := F2) (V := AdjoinRoot phi3), centFrame_card_f2]
  have hfr : Module.finrank F2 (AdjoinRoot phi3) = 2 := by
    rw [(CoordSL.rootPB phi3).finrank, rootPB_phi3_dim]
  rw [hfr]
  norm_num

theorem exists_frame_of_pow_three {n : ℕ} (t : SpecialLinearGroup (Fin (n + 1)) F2)
    (ht : t ^ 3 = 1) :
    ∃ (s r : ℕ) (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r)
      (A₀ : SpecialLinearGroup (Fin (n + 1)) F2) (k : Fin s → ℕ),
      t = A₀ * SLNS.nsSL ε det_rootMat_phi3 k * A₀⁻¹ := by
  obtain ⟨s, r, ε, A₀, h⟩ := CoordSL.exists_frame phi3 Nat.prime_three natCast_three_ne_zero
    phi3_dvd_cyclotomic {(t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)}
    (by
      intro x hx y hy
      rw [Set.mem_singleton_iff] at hx hy
      subst hx
      subst hy
      exact Commute.refl _)
    (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [← Matrix.SpecialLinearGroup.coe_pow, ht, Matrix.SpecialLinearGroup.coe_one])
  obtain ⟨k, hk⟩ := h _ (Set.mem_singleton _)
  refine ⟨s, r, ε, A₀, k, ?_⟩
  have h1 : t * A₀ = A₀ * SLNS.nsSL ε det_rootMat_phi3 k := Subtype.ext hk
  calc t = t * A₀ * A₀⁻¹ := by group
    _ = A₀ * SLNS.nsSL ε det_rootMat_phi3 k * A₀⁻¹ := by rw [h1]

end CFSG.StandardType.GGHalf

end
