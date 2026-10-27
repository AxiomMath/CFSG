module

public import CFSG.OddTranspositions.PartFour.Fourteen.ModelO4Minus
import all CFSG.OddTranspositions.PartFour.Fourteen.ModelO4Minus
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.OddTranspositions.PartFour

open Polynomial Matrix

private noncomputable abbrev quadratic {F : Type} [Semiring F] (b c : F) : F[X] :=
  X ^ 2 + C b * X + C c

private theorem hermInvol_exists_sigma {F : Type} [Field F] [CharP F 2] {b c : F}
    [CharP (AdjoinRoot (quadratic b c)) 2] (hb0 : b ≠ 0)
    (hdegpos : 0 < (quadratic b c).degree)
    (hroot : (AdjoinRoot.root (quadratic b c)) ^ 2 +
      AdjoinRoot.of (quadratic b c) b * AdjoinRoot.root (quadratic b c) +
      AdjoinRoot.of (quadratic b c) c = 0) :
    ∃ σ : AdjoinRoot (quadratic b c) ≃+* AdjoinRoot (quadratic b c),
      (∀ x, σ (σ x) = x) ∧ σ (AdjoinRoot.root (quadratic b c)) =
        AdjoinRoot.root (quadratic b c) + AdjoinRoot.of (quadratic b c) b ∧
      (∀ x : F, σ (AdjoinRoot.of (quadratic b c) x) =
        AdjoinRoot.of (quadratic b c) x) ∧
      σ (AdjoinRoot.root (quadratic b c)) ≠ AdjoinRoot.root (quadratic b c) := by
  classical
  let p : F[X] := quadratic b c
  have hpmonic : p.Monic := (Polynomial.isMonicOfDegree_add_add_two b c).monic
  let σhom : AdjoinRoot p →+* AdjoinRoot p := AdjoinRoot.lift (AdjoinRoot.of p)
    (AdjoinRoot.root p + AdjoinRoot.of p b) (by
      simp only [p, quadratic, Polynomial.eval₂_add, Polynomial.eval₂_pow,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X] at hroot ⊢
      have h2 : (2 : AdjoinRoot p) = 0 := CharTwo.two_eq_zero
      linear_combination hroot + (AdjoinRoot.of p b * AdjoinRoot.root p +
        (AdjoinRoot.of p b) ^ 2) * h2)
  have hσroot : σhom (AdjoinRoot.root p) = AdjoinRoot.root p + AdjoinRoot.of p b := by
    simp [σhom, AdjoinRoot.lift_root]
  have hσof : ∀ x : F, σhom (AdjoinRoot.of p x) = AdjoinRoot.of p x := by
    intro x
    simp [σhom, AdjoinRoot.lift_of]
  have hcomp : σhom.comp σhom = RingHom.id (AdjoinRoot p) := by
    apply AdjoinRoot.ringHom_ext
    · ext x
      simp [σhom, AdjoinRoot.lift_of]
    · simp only [RingHom.comp_apply, RingHom.id_apply, hσroot, map_add, hσof]
      have h2 : (2 : AdjoinRoot p) = 0 := CharTwo.two_eq_zero
      linear_combination (AdjoinRoot.of p b) * h2
  have hσσ : ∀ x, σhom (σhom x) = x := fun x => RingHom.congr_fun hcomp x
  let σ : AdjoinRoot p ≃+* AdjoinRoot p :=
    { toFun := σhom
      invFun := σhom
      left_inv := hσσ
      right_inv := hσσ
      map_mul' := σhom.map_mul
      map_add' := σhom.map_add }
  have hσroot' : σ (AdjoinRoot.root p) = AdjoinRoot.root p + AdjoinRoot.of p b := hσroot
  have hσof' : ∀ x : F, σ (AdjoinRoot.of p x) = AdjoinRoot.of p x := hσof
  have hof : Function.Injective (AdjoinRoot.of p) :=
    AdjoinRoot.of.injective_of_monic_of_degree_pos hpmonic (by
      rw [show p.degree = (quadratic b c).degree from rfl]
      exact hdegpos)
  have hξ : σ (AdjoinRoot.root p) ≠ AdjoinRoot.root p := by
    intro h
    have hbK : AdjoinRoot.of p b = 0 := by
      have h' : AdjoinRoot.root p + AdjoinRoot.of p b = AdjoinRoot.root p := by
        rw [← hσroot', h]
      have h'' : AdjoinRoot.root p + AdjoinRoot.of p b = AdjoinRoot.root p + 0 := by
        simpa using h'
      exact add_left_cancel h''
    exact hb0 (hof (by simpa using hbK))
  exact ⟨σ, hσσ, hσroot', hσof', hξ⟩

private theorem hermInvol_exists_coord {F : Type} [Field F] {p : F[X]}
    (hpnat : p.natDegree = 2) (hpne : p ≠ 0) :
    ∀ x : AdjoinRoot p, ∃ u w : F,
      x = AdjoinRoot.of p u + AdjoinRoot.of p w * AdjoinRoot.root p := by
  intro x
  let B : Module.Basis (Fin 2) F (AdjoinRoot p) :=
    (AdjoinRoot.powerBasisAux hpne).reindex (finCongr hpnat)
  have hB0 : B 0 = 1 := by
    simp [B, Module.Basis.reindex_apply, AdjoinRoot.powerBasisAux]
  have hB1 : B 1 = AdjoinRoot.root p := by
    simp [B, Module.Basis.reindex_apply, AdjoinRoot.powerBasisAux]
  refine ⟨B.repr x 0, B.repr x 1, ?_⟩
  calc x = ∑ i : Fin 2, B.repr x i • B i := (Module.Basis.sum_repr B x).symm
    _ = B.repr x 0 • (1 : AdjoinRoot p) + B.repr x 1 • AdjoinRoot.root p := by
      rw [Fin.sum_univ_two, hB0, hB1]
    _ = AdjoinRoot.of p (B.repr x 0) +
        AdjoinRoot.of p (B.repr x 1) * AdjoinRoot.root p := by
      simp [Algebra.smul_def, AdjoinRoot.algebraMap_eq]

private theorem hermInvol_fixed_eq_algebraMap {F : Type} [Field F] [CharP F 2] {p : F[X]}
    [CharP (AdjoinRoot p) 2] {σ : AdjoinRoot p ≃+* AdjoinRoot p}
    (b : F) (hpnat : p.natDegree = 2) (hpne : p ≠ 0) (hb0 : b ≠ 0)
    (hσroot : σ (AdjoinRoot.root p) = AdjoinRoot.root p + AdjoinRoot.of p b)
    (hσof : ∀ x : F, σ (AdjoinRoot.of p x) = AdjoinRoot.of p x)
    (hof : Function.Injective (AdjoinRoot.of p)) :
    ∀ x : AdjoinRoot p, σ x = x → ∃ u : F, x = AdjoinRoot.of p u := by
  intro x hx
  obtain ⟨u, w, hxuw⟩ := hermInvol_exists_coord hpnat hpne x
  have hσx : σ x = AdjoinRoot.of p u +
      AdjoinRoot.of p w * (AdjoinRoot.root p + AdjoinRoot.of p b) := by
    rw [hxuw, map_add, map_mul, hσof, hσof, hσroot]
  have hw : w = 0 := by
    have hEq : AdjoinRoot.of p u + AdjoinRoot.of p w * AdjoinRoot.root p =
        AdjoinRoot.of p u + AdjoinRoot.of p w *
          (AdjoinRoot.root p + AdjoinRoot.of p b) := by
      rw [← hxuw, ← hσx, hx]
    have h' := add_left_cancel hEq
    rw [mul_add] at h'
    have hbw : AdjoinRoot.of p w * AdjoinRoot.of p b = 0 := by
      have h'' : AdjoinRoot.of p w * AdjoinRoot.root p +
          AdjoinRoot.of p w * AdjoinRoot.of p b =
          AdjoinRoot.of p w * AdjoinRoot.root p + 0 := by
        simpa using h'.symm
      exact add_left_cancel h''
    have hwb : w * b = 0 := by
      apply hof
      simpa [map_mul] using hbw
    exact (mul_eq_zero.mp hwb).resolve_right hb0
  exact ⟨u, by rw [hxuw, hw, map_zero, zero_mul, add_zero]⟩

private theorem hermInvol_exists_equiv_fixedField {F : Type} [Field F] [CharP F 2] {p : F[X]}
    [Fact (Irreducible p)] [CharP (AdjoinRoot p) 2] {b c : F}
    (hroot : (AdjoinRoot.root p) ^ 2 + AdjoinRoot.of p b * AdjoinRoot.root p +
      AdjoinRoot.of p c = 0)
    (D : HermInvol (AdjoinRoot p)) (hDξ : D.ξ = AdjoinRoot.root p)
    (hDroot : D.σ (AdjoinRoot.root p) = AdjoinRoot.root p + AdjoinRoot.of p b)
    (hDof : ∀ x : F, D.σ (AdjoinRoot.of p x) = AdjoinRoot.of p x)
    (hof : Function.Injective (AdjoinRoot.of p))
    (hfixed : ∀ x : AdjoinRoot p, D.σ x = x → ∃ u : F, x = AdjoinRoot.of p u) :
    ∃ ι : F ≃+* D.F, ι b = D.b ∧ ι c = D.c := by
  classical
  let toDF : F →+* D.F :=
    { toFun := fun x => ⟨AdjoinRoot.of p x, by
        show (AdjoinRoot.of p) x ∈ RingHom.eqLocusField D.σ.toRingHom
          (RingHom.id (AdjoinRoot p))
        rw [RingHom.mem_eqLocusField]
        simpa using hDof x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hinj : Function.Injective toDF := by
    intro x y h
    apply hof
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective toDF := by
    intro y
    have hy : D.σ (y : AdjoinRoot p) = (y : AdjoinRoot p) := by
      have h := y.2
      change (y : AdjoinRoot p) ∈ RingHom.eqLocusField D.σ.toRingHom
        (RingHom.id (AdjoinRoot p)) at h
      rw [RingHom.mem_eqLocusField] at h
      simpa using h
    obtain ⟨u, hu⟩ := hfixed (y : AdjoinRoot p) hy
    exact ⟨u, Subtype.ext (hu.symm)⟩
  let ι : F ≃+* D.F := RingEquiv.ofBijective toDF ⟨hinj, hsurj⟩
  have hι_apply : ∀ x : F, ((ι x : D.F) : AdjoinRoot p) = AdjoinRoot.of p x := by
    intro x
    change ((toDF x : D.F) : AdjoinRoot p) = AdjoinRoot.of p x
    rfl
  have hbval : D.ξ + D.σ D.ξ = AdjoinRoot.of p b := by
    rw [hDξ, hDroot, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hroot' : AdjoinRoot.root p ^ 2 + AdjoinRoot.of p b * AdjoinRoot.root p =
      AdjoinRoot.of p c := by
    have h := congrArg (fun z => z + AdjoinRoot.of p c) hroot
    simpa [add_assoc, CharTwo.add_self_eq_zero] using h
  have hcval : D.ξ * D.σ D.ξ = AdjoinRoot.of p c := by
    rw [hDξ, hDroot, mul_add]
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hroot'
  refine ⟨ι, ?_, ?_⟩
  · apply Subtype.ext
    simp only [hι_apply, HermInvol.b, HermInvol.bK]
    exact hbval.symm
  · apply Subtype.ext
    simp only [hι_apply, HermInvol.c, HermInvol.cK]
    exact hcval.symm

private theorem hermInvol_natCard_adjoinRoot {F : Type} [Field F] [Finite F] {b c : F} {p : F[X]}
    (hp : p = X ^ 2 + C b * X + C c) (hpnat : p.natDegree = 2) (hpne : p ≠ 0) :
    Nat.card (AdjoinRoot p) = Nat.card F ^ 2 := by
  have hpmonic : p.Monic := by
    rw [hp]
    exact (Polynomial.isMonicOfDegree_add_add_two b c).monic
  have : Module.Finite F (AdjoinRoot p) := Polynomial.Monic.finite_adjoinRoot hpmonic
  have : Finite (AdjoinRoot p) := Module.finite_of_finite (R := F) (M := AdjoinRoot p)
  rw [Module.natCard_eq_pow_finrank (K := F) (V := AdjoinRoot p)]
  have hfin : Module.finrank F (AdjoinRoot p) = 2 := by
    rw [Module.finrank_eq_nat_card_basis
      ((AdjoinRoot.powerBasisAux hpne).reindex (finCongr hpnat))]
    simp
  rw [hfin]

theorem exists_hermInvol_of_irreducible {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ t : F, t ^ 2 + b * t + c ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (D : HermInvol K) (ι : F ≃+* D.F),
      ι b = D.b ∧ ι c = D.c ∧ Nat.card K = Nat.card F ^ 2 := by
  classical
  let p : F[X] := X ^ 2 + C b * X + C c
  have hp : p = X ^ 2 + C b * X + C c := rfl
  have hpmonic : p.Monic := (Polynomial.isMonicOfDegree_add_add_two b c).monic
  have hpnat : p.natDegree = 2 :=
    (Polynomial.isMonicOfDegree_iff' _ 2).1
      (Polynomial.isMonicOfDegree_add_add_two b c) |>.1
  have hpirr : Irreducible p := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hpnat]; decide
    · intro x hx
      apply hirr x
      simpa [p, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C] using hx
  have : Fact (Irreducible p) := ⟨hpirr⟩
  have : CharP (AdjoinRoot p) 2 :=
    CharP.of_ringHom_of_ne_zero (AdjoinRoot.of p) 2 (by norm_num)
  have hpne : p ≠ 0 := hpmonic.ne_zero
  have hdegpos : 0 < p.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hpnat]; norm_num)
  have hroot : (AdjoinRoot.root p) ^ 2 + AdjoinRoot.of p b * AdjoinRoot.root p +
      AdjoinRoot.of p c = 0 := by
    have h := AdjoinRoot.eval₂_root (f := p)
    simpa [p, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow] using h
  have hb0 : b ≠ 0 := by
    intro hb
    obtain ⟨s, hs⟩ := isSquare_of_charTwo' (R := F) c
    refine hirr s ?_
    rw [hb, hs]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (s ^ 2) * h2
  obtain ⟨σ, hσσ, hσroot, hσof, hξ⟩ :=
    hermInvol_exists_sigma hb0 hdegpos hroot
  let D : HermInvol (AdjoinRoot p) :=
    { σ := σ, σσ := hσσ, ξ := AdjoinRoot.root p, hξ := hξ }
  have hDroot : D.σ (AdjoinRoot.root p) = AdjoinRoot.root p + AdjoinRoot.of p b := hσroot
  have hDof : ∀ x : F, D.σ (AdjoinRoot.of p x) = AdjoinRoot.of p x := hσof
  have hof : Function.Injective (AdjoinRoot.of p) :=
    AdjoinRoot.of.injective_of_monic_of_degree_pos hpmonic hdegpos
  have hfixed : ∀ x : AdjoinRoot p, D.σ x = x → ∃ u : F, x = AdjoinRoot.of p u :=
    hermInvol_fixed_eq_algebraMap b hpnat hpne hb0 hDroot hDof hof
  obtain ⟨ι, hιb, hιc⟩ :=
    hermInvol_exists_equiv_fixedField hroot D rfl hDroot hDof hof hfixed
  have : Module.Finite F (AdjoinRoot p) := Polynomial.Monic.finite_adjoinRoot hpmonic
  have : Finite (AdjoinRoot p) := Module.finite_of_finite (R := F) (M := AdjoinRoot p)
  have hcard : Nat.card (AdjoinRoot p) = Nat.card F ^ 2 :=
    hermInvol_natCard_adjoinRoot hp hpnat hpne
  exact ⟨AdjoinRoot p, inferInstance, inferInstance, inferInstance, D, ι, hιb, hιc, hcard⟩

end CFSG.OddTranspositions.PartFour
