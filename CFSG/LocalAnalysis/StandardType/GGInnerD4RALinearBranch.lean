module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4RABranchDefs
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RALabels
public import CFSG.LocalAnalysis.StandardType.GGTCJDivLin

public section

namespace CFSG.StandardType.GGInnerD4RAParts

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA

private theorem ltrra3a_char_two {K : Type} [Field K] [Finite K] {n : ℕ}
    (hcard : Nat.card K = 2 ^ n) : (2 : K) = 0 := by
  have := Fintype.ofFinite K
  obtain ⟨q, hq, r, hqp, hqcard⟩ := FiniteField.card' K
  rw [Nat.card_eq_fintype_card, hqcard] at hcard
  have hdvd : q ∣ 2 ^ n := by
    rw [← hcard]
    exact dvd_pow_self q (PNat.ne_zero r)
  have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
  subst hq2
  exact_mod_cast CharP.cast_eq_zero K 2

private theorem ltrra3a_matrix_data
    {R : Type} [Group R] [Finite R] {lab : LargeEvenLabel} {β : MulAut R}
    (hcen : Subgroup.center R = ⊥) (htag : lab.tag = .A)
    (hβ3 : β ^ 3 = 1) (hin : Y10GField.InnDiagKind R lab β) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (d : ℕ), 1 ≤ d ∧ Nat.card K = 2 ^ lab.n ∧
      ∃ (A : GL (Fin d) K) (u : MulAut (LargeEvenProj (CFSG.Open.StatedSL d K)))
        (e : R ≃* LargeEvenProj (CFSG.Open.StatedSL d K)),
        (∀ l : R, e (β l) = u (e l)) ∧
        (∀ h h' : ↥(CFSG.Open.StatedSL d K),
          (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
          u (LargeEvenProjMk (CFSG.Open.StatedSL d K) h) =
            LargeEvenProjMk (CFSG.Open.StatedSL d K) h') ∧
        MulAut.congr e β = u ∧ u ^ 3 = 1 := by
  obtain ⟨K, hKf, hKfin, d, hd, hcard, A, u, e, hαu, hgraph⟩ :=
    Y10GInnLin.innDiag_linear_data hcen (Or.inl htag) hin
  have hcard' : Nat.card K = 2 ^ lab.n := by
    simpa [canonLabel, htag] using hcard
  have hMEq : MulAut.congr e β = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ 3 = 1 := by
    rw [← hMEq, ← map_pow, hβ3, map_one]
  exact ⟨K, hKf, hKfin, d, hd, hcard', A, u, e, hαu, hgraph, hMEq, hpow⟩

private theorem ltrra3a_psl_iso
    {R : Type} [Group R] {Jb : Subgroup R} {β : MulAut R}
    {K : Type} [Field K] [Finite K] {d : ℕ} (hd : 1 ≤ d) (h2 : (2 : K) = 0)
    {n : ℕ} (hcardK : Nat.card K = 2 ^ n)
    (A : GL (Fin d) K) (u : MulAut (LargeEvenProj (CFSG.Open.StatedSL d K)))
    (e : R ≃* LargeEvenProj (CFSG.Open.StatedSL d K))
    (hgraph : ∀ h h' : ↥(CFSG.Open.StatedSL d K),
      (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (CFSG.Open.StatedSL d K) h) =
        LargeEvenProjMk (CFSG.Open.StatedSL d K) h')
    (hMEq : MulAut.congr e β = u) (hpow : u ^ 3 = 1)
    (hJb : CFSG.Assembly.IsComponentOf Jb (ggAutFixedSubgroup β)) :
    ∃ (a : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ),
      2 ≤ a ∧ Nat.card E = 2 ^ m ∧ n ∣ m ∧
      Nonempty ((↥Jb ⧸ Subgroup.center ↥Jb) ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSL a E)) := by
  have hJb' : CFSG.Assembly.IsComponentOf Jb
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) := hJb
  have hJ' : CFSG.Assembly.IsComponentOf (Jb.map e.toMonoidHom)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup u) := by
    rw [← hMEq]
    exact TCJ.tcjLin_component_transport e β hJb'
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨φ⟩⟩ :=
    TCJ.tcjLin_component_psl_fixed
      CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds h2 hd A
      (by norm_num : Nat.Prime 3) (by norm_num : (3 : ℕ) ≠ 2) u hgraph hpow
      (Jb.map e.toMonoidHom) hJ'
  let eJ : ↥Jb ≃* ↥(Jb.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective Jb e.toMonoidHom e.injective
  let eQ : (↥Jb ⧸ Subgroup.center ↥Jb) ≃*
      (↥(Jb.map e.toMonoidHom) ⧸ Subgroup.center ↥(Jb.map e.toMonoidHom)) :=
    QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
  refine ⟨a, E, hEf, hEfin, n * Module.finrank K E, ha, ?_, Dvd.intro _ rfl, ⟨eQ.trans φ⟩⟩
  rw [Module.natCard_eq_pow_finrank (K := K) (V := E), hcardK, ← pow_mul]

theorem exists_linear_component_label
    {R : Type} [Group R] [Finite R] {lab : LargeEvenLabel} {β : MulAut R}
    {Jb : Subgroup R} (hcen : Subgroup.center R = ⊥) (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .A) (hβ3 : β ^ 3 = 1) (hin : Y10GField.InnDiagKind R lab β)
    (hJb : CFSG.Assembly.IsComponentOf Jb (ggAutFixedSubgroup β)) :
    ∃ labC : LargeEvenLabel, LargeEvenInLambda2 labC ∧ labC.tag = .A ∧ lab.n ∣ labC.n ∧
      GGHasLabel labC (↥Jb ⧸ Subgroup.center ↥Jb) := by
  obtain ⟨K, hKf, hKfin, d, hd, hcard, A, u, e, -, hgraph, hMEq, hpow⟩ :=
    ltrra3a_matrix_data hcen htag hβ3 hin
  have h2 : (2 : K) = 0 := ltrra3a_char_two hcard
  obtain ⟨a, E, hEf, hEfin, m, ha, hEcard, hnm, ⟨φ⟩⟩ :=
    ltrra3a_psl_iso hd h2 hcard A u e hgraph hMEq hpow hJb
  have : IsSimpleGroup (↥Jb ⧸ Subgroup.center ↥Jb) := hJb.2.2.2
  obtain ⟨hΛC, hC⟩ := S2MathAs51600RALabels.admissible_typeA_of_psl ha hEcard φ
  exact ⟨⟨.A, a - 1, m⟩, hΛC, rfl, hnm, hC⟩

theorem raLinearBranch_holds : RALinearBranch := by
  intro R _ _ lab β Jb hcen hΛ htag hβ3 hin hJb
  obtain ⟨labC, hΛC, htagC, -, hC⟩ :=
    exists_linear_component_label hcen hΛ htag hβ3 hin hJb
  exact ⟨labC, hΛC, Or.inl htagC, hC⟩

end CFSG.StandardType.GGInnerD4RAParts

end
