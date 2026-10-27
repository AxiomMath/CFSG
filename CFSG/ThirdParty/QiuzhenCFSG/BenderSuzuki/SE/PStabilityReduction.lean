module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStability
import all CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.theorem_6_1
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

/-!
# The p-stability reduction for groups with abelian Sylow 2-subgroups

This module keeps the Gorenstein 3.8.1--3.8.3 representation-theoretic
reduction below Section 7.  Its two-dimensional endpoint is supplied by
`two_dimensional_generated_pElements_isPGroup_of_abelianSylowTwo`.
-/

noncomputable section

open scoped Pointwise TensorProduct IsMulCommutative commutatorElement

namespace CFSG.BenderSuzuki

universe uG uF uV

private theorem hasQuadraticMinimalPolynomial_conj
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (e : V ≃ₗ[F] V) (T : V →ₗ[F] V) :
    HasQuadraticMinimalPolynomial F V (e.conj T) ↔
      HasQuadraticMinimalPolynomial F V T := by
  have hmin :
      minpoly F (e.conj T) = minpoly F T := by
    exact minpoly.algEquiv_eq (e.conjAlgEquiv F) T
  simp [HasQuadraticMinimalPolynomial, hmin]
private theorem square_zero_of_quadratic_pElement_representation
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] {p : ℕ} [Fact p.Prime] [CharP F p]
    (ρ : Representation F G V) {g : G} (hg : IsPElement (p := p) g)
    (hquad : HasQuadraticMinimalPolynomial F V (ρ g)) :
    (ρ g - 1) ^ 2 = 0 := by
  obtain ⟨r, _hrle, hrpoly⟩ :=
    minpoly_eq_X_sub_one_pow_of_pElement_representation ρ g hg
  have hXdeg : ((Polynomial.X : Polynomial F) - 1).natDegree = 1 := by
    simpa using (Polynomial.natDegree_X_sub_C (1 : F))
  have hr_eq_two : r = 2 := by
    have hdeg :
        (((Polynomial.X : Polynomial F) - 1) ^ r).natDegree = 2 := by
      simpa [HasQuadraticMinimalPolynomial, hrpoly] using hquad
    simpa [Polynomial.natDegree_pow, hXdeg] using hdeg
  have hroot := minpoly.aeval F (ρ g)
  have hroot' :
      Polynomial.aeval (ρ g) (((Polynomial.X : Polynomial F) - 1) ^ 2) = 0 := by
    simpa [hrpoly, hr_eq_two] using hroot
  simpa [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C, pow_two] using hroot'

private theorem hasQuadraticMinimalPolynomial_of_square_zero_of_ne_one
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (hSq : (T - 1) ^ 2 = 0) (hne : T ≠ 1) :
    HasQuadraticMinimalPolynomial F V T := by
  have : Nontrivial V := by
    by_contra hV
    push Not at hV
    exact hne (Subsingleton.elim _ _)
  let Q : Polynomial F := (Polynomial.X - Polynomial.C (1 : F)) ^ 2
  have hroot : Polynomial.aeval T Q = 0 := by
    dsimp [Q]
    simpa [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C, pow_two] using hSq
  have hInt : IsIntegral F T :=
    ⟨Q, (Polynomial.monic_X_sub_C (1 : F)).pow 2, hroot⟩
  have hmin_dvd : minpoly F T ∣ Q := minpoly.dvd F T hroot
  have hQ_ne : Q ≠ 0 := by
    dsimp [Q]
    exact pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero (1 : F))
  have hdeg_le : (minpoly F T).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd hmin_dvd hQ_ne
    have hXdeg : ((Polynomial.X : Polynomial F) - 1).natDegree = 1 := by
      simpa using (Polynomial.natDegree_X_sub_C (1 : F))
    simpa [Q, Polynomial.natDegree_pow, hXdeg] using this
  have hdeg_ne_one : (minpoly F T).natDegree ≠ 1 := by
    intro hdeg_one
    rcases (minpoly.natDegree_eq_one_iff (A := F) (B := Module.End F V) (x := T)).mp hdeg_one with
      ⟨a, ha⟩
    have hsq_map : algebraMap F (Module.End F V) ((a - 1) ^ 2) = 0 := by
      calc
        algebraMap F (Module.End F V) ((a - 1) ^ 2)
            = (algebraMap F (Module.End F V) (a - 1)) ^ 2 := by rw [map_pow]
        _ = (T - 1) ^ 2 := by simp [ha]
        _ = 0 := hSq
    have hsquare_zero : (a - 1) ^ 2 = 0 := by
      exact (algebraMap F (Module.End F V)).injective (by simpa using hsq_map)
    have ha1 : a = 1 := by
      have : a - 1 = 0 := eq_zero_of_pow_eq_zero hsquare_zero
      exact sub_eq_zero.mp this
    exact hne <| by
      calc
        T = algebraMap F (Module.End F V) a := ha.symm
        _ = algebraMap F (Module.End F V) 1 := by rw [ha1]
        _ = 1 := map_one (algebraMap F (Module.End F V))
  have hdeg_ne_zero : (minpoly F T).natDegree ≠ 0 := by
    intro hdeg_zero
    have hmin_one : minpoly F T = 1 := by
      have hmonic := minpoly.monic hInt
      exact Polynomial.eq_one_of_monic_natDegree_zero hmonic hdeg_zero
    have hroot' := minpoly.aeval F T
    exact (show (1 : Polynomial F) ≠ 0 from one_ne_zero) <| by
      simp [hmin_one] at hroot'
  have hdeg_eq : (minpoly F T).natDegree = 2 := by omega
  exact hdeg_eq

private theorem square_zero_of_kerRepresentation
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (g : G) (hSq : (ρ g - 1) ^ 2 = 0) :
    ((Theory.Representation.kerRepresentation ρ) (QuotientGroup.mk' ρ.ker g) - 1) ^ 2 = 0 := by
  rw [Theory.Representation.kerRepresentation_apply]
  exact hSq

private theorem square_zero_of_extendScalars
    {F F' V : Type*} [Field F] [Field F'] [Algebra F F']
    [AddCommGroup V] [Module F V] (T : Module.End F V)
    (hSq : (T - 1) ^ 2 = 0) :
    (T.baseChange F' - 1 : Module.End F' (F' ⊗[F] V)) ^ 2 = 0 := by
  have hbase :
      ((T - 1) ^ 2).baseChange F' =
        (T.baseChange F' - 1 : Module.End F' (F' ⊗[F] V)) ^ 2 := by
    rw [LinearMap.baseChange_pow, LinearMap.baseChange_sub, LinearMap.baseChange_one]
  simpa [hbase] using congrArg (fun S : Module.End F V => S.baseChange F') hSq

private theorem square_zero_of_quotientRepresentation
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (M : Subrepresentation ρ) (g : G)
    (hSq : (ρ g - 1) ^ 2 = 0) :
    ((Representation.quotient ρ M.toSubmodule M.apply_mem_toSubmodule) g - 1) ^ 2 = 0 := by
  let τ : Representation F G (V ⧸ M.toSubmodule) :=
    Representation.quotient ρ M.toSubmodule M.apply_mem_toSubmodule
  have hle :
      M.toSubmodule ≤ M.toSubmodule.comap (ρ g - 1) := by
    intro v hv
    change ρ g v - v ∈ M.toSubmodule
    exact M.toSubmodule.sub_mem (M.apply_mem_toSubmodule g hv) hv
  have hminus :
      τ g - 1 = M.toSubmodule.mapQ M.toSubmodule (ρ g - 1) hle := by
    ext v
    simp [τ, Representation.quotient_apply, LinearMap.sub_apply]
  rw [hminus, ← Submodule.mapQ_pow (p := M.toSubmodule) (f := ρ g - 1) (h := hle) (k := 2)]
  simp [hSq]

private theorem hasQuadraticMinimalPolynomial_of_quotientRepresentation_of_ne_one
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (M : Subrepresentation ρ) (g : G)
    (hSq : (ρ g - 1) ^ 2 = 0)
    (hne :
      (Representation.quotient ρ M.toSubmodule M.apply_mem_toSubmodule) g ≠ 1) :
    HasQuadraticMinimalPolynomial F (V ⧸ M.toSubmodule)
      ((Representation.quotient ρ M.toSubmodule M.apply_mem_toSubmodule) g) := by
  exact hasQuadraticMinimalPolynomial_of_square_zero_of_ne_one _
    (square_zero_of_quotientRepresentation ρ M g hSq) hne

private theorem square_zero_of_subrepresentation
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (W : Subrepresentation ρ) (g : G)
    (hSq : (ρ g - 1) ^ 2 = 0) :
    ((W.toRepresentation : Representation F G W.toSubmodule) g - 1) ^ 2 = 0 := by
  ext v
  have hv := congrArg (fun T : Module.End F V => T (v : V)) hSq
  simpa [Subrepresentation.toRepresentation, LinearMap.sub_apply,
    Module.End.mul_eq_comp, pow_two] using hv

private theorem square_zero_of_subrepresentation_quotient
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (W : Subrepresentation ρ)
    (M : Subrepresentation W.toRepresentation) (g : G)
    (hSq : (ρ g - 1) ^ 2 = 0) :
    ((Representation.quotient W.toRepresentation M.toSubmodule M.apply_mem_toSubmodule) g - 1) ^ 2 = 0 := by
  exact square_zero_of_quotientRepresentation W.toRepresentation M g
    (square_zero_of_subrepresentation ρ W g hSq)

private theorem isPGroup_of_closure_singleton_eq_top_of_isPElement
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {g : G}
    (hgen : Subgroup.closure ({g} : Set G) = ⊤) (hg : IsPElement (p := p) g) :
    IsPGroup p G := by
  rw [IsPGroup.iff_orderOf]
  intro a
  rcases hg with ⟨k, hk⟩
  have ha_closure : a ∈ Subgroup.closure ({g} : Set G) := by
    simp [hgen]
  have ha_zpowers : a ∈ Subgroup.zpowers g := by
    rwa [Subgroup.zpowers_eq_closure]
  have hdiv_order : orderOf a ∣ orderOf g :=
    orderOf_dvd_of_mem_zpowers ha_zpowers
  have hdiv_pow : orderOf a ∣ p ^ k := by
    exact dvd_trans hdiv_order (by simp [hk])
  rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 hdiv_pow with ⟨m, _hmle, hm⟩
  exact ⟨m, hm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_visible_irreducible_subquotient_of_not_isPGroup
    {F G V : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (hρ_faithful : Function.Injective ρ)
    (hnot_pgroup : ¬ IsPGroup p G) :
    ∃ (W : Subrepresentation ρ) (M : Subrepresentation W.toRepresentation) (g : G),
      Representation.IsIrreducible
        (Representation.quotient W.toRepresentation M.toSubmodule M.apply_mem_toSubmodule) ∧
      (Representation.quotient W.toRepresentation M.toSubmodule M.apply_mem_toSubmodule) g ≠ 1 := by
  -- Gorenstein's composition-factor choice.  Since `G` is not a `p`-group,
  -- choose a prime-order element of order `q ≠ p`; over the algebraic closure
  -- its action has a non-`1` eigenvalue on some vector.  The cyclic
  -- subrepresentation generated by that vector has a maximal subrepresentation
  -- avoiding the generator, and the corresponding simple quotient still sees
  -- that prime-order element nontrivially.
  classical
  have hnot_orderOf :
      ¬ ∀ g : G, ∃ k : ℕ, orderOf g = p ^ k := by
    intro h
    exact hnot_pgroup ((IsPGroup.iff_orderOf (p := p) (G := G)).2 h)
  push Not at hnot_orderOf
  rcases hnot_orderOf with ⟨g, hg_not_p_power⟩
  have hg_visible : ρ g ≠ 1 := by
    intro hgρ
    have hg_eq_one : g = 1 := hρ_faithful (by simpa using hgρ)
    exact hg_not_p_power 0 (by simp [hg_eq_one])
  -- The remaining construction is the standard composition-factor step:
  -- use an eigenvector of `ρ g` with eigenvalue different from `1`, take the
  -- cyclic subrepresentation it generates, and then a simple quotient of that
  -- cyclic module in which the generator survives.
  have hcard_not_pow : ¬ ∃ n : ℕ, Nat.card G = p ^ n := by
    intro hcard
    exact hnot_pgroup ((IsPGroup.iff_card (p := p) (G := G)).2 hcard)
  have hcard_ne_one : Nat.card G ≠ 1 := by
    intro h1
    apply hcard_not_pow
    exact ⟨0, by simpa using h1⟩
  have hexists_q_ne_p :
      ∃ q : ℕ, q.Prime ∧ q ∣ Nat.card G ∧ q ≠ p := by
    by_contra hcontra
    push Not at hcontra
    apply hcard_not_pow
    refine ⟨(Nat.card G).primeFactorsList.length, ?_⟩
    apply Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos.ne')
    intro d hd_prime hd_dvd
    exact hcontra d hd_prime hd_dvd
  obtain ⟨q, hq_prime, hq_dvd_card, hq_ne_p⟩ := hexists_q_ne_p
  let : Fintype G := Fintype.ofFinite G
  let : Fact q.Prime := ⟨hq_prime⟩
  obtain ⟨a, ha_order⟩ := exists_prime_orderOf_dvd_card q (by
    simpa [Nat.card_eq_fintype_card] using hq_dvd_card)
  have ha_visible : ρ a ≠ 1 := by
    intro hρa
    have ha_eq_one : a = 1 := hρ_faithful (by simpa using hρa)
    have : q = 1 := by simpa [ha_eq_one] using ha_order.symm
    exact hq_prime.ne_one this
  have ha_pow : (ρ a) ^ q = 1 := by
    simpa [ha_order, MonoidHom.map_pow] using congrArg ρ (pow_orderOf_eq_one a)
  have hq_ne_zero : (q : F) ≠ 0 := by
    exact CharP.cast_ne_zero_of_ne_of_prime (R := F) hq_prime (by simpa using hq_ne_p.symm)
  let : NeZero (q : F) := ⟨hq_ne_zero⟩
  have hρa_semisimple : Module.End.IsSemisimple (ρ a) := by
    have h_sep : (Polynomial.X ^ q - (1 : Polynomial F)).Separable := by
      rw [Polynomial.X_pow_sub_one_separable_iff]
      exact hq_ne_zero
    have h_aeval : Polynomial.aeval (ρ a) (Polynomial.X ^ q - (1 : Polynomial F)) = 0 := by
      simp [ha_pow]
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero h_sep.squarefree h_aeval
  have h_sub_semisimple : Module.End.IsSemisimple (ρ a - 1) := by
    simpa using
      (Module.End.isSemisimple_sub_algebraMap_iff (f := ρ a) (μ := (1 : F))).2 hρa_semisimple
  have h_has_eigen_ne_one : ∃ μ : F, Module.End.HasEigenvalue (ρ a) μ ∧ μ ≠ 1 := by
    by_contra hcontra
    push Not at hcontra
    have hsub_zero : ρ a - 1 = 0 := by
      rw [Module.End.IsSemisimple.eq_zero_iff_forall_eigenvalue (f := ρ a - 1) h_sub_semisimple]
      intro μ hμ
      rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
      have hv_eq : (ρ a - 1) v = μ • v := hv.apply_eq_smul
      have hρv : ρ a v = (μ + 1) • v := by
        calc
          ρ a v = (ρ a - 1) v + v := by
            simp [LinearMap.sub_apply]
          _ = μ • v + v := by rw [hv_eq]
          _ = (μ + 1) • v := by
            rw [add_smul, one_smul]
      have hμp1 : Module.End.HasEigenvalue (ρ a) (μ + 1) := by
        refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ?_
        rw [Module.End.hasEigenvector_iff]
        constructor
        · rw [Module.End.mem_eigenspace_iff]
          simpa using hρv
        · exact (Module.End.hasEigenvector_iff.mp hv).2
      have hμp1_eq_one : μ + 1 = 1 := hcontra (μ + 1) hμp1
      have hμp1_eq_zero_add : μ + 1 = (0 : F) + 1 := by
        simpa using hμp1_eq_one
      exact add_right_cancel hμp1_eq_zero_add
    have hρa_eq_one : ρ a = 1 := by
      simpa using sub_eq_zero.mp hsub_zero
    exact ha_visible hρa_eq_one
  rcases h_has_eigen_ne_one with ⟨μ, hμ_eigen, hμ_ne_one⟩
  rcases hμ_eigen.exists_hasEigenvector with ⟨v, hv_eigen⟩
  have hv_ne_zero : v ≠ 0 := (Module.End.hasEigenvector_iff.mp hv_eigen).2
  let vm : ρ.asModule := (ρ.asModuleEquiv.symm v)
  let mCyc : Submodule (MonoidAlgebra F G) ρ.asModule := Submodule.span (MonoidAlgebra F G) {vm}
  let W : Subrepresentation ρ := Subrepresentation.ofSubmodule' mCyc
  let Wsub : Submodule (MonoidAlgebra F G) ρ.asModule :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)) W
  have hv_mem_W : vm ∈ W.asSubmodule := by
    change vm ∈ mCyc
    exact Submodule.subset_span (by simp [vm])
  have hv_mem_W0 : v ∈ W.toSubmodule := by
    have hvm : vm ∈ W.toSubmodule :=
      Subrepresentation.mem_asSubmodule_iff.mp hv_mem_W
    have hvm_eq : vm = v := by
      rfl
    rw [hvm_eq] at hvm
    exact hvm
  have hW_ne_bot : W ≠ ⊥ := by
    intro hW_bot
    have hvbot : v ∈ (⊥ : Subrepresentation ρ).toSubmodule := by
      rw [← hW_bot]
      exact hv_mem_W0
    change v ∈ (⊥ : Submodule F V) at hvbot
    exact hv_ne_zero (by simpa using hvbot)
  let wv : W.toRepresentation.asModule :=
    ⟨vm, Subrepresentation.mem_asSubmodule_iff.mp hv_mem_W⟩
  let wv0 : W.toSubmodule := ⟨v, hv_mem_W0⟩
  have hsmul_wv (c : MonoidAlgebra F G) :
      ((W.toRepresentation.asModuleEquiv
          (c • wv : W.toRepresentation.asModule) : W.toSubmodule) : V) =
        ρ.asModuleEquiv (c • vm) := by
    induction c using MonoidAlgebra.induction_linear with
    | zero =>
        simp [wv]
    | add r s hr hs =>
        rw [add_smul, add_smul]
        simpa using congrArg₂ HAdd.hAdd hr hs
    | single g a =>
        rw [Representation.single_smul (ρ := W.toRepresentation)
          (t := a) (g := g) (v := wv)]
        rw [Representation.single_smul (ρ := ρ)
          (t := a) (g := g) (v := vm)]
        change a • (ρ g) vm = a • (ρ g) vm
        rfl
  have htop_eq_span_wv :
      (⊤ : Submodule (MonoidAlgebra F G) W.toRepresentation.asModule) =
        Submodule.span (MonoidAlgebra F G) ({wv} : Set W.toRepresentation.asModule) := by
    rw [eq_comm, Submodule.span_singleton_eq_top_iff]
    intro x
    have hx :
        (ρ.asModuleEquiv.symm ((W.toRepresentation.asModuleEquiv x : W.toSubmodule) : V) :
          ρ.asModule) ∈
          Submodule.span (MonoidAlgebra F G) ({vm} : Set ρ.asModule) := by
      have hx : x.1 ∈ W.asSubmodule := x.2
      have hxcast : ρ.asModuleEquiv.symm ↑(W.toRepresentation.asModuleEquiv x) = x.1 := by
        rfl
      rw [hxcast]
      simp [W, mCyc]
    rcases Submodule.mem_span_singleton.mp hx with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    change ((W.toRepresentation.asModuleEquiv (c • wv) : W.toSubmodule) : V) =
      ((W.toRepresentation.asModuleEquiv x : W.toSubmodule) : V)
    calc
      ((W.toRepresentation.asModuleEquiv (c • wv) : W.toSubmodule) : V)
          = ρ.asModuleEquiv (c • vm) := hsmul_wv c
      _ = ((W.toRepresentation.asModuleEquiv x : W.toSubmodule) : V) := by
          have hc' := congrArg (fun z : ρ.asModule => ρ.asModuleEquiv z) hc
          change ρ.asModuleEquiv (c • vm) =
            ((W.toRepresentation.asModuleEquiv x : W.toSubmodule) : V) at hc'
          exact hc'
  let : Module.Finite (MonoidAlgebra F G) W.toRepresentation.asModule :=
    have hfinite_top : Module.Finite (MonoidAlgebra F G)
        (⊤ : Submodule (MonoidAlgebra F G) W.toRepresentation.asModule) :=
      Module.Finite.of_fg (by
      simpa [htop_eq_span_wv] using (Submodule.fg_span_singleton wv))
    { fg_top := Module.Finite.iff_fg.mp hfinite_top }
  obtain hWtop | ⟨Msub, hMsub_coatom, hMsub_le⟩ := eq_top_or_exists_le_coatom
      (⊥ : Submodule (MonoidAlgebra F G) W.toRepresentation.asModule)
  · exfalso
    have hwv_zero : wv = 0 := by
      have hwv_mem_bot : wv ∈ (⊥ : Submodule (MonoidAlgebra F G) W.toRepresentation.asModule) := by
        rw [hWtop]
        exact Submodule.mem_top
      simpa using hwv_mem_bot
    have hvm_zero : vm = 0 := by
      simpa [wv] using congrArg Subtype.val hwv_zero
    exact hv_ne_zero (by simpa [vm] using congrArg ρ.asModuleEquiv hvm_zero)
  let M : Subrepresentation W.toRepresentation :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := W.toRepresentation)).symm Msub
  let : Module (MonoidAlgebra F G) W.toRepresentation.asModule :=
    Representation.instModuleMonoidAlgebraAsModule (ρ := W.toRepresentation)
  let : Module (MonoidAlgebra F G) W.toSubmodule :=
    Representation.instModuleMonoidAlgebraAsModule (ρ := W.toRepresentation)
  have hwv_not_mem_Msub : wv ∉ Msub := by
    intro hvmM
    have hspan_le : Submodule.span (MonoidAlgebra F G)
        ({wv} : Set W.toRepresentation.asModule) ≤ Msub := by
      simpa using (Submodule.span_singleton_le_iff_mem wv Msub).2 hvmM
    have htop_le : (⊤ : Submodule (MonoidAlgebra F G) W.toRepresentation.asModule) ≤ Msub := by
      rw [htop_eq_span_wv]
      exact hspan_le
    exact hMsub_coatom.1 (top_le_iff.mp htop_le)
  refine ⟨W, M, a, ?_, ?_⟩
  · let σ : Representation F G (W.toSubmodule ⧸ M.toSubmodule) :=
        Representation.quotient W.toRepresentation M.toSubmodule M.apply_mem_toSubmodule
    have hsimple :
        IsSimpleModule (MonoidAlgebra F G) (W.toRepresentation.asModule ⧸ Msub) := by
      exact (isSimpleModule_iff_isCoatom
        (R := MonoidAlgebra F G)
        (M := W.toRepresentation.asModule)
        (m := Msub)).2 hMsub_coatom
    let : Module (MonoidAlgebra F G) σ.asModule :=
      Representation.instModuleMonoidAlgebraAsModule (ρ := σ)
    let eσ : (W.toRepresentation.asModule ⧸ Msub) ≃ₗ[MonoidAlgebra F G] σ.asModule :=
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl
        map_add' := by intro x y; rfl
        map_smul' := by
          intro c x
          induction x using Submodule.Quotient.induction_on with
          | H z =>
              refine MonoidAlgebra.induction_linear c ?_ ?_ ?_
              · simp
              · intro r s hr hs
                simp [add_smul, hr, hs]
              · intro g a
                rw [RingHom.id_apply]
                calc
                  MonoidAlgebra.single g a • (Submodule.Quotient.mk z) =
                      (Submodule.Quotient.mk
                        (MonoidAlgebra.single g a • z) :
                        W.toRepresentation.asModule ⧸ Msub) := by
                    rw [← Submodule.Quotient.mk_smul]
                  _ =
                      (Submodule.Quotient.mk
                        (a • W.toRepresentation g
                          (W.toRepresentation.asModuleEquiv z)) :
                        W.toRepresentation.asModule ⧸ Msub) := by
                    rw [Representation.single_smul]
                  _ =
                      a • (Submodule.Quotient.mk
                        (W.toRepresentation g
                          (W.toRepresentation.asModuleEquiv z)) :
                        W.toRepresentation.asModule ⧸ Msub) := by
                    rw [Submodule.Quotient.mk_smul]
                  _ = _ := by
                    simp only [Representation.asModuleEquiv, Representation.quotient, σ, Representation.single_smul]; rfl}
    have hσ_simple : IsSimpleModule (MonoidAlgebra F G) σ.asModule := by
      exact (LinearEquiv.isSimpleModule_iff eσ).1 hsimple
    exact (Representation.irreducible_iff_isSimpleModule_asModule σ).2 hσ_simple
  · intro ha_quot
    have hμ_act_wv0 : W.toRepresentation a wv0 = μ • wv0 := by
      apply Subtype.ext
      simpa [Subrepresentation.toRepresentation, wv0] using hv_eigen.apply_eq_smul
    have hquot_apply :
        (Representation.quotient W.toRepresentation M.toSubmodule M.apply_mem_toSubmodule a)
            (Submodule.Quotient.mk wv0) =
          Submodule.Quotient.mk (W.toRepresentation a wv0) := by
      simp [Representation.quotient]
    have hfix :
        (Submodule.Quotient.mk (W.toRepresentation a wv0) :
            W.toSubmodule ⧸ M.toSubmodule) =
          Submodule.Quotient.mk wv0 := by
      have happ := congrArg (fun f : Module.End F (W.toSubmodule ⧸ M.toSubmodule) =>
          f (Submodule.Quotient.mk wv0)) ha_quot
      simpa [hquot_apply] using happ
    have hzero :
        (Submodule.Quotient.mk ((μ - 1) • wv0) :
            W.toSubmodule ⧸ M.toSubmodule) = 0 := by
      calc
        (Submodule.Quotient.mk ((μ - 1) • wv0) :
            W.toSubmodule ⧸ M.toSubmodule)
            = Submodule.Quotient.mk (μ • wv0) -
                Submodule.Quotient.mk wv0 := by
                simp [sub_smul]
        _ = Submodule.Quotient.mk (W.toRepresentation a wv0) -
                Submodule.Quotient.mk wv0 := by
              rw [hμ_act_wv0]
        _ = 0 := by
              rw [hfix]
              simp
    have hμ_sub_ne_zero : μ - 1 ≠ 0 := sub_ne_zero.mpr hμ_ne_one
    have hwv0_zero_quot :
        (Submodule.Quotient.mk wv0 :
            W.toSubmodule ⧸ M.toSubmodule) = 0 := by
      have hzero' :
          (μ - 1) •
            (Submodule.Quotient.mk wv0 : W.toSubmodule ⧸ M.toSubmodule) = 0 := by
        simpa [Submodule.Quotient.mk_smul] using hzero
      have hsmul_zero :
          (1 / (μ - 1)) •
            ((μ - 1) •
              (Submodule.Quotient.mk wv0 : W.toSubmodule ⧸ M.toSubmodule)) = 0 := by
        simp [hzero']
      simpa [smul_smul, ← map_mul, hμ_sub_ne_zero] using hsmul_zero
    have hwv0_mem_M : wv0 ∈ M.toSubmodule := by
      simpa [Submodule.Quotient.mk_eq_zero] using hwv0_zero_quot
    change wv ∈ Msub at hwv0_mem_M
    exact hwv_not_mem_Msub hwv0_mem_M

private theorem not_isPGroup_of_faithful_irreducible_visible_quotient
    {F G V : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (hρ_faithful : Function.Injective ρ)
    (hρ_irreducible : Representation.IsIrreducible ρ)
    (g : G) (hg_visible : ρ g ≠ 1) :
    ¬ IsPGroup p G := by
  -- Modular irreducible representations of finite `p`-groups in characteristic
  -- `p` are trivial.  A faithful irreducible quotient with a visible
  -- nontrivial element therefore cannot itself be a `p`-group.
  classical
  intro hG_p
  by_cases hG_nontrivial : Nontrivial G
  · have : Nontrivial G := hG_nontrivial
    have : Representation.IsIrreducible ρ := hρ_irreducible
    have : IsPGroup p G := hG_p
    have : Nontrivial V := by
      by_contra hV
      let : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
      exact hg_visible (by
        ext v
        exact Subsingleton.elim _ _)
    have hcenter_nontrivial : Nontrivial (Subgroup.center G) :=
      IsPGroup.center_nontrivial (p := p) (G := G) hG_p
    obtain ⟨z, hz_center, hz_ne_one⟩ :=
      Subgroup.exists_ne_one_of_nontrivial (Subgroup.center G)
    have hz_center' : z ∈ Submonoid.center G := by
      have hz_submonoid : z ∈ (Subgroup.center G).toSubmonoid := hz_center
      rw [Subgroup.center_toSubmonoid] at hz_submonoid
      exact hz_submonoid
    let f : Representation.IntertwiningMap ρ ρ :=
      Representation.IntertwiningMap.centralMul ρ z hz_center'
    obtain ⟨a, ha⟩ :=
      (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := ρ)).2 f
    have hz_scalar : ρ z = algebraMap F (Module.End F V) a := by
      have hlin := congrArg
        (fun φ : Representation.IntertwiningMap ρ ρ => φ.toLinearMap) ha.symm
      change ρ z = a • (1 : Module.End F V) at hlin
      exact hlin.trans (Algebra.algebraMap_eq_smul_one a).symm
    rcases hG_p z with ⟨n, hz_pow⟩
    have hρz_pow : (ρ z) ^ (p ^ n) = 1 := by
      simpa [MonoidHom.map_pow] using congrArg ρ hz_pow
    have ha_pow : a ^ (p ^ n) = 1 := by
      have hmap :
          algebraMap F (Module.End F V) (a ^ (p ^ n)) =
            algebraMap F (Module.End F V) (1 : F) := by
        calc
          algebraMap F (Module.End F V) (a ^ (p ^ n))
              = (algebraMap F (Module.End F V) a) ^ (p ^ n) := by
                rw [map_pow]
          _ = (ρ z) ^ (p ^ n) := by rw [hz_scalar]
          _ = 1 := hρz_pow
          _ = algebraMap F (Module.End F V) (1 : F) := by
                rw [map_one]
      exact (algebraMap F (Module.End F V)).injective hmap
    have ha_eq_one : a = 1 := by
      have hsub_pow :
          (a - 1) ^ (p ^ n) = (0 : F) := by
        calc
          (a - 1) ^ (p ^ n) = a ^ (p ^ n) - (1 : F) ^ (p ^ n) := by
            simpa using
              (sub_pow_char_pow (x := a) (y := (1 : F)) (p := p) (n := n))
          _ = 0 := by simp [ha_pow]
      have hsub_zero : a - 1 = 0 := eq_zero_of_pow_eq_zero hsub_pow
      exact sub_eq_zero.mp hsub_zero
    have hz_trivial : ρ z = 1 := by
      rw [hz_scalar, ha_eq_one, map_one]
    have hz_eq_one : z = 1 := hρ_faithful (by simpa using hz_trivial)
    exact hz_ne_one hz_eq_one
  · have hG_subsingleton : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_nontrivial
    have hg_eq_one : g = 1 := Subsingleton.elim g 1
    exact hg_visible (by simp [hg_eq_one])

private theorem fact_prime_of_charP_odd
    {F : Type*} [Field F] {p : ℕ} [CharP F p] (hpodd : Odd p) : Fact p.Prime := by
  refine ⟨?_⟩
  rcases CharP.char_is_prime_or_zero F p with hp | hp0
  · exact hp
  · exact False.elim (Nat.not_odd_zero (by simp [hp0] at hpodd))

section ZModPrime

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
private theorem isPGroup_of_closure_pair_in_abelian_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    {x y : G} (hx : IsPElement (p := p) x) (hy : IsPElement (p := p) y)
    (hcomm : x * y = y * x) :
    IsPGroup p (Subgroup.closure ({x, y} : Set G)) := by
  let S : Set G := ({x, y} : Set G)
  intro z
  have hstrong :
      ∀ g ∈ Subgroup.closure S,
        g ∈ Subgroup.centralizer S ∧ ∃ k : ℕ, g ^ (p ^ k) = 1 := by
    intro g hg
    refine Subgroup.closure_induction (k := S) ?_ ?_ ?_ ?_ hg
    · intro g hgS
      rcases (by simpa [S, Set.mem_insert_iff, Set.mem_singleton_iff] using hgS : g = x ∨ g = y) with
        rfl | rfl
      · refine ⟨?_, ?_⟩
        · rw [Subgroup.mem_centralizer_iff]
          intro t ht
          simp [S, Set.mem_insert_iff, Set.mem_singleton_iff] at ht ⊢
          rcases ht with rfl | rfl
          · simp
          · exact hcomm.symm
        · rcases hx with ⟨n, hn⟩
          exact ⟨n, by rw [← hn, pow_orderOf_eq_one]⟩
      · refine ⟨?_, ?_⟩
        · rw [Subgroup.mem_centralizer_iff]
          intro t ht
          simp [S, Set.mem_insert_iff, Set.mem_singleton_iff] at ht ⊢
          rcases ht with rfl | rfl
          · exact hcomm
          · simp
        · rcases hy with ⟨n, hn⟩
          exact ⟨n, by rw [← hn, pow_orderOf_eq_one]⟩
    · refine ⟨?_, ⟨0, by simp⟩⟩
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      simp
    · intro a b ha hb hPa hPb
      rcases hPa with ⟨ha_cent, ka, hka⟩
      rcases hPb with ⟨hb_cent, kb, hkb⟩
      refine ⟨(Subgroup.centralizer S).mul_mem ha_cent hb_cent, ?_⟩
      have ha_cent' : a ∈ Subgroup.centralizer (Subgroup.closure S : Set G) := by
        simpa [Subgroup.centralizer_closure] using ha_cent
      have hab : Commute a b := by
        apply Commute.symm
        change b * a = a * b
        exact (Subgroup.mem_centralizer_iff.mp ha_cent') b hb
      refine ⟨ka + kb, ?_⟩
      calc
        (a * b) ^ (p ^ (ka + kb)) = a ^ (p ^ (ka + kb)) * b ^ (p ^ (ka + kb)) := by
          simpa [hab.eq] using hab.mul_pow (p ^ (ka + kb))
        _ = ((a ^ (p ^ ka)) ^ (p ^ kb)) * ((b ^ (p ^ kb)) ^ (p ^ ka)) := by
          rw [Nat.pow_add, pow_mul, Nat.mul_comm (p ^ ka) (p ^ kb), pow_mul]
        _ = 1 := by simp [hka, hkb]
    · intro a ha hPa
      rcases hPa with ⟨ha_cent, ka, hka⟩
      refine ⟨(Subgroup.centralizer S).inv_mem ha_cent, ?_⟩
      refine ⟨ka, ?_⟩
      have := congrArg Inv.inv hka
      simpa [inv_pow] using this
  rcases (hstrong z z.2).2 with ⟨k, hk⟩
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

private theorem isSubnormal_of_normalizerCondition
    {G : Type*} [Group G] [Finite G] (hnc : NormalizerCondition G)
    (H : Subgroup G) :
    Subgroup.IsSubnormal H := by
  classical
  let μ : Subgroup G → ℕ := fun H => Nat.card G - Nat.card H
  refine (measure μ).wf.induction H ?_
  intro H ih
  by_cases htop : H = ⊤
  · simp [htop]
  · have hlt : H < Subgroup.normalizer (H : Set G) := hnc H (lt_top_iff_ne_top.mpr htop)
    have hcard_lt : Nat.card H < Nat.card (Subgroup.normalizer (H : Set G)) := by
      have hset : (H : Set G) ⊂ (Subgroup.normalizer (H : Set G) : Set G) := hlt
      simpa using
        (Set.Finite.card_lt_card
          (Set.toFinite (Subgroup.normalizer (H : Set G) : Set G)) hset)
    have hnorm_card_le : Nat.card (Subgroup.normalizer (H : Set G)) ≤ Nat.card G :=
      Subgroup.card_le_card_group (H := Subgroup.normalizer (H : Set G))
    have hnorm_subnormal : Subgroup.IsSubnormal (Subgroup.normalizer (H : Set G)) := by
      exact ih (Subgroup.normalizer (H : Set G)) (by
        change Nat.card G - Nat.card (Subgroup.normalizer (H : Set G)) < Nat.card G - Nat.card H
        omega)
    exact Subgroup.IsSubnormal.step H (Subgroup.normalizer (H : Set G)) hlt.le hnorm_subnormal inferInstance



private theorem exists_conjClass_mem_normalizer_closure_inter
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {C S : Set G} {D : Subgroup G} (hD_eq : D = Subgroup.closure S)
    (hC_conj : ∀ a ∈ C, ∀ g : G, g * a * g⁻¹ ∈ C)
    (A B : Sylow p G)
    (hS_C : S ⊆ C)
    (hS_A : S ⊆ (A : Set G)) (hD_le_B : D ≤ (B : Subgroup G))
    {w : G} (hwC : w ∈ C) (hwA : w ∈ (A : Subgroup G))
    (hw_not_B : w ∉ (B : Subgroup G)) :
    ∃ a : G, a ∈ C ∧ a ∈ (A : Subgroup G) ∧ a ∉ D ∧
      a ∈ Subgroup.normalizer D := by
  classical
  have hw_not_D : w ∉ D := fun hwD => hw_not_B (hD_le_B hwD)
  let DA : Subgroup (A : Subgroup G) := D.subgroupOf (A : Subgroup G)
  have hDA_subnormal : Subgroup.IsSubnormal DA := by
    have : Group.IsNilpotent A :=
      IsPGroup.isNilpotent (G := A) (p := p) A.isPGroup'
    exact isSubnormal_of_normalizerCondition
      (G := (A : Subgroup G)) (Group.normalizerCondition_of_isNilpotent) DA
  rcases Subgroup.IsSubnormal.exists_chain hDA_subnormal with
    ⟨m, f, hmono, hnormal, hf0, hfm⟩
  let Bad : ℕ → Prop := fun i =>
    ∃ a : G, ∃ haA : a ∈ (A : Subgroup G),
      a ∈ C ∧ (⟨a, haA⟩ : A) ∈ f i ∧ a ∉ D
  have hBad_exists : ∃ i, Bad i := by
    refine ⟨m, w, hwA, hwC, ?_, hw_not_D⟩
    simp [hfm]
  let i : ℕ := Nat.find hBad_exists
  have hiBad : Bad i := Nat.find_spec hBad_exists
  have hi_min : ∀ j < i, ¬ Bad j := by
    intro j hj
    exact Nat.find_min hBad_exists hj
  have hi_pos : 0 < i := by
    by_contra hpos
    have hi0 : i = 0 := Nat.eq_zero_of_not_pos hpos
    rcases hiBad with ⟨a, haA, _haC, hai, ha_not_D⟩
    have haD : a ∈ D := by
      have haDA : (⟨a, haA⟩ : A) ∈ DA := by
        simpa [hi0, hf0, DA] using hai
      change a ∈ D at haDA
      exact haDA
    exact ha_not_D haD
  let j : ℕ := i - 1
  have hji : j + 1 = i := by
    dsimp [j]
    omega
  have hprev_no : ¬ Bad j := hi_min j (by
    dsimp [j]
    omega)
  have hC_fprev_le_D :
      ∀ z : G, ∀ hzA : z ∈ (A : Subgroup G),
        z ∈ C → (⟨z, hzA⟩ : A) ∈ f j → z ∈ D := by
    intro z hzA hzC hzf
    by_contra hzD
    exact hprev_no ⟨z, hzA, hzC, hzf, hzD⟩
  rcases hiBad with ⟨a, haA, haC, hai, ha_not_D⟩
  have ha_fsucc : (⟨a, haA⟩ : A) ∈ f (j + 1) := by
    simpa [hji] using hai
  have hconj_gen_of_mem :
      ∀ {g : G} (hgA : g ∈ (A : Subgroup G)),
        (⟨g, hgA⟩ : A) ∈ f i →
        ∀ d : G, d ∈ S → g * d * g⁻¹ ∈ D := by
    intro g hgA hgf d hdS
    have hdA : d ∈ (A : Subgroup G) := hS_A hdS
    have hdD : d ∈ D := by
      rw [hD_eq]
      exact Subgroup.subset_closure hdS
    have hdDA : (⟨d, hdA⟩ : A) ∈ DA := by
      change d ∈ D
      exact hdD
    have hdfj : (⟨d, hdA⟩ : A) ∈ f j := by
      have hDA_le_fj : DA ≤ f j := by
        simpa [hf0] using hmono (Nat.zero_le j)
      exact hDA_le_fj hdDA
    have hdf_succ : (⟨d, hdA⟩ : A) ∈ f (j + 1) :=
      (hmono (Nat.le_succ j)) hdfj
    have hgf_succ : (⟨g, hgA⟩ : A) ∈ f (j + 1) := by
      simpa [hji] using hgf
    let gF : f (j + 1) := ⟨⟨g, hgA⟩, hgf_succ⟩
    let dF : f (j + 1) := ⟨⟨d, hdA⟩, hdf_succ⟩
    have hd_sub : dF ∈ (f j).subgroupOf (f (j + 1)) := by
      change (dF : A) ∈ f j
      exact hdfj
    have hconj_sub :
        gF * dF * gF⁻¹ ∈ (f j).subgroupOf (f (j + 1)) :=
      Subgroup.Normal.conj_mem (hnormal j) dF hd_sub gF
    have hgdgA : g * d * g⁻¹ ∈ (A : Subgroup G) :=
      A.mul_mem (A.mul_mem hgA hdA) (A.inv_mem hgA)
    have hconj_fj : (⟨g * d * g⁻¹, hgdgA⟩ : A) ∈ f j := by
      have hconj_fj' : ((gF * dF * gF⁻¹ : f (j + 1)) : A) ∈ f j := by
        change ((gF * dF * gF⁻¹ : f (j + 1)) : A) ∈ f j at hconj_sub
        exact hconj_sub
      have heq : ((gF * dF * gF⁻¹ : f (j + 1)) : A) =
          (⟨g * d * g⁻¹, hgdgA⟩ : A) := by
        ext
        simp [gF, dF, mul_assoc]
      simpa [heq] using hconj_fj'
    exact hC_fprev_le_D (g * d * g⁻¹) hgdgA (hC_conj d (hS_C hdS) g) hconj_fj
  have hconj_all_of_mem :
      ∀ {g : G} (hgA : g ∈ (A : Subgroup G)),
        (⟨g, hgA⟩ : A) ∈ f i →
        ∀ d : G, d ∈ D → g * d * g⁻¹ ∈ D := by
    intro g hgA hgf d hd
    refine Subgroup.closure_induction
      (p := fun d : G => fun _hd => g * d * g⁻¹ ∈ D) ?_ ?_ ?_ ?_
      (by simpa [hD_eq] using hd)
    · intro d hdS
      exact hconj_gen_of_mem hgA hgf d hdS
    · simp
    · intro x y _hx _hy hx hy
      simpa [mul_assoc] using D.mul_mem hx hy
    · intro x _hx hx
      simpa [mul_assoc] using D.inv_mem hx
  have hainv_i : (⟨a⁻¹, A.inv_mem haA⟩ : A) ∈ f i := by
    have hinv : ((⟨a, haA⟩ : A)⁻¹) ∈ f i := (f i).inv_mem hai
    have heq : ((⟨a, haA⟩ : A)⁻¹) = (⟨a⁻¹, A.inv_mem haA⟩ : A) := by
      ext
      simp
    simpa [heq] using hinv
  have ha_norm : a ∈ Subgroup.normalizer D := by
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · intro hd
      exact hconj_all_of_mem haA hai d hd
    · intro hd
      have hback := hconj_all_of_mem (A.inv_mem haA) hainv_i (a * d * a⁻¹) hd
      simpa [mul_assoc] using hback
  exact ⟨a, haC, haA, ha_not_D, ha_norm⟩

/-- Gorenstein, Chapter 3, Theorem 8.2, Alperin--Lyons form:
if every two elements in the conjugacy class of a `p`-element generate a
`p`-group, then that conjugacy class is contained in `O_p(G)`. -/
public theorem gorenstein_3_8_2_conjugacy_class_le_pCore
    {G : Type uG} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {x : G}
    (hx_p : IsPElement (p := p) x)
    (hpair :
      ∀ y : G, (∃ g : G, y = g * x * g⁻¹) →
        IsPGroup p (Subgroup.closure ({x, y} : Set G))) :
    ∀ z : G, (∃ g : G, z = g * x * g⁻¹) → z ∈ pCore p G := by
  -- Source: Daniel Gorenstein, *Finite Groups*, Chapter 3, Theorem 8.2,
  -- using the shorter Alperin--Lyons proof recorded in
  -- `Gorenstein/Gorenstein_3_8_3.tex`.
  classical
  suffices hx_core : x ∈ pCore p G by
    intro z hz
    rcases hz with ⟨g, rfl⟩
    exact Subgroup.Normal.conj_mem (inferInstance : (pCore p G).Normal) x hx_core g
  let Pmain :
      ∀ {G : Type uG}, [Group G] → [Finite G] →
        ∀ {x : G}, IsPElement (p := p) x →
          (∀ y : G, (∃ g : G, y = g * x * g⁻¹) →
            IsPGroup p (Subgroup.closure ({x, y} : Set G))) →
          x ∈ pCore p G := by
    suffices hmain :
        ∀ n : ℕ,
          ∀ {G : Type uG}, [Group G] → [Finite G] →
            Nat.card G = n →
            ∀ {x : G}, IsPElement (p := p) x →
              (∀ y : G, (∃ g : G, y = g * x * g⁻¹) →
              IsPGroup p (Subgroup.closure ({x, y} : Set G))) →
              x ∈ pCore p G by
      intro G _ _ x hx_p hpair
      exact hmain (Nat.card G) (G := G) rfl hx_p hpair
    intro n
    refine Nat.strongRecOn n (motive := fun n =>
        ∀ {G : Type uG}, [Group G] → [Finite G] →
          Nat.card G = n →
          ∀ {x : G}, IsPElement (p := p) x →
            (∀ y : G, (∃ g : G, y = g * x * g⁻¹) →
              IsPGroup p (Subgroup.closure ({x, y} : Set G))) →
            x ∈ pCore p G) ?_
    intro n ih G _ _ hcard x hx_p hpair
    by_cases hcore : pCore p G = ⊥
    · let C : Set G := {y : G | ∃ g : G, y = g * x * g⁻¹}
      have hxC : x ∈ C := ⟨1, by simp⟩
      have hC_conj : ∀ a ∈ C, ∀ g : G, g * a * g⁻¹ ∈ C := by
        rintro a ⟨t, rfl⟩ g
        refine ⟨g * t, ?_⟩
        simp [mul_assoc]
      have hcl_normal : (Subgroup.closure C).Normal := by
        refine ⟨?_⟩
        intro a ha g
        refine Subgroup.closure_induction
          (p := fun a : G => fun _ha => g * a * g⁻¹ ∈ Subgroup.closure C)
          ?_ ?_ ?_ ?_ ha
        · intro a ha
          exact Subgroup.subset_closure (hC_conj a ha g)
        · simp
        · intro a b _ha _hb ha hb
          simpa [mul_assoc] using (Subgroup.closure C).mul_mem ha hb
        · intro a _ha ha
          have hginv : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by
            simp [mul_assoc]
          simpa [hginv] using (Subgroup.closure C).inv_mem ha
      by_cases hcl_p : IsPGroup p (Subgroup.closure C)
      · have hle_core : Subgroup.closure C ≤ pCore p G := by
          exact le_sSup (a := Subgroup.closure C) ⟨hcl_normal, hcl_p⟩
        exact hle_core (Subgroup.subset_closure hxC)
      · have hcl_not_p : ¬ IsPGroup p (Subgroup.closure C) := hcl_p
        have hnot_C_le_sylow : ∀ P : Sylow p G, ¬ C ⊆ (P : Set G) := by
          intro P hCP
          have hcl_le : Subgroup.closure C ≤ (P : Subgroup G) :=
            (Subgroup.closure_le (K := (P : Subgroup G))).2 hCP
          exact hcl_not_p (IsPGroup.to_le P.isPGroup' hcl_le)
        let P₀ : Sylow p G := default
        have hnot_CP₀ : ¬ C ⊆ (P₀ : Set G) := hnot_C_le_sylow P₀
        have hnot_forall_mem : ¬ ∀ z ∈ C, z ∈ (P₀ : Subgroup G) := by
          intro hmem
          apply hnot_CP₀
          intro z hz
          exact hmem z hz
        push Not at hnot_forall_mem
        rcases hnot_forall_mem with ⟨y, hyC, hy_not_P₀⟩
        have hy_p : IsPElement (p := p) y := by
          rcases hyC with ⟨g, rfl⟩
          rcases hx_p with ⟨k, hk⟩
          have horder : orderOf x = orderOf (g * x * g⁻¹) := by
            exact SemiconjBy.orderOf_eq g (by
              dsimp [SemiconjBy]
              simp [mul_assoc])
          exact ⟨k, by simpa [hk] using horder.symm⟩
        have hy_zpowers_p : IsPGroup p (Subgroup.zpowers y) := by
          rw [IsPGroup.iff_orderOf]
          intro a
          have hdiv_order : orderOf (a : G) ∣ orderOf y := orderOf_dvd_of_mem_zpowers a.property
          rcases hy_p with ⟨k, hk⟩
          have hdiv : orderOf (a : G) ∣ p ^ k := hdiv_order.trans (by simp [hk])
          rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 hdiv with ⟨m, _hmle, hm⟩
          exact ⟨m, by simpa [Subgroup.orderOf_coe] using hm⟩
        rcases IsPGroup.exists_le_sylow (p := p) hy_zpowers_p with ⟨Q₀, hQ₀⟩
        have hyQ₀ : y ∈ (Q₀ : Subgroup G) := by
          exact hQ₀ (Subgroup.mem_zpowers y)
        have hPQ_nonempty :
            ({r : Sylow p G × Sylow p G |
                {z : G | z ∈ C ∧ z ∈ (r.1 : Subgroup G)} ≠
                  {z : G | z ∈ C ∧ z ∈ (r.2 : Subgroup G)}}).Nonempty := by
          refine ⟨(Q₀, P₀), ?_⟩
          intro hsets
          have : y ∈ {z : G | z ∈ C ∧ z ∈ (P₀ : Subgroup G)} := by
            simpa [hsets] using
              (show y ∈ {z : G | z ∈ C ∧ z ∈ (Q₀ : Subgroup G)} from ⟨hyC, hyQ₀⟩)
          exact hy_not_P₀ this.2
        have hPQ_finite :
            ({r : Sylow p G × Sylow p G |
                {z : G | z ∈ C ∧ z ∈ (r.1 : Subgroup G)} ≠
                  {z : G | z ∈ C ∧ z ∈ (r.2 : Subgroup G)}} :
                Set (Sylow p G × Sylow p G)).Finite :=
          Set.finite_univ.subset (by intro r _; simp)
        rcases Set.exists_max_image
            ({r : Sylow p G × Sylow p G |
                {z : G | z ∈ C ∧ z ∈ (r.1 : Subgroup G)} ≠
                  {z : G | z ∈ C ∧ z ∈ (r.2 : Subgroup G)}})
            (fun r : Sylow p G × Sylow p G =>
              Nat.card ({z : G | z ∈ C ∧ z ∈ (r.1 : Subgroup G) ∧ z ∈ (r.2 : Subgroup G)} : Set G))
            hPQ_finite hPQ_nonempty with ⟨r, hrPQ, hrmax⟩
        rcases r with ⟨P, Q⟩
        have hKcap_ne : {z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} ≠
            {z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} := hrPQ
        have hcard_CP_eq_CQ :
            Nat.card ({z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} : Set G) =
              Nat.card ({z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} : Set G) := by
          rcases MulAction.exists_smul_eq (M := G) P Q with ⟨g, hg⟩
          have hg_inv : g⁻¹ • Q = P := by
            rw [← hg]
            simp
          let e :
              ({z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} : Set G) ≃
                ({z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} : Set G) := {
            toFun z := by
              refine ⟨g * (z : G) * g⁻¹, hC_conj (z : G) z.2.1 g, ?_⟩
              have hmem : g * (z : G) * g⁻¹ ∈ ((g • P : Sylow p G) : Subgroup G) := by
                rw [Sylow.coe_subgroup_smul]
                simpa [MulAut.conj_apply] using
                  (Subgroup.smul_mem_pointwise_smul (z : G) (MulAut.conj g)
                    (P : Subgroup G) z.2.2)
              simpa [hg] using hmem
            invFun z := by
              refine ⟨g⁻¹ * (z : G) * g, ?_, ?_⟩
              · simpa using hC_conj (z : G) z.2.1 g⁻¹
              · have hmem : g⁻¹ * (z : G) * g ∈ ((g⁻¹ • Q : Sylow p G) : Subgroup G) := by
                  rw [Sylow.coe_subgroup_smul]
                  simpa [MulAut.conj_apply, mul_assoc] using
                    (Subgroup.smul_mem_pointwise_smul (z : G) (MulAut.conj g⁻¹)
                      (Q : Subgroup G) z.2.2)
                simpa [hg_inv] using hmem
            left_inv z := by
              ext
              simp [mul_assoc]
            right_inv z := by
              ext
              simp [mul_assoc]
          }
          exact Nat.card_congr e
        have hP_not_le_Q :
            ¬ {z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} ⊆
              {z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} := by
          intro hle
          apply hKcap_ne
          exact Set.Finite.eq_of_subset_of_card_le
            (Set.toFinite ({z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} : Set G)) hle
            (by rw [hcard_CP_eq_CQ])
        rcases Set.not_subset_iff_exists_mem_notMem.mp hP_not_le_Q with
          ⟨u, huPset, hu_not_Qset⟩
        rcases huPset with ⟨huC, huP⟩
        have hu_not_Q : u ∉ (Q : Subgroup G) := by
          intro huQ
          exact hu_not_Qset ⟨huC, huQ⟩
        have hQ_not_le_P :
            ¬ {z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} ⊆
              {z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} := by
          intro hle
          apply hKcap_ne.symm
          exact Set.Finite.eq_of_subset_of_card_le
            (Set.toFinite ({z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} : Set G)) hle
            (by rw [hcard_CP_eq_CQ])
        rcases Set.not_subset_iff_exists_mem_notMem.mp hQ_not_le_P with
          ⟨v, hvQset, hv_not_Pset⟩
        rcases hvQset with ⟨hvC, hvQ⟩
        have hv_not_P : v ∉ (P : Subgroup G) := by
          intro hvP
          exact hv_not_Pset ⟨hvC, hvP⟩
        let S : Set G := {z : G | z ∈ C ∧ z ∈ (P : Subgroup G) ∧ z ∈ (Q : Subgroup G)}
        let D : Subgroup G := Subgroup.closure S
        have hS_C : S ⊆ C := by
          intro z hz
          exact hz.1
        have hS_P : S ⊆ (P : Set G) := by
          intro z hz
          exact hz.2.1
        have hS_Q : S ⊆ (Q : Set G) := by
          intro z hz
          exact hz.2.2
        have hD_le_P : D ≤ (P : Subgroup G) := by
          dsimp [D]
          exact (Subgroup.closure_le (K := (P : Subgroup G))).2 hS_P
        have hD_le_Q : D ≤ (Q : Subgroup G) := by
          dsimp [D]
          exact (Subgroup.closure_le (K := (Q : Subgroup G))).2 hS_Q
        rcases exists_conjClass_mem_normalizer_closure_inter
            (p := p) (C := C) (S := S) (D := D) rfl hC_conj P Q
            hS_C hS_P hD_le_Q huC huP hu_not_Q with
          ⟨a, haC, haP, ha_not_D, ha_norm⟩
        rcases exists_conjClass_mem_normalizer_closure_inter
            (p := p) (C := C) (S := S) (D := D) rfl hC_conj Q P
            hS_C hS_Q hD_le_P hvC hvQ hv_not_P with
          ⟨b, hbC, hbQ, hb_not_D, hb_norm⟩
        have hpair_C :
            ∀ a : G, a ∈ C → ∀ b : G, b ∈ C →
              IsPGroup p (Subgroup.closure ({a, b} : Set G)) := by
          intro a ha b hb
          rcases ha with ⟨ga, hga⟩
          let y : G := ga⁻¹ * b * ga
          have hyC : ∃ g : G, y = g * x * g⁻¹ := by
            rcases hb with ⟨gb, hgb⟩
            refine ⟨ga⁻¹ * gb, ?_⟩
            simp [y, hgb, mul_assoc]
          have hxy_p : IsPGroup p (Subgroup.closure ({x, y} : Set G)) := hpair y hyC
          let c : G ≃* G := MulAut.conj ga
          have hmap_p : IsPGroup p ((Subgroup.closure ({x, y} : Set G)).map (c : G →* G)) :=
            IsPGroup.map (p := p) (H := Subgroup.closure ({x, y} : Set G)) hxy_p (c : G →* G)
          have hmap_eq :
              (Subgroup.closure ({x, y} : Set G)).map (c : G →* G) =
                Subgroup.closure ({a, b} : Set G) := by
            rw [MonoidHom.map_closure]
            congr 1
            ext z
            constructor
            · rintro ⟨w, hw, rfl⟩
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
              rcases hw with rfl | rfl
              · left
                simpa [c] using hga.symm
              · right
                simp [c, y, mul_assoc]
            · intro hz
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
              rcases hz with rfl | rfl
              · refine ⟨x, by simp, ?_⟩
                simpa [c] using hga.symm
              · refine ⟨y, by simp, ?_⟩
                simp [c, y, mul_assoc]
          rw [hmap_eq] at hmap_p
          exact hmap_p
        have hab_p : IsPGroup p (Subgroup.closure ({a, b} : Set G)) :=
          hpair_C a haC b hbC
        have hD_p : IsPGroup p D := IsPGroup.to_le P.isPGroup' hD_le_P
        have hab_le_norm :
            Subgroup.closure ({a, b} : Set G) ≤ Subgroup.normalizer (D : Set G) := by
          refine (Subgroup.closure_le (K := Subgroup.normalizer (D : Set G))).2 ?_
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact ha_norm
          · exact hb_norm
        let J : Subgroup G := D ⊔ Subgroup.closure ({a, b} : Set G)
        have hjoin_p : IsPGroup p J := by
          dsimp [J]
          exact IsPGroup.to_sup_of_normal_left'
            (G := G) (p := p) (H := D) (K := Subgroup.closure ({a, b} : Set G))
            hD_p hab_p hab_le_norm
        rcases IsPGroup.exists_le_sylow (p := p) (P := J) hjoin_p with
          ⟨R, hRle⟩
        have hD_le_R : D ≤ (R : Subgroup G) :=
          le_trans (show D ≤ J from by dsimp [J]; exact le_sup_left) hRle
        have hab_le_R : Subgroup.closure ({a, b} : Set G) ≤ (R : Subgroup G) :=
          le_trans (show Subgroup.closure ({a, b} : Set G) ≤ J from by
            dsimp [J]
            exact le_sup_right) hRle
        have haR : a ∈ (R : Subgroup G) :=
          hab_le_R (Subgroup.subset_closure (by simp))
        have hbR : b ∈ (R : Subgroup G) :=
          hab_le_R (Subgroup.subset_closure (by simp))
        have hcard_RP_gt :
            Nat.card ({z : G | z ∈ C ∧ z ∈ (P : Subgroup G) ∧ z ∈ (Q : Subgroup G)} : Set G) <
              Nat.card ({z : G | z ∈ C ∧ z ∈ (R : Subgroup G) ∧ z ∈ (P : Subgroup G)} : Set G) := by
          refine Set.Finite.card_lt_card
            (Set.toFinite ({z : G | z ∈ C ∧ z ∈ (R : Subgroup G) ∧ z ∈ (P : Subgroup G)} : Set G)) ?_
          refine ⟨?_, ?_⟩
          · intro z hz
            exact ⟨hz.1, hD_le_R (Subgroup.subset_closure (by simpa [S] using hz)), hz.2.1⟩
          · intro hsub
            have haS : a ∈ S := by
              simpa [S] using hsub ⟨haC, haR, haP⟩
            exact ha_not_D (Subgroup.subset_closure haS)
        have hR_eq_P : R = P := by
          by_contra hne
          have hbad_RP :
              (R, P) ∈
                ({r : Sylow p G × Sylow p G |
                    {z : G | z ∈ C ∧ z ∈ (r.1 : Subgroup G)} ≠
                      {z : G | z ∈ C ∧ z ∈ (r.2 : Subgroup G)}} :
                    Set (Sylow p G × Sylow p G)) := by
            intro hsets
            have hbP' : b ∈ (P : Subgroup G) := by
              have hbPset : b ∈ {z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} := by
                simpa [hsets] using
                  (show b ∈ {z : G | z ∈ C ∧ z ∈ (R : Subgroup G)} from ⟨hbC, hbR⟩)
              exact hbPset.2
            exact hb_not_D
              (Subgroup.subset_closure (by simpa [S] using ⟨⟨hbC, hbP'⟩, ⟨hbC, hbQ⟩⟩))
          have hmax := hrmax (R, P) hbad_RP
          exact (not_lt_of_ge hmax) hcard_RP_gt
        have hcard_RQ_gt :
            Nat.card ({z : G | z ∈ C ∧ z ∈ (P : Subgroup G) ∧ z ∈ (Q : Subgroup G)} : Set G) <
              Nat.card ({z : G | z ∈ C ∧ z ∈ (R : Subgroup G) ∧ z ∈ (Q : Subgroup G)} : Set G) := by
          refine Set.Finite.card_lt_card
            (Set.toFinite ({z : G | z ∈ C ∧ z ∈ (R : Subgroup G) ∧ z ∈ (Q : Subgroup G)} : Set G)) ?_
          refine ⟨?_, ?_⟩
          · intro z hz
            exact ⟨hz.1, hD_le_R (Subgroup.subset_closure (by simpa [S] using hz)), hz.2.2⟩
          · intro hsub
            have hbS : b ∈ S := by
              simpa [S] using hsub ⟨hbC, hbR, hbQ⟩
            exact hb_not_D (Subgroup.subset_closure hbS)
        have hR_eq_Q : R = Q := by
          by_contra hne
          have hbad_RQ :
              (R, Q) ∈
                ({r : Sylow p G × Sylow p G |
                    {z : G | z ∈ C ∧ z ∈ (r.1 : Subgroup G)} ≠
                      {z : G | z ∈ C ∧ z ∈ (r.2 : Subgroup G)}} :
                    Set (Sylow p G × Sylow p G)) := by
            intro hsets
            have haQ' : a ∈ (Q : Subgroup G) := by
              have haQset : a ∈ {z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} := by
                simpa [hsets] using
                  (show a ∈ {z : G | z ∈ C ∧ z ∈ (R : Subgroup G)} from ⟨haC, haR⟩)
              exact haQset.2
            exact ha_not_D
              (Subgroup.subset_closure (by simpa [S] using ⟨⟨haC, haP⟩, ⟨haC, haQ'⟩⟩))
          have hmax := hrmax (R, Q) hbad_RQ
          exact (not_lt_of_ge hmax) hcard_RQ_gt
        have hPQ : P = Q := by
          rw [← hR_eq_P, hR_eq_Q]
        exact False.elim (hKcap_ne (by rw [hPQ]))
    · let H : Subgroup G := pCore p G
      let q : G →* G ⧸ H := QuotientGroup.mk' H
      have : Finite (G ⧸ H) := inferInstance
      have hH_ne_bot : H ≠ ⊥ := by
        simpa [H] using hcore
      have hcard_lt : Nat.card (G ⧸ H) < n := by
        rw [← hcard]
        exact natCard_quotient_lt_natCard_of_ne_bot H hH_ne_bot
      have hH_p : IsPGroup p H := by
        dsimp [H]
        exact pCore_isPGroup (p := p) (G := G)
      have hxq_p : IsPElement (p := p) (q x) := by
        rcases hx_p with ⟨k, hk⟩
        have hdiv : orderOf (q x) ∣ p ^ k := by
          exact dvd_trans (orderOf_map_dvd (ψ := q) x) (by simp [hk])
        rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 hdiv with ⟨m, _hmle, hm⟩
        exact ⟨m, hm⟩
      have hpair_q :
          ∀ y : G ⧸ H, (∃ g : G ⧸ H, y = g * q x * g⁻¹) →
            IsPGroup p (Subgroup.closure ({q x, y} : Set (G ⧸ H))) := by
        intro y hy
        rcases hy with ⟨gbar, rfl⟩
        rcases QuotientGroup.mk'_surjective H gbar with ⟨g, rfl⟩
        let y : G := g * x * g⁻¹
        have hy_conj : ∃ g : G, y = g * x * g⁻¹ := ⟨g, rfl⟩
        have hy_pgroup : IsPGroup p (Subgroup.closure ({x, y} : Set G)) := hpair y hy_conj
        have hmap_p : IsPGroup p ((Subgroup.closure ({x, y} : Set G)).map q) :=
          IsPGroup.map (p := p) (H := Subgroup.closure ({x, y} : Set G)) hy_pgroup q
        have hmap_eq :
            (Subgroup.closure ({x, y} : Set G)).map q =
              Subgroup.closure ({q x, q y} : Set (G ⧸ H)) := by
          rw [MonoidHom.map_closure]
          congr 1
          ext z
          constructor
          · rintro ⟨w, hw, rfl⟩
            simp at hw
            rcases hw with rfl | rfl <;> simp
          · intro hz
            simp at hz
            rcases hz with rfl | rfl
            · exact ⟨x, by simp, rfl⟩
            · exact ⟨y, by simp, rfl⟩
        have : IsPGroup p (Subgroup.closure ({q x, q y} : Set (G ⧸ H))) := by
          rw [← hmap_eq]
          exact hmap_p
        exact this
      have hxq_core : q x ∈ pCore p (G ⧸ H) := by
        exact ih (Nat.card (G ⧸ H)) hcard_lt (G := G ⧸ H) rfl hxq_p hpair_q
      have hmap :
          H.map q = pCore p (G ⧸ H) := by
        simpa [H, q] using
          pCore_map_mk'_eq_of_normal_isPGroup (G := G) (p := p) H hH_p
      have hquot_core_bot : pCore p (G ⧸ H) = ⊥ := by
        calc
          pCore p (G ⧸ H) = H.map q := hmap.symm
          _ = ⊥ := by
            simp [q]
      have hxq_one : q x = 1 := by
        have : q x ∈ (⊥ : Subgroup (G ⧸ H)) := by
          simpa [hquot_core_bot] using hxq_core
        simpa using this
      have hxH : x ∈ H := (QuotientGroup.eq_one_iff (N := H) (x := x)).1 hxq_one
      simpa [H] using hxH
  exact Pmain hx_p hpair
omit [Fact p.Prime] in
/-- Gorenstein, Chapter 3, Theorem 8.1, odd-order replacement after the
faithful irreducible reduction.  The proof follows Gorenstein's middle step:
from a faithful irreducible module generated by two quadratic `p`-elements,
reduce to the two-dimensional endpoint above, then conclude that the generated
non-`p`-group has even order.

The remaining work in this file is to formalize the dimension-reduction part
of Gorenstein 3.8.1 inside this theorem. -/
private theorem gorenstein_3_8_1_false_of_faithful_irreducible
    {F H V : Type*} [Field F] [IsAlgClosed F] [Group H] [Finite H] [CharP F p]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F H V) (hρ_faithful : Function.Injective ρ)
    (hρ_irreducible : Representation.IsIrreducible ρ)
    (x y : H) (hgen : Subgroup.closure ({x, y} : Set H) = ⊤)
    (hpodd : Odd p)
    (hx_p : IsPElement (p := p) x) (hy_p : IsPElement (p := p) y)
    (hx_quad : HasQuadraticMinimalPolynomial F V (ρ x))
    (hy_quad : HasQuadraticMinimalPolynomial F V (ρ y))
    (hnot_pgroup : ¬ IsPGroup p H)
    (hSylow : HasAbelianSylow 2 H) : False := by
  -- Source: Daniel Gorenstein, *Finite Groups*, Chapter 3, Theorem 8.1:
  -- the kernels and images of `ρ x - 1` and `ρ y - 1` force a two-dimensional
  -- invariant subspace; irreducibility makes it the whole module.
  have hdim : Module.finrank F V = 2 := by
    classical
    let : Fact p.Prime := fact_prime_of_charP_odd (F := F) hpodd
    let A : Module.End F V := ρ x - 1
    let B : Module.End F V := ρ y - 1
    have hA_sq : A ^ 2 = 0 := by
      simpa [A] using square_zero_of_quadratic_pElement_representation
        (p := p) ρ hx_p hx_quad
    have hB_sq : B ^ 2 = 0 := by
      simpa [B] using square_zero_of_quadratic_pElement_representation
        (p := p) ρ hy_p hy_quad
    have hA_range_le_ker : LinearMap.range A ≤ LinearMap.ker A := by
      rw [LinearMap.range_le_ker_iff]
      ext v
      change (A * A) v = 0
      simpa [pow_two] using congrArg (fun T : Module.End F V => T v) hA_sq
    have hB_range_le_ker : LinearMap.range B ≤ LinearMap.ker B := by
      rw [LinearMap.range_le_ker_iff]
      ext v
      change (B * B) v = 0
      simpa [pow_two] using congrArg (fun T : Module.End F V => T v) hB_sq
    have hfixed_xy_bot : LinearMap.ker A ⊓ LinearMap.ker B = (⊥ : Submodule F V) := by
      let W : Subrepresentation ρ := {
        toSubmodule := LinearMap.ker A ⊓ LinearMap.ker B
        apply_mem_toSubmodule := by
          intro g v hv
          let K : Subgroup H := {
            carrier := {t : H | ∀ v ∈ LinearMap.ker A ⊓ LinearMap.ker B, ρ t v = v}
            one_mem' := by
              intro v hv
              simp
            mul_mem' := by
              intro g h hg hh v hv
              calc
                ρ (g * h) v = ρ g (ρ h v) := by
                  simp [map_mul, Module.End.mul_eq_comp]
                _ = ρ g v := by rw [hh v hv]
                _ = v := hg v hv
            inv_mem' := by
              intro g hg v hv
              calc
                ρ g⁻¹ v = ρ g⁻¹ (ρ g v) := by rw [hg v hv]
                _ = v := by
                  simp [← Module.End.mul_apply, ← map_mul]
          }
          have hclosure_le_K : Subgroup.closure ({x, y} : Set H) ≤ K := by
            refine (Subgroup.closure_le (K := K)).2 ?_
            intro g hg
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
            rcases hg with hgx | hgy
            · intro v hv
              have hvA : A v = 0 := hv.1
              have hAv : ρ g v - v = 0 := by simpa [A, hgx] using hvA
              exact sub_eq_zero.mp hAv
            · intro v hv
              have hvB : B v = 0 := hv.2
              have hBv : ρ g v - v = 0 := by simpa [B, hgy] using hvB
              exact sub_eq_zero.mp hBv
          have hgK : g ∈ K := by
            have hg_closure : g ∈ Subgroup.closure ({x, y} : Set H) := by
              simp [hgen]
            exact hclosure_le_K hg_closure
          have hfix : ρ g v = v := hgK v hv
          simpa [hfix] using hv
      }
      rcases hρ_irreducible.eq_bot_or_eq_top W with hW_bot | hW_top
      · have h := congrArg Subrepresentation.toSubmodule hW_bot
        change (LinearMap.ker A ⊓ LinearMap.ker B) = (⊥ : Submodule F V) at h
        exact h
      · have hx_ker : x ∈ ρ.ker := by
          rw [MonoidHom.mem_ker]
          ext v
          have hv : v ∈ (LinearMap.ker A ⊓ LinearMap.ker B : Submodule F V) := by
            have : v ∈ W.toSubmodule := by
              rw [hW_top]
              exact Submodule.mem_top
            simpa [W] using this
          have hvA : A v = 0 := hv.1
          have hAv : ρ x v - v = 0 := by simpa [A] using hvA
          exact sub_eq_zero.mp hAv
        have hy_ker : y ∈ ρ.ker := by
          rw [MonoidHom.mem_ker]
          ext v
          have hv : v ∈ (LinearMap.ker A ⊓ LinearMap.ker B : Submodule F V) := by
            have : v ∈ W.toSubmodule := by
              rw [hW_top]
              exact Submodule.mem_top
            simpa [W] using this
          have hvB : B v = 0 := hv.2
          have hBv : ρ y v - v = 0 := by simpa [B] using hvB
          exact sub_eq_zero.mp hBv
        have hclosure_le_ker : Subgroup.closure ({x, y} : Set H) ≤ ρ.ker := by
          exact (Subgroup.closure_le (K := ρ.ker)).2 (by
            intro z hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
            rcases hz with rfl | rfl
            · exact hx_ker
            · exact hy_ker)
        have hker_top : ρ.ker = ⊤ := by
          exact top_le_iff.mp (by
            intro g _hg
            have hg_closure : g ∈ Subgroup.closure ({x, y} : Set H) := by
              simp [hgen]
            exact hclosure_le_ker hg_closure)
        have hρ_trivial : ∀ g : H, g = 1 := by
          intro g
          apply hρ_faithful
          have hg : g ∈ ρ.ker := by
            rw [hker_top]
            exact Subgroup.mem_top g
          simpa [MonoidHom.mem_ker] using hg
        have hH_p : IsPGroup p H := by
          intro g
          refine ⟨0, ?_⟩
          simp [hρ_trivial g]
        exact False.elim (hnot_pgroup hH_p)
    have hA_range_ne_bot : LinearMap.range A ≠ (⊥ : Submodule F V) := by
      intro hA_bot
      have hA_zero : A = 0 := LinearMap.range_eq_bot.mp hA_bot
      have hx_ker : x ∈ ρ.ker := by
        rw [MonoidHom.mem_ker]
        exact sub_eq_zero.mp hA_zero
      have hx_eq_one : x = 1 := by
        apply hρ_faithful
        simpa [MonoidHom.mem_ker] using hx_ker
      subst hx_eq_one
      have hnot_quad : ¬ HasQuadraticMinimalPolynomial F V (ρ 1) := by
        intro hquad
        have hroot :
            Polynomial.aeval (ρ 1) (Polynomial.X - Polynomial.C (1 : F)) = 0 := by
          simp
        have hmin_dvd :
            minpoly F (ρ 1) ∣ (Polynomial.X - Polynomial.C (1 : F)) :=
          minpoly.dvd F (ρ 1) hroot
        have hlin_ne : (Polynomial.X - Polynomial.C (1 : F) : Polynomial F) ≠ 0 :=
          Polynomial.X_sub_C_ne_zero (1 : F)
        have hdeg_le : (minpoly F (ρ 1)).natDegree ≤ 1 := by
          have hdeg_le' :
              (minpoly F (ρ 1)).natDegree ≤
                (Polynomial.X - Polynomial.C (1 : F)).natDegree :=
            Polynomial.natDegree_le_of_dvd hmin_dvd hlin_ne
          exact hdeg_le'.trans_eq (Polynomial.natDegree_X_sub_C (1 : F))
        have htwo_le : 2 ≤ (1 : ℕ) := by
          calc
            2 = (minpoly F (ρ 1)).natDegree := by
              simpa [HasQuadraticMinimalPolynomial] using hquad.symm
            _ ≤ 1 := hdeg_le
        omega
      exact hnot_quad hx_quad
    let BA : Module.End F (LinearMap.range A) :=
      (LinearMap.codRestrict (LinearMap.range A)
        (A.comp (B.comp (LinearMap.range A).subtype)) (by
          intro a
          rcases a with ⟨v, hv⟩
          rcases hv with ⟨u, rfl⟩
          exact ⟨B (A u), rfl⟩))
    have : Nontrivial (LinearMap.range A) := by
      exact (Submodule.nontrivial_iff_ne_bot (p := LinearMap.range A)).2 hA_range_ne_bot
    rcases Module.End.exists_eigenvalue BA with ⟨c, hc⟩
    rcases hc.exists_hasEigenvector with ⟨a, haeig⟩
    have ha_ne_zero : a ≠ 0 := haeig.2
    have hBAa : BA a = c • a := haeig.apply_eq_smul
    let v : V := a
    have hv_range : v ∈ LinearMap.range A := a.2
    have hv_ne_zero : v ≠ 0 := by
      intro hv
      exact ha_ne_zero (Subtype.ext hv)
    let Wlin : Submodule F V := Submodule.span F ({v, B v} : Set V)
    have hv_mem_W : v ∈ Wlin := by
      exact Submodule.subset_span (by simp)
    have hBv_mem_W : B v ∈ Wlin := by
      exact Submodule.subset_span (by simp)
    have hW_stable_x : Wlin ≤ Wlin.comap (ρ x) := by
      rw [Submodule.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · have hAv : A v = 0 := hA_range_le_ker hv_range
        have hρxv : ρ x v = v := by
          have hAv' : ρ x v - v = 0 := by simpa [A] using hAv
          exact sub_eq_zero.mp hAv'
        change ρ x v ∈ Wlin
        simpa [hρxv] using hv_mem_W
      · have hABv : A (B v) = c • v := by
          have := congrArg Subtype.val hBAa
          simpa [BA, v] using this
        have hρxBv : ρ x (B v) = B v + c • v := by
          have h : ρ x (B v) - B v = c • v := by
            simpa [A] using hABv
          have h' : ρ x (B v) = c • v + B v := eq_add_of_sub_eq h
          simpa [add_comm] using h'
        change ρ x (B v) ∈ Wlin
        rw [hρxBv]
        exact Wlin.add_mem hBv_mem_W (Wlin.smul_mem c hv_mem_W)
    have hW_stable_y : Wlin ≤ Wlin.comap (ρ y) := by
      rw [Submodule.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · have hρyv : ρ y v = v + B v := by
          have h : ρ y v - v = B v := by simp [B]
          have h' : ρ y v = B v + v := eq_add_of_sub_eq h
          simpa [add_comm] using h'
        change ρ y v ∈ Wlin
        rw [hρyv]
        exact Wlin.add_mem hv_mem_W hBv_mem_W
      · have hBBv : B (B v) = 0 := by
          change (B * B) v = 0
          simpa [pow_two] using congrArg (fun T : Module.End F V => T v) hB_sq
        have hρyBv : ρ y (B v) = B v := by
          have h : ρ y (B v) - B v = 0 := by simpa [B] using hBBv
          exact sub_eq_zero.mp h
        change ρ y (B v) ∈ Wlin
        simpa [hρyBv] using hBv_mem_W
    have hW_stable : ∀ g : H, Wlin ≤ Wlin.comap (ρ g) := by
      intro g
      let K : Subgroup H := {
        carrier := {g : H | Wlin ≤ Wlin.comap (ρ g) ∧ Wlin ≤ Wlin.comap (ρ g⁻¹)}
        one_mem' := by
          constructor <;> intro w hw <;> simpa using hw
        mul_mem' := by
          intro g h hg hh
          constructor
          · intro w hw
            have hhw : ρ h w ∈ Wlin := hh.1 hw
            have hghw : ρ g (ρ h w) ∈ Wlin := hg.1 hhw
            simpa [map_mul, Module.End.mul_eq_comp] using hghw
          · intro w hw
            have hgw : ρ g⁻¹ w ∈ Wlin := hg.2 hw
            have hhgw : ρ h⁻¹ (ρ g⁻¹ w) ∈ Wlin := hh.2 hgw
            simpa [map_mul, Module.End.mul_eq_comp] using hhgw
        inv_mem' := by
          intro g hg
          constructor
          · simpa using hg.2
          · simpa using hg.1
      }
      have hW_stable_x_inv : Wlin ≤ Wlin.comap (ρ x⁻¹) := by
        intro w hw
        have hρxw : ρ x w ∈ Wlin := hW_stable_x hw
        have hAw_mem : A w ∈ Wlin := by
          have hAw : A w = ρ x w - w := by simp [A]
          rw [hAw]
          exact Wlin.sub_mem hρxw hw
        have hA2w : A (A w) = 0 := by
          change (A * A) w = 0
          simpa [pow_two] using congrArg (fun T : Module.End F V => T w) hA_sq
        have hx_calc : ρ x (w - A w) = w := by
          have hρx_sub : ρ x (w - A w) - (w - A w) = A (w - A w) := by
            simp [A]
          have hA_sub : A (w - A w) = A w := by
            simp [map_sub, hA2w]
          have hρx_sub' : ρ x (w - A w) - (w - A w) = A w := by
            simpa [hA_sub] using hρx_sub
          have hρx_eq : ρ x (w - A w) = A w + (w - A w) := eq_add_of_sub_eq hρx_sub'
          simpa [add_comm, add_left_comm, add_assoc] using hρx_eq
        have hxinv_eq : ρ x⁻¹ w = w - A w := by
          have hmul : ρ x⁻¹ * ρ x = 1 := by
            simp [← map_mul]
          have hAinv : ρ x⁻¹ * A = ρ x⁻¹ * ρ x - ρ x⁻¹ := by
            simp [A, sub_eq_add_neg, mul_add]
          calc
            ρ x⁻¹ w = (ρ x⁻¹ * ρ x) w - (ρ x⁻¹ * A) w := by
              simp [A, Module.End.mul_eq_comp, sub_eq_add_neg, add_comm]
            _ = w - (ρ x⁻¹ * A) w := by simp [hmul]
            _ = w - A w := by
              congr 1
              change ρ x⁻¹ (A w) = A w
              have hAkw : A w ∈ LinearMap.ker A := hA_range_le_ker ⟨w, rfl⟩
              have hAkw_zero : ρ x (A w) - A w = 0 := by simpa [A] using hAkw
              have hAkw_fix : ρ x (A w) = A w := sub_eq_zero.mp hAkw_zero
              have hfixInv : ρ x⁻¹ (A w) = A w := by
                have happ := congrArg (fun z : V => ρ x⁻¹ z) hAkw_fix
                have happ' : ρ x⁻¹ (ρ x (A w)) = ρ x⁻¹ (A w) := by
                  simpa using happ
                have hleft : ρ x⁻¹ (ρ x (A w)) = A w := by
                  change (ρ x⁻¹ * ρ x) (A w) = A w
                  simp [← map_mul]
                rw [hleft] at happ'
                exact happ'.symm
              exact hfixInv
        change ρ x⁻¹ w ∈ Wlin
        rw [hxinv_eq]
        exact Wlin.sub_mem hw hAw_mem
      have hW_stable_y_inv : Wlin ≤ Wlin.comap (ρ y⁻¹) := by
        intro w hw
        have hρyw : ρ y w ∈ Wlin := hW_stable_y hw
        have hBw_mem : B w ∈ Wlin := by
          have hBw : B w = ρ y w - w := by simp [B]
          rw [hBw]
          exact Wlin.sub_mem hρyw hw
        have hB2w : B (B w) = 0 := by
          change (B * B) w = 0
          simpa [pow_two] using congrArg (fun T : Module.End F V => T w) hB_sq
        have hy_calc : ρ y (w - B w) = w := by
          have hρy_sub : ρ y (w - B w) - (w - B w) = B (w - B w) := by
            simp [B]
          have hB_sub : B (w - B w) = B w := by
            simp [map_sub, hB2w]
          have hρy_sub' : ρ y (w - B w) - (w - B w) = B w := by
            simpa [hB_sub] using hρy_sub
          have hρy_eq : ρ y (w - B w) = B w + (w - B w) := eq_add_of_sub_eq hρy_sub'
          simpa [add_comm, add_left_comm, add_assoc] using hρy_eq
        have hyinv_eq : ρ y⁻¹ w = w - B w := by
          have hmul : ρ y⁻¹ * ρ y = 1 := by
            simp [← map_mul]
          calc
            ρ y⁻¹ w = (ρ y⁻¹ * ρ y) w - (ρ y⁻¹ * B) w := by
              simp [B, Module.End.mul_eq_comp, sub_eq_add_neg, add_comm]
            _ = w - (ρ y⁻¹ * B) w := by simp [hmul]
            _ = w - B w := by
              congr 1
              change ρ y⁻¹ (B w) = B w
              have hBkw : B w ∈ LinearMap.ker B := hB_range_le_ker ⟨w, rfl⟩
              have hBkw_zero : ρ y (B w) - B w = 0 := by simpa [B] using hBkw
              have hBkw_fix : ρ y (B w) = B w := sub_eq_zero.mp hBkw_zero
              have hfixInv : ρ y⁻¹ (B w) = B w := by
                have happ := congrArg (fun z : V => ρ y⁻¹ z) hBkw_fix
                have happ' : ρ y⁻¹ (ρ y (B w)) = ρ y⁻¹ (B w) := by
                  simpa using happ
                have hleft : ρ y⁻¹ (ρ y (B w)) = B w := by
                  change (ρ y⁻¹ * ρ y) (B w) = B w
                  simp [← map_mul]
                rw [hleft] at happ'
                exact happ'.symm
              exact hfixInv
        change ρ y⁻¹ w ∈ Wlin
        rw [hyinv_eq]
        exact Wlin.sub_mem hw hBw_mem
      have hclosure_le_K :
          Subgroup.closure ({x, y} : Set H) ≤ K := by
        refine (Subgroup.closure_le (K := K)).2 ?_
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact ⟨hW_stable_x, hW_stable_x_inv⟩
        · exact ⟨hW_stable_y, hW_stable_y_inv⟩
      have hgK : g ∈ K := by
        have hg_closure : g ∈ Subgroup.closure ({x, y} : Set H) := by
          simp [hgen]
        exact hclosure_le_K hg_closure
      exact hgK.1
    let W : Subrepresentation ρ := {
      toSubmodule := Wlin
      apply_mem_toSubmodule := by
        intro g w hw
        exact hW_stable g hw
    }
    have hW_ne_bot : W ≠ ⊥ := by
      intro hW_bot
      have hv_zero : v = 0 := by
        have hvW : v ∈ W.toSubmodule := by simpa [W] using hv_mem_W
        rw [hW_bot] at hvW
        change v ∈ (⊥ : Submodule F V) at hvW
        simpa using hvW
      exact hv_ne_zero hv_zero
    have hW_top : W = ⊤ := by
      rcases hρ_irreducible.eq_bot_or_eq_top W with hbot | htop
      · exact False.elim (hW_ne_bot hbot)
      · exact htop
    have htop_eq : Wlin = ⊤ := by
      have hsub := congrArg Subrepresentation.toSubmodule hW_top
      change Wlin = (⊤ : Submodule F V) at hsub
      exact hsub
    have hfin_le_two : Module.finrank F V ≤ 2 := by
      have hspan_le :
          Module.finrank F Wlin ≤ 2 := by
        calc
          Module.finrank F Wlin =
              Module.finrank F (Submodule.span F ({v, B v} : Set V)) := rfl
          _ ≤ ({v, B v} : Set V).toFinset.card := finrank_span_le_card ({v, B v} : Set V)
          _ ≤ 2 := by
            classical
            simpa using (Finset.card_le_two (a := v) (b := B v))
      have hfin_eq : Module.finrank F Wlin = Module.finrank F V :=
        LinearEquiv.finrank_eq (LinearEquiv.ofTop (R := F) (p := Wlin) htop_eq)
      linarith
    have hBv_ne_zero : B v ≠ 0 := by
      intro hBv
      have hv_common : v ∈ LinearMap.ker A ⊓ LinearMap.ker B := by
        constructor
        · exact hA_range_le_ker hv_range
        · simpa [LinearMap.mem_ker] using hBv
      have hv_zero : v = 0 := by
        have : v ∈ (⊥ : Submodule F V) := by
          simpa [hfixed_xy_bot] using hv_common
        simpa using this
      exact hv_ne_zero hv_zero
    have hlin_ind : LinearIndependent F ![v, B v] := by
      rw [LinearIndependent.pair_iff' hv_ne_zero]
      intro a ha
      have hA_Bv : A (B v) = c • v := by
        have := congrArg Subtype.val hBAa
        simpa [BA, v] using this
      have hA_eq : A (a • v) = 0 := by
        calc
          A (a • v) = a • A v := by simp
          _ = 0 := by
            have hAv : A v = 0 := hA_range_le_ker hv_range
            simp [hAv]
      have hAvanish : c • v = 0 := by
        calc
          c • v = A (B v) := hA_Bv.symm
          _ = A (a • v) := by rw [ha]
          _ = 0 := hA_eq
      have hc_zero : c = 0 := by
        by_contra hcne
        exact hv_ne_zero ((smul_eq_zero.mp hAvanish).resolve_left hcne)
      have hA_Bv_zero : A (B v) = 0 := by simpa [hc_zero] using hA_Bv
      have hBv_common : B v ∈ LinearMap.ker A ⊓ LinearMap.ker B := by
        constructor
        · simpa [LinearMap.mem_ker] using hA_Bv_zero
        · exact hB_range_le_ker ⟨v, rfl⟩
      have hBv_zero' : B v = 0 := by
        have : B v ∈ (⊥ : Submodule F V) := by
          simpa [hfixed_xy_bot] using hBv_common
        simpa using this
      exact hBv_ne_zero hBv_zero'
    have htwo_le_fin : 2 ≤ Module.finrank F V := by
      have hcard_le := hlin_ind.fintype_card_le_finrank
      simpa using hcard_le
    omega
  let : Fact p.Prime := fact_prime_of_charP_odd (F := F) hpodd
  exact hnot_pgroup <|
    two_dimensional_generated_pElements_isPGroup_of_abelianSylowTwo
      (p := p) ρ hρ_faithful hdim x y hgen hpodd hx_p hy_p hSylow

set_option maxHeartbeats 800000

omit [Fact p.Prime] in
/-- Scalar-extension and composition-factor reduction used in Gorenstein,
Chapter 3, Theorem 8.3: from a characteristic-`p` representation, pass to a
faithful irreducible composition factor where Gorenstein 3.8.1 applies, and
descend only the group-theoretic even-quotient conclusion.

This statement is only used for the faithful representation obtained from
non-`p`-stability; the proof below keeps Gorenstein's reduction explicit rather
than treating arbitrary representations as if they were already irreducible. -/
private theorem gorenstein_3_8_1_false_after_composition_factor
    {F H V : Type*} [Field F] [Group H] [Finite H] [CharP F p]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F H V) (hρ_faithful : Function.Injective ρ)
    (x y : H) (hgen : Subgroup.closure ({x, y} : Set H) = ⊤)
    (hpodd : Odd p)
    (hx_p : IsPElement (p := p) x) (hy_p : IsPElement (p := p) y)
    (hx_quad : HasQuadraticMinimalPolynomial F V (ρ x))
    (hy_quad : HasQuadraticMinimalPolynomial F V (ρ y))
    (hnot_pgroup : ¬ IsPGroup p H)
    (hSylow : HasAbelianSylow 2 H) : False := by
  -- Source: Daniel Gorenstein, *Finite Groups*, Chapter 3, Theorem 8.3:
  -- choose a nontrivial irreducible composition factor of the restricted
  -- module, quotient `H` by its kernel, and apply the faithful irreducible
  -- form of Theorem 8.1.
  classical
  let F' := AlgebraicClosure F
  let V' := F' ⊗[F] V
  have : FiniteDimensional F' V' := by
    dsimp [V']
    exact Module.Finite.base_change (R := F) (A := F') (M := V)
  let ρ' : Representation F' H V' := Theory.Representation.extendScalars F' ρ
  have hρ'_faithful : Function.Injective ρ' := by
    exact (Theory.Representation.extendScalars_faithful_iff F' ρ).mp hρ_faithful

  -- Gorenstein first passes to an algebraically closed coefficient field.
  have hx'_quad : HasQuadraticMinimalPolynomial F' V' (ρ' x) := by
    let : Fact p.Prime := fact_prime_of_charP_odd (F := F) hpodd
    have hx_sq : (ρ x - 1) ^ 2 = 0 :=
      square_zero_of_quadratic_pElement_representation (p := p) ρ hx_p hx_quad
    have hx'_sq : (ρ' x - 1) ^ 2 = 0 := by
      have h := square_zero_of_extendScalars (F' := F') (T := ρ x) hx_sq
      change (ρ' x - 1) ^ 2 = 0 at h
      exact h
    have hx'_ne : ρ' x ≠ 1 := by
      intro hx'_one
      have hx_one : x = 1 := by
        apply hρ'_faithful
        simpa using hx'_one
      subst hx_one
      have hnot_quad : ¬ HasQuadraticMinimalPolynomial F V (ρ 1) := by
        intro hquad
        have hroot :
            Polynomial.aeval (ρ 1) (Polynomial.X - Polynomial.C (1 : F)) = 0 := by
          simp
        have hmin_dvd :
            minpoly F (ρ 1) ∣ (Polynomial.X - Polynomial.C (1 : F)) :=
          minpoly.dvd F (ρ 1) hroot
        have hlin_ne : (Polynomial.X - Polynomial.C (1 : F) : Polynomial F) ≠ 0 :=
          Polynomial.X_sub_C_ne_zero (1 : F)
        have hdeg_le : (minpoly F (ρ 1)).natDegree ≤ 1 := by
          have hdeg_le' :
              (minpoly F (ρ 1)).natDegree ≤
                (Polynomial.X - Polynomial.C (1 : F)).natDegree :=
            Polynomial.natDegree_le_of_dvd hmin_dvd hlin_ne
          exact hdeg_le'.trans_eq (Polynomial.natDegree_X_sub_C (1 : F))
        have htwo_le : 2 ≤ (1 : ℕ) := by
          calc
            2 = (minpoly F (ρ 1)).natDegree := by
              simpa [HasQuadraticMinimalPolynomial] using hquad.symm
            _ ≤ 1 := hdeg_le
        omega
      exact hnot_quad hx_quad
    exact hasQuadraticMinimalPolynomial_of_square_zero_of_ne_one (ρ' x) hx'_sq hx'_ne
  have hy'_quad : HasQuadraticMinimalPolynomial F' V' (ρ' y) := by
    let : Fact p.Prime := fact_prime_of_charP_odd (F := F) hpodd
    have hy_sq : (ρ y - 1) ^ 2 = 0 :=
      square_zero_of_quadratic_pElement_representation (p := p) ρ hy_p hy_quad
    have hy'_sq : (ρ' y - 1) ^ 2 = 0 := by
      have h := square_zero_of_extendScalars (F' := F') (T := ρ y) hy_sq
      change (ρ' y - 1) ^ 2 = 0 at h
      exact h
    have hy'_ne : ρ' y ≠ 1 := by
      intro hy'_one
      have hy_one : y = 1 := by
        apply hρ'_faithful
        simpa using hy'_one
      subst hy_one
      have hnot_quad : ¬ HasQuadraticMinimalPolynomial F V (ρ 1) := by
        intro hquad
        have hroot :
            Polynomial.aeval (ρ 1) (Polynomial.X - Polynomial.C (1 : F)) = 0 := by
          simp
        have hmin_dvd :
            minpoly F (ρ 1) ∣ (Polynomial.X - Polynomial.C (1 : F)) :=
          minpoly.dvd F (ρ 1) hroot
        have hlin_ne : (Polynomial.X - Polynomial.C (1 : F) : Polynomial F) ≠ 0 :=
          Polynomial.X_sub_C_ne_zero (1 : F)
        have hdeg_le : (minpoly F (ρ 1)).natDegree ≤ 1 := by
          have hdeg_le' :
              (minpoly F (ρ 1)).natDegree ≤
                (Polynomial.X - Polynomial.C (1 : F)).natDegree :=
            Polynomial.natDegree_le_of_dvd hmin_dvd hlin_ne
          exact hdeg_le'.trans_eq (Polynomial.natDegree_X_sub_C (1 : F))
        have htwo_le : 2 ≤ (1 : ℕ) := by
          calc
            2 = (minpoly F (ρ 1)).natDegree := by
              simpa [HasQuadraticMinimalPolynomial] using hquad.symm
            _ ≤ 1 := hdeg_le
        omega
      exact hnot_quad hy_quad
    exact hasQuadraticMinimalPolynomial_of_square_zero_of_ne_one (ρ' y) hy'_sq hy'_ne

  -- Next choose an irreducible composition factor on which the action is
  -- nontrivial.  This is Gorenstein's composition-factor step.
  let : Fact p.Prime := fact_prime_of_charP_odd (F := F) hpodd
  obtain ⟨W, M, g0, hM_irreducible, hg0_not_ker_M⟩ :=
    exists_visible_irreducible_subquotient_of_not_isPGroup
      (p := p) ρ' hρ'_faithful hnot_pgroup
  let σ := Representation.quotient (k := F') (G := H) (V := W.toSubmodule)
    W.toRepresentation M.toSubmodule M.apply_mem_toSubmodule
  have hσ_irreducible : Representation.IsIrreducible σ := by
    simpa [σ] using hM_irreducible
  have : Representation.IsIrreducible σ := hσ_irreducible
  let := finiteDimensional_of_irreducible_finite_group (ρ := σ) hσ_irreducible

  -- The composition factor is then made faithful by quotienting by its kernel.
  let σq := Theory.Representation.kerRepresentation σ
  have hσq_faithful : Function.Injective σq :=
    Theory.Representation.kerRepresentation_faithful σ
  have hσq_irreducible : Representation.IsIrreducible σq := by
    infer_instance

  let xq : H ⧸ σ.ker := QuotientGroup.mk' σ.ker x
  let yq : H ⧸ σ.ker := QuotientGroup.mk' σ.ker y
  have hxq_p : IsPElement (p := p) xq := by
    -- `p`-elementhood passes to quotients.
    let : Fact p.Prime := fact_prime_of_charP_odd (F := F) hpodd
    rcases hx_p with ⟨k, hk⟩
    have hdiv : orderOf xq ∣ p ^ k := by
      exact dvd_trans (orderOf_map_dvd (ψ := QuotientGroup.mk' σ.ker) x) (by simp [hk])
    rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 hdiv with ⟨m, _hmle, hm⟩
    exact ⟨m, hm⟩
  have hyq_p : IsPElement (p := p) yq := by
    -- `p`-elementhood passes to quotients.
    let : Fact p.Prime := fact_prime_of_charP_odd (F := F) hpodd
    rcases hy_p with ⟨k, hk⟩
    have hdiv : orderOf yq ∣ p ^ k := by
      exact dvd_trans (orderOf_map_dvd (ψ := QuotientGroup.mk' σ.ker) y) (by simp [hk])
    rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 hdiv with ⟨m, _hmle, hm⟩
    exact ⟨m, hm⟩
  have hq_gen : Subgroup.closure ({xq, yq} : Set (H ⧸ σ.ker)) = ⊤ := by
    -- The quotient group is still generated by the images of `x` and `y`.
    let q : H →* (H ⧸ σ.ker) := QuotientGroup.mk' σ.ker
    have hmap :
        (Subgroup.closure ({x, y} : Set H)).map q =
          Subgroup.closure ({xq, yq} : Set (H ⧸ σ.ker)) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · left
          rfl
        · right
          rfl
      · intro hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact ⟨x, by simp, rfl⟩
        · exact ⟨y, by simp, rfl⟩
    have htop : (Subgroup.closure ({x, y} : Set H)).map q = ⊤ := by
      rw [hgen]
      exact Subgroup.map_top_of_surjective (f := q) (QuotientGroup.mk'_surjective _)
    exact hmap ▸ htop
  have hquot_not_pgroup : ¬ IsPGroup p (H ⧸ σ.ker) := by
    -- If this faithful irreducible quotient were a `p`-group, then Gorenstein's
    -- modular `p`-group argument would make its action trivial, contradicting
    -- the chosen composition factor where `g0` remains visible.
    let : Fact p.Prime := fact_prime_of_charP_odd (F := F) hpodd
    let g0q : H ⧸ σ.ker := QuotientGroup.mk' σ.ker g0
    have hg0q_visible : σq g0q ≠ 1 := by
      change σ g0 ≠ 1
      simpa [σ] using hg0_not_ker_M
    exact not_isPGroup_of_faithful_irreducible_visible_quotient
      (p := p) σq hσq_faithful hσq_irreducible g0q hg0q_visible
  have hxq_ne_one : σq xq ≠ 1 := by
    intro hxq_one
    have hxq_eq_one : xq = 1 := hσq_faithful (by simpa using hxq_one)
    have hclosure_singleton :
        Subgroup.closure ({yq} : Set (H ⧸ σ.ker)) = ⊤ := by
      rw [← hq_gen]
      rw [hxq_eq_one]
      exact (Subgroup.closure_insert_one ({yq} : Set (H ⧸ σ.ker))).symm
    let : Fact p.Prime := fact_prime_of_charP_odd (F := F) hpodd
    exact hquot_not_pgroup
      (isPGroup_of_closure_singleton_eq_top_of_isPElement hclosure_singleton hyq_p)
  have hyq_ne_one : σq yq ≠ 1 := by
    intro hyq_one
    have hyq_eq_one : yq = 1 := hσq_faithful (by simpa using hyq_one)
    have hclosure_singleton :
        Subgroup.closure ({xq} : Set (H ⧸ σ.ker)) = ⊤ := by
      rw [← hq_gen]
      rw [hyq_eq_one]
      have hset :
          ({xq, (1 : H ⧸ σ.ker)} : Set (H ⧸ σ.ker)) =
            ({1, xq} : Set (H ⧸ σ.ker)) := by
        ext z
        simp [or_comm]
      simp [hset]
    let : Fact p.Prime := fact_prime_of_charP_odd (F := F) hpodd
    exact hquot_not_pgroup
      (isPGroup_of_closure_singleton_eq_top_of_isPElement hclosure_singleton hxq_p)
  have hxq_quad : HasQuadraticMinimalPolynomial F' _ (σq xq) := by
    -- Pass the square-zero operator `ρ' x - 1` to the chosen simple quotient,
    -- then through the faithful kernel quotient.
    let : Fact p.Prime := fact_prime_of_charP_odd (F := F) hpodd
    have hx'_sq : (ρ' x - 1) ^ 2 = 0 :=
      square_zero_of_quadratic_pElement_representation (p := p) ρ' hx_p hx'_quad
    have hxσ_sq : (σ x - 1) ^ 2 = 0 := by
      simpa [σ] using square_zero_of_subrepresentation_quotient ρ' W M x hx'_sq
    have hxσq_sq : (σq xq - 1) ^ 2 = 0 := by
      simpa [σq, xq] using square_zero_of_kerRepresentation σ x hxσ_sq
    exact hasQuadraticMinimalPolynomial_of_square_zero_of_ne_one (σq xq) hxσq_sq hxq_ne_one
  have hyq_quad : HasQuadraticMinimalPolynomial F' _ (σq yq) := by
    let : Fact p.Prime := fact_prime_of_charP_odd (F := F) hpodd
    have hy'_sq : (ρ' y - 1) ^ 2 = 0 :=
      square_zero_of_quadratic_pElement_representation (p := p) ρ' hy_p hy'_quad
    have hyσ_sq : (σ y - 1) ^ 2 = 0 := by
      simpa [σ] using square_zero_of_subrepresentation_quotient ρ' W M y hy'_sq
    have hyσq_sq : (σq yq - 1) ^ 2 = 0 := by
      simpa [σq, yq] using square_zero_of_kerRepresentation σ y hyσ_sq
    exact hasQuadraticMinimalPolynomial_of_square_zero_of_ne_one (σq yq) hyσq_sq hyq_ne_one

  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSylowq : HasAbelianSylow 2 (H ⧸ σ.ker) :=
    hSylow.mapSurjective (QuotientGroup.mk' σ.ker)
      (QuotientGroup.mk'_surjective σ.ker)
  exact gorenstein_3_8_1_false_of_faithful_irreducible
    (p := p) σq hσq_faithful hσq_irreducible
    xq yq hq_gen hpodd hxq_p hyq_p hxq_quad hyq_quad
    hquot_not_pgroup hSylowq

omit [Fact p.Prime] in
/-- Gorenstein, Chapter 3, Theorems 8.1--8.3, odd-order extraction:
from a non-`p`-stable faithful representation, Theorem 8.2 supplies two
conjugate quadratic `p`-elements generating a non-`p`-group, and Theorem 8.1
applied to a faithful irreducible composition factor produces an even-order
subquotient of `G`.  This is the exact part of Gorenstein's proof needed for
the odd-order replacement of Theorem 8.3. -/
private theorem gorenstein_3_8_1_3_8_2_false_of_not_pStable
    {G : Type uG} [Group G] [Finite G]
    (hpodd : Odd p) (hpcore : pCore p G = ⊥)
    (hSylow : HasAbelianSylow 2 G) :
    ¬ PStableGroup.{uG, uF, uV} p G → False := by
  intro hnstable
  -- Gorenstein 3.8.3 begins by choosing a faithful representation in
  -- characteristic `p` and a `p`-element acting with quadratic minimal
  -- polynomial.
  unfold PStableGroup PStableRepresentation at hnstable
  push Not at hnstable
  rcases hnstable with
    ⟨F, V, _hF, _hchar, _hVadd, _hVmodule, _hVfiniteDimensional, ρ,
      hρ_faithful, hρ_not_stable⟩
  rcases hρ_not_stable with ⟨x, hx_p, hx_quad⟩
  -- The conjugacy class of `x` cannot have every pair generate a `p`-group:
  -- otherwise Gorenstein 3.8.2 puts the class in `O_p(G)=1`, contradicting
  -- the quadratic minimal polynomial.
  have h38_2_pair :
      ∃ y : G,
        (∃ g : G, y = g * x * g⁻¹) ∧
        ¬ IsPGroup p (Subgroup.closure ({x, y} : Set G)) := by
    -- Source: Daniel Gorenstein, *Finite Groups*, Chapter 3, Theorem 8.2
    -- (Alperin--Lyons/Baer--Suzuki form), applied to the conjugacy class of `x`.
    by_contra hpair
    push Not at hpair
    let : Fact p.Prime := by
      refine ⟨?_⟩
      rcases CharP.char_is_prime_or_zero (R := F) p with hp | hp0
      · exact hp
      · exact False.elim (Nat.not_odd_zero (by simp [hp0] at hpodd))
    have hclass_le_core :
        ∀ z : G, (∃ g : G, z = g * x * g⁻¹) → z ∈ pCore p G := by
      exact gorenstein_3_8_2_conjugacy_class_le_pCore
        (G := G) (p := p) (x := x) hx_p hpair
    have hx_in_core : x ∈ pCore p G := hclass_le_core x ⟨1, by simp⟩
    have hx_eq_one : x = 1 := by
      have : x ∈ (⊥ : Subgroup G) := by
        simpa [hpcore] using hx_in_core
      simpa using this
    have hρx_one : ρ x = 1 := by
      simp [hx_eq_one]
    have hnot_quad : ¬ HasQuadraticMinimalPolynomial F V (ρ x) := by
      intro hquad
      have hroot :
          Polynomial.aeval (ρ x) (Polynomial.X - Polynomial.C (1 : F)) = 0 := by
        rw [hρx_one]
        simp [Polynomial.aeval_X]
      have hmin_dvd :
          minpoly F (ρ x) ∣ (Polynomial.X - Polynomial.C (1 : F)) :=
        minpoly.dvd F (ρ x) hroot
      have hlin_ne : (Polynomial.X - Polynomial.C (1 : F) : Polynomial F) ≠ 0 :=
        Polynomial.X_sub_C_ne_zero (1 : F)
      have hdeg_le : (minpoly F (ρ x)).natDegree ≤ 1 := by
        have hdeg_le' :
            (minpoly F (ρ x)).natDegree ≤
              (Polynomial.X - Polynomial.C (1 : F)).natDegree :=
          Polynomial.natDegree_le_of_dvd hmin_dvd hlin_ne
        exact hdeg_le'.trans_eq (Polynomial.natDegree_X_sub_C (1 : F))
      have htwo_le : 2 ≤ (1 : ℕ) := by
        calc
          2 = (minpoly F (ρ x)).natDegree := by
            simpa [HasQuadraticMinimalPolynomial] using hquad.symm
          _ ≤ 1 := hdeg_le
      omega
    exact hnot_quad hx_quad
  rcases h38_2_pair with ⟨y, hy_conj, hxy_not_pgroup⟩
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  -- Passing to an irreducible composition factor of the restriction to `H`,
  -- modulo its kernel, gives a faithful irreducible group generated by the
  -- two images of `x` and `y`.  Gorenstein 3.8.1 then says this quotient has
  -- even order in the odd-prime case.
  have h38_1_factor : False := by
    -- Source: Daniel Gorenstein, *Finite Groups*, Chapter 3, Theorem 8.1,
    -- together with the composition-factor reduction in Theorem 8.3.
    have hx_mem_H : x ∈ H := by
      dsimp [H]
      exact Subgroup.subset_closure (by simp)
    have hy_mem_H : y ∈ H := by
      dsimp [H]
      exact Subgroup.subset_closure (by simp)
    let xH : H := ⟨x, hx_mem_H⟩
    let yH : H := ⟨y, hy_mem_H⟩
    let ρH : Representation F H V := ρ.comp H.subtype
    have hH_gen : Subgroup.closure ({xH, yH} : Set H) = ⊤ := by
      let K : Subgroup H := Subgroup.closure ({xH, yH} : Set H)
      apply eq_top_iff.mpr
      intro h _hh
      change h ∈ K
      have hmem :
          ∃ hh : (h : G) ∈ H, (⟨(h : G), hh⟩ : H) ∈ K := by
        refine Subgroup.closure_induction
          (p := fun g : G => fun _hg => ∃ hg : g ∈ H, (⟨g, hg⟩ : H) ∈ K)
          ?_ ?_ ?_ ?_
          h.property
        · intro g hg
          rcases (by simpa using hg : g = x ∨ g = y) with rfl | rfl
          · exact ⟨hx_mem_H, Subgroup.subset_closure (by simp [xH])⟩
          · exact ⟨hy_mem_H, Subgroup.subset_closure (by simp [yH])⟩
        · exact ⟨H.one_mem, K.one_mem⟩
        · intro a b _ha _hb ha hb
          rcases ha with ⟨haH, haK⟩
          rcases hb with ⟨hbH, hbK⟩
          refine ⟨H.mul_mem haH hbH, ?_⟩
          change (⟨a, haH⟩ : H) * (⟨b, hbH⟩ : H) ∈ K
          exact K.mul_mem haK hbK
        · intro a _ha ha
          rcases ha with ⟨haH, haK⟩
          refine ⟨H.inv_mem haH, ?_⟩
          change (⟨a, haH⟩ : H)⁻¹ ∈ K
          exact K.inv_mem haK
      rcases hmem with ⟨hh, hK⟩
      simpa using hK
    have hxH_p : IsPElement (p := p) xH := by
      rcases hx_p with ⟨n, hn⟩
      exact ⟨n, by simpa [xH, Subgroup.orderOf_coe] using hn⟩
    have hy_p : IsPElement (p := p) y := by
      rcases hy_conj with ⟨g, rfl⟩
      rcases hx_p with ⟨n, hn⟩
      have horder : orderOf x = orderOf (g * x * g⁻¹) := by
        exact SemiconjBy.orderOf_eq g (by
          dsimp [SemiconjBy]
          simp [mul_assoc])
      exact ⟨n, by simpa [hn] using horder.symm⟩
    have hyH_p : IsPElement (p := p) yH := by
      rcases hy_p with ⟨n, hn⟩
      exact ⟨n, by simpa [yH, Subgroup.orderOf_coe] using hn⟩
    have hH_not_pgroup : ¬ IsPGroup p H := by
      simpa [H] using hxy_not_pgroup
    have hxH_quad : HasQuadraticMinimalPolynomial F V (ρH xH) := by
      simpa [ρH, xH] using hx_quad
    have hy_quad : HasQuadraticMinimalPolynomial F V (ρ y) := by
      rcases hy_conj with ⟨g, rfl⟩
      -- Conjugate linear transformations have the same minimal polynomial,
      -- so the quadratic condition transfers from `x` to every conjugate.
      let e : V ≃ₗ[F] V :=
        LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
          (by
            ext v
            change ((ρ g) * (ρ g⁻¹)) v = v
            rw [← map_mul]
            simp
          )
          (by
            ext v
            change ((ρ g⁻¹) * (ρ g)) v = v
            rw [← map_mul]
            simp)
      have hconj : e.conj (ρ x) = ρ (g * x * g⁻¹) := by
        ext v
        simp [e, LinearEquiv.conj_apply, Module.End.mul_eq_comp, mul_assoc]
      rw [← hconj]
      exact (hasQuadraticMinimalPolynomial_conj e (ρ x)).2 hx_quad
    have hyH_quad : HasQuadraticMinimalPolynomial F V (ρH yH) := by
      simpa [ρH, yH] using hy_quad
    let : Fact p.Prime := fact_prime_of_charP_odd (F := F) hpodd
    exact gorenstein_3_8_1_false_after_composition_factor
      (p := p) ρH (by
        exact hρ_faithful.comp H.subtype_injective)
      xH yH hH_gen hpodd hxH_p hyH_p hxH_quad hyH_quad hH_not_pgroup
      (hSylow.subgroup H)
  exact h38_1_factor

omit [Fact p.Prime] in
/-- Gorenstein 3.8.1--3.8.3 with the two-dimensional obstruction replaced by
the abelian-Sylow-`2` endpoint. -/
public theorem pStableGroup_of_abelianSylowTwo
    {G : Type uG} [Group G] [Finite G]
    (hpodd : Odd p) (hpcore : pCore p G = ⊥)
    (hSylow : HasAbelianSylow 2 G) :
    PStableGroup.{uG, uF, uV} p G := by
  by_contra hnot
  exact gorenstein_3_8_1_3_8_2_false_of_not_pStable
    (G := G) (p := p) hpodd hpcore hSylow hnot

private theorem chief_conj_range_pCore_eq_bot_local
    {G : Type*} [Group G] [Finite G] (cf : ChiefFactor G) [cf.V.Normal]
    {p : ℕ} [Fact p.Prime]
    (hUq_elem :
      let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
      let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
      letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
      IsElementaryAbelian p (↥Uq)) :
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
    let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
    pCore p φ.range = ⊥ := by
  classical
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hmin :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using chiefFactor_quotient_minimal_local (G := G) cf
  let : Uq.Normal := hmin.1
  let : IsElementaryAbelian p (↥Uq) := by
    simpa [π, Uq] using hUq_elem
  let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
  let A : Subgroup (MulAut Uq) := φ.range
  have hUq_p : IsPGroup p Uq := IsElementaryAbelian.isPGroup p Uq
  let P : Subgroup A := pCore p A
  have hP_p : IsPGroup p P := by
    dsimp [P]
    exact pCore_isPGroup (G := A) (p := p)
  have hUq_dvd : p ∣ Nat.card Uq := by
    have hUq_nontrivial : Nontrivial Uq := (Subgroup.nontrivial_iff_ne_bot Uq).2 hmin.2.1
    rcases (IsPGroup.nontrivial_iff_card (p := p) (G := Uq) (hG := hUq_p)).1 hUq_nontrivial with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn)
  let F : Subgroup Uq := fixedPointSubgroup P Uq
  have hF_ne_bot : F ≠ ⊥ := by
    have hone_fix : (1 : Uq) ∈ MulAction.fixedPoints P Uq := by
      simp [MulAction.mem_fixedPoints]
    obtain ⟨u, hu_fix, hu_ne_one'⟩ :=
      hP_p.exists_fixed_point_of_prime_dvd_card_of_fixed_point
        (α := Uq) hUq_dvd hone_fix
    have hu_ne_one : u ≠ 1 := by
      intro hu
      exact hu_ne_one' hu.symm
    intro hbot
    have hu_mem : u ∈ F := by
      simpa [F, fixedPointSubgroup, FixedPoints.mem_subgroup] using
        MulAction.mem_fixedPoints.mp hu_fix
    have hu_bot : u ∈ (⊥ : Subgroup Uq) := by
      simpa [hbot] using hu_mem
    exact hu_ne_one (Subgroup.mem_bot.mp hu_bot)
  have : P.Normal := by
    dsimp [P]
    infer_instance
  have hF_inv : IsInvariant A Uq F := by
    refine ⟨?_⟩
    intro a u
    constructor
    · intro hu
      change u ∈ fixedPointSubgroup P Uq at hu
      change a • u ∈ fixedPointSubgroup P Uq
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hu ⊢
      exact smul_mem_fixedPoints_of_normal (H := P) a hu
    · intro hu
      change a • u ∈ fixedPointSubgroup P Uq at hu
      change u ∈ fixedPointSubgroup P Uq
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hu ⊢
      have hsmul := smul_mem_fixedPoints_of_normal (H := P) a⁻¹ hu
      simpa [mul_smul] using hsmul
  let Fmap : Subgroup (G ⧸ cf.V) := F.map Uq.subtype
  have hFmap_normal : Fmap.Normal := by
    refine ⟨?_⟩
    intro x hx g
    rcases Subgroup.mem_map.mp hx with ⟨u, huF, rfl⟩
    let ag : A := ⟨φ g, ⟨g, rfl⟩⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨ag • u, (hF_inv.invariant ag u).1 huF, ?_⟩
    change (((φ g) u : Uq) : G ⧸ cf.V) = g * (u : G ⧸ cf.V) * g⁻¹
    simp [φ, MulAut.conjNormal_apply]
  have hFmap_le_Uq : Fmap ≤ Uq := by
    exact Subgroup.map_subtype_le F
  have hFmap_ne_bot : Fmap ≠ ⊥ := by
    intro hbot
    have : F = ⊥ := by
      exact
        (Subgroup.map_eq_bot_iff_of_injective (H := F) (f := Uq.subtype)
          Uq.subtype_injective).1 (by simpa [Fmap] using hbot)
    exact hF_ne_bot this
  have hFmap_eq_Uq : Fmap = Uq :=
    hmin.2.2 Fmap hFmap_normal hFmap_le_Uq hFmap_ne_bot
  have htop_map_Uq : (⊤ : Subgroup Uq).map Uq.subtype = Uq := by
    simpa [MonoidHom.range_eq_map] using
      (Uq.range_subtype : Uq.subtype.range = Uq)
  have hF_top : F = ⊤ := by
    have hinj : Function.Injective (Subgroup.map Uq.subtype) :=
      Subgroup.map_injective (f := Uq.subtype) Uq.subtype_injective
    apply hinj
    simpa [Fmap, htop_map_Uq] using hFmap_eq_Uq
  have htriv : ActsTrivially (A := P) (G := Uq) := by
    intro a u
    have huF : u ∈ F := by
      simp [F, hF_top]
    exact (FixedPoints.mem_subgroup (M := P) (a := u)).mp huF a
  have hsub : Subsingleton P := by
    refine ⟨?_⟩
    intro a b
    apply Subtype.ext
    ext u
    change ((a • u : Uq) : G ⧸ cf.V) = ((b • u : Uq) : G ⧸ cf.V)
    exact congrArg (fun x : Uq => (x : G ⧸ cf.V))
      ((htriv a u).trans (htriv b u).symm)
  have hcard_one : Nat.card P = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  change P = ⊥
  exact (Subgroup.card_eq_one (H := P)).1 hcard_one

set_option backward.isDefEq.respectTransparency false in
private theorem pStable_le_centralizerOfChiefFactor_of_abelianSylowTwo
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (hSylow : HasAbelianSylow 2 G)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Q A : Subgroup G} [Q.Normal]
    (hQp : IsPGroup p Q) (hAp : IsPGroup p A)
    (hcomm2 : ⁅⁅Q, A⁆, A⁆ = ⊥)
    (cf : ChiefFactor G) (hcfU_le_Q : cf.U ≤ Q) :
    A ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf := by
  classical
  have hQA_cent : ⁅Q, A⁆ ≤ Subgroup.centralizer (A : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm2
  let Usub : Subgroup Q := cf.U.subgroupOf Q
  have hUsub_p : IsPGroup p Usub := hQp.to_subgroup Usub
  have hcfU_p : IsPGroup p cf.U := by
    exact hUsub_p.of_equiv (Subgroup.subgroupOfEquivOfLe (H := cf.U) (K := Q) hcfU_le_Q)
  have : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hUq_min :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using chiefFactor_quotient_minimal_local (G := G) cf
  let : Uq.Normal := hUq_min.1
  have hUq_p : IsPGroup p Uq := by
    simpa [Uq, π] using hcfU_p.map π
  obtain ⟨q, hqprime, hUq_elem'⟩ :=
    chiefFactor_quotient_exists_isElementaryAbelian (G := G) inferInstance cf
  let : Fact q.Prime := ⟨hqprime⟩
  have hq_dvd_card : q ∣ Nat.card Uq := by
    have hUq_nontrivial : Nontrivial Uq := (Subgroup.nontrivial_iff_ne_bot Uq).2 hUq_min.2.1
    have hUq_q : IsPGroup q Uq := IsElementaryAbelian.isPGroup q Uq
    rcases (IsPGroup.nontrivial_iff_card (p := q) (G := Uq) (hG := hUq_q)).1 hUq_nontrivial with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self q (Nat.pos_iff_ne_zero.mp hn)
  rcases IsPGroup.iff_card.mp hUq_p with ⟨n, hn⟩
  have hq_eq_p : q = p := by
    exact Nat.prime_eq_prime_of_dvd_pow hqprime Fact.out (hn ▸ hq_dvd_card)
  have hUq_elem : IsElementaryAbelian p (↥Uq) := by
    simpa [hq_eq_p] using hUq_elem'
  let : IsElementaryAbelian p (↥Uq) := hUq_elem
  let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
  have hφ_pcore_bot : pCore p φ.range = ⊥ := by
    simpa [π, Uq, φ] using
      chief_conj_range_pCore_eq_bot_local (G := G) (cf := cf) (p := p) hUq_elem
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hquotSylow : HasAbelianSylow 2 (G ⧸ cf.V) :=
    hSylow.mapSurjective π (QuotientGroup.mk'_surjective cf.V)
  have hφSylow : HasAbelianSylow 2 φ.range :=
    hquotSylow.mapSurjective φ.rangeRestrict
      (MonoidHom.rangeRestrict_surjective φ)
  let ρ : Representation (ZMod p) φ.range (Additive Uq) :=
    Theory.Representation.ofElementaryAbelianAction (A := φ.range) (G := Uq) (p := p)
  have hρ_faithful : Function.Injective ρ := by
    have hρker_bot : ρ.ker = ⊥ := by
      rw [Theory.Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup]
      rw [fixingSubgroupOf_univ_eq_ker_toMulAut]
      exact (MonoidHom.ker_eq_bot_iff (φ.range.subtype)).2 φ.range.subtype_injective
    exact (MonoidHom.ker_eq_bot_iff ρ).1 hρker_bot
  have hpodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hρ_pstable : PStableRepresentation p ρ := by
    have hφ_pstable : PStableGroup p φ.range :=
      pStableGroup_of_abelianSylowTwo (G := φ.range) (p := p)
        hpodd hφ_pcore_bot hφSylow
    exact hφ_pstable (ZMod p) (Additive Uq) ρ hρ_faithful
  intro a ha
  let ψ : A →* φ.range :=
    ((φ.comp π).comp A.subtype).codRestrict φ.range (by
      intro x
      exact ⟨π (x : G), rfl⟩)
  let z : φ.range := ψ ⟨a, ha⟩
  have hz_p : IsPElement (p := p) z := by
    obtain ⟨n, hn'⟩ := (IsPGroup.iff_orderOf (p := p) (G := A)).1 hAp ⟨a, ha⟩
    have hdiv : orderOf z ∣ p ^ n := by
      exact (orderOf_map_dvd (ψ := ψ) ⟨a, ha⟩).trans (by simp [hn'])
    rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 hdiv with ⟨m, _hm, hm⟩
    exact ⟨m, hm⟩
  have hdev (u : Uq) :
      (ρ z - 1) (Additive.ofMul u) = Additive.ofMul ((z • u) / u) := by
    rw [LinearMap.sub_apply, Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
    change Additive.ofMul (z • u) - Additive.ofMul u = Additive.ofMul ((z • u) / u)
    rw [sub_eq_add_neg]
    simp [div_eq_mul_inv]
  have hfirst_fix (u : Uq) : z • (((z • u) / u : Uq)) = ((z • u) / u : Uq) := by
    rcases Subgroup.mem_map.mp u.2 with ⟨y, hyU, hy_eq⟩
    let uy : Uq := ⟨π y, Subgroup.mem_map_of_mem π hyU⟩
    have hu_eq : u = uy := Subtype.ext (by simpa [uy] using hy_eq.symm)
    subst hu_eq
    let d : Uq := ((z • uy) / uy : Uq)
    have hd_val : (d : G ⧸ cf.V) = π ⁅(a : G), y⁆ := by
      calc
        (d : G ⧸ cf.V) =
            ((z • uy : Uq) : G ⧸ cf.V) * ((uy : G ⧸ cf.V))⁻¹ := by
              simp [d, div_eq_mul_inv]
        _ =
            (π (a : G)) * π y * (π (a : G))⁻¹ * (π y)⁻¹ := by
              simp [z, ψ, uy, φ, π, mul_assoc]
        _ = π ⁅(a : G), y⁆ := by
              simp [π, commutatorElement_def, mul_assoc]
    have hcomm_mem' : ⁅y, (a : G)⁆ ∈ ⁅Q, A⁆ :=
      Subgroup.commutator_mem_commutator (hcfU_le_Q hyU) ha
    have hcomm_mem : ⁅(a : G), y⁆ ∈ ⁅Q, A⁆ := by
      simpa [commutatorElement_inv] using (⁅Q, A⁆).inv_mem hcomm_mem'
    have hcommU : ⁅(a : G), y⁆ ∈ cf.U := by
      have haya : (a : G) * y * (a : G)⁻¹ ∈ cf.U :=
        cf.isChief.normal_H.conj_mem y hyU (a : G)
      simpa [commutatorElement_def, mul_assoc] using cf.U.mul_mem haya (cf.U.inv_mem hyU)
    have hcent_d : ⁅(a : G), y⁆ ∈ Subgroup.centralizer (A : Set G) := hQA_cent hcomm_mem
    have hfix_d : (a : G) * ⁅(a : G), y⁆ * (a : G)⁻¹ = ⁅(a : G), y⁆ := by
      let c : G := ⁅(a : G), y⁆
      have hcomm : (a : G) * c = c * (a : G) := by
        simpa [c] using (Subgroup.mem_centralizer_iff.mp hcent_d) (a : G) ha
      calc
        (a : G) * ⁅(a : G), y⁆ * (a : G)⁻¹ = (a : G) * c * (a : G)⁻¹ := by rfl
        _ = c * (a : G) * (a : G)⁻¹ := by rw [hcomm]
        _ = c := by simp [mul_assoc]
        _ = ⁅(a : G), y⁆ := by rfl
    let d0 : Uq := ⟨π ⁅(a : G), y⁆, Subgroup.mem_map_of_mem π hcommU⟩
    have hd_eq : d = d0 := Subtype.ext (by simpa [d0] using hd_val)
    have hfix_d0 : z • d0 = d0 := by
      apply Subtype.ext
      calc
        ((z • d0 : Uq) : G ⧸ cf.V) =
            π ((a : G) * ⁅(a : G), y⁆ * (a : G)⁻¹) := by
              simp [z, ψ, φ, π, d0,
                commutatorElement_def, mul_assoc]
        _ = π ⁅(a : G), y⁆ := by
              simpa [π] using congrArg π hfix_d
        _ = (d0 : G ⧸ cf.V) := rfl
    change z • d = d
    simpa [hd_eq] using hfix_d0
  have hsq : (ρ z - 1) ^ 2 = 0 := by
    ext v
    cases v with
    | ofMul u =>
        rw [pow_two, Module.End.mul_eq_comp]
        have hsq_u : ((ρ z - 1) ∘ₗ (ρ z - 1)) (Additive.ofMul u) = 0 := by
          rw [LinearMap.comp_apply, hdev u, hdev (((z • u) / u : Uq))]
          change Additive.ofMul (z • (((z • u) / u : Uq)) / (((z • u) / u : Uq))) = Additive.ofMul 1
          exact congrArg Additive.ofMul (by simp [hfirst_fix u])
        simpa [commutatorElement_def] using
          congrArg (fun x : Additive Uq => (((x.toMul : Uq) : G ⧸ cf.V))) hsq_u
  have hzρ : ρ z = 1 := eq_one_of_pStable_square_zero ρ hρ_pstable hz_p hsq
  have hz_eq_one : z = 1 := hρ_faithful (by simpa using hzρ)
  have hphi_one : φ (π (a : G)) = 1 := by
    simpa [z, ψ] using congrArg Subtype.val hz_eq_one
  refine (mem_centralizerOfChiefFactor (G := G) (H := (⊤ : Subgroup G)) (cf := cf) (g := a)).2 ?_
  refine ⟨by simp, ?_⟩
  intro u hu
  let uq : Uq := ⟨π u, Subgroup.mem_map_of_mem π hu⟩
  have hfix_u : (φ (π (a : G))) uq = uq := by
    simpa using congrArg (fun f : MulAut Uq => f uq) hphi_one
  have hqeq : π ((a : G) * u * (a : G)⁻¹) = π u := by
    exact congrArg Subtype.val hfix_u
  have hdiv_mem : ((a : G) * u * (a : G)⁻¹) / u ∈ cf.V :=
    (QuotientGroup.eq_iff_div_mem (N := cf.V)
      (x := (a : G) * u * (a : G)⁻¹) (y := u)).1 hqeq
  simpa [commutatorElement_def, div_eq_mul_inv, mul_assoc] using hdiv_mem



private theorem pStableGroup'_of_pPrimeCore_eq_bot_abelianSylowTwo
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (hSylow : HasAbelianSylow 2 G)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hcore : pPrimeCore p G = ⊥) :
    PStableGroup' (G := G) p := by
  intro Q A htopQ_normal hQp hAp hA_norm hcomm2
  rw [hcore, bot_sup_eq] at htopQ_normal
  have hQ_normal : Q.Normal := htopQ_normal
  let : Q.Normal := hQ_normal
  let N : Subgroup (G) := Subgroup.normalizer (Q : Set (G))
  let C : Subgroup (G) := Subgroup.centralizer (Q : Set (G))
  have hnormQ_top : N = ⊤ := by
    dsimp [N]
    exact Subgroup.normalizer_eq_top (H := Q)
  have hC_normal : C.Normal := by
    simpa [C] using
      (inferInstance : (Subgroup.centralizer (Q : Set (G))).Normal)
  let : C.Normal := hC_normal
  let : (C.subgroupOf N).Normal := Subgroup.Normal.subgroupOf hC_normal N
  obtain ⟨r, f, hf0, hfr, hf_norm, hf_chief⟩ :=
    exists_chief_series_from_to Q hQ_normal
  have hf_le_Q : ∀ i, i ≤ r → f i ≤ Q := by
    intro i hi
    induction i with
    | zero =>
        simp [hf0]
    | succ i ih =>
        have hir : i < r := by omega
        exact (hf_chief i hir).lt.le.trans (ih (by omega))
  let cf : Fin r → ChiefFactor (G) := fun i =>
    ⟨f (i.1 + 1), f i.1, hf_chief i.1 i.2⟩
  let H : Subgroup (G) :=
    ⨅ i : Fin r, centralizerOfChiefFactor (G := G) (⊤ : Subgroup (G)) (cf i)
  have hA_le_H : A ≤ H := by
    intro a ha
    rw [Subgroup.mem_iInf]
    intro i
    have hA_le_cf :
        A ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup (G)) (cf i) :=
      pStable_le_centralizerOfChiefFactor_of_abelianSylowTwo
        (G := G) hSylow (p := p) hp2 hQp hAp hcomm2 (cf i)
        (hf_le_Q i.1 (Nat.le_of_lt i.2))
    exact hA_le_cf ha
  have hH_normal : H.Normal := by
    dsimp [H]
    refine Subgroup.normal_iInf_normal (fun i => ?_)
    simpa [cf] using
      (centralizerOfChiefFactor_normal (G := G) (H := (⊤ : Subgroup (G)))
        (hH := (inferInstance : (⊤ : Subgroup (G)).Normal)) (cf i))
  let : H.Normal := hH_normal
  have hH_normQ : H ≤ N := by
    rw [hnormQ_top]
    exact le_top
  let : MulDistribMulAction H Q :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer H Q hH_normQ
  have hfix_eq_Csub :
      fixingSubgroupOf H Q (Set.univ : Set Q) = C.subgroupOf H := by
    ext h
    rw [mem_fixingSubgroup_iff]
    constructor
    · intro hh
      change (h : G) ∈ C
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hfix : h • (⟨x, hx⟩ : Q) = (⟨x, hx⟩ : Q) := hh ⟨x, hx⟩ (by trivial)
      have hconj : (h : G) * x * (h : G)⁻¹ = x := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH_normQ] using
          congrArg Subtype.val hfix
      simpa [mul_assoc] using
        (congrArg (fun t : G => t * (h : G)) hconj).symm
    · intro hhC x hx
      apply Subtype.ext
      have hcomm : x * (h : G) = (h : G) * x :=
        (Subgroup.mem_centralizer_iff.mp hhC) x (by simp)
      have hconj : (h : G) * x * (h : G)⁻¹ = x := by
        simpa [mul_assoc] using
          congrArg (fun t : G => t * (h : G)⁻¹) hcomm.symm
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH_normQ] using
        hconj
  have hker_normal : (fixingSubgroupOf H Q (Set.univ : Set Q)).Normal := by
    rw [hfix_eq_Csub]
    exact Subgroup.Normal.subgroupOf hC_normal H
  let πset : Set Nat.Primes := {⟨p, Fact.out⟩}
  have hQ_pi : IsPiGroup πset Q := by
    rw [IsPiGroup_iff πset Q]
    intro q hqdvd
    rcases hQp.exists_card_eq with ⟨n, hn⟩
    have hqdvd_pow : q.1 ∣ p ^ n := by
      simpa [hn] using hqdvd
    have hq_eq : q.1 = p := Nat.prime_eq_prime_of_dvd_pow q.2 Fact.out hqdvd_pow
    have hq_eq' : q = ⟨p, Fact.out⟩ := by
      apply Subtype.ext
      simpa using hq_eq
    exact Set.mem_singleton_iff.mpr hq_eq'
  let Gi : ℕ → Subgroup Q := fun i =>
    if hi : i ≤ r then (f i).subgroupOf Q else ⊥
  have hGi_zero : Gi 0 = ⊤ := by
    simp [Gi, hf0]
  have hGi_bot : Gi (r + 1) = ⊥ := by
    simp [Gi]
  have hGi_desc : ∀ i, Gi (i + 1) ≤ Gi i := by
    intro i x hx
    by_cases hi : i < r
    · have hi0 : i ≤ r := Nat.le_of_lt hi
      have hi1 : i + 1 ≤ r := Nat.succ_le_of_lt hi
      have hx' : (x : G) ∈ f (i + 1) := by
        simpa [Gi, hi1, Subgroup.mem_subgroupOf] using hx
      have hx'' : (x : G) ∈ f i := (hf_chief i hi).lt.le hx'
      simpa [Gi, hi0, Subgroup.mem_subgroupOf] using hx''
    · have hi1_not : ¬ i + 1 ≤ r := by omega
      have hxbot : x ∈ (⊥ : Subgroup Q) := by
        simpa [Gi, hi1_not] using hx
      by_cases hi0 : i ≤ r
      · have hi_eq : i = r := by omega
        simpa [Gi, hi0, hi_eq, hfr] using hxbot
      · simpa [Gi, hi0] using hxbot
  have hGi_normal : ∀ i, (Gi i).Normal := by
    intro i
    by_cases hi : i ≤ r
    · simpa [Gi, hi] using Subgroup.Normal.subgroupOf (hf_norm i hi) Q
    · simp [Gi, hi]
  have hGi_inv : ∀ i, IsInvariant H Q (Gi i) := by
    intro i
    by_cases hi : i ≤ r
    · have hH_norm_fi : H ≤ Subgroup.normalizer (f i : Set (G)) := by
        let : (f i).Normal := hf_norm i hi
        simpa using
          (Subgroup.le_normalizer_of_normal (H := f i) :
            H ≤ Subgroup.normalizer (f i : Set (G)))
      refine ⟨?_⟩
      intro h x
      constructor
      · intro hx
        have hx' : (x : G) ∈ f i := by
          simpa [Gi, hi, Subgroup.mem_subgroupOf] using hx
        have hconj : (h : G) * (x : G) * (h : G)⁻¹ ∈ f i :=
          (Subgroup.mem_normalizer_iff.mp (hH_norm_fi h.2) (x : G)).1 hx'
        simpa [Gi, hi, Subgroup.mem_subgroupOf,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH_normQ] using hconj
      · intro hx
        have hhInv : ((h : G)⁻¹) ∈ Subgroup.normalizer (f i : Set (G)) := by
          exact (Subgroup.normalizer (f i : Set (G))).inv_mem (hH_norm_fi h.2)
        have hx' : (h : G) * (x : G) * (h : G)⁻¹ ∈ f i := by
          simpa [Gi, hi, Subgroup.mem_subgroupOf,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH_normQ] using hx
        have hback :
            ((h : G)⁻¹ * (((h : G) * (x : G) * (h : G)⁻¹)) *
              (((h : G)⁻¹)⁻¹)) ∈ f i :=
          (Subgroup.mem_normalizer_iff.mp hhInv _).1 hx'
        have hx'' : (x : G) ∈ f i := by
          simpa [mul_assoc] using hback
        simpa [Gi, hi, Subgroup.mem_subgroupOf] using hx''
    · refine ⟨?_⟩
      intro h x
      constructor
      · intro hx
        have hxbot : x ∈ (⊥ : Subgroup Q) := by
          simpa [Gi, hi] using hx
        have hxEq : x = 1 := by simpa using hxbot
        subst x
        simp [Gi, hi]
      · intro hx
        have hxbot : h • x ∈ (⊥ : Subgroup Q) := by
          simpa [Gi, hi] using hx
        have hxEq : h • x = 1 := by
          simpa using hxbot
        have hx' : ((h : G) * (x : G) * (h : G)⁻¹) = 1 := by
          simpa using (congrArg Subtype.val hxEq : ((h • x : Q) : G) = 1)
        have hx'' : (x : G) = 1 := by
          calc
            (x : G) =
                (h : G)⁻¹ * (((h : G) * (x : G) * (h : G)⁻¹)) *
                  (h : G) := by group
            _ = 1 := by simp [hx']
        have hxbot : x ∈ (⊥ : Subgroup Q) := by
          apply Subgroup.mem_bot.mpr
          apply Subtype.ext
          simpa using hx''
        simpa [Gi, hi] using hxbot
  have hGi_triv :
      ∀ i (aH : H) (x : Q), x ∈ Gi i → (aH • x) * x⁻¹ ∈ Gi (i + 1) := by
    intro i aH x hx
    by_cases hi : i < r
    · let cfi : ChiefFactor (G) := ⟨f (i + 1), f i, hf_chief i hi⟩
      have hH_cent :
          H ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup (G)) cfi := by
        let j : Fin r := ⟨i, hi⟩
        have htmp :
            H ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup (G)) (cf j) :=
          iInf_le _ j
        simpa [cfi, cf, j] using htmp
      have hcomm_le : ⁅H, cfi.U⁆ ≤ cfi.V :=
          (le_centralizerOfChiefFactor_iff
            (G := G) (H := (⊤ : Subgroup (G))) (N := H) (cf := cfi)).1 hH_cent |>.2
      have hxfi : (x : G) ∈ f i := by
        simpa [Gi, Nat.le_of_lt hi, Subgroup.mem_subgroupOf] using hx
      have hmem : ⁅(aH : G), (x : G)⁆ ∈ f (i + 1) := by
        exact hcomm_le (Subgroup.commutator_mem_commutator aH.property hxfi)
      have hi1 : i + 1 ≤ r := Nat.succ_le_of_lt hi
      simpa [Gi, hi1, Subgroup.mem_subgroupOf,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        div_eq_mul_inv, commutatorElement_def, mul_assoc] using hmem
    · have hxbot : x ∈ (⊥ : Subgroup Q) := by
        by_cases hir : i ≤ r
        · have hi_eq : i = r := by omega
          simpa [Gi, hir, hi_eq, hfr] using hx
        · simpa [Gi, hir] using hx
      have hx_eq_one : x = 1 := by simpa using hxbot
      have hi1_not : ¬ i + 1 ≤ r := by omega
      subst x
      simp [Gi, hi1_not]
  have hstab :
      ∃ (ι : Type) (Gi' : ι → Subgroup Q) (next : ι → ι),
        StabilizesNormalSeries (G := Q) (A := H) Gi' next := by
    have hseries : StabilizesNormalSeries (G := Q) (A := H) Gi Nat.succ := by
      refine ⟨⟨0, r + 1, hGi_zero, hGi_bot, ⟨r + 1, ?_⟩⟩,
        hGi_desc, hGi_normal, hGi_inv, hGi_triv⟩
      simpa using Nat.succ_iterate 0 (r + 1)
    exact ⟨Nat, Gi, Nat.succ, hseries⟩
  have hHquot_pi :
      IsPiGroup πset (H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q)) := by
    exact lemma_1_9 (G := Q) (A := H) πset (by infer_instance) hQ_pi
      hstab hker_normal
  have hHquot_p :
      IsPGroup p (H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q)) := by
    refine (IsPGroup.iff_card (p := p) (G := H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q))).2 ?_
    have hpos : 0 < Nat.card (H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q)) := Nat.card_pos (α := H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q))
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne' ?_⟩
    intro q hqprime hqdvd
    let q' : Nat.Primes := ⟨q, hqprime⟩
    have hq_mem : q' ∈ πset := (IsPiGroup_iff πset _).1 hHquot_pi q' hqdvd
    have hq_eq' : q' = ⟨p, Fact.out⟩ := by
      exact Set.mem_singleton_iff.mp hq_mem
    simpa using congrArg Subtype.val hq_eq'
  let qCN : N →* N ⧸ C.subgroupOf N := QuotientGroup.mk' (C.subgroupOf N)
  let φH : H →* N := H.subtype.codRestrict N (by
    intro h
    exact hH_normQ h.2)
  let ψH : H →* N ⧸ C.subgroupOf N := qCN.comp φH
  have hψH_ker : ψH.ker = fixingSubgroupOf H Q (Set.univ : Set Q) := by
    calc
      ψH.ker = C.subgroupOf H := by
        ext h
        change qCN (φH h) = 1 ↔ h ∈ C.subgroupOf H
        have hq :
            qCN (φH h) = 1 ↔ φH h ∈ C.subgroupOf N := by
          simp [qCN]
        have hmem : φH h ∈ C.subgroupOf N ↔ h ∈ C.subgroupOf H := by
          change ((h : G) ∈ C) ↔ ((h : G) ∈ C)
          rfl
        exact hq.trans hmem
      _ = fixingSubgroupOf H Q (Set.univ : Set Q) := hfix_eq_Csub.symm
  let e1 :
      H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q) ≃* H ⧸ ψH.ker :=
    QuotientGroup.quotientMulEquivOfEq hψH_ker.symm
  let e2 : H ⧸ ψH.ker ≃* ψH.range := QuotientGroup.quotientKerEquivRange ψH
  have hHrange_p : IsPGroup p ψH.range := hHquot_p.of_equiv (e1.trans e2)
  have hHrange_eq : ψH.range = (H.subgroupOf N).map qCN := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨h, rfl⟩
      exact Subgroup.mem_map.mpr ⟨φH h, by
        show ((φH h : N) : G) ∈ H
        exact h.2, rfl⟩
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨n, hn, rfl⟩
      let hH : H := ⟨(n : G), hn⟩
      refine ⟨hH, ?_⟩
      change qCN (φH hH) = qCN n
      have hφ : φH hH = n := by
        apply Subtype.ext
        rfl
      rw [hφ]
  have hHmap_p : IsPGroup p ((H.subgroupOf N).map qCN) := by
    rw [← hHrange_eq]
    exact hHrange_p
  have hHmap_normal : ((H.subgroupOf N).map qCN).Normal :=
    (Subgroup.Normal.subgroupOf hH_normal N).map qCN (QuotientGroup.mk'_surjective _)
  have hHmap_le_pCore : (H.subgroupOf N).map qCN ≤ pCore p (N ⧸ C.subgroupOf N) := by
    exact le_sSup ⟨hHmap_normal, hHmap_p⟩
  have hA_sub_le_H_sub : A.subgroupOf N ≤ H.subgroupOf N := by
    intro a ha
    exact hA_le_H ha
  have hAmap_le : (A.subgroupOf N).map qCN ≤ (H.subgroupOf N).map qCN :=
    Subgroup.map_mono hA_sub_le_H_sub
  have hfinal : (A.subgroupOf N).map qCN ≤ pCore p (N ⧸ C.subgroupOf N) :=
    hAmap_le.trans hHmap_le_pCore
  change (A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N)) ≤
      pCore p (N ⧸ C.subgroupOf N)
  simpa [qCN] using hfinal


private theorem pStable_normal_pSubgroup_quotient_of_abelianSylowTwo
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (hSylow : HasAbelianSylow 2 G)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Q A C : Subgroup G} [Q.Normal] [C.Normal]
    (hC : C = Subgroup.centralizer (Q : Set G))
    (hQp : IsPGroup p Q) (hAp : IsPGroup p A)
    (hcomm2 : ⁅⁅Q, A⁆, A⁆ = ⊥) :
    A.map (QuotientGroup.mk' C) ≤ pCore p (G ⧸ C) := by
  classical
  subst C
  let C : Subgroup G := Subgroup.centralizer (Q : Set G)
  have hC_normal : C.Normal := by
    simpa [C] using
      (inferInstance : (Subgroup.centralizer (Q : Set G)).Normal)
  let : C.Normal := hC_normal
  have hQA_cent : ⁅Q, A⁆ ≤ Subgroup.centralizer (A : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm2
  have hQ_normal : Q.Normal := inferInstance
  obtain ⟨r, f, hf0, hfr, hf_norm, hf_chief⟩ :=
    exists_chief_series_from_to Q hQ_normal
  have hf_le_Q : ∀ i, i ≤ r → f i ≤ Q := by
    intro i hi
    induction i with
    | zero =>
        simp [hf0]
    | succ i ih =>
        have hir : i < r := by omega
        exact (hf_chief i hir).lt.le.trans (ih (by omega))
  let cf : Fin r → ChiefFactor (G) := fun i =>
    ⟨f (i.1 + 1), f i.1, hf_chief i.1 i.2⟩
  let H : Subgroup (G) :=
    ⨅ i : Fin r, centralizerOfChiefFactor (G := G) (⊤ : Subgroup (G)) (cf i)
  have hA_le_H : A ≤ H := by
    intro a ha
    rw [Subgroup.mem_iInf]
    intro i
    have hA_le_cf :
        A ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup (G)) (cf i) :=
      pStable_le_centralizerOfChiefFactor_of_abelianSylowTwo
        (G := G) hSylow (p := p) hp2 hQp hAp hcomm2 (cf i)
        (hf_le_Q i.1 (Nat.le_of_lt i.2))
    exact hA_le_cf ha
  have hH_normal : H.Normal := by
    dsimp [H]
    refine Subgroup.normal_iInf_normal (fun i => ?_)
    simpa [cf] using
      (centralizerOfChiefFactor_normal (G := G) (H := (⊤ : Subgroup (G)))
        (hH := (inferInstance : (⊤ : Subgroup (G)).Normal)) (cf i))
  let : H.Normal := hH_normal
  have hH_normQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.le_normalizer_of_normal
  let : MulDistribMulAction H Q :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer H Q hH_normQ
  have hfix_eq_Csub :
      fixingSubgroupOf H Q (Set.univ : Set Q) = C.subgroupOf H := by
    ext h
    rw [mem_fixingSubgroup_iff]
    constructor
    · intro hh
      change (h : G) ∈ C
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hfix : h • (⟨x, hx⟩ : Q) = (⟨x, hx⟩ : Q) := hh ⟨x, hx⟩ (by trivial)
      have hconj : (h : G) * x * (h : G)⁻¹ = x := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH_normQ] using
          congrArg Subtype.val hfix
      simpa [mul_assoc] using
        (congrArg (fun t : G => t * (h : G)) hconj).symm
    · intro hhC x hx
      apply Subtype.ext
      have hcomm : x * (h : G) = (h : G) * x :=
        (Subgroup.mem_centralizer_iff.mp hhC) x (by simp)
      have hconj : (h : G) * x * (h : G)⁻¹ = x := by
        simpa [mul_assoc] using
          congrArg (fun t : G => t * (h : G)⁻¹) hcomm.symm
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH_normQ] using
        hconj
  have hker_normal : (fixingSubgroupOf H Q (Set.univ : Set Q)).Normal := by
    rw [hfix_eq_Csub]
    exact Subgroup.Normal.subgroupOf hC_normal H
  let πset : Set Nat.Primes := {⟨p, Fact.out⟩}
  have hQ_pi : IsPiGroup πset Q := by
    rw [IsPiGroup_iff πset Q]
    intro q hqdvd
    rcases hQp.exists_card_eq with ⟨n, hn⟩
    have hqdvd_pow : q.1 ∣ p ^ n := by
      simpa [hn] using hqdvd
    have hq_eq : q.1 = p := Nat.prime_eq_prime_of_dvd_pow q.2 Fact.out hqdvd_pow
    have hq_eq' : q = ⟨p, Fact.out⟩ := by
      apply Subtype.ext
      simpa using hq_eq
    exact Set.mem_singleton_iff.mpr hq_eq'
  let Gi : ℕ → Subgroup Q := fun i =>
    if hi : i ≤ r then (f i).subgroupOf Q else ⊥
  have hGi_zero : Gi 0 = ⊤ := by
    simp [Gi, hf0]
  have hGi_bot : Gi (r + 1) = ⊥ := by
    simp [Gi]
  have hGi_desc : ∀ i, Gi (i + 1) ≤ Gi i := by
    intro i x hx
    by_cases hi : i < r
    · have hi0 : i ≤ r := Nat.le_of_lt hi
      have hi1 : i + 1 ≤ r := Nat.succ_le_of_lt hi
      have hx' : (x : G) ∈ f (i + 1) := by
        simpa [Gi, hi1, Subgroup.mem_subgroupOf] using hx
      have hx'' : (x : G) ∈ f i := (hf_chief i hi).lt.le hx'
      simpa [Gi, hi0, Subgroup.mem_subgroupOf] using hx''
    · have hi1_not : ¬ i + 1 ≤ r := by omega
      have hxbot : x ∈ (⊥ : Subgroup Q) := by
        simpa [Gi, hi1_not] using hx
      by_cases hi0 : i ≤ r
      · have hi_eq : i = r := by omega
        simpa [Gi, hi0, hi_eq, hfr] using hxbot
      · simpa [Gi, hi0] using hxbot
  have hGi_normal : ∀ i, (Gi i).Normal := by
    intro i
    by_cases hi : i ≤ r
    · simpa [Gi, hi] using Subgroup.Normal.subgroupOf (hf_norm i hi) Q
    · simp [Gi, hi]
  have hGi_inv : ∀ i, IsInvariant H Q (Gi i) := by
    intro i
    by_cases hi : i ≤ r
    · have hH_norm_fi : H ≤ Subgroup.normalizer (f i : Set (G)) := by
        let : (f i).Normal := hf_norm i hi
        simpa using
          (Subgroup.le_normalizer_of_normal (H := f i) :
            H ≤ Subgroup.normalizer (f i : Set (G)))
      refine ⟨?_⟩
      intro h x
      constructor
      · intro hx
        have hx' : (x : G) ∈ f i := by
          simpa [Gi, hi, Subgroup.mem_subgroupOf] using hx
        have hconj : (h : G) * (x : G) * (h : G)⁻¹ ∈ f i :=
          (Subgroup.mem_normalizer_iff.mp (hH_norm_fi h.2) (x : G)).1 hx'
        simpa [Gi, hi, Subgroup.mem_subgroupOf,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH_normQ] using hconj
      · intro hx
        have hhInv : ((h : G)⁻¹) ∈ Subgroup.normalizer (f i : Set (G)) := by
          exact (Subgroup.normalizer (f i : Set (G))).inv_mem (hH_norm_fi h.2)
        have hx' : (h : G) * (x : G) * (h : G)⁻¹ ∈ f i := by
          simpa [Gi, hi, Subgroup.mem_subgroupOf,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH_normQ] using hx
        have hback :
            ((h : G)⁻¹ * (((h : G) * (x : G) * (h : G)⁻¹)) *
              (((h : G)⁻¹)⁻¹)) ∈ f i :=
          (Subgroup.mem_normalizer_iff.mp hhInv _).1 hx'
        have hx'' : (x : G) ∈ f i := by
          simpa [mul_assoc] using hback
        simpa [Gi, hi, Subgroup.mem_subgroupOf] using hx''
    · refine ⟨?_⟩
      intro h x
      constructor
      · intro hx
        have hxbot : x ∈ (⊥ : Subgroup Q) := by
          simpa [Gi, hi] using hx
        have hxEq : x = 1 := by simpa using hxbot
        subst x
        simp [Gi, hi]
      · intro hx
        have hxbot : h • x ∈ (⊥ : Subgroup Q) := by
          simpa [Gi, hi] using hx
        have hxEq : h • x = 1 := by
          simpa using hxbot
        have hx' : ((h : G) * (x : G) * (h : G)⁻¹) = 1 := by
          simpa using (congrArg Subtype.val hxEq : ((h • x : Q) : G) = 1)
        have hx'' : (x : G) = 1 := by
          calc
            (x : G) =
                (h : G)⁻¹ * (((h : G) * (x : G) * (h : G)⁻¹)) *
                  (h : G) := by group
            _ = 1 := by simp [hx']
        have hxbot : x ∈ (⊥ : Subgroup Q) := by
          apply Subgroup.mem_bot.mpr
          apply Subtype.ext
          simpa using hx''
        simpa [Gi, hi] using hxbot
  have hGi_triv :
      ∀ i (aH : H) (x : Q), x ∈ Gi i → (aH • x) * x⁻¹ ∈ Gi (i + 1) := by
    intro i aH x hx
    by_cases hi : i < r
    · let cfi : ChiefFactor (G) := ⟨f (i + 1), f i, hf_chief i hi⟩
      have hH_cent :
          H ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup (G)) cfi := by
        let j : Fin r := ⟨i, hi⟩
        have htmp :
            H ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup (G)) (cf j) :=
          iInf_le _ j
        simpa [cfi, cf, j] using htmp
      have hcomm_le : ⁅H, cfi.U⁆ ≤ cfi.V :=
          (le_centralizerOfChiefFactor_iff
            (G := G) (H := (⊤ : Subgroup (G))) (N := H) (cf := cfi)).1 hH_cent |>.2
      have hxfi : (x : G) ∈ f i := by
        simpa [Gi, Nat.le_of_lt hi, Subgroup.mem_subgroupOf] using hx
      have hmem : ⁅(aH : G), (x : G)⁆ ∈ f (i + 1) := by
        exact hcomm_le (Subgroup.commutator_mem_commutator aH.property hxfi)
      have hi1 : i + 1 ≤ r := Nat.succ_le_of_lt hi
      simpa [Gi, hi1, Subgroup.mem_subgroupOf,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        div_eq_mul_inv, commutatorElement_def, mul_assoc] using hmem
    · have hxbot : x ∈ (⊥ : Subgroup Q) := by
        by_cases hir : i ≤ r
        · have hi_eq : i = r := by omega
          simpa [Gi, hir, hi_eq, hfr] using hx
        · simpa [Gi, hir] using hx
      have hx_eq_one : x = 1 := by simpa using hxbot
      have hi1_not : ¬ i + 1 ≤ r := by omega
      subst x
      simp [Gi, hi1_not]
  have hstab :
      ∃ (ι : Type) (Gi' : ι → Subgroup Q) (next : ι → ι),
        StabilizesNormalSeries (G := Q) (A := H) Gi' next := by
    have hseries : StabilizesNormalSeries (G := Q) (A := H) Gi Nat.succ := by
      refine ⟨⟨0, r + 1, hGi_zero, hGi_bot, ⟨r + 1, ?_⟩⟩,
        hGi_desc, hGi_normal, hGi_inv, hGi_triv⟩
      simpa using Nat.succ_iterate 0 (r + 1)
    exact ⟨Nat, Gi, Nat.succ, hseries⟩
  have hHquot_pi :
      IsPiGroup πset (H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q)) := by
    exact lemma_1_9 (G := Q) (A := H) πset (by infer_instance) hQ_pi
      hstab hker_normal
  have hHquot_p :
      IsPGroup p (H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q)) := by
    refine (IsPGroup.iff_card (p := p) (G := H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q))).2 ?_
    have hpos : 0 < Nat.card (H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q)) := Nat.card_pos (α := H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q))
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne' ?_⟩
    intro q hqprime hqdvd
    let q' : Nat.Primes := ⟨q, hqprime⟩
    have hq_mem : q' ∈ πset := (IsPiGroup_iff πset _).1 hHquot_pi q' hqdvd
    have hq_eq' : q' = ⟨p, Fact.out⟩ := by
      exact Set.mem_singleton_iff.mp hq_mem
    simpa using congrArg Subtype.val hq_eq'

  let qC : G →* G ⧸ C := QuotientGroup.mk' C
  let ψH : H →* G ⧸ C := qC.comp H.subtype
  have hψH_ker : ψH.ker = C.subgroupOf H := by
    ext h
    change qC (h : G) = 1 ↔ (h : G) ∈ C
    simp [qC]
  let e1 :
      H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q) ≃* H ⧸ ψH.ker :=
    QuotientGroup.quotientMulEquivOfEq
      (hfix_eq_Csub.trans hψH_ker.symm)
  let e2 : H ⧸ ψH.ker ≃* ψH.range :=
    QuotientGroup.quotientKerEquivRange ψH
  have hHrange_p : IsPGroup p ψH.range :=
    hHquot_p.of_equiv (e1.trans e2)
  have hHrange_eq : ψH.range = H.map qC := by
    ext y
    simp [ψH]
  have hHrange_normal : ψH.range.Normal := by
    rw [hHrange_eq]
    exact hH_normal.map qC (QuotientGroup.mk'_surjective C)
  have hHrange_le_pCore : ψH.range ≤ pCore p (G ⧸ C) :=
    le_sSup ⟨hHrange_normal, hHrange_p⟩
  have hAmap_le : A.map qC ≤ H.map qC :=
    Subgroup.map_mono hA_le_H
  have hfinal : A.map qC ≤ pCore p (G ⧸ C) := by
    rw [← hHrange_eq] at hAmap_le
    exact hAmap_le.trans hHrange_le_pCore
  simpa [C, qC] using hfinal

/-- A finite solvable group with abelian Sylow `2`-subgroups is `p`-stable
for every odd prime `p`, in the operational form used by Glauberman's ZJ
theorem. -/
public theorem pStableGroup'_of_solvable_abelianSylowTwo
    {G : Type*} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G) (hSylow : HasAbelianSylow 2 G)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) :
    PStableGroup' (G := G) p := by
  classical
  let : Group.IsSolvable G := hsolv
  have hp2 : p ≠ 2 := by
    intro hp
    subst p
    exact (by decide : ¬ Odd 2) hpodd
  intro Q A _hMQ_normal hQp hAp hA_norm hcomm2
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  let C : Subgroup G := Subgroup.centralizer (Q : Set G)
  have hQleN : Q ≤ N := by
    simpa [N] using (Subgroup.le_normalizer : Q ≤ Subgroup.normalizer (Q : Set G))
  let QN : Subgroup N := Q.subgroupOf N
  let AN : Subgroup N := A.subgroupOf N
  have hQNnormal : QN.Normal := by
    dsimp [QN]
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQleN).2
    simp [N]
  let : QN.Normal := hQNnormal
  have hQNp : IsPGroup p QN :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQleN).symm
  have hANp : IsPGroup p AN :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hA_norm).symm
  have hcommMap :
      (⁅⁅QN, AN⁆, AN⁆).map N.subtype = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hQleN,
      Subgroup.map_subgroupOf_eq_of_le hA_norm, hcomm2]
  have hcomm2N : ⁅⁅QN, AN⁆, AN⁆ = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective
      (H := ⁅⁅QN, AN⁆, AN⁆) (f := N.subtype)
      N.subtype_injective).1 hcommMap
  let : Group.IsSolvable N := by infer_instance
  have hcentralizer :
      Subgroup.centralizer (QN : Set N) = C.subgroupOf N := by
    simpa [QN, N, C] using
      (centralizer_subgroupOf_normalizer_eq (R := Q))
  have hCnormal : (C.subgroupOf N).Normal := by
    rw [← hcentralizer]
    infer_instance
  let : (C.subgroupOf N).Normal := hCnormal
  have hresult :=
    pStable_normal_pSubgroup_quotient_of_abelianSylowTwo
      (G := N) (hSylow.subgroup N) (p := p) hp2
      (C := C.subgroupOf N) hcentralizer.symm
      hQNp hANp hcomm2N
  change (A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N)) ≤
    pCore p (N ⧸ C.subgroupOf N)
  simpa [AN] using hresult

end ZModPrime

end CFSG.BenderSuzuki
