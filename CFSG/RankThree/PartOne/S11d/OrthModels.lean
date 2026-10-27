module

public import CFSG.RankThree.PartOne.S11d.OrthLayer
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.RankThree.PartOne

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LieType.Universal.Spin
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedOmega StatedQuadPlus StatedQuadMinus)
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff centerQuotientEquivSelf)

section Transport

variable {K : Type} [Field K]

@[expose] def linConj {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (e : V ≃ₗ[K] V') : (V ≃ₗ[K] V) ≃* (V' ≃ₗ[K] V') where
  toFun g := e.symm.trans (g.trans e)
  invFun g := e.trans (g.trans e.symm)
  left_inv g := by ext v; simp
  right_inv g := by ext v; simp
  map_mul' g h := by ext v; simp

theorem linConj_apply {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (e : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (v : V') : linConj e g v = e (g (e.symm v)) := rfl

variable {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}

theorem map_orthogonalGroup_linConj (e : Q.IsometryEquiv Q') :
    (TauCeti.QuadraticMap.orthogonalGroup Q).map (linConj e.toLinearEquiv).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q' := by
  ext g'
  rw [Subgroup.mem_map, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩ v
    have hg' := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
    change Q' (e (g (e.symm v))) = Q' v
    rw [e.map_app, hg', e.symm.map_app]
  · intro hg'
    refine ⟨(linConj e.toLinearEquiv).symm g', ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    change Q (e.symm (g' (e v))) = Q v
    rw [e.symm.map_app, hg', e.map_app]

theorem map_orthDerived_linConj (e : Q.IsometryEquiv Q') :
    (orthDerived Q).map (linConj e.toLinearEquiv).toMonoidHom = orthDerived Q' := by
  rw [orthDerived, orthDerived, Subgroup.map_commutator, map_orthogonalGroup_linConj]

@[expose] def orthDerivedEquiv (e : Q.IsometryEquiv Q') : orthDerived Q ≃* orthDerived Q' :=
  ((linConj e.toLinearEquiv).subgroupMap (orthDerived Q)).trans
    (MulEquiv.subgroupCongr (map_orthDerived_linConj e))

end Transport

section Center

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem center_orthDerived_eq_bot [Finite K] [Nontrivial V] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Subgroup.center ↥(orthDerived Q) = ⊥ := by
  obtain ⟨-, hc, -⟩ := CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts
    hQ hT
  rw [hc, eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  exact Subtype.ext (eq_one_of_mem_scalars_of_mem_orthDerived hQ g.2 (Subgroup.mem_subgroupOf.mp hg))

end Center

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W} {G : Type} [Group G] {m f : ℕ}

omit [FiniteDimensional K W] in
theorem lieModel_of_orthDerived_plus (hm : 4 ≤ m) (hf : 1 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (e : R.IsometryEquiv (quadPlus m K)) (φ : G ≃* ↥(orthDerived R)) :
    LieModel G .POmegaPlus m 2 f := by
  obtain ⟨hnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := m) (by omega)
  have : Inhabited (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have : Nontrivial (Fin m ⊕ Fin m → K) := Pi.nontrivial
  let ψ : G ≃* StatedProj (StatedOmega (StatedQuadPlus m K)) :=
    φ.trans ((orthDerivedEquiv e).trans ((MulEquiv.ofBijective (piOrth (quadPlus m K))
      ⟨piOrth_injective hnd, piOrth_surjective⟩).trans
      (statedProjOrthEquiv (coe_quadPlus (n := m) (K := K))).symm))
  exact (lieModel_classical_iff (by decide)).mpr ⟨⟨Nat.prime_two, hf, hm⟩, K, inferInstance,
    inferInstance, hcard, ⟨ψ⟩⟩

omit [FiniteDimensional K W] in
theorem lieModel_of_orthDerived_minus (hm : 4 ≤ m) (hf : 1 ≤ f) (hcard : Nat.card K = 2 ^ f)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (e : R.IsometryEquiv (quadMinus m K b c))
    (φ : G ≃* ↥(orthDerived R)) : LieModel G .POmegaMinus m 2 f := by
  obtain ⟨hnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := m) hm hirr
  have : Inhabited (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have : Nontrivial (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := Pi.nontrivial
  let ψ : G ≃* StatedProj (StatedOmega (StatedQuadMinus m K b c)) :=
    φ.trans ((orthDerivedEquiv e).trans ((MulEquiv.ofBijective (piOrth (quadMinus m K b c))
      ⟨piOrth_injective hnd, piOrth_surjective⟩).trans
      (statedProjOrthEquiv (coe_quadMinus m K b c)).symm))
  exact (lieModel_classical_iff (by decide)).mpr ⟨⟨Nat.prime_two, hf, hm⟩, K, inferInstance,
    inferInstance, hcard, b, c, hirr, ⟨ψ⟩⟩

theorem exists_lieModel_quotient_of_orthDerived (hR : (polarBilin R).Nondegenerate)
    (hm : 4 ≤ m) (hdim : finrank K W = 2 * m) (hf : 1 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (φ : G ≃* ↥(orthDerived R)) :
    ∃ (t' : StatedLieTag) (n' : ℕ), LieModel (G ⧸ Subgroup.center G) t' n' 2 f := by
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus R hR (by omega) hdim with
    he | ⟨b, c, hirr, he⟩
  · obtain ⟨e⟩ := he
    obtain ⟨hnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := m)
      (by omega)
    have : Inhabited (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have : Nontrivial (Fin m ⊕ Fin m → K) := Pi.nontrivial
    have hZ : Subgroup.center ↥(orthDerived (quadPlus m K)) = ⊥ := center_orthDerived_eq_bot hnd hT
    let φ' := φ.trans (orthDerivedEquiv e)
    have hZG : Subgroup.center G = ⊥ := by
      have h1 := Subgroup.map_center_eq φ'
      rw [hZ] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ φ'.injective).mp h1
    exact ⟨.POmegaPlus, m, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (centerQuotientEquivSelf hZG).symm (lieModel_of_orthDerived_plus hm hf hcard e φ)⟩
  · obtain ⟨e⟩ := he
    obtain ⟨hnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := m) hm hirr
    have : Inhabited (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have : Nontrivial (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := Pi.nontrivial
    have hZ : Subgroup.center ↥(orthDerived (quadMinus m K b c)) = ⊥ :=
      center_orthDerived_eq_bot hnd hT
    let φ' := φ.trans (orthDerivedEquiv e)
    have hZG : Subgroup.center G = ⊥ := by
      have h1 := Subgroup.map_center_eq φ'
      rw [hZ] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ φ'.injective).mp h1
    exact ⟨.POmegaMinus, m, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (centerQuotientEquivSelf hZG).symm (lieModel_of_orthDerived_minus hm hf hcard hirr e φ)⟩

end Model

end CFSG.RankThree.PartOne
