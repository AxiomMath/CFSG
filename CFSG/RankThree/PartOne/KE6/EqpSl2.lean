module

public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityConjugacy
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenComponents
public import CFSG.RankThree.PartOne.KE6.EqpOpp

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix MatrixGroups Pointwise

section Finite

theorem e6_gammaFixed_support : ∀ k : Fin 72,
    permLattice e6Rho (e6RootVec k) = e6RootVec k → e6RootVec k 1 ≠ 0 ∨ e6RootVec k 3 ≠ 0 := by
  decide +kernel

theorem e6Qp_mem_one_or_three (m : Fin 15)
    (h : ∃ β ∈ parabolicRoots Tag.E6 (e6QpSupport m), permLattice e6Rho β = β) :
    (1 : Fin Tag.E6.rank) ∈ e6QpSupportList m ∨ (3 : Fin Tag.E6.rank) ∈ e6QpSupportList m := by
  obtain ⟨β, ⟨hβ, hsupp⟩, hfix⟩ := h
  obtain ⟨k, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hβ
  by_contra hcon
  rw [not_or] at hcon
  have h1 := hsupp 1 hcon.1
  have h3 := hsupp 3 hcon.2
  rcases e6_gammaFixed_support k hfix with h | h
  · exact h h1
  · exact h h3

theorem e6Qp_fixed_simple : ∀ m : Fin 15, m ≠ 12 → m ≠ 13 →
    ((1 : Fin Tag.E6.rank) ∈ e6QpSupportList m ∨ (3 : Fin Tag.E6.rank) ∈ e6QpSupportList m) →
    ∃ j : Fin Tag.E6.rank, (j = 1 ∨ j = 3) ∧ j ∈ e6QpSupportList m ∧ e6QpPerm m j = j := by
  decide +kernel

theorem e6QpSupportList_inj : ∀ m m' : Fin 15,
    (∀ i : Fin Tag.E6.rank, i ∈ e6QpSupportList m ↔ i ∈ e6QpSupportList m') → m = m' := by
  decide +kernel

theorem e6QpSupport_inj {m m' : Fin 15} (h : e6QpSupport m = e6QpSupport m') : m = m' :=
  e6QpSupportList_inj m m' fun i => by
    have := Set.ext_iff.1 h i
    exact this

end Finite

section Datum

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω]

theorem eqp_sl2_datum (D : E6EvenFixedRootDatum Ω) {K : Type} [Field K] [Finite K]
    [Algebra K Ω] (hK : Nat.card K = 2 ^ D.f) {j : Fin Tag.E6.rank}
    (hj : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ D.Ξ)
    (hfix : D.δ (Pi.single j 1) = Pi.single j 1) (B : SL(2, K)) :
    simpleRootSL2 Tag.E6 Ω j (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) ∈
      D.orbitGroup := by
  classical
  set O := D.simpleOrbit j with hOdef
  have hO : O ∈ D.orbits := ⟨j, hj, rfl⟩
  have hOs : O = {Pi.single j 1} := by
    ext β
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact Function.iterate_fixed hfix k
    · rintro rfl
      exact ⟨0, rfl⟩
  have h1 : E6EvenFixedRootDatum.orbitCard O = 1 := by
    rw [E6EvenFixedRootDatum.orbitCard, hOs, Set.ncard_singleton]
  have hroot : E6EvenFixedRootDatum.orbitRoot O = Pi.single j 1 := by
    have h := D.orbitRoot_mem hO
    generalize E6EvenFixedRootDatum.orbitRoot O = r at h ⊢
    rw [hOs] at h
    exact h
  have hmem : ∀ b : K, algebraMap K Ω b ∈ D.orbitField O := fun b => by
    rw [D.mem_orbitField, h1, pow_one, ← map_pow]
    have : b ^ D.q = b := by
      have hq : D.q = Nat.card K := by rw [E6EvenFixedRootDatum.q, hK]
      rw [hq]
      have : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card b
    rw [this]
  let φ : K →+* D.orbitField O := (algebraMap K Ω).codRestrict (D.orbitField O) hmem
  have hsub : (D.orbitField O).subtype.comp φ = algebraMap K Ω := rfl
  have hA := D.orbitMap_mem_orbitGroup hO (Matrix.SpecialLinearGroup.map φ B)
  have hform : D.orbitMap O (Matrix.SpecialLinearGroup.map φ B) =
      simpleRootSL2 Tag.E6 Ω j (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) := by
    rw [E6EvenFixedRootDatum.orbitMap, h1, List.range_one, List.map_singleton, List.prod_singleton,
      hroot, Function.iterate_zero, id, ← CFSG.RankThree.Chevalley.rootSL2_single_apply]
    congr 1
    ext a b
    simp [φ, Matrix.SpecialLinearGroup.map_apply_coe, mul_zero, iterateFrobenius]
  rw [← hform]
  exact hA

end Datum

section Psi

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω]

theorem eqp_pow_card {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (b : K) :
    b ^ 2 ^ f = b := by
  have : Fintype K := Fintype.ofFinite K
  rw [← hK, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card b

omit [IsAlgClosed Ω] in
theorem eqp_map_frob_fixed {K : Type} [Field K] [Finite K] [Algebra K Ω] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (B : SL2 K) :
    Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f)
        (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) =
      Matrix.SpecialLinearGroup.map (algebraMap K Ω) B := by
  ext a b
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    iterateFrobenius_def, ← map_pow, eqp_pow_card hK]

theorem single_mem_e6Xi {J : Set (Fin Tag.E6.rank)} {j : Fin Tag.E6.rank} :
    (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ e6Xi J j :=
  Set.mem_iUnion.2 ⟨0, Pi.single j 1, single_mem_parabolicRoots (mem_e6JComponent_self J j), rfl⟩

theorem iform_e6ε_e6ε' : CFSG.LieType.Steinberg.Adjoint.iform e6ε e6ε' = -1 := by
  decide +kernel

theorem e6Delta_e6ε_add {J : Set (Fin Tag.E6.rank)}
    (hJ : J = e6QpSupport 12 ∨ J = e6QpSupport 13) :
    e6Delta J (e6ε + e6ε') = e6ε + e6ε' := by
  have h : ∀ x y, e6Delta J (x + y) = e6Delta J x + e6Delta J y := by
    intro x y
    rcases hJ with rfl | rfl
    · rw [e6Delta_qp, e6Delta_qp, e6Delta_qp, Matrix.mulVec_add]
    · rw [e6Delta_qp, e6Delta_qp, e6Delta_qp, Matrix.mulVec_add]
  rw [h, e6Delta_e6ε hJ, e6Delta_e6ε' hJ, add_comm]

omit [IsAlgClosed Ω] in
theorem eqp_sl2_a2 {K : Type} [Field K] [Finite K] [Algebra K Ω] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) {J : Set (Fin Tag.E6.rank)}
    (hJ : J = e6QpSupport 12 ∨ J = e6QpSupport 13) :
    ∃ (j : Fin Tag.E6.rank) (h₀ : ModGL Tag.E6 Ω), ∀ B : SL(2, K),
      h₀ * simpleRootSL2 Tag.E6 Ω j (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * h₀⁻¹ ∈
        e6P24 Ω J f := by
  have hγ₀ := isRoot_e6ε_add
  have hmem : e6ε + e6ε' ∈ parabolicRoots Tag.E6 e6Supp24 := e6ε_add_mem
  have hneg : -(e6ε + e6ε') ∈ parabolicRoots Tag.E6 e6Supp24 :=
    ⟨IsRoot.neg hγ₀, fun i hi => by simp [hmem.2 i hi]⟩
  obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 hγ₀
  refine ⟨j, canonicalRep (coxeterSystem Tag.E6) Ω w, fun B => ?_⟩
  set M : SL2 Ω := Matrix.SpecialLinearGroup.map (algebraMap K Ω) B with hM
  have hconj := canonicalRep_conj_rootSL2 (Ω := Ω) w (isRoot_single Tag.E6 j) M
  rw [CFSG.RankThree.Chevalley.rootSL2_single_apply, hwj] at hconj
  rw [hconj]
  refine ⟨rootSL2_mem_rootSpan hγ₀ hmem hneg M, ?_⟩
  show e6Psi Ω J f (rootSL2 Tag.E6 Ω (e6ε + e6ε') M) = rootSL2 Tag.E6 Ω (e6ε + e6ε') M
  rw [e6Psi_rootSL2 J f hγ₀, e6Delta_e6ε_add hJ, hM, eqp_map_frob_fixed hK]

theorem eqp_sl2_psi {K : Type} [Field K] [Finite K] [Algebra K Ω] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (m : Fin 15) {ι : Type} (Ξ : ι → Set (Fin Tag.E6.rank → ℤ))
    (P : ι → Subgroup (ModGL Tag.E6 Ω))
    (hrange : Set.range Ξ = e6ComponentOrbits (e6QpSupport m))
    (hP : ∀ k, IsE6EvenFactor Ω (e6QpSupport m) f (Ξ k) (P k))
    (hfix : ∃ α ∈ parabolicRoots Tag.E6 (e6QpSupport m), permLattice e6Rho α = α) :
    ∃ (k : ι) (j : Fin Tag.E6.rank) (h₀ : ModGL Tag.E6 Ω), ∀ B : SL(2, K),
      h₀ * simpleRootSL2 Tag.E6 Ω j (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * h₀⁻¹ ∈
        P k := by
  classical
  have h13 := e6Qp_mem_one_or_three m hfix
  by_cases hm : m = 12 ∨ m = 13
  · have h1 : (1 : Fin Tag.E6.rank) ∈ e6QpSupport m := by
      rcases hm with rfl | rfl
      · exact one_mem_e6Supp24
      · show (1 : Fin Tag.E6.rank) ∈ e6QpSupportList 13
        decide
    obtain ⟨k, hk⟩ : e6Xi (e6QpSupport m) 1 ∈ Set.range Ξ := by
      rw [hrange]
      exact ⟨1, h1, rfl⟩
    have hJ : e6QpSupport m = e6QpSupport 12 ∨ e6QpSupport m = e6QpSupport 13 := by
      rcases hm with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hP k with ⟨D, hDJ, hDf, hDΞ, hPD⟩ | ⟨-, -, hPe⟩
    · exfalso
      have hJ' : D.J = e6QpSupport 12 ∨ D.J = e6QpSupport 13 := by
        rw [hDJ]
        exact hJ
      have hα : (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) ∈ D.Ξ := by
        rw [hDΞ, hk]
        exact single_mem_e6Xi
      have hδ : e6Delta D.J (Pi.single 1 1) = Pi.single 3 1 := e6Delta_e6ε hJ'
      have hne : (e6Delta D.J)^[1] (Pi.single 1 1) ≠ Pi.single 1 1 := by
        rw [Function.iterate_one, hδ]
        intro h
        have := congrFun h 1
        simp at this
      have h0 := D.orthogonal _ hα 1 hne
      rw [Function.iterate_one, hδ] at h0
      have h2 : CFSG.LieType.Steinberg.Adjoint.iform e6ε e6ε' = 0 := h0
      rw [iform_e6ε_e6ε'] at h2
      exact absurd h2 (by norm_num)
    · obtain ⟨j, h₀, h⟩ := eqp_sl2_a2 (Ω := Ω) (f := f) hK hJ
      exact ⟨k, j, h₀, fun B => hPe ▸ h B⟩
  · rw [not_or] at hm
    obtain ⟨j, -, hjJ, hjperm⟩ := e6Qp_fixed_simple m hm.1 hm.2 h13
    have hjJ' : j ∈ e6QpSupport m := hjJ
    obtain ⟨k, hk⟩ : e6Xi (e6QpSupport m) j ∈ Set.range Ξ := by
      rw [hrange]
      exact ⟨j, hjJ', rfl⟩
    rcases hP k with ⟨D, hDJ, hDf, hDΞ, hPD⟩ | ⟨hJ, -, -⟩
    · refine ⟨k, j, 1, fun B => ?_⟩
      have hα : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ D.Ξ := by
        rw [hDΞ, hk]
        exact single_mem_e6Xi
      have hfixδ : D.δ (Pi.single j 1) = Pi.single j 1 := by
        show e6Delta D.J (Pi.single j 1) = _
        rw [hDJ, e6Delta_qp, (e6QpPerm_check m).2 j hjJ, hjperm]
      have hKD : Nat.card K = 2 ^ D.f := by
        rw [hDf]
        exact hK
      have := eqp_sl2_datum D hKD hα hfixδ B
      rw [hPD]
      simpa using this
    · exfalso
      rcases hJ with h | h
      · exact hm.1 (e6QpSupport_inj h)
      · exact hm.2 (e6QpSupport_inj h)

end Psi

end CFSG.RankThree.PartOne.KE6
