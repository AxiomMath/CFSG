module

public import CFSG.RankThree.Lattice.SteinbergBIE6QplusFold
public import CFSG.RankThree.Lattice.SteinbergBIE6QplusStab

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 Matrix

theorem setReflection_e6QpC (m : Fin 15) :
    setReflection {β | β ∈ e6QpC m} = e6Longest (e6QpSupport m) := by
  obtain ⟨hnd, hmem, horth, hact⟩ := e6QpC_check m
  have hroot : ∀ β ∈ e6QpC m, IsRoot Tag.E6 β := fun β hβ =>
    isRoot_iff_mem_artifactRoots.2 (hmem β hβ).1
  have hcomm : {β | β ∈ e6QpC m}.Pairwise fun β γ => Commute (rootReflection β)
      (rootReflection γ) := fun β hβ γ hγ hne =>
    commute_rootReflection_of_iform_eq_zero (hroot β hβ) (hroot γ hγ) (horth β hβ γ hγ hne)
  rw [setReflection_eq_list_prod (List.finite_toSet _) hcomm hnd (fun β => Iff.rfl),
    e6Longest_qp]
  refine ext_single fun i => ?_
  rw [wordProd_smul, ← hact i]
  have key : ∀ l : List (Fin Tag.E6.rank → ℤ), (∀ β ∈ l, IsRoot Tag.E6 β) →
      ∀ v, (l.map rootReflection).prod • v = l.foldr (fun β v => v - corootPair β v • β) v := by
    intro l hl v
    induction l with
    | nil => simp
    | cons β l ih =>
      rw [List.map_cons, List.prod_cons, mul_smul, ih fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ),
        rootReflection_smul (hl β List.mem_cons_self), List.foldr_cons]
  exact key _ hroot _

theorem E6_even_qplus_folded_parabolic_kernels_and_prime_five_stabilizers :
    (∀ v, e6W0 • v = -permLattice e6Rho v) ∧
    (∀ w : WeylGroup Tag.E6, (coxeterSystem Tag.E6).length w ≤
      (coxeterSystem Tag.E6).length e6W0) ∧
    (∀ α, IsRoot Tag.E6 α → permLattice e6Rho α ≠ α → iform α (permLattice e6Rho α) = 0) ∧
    (∀ w : WeylGroup Tag.E6, w ∈ e6WGamma ↔
      ∀ x, w • permLattice e6Rho x = permLattice e6Rho (w • x)) ∧
    Nat.card (e6WGamma) = 1152 ∧
    e6WGamma = Subgroup.closure {simple Tag.E6 0 * simple Tag.E6 5,
      simple Tag.E6 2 * simple Tag.E6 4, simple Tag.E6 3, simple Tag.E6 1} ∧
    (∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ z : Fin Tag.E6.rank → ZMod p, z ≠ 0 →
      (∀ i, z (e6Rho i) = z i) →
        dualWeylStabilizer z = Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α} ∧
        ∃ w ∈ e6WGamma, ∃ J : Set (Fin Tag.E6.rank), J ≠ Set.univ ∧
          (∀ i, i ∈ J ↔ e6Rho i ∈ J) ∧ (w • ·) '' rootKernel z = parabolicRoots Tag.E6 J) ∧
    (∀ J : Set (Fin Tag.E6.rank),
      (J ≠ Set.univ ∧ ∀ i, i ∈ J ↔ e6Rho i ∈ J) ↔ ∃ m, J = e6QpSupport m) ∧
    ∀ m : Fin 15,
      (∀ j, j ∈ e6QpSupport m ↔ e6QpPerm m j ∈ e6QpSupport m) ∧
      (∀ j ∈ e6QpSupport m,
        e6Delta (e6QpSupport m) (Pi.single j 1) = Pi.single (e6QpPerm m j) 1) ∧
      (∀ α ∈ parabolicRoots Tag.E6 (e6QpSupport m),
        e6Delta (e6QpSupport m) (e6Delta (e6QpSupport m) α) = α) ∧
      (∀ α ∈ parabolicRoots Tag.E6 (e6QpSupport m), e6Delta (e6QpSupport m) α ≠ α →
        iform α (e6Delta (e6QpSupport m) α) ≠ 0 →
          (m = 12 ∨ m = 13) ∧ α ∈ parabolicRoots Tag.E6 {1, 3}) ∧
      ((m = 12 ∨ m = 13) → e6Delta (e6QpSupport m) (Pi.single 1 1) = Pi.single 3 1 ∧
        iform (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) (Pi.single 3 1) ≠ 0) ∧
      (m = 14 → e6Delta (e6QpSupport m) (Pi.single 2 1) = Pi.single 4 1 ∧
        e6Delta (e6QpSupport m) (Pi.single 4 1) = Pi.single 2 1 ∧
        e6Delta (e6QpSupport m) (Pi.single 1 1) = Pi.single 1 1 ∧
        e6Delta (e6QpSupport m) (Pi.single 3 1) = Pi.single 3 1) ∧
      (∃ C : Set (Fin Tag.E6.rank → ℤ), C ⊆ parabolicRoots Tag.E6 (e6QpSupport m) ∧
        (∀ β ∈ C, 0 < height β) ∧ (∀ β ∈ C, e6Delta (e6QpSupport m) β ∈ C) ∧
        C.Pairwise (fun β β' => iform β β' = 0) ∧
        setReflection C = e6Longest (e6QpSupport m)) ∧
      ∀ i₀ ∈ e6QpSupport m, e6XiOrth (e6QpSupport m) i₀ →
        (∀ O ∈ e6Orbits (e6QpSupport m) i₀, ∀ O' ∈ e6Orbits (e6QpSupport m) i₀,
          Relation.ReflTransGen (fun A B => A ∈ e6Orbits (e6QpSupport m) i₀ ∧
            B ∈ e6Orbits (e6QpSupport m) i₀ ∧ ∃ β ∈ A, ∃ β' ∈ B, iform β β' ≠ 0) O O') ∧
        (∀ γ ∈ e6Xi (e6QpSupport m) i₀, ∃ w ∈ e6RelWeyl (e6QpSupport m) i₀,
          ∃ O ∈ e6Orbits (e6QpSupport m) i₀,
            (w • ·) '' O = e6RootOrbit (e6QpSupport m) γ) ∧
        (∀ O ∈ e6Orbits (e6QpSupport m) i₀, ∀ w ∈ e6RelWeyl (e6QpSupport m) i₀,
          (e6RelLength (e6QpSupport m) i₀ (setReflection O * w) =
              e6RelLength (e6QpSupport m) i₀ w + 1 ↔ ∀ β ∈ O, 0 < height (w⁻¹ • β)) ∧
          (e6RelLength (e6QpSupport m) i₀ (setReflection O * w) =
              e6RelLength (e6QpSupport m) i₀ w + 1 ∨
            e6RelLength (e6QpSupport m) i₀ (setReflection O * w) + 1 =
              e6RelLength (e6QpSupport m) i₀ w)) ∧
        ∀ O ∈ e6Orbits (e6QpSupport m) i₀, ∀ O' ∈ e6Orbits (e6QpSupport m) i₀, O ≠ O' →
          (∃ β ∈ O, ∃ β' ∈ O', iform β β' ≠ 0) →
            e6RelLength (e6QpSupport m) i₀
              (setReflection O * setReflection O' * setReflection O) = 3 := by
  refine ⟨e6W0_smul, fun w => ?_, fun α hα hne => iform_rho_eq_zero hα hne,
    fun w => mem_e6WGamma_iff, card_e6WGamma, e6WGamma_eq_closure,
    fun p _ hp3 z hz0 hzγ => ⟨dualWeylStabilizer_gammaFixed_eq_closure hp3 hz0 hzγ,
      exists_relWeylTwist_smul_rootKernel hp3 hz0 hzγ⟩,
    gammaStable_iff_mem_e6QpSupport, fun m => ?_⟩
  · have h := (CFSG.Monster.B.Geometry.isLongest_longest (cs := coxeterSystem Tag.E6)
      (Set.univ : Set (Fin Tag.E6.rank))).2 w (by
        rw [CoxeterSystem.parabolic_univ]
        trivial)
    exact h
  refine ⟨e6QpPerm_mem_iff m, fun j hj => e6Delta_qp_single m hj,
    fun α _ => e6Delta_qp_involutive m α, fun α hα hne hnz => ?_, fun hm => ?_, fun hm => ?_,
    ⟨{β | β ∈ e6QpC m}, ?_, ?_, ?_, ?_, setReflection_e6QpC m⟩,
    fun i₀ hi₀ horth => ⟨fun O hO O' hO' => e6Orbits_connected m hi₀ hO hO',
      fun γ hγ => exists_smul_e6Orbit_eq m hi₀ horth hγ,
      fun O hO w hw => e6RelLength_mul m hi₀ horth hO hw,
      fun O hO O' hO' hne hadj => e6RelLength_braid m hi₀ horth hO hO' hne hadj⟩⟩
  · obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα.1
    rw [e6Delta_qp] at hne hnz
    obtain ⟨hm, hsupp⟩ := e6QpDelta_nonorth hl (fun i hi => hα.2 i hi) hne hnz
    refine ⟨hm, hα.1, fun i hi => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
    exact hsupp i hi.1 hi.2
  · obtain ⟨h1, h2⟩ := e6QpDelta_exception m hm
    rw [e6Delta_qp]
    exact ⟨h1, by rw [h2]; norm_num⟩
  · subst hm
    obtain ⟨h1, h2, h3, h4⟩ := e6QpDelta_D4
    simp only [e6Delta_qp]
    exact ⟨h1, h2, h3, h4⟩
  · intro β hβ
    have h := ((e6QpC_check m).2.1 β hβ)
    exact ⟨isRoot_iff_mem_artifactRoots.2 h.1, fun i hi => h.2.2.1 i hi⟩
  · intro β hβ
    exact ((e6QpC_check m).2.1 β hβ).2.1
  · intro β hβ
    rw [e6Delta_qp]
    exact ((e6QpC_check m).2.1 β hβ).2.2.2
  · intro β hβ β' hβ' hne
    exact (e6QpC_check m).2.2.1 β hβ β' hβ' hne

end CFSG.RankThree.Lattice
