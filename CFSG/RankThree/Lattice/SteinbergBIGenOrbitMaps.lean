module

public import CFSG.RankThree.Lattice.SteinbergBIGenFoldedWeyl
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

include D in
theorem iform_self_eq_two {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : iform α α = 2 := by
  rw [← dotProduct_mulVec_eq_iform]
  exact rootForm_self D.simplyLaced hα

include D in
theorem not_isRoot_add_sub {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (h0 : iform β γ = 0) : ¬IsRoot τ (β + γ) ∧ ¬IsRoot τ (β - γ) := by
  have h0' : iform γ β = 0 := by rw [iform_comm]; exact h0
  have hβ2 := D.iform_self_eq_two hβ
  have hγ2 := D.iform_self_eq_two hγ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have e := D.iform_self_eq_two h
    rw [iform_add_left, iform_add_right, iform_add_right, hβ2, hγ2, h0, h0'] at e
    omega
  · have e := D.iform_self_eq_two h
    rw [sub_eq_add_neg, iform_add_left, iform_add_right, iform_add_right, iform_neg_right,
      iform_neg_left, iform_neg_left, iform_neg_right, hβ2, hγ2, h0, h0'] at e
    omega

@[expose] def orbitVec (O : Set (Fin τ.rank → ℤ)) (j : ℕ) : Fin τ.rank → ℤ :=
  thetaPowVec D.θ j (orbitRoot O)

theorem orbitRoot_mem_kernelRoots {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    orbitRoot O ∈ kernelRoots D.χ :=
  D.mem_kernelRoots_of_mem_orbits hO (D.orbitRoot_mem hO)

theorem eq_thetaOrbit_orbitRoot {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    O = thetaOrbit D.θ (orbitRoot O) :=
  D.eq_thetaOrbit_of_mem_orbits hO (D.orbitRoot_mem hO)

theorem toReal_orbitVec {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (j : ℕ) :
    toReal (D.orbitVec O j) = (D.θ ^ j) (toReal (orbitRoot O)) :=
  (D.thetaPowVec_spec (D.orbitRoot_mem_kernelRoots hO) j).1

theorem orbitVec_mem {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (j : ℕ) :
    D.orbitVec O j ∈ O := by
  have h := (D.thetaPowVec_spec (D.orbitRoot_mem_kernelRoots hO) j).2.1
  rw [← D.eq_thetaOrbit_orbitRoot hO] at h
  exact h

theorem orbitVec_zero {O : Set (Fin τ.rank → ℤ)} : D.orbitVec O 0 = orbitRoot O :=
  thetaPowVec_eq (by rw [pow_zero, Module.End.one_apply])

theorem theta_orbitVec {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (j : ℕ) :
    D.θ (toReal (D.orbitVec O j)) = toReal (D.orbitVec O (j + 1)) := by
  rw [D.toReal_orbitVec hO, D.toReal_orbitVec hO, pow_succ', Module.End.mul_apply]

theorem toReal_orbitRoot_mem_periodicPts {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    toReal (orbitRoot O) ∈ Function.periodicPts D.θ := by
  obtain ⟨n, hn, hper⟩ := D.exists_pow_eq_on_kernelRoots
  refine Function.mem_periodicPts.2 ⟨n, hn, ?_⟩
  have h := hper _ (D.orbitRoot_mem_kernelRoots hO)
  rw [Module.End.pow_apply] at h
  exact h

theorem orbitVec_eq_iff {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) {i j : ℕ} :
    D.orbitVec O i = D.orbitVec O j ↔
      D.θ^[i] (toReal (orbitRoot O)) = D.θ^[j] (toReal (orbitRoot O)) := by
  rw [← Module.End.pow_apply, ← Module.End.pow_apply, ← D.toReal_orbitVec hO,
    ← D.toReal_orbitVec hO]
  exact ⟨fun h => by rw [h], fun h => toReal_injective h⟩

theorem orbitCard_eq_minimalPeriod {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    orbitCard O = Function.minimalPeriod D.θ (toReal (orbitRoot O)) := by
  classical
  set P := Function.minimalPeriod D.θ (toReal (orbitRoot O)) with hP
  have hinj : Set.InjOn (D.orbitVec O) ↑(Finset.range P) := by
    intro i hi j hj h
    rw [D.orbitVec_eq_iff hO] at h
    exact Function.iterate_injOn_Iio_minimalPeriod (Finset.mem_range.1 hi)
      (Finset.mem_range.1 hj) h
  have hOeq : O = ↑((Finset.range P).image (D.orbitVec O)) := by
    ext γ
    rw [Finset.coe_image, Set.mem_image]
    constructor
    · intro hγ
      rw [D.eq_thetaOrbit_orbitRoot hO] at hγ
      obtain ⟨m, hm⟩ := hγ
      refine ⟨m % P, Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _
        (Function.minimalPeriod_pos_of_mem_periodicPts
          (D.toReal_orbitRoot_mem_periodicPts hO)))), toReal_injective ?_⟩
      rw [D.toReal_orbitVec hO, Module.End.pow_apply, Function.iterate_mod_minimalPeriod_eq,
        ← Module.End.pow_apply, hm]
    · rintro ⟨j, -, rfl⟩
      exact D.orbitVec_mem hO j
  rw [orbitCard, hOeq, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, Finset.card_range]

theorem orbitVec_injOn {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) {i j : ℕ}
    (hi : i < orbitCard O) (hj : j < orbitCard O) (h : D.orbitVec O i = D.orbitVec O j) :
    i = j := by
  rw [D.orbitCard_eq_minimalPeriod hO] at hi hj
  rw [D.orbitVec_eq_iff hO] at h
  exact Function.iterate_injOn_Iio_minimalPeriod hi hj h

theorem orbitVec_orbitCard {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.orbitVec O (orbitCard O) = D.orbitVec O 0 := by
  rw [D.orbitVec_eq_iff hO, D.orbitCard_eq_minimalPeriod hO, Function.iterate_minimalPeriod,
    Function.iterate_zero, id]

theorem exists_orbitVec_eq {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ O) : ∃ j < orbitCard O, D.orbitVec O j = γ := by
  rw [D.eq_thetaOrbit_orbitRoot hO] at hγ
  obtain ⟨m, hm⟩ := hγ
  have hpos := Function.minimalPeriod_pos_of_mem_periodicPts
    (D.toReal_orbitRoot_mem_periodicPts hO)
  refine ⟨m % orbitCard O, by rw [D.orbitCard_eq_minimalPeriod hO]; exact Nat.mod_lt _ hpos,
    toReal_injective ?_⟩
  rw [D.toReal_orbitVec hO, Module.End.pow_apply, D.orbitCard_eq_minimalPeriod hO,
    Function.iterate_mod_minimalPeriod_eq, ← Module.End.pow_apply, hm]

theorem orbitVec_mem_unionSimpleRoots {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (j : ℕ) :
    D.orbitVec O j ∈ unionSimpleRoots D.χ Set.univ :=
  (D.subset_simpleRootsJ_of_mem_orbits hO (D.orbitVec_mem hO j)).1

theorem isRoot_orbitVec {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (j : ℕ) :
    IsRoot τ (D.orbitVec O j) :=
  D.isRoot_of_mem_orbits hO (D.orbitVec_mem hO j)

theorem commute_rootRankOneGroup_orbitVec {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {i j : ℕ} (hi : i < orbitCard O) (hj : j < orbitCard O) (hij : i ≠ j) :
    ∀ g ∈ rootRankOneGroup τ k (D.orbitVec O i), ∀ h ∈ rootRankOneGroup τ k (D.orbitVec O j),
      g * h = h * g := by
  have hne : D.orbitVec O i ≠ D.orbitVec O j := fun h => hij (D.orbitVec_injOn hO hi hj h)
  have hK := D.orbitRoot_mem_kernelRoots hO
  have h0 : iform (D.orbitVec O i) (D.orbitVec O j) = 0 :=
    D.orbit_orthogonal _ hK _ (D.thetaPowVec_spec hK i).2.1 _ (D.thetaPowVec_spec hK j).2.1 hne
  have hr1 := D.isRoot_orbitVec hO i
  have hr2 := D.isRoot_orbitVec hO j
  obtain ⟨hp, hm⟩ := D.not_isRoot_add_sub hr1 hr2 h0
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ k hr1 hr2 h0 hp hm

end GenFixedRootDatum

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)


@[expose] def orbitFactor (O : Set (Fin τ.rank → ℤ)) (j : ℕ) :
    SL2 (D.orbitField O) →* ModGL τ k :=
  (rootSL2 τ k (D.orbitVec O j)).comp
    ((Matrix.SpecialLinearGroup.map (iterateFrobenius k p₀ (D.e * j))).comp
      (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype))

theorem orbitFactor_apply (O : Set (Fin τ.rank → ℤ)) (j : ℕ) (A : SL2 (D.orbitField O)) :
    D.orbitFactor O j A = rootSL2 τ k (D.orbitVec O j)
      (Matrix.SpecialLinearGroup.map (iterateFrobenius k p₀ (D.e * j))
        (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A)) :=
  rfl

theorem orbitMap_eq_prod (O : Set (Fin τ.rank → ℤ)) (A : SL2 (D.orbitField O)) :
    D.orbitMap O A = ((List.range (orbitCard O)).map fun j => D.orbitFactor O j A).prod :=
  rfl

theorem orbitFactor_mem_rootRankOneGroup (O : Set (Fin τ.rank → ℤ)) (j : ℕ)
    (A : SL2 (D.orbitField O)) : D.orbitFactor O j A ∈ rootRankOneGroup τ k (D.orbitVec O j) :=
  ⟨_, rfl⟩

omit [IsAlgClosed k] in
theorem rootSL2_injective' (β : Fin τ.rank → ℤ) : Function.Injective (rootSL2 τ k β) := by
  have hj : Function.Injective (simpleRootSL2 τ k (pinnedData τ β).1) := by
    by_cases h2 : ringChar k = 2
    · have : CharP k 2 := ringChar.of_eq h2
      exact CFSG.RankThree.Chevalley.simpleRootSL2_injective_of_charTwo _
    · exact simpleRootSL2_injective h2 _
  exact (MulAut.conj (pinnedWeyl τ k β)).injective.comp hj

theorem orbitFactor_mem_adjointGroup (O : Set (Fin τ.rank → ℤ)) (j : ℕ)
    (A : SL2 (D.orbitField O)) : D.orbitFactor O j A ∈ adjointGroup τ k :=
  rootSL2_mem_adjointGroup _ _

theorem orbitMap_mem_adjointGroup (O : Set (Fin τ.rank → ℤ)) (A : SL2 (D.orbitField O)) :
    D.orbitMap O A ∈ adjointGroup τ k :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact D.orbitFactor_mem_adjointGroup O j A

theorem rootRankOneGroup_le_rootSpanJ {β : Fin τ.rank → ℤ} (hβ : β ∈ D.roots) :
    rootRankOneGroup τ k β ≤ D.rootSpanJ := by
  rw [(exceptional_Lang_root_rank_one_torus_transport τ k (isRoot_of_mem_unionRoots hβ)).1]
  exact sup_le (rootSubgroup_le_unionRootSpan hβ) (rootSubgroup_le_unionRootSpan
    (neg_mem_unionRoots hβ))

theorem orbitMap_mem_rootSpanJ {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (A : SL2 (D.orbitField O)) : D.orbitMap O A ∈ D.rootSpanJ :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact D.rootRankOneGroup_le_rootSpanJ (D.mem_roots_of_mem_orbits hO (D.orbitVec_mem hO j))
      (D.orbitFactor_mem_rootRankOneGroup O j A)

theorem orbitMap_mul {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (A B : SL2 (D.orbitField O)) :
    D.orbitMap O (A * B) = D.orbitMap O A * D.orbitMap O B := by
  have h := list_prod_map_apply_mul (l := (List.range (orbitCard O)).map (D.orbitFactor O))
    (by
      rw [List.pairwise_map]
      refine List.pairwise_lt_range.imp_of_mem fun hi hj hij a b => ?_
      exact D.commute_rootRankOneGroup_orbitVec hO (List.mem_range.1 hi) (List.mem_range.1 hj)
        hij.ne _ (D.orbitFactor_mem_rootRankOneGroup O _ a) _
        (D.orbitFactor_mem_rootRankOneGroup O _ b)) A B
  simp only [List.map_map, Function.comp_def] at h
  rw [orbitMap_eq_prod, orbitMap_eq_prod, orbitMap_eq_prod]
  exact h

theorem orbitMap_one (O : Set (Fin τ.rank → ℤ)) : D.orbitMap O 1 = 1 := by
  rw [orbitMap_eq_prod]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact map_one _

@[expose] def orbitMapHom {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    SL2 (D.orbitField O) →* ModGL τ k where
  toFun := D.orbitMap O
  map_one' := D.orbitMap_one O
  map_mul' := D.orbitMap_mul hO

theorem orbitMapHom_apply {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (A : SL2 (D.orbitField O)) : D.orbitMapHom hO A = D.orbitMap O A :=
  rfl

theorem map_frobenius_map_frobenius (j : ℕ) (B : SL2 k) :
    Matrix.SpecialLinearGroup.map (iterateFrobenius k p₀ D.e)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius k p₀ (D.e * j)) B) =
      Matrix.SpecialLinearGroup.map (iterateFrobenius k p₀ (D.e * (j + 1))) B := by
  ext i i'
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [mul_add, mul_one, add_comm, iterateFrobenius_add]
  rfl

theorem coe_F_orbitFactor {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (j : ℕ)
    (A : SL2 (D.orbitField O)) :
    (D.F ⟨_, D.orbitFactor_mem_adjointGroup O j A⟩ : ModGL τ k) = D.orbitFactor O (j + 1) A := by
  have h := D.map_rootSL2 _ (D.orbitVec_mem_unionSimpleRoots hO j) _ (D.theta_orbitVec hO j)
    (Matrix.SpecialLinearGroup.map (iterateFrobenius k p₀ (D.e * j))
      (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A))
    ⟨_, D.orbitFactor_mem_adjointGroup O j A⟩ rfl
  rw [h, D.map_frobenius_map_frobenius]
  rfl

theorem map_frobenius_orbitCard (O : Set (Fin τ.rank → ℤ)) (A : SL2 (D.orbitField O)) :
    Matrix.SpecialLinearGroup.map (iterateFrobenius k p₀ (D.e * orbitCard O))
        (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A) =
      Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A := by
  ext i i'
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    iterateFrobenius_def]
  exact mem_frobeniusFixedField.1 ((A : Matrix (Fin 2) (Fin 2) (D.orbitField O)) i i').2

theorem map_frobenius_zero (B : SL2 k) :
    Matrix.SpecialLinearGroup.map (iterateFrobenius k p₀ (D.e * 0)) B = B := by
  ext i i'
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem orbitFactor_orbitCard {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (A : SL2 (D.orbitField O)) : D.orbitFactor O (orbitCard O) A = D.orbitFactor O 0 A := by
  rw [D.orbitFactor_apply, D.orbitFactor_apply, D.orbitVec_orbitCard hO,
    D.map_frobenius_orbitCard, D.map_frobenius_zero]

theorem orbitFactor_zero (O : Set (Fin τ.rank → ℤ)) (A : SL2 (D.orbitField O)) :
    D.orbitFactor O 0 A = rootSL2 τ k (D.orbitVec O 0)
      (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A) := by
  rw [D.orbitFactor_apply, D.map_frobenius_zero]

theorem F_orbitMap {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (A : SL2 (D.orbitField O))
    {x : adjointGroup τ k} (hx : (x : ModGL τ k) = D.orbitMap O A) : D.F x = x := by
  set y : ℕ → adjointGroup τ k :=
    fun j => ⟨D.orbitFactor O j A, D.orbitFactor_mem_adjointGroup O j A⟩ with hy
  have hxy : x = ((List.range (orbitCard O)).map y).prod := by
    apply Subtype.ext
    rw [hx, Subgroup.val_list_prod, List.map_map]
    rfl
  have hFy : ∀ j, D.F (y j) = y (j + 1) := fun j => Subtype.ext (D.coe_F_orbitFactor hO j A)
  obtain ⟨n, hn⟩ : ∃ n, orbitCard O = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (D.orbitCard_pos hO).ne'
  have hyd : y (n + 1) = y 0 := Subtype.ext (by
    show D.orbitFactor O (n + 1) A = D.orbitFactor O 0 A
    rw [← hn]
    exact D.orbitFactor_orbitCard hO A)
  have hc : Commute (y 0) ((List.range n).map fun j => y (j + 1)).prod :=
    Commute.list_prod_right _ _ fun z hz => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
      have hj' := List.mem_range.1 hj
      exact Subtype.ext (D.commute_rootRankOneGroup_orbitVec hO (by omega) (by omega)
        (by omega) _ (D.orbitFactor_mem_rootRankOneGroup O 0 A) _
        (D.orbitFactor_mem_rootRankOneGroup O (j + 1) A))
  have hL : (List.range (n + 1)).map (fun j => y (j + 1)) =
      (List.range n).map (fun j => y (j + 1)) ++ [y 0] := by
    rw [List.range_succ, List.map_append, List.map_singleton, hyd]
  have hR : (List.range (n + 1)).map y = y 0 :: (List.range n).map (fun j => y (j + 1)) := by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  rw [hxy, map_list_prod, List.map_map,
    List.map_congr_left (f := ⇑D.F ∘ y) (g := fun j => y (j + 1)) (fun j _ => hFy j), hn, hL, hR,
    List.prod_append, List.prod_singleton, List.prod_cons]
  exact hc.eq.symm

theorem orbitMap_mem_fixedGroup {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (A : SL2 (D.orbitField O)) :
    (⟨D.orbitMap O A, D.orbitMap_mem_adjointGroup O A⟩ : adjointGroup τ k) ∈ D.fixedGroup :=
  ⟨Subgroup.mem_subgroupOf.2 (D.orbitMap_mem_rootSpanJ hO A), D.F_orbitMap hO A rfl⟩

@[expose] def orbitFixedHom {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    SL2 (D.orbitField O) →* D.fixedGroup where
  toFun A := ⟨⟨D.orbitMap O A, D.orbitMap_mem_adjointGroup O A⟩, D.orbitMap_mem_fixedGroup hO A⟩
  map_one' := Subtype.ext (Subtype.ext (D.orbitMap_one O))
  map_mul' A B := Subtype.ext (Subtype.ext (D.orbitMap_mul hO A B))

theorem coe_orbitFixedHom {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (A : SL2 (D.orbitField O)) :
    (((D.orbitFixedHom hO A : D.fixedGroup) : adjointGroup τ k) : ModGL τ k) = D.orbitMap O A :=
  rfl

theorem map_subtype_injective (O : Set (Fin τ.rank → ℤ)) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) (D.orbitField O).subtype) := by
  intro A A' h
  ext i j
  have := congrArg (fun M : SL2 k => (M : Matrix (Fin 2) (Fin 2) k) i j) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at this
  exact this

theorem eq_one_or_neg_one_of_orbitMap_eq_one {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {A : SL2 (D.orbitField O)} (h : D.orbitMap O A = 1) : A = 1 ∨ A = -1 := by
  obtain ⟨n, hn⟩ : ∃ n, orbitCard O = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (D.orbitCard_pos hO).ne'
  set B := Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A with hB
  rw [orbitMap_eq_prod, hn, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map,
    D.orbitFactor_zero] at h
  set P := ((List.range n).map ((fun j => D.orbitFactor O j A) ∘ Nat.succ)).prod with hP
  have hcP : ∀ C : SL2 k, Commute (rootSL2 τ k (D.orbitVec O 0) C) P := fun C =>
    Commute.list_prod_right _ _ fun z hz => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
      have hj' := List.mem_range.1 hj
      exact D.commute_rootRankOneGroup_orbitVec hO (i := 0) (j := j + 1) (by omega) (by omega)
        (by omega) _ ⟨C, rfl⟩ _ (D.orbitFactor_mem_rootRankOneGroup O (j + 1) A)
  have e : rootSL2 τ k (D.orbitVec O 0) B = P⁻¹ := eq_inv_of_mul_eq_one_left h
  have hcen : B ∈ Subgroup.center (SL2 k) := by
    refine Subgroup.mem_center_iff.2 fun C => rootSL2_injective' (D.orbitVec O 0) ?_
    rw [map_mul, map_mul, e]
    exact ((hcP C).inv_right).eq
  have h1 : Matrix.SpecialLinearGroup.map (D.orbitField O).subtype (-1 : SL2 (D.orbitField O)) =
      -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]
  rcases sl2_eq_one_or_neg_one_of_mem_center hcen with h2 | h2
  · left
    exact D.map_subtype_injective O (by rw [← hB, h2, map_one])
  · right
    exact D.map_subtype_injective O (by rw [← hB, h2, h1])

end GenFixedRootDatum

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem orbitFactor_uSL (O : Set (Fin τ.rank → ℤ)) (j : ℕ) (c : D.orbitField O) :
    D.orbitFactor O j (uSL c) = rootSL2 τ k (D.orbitVec O j) (uSL ((c : k) ^ D.q ^ j)) := by
  rw [D.orbitFactor_apply, map_uSL, map_uSL, iterateFrobenius_def, pow_mul]
  rfl

theorem orbitFactor_vSL (O : Set (Fin τ.rank → ℤ)) (j : ℕ) (c : D.orbitField O) :
    D.orbitFactor O j (vSL c) = rootSL2 τ k (D.orbitVec O j) (vSL ((c : k) ^ D.q ^ j)) := by
  rw [D.orbitFactor_apply, map_vSL, map_vSL, iterateFrobenius_def, pow_mul]
  rfl

theorem orbitX_add {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (c c' : D.orbitField O) :
    D.orbitX O (c + c') = D.orbitX O c * D.orbitX O c' := by
  rw [orbitX, orbitX, orbitX, uSL_add_eq_mul, D.orbitMap_mul hO]

theorem orbitY_add {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (c c' : D.orbitField O) :
    D.orbitY O (c + c') = D.orbitY O c * D.orbitY O c' := by
  rw [orbitY, orbitY, orbitY, vSL_add_eq_mul, D.orbitMap_mul hO]

theorem orbitMap_eq_one_of_eq {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {A B C : SL2 (D.orbitField O)} (hA : A = B * C) (h : D.orbitMap O A = D.orbitMap O C) :
    D.orbitMap O B = 1 := by
  rw [hA, D.orbitMap_mul hO] at h
  exact mul_right_cancel (h.trans (one_mul _).symm)

theorem orbitX_injective {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    Function.Injective (D.orbitX O) := by
  intro c c' h
  have h1 := D.orbitMap_eq_one_of_eq hO (by rw [← uSL_add_eq_mul, sub_add_cancel]) h
  exact sub_eq_zero.1 (eq_zero_of_uSL_eq_one_or_neg_one
    (D.eq_one_or_neg_one_of_orbitMap_eq_one hO h1))

theorem orbitY_injective {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    Function.Injective (D.orbitY O) := by
  intro c c' h
  have h1 := D.orbitMap_eq_one_of_eq hO (by rw [← vSL_add_eq_mul, sub_add_cancel]) h
  exact sub_eq_zero.1 (eq_zero_of_vSL_eq_one_or_neg_one
    (D.eq_one_or_neg_one_of_orbitMap_eq_one hO h1))

@[expose] def fixedRootSpan (S : Set (Fin τ.rank → ℤ)) : Subgroup (adjointGroup τ k) :=
  (rootSpan τ k S).subgroupOf (adjointGroup τ k) ⊓ D.F.toMonoidHom.eqLocus (MonoidHom.id _)

theorem mem_fixedRootSpan {S : Set (Fin τ.rank → ℤ)} {x : adjointGroup τ k} :
    x ∈ D.fixedRootSpan S ↔ (x : ModGL τ k) ∈ rootSpan τ k S ∧ D.F x = x := by
  rw [fixedRootSpan, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rfl

theorem orbitX_mem_rootSpan {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (c : D.orbitField O) :
    D.orbitX O c ∈ rootSpan τ k O := by
  rw [orbitX, orbitMap_eq_prod]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  rw [D.orbitFactor_uSL, rootSL2_uSL_eq]
  exact rootSubgroup_le_rootSpan (D.orbitVec_mem hO j) (mem_rootSubgroup.2 ⟨_, rfl⟩)

theorem orbitX_mem_fixedRootSpan {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (c : D.orbitField O) :
    (⟨D.orbitX O c, D.orbitMap_mem_adjointGroup O _⟩ : adjointGroup τ k) ∈ D.fixedRootSpan O :=
  D.mem_fixedRootSpan.2 ⟨D.orbitX_mem_rootSpan hO c, D.F_orbitMap hO _ rfl⟩

theorem range_orbitMap {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    Set.range (D.orbitMap O) =
      (Subgroup.closure (Set.range (D.orbitX O) ∪ Set.range (D.orbitY O)) : Set (ModGL τ k)) := by
  have h1 : Set.range (D.orbitMap O) = ((D.orbitMapHom hO).range : Set (ModGL τ k)) := by
    rw [MonoidHom.coe_range]
    rfl
  have htop : Subgroup.closure (Set.range (uSL (K := D.orbitField O)) ∪ Set.range vSL) = ⊤ :=
    sl2_closure_upper_lower
  rw [h1, MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure, Set.image_union,
    ← Set.range_comp, ← Set.range_comp]
  rfl

theorem range_orbitMap_subset {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    Set.range (D.orbitMap O) ⊆ D.orbitGroup := by
  rw [D.range_orbitMap hO]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact Subgroup.subset_closure ⟨O, hO, c, Or.inl rfl⟩
  · exact Subgroup.subset_closure ⟨O, hO, c, Or.inr rfl⟩

theorem orbitMap_mem_orbitGroup {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (A : SL2 (D.orbitField O)) : D.orbitMap O A ∈ D.orbitGroup :=
  D.range_orbitMap_subset hO ⟨A, rfl⟩

theorem orbitH_mem_torusGroup {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (t : (D.orbitField O)ˣ) : D.orbitH O t ∈ torusGroup τ k := by
  rw [orbitH, orbitMap_eq_prod]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  rw [D.orbitFactor_apply, map_HSL, map_HSL]
  exact (exceptional_Lang_root_rank_one_torus_transport τ k (D.isRoot_orbitVec hO j)).2.1 _

theorem orbitFactor_WSL (O : Set (Fin τ.rank → ℤ)) (j : ℕ) :
    D.orbitFactor O j WSL = rootWeylSL2 τ k (D.orbitVec O j) 1 := by
  rw [D.orbitFactor_apply, map_WSL, map_WSL, rootWeylSL2, nSL_one]

theorem orbitN_mem_monomialSubgroup {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.orbitN O ∈ monomialSubgroup τ k ∧ MapsRootLines (D.orbitN O) (setReflection O) := by
  have hfac : ∀ j, ∃ h : D.orbitFactor O j WSL ∈ monomialSubgroup τ k,
      weylQuotientHom τ k ⟨_, h⟩ = rootReflection (D.orbitVec O j) := fun j => by
    rw [D.orbitFactor_WSL]
    exact (exceptional_Lang_root_rank_one_torus_transport τ k (D.isRoot_orbitVec hO j)).2.2.1 1
  have key : ∀ l : List ℕ, (l.map fun j => D.orbitFactor O j WSL).prod ∈ monomialSubgroup τ k ∧
      MapsRootLines (l.map fun j => D.orbitFactor O j WSL).prod
        (l.map fun j => rootReflection (D.orbitVec O j)).prod := by
    intro l
    induction l with
    | nil => exact ⟨one_mem _, by simpa using mapsRootLines_one⟩
    | cons j l ih =>
      obtain ⟨h, hw⟩ := hfac j
      have hm := mapsRootLines_weylQuotientHom (⟨_, h⟩ : monomialSubgroup τ k)
      rw [hw] at hm
      simp only [List.map_cons, List.prod_cons]
      exact ⟨mul_mem h ih.1, hm.mul ih.2⟩
  obtain ⟨h1, h2⟩ := key (List.range (orbitCard O))
  have hnd : ((List.range (orbitCard O)).map (D.orbitVec O)).Nodup :=
    List.nodup_range.map_on fun i hi j hj h =>
      D.orbitVec_injOn hO (List.mem_range.1 hi) (List.mem_range.1 hj) h
  have hmem : ∀ β, β ∈ (List.range (orbitCard O)).map (D.orbitVec O) ↔ β ∈ O := fun β => by
    rw [List.mem_map]
    constructor
    · rintro ⟨j, -, rfl⟩
      exact D.orbitVec_mem hO j
    · intro hβ
      obtain ⟨j, hj, rfl⟩ := D.exists_orbitVec_eq hO hβ
      exact ⟨j, List.mem_range.2 hj, rfl⟩
  have hset := setReflection_eq_list_prod (D.finite_of_mem_orbits hO)
    (D.pairwise_commute_of_mem_orbits hO) hnd hmem
  rw [List.map_map] at hset
  refine ⟨h1, ?_⟩
  rw [hset]
  exact h2

theorem orbitN_mem_normalizer {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.orbitN O ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)) :=
  mem_normalizer_torusGroup_of_mem_monomialSubgroup (D.orbitN_mem_monomialSubgroup hO).1

theorem weylQuotientHom_orbitN {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    weylQuotientHom τ k ⟨_, (D.orbitN_mem_monomialSubgroup hO).1⟩ = setReflection O :=
  weylQuotientHom_eq (D.orbitN_mem_monomialSubgroup hO).2

theorem orbitN_mul_self_mem_torusGroup {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.orbitN O * D.orbitN O ∈ torusGroup τ k := by
  rw [orbitN, ← D.orbitMap_mul hO, WSL_mul_WSL_eq_HSL]
  exact D.orbitH_mem_torusGroup hO (-1)

end GenFixedRootDatum

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

@[expose] def orbitUpper (O : Set (Fin τ.rank → ℤ)) (c : ℕ → k) : ModGL τ k :=
  ((List.range (orbitCard O)).map fun j => rootSL2 τ k (D.orbitVec O j) (uSL (c j))).prod

include D in
theorem not_isRoot_nsmul_add_nsmul_of_orthogonal {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (h0 : α ≠ β → iform α β = 0) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬IsRoot τ (a • α + b • β) := by
  by_cases hαβ : α = β
  · subst hαβ
    intro h
    have e := D.iform_self_eq_two h
    rw [iform_nsmul_add_nsmul, D.iform_self_eq_two hα] at e
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  · exact not_isRoot_nsmul_add_nsmul hα hβ (h0 hαβ) (D.not_isRoot_add_sub hα hβ (h0 hαβ)).1
      (by omega) (by omega)

theorem not_isRoot_nsmul_add_nsmul_of_mem_orbits {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {α β : Fin τ.rank → ℤ} (hα : α ∈ O) (hβ : β ∈ O) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬IsRoot τ (a • α + b • β) := by
  have hαr := D.isRoot_of_mem_orbits hO hα
  have hβr := D.isRoot_of_mem_orbits hO hβ
  obtain ⟨β₀, hβ₀, rfl⟩ := hO
  exact D.not_isRoot_nsmul_add_nsmul_of_orthogonal hαr hβr
    (D.orbit_orthogonal β₀ (D.mem_kernelRoots_of_mem_simpleRootsJ hβ₀) α hα β hβ) ha hb

theorem orbitUpper_bijective {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    (∀ c c' : ℕ → k, D.orbitUpper O c = D.orbitUpper O c' → ∀ j < orbitCard O, c j = c' j) ∧
    ∀ g ∈ rootSpan τ k O, ∃ c : ℕ → k, D.orbitUpper O c = g := by
  set α : Fin (orbitCard O) → Fin τ.rank → ℤ := fun i => D.orbitVec O i with hαdef
  have hαinj : Function.Injective α := fun i j h =>
    Fin.ext (D.orbitVec_injOn hO i.2 j.2 h)
  have hαrange : Set.range α = O := by
    ext γ
    constructor
    · rintro ⟨i, rfl⟩
      exact D.orbitVec_mem hO i
    · intro hγ
      obtain ⟨j, hj, rfl⟩ := D.exists_orbitVec_eq hO hγ
      exact ⟨⟨j, hj⟩, rfl⟩
  have hbij := (positive_root_collection τ k).1 O
    (fun γ hγ => ⟨D.isRoot_of_mem_orbits hO hγ, (D.mem_posRootsJ_of_mem_orbits hO hγ).2⟩)
    (fun γ hγ δ hδ a b ha hb hr =>
      absurd hr (D.not_isRoot_nsmul_add_nsmul_of_mem_orbits hO hγ hδ ha hb)) α hαinj hαrange
  have hrel : ∀ c : ℕ → k, D.orbitUpper O c =
      (List.ofFn fun i => pinnedX τ k (α i) ((pinnedData τ (α i)).2.2 • c i)).prod := by
    intro c
    rw [orbitUpper, list_range_map_eq_ofFn]
    congr 1
    exact List.ofFn_inj.2 (funext fun i => rootSL2_uSL_eq _ _)
  refine ⟨fun c c' h j hj => ?_, fun g hg => ?_⟩
  · rw [hrel, hrel] at h
    have h1 := hbij.injOn (Set.mem_univ _) (Set.mem_univ _) h
    have h2 := congrFun h1 ⟨j, hj⟩
    have h3 := congrArg (fun z => (pinnedData τ (α ⟨j, hj⟩)).2.2 • z) h2
    simp only [zsmul_zsmul_pinnedSign] at h3
    exact h3
  · obtain ⟨z, -, hz⟩ := hbij.surjOn hg
    refine ⟨fun j => if h : j < orbitCard O then
      (pinnedData τ (α ⟨j, h⟩)).2.2 • z ⟨j, h⟩ else 0, ?_⟩
    rw [hrel, ← hz]
    congr 1
    refine List.ofFn_inj.2 (funext fun i => ?_)
    simp only [Fin.is_lt, dite_true, Fin.eta, zsmul_zsmul_pinnedSign]

theorem orbitUpper_mem_adjointGroup (O : Set (Fin τ.rank → ℤ)) (c : ℕ → k) :
    D.orbitUpper O c ∈ adjointGroup τ k :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact rootSL2_mem_adjointGroup _ _

theorem coe_F_orbitUpper {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) {n : ℕ}
    (hn : orbitCard O = n + 1) (c : ℕ → k) :
    (D.F ⟨_, D.orbitUpper_mem_adjointGroup O c⟩ : ModGL τ k) =
      D.orbitUpper O (fun j => if j = 0 then (c n) ^ D.q else (c (j - 1)) ^ D.q) := by
  set c' : ℕ → k := fun j => if j = 0 then (c n) ^ D.q else (c (j - 1)) ^ D.q with hc'
  set y : ℕ → k → adjointGroup τ k :=
    fun j z => ⟨rootSL2 τ k (D.orbitVec O j) (uSL z), rootSL2_mem_adjointGroup _ _⟩ with hy
  have hlift : ∀ e : ℕ → k, (⟨_, D.orbitUpper_mem_adjointGroup O e⟩ : adjointGroup τ k) =
      ((List.range (orbitCard O)).map fun j => y j (e j)).prod := fun e => by
    apply Subtype.ext
    rw [Subgroup.val_list_prod, List.map_map]
    rfl
  have hFy : ∀ j z, D.F (y j z) = y (j + 1) (z ^ D.q) := fun j z => Subtype.ext (by
    have h := D.map_rootSL2 _ (D.orbitVec_mem_unionSimpleRoots hO j) _ (D.theta_orbitVec hO j)
      (uSL z) (y j z) rfl
    rw [h, map_uSL, iterateFrobenius_def]
    rfl)
  have hyd : ∀ z, y (n + 1) z = y 0 z := fun z => Subtype.ext (by
    show rootSL2 τ k (D.orbitVec O (n + 1)) _ = rootSL2 τ k (D.orbitVec O 0) _
    rw [← hn, D.orbitVec_orbitCard hO])
  have hc : Commute (y 0 ((c n) ^ D.q))
      ((List.range n).map fun j => y (j + 1) ((c j) ^ D.q)).prod :=
    Commute.list_prod_right _ _ fun z hz => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
      have hj' := List.mem_range.1 hj
      exact Subtype.ext (D.commute_rootRankOneGroup_orbitVec hO (by omega) (by omega)
        (by omega) _ ⟨_, rfl⟩ _ ⟨_, rfl⟩)
  suffices h : D.F ⟨_, D.orbitUpper_mem_adjointGroup O c⟩ =
      ⟨_, D.orbitUpper_mem_adjointGroup O c'⟩ by
    rw [h]
  have hL : (List.range (n + 1)).map (fun j => y (j + 1) ((c j) ^ D.q)) =
      (List.range n).map (fun j => y (j + 1) ((c j) ^ D.q)) ++ [y 0 ((c n) ^ D.q)] := by
    rw [List.range_succ, List.map_append, List.map_singleton, hyd]
  have hR : (List.range (n + 1)).map (fun j => y j (c' j)) =
      y 0 ((c n) ^ D.q) :: (List.range n).map (fun j => y (j + 1) ((c j) ^ D.q)) := by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
  rw [hlift, hlift, map_list_prod, List.map_map,
    List.map_congr_left (f := ⇑D.F ∘ fun j => y j (c j))
      (g := fun j => y (j + 1) ((c j) ^ D.q)) (fun j _ => hFy j (c j)), hn, hL, hR,
    List.prod_append, List.prod_singleton, List.prod_cons]
  exact hc.eq.symm

theorem exists_orbitX_eq {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) {g : adjointGroup τ k}
    (hg : g ∈ D.fixedRootSpan O) : ∃ c : D.orbitField O, D.orbitX O c = (g : ModGL τ k) := by
  obtain ⟨hgU, hgF⟩ := D.mem_fixedRootSpan.1 hg
  obtain ⟨hinj, hsurj⟩ := D.orbitUpper_bijective hO
  obtain ⟨n, hn⟩ : ∃ n, orbitCard O = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (D.orbitCard_pos hO).ne'
  obtain ⟨c, hc⟩ := hsurj _ hgU
  have hgc : g = ⟨_, D.orbitUpper_mem_adjointGroup O c⟩ := Subtype.ext hc.symm
  have hF := D.coe_F_orbitUpper hO hn c
  rw [← hgc, hgF, ← hc] at hF
  have hcoord := hinj _ _ hF
  have h0 : c 0 = (c n) ^ D.q := by
    have := hcoord 0 (by omega)
    simpa using this
  have hsucc : ∀ j < n, c (j + 1) = (c j) ^ D.q := fun j hj => by
    have := hcoord (j + 1) (by omega)
    simpa using this
  have hpow : ∀ j ≤ n, c j = (c 0) ^ D.q ^ j := by
    intro j hj
    induction j with
    | zero => rw [pow_zero, pow_one]
    | succ j ih => rw [hsucc j (by omega), ih (by omega), ← pow_mul, ← pow_succ]
  have hfix : (c 0) ^ D.q ^ orbitCard O = c 0 := by
    rw [hn, pow_succ, pow_mul, ← hpow n le_rfl, ← h0]
  refine ⟨⟨c 0, D.mem_orbitField.2 hfix⟩, ?_⟩
  rw [← hc, orbitX, orbitMap_eq_prod, orbitUpper]
  refine congrArg List.prod (List.map_congr_left fun j hj => ?_)
  have hj' := List.mem_range.1 hj
  rw [D.orbitFactor_uSL, hpow j (by omega)]

end GenFixedRootDatum

end CFSG.RankThree.Lattice
