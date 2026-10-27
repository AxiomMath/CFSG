module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaThreeFamily
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticRankTwoCounts

public section

namespace CFSG.RankThree.EvenD4Centralizer

open QuadraticMap
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixDerived matrixProjectiveDerived matrixProjectiveImage matrixProjectiveProjection
    matrixLinearEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus projectivePointFamily projectivePointFamilyAut
    mem_projectivePointFamilyAut_iff plusIndexEquiv reindexVectorEquiv reindexQuadraticForm_map
    coordinate_plus_family_eq_matrixImage)
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.ThreeFamily
open scoped Pointwise

section Transport

variable {G J : Type*} [Group G] [Group J]

theorem card_fixed_familyTransport (e : G ≃* J) (a : MulAut G) (S : Set (Subgroup G)) :
    Nat.card {U : Subgroup J // U ∈ familyTransport e S ∧ MulAut.congr e a • U = U} =
      Nat.card {U : Subgroup G // U ∈ S ∧ a • U = U} := by
  have hinj : Function.Injective (fun U : Subgroup G => U.map e.toMonoidHom) :=
    Subgroup.map_injective e.injective
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv e.mapSubgroup.toEquiv fun U => ?_)
  change U ∈ S ∧ U.map a.toMonoidHom = U ↔
    U.map e.toMonoidHom ∈ (fun U => U.map e.toMonoidHom) '' S ∧
      (U.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom = U.map e.toMonoidHom
  rw [hinj.mem_set_image, ← subgroupTransport_automorphism]
  exact and_congr_right fun _ => hinj.eq_iff.symm

end Transport

section Isometry

variable {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V']
  [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}

theorem polar_map_isometry (r : V ≃ₗ[K] V') (hr : ∀ x, Q' (r x) = Q x) (x y : V) :
    polar Q' (r x) (r y) = polar Q x y := by
  rw [polar, polar, ← map_add, hr, hr, hr]

theorem orthElementaryMap_map_isometry (r : V ≃ₗ[K] V') (hr : ∀ x, Q' (r x) = Q x)
    (a b x : V) :
    orthElementaryMap Q' (r a) (r b) (r x) = r (orthElementaryMap Q a b x) := by
  rw [orthElementaryMap_apply, orthElementaryMap_apply, polar_map_isometry r hr,
    polar_map_isometry r hr, hr]
  simp only [map_add, map_sub, map_smul]

variable [CharP K 2]

theorem reflect_apply_of_charTwo {u : V} (hu : Q u = 1) (x : V) :
    reflect Q u x = x + polar Q x u • u := by
  rw [reflect_apply (by rw [hu]; exact one_ne_zero), hu, div_one, polar_comm, sub_eq_add_neg,
    ← neg_smul, CharTwo.neg_eq]

theorem reflect_commute_rankTwo {u v : V} (hu : Q u = 1) (hB : polar Q u v = 0)
    {g : V ≃ₗ[K] V} (hg : ∀ x, g x = x + polar Q x u • u + polar Q x v • v) :
    reflect Q u * g = g * reflect Q u := by
  have huu : polar Q u u = 0 := polar_self_charTwo Q u
  have hvu : polar Q v u = 0 := by rw [polar_comm, hB]
  refine LinearEquiv.ext fun x => ?_
  simp only [LinearEquiv.mul_apply, reflect_apply_of_charTwo hu, hg, polar_add_left,
    polar_smul_left, huu, hvu, hB, smul_eq_mul, mul_zero, add_zero]
  abel

end Isometry

section Orbits

variable {K : Type} [Field K] {r : ℕ}

theorem reflect_single_sub_single (i : Fin r) :
    reflect (quadPlus r K) (Pi.single (Sum.inl i) 1 - Pi.single (Sum.inr i) 1) =
      swapPair K i := by
  have hw := quadPlus_single_sub_single (K := K) i
  refine LinearEquiv.ext fun x => ?_
  rw [reflect_apply (by rw [hw]; exact neg_ne_zero.mpr one_ne_zero), swapPair_eq_add_smul, hw,
    div_neg, div_one, neg_smul, sub_neg_eq_add]

theorem smul_orbit_elementary {a : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (ha : a ∈ orthElementaryGroup (quadPlus r K)) (Y : Submodule K (Fin r ⊕ Fin r → K)) :
    a • MulAction.orbit (orthElementaryGroup (quadPlus r K)) Y =
      MulAction.orbit (orthElementaryGroup (quadPlus r K)) Y :=
  MulAction.smul_orbit (⟨a, ha⟩ : orthElementaryGroup (quadPlus r K)) Y

theorem map_mem_orbit_elementary {a : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (ha : a ∈ orthElementaryGroup (quadPlus r K)) {Y M : Submodule K (Fin r ⊕ Fin r → K)}
    (hM : M ∈ MulAction.orbit (orthElementaryGroup (quadPlus r K)) Y) :
    M.map (a : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) ∈
      MulAction.orbit (orthElementaryGroup (quadPlus r K)) Y := by
  rw [← smul_orbit_elementary ha Y]
  exact Set.smul_mem_smul_set hM

variable [Finite K]

theorem reflect_smul_orbit_flag (hr : 3 ≤ r) {u : Fin r ⊕ Fin r → K}
    (hu : quadPlus r K u = -1) :
    reflect (quadPlus r K) u • MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r) =
      MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K (by omega)) := by
  have hw := quadPlus_single_sub_single (K := K) (⟨r - 1, by omega⟩ : Fin r)
  have hne : ∀ x : Fin r ⊕ Fin r → K, quadPlus r K x = -1 → x ≠ 0 := fun x hx h0 => by
    rw [h0, QuadraticMap.map_zero, zero_eq_neg] at hx
    exact one_ne_zero hx
  obtain ⟨h, hh, hhu⟩ := (orthogonal_norm_shell_transitive (nondegenerate_polarBilin_quadPlus r K)
    ⟨flag r K 2, (flag_mem_singularSubspaces (by omega)).1,
      (flag_mem_singularSubspaces (by omega)).2⟩).1 u _ (hne u hu) (hne _ hw) (by rw [hu, hw])
  have hs : reflect (quadPlus r K) u = h⁻¹ * swapPair K (⟨r - 1, by omega⟩ : Fin r) * h := by
    rw [← reflect_single_sub_single, ← hhu, ← reflect_conj (orthElementaryGroup_le _ hh)]
    group
  obtain ⟨-, -, -, -, -, -, -, -, -, hswap, -⟩ :=
    orthogonal_geometry_split_maximal_family_orbits (K := K) hr
  have hswap' : swapPair K (⟨r - 1, by omega⟩ : Fin r) •
      MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r) =
        MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K (by omega)) := hswap
  rw [hs, mul_smul, mul_smul, smul_orbit_elementary hh, hswap',
    smul_orbit_elementary (inv_mem hh)]

theorem card_fixed_orbit_flag_eq_Xstar (hr : 3 ≤ r) {u : Fin r ⊕ Fin r → K}
    (hu : quadPlus r K u = -1) {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ orthElementaryGroup (quadPlus r K))
    (hc : reflect (quadPlus r K) u * g = g * reflect (quadPlus r K) u) :
    Nat.card {M // M ∈ MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r) ∧
        M.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = M} =
      Nat.card {M // M ∈ MulAction.orbit (orthElementaryGroup (quadPlus r K))
          (Xstar r K (by omega)) ∧
        M.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = M} := by
  rw [← reflect_smul_orbit_flag hr hu]
  have hcomp : (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)).comp
      (reflect (quadPlus r K) u : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        (reflect (quadPlus r K) u : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)).comp
          (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) :=
    LinearMap.ext fun x => (DFunLike.congr_fun hc x).symm
  exact (card_fixed_image
    (fun M : Submodule K (Fin r ⊕ Fin r → K) =>
      M.map (reflect (quadPlus r K) u : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)))
    (Set.injOn_of_injective
      (Submodule.map_injective_of_injective (reflect (quadPlus r K) u).injective))
    (fun M => M.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)))
    (fun M => M.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)))
    (fun _ hM => map_mem_orbit_elementary hg hM)
    (fun M _ => by rw [← Submodule.map_comp, ← Submodule.map_comp, hcomp])).symm

theorem card_fixed_orbits_rankTwo [CharP K 2] {u v : Fin 4 ⊕ Fin 4 → K}
    (huv : LinearIndependent K ![u, v]) (hu : quadPlus 4 K u = 1) (hv : quadPlus 4 K v = 1)
    (hB : polar (quadPlus 4 K) u v = 0) :
    Nat.card {M // M ∈ MulAction.orbit (orthElementaryGroup (quadPlus 4 K)) (flag 4 K 4) ∧
        M.map (eichler (quadPlus 4 K) (u + v) u :
          (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} =
        Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1 ∧
      Nat.card {M // M ∈ MulAction.orbit (orthElementaryGroup (quadPlus 4 K))
          (Xstar 4 K (by norm_num)) ∧
        M.map (eichler (quadPlus 4 K) (u + v) u :
          (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} =
        Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1 := by
  obtain ⟨-, -, -, hE, -, -, hg, -, hm, -⟩ :=
    even_split_eight_rank_two_elementary_fixed_counts huv hu hv hB
  have hu' : quadPlus 4 K u = -1 := by rw [hu, CharTwo.neg_eq]
  have heq := card_fixed_orbit_flag_eq_Xstar (by norm_num) hu' hE
    (reflect_commute_rankTwo hu hB hg)
  have hsum := card_fixed_maximal (K := K) (n := 4) (by norm_num) (eichler (quadPlus 4 K) (u + v) u)
  omega

end Orbits

section Coordinate

variable {K : Type} [Field K]

theorem conj_projection_reindex (A : StatedOmega (StatedQuadPlus 4 K)) :
    MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
        (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) =
      MulAut.congr (plusCoordinateEquiv 4 K)
        (MulAut.conj (QuotientGroup.mk' _ A : StatedProj (StatedOmega (StatedQuadPlus 4 K)))) := by
  rw [automorphismTransport_conj]
  exact congrArg MulAut.conj (statedProjectiveReindexEquiv_mk (plusIndexEquiv 4) (quadPlus 4 K)
    (coe_quadPlus 4 K) A).symm

theorem card_fixed_coordinate_families (A : StatedOmega (StatedQuadPlus 4 K)) :
    Nat.card {U // U ∈ projectivePointFamily (coordinateQuadPlus 4 K) ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
          (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) •
            U = U} =
      Nat.card {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map (toLinEquiv _ K A.val).toLinearMap = L} ∧
    Nat.card {U // U ∈ plusCX 4 K ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
          (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) •
            U = U} =
      Nat.card {M : Submodule K (Fin 4 ⊕ Fin 4 → K) //
        M ∈ MulAction.orbit (orthElementaryGroup (quadPlus 4 K)) (flag 4 K 4) ∧
          M.map (toLinEquiv _ K A.val).toLinearMap = M} ∧
    Nat.card {U // U ∈ plusCXstar 4 K (by norm_num) ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
          (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) •
            U = U} =
      Nat.card {M : Submodule K (Fin 4 ⊕ Fin 4 → K) //
        M ∈ MulAction.orbit (orthElementaryGroup (quadPlus 4 K)) (Xstar 4 K (by norm_num)) ∧
          M.map (toLinEquiv _ K A.val).toLinearMap = M} := by
  rw [conj_projection_reindex]
  refine ⟨?_, ?_, ?_⟩
  · rw [← plusCoordinate_pointFamily, card_fixed_familyTransport]
    exact card_fixed_pointFamily (by norm_num) A
  · rw [show plusCX 4 K = familyTransport (plusCoordinateEquiv 4 K) (conjugacyFamily
        (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4))) from
      (familyTransport_conjugacy _ _).symm, card_fixed_familyTransport]
    exact card_fixed_conjugacyFamily (by norm_num) A (flag_mem_singularSubspaces le_rfl)
  · rw [show plusCXstar 4 K (by norm_num) = familyTransport (plusCoordinateEquiv 4 K)
        (conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
          (Xstar 4 K (by norm_num)))) from
      (familyTransport_conjugacy _ _).symm, card_fixed_familyTransport]
    exact card_fixed_conjugacyFamily (by norm_num) A (Xstar_mem_singularSubspaces (by norm_num))

theorem mem_pointFamilyAut_of_card_fixed_ne [Finite K]
    {c : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (h1 : Nat.card {U // U ∈ plusCX 4 K ∧ c • U = U} ≠
      Nat.card {U // U ∈ projectivePointFamily (coordinateQuadPlus 4 K) ∧ c • U = U})
    (h2 : Nat.card {U // U ∈ plusCXstar 4 K (by norm_num) ∧ c • U = U} ≠
      Nat.card {U // U ∈ projectivePointFamily (coordinateQuadPlus 4 K) ∧ c • U = U})
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))} (hα : α * c * α⁻¹ = c) :
    α ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K) := by
  have hcard := card_fixed_smul_set (mul_inv_eq_iff_eq_mul.mp hα)
    (projectivePointFamily (coordinateQuadPlus 4 K))
  have hO := coordinate_plus_pointFamily_orbit_subset (K := K) (n := 4) rfl
    (MulAction.mem_orbit _ α)
  rw [mem_projectivePointFamilyAut_iff]
  change α • projectivePointFamily (coordinateQuadPlus 4 K) =
    projectivePointFamily (coordinateQuadPlus 4 K)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hO
  rcases hO with hO | hO | hO
  · exact hO
  · rw [hO] at hcard
    exact absurd hcard h1
  · rw [hO] at hcard
    exact absurd hcard h2

end Coordinate

theorem even_D4_rank_two_involution_full_centralizer_preserves_point_family (G : Type)
    [Group G] {f : ℕ} (h : StatedClassicalModel G .POmegaPlus 4 2 f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    {u v : Fin (2 * 4) → K} (huv : LinearIndependent K ![u, v])
    (hu : coordinateQuadPlus 4 K u = 1) (hv : coordinateQuadPlus 4 K v = 1)
    (hB : polar (coordinateQuadPlus 4 K) u v = 0) :
    ∃ g : matrixDerived (coordinateQuadPlus 4 K),
      (matrixLinearEquiv g.val : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)) =
        orthElementaryMap (coordinateQuadPlus 4 K) (u + v) u ∧
      (∀ x, matrixLinearEquiv g.val x =
        x + polar (coordinateQuadPlus 4 K) x u • u + polar (coordinateQuadPlus 4 K) x v • v) ∧
      g ≠ 1 ∧ g * g = 1 ∧
      projectivePointFamilyAut (coordinateQuadPlus 4 K) =
        matrixProjectiveImage (coordinateQuadPlus 4 K) ∧
      (∀ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
        α * MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) * α⁻¹ =
          MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) →
        α ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K) ∧
          α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) ∧
      Nat.card {U // U ∈ projectivePointFamily (coordinateQuadPlus 4 K) ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) • U = U} =
          (2 ^ f) ^ 3 + (2 ^ f) ^ 2 + 2 ^ f + 1 + (2 ^ f) ^ 4 ∧
      Nat.card {U // U ∈ plusCX 4 K ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) • U = U} =
          (2 ^ f) ^ 3 + (2 ^ f) ^ 2 + 2 ^ f + 1 ∧
      Nat.card {U // U ∈ plusCXstar 4 K (by norm_num) ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) • U = U} =
          (2 ^ f) ^ 3 + (2 ^ f) ^ 2 + 2 ^ f + 1 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have hr : ∀ x, coordinateQuadPlus 4 K (reindexVectorEquiv (plusIndexEquiv 4) x) =
      quadPlus 4 K x := reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 K)
  obtain ⟨u₀, rfl⟩ := (reindexVectorEquiv (K := K) (plusIndexEquiv 4)).surjective u
  obtain ⟨v₀, rfl⟩ := (reindexVectorEquiv (K := K) (plusIndexEquiv 4)).surjective v
  rw [hr] at hu hv
  rw [polar_map_isometry (reindexVectorEquiv (K := K) (plusIndexEquiv 4)) hr] at hB
  have huv₀ : LinearIndependent K ![u₀, v₀] := by
    refine LinearIndependent.of_comp (reindexVectorEquiv (K := K) (plusIndexEquiv 4)).toLinearMap
      ?_
    convert huv using 1
    ext i : 1
    fin_cases i <;> rfl
  obtain ⟨-, -, hcoe, hE, hsq, hne, hg₀, hp, hm, -⟩ :=
    even_split_eight_rank_two_elementary_fixed_counts huv₀ hu hv hB
  obtain ⟨hcX, hcXs⟩ := card_fixed_orbits_rankTwo huv₀ hu hv hB
  have h4 : 3 ≤ 4 := by norm_num
  obtain ⟨A, hA⟩ : ∃ A : StatedOmega (StatedQuadPlus 4 K),
      toLinEquiv _ K A.val = eichler (quadPlus 4 K) (u₀ + v₀) u₀ :=
    ⟨(plusDerivedEquiv 4 K h4).symm ⟨_, hE⟩, (plusDerivedEquiv_val 4 K h4 _).symm.trans
      (congrArg Subtype.val ((plusDerivedEquiv 4 K h4).apply_symm_apply _))⟩
  have hAA : A * A = 1 := by
    apply Subtype.ext
    apply (toLinEquiv _ K).injective
    rw [Subgroup.coe_mul, map_mul, hA, Subgroup.coe_one, map_one, hsq]
  have hA1 : A ≠ 1 := fun h1 => hne (by rw [← hA, h1, Subgroup.coe_one, map_one])
  have hvec : ∀ x, matrixLinearEquiv
      (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A).val
        (reindexVectorEquiv (plusIndexEquiv 4) x) =
      reindexVectorEquiv (plusIndexEquiv 4) (eichler (quadPlus 4 K) (u₀ + v₀) u₀ x) := by
    intro x
    rw [statedDerivedReindexEquiv_vector, hA]
  obtain ⟨cP, cX, cXs⟩ := card_fixed_coordinate_families A
  rw [hA] at cP cX cXs
  have hq4 : 0 < Nat.card K ^ 4 := pow_pos Nat.card_pos 4
  have himage := coordinate_plus_family_eq_matrixImage h K hK e
  refine ⟨statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A,
    ?_, ?_, ?_, ?_, himage, fun α hα => ?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := (reindexVectorEquiv (K := K) (plusIndexEquiv 4)).surjective y
    rw [LinearEquiv.coe_coe, hvec, ← map_add,
      orthElementaryMap_map_isometry (reindexVectorEquiv (K := K) (plusIndexEquiv 4)) hr]
    exact congrArg (reindexVectorEquiv (K := K) (plusIndexEquiv 4)) (LinearMap.congr_fun hcoe x)
  · intro y
    obtain ⟨x, rfl⟩ := (reindexVectorEquiv (K := K) (plusIndexEquiv 4)).surjective y
    rw [hvec, hg₀, map_add, map_add, map_smul, map_smul,
      polar_map_isometry (reindexVectorEquiv (K := K) (plusIndexEquiv 4)) hr,
      polar_map_isometry (reindexVectorEquiv (K := K) (plusIndexEquiv 4)) hr]
  · intro h1
    apply hA1
    apply (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).injective
    rw [map_one]
    exact h1
  · have h2 := congrArg (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K)
      (coe_quadPlus 4 K)) hAA
    rw [map_mul, map_one] at h2
    exact h2
  · have hmem := mem_pointFamilyAut_of_card_fixed_ne (by rw [cX, cP, hcX, hp]; omega)
      (by rw [cXs, cP, hcXs, hp]; omega) hα
    exact ⟨hmem, himage ▸ hmem⟩
  · rw [cP, hp, hK]
  · rw [cX, hcX, hK]
  · rw [cXs, hcXs, hK]

end CFSG.RankThree.EvenD4Centralizer
