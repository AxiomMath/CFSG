module

public import CFSG.RankThree.PartOne.KLC.ThreePoint
public import CFSG.RankThree.PartOne.S11d.OutStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusSwap

public section

namespace CFSG.RankThree.PartOne.KLC

open Matrix Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.RankThree.PartOne.OutStructure (Inn OutPCentral orthD inner_le_orthD exists_gen mem_orthD_iff)
open scoped commutatorElement Pointwise

section Coordinate

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem index_powMonoidHom_two : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = 1 := by
  rw [Subgroup.index_eq_one, MonoidHom.range_eq_top]
  intro u
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (u : K)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
  simp [powMonoidHom, sq, hr]

theorem relIndex_inner_orthD_le_two (hQ : ∃ v, Q v ≠ 0)
    (hA : Nat.card (Abelianization (matrixIsometries Q)) ≤ 2) :
    (CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q)).relIndex
      (orthD Q) ≤ 2 := by
  have h1 : CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤
      (isometryConjugationHom Q).range := by
    rw [inner_eq_map_commutator Q]
    exact Subgroup.map_le_range _ _
  have h2 := isometryConjugationHom_range_le Q
  have hD : orthD Q = (linearConjugationHom Q).range := by
    ext δ
    rw [mem_orthD_iff, MonoidHom.mem_range]
    exact Iff.rfl
  rw [hD, ← Subgroup.relIndex_mul_relIndex _ _ _ h1 h2]
  have ha := relIndex_inner_dvd Q
  have hb := relIndex_isometryRange_dvd Q hQ
  rw [index_powMonoidHom_two] at hb
  have hb1 := Nat.dvd_one.1 hb
  rw [hb1, mul_one]
  exact (Nat.le_of_dvd Nat.card_pos ha).trans hA

theorem matrixProjectiveImage_commutator_mem_inner (hQ : ∃ v, Q v ≠ 0)
    (hA : Nat.card (Abelianization (matrixIsometries Q)) ≤ 2)
    {a b : MulAut (matrixProjectiveDerived Q)} (ha : a ∈ matrixProjectiveImage Q)
    (hb : b ∈ matrixProjectiveImage Q) :
    ⁅a, b⁆ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
  have : Finite (matrixProjectiveDerived Q) := inferInstance
  have : Finite (MulAut (matrixProjectiveDerived Q)) := inferInstance
  obtain ⟨g₀, hg₀⟩ := exists_gen Q
  have hDE : orthD Q ≤ matrixProjectiveImage Q := by
    intro δ hδ
    obtain ⟨g, rfl⟩ := (mem_orthD_iff Q δ).1 hδ
    exact ⟨g.val, rfl⟩
  refine commutator_mem_of_cyclic_quotient
    (CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q))
    (matrixProjectiveImage Q) (orthD Q) hDE (u := matrixProjectiveConjugationHom Q g₀)
    ⟨g₀, rfl⟩ (fun e he => ?_) (fun e he d hd => ?_) a ha b hb
  · obtain ⟨h, rfl⟩ := (mem_matrixProjectiveImage_iff Q e).1 he
    obtain ⟨k, hk⟩ := hg₀ h
    refine ⟨k, (mem_orthD_iff Q _).2 ⟨⟨g₀ ^ k * h, hk⟩, ?_⟩⟩
    rw [map_mul, map_zpow]
    rfl
  · obtain ⟨g, rfl⟩ := (mem_matrixProjectiveImage_iff Q e).1 he
    have hed : matrixProjectiveConjugationHom Q g * d *
        (matrixProjectiveConjugationHom Q g)⁻¹ ∈ orthD Q := by
      obtain ⟨ℓ, rfl⟩ := (mem_orthD_iff Q d).1 hd
      refine (mem_orthD_iff Q _).2 ⟨⟨g * ℓ.val * g⁻¹, (linearPairsNormal Q).conj_mem ℓ.val ℓ.property g⟩, ?_⟩
      simp [map_mul, map_inv]
    exact commutator_mem_of_relIndex_le_two _ _ (inner_le_orthD Q)
      (relIndex_inner_orthD_le_two Q hQ hA) hd hed

end Coordinate

section Transport

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

variable (K : Type) [Field K] [Finite K]

theorem swap_data_coordinate :
    ∃ κ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      κ • projectivePointFamily (coordinateQuadPlus 4 K) =
          projectivePointFamily (coordinateQuadPlus 4 K) ∧
        κ • plusCX 4 K = plusCXstar 4 K (by omega) ∧
        κ • plusCXstar 4 K (by omega) = plusCX 4 K ∧
        plusCX 4 K ≠ plusCXstar 4 K (by omega) := by
  set φ := plusCoordinateEquiv 4 K with hφ
  have hflag : plusCX 4 K = familyTransport φ (conjugacyFamily
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4))) :=
    (familyTransport_conjugacy φ _).symm
  have hX : plusCXstar 4 K (by omega) = familyTransport φ (conjugacyFamily
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (Xstar 4 K (by omega)))) :=
    (familyTransport_conjugacy φ _).symm
  refine ⟨MulAut.congr φ (plusSwapAut 4 K (by omega)), ?_, ?_, ?_, ?_⟩
  · rw [← plusCoordinate_pointFamily, ← familyTransport_automorphism,
      plusSwapAut_smul_statedPointFamily]
  · rw [hflag, hX, ← familyTransport_automorphism, plusSwapAut_smul_conjugacyFamily_flag]
  · rw [hflag, hX, ← familyTransport_automorphism, plusSwapAut_smul_conjugacyFamily_Xstar]
  · rw [hflag, hX]
    exact fun h => conjugacyFamily_flag_ne_Xstar 4 K (by omega) ((familyTransport φ).injective h)

omit [Finite K] in
theorem inner_smul_pointFamily_coordinate (g : matrixProjectiveDerived (coordinateQuadPlus 4 K)) :
    MulAut.conj g • projectivePointFamily (coordinateQuadPlus 4 K) =
      projectivePointFamily (coordinateQuadPlus 4 K) := by
  set φ := plusCoordinateEquiv 4 K with hφ
  have hF := statedPointFamily_eq_conjugacyFamily (K := K) (n := 4) (by omega)
  have hg : MulAut.conj g = MulAut.congr φ (MulAut.conj (φ.symm g)) := by
    rw [automorphismTransport_conj, φ.apply_symm_apply]
  rw [← plusCoordinate_pointFamily, hg, ← familyTransport_automorphism, hF, conj_conjugacyFamily]

end Transport

section Assembly

theorem outPCentral_of_mulEquiv {X Y : Type*} [Group X] [Group Y] {p : ℕ} (e : X ≃* Y)
    (h : OutPCentral p Y) : OutPCentral p X := by
  intro γ α hα
  let φ : MulAut X ≃* MulAut Y := MulAut.congr e
  have hinner : (Inn X).map φ.toMonoidHom = Inn Y :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  have hmem : ∀ α : MulAut X, α ∈ Inn X ↔ φ α ∈ Inn Y := by
    intro α
    rw [← hinner]
    constructor
    · exact fun h => ⟨α, h, rfl⟩
    · rintro ⟨β, hβ, hβα⟩
      have : β = α := φ.injective hβα
      exact this ▸ hβ
  rw [hmem, map_commutatorElement]
  exact h (φ γ) (φ α) (by rw [← map_pow]; exact (hmem _).mp hα)

theorem outPCentral_of_swap {P : Type*} [Group P] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {F y z : Set (Subgroup P)}
    (hO : ∀ a : MulAut P, a • F = F ∨ a • F = y ∨ a • F = z)
    {κ : MulAut P} (hκF : κ • F = F) (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z)
    (hN : ∀ n ∈ Inn P, n • F = F)
    (hE : ∀ a b : MulAut P, a • F = F → b • F = F → ⁅a, b⁆ ∈ Inn P) : OutPCentral p P :=
  fun γ _ hα => commutator_mem_of_three_point_orbit (Inn P) hO hκF hκy hκz hyz hN hE hp hp5 hα γ

end Assembly

section Main

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit

theorem d4OutCentral : CFSG.RankThree.PartOne.D4OutCentral := by
  intro X _ p m hp hp5 h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus (.inr (.inl rfl))
    4 2 m h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hA : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 2 := by
    rw [coordinateQuadPlus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e).1
  have hsub := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  obtain ⟨κ, hκF, hκy, hκz, hyz⟩ := swap_data_coordinate K
  refine outPCentral_of_mulEquiv (coordinatePlusWitnessEquiv K e)
    (outPCentral_of_swap hp hp5 (F := projectivePointFamily (coordinateQuadPlus 4 K))
      (y := plusCX 4 K) (z := plusCXstar 4 K (by omega)) ?_ hκF hκy hκz hyz ?_ ?_)
  · intro a
    have := hsub (MulAction.mem_orbit _ a)
    simpa using this
  · rintro _ ⟨g, rfl⟩
    exact inner_smul_pointFamily_coordinate K g
  · intro a b ha hb
    refine matrixProjectiveImage_commutator_mem_inner _ hQ hA ?_ ?_
    · rw [← hEA]
      exact (mem_projectivePointFamilyAut_iff _ _).2 ha
    · rw [← hEA]
      exact (mem_projectivePointFamilyAut_iff _ _).2 hb

end Main

end CFSG.RankThree.PartOne.KLC
