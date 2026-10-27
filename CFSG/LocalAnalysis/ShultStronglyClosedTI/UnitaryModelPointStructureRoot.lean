module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructureTorus
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearUnitaryPointInvolutions
public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryModel

open Matrix CFSG.Open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth

universe u

variable {K : Type u} [Field K]

@[expose] def heisenbergMatrix (J : HermitianForm 3 K) (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, -J.conj a, b; 0, 1, a; 0, 0, 1]

theorem hermitianUnipotentMatrix_eq_heisenbergMatrix (J : HermitianForm 3 K)
    (z : hermitianUnipotentCoord J) :
    hermitianUnipotentMatrix J z = heisenbergMatrix J (-J.conj z.1.1) z.1.2 := by
  rw [hermitianUnipotentMatrix_eq, heisenbergMatrix, map_neg, J.conj_involutive, neg_neg]

theorem mem_root_iff (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (g : ProjectiveSpecialUnitaryMatrixGroup J) :
    g ∈ (hermitianUnipotentPSU J hJ).range ↔
      ∃ (a b : K) (M : GL (Fin 3) K), a * J.conj a + (b + J.conj b) = 0 ∧
        (M : Matrix (Fin 3) (Fin 3) K) = heisenbergMatrix J a b ∧
        (g : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨-J.conj z.1.1, z.1.2, hermitianUnipotentGL J z, ?_, ?_, rfl⟩
    · rw [map_neg, J.conj_involutive, neg_mul_neg]
      linear_combination z.2
    · rw [hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq_heisenbergMatrix]
  · rintro ⟨a, b, M, hab, hM, hg⟩
    let z : hermitianUnipotentCoord J := ⟨(-J.conj a, b), by
      rw [map_neg, J.conj_involutive, neg_mul_neg]
      linear_combination hab⟩
    refine ⟨z, Subtype.ext ?_⟩
    rw [hermitianUnipotentPSU_val, hg]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq_heisenbergMatrix, hM]
    simp only [z, map_neg, neg_neg, J.conj_involutive a]

theorem coord_mul_comm_of_fst_eq_zero (J : HermitianForm 3 K) {z : hermitianUnipotentCoord J}
    (hz : z.1.1 = 0) (w : hermitianUnipotentCoord J) : z * w = w * z := by
  apply Subtype.ext
  apply Prod.ext
  · change z.1.1 + w.1.1 = w.1.1 + z.1.1
    rw [add_comm]
  · change z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1 = w.1.2 + z.1.2 - w.1.1 * J.conj z.1.1
    rw [hz, map_zero]
    ring

theorem root_inf_stabilizer_two (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (hermitianUnipotentPSU J hJ).range ⊓ unitaryCoordinateStabilizer J 2 = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨z, rfl⟩, hz⟩
  change ProjGenLinGroup.mk (hermitianUnipotentGL J z) • unitaryCoordinatePoint (K := K) 2 =
    unitaryCoordinatePoint (K := K) 2 at hz
  rw [unitary_projective_coordinate_maps_iff] at hz
  have h02 := hz 0 (by decide)
  have h12 := hz 1 (by decide)
  simp only [hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq] at h02 h12
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, neg_eq_zero, map_eq_zero] at h02 h12
  have hz1 : z = 1 := Subtype.ext (Prod.ext h12 h02)
  rw [hz1, map_one]
  exact Subgroup.one_mem _

section Finite

variable [Finite K]

theorem point_involution_iff (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (g : ProjectiveSpecialUnitaryMatrixGroup J) :
    (g ∈ unitaryCoordinateStabilizer J 0 ∧ orderOf g = 2) ↔
      ∃ (b : K) (M : GL (Fin 3) K), b + J.conj b = 0 ∧ b ≠ 0 ∧
        (M : Matrix (Fin 3) (Fin 3) K) = heisenbergMatrix J 0 b ∧
        (g : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M := by
  rw [unitary_point_involution_coordinates J f hf hcard hfixed hJ g]
  constructor
  · rintro ⟨z, hz1, hz2, rfl⟩
    refine ⟨z.1.2, hermitianUnipotentGL J z, ?_, hz2, ?_, rfl⟩
    · simpa [hz1] using z.2
    · rw [hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq_heisenbergMatrix, hz1,
        map_zero, neg_zero]
  · rintro ⟨b, M, hb, hb0, hM, hg⟩
    let z : hermitianUnipotentCoord J := ⟨(0, b), by simpa using hb⟩
    refine ⟨z, rfl, hb0, Subtype.ext ?_⟩
    rw [hermitianUnipotentPSU_val, hg]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq_heisenbergMatrix, hM]
    simp [z]

theorem point_involution_mem_center (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hg : g ∈ unitaryCoordinateStabilizer J 0) (horder : orderOf g = 2) :
    g ∈ (hermitianUnipotentPSU J hJ).range ∧
      ∀ u ∈ (hermitianUnipotentPSU J hJ).range, u * g = g * u := by
  obtain ⟨z, hz1, -, rfl⟩ :=
    (unitary_point_involution_coordinates J f hf hcard hfixed hJ g).mp ⟨hg, horder⟩
  refine ⟨⟨z, rfl⟩, ?_⟩
  rintro _ ⟨w, rfl⟩
  rw [← map_mul, ← map_mul, coord_mul_comm_of_fst_eq_zero J hz1 w]

theorem exists_elementary_root_center (J : HermitianForm 3 K) (f : ℕ)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ E : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      IsElemAbelian 2 E ∧ Nat.card E = 2 ^ f := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  let Z := (unitaryCoverFirstCoord J).ker
  have hfixcard : Nat.card (unitaryCoverFixedField J) = 2 ^ f := by
    let c : unitaryCoverFixedField J ≃ {x : K // J.conj x = x} :=
      { toFun := fun x => ⟨x, x.property⟩
        invFun := fun x => ⟨x, x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr c).trans hfixed
  have hZcard : Nat.card Z = 2 ^ f :=
    (Nat.card_congr (unitaryCoverZeroFirstEquiv J).toEquiv).trans
      ((Nat.card_congr (Multiplicative.toAdd :
        Multiplicative (unitaryCoverFixedField J) ≃ _)).trans hfixcard)
  refine ⟨Z.map (hermitianUnipotentPSU J hJ), ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, ⟨z, hz, rfl⟩⟩ := x
    obtain ⟨_, ⟨w, -, rfl⟩⟩ := y
    apply Subtype.ext
    change hermitianUnipotentPSU J hJ z * hermitianUnipotentPSU J hJ w =
      hermitianUnipotentPSU J hJ w * hermitianUnipotentPSU J hJ z
    rw [← map_mul, ← map_mul, coord_mul_comm_of_fst_eq_zero J (show z.1.1 = 0 from hz) w]
  · rintro _ ⟨z, hz, rfl⟩
    exact (unitary_projective_root_square_one_iff J hJ z).mpr hz
  · rw [Subgroup.card_map_of_injective (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ)]
    exact hZcard

theorem two_le_twoRank (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    2 ≤ twoRank (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨E, hE, hEcard⟩ := exists_elementary_root_center J f hcard hfixed hJ
  exact hf.trans (CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary _ E hE f hEcard)

end Finite

end CFSG.ShultStronglyClosedTI.UnitaryModel
