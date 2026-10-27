module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure
public import CFSG.Quasithin.EmptyFaithful.E22PGen

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryModel
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth

section Root

variable {K : Type} [Field K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

abbrev rootU : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (hermitianUnipotentPSU J hJ).range

abbrev rootZ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (unitaryCoverFirstCoord J).ker.map (hermitianUnipotentPSU J hJ)

theorem rootZ_le_rootU : rootZ J hJ ≤ rootU J hJ := Subgroup.map_le_range _ _

theorem mem_rootZ_of_sq_eq_one [CharP K 2] {u : ProjectiveSpecialUnitaryMatrixGroup J}
    (hu : u ∈ rootU J hJ) (h2 : u ^ 2 = 1) : u ∈ rootZ J hJ := by
  obtain ⟨z, rfl⟩ := hu
  refine ⟨z, ?_, rfl⟩
  have hz : z.1.1 = 0 := (unitary_projective_root_square_one_iff J hJ z).mp h2
  change Multiplicative.ofAdd z.1.1 = 1
  rw [hz]
  rfl

theorem sq_eq_one_of_mem_rootZ [CharP K 2] {u : ProjectiveSpecialUnitaryMatrixGroup J}
    (hu : u ∈ rootZ J hJ) : u ^ 2 = 1 := by
  obtain ⟨z, hz, rfl⟩ := hu
  exact (unitary_projective_root_square_one_iff J hJ z).mpr (congrArg Multiplicative.toAdd hz)

theorem commute_of_mem_rootZ {z u : ProjectiveSpecialUnitaryMatrixGroup J}
    (hz : z ∈ rootZ J hJ) (hu : u ∈ rootU J hJ) : u * z = z * u := by
  obtain ⟨z, hz, rfl⟩ := hz
  obtain ⟨w, rfl⟩ := hu
  rw [← map_mul, ← map_mul,
    coord_mul_comm_of_fst_eq_zero J (show z.1.1 = 0 from congrArg Multiplicative.toAdd hz) w]

theorem isElemAbelian_rootZ [CharP K 2] : IsElemAbelian 2 (rootZ J hJ) :=
  ⟨⟨⟨fun x y => Subtype.ext (commute_of_mem_rootZ J hJ x.2 (rootZ_le_rootU J hJ y.2)).symm⟩⟩,
    fun _ hx => sq_eq_one_of_mem_rootZ J hJ hx⟩

theorem card_rootZ [Finite K] [CharP K 2] {f : ℕ}
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f) : Nat.card (rootZ J hJ) = 2 ^ f := by
  have hfixcard : Nat.card (unitaryCoverFixedField J) = 2 ^ f := by
    let c : unitaryCoverFixedField J ≃ {x : K // J.conj x = x} :=
      { toFun := fun x => ⟨x, x.property⟩
        invFun := fun x => ⟨x, x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr c).trans hfixed
  rw [Subgroup.card_map_of_injective
    (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ)]
  exact (Nat.card_congr (unitaryCoverZeroFirstEquiv J).toEquiv).trans
    ((Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (unitaryCoverFixedField J) ≃ _)).trans hfixcard)

end Root

theorem commute_of_isCyclic {X : Type*} [Group X] {C : Subgroup X} (hC : IsCyclic C) {a b : X}
    (ha : a ∈ C) (hb : b ∈ C) : a * b = b * a := by
  obtain ⟨g, hg⟩ := hC.exists_generator
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
  have h := congrArg Subtype.val (Commute.zpow_zpow_self g i j).eq
  rw [hi, hj] at h
  exact h

theorem isSolvable_sup_of_normal {X : Type*} [Group X] {N C : Subgroup X}
    (hN : (N.subgroupOf (N ⊔ C)).Normal) (hNs : Group.IsSolvable ↥N)
    (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) : Group.IsSolvable ↥(N ⊔ C) := by
  set N' := N.subgroupOf (N ⊔ C) with hN'
  set π := QuotientGroup.mk' N' with hπ
  have hsup : N' ⊔ C.subgroupOf (N ⊔ C) = ⊤ := (Subgroup.codisjoint_subgroupOf_sup N C).eq_top
  have hcomm : ∀ a b : ↥(N ⊔ C) ⧸ N', a * b = b * a := by
    have hsurj : ∀ y : ↥(N ⊔ C) ⧸ N', ∃ c ∈ C.subgroupOf (N ⊔ C), π c = y := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N' y
      have hx : x ∈ N' ⊔ C.subgroupOf (N ⊔ C) := hsup ▸ Subgroup.mem_top x
      obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      refine ⟨c, hc, ?_⟩
      rw [map_mul, show π a = 1 from (QuotientGroup.eq_one_iff a).mpr ha, one_mul]
    intro a b
    obtain ⟨c, hc, rfl⟩ := hsurj a
    obtain ⟨d, hd, rfl⟩ := hsurj b
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hC _ (Subgroup.mem_subgroupOf.mp hc) _ (Subgroup.mem_subgroupOf.mp hd))
  have : Group.IsSolvable (↥(N ⊔ C) ⧸ N') := Group.isSolvable_of_comm hcomm
  have : Group.IsSolvable ↥N' :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : N ≤ N ⊔ C)).toMonoidHom) (Subgroup.subgroupOfEquivOfLe _).injective
  exact Group.isSolvable_of_ker_le_range N'.subtype π (by
    rw [hπ, QuotientGroup.ker_mk', Subgroup.range_subtype])

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {f : ℕ} (hf : 2 ≤ f)
  (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)

include hJ hf hcard hfixed

theorem isSolvable_stabilizer : Group.IsSolvable ↥(unitaryCoordinateStabilizer J 0) := by
  obtain ⟨-, -, -, -, -, rho, -, -, -, -, -, -, hnormal, -, hUT, -, hcyc, -, ⟨S, hS⟩, -⟩ :=
    unitary_three_point_structure J f hf hcard hfixed hJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← hUT] at hnormal ⊢
  have hU2 : IsPGroup 2 ↥((hermitianUnipotentPSU J hJ).range) := by
    have h := S.isPGroup'
    rwa [hS] at h
  have := hU2.isNilpotent
  exact isSolvable_sup_of_normal hnormal inferInstance fun a ha b hb =>
    commute_of_isCyclic hcyc ha hb

theorem card_le_of_isElemAbelian {E : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hE : IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ f := by
  obtain ⟨-, -, -, -, -, rho, -, -, -, -, -, -, -, -, -, -, -, -, ⟨S, hS⟩, -⟩ :=
    unitary_three_point_structure J f hf hcard hfixed hJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  obtain ⟨P, hEP⟩ := (E1.isPGroup_of_isElemAbelian hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) P S
  have hle : A1b.conjSub g E ≤ rootZ J hJ := by
    rintro _ ⟨e, he, rfl⟩
    have heU : (MulAut.conj g).toMonoidHom e ∈ rootU J hJ := by
      have h : (MulAut.conj g).toMonoidHom e ∈ ((g • P : Sylow 2 _) : Subgroup _) := by
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
        exact ⟨e, hEP he, rfl⟩
      rwa [hg, hS] at h
    refine mem_rootZ_of_sq_eq_one J hJ heU ?_
    rw [← map_pow, hE.2 e he, map_one]
  calc Nat.card E = Nat.card (A1b.conjSub g E) := (E1.card_conjSub_eq g E).symm
    _ ≤ Nat.card (rootZ J hJ) := Subgroup.card_le_of_le hle
    _ = 2 ^ f := card_rootZ J hJ hfixed

end Model

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
