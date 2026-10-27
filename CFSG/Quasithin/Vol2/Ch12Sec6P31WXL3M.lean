module

public import CFSG.Milestones.ASVolI.A3Aut.SBL3
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OBorelCard

public section

namespace CFSG.Quasithin.H13.P31X

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

@[expose] noncomputable def l3DiagElt (a b : Kˣ) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal ![(a : K), (b : K), ((a : K) * (b : K))⁻¹], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    exact mul_inv_cancel₀ (mul_ne_zero a.ne_zero b.ne_zero)⟩

theorem l3DiagElt_mem (a b : Kˣ) : l3DiagElt a b ∈ upperTriangular 3 K := by
  rw [mem_upperTriangular]
  intro i j hij
  exact Matrix.diagonal_apply_ne _ hij.ne'

theorem l3_diagPair_surjective :
    Function.Surjective (CFSG.Quasithin.H13.NQCore.L3Odd.diagPair K) := by
  rintro ⟨a, b⟩
  refine ⟨⟨l3DiagElt a b, l3DiagElt_mem a b⟩, Prod.ext ?_ ?_⟩
  · apply Units.ext
    simp [l3DiagElt, CFSG.Quasithin.H13.NQCore.L3Odd.diagPair,
      CFSG.LieType.SteinbergBR.upperDiagHom]
  · apply Units.ext
    simp [l3DiagElt, CFSG.Quasithin.H13.NQCore.L3Odd.diagPair,
      CFSG.LieType.SteinbergBR.upperDiagHom]

theorem l3_card_upperTriangular [Finite K] :
    Nat.card (upperTriangular 3 K) = Nat.card K ^ 3 * (Nat.card K - 1) ^ 2 := by
  have hker : (CFSG.Quasithin.H13.NQCore.L3Odd.diagPair K).ker =
      (CFSG.LieType.SteinbergBR.upperDiagHom K 3).ker := by
    refine le_antisymm CFSG.Quasithin.H13.NQCore.L3Odd.ker_diagPair_le ?_
    intro b hb
    rw [MonoidHom.mem_ker] at hb ⊢
    have h0 : CFSG.LieType.SteinbergBR.upperDiagHom K 3 b 0 = 1 := congrFun hb 0
    have h1 : CFSG.LieType.SteinbergBR.upperDiagHom K 3 b 1 = 1 := congrFun hb 1
    exact Prod.ext h0 h1
  rw [← Subgroup.card_ker_mul_card_range (CFSG.Quasithin.H13.NQCore.L3Odd.diagPair K), hker,
    CFSG.LieType.SteinbergBR.ker_upperDiagHom,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (unitriangular_le_upperTriangular 3 K)).toEquiv,
    card_unitriangular, MonoidHom.range_eq_top.2 (l3_diagPair_surjective (K := K)),
    Subgroup.card_top, Nat.card_prod, Nat.card_units]
  have h3 : 3 * (3 - 1) / 2 = 3 := by norm_num
  rw [h3]
  ring

theorem l3_card_scalars [Finite K] :
    Nat.card (scalars 3 K) = Nat.gcd 3 (Nat.card K - 1) :=
  CFSG.LocalAnalysis.ComponentInitial.card_scalars_eq_gcd K (by norm_num)

theorem l3_card_projUpperTriangular [Finite K] :
    Nat.card (projUpperTriangular 3 K) * Nat.gcd 3 (Nat.card K - 1) =
      Nat.card K ^ 3 * (Nat.card K - 1) ^ 2 := by
  let φ : upperTriangular 3 K →* projectiveSL 3 K :=
    (proj 3 K).comp (upperTriangular 3 K).subtype
  have hrange : φ.range = projUpperTriangular 3 K := by
    rw [projUpperTriangular]
    ext x
    constructor
    · intro hx
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hx
      exact Subgroup.mem_map.2 ⟨b, b.2, rfl⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      exact MonoidHom.mem_range.2 ⟨⟨y, hy⟩, rfl⟩
  have hker : φ.ker = (scalars 3 K).subgroupOf (upperTriangular 3 K) := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact proj_eq_one_iff
  have key := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (scalars_le_upperTriangular 3 K)).toEquiv,
    l3_card_scalars, l3_card_upperTriangular] at key
  exact (mul_comm _ _).trans key

theorem l3_comm_prod_eq_one {G : Type} [CommGroup G] (u v : G) : u * v * u⁻¹ * v⁻¹ = 1 := by
  rw [mul_comm u v]
  simp

theorem l3_comm_mem_unitriangular (x y : upperTriangular 3 K) :
    ((x * y * x⁻¹ * y⁻¹ : upperTriangular 3 K) : Matrix.SpecialLinearGroup (Fin 3) K) ∈
      unitriangular 3 K := by
  have hker : x * y * x⁻¹ * y⁻¹ ∈ (CFSG.Quasithin.H13.NQCore.L3Odd.diagPair K).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    exact l3_comm_prod_eq_one _ _
  have h := CFSG.Quasithin.H13.NQCore.L3Odd.ker_diagPair_le hker
  rw [CFSG.LieType.SteinbergBR.ker_upperDiagHom, Subgroup.mem_subgroupOf] at h
  exact h

theorem l3_comm_upperTriangular {a b : Matrix.SpecialLinearGroup (Fin 3) K}
    (ha : a ∈ upperTriangular 3 K) (hb : b ∈ upperTriangular 3 K) :
    a * b * a⁻¹ * b⁻¹ ∈ unitriangular 3 K :=
  l3_comm_mem_unitriangular ⟨a, ha⟩ ⟨b, hb⟩

theorem l3_comm_projUpperTriangular {a b : projectiveSL 3 K}
    (ha : a ∈ projUpperTriangular 3 K) (hb : b ∈ projUpperTriangular 3 K) :
    a * b * a⁻¹ * b⁻¹ ∈ projUnitriangular 3 K := by
  rw [projUpperTriangular, Subgroup.mem_map] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  rw [projUnitriangular, Subgroup.mem_map]
  exact ⟨a' * b' * a'⁻¹ * b'⁻¹, l3_comm_upperTriangular ha' hb', by simp only [map_mul, map_inv]⟩

theorem l3_isSylow_unitriangular [Finite K] [CharP K 2] :
    CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular 3 K) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (by norm_num : 1 ≤ 3)
  rw [← hP]
  exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P

theorem l3_isSylow_projUnitriangular [Finite K] [CharP K 2] :
    CFSG.QuasithinUnique.IsSylowTwoOf (projUnitriangular 3 K) ⊤ := by
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 3) K) := inferInstance
  haveI : Finite (projectiveSL 3 K) := Finite.of_surjective (proj 3 K) (proj_surjective 3 K)
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (by norm_num : 1 ≤ 3)
  rw [← hP]
  exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P

theorem l3_isPerfect_sl3 : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
  CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)

theorem l3_solv_S [Finite K] (hK : 4 ≤ Nat.card K)
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)} (hU : unitriangular 3 K ≤ A)
    (hA : Group.IsSolvable ↥A) : A ≤ upperTriangular 3 K :=
  CFSG.ASVolI.burnsideAut_sl3_solvable_le hK hU hA

theorem l3_solv_P [Finite K] (hK : 4 ≤ Nat.card K) :
    CFSG.ASVolI.burnsideAut_SolvBorel (projectiveSL 3 K) (projUnitriangular 3 K) :=
  CFSG.ASVolI.burnsideAut_solvBorel_projectiveSL3 hK

theorem l3_solv_P' [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {A : Subgroup (projectiveSL 3 K)} (hU : projUnitriangular 3 K ≤ A)
    (hA : Group.IsSolvable ↥A) : A ≤ projUpperTriangular 3 K :=
  (l3_solv_P hK A hU hA).trans (normalizer_projUnitriangular (K := K) (n := 3) 2).le

end CFSG.Quasithin.H13.P31X
