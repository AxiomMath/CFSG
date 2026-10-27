module

public import CFSG.Quasithin.Vol2.GoldschmidtF431BNPoly
public import CFSG.Quasithin.Recognition.Stroth.RankTwoSystemMoufang
public import CFSG.Quasithin.Recognition.Stroth.PolygonRigidity
public import CFSG.GH74.GLS.SP.Identify

public section

namespace CFSG.Quasithin.Stroth

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Quasithin CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Geometry.GeneralizedPolygons
  CFSG.LieType.Universal.Unitary.SUExtras
open scoped Pointwise

universe u

abbrev Un5Group (k : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] : Type :=
  SU (unitaryInvolution F 2 k) 5 ⧸ Subgroup.center (SU (unitaryInvolution F 2 k) 5)

variable {k : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)]
  (hF : Nat.card F = (2 ^ k) ^ 2) (ζ : traceZero (unitaryInvolution F 2 k))
  [hζ : Fact ((ζ : F) ≠ 0)]

instance finite_Un5Group : Finite (Un5Group k F) := inferInstance

noncomputable instance un5System_fintypeVertex : Fintype (un5System hF ζ).Vertex :=
  letI := Fintype.ofFinite (Un5Group k F)
  rankTwoVertexFintype _

theorem un5System_faithfulSMul :
    letI : MulAction (Un5Group k F) (un5System hF ζ).Vertex := rtsMulAction (un5System hF ζ)
    FaithfulSMul (Un5Group k F) (un5System hF ζ).Vertex :=
  faithfulSMul_of_faithfulOnBuilding (un5System hF ζ)

theorem un5System_isGeneralizedPolygon :
    IsGeneralizedPolygon (un5System hF ζ).graph 4 := by
  exact isGeneralizedPolygon_of_isGenPolygon (by norm_num)
    (CFSG.Quasithin.H13.F431.BN.isGenPolygon (un5System hF ζ))

theorem un5System_isThick : IsThick (un5System hF ζ).graph := by
  intro v
  rw [← SimpleGraph.ncard_neighborSet, ← Nat.card_coe_set_eq]
  exact CFSG.Quasithin.H13.F431.BN.three_le_card_neighborSet (un5System hF ζ) v

theorem un5System_xplus_eq_top : (un5System hF ζ).Xplus = ⊤ := by
  haveI : IsSimpleGroup (Un5Group k F) := isSimpleGroup_un5 hF
  exact CFSG.GH74.GLS.SP.xplus_eq_top (un5System hF ζ)

section RootGroups

variable {k : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)]
  (hF : Nat.card F = (2 ^ k) ^ 2) (ζ : traceZero (unitaryInvolution F 2 k))
  [Fact ((ζ : F) ≠ 0)]

theorem rootHom_injective {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (hji : j ≠ Fin.rev i) :
    Function.Injective (rootHom σ hσ hij hi hj) := by
  intro c d hcd
  have hm := congrArg (fun x : SU σ n => ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) hcd
  rw [coe_rootHom, coe_rootHom] at hm
  have h1 := congrFun (congrFun hm i) j
  rw [SUExtras.rootMatrix_apply_pq hij hji] at h1
  rw [SUExtras.rootMatrix_apply_pq hij hji] at h1
  exact Multiplicative.toAdd.injective h1

theorem un5Oct_one_card :
    Nat.card (un5Oct (p := 2) (f := k) hF 1) = (2 ^ k) ^ 2 := by
  have hσ := unitaryInvolution_involutive (p := 2) (f := k) hF
  have hw : weight 5 0 - weight 5 1 = toStd 5 (octRootB 1) := by decide
  have hne : toStd 5 (octRootB 1) ≠ 0 := by decide
  have hle : un5Oct (p := 2) (f := k) hF 1 ≤
      (rootHom (unitaryInvolution F 2 k) hσ
        (n := 5) (i := 0) (j := 1) (by decide) (by decide) (by decide)).range := by
    intro x hx
    refine ⟨Multiplicative.ofAdd (mat (unitaryInvolution F 2 k) 5 x 0 1), ?_⟩
    refine (eq_of_mem_rootGroup hσ hx
      (rootHom_mem hσ (by decide) (by decide) (by decide) (by decide) hw
        (Multiplicative.ofAdd _)) ?_).symm
    intro a b hab
    rcases hab with h | h
    · have hmem : (a = 0 ∧ b = 1) ∨ (a = 3 ∧ b = 4) := by
        revert h
        fin_cases a <;> fin_cases b <;> decide
      have hrel : mat (unitaryInvolution F 2 k) 5 x 3 4 =
          -unitaryInvolution F 2 k (mat (unitaryInvolution F 2 k) 5 x 0 1) := by
        have hsum := sum_mat_mul_mat x 1 4
        rw [Fin.sum_univ_five] at hsum
        have h44 : mat (unitaryInvolution F 2 k) 5 x (Fin.rev 0) 4 = 1 := by
          rw [show (Fin.rev 0 : Fin 5) = 4 from rfl]
          exact mat_apply_self_of_mem_rootGroup hσ hne hx 4
        have h11 : mat (unitaryInvolution F 2 k) 5 x 1 1 = 1 :=
          mat_apply_self_of_mem_rootGroup hσ hne hx 1
        have h24 : mat (unitaryInvolution F 2 k) 5 x 2 4 = 0 := by
          rw [mat_apply_of_mem_rootGroup hσ hx (a := 2) (b := 4) (by decide) (by decide)]
          rfl
        have h14 : mat (unitaryInvolution F 2 k) 5 x 1 4 = 0 := by
          rw [mat_apply_of_mem_rootGroup hσ hx (a := 1) (b := 4) (by decide) (by decide)]
          rfl
        have h04 : mat (unitaryInvolution F 2 k) 5 x 0 4 = 0 := by
          rw [mat_apply_of_mem_rootGroup hσ hx (a := 0) (b := 4) (by decide) (by decide)]
          rfl
        have h21 : mat (unitaryInvolution F 2 k) 5 x 2 1 = 0 := by
          rw [mat_apply_of_mem_rootGroup hσ hx (a := 2) (b := 1) (by decide) (by decide)]
          rfl
        have h31 : mat (unitaryInvolution F 2 k) 5 x 3 1 = 0 := by
          rw [mat_apply_of_mem_rootGroup hσ hx (a := 3) (b := 1) (by decide) (by decide)]
          rfl
        have h41 : mat (unitaryInvolution F 2 k) 5 x 4 1 = 0 := by
          rw [mat_apply_of_mem_rootGroup hσ hx (a := 4) (b := 1) (by decide) (by decide)]
          rfl
        rw [show (Fin.rev 1 : Fin 5) = 3 from rfl, show (Fin.rev 2 : Fin 5) = 2 from rfl,
          show (Fin.rev 3 : Fin 5) = 1 from rfl, show (Fin.rev 4 : Fin 5) = 0 from rfl] at hsum
        rw [h44, h11, h24, h14, h04, h21, h31, h41] at hsum
        simp only [map_one, map_zero, mul_one, mul_zero, add_zero, zero_add,
          show ((4 : Fin 5) = 3) = False from by decide, if_false] at hsum
        linear_combination hsum
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [mat_apply, mat_apply, coe_rootHom, SUExtras.rootMatrix_apply_pq (by decide) (by decide)]
        rfl
      · have hroot : mat (unitaryInvolution F 2 k) 5
            (rootHom (unitaryInvolution F 2 k) hσ
              (n := 5) (i := 0) (j := 1) (by decide) (by decide) (by decide)
              (Multiplicative.ofAdd (mat (unitaryInvolution F 2 k) 5 x 0 1))) 3 4 =
            -unitaryInvolution F 2 k (mat (unitaryInvolution F 2 k) 5 x 0 1) := by
          rw [mat_apply, coe_rootHom]
          simp only [rootMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
            Matrix.single_apply, Fin.rev, Fin.val_zero, Fin.val_one]
          norm_num
        rw [hrel, hroot]
    · exfalso
      revert h
      fin_cases a <;> fin_cases b <;> decide
  have hge : (rootHom (unitaryInvolution F 2 k) hσ
      (n := 5) (i := 0) (j := 1) (by decide) (by decide) (by decide)).range ≤
      un5Oct (p := 2) (f := k) hF 1 := by
    rintro x ⟨c, rfl⟩
    exact rootHom_mem hσ (by decide) (by decide) (by decide) (by decide) hw c
  rw [le_antisymm hle hge]
  have hinj := rootHom_injective (F := F) (σ := unitaryInvolution F 2 k) (hσ := hσ)
    (n := 5) (i := 0) (j := 1) (by decide) (by decide) (by decide) (by decide)
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤) hinj,
    Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, hF]

theorem un5Proj_injOn_unU {x y : SU (unitaryInvolution F 2 k) 5}
    (hx : x ∈ unU (p := 2) (f := k) hF 5) (hy : y ∈ unU (p := 2) (f := k) hF 5)
    (hxy : un5Proj (F := F) (f := k) x = un5Proj (F := F) (f := k) y) : x = y := by
  have hker : x⁻¹ * y ∈ (un5Proj (F := F) (f := k)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hU : x⁻¹ * y ∈ unU (p := 2) (f := k) hF 5 :=
    (unU (p := 2) (f := k) hF 5).mul_mem ((unU (p := 2) (f := k) hF 5).inv_mem hx) hy
  have h1 : x⁻¹ * y = 1 := by
    have h := un5_U_inf_ker (F := F) (f := k) hF
    have : x⁻¹ * y ∈ unU (p := 2) (f := k) hF 5 ⊓ (un5Proj (F := F) (f := k)).ker :=
      ⟨hU, hker⟩
    rwa [h, Subgroup.mem_bot] at this
  exact inv_mul_eq_one.mp h1

theorem card_map_eq_card_of_injOn {G H : Type*} [Group G] [Group H] (f : G →* H)
    {K S : Subgroup G} (hK : K ≤ S) (hS : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) :
    Nat.card (K.map f) = Nat.card K := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : K => (⟨f x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ : K.map f)) ⟨?_, ?_⟩).symm
  · intro x y hxy
    exact Subtype.ext (hS x (hK x.2) y (hK y.2) (congrArg Subtype.val hxy))
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨⟨x, hx⟩, rfl⟩

theorem un5System_root_one_card :
    Nat.card ((un5System hF ζ).root 1) = (2 ^ k) ^ 2 := by
  have hroot : (un5System hF ζ).root 1 =
      (un5Oct (p := 2) (f := k) hF 1).map (un5Proj (F := F) (f := k)) := rfl
  rw [hroot, card_map_eq_card_of_injOn (un5Proj (F := F) (f := k))
    (octGroup_le_un5U (p := 2) (f := k) hF (by norm_num) (by norm_num))
    (fun x hx y hy h => un5Proj_injOn_unU hF hx hy h), un5Oct_one_card]

end RootGroups

end CFSG.Quasithin.Stroth