module

public import CFSG.LieType.SteinbergBRLinearSmallParabolic
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X6

variable {K : Type} [Field K] [Finite K]

abbrev parab34 (K : Type) [Field K] (j : Fin 2) : Subgroup (projectiveSL 3 K) :=
  projStabilizer (flagSpace 3 K ((j : ℕ) + 1))

theorem card_SL2_four (hK : Nat.card K = 4) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 60 := by
  rw [CFSG.OrderReductions.LinearOrders.card_specialLinear K 2 (by norm_num), hK]
  decide

theorem parab34_structure (hK : Nat.card K = 4) (j : Fin 2) :
    Nat.card ↥(dInf (parab34 K j)) = 960 ∧
      Nat.card ↥(CFSG.pCore 2 ↥(dInf (parab34 K j))) = 16 ∧
      Nonempty (↥(dInf (parab34 K j)) ⧸ CFSG.pCore 2 ↥(dInf (parab34 K j)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hd : 1 ≤ (j : ℕ) + 1 := by omega
  have hdn : (j : ℕ) + 1 < 3 := by omega
  have hF : Even (Nat.card K) := by rw [hK]; decide
  have hW := finrank_flagSpace (n := 3) (K := K) (i := (j : ℕ) + 1) hdn.le
  obtain ⟨-, -, hrad, hpcore, hsolv, ⟨eQ⟩, ⟨eS⟩, hcard, -⟩ :=
    CFSG.LieType.linear_small_parabolic_perfect_residual_structure hF hd hdn
      (Or.inl ⟨rfl, hK.ge⟩) (flagSpace 3 K ((j : ℕ) + 1)) hW (P := parab34 K j)
      (B := dInf (parab34 K j)) rfl rfl
  have hmax : max ((j : ℕ) + 1) (3 - ((j : ℕ) + 1)) = 2 := by
    fin_cases j <;> rfl
  have hdd : ((j : ℕ) + 1) * (3 - ((j : ℕ) + 1)) = 2 := by
    fin_cases j <;> rfl
  rw [hmax] at eS eQ
  rw [hdd, hK] at hcard
  set B := dInf (parab34 K j) with hB
  have hsc : Nat.card ↥(CFSG.solvableRadical ↥B) = 16 := by
    rw [hsolv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hrad).toEquiv, hcard]
    norm_num
  have e : ↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hpcore).trans (eQ.trans eS)
  refine ⟨?_, by rw [hpcore, hsc], ⟨e⟩⟩
  rw [(CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr e.toEquiv,
    card_SL2_four hK, hpcore, hsc]

omit [Finite K] in
theorem card_scalars_four (hK : Nat.card K = 4) : Nat.card (scalars 3 K) = 3 := by
  have hu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  rw [scalars_eq_center, Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (⟨0, by norm_num⟩ : Fin 3)).toEquiv]
  have htop : rootsOfUnity (Fintype.card (Fin 3)) K = ⊤ := by
    rw [eq_top_iff]
    intro u _
    rw [mem_rootsOfUnity, Fintype.card_fin, ← hu]
    exact pow_card_eq_one'
  rw [htop, Subgroup.card_top, hu]

theorem card_projectiveSL_four (hK : Nat.card K = 4) : Nat.card (projectiveSL 3 K) = 20160 := by
  rw [card_projectiveSL, card_SL_eq (by norm_num), card_scalars_four hK, hK]
  decide

theorem normalizer_le_parab34 [CharP K 2] (j : Fin 2) :
    Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) ≤ parab34 K j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_projUnitriangular 2]
  exact projUpperTriangular_le_projStabilizer _

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
