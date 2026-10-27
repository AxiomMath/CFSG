module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowMGe
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4MClass
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4BF
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowAutInner
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowIndex
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.M
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open ArithmeticFunction CFSG.Monster.Generated CFSG.YGroups CFSG.YGroups.Y443
  CFSG.Monster.Existence CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
  CFSG.EvenSporadicStandard.Solomon78

theorem m4_cardFactors_two_mul_monsterBabyOrder :
    cardFactors (2 * CFSG.Open.monsterBabyOrder) = 70 := by
  unfold CFSG.Open.monsterBabyOrder
  rw [show 2 * (2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47 : ℕ) =
    2 ^ 42 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47 by ring]
  repeat rw [cardFactors_mul (by norm_num) (by norm_num)]
  rw [cardFactors_apply_prime_pow (by norm_num), cardFactors_apply_prime_pow (by norm_num),
    cardFactors_apply_prime_pow (by norm_num), cardFactors_apply_prime_pow (by norm_num),
    cardFactors_apply_prime (by norm_num), cardFactors_apply_prime (by norm_num),
    cardFactors_apply_prime (by norm_num), cardFactors_apply_prime (by norm_num),
    cardFactors_apply_prime (by norm_num), cardFactors_apply_prime (by norm_num),
    cardFactors_apply_prime (by norm_num)]

theorem w4Thm11_1RowM4_M_holds :
    W4Thm11_1RowM4 .M := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  show 4 ≤ E3.mParam Y
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  obtain ⟨e0⟩ := hs
  obtain ⟨f⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_gmat
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* Gmat := e0.trans f
  have hZ : Nat.card (Subgroup.center ↥L) = 1 := gmat_center_trivial ↥L hq ⟨e⟩
  have hYL : Y = L :=
    W4Row.eq_of_fstar_eq_of_autInner hLY hLn hF hq e gmat_autInner
  have hZb : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
  let e1 : ↥L ≃* Gmat :=
    (QuotientGroup.quotientBot (G := ↥L)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZb).symm.trans e)
  let ι : Gmat →* MulAut W := L.subtype.comp e1.symm.toMonoidHom
  have hι : Function.Injective ι := L.subtype_injective.comp e1.symm.injective
  have hc2 : orderOf (fM y443C) = 2 := gmat_c_order
  have hcx : ∀ g : Gmat, orderOf g = 2 → IsConj (fM y443C) g ∨ IsConj xGmat g := by
    intro g hg
    rcases Census.generated_group_two_involution_classes g hg with h | h
    · exact Or.inr h
    · exact Or.inl (isConj_tStar_fM_C.symm.trans h)
  have hcc : ∀ {a b : Gmat}, IsConj a b →
      Nat.card (Subgroup.centralizer ({a} : Set Gmat)) =
        Nat.card (Subgroup.centralizer ({b} : Set Gmat)) := by
    intro a b h
    obtain ⟨c, rfl⟩ := isConj_iff.1 h
    refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj c).toEquiv fun g => ?_)
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    constructor
    · intro hg
      calc c * g * c⁻¹ * (c * a * c⁻¹) = c * (g * a) * c⁻¹ := by group
        _ = c * (a * g) * c⁻¹ := by rw [hg]
        _ = c * a * c⁻¹ * (c * g * c⁻¹) := by group
    · intro hg
      have h2 : c * (g * a) * c⁻¹ = c * (a * g) * c⁻¹ :=
        calc c * (g * a) * c⁻¹ = c * g * c⁻¹ * (c * a * c⁻¹) := by group
          _ = c * a * c⁻¹ * (c * g * c⁻¹) := hg
          _ = c * (a * g) * c⁻¹ := by group
      simpa using h2
  have hcent : Nat.card ↥(Subgroup.centralizer ({fM y443C} : Set Gmat)) =
      2 * CFSG.Open.monsterBabyOrder := by
    rw [← natCard_centralizer_tGmat]
    exact (hcc isConj_tStar_fM_C).symm
  have hord : (Nat.card (Subgroup.centralizer ({fM y443C} : Set Gmat))).factorization 2 <
      (Nat.card Gmat).factorization 2 := by
    rw [hcent, natCard_Gmat_eq_monsterOrder, factorization_two_double_baby,
      factorization_two_monsterOrder]
    norm_num
  have hΩ : cardFactors (Nat.card ↥(Subgroup.centralizer ({fM y443C} : Set Gmat))) ≤ 70 := by
    rw [hcent, m4_cardFactors_two_mul_monsterBabyOrder]
  have hB := exists_noncentral_isConj_centre_B
  obtain ⟨x0, y0, z0, -, hcfg0, hy0, -⟩ := hB
  obtain ⟨-, hz, -⟩ := gmat_twoA
  obtain ⟨π, hπs, hker⟩ := gmat_twoA_hom
  obtain ⟨x1, y1, z1, hcfg1, -⟩ := heis_in_centralizer_of_hom hc2 hz π hπs hker hcfg0 hy0
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.B := CFSG.Sporadic.B.fam_b_simplicity
  have key := two_pow_four_le_index_of_two_classes hW' ι hι hc2 hcx hord gmat_twoA hΩ
    gmat_gen ⟨x1, y1, z1, hcfg1⟩ exists_noncentral_isConj_centre_B
  have hY2 : ∃ t ∈ Y, orderOf t = 2 := by
    refine ⟨ι (fM y443C), hLY (e1.symm (fM y443C)).2, ?_⟩
    rw [orderOf_injective ι hι, hc2]
  refine le_mParam_of_index_sq (ρ := 4) hW' hY2 fun t htY hto => ?_
  have htL : t ∈ L := hYL ▸ htY
  have hg2 : orderOf (e1 ⟨t, htL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hto]
  have hιg : ι (e1 ⟨t, htL⟩) = t := by simp [ι]
  have h4 := key _ hg2
  rw [hιg] at h4
  calc 2 ^ (2 * 4) = (2 ^ 4) ^ 2 := by norm_num
    _ ≤ _ := Nat.pow_le_pow_left h4 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
