module

public import CFSG.Quasithin.Background.G118Inputs
public import CFSG.Quasithin.Background.G118Alt
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace G11

namespace G118

theorem sl24IsoA5 : SL24IsoA5 := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
    obtain ⟨r, hr, hAr⟩ := hA
    rw [Fintype.card_fin] at hr
    have h2 : (2 : GaloisField 2 2) = 0 := CharTwo.two_eq_zero
    have hr1 : r = 1 := by
      have : (r - 1) * (r - 1) = 0 := by linear_combination hr + (1 - r) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hAr, hr1]
    simp
  obtain ⟨e⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hK)
  let ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact ⟨(specialLinearGroupEquivStatedSL 2 (GaloisField 2 2)).symm.trans
    (ePSL.symm.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 2)).trans e))⟩

theorem autA5Input : AutA5Input :=
  ⟨CFSG.Quasithin.SteinbergCB.conjPerm_injective (by norm_num),
    CFSG.Quasithin.SteinbergCB.conjPerm_surjective (Or.inl rfl)⟩

end G118

end G11

end CFSG.Quasithin
