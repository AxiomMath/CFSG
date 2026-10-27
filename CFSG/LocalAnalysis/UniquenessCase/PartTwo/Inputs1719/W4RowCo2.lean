module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowAutInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHeisOut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowIndex
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Model
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family CFSG.Blueprint
open CFSG.Sporadic.Co2Cert CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

theorem w4Thm11_1RowM_Co2_holds :
    W4Thm11_1RowM .Co2 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  let e : CQ L ≃* ↥co2P := e₀.trans co2PermEquiv
  have hYL : Y = L := W4Row.eq_of_fstar_eq_of_autInner hLY hLn hF hq e Co2Model.co2P_autInner
  show 6 ≤ E3.mParam Y
  obtain ⟨D⟩ := Co2Model.co2CutData_nonempty
  have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := Co2Model.co2P_hZ ↥L hq.1 ⟨e⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hY2 : ∃ t ∈ Y, orderOf t = 2 := by
    have h2S : 2 ∣ Nat.card ↥co2P := by
      rw [card_co2P]
      norm_num
    have hS : Nat.card ↥co2P ∣ Nat.card L := by
      rw [← Nat.card_congr e.toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    obtain ⟨t, hto⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 (h2S.trans hS)
    exact ⟨t, hLY t.2, by rwa [Subgroup.orderOf_coe]⟩
  refine W4Row.le_mParam_of_index_sq hW' hY2 fun t htY hto => ?_
  have htL : t ∈ L := hYL ▸ htY
  have ht2 : t * t = 1 := by
    rw [← sq, ← hto]
    exact pow_orderOf_eq_one t
  have hb2 : e (QuotientGroup.mk ⟨t, htL⟩) * e (QuotientGroup.mk ⟨t, htL⟩) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul,
      show (⟨t, htL⟩ : ↥L) * ⟨t, htL⟩ = 1 from Subtype.ext ht2, QuotientGroup.mk_one, map_one]
  have hb1 : e (QuotientGroup.mk ⟨t, htL⟩) ≠ 1 := fun h1 =>
    W4Row.redHom_ne_one_of_o2Trivial hO2 e htL hto (by rw [X1.redHom_apply]; exact h1)
  by_cases hA : IsConj D.z0 (e (QuotientGroup.mk ⟨t, htL⟩))
  · obtain ⟨x, y, w, h, hy, hinv⟩ := Co2Engine.heis_conj hA D.heisA
    have h1 := W4Row.two_pow_le_index_sq_of_inner_heisCfg hW' e (p := 3) (n := 1) (by norm_num)
      (by rw [hZ1]; norm_num) htL ht2 h hy hinv
    rw [Co2Engine.orderOf_two_zmod_three_co2] at h1
    calc 2 ^ (2 * 6) = 2 ^ ((3 - 1) * 3 ^ 1 * 2) := by norm_num
      _ ≤ _ := h1
  · have hB : ∃ (x y : Fin (0 + 1) → ↥co2P) (w : ↥co2P),
        CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisCfg 5 (0 + 1) x y w ∧
          (∀ i, y i ^ 5 = 1) ∧ e (QuotientGroup.mk ⟨t, htL⟩) * x 0 *
            (e (QuotientGroup.mk ⟨t, htL⟩))⁻¹ = (x 0)⁻¹ := by
      rcases D.classes _ hb2 hb1 hA with hc | hc
      · exact Co2Engine.heis_conj hc D.heisB
      · exact Co2Engine.heis_conj hc D.heisC
    obtain ⟨x, y, w, h, hy, hinv⟩ := hB
    have h1 := W4Row.two_pow_le_index_sq_of_inner_heisCfg hW' e (p := 5) (n := 0) (by norm_num)
      (by rw [hZ1]; norm_num) htL ht2 h hy hinv
    rw [Co2Engine.orderOf_two_zmod_five_co2] at h1
    exact (Nat.pow_le_pow_right (by norm_num) (by norm_num)).trans h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
