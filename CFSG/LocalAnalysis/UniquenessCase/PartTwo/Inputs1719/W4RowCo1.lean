module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowAutInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHeisOut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowIndex
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1Final
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1HeisInv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family CFSG.Blueprint
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

theorem w4Thm11_1RowM_Co1_holds :
    W4Thm11_1RowM .Co1 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e⟩ := hs
  have hYL : Y = L := W4Row.eq_of_fstar_eq_of_autInner hLY hLn hF hq e co1_autInner
  show 8 ≤ E3.mParam Y
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hZ2 : Nat.card (Subgroup.center ↥L) ∣ 2 := co1_center_dvd ↥L hq e
  have hZ5 : ¬ 5 ∣ Nat.card (Subgroup.center ↥L) := fun h5 => by
    have := Nat.le_of_dvd (by norm_num) (h5.trans hZ2)
    omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hY2 : ∃ t ∈ Y, orderOf t = 2 := by
    have h2S : 2 ∣ Nat.card (NativeSporadic.Carrier .Co1) := by
      change 2 ∣ Nat.card NativeSporadic.Co1
      rw [CFSG.Sporadic.Co1.card_Co1]
      norm_num
    have hS : Nat.card (NativeSporadic.Carrier .Co1) ∣ Nat.card L := by
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
  have hbo : orderOf (e (QuotientGroup.mk ⟨t, htL⟩)) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  obtain ⟨x, y, w, h, hy, hinv⟩ := co1_heis_inv _ hbo
  have h1 := W4Row.two_pow_le_index_sq_of_inner_heisCfg hW' e (p := 5) (n := 0) (by norm_num)
    hZ5 htL ht2 h hy hinv
  rw [orderOf_two_zmod_five_cut] at h1
  exact (Nat.pow_le_pow_right (by norm_num) (by norm_num)).trans h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
