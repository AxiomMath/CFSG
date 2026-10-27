module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowMGe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4ChainL
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi23
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.MDichotomy

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.Fi23
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open ArithmeticFunction

theorem w4Thm11_1RowM4_Fi23_holds :
    W4Thm11_1RowM4 .Fi23 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e⟩ := hs
  have hZ : Nat.card (Subgroup.center ↥L) = 1 := fi23_center_card ↥L hq e
  have hbot : Subgroup.center ↥L = ⊥ :=
    Subgroup.eq_bot_of_card_eq (Subgroup.center ↥L) hZ
  let eL : ↥L ≃* NativeSporadic.Fi23 :=
    ((QuotientGroup.quotientMulEquivOfEq (M := Subgroup.center ↥L) (N := ⊥) hbot).trans
      QuotientGroup.quotientBot).symm.trans e
  let f : NativeSporadic.Fi23 →* MulAut W :=
    L.subtype.comp (eL.symm : NativeSporadic.Fi23 →* ↥L)
  have hf_inj : Function.Injective f := L.subtype_injective.comp eL.symm.injective
  obtain ⟨cx, cy, cz, hcfg, _hy⟩ := fi23_heisCfg
  have hfz : f cz ≠ 1 := by
    intro h1
    exact hcfg.z1 (hf_inj (by rw [h1, map_one]))
  have hcfgmap : HeisCfg 3 4
      (fun i : Fin 4 => f (cx i))
      (fun i : Fin 4 => f (cy i))
      (f cz) :=
    hcfg.map f hfz
  let z' : MulAut W := f cz
  have hz'L : z' ∈ L := by
    change f cz ∈ L
    exact (eL.symm cz).2
  have hEL : Subgroup.zpowers z' ≤ L := Subgroup.zpowers_le.2 hz'L
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have h162 : 2 ^ 162 ≤ (fixV (Subgroup.zpowers z')).index := by
    have hbase : 2 ^ (3 ^ 4 * orderOf (2 : ZMod 3)) ≤
        Nat.card (imgT (f cz)) := by
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact two_pow_le_card_imgT_of_heisCfg hW' (p := 3) (n := 4) (by norm_num) hcfgmap
    have hord : orderOf (2 : ZMod 3) = 2 := by
      have h2 : (2 : ZMod 3) ^ 2 = 1 := by decide
      have h1 : (2 : ZMod 3) ≠ 1 := by decide
      exact orderOf_eq_prime h2 h1
    rw [show 3 ^ 4 * orderOf (2 : ZMod 3) = 162 by rw [hord]; norm_num] at hbase
    rw [← index_fixV_zpowers_eq_card_imgT (f cz)] at hbase
    exact hbase
  have hΩ : cardFactors (Nat.card ↥L) = 38 := by
    rw [Nat.card_congr eL.toEquiv, CFSG.Sporadic.Fi23.card_Fi23]
    norm_num [cardFactors, Nat.primeFactorsList]
  have hE : 2 ^ ((4 - 1) * (cardFactors (Nat.card ↥L) + 1)) <
      (fixV (Subgroup.zpowers z')).index := by
    rw [hΩ]
    have h117 : (4 - 1) * (38 + 1) = 117 := by norm_num
    rw [h117]
    exact lt_of_lt_of_le
      (Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ)) (by norm_num : 117 < 162)) h162
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hY2 : ∃ t ∈ Y, orderOf t = 2 := by
    have h2S : 2 ∣ Nat.card (NativeSporadic.Carrier .Fi23) := by
      change 2 ∣ Nat.card NativeSporadic.Fi23
      rw [CFSG.Sporadic.Fi23.card_Fi23]
      norm_num
    have hS : Nat.card (NativeSporadic.Carrier .Fi23) ∣ Nat.card L := by
      rw [← Nat.card_congr e.toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    obtain ⟨t, hto⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 (h2S.trans hS)
    exact ⟨t, hLY t.2, by rwa [Subgroup.orderOf_coe]⟩
  exact le_mParam_of_chain_L hW' hLY hLn hF hq hO2 hY2 hEL (c := 4) hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
