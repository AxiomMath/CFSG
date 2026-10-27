module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowMGe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4ChainL
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi24Prime
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.MDichotomy

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint CFSG.QuasithinUnique.Setup.X1 CFSG.AGLEmbedding
open CFSG.Sporadic.Fi23
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
open ArithmeticFunction

theorem w4Thm11_1RowM4_Fi24Prime_holds :
    W4Thm11_1RowM4 .Fi24Prime := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e⟩ := hs
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hZd : Nat.card (Subgroup.center ↥L) ∣ 3 := fi24_center_dvd ↥L hq e
  have hZp : IsPGroup 3 (Subgroup.center ↥L) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by rwa [pow_one])
  obtain ⟨hfinF, -, hperfF, -⟩ := fi23_carrierFacts
  haveI : Finite NativeSporadic.Fi23 := hfinF
  haveI : Group.IsPerfect NativeSporadic.Fi23 := hperfF
  have hk : KernelTrivialAt NativeSporadic.Fi23 3 := kernelTrivialAt_three_Fi23
  have hK := ker_centerQuotientHom e
  obtain ⟨σ, hσ⟩ := exists_hom_lift_of_kernelTrivialAt (G := ↥L) hk (centerQuotientHom e)
    (centerQuotientHom_surjective e) hK.le (hK ▸ hZp) fi23ToFi24
  obtain ⟨cx, cy, cz, hcfg, -⟩ := fi23_heisCfg
  have hz : σ cz ≠ 1 := by
    intro h1
    apply hcfg.z1
    apply fi23ToFi24_injective
    have h3 : fi23ToFi24 cz = 1 :=
      (hσ cz).symm.trans
        ((congrArg (centerQuotientHom e) h1).trans (map_one (centerQuotientHom e)))
    exact h3.trans (map_one fi23ToFi24).symm
  have hz' : L.subtype (σ cz) ≠ 1 := fun h1 =>
    hz (L.subtype_injective (by rw [h1, map_one]))
  have hcfgmap : HeisCfg 3 4
      (fun i : Fin 4 => L.subtype (σ (cx i)))
      (fun i : Fin 4 => L.subtype (σ (cy i)))
      (L.subtype (σ cz)) :=
    (hcfg.map σ hz).map L.subtype hz'
  let z' : MulAut W := L.subtype (σ cz)
  have hz'L : z' ∈ L := (σ cz).2
  have hEL : Subgroup.zpowers z' ≤ L := Subgroup.zpowers_le.2 hz'L
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have h162 : 2 ^ 162 ≤ (fixV (Subgroup.zpowers z')).index := by
    have hbase : 2 ^ (3 ^ 4 * orderOf (2 : ZMod 3)) ≤ Nat.card (imgT z') := by
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact two_pow_le_card_imgT_of_heisCfg hW' (p := 3) (n := 4) (by norm_num) hcfgmap
    have h2 : (2 : ZMod 3) ^ 2 = 1 := by decide
    have h1 : (2 : ZMod 3) ≠ 1 := by decide
    have hord : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime h2 h1
    rw [show 3 ^ 4 * orderOf (2 : ZMod 3) = 162 by rw [hord]; norm_num] at hbase
    rwa [← index_fixV_zpowers_eq_card_imgT z'] at hbase
  have hZcf : cardFactors (Nat.card (Subgroup.center ↥L)) ≤ 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hZd with h | h
    · rw [h]; simp
    · rw [h, cardFactors_apply_prime Nat.prime_three]
  have hFcf : cardFactors (Nat.card NativeSporadic.Fi24prime) = 47 := by
    rw [CFSG.Sporadic.Fi24.card_Fi24prime]
    norm_num [cardFactors, Nat.primeFactorsList]
  have hcardL : Nat.card ↥L =
      Nat.card (Subgroup.center ↥L) * Nat.card NativeSporadic.Fi24prime := by
    calc Nat.card ↥L
        = Nat.card (↥L ⧸ Subgroup.center ↥L) * Nat.card (Subgroup.center ↥L) :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup _
      _ = Nat.card NativeSporadic.Fi24prime * Nat.card (Subgroup.center ↥L) := by
          rw [show Nat.card (↥L ⧸ Subgroup.center ↥L) =
            Nat.card NativeSporadic.Fi24prime from Nat.card_congr e.toEquiv]
      _ = Nat.card (Subgroup.center ↥L) * Nat.card NativeSporadic.Fi24prime := mul_comm _ _
  have hΩ : cardFactors (Nat.card ↥L) ≤ 48 := by
    have hZ0 : Nat.card (Subgroup.center ↥L) ≠ 0 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hZd with h | h <;> rw [h] <;> norm_num
    have hF0 : Nat.card NativeSporadic.Fi24prime ≠ 0 := by
      rw [CFSG.Sporadic.Fi24.card_Fi24prime]; norm_num
    rw [hcardL, cardFactors_mul hZ0 hF0]
    omega
  have hE : 2 ^ ((4 - 1) * (cardFactors (Nat.card ↥L) + 1)) <
      (fixV (Subgroup.zpowers z')).index := by
    have hexp : (4 - 1) * (cardFactors (Nat.card ↥L) + 1) < 162 := by omega
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hexp) h162
  have hY2 : ∃ t ∈ Y, orderOf t = 2 := by
    have h2S : 2 ∣ Nat.card (NativeSporadic.Carrier .Fi24Prime) := by
      change 2 ∣ Nat.card NativeSporadic.Fi24prime
      rw [CFSG.Sporadic.Fi24.card_Fi24prime]
      norm_num
    have hS : Nat.card (NativeSporadic.Carrier .Fi24Prime) ∣ Nat.card L := by
      rw [← Nat.card_congr e.toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    obtain ⟨t, hto⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 (h2S.trans hS)
    exact ⟨t, hLY t.2, by rwa [Subgroup.orderOf_coe]⟩
  exact le_mParam_of_chain_L hW' hLY hLn hF hq hO2 hY2 hEL (c := 4) hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
