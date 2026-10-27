module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Defs
public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Outer
public import Certificates.Data.G2GenCheck
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Map
import CFSG.CGT.PushingUpLit.CGT6.EmbModule.K7bX
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.CGT.PushingUpLit.CGT6.EmbG23 Certificates.G2Gen
open CFSG.CGT.PushingUpLit.CGT6.EmbModule
open CFSG.LieType.Ree
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert
open Certificates.G2ThreeMax

local notation "mt" => CFSG.CGT.PushingUpLit.CGT6.EmbModule.mt


private theorem g2GenOut_wordElem_append (u v : List ℕ) :
    wordElem gensG (u ++ v) = wordElem gensG u * wordElem gensG v := by
  simp [wordElem, List.map_append, List.prod_append]

private noncomputable def g2GenOut_mtHom : G3 →* Mat3 where
  toFun := mt
  map_one' := mt_one.trans M_idArr
  map_mul' := fun a b => (mt_mul a b).symm

private theorem g2GenOut_mt_pow (x : G3) (n : ℕ) : mt (x ^ n) = mt x ^ n :=
  map_pow g2GenOut_mtHom x n

private theorem g2GenOut_M_pow (a : Array ℕ) (n : ℕ) : M a ^ n = M (mpowArr a n) := by
  induction n with
  | zero => simp [mpowArr, M_idArr]
  | succ n ih =>
    rw [pow_succ', ih, ← M_mmul]
    rfl

theorem g23_phi_genGood_of_check (hchk : g2GenCheck = true) : IsGenGood phi := by
  change IsGenGood phiG
  haveI : CharP (ZMod 3) ReeTag.G2.prime := ZMod.charP 3
  have h := hchk
  simp only [g2GenCheck, Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, -, -, -, h6, h7, h8, h9, h10⟩ := h
  have hp1 : phiG (wordElem gensG g1W) = wordElem gensG [5] := by
    have h1 := phi_word g1W (by decide)
    rwa [show swapK7b g1W = [5] from by decide] at h1
  have hp2 : phiG (wordElem gensG g2W) = wordElem gensG [1] := by
    have h2 := phi_word g2W (by decide)
    rwa [show swapK7b g2W = [1] from by decide] at h2
  have hg1i : wordElem gensG g1iW = (wordElem gensG g1W)⁻¹ :=
    eq_inv_of_mul_eq_one_right
      (eq_of_beq3 (mt_mul' (mt_word g1W (by decide)) (mt_word g1iW (by decide))) mt_one h6)
  have hg2i : wordElem gensG g2iW = (wordElem gensG g2W)⁻¹ :=
    eq_inv_of_mul_eq_one_right
      (eq_of_beq3 (mt_mul' (mt_word g2W (by decide)) (mt_word g2iW (by decide))) mt_one h7)
  have hc1i : wordElem gensG c1iW = (wordElem gensG c1W)⁻¹ :=
    eq_inv_of_mul_eq_one_right
      (eq_of_beq3 (mt_mul' (mt_word c1W (by decide)) (mt_word c1iW (by decide))) mt_one h8)
  have hc1 : (wordElem gensG g1W)⁻¹ * phiG (wordElem gensG g1W) = wordElem gensG c1W := by
    rw [← hg1i, hp1, ← g2GenOut_wordElem_append]
    rfl
  have hc2 : (wordElem gensG g2W)⁻¹ * phiG (wordElem gensG g2W) = wordElem gensG c2W := by
    rw [← hg2i, hp2, ← g2GenOut_wordElem_append]
    rfl
  let y : G3 := wordElem gensG yOutW
  have hy_mt : mt y = M (wordArr yOutW) := mt_word yOutW (by decide)
  have hy_eq : wordElem gensG yOutW =
      wordElem gensG c1W * wordElem gensG c1W * wordElem gensG c2W *
        wordElem gensG c1W * wordElem gensG c2W * wordElem gensG c1iW *
        wordElem gensG c2W := by
    simp only [yOutW, g2GenOut_wordElem_append]
  have hy13 : y ^ 13 = 1 := by
    have hmt : mt (y ^ 13) = M (mpowArr (wordArr yOutW) 13) := by
      rw [g2GenOut_mt_pow, hy_mt, g2GenOut_M_pow]
    exact eq_of_beq3 hmt mt_one h9
  have hyne : y ≠ 1 := ne_one_of_nz hy_mt (by decide) (by decide) h10
  have hyord : orderOf y = 13 := by
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    exact orderOf_eq_prime hy13 hyne
  let g : Fin 2 → G3 := ![wordElem gensG g1W, wordElem gensG g2W]
  have hf0 : (g 0)⁻¹ * phiG (g 0) = wordElem gensG c1W := by simp [g, hc1]
  have hf1 : (g 1)⁻¹ * phiG (g 1) = wordElem gensG c2W := by simp [g, hc2]
  have hc1mem : wordElem gensG c1W ∈
      Subgroup.closure (Set.range fun i => (g i)⁻¹ * phiG (g i)) := by
    rw [← hf0]; exact Subgroup.subset_closure ⟨0, rfl⟩
  have hc2mem : wordElem gensG c2W ∈
      Subgroup.closure (Set.range fun i => (g i)⁻¹ * phiG (g i)) := by
    rw [← hf1]; exact Subgroup.subset_closure ⟨1, rfl⟩
  have hymem : y ∈ Subgroup.closure (Set.range fun i => (g i)⁻¹ * phiG (g i)) := by
    dsimp only [y]
    rw [hy_eq, hc1i]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hc1mem hc1mem) hc2mem)
        hc1mem) hc2mem) (Subgroup.inv_mem _ hc1mem)) hc2mem
  refine ⟨2, g, y, 13, by norm_num, hyord, hymem, ?_⟩
  have hord : dParam 13 = 12 := by
    show orderOf (2 : ZMod 13) = 12
    rw [orderOf_eq_iff (by norm_num : 0 < 12)]
    refine ⟨by decide, ?_⟩
    intro k hk _
    interval_cases k <;> decide
  rw [hord]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
