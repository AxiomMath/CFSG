module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerModelTri
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerLeafDefs
import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerModel
import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2G2
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofBlockMain
import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofG2Data

public section

namespace CFSG.StandardType

namespace D4Inner

open CFSG.StandardType.Triality CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
open CFSG.HardMathSupport.Lang.D4Three
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec4.E27
open CFSG.LieType.HighestRoot (g2s)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem bridge_theta
    (y : Om8 K) :
    (TriBridge.bridge (theta y) : ModGL TwistTag.D4.tag K) =
      (d4Graph K 1 (TriBridge.bridge y) : ModGL Tag.D4 K) := by
  have h1 := TriBridge.coe_bridge_theta_fieldAutP (K := K) 1 y
  rw [map_one, MulAut.one_apply] at h1
  have h2 := coe_d4Graph (K := K) 1 (TriBridge.bridge y)
  rw [pow_one] at h2
  rw [h1, h2]
  exact twistHom_id_eq TwistTag.D4 K _

theorem theta_bridge_symm_of_mem
    {w : adjointGroup Tag.D4 K}
    (hw : w ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (d4Graph K 1)) :
    theta (TriBridge.bridge.symm w) = TriBridge.bridge.symm w := by
  have h2 : TriBridge.bridge (TriBridge.bridge.symm w) = w := MulEquiv.apply_symm_apply _ w
  have hw' : d4Graph K 1 w = w := CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup.1 hw
  apply TriBridge.bridge.injective
  apply Subtype.ext
  refine (bridge_theta _).trans ?_
  refine (congrArg (fun x => ((d4Graph K 1 x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K)) h2).trans
    ?_
  exact (congrArg Subtype.val hw').trans (congrArg Subtype.val h2).symm

theorem theta_fix_centDer_sZero
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n) :
    ∀ y ∈ centDer (sZero (K := K)), (theta : MulAut (Om8 K)) y = y := by
  classical
  have hK8 : 8 ≤ Nat.card K := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hK3 : 3 ≤ Nat.card K := by omega
  have hK4 : 4 ≤ Nat.card K := by omega
  have hn1 : 1 ≤ n := by omega
  have h3 : 3 ∣ Nat.card K + 1 := three_dvd_card_add_one hK hn
  set e := fixSubgroupEquivG2 K hK3
  set ι : adjointGroup Tag.G2 K →* Om8 K :=
    (TriBridge.bridge (K := K)).symm.toMonoidHom.comp
      ((CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (d4Graph K 1)).subtype.comp
        e.symm.toMonoidHom)
  have hιapp : ∀ g, ι g = TriBridge.bridge.symm ((e.symm g : _) : adjointGroup Tag.D4 K) :=
    fun g => rfl
  have hιinj : Function.Injective ι := by
    intro a b hab
    rw [hιapp, hιapp] at hab
    exact e.symm.injective (Subtype.ext ((TriBridge.bridge (K := K)).symm.injective hab))
  have hιθ : ∀ g, theta (ι g) = ι g := fun g => by
    rw [hιapp]
    exact theta_bridge_symm_of_mem (e.symm g).2
  set z₁ : adjointGroup Tag.G2 K := g2RootSL2 g2s K tThree with hz₁
  have hez : e (sl2ShortFix tThree) = z₁ :=
    Subtype.ext (fixSubgroupEquivG2_sl2Short hK3 tThree)
  have hιz : ι z₁ = sZero := by
    rw [hιapp, ← hez, MulEquiv.symm_apply_apply, sZero_eq_bridge_symm]
    rfl
  have hz₁3 : z₁ ^ 3 = 1 := by
    rw [hz₁, ← map_pow, tThree_pow_three, map_one]
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    apply sZero_ne_one (K := K)
    rw [← hιz, h, map_one]
  set m : adjointGroup Tag.G2 K := g2WeylRep K
  have hzS : m * z₁ * m⁻¹ ∈ KS11Lie4Proof.g2ShortSL2 K := conj_g2RootSL2_short_mem K tThree
  have hz3 : (m * z₁ * m⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hz₁3, mul_one, mul_inv_cancel]
  have hz1 : m * z₁ * m⁻¹ ≠ 1 := by
    intro h
    apply hz₁1
    calc z₁ = m⁻¹ * (m * z₁ * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group
  have hq := KS11Lie7Proof.isQuasisimple_centralizer_threeA h3 hK4 hzS hz3 hz1
  have hcard := card_centralizer_short_unitary hn1 hK h3 hzS hz3 hz1
  set M : Subgroup (Om8 K) :=
    (Subgroup.centralizer ({z₁} : Set (adjointGroup Tag.G2 K))).map ι
  have eM : Subgroup.centralizer ({m * z₁ * m⁻¹} : Set (adjointGroup Tag.G2 K)) ≃* M :=
    (centralizerConjEquiv m z₁).symm.trans
      ((Subgroup.centralizer ({z₁} : Set (adjointGroup Tag.G2 K))).equivMapOfInjective ι hιinj)
  have hMC : M ≤ Subgroup.centralizer ({sZero} : Set (Om8 K)) := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ Subgroup.centralizer ({z₁} : Set (adjointGroup Tag.G2 K)) := hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg' ⊢
    rw [← hιz, ← map_mul, ← map_mul, hg']
  have hperf : Group.IsPerfect M := (CFSG.LocalCores.isQuasisimple_of_mulEquiv eM hq).1
  have hMD : M ≤ centDer (sZero (K := K)) := by
    calc M = ⁅M, M⁆ := (Subgroup.isPerfect_iff.mp hperf).symm
      _ ≤ _ := Subgroup.commutator_mono hMC hMC
  obtain ⟨E, _, _, hE, ⟨eD⟩⟩ :=
    exists_centDer_mulEquiv_statedSU hK hn hn3 (sZero_pow_three (K := K)) omFixDim_sZero
  have hcardD : Nat.card (centDer (sZero (K := K))) =
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
    rw [Nat.card_congr eD.toEquiv]
    exact CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hE
  have hpos : 0 < (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
    have h1 : 1 < (2 ^ n) ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
    have h2 : 0 < (2 ^ n) ^ 2 - 1 := by omega
    exact Nat.mul_pos (Nat.mul_pos (by positivity) h2) (by positivity)
  have : Finite (centDer (sZero (K := K))) :=
    Nat.finite_of_card_ne_zero (by rw [hcardD]; exact hpos.ne')
  have hEq : M = centDer (sZero (K := K)) :=
    Subgroup.eq_of_le_of_card_ge hMD (by rw [hcardD, ← Nat.card_congr eM.toEquiv, hcard])
  intro y hy
  rw [← hEq] at hy
  obtain ⟨g, -, rfl⟩ := hy
  exact hιθ g

end D4Inner

end CFSG.StandardType

end
