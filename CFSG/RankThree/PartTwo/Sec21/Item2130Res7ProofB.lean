module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofAssembly
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res7ProofUnitary
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res7ProofL

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly (IsElemAbelian)

open CFSG.Assembly.RankThreeEven (projImage)

open Matrix (ProjGenLinGroup)

open Item211Proof Item211Res2Proof Item2130Res5Proof Item2130Res6Proof Item2130Res7Proof

section LThreeCerts

theorem item2130CaseBEven_holds : Item2130CaseBEven := by
  intro G _ _ A E U c L b U₀ Y hcfg h9 hC hAY _ _ _ hTC hcY _ _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hA : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hbA : b ∈ A := hC.b_mem.1
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))
  have hAL : A ≤ Subgroup.normalizer (Y : Set G) := hC.three_norm A hA hAC
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hqY : IsQuasisimple (lBar Y) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have : Group.IsPerfect (lBar Y) := hqY.1
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hcA : c ∈ A := hcfg.pair.mem_E.2 hpairs.1.1
  rcases hTC with hTC' | hTC'
  ·
    obtain ⟨π, p, f, K, _, hK, hq, e, D, hD, hAD', hDA'⟩ := hTC'
    have hq2 := two_lt_of_projImage hK hq hqY e
    have hAD : ∀ x ∈ A, ∃ y ∈ D,
        ActsVia Y ((projImage (slPi π 3 (p ^ f) K)).subtype.comp e.toMonoidHom) x y :=
      fun x hx => by
        obtain ⟨y, hy, hyz⟩ := hAD' _ (mem_autThetaQuot_iff.mpr ⟨x, hAL hx, hx, rfl⟩)
        exact ⟨y, hy, hAL hx, hyz⟩
    obtain ⟨yc, hycD, hycz⟩ := hAD' _ (mem_autThetaQuot_iff.mpr ⟨c, hAL hcA, hcA, rfl⟩)
    cases π
    · exact false_of_typeC_model_unitary hcfg hC (isBarModel_projImage hK hq hq2 e)
        (odd_oThreePrime_of_projImage hK hq2 e) hD hAD hycD ⟨hAL hcA, hycz⟩
    · refine false_of_typeC_model hcfg hC (isBarModel_projImage hK hq hq2 e)
        (odd_oThreePrime_of_projImage hK hq2 e) hD hAD hycD ⟨hAL hcA, hycz⟩ fun h2t h20 => ?_
      exact false_of_typeC_l hcfg h9 hC hcY hK hq h20 e hD hAD' hDA' hycD hycz h2t
  ·
    obtain ⟨π, p, f, K, _, hK, hq, e, D, hD, hAD', -⟩ := hTC'
    have hq2 := two_lt_of_slPi hK hq hqY e
    have hmk : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (Y : Set G)) (y : GL (Fin 3) K),
        (∀ z : lBar Y, ((e (thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨x, hx⟩) z) :
          slPi π 3 (p ^ f) K) : GL (Fin 3) K) = y * (e z : GL (Fin 3) K) * y⁻¹) →
        ActsVia Y ((ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).comp
          ((slPi π 3 (p ^ f) K).subtype.comp e.toMonoidHom)) x y := fun x hx y hxy =>
      ⟨hx, fun z => by
        change ProjGenLinGroup.mk ((e (thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨x, hx⟩) z) :
            slPi π 3 (p ^ f) K) : GL (Fin 3) K) = ProjGenLinGroup.mk y *
          ProjGenLinGroup.mk ((e z : slPi π 3 (p ^ f) K) : GL (Fin 3) K) *
            (ProjGenLinGroup.mk y)⁻¹
        rw [hxy z, map_mul, map_mul, map_inv]⟩
    have hAD : ∀ x ∈ A, ∃ y ∈ D, ActsVia Y ((ProjGenLinGroup.mk : GL (Fin 3) K →*
        ProjGenLinGroup (Fin 3) K).comp ((slPi π 3 (p ^ f) K).subtype.comp e.toMonoidHom)) x y :=
      fun x hx => by
        obtain ⟨y, hy, hyz⟩ := hAD' _ (mem_autThetaQuot_iff.mpr ⟨x, hAL hx, hx, rfl⟩)
        exact ⟨y, hy, hmk x (hAL hx) y hyz⟩
    obtain ⟨yc, hycD, hycz⟩ := hAD' _ (mem_autThetaQuot_iff.mpr ⟨c, hAL hcA, hcA, rfl⟩)
    cases π
    · exact false_of_typeC_model_unitary hcfg hC (isBarModel_slPi hK hq hq2 e)
        (odd_oThreePrime_of_slPi hK hq2 e) hD hAD hycD (hmk c (hAL hcA) yc hycz)
    · refine false_of_typeC_model hcfg hC (isBarModel_slPi hK hq hq2 e)
        (odd_oThreePrime_of_slPi hK hq2 e) hD hAD hycD (hmk c (hAL hcA) yc hycz)
        fun h2t _ => ?_
      exact false_of_typeC_sl hcfg hC hcY hK hq e hD hAD' hycD hycz h2t

theorem item2130TypesLThree_of_res7 (h41 : Sec4.Item4_1LargePrime) : Item2130TypesLThree :=
  item2130TypesLThree_of_res6 h41 item2130CaseBEven_holds

end LThreeCerts

end CFSG.RankThree.PartTwo.Sec21
