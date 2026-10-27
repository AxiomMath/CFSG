module

public import Certificates.Certificate43
public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.Timmesfeld.Bridge.Asc72WreathDefs
import CFSG.Timmesfeld.Bridge.Asc72Minimal
import CFSG.Timmesfeld.Bridge.Asc72WreathStruct
import CFSG.OddTranspositions.WreathBase
import CFSG.OddTranspositions.WreathBaseMinimal
import CFSG.OddTranspositions.MinimalNormalTransport
import CFSG.OddTranspositions.PartThree.EightSix.WreathCount
import CFSG.OddTranspositions.PartThree.EightSix.WreathOrder
import CFSG.OddTranspositions.PartThree.EightSix.TriangleThree
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
import CFSG.Timmesfeld.Bridge.Asc72Lift

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

theorem isSolvable_of_l2Wreath_of_triangle {X : Type} [Group X]
    [Finite X] {D : Set X} (hS : Setup X D)
    (hrad : ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥) {f n : ℕ} (hf : 2 ≤ f)
    (hn : n = 3 ∨ n = 4) (e : X ≃* L2Wreath f n) {u w v : X} (htri : IsTriangle D u w v)
    (hgen : Subgroup.closure ({u, w, v} : Set X) = ⊤) : Group.IsSolvable X := by
  have hn2 : 2 ≤ n := by omega
  have hbase : Asc72.IsMinimalNormal (l2WreathBase f n) := base_isMinimalNormal f n hf hn2
  have hM : Asc72.IsMinimalNormal ((l2WreathBase f n).comap e.toMonoidHom) :=
    CFSG.OddTranspositions.IsMinimalNormal.comap_mulEquiv e hbase
  have hMs : ¬ IsSimpleGroup ((l2WreathBase f n).comap e.toMonoidHom) :=
    not_isSimpleGroup_comap_mulEquiv e (l2WreathBase_not_isSimpleGroup hf hn2)
  obtain ⟨W⟩ := nonempty_wreathData hS hrad hM hMs
  have hC : Subgroup.centralizer
      (((l2WreathBase f n).comap e.toMonoidHom : Subgroup X) : Set X) = ⊥ :=
    centralizer_eq_bot_of_minimal hS hrad hM
  have hr : 2 < W.r := two_lt_r_of_l2Wreath hS hf hn e W
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one htri.1
  have hw2 : w * w = 1 := hS.oddT.mul_self_eq_one htri.2.2.1
  have hv2 : v * v = 1 := hS.oddT.mul_self_eq_one htri.2.1
  have huv : Commute u v := htri.2.2.2.2.1
  obtain ⟨i, j, k, hij, hjk, hik, hπu, hπw⟩ :=
    exists_swap_swap_of_closure_eq_top W hr htri.1 htri.2.2.1 htri.2.1 huv hgen
  have huw : orderOf (u * w) = 3 :=
    orderOf_mul_eq_three_of_wreathData W hC htri.1 htri.2.2.1 hu2 hw2 hij hjk hik hπu hπw
  have hgen' : Subgroup.closure ({v, w, u} : Set X) = ⊤ := by
    rw [show ({v, w, u} : Set X) = {u, w, v} by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto]
    exact hgen
  obtain ⟨i', j', k', hi'j', hj'k', hi'k', hπv, hπw'⟩ :=
    exists_swap_swap_of_closure_eq_top W hr htri.2.1 htri.2.2.1 htri.1 (huv.symm) hgen'
  have hvw : orderOf (v * w) = 3 :=
    orderOf_mul_eq_three_of_wreathData W hC htri.2.1 htri.2.2.1 hv2 hw2 hi'j' hj'k' hi'k'
      hπv hπw'
  exact isSolvable_of_orderOf_mul_eq_three hu2 hw2 hv2 huv huw hvw hgen

end CFSG.OddTranspositions.PartThree.EightSix
