module

public import CFSG.Timmesfeld.Bridge.OddTranspSecondKind
import CFSG.LocalAnalysis.WeakClosure81.FiveNineTwo
import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedProduct
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43
import CFSG.Assembly.QuasithinDefs
import CFSG.CGT.Timmesfeld75.Cfg214Gen
import CFSG.CGT.Timmesfeld75.L2Real
import CFSG.Foundations
import CFSG.LargeExtraspecial.S9TIXC
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
import CFSG.LocalAnalysis.WeakClosure81.FiveDefs
import CFSG.LocalAnalysis.WeakClosure81.SevenThree
import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

open CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp

theorem exists_thirdKind_of_not_isSolvable {G : Type} [Group G] [Finite G] {D : Set G}
    (hD : IsOddTransp D) (hN : IsNormalSet D) {u w v : G} (htri : IsTriangle D u w v)
    (h4 : orderOf (u * v * w) = 4)
    (hns : ¬ Group.IsSolvable (Subgroup.closure ({u, w, v} : Set G))) :
    ∃ x ∈ D, x ∈ Subgroup.closure {u, w} ∧ IsTriangle D u x v ∧ IsThirdKind u x v := by
  by_contra hcon
  have hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v := fun x hx hxX htri' hthird =>
    hcon ⟨x, hx, hxX, htri', hthird⟩
  have hS := secondKind_structure hD hN htri h4 hno
  set X := Subgroup.closure ({u, w} : Set G) with hX
  set K := Subgroup.closure ({u, w, v} : Set G) with hK
  set Q := conjClosure X (u * v) with hQ
  have hu2 : u * u = 1 := hD.mul_self_eq_one htri.1
  have hw2 : w * w = 1 := hD.mul_self_eq_one htri.2.2.1
  have huX : u ∈ X := Subgroup.subset_closure (by simp)
  have hwX : w ∈ X := Subgroup.subset_closure (by simp)
  have hXK : X ≤ K := by
    rw [hX, hK]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have huvQ : u * v ∈ Q := Subgroup.subset_closure ⟨1, X.one_mem, by simp⟩
  have hXeq : X = Subgroup.zpowers u ⊔ Subgroup.zpowers w := by
    rw [hX, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union]
    congr 1
  have hXsolv : Group.IsSolvable X := by
    rw [hXeq]
    exact CFSG.LocalAnalysis.WeakClosure81.isSolvable_sup_zpowers_of_mul_self_eq_one hu2 hw2
  have hQsolv : Group.IsSolvable Q :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hS.comm a a.2 b b.2).eq
  have hXN : X ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx q hq
    exact hS.normal x (hXK hx) q hq
  have hLsolv : Group.IsSolvable (Q ⊔ X : Subgroup G) :=
    CFSG.RankThreeEvenClassification.Helpers.normalized_sup_solvable Q X hXN hQsolv hXsolv
  have hKle : K ≤ Q ⊔ X := by
    rw [hK, Subgroup.closure_le]
    intro y hy
    rcases hy with hy | hy | hy
    · rw [hy]; exact Subgroup.mem_sup_right huX
    · rw [hy]; exact Subgroup.mem_sup_right hwX
    · rw [hy]
      have hv : v = u * (u * v) := by rw [← mul_assoc, hu2, one_mul]
      rw [hv]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right huX) (Subgroup.mem_sup_left huvQ)
  have hKeq : Q ⊔ X = K := le_antisymm (sup_le hS.le hXK) hKle
  exact hns (hKeq ▸ hLsolv)

end CFSG.OddTranspositions.PartThree.EightSix
