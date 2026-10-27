module

public import CFSG.RankThree.PartTwo.Sec4.Item413
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.LieType.Steinberg.CentralExt.SUThree
import Mathlib
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate45
public import Certificates.Certificate46
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
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item413Cases
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Back

variable {G : Type} [Group G] [Finite G]

theorem exists_le_maximal_isElemAbelian {P : Subgroup G}
    (hP : CFSG.Assembly.IsElemAbelian 3 P) :
    ∃ A : Subgroup G, P ≤ A ∧ Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A :=
  Finite.exists_le_maximal (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) hP

omit [Finite G] in
theorem exists_isElemAbelian_le_mem {P : Subgroup G} (hP : CFSG.Assembly.IsElemAbelian 3 P)
    {x : G} (hx3 : x ^ 3 = 1) (hxP : ∀ a ∈ P, a * x = x * a) :
    ∃ B : Subgroup G, P ≤ B ∧ x ∈ B ∧ CFSG.Assembly.IsElemAbelian 3 B := by
  obtain ⟨hPc, hP3⟩ := hP
  have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hPc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hxk : ∀ a ∈ P, ∀ k : ℤ, a * x ^ k = x ^ k * a := fun a ha k =>
    (Commute.zpow_right (hxP a ha) k).eq
  let B : Subgroup G :=
    { carrier := {g | ∃ a ∈ P, ∃ k : ℤ, g = a * x ^ k}
      mul_mem' := by
        rintro _ _ ⟨a, ha, k, rfl⟩ ⟨a', ha', k', rfl⟩
        refine ⟨a * a', P.mul_mem ha ha', k + k', ?_⟩
        rw [_root_.zpow_add]
        calc a * x ^ k * (a' * x ^ k') = a * (x ^ k * a') * x ^ k' := by group
          _ = a * (a' * x ^ k) * x ^ k' := by rw [hxk a' ha' k]
          _ = a * a' * (x ^ k * x ^ k') := by group
      one_mem' := ⟨1, P.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, k, rfl⟩
        refine ⟨a⁻¹, P.inv_mem ha, -k, ?_⟩
        rw [_root_.mul_inv_rev, ← _root_.zpow_neg]
        exact (hxk a⁻¹ (P.inv_mem ha) (-k)).symm }
  have hBcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g := by
    rintro _ ⟨a, ha, k, rfl⟩ _ ⟨a', ha', k', rfl⟩
    calc a * x ^ k * (a' * x ^ k') = a * (x ^ k * a') * x ^ k' := by group
      _ = a * (a' * x ^ k) * x ^ k' := by rw [hxk a' ha' k]
      _ = (a * a') * (x ^ k * x ^ k') := by group
      _ = (a' * a) * (x ^ k' * x ^ k) := by
          rw [hPcomm a ha a' ha', ← _root_.zpow_add, ← _root_.zpow_add, add_comm]
      _ = a' * (a * x ^ k') * x ^ k := by group
      _ = a' * (x ^ k' * a) * x ^ k := by rw [hxk a ha k']
      _ = a' * x ^ k' * (a * x ^ k) := by group
  have hB3 : ∀ g ∈ B, g ^ 3 = 1 := by
    rintro _ ⟨a, ha, k, rfl⟩
    rw [(Commute.zpow_right (hxP a ha) k).mul_pow, hP3 a ha, one_mul, ← zpow_natCast,
      ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx3, _root_.one_zpow]
  exact ⟨B, fun a ha => ⟨a, ha, 0, by simp⟩, ⟨1, P.one_mem, 1, by simp⟩,
    ⟨⟨⟨fun g h => Subtype.ext (hBcomm g g.2 h h.2)⟩⟩, hB3⟩⟩

end Back

end CFSG.RankThree.PartTwo.Sec4
