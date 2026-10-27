module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsIdx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HeGen
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.A312Words

open CFSG.QuasithinUnique.Ch1.SporLat

variable {Γ : Type} [Group Γ]

theorem card_quot_le_one {Y : Subgroup Γ} {ol : List Γ} {t : Γ} (h : IdxTwoData Y ol t)
    (ht1 : t = 1) (N : Subgroup ↥Y) [N.Normal] (hp : IsPGroup 2 (↥Y ⧸ N)) :
    Nat.card (↥Y ⧸ N) ≤ 1 := by
  classical
  let Nγ : Subgroup Γ := N.map Y.subtype
  have hmem : ∀ g ∈ ol ++ [t], g ∈ Nγ := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨m, hm, hgm⟩ := h.odd g hg
      refine ⟨⟨g, h.mem g hg⟩, ?_, rfl⟩
      exact mem_of_pow_eq_one_odd N hp hm (Subtype.ext (by simpa using hgm))
    · have : g = t := by simpa using hg
      rw [this, ht1]
      exact Nγ.one_mem
  have hYN : Y ≤ Nγ := h.gen.trans ((Subgroup.closure_le Nγ).mpr hmem)
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, hz, hzy⟩ := hYN y.2
    have : z = y := Subtype.ext hzy
    rwa [← this]
  rw [hNtop]
  simp

variable [Finite Γ]

theorem pCore_eq_subgroupOf {Y W : Subgroup Γ} (hWY : W ≤ Y)
    (hnorm : ∀ y ∈ Y, ∀ w ∈ W, y⁻¹ * w * y ∈ W) {k : ℕ} (hW : Nat.card W = 2 ^ k)
    (hP : Nat.card (CFSG.pCore 2 ↥Y) = 2 ^ k) : CFSG.pCore 2 ↥Y = W.subgroupOf Y := by
  have hWn : (W.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hWY]
    intro w y hw hy
    simpa using hnorm y⁻¹ (Y.inv_mem hy) w hw
  have hcard : Nat.card (W.subgroupOf Y) = 2 ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWY).toEquiv]; exact hW
  have hW2 : IsPGroup 2 (W.subgroupOf Y) := IsPGroup.of_card hcard
  have hle : W.subgroupOf Y ≤ CFSG.pCore 2 ↥Y := le_sSup ⟨hWn, hW2⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hP, hcard])).symm

end CFSG.Quasithin.A312Words
