module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Defs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_case9_mbar_seven {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h9 : Case168_9 D V₀ V hV L) :
    padicValNat 7 (Nat.card ↥(Mbar D.M V₀ V hV)) = 3 ∧
      ∀ x ∈ Mbar D.M V₀ V hV, (∃ n : ℕ, x ^ 7 ^ n = 1) → x ^ 7 = 1 := by
  obtain ⟨e7⟩ := h9.1
  have hL3 : IsL3 ↥(lBar V₀ V hV L) 1 := h9.2.1
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let Fs : Subgroup (MulAut (Vtil V₀ V hV)) := Fstar Mb
  obtain ⟨hFX, hFn, hself⟩ := s16c167_cfg10_fstar_facts Mb
  haveI : (Fs.subgroupOf Mb).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hFX]
    intro h k hh hk
    exact hFn k hk h hh
  have hFcent : centralizer ((Fs.subgroupOf Mb : Subgroup ↥Mb) : Set ↥Mb) ≤
      (Fs.subgroupOf Mb : Subgroup ↥Mb) := by
    intro y hy
    refine Subgroup.mem_subgroupOf.mpr ?_
    refine hself (y : MulAut (Vtil V₀ V hV)) y.2 ?_
    intro f hf
    have hcomm := (Subgroup.mem_centralizer_iff.mp hy) (⟨f, hFX hf⟩ : ↥Mb)
      (Subgroup.mem_subgroupOf.mpr hf)
    exact (congrArg Subtype.val hcomm).symm
  haveI : Finite ↥Mb := Subtype.finite
  haveI : Finite ↥(lBar V₀ V hV L) := Subtype.finite
  have hcount := s1611e3_c9_seven_count hFcent hL3
    ((Subgroup.subgroupOfEquivOfLe hFX).trans e7)
  refine ⟨?_, ?_⟩
  · show padicValNat 7 (Nat.card ↥Mb) = 3
    exact hcount.1
  · intro x hx hxpow
    obtain ⟨n, hn⟩ := hxpow
    have hn' : (⟨x, hx⟩ : ↥Mb) ^ 7 ^ n = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow] using hn
    have h7 := hcount.2 ⟨x, hx⟩ ⟨n, hn'⟩
    simpa [Subgroup.coe_pow] using congrArg Subtype.val h7

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
