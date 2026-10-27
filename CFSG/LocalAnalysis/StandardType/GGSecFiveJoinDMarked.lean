module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEData
public import CFSG.LocalAnalysis.StandardType.PhanDLift
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRest
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinHCRowDefs
public import CFSG.ClassicalInvolution.Phan.PhanDn.MainA
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanSystem
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
public import CFSG.RankThree.PartOne.CTP.ExtPhan

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Phan.PhanE

section StdFamily

open CFSG.ClassicalInvolution.PhanDn

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} [Algebra (GaloisField 2 f) K]

@[expose] noncomputable def stdFamilyDPlus (hF : Nat.card (GaloisField 2 f) = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (m : ℕ) (hm : 3 ≤ m) (he : Even (m + 1)) :
    PhanFamilyE K 2 f (ggCoxeterMatrixD (m + 1)) (ggU .POmegaPlus (m + 1) f).K :=
  (stdFamilyΩ (quadExt_of_card_of_char_two f hF hK) m hm hK hq).map
    (omegaEquivLieUniversalPlus (quadExt_of_card_of_char_two f hF hK) he (by omega)).toMonoidHom

theorem stdFamilyDPlus_isUniversal (hF : Nat.card (GaloisField 2 f) = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (m : ℕ) (hm : 3 ≤ m) (he : Even (m + 1)) :
    (stdFamilyDPlus hF hK hq m hm he).IsUniversal :=
  (isUniversal_stdFamilyΩ_of_dChamberSystem _ hm hK hq (stdFamilyΩ_good _ m hm hK hq)
    (dChamberSystemConnected_holds K f hK hq m hm)
    (dChamberSystemSimplyTwoConnected_holds K f hK hq m hm)).map _

end StdFamily

theorem exists_markedPres_of_phanD_system {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hJ : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) {ι : Type} {M : CoxeterMatrix ι} {m : ℕ}
    (hm : 4 ≤ m) (σ : Fin m ≃ ι) (hM : M = (ggCoxeterMatrixD m).reindex σ) {f : ℕ}
    (hq : 4 ≤ 2 ^ f) (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
    (S : ι → Subgroup G) (hiso : ∀ i, Nonempty (Su F 2 f 2 ≃* S i))
    (hcomm : ∀ i j, i ≠ j → M.M i j = 2 → ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a)
    (hpair : ∀ i j, M.M i j = 3 → ∃ W : Subgroup G, UnitaryBlockStandardPair F 2 f W (S i) (S j))
    (hgen : ⨆ i, S i = L ⊔ ⨆ K ∈ 𝒦, K) {t : StatedLieTag}
    (ht : t = .POmegaPlus ∧ Even m ∨ t = .POmegaMinus ∧ Odd m)
    (T : PhanFamilyE F 2 f (ggCoxeterMatrixD m) (ggU t m f).K) (hT : T.IsUniversal) :
    ∃ ψ₀ : (ggU t m f).K →* G, GGPresentsG0 (ggG0 p B x L D J) (ggU t m f).D t m f ψ₀ ∧
      ∀ k, (T.ι k).range.map ψ₀ = S (σ k) := by
  set H : Subgroup G := L ⊔ ⨆ K ∈ 𝒦, K with hH
  have hSH : ∀ i, S i ≤ H := fun i => hgen ▸ le_iSup S i
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h; norm_num at hq
    · exact h
  have hsys := ggWeakPhanSL_subgroupOf σ hM hq F hF S hiso hcomm hpair hgen
  obtain ⟨Φ, hΦ, hΦinj⟩ := CFSG.ClassicalInvolution.PhanDn.exists_phanFamilyE hm hF hsys
  have hΦgen : (⨆ k, (Φ.ι k).range) = ⊤ := by simpa only [hΦ] using hsys.gen
  have hY : CFSG.IsQuasisimple (ggU t m f).K := by
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact CFSG.ClassicalInvolution.PhanDn.isQuasisimple_lieUniversal_POmegaPlus hm
    · exact CFSG.ClassicalInvolution.PhanDn.isQuasisimple_lieUniversal_POmegaMinus hm
  obtain ⟨θ, hθ, hker, hθι, -⟩ := hT.exists_central_epimorphism hF (by omega) hY Φ hΦinj hΦgen
  have hadm : StatedLieAdmissible t m 2 f := by
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨Nat.prime_two, hf, hm⟩
    · exact ⟨Nat.prime_two, hf, hm⟩
  have hrk : 2 ≤ (ggU t m f).D.rank := by
    have h3 : 3 ≤ bnRank t m := by
      rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp only [bnRank] <;> omega
    rw [show (ggU t m f).D.rank = bnRank t m from
      lieUniversal_rank_eq_bnRank t m 2 f Nat.prime_two hadm h3]
    omega
  set ψ₀ : (ggU t m f).K →* G := H.subtype.comp θ with hψ₀
  have hrange : ψ₀.range = ggG0 p B x L D J := by
    rw [hψ₀, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hθ, Subgroup.map_top,
      Subgroup.range_subtype, hJ]
  have hker₀ : ψ₀.ker ≤ Subgroup.center (ggU t m f).K := by
    rw [hψ₀, MonoidHom.ker_comp_of_injective θ H.subtype H.subtype_injective]
    exact hker
  have : Group.IsPerfect (ggU t m f).K := ⟨(ggU_perfect_lieModel hadm hrk).1⟩
  have hperf : commutator ↥ψ₀.range = ⊤ := by
    have := Group.IsPerfect.range ψ₀
    exact Group.IsPerfect.commutator_eq_top
  have hmodel := lieModel_range_centerQuot hadm hrk ψ₀ hker₀
  refine ⟨ψ₀, ⟨⟨hadm, hrk⟩, ⟨hrange, hker₀⟩, hrange ▸ hperf, hrange ▸ hmodel⟩, fun k => ?_⟩
  rw [hψ₀, ← Subgroup.map_map, ← MonoidHom.range_comp, hθι k, hΦ k]
  exact Subgroup.subgroupOf_map_subtype _ _ |>.trans (inf_eq_left.mpr (hSH _))

theorem ggSecFiveJoinD_markedPres (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput) (hL2 : GGSecFiveL2PhanInput)
    (hPair : GGSecFivePhanPairInput) (hNbr : GGSecFiveNonSplitNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {m : ℕ} (hm : 4 ≤ m)
    (σ : Fin m ≃ ι) (hM : M = (ggCoxeterMatrixD m).reindex σ)
    (hSix : ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e) (hJ : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) :
    ∃ f : ℕ, 4 ≤ 2 ^ f ∧ p ∣ 2 ^ f + 1 ∧
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = (2 ^ f) ^ 2 →
      ∀ t : StatedLieTag, (t = .POmegaPlus ∧ Even m ∨ t = .POmegaMinus ∧ Odd m) →
      ∀ T : PhanFamilyE F 2 f (ggCoxeterMatrixD m) (ggU t m f).K, T.IsUniversal →
        ∃ ψ₀ : (ggU t m f).K →* G, GGPresentsG0 (ggG0 p B x L D J) (ggU t m f).D t m f ψ₀ ∧
          ∀ k, (T.ι k).range.map ψ₀ =
            ggRankOnePerf Bs ((e (M.simple (σ k)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
  have hs : ¬ GGSplitLie p L := fun hs =>
    hReg ⟨𝒦, hcfg, hs, ι, M, e, hpres, Or.inl (Or.inr ⟨m, σ, hm, hM⟩)⟩
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := fun i j hij =>
    GGIsWeylMatrixAD.le_three (Or.inr ⟨m, σ, hm, hM⟩) i j hij
  have hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6 :=
    fun r hrA hrC h => hSix ⟨hpres, Or.inr (Or.inl ⟨m, σ, hm, hM⟩), r, hrA, hrC, h⟩
  obtain ⟨f, hf4, hpf, hsys⟩ :=
    ggSecFivePhanSystem_of_prim hL1 hRk1 hGen hOrb hL2 hPair hNbr hcfg hs hpres hle3 hbig
  refine ⟨f, hf4, hpf, fun F _ _ _ hF t ht T hT => ?_⟩
  obtain ⟨hiso, hcomm, hpair, hgen⟩ := hsys F hF
  exact exists_markedPres_of_phanD_system hJ hm σ hM hf4 F hF _ hiso hcomm hpair hgen ht T hT

end CFSG.StandardType
