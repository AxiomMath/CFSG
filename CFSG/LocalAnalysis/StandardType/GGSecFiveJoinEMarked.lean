module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinCells
public import CFSG.LocalAnalysis.StandardType.GGPhanMarkedRecognition
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEData
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanSystem
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
import CFSG.Milestones.CL_LIT_Curtis_Tits_presentation_theorem

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.PhanE

section Universal

theorem ggPresentsG0_of_surjective {G : Type} [Group G] {G₀ H : Subgroup G} (hG₀ : G₀ = H)
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hrk : 2 ≤ (ggU t n f).D.rank) (hQ : IsQuasisimple (ggU t n f).K)
    (hmodel : LieModel ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) t n 2 f)
    (θ : (ggU t n f).K →* ↥H) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (ggU t n f).K) :
    GGPresentsG0 G₀ (ggU t n f).D t n f (H.subtype.comp θ) := by
  subst hG₀
  refine ⟨⟨hadm, hrk⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hθ, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [MonoidHom.ker_comp_of_injective θ G₀.subtype G₀.subtype_injective]
    exact hker
  · have h1 : (commutator (ggU t n f).K).map θ = commutator ↥G₀ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.2 hθ, commutator_def]
    rw [← h1, hQ.1.commutator_eq_top, Subgroup.map_top, MonoidHom.range_eq_top.2 hθ]
  · exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hQ hθ hker) hmodel

section Cell

theorem ggSecFiveJoinE_markedTop
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput) (hGen : GGSecFiveGenPhanInput)
    (hOrb : GGSecFiveOrbPhanInput) (hL2 : GGSecFiveL2PhanInput) (hPair : GGSecFivePhanPairInput)
    (hNbr : GGSecFiveNonSplitNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (hSix : ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e)
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) :
    ∃ (f : ℕ) (hq : 4 ≤ 2 ^ f), p ∣ 2 ^ f + 1 ∧
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2),
        (∃ σ : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex σ ∧
          ∃ ψ₀ : (ggU .twistedE6 0 f).K →* G,
            GGPresentsG0 (ggG0 p B x L D J) (ggU .twistedE6 0 f).D .twistedE6 0 f ψ₀ ∧
            ∀ k, ((e6StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.ι k).range.map ψ₀ =
              ggRankOnePerf Bs ((e (M.simple (σ k)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) ∨
        (∃ σ : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex σ ∧
          ∃ ψ₀ : (ggU .E7 0 f).K →* G,
            GGPresentsG0 (ggG0 p B x L D J) (ggU .E7 0 f).D .E7 0 f ψ₀ ∧
            ∀ k, ((e7StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.ι k).range.map ψ₀ =
              ggRankOnePerf Bs ((e (M.simple (σ k)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) ∨
        (∃ σ : Fin 8 ≃ ι, M = CoxeterMatrix.E₈.reindex σ ∧
          ∃ ψ₀ : (ggU .E8 0 f).K →* G,
            GGPresentsG0 (ggG0 p B x L D J) (ggU .E8 0 f).D .E8 0 f ψ₀ ∧
            ∀ k, ((e8StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.ι k).range.map ψ₀ =
              ggRankOnePerf Bs ((e (M.simple (σ k)) : ↥(ggAutomizerJoin L Bs 𝒦)) :
                MulAut ↥Bs)) := by
  have hns : ¬ GGSplitLie p L := fun hs => hReg ⟨𝒦, hcfg, hs, ι, M, e, hpres, Or.inr hE⟩
  have hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6 :=
    fun r hr hrR h6 => hSix ⟨hpres, Or.inr (Or.inr hE), r, hr, hrR, h6⟩
  obtain ⟨f, hf4, hpf, hsys⟩ := ggSecFivePhanSystem_of_prim hL1 hRk1 hGen hOrb hL2 hPair hNbr
    hcfg hns hpres (fun i j hij => GGIsWeylMatrixE.le_three hE i j hij) hbig
  refine ⟨f, hf4, hpf, fun F _ _ _ hF => ?_⟩
  obtain ⟨hiso, hcomm, hpair, hgen⟩ := hsys F hF
  have hf : 1 ≤ f := one_le_of_four_le_two_pow hf4
  have hnode : ∀ {Y : Type} [Group Y] (θ : Y →* ↥(L ⊔ ⨆ K ∈ 𝒦, K)) (N : Subgroup Y) (i : ι),
      N.map θ = (ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) :
        MulAut ↥Bs)).subgroupOf (L ⊔ ⨆ K ∈ 𝒦, K) →
      N.map ((L ⊔ ⨆ K ∈ 𝒦, K).subtype.comp θ) =
        ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
    intro Y _ θ N i h
    rw [← Subgroup.map_map, h, Subgroup.subgroupOf_map_subtype, inf_eq_left]
    rw [← hgen]
    exact le_iSup (fun i => ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) :
      MulAut ↥Bs)) i
  rcases hE with ⟨σ, hM⟩ | ⟨σ, hM⟩ | ⟨σ, hM⟩
  · have hadm : StatedLieAdmissible .twistedE6 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
    obtain ⟨θ, hθ, hker, hθn, -⟩ := PhanEInput2.exists_marked_epimorphism_E6 hF hf4 _ _
      (ggWeakPhanSL_subgroupOf σ hM hf4 F hF _ hiso hcomm hpair hgen)
    obtain ⟨⟨-, hQ, hmodel⟩, -⟩ :=
      CFSG.Milestones.cl_lit_curtis_tits_presentation_theorem.{0} .twistedE6 0 2 f hadm
        (by decide)
    exact Or.inl ⟨σ, hM, _, ggPresentsG0_of_surjective hJoin hadm
      (two_le_lieUniversal_rank _ 0 2 f Nat.prime_two hadm (by decide)) hQ hmodel θ hθ hker,
      fun k => hnode θ _ (σ k) (hθn k)⟩
  · have hadm : StatedLieAdmissible .E7 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
    obtain ⟨θ, hθ, hker, hθn, -⟩ := PhanEInput2.exists_marked_epimorphism_E7 hF hf4 _ _
      (ggWeakPhanSL_subgroupOf σ hM hf4 F hF _ hiso hcomm hpair hgen)
    obtain ⟨⟨-, hQ, hmodel⟩, -⟩ :=
      CFSG.Milestones.cl_lit_curtis_tits_presentation_theorem.{0} .E7 0 2 f hadm (by decide)
    exact Or.inr (Or.inl ⟨σ, hM, _, ggPresentsG0_of_surjective hJoin hadm
      (two_le_lieUniversal_rank _ 0 2 f Nat.prime_two hadm (by decide)) hQ hmodel θ hθ hker,
      fun k => hnode θ _ (σ k) (hθn k)⟩)
  · have hadm : StatedLieAdmissible .E8 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
    obtain ⟨θ, hθ, hker, hθn, -⟩ := PhanEInput2.exists_marked_epimorphism_E8 hF hf4 _ _
      (ggWeakPhanSL_subgroupOf σ hM hf4 F hF _ hiso hcomm hpair hgen)
    obtain ⟨⟨-, hQ, hmodel⟩, -⟩ :=
      CFSG.Milestones.cl_lit_curtis_tits_presentation_theorem.{0} .E8 0 2 f hadm (by decide)
    exact Or.inr (Or.inr ⟨σ, hM, _, ggPresentsG0_of_surjective hJoin hadm
      (two_le_lieUniversal_rank _ 0 2 f Nat.prime_two hadm (by decide)) hQ hmodel θ hθ hker,
      fun k => hnode θ _ (σ k) (hθn k)⟩)

end Cell

end Universal

end CFSG.StandardType

end
