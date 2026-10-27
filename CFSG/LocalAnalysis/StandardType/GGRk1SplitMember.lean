module

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnolaLabel
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNbrRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveNbrGenKNOfInputs
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylEltOfAutomizer
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

private theorem ggRk1SplitMember_n_le_markDeg {lab : LargeEvenLabel} (h0 : LargeEvenInLambda2 lab) :
    lab.n ≤ markDeg lab := by
  obtain ⟨tg, rk, m⟩ := lab
  cases tg <;> simp only [LargeEvenInLambda2, markDeg] at h0 ⊢ <;> (try split_ifs) <;> omega

theorem ggLabelIso_n_le_markDeg {lab₀ lab : LargeEvenLabel} (h0 : LargeEvenInLambda2 lab₀)
    (h : GGLabelIso lab₀ lab) : lab.n ≤ markDeg lab₀ := by
  rcases h with rfl | ⟨htg, -, -, hn⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ |
      ⟨-, rfl⟩
  · exact ggRk1SplitMember_n_le_markDeg h0
  · rw [← hn]
    rcases htg with htg | htg <;> simp [markDeg, htg]
  all_goals first
    | (rw [h1]; simp [markDeg])
    | (simp only [markDeg]; omega)


theorem ggSplitLie_label_n_le
    {G : Type} [Group G] {X : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hadm : StatedLieAdmissible t n 2 f)
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) (hrange : ψ.range = X)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hl : GGHasLabel lab (X ⧸ Subgroup.center X)) :
    lab.n ≤ f := by
  obtain ⟨lab₀, h0, hl0, -, -, hdeg⟩ := ggSplitLie_markLabel hadm hker hrange ht
  rw [← hdeg]
  exact ggLabelIso_n_le_markDeg h0 (ggLabelRigidInput_holds lab₀ lab _ h0 hlab hl0 hl)

section Nbr


theorem ggRk1Concl_split_nbr {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) (hXs : GGSplitLie p X) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e) : GGRk1Concl p Bs X r := by
  obtain ⟨t, n, f, ψ, hadm, h3, hker, hrange, htag, hpf, hpos⟩ :=
    ggSecFiveKGPosAt_splitNbr hcfg hX hXs
  have hr : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
  obtain ⟨θ, hθinj, hθrange⟩ := s2jn_exists_sl2_of_tableBPos (ggRouteCfg_prime hcfg).1
    (ggRouteCfg_prime hcfg).2 (ggRouteCfg_isElemAbelian hcfg) (ggRouteCfg_noTransvection hcfg)
    htag hadm h3 hker hpos hrA hr
  have hr2 : r * r = 1 := by simpa [pow_two] using hr.1
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by have := hadm.2.1; omega)
  refine ⟨GaloisField 2 f, inferInstance, inferInstance, θ, inferInstance, hθinj, hθrange,
    ggExists_weylElt_of_mem_ggAutomizer hrA hr2, fun _ => by rw [hcard]; exact hpf,
    fun hns => absurd hXs hns, fun lab hlab hl => ?_⟩
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) (ggSplitLie_label_n_le hadm hker hrange htag hlab hl)

end Nbr

theorem ggRk1SplitMemberInput_holds :
    GGRk1SplitMemberInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _ ι M e hpres _ X hX hXs r hrA hrC
  exact ggRk1Concl_split_nbr hcfg hpres (hX.imp_right (hcfg.2.2.2.1.2 X)) hXs hrA hrC

end CFSG.StandardType

end
