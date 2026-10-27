module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTransport
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapter
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosFinal
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSExcl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEsu
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

@[expose] def GGSecFiveNSLieAInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
        (∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X →
          ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (f n : ℕ) (ψ : Su K 2 f n →* G),
            Nat.card K = (2 ^ f) ^ 2 ∧ 4 ≤ n ∧ ψ.ker ≤ Subgroup.center (Su K 2 f n) ∧ ψ.range = X ∧
              p ∣ 2 ^ f + 1 ∧ GGActsUnitarily (p := 2) (f := f) ψ Bs ∧
              ∃ b : ℕ, n = b + 1 ∧ GGHasLabel ⟨.twA, b, f⟩ (↥X ⧸ Subgroup.center ↥X)

theorem ggSecFiveNSKGPosAInput_of_nsLieA
    (hC : GGSecFiveNSCornerInput) (hLie : GGSecFiveNSLieAInput) : GGSecFiveNSKGPosAInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL ι M e hpres hA hbig X hX hXns
  obtain ⟨K, hKf, hKfin, hKchar, f, n, ψ, hcard, hn, hker, hrange, hdvd, hacts, hlabel⟩ :=
    hLie G p B Bs x L D J 𝒦 hcfg hL ι M e hpres hA hbig X hX hXns
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  have h : GGNSLocalHyp p B Bs K f n ψ :=
    ggNSLocalHyp_of_routeCfg hcfg hX hcard hn hker hrange hdvd hacts
  obtain ⟨c, hc⟩ := ggNSLocal_position hC h
  have hr : (ψ.comp (MulAut.conj c).toMonoidHom).range = X := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective, Subgroup.map_top, hrange]
  refine ⟨K, hKf, hKfin, hKchar, f, n, ψ.comp (MulAut.conj c).toMonoidHom, hcard, hn,
    (h.comp_conj c).ker, hr, hdvd, ?_, hlabel⟩
  rw [← hrange] at hr
  have hc' := hc
  rwa [hrange] at hc'

section Nbr


theorem ggInnerDiagUnitary_of_ennola_q2_nbr
    (hEn : GGSecFiveNSEnnolaInput) (hQ2 : GGSecFiveNSQ2Input) (hFix : GGTBFixInput)
    (hWA : GGTBFixNbrXInput) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hL : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hA : ∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    {X : Subgroup G}
    (hX : X = L ∨ ((∃ y : G, GGNbr p B x D J y X) ∧ ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦))
    (hXns : ¬ GGSplitLie p X) :
    GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)))
      p Bs X := by
  have hE := ggX_esu_of_nonSplit hEn hcfg hL hpres hA hX hXns
  have hQ := hQ2 hFix hWA hLB hSP G p B Bs x L D J 𝒦 hcfg hL ι M e hpres hA hbig X hX hXns
  have h' : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) ∨
      (ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)))) p Bs X :=
    hE.mono' fun lab hl => (em (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))).imp
      (fun h3 => ⟨hl, h3⟩) (fun h3 => ⟨hl, h3⟩)
  rcases GGInnerDiagOnLabel.elim_or h' with h | h
  · exact absurd h hQ
  · exact h

end Nbr

theorem ggSecFiveNSLieAInput_of_ennola_q2
    (hEn : GGSecFiveNSEnnolaInput) (hQ2 : GGSecFiveNSQ2Input) (hFix : GGTBFixInput)
    (hWA : GGTBFixNbrXInput) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) :
    GGSecFiveNSLieAInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL ι M e hpres hA hbig X hX hXns
  exact ggNSLie_cover_of_esu (ggInnerDiagUnitary_of_ennola_q2_nbr hEn hQ2 hFix hWA hLB hSP hcfg hL hpres hA
    hbig (ggSecFive_weakMember_of_sel hcfg hX) hXns)

end CFSG.StandardType

end
