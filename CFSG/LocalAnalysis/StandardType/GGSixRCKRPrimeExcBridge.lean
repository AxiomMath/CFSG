module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcDefs
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHolds
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped commutatorElement
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

theorem rckBridgeFrame_exists
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X} (ht : GGExcFive t)
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e) :
    ∃ (θ : ↥G₀ →* ModGL (langTag t) GGL) (A' : Subgroup (ModGL (langTag t) GGL)),
      RCKBridgeFrame t f p G₀ A θ A' := by
  unfold RCKRPConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6, hRJ, hRmJ, hRootJ, heD, he1, hKcomp, hJK, hOddK⟩
  have hadm : StatedLieAdmissible t n 2 f := hGG.1.1
  have hker : ψ.ker ≤ Subgroup.center (ggU t n f).K := hGG.2.1.2
  have hrange : ψ.range = G₀ := hGG.2.1.1
  have hMp := ggInnerDiagMpInput_holds X t n f ψ hadm hGG.1.2 hker G₀ hrange _ hMarkG0
  have hdiag : ∀ b ∈ A, GGPsiInnerDiag (ggU t n f).D ψ b := by
    have hc := largeEvenMarking_mono
      (P' := fun _ _ _ _ _ _ => ∀ b ∈ A, GGPsiInnerDiag (ggU t n f).D ψ b)
      (fun _ _ _ _ _ _ hPQ b hb => hPQ.2 b (hAnorm hb) (hPQ.1 b hb)) hMp
    exact largeEvenMarking_elim_const hc
  have hHyp : GGLieBridgeHyp t n f p ψ G₀ A :=
    ⟨hrange, hker, hGG.2.2.2, hAnorm, hdiag, hAel, hAc⟩
  obtain ⟨θ, A', hθker, hθrange, hA'le, hA'el, hA'card, h1, h2, -⟩ :=
    ggLieBridge_holds p t n f ψ G₀ A J hp hp2 ht hadm.2.1 hHyp
  exact ⟨θ, A', hθker, hθrange, hA'le, hA'el, hA'card, h1, h2⟩

theorem rckBridgeFrame_eq_map_of_le
    {t : StatedLieTag} {f p : ℕ} {X : Type} [Group X]
    {G₀ A : Subgroup X} {θ : ↥G₀ →* ModGL (langTag t) GGL}
    {A' : Subgroup (ModGL (langTag t) GGL)}
    (hFrame : RCKBridgeFrame t f p G₀ A θ A') (hAG : A ≤ G₀)
    (hcent : ∀ z ∈ ggFixGp t f, (∀ x : ↥G₀, z * θ x = θ x * z) → z = 1) :
    A' = (A.subgroupOf G₀).map θ := by
  obtain ⟨-, hrange, hA'le, -, -, hfwd, hbwd⟩ := hFrame
  ext y
  constructor
  · intro hy
    obtain ⟨d, hdA, hdpart⟩ := hbwd y hy
    have hdG₀ : d ∈ G₀ := hAG hdA
    have hdN : d ∈ Subgroup.normalizer (G₀ : Set X) := G₀.le_normalizer hdG₀
    have hθΦ : θ ⟨d, hdG₀⟩ ∈ ggFixGp t f := by
      have hmem : θ ⟨d, hdG₀⟩ ∈ θ.range := MonoidHom.mem_range.2 ⟨⟨d, hdG₀⟩, rfl⟩
      rw [hrange] at hmem
      exact Subgroup.commutator_le_self (ggFixGp t f) hmem
    have huniq := GGLiePartner.unique hcent hdN (hA'le hy) hθΦ hdpart
      (GGLiePartner.of_mem ⟨d, hdG₀⟩)
    rw [huniq]
    exact Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.mpr hdA)
  · intro hy
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy
    have hdA : (d : X) ∈ A := Subgroup.mem_subgroupOf.mp hd
    obtain ⟨a, haA', hpart⟩ := hfwd (d : X) hdA
    have hdN : (d : X) ∈ Subgroup.normalizer (G₀ : Set X) := G₀.le_normalizer d.2
    have hθΦ : θ d ∈ ggFixGp t f := by
      have hmem : θ d ∈ θ.range := MonoidHom.mem_range.2 ⟨d, rfl⟩
      rw [hrange] at hmem
      exact Subgroup.commutator_le_self (ggFixGp t f) hmem
    have huniq := GGLiePartner.unique hcent hdN (hA'le haA') hθΦ hpart
      (GGLiePartner.of_mem d)
    rw [← huniq]
    exact haA'

theorem rckBridgeFrame_eq_map_of_presentation
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A : Subgroup X}
    (ht : GGExcFive t) (hGG : GGPresentsG0 G₀ (ggU t n f).D t n f ψ)
    {θ : ↥G₀ →* ModGL (langTag t) GGL} {A' : Subgroup (ModGL (langTag t) GGL)}
    (hFrame : RCKBridgeFrame t f p G₀ A θ A') (hAG : A ≤ G₀) :
    A' = (A.subgroupOf G₀).map θ := by
  have hf : 1 ≤ f := hGG.1.1.2.1
  obtain ⟨θ₀, -, -, hθ₀range, hθ₀cent⟩ := ggLieBridge_theta ht hf hGG
  have hcent : ∀ z ∈ ggFixGp t f, (∀ x : ↥G₀, z * θ x = θ x * z) → z = 1 := by
    intro z hz hc
    refine hθ₀cent z hz (fun x => ?_)
    have hx : θ₀ x ∈ θ.range := by
      rw [hFrame.2.1, ← hθ₀range]
      exact MonoidHom.mem_range.2 ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hx
    rw [← hy]
    exact hc y
  exact rckBridgeFrame_eq_map_of_le hFrame hAG hcent

end CFSG.StandardType.RCKRP
