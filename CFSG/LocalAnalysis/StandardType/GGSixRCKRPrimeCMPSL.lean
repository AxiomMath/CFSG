module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMAt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMLiftsPSL
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3EquivPSL
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSL
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDConversePSL

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckClassicalCompModelAt_PSL :
    RCKClassicalCompModelAt .PSL := by
  intro X _ _ n f ψ p G₀ A B₁ D J L K e h hKJ hID
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    have hn : 2 ≤ n := h.1.1.1.2.2.1
    exact ⟨n - 1, by omega⟩
  have hcfg : RCKCompConfig .PSL (m + 1) f ψ p G₀ A B₁ D J L K e := h
  have hf : 1 ≤ f := h.1.1.1.2.1
  have hrange : ψ.range = G₀ := h.1.2.1.1
  have hker : ψ.ker ≤ Subgroup.center (ggU .PSL (m + 1) f).K := h.1.2.1.2
  unfold RCKCompConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6, heD, he1, hKcomp, hJK, hOddK⟩
  obtain ⟨hlift, hcomm⟩ := rckCM_lifts_PSL hcfg hID
  have heA : e ∈ A := hB1A (hDB1 heD)
  have hep : e ^ p = 1 := hAel.2 e heA
  obtain ⟨s, hslift, hsodd, ê, hê, J', hJ'comp, hJ'map⟩ :=
    rckF1_PSL hp hp2 hep hf ψ hrange hker (hAnorm heA) (hID e heA) hKcomp
  have hS : ∀ a ∈ ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 f))),
      ∀ b ∈ ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 f))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a; subst b
    exact Commute.refl s
  have hodd : ∀ a ∈ ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 f))), Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hsodd
  obtain ⟨k, hh, ι, hh1, hιinj, hιrange, hιequiv⟩ :=
    rckM3_PSL_equiv m f hf {s} hS hodd hê hJ'comp
  let ψ' : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X := ψ
  have hlift' : ∀ a ∈ A, ∃ s : GL (Fin (m + 1)) (GaloisField 2 f),
      IsGLLift Matrix.SpecialLinearGroup.toGL ψ' s a := hlift
  have hcomm' : ∀ a ∈ A, ∀ a' ∈ A, ∀ s s' : GL (Fin (m + 1)) (GaloisField 2 f),
      IsGLLift Matrix.SpecialLinearGroup.toGL ψ' s a →
        IsGLLift Matrix.SpecialLinearGroup.toGL ψ' s' a' → Commute s s' := hcomm
  have hslift' : IsGLLift Matrix.SpecialLinearGroup.toGL ψ' s e := hslift
  have hker' : ψ'.ker ≤ Subgroup.center
      (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) := hker
  have hJ'map' : Subgroup.map ψ' J' = K := hJ'map
  let φ : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 hh) →* X := ψ'.comp ι
  have hφrange : (ψ'.comp ι).range = K := by
    rw [MonoidHom.range_comp, hιrange, hJ'map']
  have hφker : φ.ker ≤ Subgroup.center
      (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 hh)) := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    rw [Subgroup.mem_center_iff]
    intro z
    apply hιinj
    rw [map_mul, map_mul]
    have hyc : ι y ∈ Subgroup.center
        (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :=
      hker' (by rwa [MonoidHom.mem_ker])
    exact Subgroup.mem_center_iff.mp hyc (ι z)
  have hφinner : ∀ b ∈ B₁,
      GGPsiInnerDiag (SpecialLinear.rootDatum k (GaloisField 2 hh)) φ b := by
    intro b hb
    obtain ⟨s_b, hs_b⟩ := hlift' b (hB1A hb)
    have hcomm_b : Commute s_b s := hcomm' b (hB1A hb) e heA s_b s hs_b hslift'
    obtain ⟨t, ht⟩ := hιequiv s_b (by
      intro s' hs'
      rw [Set.mem_singleton_iff] at hs'
      subst s'
      exact hcomm_b)
    refine ggPsiInnerDiag_of_conjSL (k := k) (F := GaloisField 2 hh) (φ := φ) (t := t) ?_
    intro y
    obtain ⟨u', hu'1, hu'2⟩ := hs_b (ι y)
    have hu'2φ : b⁻¹ * φ y * b = ψ' u' := hu'2
    have hu'eq : u' = ι (InnerDiagA.conjSL t y) := by
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [hu'1, ht y]
    rw [hu'2φ, hu'eq]
    rfl
  refine ⟨.PSL, k + 1, hh, ψ'.comp ι, Or.inl rfl, hh1, hφrange, ?_, ?_⟩
  · exact hφker
  · exact hφinner

end CFSG.StandardType.RCKRP
