module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)

theorem rckFrameCoverPair_mono
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {h : ℕ} {Mod₁ Mod₂ : LieUniversal → ℕ → Prop}
    (hm : ∀ M g, Mod₁ M g → Mod₂ M g) (hc : RCKFrameCoverPair S a i h Mod₁) :
    RCKFrameCoverPair S a i h Mod₂ := by
  obtain ⟨M, φ, hMod, hrest⟩ := hc
  exact ⟨M, φ, hm _ _ hMod, hrest⟩

theorem rckReturnedCover_mono
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {h : ℕ} {Mod₁ Mod₂ : LieUniversal → ℕ → Prop}
    (hm : ∀ M g, Mod₁ M g → Mod₂ M g) (hc : RCKReturnedCover S a i h Mod₁) :
    RCKReturnedCover S a i h Mod₂ := by
  obtain ⟨M, φ, τK, SK, κ, ι, hMod, hrest⟩ := hc
  exact ⟨M, φ, τK, SK, κ, ι, hm _ _ hMod, hrest⟩

theorem rckNC_exc_rank {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* GGLˣ} {i : KernelComponent χ}
    (h : twistKind ρ χ i = .exc) : compRank (componentRoots χ i) = 6 ∨
      compRank (componentRoots χ i) = 4 := by
  unfold twistKind at h
  split_ifs at h with c1 c2 c3 c4 <;>
    first
    | exact absurd h (by decide)
    | (rcases c2 with c2 | c2
       · exact Or.inl c2.1
       · exact Or.inr c2.1)

theorem rckNC_kind_six {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* GGLˣ} {i : KernelComponent χ}
    (h6 : compRank (componentRoots χ i) = 6) (h72 : (componentRoots χ i).ncard = 72) :
    twistKind ρ χ i = .inner ∨ twistKind ρ χ i = .exc := by
  by_cases c1 : twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)])
  · left
    unfold twistKind
    rw [if_pos c1]
  · right
    unfold twistKind
    rw [if_neg c1, if_pos (Or.inl ⟨h6, h72⟩)]

@[expose] def RCKPairA1
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    compRank (componentRoots (rootCharHom a) i) = 1 →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCoverPair S a i h
      (fun M g =>
        M = ggU .PSL 2 g)

@[expose] def RCKPairSLInner
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    twistKind S.ρ (rootCharHom a) i = .inner ∧
      2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1) →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCoverPair S a i h
      (fun M g =>
        M = ggU .PSL (compRank (componentRoots (rootCharHom a) i) + 1) g)

@[expose] def RCKPairSU
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    twistKind S.ρ (rootCharHom a) i = .suN →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCoverPair S a i h
      (fun M g =>
        M = ggU .PSU (compRank (componentRoots (rootCharHom a) i) + 1) g)

@[expose] def RCKPairDInner
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    twistKind S.ρ (rootCharHom a) i = .inner ∧
      4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1) →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCoverPair S a i h
      (fun M g =>
        M = ggU .POmegaPlus (compRank (componentRoots (rootCharHom a) i)) g)

@[expose] def RCKPairTwoD
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    twistKind S.ρ (rootCharHom a) i = .twoD →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCoverPair S a i h
      (fun M g =>
        M = ggU .POmegaMinus (compRank (componentRoots (rootCharHom a) i)) g)

@[expose] def RCKPairE6
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    twistKind S.ρ (rootCharHom a) i = .inner ∧
      compRank (componentRoots (rootCharHom a) i) = 6 ∧
      (componentRoots (rootCharHom a) i).ncard = 72 →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCoverPair S a i h
      (fun M g =>
        M = ggU .E6 0 g)

@[expose] def RCKPairE7
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    twistKind S.ρ (rootCharHom a) i = .inner ∧
      compRank (componentRoots (rootCharHom a) i) = 7 ∧
      (componentRoots (rootCharHom a) i).ncard = 126 →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCoverPair S a i h
      (fun M g =>
        M = ggU .E7 0 g)

@[expose] def RCKPairE8
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    twistKind S.ρ (rootCharHom a) i = .inner ∧
      compRank (componentRoots (rootCharHom a) i) = 8 ∧
      (componentRoots (rootCharHom a) i).ncard = 240 →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCoverPair S a i h
      (fun M g =>
        M = ggU .E8 0 g)

@[expose] def RCKPairTwE6
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    twistKind S.ρ (rootCharHom a) i = .exc ∧ compRank (componentRoots (rootCharHom a) i) = 6 →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCoverPair S a i h
      (fun M g =>
        M = ggU .twistedE6 0 g)

@[expose] def RCKPairTriD4
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    twistKind S.ρ (rootCharHom a) i = .exc ∧ compRank (componentRoots (rootCharHom a) i) = 4 →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCoverPair S a i h
      (fun M g =>
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
          TriField F σ g ∧ M = triD4Universal F σ)

@[expose] def RCKRetE6
    : Prop :=
  ∀ (τ : Tag) (S : LangSetup τ GGL 5) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    twistKind S.ρ (rootCharHom a) i = .inner ∧
      compRank (componentRoots (rootCharHom a) i) = 6 ∧
      (componentRoots (rootCharHom a) i).ncard = 72 →
    RCKReturnedCover S a i h
      (fun M g =>
        M = ggU .E6 0 g)

@[expose] def RCKRetTwE6
    : Prop :=
  ∀ (τ : Tag) (S : LangSetup τ GGL 5) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    twistKind S.ρ (rootCharHom a) i = .exc ∧
      compRank (componentRoots (rootCharHom a) i) = 6 ∧
      (componentRoots (rootCharHom a) i).ncard = 72 →
    RCKReturnedCover S a i h
      (fun M g =>
        M = ggU .twistedE6 0 g)

@[expose] def RCKRetE7
    : Prop :=
  ∀ (τ : Tag) (S : LangSetup τ GGL 5) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    compRank (componentRoots (rootCharHom a) i) = 7 ∧
      (componentRoots (rootCharHom a) i).ncard = 126 →
    RCKReturnedCover S a i h
      (fun M g =>
        M = ggU .E7 0 g)

@[expose] def RCKRetTriD4
    : Prop :=
  ∀ (τ : Tag) (S : LangSetup τ GGL 5) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    compRank (componentRoots (rootCharHom a) i) = 4 ∧
      (componentRoots (rootCharHom a) i).ncard = 24 ∧
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) →
    RCKReturnedCover S a i h
      (fun M g =>
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
          TriField F σ g ∧ M = triD4Universal F σ)

theorem rckCarrierPairADE_of_shapes
    (h1 : RCKPairA1) (h2 : RCKPairSLInner) (h3 : RCKPairSU) (h4 : RCKPairDInner)
    (h5 : RCKPairTwoD) (h6 : RCKPairE6) (h7 : RCKPairE7) (h8 : RCKPairE8) (h9 : RCKPairTwE6)
    (h10 : RCKPairTriD4) : RCKCarrierPairADE := by
  intro τ p₀ S a haT p hp hp2 hap i h hq hshape hqs
  rcases hshape with hs | hs | hs | hs | hs | hs | hs
  · refine rckFrameCoverPair_mono (fun M g hM => ?_) (h1 τ p₀ S a haT p hp hp2 hap i h hq hs hqs)
    exact Or.inl ⟨hs, hM⟩
  · refine rckFrameCoverPair_mono (fun M g hM => ?_) (h2 τ p₀ S a haT p hp hp2 hap i h hq hs hqs)
    exact Or.inr (Or.inl ⟨hs.1, hs.2.1, hs.2.2, hM⟩)
  · refine rckFrameCoverPair_mono (fun M g hM => ?_) (h3 τ p₀ S a haT p hp hp2 hap i h hq hs hqs)
    exact Or.inr (Or.inr (Or.inl ⟨hs, hM⟩))
  · refine rckFrameCoverPair_mono (fun M g hM => ?_) (h4 τ p₀ S a haT p hp hp2 hap i h hq hs hqs)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hs.1, hs.2.1, hs.2.2, hM⟩)))
  · refine rckFrameCoverPair_mono (fun M g hM => ?_) (h5 τ p₀ S a haT p hp hp2 hap i h hq hs hqs)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, hM⟩))))
  · obtain ⟨hin, hE⟩ := hs
    rcases hE with ⟨hr, hc⟩ | ⟨hr, hc⟩ | ⟨hr, hc⟩
    · refine rckFrameCoverPair_mono (fun M g hM => ?_)
        (h6 τ p₀ S a haT p hp hp2 hap i h hq ⟨hin, hr, hc⟩ hqs)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hin, Or.inl ⟨hr, hc, hM⟩⟩)))))
    · refine rckFrameCoverPair_mono (fun M g hM => ?_)
        (h7 τ p₀ S a haT p hp hp2 hap i h hq ⟨hin, hr, hc⟩ hqs)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hin, Or.inr (Or.inl ⟨hr, hc, hM⟩)⟩)))))
    · refine rckFrameCoverPair_mono (fun M g hM => ?_)
        (h8 τ p₀ S a haT p hp hp2 hap i h hq ⟨hin, hr, hc⟩ hqs)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hin, Or.inr (Or.inr ⟨hr, hc, hM⟩)⟩)))))
  · rcases rckNC_exc_rank hs with hr | hr
    · refine rckFrameCoverPair_mono (fun M g hM => ?_)
        (h9 τ p₀ S a haT p hp hp2 hap i h hq ⟨hs, hr⟩ hqs)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hs, Or.inl ⟨hr, hM⟩⟩)))))
    · refine rckFrameCoverPair_mono (fun M g hM => ?_)
        (h10 τ p₀ S a haT p hp hp2 hap i h hq ⟨hs, hr⟩ hqs)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hs, Or.inr ⟨hr, hM⟩⟩)))))

theorem rckCarrierRet_of_shapes
    (h1 : RCKRetE6) (h2 : RCKRetTwE6) (h3 : RCKRetE7) (h4 : RCKRetTriD4) : RCKCarrierRet := by
  intro τ S a haT p hp hp2 hap i h hq hqs hshape
  rcases hshape with ⟨hr, hc⟩ | ⟨hr, hc⟩ | ⟨hr, hc, hn⟩
  · rcases rckNC_kind_six hr hc with hk | hk
    · refine rckReturnedCover_mono (fun M g hM => ?_)
        (h1 τ S a haT p hp hp2 hap i h hq hqs ⟨hk, hr, hc⟩)
      exact Or.inl ⟨hr, Or.inl ⟨hk, hM⟩⟩
    · refine rckReturnedCover_mono (fun M g hM => ?_)
        (h2 τ S a haT p hp hp2 hap i h hq hqs ⟨hk, hr, hc⟩)
      exact Or.inl ⟨hr, Or.inr ⟨hk, hM⟩⟩
  · refine rckReturnedCover_mono (fun M g hM => ?_)
      (h3 τ S a haT p hp hp2 hap i h hq hqs ⟨hr, hc⟩)
    exact Or.inr (Or.inl ⟨hr, hM⟩)
  · refine rckReturnedCover_mono (fun M g hM => ?_)
      (h4 τ S a haT p hp hp2 hap i h hq hqs ⟨hr, hc, hn⟩)
    exact Or.inr (Or.inr ⟨hr, hM⟩)

end CFSG.StandardType.RCKRP
