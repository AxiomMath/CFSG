module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFirstPass
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcRelOneAt
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
public import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.RCKC1 CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag IsElemAbelian)

@[expose] def RCKClassicalShape {τ : Tag} (q : ℕ) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* GGLˣ) (i : KernelComponent χ) : Prop :=
  compRank (componentRoots χ i) = 1 ∨
    (twistKind ρ χ i = .inner ∧ 2 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = compRank (componentRoots χ i) *
        (compRank (componentRoots χ i) + 1)) ∨
    twistKind ρ χ i = .suN ∨
    (τ = Tag.F4 ∧ twistKind ρ χ i = .inner ∧ compRank (componentRoots χ i) = 3 ∧
      (componentRoots χ i).ncard = 18) ∨
    (τ = Tag.F4 ∧ compRank (componentRoots χ i) = 2 ∧ (componentRoots χ i).ncard = 8 ∧
      4 ≤ q ^ componentOrbitLength ρ (componentRoots χ i)) ∨
    (twistKind ρ χ i = .inner ∧ 4 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = 2 * compRank (componentRoots χ i) *
        (compRank (componentRoots χ i) - 1)) ∨
    twistKind ρ χ i = .twoD

@[expose] def RCKSmallShape {τ : Tag} (q : ℕ) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* GGLˣ) (i : KernelComponent χ) : Prop :=
  (twistKind ρ χ i = .suN ∧ compRank (componentRoots χ i) = 2) ∨
    (τ = Tag.F4 ∧ compRank (componentRoots χ i) = 2 ∧ (componentRoots χ i).ncard = 8 ∧
      q ^ componentOrbitLength ρ (componentRoots χ i) < 4)

@[expose] def RCKNonclassShape {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (Ψ : Set (Fin τ.rank → ℤ)) : Prop :=
  (compRank Ψ = 6 ∧ Ψ.ncard = 72) ∨ (compRank Ψ = 7 ∧ Ψ.ncard = 126) ∨
    (compRank Ψ = 4 ∧ Ψ.ncard = 24 ∧
      ¬ twistInner Ψ ((ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength ρ Ψ]))

theorem RCKNonclassShape.excShape {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {Ψ : Set (Fin τ.rank → ℤ)} (h : RCKNonclassShape ρ Ψ) : RCKExcShape ρ Ψ := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

@[expose] def RCKClassEnvelope
    : Prop :=
  ∀ (t : StatedLieTag), GGExcFive t → ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (S : LangSetup (langTag t) GGL 5) (a : Fin (langTag t).rank → GGLˣ),
      rootDiagUnit (langTag t) a ∈ S.D.torus → rootDiagUnit (langTag t) a ≠ 1 →
      (∀ j, a j ^ p = 1) → ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        RCKNonclassShape S.ρ (componentRoots (rootCharHom a) i) ∨
          RCKClassicalShape S.D.q S.ρ (rootCharHom a) i ∨ RCKSmallShape S.D.q S.ρ (rootCharHom a) i

@[expose] def RCKNoSmall
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), GGExcFive t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → K ≠ J →
    ∀ (θ : ↥G₀ →* ModGL (langTag t) GGL) (A' : Subgroup (ModGL (langTag t) GGL))
      (η : ↥G₀ →* ModGL (langTag t) GGL) (E' : Subgroup (ModGL (langTag t) GGL))
      (S : LangSetup (langTag t) GGL 5) (a : Fin (langTag t).rank → GGLˣ)
      (i : KernelComponent (rootCharHom a)),
      RCKFirstPassAt t f p G₀ A B₁ D J K e θ A' η E' S a i →
      ¬ RCKSmallShape S.D.q S.ρ (rootCharHom a) i

@[expose] def RCKNonclassicalArm
    : Prop :=
  RCKExcRelOneAt GGExcFive →
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), GGExcFive t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → K ≠ J →
    ∀ (θ : ↥G₀ →* ModGL (langTag t) GGL) (A' : Subgroup (ModGL (langTag t) GGL))
      (η : ↥G₀ →* ModGL (langTag t) GGL) (E' : Subgroup (ModGL (langTag t) GGL))
      (S : LangSetup (langTag t) GGL 5) (a : Fin (langTag t).rank → GGLˣ)
      (i : KernelComponent (rootCharHom a)),
      RCKFirstPassAt t f p G₀ A B₁ D J K e θ A' η E' S a i →
      RCKNonclassShape S.ρ (componentRoots (rootCharHom a) i) → GGRootPosNbr K R

@[expose] def RCKExcReturnModelAt
    : Prop :=
  RCKExcRelOneAt GGExcFive →
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), GGExcFive t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → K ≠ J → RCKToralFrame t f p G₀ A →
      RCKClassicalModelID K B₁ ∨ GGRootPosNbr K R

theorem rckClassicalModelID_of_pinned
    {X Y : Type} [Group X] [Group Y] {M : LieUniversal} {g : ℕ} {K B : Subgroup X}
    {η : K →* Y} {P0 Pm0 : Subgroup Y} (D : PinnedReturnAt M g K B η P0 Pm0)
    (hcl : ∃ (t : StatedLieTag) (n : ℕ), RCKClassicalTag t ∧ M = ggU t n g)
    (hact : D.ClassicalAction) : RCKClassicalModelID K B := by
  obtain ⟨t, n, ht, rfl⟩ := hcl
  have hg : 1 ≤ g := by
    rcases D.model_at with ⟨t', n', -, hadm, -⟩ | ⟨F, hFld, hFin, σ, hF, -⟩
    · exact hadm.2.1
    · exact hF.1
  refine ⟨t, n, g, K.subtype.comp D.cover, ht, hg, ?_, ?_, hact⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr D.surj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro x hx
    apply D.central
    exact Subtype.ext (by simpa using hx)

theorem rckClassicalModelID_of_shape
    (hSL : RCKCarrierSL) (hA1 : RCKCarrierA1) (hSU : RCKCarrierSU) (hSpF4 : RCKCarrierSpF4)
    (hSpB2 : RCKCarrierSpB2) (hSpin : RCKCarrierSpinPlus) (hTwoD : RCKCarrierTwoD)
    (hTr : RCKPinnedOfFrameCover)
    {X : Type} [Group X] [Finite X] {τ : Tag} {G₀ K B : Subgroup X} (hK : K ≤ G₀)
    {η : ↥G₀ →* ModGL τ GGL} {S : LangSetup τ GGL 5} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hap : rootDiagUnit τ a ^ p = 1)
    (hker : η.ker ≤ Subgroup.center ↥G₀) (hq : S.D.q = 2 ^ f)
    (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hKη : (K.subgroupOf G₀).map η = rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hKqs : CFSG.IsQuasisimple ↥K) (hKodd : Odd (Nat.card (Subgroup.center ↥K)))
    (hB : B ≤ Subgroup.normalizer (K : Set X))
    (hpart : ∀ b ∈ B, ∃ a' ∈ S.D.torus, GGLiePartner G₀ η b a')
    (hsh : RCKClassicalShape S.D.q S.ρ (rootCharHom a) i)
    (hno : ¬ (twistKind S.ρ (rootCharHom a) i = .suN ∧
      compRank (componentRoots (rootCharHom a) i) = 2)) :
    RCKClassicalModelID K B := by
  have key : ∀ (Mod : LieUniversal → ℕ → Prop),
      (∀ M g, Mod M g → ∃ (t' : StatedLieTag) (n' : ℕ), RCKClassicalTag t' ∧ M = ggU t' n' g) →
      RCKFrameCover S a i f Mod → RCKClassicalModelID K B := by
    intro Mod hMod hcov
    obtain ⟨M, P0, Pm0, DK, hM, hact⟩ := hTr X τ G₀ K B hK η 5 S a i f Mod hker hKη hKqs hKodd
      hB hpart hcov
    exact rckClassicalModelID_of_pinned DK (hMod M _ hM) hact
  rcases hsh with h | ⟨hk, h2, hn⟩ | h | ⟨rfl, hk, h3, hn⟩ | ⟨rfl, h2, hn, hQ⟩ | ⟨hk, h4, hn⟩ | h
  · exact key _ (fun M g hM => ⟨.PSL, 2, Or.inl rfl, hM⟩)
      (hA1 τ 5 S a hT p hp hp2 hap i f hq h hqs)
  · exact key _ (fun M g hM => ⟨.PSL, _, Or.inl rfl, hM⟩)
      (hSL τ 5 S a hT p hp hp2 hap i f hq hk h2 hn hqs)
  · by_cases hr2 : compRank (componentRoots (rootCharHom a) i) = 2
    · exact absurd ⟨h, hr2⟩ hno
    · have h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i) := by
        have := (suN_rank_ncard h).1
        omega
      exact key _ (fun M g hM => ⟨.PSU, _, Or.inr (Or.inl rfl), hM⟩)
        (hSU τ 5 S a hT p hp hp2 hap i f hq h h3 hqs)
  · exact key _ (fun M g hM => ⟨.PSp, 3, Or.inr (Or.inr (Or.inl rfl)), hM⟩)
      (hSpF4 5 S a hT p hp hp2 hap i f hq hk h3 hn hqs)
  · have hQ' : 4 ≤ 2 ^ (f * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
      rw [pow_mul, ← hq]
      exact hQ
    exact key _ (fun M g hM => ⟨.PSp, 2, Or.inr (Or.inr (Or.inl rfl)), hM⟩)
      (hSpB2 5 S a hT p hp hp2 hap i f hq h2 hn hQ' hqs)
  · exact key _ (fun M g hM => ⟨.POmegaPlus, _, Or.inr (Or.inr (Or.inr (Or.inl rfl))), hM⟩)
      (hSpin τ 5 S a hT p hp hp2 hap i f hq hk h4 hn hqs)
  · exact key _ (fun M g hM => ⟨.POmegaMinus, _, Or.inr (Or.inr (Or.inr (Or.inr rfl))), hM⟩)
      (hTwoD τ 5 S a hT p hp hp2 hap i f hq h hqs)

theorem rckExc_classicalArm
    (hSL : RCKCarrierSL) (hA1 : RCKCarrierA1) (hSU : RCKCarrierSU) (hSpF4 : RCKCarrierSpF4)
    (hSpB2 : RCKCarrierSpB2) (hSpin : RCKCarrierSpinPlus) (hTwoD : RCKCarrierTwoD)
    (hTr : RCKPinnedOfFrameCover) (hNo : RCKNoSmall)
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* X}
    {p : ℕ} {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X} (ht : GGExcFive t)
    (hcfg : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e) (hKJ : K ≠ J)
    {θ : ↥G₀ →* ModGL (langTag t) GGL} {A' : Subgroup (ModGL (langTag t) GGL)}
    {η : ↥G₀ →* ModGL (langTag t) GGL} {E' : Subgroup (ModGL (langTag t) GGL)}
    {S : LangSetup (langTag t) GGL 5} {a : Fin (langTag t).rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)}
    (hfp : RCKFirstPassAt t f p G₀ A B₁ D J K e θ A' η E' S a i)
    (hsh : RCKClassicalShape S.D.q S.ρ (rootCharHom a) i) : RCKClassicalModelID K B₁ := by
  have hno := hNo X t n f ψ p G₀ A B₁ D J L R Rm K e ht hcfg hKJ θ A' η E' S a i hfp
  have hcfg' := hcfg
  unfold RCKRPConfig at hcfg'
  obtain ⟨-, -, hp, hp2, -, hB1A, -⟩ := hcfg'
  obtain ⟨-, -, hKG, hker, -, hq, -, -, -, hEt, -, hpart, hamem, -, hap, -, hKη, hqs, hKqs, hKodd,
    hB1N, -⟩ := hfp
  have hap' : rootDiagUnit (langTag t) a ^ p = 1 := by
    have h1 : a ^ p = 1 := funext fun j => by simpa using hap j
    calc rootDiagUnit (langTag t) a ^ p = rootDiagUnitHom (langTag t) GGL (a ^ p) := by
          rw [map_pow]
          rfl
      _ = 1 := by rw [h1, map_one]
  have hKqs' : CFSG.IsQuasisimple ↥K :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥K).2.1).mpr hKqs
  refine rckClassicalModelID_of_shape hSL hA1 hSU hSpF4 hSpB2 hSpin hTwoD hTr hKG hp hp2 hap'
    hker.le hq (hEt hamem) hKη hqs hKqs' hKodd hB1N ?_ hsh (fun h => hno (Or.inl h))
  intro b hb
  obtain ⟨a', ha', hpa⟩ := hpart b (hB1A hb)
  exact ⟨a', hEt ha', hpa⟩

theorem rckExcReturnModelAt_of_contracts
    (hSL : RCKCarrierSL) (hA1 : RCKCarrierA1) (hSU : RCKCarrierSU) (hSpF4 : RCKCarrierSpF4)
    (hSpB2 : RCKCarrierSpB2) (hSpin : RCKCarrierSpinPlus) (hTwoD : RCKCarrierTwoD)
    (hTr : RCKPinnedOfFrameCover) (hNo : RCKNoSmall) (hEnv : RCKClassEnvelope)
    (hNon : RCKNonclassicalArm) : RCKExcReturnModelAt := by
  intro hOne X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht hcfg hKJ hframe
  obtain ⟨θ, A', η, E', S, a, i, hfp⟩ := rckExc_firstPass ht hcfg hframe
  have hcfg' := hcfg
  unfold RCKRPConfig at hcfg'
  obtain ⟨-, -, hp, hp2, -⟩ := hcfg'
  have hfp' := hfp
  obtain ⟨-, -, -, -, -, -, -, -, -, hEt, -, -, hamem, ha1, hap, -, -, hqs, -⟩ := hfp'
  rcases hEnv t ht p hp hp2 S a (hEt hamem) ha1 hap i hqs with hsh | hsh | hsh
  · exact Or.inr (hNon hOne X t n f ψ p G₀ A B₁ D J L R Rm K e ht hcfg hKJ θ A' η E' S a i hfp
      hsh)
  · exact Or.inl (rckExc_classicalArm hSL hA1 hSU hSpF4 hSpB2 hSpin hTwoD hTr hNo ht hcfg hKJ hfp
      hsh)
  · exact absurd hsh (hNo X t n f ψ p G₀ A B₁ D J L R Rm K e ht hcfg hKJ θ A' η E' S a i hfp)

end CFSG.StandardType.RCKRP
