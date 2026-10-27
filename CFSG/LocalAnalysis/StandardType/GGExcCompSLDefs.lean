module

public import CFSG.LocalAnalysis.StandardType.GGCompFieldLieModel
public import CFSG.LocalAnalysis.StandardType.GGLangRatCompTorusLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGSLTag (t : LargeEvenLieTag) : Prop :=
  t = .A ∨ t = .twA ∨ t = .D ∨ t = .twD ∨ t = .E6 ∨ t = .twE6 ∨ t = .E7 ∨ t = .E8 ∨ t = .triD4

@[expose] def GGCompFieldAtSL {G : Type} [Group G] (Q : ℕ) (X : Subgroup G) : Prop :=
  ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ markChar lab = 2 ∧ 2 ^ markDeg lab = Q ∧
    GGSLTag lab.tag ∧ GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) ∧
    ∃ (R : Type) (_ : Group R), MarkedModel lab R ∧ Nonempty (↥X ⧸ Subgroup.center ↥X ≃* R)

@[expose] def GGCompFieldDataSL {G : Type} [Group G] (q : ℕ) (X : Subgroup G) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ GGCompFieldAtSL (q ^ m) X

theorem GGCompFieldAtSL.toAt {G : Type} [Group G] {Q : ℕ} {X : Subgroup G}
    (h : GGCompFieldAtSL Q X) : GGCompFieldAt Q X := by
  obtain ⟨lab, hlab, hc, hdeg, hsl, hhas, R, hR, hmm, he⟩ := h
  refine ⟨lab, hlab, hc, hdeg, ?_, ?_, ?_, hhas, R, hR, hmm, he⟩ <;>
    rcases hsl with h | h | h | h | h | h | h | h | h <;> simp [h]

theorem GGCompFieldAtSL.of_centerQuotEquiv {G H : Type} [Group G] [Group H] {X : Subgroup G}
    {Y : Subgroup H} {Q : ℕ} (θ : ↥X ⧸ Subgroup.center ↥X ≃* ↥Y ⧸ Subgroup.center ↥Y)
    (h : GGCompFieldAtSL Q X) : GGCompFieldAtSL Q Y := by
  obtain ⟨lab, hlab, hchar, hdeg, hsl, hhas, R, instR, hR, ⟨φ⟩⟩ := h
  letI : Group R := instR
  have hhas' : GGHasLabel lab (↥Y ⧸ Subgroup.center ↥Y) := by
    unfold GGHasLabel at hhas ⊢
    refine largeEvenRawDatum_mono ?_ hhas
    rintro R' _ I F ⟨ψ⟩
    exact ⟨θ.symm.trans ψ⟩
  exact ⟨lab, hlab, hchar, hdeg, hsl, hhas', R, instR, hR, ⟨θ.symm.trans φ⟩⟩

theorem GGCompFieldAtSL.congr {G H : Type} [Group G] [Group H] {X : Subgroup G} {Y : Subgroup H}
    {Q : ℕ} (h : GGCompFieldAtSL Q X) (θ : ↥X ≃* ↥Y) : GGCompFieldAtSL Q Y :=
  h.of_centerQuotEquiv (QuotientGroup.congr _ _ θ (Subgroup.map_center_eq θ))

theorem ggCompFieldAtSL_of_lieModel
    {G : Type} [Group G] {X : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥X) {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (h : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) t n 2 f)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .E6 ∨ t = .E7 ∨
      t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4) : GGCompFieldAtSL (2 ^ f) X := by
  have hZ := CFSG.HardMathSupport.Timmesfeld.SporadicRank.center_quotient_center_eq_bot hq
  obtain ⟨lab, hlab, htag, hrank, hchar, hdeg, hraw⟩ := exists_label_rawDatum_of_lieModel hZ h
  have hsl : GGSLTag lab.tag := by
    obtain ⟨tg, r, n⟩ := lab
    cases tg with
    | A => simp [GGSLTag]
    | twA => simp [GGSLTag]
    | D => simp [GGSLTag]
    | twD => simp [GGSLTag]
    | E6 => simp [GGSLTag]
    | E7 => simp [GGSLTag]
    | E8 => simp [GGSLTag]
    | twE6 => simp [GGSLTag]
    | triD4 => simp [GGSLTag]
    | B =>
      rcases ht with h | h | h | h | h | h | h | h | h <;>
        (rw [← htag] at h; exact absurd h (by simp [markTag]))
    | C =>
      rcases ht with h | h | h | h | h | h | h | h | h <;>
        (rw [← htag] at h; exact absurd h (by simp [markTag]))
    | F4 =>
      rcases ht with h | h | h | h | h | h | h | h | h <;>
        (rw [← htag] at h; exact absurd h (by simp [markTag]))
    | G2 =>
      rcases ht with h | h | h | h | h | h | h | h | h <;>
        (rw [← htag] at h; exact absurd h (by simp [markTag]))
    | twB2 =>
      rcases ht with h | h | h | h | h | h | h | h | h <;>
        (rw [← htag] at h; exact absurd h (by simp [markTag]))
    | twF4 =>
      rcases ht with h | h | h | h | h | h | h | h | h <;>
        (rw [← htag] at h; exact absurd h (by simp [markTag]))
    | twF4der =>
      rcases ht with h | h | h | h | h | h | h | h | h <;>
        (rw [← htag] at h; exact absurd h (by simp [markTag]))
    | B2der => exact absurd hchar (by simp [markChar])
    | G2der => exact absurd hchar (by simp [markChar])
  have hmk : MarkedModel lab (↥X ⧸ Subgroup.center ↥X) := by
    unfold MarkedModel
    rw [htag, hrank, hchar, hdeg]
    exact h
  exact ⟨lab, hlab, hchar, by rw [hdeg], hsl, hraw, _, inferInstance, hmk,
    ⟨MulEquiv.refl _⟩⟩

end CFSG.StandardType

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

@[expose] def LangRatCompFieldLenSL :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ S.D.torus →
      (∀ j, a j ^ p = 1) → rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        CFSG.StandardType.GGCompFieldAtSL
          (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
          (rationalComponent S.ρ S.Γ (rootCharHom a) i)

end CFSG.StandardType.LangRat
