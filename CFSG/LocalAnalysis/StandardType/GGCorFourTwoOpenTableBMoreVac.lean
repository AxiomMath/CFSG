module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestVac

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB StdSubRestThree

namespace CorFourTwoMore

section Lift

variable {G : Type} [Group G] [Finite G]

theorem false_of_labelAll_lift {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => ∀ (L' : Type) [Group L']
        [Finite L'] (ψ : L' →* R), Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' →
        commutator L' = ⊤ → ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
          (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A < p ^ 3)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hM : GGInnerDiagOnLab S p B L) : False := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have := Fact.mk hp
  obtain ⟨hL, lab, -, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => S p lab ∧ LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs.1 hs.2) (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1⟩) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, hB3⟩, hlt⟩ := largeEvenRawDatum_exists hraw
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hB : IsElemAbelian p B := hS.1.1
  set γ := ggGamma L hBN with hγ
  have hBp : ∀ b : B, b ^ p = 1 := fun b => Subtype.ext (by simpa using hB.2 b b.2)
  have hBc : ∀ a b : B, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hB a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBN b, ggBeta_mem L θ hBN hB3 b, fun l => ggBeta_ggQuotHom L hBN θ b l⟩
  have hcA := card_range_ggGamma_mul L hBN hp hS
  have h3 : p ^ 3 ≤ Nat.card γ.range := by
    have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
    rw [← hcA, pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 hp.pos
  exact absurd (hlt L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range
    hA hAI) (not_lt.mpr h3)

theorem corFourTwoInputsOn_of_lift {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => ∀ (L' : Type) [Group L']
        [Finite L'] (ψ : L' →* R), Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' →
        commutator L' = ⊤ → ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
          (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A < p ^ 3) :
    GGBstarInnerDiagLInputOn S ∧ GGLTransvectionCenterInputOn S ∧
      GGLNoInvariantLineInputOn S ∧ GGTableBCxInputOn S ∧ GGTableBModuleInputOn S ∧
        GGTableBActionInputOn S := by
  have hBs : ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
      {L D J : Subgroup G}, GGConfig p B Bs x L D J → GGInnerDiagOnLab S p Bs L → False := by
    intro G _ _ p B Bs x L D J hC hL
    exact false_of_labelAll_lift h hC (largeEvenMarking_mono
      (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1, hC.2.1.1.trans hP.2.2.1,
        fun b hb => hP.2.2.2 b (hC.2.1.1 hb)⟩) hL)
  refine ⟨fun G _ _ p B Bs x L D J hC hL => (false_of_labelAll_lift h hC hL).elim,
    fun G _ _ p B Bs x L D J hC hL => (hBs hC hL).elim,
    fun G _ _ p B Bs x L D J hC hL => (hBs hC hL).elim,
    fun G _ _ p B Bs x L D J hC hL => (false_of_labelAll_lift h hC hL).elim,
    fun G _ _ p B Bs x L D J hC hL => (false_of_labelAll_lift h hC hL).elim,
    fun G _ _ p B Bs x L D J B₂ hC hL => (false_of_labelAll_lift h hC hL).elim⟩

end Lift

end CorFourTwoMore

open CorFourTwoMore

@[expose] def GGCorFourTwoTableBVacLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTwoThreeSmallLabel p lab ∨ GGTableBNbrInnerA2Label p lab ∨
    (lab.tag = .twA ∧ lab.rank = 2)

theorem ggCorFourTwoInputsOn_tableBVac :
    GGBstarInnerDiagLInputOn GGCorFourTwoTableBVacLabel ∧
      GGLTransvectionCenterInputOn GGCorFourTwoTableBVacLabel ∧
      GGLNoInvariantLineInputOn GGCorFourTwoTableBVacLabel ∧
      GGTableBCxInputOn GGCorFourTwoTableBVacLabel ∧
      GGTableBModuleInputOn GGCorFourTwoTableBVacLabel ∧
        GGTableBActionInputOn GGCorFourTwoTableBVacLabel := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ggCorFourTwoInputsOn_of_small
    (S := fun p lab => GGTwoThreeSmallLabel p lab ∨ GGTableBNbrInnerA2Label p lab)
    fun p lab hp _ h _ => by
      rcases h with h | h
      · exact largeEvenLabelAll_card_lt_twoThreeSmall h
      · exact largeEvenLabelAll_card_lt_A2 hp h
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := corFourTwoInputsOn_of_lift
    (S := fun _ lab => lab.tag = .twA ∧ lab.rank = 2)
    fun _ _ hp hlab h hs => largeEvenLabelAll_lift_card_lt_unitaryThree hp hlab h.1 h.2 hs
  have hS : ∀ p lab, GGCorFourTwoTableBVacLabel p lab →
      (GGTwoThreeSmallLabel p lab ∨ GGTableBNbrInnerA2Label p lab) ∨
        (lab.tag = .twA ∧ lab.rank = 2) := fun p lab h => by
    rcases h with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro G _ _ p B Bs x L D J hC hL
    exact ((h1.or k1) G p B Bs x L D J hC (hL.mono hS)).mono fun p lab h => by
      rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · intro G _ _ p B Bs x L D J hC hL
    exact (h2.or k2) G p B Bs x L D J hC (hL.mono hS)
  · intro G _ _ p B Bs x L D J hC hL
    exact (h3.or k3) G p B Bs x L D J hC (hL.mono hS)
  · intro G _ _ p B Bs x L D J hC hL
    exact (h4.or k4) G p B Bs x L D J hC (hL.mono hS)
  · intro G _ _ p B Bs x L D J hC hL
    exact (h5.or k5) G p B Bs x L D J hC (hL.mono hS)
  · intro G _ _ p B Bs x L D J B₂ hC hL
    exact (h6.or k6) G p B Bs x L D J B₂ hC (hL.mono hS)

end CFSG.StandardType

end
