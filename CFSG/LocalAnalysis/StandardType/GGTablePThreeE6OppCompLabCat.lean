module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6UniqueCompLabelCat
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6OppLangComp
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoCoset
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6UniqueCompLabel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreLang

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def E6OppCompLabel (n : ℕ) (lab : LargeEvenLabel) : Prop :=
  (3 ∣ 2 ^ n + 1 ∧ lab = ⟨.A, 5, n⟩) ∨ (3 ∣ 2 ^ n - 1 ∧ lab = ⟨.twA, 5, n⟩) ∨ lab = ⟨.twD, 4, n⟩

@[expose] def CompLabE6OppAt (d : TauCeti.LieTypeIndex) (S : Type) [Group S] : Prop :=
  ∀ β : MulAut S, β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S →
    β ^ 3 = 1 → β ≠ 1 →
    ∀ K : Subgroup S,
      CFSG.Open.IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) →
      (∀ K' : Subgroup S,
        CFSG.Open.IsComponentOf K'
          (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) → K' = K) →
      ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
        2 ^ lab.n = CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d ∧ E6OppCompLabel lab.n lab

theorem compLabE6OppAt_iff (d : TauCeti.LieTypeIndex) (S : Type) [Group S] :
    CompLabE6OppAt d S ↔
      UniqueCompLabelAt (fun lab : LargeEvenLabel =>
        2 ^ lab.n = CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d ∧
          E6OppCompLabel lab.n lab) S :=
  Iff.rfl

theorem compLabE6Opp_cat_of_lang
    (d : TauCeti.ValidLieTypeIndex) (hch : d.1.characteristic = 2)
    (hd : (∃ q, d.1 = .E6 q ∧ 3 ∣ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 + 1) ∨
      ∃ q, d.1 = .twistedE6 q ∧ 3 ∣ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 - 1)
    (hq : 4 ≤ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1) :
    CompLabE6OppAt d.1 (TauCeti.CFSGIndex.lie d).Group := by
  rw [compLabE6OppAt_iff]
  refine uniqueCompLabelAt_e6_cat_of_lang
    (P := fun lab : LargeEvenLabel =>
      2 ^ lab.n = CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 ∧
        E6OppCompLabel lab.n lab)
    d hch ?_ hq ?_
  · exact hd.imp (fun ⟨q, hqE, _⟩ => ⟨q, hqE⟩) (fun ⟨q, hqT, _⟩ => ⟨q, hqT⟩)
  · intro L _ _ _ S Fr hFr hshape hSq a hT hap h1 i huniq
    rcases hshape with ⟨⟨qE, hqE⟩, hΦ⟩ | ⟨⟨qT, hqT⟩, hΦ⟩
    ·
      have h3 : 3 ∣ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 + 1 := by
        rcases hd with ⟨q, _, hdiv⟩ | ⟨q, hq', _⟩
        · exact hdiv
        · exfalso
          rw [hqE] at hq'
          cases hq'
      have hr : ((S.D.q : ℕ) : ZMod 3) = 2 := by
        rw [hSq]
        have hf :
            ((CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 : ℕ) : ZMod 3) + 1 = 0 := by
          have hz := (ZMod.natCast_eq_zero_iff
            (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 + 1) 3).mpr h3
          simpa only [Nat.cast_add, Nat.cast_one] using hz
        rw [eq_neg_of_add_eq_zero_left hf]
        decide
      have hW : E6CosetW S.ρ := e6_cosetW_of_untw S.D S.frob ⟨Fr, hFr, hΦ⟩
      obtain ⟨lab, hRlab, hpow, hcase⟩ :=
        e6Opp_lang_rationalComponents_untw S hr hW hT hap h1 i huniq
      unfold RationalLabelIs at hRlab
      obtain ⟨hlab, hhas⟩ := hRlab
      refine ⟨lab, hlab, hhas, ?_, ?_⟩
      · rw [hpow, hSq]
      · rcases hcase with ⟨htag, hrank⟩ | ⟨htag, hrank⟩
        · left
          exact ⟨by rw [hpow, hSq]; exact h3, by rw [← htag, ← hrank]⟩
        · right
          right
          rw [← htag, ← hrank]
    ·
      have h3 : 3 ∣ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 - 1 := by
        rcases hd with ⟨q, hq', _⟩ | ⟨q, _, hdiv⟩
        · exfalso
          rw [hqT] at hq'
          cases hq'
        · exact hdiv
      have hr : ((S.D.q : ℕ) : ZMod 3) = 1 := by
        rw [hSq]
        have h1le : 1 ≤ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 :=
          le_trans (by norm_num) hq
        have hsub : ((CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 - 1 : ℕ) : ZMod 3) = 0 :=
          (ZMod.natCast_eq_zero_iff
            (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 - 1) 3).mpr h3
        have hcast : ((CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 : ℕ) : ZMod 3) =
            ((CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 - 1 : ℕ) : ZMod 3) + 1 := by
          conv_lhs => rw [← Nat.sub_add_cancel h1le]
          rw [Nat.cast_add, Nat.cast_one]
        rw [hcast, hsub, zero_add]
      have hneg : ∃ u : WeylGroup Tag.E6, ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -(u • γ) :=
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.exists_weyl_rho_eq_neg
          S hFr hΦ
      obtain ⟨lab, hRlab, hpow, hcase⟩ :=
        e6Opp_lang_rationalComponents_tw S hr hneg hT hap h1 i huniq
      unfold RationalLabelIs at hRlab
      obtain ⟨hlab, hhas⟩ := hRlab
      refine ⟨lab, hlab, hhas, ?_, ?_⟩
      · rw [hpow, hSq]
      · rcases hcase with ⟨htag, hrank⟩ | ⟨htag, hrank⟩
        · right
          left
          exact ⟨by rw [hpow, hSq]; exact h3, by rw [← htag, ← hrank]⟩
        · right
          right
          rw [← htag, ← hrank]

end CFSG.StandardType.TablePThreeKG
