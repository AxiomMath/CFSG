module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Defs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
import CFSG.LocalAnalysis.StandardType.GGFamLabelKind
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestTypeDet
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts4
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AR
import CFSG.Blueprint.OddStandardExact
import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TFAbModels
import CFSG.RankThree.PartTwo.KFacts.K72OutL2

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableCRes

private theorem l10lB_image_eq {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {Ψ : Set (Fin τ.rank → ℤ)} (h : componentOrbitLength ρ Ψ = 1) :
    (fun u => ρ u) '' Ψ = Ψ := by
  have hne : {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ}.Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    simp [componentOrbitLength, hc] at h
  have hmem := Nat.sInf_mem hne
  have h1 : sInf {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ} = 1 := h
  rw [h1] at hmem
  simpa using hmem.2

private theorem l10lB_mul_eq_one {q f s : ℕ} (hqf : q = 2 ^ f) (hs : q ^ s = 2) :
    f * s = 1 := by
  subst hqf
  rw [← pow_mul] at hs
  exact Nat.pow_right_injective le_rfl (hs.trans (pow_one 2).symm)

private theorem l10lB_componentLabel_n (r N n : ℕ) (k : TwistKind) :
    (componentLabel r N k n).n = n := by
  cases k <;> simp only [componentLabel] <;> split_ifs <;> rfl

private theorem l10lB_tag_rank_n {lab : LargeEvenLabel}
    (hmt : markTag lab = .PSL) (hrk : markRank lab = 4) (hdg : markDeg lab = 1) :
    (lab.tag = .A ∨ lab.tag = .D) ∧ lab.rank = 3 ∧ lab.n = 1 := by
  rcases lab with ⟨tag, r, n⟩
  cases tag <;>
    simp only [markTag, markRank, markDeg] at hmt hrk hdg ⊢
  · exact ⟨Or.inl trivial, by omega, hdg⟩
  · exact absurd hmt (by decide)
  · exact absurd hmt (by decide)
  · exact absurd hmt (by decide)
  · by_cases h3 : r = 3
    · exact ⟨Or.inr trivial, h3, hdg⟩
    · rw [if_neg h3] at hmt
      exact absurd hmt (by decide)
  · by_cases h2 : r = 2
    · rw [if_pos h2] at hrk
      exact absurd hrk (by decide)
    · rw [if_neg h2] at hmt hrk
      by_cases h3 : r = 3
      · rw [if_pos h3] at hmt
        exact absurd hmt (by decide)
      · rw [if_neg h3] at hmt
        exact absurd hmt (by decide)
  · exact absurd hmt (by decide)
  · exact absurd hmt (by decide)
  · exact absurd hmt (by decide)
  · exact absurd hmt (by decide)
  · exact absurd hmt (by decide)
  · exact absurd hmt (by decide)
  · exact absurd hmt (by decide)
  · exact absurd hmt (by decide)
  · exact absurd hmt (by decide)
  · exact absurd hrk (by decide)
  · exact absurd hmt (by decide)
  · exact absurd hmt (by decide)

private theorem l10lB_label_inner {r N n : ℕ} {k : TwistKind}
    (htag : (componentLabel r N k n).tag = .A ∨ (componentLabel r N k n).tag = .D)
    (hrk : (componentLabel r N k n).rank = 3) :
    k = .inner ∧ r = 3 ∧ N = 12 := by
  cases k
  · simp only [componentLabel] at htag hrk ⊢
    split_ifs at htag hrk ⊢
    · subst hrk
      refine ⟨trivial, rfl, ?_⟩
      omega
    · subst hrk
      refine ⟨trivial, rfl, ?_⟩
      omega
  · simp only [componentLabel] at htag
    exact absurd htag (by decide)
  · simp only [componentLabel] at htag
    exact absurd htag (by decide)
  · simp only [componentLabel] at htag
    split_ifs at htag
    · exact absurd htag (by decide)
    · exact absurd htag (by decide)

theorem ggLieA8_of_label
    {τ : Tag} {G : Type} [Group G] (ρ : Equiv.Perm (Fin τ.rank → ℤ)) {q f : ℕ} (hf : 1 ≤ f)
    (hq : q = 2 ^ f) (Ψ : Set (Fin τ.rank → ℤ)) (n : ℕ)
    (hn : 2 ^ n = q ^ componentOrbitLength ρ Ψ) (X : Subgroup G)
    (hX : GGCompLabelAt (componentLabel (compRank Ψ) Ψ.ncard (twistKindOf ρ Ψ) n) X)
    (hA3 : GGSixLSevenA3Case X) :
    compRank Ψ = 3 ∧ Ψ.ncard = 12 ∧ (fun u => ρ u) '' Ψ = Ψ ∧
      twistInner Ψ (fun u => ρ u) ∧ q = 2 := by
  set lab : LargeEvenLabel :=
    componentLabel (compRank Ψ) Ψ.ncard (twistKindOf ρ Ψ) n with hlab
  obtain ⟨-, hchar, -, R, hR, hmm, ⟨e⟩⟩ := hX
  letI := hR
  have hLM : LieModel (↥X ⧸ Subgroup.center ↥X) (markTag lab) (markRank lab) 2 (markDeg lab) :=
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm
      (CFSG.StandardType.lieModel_of_markedModel hchar hmm)
  have hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hcard : Nat.card (↥X ⧸ Subgroup.center ↥X) = 20160 :=
    CFSG.OddStandard.HigherRank.YamadaG23.y6f4a_card_psl_four_two hO hA3
  obtain ⟨hmt, halt⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts4.tuple_of_card_20160
      hO hLM.admissible hLM hcard
  have h4 : markRank lab = 4 ∧ markDeg lab = 1 := by
    rcases halt with ⟨h3, -, hd2⟩ | h
    · exfalso
      have hLM3 : LieModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 := by
        rw [hmt, h3, hd2] at hLM
        exact hLM
      exact (CFSG.SeitzReduction.LinearPilot.not_lieModel_PSL_three_four hLM3 hA3).elim
    · exact ⟨h.1, h.2.2⟩
  obtain ⟨htaglab, hrklab, hdnlab⟩ := l10lB_tag_rank_n hmt h4.1 h4.2
  have htag : (componentLabel (compRank Ψ) Ψ.ncard (twistKindOf ρ Ψ) n).tag = .A ∨
      (componentLabel (compRank Ψ) Ψ.ncard (twistKindOf ρ Ψ) n).tag = .D := by
    rwa [← hlab]
  have hrk : (componentLabel (compRank Ψ) Ψ.ncard (twistKindOf ρ Ψ) n).rank = 3 := by
    rwa [← hlab]
  obtain ⟨hk, hr, hN⟩ := l10lB_label_inner (n := n) htag hrk
  have hn1 : n = 1 := by
    have h := hdnlab
    rw [hlab, l10lB_componentLabel_n] at h
    exact h
  rw [hn1] at hn
  have hfs : f * componentOrbitLength ρ Ψ = 1 :=
    l10lB_mul_eq_one hq (by simpa using hn.symm)
  obtain ⟨hf1, hs1⟩ := mul_eq_one.mp hfs
  have hti : twistInner Ψ (fun u => ρ u) := by
    have hti0 : twistInner Ψ
        ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength ρ Ψ]) := by
      by_contra h
      have hs := twistKindOf_eq_suN ρ Ψ h (by omega) (by rw [hr, hN])
      rw [hk] at hs
      exact absurd hs (by decide)
    rw [hs1] at hti0
    simpa using hti0
  exact ⟨hr, hN, l10lB_image_eq hs1, hti, by rw [hq, hf1, pow_one]⟩

end CFSG.StandardType.LieCore
