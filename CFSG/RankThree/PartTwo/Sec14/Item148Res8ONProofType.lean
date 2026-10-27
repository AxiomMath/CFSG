module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res7ProofSig
import CFSG.RankThree.PartTwo.Sec14.Item148Res8ONProofImg
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec6.Item65One

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148

variable {G : Type} [Group G] [Finite G]

@[expose] def KType148Cover (A Y : Subgroup G) [(ker148 A Y).Normal] (e : G)
    (K Le : Subgroup G) : Prop :=
  KType148 A Y e K Le ∨
    (Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G) ∧
      Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) CFSG.Blueprint.NativeSporadic.ON ∧
      Sec4.IsTripleCover ↥(img148 A Y K) (alternatingGroup (Fin 7)))

@[expose] def Step148KTypeCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
        letI := ker148_normal hY.2
        KType148Cover A Y e K Le

theorem step148KTypeCover_of_theta
    (hθ : Step148KTheta)
    (hΩ : Step148KThetaOmega) (hON : Step148KThetaONCover) : Step148KTypeCover := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP
  let := ker148_normal hY.2
  obtain ⟨hB, -, -, heB, he1, hK, hKΔ, -, -, halt⟩ := id hP
  have hKY := le_of_mem_thetaComponentsIn hK
  have hKM : K ≤ Y ⊔ A := (hKY.trans inf_le_left).trans le_sup_left
  have hθK := hθ G A c L h Y hY hs hYB B Q e K Le hP
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hsec : 3 ∣ Nat.card ↥(img148 A Y K) →
      Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G) :=
    fun h3 => sectionCentralizer_eq_zpowers148 h.isE27 hY.2 hYB (hB.1 heB) he1 hKY hKΔ
      (h3.trans (card_img148_dvd hKM))
  rcases halt with ⟨he, hLe⟩ | ⟨c', L', hc', hc'B, hL', hJ2, hd, hON3⟩
  ·
    have ht : Nonempty (↥(img148 A Y K) ≃* ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ∨
        ((Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
            (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
              CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
            (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
              CFSG.Assembly.RankThreeEven.projSU 3 5 1))) ∧
          Nonempty (↥(img148 A Y K) ≃* alternatingGroup (Fin 7))) ∨
        (∃ (p f e' : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e' ∧
          Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) p (f * e') ∧
          IsLThreeEpsAt ↥(img148 A Y K) p f) := by
      rcases hΩ G A c L h Y hY hs hYB B Q e K Le hP he hLe with ⟨⟨φ⟩⟩ | ⟨hL, ⟨φ⟩⟩ |
          ⟨p, f, e', hp, hf, he', hiso, hL3⟩
      · exact Or.inl (img148_equiv_of_theta hKM hθK (isSimpleGroup_of_mem_lA148 h he hLe)
          (three_dvd_card_of_types136 (h.chosen136.2 e he Le hLe).1) φ)
      · exact Or.inr (Or.inl ⟨hL, img148_equiv_of_theta hKM hθK isSimpleGroup_a7_148.1
          isSimpleGroup_a7_148.2 φ⟩)
      · have hs' := isSimpleGroup_of_isLThreeEpsAt148 hf hL3
        have h3 := three_dvd_card_of_isLThreeEpsAt148 hf hL3
        obtain ⟨ψ⟩ := img148_equiv_of_theta hKM hθK hs' h3 (MulEquiv.refl _)
        exact Or.inr (Or.inr ⟨p, f, e', hp, hf, he', hiso, isLThreeEpsAt_congr148 ψ.symm hL3⟩)
    have h3 := three_dvd_card_img148_of_types h (Or.inl ⟨he, hLe, ht⟩)
    exact Or.inl ⟨hsec h3, Or.inl ⟨he, hLe, ht⟩⟩
  ·
    rcases hON G A c L h Y hY hs hYB B Q e K Le hP c' L' hc' hc'B hL' hJ2 hd hON3 with
      htc | ⟨h7, ⟨φ⟩⟩
    · have hA7 := Res8ON.isTripleCover_img148_of_theta hKM hθK hKq htc
      exact Or.inr ⟨hsec (Res8ON.three_dvd_card_of_isTripleCover hA7), hON3, hA7⟩
    · have hL37 := img148_equiv_of_theta hKM hθK (isSimpleGroup_l37_148 h7).1
        (isSimpleGroup_l37_148 h7).2 φ
      have h3 := three_dvd_card_img148_of_types (e := e) (Le := Le) h
        (Or.inr ⟨hON3, Or.inr ⟨h7, hL37⟩⟩)
      exact Or.inl ⟨hsec h3, Or.inr ⟨hON3, Or.inr ⟨h7, hL37⟩⟩⟩

end CFSG.RankThree.PartTwo.Sec14
