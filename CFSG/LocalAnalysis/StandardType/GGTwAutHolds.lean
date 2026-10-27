module

public import CFSG.LocalAnalysis.StandardType.GGTwAutBasic
public import CFSG.LocalAnalysis.StandardType.GGTwSLFacts
public import CFSG.LocalAnalysis.StandardType.GGTwSUFacts
public import CFSG.LocalAnalysis.StandardType.GGTwOmFacts
public import CFSG.LocalAnalysis.StandardType.GGTwSLRank
public import CFSG.LocalAnalysis.StandardType.GGTwSURank
public import CFSG.LocalAnalysis.StandardType.GGTwOmRankLE
public import CFSG.LocalAnalysis.StandardType.GGTwOmScRank
public import CFSG.LocalAnalysis.StandardType.GGTwSUSigned
public import CFSG.LocalAnalysis.StandardType.GGR4JNCDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ExcRank
import CFSG.LocalAnalysis.StandardType.GGKGForkLinNsB
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggTwSL_label_of_rec {r f ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1)
    {P : (R : Type) → [Group R] → Set (MulAut R) → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
      P (LargeEvenProj (LargeEvenSLGroup (Fin (2 * r - 1 + ε + 1)) K))
        (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ)) :
    LargeEvenLabelAll ⟨.A, 2 * r - 1 + ε, f⟩ fun R _ I _ => P R I := by
  have _ : ε ≤ 1 := hε
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', h K hK⟩

theorem ggTwSL_label {r f : ℕ} (hr : 3 ≤ r) (h3 : 3 ∣ 2 ^ f + 1)
    (ε : ℕ := 0) (hε : ε ≤ 1 := by omega) :
    LargeEvenLabelAll ⟨.A, 2 * r - 1 + ε, f⟩ fun R _ I _ =>
      GGTorusAutCardSC 3 R I r (2 ^ r * r.factorial) :=
  ggTwSL_label_of_rec (ε := ε) (P := fun R _ I => GGTorusAutCardSC 3 R I r (2 ^ r * r.factorial))
    (by omega) hε fun K _ _ _ hK =>
    ggTwTorus_recipe_of_pieces Nat.prime_three (by norm_num)
      (ggTwSL_facts_rec (d := 2 * r - 1 + ε + 1) hr (by omega) (by rw [hK]; exact h3)).1
      (ggTwSL_facts_rec (d := 2 * r - 1 + ε + 1) hr (by omega) (by rw [hK]; exact h3)).2.1
      (ggTwSL_facts_rec (d := 2 * r - 1 + ε + 1) hr (by omega) (by rw [hK]; exact h3)).2.2
      (ggKGLn_signedEltSC_linearNonsplit Nat.prime_three (by norm_num) ggTw_cast_three_ne_zero
        (by rw [hK]; exact h3) (by omega))
      (ggTwSL_rankLE_rec (d := 2 * r - 1 + ε + 1) hr (by omega) (by rw [hK]; exact h3))
      (ggTwSL_scRank_rec (d := 2 * r - 1 + ε + 1) hr (by omega) (by rw [hK]; exact h3))

theorem ggTwSU_label_of_rec {r f ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1)
    {P : (R : Type) → [Group R] → Set (MulAut R) → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = (2 ^ f) ^ 2 →
      P (LargeEvenProj (LargeEvenSUGroup (Fin (2 * r - 1 + ε + 1)) K (2 ^ f)))
        (LargeEvenMatConjImage (LargeEvenProjMk _)
          (LargeEvenGUSet (Fin (2 * r - 1 + ε + 1)) K (2 ^ f)))) :
    LargeEvenLabelAll ⟨.twA, 2 * r - 1 + ε, f⟩ fun R _ I _ => P R I := by
  have _ : ε ≤ 1 := hε
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := f * 2) (by rw [hK, pow_mul])
  exact ⟨K, inferInstance, inferInstance, hK, hQ', h K hK⟩

theorem ggTwSU_label
    {r f : ℕ} (hf : 1 ≤ f) (hr : 3 ≤ r) (h3 : 3 ∣ 2 ^ f - 1)
    (ε : ℕ := 0) (hε : ε ≤ 1 := by omega) :
    LargeEvenLabelAll ⟨.twA, 2 * r - 1 + ε, f⟩ fun R _ I _ =>
      GGTorusAutCardSC 3 R I r (2 ^ r * r.factorial) :=
  ggTwSU_label_of_rec (ε := ε) (P := fun R _ I => GGTorusAutCardSC 3 R I r (2 ^ r * r.factorial))
    (by omega) hε fun K _ _ _ hK =>
    ggTwTorus_recipe_of_pieces Nat.prime_three (by norm_num)
      (ggTwSU_facts_rec (n := f) (d := 2 * r - 1 + ε + 1) hK hf hr (by omega) h3).1
      (ggTwSU_facts_rec (n := f) (d := 2 * r - 1 + ε + 1) hK hf hr (by omega) h3).2.1
      (ggTwSU_facts_rec (n := f) (d := 2 * r - 1 + ε + 1) hK hf hr (by omega) h3).2.2
      (ggTwSU_signed_rec (n := f) (d := 2 * r - 1 + ε + 1) hK hf hr (by omega) h3)
      (ggTwSU_rankLE_rec (n := f) (d := 2 * r - 1 + ε + 1) hK hf hr (by omega) h3)
      (ggTwSU_scRank_rec (n := f) (d := 2 * r - 1 + ε + 1) hK hf hr (by omega) h3)

theorem ggTwOm_label_of_rec {r f : ℕ} (hr : 3 ≤ r)
    {P : (R : Type) → [Group R] → Set (MulAut R) → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → ∀ b c : K,
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      P (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r + 1 - 1) b c)))
        (LargeEvenInnSet _)) :
    LargeEvenLabelAll ⟨.twD, r + 1, f⟩ fun R _ I _ => P R I := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [if_neg (by omega), if_neg (by omega)] at hQ ⊢
  obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', h K hK b c hbc⟩

theorem ggTwOm_label
    {r f : ℕ} (hf : 1 ≤ f) (hr : 3 ≤ r)
    (h3 : 3 ∣ 2 ^ f - 1 ∨ (Odd r ∧ 3 ∣ 2 ^ f + 1)) :
    LargeEvenLabelAll ⟨.twD, r + 1, f⟩ fun R _ I _ =>
      GGTorusAutCardSC 3 R I r (2 ^ r * r.factorial) :=
  ggTwOm_label_of_rec (P := fun R _ I => GGTorusAutCardSC 3 R I r (2 ^ r * r.factorial)) hr
    fun K _ _ _ hK b c hbc =>
    ggTwTorus_recipe_of_pieces Nat.prime_three (by norm_num)
      (ggTwOm_facts_rec (m := r + 1 - 1) hK hbc hr rfl h3).1
      (ggTwOm_facts_rec (m := r + 1 - 1) hK hbc hr rfl h3).2.1
      (ggTwOm_facts_rec (m := r + 1 - 1) hK hbc hr rfl h3).2.2
      (ggOrthSignedTorusInput_holds.2 K (r + 1 - 1) 3 b c (by omega) hbc Nat.prime_three
        (by rw [hK]; simpa using h3))
      (ggTwOm_rankLE_rec hK hbc hr rfl h3)
      (ggTwOm_scRank_rec hK hbc hr rfl h3)

theorem ggTwTorusAutKnown_of_families :
    GGTwTorusAutKnown := by
  intro f hf
  have h48 : (2 : ℕ) ^ 3 * Nat.factorial 3 = 48 := by decide
  refine ⟨fun h3 => ?_, fun h3 => ?_, ?_⟩
  · have h := ggTwSU_label (r := 3) hf le_rfl h3
    rwa [h48] at h
  · have h := ggTwSL_label (r := 3) le_rfl h3
    rwa [h48] at h
  · have h := ggTwOm_label (r := 3) hf le_rfl (by
      rcases three_dvd_two_pow_pred_or_succ f with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by decide, h⟩)
    rwa [h48] at h

end CFSG.StandardType

end
