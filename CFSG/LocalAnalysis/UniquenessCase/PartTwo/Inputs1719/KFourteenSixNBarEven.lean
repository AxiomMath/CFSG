module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BT
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214h
import CFSG.Quasithin.Background.C35InspSmall
import CFSG.CGT.Timmesfeld75.ListWCSzU3
import CFSG.StronglyEmbedded.PSL2Facts
import CFSG.Quasithin.Vol2.Ch11SecOE7E
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
import CFSG.GroupTheory.SylowPairGeneration

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar

open Subgroup CFSG.Blueprint CFSG.Open

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem not_modEq_one_of_card_sylow_two_eq {k r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : Nat.card (Sylow 2 X) = 2 ^ k + 1) :
    ¬ Nat.card (Sylow 2 X) ≡ 1 [MOD r] := by
  rw [h]
  intro hc
  have h1 : r ∣ 2 ^ k := by
    have h2 : 1 ≡ 2 ^ k + 1 [MOD r] := hc.symm
    rwa [Nat.modEq_iff_dvd' (Nat.le_add_left 1 (2 ^ k)), Nat.add_sub_cancel] at h2
  have h3 : r ∣ 2 := hr.dvd_of_dvd_pow h1
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h3)

theorem le_normalizer_of_solvable_sup_of_lieModel [IsSimpleGroup X]
    {F : (S : Type) → [Group S] → Prop}
    (hF : ∀ (S : Type) [Group S], F S → ∃ (t : StatedLieTag) (m n : ℕ), 2 ≤ n ∧
      (t = .PSL ∨ t = .PSp ∨ t = .PSU ∨ t = .POmegaMinus) ∧ LieModel S t m 2 n)
    (hFX : F X) (hnab : ∃ a b : X, a * b ≠ b * a)
    {A U : Subgroup X} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hA : Nat.card A = r) (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤)
    (hAU : UC22.Permutes A U) : A ≤ normalizer (U : Set X) := by
  have hAp : IsPGroup r A := IsPGroup.of_card (n := 1) (by rw [pow_one, hA])
  have hdisj : A ⊓ U = ⊥ :=
    (IsPGroup.disjoint_of_ne (p₁ := r) (p₂ := 2) (hp₁ := ⟨hr⟩) (hp₂ := ⟨Nat.prime_two⟩)
      hr2 A U hAp hU.isPGroup).eq_bot
  have hcard := UC22.uc22p2214_card_sup_of_permutes hAU hdisj
  obtain ⟨k, hk⟩ := hU.isPGroup.exists_card_eq
  have hsol : Group.IsSolvable ↥(A ⊔ U) :=
    CFSG.Quasithin.C35Pf.isSolvable_of_card_pow_mul_pow hr Nat.prime_two hr2 (by
      rw [hcard, hA, hk, pow_one])
  have h := (CFSG.LocalAnalysis.UniquenessCase.UC22.F10.k108BT_of_lieModel hF) X
    (inferInstance : IsSimpleGroup X) hnab hFX U hU (A ⊔ U) le_sup_right hsol
  exact le_sup_left.trans h

theorem psu3_sup_sylow_eq_top {f : ℕ} (h : StatedClassicalModel X .PSU 3 2 f) (hf : 2 ≤ f) :
    ∀ P Q : Sylow 2 X, P ≠ Q → (P : Subgroup X) ⊔ (Q : Subgroup X) = ⊤ := by
  obtain ⟨-, -, -, K, _, _, J, hJ, hKcard, hfixed, ⟨e⟩⟩ :=
    CFSG.AGLEmbedding.UnitaryModel.exists_equiv_psu h
  intro P Q hPQ
  let e' : ↥(⊤ : Subgroup X) ≃*
      CFSG.BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J :=
    Subgroup.topEquiv.trans e
  have hT : quasithinIsSylowTwo (P : Subgroup X) := ⟨P.isPGroup', P.not_dvd_index⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
  have hg' : CFSG.Quasithin.A1b.conjSub g (P : Subgroup X) = (Q : Subgroup X) := by
    rw [← CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.coe_smul_sylow g P, hg]
  have hne : CFSG.Quasithin.A1b.conjSub g ((P : Subgroup X) ⊓ ⊤) ≠
      (P : Subgroup X) ⊓ ⊤ := by
    rw [inf_top_eq, hg']
    intro h
    exact hPQ (Sylow.ext h.symm)
  have hle := CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.le_sup_conjSub_of_psu3 J hJ hf hKcard hfixed
    (L := ⊤) hT e' (l := g) trivial hne
  rw [inf_top_eq, hg'] at hle
  exact top_le_iff.mp hle

theorem barOne_of_sup_normalizer_generation [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) {A U : Subgroup X} {r : ℕ} (hr : r.Prime)
    (hA : Nat.card A = r) (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤)
    (hAU : A ≤ normalizer (U : Set X))
    (hcount : ¬ Nat.card (Sylow 2 X) ≡ 1 [MOD Nat.card A])
    (hgen : ∀ P Q : Sylow 2 X, P ≠ Q → (P : Subgroup X) ⊔ (Q : Subgroup X) = ⊤)
    (hrank : pRank r (⊤ : Subgroup X) ≤ 1) : BarOne A U := by
  have hUidx : ¬ 2 ∣ U.index := by
    have hdvd : ¬ 2 ∣ U.relIndex (⊤ : Subgroup X) :=
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hU).2.2
    rwa [Subgroup.relIndex_top_right] at hdvd
  let U' : Sylow 2 X := hU.isPGroup.toSylow hUidx
  have hrank' : CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := r) (H := (⊤ : Subgroup X)),
      ← CFSG.SectionRank.pRank_eq_open_pRank_top r ↥(⊤ : Subgroup X)]
    exact hrank
  have hsup := CFSG.GroupTheory.sup_normalizer_eq_top_of_sylow_pair
    (p := 2) (by rw [hA]; exact hr) U' hAU hcount hgen (by rw [hA]; exact hrank')
  have hsup' : U ⊔ normalizer (A : Set X) = ⊤ := hsup
  exact ⟨inferInstance, hsup', ⟨U, hU.isPGroup, hAU,
    CFSG.GroupTheory.commutator_ne_bot_of_sup_normalizer_eq_top hnab (by rw [hA]; exact hr)
      hsup'⟩⟩

theorem barOne_of_lieModel_psl2_two [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    {f r : ℕ} (hX : LieModel X .PSL 2 2 f) (hr : r.Prime) (hr2 : r ≠ 2)
    {A U : Subgroup X} (hA : Nat.card A = r)
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) (hAU : UC22.Permutes A U)
    (hrank : pRank r (⊤ : Subgroup X) ≤ 1) : BarOne A U := by
  have hcl : StatedClassicalModel X .PSL 2 2 f := hX.statedClassicalModel (by decide)
  obtain ⟨-, hf1, -, hne, -⟩ := hcl.1
  have hf : 2 ≤ f := by
    by_contra hlt
    have h1 : f = 1 := by omega
    subst h1
    exact hne (by simp)
  have hAU' := le_normalizer_of_solvable_sup_of_lieModel
    (F := fun S _ => LieModel S .PSL 2 2 f)
    (fun S _ hS => ⟨.PSL, 2, f, hf, Or.inl rfl, hS⟩) hX hnab hr hr2 hA hU hAU
  have hcount : ¬ Nat.card (Sylow 2 X) ≡ 1 [MOD Nat.card A] := by
    rw [hA]
    exact not_modEq_one_of_card_sylow_two_eq hr hr2
      (CFSG.LargeExtraspecial.Bender.card_sylow_of_psl2 X 2 f hcl)
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even hf hX
  refine barOne_of_sup_normalizer_generation hnab hr hA hU hAU' hcount ?_ hrank
  intro P Q hPQ
  exact CFSG.BenderSuzuki.psl2_sup_sylow_eq_top e hf hPQ

theorem barOne_of_lieModel_psu3_two [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    {f r : ℕ} (hX : LieModel X .PSU 3 2 f) (hr : r.Prime) (hr2 : r ≠ 2)
    {A U : Subgroup X} (hA : Nat.card A = r)
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) (hAU : UC22.Permutes A U)
    (hrank : pRank r (⊤ : Subgroup X) ≤ 1) : BarOne A U := by
  have hcl : StatedClassicalModel X .PSU 3 2 f := hX.statedClassicalModel (by decide)
  obtain ⟨-, hf1, -, hne⟩ := hcl.1
  have hf : 2 ≤ f := by
    by_contra hlt
    have h1 : f = 1 := by omega
    subst h1
    exact hne (by simp)
  have hAU' := le_normalizer_of_solvable_sup_of_lieModel
    (F := fun S _ => LieModel S .PSU 3 2 f)
    (fun S _ hS => ⟨.PSU, 3, f, hf, Or.inr (Or.inr (Or.inl rfl)), hS⟩) hX hnab hr hr2 hA hU hAU
  have hcount : ¬ Nat.card (Sylow 2 X) ≡ 1 [MOD Nat.card A] := by
    rw [hA]
    exact not_modEq_one_of_card_sylow_two_eq hr hr2
      (CFSG.CGT.Timmesfeld75.card_sylow_psu3 (G := X) (s := f) hcl)
  exact barOne_of_sup_normalizer_generation hnab hr hA hU hAU' hcount
    (psu3_sup_sylow_eq_top hcl hf) hrank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar
