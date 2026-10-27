module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5Cfg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.ComponentClassification (Layer.subgroup)

variable {K : Type} [Group K] [Finite K]

theorem isComponentOf_map_conj {J : Subgroup K} (hJ : IsComponentOf J ⊤) (k : K) :
    IsComponentOf (J.map (MulAut.conj k).toMonoidHom) ⊤ := by
  refine CFSG.ComponentClassification.LocalComponents.image hJ
    (MulAut.conj k).toMonoidHom (MulAut.conj k).surjective ?_
  intro hle
  have hker : (MulAut.conj k).toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff (MulAut.conj k).toMonoidHom).mpr (MulAut.conj k).injective
  have hJbot : J = ⊥ := le_antisymm (hker ▸ hle) bot_le
  exact (Subgroup.nontrivial_iff_ne_bot J).mp
    (CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2) hJbot

theorem layer_eq_of_forall {J : Subgroup K} (hJ : IsComponentOf J ⊤)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J) : Layer.subgroup K = J := by
  rw [CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
  exact le_antisymm (sSup_le fun J' hJ' => (hJu J' hJ').le) (le_sSup hJ)

theorem layer_eq_sup_of_forall {J₁ J₂ : Subgroup K} (hJ₁ : IsComponentOf J₁ ⊤)
    (hJ₂ : IsComponentOf J₂ ⊤) (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂) :
    Layer.subgroup K = J₁ ⊔ J₂ := by
  rw [CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
  refine le_antisymm (sSup_le ?_) (sup_le (le_sSup hJ₁) (le_sSup hJ₂))
  rintro J' hJ'
  rcases hJu J' hJ' with h | h
  · rw [h]; exact le_sup_left
  · rw [h]; exact le_sup_right

namespace Cfg145

variable {M X₁ X₂ P : Subgroup K}

theorem centralizer_layer_eq_bot (c : Cfg145 M X₁ X₂ P) :
    centralizer (Layer.subgroup K : Set K) = ⊥ :=
  CFSG.ComponentClassification.RadicalFreeLayer.layer_centralizer_eq_bot c.free

theorem isSimpleGroup_of_isComponentOf (c : Cfg145 M X₁ X₂ P) {J : Subgroup K}
    (hJ : IsComponentOf J ⊤) : IsSimpleGroup ↥J :=
  CFSG.ComponentClassification.RadicalFreeLayer.component_simple c.free J hJ

theorem inf_centralizer_eq_bot (c : Cfg145 M X₁ X₂ P) {J : Subgroup K} (hJ : IsComponentOf J ⊤) :
    J ⊓ centralizer (J : Set K) = ⊥ := by
  rw [CFSG.GroupTheory.inf_centralizer_eq_map_center J,
    CFSG.ComponentClassification.RadicalFreeLayer.component_center_eq_bot c.free J hJ,
    Subgroup.map_bot]

theorem inf_eq_bot_of_isComponentOf (c : Cfg145 M X₁ X₂ P) {J J' : Subgroup K}
    (hJ : IsComponentOf J ⊤) (hJ' : IsComponentOf J' ⊤) (hne : J ≠ J') : J ⊓ J' = ⊥ := by
  have hcomm : ⁅J, J'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne J J' hJ hJ' hne
  have hle : J ≤ centralizer (J' : Set K) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hsub : J ⊓ J' ≤ J' ⊓ centralizer (J' : Set K) :=
    le_inf inf_le_right (inf_le_left.trans hle)
  rw [inf_centralizer_eq_bot c hJ'] at hsub
  exact le_antisymm hsub bot_le

theorem three_dvd_card_of_isComponentOf (c : Cfg145 M X₁ X₂ P) {J : Subgroup K}
    (hJ : IsComponentOf J ⊤) : 3 ∣ Nat.card J := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let S : Set (Subgroup K) := {J' | IsComponentOf J' ⊤ ∧ ¬ 3 ∣ Nat.card J'}
  let N : Subgroup K := sSup S
  let H : S → Subgroup K := fun i => (i : Subgroup K)
  haveI : Fintype S := Fintype.ofFinite S
  have hcomm : Pairwise fun i j : S => ∀ x y : K, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij x y hx hy
    have hne : (i : Subgroup K) ≠ (j : Subgroup K) := fun h => hij (Subtype.ext h)
    have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne
      (i : Subgroup K) (j : Subgroup K) i.2.1 j.2.1 hne
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm
  have hNnormal : N.Normal := by
    have hmap : ∀ k : K, N.map (MulAut.conj k).toMonoidHom ≤ N := by
      intro k
      change (sSup S).map (MulAut.conj k).toMonoidHom ≤ sSup S
      rw [Subgroup.map_le_iff_le_comap]
      apply sSup_le
      rintro J' ⟨hJ', hJ'3⟩
      rw [← Subgroup.map_le_iff_le_comap]
      apply le_sSup
      refine ⟨isComponentOf_map_conj hJ' k, ?_⟩
      rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
      exact hJ'3
    refine ⟨fun n hn k => ?_⟩
    have hmem : (MulAut.conj k).toMonoidHom n ∈ N.map (MulAut.conj k).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hn
    have hk := hmap k hmem
    change (MulAut.conj k) n ∈ N at hk
    rwa [MulAut.conj_apply] at hk
  have hN3 : ¬ 3 ∣ Nat.card N := by
    have hrange : N = (Subgroup.noncommPiCoprod (H := H) hcomm).range := by
      rw [show N = sSup S from rfl, sSup_eq_iSup']
      exact (Subgroup.noncommPiCoprod_range (H := H) (hcomm := hcomm)).symm
    have hdvd : Nat.card N ∣ ∏ i : S, Nat.card (H i) := by
      rw [hrange]
      simpa only [Nat.card_pi] using
        Subgroup.card_range_dvd (Subgroup.noncommPiCoprod (H := H) hcomm)
    have hcop : Nat.Coprime 3 (∏ i : S, Nat.card (H i)) :=
      Nat.coprime_fintype_prod_right_iff.mpr fun i =>
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr i.2.2
    intro h3
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop)
      (dvd_trans h3 hdvd)
  have hNbot : N = ⊥ := c.normal_eq_bot N hNnormal hN3
  by_contra h3J
  have hJS : J ∈ S := ⟨hJ, h3J⟩
  have hJle : J ≤ N := le_sSup hJS
  rw [hNbot] at hJle
  have hJbot : J = ⊥ := le_antisymm hJle bot_le
  exact (Subgroup.nontrivial_iff_ne_bot J).mp
    (CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2) hJbot

theorem isSylowOf_inf_of_isComponentOf (c : Cfg145 M X₁ X₂ P) {J : Subgroup K}
    (hJ : IsComponentOf J ⊤) : CFSG.ABGLocalTools.IsSylowOf 3 ((X₁ ⊔ X₂) ⊓ J) J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let E : Subgroup K := Layer.subgroup K
  have hJE : J ≤ E := CFSG.ComponentClassification.Layer.component_le hJ
  have hEnormal : E.Normal := CFSG.ComponentClassification.Layer.normal K
  have hEnorm : E ≤ normalizer (J : Set K) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJE).mp
      (CFSG.ComponentClassification.Layer.normal_component hJ)
  have h1 : CFSG.ABGLocalTools.IsSylowOf 3 ((X₁ ⊔ X₂) ⊓ E) E :=
    c.isSylowOf_three.inf_of_le_normalizer le_top
      (Subgroup.normalizer_eq_top_iff.mpr hEnormal).ge
  have h2 : CFSG.ABGLocalTools.IsSylowOf 3 (((X₁ ⊔ X₂) ⊓ E) ⊓ J) J :=
    h1.inf_of_le_normalizer hJE hEnorm
  have heq : ((X₁ ⊔ X₂) ⊓ E) ⊓ J = (X₁ ⊔ X₂) ⊓ J := by
    rw [inf_assoc, inf_comm E J, ← inf_assoc,
      inf_eq_left.mpr (inf_le_right.trans hJE)]
  rw [heq] at h2
  exact h2

theorem inf_ne_bot_of_isComponentOf (c : Cfg145 M X₁ X₂ P) {J : Subgroup K}
    (hJ : IsComponentOf J ⊤) : (X₁ ⊔ X₂) ⊓ J ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card J := three_dvd_card_of_isComponentOf c hJ
  have hcard := CFSG.ABGLocalTools.IsSylowOf.card_eq
    (isSylowOf_inf_of_isComponentOf c hJ)
  have hpos : 1 ≤ (Nat.card J).factorization 3 :=
    (Nat.prime_three.dvd_iff_one_le_factorization (Nat.card_pos (α := J)).ne').mp h3
  have hlt : 1 < Nat.card ((X₁ ⊔ X₂) ⊓ J : Subgroup K) := by
    rw [hcard]
    calc 1 < 3 := by norm_num
      _ = 3 ^ 1 := by rw [pow_one]
      _ ≤ 3 ^ (Nat.card J).factorization 3 :=
          pow_le_pow_right' (show (1 : ℕ) ≤ 3 by norm_num) hpos
  exact (Subgroup.one_lt_card_iff_ne_bot ((X₁ ⊔ X₂) ⊓ J)).mp hlt

theorem false_of_three_components (c : Cfg145 M X₁ X₂ P) {J₁ J₂ J₃ : Subgroup K}
    (hJ₁ : IsComponentOf J₁ ⊤) (hJ₂ : IsComponentOf J₂ ⊤) (hJ₃ : IsComponentOf J₃ ⊤)
    (h₁₂ : J₁ ≠ J₂) (h₁₃ : J₁ ≠ J₃) (h₂₃ : J₂ ≠ J₃) : False := by
  let X : Subgroup K := X₁ ⊔ X₂
  let Z₁ : Subgroup K := X ⊓ J₁
  let Z₂ : Subgroup K := X ⊓ J₂
  let Z₃ : Subgroup K := X ⊓ J₃
  have hZ₁ : Z₁ ≠ ⊥ := inf_ne_bot_of_isComponentOf c hJ₁
  have hZ₂ : Z₂ ≠ ⊥ := inf_ne_bot_of_isComponentOf c hJ₂
  have hZ₃ : Z₃ ≠ ⊥ := inf_ne_bot_of_isComponentOf c hJ₃
  have hZ₁X : Z₁ ≤ X := inf_le_left
  have hZ₂X : Z₂ ≤ X := inf_le_left
  have hZ₃X : Z₃ ≤ X := inf_le_left
  have hZ₁J : Z₁ ≤ J₁ := inf_le_right
  have hZ₂J : Z₂ ≤ J₂ := inf_le_right
  have hXcard : Nat.card X = 9 := c.card_sup
  have hcomm : ∀ x ∈ Z₁, ∀ y ∈ Z₂, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val ((c.isElemAbelian.1.is_comm.comm
      (⟨x, hZ₁X hx⟩ : X) ⟨y, hZ₂X hy⟩))
  have hinf : Z₁ ⊓ Z₂ = ⊥ := by
    have hsub : Z₁ ⊓ Z₂ ≤ J₁ ⊓ J₂ :=
      le_inf (inf_le_left.trans hZ₁J) (inf_le_right.trans hZ₂J)
    rw [inf_eq_bot_of_isComponentOf c hJ₁ hJ₂ h₁₂] at hsub
    exact le_antisymm hsub bot_le
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Z₁ Z₂ hcomm
  rw [hinf, Subgroup.card_bot, mul_one] at hcard
  have hcardZ₁ : 3 ≤ Nat.card Z₁ := by
    have hdvd : Nat.card Z₁ ∣ 3 ^ 2 := by
      have h : Nat.card Z₁ ∣ Nat.card X := Subgroup.card_dvd_of_le hZ₁X
      rwa [hXcard, show (9 : ℕ) = 3 ^ 2 by norm_num] at h
    have hne : Nat.card Z₁ ≠ 1 := fun h => hZ₁ (Subgroup.card_eq_one.mp h)
    obtain ⟨k, hk, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    interval_cases k
    · rw [pow_zero] at hk_eq
      exact absurd hk_eq hne
    · rw [hk_eq]; norm_num
    · rw [hk_eq]; norm_num
  have hcardZ₂ : 3 ≤ Nat.card Z₂ := by
    have hdvd : Nat.card Z₂ ∣ 3 ^ 2 := by
      have h : Nat.card Z₂ ∣ Nat.card X := Subgroup.card_dvd_of_le hZ₂X
      rwa [hXcard, show (9 : ℕ) = 3 ^ 2 by norm_num] at h
    have hne : Nat.card Z₂ ≠ 1 := fun h => hZ₂ (Subgroup.card_eq_one.mp h)
    obtain ⟨k, hk, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    interval_cases k
    · rw [pow_zero] at hk_eq
      exact absurd hk_eq hne
    · rw [hk_eq]; norm_num
    · rw [hk_eq]; norm_num
  have hsupX : Z₁ ⊔ Z₂ = X := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hZ₁X hZ₂X)
    rw [hcard, hXcard]
    nlinarith [hcardZ₁, hcardZ₂]
  have h₁C : J₁ ≤ centralizer (J₃ : Set K) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne J₁ J₃ hJ₁ hJ₃ h₁₃)
  have h₂C : J₂ ≤ centralizer (J₃ : Set K) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne J₂ J₃ hJ₂ hJ₃ h₂₃)
  have hXle : X ≤ centralizer (J₃ : Set K) := by
    rw [← hsupX]
    exact sup_le (hZ₁J.trans h₁C) (hZ₂J.trans h₂C)
  have hbot : Z₃ = ⊥ := by
    have hle : Z₃ ≤ J₃ ⊓ centralizer (J₃ : Set K) :=
      le_inf inf_le_right (hZ₃X.trans hXle)
    rw [inf_centralizer_eq_bot c hJ₃] at hle
    exact le_antisymm hle bot_le
  exact hZ₃ hbot

theorem components (c : Cfg145 M X₁ X₂ P) :
    (∃ J : Subgroup K, IsComponentOf J ⊤ ∧ ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J) ∨
      ∃ J₁ J₂ : Subgroup K, IsComponentOf J₁ ⊤ ∧ IsComponentOf J₂ ⊤ ∧ J₁ ≠ J₂ ∧
        ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂ := by
  haveI : Nontrivial K := by
    have hX₁ : X₁ ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card X₁ = 1 := by rw [hbot, Subgroup.card_bot]
      have hthree : Nat.card X₁ = 3 := c.card_left
      omega
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX₁
    exact ⟨(x : K), 1, fun h => hx (Subtype.ext h)⟩
  obtain ⟨J, hJ⟩ := CFSG.ComponentClassification.RadicalFreeLayer.exists_component c.free
  by_cases hall : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J
  · exact Or.inl ⟨J, hJ, hall⟩
  · push Not at hall
    obtain ⟨J₂, hJ₂, hne₂⟩ := hall
    refine Or.inr ⟨J, J₂, hJ, hJ₂, Ne.symm hne₂, ?_⟩
    intro J' hJ'
    by_cases h : J' = J
    · exact Or.inl h
    · refine Or.inr ?_
      by_contra hne
      exact false_of_three_components c hJ hJ₂ hJ' (Ne.symm hne₂) (Ne.symm h) (Ne.symm hne)

end Cfg145

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
