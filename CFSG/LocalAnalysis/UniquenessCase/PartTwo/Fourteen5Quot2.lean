module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5Quot1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5Inputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem star_inf_sup_star_inf (h : Hyp141 D L₁ L₂ X) {H : Subgroup G} (hXH : X ≤ H) :
    Fourteen5.star H (X ⊓ L₁) ⊔ Fourteen5.star H (X ⊓ L₂) = Fourteen5.star H X := by
  rw [← Fourteen5.star_sup (inf_le_left.trans hXH) (inf_le_left.trans hXH), ← h.X_eq_sup]

theorem inversion_star (h : Hyp141 D L₁ L₂ X) {H : Subgroup G} (hXH : X ≤ H)
    (hAut : ∀ n ∈ (L₁ ⊔ L₂) ⊓ normalizer (X : Set G),
      ∃ m ∈ (H ⊓ (L₁ ⊔ L₂)) ⊓ normalizer (X : Set G), ∀ x ∈ X, m * x * m⁻¹ = n * x * n⁻¹)
    (s₁ s₂ : Bool) :
    ∃ n ∈ normalizer ((Fourteen5.star H (X ⊓ L₁) ⊔ Fourteen5.star H (X ⊓ L₂) :
        Subgroup (Fourteen5.HStar H)) : Set (Fourteen5.HStar H)),
      (∀ x ∈ Fourteen5.star H (X ⊓ L₁), n * x * n⁻¹ = if s₁ then x⁻¹ else x) ∧
        (∀ x ∈ Fourteen5.star H (X ⊓ L₂), n * x * n⁻¹ = if s₂ then x⁻¹ else x) := by
  obtain ⟨n, hn, hn₁, hn₂⟩ := h.exists_inversion s₁ s₂
  obtain ⟨m, hm, hmx⟩ := hAut n hn
  have hmH : m ∈ H := hm.1.1
  have hmN : m ∈ normalizer (X : Set G) := hm.2
  have key : ∀ (s : Bool) (L : Subgroup G),
      (∀ x ∈ X ⊓ L, n * x * n⁻¹ = if s then x⁻¹ else x) →
      ∀ x ∈ Fourteen5.star H (X ⊓ L),
        QuotientGroup.mk' (Fourteen5.core H) ⟨m, hmH⟩ * x *
            (QuotientGroup.mk' (Fourteen5.core H) ⟨m, hmH⟩)⁻¹ =
          if s then x⁻¹ else x := by
    intro s L hinv x hx
    obtain ⟨a, ha, rfl⟩ := (Fourteen5.mem_star_iff).1 hx
    have hsub : (⟨m, hmH⟩ : ↥H) * a * (⟨m, hmH⟩ : ↥H)⁻¹ = (if s then a⁻¹ else a) := by
      apply Subtype.ext
      change m * (a : G) * m⁻¹ = (((if s then a⁻¹ else a) : ↥H) : G)
      rw [show m * (a : G) * m⁻¹ = n * (a : G) * n⁻¹ from hmx (a : G) ha.1,
        hinv (a : G) ha]
      cases s <;> rfl
    have hL : QuotientGroup.mk' (Fourteen5.core H)
          (⟨m, hmH⟩ * a * (⟨m, hmH⟩ : ↥H)⁻¹) =
        QuotientGroup.mk' (Fourteen5.core H) ⟨m, hmH⟩ *
          QuotientGroup.mk' (Fourteen5.core H) a *
            (QuotientGroup.mk' (Fourteen5.core H) ⟨m, hmH⟩)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [← hL, hsub]
    cases s <;> simp [map_inv]
  refine ⟨QuotientGroup.mk' (Fourteen5.core H) ⟨m, hmH⟩, ?_, key s₁ L₁ hn₁, key s₂ L₂ hn₂⟩
  rw [star_inf_sup_star_inf h hXH, Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [show (Fourteen5.star H X).map
      (↑(MulAut.conj (QuotientGroup.mk' (Fourteen5.core H) ⟨m, hmH⟩))) =
      Fourteen5.star H (X.map (MulAut.conj m).toMonoidHom) from Fourteen5.map_conj_star X hmH]
  rw [show X.map (MulAut.conj m).toMonoidHom = X from
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hmN]

theorem permutes_star (h : Hyp141 D L₁ L₂ X) (h1421 : Thm1421 D) (hperm : PermutesPair D.M L₁ L₂)
    {H : Subgroup G} (hXH : X ≤ H) :
    ∀ n ∈ normalizer ((Fourteen5.star H (X ⊓ L₁) ⊔ Fourteen5.star H (X ⊓ L₂) :
        Subgroup (Fourteen5.HStar H)) : Set (Fourteen5.HStar H)),
      ((Fourteen5.star H (X ⊓ L₁)).map (MulAut.conj n).toMonoidHom = Fourteen5.star H (X ⊓ L₁) ∧
        (Fourteen5.star H (X ⊓ L₂)).map (MulAut.conj n).toMonoidHom =
          Fourteen5.star H (X ⊓ L₂)) ∨
      ((Fourteen5.star H (X ⊓ L₁)).map (MulAut.conj n).toMonoidHom = Fourteen5.star H (X ⊓ L₂) ∧
        (Fourteen5.star H (X ⊓ L₂)).map (MulAut.conj n).toMonoidHom =
          Fourteen5.star H (X ⊓ L₁)) := by
  intro n hn
  rw [star_inf_sup_star_inf h hXH] at hn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hI3 : ¬ 3 ∣ Nat.card (rankThreePrimeCore 3 H) := (rankThreePrimeCore_facts H).2.2
  have hn' : n ∈ Fourteen5.star H (normalizer (X : Set G)) :=
    Fourteen5.normalizer_star_le hXH h.sylow.isPGroup hI3 hn
  obtain ⟨a, ha, rfl⟩ := (Fourteen5.mem_star_iff).1 hn'
  have haM : (a : G) ∈ D.M := h.normalizer_X_le h1421 ha
  have hXmap : X.map (MulAut.conj (a : G)).toMonoidHom = X :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 ha
  have hstar1 : (Fourteen5.star H (X ⊓ L₁)).map
      (MulAut.conj (QuotientGroup.mk' (Fourteen5.core H) a)).toMonoidHom =
      Fourteen5.star H ((X ⊓ L₁).map (MulAut.conj (a : G)).toMonoidHom) :=
    Fourteen5.map_conj_star (X ⊓ L₁) a.2
  have hstar2 : (Fourteen5.star H (X ⊓ L₂)).map
      (MulAut.conj (QuotientGroup.mk' (Fourteen5.core H) a)).toMonoidHom =
      Fourteen5.star H ((X ⊓ L₂).map (MulAut.conj (a : G)).toMonoidHom) :=
    Fourteen5.map_conj_star (X ⊓ L₂) a.2
  have hinf1 : (X ⊓ L₁).map (MulAut.conj (a : G)).toMonoidHom =
      X.map (MulAut.conj (a : G)).toMonoidHom ⊓ L₁.map (MulAut.conj (a : G)).toMonoidHom :=
    Subgroup.map_inf_eq X L₁ _ (MulAut.conj (a : G)).injective
  have hinf2 : (X ⊓ L₂).map (MulAut.conj (a : G)).toMonoidHom =
      X.map (MulAut.conj (a : G)).toMonoidHom ⊓ L₂.map (MulAut.conj (a : G)).toMonoidHom :=
    Subgroup.map_inf_eq X L₂ _ (MulAut.conj (a : G)).injective
  rcases hperm (a : G) haM with ⟨hL1, hL2⟩ | ⟨hL1, hL2⟩
  · left
    exact ⟨by rw [hstar1, hinf1, hXmap, hL1], by rw [hstar2, hinf2, hXmap, hL2]⟩
  · right
    exact ⟨by rw [hstar1, hinf1, hXmap, hL1], by rw [hstar2, hinf2, hXmap, hL2]⟩

theorem cfg145 (h : Hyp141 D L₁ L₂ X) (hSg : UC6S846.SigmaStd D) (h1421 : Thm1421 D)
    (hperm : PermutesPair D.M L₁ L₂) {H : Subgroup G} (hH : H ≠ ⊤)
    (hX3 : CFSG.ABGLocalTools.IsSylowOf 3 X H) (hodd : Odd (D.M.relIndex H))
    (hAut : ∀ n ∈ (L₁ ⊔ L₂) ⊓ normalizer (X : Set G),
      ∃ m ∈ (H ⊓ (L₁ ⊔ L₂)) ⊓ normalizer (X : Set G), ∀ x ∈ X, m * x * m⁻¹ = n * x * n⁻¹)
    (h7 : 7 ∣ Nat.card ↥(H ⊓ D.M)) (hHM : ¬ H ≤ D.M) (hIM : rankThreePrimeCore 3 H ≤ D.M)
    (hI7 : ¬ 7 ∣ Nat.card (rankThreePrimeCore 3 H)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 7 P (H ⊓ D.M)) (hPX : P ≤ centralizer (X : Set G))
    (hPc : IsCyclic ↥P) :
    Cfg145 (Fourteen5.star H D.M) (Fourteen5.star H (X ⊓ L₁)) (Fourteen5.star H (X ⊓ L₂))
      (Fourteen5.star H P) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hXH : X ≤ H := hX3.le
  have hI3 : ¬ 3 ∣ Nat.card (rankThreePrimeCore 3 H) := (rankThreePrimeCore_facts H).2.2
  refine
    { isKGroup := Fourteen5.isKGroup_star D.standing.kProper hH
      strong := Fourteen5.isStronglyPEmbedded_star (M := D.M) (h.isStronglyPEmbedded_seven hSg)
        hHM h7 hIM hI7
      card_left := ?_
      card_right := ?_
      card_sup := ?_
      isSylowOf_three := ?_
      normal_eq_bot := fun N hN h3 => Fourteen5.normal_eq_bot_star hN h3
      normalizer_le := ?_
      normalizer_left_le := ?_
      normalizer_right_le := ?_
      inversion := fun s₁ s₂ => inversion_star h hXH hAut s₁ s₂
      permutes := permutes_star h h1421 hperm hXH
      isSylowOf_seven := ?_
      le_centralizer := ?_
      isCyclic := Fourteen5.isCyclic_star hPc
      exists_isSylowOf_two := Fourteen5.exists_isSylowOf_two_star (M := D.M) hodd }
  · rw [Fourteen5.card_star (inf_le_left.trans hXH) (h.sylow.isPGroup.to_le inf_le_left) hI3,
      h.card_inf_left]
  · rw [Fourteen5.card_star (inf_le_left.trans hXH) (h.sylow.isPGroup.to_le inf_le_left) hI3,
      h.card_inf_right]
  · rw [star_inf_sup_star_inf h hXH, Fourteen5.card_star hXH h.sylow.isPGroup hI3, h.card_X]
  · rw [star_inf_sup_star_inf h hXH, ← Fourteen5.star_self (H := H)]
    exact Fourteen5.isSylowOf_star (le_rfl : H ≤ H) hX3
  · rw [star_inf_sup_star_inf h hXH]
    exact (Fourteen5.normalizer_star_le hXH h.sylow.isPGroup hI3).trans
      (Fourteen5.star_mono (h.normalizer_X_le h1421))
  · exact (Fourteen5.normalizer_star_le (inf_le_left.trans hXH)
      (h.sylow.isPGroup.to_le inf_le_left) hI3).trans
      (Fourteen5.star_mono (h.normalizer_inf_le h1421 (L := L₁) (by simp)))
  · exact (Fourteen5.normalizer_star_le (inf_le_left.trans hXH)
      (h.sylow.isPGroup.to_le inf_le_left) hI3).trans
      (Fourteen5.star_mono (h.normalizer_inf_le h1421 (L := L₂) (by simp)))
  · simpa only [Fourteen5.star_inf_left D.M] using
      Fourteen5.isSylowOf_star (inf_le_left : H ⊓ D.M ≤ H) hP
  · rw [star_inf_sup_star_inf h hXH]
    exact Fourteen5.star_le_centralizer hPX

end Hyp141

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
