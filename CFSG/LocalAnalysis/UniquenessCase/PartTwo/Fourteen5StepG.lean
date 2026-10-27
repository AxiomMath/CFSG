module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5StepC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem exists_isSylowOf_seven_le_centralizer (h : Hyp141 D L₁ L₂ X) (h1422 : Thm1422 D)
    (hperm : PermutesPair D.M L₁ L₂) {H : Subgroup G} (hH : H ≠ ⊤) (hXH : X ≤ H)
    (hAut : ∀ n ∈ (L₁ ⊔ L₂) ⊓ normalizer (X : Set G),
      ∃ m ∈ (H ⊓ (L₁ ⊔ L₂)) ⊓ normalizer (X : Set G), ∀ x ∈ X, m * x * m⁻¹ = n * x * n⁻¹)
    (hHM : ¬ H ≤ D.M) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 7 P (H ⊓ D.M) ∧
      P ≤ centralizer (X : Set G) := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf 7 (H ⊓ D.M)
  have hP₀H : P₀ ≤ H := hP₀.le.trans inf_le_left
  have hP₀M : P₀ ≤ D.M := hP₀.le.trans inf_le_right
  have hP₀n12 : P₀ ≤ normalizer (L₁ : Set G) ⊓ normalizer (L₂ : Set G) :=
    le_normalizer_of_isPGroup h hperm Nat.prime_seven (by norm_num) hP₀.isPGroup hP₀M
  have hP₀nL : P₀ ≤ normalizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) :=
    hP₀n12.trans (Subgroup.inf_normalizer_le_normalizer_sup L₁ L₂)
  have hP₀nQcore : P₀ ≤ normalizer (pCoreOf 2 (L₁ ⊔ L₂) : Set G) :=
    hP₀nL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (L₁ ⊔ L₂))
  have hact₁ : ∀ w ∈ P₀, ∀ l ∈ L₁, w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁ :=
    h.acts_trivially_of_not_le h1422 hperm hH hXH hAut hHM (L := L₁) (by simp)
      hP₀.isPGroup hP₀.le
  have hact₂ : ∀ w ∈ P₀, ∀ l ∈ L₂, w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 L₂ :=
    h.acts_trivially_of_not_le h1422 hperm hH hXH hAut hHM (L := L₂) (by simp)
      hP₀.isPGroup hP₀.le
  have hactQ : ∀ p ∈ P₀, ∀ l ∈ L₁ ⊔ L₂,
      p * l * p⁻¹ * l⁻¹ ∈ pCoreOf 2 (L₁ ⊔ L₂) := by
    intro p hp l hl
    exact (acts_trivially_sup_iff h (hP₀n12 hp).1 (hP₀n12 hp).2).2
      ⟨hact₁ p hp, hact₂ p hp⟩ l hl
  set Q : Subgroup G := pCoreOf 2 (L₁ ⊔ L₂) with hQ
  set O : Subgroup G := H ⊓ Q with hO
  set R : Subgroup G := O ⊔ X with hR
  have hO2 : IsPGroup 2 O := by
    rw [hO, hQ]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L₁ ⊔ L₂)).to_inf_right
  have hXnQ : X ≤ normalizer (Q : Set G) := by
    rw [hQ]
    exact h.sylow.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ L₂))
  have hP₀nQ : P₀ ≤ normalizer (Q : Set G) := by
    rw [hQ]
    exact hP₀nQcore
  have hXnO : X ≤ normalizer (O : Set G) := by
    rw [hO]
    exact (le_inf (hXH.trans Subgroup.le_normalizer) hXnQ).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := H) (K := Q))
  have hP₀nO : P₀ ≤ normalizer (O : Set G) := by
    rw [hO]
    exact (le_inf (hP₀H.trans Subgroup.le_normalizer) hP₀nQ).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := H) (K := Q))
  have hOX : O ⊓ X = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 2 3 (by norm_num) O X hO2 h.sylow.isPGroup)
  have hcardX : Nat.card X = 9 := card_X h
  have hcardR : Nat.card R = Nat.card O * 9 := by
    have h := CFSG.GH74.Uniqueness.card_sup_mul_card_inf' (A := O) (C := X) hXnO
    rw [hOX, Subgroup.card_bot, mul_one, hcardX] at h
    rw [hR, sup_comm]
    exact h
  have h7O : ¬ 7 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hO2
    rw [hk]
    intro hdvd
    have h72 : 7 ∣ 2 := Nat.prime_seven.dvd_of_dvd_pow hdvd
    norm_num at h72
  have h3O : ¬ 3 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hO2
    rw [hk]
    intro hdvd
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdvd
    norm_num at h32
  have h7R : ¬ 7 ∣ Nat.card R := by
    rw [hcardR]
    exact Nat.Prime.not_dvd_mul Nat.prime_seven h7O (by norm_num)
  have hconvO : ∀ p ∈ P₀, ∀ x ∈ X, p * x * p⁻¹ * x⁻¹ ∈ O := by
    intro p hp x hx
    rw [hO]
    exact ⟨H.mul_mem (H.mul_mem (H.mul_mem (hP₀H hp) (hXH hx)) (H.inv_mem (hP₀H hp)))
        (H.inv_mem (hXH hx)), hactQ p hp x (h.sylow.le hx)⟩
  have hdecomp : (↑R : Set G) = (↑O : Set G) * (↑X : Set G) := by
    rw [hR]
    exact Subgroup.coe_mul_of_right_le_normalizer_left O X hXnO
  have hdecomp_mem : ∀ r ∈ R, ∃ o ∈ O, ∃ x ∈ X, o * x = r := by
    intro r hr
    have hr' : r ∈ (↑O : Set G) * (↑X : Set G) := by
      rw [← hdecomp]
      exact hr
    exact Set.mem_mul.mp hr'
  have hOR : O ≤ R := by rw [hR]; exact le_sup_left
  have hconj_mem : ∀ p ∈ P₀, ∀ r ∈ R, p * r * p⁻¹ ∈ R := by
    intro p hp r hr
    obtain ⟨o, ho, x, hx, hox⟩ := hdecomp_mem r hr
    rw [← hox]
    have hpo : p * o * p⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hP₀nO hp) o).1 ho
    have hpxR : p * x * p⁻¹ ∈ R := by
      rw [show p * x * p⁻¹ = (p * x * p⁻¹ * x⁻¹) * x by group, hR]
      exact Subgroup.mul_mem_sup (hconvO p hp x hx) hx
    rw [show p * (o * x) * p⁻¹ = (p * o * p⁻¹) * (p * x * p⁻¹) by group]
    exact R.mul_mem (hOR hpo) hpxR
  have hP₀nR : P₀ ≤ normalizer (R : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · exact hconj_mem p hp r
    · intro hr
      have h := hconj_mem p⁻¹ (P₀.inv_mem hp) (p * r * p⁻¹) hr
      have heq : p⁻¹ * (p * r * p⁻¹) * (p⁻¹)⁻¹ = r := by group
      rwa [heq] at h
  have htriv : ∀ p ∈ P₀, ∀ r ∈ R, p * r * p⁻¹ * r⁻¹ ∈ O := by
    intro p hp r hr
    obtain ⟨o, ho, x, hx, hox⟩ := hdecomp_mem r hr
    rw [← hox]
    have h1 : p * o * p⁻¹ * o⁻¹ ∈ O :=
      O.mul_mem ((Subgroup.mem_normalizer_iff.1 (hP₀nO hp) o).1 ho) (O.inv_mem ho)
    have h2 : o * (p * x * p⁻¹ * x⁻¹) * o⁻¹ ∈ O :=
      O.mul_mem (O.mul_mem ho (hconvO p hp x hx)) (O.inv_mem ho)
    rw [show p * (o * x) * p⁻¹ * (o * x)⁻¹ =
      (p * o * p⁻¹ * o⁻¹) * (o * (p * x * p⁻¹ * x⁻¹) * o⁻¹) by group]
    exact O.mul_mem h1 h2
  obtain ⟨S, hS_fus, -, hP₀nS⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing (A := P₀) (M := R) (Q := ⊥)
      Nat.prime_seven Nat.prime_three hP₀.isPGroup h7R hP₀nR bot_le
      (IsPGroup.of_card (n := 0) (by simp))
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 S R :=
    CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS_fus
  have hSO : S ⊓ O = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) S O hS.isPGroup hO2)
  have hP₀centS : P₀ ≤ centralizer (S : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hcommS : p * s * p⁻¹ * s⁻¹ ∈ S :=
      S.mul_mem ((Subgroup.mem_normalizer_iff.1 (hP₀nS hp) s).1 hs) (S.inv_mem hs)
    have hcommO : p * s * p⁻¹ * s⁻¹ ∈ O := htriv p hp s (hS.le hs)
    have hbot : p * s * p⁻¹ * s⁻¹ = 1 := by
      have hmem : p * s * p⁻¹ * s⁻¹ ∈ S ⊓ O := ⟨hcommS, hcommO⟩
      rw [hSO] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hconj : p * s * p⁻¹ = s := by
      have h1 : (p * s * p⁻¹) * s⁻¹ = 1 := hbot
      calc p * s * p⁻¹ = (p * s * p⁻¹) * s⁻¹ * s := by group
        _ = 1 * s := by rw [h1]
        _ = s := by group
    have hps : p * s = s * p := by
      calc p * s = (p * s * p⁻¹) * p := by group
        _ = s * p := by rw [hconj]
    exact hps.symm
  have hXR : X ≤ R := by rw [hR]; exact le_sup_right
  have hrelX : X.relIndex R = Nat.card O := by
    have h1 : X.relIndex R * Nat.card X = Nat.card R := by
      have h := Subgroup.relIndex_mul_card (H := X) (K := R)
      rwa [inf_eq_left.mpr hXR] at h
    have h2 : X.relIndex R * Nat.card X = Nat.card O * Nat.card X := by
      rw [h1, hcardR, hcardX]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hX_sylow_R : CFSG.ABGLocalTools.IsSylowOf 3 X R := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hXR, h.sylow.isPGroup, by rw [hrelX]; exact h3O⟩
  obtain ⟨k, hkR, hkconj⟩ := hS.exists_mem_conj hX_sylow_R
  have hO_HDM : O ≤ H ⊓ D.M := by
    rw [hO]
    refine le_inf inf_le_left (inf_le_right.trans ?_)
    rw [hQ]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 (L₁ ⊔ L₂)).trans (sup_le_M h)
  have hR_le : R ≤ H ⊓ D.M := by
    rw [hR]
    exact sup_le hO_HDM (le_inf hXH (X_le_M h))
  have hkHDM : k ∈ H ⊓ D.M := hR_le hkR
  set P : Subgroup G := P₀.map (MulAut.conj k).toMonoidHom with hP
  refine ⟨P, ?_, ?_⟩
  · have hPle : P ≤ H ⊓ D.M := by
      rw [hP]
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
      have hmem :=
        (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hkHDM) p).1 (hP₀.le hp)
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
    refine CFSG.ABGLocalTools.isSylowOf_of_card hPle ?_
    rw [hP, Subgroup.card_map_of_injective (MulAut.conj k).injective, hP₀.card_eq]
  · rw [hP]
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxS : k⁻¹ * x * k ∈ S := (hkconj x).mp hx
    have hcomm : (k⁻¹ * x * k) * p = p * (k⁻¹ * x * k) :=
      Subgroup.mem_centralizer_iff.mp (hP₀centS hp) (k⁻¹ * x * k) hxS
    have hgoal : x * (k * p * k⁻¹) = (k * p * k⁻¹) * x := by
      calc x * (k * p * k⁻¹) = k * ((k⁻¹ * x * k) * p) * k⁻¹ := by group
        _ = k * (p * (k⁻¹ * x * k)) * k⁻¹ := by rw [hcomm]
        _ = (k * p * k⁻¹) * x := by group
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hgoal

end Hyp141

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
