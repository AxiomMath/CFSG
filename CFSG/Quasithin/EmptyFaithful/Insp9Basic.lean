module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Recognition.GoldschmidtTriple

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Insp9

variable {D : Type} [Group D] [Finite D]

structure Data (D₁ D₂ J N : Subgroup D) : Prop where
  amalgam : IsGoldschmidtAmalgam D₁ D₂
  le : J ≤ D₁
  pgrp : IsPGroup 2 ↥J
  norm : D₁ ≤ Subgroup.normalizer (J : Set D)
  comm : ⁅oTwoUpper D₂, J⁆ = oTwoUpper D₂
  eq : N = Subgroup.normalClosure (J : Set D)

variable {D₁ D₂ J N : Subgroup D}

omit [Finite D] in
theorem Data.normal (h : Data D₁ D₂ J N) : N.Normal := by
  rw [h.eq]
  exact Subgroup.normalClosure_normal

omit [Finite D] in
theorem Data.J_le_N (h : Data D₁ D₂ J N) : J ≤ N := by
  rw [h.eq]
  exact Subgroup.le_normalClosure

theorem Data.exists_orderOf_three (h : Data D₁ D₂ J N) :
    ∃ x : D, x ∈ D₂ ∧ orderOf x = 3 := by
  obtain ⟨e⟩ := h.amalgam.quotient₂
  have h6 : Nat.card (↥D₂ ⧸ Open.pCore 2 ↥D₂) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hdvd : 3 ∣ Nat.card ↥D₂ := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 ↥D₂)
    rw [h6] at this
    rw [this]
    exact Dvd.dvd.mul_right (by norm_num) _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨(x : D), x.2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hx

theorem Data.oTwoUpper_ne_bot (h : Data D₁ D₂ J N) : oTwoUpper D₂ ≠ ⊥ := by
  obtain ⟨x, hx, hxo⟩ := h.exists_orderOf_three
  intro hbot
  have hmem : x ∈ oTwoUpper D₂ := mem_oTwoUpper_of_odd hx (by rw [hxo]; decide)
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hxo
  exact absurd hxo (by norm_num)

theorem Data.J_ne_bot (h : Data D₁ D₂ J N) : J ≠ ⊥ := by
  intro hJ
  apply h.oTwoUpper_ne_bot
  rw [← h.comm, hJ]
  exact Subgroup.commutator_bot_right _

omit [Finite D] in
theorem Data.oTwoUpper_le_N (h : Data D₁ D₂ J N) : oTwoUpper D₂ ≤ N := by
  have := h.normal
  rw [← h.comm]
  exact (Subgroup.commutator_mono le_rfl h.J_le_N).trans (Subgroup.commutator_le_right _ _)

theorem Data.card_D₁ (h : Data D₁ D₂ J N) : Nat.card ↥D₁ = 3 * Nat.card ↥(D₁ ⊓ D₂) := by
  have h1 := h.amalgam.toIsGoldschmidtTriple.relIndex_inf_left
  have h2 := Subgroup.relIndex_mul_card (H := D₁ ⊓ D₂) (K := D₁)
  rw [h1, inf_eq_left.mpr inf_le_left] at h2
  exact h2.symm

theorem Data.sup_eq_top (h : Data D₁ D₂ J N) : N ⊔ D₁ = ⊤ := by
  have hN := h.normal
  set T : Subgroup D := D₁ ⊓ D₂ with hT
  set P : Subgroup D := oTwoUpper D₂ ⊔ T with hP
  have hTle : T ≤ D₂ := inf_le_right
  have hPle : P ≤ D₂ := sup_le (oTwoUpper_le D₂) hTle
  have hTP : T ≤ P := le_sup_right
  have h3 : T.relIndex D₂ = 3 := h.amalgam.toIsGoldschmidtTriple.relIndex_inf_right
  have hmul := Subgroup.relIndex_mul_relIndex T P D₂ hTP hPle
  rw [h3] at hmul
  have hPD : P.relIndex D₂ = 1 := by
    have hdvd : P.relIndex D₂ ∣ 3 := ⟨T.relIndex P, hmul.symm.trans (mul_comm _ _)⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
    · exact h1
    · exfalso
      rw [h3'] at hmul
      have hone : T.relIndex P = 1 := by omega
      have hPT : P ≤ T := Subgroup.relIndex_eq_one.mp hone
      obtain ⟨x, hx, hxo⟩ := h.exists_orderOf_three
      have hxo2 : x ∈ oTwoUpper D₂ := mem_oTwoUpper_of_odd hx (by rw [hxo]; decide)
      have hxT : x ∈ T := hPT ((le_sup_left : oTwoUpper D₂ ≤ P) hxo2)
      have hp := h.amalgam.toIsGoldschmidtTriple.isPGroup_inf
      obtain ⟨k, hk⟩ := hp ⟨x, hxT⟩
      have : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hd : 3 ∣ 2 ^ k := hxo ▸ orderOf_dvd_of_pow_eq_one this
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
      omega
  have hD2P : D₂ ≤ P := Subgroup.relIndex_eq_one.mp hPD
  have hD2M : D₂ ≤ N ⊔ D₁ :=
    hD2P.trans (sup_le (h.oTwoUpper_le_N.trans le_sup_left)
      (inf_le_left.trans le_sup_right))
  rw [eq_top_iff, ← h.amalgam.toIsGoldschmidtTriple.gen]
  exact sup_le le_sup_right hD2M

theorem Data.index_dvd (h : Data D₁ D₂ J N) : N.index ∣ Nat.card ↥D₁ := by
  have hN := h.normal
  have hsup := h.sup_eq_top
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp D₁.subtype) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ N ⊔ D₁ := by rw [hsup]; trivial
    obtain ⟨n, hn, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    refine ⟨⟨d, hd⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using hN.conj_mem n hn d⁻¹)
  have := Subgroup.card_dvd_of_surjective hsurj
  rwa [← Subgroup.index_eq_card] at this

end Insp9

end CFSG.Quasithin
