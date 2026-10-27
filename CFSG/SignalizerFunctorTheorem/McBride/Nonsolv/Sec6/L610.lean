module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Types

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_max_apply (_h : Counterexample p A θ) (S : Set G) (hS : ∃ a ∈ S, a ∈ A ∧ a ≠ 1) :
    ∃ a ∈ S, a ∈ A ∧ a ≠ 1 ∧
      ∀ c ∈ S, c ∈ A → c ≠ 1 → Nat.card (θ c) ≤ Nat.card (θ a) := by
  obtain ⟨a, ⟨haS, haA, ha1⟩, hmax⟩ := Set.exists_max_image {a : G | a ∈ S ∧ a ∈ A ∧ a ≠ 1}
    (fun a => Nat.card (θ a)) (Set.toFinite _)
    (by obtain ⟨a, h1, h2, h3⟩ := hS; exact ⟨a, h1, h2, h3⟩)
  exact ⟨a, haS, haA, ha1, fun c hc hcA hc1 => hmax c ⟨hc, hcA, hc1⟩⟩

theorem sq_le_card_of_quot (h : Counterexample p A θ) {B : Subgroup G} {x : G} (hx : x ∈ A)
    (hB : B ≤ A) (hcyc : ∀ y ∈ A, ∃ k : ℤ, x ^ k * y⁻¹ ∈ B) : p ^ 2 ≤ Nat.card B := by
  have hC : B ⊔ Subgroup.zpowers x = A := by
    refine le_antisymm (sup_le hB (Subgroup.zpowers_le.mpr hx)) fun y hy => ?_
    obtain ⟨k, hk⟩ := hcyc y hy
    have hy' : y = (x ^ k * y⁻¹)⁻¹ * x ^ k := by group
    rw [hy']
    exact mul_mem (inv_mem (Subgroup.mem_sup_left hk))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers x k))
  have hprod := h.card_sup_mul_card_inf hB (Subgroup.zpowers_le.mpr hx)
  rw [hC, h.card] at hprod
  have hz : Nat.card (Subgroup.zpowers x) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd h.prime.pos (orderOf_dvd_of_pow_eq_one (h.elemAbelian.2 x hx))
  have hinf : 1 ≤ Nat.card ↥(B ⊓ Subgroup.zpowers x) := Nat.card_pos
  have h3 : p ^ 2 * p ≤ Nat.card B * p := by
    calc p ^ 2 * p = p ^ 3 := by ring
      _ ≤ p ^ 3 * Nat.card ↥(B ⊓ Subgroup.zpowers x) := Nat.le_mul_of_pos_right _ hinf
      _ = Nat.card B * Nat.card (Subgroup.zpowers x) := hprod
      _ ≤ Nat.card B * p := Nat.mul_le_mul_left _ hz
  exact Nat.le_of_mul_le_mul_right h3 h.prime.pos

theorem apply_le_apply_of_comm (h : Counterexample p A θ) {a r : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hr : r ∈ A) (hr1 : r ≠ 1) (hcomm : ∀ y ∈ θ a, r * y = y * r) : θ a ≤ θ r := fun y hy =>
  h.isFunctor.balance a ha ha1 r hr hr1 ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr
    (hcomm y hy).symm⟩

theorem exists_plane_containing (h : Counterexample p A θ) {R : Subgroup G} {t : G} (hR : R ≤ A)
    (hRc : p ^ 2 ≤ Nat.card R) (ht : t ∈ R) (ht1 : t ≠ 1) :
    ∃ T ∈ signalizerFunctorEk p 2 A, t ∈ T ∧ T ≤ R := by
  obtain ⟨T₀, hT₀R, hT₀c⟩ := exists_le_card_eq_pow h.prime (h.isElemAbelian_of_le hR) hRc
  by_cases htT : t ∈ T₀
  · exact ⟨T₀, ⟨hT₀R.trans hR, hT₀c⟩, htT, hT₀R⟩
  · have hne : ∃ e ∈ T₀, e ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : T₀ = ⊥ := (Subgroup.eq_bot_iff_forall T₀).2 hcon
      rw [this, Subgroup.card_bot] at hT₀c
      exact absurd hT₀c.symm (Nat.one_lt_pow (by norm_num) h.prime.one_lt).ne'
    obtain ⟨e, heT, he1⟩ := hne
    have hE : Subgroup.zpowers e ∈ signalizerFunctorEk p 1 A :=
      h.zpowers_mem_E1 (hT₀R.trans hR heT) he1
    have hEt : Subgroup.zpowers t ∈ signalizerFunctorEk p 1 A := h.zpowers_mem_E1 (hR ht) ht1
    have hne' : Subgroup.zpowers t ≠ Subgroup.zpowers e := by
      intro heq
      apply htT
      have : t ∈ Subgroup.zpowers e := heq ▸ Subgroup.mem_zpowers t
      exact (Subgroup.zpowers_le.mpr heT) this
    refine ⟨Subgroup.zpowers t ⊔ Subgroup.zpowers e, h.sup_mem_E2_of_ne hEt hE hne',
      Subgroup.mem_sup_left (Subgroup.mem_zpowers t), sup_le (Subgroup.zpowers_le.mpr ht)
        ((Subgroup.zpowers_le.mpr heT).trans hT₀R)⟩

theorem bN_eq_of_le
    (h : Counterexample p A θ) (h2 : ¬ (sSet p A θ 2).Nonempty)
    {F E : Subgroup G} (hF : F ∈ sSet p A θ 1) (hE : E ∈ signalizerFunctorEk p 1 A)
    (hEF : E ≤ bN A θ F) : E ∈ sSet p A θ 1 ∧ bN A θ E = bN A θ F := by
  have hF1 : F ∈ signalizerFunctorEk p 1 A := hF.1
  by_cases hEeq : E = F
  · subst hEeq
    exact ⟨hF, rfl⟩
  have hcF : Nat.card (lcal (thetaOf θ F)) = p := by simpa using hF.2
  by_cases hFE : F ≤ bN A θ E
  · have hcE : Nat.card (lcal (thetaOf θ E)) = p :=
      (h.lemma_6_9_g hE hF1 hFE hEF).trans hcF
    have hEs : E ∈ sSet p A θ 1 := ⟨hE, by rw [hcE, pow_one]⟩
    refine ⟨hEs, ?_⟩
    have hsup := h.sup_mem_E2_of_ne hE hF1 hEeq
    have e1 : bN A θ E = E ⊔ F := (Subgroup.eq_of_le_of_card_ge
      (sup_le (h.le_bN hE) hFE) (by rw [(h.mem_sSet_one_iff hE).mp hEs, hsup.2])).symm
    have e2 : bN A θ F = E ⊔ F := (Subgroup.eq_of_le_of_card_ge
      (sup_le hEF (h.le_bN hF1)) (by rw [(h.mem_sSet_one_iff hF1).mp hF, hsup.2])).symm
    rw [e1, e2]
  · exfalso
    exact h2 ⟨E, hE, by rw [h.lemma_6_9_f hE hF1 hFE hEF, hcF]; ring⟩

theorem isCompleteIn_of_apply_eq (h : Counterexample p A θ) {T : Subgroup G} (hTA : T ≤ A)
    (hT : p ^ 2 ≤ Nat.card T) {H : Subgroup G} (hH : H ∈ Msig p A θ)
    (hall : ∀ t ∈ T, t ≠ 1 → θ t ≤ H) : IsCompleteIn (Msig p A θ) :=
  ⟨H, hH, fun _ hZ => (le_thetaSup_of_mem_signalizers h.prime h.elemAbelian hTA hT hZ).trans
    (thetaSup_le hall)⟩

theorem lemma_6_10
    (h : Counterexample p A θ) : (sSet p A θ 2).Nonempty := by
  by_contra h2
  obtain ⟨a₀, ha₀, ha₀1⟩ := h.exists_ne_one
  by_cases h1 : (sSet p A θ 1).Nonempty
  ·
    obtain ⟨F₁, hF₁⟩ := h1
    have hF₁E : F₁ ∈ signalizerFunctorEk p 1 A := hF₁.1
    set B₀ := bN A θ F₁ with hB₀
    have hB₀c : Nat.card B₀ = p ^ 2 := (h.mem_sSet_one_iff hF₁E).mp hF₁
    have hB₀E : B₀ ∈ signalizerFunctorEk p 2 A := ⟨bN_le A θ F₁, hB₀c⟩
    have hS1 : ∀ L ∈ sSet p A θ 1, L ≤ B₀ := by
      intro L hL
      by_cases hLB : bN A θ L = B₀
      · exact (h.le_bN hL.1).trans hLB.le
      · have hLN : bN A θ L ∈ signalizerFunctorEk p 2 A :=
          ⟨bN_le A θ L, (h.mem_sSet_one_iff hL.1).mp hL⟩
        have hE' := h.inf_mem_E1_of_ne_E2 hLN hB₀E hLB
        have e1 := (h.bN_eq_of_le h2 hF₁ hE' (inf_le_right.trans le_rfl)).2
        have e2 := (h.bN_eq_of_le h2 hL hE' inf_le_left).2
        exact absurd (e2.symm.trans e1) hLB
    obtain ⟨t₀, ht₀A, ht₀B⟩ : ∃ t₀ ∈ A, t₀ ∉ B₀ := by
      by_contra hcon
      push Not at hcon
      have : A ≤ B₀ := hcon
      have := Subgroup.card_le_of_le this
      rw [h.card, hB₀c] at this
      have h3 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
      omega
    have ht₀1 : t₀ ≠ 1 := fun e => ht₀B (e ▸ B₀.one_mem)
    obtain ⟨t, htB, htA, ht1, hmax⟩ := h.exists_max_apply {a | a ∉ B₀} ⟨t₀, ht₀B, ht₀A, ht₀1⟩
    have htB' : t ∉ B₀ := htB
    set Ft := Subgroup.zpowers t with hFt
    have hFtE : Ft ∈ signalizerFunctorEk p 1 A := h.zpowers_mem_E1 htA ht1
    have hFt0 : Ft ∈ sSet p A θ 0 := by
      rcases h.line_cases hFtE with h0 | h1 | h2'
      · exact h0
      · exact absurd (hS1 Ft h1 (Subgroup.mem_zpowers t)) htB'
      · exact absurd ⟨Ft, h2'⟩ h2
    have hbN : bN A θ Ft = A := (h.mem_sSet_zero_iff hFtE).mp hFt0
    have hH : thetaOf θ Ft = θ t := h.thetaOf_line hFtE (Subgroup.mem_zpowers t) ht1
    have hR := (h.lemma_6_9_a hFtE.1 (h.ne_bot_of_mem_E1 hFtE)).1
    obtain ⟨x, hx, hxy⟩ := h.lemma_6_9_h hFtE.1 (h.ne_bot_of_mem_E1 hFtE)
    rw [hbN] at hx hxy
    have hRc : p ^ 2 ≤ Nat.card (bC A θ Ft) :=
      h.sq_le_card_of_quot hx (by rw [hR]; exact inf_le_left) hxy
    have hRA : bC A θ Ft ≤ A := by rw [hR]; exact inf_le_left
    have hcomm : ∀ r ∈ bC A θ Ft, ∀ y ∈ θ t, r * y = y * r := by
      intro r hr y hy
      rw [hR, hH] at hr
      exact (Subgroup.mem_centralizer_iff.mp hr.2 y hy).symm
    have htR : t ∈ bC A θ Ft := by
      rw [hR, hH]
      refine Subgroup.mem_inf.mpr ⟨htA, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp (h.isFunctor.le_centralizer t htA ht1 hy)
    obtain ⟨T, hTE, htT, hTR⟩ := h.exists_plane_containing hRA hRc htR ht1
    have hTB : T ≠ B₀ := fun e => htB' (e ▸ htT)
    have hEE := h.inf_mem_E1_of_ne_E2 hTE hB₀E hTB
    set E := T ⊓ B₀ with hEdef
    have hall : ∀ r ∈ T, r ≠ 1 → θ r ≤ thetaOf θ E := by
      intro r hrT hr1
      by_cases hrE : r ∈ E
      · rw [h.thetaOf_line hEE hrE hr1]
      · have hrB : r ∉ B₀ := fun hrB => hrE ⟨hrT, hrB⟩
        have hrA : r ∈ A := hTE.1 hrT
        have h1 : θ t ≤ θ r := h.apply_le_apply_of_comm htA ht1 hrA hr1
          (fun y hy => hcomm r (hTR hrT) y hy)
        have h2' : Nat.card (θ r) ≤ Nat.card (θ t) := hmax r hrB hrA hr1
        have h3 : θ r = θ t := (Subgroup.eq_of_le_of_card_ge h1 h2').symm
        rw [h3]
        rw [le_thetaOf_iff]
        intro e he he1
        exact h.apply_le_apply_of_comm htA ht1 (hEE.1 he) he1
          (fun y hy => hcomm e (hTR ((inf_le_left : T ⊓ B₀ ≤ T) he)) y hy)
    exact h.notComplete (h.isCompleteIn_of_apply_eq hTE.1 hTE.2.ge
      (h.thetaOf_mem_msig hEE.1 (h.ne_bot_of_mem_E1 hEE)) hall)
  ·
    obtain ⟨a, haS, haA, ha1, hmax⟩ := h.exists_max_apply Set.univ ⟨a₀, trivial, ha₀, ha₀1⟩
    set F := Subgroup.zpowers a with hF
    have hFE : F ∈ signalizerFunctorEk p 1 A := h.zpowers_mem_E1 haA ha1
    have hF0 : F ∈ sSet p A θ 0 := by
      rcases h.line_cases hFE with h0 | h1' | h2'
      · exact h0
      · exact absurd ⟨F, h1'⟩ h1
      · exact absurd ⟨F, h2'⟩ h2
    have hbN : bN A θ F = A := (h.mem_sSet_zero_iff hFE).mp hF0
    have hH : thetaOf θ F = θ a := h.thetaOf_line hFE (Subgroup.mem_zpowers a) ha1
    have hR := (h.lemma_6_9_a hFE.1 (h.ne_bot_of_mem_E1 hFE)).1
    obtain ⟨x, hx, hxy⟩ := h.lemma_6_9_h hFE.1 (h.ne_bot_of_mem_E1 hFE)
    rw [hbN] at hx hxy
    have hRA : bC A θ F ≤ A := by rw [hR]; exact inf_le_left
    have hRc : p ^ 2 ≤ Nat.card (bC A θ F) := h.sq_le_card_of_quot hx hRA hxy
    obtain ⟨T, hTR, hTc⟩ := exists_le_card_eq_pow h.prime (h.isElemAbelian_of_le hRA) hRc
    have hall : ∀ t ∈ T, t ≠ 1 → θ t ≤ θ a := by
      intro t htT ht1
      have htA : t ∈ A := hRA (hTR htT)
      have htR := hTR htT
      rw [hR, hH] at htR
      have h1 : θ a ≤ θ t := h.apply_le_apply_of_comm haA ha1 htA ht1
        (fun y hy => (Subgroup.mem_centralizer_iff.mp htR.2 y hy).symm)
      exact (Subgroup.eq_of_le_of_card_ge h1 (hmax t trivial htA ht1)).symm.le
    exact h.notComplete (h.isCompleteIn_of_apply_eq (hTR.trans hRA) hTc.ge
      (h.apply_mem_msig haA ha1) hall)

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
