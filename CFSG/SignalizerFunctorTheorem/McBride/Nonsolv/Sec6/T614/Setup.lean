module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L611
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L612
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L68
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L67
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L63
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T61.Geom
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T66

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E : Subgroup G}

structure Setting614 (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (E : Subgroup G) :
    Prop where
  mem : E ∈ signalizerFunctorEk p 1 A
  sSet_two : sSet p A θ 2 = {E}
  bN_eq : ∀ F ∈ signalizerFunctorEk p 1 A, bN A θ F = F ⊔ E
  card_E : Nat.card (lcal (thetaOf θ E)) = p ^ 2
  card_F : ∀ F ∈ signalizerFunctorEk p 1 A, F ≠ E → Nat.card (lcal (thetaOf θ F)) = p

theorem exists_setting614
    (h : Counterexample p A θ) (hS : (sSet p A θ 1).Nonempty) :
    ∃ E, Setting614 p A θ E := by
  rcases h.lemma_6_11 with hall | ⟨E, hE2, hunion, hN⟩
  · obtain ⟨F, hF⟩ := hS
    have hF2 : F ∈ sSet p A θ 2 := hall ▸ hF.1
    have e1 : Nat.card (lcal (thetaOf θ F)) = p ^ 1 := hF.2
    have e2 : Nat.card (lcal (thetaOf θ F)) = p ^ 2 := hF2.2
    have : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
    omega
  · have hEm : E ∈ sSet p A θ 2 := by rw [hE2]; rfl
    refine ⟨E, hEm.1, hE2, hN, hEm.2, fun F hF hFE => ?_⟩
    have hF' : F ∈ sSet p A θ 1 ∪ sSet p A θ 2 := hunion ▸ hF
    rcases hF' with h1 | h2
    · simpa using h1.2
    · rw [hE2] at h2
      exact absurd (Set.mem_singleton_iff.mp h2) hFE

theorem Setting614.exists_line_ne (S : Setting614 p A θ E) (h : Counterexample p A θ)
    (hS : (sSet p A θ 1).Nonempty) : ∃ F ∈ signalizerFunctorEk p 1 A, F ≠ E := by
  obtain ⟨F, hF⟩ := hS
  refine ⟨F, hF.1, fun hFE => ?_⟩
  have hF2 : F ∈ sSet p A θ 2 := by rw [S.sSet_two, hFE]; rfl
  have e1 : Nat.card (lcal (thetaOf θ F)) = p ^ 1 := hF.2
  have e2 : Nat.card (lcal (thetaOf θ F)) = p ^ 2 := hF2.2
  have : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
  omega

theorem Setting614.exists_complement (S : Setting614 p A θ E) (h : Counterexample p A θ)
    {a : G} (ha : a ∈ A) (haE : a ∉ E) :
    ∃ B ∈ signalizerFunctorEk p 2 A, E ⊓ B = ⊥ ∧ a ∈ B := by
  have ha1 : a ≠ 1 := fun e => haE (e ▸ E.one_mem)
  have hdisj : E ⊓ Subgroup.zpowers a = ⊥ :=
    inf_eq_bot_of_not_le h.prime (h.card_zpowers ha ha1)
      fun hle => haE (hle (Subgroup.mem_zpowers a))
  obtain ⟨B, hBA, haB, hEB, hsup⟩ := exists_complement_containing h.prime h.elemAbelian S.mem.1
    (Subgroup.zpowers_le.mpr ha) hdisj
  refine ⟨B, ⟨hBA, ?_⟩, hEB, haB (Subgroup.mem_zpowers a)⟩
  have hcard := card_mul_card_complement h.elemAbelian S.mem.1 hBA hEB hsup
  rw [S.mem.2, h.card, pow_one] at hcard
  exact Nat.eq_of_mul_eq_mul_left h.prime.pos (hcard.trans (by ring))

theorem Setting614.exists_complement_some (S : Setting614 p A θ E) (h : Counterexample p A θ) :
    ∃ B ∈ signalizerFunctorEk p 2 A, E ⊓ B = ⊥ := by
  have hex : ∃ a ∈ A, a ∉ E := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ E := fun a ha => hcon a ha
    have h1 := Subgroup.card_le_of_le hle
    rw [h.card, S.mem.2] at h1
    have h2 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
    omega
  obtain ⟨a, ha, haE⟩ := hex
  obtain ⟨B, hB, hEB, -⟩ := S.exists_complement h ha haE
  exact ⟨B, hB, hEB⟩

theorem Setting614.sup_eq (S : Setting614 p A θ E) (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥) : E ⊔ B = A := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le S.mem.1 hB.1) ?_
  rw [card_sup_of_le_elemAbelian h.elemAbelian S.mem.1 hB.1 hEB, S.mem.2, hB.2, h.card,
    ← pow_add]

theorem kDown_apply
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    kDown (θ a) A = ⊥ :=
  h.theorem_6_6_b (h.apply_mem_msig ha ha1) (thetaOf_le_apply ha ha1)

theorem sol_apply
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    sol (θ a) = ⊥ :=
  sol_eq_bot_of_kDown_eq_bot (h.kDown_apply ha ha1)

theorem inf_sup_eq_of_le (h : Counterexample p A θ) (hE : E ≤ A) {B R : Subgroup G}
    (hB : B ≤ A) (hEB : E ⊓ B = ⊥) (hR : R ≤ B) : B ⊓ (R ⊔ E) = R := by
  apply le_antisymm
  · rintro x ⟨hxB, hxRE⟩
    have hcomm : ∀ r ∈ R, ∀ y ∈ E, Commute r y := fun r hr y hy =>
      comm_of_mem_of_isMulCommutative h.elemAbelian.1 (hB (hR hr)) (hE hy)
    obtain ⟨r, hr, y, hy, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hxRE
    have hyB : y ∈ B := by
      have := mul_mem (inv_mem (hR hr)) hxB
      simpa using this
    have hy1 : y ∈ E ⊓ B := ⟨hy, hyB⟩
    rw [hEB, Subgroup.mem_bot] at hy1
    rw [hy1, mul_one]
    exact hr
  · exact le_inf hR le_sup_left

theorem exists_ne_one_of_mem_E2 (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) : ∃ b ∈ B, b ≠ 1 := by
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (h.ne_bot_of_mem_E2 hB)
  exact ⟨b, hb, fun e => hb1 (Subtype.ext e)⟩

theorem exists_basis (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    ∃ b' ∈ B, b' ∉ Subgroup.zpowers b ∧ Subgroup.zpowers b ⊔ Subgroup.zpowers b' = B := by
  by_cases hex : ∃ b' ∈ B, b' ∉ Subgroup.zpowers b
  · obtain ⟨b', hb', hnot⟩ := hex
    have hb'1 : b' ≠ 1 := fun e => hnot (e ▸ one_mem _)
    have hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers b' = ⊥ :=
      inf_eq_bot_of_not_le h.prime (h.card_zpowers (hB.1 hb') hb'1)
        fun hle => hnot (hle (Subgroup.mem_zpowers b'))
    have hE2 := h.zpowers_sup_mem_E2 (hB.1 hb) (hB.1 hb') hb1 hb'1 hdisj
    have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers b' ≤ B :=
      sup_le (Subgroup.zpowers_le.mpr hb) (Subgroup.zpowers_le.mpr hb')
    exact ⟨b', hb', hnot, Subgroup.eq_of_le_of_card_ge hle (by rw [hE2.2, hB.2])⟩
  · exfalso
    push Not at hex
    have hle : B ≤ Subgroup.zpowers b := fun x hx => hex x hx
    have h1 := Subgroup.card_le_of_le hle
    rw [hB.2, h.card_zpowers (hB.1 hb) hb1] at h1
    have h2 : p < p ^ 2 := by nlinarith [h.prime.one_lt]
    omega

omit [Finite G] in
theorem Setting614.bN_E (S : Setting614 p A θ E) : bN A θ E = E := by
  rw [S.bN_eq E S.mem, sup_idem]

theorem normalizes_of_mem_lcal_thetaOf
    (h : Counterexample p A θ) {B : Subgroup G}
    (hBA : B ≤ A) (hB : B ≠ ⊥) :
    ∀ x ∈ thetaOf θ B, ∀ J ∈ lcal (thetaOf θ B), x ∈ Subgroup.normalizer (J : Set G) :=
  normalizes_of_isPGroup_transitive_conj h.prime (IsPGroup.of_card h.card)
    (h.isFunctor.coprime_thetaOf hBA hB) (h.isFunctor.normalizes_thetaOf hBA)
    (fun _ hg _ hJ => map_conj_mem_lcal hJ
      ((sup_le Subgroup.le_normalizer (h.isFunctor.normalizes_thetaOf hBA)) hg))
    (fun _ hJ _ hK => h.exists_conj_eq_of_mem_lcal hBA hB hJ hK)

theorem thetaOf_inf_centralizer_le (h : Counterexample p A θ) {B E' : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) (hE' : E' ≤ A) :
    thetaOf θ B ⊓ Subgroup.centralizer (E' : Set G) ≤ thetaOf θ (B ⊔ E') := by
  rintro x ⟨hxB, hxE⟩
  rw [mem_thetaOf_iff]
  intro a ha ha1
  have hcomm : ∀ β ∈ B, ∀ ε ∈ E', Commute β ε := fun β hβ ε hε =>
    h.comm_of_mem_A (hBA hβ) (hE' hε)
  obtain ⟨β, hβ, ε, hε, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp ha
  have hxε : x * ε = ε * x := (Subgroup.mem_centralizer_iff.mp hxE ε hε).symm
  by_cases hβ1 : β = 1
  · subst hβ1
    rw [one_mul] at ha1 ⊢
    obtain ⟨⟨b', hb'⟩, hb'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
    have hb'1' : b' ≠ 1 := fun e => hb'1 (Subtype.ext e)
    refine h.isFunctor.balance b' (hBA hb') hb'1' ε (hE' hε) ha1
      ⟨mem_thetaOf_iff.mp hxB b' hb' hb'1', ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxε
  · have hxβ : x ∈ θ β := mem_thetaOf_iff.mp hxB β hβ hβ1
    refine h.isFunctor.balance β (hBA hβ) hβ1 (β * ε) (mul_mem (hBA hβ) (hE' hε)) ha1
      ⟨hxβ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hxβ' : x * β = β * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.isFunctor.le_centralizer β (hBA hβ) hβ1 hxβ)
    calc x * (β * ε) = (x * β) * ε := by group
      _ = (β * x) * ε := by rw [hxβ']
      _ = β * (x * ε) := by group
      _ = β * (ε * x) := by rw [hxε]
      _ = (β * ε) * x := by group

theorem eq_of_kOf_le_of_le
    (h : Counterexample p A θ) {θ' : G → Subgroup G}
    (hθ' : IsFunctor p A θ') (hlo : ∀ a ∈ A, a ≠ 1 → kOf (θ a) ≤ θ' a)
    (hhi : ∀ a ∈ A, a ≠ 1 → θ' a ≤ θ a) : ∀ a ∈ A, a ≠ 1 → θ' a = θ a := by
  intro a ha ha1
  have hC : ∀ x ∈ A, x ≠ 1 → signalizerMcBrideHypothesisB p (θ' x) :=
    fun x hx hx1 => hypB_mono (hhi x hx hx1) (h.hypC x hx hx1)
  by_contra hne
  have hlt : size A θ' < size A θ := size_lt_size hhi ⟨a, ha, ha1, hne⟩
  obtain ⟨U, hU, hUmax⟩ :=
    h.complete_of_size_lt ⟨h.prime, h.odd, h.elemAbelian, h.card, hθ', hC⟩ hlt
  have hUθ : U ∈ Msig p A θ := signalizers_mono_functor hhi hU
  obtain ⟨b, hb, hb1, hbU⟩ := (h.lemma_6_3 hUθ).1
  exact hbU ((hlo b hb hb1).trans (hUmax _ (hθ'.apply_mem_signalizers hb hb1 (hC b hb hb1))))

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
