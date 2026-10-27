module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L63
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T613.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T613.Free

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T613

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem kOf_apply_inf_centralizer
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {a b : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1)
    (hne : Subgroup.zpowers a ≠ Subgroup.zpowers b) :
    kOf (θ a) ⊓ Subgroup.centralizer {b} =
      kOf (thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) := by
  have hEa := h.zpowers_mem_E1 ha ha1
  have hEb := h.zpowers_mem_E1 hb hb1
  have hbA : Subgroup.zpowers b ≤ A := hEb.1
  have hfree : ∀ J ∈ lcal (θ a), Subgroup.zpowers b ⊓ Subgroup.normalizer (J : Set G) ≤
      Subgroup.centralizer (J : Set G) := by
    intro J hJ
    have h1 : Subgroup.zpowers b ⊓ Subgroup.normalizer (J : Set G) ≤
        Subgroup.zpowers a ⊓ Subgroup.zpowers b := by
      refine le_inf ?_ inf_le_left
      calc Subgroup.zpowers b ⊓ Subgroup.normalizer (J : Set G)
          ≤ A ⊓ Subgroup.normalizer (J : Set G) := inf_le_inf_right _ hbA
        _ = Subgroup.zpowers a := inf_normalizer_eq_zpowers h hS ha ha1 hJ
    rw [h.inf_eq_bot_of_ne_E1 hEa hEb hne] at h1
    exact h1.trans bot_le
  have h1 := kOf_inf_centralizer_eq_kOf_of_free (h.kSetting_apply ha ha1) (kDown_eq_bot h ha ha1)
    hbA hfree
  rw [← h.isFunctor.inf_centralizer_eq_thetaOf ha ha1 hbA, ← centralizer_zpowers_eq_singleton b]
  exact h1

theorem kOf_apply_balance
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {a b : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1) :
    kOf (θ a) ⊓ Subgroup.centralizer {b} ≤ kOf (θ b) := by
  by_cases hab : Subgroup.zpowers a = Subgroup.zpowers b
  · rw [h.isFunctor.eq_of_zpowers_eq ha ha1 hb hb1 hab]
    exact inf_le_left
  · rw [kOf_apply_inf_centralizer h hS ha ha1 hb hb1 hab, sup_comm,
      ← kOf_apply_inf_centralizer h hS hb hb1 ha ha1 (Ne.symm hab)]
    exact inf_le_left

theorem isFunctor_kOf
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) :
    IsFunctor p A (fun x => kOf (θ x)) :=
  ⟨fun a ha ha1 => (kOf_le _).trans (h.isFunctor.le_centralizer a ha ha1),
    fun a ha ha1 => (h.isFunctor.coprime a ha ha1).coprime_dvd_right
      (Subgroup.card_dvd_of_le (kOf_le _)),
    fun a ha ha1 => le_normalizer_kOf_of_le_normalizer (h.isFunctor.normalized a ha ha1),
    fun _ ha ha1 _ hb hb1 => kOf_apply_balance h hS ha ha1 hb hb1⟩

theorem kOf_apply_eq
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) : kOf (θ a) = θ a := by
  have hfun := isFunctor_kOf h hS
  have hC : ∀ x ∈ A, x ≠ 1 → signalizerMcBrideHypothesisB p (kOf (θ x)) :=
    fun x hx hx1 => hypB_mono (kOf_le _) (h.hypC x hx hx1)
  by_contra hne
  have hlt : size A (fun x => kOf (θ x)) < size A θ :=
    size_lt_size (fun x hx hx1 => kOf_le _) ⟨a, ha, ha1, hne⟩
  obtain ⟨U, hU, hUmax⟩ := h.complete_of_size_lt
    ⟨h.prime, h.odd, h.elemAbelian, h.card, hfun, hC⟩ hlt
  have hUθ : U ∈ Msig p A θ := signalizers_mono_functor (fun x hx hx1 => kOf_le _) hU
  obtain ⟨b, hb, hb1, hbU⟩ := (h.lemma_6_3 hUθ).1
  exact hbU (hUmax _ (hfun.apply_mem_signalizers hb hb1 (hC b hb hb1)))

theorem kOf_thetaOf_zpowers
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) :
    kOf (thetaOf θ (Subgroup.zpowers a)) = thetaOf θ (Subgroup.zpowers a) := by
  rw [h.isFunctor.thetaOf_zpowers ha ha1]
  exact kOf_apply_eq h hS ha ha1

theorem kOf_thetaOf_sup
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {a b : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1)
    (hne : Subgroup.zpowers a ≠ Subgroup.zpowers b) :
    kOf (thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) =
      thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
  rw [← kOf_apply_inf_centralizer h hS ha ha1 hb hb1 hne, kOf_apply_eq h hS ha ha1,
    ← centralizer_zpowers_eq_singleton b,
    h.isFunctor.inf_centralizer_eq_thetaOf ha ha1 (h.zpowers_mem_E1 hb hb1).1]

theorem kOf_thetaOf_plane
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) : kOf (thetaOf θ B) = thetaOf θ B := by
  obtain ⟨⟨a, haB⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (h.ne_bot_of_mem_E2 hB)
  have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
  have haA : a ∈ A := hB.1 haB
  have hlt : ¬ B ≤ Subgroup.zpowers a := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [hB.2, h.card_zpowers haA ha1'] at h1
    have : p < p ^ 2 := by nlinarith [h.prime.one_lt]
    omega
  obtain ⟨b, hbB, hbna⟩ := IsConcreteLE.not_le_iff_exists.mp hlt
  have hb1 : b ≠ 1 := fun h' => hbna (h' ▸ one_mem _)
  have hbA : b ∈ A := hB.1 hbB
  have hne : Subgroup.zpowers a ≠ Subgroup.zpowers b := fun heq =>
    hbna (heq ▸ Subgroup.mem_zpowers b)
  have hsup := h.sup_mem_E2_of_ne (h.zpowers_mem_E1 haA ha1') (h.zpowers_mem_E1 hbA hb1) hne
  have hBeq : Subgroup.zpowers a ⊔ Subgroup.zpowers b = B :=
    Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr haB)
      (Subgroup.zpowers_le.mpr hbB)) (by rw [hB.2, hsup.2])
  rw [← hBeq]
  exact kOf_thetaOf_sup h hS haA ha1' hbA hb1 hne

theorem isDirectProduct_lcal
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) : IsDirectProduct (lcal (θ a)) (θ a) := by
  have := isDirectProduct_lcal_kOf (sol_eq_bot h ha ha1)
  rwa [kOf_apply_eq h hS ha ha1] at this

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T613
