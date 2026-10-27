module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T613.KFunctor

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T613

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem diagSetting
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) : DiagSetting p A (θ a) where
  prime := h.prime
  elemAbelian := h.elemAbelian
  normalizes := h.isFunctor.normalized a ha ha1
  direct := isDirectProduct_lcal h hS ha ha1
  nonempty := lcal_nonempty h ha ha1
  transitive := fun _ hJ _ hJ' => exists_conj_eq h ha ha1 hJ hJ'

theorem zpowers_eq_inf_normalizer
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) : ∀ J ∈ lcal (θ a),
      Subgroup.zpowers a = A ⊓ Subgroup.normalizer (J : Set G) :=
  fun _ hJ => (inf_normalizer_eq_zpowers h hS ha ha1 hJ).symm

theorem sup_inf_sup_eq (h : Counterexample p A θ) {a b d : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) (hd : d ∈ A) (hd1 : d ≠ 1) {B : Subgroup G} (hbB : b ∈ B)
    (hdB : d ∈ B) (haB : a ∉ B) (hdb : d ∉ Subgroup.zpowers b) :
    (Subgroup.zpowers a ⊔ Subgroup.zpowers d) ⊓ (Subgroup.zpowers b ⊔ Subgroup.zpowers d) =
      Subgroup.zpowers d := by
  have hEa := h.zpowers_mem_E1 ha ha1
  have hEb := h.zpowers_mem_E1 hb hb1
  have hEd := h.zpowers_mem_E1 hd hd1
  have hdB' : Subgroup.zpowers d ≤ B := Subgroup.zpowers_le.mpr hdB
  have had : Subgroup.zpowers a ≠ Subgroup.zpowers d := fun heq =>
    haB (hdB' (heq ▸ Subgroup.mem_zpowers a))
  have hbd : Subgroup.zpowers b ≠ Subgroup.zpowers d := fun heq =>
    hdb (heq ▸ Subgroup.mem_zpowers d)
  have hP₁ := h.sup_mem_E2_of_ne hEa hEd had
  have hP₂ := h.sup_mem_E2_of_ne hEb hEd hbd
  have hne : Subgroup.zpowers a ⊔ Subgroup.zpowers d ≠ Subgroup.zpowers b ⊔ Subgroup.zpowers d := by
    intro heq
    have haP : a ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers d :=
      heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    exact haB (sup_le (Subgroup.zpowers_le.mpr hbB) hdB' haP)
  have hline := h.inf_mem_E1_of_ne_E2 hP₁ hP₂ hne
  exact (Subgroup.eq_of_le_of_card_ge (le_inf le_sup_right le_sup_right)
    (by rw [hline.2, hEd.2])).symm

theorem exists_plane (h : Counterexample p A θ) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) (hne : Subgroup.zpowers a ≠ Subgroup.zpowers b) :
    ∃ B : Subgroup G, B ≤ A ∧ b ∈ B ∧ a ∉ B ∧ Nat.card B = p ^ 2 := by
  have hEa := h.zpowers_mem_E1 ha ha1
  have hEb := h.zpowers_mem_E1 hb hb1
  obtain ⟨F, hFA, hbF, hEF, hsup⟩ := exists_complement_containing h.prime h.elemAbelian
    (E := Subgroup.zpowers a) (R := Subgroup.zpowers b) hEa.1 hEb.1
    (h.inf_eq_bot_of_ne_E1 hEa hEb hne)
  have hcard := card_mul_card_complement h.elemAbelian hEa.1 hFA hEF hsup
  rw [hEa.2, h.card, pow_one] at hcard
  refine ⟨F, hFA, hbF (Subgroup.mem_zpowers b), fun haF => ha1 ?_, ?_⟩
  · have : a ∈ Subgroup.zpowers a ⊓ F := ⟨Subgroup.mem_zpowers a, haF⟩
    rw [hEF] at this
    exact Subgroup.mem_bot.mp this
  · exact Nat.eq_of_mul_eq_mul_left h.prime.pos (hcard.trans (by ring))

theorem maximal_apply
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) : Maximal (· ∈ Msig p A θ) (θ a) := by
  refine ⟨h.apply_mem_msig ha ha1, fun X hX hHX => ?_⟩
  by_contra hXH
  obtain ⟨b, hb, hb1, hbX⟩ : ∃ b ∈ A, b ≠ 1 ∧ ¬ X ⊓ Subgroup.centralizer {b} ≤ θ a := by
    by_contra hcon
    push Not at hcon
    refine hXH ?_
    calc X = ⨆ (b : G) (_ : b ∈ A) (_ : b ≠ 1), X ⊓ Subgroup.centralizer {b} :=
          (iSup_inf_centralizer h.prime h.elemAbelian h.rank_two_le hX.1 hX.2.1).symm
      _ ≤ θ a := iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => hcon b hb hb1
  have hEb := h.zpowers_mem_E1 hb hb1
  have hbA : Subgroup.zpowers b ≤ A := hEb.1
  have hne : Subgroup.zpowers a ≠ Subgroup.zpowers b := by
    intro heq
    refine hbX ?_
    rw [h.isFunctor.eq_of_zpowers_eq ha ha1 hb hb1 heq]
    exact hX.2.2.1 b hb hb1
  have haN : a ∉ Subgroup.zpowers b := fun hmem =>
    hne (h.line_eq_zpowers hEb hmem ha1).symm
  have hAY : A ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer {b} : Subgroup G) : Set G) := by
    have := (inf_centralizer_mem_signalizers hX hbA h.elemAbelian.1
      fun Y hYX _ hP => hypB_mono hYX hP).1
    rwa [centralizer_zpowers_eq_singleton] at this
  have hcomm := h.isFunctor.inf_centralizer_comm ha ha1 hb hb1
  have hHb : θ b ≤ X := by
    rcases (diagSetting h hS hb hb1).eq_or_eq_top (zpowers_eq_inf_normalizer h hS hb hb1) ha haN
        (Y := X ⊓ Subgroup.centralizer {b}) (hX.2.2.1 b hb hb1)
        (by rw [← hcomm]; exact inf_le_inf_right _ hHX) hAY with h1 | h1
    · refine absurd ?_ hbX
      rw [h1, ← hcomm]
      exact inf_le_left
    · exact h1 ▸ inf_le_left
  obtain ⟨B, hBA, hbB, haB, hBcard⟩ := exists_plane h ha ha1 hb hb1 hne
  have hall : ∀ d ∈ B, d ≠ 1 → θ d ≤ X := by
    intro d hd hd1
    have hdA : d ∈ A := hBA hd
    by_cases hdb : d ∈ Subgroup.zpowers b
    · rw [← h.isFunctor.eq_of_zpowers_eq hb hb1 hdA hd1 (h.line_eq_zpowers hEb hdb hd1)]
      exact hHb
    · have hEd := h.zpowers_mem_E1 hdA hd1
      have haNd : a ∉ Subgroup.zpowers d := fun hmem => haB (Subgroup.zpowers_le.mpr hd hmem)
      have hbNd : b ∉ Subgroup.zpowers d := fun hmem =>
        hdb (h.line_eq_zpowers hEd hmem hb1 ▸ Subgroup.mem_zpowers d)
      have h1 := (diagSetting h hS hdA hd1).sup_eq_top (zpowers_eq_inf_normalizer h hS hdA hd1)
        ha hb haNd hbNd (sup_inf_sup_eq h ha ha1 hb hb1 hdA hd1 hbB hd haB hdb)
      exact h1.ge.trans (sup_le
        (((h.isFunctor.inf_centralizer_comm hdA hd1 ha ha1).le.trans inf_le_left).trans hHX)
        (((h.isFunctor.inf_centralizer_comm hdA hd1 hb hb1).le.trans inf_le_left).trans hHb))
  obtain ⟨d, hdB, hd1, hdX⟩ := exists_apply_not_le_of_mem h.prime h.elemAbelian h.notComplete hBA
    (by rw [hBcard]) hX
  exact hdX (hall d hdB hd1)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T613
