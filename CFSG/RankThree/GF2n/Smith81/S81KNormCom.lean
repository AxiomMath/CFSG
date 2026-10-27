module

public import CFSG.RankThree.GF2n.Smith81.S81E7Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.D6Normalizer

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley
  CFSG.RankThree.GF2n.Smith81.E7Model


abbrev rootK (k : Fin 126) : Fin (Tag.rank .E7) → ℤ := (Tag.rootCertificate .E7).root k

@[expose] def PosK (k : Fin 126) : Prop :=
  MinData.toWeight (rootK k) ⬝ᵥ theta = 0 ∧ 0 < height (τ := .E7) (rootK k)

instance (k : Fin 126) : Decidable (PosK k) := by unfold PosK; infer_instance

@[expose] def RelK (b c : Fin e7Data.d) : Prop :=
  ∃ k : Fin 126, PosK k ∧ pr b (rootK k) = -1 ∧
    e7Data.wt c = e7Data.wt b + MinData.toWeight (rootK k)

instance (b c : Fin e7Data.d) : Decidable (RelK b c) := by unfold RelK; infer_instance

@[expose] def tb (m : List ℕ) (b c : ℕ) : Bool := (m.getD b 0).testBit c

@[expose] def relTab : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, 0, 768, 0, 2816, 2816, 0, 25344, 19200, 0, 92416, 205568, 150272,
    616960, 1714432, 3220224, 13773312, 10174720, 27797760, 106119680, 190851584, 220807424,
    382355456, 1902199296, 1303511296, 2530811904, 8194115584, 13743817216, 0, 57600974848,
    114531895296, 0, 919853867008, 669278945280, 0, 6972159098880, 0, 25077450539008, 0,
    95510178299904, 0, 0, 0, 0, 0, 0, 0]

@[expose] def ltTab : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, 0, 768, 0, 2816, 2816, 0, 27392, 19200, 0, 92928, 224000, 150272,
    617216, 1796864, 3369728, 14379776, 10185472, 29059840, 115043072, 201026304, 230386432,
    383478528, 2147183360, 1304128256, 2530962176, 8589634304, 15032085248, 0, 60129241856,
    120258784000, 0, 962072374016, 670014597888, 0, 7559142140672, 0, 25151328185088, 0,
    95520072362752, 0, 0, 0, 0, 0, 0, 0]

@[expose] def ltB (b c : Fin e7Data.d) : Bool := tb ltTab b c

theorem relTab_spec : ∀ b c : Fin e7Data.d, pr b theta = 0 →
    (tb relTab b c = true ↔ RelK b c) := by
  unfold pr RelK PosK tb relTab
  decide +kernel

theorem rel_le_lt : ∀ b c : Fin e7Data.d, tb relTab b c = true → ltB b c = true := by
  unfold ltB tb relTab ltTab
  decide +kernel

theorem lt_trans' : ∀ b c d : Fin e7Data.d, ltB b c = true → ltB c d = true → ltB b d = true := by
  unfold ltB tb ltTab
  decide +kernel

theorem lt_first : ∀ b c : Fin e7Data.d, ltB b c = true →
    ∃ d : Fin e7Data.d, tb relTab b d = true ∧ (d = c ∨ ltB d c = true) := by
  unfold ltB tb relTab ltTab
  decide +kernel

theorem lt_idx0 : ∀ b c : Fin e7Data.d, ltB b c = true → pr b theta = 0 ∧ pr c theta = 0 := by
  unfold ltB tb ltTab pr
  decide +kernel

@[expose] def cntUp (b : Fin e7Data.d) : ℕ :=
  (Finset.univ.filter fun c : Fin e7Data.d => ltB b c = true).card

@[expose] def cntDown (b : Fin e7Data.d) : ℕ :=
  (Finset.univ.filter fun c : Fin e7Data.d => ltB c b = true).card

theorem inv_injective : ∀ b c : Fin e7Data.d, pr b theta = 0 → pr c theta = 0 →
    cntUp b = cntUp c → cntDown b = cntDown c → b = c := by
  unfold cntUp cntDown ltB tb ltTab pr
  decide +kernel

theorem cntUp_lt : ∀ b d : Fin e7Data.d, ltB b d = true → cntUp d < cntUp b := by
  unfold cntUp ltB tb ltTab
  decide +kernel


theorem cntDown_lt_of_lt : ∀ b d : Fin e7Data.d, ltB b d = true → cntDown b < cntDown d := by
  unfold cntDown ltB tb ltTab
  decide +kernel

theorem cntDown_lt_32 : ∀ c : Fin e7Data.d, cntDown c < 32 := by
  unfold cntDown ltB tb ltTab
  decide +kernel

theorem lt_mono_of_edges (σ : Fin e7Data.d → Fin e7Data.d)
    (hmono : ∀ b c : Fin e7Data.d, tb relTab b c = true → ltB (σ b) (σ c) = true) :
    ∀ b c : Fin e7Data.d, ltB b c = true → ltB (σ b) (σ c) = true := by
  intro b
  induction h : cntUp b using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    intro c hbc
    obtain ⟨d, hd, hdc⟩ := lt_first b c hbc
    have h1 := hmono b d hd
    rcases hdc with rfl | hdc
    · exact h1
    · have hlt : cntUp d < n := h ▸ cntUp_lt b d (rel_le_lt b d hd)
      exact lt_trans' _ _ _ h1 (ih _ hlt d rfl c hdc)

theorem eq_self_of_mono (σ : Fin e7Data.d → Fin e7Data.d)
    (hσ : ∀ b, pr b theta = 0 → pr (σ b) theta = 0)
    (hinj : ∀ b c, pr b theta = 0 → pr c theta = 0 → σ b = σ c → b = c)
    (hmono : ∀ b c : Fin e7Data.d, tb relTab b c = true → ltB (σ b) (σ c) = true) :
    ∀ b, pr b theta = 0 → σ b = b := by
  classical
  have hlt := lt_mono_of_edges σ hmono
  have hmem : ∀ b, b ∈ idx0 ↔ pr b theta = 0 := fun b => mem_idx0
  have hinjOn : Set.InjOn σ (idx0 : Set (Fin e7Data.d)) := fun b hb c hc h =>
    hinj b c ((hmem b).1 hb) ((hmem c).1 hc) h
  have himg : idx0.image σ = idx0 := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
      exact (hmem _).2 (hσ b ((hmem b).1 hb))
    · rw [Finset.card_image_of_injOn hinjOn]
  have hsum : ∀ f : Fin e7Data.d → ℕ, (∑ b ∈ idx0, f (σ b)) = ∑ b ∈ idx0, f b := by
    intro f
    rw [← Finset.sum_image (f := f) (g := σ) hinjOn, himg]
  have hup : ∀ b ∈ idx0, cntUp b ≤ cntUp (σ b) := by
    intro b hb
    apply Finset.card_le_card_of_injOn σ
    · intro c hc
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hc ⊢
      exact hlt b c hc
    · intro c hc c' hc' h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hc hc'
      exact hinj c c' (lt_idx0 b c hc).2 (lt_idx0 b c' hc').2 h
  have hdown : ∀ b ∈ idx0, cntDown b ≤ cntDown (σ b) := by
    intro b hb
    apply Finset.card_le_card_of_injOn σ
    · intro c hc
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hc ⊢
      exact hlt c b hc
    · intro c hc c' hc' h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hc hc'
      exact hinj c c' (lt_idx0 c b hc).1 (lt_idx0 c' b hc').1 h
  have hup' := (Finset.sum_eq_sum_iff_of_le hup).1 (hsum cntUp).symm
  have hdown' := (Finset.sum_eq_sum_iff_of_le hdown).1 (hsum cntDown).symm
  intro b hb
  have hbI : b ∈ idx0 := (hmem b).2 hb
  exact (inv_injective (σ b) b (hσ b hb) hb (hup' b hbI).symm (hdown' b hbI).symm)

end CFSG.RankThree.GF2n.Smith81.D6Normalizer
