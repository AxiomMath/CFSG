module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NIndStep

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open CFSG

@[expose] def NBaseAb : Prop := ∀ (G : Type) [Group G] [Finite G] (Q L : Subgroup G) (b : G),
  NHyp Q L b → (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) → NLeast Q L →
    Q ≤ Subgroup.centralizer (L : Set G)

@[expose] def NBaseNab : Prop := ∀ (G : Type) [Group G] [Finite G] (Q L : Subgroup G) (b : G),
  NHyp Q L b → (∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x) → NLeast Q L →
    Q ≤ Subgroup.centralizer (L : Set G)

theorem lemmaN_of_bases (hA : NBaseAb) (hN : NBaseNab) {G : Type} [Group G] [Finite G]
    {Q L : Subgroup G} {b : G} (h : NHyp Q L b) : Q ≤ Subgroup.centralizer (L : Set G) := by
  suffices key : ∀ n, ∀ (G : Type) [Group G] [Finite G] (Q L : Subgroup G) (b : G),
      Nat.card Q = n → NHyp Q L b → Q ≤ Subgroup.centralizer (L : Set G) from
    key _ G Q L b rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ Q L b hn h
  by_cases hmin : NLeast Q L
  · by_cases hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x
    · exact hA G Q L b h hab hmin
    · push_neg at hab
      exact hN G Q L b h hab hmin
  · unfold NLeast at hmin
    push_neg at hmin
    obtain ⟨R, hRQ, hRQn, hRLn, hR1, hRne⟩ := hmin
    have hRlt : Nat.card R < Nat.card Q :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hRQ hRne)
    have hRh : NHyp R L b :=
      { kgroup := h.kgroup.of_injective CFSG.Assembly.inCatalog_isoInvariant
          (Subgroup.inclusion hRQ) (Subgroup.inclusion_injective hRQ)
        iso := h.iso
        normalizes := Subgroup.le_normalizer_iff.mpr hRLn
        coprime := h.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hRQ)
        mem := h.mem
        order := h.order
        cent := fun x hx => h.cent ⟨hRQ hx.1, hx.2⟩ }
    have hRC : R ≤ Subgroup.centralizer (L : Set G) :=
      ih _ (hn ▸ hRlt) G R L b rfl hRh
    have hcomm := comm_mem_of_ih h hRQ hRQn hRLn hR1 (fun G' _ _ Q' L' b' hlt hh =>
      ih _ (hn ▸ hlt) G' Q' L' b' rfl hh)
    have hLQ : ⁅L, Q⁆ ≤ R := by
      rw [Subgroup.commutator_le]
      intro l hl x hx
      have := R.inv_mem (hcomm x hx l hl)
      simpa [commutatorElement_def, mul_assoc] using this
    have h1 : ⁅⁅L, Q⁆, L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hLQ.trans hRC)
    have h2 : ⁅⁅Q, L⁆, L⁆ = ⊥ := by rwa [Subgroup.commutator_comm Q L]
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    obtain ⟨e⟩ := h.iso
    rw [commutator_self_of_iso e] at h3
    rw [Subgroup.commutator_comm] at h3
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN
