module

public import CFSG.RankThree.PartOne.S12.BaseNodes

public section

namespace CFSG.RankThree.PartOne

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

omit [Finite G] in
theorem torusNormalizer_le_cNormalizer_of_invariant
    (h : torusInvariant E ⊤ (Subgroup.zpowers c)) : torusNormalizer E ≤ cNormalizer c := by
  intro w hw
  rw [cNormalizer, Subgroup.mem_normalizer_iff]
  intro x
  have hw' : w⁻¹ ∈ torusNormalizer E := inv_mem hw
  refine ⟨fun hx => h w ⟨Subgroup.mem_top w, hw⟩ x hx, fun hx => ?_⟩
  have := h w⁻¹ ⟨Subgroup.mem_top _, hw'⟩ _ hx
  simpa [mul_assoc] using this

theorem sec126_a (h124 : Node124) (h125 : Node125) (h : Sec12Hyp G p A c L E)
    (hirr : ¬ torusIrreducible E) :
    torusInvariant E ⊤ ⁅E, L ⊓ torusNormalizer E⁆ ∧ ⁅E, L ⊓ torusNormalizer E⁆ ≠ ⊥ ∧
      ⁅E, L ⊓ torusNormalizer E⁆ ≠ E ∧ ⁅E, L ⊓ torusNormalizer E⁆ ≤ E ∧
      E = Subgroup.zpowers c ⊔ ⁅E, L ⊓ torusNormalizer E⁆ ∧
      Subgroup.zpowers c ⊓ ⁅E, L ⊓ torusNormalizer E⁆ = ⊥ := by
  unfold torusIrreducible at hirr
  push Not at hirr
  obtain ⟨B, hBE, hBinv, hB1, hB2⟩ := hirr
  have hBL : torusInvariant E L B := fun w hw => hBinv w ⟨Subgroup.mem_top w, hw.2⟩
  obtain ⟨h1, h2⟩ := h124 G p A c L E h
  have hB : B = ⁅E, L ⊓ torusNormalizer E⁆ := by
    rcases h1 B hBE hBL hB1 hB2 with hBc | hBc
    · exact absurd (torusNormalizer_le_cNormalizer_of_invariant (hBc ▸ hBinv)) (h125 G p A c L E h)
    · exact hBc
  subst hB
  rcases h2 with ⟨hdec, hmeet⟩ | ⟨-, hEE⟩
  · exact ⟨hBinv, hB1, hB2, hBE, hdec, hmeet⟩
  · exact absurd hEE hB2

theorem sec126_c_irredL (h124 : Node124) (h : Sec12Hyp G p A c L E)
    (hmeet : Subgroup.zpowers c ⊓ ⁅E, L ⊓ torusNormalizer E⁆ = ⊥)
    (hBE : ⁅E, L ⊓ torusNormalizer E⁆ ≤ E) (hBE' : ⁅E, L ⊓ torusNormalizer E⁆ ≠ E)
    {B' : Subgroup G} (hle : B' ≤ ⁅E, L ⊓ torusNormalizer E⁆) (hBL : torusInvariant E L B') :
    B' = ⊥ ∨ B' = ⁅E, L ⊓ torusNormalizer E⁆ := by
  by_contra hcon
  push Not at hcon
  have hB'E : B' ≠ E := fun h1 => hBE' (le_antisymm hBE (h1 ▸ hle))
  rcases (h124 G p A c L E h).1 B' (hle.trans hBE) hBL hcon.1 hB'E with hc | hc
  · have hcB : c ∈ ⁅E, L ⊓ torusNormalizer E⁆ := hle (hc ▸ Subgroup.mem_zpowers c)
    have : c ∈ Subgroup.zpowers c ⊓ ⁅E, L ⊓ torusNormalizer E⁆ :=
      ⟨Subgroup.mem_zpowers c, hcB⟩
    rw [hmeet, Subgroup.mem_bot] at this
    exact h.c_ne_one this
  · exact hcon.2 hc

theorem sec126_c_irred (h124 : Node124) (h : Sec12Hyp G p A c L E)
    (hmeet : Subgroup.zpowers c ⊓ ⁅E, L ⊓ torusNormalizer E⁆ = ⊥)
    (hBE : ⁅E, L ⊓ torusNormalizer E⁆ ≤ E) (hBE' : ⁅E, L ⊓ torusNormalizer E⁆ ≠ E)
    {B' : Subgroup G} (hle : B' ≤ ⁅E, L ⊓ torusNormalizer E⁆) (hinv : torusInvariant E ⊤ B') :
    B' = ⊥ ∨ B' = ⁅E, L ⊓ torusNormalizer E⁆ :=
  sec126_c_irredL h124 h hmeet hBE hBE' hle fun w hw => hinv w ⟨Subgroup.mem_top w, hw.2⟩

theorem sec126_d_no_complement (h124 : Node124) (h125 : Node125) (h : Sec12Hyp G p A c L E)
    (hB1 : ⁅E, L ⊓ torusNormalizer E⁆ ≠ ⊥) (hBE' : ⁅E, L ⊓ torusNormalizer E⁆ ≠ E)
    (hBE : ⁅E, L ⊓ torusNormalizer E⁆ ≤ E) {C : Subgroup G} (hCE : C ≤ E)
    (hCinv : torusInvariant E ⊤ C) (hCB : C ⊓ ⁅E, L ⊓ torusNormalizer E⁆ = ⊥)
    (hsup : C ⊔ ⁅E, L ⊓ torusNormalizer E⁆ = E) : False := by
  have hCL : torusInvariant E L C := fun w hw => hCinv w ⟨Subgroup.mem_top w, hw.2⟩
  have hC1 : C ≠ ⊥ := fun h1 => hBE' (by rw [h1, bot_sup_eq] at hsup; exact hsup)
  have hC2 : C ≠ E := fun h1 => hB1 (by
    rw [h1] at hCB
    simpa [inf_eq_right.mpr hBE] using hCB)
  rcases (h124 G p A c L E h).1 C hCE hCL hC1 hC2 with hc | hc
  · exact h125 G p A c L E h (torusNormalizer_le_cNormalizer_of_invariant (hc ▸ hCinv))
  · rw [hc, inf_idem] at hCB
    exact hB1 hCB

end CFSG.RankThree.PartOne
