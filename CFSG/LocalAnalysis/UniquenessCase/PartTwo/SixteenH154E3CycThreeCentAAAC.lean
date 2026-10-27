module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycThreeCentAAAB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ZpFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Seventeen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_CycThreeCentAAAC_zpRow {W : Type} [CommGroup W]
    {A L : Subgroup (MulAut W)} {t : MulAut W} {p : ℕ}
    (hp : p.Prime) (hL : Nat.card ↥L = p) (h : Conc4_133 A t L) :
    s16h_ZpRow p (rk ↥(commSub (⊤ : Subgroup W) L)) := by
  obtain ⟨q, -, -, -, -, hrows⟩ := h
  unfold s16h_ZpRow
  rcases hrows with ⟨hcyc, hr⟩ | ⟨hcyc, hr⟩ | ⟨hP, hr⟩ | ⟨hE, hr, -, -⟩ | ⟨hcyc, hr⟩ |
    ⟨r, m, -, hr2, hE, -, -⟩ | ⟨hE, hr, -⟩
  · exact Or.inl ⟨hL.symm.trans hcyc.2, hr⟩
  · exact Or.inr (Or.inl ⟨hL.symm.trans hcyc.2, hr⟩)
  · exfalso
    have h3p : 3 ^ 3 = p := hP.2.1.symm.trans hL
    exact absurd (hp.pow_eq_iff.mp h3p).2 (by norm_num)
  · exfalso
    have h32p : 3 ^ 2 = p := (s16h_dc_card_of_elem hE).symm.trans hL
    exact absurd (hp.pow_eq_iff.mp h32p).2 (by norm_num)
  · exact Or.inr (Or.inr ⟨hL.symm.trans hcyc.2, hr⟩)
  · exfalso
    have hqp : q ^ r = p := (s16h_dc_card_of_elem hE).symm.trans hL
    have hr1 : r = 1 := (hp.pow_eq_iff.mp hqp).2
    omega
  · exfalso
    have h32p : 3 ^ 2 = p := (s16h_dc_card_of_elem hE).symm.trans hL
    exact absurd (hp.pow_eq_iff.mp h32p).2 (by norm_num)

theorem s16h_e3_cyc_rank_one_wTil
    (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p) (hp3 : p ≠ 3)
    (hn76 : ¬ (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6))
    {B : Subgroup (MulAut (Vtil V₀ V hV))} (hBM : B ≤ Mbar D.M V₀ V hV)
    (hB : IsElemAbelian 3 B) (hBW : B ≤ stabSub (wTil V₀ V hV L)) :
    Nat.card ↥B ≤ 3 * Nat.card ↥(B ⊓ centSub (wTil V₀ V hV L)) := by
  have hc' := hc
  obtain ⟨t, -, -, -, -, hW⟩ := hc
  have h133 : Conc4_133 (Mbar D.M V₀ V hV) t (lBar V₀ V hV L) :=
    s16h_conc4_133_of_prime_card hp hLp.2 hW
  have hrow : s16h_ZpRow p (rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))) :=
    s16h_e3_CycThreeCentAAAC_zpRow hp hLp.2 h133
  have hp2 : p ≠ 2 := by
    rcases hrow with ⟨h3, -⟩ | ⟨h5, -⟩ | ⟨h7, -⟩
    · omega
    · omega
    · omega
  have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by
    rw [hLp.2]
    exact hp.odd_of_ne_two hp2
  have hfix : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
      fixV (lBar V₀ V hV L) = ⊥ :=
    s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd
  have hbb : s16h_BlockBound (Mbar D.M V₀ V hV) (lBar V₀ V hV L) 3 1 :=
    s16h_blockBound_one_of_cyclic (W := Vtil V₀ V hV) (p := p) (q := 3)
      (s15_Infra_vtil_sq_eq_one V₀ V hV) hp Nat.prime_three hp2 (by norm_num)
      (Ne.symm hp3) hLp.1 hLp.2 hfix hrow (by
        rintro ⟨hp7, hrk6, -⟩
        exact hn76 ⟨hp7, hrk6⟩)
  have hBnorm : B ≤ Subgroup.normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) := by
    intro φ hφ
    exact s16h_e3_cyc_stab_wTil_le_normalizer D hV h hc' hp hLp (hBM hφ) (hBW hφ)
  have hmain := hbb B (le_inf hBM hBnorm) hB
  rw [show commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) = wTil V₀ V hV L from rfl]
    at hmain
  exact hmain

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
