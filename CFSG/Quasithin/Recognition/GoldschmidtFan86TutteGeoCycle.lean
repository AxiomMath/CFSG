module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteGeoPow

public section

namespace CFSG.Quasithin.Fan86.Tutte.Geo

open CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.Fan86.Tutte.Red

variable {W : Type} {Γ : SimpleGraph W} {H : Type} [Group H] [MulAction H W] {s : ℕ}

namespace RegData

variable (R : RegData Γ H s) {a : Arc Γ s} {r l ξ : H}

include R

omit R in
theorem shift_inv_vert {g : H} (hg : ∀ j, j < s → g • a.vert j = a.vert (j + 1)) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j ≤ s) : g⁻¹ • a.vert j = a.vert (j - 1) := by
  rw [inv_smul_eq_iff, hg (j - 1) (by omega), show j - 1 + 1 = j by omega]

theorem adj_inv_a0 (hs : 2 ≤ s) {g : H} (hg : ∀ j, j < s → g • a.vert j = a.vert (j + 1)) :
    Γ.Adj (a.vert 0) (g⁻¹ • a.vert 0) := by
  have h2 := (R.adj g⁻¹ _ _).2 (a.adj 0 (by omega))
  have e1 : g⁻¹ • a.vert 1 = a.vert 0 := shift_inv_vert hg (j := 1) (by omega) (by omega)
  rw [show (0 : ℕ) + 1 = 1 from rfl, e1] at h2
  exact h2.symm

theorem nbrs_a0 (hs : 2 ≤ s) (C : Config a r l ξ) :
    r⁻¹ • a.vert 0 ≠ a.vert 1 ∧ l⁻¹ • a.vert 0 ≠ a.vert 1 ∧ r⁻¹ • a.vert 0 ≠ l⁻¹ • a.vert 0 ∧
    ∀ w, Γ.Adj (a.vert 0) w → w = a.vert 1 ∨ w = r⁻¹ • a.vert 0 ∨ w = l⁻¹ • a.vert 0 := by
  have h1 : ∀ g : H, (∀ j, j < s → g • a.vert j = a.vert (j + 1)) → g⁻¹ • a.vert 0 ≠ a.vert 1 := by
    intro g hg h
    rw [inv_smul_eq_iff, hg 1 (by omega)] at h
    exact a.nb 0 (by omega) h
  have hb : r⁻¹ • a.vert 0 ≠ a.vert 1 := h1 r C.r_shift
  have hb' : l⁻¹ • a.vert 0 ≠ a.vert 1 := h1 l C.l_shift
  have hbb : r⁻¹ • a.vert 0 ≠ l⁻¹ • a.vert 0 := by
    intro h
    refine C.ne (inv_injective (R.eq_of_agree a fun j hj => ?_))
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact h
    · rw [shift_inv_vert C.r_shift hj0 hj, shift_inv_vert C.l_shift hj0 hj]
  refine ⟨hb, hb', hbb, fun w hw => ?_⟩
  have hsub : ({a.vert 1, r⁻¹ • a.vert 0, l⁻¹ • a.vert 0} : Set W) ⊆ Γ.neighborSet (a.vert 0) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact a.adj 0 (by omega)
    · exact R.adj_inv_a0 hs C.r_shift
    · exact R.adj_inv_a0 hs C.l_shift
  have hN : (Γ.neighborSet (a.vert 0)).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact R.card3 _
  have hfin : (Γ.neighborSet (a.vert 0)).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hc3 : ({a.vert 1, r⁻¹ • a.vert 0, l⁻¹ • a.vert 0} : Set W).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨_, _, _, hb.symm, hb'.symm, hbb, rfl⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub (by omega) hfin
  have hw' : w ∈ Γ.neighborSet (a.vert 0) := hw
  rw [← heq] at hw'
  simpa using hw'

omit R in
theorem rpow_s_b (hs : 1 ≤ s) (C : Config a r l ξ) :
    r ^ s • (r⁻¹ • a.vert 0) = a.vert (s - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have := pow_smul_vert C.r_shift t 0 (by omega)
  rw [zero_add] at this
  rw [pow_succ, mul_smul, smul_inv_smul, this, Nat.add_sub_cancel]

omit R in
theorem tx_s_b (hs : 1 ≤ s) (C : Config a r l ξ) :
    tx r l (s : ℤ) • (r⁻¹ • a.vert 0) = l⁻¹ • a.vert 0 := by
  have h1 := rpow_s_b hs C
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have h2 : (l ^ t)⁻¹ • a.vert t = a.vert 0 := by
    have := inv_pow_smul_vert C.l_shift (k := t) (j := 0) (by omega)
    rwa [zero_add] at this
  rw [tx_natCast, mul_smul, h1, Nat.add_sub_cancel, pow_succ, mul_inv_rev, mul_smul, h2]

theorem tx_s_cycle (hs : 2 ≤ s) (C : Config a r l ξ) :
    tx r l (s : ℤ) • a.vert 1 = r⁻¹ • a.vert 0 ∧
      tx r l (s : ℤ) • (r⁻¹ • a.vert 0) = l⁻¹ • a.vert 0 ∧
      tx r l (s : ℤ) • (l⁻¹ • a.vert 0) = a.vert 1 := by
  obtain ⟨hb, hb', hbb, hall⟩ := R.nbrs_a0 hs C
  have hfix : tx r l (s : ℤ) • a.vert 0 = a.vert 0 := tx_smul_vert C le_rfl (by omega)
  have hnb : ∀ w, Γ.Adj (a.vert 0) w → Γ.Adj (a.vert 0) (tx r l (s : ℤ) • w) := by
    intro w hw
    have := (R.adj (tx r l (s : ℤ)) _ _).2 hw
    rwa [hfix] at this
  have h1 : tx r l (s : ℤ) • a.vert 1 ≠ a.vert 1 := by
    have := R.tx_smul_vert_ne C (i := s) (by omega) le_rfl
    rwa [Nat.sub_self] at this
  have hxb := tx_s_b (by omega) C
  have ha1 : tx r l (s : ℤ) • a.vert 1 = r⁻¹ • a.vert 0 := by
    rcases hall _ (hnb _ (a.adj 0 (by omega))) with h | h | h
    · exact absurd h h1
    · exact h
    · exact absurd (MulAction.injective _ (h.trans hxb.symm)) hb.symm
  refine ⟨ha1, hxb, ?_⟩
  rcases hall _ (hnb _ (R.adj_inv_a0 hs C.l_shift)) with h | h | h
  · exact h
  · exact absurd (MulAction.injective _ (h.trans ha1.symm)) hb'
  · exact absurd (MulAction.injective _ (h.trans hxb.symm)) hbb.symm

end RegData

end CFSG.Quasithin.Fan86.Tutte.Geo
