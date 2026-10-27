module

public import CFSG.LocalAnalysis.WeakClosure81.FiveInputs
public import CFSG.LocalAnalysis.WeakClosure81.FiveSixCases
public import CFSG.LocalAnalysis.WeakClosure81.FiveSixOrbit
public import CFSG.LocalAnalysis.WeakClosure81.FiveSixOrder

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 Equiv

theorem five_six_perm (hR : R3_1) {n : ℕ} (hn : 4 < n) {K T : Subgroup (Perm (Fin n))}
    (hA : alternatingGroup (Fin n) ≤ K) (hT : IsPGroup 2 T) (h1 : (maxOver K T).ncard = 1) :
    (∃ m : ℕ, n = 2 ^ m + 1) ∧
      ∃ α : Fin n, maxOver K T = {K ⊓ MulAction.stabilizer (Perm (Fin n)) α} := by
  obtain ⟨M, hM⟩ := Set.ncard_eq_one.1 h1
  have hMK : M < K := (hM ▸ Set.mem_singleton M : M ∈ maxOver K T).1.1
  obtain ⟨S, hS, hTS⟩ := B6.exists_isSylowTwoOf_ge hT (le_top : T ≤ ⊤)
  obtain ⟨Γ, hSΓ, hΓc, hpow, a, b, c, hab, hac, hbc, hsw, ha, hb, hc⟩ := exists_goodPart hn hS
  have hΓ3 : 3 ≤ Γ.ncard :=
    (Set.two_lt_ncard_iff (Set.toFinite Γ)).2 ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
  have hMΓ : K ⊓ partStab Γ ≤ M :=
    inf_partStab_le (by omega) hA hM ⟨a, ha⟩ hΓc (hTS.trans hSΓ)
  have hMΔ : K ⊓ Subgroup.setNormalizer {t : Perm (Fin n) | t ∈ S ∧ t.IsSwap} ≤ M :=
    inf_setNormalizer_swaps_le (by omega) hA hM hTS hS.2.1 ⟨a, b, hab, hsw⟩
  rcases hR n hn K S M hA hS hMΔ hMK.le with
    h | h | ⟨hodd, α, -, hMα⟩ | ⟨e7, hL⟩ | ⟨e89, E, hEn, hEM, -, h8, hL⟩
  · exact absurd h hMK.ne
  · exfalso
    have hcyc : cyc3 a b c ∈ M :=
      hMΓ ⟨hA (cyc3_mem_alternatingGroup hab hbc), cyc3_mem_partStab_of_mem ha hb hc⟩
    rw [h] at hcyc
    have h2 := (Subgroup.mem_set_normalizer_iff.1 hcyc.2 (swap a b)).1 ⟨hsw, a, b, hab, rfl⟩
    rw [cyc3_mul_swap_mul_inv hab hac hbc] at h2
    exact false_of_swap_mem_of_swap_mem hS.2.1 hab hac hbc hsw h2.1
  · exact ⟨exists_two_pow_add_one_of_stabilizer hA hMΓ ((le_of_eq hMα).trans inf_le_right) hΓ3
      hpow hodd, α, by rw [hM, hMα]⟩
  · exact (false_of_not_nine_dvd (seven_le_of_nonempty_mulEquiv_alternatingGroup le_rfl e7) hA
      hMΓ hΓ3 hpow (not_nine_dvd_card_of_isL3 hL)).elim
  · haveI := hEn
    have hn7 : 7 ≤ n := by
      rcases e89 with e | e
      · exact seven_le_of_nonempty_mulEquiv_alternatingGroup (by norm_num) e
      · exact seven_le_of_nonempty_mulEquiv_alternatingGroup (by norm_num) e
    exact (false_of_not_nine_dvd hn7 hA hMΓ hΓ3 hpow
      (not_nine_dvd_card_of_isL3_quotient hEM h8 hL)).elim

end CFSG.LocalAnalysis.WeakClosure81
