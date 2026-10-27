module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.Timmesfeld.Bridge.OddTranspGenL2
import CFSG.CGT.Timmesfeld75.L2Three

public section

namespace CFSG.BenderSuzuki

open CFSG.CGT.Timmesfeld75

variable {L : Type} [Group L] {n : ℕ}

private theorem isL2Pair_of_sylow (e : L ≃* PSL2Model n) (hn : 2 ≤ n) (P : Sylow 2 L) :
    IsL2Pair L (P : Subgroup L) (2 ^ n) :=
  IsL2Pair.of_psl_sylow (by omega) ⟨e⟩ P

theorem psl2_centralizer_eq_sylow (e : L ≃* PSL2Model n) (hn : 2 ≤ n) {s : L} {S : Sylow 2 L}
    (hs : s ∈ S) (hs1 : s ≠ 1) : Subgroup.centralizer ({s} : Set L) = (S : Subgroup L) :=
  (isL2Pair_of_sylow e hn S).centralizer_eq hs hs1

theorem psl2_sylow_eq_of_mem (e : L ≃* PSL2Model n) (hn : 2 ≤ n) {s : L} (hs1 : s ≠ 1)
    {S S' : Sylow 2 L} (hsS : s ∈ S) (hsS' : s ∈ S') : S = S' := by
  have hS := (isL2Pair_of_sylow e hn S).centralizer_eq hsS hs1
  have hS' := (isL2Pair_of_sylow e hn S').centralizer_eq hsS' hs1
  exact Sylow.ext (by rw [← hS, ← hS'])

theorem psl2_mem_sylow_of_commute (e : L ≃* PSL2Model n) (hn : 2 ≤ n) {t : L} (ht1 : t ≠ 1)
    {S : Sylow 2 L} (htS : t ∈ S) {c : L} (hc : Commute c t) : c ∈ (S : Subgroup L) := by
  rw [← psl2_centralizer_eq_sylow e hn htS ht1]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hc.eq

theorem psl2_normalizer_inf_eq_bot (e : L ≃* PSL2Model n) (hn : 2 ≤ n) {S S' : Sylow 2 L}
    (hne : S ≠ S') :
    Subgroup.normalizer ((S : Subgroup L) : Set L) ⊓ (S' : Subgroup L) = ⊥ := by
  obtain ⟨g, hg⟩ := (isL2Pair_of_sylow e hn S).exists_conj_eq_sylow S'
  have hgN : g ∉ Subgroup.normalizer ((S : Subgroup L) : Set L) := by
    intro hmem
    rw [mem_normalizer_iff_conjSubgroup_eq] at hmem
    exact hne (Sylow.ext (by rw [← hg, hmem]))
  have h := (isL2Pair_of_sylow e hn S).normalizer_inf_conj_eq_bot hgN
  rwa [hg] at h

theorem psl2_sup_sylow_eq_top (e : L ≃* PSL2Model n) (hn : 2 ≤ n) {S S' : Sylow 2 L}
    (hne : S ≠ S') : (S : Subgroup L) ⊔ (S' : Subgroup L) = ⊤ :=
  (isL2Pair_of_sylow e hn S).sup_sylow_eq_top hne

theorem psl2_exists_involution_swap (e : L ≃* PSL2Model n) (hn : 2 ≤ n) {S S' : Sylow 2 L}
    (hne : S ≠ S') :
    ∃ t : L, t * t = 1 ∧ t ≠ 1 ∧ conjSubgroup t (S : Subgroup L) = (S' : Subgroup L) := by
  obtain ⟨b, hbS, hb1, -, -, -⟩ :=
    (isL2Pair_of_sylow e hn S).exists_mul_orderOf_three_of_sylow hne
  obtain ⟨g, hg⟩ := (isL2Pair_of_sylow e hn S).exists_conj_eq_sylow S'
  have hgS : conjSubgroup g (S : Subgroup L) ≠ (S : Subgroup L) := by
    rw [hg]
    intro h
    exact hne (Sylow.ext h.symm)
  obtain ⟨t, ht2, htc, -⟩ :=
    (isL2Pair_of_sylow e hn S).exists_swap_orderOf_three hbS hb1 hgS
  refine ⟨t, ht2, ?_, by rw [htc, hg]⟩
  rintro rfl
  rw [conjSubgroup_one] at htc
  exact hgS htc.symm

theorem psl2_involutionThreeGen (e : L ≃* PSL2Model n)
    (hn : 2 ≤ n) : CFSG.Timmesfeld.Bridge.OddTransp.InvolutionThreeGen L :=
  (CFSG.Timmesfeld.Bridge.OddTransp.involutionThreeGen_psl2 hn).of_mulEquiv e

end CFSG.BenderSuzuki
