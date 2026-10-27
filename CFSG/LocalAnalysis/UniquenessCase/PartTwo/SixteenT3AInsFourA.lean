module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsOrb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsPerm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_a_case168_4_two_of_fixing (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V)
    {p : ℕ} (hp37 : p = 3 ∨ p = 7) (hpσ : p ∈ D.sig)
    {ι : Type} [Fintype ι] {Y : ι → Subgroup (Vtil ⊥ V h.isElemAbelian)}
    (hinj : Function.Injective Y) (hcard : Fintype.card ι = 3)
    (hrk : ∀ i, rk ↥(Y i) = dParam p)
    (hperm : ∀ g ∈ Mbar D.M ⊥ V h.isElemAbelian, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j)
    {E : Subgroup G} (hEM : E ≤ D.M) (hEel : IsElemAbelian p E) (hEc : p ^ 3 ≤ Nat.card E)
    (hEfix : ∀ b ∈ barSub ⊥ V h.isElemAbelian E, ∀ i, (Y i).map b.toMonoidHom = Y i) :
    Insp1613U D V := by
  classical
  have hV := h.isElemAbelian
  obtain ⟨i₀, hi₀⟩ := s16c13bcA_exists_stable_index hinj (s16c13bcA_wBar_isPGroup D hV)
    (fun b hb i => hperm b (s16c13bcA_wBar_le_mbar D hV hb) i)
    (by rw [Nat.card_eq_fintype_card, hcard]; exact ⟨1, rfl⟩)
  have hY0 : Y i₀ ≠ ⊥ := by
    intro h0
    have h1 := hrk i₀
    rw [h0, rk_bot] at h1
    rcases hp37 with rfl | rfl
    · rw [s16c1610_dParam_three] at h1
      omega
    · rw [s16c1610_dParam_seven] at h1
      omega
  obtain ⟨n, hnY, hn1, hnfix⟩ := s16c13bc_exists_fixed_in D h hY0
    (fun b hb => s16c13bcA_mem_stabSub_of_map_eq (hi₀ b hb))
  have hYcard : Nat.card ↥(Y i₀) < p ^ 2 := by
    have hsq : ∀ v : ↥(Y i₀), v ^ 2 = 1 := fun v =>
      Subtype.ext (by simpa using s15_Infra_vtil_sq_eq_one ⊥ V hV v.1)
    rw [card_eq_two_pow_rk hsq, hrk i₀]
    rcases hp37 with rfl | rfl
    · rw [s16c1610_dParam_three]
      norm_num
    · rw [s16c1610_dParam_seven]
      norm_num
  exact s16t_a_insp_of_orbit D h hpσ hEM hEel hEc hYcard (fun b hb => hEfix b hb i₀) hnY hn1
    hnfix

theorem s16t_a_case168_4_two_of_rank (D : Data G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) {p : ℕ} (hp37 : p = 3 ∨ p = 7)
    (hL : IsElemAbelianOfRank p 2 ↥(lBar ⊥ V hV L))
    (hS : SymSumOfConj (Mbar D.M ⊥ V hV) (⊤ : Subgroup (Vtil ⊥ V hV)) 2 (dParam p))
    (hpσ : p ∈ D.sig) (hrank : 3 ≤ CFSG.Open.pRank p (Mbar D.M ⊥ V hV)) :
    Insp1613U D V := by
  classical
  have hpp : p.Prime := by rcases hp37 with rfl | rfl <;> norm_num
  have h125 : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hcore := s16n9b_case4_pcore D hV hc hpp (by norm_num : 1 < 2) hL
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩ := s16n9b_case4_data hS
  letI := hι
  obtain ⟨F, hFX, hFel, hFcard, hFY, -⟩ := s16n9b_case4_kernel
    (s15_Infra_vtil_sq_eq_one ⊥ V hV) hp37 (by norm_num) hL hcore hrank hind hinj hsup hcard hrk
    hperm hsurj
  obtain ⟨i₀, hi₀⟩ := s16c13bcA_exists_stable_index hinj (s16c13bcA_wBar_isPGroup D hV)
    (fun b hb i => hperm b (s16c13bcA_wBar_le_mbar D hV hb) i)
    (by rw [Nat.card_eq_fintype_card, hcard]; exact ⟨1, rfl⟩)
  have hY0 : Y i₀ ≠ ⊥ := by
    intro h0
    have h1 := hrk i₀
    rw [h0, rk_bot] at h1
    rcases hp37 with rfl | rfl
    · rw [s16c1610_dParam_three] at h1
      omega
    · rw [s16c1610_dParam_seven] at h1
      omega
  obtain ⟨n, hnY, hn1, hnfix⟩ := s16c13bc_exists_fixed_in D h125 hY0
    (fun b hb => s16c13bcA_mem_stabSub_of_map_eq (hi₀ b hb))
  have hYcard : Nat.card ↥(Y i₀) < p ^ 2 := by
    have hsq : ∀ v : ↥(Y i₀), v ^ 2 = 1 := fun v =>
      Subtype.ext (by simpa using s15_Infra_vtil_sq_eq_one ⊥ V hV v.1)
    rw [card_eq_two_pow_rk hsq, hrk i₀]
    rcases hp37 with rfl | rfl
    · rw [s16c1610_dParam_three]
      norm_num
    · rw [s16c1610_dParam_seven]
      norm_num
  obtain ⟨P, hPF, hPc, hPfix⟩ := s16c13bcA_exists_noncyclic_fixing hpp hFel hFcard
    (fun f hf => hFY f hf i₀) hYcard hnY
  have hPp : IsPGroup p P := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hFel.2 g (hPF g.2))⟩
  exact s16c13bcA_insp_of_fixing D h125 hpσ hn1 hnfix (hPF.trans hFX) hPp hPc hPfix

theorem s16t_a_case168_4_two_seven (D : Data G) (hSg : UC6S846.SigmaStd D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (h : Case168_4At D ⊥ V hV L 7 2) : Insp1613U D V := by
  classical
  obtain ⟨-, hS, h7σ⟩ := h
  have h125 : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩ := s16n9b_case4_data hS
  letI := hι
  have hP := h125.pairFacts
  have hMst : D.M ≤ stabTil ⊥ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (M := D.M) (by norm_num) (k := 3)
      (hSg.three_le 7 h7σ)
  have hEb : IsElemAbelian 7 (barSub ⊥ V hV E) :=
    (hEel.subgroupOf (stabTil ⊥ V)).map (actTil ⊥ V hV)
  have hEbM : barSub ⊥ V hV E ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hEM
  have hfix := s16t_a_fix_of_pGroup_of_not_dvd hinj hperm (p := 7) (by norm_num)
    (by rw [hcard]; decide) hEbM hEb.isPGroup
  exact s16t_a_case168_4_two_of_fixing D h125 (Or.inr rfl) h7σ hinj hcard hrk hperm hEM hEel
    hEcard.ge hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
