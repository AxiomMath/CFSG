module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_w3_sig_eq (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V : Subgroup G} (h : Hyp125 D ⊥ V) (h3σ : 3 ∈ D.sig)
    (hexp : ∀ g ∈ Mbar D.M ⊥ V h.isElemAbelian, g ^ 36 = 1) : D.sig = {3} := by
  have hV := h.isElemAbelian
  have hpf := h.pairFacts
  have hMn : D.M ≤ normalizer (V : Set G) := hpf.le_normalizer
  have hMst : D.M ≤ stabTil ⊥ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hc4 : Nat.card (⊥ : Subgroup G) ≤ 4 := by simp
  have h115 : F11.R115 D := uc22p22q_r115_of D hx h61
  ext q
  rw [Set.mem_singleton_iff]
  refine ⟨fun hq => ?_, fun hq => hq ▸ h3σ⟩
  obtain ⟨hqP, hq2⟩ := D.sig_prime q hq
  haveI : Fact q.Prime := ⟨hqP⟩
  obtain ⟨E, hE, hEc, hY'⟩ := exists_rank_data h115 (Hyp125.hyp11 h127 h) hc4 hq
  have hEM : E.map D.M.subtype ≤ D.M := Subgroup.map_subtype_le E
  have hEst : E.map D.M.subtype ≤ stabTil ⊥ V := hEM.trans hMst
  have hEel : IsElemAbelian q (E.map D.M.subtype) := hE.map D.M.subtype
  have hEc' : q ^ 3 ≤ Nat.card ↥(E.map D.M.subtype) := by
    rw [Subgroup.card_map_of_injective D.M.subtype_injective]
    exact hEc
  have hΛM : barSub ⊥ V hV (E.map D.M.subtype) ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hEM
  have hΛel : IsElemAbelian q (barSub ⊥ V hV (E.map D.M.subtype)) :=
    (hEel.subgroupOf (stabTil ⊥ V)).map (actTil ⊥ V hV)
  have hE₀E : preBarSub (E.map D.M.subtype) ⊥ V hV ⊥ ≤ E.map D.M.subtype := inf_le_left
  have hE₀M : preBarSub (E.map D.M.subtype) ⊥ V hV ⊥ ≤ D.M := hE₀E.trans hEM
  have hE₀card : Nat.card (preBarSub (E.map D.M.subtype) ⊥ V hV ⊥) ≤ q := by
    have hel : IsElemAbelian q ((preBarSub (E.map D.M.subtype) ⊥ V hV ⊥).subgroupOf D.M) :=
      (hEel.mono hE₀E).subgroupOf D.M
    have hker : (preBarSub (E.map D.M.subtype) ⊥ V hV ⊥).subgroupOf D.M ≤
        (F11.CTilde D.M ⊥ V).subgroupOf D.M := by
      rw [← ker_barHom ⊥ V hV hMn hMst]
      intro x hx'
      obtain ⟨-, hst, hx1⟩ :=
        (mem_preBarSub (E.map D.M.subtype) ⊥ V hV ⊥).1 (Subgroup.mem_subgroupOf.1 hx')
      rw [MonoidHom.mem_ker]
      have : barHom ⊥ V hV hMst x = actTil ⊥ V hV ⟨(x : G), hst⟩ := rfl
      rw [this]
      exact Subgroup.mem_bot.1 hx1
    have h3 := hY' _ hel hker
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀M).toEquiv] at h3
  have hid := s16c7_card_mul_card_preBarSub hV hEst (Q := ⊥) bot_le
  rw [Subgroup.card_bot, mul_one] at hid
  have hΛne : barSub ⊥ V hV (E.map D.M.subtype) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, mul_one] at hid
    have h1 : q ^ 1 < q ^ 3 := Nat.pow_lt_pow_right hqP.one_lt (by norm_num)
    rw [pow_one] at h1
    omega
  obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hΛne
  have hgq : orderOf (g : MulAut (Vtil ⊥ V hV)) = q :=
    orderOf_eq_prime (hΛel.2 _ g.2) fun h1 => hg1 (Subtype.ext h1)
  have h36 : q ∣ 2 ^ 2 * 3 ^ 2 := hgq ▸ orderOf_dvd_of_pow_eq_one (hexp _ (hΛM g.2))
  rcases (Nat.Prime.dvd_mul hqP).1 h36 with h2 | h3
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hqP Nat.prime_two).1 (hqP.dvd_of_dvd_pow h2)) hq2
  · exact (Nat.prime_dvd_prime_iff_eq hqP Nat.prime_three).1 (hqP.dvd_of_dvd_pow h3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
