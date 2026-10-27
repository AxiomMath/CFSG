module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38M3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Unique
public import CFSG.Milestones.ASVolI.A3OddFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16c1610_three_le_pRank_mBar_of_four (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V : Subgroup G} (h16 : Hyp16 D V₀ V) (hV : IsElemAbelian 2 V)
    (h4 : 3 < CFSG.Open.evenRank G) {p : ℕ} (hp : p ∈ D.sig) :
    3 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV) := by
  have h125 : Hyp125 D V₀ V := h16.hyp125
  have hprime : p.Prime := (D.sig_prime p hp).1
  have h115 : F11.R115 D := uc22p22q_r115_of D hx h61
  obtain ⟨hC, -, -⟩ := h115 V₀ V (Hyp125.hyp11 h127 h125) (c23_card_v0_le_four D h16) p hp
  have h1 := hx.four_le h4 p hp
  have h2 := r38m3_pRank_le_add hV h125.pairFacts hprime
  omega

private theorem s16c1610_card_dvd_alt6 {E : Subgroup (MulAut ↥(alternatingGroup (Fin 6)))}
    (hE : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ∣ 360 := by
  have hle : E ≤ (MulAut.conj :
      ↥(alternatingGroup (Fin 6)) →* MulAut ↥(alternatingGroup (Fin 6))).range := by
    intro x hx
    have hodd : Odd (orderOf x) := by
      have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hE x hx)
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h <;> rw [h] <;> decide
    obtain ⟨l, rfl⟩ := CFSG.ASVolI.burnsideA315x_alt6_odd_inner hodd
    exact ⟨l, rfl⟩
  have h1 := Subgroup.card_dvd_of_le hle
  have h2 := Subgroup.card_ker_mul_card_range (MulAut.conj :
      ↥(alternatingGroup (Fin 6)) →* MulAut ↥(alternatingGroup (Fin 6)))
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  rw [h360] at h2
  exact h1.trans (Dvd.intro_left _ h2)

theorem s16c1610_pRank_le_two_of_mulAut_alt6 {X : Type} [Group X] [Finite X] {H : Subgroup X}
    (e : ↥H ≃* MulAut ↥(alternatingGroup (Fin 6))) : CFSG.Open.pRank 3 H ≤ 2 := by
  by_contra hlt
  have h3 : 3 ≤ CFSG.Open.pRank 3 H := by omega
  obtain ⟨E, hE, hcard⟩ := exists_isElemAbelian_subgroupOf_of_le_pRank Nat.prime_three h3
  have hdvd := s16c1610_card_dvd_alt6 (E := E.map e.toMonoidHom) (fun x hx => by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hE.2 y hy, map_one])
  rw [Subgroup.card_map_of_injective e.injective, hcard] at hdvd
  revert hdvd
  decide

theorem s16c1610_false_of_case1_four (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h4 : 3 < CFSG.Open.evenRank G)
    (h1 : Case168_1 D V₀ V hV L) : False := by
  have h3σ : 3 ∈ D.sig := by
    rw [h1.2.2.2]
    exact Set.mem_singleton 3
  have h3 := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hc.setting.hyp16 hV h4 h3σ
  obtain ⟨e⟩ := h1.1
  have := s16c1610_pRank_le_two_of_mulAut_alt6 e
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
