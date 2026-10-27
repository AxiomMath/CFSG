module

public import CFSG.Milestones.ASVolI.A3L3.Defs
public import CFSG.Milestones.ASVolI.A3OddFacts

public section

namespace CFSG.ASVolI

open scoped Pointwise

theorem burnsideA315y_cartan : burnsideA315y_CartanStatement := by
  intro X _ _ p hp L I U Q hLI hU hpLI hQI hQN hpQ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hUL, hUp, hpUL⟩ := hU
  set M : Subgroup X := I ⊓ Subgroup.normalizer (U : Set X) with hMdef
  have hUM : U ≤ M := le_inf (hUL.trans hLI) Subgroup.le_normalizer
  have hQM : Q ≤ M := le_inf hQI hQN
  have hidx : ¬ p ∣ U.relIndex M := by
    intro hd
    have h1 := Subgroup.relIndex_mul_relIndex U M I hUM inf_le_left
    have h2 := Subgroup.relIndex_mul_relIndex U L I hUL hLI
    have h3 : p ∣ U.relIndex I := h1 ▸ Dvd.dvd.mul_right hd _
    rw [← h2] at h3
    rcases (Nat.Prime.dvd_mul hp).1 h3 with h | h
    · exact hpUL h
    · exact hpLI h
  obtain ⟨a, ha⟩ := hUp.exists_card_eq
  have hcopU : ∀ {n : ℕ}, ¬ p ∣ n → Nat.Coprime (Nat.card ↥U) n := fun hn => by
    rw [ha]
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)
  set N : Subgroup ↥M := U.subgroupOf M with hNdef
  haveI hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUM).2 inf_le_right
  have hNcard : Nat.card ↥N = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
  have hcopM : Nat.Coprime (Nat.card ↥N) N.index := by
    rw [hNcard]
    exact hcopU hidx
  obtain ⟨H₀', hH₀'⟩ := Subgroup.exists_right_complement'_of_coprime hcopM
  set H₀ : Subgroup X := H₀'.map M.subtype with hH₀def
  have hH₀M : H₀ ≤ M := Subgroup.map_subtype_le H₀'
  have hH₀card : Nat.card ↥H₀ = U.relIndex M := by
    rw [hH₀def, Subgroup.card_map_of_injective M.subtype_injective]
    exact (hH₀'.symm.index_eq_card).symm
  have hdecomp : ∀ m ∈ M, ∃ u ∈ U, ∃ h ∈ H₀, m = u * h := by
    intro m hm
    obtain ⟨⟨u, h⟩, huh⟩ := hH₀'.2 ⟨m, hm⟩
    refine ⟨(u.1 : X), Subgroup.mem_subgroupOf.mp u.2, (h.1 : X), ⟨h.1, h.2, rfl⟩, ?_⟩
    have := congrArg Subtype.val huh
    simpa using this.symm
  set T : Subgroup X := U ⊔ Q with hTdef
  have hTM : T ≤ M := sup_le hUM hQM
  have hUT : U ≤ T := le_sup_left
  have hQT : Q ≤ T := le_sup_right
  have hTcoe : (T : Set X) = (U : Set X) * (Q : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left U Q hQN
  have hUQbot : U ⊓ Q = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (hcopU hpQ))
  have hperm : (U : Set X) * (Q : Set X) = (Q : Set X) * (U : Set X) :=
    (Subgroup.set_mul_normalizer_comm (Q : Set X) U (fun x hx => hQN hx)).symm
  have hTcard : Nat.card ↥T = Nat.card ↥U * Nat.card ↥Q := burnsideA315x_card_sup hperm hUQbot
  set NT : Subgroup ↥T := U.subgroupOf T with hNTdef
  haveI : NT.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUT).2 (sup_le Subgroup.le_normalizer hQN)
  have eNT : ↥NT ≃* ↥U := Subgroup.subgroupOfEquivOfLe hUT
  haveI : Group.IsNilpotent ↥NT := (hUp.of_equiv eNT.symm).isNilpotent
  have hNTsolv : Group.IsSolvable ↥NT := inferInstance
  have hNTcard : Nat.card ↥NT = Nat.card ↥U := Nat.card_congr eNT.toEquiv
  have hNTidx : NT.index = Nat.card ↥Q := by
    have h := Subgroup.relIndex_mul_card U T
    rw [inf_of_le_left hUT, hTcard, mul_comm (Nat.card ↥U)] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hcopT : Nat.Coprime (Nat.card ↥NT) NT.index := by
    rw [hNTcard, hNTidx]
    exact hcopU hpQ
  set H₁ : Subgroup ↥T := H₀.subgroupOf T with hH₁def
  set Q₁ : Subgroup ↥T := Q.subgroupOf T with hQ₁def
  have hH₁ : (NT : Set ↥T) * (H₁ : Set ↥T) = Set.univ := by
    refine Set.eq_univ_of_forall fun t => ?_
    obtain ⟨u, hu, h, hh, hut⟩ := hdecomp t (hTM t.2)
    have hhT : h ∈ T := by
      have : h = u⁻¹ * t := by rw [hut]; group
      rw [this]
      exact T.mul_mem (T.inv_mem (hUT hu)) t.2
    refine ⟨⟨u, hUT hu⟩, hu, ⟨h, hhT⟩, hh, ?_⟩
    apply Subtype.ext
    simp [hut]
  have hQ₁ : (NT : Set ↥T) * (Q₁ : Set ↥T) = Set.univ := by
    refine Set.eq_univ_of_forall fun t => ?_
    have ht : (t : X) ∈ (U : Set X) * (Q : Set X) := hTcoe ▸ t.2
    obtain ⟨u, hu, q, hq, huq⟩ := ht
    exact ⟨⟨u, hUT hu⟩, hu, ⟨q, hQT hq⟩, hq, Subtype.ext huq⟩
  have hUH₀ : U ⊓ H₀ = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hH₀card]
    exact hcopU hidx
  have hH₁' : NT ⊓ H₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : X) ∈ U ⊓ H₀ := ⟨hx.1, hx.2⟩
    rw [hUH₀, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (Subtype.ext hx')
  have hQ₁' : NT ⊓ Q₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : X) ∈ U ⊓ Q := ⟨hx.1, hx.2⟩
    rw [hUQbot, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (Subtype.ext hx')
  obtain ⟨n, hn, hconj⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy NT
    hNTsolv hcopT hH₁ hQ₁ hH₁' hQ₁'
  set g : X := ((n⁻¹ : ↥T) : X) with hgdef
  have hgU : g ∈ U := NT.inv_mem hn
  have hgM : g ∈ M := hUM hgU
  set H : Subgroup X := H₀.map (MulAut.conj g).toMonoidHom with hHdef
  have hHcard : Nat.card ↥H = Nat.card ↥H₀ :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hHM : H ≤ M := by
    rintro _ ⟨h, hh, rfl⟩
    change g * h * g⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem hgM (hH₀M hh)) (M.inv_mem hgM)
  refine ⟨H, ⟨hHM, ?_, ⟨a, ?_⟩⟩, ?_⟩
  · rw [hHcard, hH₀card]
    exact hidx
  · have h1 := Subgroup.relIndex_mul_card H M
    have h2 := Subgroup.relIndex_mul_card U M
    rw [inf_of_le_left hHM, hHcard, hH₀card] at h1
    rw [inf_of_le_left hUM] at h2
    have hr0 : U.relIndex M ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h2
      exact Nat.card_pos.ne' h2.symm
    rw [← ha]
    have h3 : H.relIndex M * U.relIndex M = Nat.card ↥U * U.relIndex M := by
      rw [h1, ← h2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hr0) h3
  · intro q hq
    have hq1 : (⟨q, hQT hq⟩ : ↥T) ∈ Q₁ := hq
    rw [hconj] at hq1
    obtain ⟨h, hh, hhq⟩ := hq1
    refine ⟨(h : X), hh, ?_⟩
    have := congrArg Subtype.val hhq
    simpa [MulAut.conj_apply, hgdef] using this

end CFSG.ASVolI
