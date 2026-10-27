module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3B1

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P2K

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem exists_arc8_calpha (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) :
    ∃ P : Arc Γ 8, P.vert 0 = D.delta 2 ∧ P.vert 4 = α ∧ P.vert 8 = D.delta 0 ∧
      (∀ m, m ≤ 4 → P.vert m = (D.P 2).vert (4 - m)) ∧
      (∀ m, m ≤ 4 → P.vert (4 + m) = (D.P 0).vert m) ∧ L.calpha P = D.calpha ∧
      D.calpha = P.stab G := by
  obtain ⟨P, h0, h4, h8, hl, hr⟩ := D.exists_arc8 F h71c (i := 2) (j := 0) (by decide)
  have hne : P.vert 0 ≠ P.vert 8 := by
    rw [h0, h8]
    intro h'
    exact absurd (D.delta_injective h') (by decide)
  have hcal := ZLab.calpha_eq_stab h71a h71c P (by rw [h0]; exact D.valence_delta F 2) hne
  have hLD : L.calpha P = D.calpha := by
    show nbrStab Γ G (P.vert 4) ⊓ Subgroup.centralizer ({L.z (P.vert 0) * L.z (P.vert 8)} : Set G) =
      nbrStab Γ G α ⊓ Subgroup.centralizer ({D.x} : Set G)
    rw [h0, h8, h4]
    rfl
  exact ⟨P, h0, h4, h8, hl, hr, hLD, hLD.symm.trans hcal⟩

theorem card_calpha_le_four (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L)
    (h75 : Fan75 F L) : Nat.card ↥D.calpha ≤ 4 := by
  obtain ⟨P, -, h4, -, -, -, hLD, -⟩ := exists_arc8_calpha D F h71a h71c
  have hv : valence Γ (P.vert 4) = 5 := by
    rw [h4]
    exact D.val
  have := (h75 P hv).2.2
  rwa [hLD] at this

theorem card_calpha_two_or_four (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L)
    (h75 : Fan75 F L) : Nat.card ↥D.calpha = 2 ∨ Nat.card ↥D.calpha = 4 := by
  have := Sec8P3.finite_calpha D F
  have hz := Sec8P3.z_mem_calpha_of_fan75 D h71c h75
  have hzo : orderOf (⟨L.z α, hz⟩ : ↥D.calpha) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa [pow_two] using L.z_mul_self D.val)
    · intro h
      exact L.z_ne_one D.val (congrArg Subtype.val h)
  have h2 : 2 ∣ Nat.card ↥D.calpha := hzo ▸ orderOf_dvd_natCard _
  have hpos : 0 < Nat.card ↥D.calpha := Nat.card_pos
  have hle := card_calpha_le_four D F h71a h71c h75
  omega

theorem klein_of_not_cyclic (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L)
    (h75 : Fan75 F L) (hnc : ¬ IsCyclic ↥D.calpha) :
    Nat.card ↥D.calpha = 4 ∧ ∀ c ∈ D.calpha, c * c = 1 := by
  have := Sec8P3.finite_calpha D F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases card_calpha_two_or_four D F h71a h71c h75 with h2 | h4
  · exact absurd (isCyclic_of_prime_card h2) hnc
  · refine ⟨h4, fun c hc => ?_⟩
    have hdvd : orderOf (⟨c, hc⟩ : ↥D.calpha) ∣ 2 ^ 2 := by
      have := orderOf_dvd_natCard (⟨c, hc⟩ : ↥D.calpha)
      rwa [h4] at this
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hne4 : orderOf (⟨c, hc⟩ : ↥D.calpha) ≠ 4 := fun h =>
      hnc (isCyclic_of_orderOf_eq_card _ (h.trans h4.symm))
    have hsq : (⟨c, hc⟩ : ↥D.calpha) ^ 2 = 1 := by
      interval_cases m
      · rw [pow_zero] at hm'
        rw [orderOf_eq_one_iff.1 hm']
        simp
      · rw [pow_one] at hm'
        exact orderOf_dvd_iff_pow_eq_one.1 hm'.dvd
      · exact absurd (by simpa using hm') hne4
    simpa [pow_two] using congrArg Subtype.val hsq

theorem exists_not_mem_zpowers (F : FanTree Γ G) (h71c : Fan71c F L) (h75 : Fan75 F L)
    (h4 : Nat.card ↥D.calpha = 4) : ∃ u ∈ D.calpha, u ∉ Subgroup.zpowers (L.z α) := by
  have := Sec8P3.finite_calpha D F
  have hz := Sec8P3.z_mem_calpha_of_fan75 D h71c h75
  by_contra hcon
  push Not at hcon
  have hle : D.calpha ≤ Subgroup.zpowers (L.z α) := fun c hc => hcon c hc
  have hz2 : Nat.card ↥(Subgroup.zpowers (L.z α)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa [pow_two] using L.z_mul_self D.val)
      (L.z_ne_one D.val)
  have hfin : Finite ↥(Subgroup.zpowers (L.z α)) :=
    Nat.finite_of_card_ne_zero (by rw [hz2]; norm_num)
  have := Subgroup.card_le_of_le hle
  omega

end Sec8P2K

end CFSG.Quasithin.Fan86
