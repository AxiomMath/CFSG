module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation

public section

namespace CFSG.Quasithin.H13.KG12614

open Equiv Equiv.Perm Subgroup

theorem not_dvd_card_centralizer_seven {τ : Perm (Fin 7)} {p : ℕ} (hp : p.Prime)
    (hτ : orderOf τ = p) : ¬ 360 ∣ Nat.card (centralizer ({τ} : Set (Perm (Fin 7)))) := by
  have hc : ∀ n ∈ τ.cycleType, n = p := by
    intro n hn
    have h1 := dvd_of_mem_cycleType hn
    rw [hτ] at h1
    have h2 := two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · omega
    · exact h
  have hrep : τ.cycleType = Multiset.replicate (Multiset.card τ.cycleType) p :=
    Multiset.eq_replicate_card.mpr hc
  have hsum := sum_cycleType_le τ
  rw [hrep, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hne : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    exact hp.one_lt.ne hτ
  have hk : Multiset.card τ.cycleType ≠ 0 := fun h => hne (card_cycleType_eq_zero.mp h)
  rw [nat_card_centralizer, hrep]
  generalize Multiset.card τ.cycleType = k at hsum hk ⊢
  have hp2 := hp.two_le
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
  have hp7 : p ≤ 7 := by nlinarith
  have hk7 : k ≤ 3 := by nlinarith
  interval_cases p <;> (try norm_num at hp) <;> interval_cases k <;> first | omega | decide

theorem eq_one_of_fix_alt7 (α : MulAut (alternatingGroup (Fin 7)))
    (H : Subgroup (alternatingGroup (Fin 7))) (hH : Nat.card H = 360)
    (hfix : ∀ h ∈ H, α h = h) : α = 1 := by
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (n := 7) (Or.inr le_rfl) α
  have hα : α = MulAut.conjNormal σ :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hσ g, MulAut.conjNormal_apply])
  have hcomm : ∀ h ∈ H, Commute σ (h : Perm (Fin 7)) := by
    intro h hh
    have h1 := hσ h
    rw [hfix h hh] at h1
    show σ * (h : Perm (Fin 7)) = h * σ
    calc σ * (h : Perm (Fin 7)) = (σ * h * σ⁻¹) * σ := by group
      _ = h * σ := by rw [← h1]
  have hσ1 : σ = 1 := by
    by_contra hne
    have ho : orderOf σ ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd ho
    have hτ := orderOf_pow_orderOf_div (orderOf_pos σ).ne' hpd
    apply not_dvd_card_centralizer_seven hp hτ
    rw [← hH]
    have hle : H.map (alternatingGroup (Fin 7)).subtype ≤
        centralizer ({σ ^ (orderOf σ / p)} : Set (Perm (Fin 7))) := by
      rintro _ ⟨h, hh, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((hcomm h hh).pow_left _).eq.symm
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective] at this
  rw [hα, hσ1, map_one]

theorem eq_one_of_fix_isAlt7 {Q : Type} [Group Q] (hQ : CFSG.Quasithin.IsAlt 7 Q)
    (α : MulAut Q) (H : Subgroup Q) (hH : Nat.card H = 360) (hfix : ∀ h ∈ H, α h = h) :
    α = 1 := by
  obtain ⟨e⟩ := hQ
  have h1 : (e.symm.trans α).trans e = 1 := by
    refine eq_one_of_fix_alt7 _ (H.map e.toMonoidHom) ?_ ?_
    · rw [Subgroup.card_map_of_injective e.injective, hH]
    · rintro _ ⟨h, hh, rfl⟩
      simp [hfix h hh]
  ext q
  have h2 := congrArg (fun β : MulAut ↥(alternatingGroup (Fin 7)) => e.symm (β (e q))) h1
  simpa using h2

end CFSG.Quasithin.H13.KG12614
