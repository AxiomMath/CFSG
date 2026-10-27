module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2That

public section

namespace CFSG.Quasithin.SimsF5

open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.U42Aut U42F431

theorem af_good_check : ∀ t ∈ Tl, comp (comp t fhatL) (comp t fhatL) = idL →
    8 ≤ (Finset.univ.filter fun ℓ : Fin 45 => (comp t fhatL).getD ℓ 0 = ℓ).card →
    ∃ s ∈ Thl, comp s fhatL = comp (comp t fhatL) s := by
  decide +kernel

theorem good_of_fixed {g : Ah}
    (hg : g ∈ That) (hY : g ∉ Yh) (h2 : g * g = 1)
    (hfix : 8 ≤ (Finset.univ.filter fun ℓ : Fin 45 => (g : Equiv.Perm (Fin 45)) ℓ = ℓ).card) :
    ∃ s ∈ That, s * fhatA * s⁻¹ = g := by
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff g).1 hg
  rcases List.mem_append.1 hl with h | h
  · obtain ⟨g', -, hrep'⟩ := exists_T_of_mem_Tl h
    exfalso
    apply hY
    have : g = incl g' := Subtype.ext (eq_of_repL hrep hrep')
    rw [this, Yh_eq_range]
    exact ⟨g', rfl⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
    have hsq : comp (comp t fhatL) (comp t fhatL) = idL := by
      have h1 := repL_mul hrep hrep
      have h1' : RepL (compL (comp t fhatL) (comp t fhatL)) ((g * g : Ah) : Equiv.Perm (Fin 45)) :=
        h1
      rw [h2] at h1'
      exact repL_unique h1' (repL_one 45)
    have hfixL : 8 ≤ (Finset.univ.filter fun ℓ : Fin 45 => (comp t fhatL).getD ℓ 0 = ℓ).card := by
      have hset : (Finset.univ.filter fun ℓ : Fin 45 => (comp t fhatL).getD ℓ 0 = ℓ) =
          (Finset.univ.filter fun ℓ : Fin 45 => (g : Equiv.Perm (Fin 45)) ℓ = ℓ) := by
        ext ℓ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hrep.2 ℓ]
        constructor
        · intro hℓ
          exact Fin.ext hℓ
        · intro hℓ
          rw [hℓ]
      rw [hset]
      exact hfix
    obtain ⟨s, hs, hseq⟩ := af_good_check t ht hsq hfixL
    obtain ⟨s', hs', hrep_s⟩ := exists_That_of_mem_Thl hs
    refine ⟨s', hs', ?_⟩
    have hrep1 : RepL (comp s fhatL) ((s' * fhatA : Ah) : Equiv.Perm (Fin 45)) :=
      repL_mul hrep_s repL_fhat
    have hrep2 : RepL (comp (comp t fhatL) s) ((g * s' : Ah) : Equiv.Perm (Fin 45)) :=
      repL_mul hrep hrep_s
    rw [← hseq] at hrep2
    have heq : s' * fhatA = g * s' := Subtype.ext (eq_of_repL hrep1 hrep2)
    calc s' * fhatA * s'⁻¹ = g * s' * s'⁻¹ := by rw [heq]
      _ = g := by group

end CFSG.Quasithin.SimsF5
