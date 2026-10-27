module

public import CFSG.Walter.W67.Defs
public import CFSG.Walter.JRAssembly
public import CFSG.Walter.JRFacts

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCore_two_eq_bot_of_simple [IsSimpleGroup G] (heven : Even (Nat.card G)) :
    CFSG.pPrimeCore 2 G = ⊥ := by
  have hN : (CFSG.pPrimeCore 2 G).Normal := CFSG.pPrimeCore_normal
  rcases hN.eq_bot_or_eq_top with hb | ht
  · exact hb
  · exfalso
    have hc : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 G)) := CFSG.pPrimeCore_coprime_card
    rw [ht, Subgroup.card_top] at hc
    obtain ⟨k, hk⟩ := heven
    rw [hk] at hc
    have : (2 : ℕ) ∣ k + k := ⟨k, by ring⟩
    exact absurd (Nat.Coprime.coprime_dvd_right this hc) (by norm_num)

theorem not_case1_of_simple [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (h : Hyp G) :
    ¬ Case1 h := by
  rintro ⟨hHO, -, -⟩
  rw [pPrimeCore_two_eq_bot_of_simple (even_card_of_isSimpleGroup hnonab), sup_bot_eq] at hHO
  have hJZ : h.J ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({h.J} : Set G) := by rw [hHO]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have hJ1 : h.J ≠ 1 := by
    intro h1
    have := h.orderOf_J
    rw [h1, orderOf_one] at this
    omega
  have hZ : Subgroup.center G = ⊤ := by
    rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with hb | ht
    · exact absurd ((Subgroup.mem_bot.mp (hb ▸ hJZ))) hJ1
    · exact ht
  obtain ⟨a, b, hab⟩ := hnonab
  have ha : a ∈ Subgroup.center G := hZ ▸ Subgroup.mem_top a
  exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem eq_top_of_normal_odd_index [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {L : Subgroup G} (hL : L.Normal) (hodd : Odd L.index) : L = ⊤ := by
  rcases hL.eq_bot_or_eq_top with hb | ht
  · exfalso
    rw [hb, Subgroup.index_bot] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_card_of_isSimpleGroup hnonab)
  · exact ht

theorem walter67Hyp_of_theorem (hT : Theorem) : Walter67Hyp := by
  intro G _ _ hJR hnonab t ht
  have : IsSimpleGroup G := hJR.1
  obtain ⟨-, p, f, hp, L, hpodd, hf, h5, hLC, hLn, ⟨e⟩, -⟩ := hJR.2.2 t ht
  have hsyl := hJR.sylow_two_of_nonabelian hnonab
  let h : Hyp G := ⟨p, f, (by rintro rfl; exact (Nat.not_even_iff_odd.mpr hpodd) even_two), hf,
    hJR.2.1, fun P => (hsyl P).2, t, ht, L, hLC, hLn, e⟩
  rcases hT G h with h1 | ⟨L', hL'n, hodd, -, ⟨K', hK', hJK', hC, hK'e⟩, -⟩
  · exact absurd h1 (not_case1_of_simple hnonab h)
  · have hL'top := eq_top_of_normal_odd_index hnonab hL'n hodd
    rw [hL'top, top_inf_eq] at hC hK'
    exact ⟨p, f, hp, K', hpodd, hf, h5, hK', hJK', hC, hK'e⟩

end CFSG.Walter.W67
