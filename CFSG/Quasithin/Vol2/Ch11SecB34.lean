module

public import CFSG.Quasithin.Vol2.Ch11SecBBasic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

theorem stmt11_3_4_of (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1110 : Stmt11_1_0) (h1121 : Stmt11_2_1) (h1122 : Stmt11_2_2) (h1123 : Stmt11_2_3)
    (h1133 : Stmt11_3_3) : Stmt11_3_4 := by
  intro G _ _ T L I n V₁ H g hyp hV₁ h31 hnot hAT hAC
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n hyp).1 2 (by norm_num) (by norm_num)
  have hW := h1133 G T L I n V₁ H hyp hV₁ h31 hnot
  have hVab := SecA.isElemAbelian_fsuV hyp
  have hVH := isElemAbelian_VZ hyp h31
  have hHV : H ≤ Subgroup.normalizer (VZ T H : Set G) := le_normalizer_conjClosure _ H
  have hk := sParam_le_nParam hyp h31 hW hVab
  obtain ⟨m, hm, hmn⟩ : ∃ m : ℕ, E3.sParam hVab = m ∧ n ≤ m ∧
      (KindG2 L (fsuV T I) n → m = 2 * n) := by
    by_cases hG2 : KindG2 L (fsuV T I) n
    · exact ⟨2 * n, (h1122 G T L I n (2 * n) V₁ V₂ hyp hV₁ hV₂ (Or.inl ⟨hG2, rfl⟩)).2.2.2.1 hVab,
        by omega, fun _ => rfl⟩
    · exact ⟨n, (h1122 G T L I n n V₁ V₂ hyp hV₁ hV₂ (Or.inr ⟨hG2, rfl⟩)).2.2.2.1 hVab,
        le_rfl, fun h => absurd h hG2⟩
  have hkn : (n : ℕ∞) ≤ E1.nParam H := le_trans (by rw [hm]; exact_mod_cast hmn.1) hk
  have h2 : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n := by
    rcases SecA.kind_cases h1102 hyp with hk3 | hk4 | hk6
    · exact Or.inl hk3
    · exact Or.inr hk4
    · have h2n : ((2 * n : ℕ) : ℕ∞) ≤ E1.nParam H := by
        rw [← hmn.2 hk6, ← hm]; exact hk
      have hlt : (n : ℕ∞) < E1.nParam H :=
        lt_of_lt_of_le (by exact_mod_cast (by have := hyp.one_lt; omega : n < 2 * n)) h2n
      rcases h1121 G T L I n hyp H h31.hstar with h | h
      · exact absurd h (not_le.2 hlt)
      · exact Or.inl h.1
  have h3 : E1.nParam H = n ∨ ((n : ℕ∞) < E1.nParam H ∧ Case11_2_1Two T L I n H) := by
    rcases eq_or_lt_of_le hkn with h | h
    · exact Or.inl h.symm
    · refine Or.inr ⟨h, ?_⟩
      rcases h1121 G T L I n hyp H h31.hstar with h' | h'
      · exact absurd h' (not_le.2 h)
      · exact h'
  have h4 : Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (fsuV T I : Set G) := by
    by_cases hC : Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)
    · have hN := (h1123 G T L I n V₁ hyp hV₁).2 hC
      exact le_inf hN fun x hx => normalizer_inf_le h1103 hyp hV₁ ⟨hN hx, hx⟩
    · exfalso
      apply hnot
      exact ⟨h2.resolve_left fun h => hC (h31.sl3 h), hC, inf_centralizer_eq_bot h331 hyp hV₁ hC,
        fun hW' => absurd hW' hW⟩
  exact ⟨⟨hVH.1, fun hV => autI_mem_aSet hV hVH (hAT.trans h31.hstar.1.1) hHV hAC⟩, h2, h3, h4⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
