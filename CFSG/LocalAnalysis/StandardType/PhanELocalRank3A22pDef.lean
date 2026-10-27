module

public import CFSG.LocalAnalysis.StandardType.PhanELocalCls
public import CFSG.LocalAnalysis.StandardType.PhanELocalGate
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] noncomputable def D22p : ClsData K where
  ok c := c ⊓ sgS K f 2 c = ⊥
  good _ M := M ⊓ sgS K f 4 M = ⊥

private theorem plh_rho_sgv (v : Fin 4 → K) :
    rho (K := K) (sgv K f 4 v) = sgv K f 2 (rho (K := K) v) := by
  ext i
  simp [rho_apply, sgv_apply]

private theorem plh_sgS_comap_rho (c : Submodule K (Fin 2 → K)) :
    sgS K f 4 (c.comap (rho (K := K))) = (sgS K f 2 c).comap (rho (K := K)) := by
  ext v
  simp only [mem_sgS, Submodule.mem_comap, plh_rho_sgv]

private theorem plh_comap_rho_bot_iff (e : Submodule K (Fin 2 → K)) :
    e.comap (rho (K := K)) = Vsub 4 2 ↔ e = ⊥ := by
  constructor
  · intro h
    apply Submodule.comap_injective_of_surjective (f := rho (K := K)) rho_surjective
    rw [h, Submodule.comap_bot, ker_rho]
  · intro h
    rw [h, Submodule.comap_bot, ker_rho]

private theorem plh_sup_eq_comap_map (p : Submodule K (Fin 4 → K)) :
    p ⊔ Vsub 4 2 = (p.map (rho (K := K))).comap (rho (K := K)) := by
  rw [Submodule.comap_map_eq, ker_rho]

private theorem plh_sgS_sup_Vsub (p : Submodule K (Fin 4 → K)) :
    sgS K f 4 (p ⊔ Vsub 4 2) =
      (sgS K f 2 (p.map (rho (K := K)))).comap (rho (K := K)) := by
  rw [plh_sup_eq_comap_map (K := K) p, plh_sgS_comap_rho]

private theorem plh_sgS_sup_inf_eq (p : Submodule K (Fin 4 → K)) :
    (p ⊔ Vsub 4 2) ⊓ sgS K f 4 (p ⊔ Vsub 4 2) =
      (p.map (rho (K := K)) ⊓ sgS K f 2 (p.map (rho (K := K)))).comap (rho (K := K)) := by
  rw [plh_sgS_sup_Vsub (K := K) f p, plh_sup_eq_comap_map (K := K) p,
    ← Submodule.comap_inf]

private theorem plh_map_inf_sgS_eq_bot_iff (p : Submodule K (Fin 4 → K)) :
    (p.map (rho (K := K)) ⊓ sgS K f 2 (p.map (rho (K := K))) = ⊥) ↔
      ((p ⊔ Vsub 4 2) ⊓ sgS K f 4 (p ⊔ Vsub 4 2) = Vsub 4 2) := by
  rw [plh_sgS_sup_inf_eq (K := K) f p]
  constructor
  · intro h
    rw [h, Submodule.comap_bot, ker_rho]
  · intro h
    exact (plh_comap_rho_bot_iff (K := K) _).mp h

private theorem plh_blockU_zero_a3_22p (E : ℕ → Submodule K (Fin 4 → K)) :
    blockU K 4 [0, 2, 4] E 0 1 = E 3 ⊓ Vsub 4 2 := by
  simp [blockU, Vsub_zero]

private theorem plh_blockU_one_a3_22p (E : ℕ → Submodule K (Fin 4 → K)) :
    blockU K 4 [0, 2, 4] E 1 1 = E 1 ⊔ Vsub 4 2 := by
  simp [blockU, Vsub_self]

private theorem plh_mem_farSet_a3_22p_iff (x : FlagK K 4) :
    x ∈ farSet 4 [0, 2, 4] ↔ x.E 2 ⊓ Vsub 4 2 = ⊥ := by
  have hd : ∀ i, i < ([0, 2, 4] : List ℕ).length →
      ([0, 2, 4] : List ℕ).getD i 0 ≤ 4 := by
    intro i hi
    have hi3 : i < 3 := by simpa using hi
    interval_cases i <;> decide
  rw [mem_farSet_iff (K := K) (n := 4) (d := [0, 2, 4]) hd]
  constructor
  · intro h
    have h' := (h 1 (by decide) 2 (by decide)).1 (by decide)
    simpa using h'
  · intro h i hi j hj
    have hi3 : i < 3 := by simpa using hi
    interval_cases i
    · constructor
      · intro _
        rw [show ([0, 2, 4] : List ℕ).getD 0 0 = 0 from by decide, Vsub_zero, inf_bot_eq]
      · intro hge
        have hj4 : j = 4 := by
          have : 4 ≤ j := by simpa using hge
          omega
        subst hj4
        rw [show ([0, 2, 4] : List ℕ).getD 0 0 = 0 from by decide, Vsub_zero, sup_bot_eq]
        exact x.top 4 le_rfl
    · constructor
      · intro hjc
        have hj2 : j ≤ 2 := by
          have : j + 2 ≤ 4 := by simpa using hjc
          omega
        exact le_bot_iff.mp ((inf_le_inf_right (Vsub (K := K) 4 2) (x.mono hj2)).trans
          (le_of_eq h))
      · intro hge
        have hj2 : 2 ≤ j := by
          have : 4 ≤ j + 2 := by simpa using hge
          omega
        have htop : x.E j ⊔ Vsub (K := K) 4 2 = ⊤ := by
          have hsup2 : x.E 2 ⊔ Vsub (K := K) 4 2 = ⊤ := by
            refine Submodule.eq_top_of_finrank_eq ?_
            rw [Module.finrank_fin_fun]
            have hsum := Submodule.finrank_sup_add_finrank_inf_eq (x.E 2)
              (Vsub (K := K) 4 2)
            rw [h, finrank_bot, add_zero, FlagK.finrank_E_two,
              finrank_Vsub (K := K) (n := 4) (c := 2) (by norm_num)] at hsum
            omega
          exact top_le_iff.mp (hsup2 ▸ sup_le_sup (x.mono hj2) le_rfl)
        exact htop
    · constructor
      · intro hjc
        have hj0 : j = 0 := by
          have : j + 4 ≤ 4 := by simpa using hjc
          omega
        subst hj0
        rw [show ([0, 2, 4] : List ℕ).getD 2 0 = 4 from by decide, Vsub_self, inf_top_eq]
        exact FlagK.E_zero x
      · intro _
        rw [show ([0, 2, 4] : List ℕ).getD 2 0 = 4 from by decide, Vsub_self, sup_top_eq]

theorem genSet_a3_22p_eq :
    genSet K f 4 [0, 2, 4] [] = admSet (AdmS (D22p (K := K) f)) := by
  have hle : ∀ i, i < ([0, 2, 4] : List ℕ).length →
      ([0, 2, 4] : List ℕ).getD i 0 ≤ 4 := by
    intro i hi
    have hi3 : i < 3 := by simpa using hi
    interval_cases i <;> decide
  have hmono : ∀ i, i + 1 < ([0, 2, 4] : List ℕ).length →
      ([0, 2, 4] : List ℕ).getD i 0 ≤ ([0, 2, 4] : List ℕ).getD (i + 1) 0 := by
    intro i hi
    have hi2 : i < 2 := by
      have : i + 1 < 3 := by simpa using hi
      omega
    interval_cases i <;> decide
  ext x
  simp only [genSet, Set.mem_setOf_eq, admSet, AdmS, D22p]
  constructor
  · rintro ⟨hfar, hblocks⟩
    refine ⟨(plh_mem_farSet_a3_22p_iff (K := K) x).mp hfar, ?_, ?_⟩
    · have h1 := hblocks 1 (by decide)
      rw [blockOK_iff_of_far f hle hmono hfar (by decide)] at h1
      have h := h1 1 (by decide) (by decide)
      simp only [List.getD_nil, Bool.false_eq_true, ↓reduceIte] at h
      rw [show ([0, 2, 4] : List ℕ).getD (1 + 1) 0 - ([0, 2, 4] : List ℕ).getD 1 0 - 1 = 1
        from by decide] at h
      rw [plh_blockU_one_a3_22p (K := K) x.E] at h
      rw [show ([0, 2, 4] : List ℕ).getD 1 0 = 2 from by decide] at h
      exact (plh_map_inf_sgS_eq_bot_iff (K := K) f (x.E 1)).mpr h
    · have h0 := hblocks 0 (by decide)
      rw [blockOK_iff_of_far f hle hmono hfar (by decide)] at h0
      have h := h0 1 (by decide) (by decide)
      simp only [List.getD_nil, Bool.false_eq_true, ↓reduceIte] at h
      rw [show ([0, 2, 4] : List ℕ).getD (0 + 1) 0 - ([0, 2, 4] : List ℕ).getD 0 0 - 1 = 1
        from by decide] at h
      rw [plh_blockU_zero_a3_22p (K := K) x.E] at h
      rw [show ([0, 2, 4] : List ℕ).getD 0 0 = 0 from by decide, Vsub_zero] at h
      exact h
  · rintro ⟨hL, hok, hgood⟩
    have hfar := (plh_mem_farSet_a3_22p_iff (K := K) x).mpr hL
    refine ⟨hfar, ?_⟩
    intro i hi
    rw [blockOK_iff_of_far f hle hmono hfar hi]
    intro r hr0 hrm
    simp only [List.getD_nil, Bool.false_eq_true, ↓reduceIte]
    have hi2 : i < 2 := by
      have : i + 1 < 3 := by simpa using hi
      omega
    interval_cases i
    · have hr : r = 1 := by
        have hdiff : ([0, 2, 4] : List ℕ).getD (0 + 1) 0 -
            ([0, 2, 4] : List ℕ).getD 0 0 = 2 := by decide
        rw [hdiff] at hrm
        omega
      subst hr
      rw [show ([0, 2, 4] : List ℕ).getD (0 + 1) 0 - ([0, 2, 4] : List ℕ).getD 0 0 - 1 = 1
        from by decide]
      rw [plh_blockU_zero_a3_22p (K := K) x.E]
      rw [show ([0, 2, 4] : List ℕ).getD 0 0 = 0 from by decide, Vsub_zero]
      exact hgood
    · have hr : r = 1 := by
        have hdiff : ([0, 2, 4] : List ℕ).getD (1 + 1) 0 -
            ([0, 2, 4] : List ℕ).getD 1 0 = 2 := by decide
        rw [hdiff] at hrm
        omega
      subst hr
      rw [show ([0, 2, 4] : List ℕ).getD (1 + 1) 0 - ([0, 2, 4] : List ℕ).getD 1 0 - 1 = 1
        from by decide]
      rw [plh_blockU_one_a3_22p (K := K) x.E]
      rw [show ([0, 2, 4] : List ℕ).getD 1 0 = 2 from by decide]
      exact (plh_map_inf_sgS_eq_bot_iff (K := K) f (x.E 1)).mp hok

end CFSG.ClassicalInvolution.Phan.PhanE

end
