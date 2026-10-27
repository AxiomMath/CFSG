module

public import CFSG.LocalAnalysis.StandardType.PhanELocalCls
public import CFSG.LocalAnalysis.StandardType.PhanELocalGate
import CFSG.ClassicalInvolution.Phan.Geometry.Points
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private theorem plh_mem_farSet_a3_211_iff (x : FlagK K 4) :
    x ∈ farSet 4 [0, 2, 3, 4] ↔
      x.E 1 ⊓ Vsub 4 3 = ⊥ ∧ x.E 2 ⊓ Vsub 4 2 = ⊥ := by
  have hd : ∀ i, i < ([0, 2, 3, 4] : List ℕ).length →
      ([0, 2, 3, 4] : List ℕ).getD i 0 ≤ 4 := by
    intro i hi
    have hi4 : i < 4 := by simpa using hi
    interval_cases i <;> decide
  rw [mem_farSet_iff (K := K) (n := 4) (d := [0, 2, 3, 4]) hd]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h' := (h 2 (by decide) 1 (by decide)).1 (by decide)
      simpa using h'
    · have h' := (h 1 (by decide) 2 (by decide)).1 (by decide)
      simpa using h'
  · rintro ⟨h1, h2⟩
    intro i hi j hj
    have hi4 : i < 4 := by simpa using hi
    interval_cases i
    · constructor
      · intro _
        rw [show ([0, 2, 3, 4] : List ℕ).getD 0 0 = 0 from rfl, Vsub_zero, inf_bot_eq]
      · intro hge
        have hj4 : j = 4 := by
          have : 4 ≤ j := by simpa using hge
          omega
        subst hj4
        rw [show ([0, 2, 3, 4] : List ℕ).getD 0 0 = 0 from rfl, Vsub_zero, sup_bot_eq]
        exact x.top 4 le_rfl
    · constructor
      · intro hjc
        have hj2 : j ≤ 2 := by
          have : j + 2 ≤ 4 := by simpa using hjc
          omega
        exact le_bot_iff.mp ((inf_le_inf_right (Vsub (K := K) 4 2) (x.mono hj2)).trans
          (le_of_eq h2))
      · intro hge
        have hj2 : 2 ≤ j := by
          have : 4 ≤ j + 2 := by simpa using hge
          omega
        have hsup : x.E 2 ⊔ Vsub (K := K) 4 2 = ⊤ := by
          refine Submodule.eq_top_of_finrank_eq ?_
          rw [Module.finrank_fin_fun]
          have hsum := Submodule.finrank_sup_add_finrank_inf_eq (x.E 2)
            (Vsub (K := K) 4 2)
          rw [h2, finrank_bot, add_zero, FlagK.finrank_E_two,
            finrank_Vsub (K := K) (n := 4) (c := 2) (by norm_num)] at hsum
          omega
        exact top_le_iff.mp (hsup ▸ sup_le_sup (x.mono hj2) le_rfl)
    · constructor
      · intro hjc
        have hj1 : j ≤ 1 := by
          have : j + 3 ≤ 4 := by simpa using hjc
          omega
        exact le_bot_iff.mp ((inf_le_inf_right (Vsub (K := K) 4 3) (x.mono hj1)).trans
          (le_of_eq h1))
      · intro hge
        have hj1 : 1 ≤ j := by
          have : 4 ≤ j + 3 := by simpa using hge
          omega
        have hsup : x.E 1 ⊔ Vsub (K := K) 4 3 = ⊤ := by
          refine Submodule.eq_top_of_finrank_eq ?_
          rw [Module.finrank_fin_fun]
          have hsum := Submodule.finrank_sup_add_finrank_inf_eq (x.E 1)
            (Vsub (K := K) 4 3)
          rw [h1, finrank_bot, add_zero, FlagK.finrank_E_one,
            finrank_Vsub (K := K) (n := 4) (c := 3) (by norm_num)] at hsum
          omega
        exact top_le_iff.mp (hsup ▸ sup_le_sup (x.mono hj1) le_rfl)
    · constructor
      · intro hjc
        have hj0 : j = 0 := by
          have : j + 4 ≤ 4 := by simpa using hjc
          omega
        subst hj0
        rw [FlagK.E_zero, bot_inf_eq]
      · intro _
        rw [show ([0, 2, 3, 4] : List ℕ).getD 3 0 = 4 from rfl, Vsub_self, sup_top_eq]

private theorem plh_ok_iff (p L : Submodule K (Fin 4 → K))
    (hp : finrank K p = 1) (hpL : p ≤ L) (hL : L ⊓ Vsub 4 2 = ⊥) :
    (![1, 0] : Fin 2 → K) ∉ p.map (rho (K := K)) ↔ p ⊓ Vsub 4 3 = ⊥ := by
  have hp2 : p ⊓ Vsub 4 2 = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right (Vsub (K := K) 4 2) hpL).trans (le_of_eq hL))
  obtain ⟨v, hv0, rfl⟩ := exists_eq_span_of_finrank_eq_one hp
  have hvV2 : v ∉ Vsub 4 2 := by
    intro hv
    have hmem : v ∈ K ∙ v ⊓ Vsub 4 2 := ⟨Submodule.mem_span_singleton_self v, hv⟩
    rw [hp2] at hmem
    exact hv0 (by simpa using hmem)
  have hrv0 : rho (K := K) v ≠ 0 := by
    intro h
    exact hvV2 (by rw [← ker_rho]; exact LinearMap.mem_ker.mpr h)
  have hmap : (K ∙ v).map (rho (K := K)) = K ∙ rho v := by
    rw [Submodule.map_span, Set.image_singleton]
  have hrho : rho (K := K) v = ![v 2, v 3] := by
    funext i
    fin_cases i
    · rw [rho_apply]
      exact congrArg v (by decide)
    · rw [rho_apply]
      exact congrArg v (by decide)
  have hmem_single : (![1, 0] : Fin 2 → K) ∈ K ∙ rho (K := K) v ↔ v 3 = 0 := by
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, ha⟩
      rw [hrho] at ha
      have h1 : a * v 3 = 0 := by
        have := congrFun ha 1
        simpa using this
      have h0 : a * v 2 = 1 := by
        have := congrFun ha 0
        simpa using this
      have ha0 : a ≠ 0 := by
        intro h
        rw [h, zero_mul] at h0
        exact zero_ne_one h0
      exact (mul_eq_zero.mp h1).resolve_left ha0
    · intro hv3
      have hv2ne : v 2 ≠ 0 := by
        intro h2
        apply hrv0
        rw [hrho]
        funext i
        fin_cases i <;> simp [h2, hv3]
      refine ⟨(v 2)⁻¹, ?_⟩
      rw [hrho]
      funext i
      fin_cases i <;> simp [hv3, hv2ne, inv_mul_cancel₀]
  have hdisj : (K ∙ v) ⊓ Vsub 4 3 = ⊥ ↔ v 3 ≠ 0 := by
    constructor
    · intro hbot hv3
      have hvV3 : v ∈ Vsub 4 3 := by
        intro j hj
        have hj3 : j = 3 := by
          apply Fin.ext
          have := j.isLt
          omega
        rw [hj3]
        exact hv3
      have hmem : v ∈ K ∙ v ⊓ Vsub 4 3 := ⟨Submodule.mem_span_singleton_self v, hvV3⟩
      rw [hbot] at hmem
      exact hv0 (by simpa using hmem)
    · intro hv3ne
      rw [Submodule.eq_bot_iff]
      rintro u ⟨hu, huV3⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
      have h3 : a * v 3 = 0 := by
        have := huV3 3 (by decide)
        simpa using this
      have ha : a = 0 := (mul_eq_zero.mp h3).resolve_right hv3ne
      simp [ha]
  rw [hmap, hdisj]
  exact not_congr hmem_single

@[expose] noncomputable def D211 : ClsData K where
  ok c := (![1, 0] : Fin 2 → K) ∉ c
  good _ M := M ⊓ sgS K f 4 M = ⊥

theorem genSet_a3_211_eq :
    genSet K f 4 [0, 2, 3, 4] [] = admSet (AdmS (D211 (K := K) f)) := by
  ext x
  simp only [genSet, Set.mem_setOf_eq, admSet, AdmS, D211]
  have hfar_iff := plh_mem_farSet_a3_211_iff (K := K) x
  have hle : ∀ i, i < ([0, 2, 3, 4] : List ℕ).length →
      ([0, 2, 3, 4] : List ℕ).getD i 0 ≤ 4 := by
    intro i hi
    have hi4 : i < 4 := by simpa using hi
    interval_cases i <;> decide
  have hmono : ∀ i, i + 1 < ([0, 2, 3, 4] : List ℕ).length →
      ([0, 2, 3, 4] : List ℕ).getD i 0 ≤
        ([0, 2, 3, 4] : List ℕ).getD (i + 1) 0 := by
    intro i hi
    have hi3 : i < 3 := by
      have : i + 1 < 4 := by simpa using hi
      omega
    interval_cases i <;> decide
  constructor
  · rintro ⟨hfar, hblock⟩
    have hfar' := hfar_iff.mp hfar
    refine ⟨hfar'.2, ?_, ?_⟩
    · exact (plh_ok_iff (K := K) (x.E 1) (x.E 2) (FlagK.finrank_E_one x)
        (FlagK.E_one_le_two x) hfar'.2).mpr hfar'.1
    · have hb := hblock 0 (by decide)
      rw [blockOK] at hb
      have hb1 := hb 1 (by decide)
      simp only [List.getD_nil, Bool.false_eq_true, ↓reduceIte] at hb1
      simpa [blockU, Vsub_zero] using hb1
  · rintro ⟨hL2, hok, hgood⟩
    have h1 : x.E 1 ⊓ Vsub 4 3 = ⊥ :=
      (plh_ok_iff (K := K) (x.E 1) (x.E 2) (FlagK.finrank_E_one x)
        (FlagK.E_one_le_two x) hL2).mp hok
    have hfar : x ∈ farSet 4 [0, 2, 3, 4] := hfar_iff.mpr ⟨h1, hL2⟩
    refine ⟨hfar, ?_⟩
    intro i hi
    have hi3 : i < 3 := by
      have : i + 1 < 4 := by simpa using hi
      omega
    interval_cases i
    · rw [blockOK_iff_of_far f hle hmono hfar (by decide)]
      intro r hr0 hrm
      have hr1 : r = 1 := by
        have : r < 2 := by simpa using hrm
        omega
      subst hr1
      simp only [List.getD_nil, Bool.false_eq_true, ↓reduceIte]
      simpa [blockU, Vsub_zero] using hgood
    · exact blockOK_of_size_one f hle hmono hfar (by decide) (by decide)
    · exact blockOK_of_size_one f hle hmono hfar (by decide) (by decide)

end CFSG.ClassicalInvolution.Phan.PhanE

end
