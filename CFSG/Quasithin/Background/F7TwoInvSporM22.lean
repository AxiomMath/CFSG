module

public import CFSG.Quasithin.Background.F7TwoInvSporOut
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public import CFSG.Quasithin.Background.F7TwoInvSporGen

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem m22_closure_eq_top : Subgroup.closure ({m22a, m22b} : Set NativeSporadic.M22) = ⊤ :=
  closure_pair_eq_top m22_eq _ _

theorem m22_inner_cover
    {u : Equiv.Perm (Fin 22)} (hu : u ∈ NativeSporadic.M22) (hu2 : orderOf u = 2) :
    ∃ c ∈ NativeSporadic.M22, u = c * m22Rep1 * c⁻¹ := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, -, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, -, -, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK hn m22Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) (by norm_num) [m22Rep1]
    (fun r hr => by
      rw [List.mem_singleton] at hr
      subst hr
      exact ⟨by simpa using hr1, hro1⟩) 2000 hok
  obtain ⟨r, hrm, c, hc, hur⟩ := hcov u (by simpa [m22Certificate_originalSubgroup] using hu) hu2
  rw [List.mem_singleton] at hrm
  subst hrm
  exact ⟨c, by simpa [← m22Certificate_originalSubgroup] using hc, hur⟩

theorem m22_outer_cover_conj :
    ∀ u : Equiv.Perm (Fin 22), m22Delta⁻¹ * u ∈ NativeSporadic.M22 → orderOf u = 2 →
      ∃ r ∈ ({m22OutRep1, m22OutRep2} : Set (Equiv.Perm (Fin 22))),
        ∃ c ∈ NativeSporadic.M22, u = c * r * c⁻¹ := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, -, -⟩ := m22_outer_cover
  obtain ⟨hr1, hro1, -⟩ := m22_out_rep_data1
  obtain ⟨hr2, hro2, -⟩ := m22_out_rep_data2
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
      m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
    rw [m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq
  have hreps : ∀ r ∈ m22OutReps,
      m22Delta⁻¹ * r ∈ m22Certificate.originalSubgroup ∧ orderOf r = 2 := by
    intro r hr
    rw [m22OutReps_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨hr1, hro1⟩
    · exact ⟨hr2, hro2⟩
  intro u hu ho
  rw [← m22Certificate_originalSubgroup] at hu
  obtain ⟨r, hr, c, hc, hur⟩ := (exists_conj_of_repsOK hn m22Certificate hQ
    (pairTables_spec hn hA hB) m22Delta hg₀ (by norm_num) m22OutReps hreps 2000 hok).1 u hu ho
  rw [m22OutReps_eq] at hr
  refine ⟨r, by simpa using hr, c, ?_, hur⟩
  rwa [← m22Certificate_originalSubgroup]

theorem m22OutRep2_eq_cycles : m22OutRep2 = List.formPerm [0, 21] * List.formPerm [1, 16] *
    List.formPerm [3, 18] * List.formPerm [5, 14] * List.formPerm [7, 8] *
    List.formPerm [12, 17] * List.formPerm [15, 19] := by
  decide +kernel

theorem m22_class_inner (x c : NativeSporadic.M22)
    (h : (x : Equiv.Perm (Fin 22)) = c * m22Rep1 * (c : Equiv.Perm (Fin 22))⁻¹) :
    InvAutGen NativeSporadic.M22 (MulAut.conj x) :=
  invAutGen_of_hom_class NativeSporadic.M22.subtype m22_closure_eq_top (A := m22gA) (B := m22gB)
    (D := m22gB⁻¹) (r := m22Rep1) (u := x) rfl rfl (d := m22b⁻¹) (c := c) rfl
    (sa := 0) (ma := 3) (sb := 1) (mb := 3) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun y => by simp [MulAut.conj_apply]) h

theorem m22_class_out1 (α : MulAut NativeSporadic.M22) (u : Equiv.Perm (Fin 22))
    (c : NativeSporadic.M22)
    (hα : ∀ y : NativeSporadic.M22, (α y : Equiv.Perm (Fin 22)) = u * y * u⁻¹)
    (h : u = c * m22OutRep1 * (c : Equiv.Perm (Fin 22))⁻¹) : InvAutGen NativeSporadic.M22 α :=
  invAutGen_of_hom_class NativeSporadic.M22.subtype m22_closure_eq_top (A := m22gA) (B := m22gB)
    (D := 1) (r := m22OutRep1) (u := u) rfl rfl (d := 1) (c := c) rfl
    (sa := 0) (ma := 5) (sb := 0) (mb := 11) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hα h

theorem m22_class_out2 (α : MulAut NativeSporadic.M22) (u : Equiv.Perm (Fin 22))
    (c : NativeSporadic.M22)
    (hα : ∀ y : NativeSporadic.M22, (α y : Equiv.Perm (Fin 22)) = u * y * u⁻¹)
    (h : u = c * m22OutRep2 * (c : Equiv.Perm (Fin 22))⁻¹) : InvAutGen NativeSporadic.M22 α := by
  rw [m22OutRep2_eq_cycles] at h
  exact invAutGen_of_hom_class NativeSporadic.M22.subtype m22_closure_eq_top (A := m22gA)
    (B := m22gB) (D := 1) (r := List.formPerm [0, 21] * List.formPerm [1, 16] *
      List.formPerm [3, 18] * List.formPerm [5, 14] * List.formPerm [7, 8] *
      List.formPerm [12, 17] * List.formPerm [15, 19])
    (u := u) rfl rfl (d := 1) (c := c) rfl (sa := 0) (ma := 3) (sb := 0) (mb := 3)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hα h

theorem invAutGen_carrier_M22 :
    ∀ φ : MulAut (NativeSporadic.Carrier .M22), φ * φ = 1 → φ ≠ 1 →
      InvAutGen (NativeSporadic.Carrier .M22) φ := by
  intro φ h2 h1
  by_cases hin : φ ∈ inner NativeSporadic.M22
  · refine invAutGen_of_inner_involutory NativeSporadic.M22 {m22Rep1} m22_center_eq_bot'
      (fun u hu ho => ?_) (fun r hr x c h => ?_) φ hin h2 h1
    · obtain ⟨c, hc, hur⟩ := m22_inner_cover hu ho
      exact ⟨_, rfl, c, hc, hur⟩
    · rw [Set.mem_singleton_iff] at hr
      subst hr
      exact m22_class_inner x c h
  · refine invAutGen_of_outer_involutory NativeSporadic.M22 m22Delta m22_delta_normalizes
      m22_delta_sq m22_center_eq_bot' m22_delta_outer m22_mulAut_card
      {m22OutRep1, m22OutRep2} m22_outer_cover_conj (fun r hr α u c hα h => ?_) φ h2 hin
    rcases hr with rfl | rfl
    · exact m22_class_out1 α u c hα h
    · exact m22_class_out2 α u c hα h

end CFSG.Quasithin.F7Two
