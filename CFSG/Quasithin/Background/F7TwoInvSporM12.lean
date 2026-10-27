module

public import CFSG.Quasithin.Background.F7TwoInvSporOut
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalOuter
public import CFSG.Quasithin.Background.F7TwoInvSporGen

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.M12Cover

theorem m12_involution_conj
    {u : Equiv.Perm (Fin 12)}
    (hu : u ∈ NativeSporadic.M12) (hu2 : orderOf u = 2) :
    ∃ r ∈ ({m12Rep1, m12Rep2} : Set (Equiv.Perm (Fin 12))),
      ∃ c ∈ NativeSporadic.M12, u = c * r * c⁻¹ := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  obtain ⟨hok, -, -⟩ := m12_oddcore_cover
  obtain ⟨hr1, hro1, -, -, -⟩ := m12_rep_data1
  obtain ⟨hr2, hro2, -, -, -⟩ := m12_rep_data2
  have hA : m12gA ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hreps : ∀ r ∈ m12InvReps,
      (1 : Equiv.Perm (Fin 12))⁻¹ * r ∈ m12Certificate.originalSubgroup ∧ orderOf r = 2 := by
    intro r hr
    rw [m12InvReps_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨by simpa using hr1, hro1⟩
    · exact ⟨by simpa using hr2, hro2⟩
  obtain ⟨r, hr, c, hc, hur⟩ := (exists_conj_of_repsOK hn m12Certificate hQ
    (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh) (by norm_num) m12InvReps
    hreps 1000 hok).1 u (by simpa [m12Certificate_originalSubgroup] using hu) hu2
  rw [m12InvReps_eq] at hr
  exact ⟨r, by simpa using hr, c, by simpa [← m12Certificate_originalSubgroup] using hc, hur⟩

theorem m12_class1 (x c : NativeSporadic.M12)
    (h : (x : Equiv.Perm (Fin 12)) = c * m12Rep1 * (c : Equiv.Perm (Fin 12))⁻¹) :
    InvAutGen NativeSporadic.M12 (MulAut.conj x) :=
  invAutGen_of_hom_class NativeSporadic.M12.subtype m12_closure_eq_top (A := m12gA) (B := m12gB)
    (D := m12gB⁻¹) (r := m12Rep1) (u := x) rfl rfl (d := m12b⁻¹) (c := c) rfl
    (sa := 0) (ma := 3) (sb := 1) (mb := 3) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun y => by simp [MulAut.conj_apply]) h

theorem m12_class2 (x c : NativeSporadic.M12)
    (h : (x : Equiv.Perm (Fin 12)) = c * m12Rep2 * (c : Equiv.Perm (Fin 12))⁻¹) :
    InvAutGen NativeSporadic.M12 (MulAut.conj x) :=
  invAutGen_of_hom_class NativeSporadic.M12.subtype m12_closure_eq_top (A := m12gA) (B := m12gB)
    (D := m12gB) (r := m12Rep2) (u := x) rfl rfl (d := m12b) (c := c) rfl
    (sa := 0) (ma := 5) (sb := 1) (mb := 3) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun y => by simp [MulAut.conj_apply]) h

@[expose] noncomputable def m12Emb :
    NativeSporadic.M12 →* Equiv.Perm (Fin 24) :=
  blockGroup.subtype.comp m12EquivD.toMonoidHom

theorem m12Emb_a :
    m12Emb m12a = m12A1 :=
  m12EquivD_apply (Subgroup.subset_closure (Set.mem_insert _ _))

theorem m12Emb_b :
    m12Emb m12b = m12B1 :=
  m12EquivD_apply (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem m12Emb_beta
    (g : NativeSporadic.M12) :
    m12Emb (beta g) = m12Sigma * m12Emb g * m12Sigma⁻¹ := by
  rw [beta, autModelEquiv_apply, autModelHom_apply]
  change ((m12EquivD (m12EquivD.symm _) : blockGroup) : Equiv.Perm (Fin 24)) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem m12_outer
    (α : MulAut NativeSporadic.M12) (h2 : orderOf α = 2) (hα : α ∉ inner NativeSporadic.M12) :
    InvAutGen NativeSporadic.M12 α := by
  obtain ⟨g, rfl⟩ := exists_conj_beta_of_outer h2 hα
  refine invAutGen_of_hom_class m12Emb m12_closure_eq_top (A := m12A1) (B := m12B1)
    (D := m12B1) (r := m12Sigma) (u := m12Emb g * m12Sigma * (m12Emb g)⁻¹) m12Emb_a m12Emb_b
    (d := m12b) (c := g) m12Emb_b (sa := 0) (ma := 3) (sb := 1) (mb := 3)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun x => ?_) rfl
  rw [conj_conj_inv_apply, map_mul, map_mul, m12Emb_beta]
  simp only [map_inv, map_mul]
  group

theorem invAutGen_M12 :
    ∀ φ : MulAut NativeSporadic.M12, φ * φ = 1 → φ ≠ 1 → InvAutGen NativeSporadic.M12 φ := by
  intro φ h2 h1
  by_cases hin : φ ∈ inner NativeSporadic.M12
  · refine invAutGen_of_inner_involutory NativeSporadic.M12 {m12Rep1, m12Rep2}
      m12_center_eq_bot' (fun u hu ho => m12_involution_conj hu ho)
      (fun r hr x c h => ?_) φ hin h2 h1
    rcases hr with rfl | rfl
    · exact m12_class1 x c h
    · exact m12_class2 x c h
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact m12_outer φ (orderOf_eq_prime (by rw [sq]; exact h2) h1) hin

theorem invAutGen_carrier_M12 :
    ∀ φ : MulAut (NativeSporadic.Carrier .M12), φ * φ = 1 → φ ≠ 1 →
      InvAutGen (NativeSporadic.Carrier .M12) φ :=
  invAutGen_M12

end CFSG.Quasithin.F7Two
