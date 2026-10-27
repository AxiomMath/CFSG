module

public import CFSG.Quasithin.Background.F7TwoInvSporGen
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem m23_closure_eq_top : Subgroup.closure ({m23GenA, m23GenB} : Set NativeSporadic.M23) = ⊤ :=
  closure_pair_eq_top m23_eq_closure _ _

theorem m23_involution_conj
    {u : Equiv.Perm (Fin 23)} (hu : u ∈ NativeSporadic.M23)
    (hu2 : orderOf u = 2) : ∃ c ∈ NativeSporadic.M23, u = c * m23Rep1 * c⁻¹ := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, -, -⟩ := m23_oddcore_cover
  obtain ⟨hr1, hro1, -, -, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23InvReps_eq] at hok
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK hn m23Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) (by norm_num) [m23Rep1]
    (fun r hr => by
      rw [List.mem_singleton] at hr
      subst hr
      exact ⟨by simpa using hr1, hro1⟩) 4000 hok
  obtain ⟨r, hrm, c, hc, hur⟩ := hcov u (by simpa [m23Certificate_originalSubgroup] using hu) hu2
  rw [List.mem_singleton] at hrm
  subst hrm
  exact ⟨c, by simpa [← m23Certificate_originalSubgroup] using hc, hur⟩

theorem m23_class (x c : NativeSporadic.M23)
    (h : (x : Equiv.Perm (Fin 23)) = c * m23Rep1 * (c : Equiv.Perm (Fin 23))⁻¹) :
    InvAutGen NativeSporadic.M23 (MulAut.conj x) :=
  invAutGen_of_hom_class NativeSporadic.M23.subtype m23_closure_eq_top (A := m23PermA)
    (B := m23PermB) (D := m23PermB⁻¹) (r := m23Rep1) (u := x) rfl rfl (d := m23GenB⁻¹)
    (c := c) rfl (sa := 0) (ma := 3) (sb := 1) (mb := 3) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun y => by simp [MulAut.conj_apply]) h

theorem invAutGen_carrier_M23 :
    ∀ φ : MulAut (NativeSporadic.Carrier .M23), φ * φ = 1 → φ ≠ 1 →
      InvAutGen (NativeSporadic.Carrier .M23) φ := by
  have hin : ∀ φ : MulAut NativeSporadic.M23, ∃ x : NativeSporadic.M23, MulAut.conj x = φ := by
    intro φ
    have : φ ∈ inner NativeSporadic.M23 := by
      rw [inner_eq_top_of_card_le m23_center_eq_bot' m23_mulAut_card]
      trivial
    exact this
  refine invAutGen_of_inner_classes NativeSporadic.M23 {m23Rep1}
    m23_center_eq_bot' hin (fun u hu ho => ?_) (fun r hr x c h => ?_)
  · obtain ⟨c, hc, hur⟩ := m23_involution_conj hu ho
    exact ⟨_, rfl, c, hc, hur⟩
  · rw [Set.mem_singleton_iff] at hr
    subst hr
    exact m23_class x c h

end CFSG.Quasithin.F7Two
