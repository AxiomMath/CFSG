module

public import CFSG.Quasithin.Background.F7TwoInvSporGen
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem m11_involution_conj
    {u : Equiv.Perm (Fin 11)} (hu : u ∈ NativeSporadic.M11)
    (hu2 : orderOf u = 2) :
    ∃ c ∈ NativeSporadic.M11, u = c * evalCodes [m11gA, m11gB] [1] * c⁻¹ := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m11Certificate := m11Certificate_check.1
  obtain ⟨hok, -, -⟩ := m11_oddcore_cover
  obtain ⟨hr, hro, -, -, -⟩ := m11_rep_data
  have hA : m11gA ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11a.2
  have hB : m11gB ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11b.2
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK hn m11Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) (m := 2) (by norm_num) [evalCodes [m11gA, m11gB] [1]]
    (by simpa using ⟨hr, hro⟩) 400 (by simpa [m11InvReps, m11InvRepWords] using hok)
  obtain ⟨r, hrm, c, hc, hur⟩ := hcov u (by simpa [m11Certificate_originalSubgroup] using hu) hu2
  rw [List.mem_singleton] at hrm
  subst hrm
  exact ⟨c, by simpa [← m11Certificate_originalSubgroup] using hc, hur⟩

theorem m11_class (x c : NativeSporadic.M11)
    (h : (x : Equiv.Perm (Fin 11)) =
      c * evalCodes [m11gA, m11gB] [1] * (c : Equiv.Perm (Fin 11))⁻¹) :
    InvAutGen NativeSporadic.M11 (MulAut.conj x) :=
  invAutGen_of_hom_class NativeSporadic.M11.subtype m11_closure_eq_top (A := m11gA) (B := m11gB)
    (D := m11gB⁻¹) (r := evalCodes [m11gA, m11gB] [1]) (u := x) rfl rfl (d := m11b⁻¹)
    (c := c) rfl (sa := 0) (ma := 3) (sb := 1) (mb := 3) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun y => by simp [MulAut.conj_apply]) h

theorem invAutGen_carrier_M11 :
    ∀ φ : MulAut (NativeSporadic.Carrier .M11), φ * φ = 1 → φ ≠ 1 →
      InvAutGen (NativeSporadic.Carrier .M11) φ := by
  have hin : ∀ φ : MulAut NativeSporadic.M11, ∃ x : NativeSporadic.M11, MulAut.conj x = φ := by
    intro φ
    have : φ ∈ inner NativeSporadic.M11 := by
      rw [inner_eq_top_of_card_le m11_center_eq_bot' m11_mulAut_card]
      trivial
    exact this
  refine invAutGen_of_inner_classes NativeSporadic.M11 {evalCodes [m11gA, m11gB] [1]}
    m11_center_eq_bot' hin (fun u hu ho => ?_) (fun r hr x c h => ?_)
  · obtain ⟨c, hc, hur⟩ := m11_involution_conj hu ho
    exact ⟨_, rfl, c, hc, hur⟩
  · rw [Set.mem_singleton_iff] at hr
    subst hr
    exact m11_class x c h

end CFSG.Quasithin.F7Two
