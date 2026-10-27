module

public import CFSG.Quasithin.Background.F7TwoInvSporGen
public import CFSG.CGT.M24R.WrapM24Inv

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem m24_closure_eq_top : Subgroup.closure ({m24a, m24b} : Set NativeSporadic.M24) = ⊤ :=
  closure_pair_eq_top m24_eq _ _

theorem m24_class1 (x c : NativeSporadic.M24)
    (h : (x : Equiv.Perm (Fin 24)) = c * m24Rep1 * (c : Equiv.Perm (Fin 24))⁻¹) :
    InvAutGen NativeSporadic.M24 (MulAut.conj x) :=
  invAutGen_of_hom_class NativeSporadic.M24.subtype m24_closure_eq_top (A := m24gA) (B := m24gB)
    (D := m24gB⁻¹) (r := m24Rep1) (u := x) rfl rfl (d := m24b⁻¹) (c := c) rfl
    (sa := 1) (ma := 3) (sb := 2) (mb := 3) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun y => by simp [MulAut.conj_apply]) h

theorem m24Rep2_eq : m24Rep2 = List.formPerm [0, 4] * List.formPerm [2, 8] *
    List.formPerm [3, 13] * List.formPerm [5, 11] * List.formPerm [6, 16] *
    List.formPerm [7, 15] * List.formPerm [14, 23] * List.formPerm [17, 20] := by
  decide +kernel

theorem m24_class2 (x c : NativeSporadic.M24)
    (h : (x : Equiv.Perm (Fin 24)) = c * m24Rep2 * (c : Equiv.Perm (Fin 24))⁻¹) :
    InvAutGen NativeSporadic.M24 (MulAut.conj x) := by
  rw [m24Rep2_eq] at h
  exact invAutGen_of_hom_class NativeSporadic.M24.subtype m24_closure_eq_top (A := m24gA)
    (B := m24gB) (D := 1) (r := List.formPerm [0, 4] * List.formPerm [2, 8] *
      List.formPerm [3, 13] * List.formPerm [5, 11] * List.formPerm [6, 16] *
      List.formPerm [7, 15] * List.formPerm [14, 23] * List.formPerm [17, 20])
    (u := x) rfl rfl (d := 1) (c := c) rfl (sa := 0) (ma := 5) (sb := 0) (mb := 5)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun y => by simp [MulAut.conj_apply]) h

theorem invAutGen_carrier_M24 :
    ∀ φ : MulAut (NativeSporadic.Carrier .M24), φ * φ = 1 → φ ≠ 1 →
      InvAutGen (NativeSporadic.Carrier .M24) φ := by
  have hin : ∀ φ : MulAut NativeSporadic.M24, ∃ x : NativeSporadic.M24, MulAut.conj x = φ := by
    intro φ
    have : φ ∈ inner NativeSporadic.M24 := by
      rw [inner_eq_top_of_card_le m24_center_eq_bot' m24_mulAut_card]
      trivial
    exact this
  refine invAutGen_of_inner_classes NativeSporadic.M24 {m24Rep1, m24Rep2}
    m24_center_eq_bot' hin (fun u hu ho => ?_) (fun r hr x c h => ?_)
  · obtain ⟨r, hr, c, hc, hur⟩ := CFSG.CGT.M24R.m24_involution_conj_reps hu ho
    rw [m24InvReps_eq] at hr
    exact ⟨r, by simpa using hr, c, hc, hur⟩
  · rcases hr with rfl | rfl
    · exact m24_class1 x c h
    · exact m24_class2 x c h

end CFSG.Quasithin.F7Two
