module

public import CFSG.Quasithin.Background.F7TwoInvSporM22
public import CFSG.Quasithin.Background.SmithB45MatM22Rep
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitM22Fix
public import Certificates.Certificate1037115

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W115

open CFSG.Blueprint CFSG.CharacterTheory.SteinbergBY CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M22 CFSG.Quasithin.F7Two
  CFSG.OddStandard.HigherRank.YamadaG23 CFSG.ComponentClassification.OuterAutomorphisms

theorem w115_rank34_checks :
    mulT (mulT w115PA (subIdT (tab34P w115HA))) w115QA = idT 24 ∧
      mulT (mulT w115PD (subIdT (tab34P w115HD))) w115QD = idT 24 ∧
      mulT (mulT w115PR (subIdT (tab34P w115HR))) w115QR = idT 24 :=
  Certificates.certificate1037115

theorem untab_subIdT {n : ℕ} (A : Vector (Vector (ZMod 2) n) n) :
    untab (subIdT A) = untab A - 1 := by
  ext i j
  simp only [subIdT, untab_apply, Matrix.sub_apply, Matrix.one_apply, Fin.getElem_fin,
    Vector.getElem_ofFn]
  rfl

theorem le_rank_of_mul_mul_eq_one {K : Type*} [Field K] {m n : ℕ}
    {P : Matrix (Fin m) (Fin n) K} {T : Matrix (Fin n) (Fin n) K} {Q : Matrix (Fin n) (Fin m) K}
    (h : P * T * Q = 1) : m ≤ T.rank := by
  have h1 : (P * T * Q).rank = m := by rw [h, Matrix.rank_one, Fintype.card_fin]
  calc m = (P * T * Q).rank := h1.symm
    _ ≤ (P * T).rank := Matrix.rank_mul_le_left _ _
    _ ≤ T.rank := Matrix.rank_mul_le_right _ _

theorem w115_conj_mul_conj_eq_inv {G : Type*} [Group G] {r y : G} (hr : r * r = 1) :
    r * (r * (y * r * y⁻¹)) * r⁻¹ = (r * (y * r * y⁻¹))⁻¹ := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have h1 : r * (r * (y * r * y⁻¹)) * r⁻¹ = r * r * (y * r * y⁻¹) * r⁻¹ := by group
  have h2 : (r * (y * r * y⁻¹))⁻¹ = y * r⁻¹ * y⁻¹ * r⁻¹ := by group
  rw [h1, h2, hr, one_mul, hri]

theorem w115_mul_conj_mem {r y : Equiv.Perm (Fin 22)}
    (hr : ∀ h ∈ NativeSporadic.M22, r * h * r⁻¹ ∈ NativeSporadic.M22)
    (hr2 : r * r ∈ NativeSporadic.M22) (hy : y ∈ NativeSporadic.M22) :
    r * (y * r * y⁻¹) ∈ NativeSporadic.M22 := by
  have h : r * (y * r * y⁻¹) = r * y * r⁻¹ * (r * r) * y⁻¹ := by group
  rw [h]
  exact mul_mem (mul_mem (hr y hy) hr2) (inv_mem hy)

theorem w115Y_mem : w115Y ∈ NativeSporadic.M22 :=
  mul_mem (mul_mem m22b.2 m22a.2) m22b.2

theorem w115HA_mem : w115HA ∈ NativeSporadic.M22 :=
  mul_mem m22a.2 (mul_mem (mul_mem w115Y_mem m22a.2) (inv_mem w115Y_mem))

theorem w115HD_mem :
    w115HD ∈ NativeSporadic.M22 :=
  w115_mul_conj_mem m22_delta_normalizes m22_delta_sq w115Y_mem

theorem w115R2_eq : m22OutRep2 = w115R2 :=
  m22OutRep2_eq_cycles

theorem w115HR_mem :
    w115HR ∈ NativeSporadic.M22 := by
  have hk : m22Delta⁻¹ * w115R2 ∈ NativeSporadic.M22 := by
    rw [← w115R2_eq, ← m22Certificate_originalSubgroup]
    exact m22_out_rep_data2.1
  have hr : ∀ h ∈ NativeSporadic.M22, w115R2 * h * w115R2⁻¹ ∈ NativeSporadic.M22 := by
    intro h hh
    have he : w115R2 * h * w115R2⁻¹ =
        m22Delta * ((m22Delta⁻¹ * w115R2) * h * (m22Delta⁻¹ * w115R2)⁻¹) * m22Delta⁻¹ := by
      group
    rw [he]
    exact m22_delta_normalizes _ (mul_mem (mul_mem hk hh) (inv_mem hk))
  have hr2 : w115R2 * w115R2 = 1 := by decide +kernel
  exact w115_mul_conj_mem hr (hr2 ▸ one_mem _) m22a.2

theorem orderOf_w115HA : orderOf w115HA = 3 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem orderOf_w115HD : orderOf w115HD = 3 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem orderOf_w115HR : orderOf w115HR = 3 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

section Rep


theorem untab_subIdT_tab34P (g : G22) :
    untab (subIdT (tab34P (g : Equiv.Perm (Fin 22)))) = rep34 g - 1 := by
  rw [untab_subIdT, show tab34P (g : Equiv.Perm (Fin 22)) = tab34 g from rfl, untab_tab34]

theorem le_rank_rep34_sub_one {g : G22} {P : Vector (Vector (ZMod 2) 34) 24}
    {Q : Vector (Vector (ZMod 2) 24) 34}
    (h : mulT (mulT P (subIdT (tab34P (g : Equiv.Perm (Fin 22))))) Q = idT 24) :
    24 ≤ (rep34 g - 1).rank := by
  have h' := congrArg untab h
  rw [untab_mulT, untab_mulT, untab_idT, untab_subIdT_tab34P] at h'
  exact le_rank_of_mul_mul_eq_one h'

theorem rep34_conj_sub_one (c g : G22) :
    rep34 c⁻¹ * (rep34 (c * g * c⁻¹) - 1) * rep34 c = rep34 g - 1 := by
  have h : rep34 c⁻¹ * rep34 c = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : rep34 c⁻¹ * (rep34 c * rep34 g * rep34 c⁻¹) * rep34 c = rep34 g :=
    calc rep34 c⁻¹ * (rep34 c * rep34 g * rep34 c⁻¹) * rep34 c
        = rep34 c⁻¹ * rep34 c * rep34 g * (rep34 c⁻¹ * rep34 c) := by simp only [mul_assoc]
      _ = rep34 g := by rw [h, one_mul, mul_one]
  rw [map_mul, map_mul, mul_sub, sub_mul, mul_one, h, h2]

theorem rank_rep34_sub_one_le_conj (c g : G22) :
    (rep34 g - 1).rank ≤ (rep34 (c * g * c⁻¹) - 1).rank := by
  rw [← rep34_conj_sub_one c g]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem w115_exists_inv_rank34_of_rep {α : MulAut G22} {u r y c : Equiv.Perm (Fin 22)}
    (hc : c ∈ NativeSporadic.M22) (hα : ∀ h : G22, (α h : Equiv.Perm (Fin 22)) = u * h * u⁻¹)
    (hu : u = c * r * c⁻¹) (hrr : r * r = 1) (hh : r * (y * r * y⁻¹) ∈ NativeSporadic.M22)
    (h3 : orderOf (r * (y * r * y⁻¹)) = 3)
    (hrk : 24 ≤ (rep34 ⟨r * (y * r * y⁻¹), hh⟩ - 1).rank) :
    ∃ g : G22, orderOf g = 3 ∧ α g = g⁻¹ ∧ 24 ≤ (rep34 g - 1).rank := by
  set h0 : G22 := ⟨r * (y * r * y⁻¹), hh⟩ with h0_def
  set c0 : G22 := ⟨c, hc⟩ with c0_def
  refine ⟨c0 * h0 * c0⁻¹, ?_, ?_, hrk.trans (rank_rep34_sub_one_le_conj c0 h0)⟩
  · have hsc : SemiconjBy c0 h0 (c0 * h0 * c0⁻¹) := by
      unfold SemiconjBy
      group
    rw [← SemiconjBy.orderOf_eq c0 hsc, h0_def, Subgroup.orderOf_mk, h3]
  · apply Subtype.ext
    rw [hα, hu]
    show c * r * c⁻¹ * (c * (r * (y * r * y⁻¹)) * c⁻¹) * (c * r * c⁻¹)⁻¹ =
      (c * (r * (y * r * y⁻¹)) * c⁻¹)⁻¹
    calc c * r * c⁻¹ * (c * (r * (y * r * y⁻¹)) * c⁻¹) * (c * r * c⁻¹)⁻¹
        = c * (r * (r * (y * r * y⁻¹)) * r⁻¹) * c⁻¹ := by group
      _ = c * (r * (y * r * y⁻¹))⁻¹ * c⁻¹ := by rw [w115_conj_mul_conj_eq_inv hrr]
      _ = (c * (r * (y * r * y⁻¹)) * c⁻¹)⁻¹ := by group

theorem w115_exists_inv_rank34
    (α : MulAut G22) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    ∃ g : G22, orderOf g = 3 ∧ α g = g⁻¹ ∧ 24 ≤ (rep34 g - 1).rank := by
  obtain ⟨hA, hD, hR⟩ := w115_rank34_checks
  by_cases hin : α ∈ inner NativeSporadic.M22
  · obtain ⟨u, hu2, huM, hαu⟩ :=
      lit_inner_invol_conj NativeSporadic.M22 m22_center_eq_bot' α hα2 hα1 hin
    obtain ⟨c, hc, huc⟩ := m22_inner_cover huM hu2
    rw [show m22Rep1 = m22gA by decide +kernel] at huc
    exact w115_exists_inv_rank34_of_rep (y := w115Y) hc hαu huc (by decide +kernel) w115HA_mem
      orderOf_w115HA (le_rank_rep34_sub_one (g := ⟨w115HA, w115HA_mem⟩) hA)
  · obtain ⟨u, hu2, huδ, hαu⟩ := lit_outer_invol_conj NativeSporadic.M22 m22Delta
      m22_delta_normalizes m22_delta_sq m22_center_eq_bot' m22_delta_outer m22_mulAut_card α hα2
      hin
    obtain ⟨r, hr, c, hc, huc⟩ := m22_outer_cover_conj u huδ hu2
    rcases hr with rfl | rfl
    · rw [show m22OutRep1 = w115Delta by decide +kernel] at huc
      exact w115_exists_inv_rank34_of_rep (y := w115Y) hc hαu huc (by decide +kernel) w115HD_mem
        orderOf_w115HD (le_rank_rep34_sub_one (g := ⟨w115HD, w115HD_mem⟩) hD)
    · rw [w115R2_eq] at huc
      exact w115_exists_inv_rank34_of_rep (y := m22gA) hc hαu huc (by decide +kernel) w115HR_mem
        orderOf_w115HR (le_rank_rep34_sub_one (g := ⟨w115HR, w115HR_mem⟩) hR)

end Rep

end CFSG.LocalAnalysis.WeakClosure81.W115
