module

public import CFSG.LocalAnalysis.WeakClosure81.W115ConjOutAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W115

open CFSG.Blueprint


noncomputable def w115_nu :
    CFSG.Sporadic.Mathieu.Asc1113M22.N0 →*
      MulAut CFSG.Sporadic.Mathieu.Asc1113M22.H0 :=
  (Subgroup.normalizerMonoidHom CFSG.Sporadic.Mathieu.Asc1113M22.H0).comp
    (Subgroup.inclusion CFSG.Sporadic.Mathieu.Asc1113M22.N0_le_normalizer)

theorem w115_nu_apply (v : CFSG.Sporadic.Mathieu.Asc1113M22.N0)
    (x : CFSG.Sporadic.Mathieu.Asc1113M22.H0) :
    ((w115_nu v x : CFSG.Sporadic.Mathieu.Asc1113M22.H0) : Equiv.Perm (Fin 22)) =
      (v : Equiv.Perm (Fin 22)) * (x : Equiv.Perm (Fin 22)) *
        (v : Equiv.Perm (Fin 22))⁻¹ := by
  rfl

theorem w115_nu_h (h : CFSG.Sporadic.Mathieu.Asc1113M22.H0) :
    w115_nu ⟨h, w115_H0_le_N0 h.2⟩ = MulAut.conj h := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rfl

@[expose] def w115_P (β : MulAut CFSG.Sporadic.Mathieu.Asc1113M22.H0) : Prop :=
  ∃ h : Fin 4 → CFSG.Sporadic.Mathieu.Asc1113M22.H0,
    CFSG.ComponentClassification.OuterAutomorphisms.inner
        CFSG.Sporadic.Mathieu.Asc1113M22.H0 ≤
      Subgroup.closure
        (Set.range fun i => MulAut.conj (h i) * β * (MulAut.conj (h i))⁻¹)

theorem w115_P_conj {β : MulAut CFSG.Sporadic.Mathieu.Asc1113M22.H0}
    (x : CFSG.Sporadic.Mathieu.Asc1113M22.H0) (hP : w115_P β) :
    w115_P (MulAut.conj x * β * (MulAut.conj x)⁻¹) := by
  obtain ⟨h, hh⟩ := hP
  let f : MulAut CFSG.Sporadic.Mathieu.Asc1113M22.H0 →*
      MulAut CFSG.Sporadic.Mathieu.Asc1113M22.H0 :=
    (MulAut.conj (MulAut.conj x)).toMonoidHom
  have hf : ∀ g : MulAut CFSG.Sporadic.Mathieu.Asc1113M22.H0,
      f g = MulAut.conj x * g * (MulAut.conj x)⁻¹ := fun g => rfl
  have hinner_le : CFSG.ComponentClassification.OuterAutomorphisms.inner
        CFSG.Sporadic.Mathieu.Asc1113M22.H0 ≤
      f '' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        CFSG.Sporadic.Mathieu.Asc1113M22.H0) := by
    rintro g ⟨y, rfl⟩
    exact ⟨MulAut.conj (x⁻¹ * y * x), ⟨x⁻¹ * y * x, rfl⟩, by
      simp only [hf, map_mul, map_mul, map_inv]
      group⟩
  refine ⟨fun i => x * h i * x⁻¹, ?_⟩
  have himg : (Set.range fun i => MulAut.conj (x * h i * x⁻¹) *
        (MulAut.conj x * β * (MulAut.conj x)⁻¹) *
        (MulAut.conj (x * h i * x⁻¹))⁻¹) =
      f '' (Set.range fun i => MulAut.conj (h i) * β * (MulAut.conj (h i))⁻¹) := by
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext i
    simp only [Function.comp_apply, map_mul, map_inv, hf]
    group
  have hmap := MonoidHom.map_closure f
    (Set.range fun i => MulAut.conj (h i) * β * (MulAut.conj (h i))⁻¹)
  rw [himg, ← hmap]
  intro g hg
  obtain ⟨k, hk, hfk⟩ := hinner_le hg
  exact Subgroup.mem_map.mpr ⟨k, hh hk, hfk⟩

section Outer

open CFSG.Mathieu.Asc1113M22
open CFSG.Sporadic.Mathieu.Asc1113M22


private def w115_TG : Fin 4 → Equiv.Perm (Fin 22) := ![tg1, tg2, tg3, tg4]

private def w115_UG : Fin 4 → Equiv.Perm (Fin 22) := ![ug1, ug2, ug3, ug4]

private theorem w115_TG_mem_N0 (i : Fin 4) : w115_TG i ∈ N0 := by
  fin_cases i <;> simp [w115_TG, tg1_mem_N0, tg2_mem_N0, tg3_mem_N0, tg4_mem_N0]

private theorem w115_UG_mem_N0 (i : Fin 4) : w115_UG i ∈ N0 := by
  fin_cases i <;> simp [w115_UG, ug1_mem_N0, ug2_mem_N0, ug3_mem_N0, ug4_mem_N0]

private theorem w115_TC4_eq (i : Fin 4) :
    TC4 i = w115_TG i * t * (w115_TG i)⁻¹ := by
  fin_cases i <;> simp [TC4, w115_TG, qt1_eq_conj, qt2_eq_conj, qt3_eq_conj, qt4_eq_conj]

private theorem w115_UC4_eq (i : Fin 4) :
    UC4 i = w115_UG i * u * (w115_UG i)⁻¹ := by
  fin_cases i <;> simp [UC4, w115_UG, qu1_eq_conj, qu2_eq_conj, qu3_eq_conj, qu4_eq_conj]

theorem w115_nu_conj_t (g : N0) :
    ∃ h : H0, w115_nu (g * ⟨t, t_mem_N0⟩ * g⁻¹) =
      MulAut.conj h * w115_nu ⟨t, t_mem_N0⟩ * (MulAut.conj h)⁻¹ := by
  have ht2 : (⟨t, t_mem_N0⟩ : N0) * ⟨t, t_mem_N0⟩ = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    decide
  have hnu_t2 : w115_nu ⟨t, t_mem_N0⟩ * w115_nu ⟨t, t_mem_N0⟩ = 1 := by
    rw [← map_mul, ht2, map_one]
  rcases w115_N0_mem_cases_t g with ⟨h, hh⟩ | ⟨h, hh⟩
  · refine ⟨h, ?_⟩
    have hg : g = ⟨(h : Equiv.Perm (Fin 22)), w115_H0_le_N0 h.2⟩ := by
      apply Subtype.ext; exact hh
    simp only [hg, map_mul, map_inv, w115_nu_h]
  · refine ⟨h, ?_⟩
    have hg : g = ⟨(h : Equiv.Perm (Fin 22)), w115_H0_le_N0 h.2⟩ * ⟨t, t_mem_N0⟩ := by
      apply Subtype.ext; exact hh
    simp only [hg, map_mul, map_inv, w115_nu_h, hnu_t2, mul_one]
    group

theorem w115_nu_conj_u (g : N0) :
    ∃ h : H0, w115_nu (g * ⟨u, u_mem_N0⟩ * g⁻¹) =
      MulAut.conj h * w115_nu ⟨u, u_mem_N0⟩ * (MulAut.conj h)⁻¹ := by
  have hu2 : (⟨u, u_mem_N0⟩ : N0) * ⟨u, u_mem_N0⟩ = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    exact uU_sq
  have hnu_u2 : w115_nu ⟨u, u_mem_N0⟩ * w115_nu ⟨u, u_mem_N0⟩ = 1 := by
    rw [← map_mul, hu2, map_one]
  rcases w115_N0_mem_cases_u g with ⟨h, hh⟩ | ⟨h, hh⟩
  · refine ⟨h, ?_⟩
    have hg : g = ⟨(h : Equiv.Perm (Fin 22)), w115_H0_le_N0 h.2⟩ := by
      apply Subtype.ext; exact hh
    simp only [hg, map_mul, map_inv, w115_nu_h]
  · refine ⟨h, ?_⟩
    have hg : g = ⟨(h : Equiv.Perm (Fin 22)), w115_H0_le_N0 h.2⟩ * ⟨u, u_mem_N0⟩ := by
      apply Subtype.ext; exact hh
    simp only [hg, map_mul, map_inv, w115_nu_h, hnu_u2, mul_one]
    group

private theorem w115_closure_TC4_eq_top :
    Subgroup.closure (Set.range fun i : Fin 4 =>
      (⟨TC4 i, Kt_le_N0 (Subgroup.subset_closure ⟨i, rfl⟩)⟩ : N0)) = ⊤ := by
  apply Subgroup.map_subtype_inj.mp
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
  rw [show N0.subtype '' (Set.range fun i : Fin 4 =>
      (⟨TC4 i, Kt_le_N0 (Subgroup.subset_closure ⟨i, rfl⟩)⟩ : N0)) = Set.range TC4 by
    rw [← Set.range_comp]
    rfl]
  exact Kt_eq_N0

private theorem w115_closure_UC4_eq_top :
    Subgroup.closure (Set.range fun i : Fin 4 =>
      (⟨UC4 i, Ku_le_N0 (Subgroup.subset_closure ⟨i, rfl⟩)⟩ : N0)) = ⊤ := by
  apply Subgroup.map_subtype_inj.mp
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
  rw [show N0.subtype '' (Set.range fun i : Fin 4 =>
      (⟨UC4 i, Ku_le_N0 (Subgroup.subset_closure ⟨i, rfl⟩)⟩ : N0)) = Set.range UC4 by
    rw [← Set.range_comp]
    rfl]
  exact Ku_eq_N0

private theorem w115_inner_le_map_top :
    CFSG.ComponentClassification.OuterAutomorphisms.inner H0 ≤
      (⊤ : Subgroup N0).map w115_nu := by
  rintro g ⟨y, rfl⟩
  exact Subgroup.mem_map.mpr ⟨⟨y, w115_H0_le_N0 y.2⟩, Subgroup.mem_top _, w115_nu_h y⟩

theorem w115_P_nu_t :
    w115_P (w115_nu ⟨t, t_mem_N0⟩) := by
  have hh : ∀ i : Fin 4, ∃ h : H0,
      w115_nu (⟨TC4 i, Kt_le_N0 (Subgroup.subset_closure ⟨i, rfl⟩)⟩ : N0) =
        MulAut.conj h * w115_nu ⟨t, t_mem_N0⟩ * (MulAut.conj h)⁻¹ := by
    intro i
    have hg : (⟨TC4 i, Kt_le_N0 (Subgroup.subset_closure ⟨i, rfl⟩)⟩ : N0) =
        (⟨w115_TG i, w115_TG_mem_N0 i⟩ : N0) *
          ⟨t, t_mem_N0⟩ *
          (⟨w115_TG i, w115_TG_mem_N0 i⟩ : N0)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact w115_TC4_eq i
    rw [hg]
    exact w115_nu_conj_t ⟨w115_TG i, w115_TG_mem_N0 i⟩
  choose h hh using hh
  refine ⟨h, ?_⟩
  have hmap : (⊤ : Subgroup N0).map w115_nu =
      Subgroup.closure (Set.range fun i : Fin 4 => MulAut.conj (h i) *
        w115_nu ⟨t, t_mem_N0⟩ * (MulAut.conj (h i))⁻¹) := by
    rw [← w115_closure_TC4_eq_top, MonoidHom.map_closure]
    congr 1
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext i
    exact hh i
  rw [← hmap]
  exact w115_inner_le_map_top

theorem w115_P_nu_u :
    w115_P (w115_nu ⟨u, u_mem_N0⟩) := by
  have hh : ∀ i : Fin 4, ∃ h : H0,
      w115_nu (⟨UC4 i, Ku_le_N0 (Subgroup.subset_closure ⟨i, rfl⟩)⟩ : N0) =
        MulAut.conj h * w115_nu ⟨u, u_mem_N0⟩ * (MulAut.conj h)⁻¹ := by
    intro i
    have hg : (⟨UC4 i, Ku_le_N0 (Subgroup.subset_closure ⟨i, rfl⟩)⟩ : N0) =
        (⟨w115_UG i, w115_UG_mem_N0 i⟩ : N0) *
          ⟨u, u_mem_N0⟩ *
          (⟨w115_UG i, w115_UG_mem_N0 i⟩ : N0)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact w115_UC4_eq i
    rw [hg]
    exact w115_nu_conj_u ⟨w115_UG i, w115_UG_mem_N0 i⟩
  choose h hh using hh
  refine ⟨h, ?_⟩
  have hmap : (⊤ : Subgroup N0).map w115_nu =
      Subgroup.closure (Set.range fun i : Fin 4 => MulAut.conj (h i) *
        w115_nu ⟨u, u_mem_N0⟩ * (MulAut.conj (h i))⁻¹) := by
    rw [← w115_closure_UC4_eq_top, MonoidHom.map_closure]
    congr 1
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext i
    exact hh i
  rw [← hmap]
  exact w115_inner_le_map_top

theorem w115_P_conj_iff {β : MulAut CFSG.Sporadic.Mathieu.Asc1113M22.H0}
    (x : CFSG.Sporadic.Mathieu.Asc1113M22.H0) :
    w115_P (MulAut.conj x * β * (MulAut.conj x)⁻¹) ↔ w115_P β := by
  constructor
  · intro h
    have h' := w115_P_conj x⁻¹ h
    convert h' using 1
    simp only [map_inv]
    group
  · exact w115_P_conj x

theorem w115_nu_t_sq :
    w115_nu ⟨t, t_mem_N0⟩ * w115_nu ⟨t, t_mem_N0⟩ = 1 := by
  have h : (⟨t, t_mem_N0⟩ : N0) * ⟨t, t_mem_N0⟩ = 1 := by
    apply Subtype.ext
    show (t : Equiv.Perm (Fin 22)) * t = 1
    decide
  rw [← map_mul, h, map_one]

theorem w115_nu_u_sq :
    w115_nu ⟨u, u_mem_N0⟩ * w115_nu ⟨u, u_mem_N0⟩ = 1 := by
  have h : (⟨u, u_mem_N0⟩ : N0) * ⟨u, u_mem_N0⟩ = 1 := by
    apply Subtype.ext
    show (u : Equiv.Perm (Fin 22)) * u = 1
    exact uU_sq
  rw [← map_mul, h, map_one]

theorem w115_nu_t_not_inner :
    w115_nu ⟨t, t_mem_N0⟩ ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner H0 := by
  rintro ⟨k, hk⟩
  have hc : ((k : Equiv.Perm (Fin 22))⁻¹ * t) ∈
      Subgroup.centralizer (H0 : Set (Equiv.Perm (Fin 22))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun φ : MulAut H0 => (φ ⟨y, hy⟩ : Equiv.Perm (Fin 22))) hk
    simp only [MulAut.conj_apply, w115_nu_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    calc y * ((k : Equiv.Perm (Fin 22))⁻¹ * t) =
        (k : Equiv.Perm (Fin 22))⁻¹ *
          ((k : Equiv.Perm (Fin 22)) * y * (k : Equiv.Perm (Fin 22))⁻¹) * t := by group
      _ = (k : Equiv.Perm (Fin 22))⁻¹ * (t * y * t⁻¹) * t := by rw [h]
      _ = ((k : Equiv.Perm (Fin 22))⁻¹ * t) * y := by group
  rw [w115_centralizer_H0_eq_bot, Subgroup.mem_bot] at hc
  have htk : t = (k : Equiv.Perm (Fin 22)) := by
    have := congrArg (fun q : Equiv.Perm (Fin 22) => (k : Equiv.Perm (Fin 22)) * q) hc
    simpa [mul_assoc] using this
  exact w115_t_not_mem_H0 (htk.symm ▸ k.2)

theorem w115_nu_u_not_inner :
    w115_nu ⟨u, u_mem_N0⟩ ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner H0 := by
  rintro ⟨k, hk⟩
  have hc : ((k : Equiv.Perm (Fin 22))⁻¹ * u) ∈
      Subgroup.centralizer (H0 : Set (Equiv.Perm (Fin 22))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun φ : MulAut H0 => (φ ⟨y, hy⟩ : Equiv.Perm (Fin 22))) hk
    simp only [MulAut.conj_apply, w115_nu_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    calc y * ((k : Equiv.Perm (Fin 22))⁻¹ * u) =
        (k : Equiv.Perm (Fin 22))⁻¹ *
          ((k : Equiv.Perm (Fin 22)) * y * (k : Equiv.Perm (Fin 22))⁻¹) * u := by group
      _ = (k : Equiv.Perm (Fin 22))⁻¹ * (u * y * u⁻¹) * u := by rw [h]
      _ = ((k : Equiv.Perm (Fin 22))⁻¹ * u) * y := by group
  rw [w115_centralizer_H0_eq_bot, Subgroup.mem_bot] at hc
  have huk : u = (k : Equiv.Perm (Fin 22)) := by
    have := congrArg (fun q : Equiv.Perm (Fin 22) => (k : Equiv.Perm (Fin 22)) * q) hc
    simpa [mul_assoc] using this
  exact CFSG.Sporadic.Mathieu.Asc1113M22.u_not_mem_H0 (huk.symm ▸ k.2)

theorem w115_nu_injective : Function.Injective w115_nu := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext v
  rw [MonoidHom.mem_ker]
  constructor
  · intro hv
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hc : (v : Equiv.Perm (Fin 22)) ∈
        Subgroup.centralizer (H0 : Set (Equiv.Perm (Fin 22))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := congrArg (fun φ : MulAut H0 => (φ ⟨y, hy⟩ : Equiv.Perm (Fin 22))) hv
      simp only [MulAut.one_apply, w115_nu_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
      calc y * (v : Equiv.Perm (Fin 22)) =
          ((v : Equiv.Perm (Fin 22)) * y * (v : Equiv.Perm (Fin 22))⁻¹) *
            (v : Equiv.Perm (Fin 22)) := by rw [h]
        _ = (v : Equiv.Perm (Fin 22)) * y := by group
    rw [w115_centralizer_H0_eq_bot, Subgroup.mem_bot] at hc
    exact hc
  · intro hv
    rw [Subgroup.mem_bot] at hv
    rw [hv, map_one]

theorem w115_nu_t_ne_conj_u : ¬ ∃ x : H0,
    w115_nu ⟨t, t_mem_N0⟩ =
      MulAut.conj x * w115_nu ⟨u, u_mem_N0⟩ * (MulAut.conj x)⁻¹ := by
  rintro ⟨x, hx⟩
  have h1 : w115_nu ⟨t, t_mem_N0⟩ =
      w115_nu ((⟨x, w115_H0_le_N0 x.2⟩ : N0) * ⟨u, u_mem_N0⟩ *
        (⟨x, w115_H0_le_N0 x.2⟩ : N0)⁻¹) := by
    rw [hx, map_mul, map_mul, map_inv, w115_nu_h]
  have ht_eq : (⟨t, t_mem_N0⟩ : N0) = (⟨x, w115_H0_le_N0 x.2⟩ : N0) *
      ⟨u, u_mem_N0⟩ * (⟨x, w115_H0_le_N0 x.2⟩ : N0)⁻¹ :=
    w115_nu_injective h1
  have hfix : w115_fixCount t = w115_fixCount u := by
    have hcoe := congrArg (fun v : N0 => (v : Equiv.Perm (Fin 22))) ht_eq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcoe
    rw [show t = (x : Equiv.Perm (Fin 22)) * u * (x : Equiv.Perm (Fin 22))⁻¹ from hcoe]
    exact w115_fixCount_conj (x : Equiv.Perm (Fin 22)) u
  rw [w115_fixCount_t, w115_fixCount_u] at hfix
  exact absurd hfix (by decide)

theorem w115_P_of_outer_reps {α₁ α₂ : MulAut H0}
    (hcover : ∀ α : MulAut H0, α * α = 1 →
      α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner H0 →
      ∃ x : H0, α = MulAut.conj x * α₁ * (MulAut.conj x)⁻¹ ∨
        α = MulAut.conj x * α₂ * (MulAut.conj x)⁻¹) :
    w115_P α₁ ∧ w115_P α₂ := by
  obtain ⟨x, hx⟩ := hcover (w115_nu ⟨t, t_mem_N0⟩) w115_nu_t_sq w115_nu_t_not_inner
  obtain ⟨y, hy⟩ := hcover (w115_nu ⟨u, u_mem_N0⟩) w115_nu_u_sq w115_nu_u_not_inner
  have hPt := w115_P_nu_t
  have hPu := w115_P_nu_u
  rcases hx with hx | hx
  · have hP1 : w115_P α₁ := by
      rw [hx] at hPt
      exact (w115_P_conj_iff x).mp hPt
    rcases hy with hy | hy
    · exfalso
      apply w115_nu_t_ne_conj_u
      refine ⟨x * y⁻¹, ?_⟩
      rw [hx, hy, map_mul]
      simp only [map_inv]
      group
    · have hP2 : w115_P α₂ := by
        rw [hy] at hPu
        exact (w115_P_conj_iff y).mp hPu
      exact ⟨hP1, hP2⟩
  · have hP2 : w115_P α₂ := by
      rw [hx] at hPt
      exact (w115_P_conj_iff x).mp hPt
    rcases hy with hy | hy
    · have hP1 : w115_P α₁ := by
        rw [hy] at hPu
        exact (w115_P_conj_iff y).mp hPu
      exact ⟨hP1, hP2⟩
    · exfalso
      apply w115_nu_t_ne_conj_u
      refine ⟨x * y⁻¹, ?_⟩
      rw [hx, hy, map_mul]
      simp only [map_inv]
      group

end Outer

end CFSG.LocalAnalysis.WeakClosure81.W115

