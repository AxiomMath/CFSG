module

public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.C116Three.L3Fin
public import CFSG.Quasithin.EmptyFaithful.R3c23Glue1

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {M C : Subgroup V}

@[expose] def IsLift (D : L3Data G M C) (m : V) : Prop :=
  ∃ hm : m ∈ M, D.β ⟨m, hm⟩ = Multiplicative.ofAdd L3F.e1

theorem exists_lift (D : L3Data G M C) : ∃ m : V, IsLift D m := by
  obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd L3F.e1)
  exact ⟨u.1, u.2, hu⟩

theorem lift_spec {D : L3Data G M C} {m : V} (hm : IsLift D m) :
    ∃ h : m ∈ M, D.β ⟨m, h⟩ = Multiplicative.ofAdd L3F.e1 := hm

theorem beta_eq_mem_C (D : L3Data G M C) {a b : V} (ha : a ∈ M) (hb : b ∈ M)
    (h : D.β ⟨a, ha⟩ = D.β ⟨b, hb⟩) : a * b⁻¹ ∈ C := by
  have h1 : D.β (⟨a, ha⟩ * (⟨b, hb⟩ : ↥M)⁻¹) = 1 := by
    rw [map_mul, map_inv, h]
    exact mul_inv_cancel _
  exact (D.ker_β _).1 h1

theorem rho_mul_apply_L3 (D : L3Data G M C) (γ δ : L3.Γ) (v : V) :
    D.rho (γ * δ) v = D.rho γ (D.rho δ v) := by
  rw [map_mul, MulAut.mul_apply]

theorem beta_fixed_act (D : L3Data G M C) {x : V} (hxM : x ∈ M) {γ : L3.Γ}
    (hfix : D.rho γ x = x) :
    L3.act γ (Multiplicative.toAdd (D.β ⟨x, hxM⟩)) = Multiplicative.toAdd (D.β ⟨x, hxM⟩) := by
  have hbx : D.rho γ x ∈ M := D.inv_U _ (D.rho_mem γ) x hxM
  have h2 : (⟨D.rho γ x, hbx⟩ : ↥M) = ⟨x, hxM⟩ := Subtype.ext hfix
  have h1 := D.β_rho γ x hxM hbx
  rw [h2] at h1
  have h3 := congrArg Multiplicative.toAdd h1
  rw [toAdd_ofAdd] at h3
  exact h3.symm

theorem lift_beta_rho {D : L3Data G M C} {m : V} (hm : IsLift D m) {γ : L3.Γ}
    (hγ : L3F.Ppt γ) :
    ∃ hx : D.rho γ m ∈ M, D.β ⟨D.rho γ m, hx⟩ = Multiplicative.ofAdd L3F.e1 := by
  obtain ⟨hmM, hβm⟩ := lift_spec hm
  have hx : D.rho γ m ∈ M := D.inv_U _ (D.rho_mem γ) m hmM
  have hγ' : L3.act γ L3F.e1 = L3F.e1 := hγ
  refine ⟨hx, ?_⟩
  rw [D.β_rho γ m hmM hx, hβm, toAdd_ofAdd, hγ']

theorem ppt_mul {γ δ : L3.Γ} (hγ : L3F.Ppt γ) (hδ : L3F.Ppt δ) : L3F.Ppt (γ * δ) := by
  have hγ' : L3.act γ L3F.e1 = L3F.e1 := hγ
  have hδ' : L3.act δ L3F.e1 = L3F.e1 := hδ
  show L3.act (γ * δ) L3F.e1 = L3F.e1
  rw [L3.act_mul, hδ', hγ']

set_option maxRecDepth 100000 in
theorem U_B1B2_decomp : ∀ s : L3.Γ, L3F.Ustd s → ∃ b₁ ∈ L3F.B1, ∃ b₂ ∈ L3F.B2, s = b₁ * b₂ := by
  unfold L3F.B1 L3F.B2; decide +kernel

theorem lift_comm_mem (D : L3Data G M C) {m : V} (hm : IsLift D m) {γ : L3.Γ} (hγ : L3F.Ppt γ) :
    D.rho γ m * m⁻¹ ∈ C := by
  obtain ⟨hmM, hβm⟩ := lift_spec hm
  obtain ⟨hx, hβx⟩ := lift_beta_rho hm hγ
  exact beta_eq_mem_C D hx hmM (hβx.trans hβm.symm)

theorem lift_mul (D : L3Data G M C) (hCfix : ∀ g ∈ G, ∀ c ∈ C, g c = c) {m : V} (hm : IsLift D m)
    {γ δ : L3.Γ} (hγ : L3F.Ppt γ) (hδ : L3F.Ppt δ) :
    D.rho (γ * δ) m * m⁻¹ = (D.rho γ m * m⁻¹) * (D.rho δ m * m⁻¹) := by
  obtain ⟨c, hc, hcδ⟩ : ∃ c ∈ C, D.rho δ m = c * m :=
    ⟨D.rho δ m * m⁻¹, lift_comm_mem D hm hδ, by simp⟩
  have hgc : D.rho γ c = c := hCfix (D.rho γ) (D.rho_mem γ) c hc
  have h1 : D.rho (γ * δ) m = c * D.rho γ m := by
    rw [rho_mul_apply_L3, hcδ, map_mul, hgc]
  rw [h1, hcδ, mul_inv_cancel_right]
  ac_rfl

theorem lift_B2 (D : L3Data G M C) (hCfix : ∀ g ∈ G, ∀ c ∈ C, g c = c) {m : V} (hm : IsLift D m)
    {γ : L3.Γ} (hγ : γ ∈ L3F.B2) : D.rho γ m = m := by
  obtain ⟨p, q, hp, hq, hpq⟩ := L3F.B2_comm γ hγ
  have hγP : L3F.Ppt γ := L3F.B2_fix_e1 γ hγ
  have A1 := lift_mul D hCfix hm hγP (ppt_mul hq hp)
  have A2 := lift_mul D hCfix hm hq hp
  have A3 := lift_mul D hCfix hm hp hq
  rw [hpq, A3, A2] at A1
  have h2 : (D.rho γ m * m⁻¹) * ((D.rho q m * m⁻¹) * (D.rho p m * m⁻¹)) =
      1 * ((D.rho q m * m⁻¹) * (D.rho p m * m⁻¹)) := by
    rw [one_mul, ← A1, mul_comm (D.rho p m * m⁻¹) (D.rho q m * m⁻¹)]
  exact mul_inv_eq_one.mp (mul_right_cancel h2)

theorem fix_B1_le_C (D : L3Data G M C) (hCfix : ∀ g ∈ G, ∀ c ∈ C, g c = c) {m : V} (hm : IsLift D m)
    (hII : ∃ s : L3.Γ, L3F.Ustd s ∧ D.rho s m ≠ m) :
    ∀ x ∈ M, (∀ b ∈ L3F.B1, D.rho b x = x) → x ∈ C := by
  intro x hxM hxB1
  obtain ⟨s, hsU, hsm⟩ := hII
  by_contra hxC
  have hβne : D.β ⟨x, hxM⟩ ≠ 1 := fun h => hxC ((D.ker_β ⟨x, hxM⟩).1 h)
  have hv0 : Multiplicative.toAdd (D.β ⟨x, hxM⟩) ≠ 0 := fun h => hβne (toAdd_eq_zero.mp h)
  have hvB1 : ∀ b ∈ L3F.B1,
      L3.act b (Multiplicative.toAdd (D.β ⟨x, hxM⟩)) = Multiplicative.toAdd (D.β ⟨x, hxM⟩) :=
    fun b hb => beta_fixed_act D hxM (hxB1 b hb)
  obtain ⟨p, hp, hpv⟩ := L3F.Pline_trans _ (L3F.B1_fix _ hvB1) hv0
  have hyM : D.rho p x ∈ M := D.inv_U _ (D.rho_mem p) x hxM
  have hyβ : D.β ⟨D.rho p x, hyM⟩ = Multiplicative.ofAdd L3F.e1 := by
    rw [D.β_rho p x hxM hyM, hpv]
  have hyB1 : ∀ b ∈ L3F.B1, D.rho b (D.rho p x) = D.rho p x := by
    intro b hb
    obtain ⟨b', hb', hbb'⟩ := L3F.Pline_norm p hp b hb
    rw [← rho_mul_apply_L3, hbb', rho_mul_apply_L3, hxB1 b' hb']
  obtain ⟨hmM, hβm⟩ := lift_spec hm
  have hcm : D.rho p x * m⁻¹ ∈ C := beta_eq_mem_C D hyM hmM (hyβ.trans hβm.symm)
  obtain ⟨c, hc, hcy⟩ : ∃ c ∈ C, D.rho p x = c * m := ⟨D.rho p x * m⁻¹, hcm, by simp⟩
  have hB1m : ∀ b ∈ L3F.B1, D.rho b m = m := by
    intro b hb
    have e := hyB1 b hb
    rw [hcy, map_mul, hCfix (D.rho b) (D.rho_mem b) c hc] at e
    exact mul_left_cancel e
  obtain ⟨b₁, hb₁, b₂, hb₂, hsb⟩ := U_B1B2_decomp s hsU
  apply hsm
  rw [hsb, rho_mul_apply_L3, lift_B2 D hCfix hm hb₂, hB1m b₁ hb₁]

end CFSG.Quasithin.C116Three
