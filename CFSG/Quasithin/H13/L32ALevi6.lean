module

public import CFSG.Quasithin.H13.L32ALevi5

public section

namespace CFSG.Quasithin.H13.L32A.C.Levi

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

structure Model (Q Γ : Type*) [CommGroup Q] [Group Γ] where
  ρ : Γ →* MulAut Q
  β : Γ →* MulAut (Lin.SLn 4)
  φ : Lin.SLn 4 → Q

namespace Model

variable {Q Γ : Type*} [CommGroup Q] [Group Γ]

structure Hyp (M : Model Q Γ) : Prop where
  sq : ∀ q : Q, q * q = 1
  right : ∀ g u, u ∈ unitriangular 4 (ZMod 2) → M.φ (g * u) = M.φ g
  inj : ∀ g g', M.φ g = M.φ g' → g⁻¹ * g' ∈ unitriangular 4 (ZMod 2)
  line : ∀ g, M.φ g * M.φ (g * R2) * M.φ (g * M2) = 1
  eqv : ∀ γ v e, M.β γ = autOf v e → ∀ g, M.ρ γ (M.φ g) = M.φ (mact v e g)
  ne1 : ∀ g, M.φ g ≠ 1
  ker : ∀ γ, M.β γ = 1 → M.ρ γ = 1
  inner : ∀ v, ∃ γ, M.β γ = autOf v false

@[expose] def f (M : Model Q Γ) (b : Γ) (q : Q) : Q := M.ρ b q * q⁻¹

@[expose] def AtMost4 (F : Q → Q) : Prop :=
  ∀ q₀ q₁ q₂ q₃ q₄ : Q, F q₀ = F q₁ ∨ F q₀ = F q₂ ∨ F q₀ = F q₃ ∨ F q₀ = F q₄ ∨ F q₁ = F q₂ ∨
    F q₁ = F q₃ ∨ F q₁ = F q₄ ∨ F q₂ = F q₃ ∨ F q₂ = F q₄ ∨ F q₃ = F q₄

variable {M : Model Q Γ}

theorem f_mul (b : Γ) (q q' : Q) : M.f b (q * q') = M.f b q * M.f b q' := by
  simp only [f, map_mul, mul_inv]
  ac_rfl

theorem f_one (b : Γ) : M.f b 1 = 1 := by simp [f]

theorem invol_of {b : Γ} (hbb : b * b = 1) {u : Lin.SLn 4} {e : Bool} (hb : M.β b = autOf u e) :
    Invol u e := by
  have h1 : autOf u e * autOf u e = autOf 1 false := by
    rw [← hb, ← map_mul, hbb, map_one, autOf_one]
  rw [autOf_mul] at h1
  exact (autOf_inj h1).1

theorem nontriv_of {b : Γ} (hb1 : M.β b ≠ 1) {u : Lin.SLn 4} {e : Bool} (hb : M.β b = autOf u e) :
    ¬ (u = 1 ∧ e = false) := by
  rintro ⟨rfl, rfl⟩
  exact hb1 (hb.trans autOf_one)

variable (hM : M.Hyp)
include hM

theorem inv_eq (q : Q) : q⁻¹ = q := inv_eq_of_mul_eq_one_right (hM.sq q)

theorem phi_eq_f {b : Γ} {v : Lin.SLn 4} {e : Bool} (hb : M.β b = autOf v e) {g : Lin.SLn 4}
    (hsw : Sw v e g) : M.φ g = M.f b (M.φ (g * R2)) := by
  have h1 : M.ρ b (M.φ (g * R2)) = M.φ (g * M2) := by
    rw [hM.eqv b v e hb, ← hM.right (g * M2) _ hsw, mul_inv_cancel_left]
  have h2 := hM.line g
  rw [f, h1, inv_eq hM]
  calc M.φ g = M.φ g * (M.φ (g * R2) * M.φ (g * M2)) * (M.φ (g * R2) * M.φ (g * M2)) := by
        rw [mul_assoc, hM.sq, mul_one]
    _ = M.φ (g * M2) * M.φ (g * R2) := by
        rw [← mul_assoc (M.φ g), h2, one_mul, mul_comm]

theorem phi_ne {g g' : Lin.SLn 4} (h : Ne' g g') : M.φ g ≠ M.φ g' := fun e => h (hM.inj g g' e)

theorem false_of_four {b : Γ} {v : Lin.SLn 4} {e : Bool} (hb : M.β b = autOf v e)
    (hpig : AtMost4 (M.f b)) (h4 : Four v e) : False := by
  obtain ⟨g₁, g₂, g₃, g₄, s₁, s₂, s₃, s₄, n₁₂, n₁₃, n₁₄, n₂₃, n₂₄, n₃₄⟩ := h4
  have h := hpig 1 (M.φ (g₁ * R2)) (M.φ (g₂ * R2)) (M.φ (g₃ * R2)) (M.φ (g₄ * R2))
  rw [f_one, ← phi_eq_f hM hb s₁, ← phi_eq_f hM hb s₂, ← phi_eq_f hM hb s₃,
    ← phi_eq_f hM hb s₄] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact hM.ne1 g₁ h.symm
  · exact hM.ne1 g₂ h.symm
  · exact hM.ne1 g₃ h.symm
  · exact hM.ne1 g₄ h.symm
  · exact phi_ne hM n₁₂ h
  · exact phi_ne hM n₁₃ h
  · exact phi_ne hM n₁₄ h
  · exact phi_ne hM n₂₃ h
  · exact phi_ne hM n₂₄ h
  · exact phi_ne hM n₃₄ h

omit hM in
theorem no_sqrt : ∀ σ : Fin 3 → Fin 3, ¬ (σ (σ 0) = 0 ∧ σ (σ 1) = 2 ∧ σ (σ 2) = 1) := by
  decide

omit hM in
theorem R2_gam (e : Bool) : R2⁻¹ * gamE e R2 ∈ unitriangular 4 (ZMod 2) := by
  cases e
  · rw [show gamE false R2 = R2 from rfl, inv_mul_cancel]
    exact one_mem _
  · rw [show gamE true R2 = BinaryParabolic.graphFun R2 from rfl, R2, ← PP.toSL_gam PP.valid_R2P,
      ← PP.sameB_iff PP.valid_R2P PP.valid_R2P.gam]
    decide +kernel

omit hM in
theorem M2_gam (e : Bool) : M2⁻¹ * gamE e M2 ∈ unitriangular 4 (ZMod 2) := by
  cases e
  · rw [show gamE false M2 = M2 from rfl, inv_mul_cancel]
    exact one_mem _
  · rw [show gamE true M2 = BinaryParabolic.graphFun M2 from rfl, M2, ← PP.toSL_gam PP.valid_M2P,
      ← PP.sameB_iff PP.valid_M2P PP.valid_M2P.gam]
    decide +kernel

theorem phi_of_mem {g h : Lin.SLn 4} (hgh : g⁻¹ * h ∈ unitriangular 4 (ZMod 2)) :
    M.φ h = M.φ g := by
  rw [← hM.right g _ hgh, mul_inv_cancel_left]

theorem line_image (v : Lin.SLn 4) (e : Bool) (g : Lin.SLn 4) :
    M.φ (mact v e g) * M.φ (mact v e (g * R2)) * M.φ (mact v e (g * M2)) = 1 := by
  have e1 : mact v e (g * R2) = mact v e g * R2 * (R2⁻¹ * gamE e R2) := by
    rw [mact_eq, mact_eq, gamE_mul]
    group
  have e2 : mact v e (g * M2) = mact v e g * M2 * (M2⁻¹ * gamE e M2) := by
    rw [mact_eq, mact_eq, gamE_mul]
    group
  rw [e1, e2, hM.right _ _ (R2_gam e), hM.right _ _ (M2_gam e)]
  exact hM.line _

theorem false_of_tr {b : Γ} {v : Lin.SLn 4} {e : Bool} (hb : M.β b = autOf v e)
    (hpig : AtMost4 (M.f b)) (htr : Tr v e) : False := by
  obtain ⟨g, y, hy, m₀, m₁, m₂, y₀, y₁, y₂⟩ := htr
  have hf : ∀ h, M.f b (M.φ h) = M.φ (mact v e h) * M.φ h := fun h => by
    rw [f, hM.eqv b v e hb, inv_eq hM]
  set p : Fin 3 → Lin.SLn 4 := ![g, g * R2, g * M2] with hp
  have p0 : p 0 = g := rfl
  have p1 : p 1 = g * R2 := rfl
  have p2 : p 2 = g * M2 := rfl
  set d : Fin 3 → Q := fun i => M.f b (M.φ (p i)) with hd
  have hd1 : ∀ i, d i ≠ 1 := by
    intro i h
    have h' : M.φ (mact v e (p i)) = M.φ (p i) := by
      rw [← inv_eq hM (M.φ (p i))]
      exact eq_inv_of_mul_eq_one_left ((hf (p i)).symm.trans h)
    have := hM.inj _ _ h'.symm
    fin_cases i
    · exact m₀ this
    · exact m₁ this
    · exact m₂ this
  have h012 : d 0 * d 1 = d 2 := by
    have a1 : M.φ g * M.φ (g * R2) = M.φ (g * M2) := by
      rw [← inv_eq hM (M.φ (g * M2))]
      exact eq_inv_of_mul_eq_one_left (hM.line g)
    have a2 : M.φ (mact v e g) * M.φ (mact v e (g * R2)) = M.φ (mact v e (g * M2)) := by
      rw [← inv_eq hM (M.φ (mact v e (g * M2)))]
      exact eq_inv_of_mul_eq_one_left (line_image hM v e g)
    show M.f b (M.φ (p 0)) * M.f b (M.φ (p 1)) = M.f b (M.φ (p 2))
    rw [p0, p1, p2, hf, hf, hf, ← a1, ← a2]
    ac_rfl
  have hd2 : ∀ i, d i * d i = 1 := fun i => hM.sq _
  have k01 : d 0 ≠ d 1 := fun h => hd1 2 (by rw [← h012, h, hd2])
  have k02 : d 0 ≠ d 2 := fun h => hd1 1 (by
    rw [← h012] at h
    have := congrArg (d 0 * ·) h
    simp only [← mul_assoc, hd2, one_mul] at this
    exact this.symm)
  have k12 : d 1 ≠ d 2 := fun h => hd1 0 (by
    rw [← h012] at h
    have := congrArg (· * d 1) h
    simp only [mul_assoc, hd2, mul_one] at this
    exact this.symm)
  have hdinj : Function.Injective d := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact absurd hij k01
      | exact absurd hij k02
      | exact absurd hij k12
      | exact absurd hij.symm k01
      | exact absurd hij.symm k02
      | exact absurd hij.symm k12
  have himg : ∀ q, M.f b q = 1 ∨ ∃ i, M.f b q = d i := by
    intro q
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c⟩ := hcon
    have h := hpig 1 (M.φ (p 0)) (M.φ (p 1)) (M.φ (p 2)) q
    rw [f_one] at h
    rcases h with h | h | h | h | h | h | h | h | h | h
    · exact hd1 0 h.symm
    · exact hd1 1 h.symm
    · exact hd1 2 h.symm
    · exact c1 h.symm
    · exact k01 h
    · exact k02 h
    · exact c 0 h.symm
    · exact k12 h
    · exact c 1 h.symm
    · exact c 2 h.symm
  obtain ⟨c, hc⟩ := hM.inner y
  have hβ : M.β (c * b) = M.β (b * c) := by
    rw [map_mul, map_mul, hc, hb, autOf_mul, autOf_mul]
    have e1 : y * gamE false v = y * v := rfl
    have e2 : v * gamE e y = y * v := by rw [← mact_eq, hy]
    rw [e1, e2, Bool.false_xor, Bool.xor_false]
  have hcb : M.ρ c * M.ρ b = M.ρ b * M.ρ c := by
    have h1 : M.β (c * b * (b * c)⁻¹) = 1 := by rw [map_mul, map_inv, hβ, mul_inv_cancel]
    have h2 := hM.ker _ h1
    rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul] at h2
    exact h2
  have hcf : ∀ q, M.ρ c (M.f b q) = M.f b (M.ρ c q) := fun q => by
    have := congrArg (fun α : MulAut Q => α q) hcb
    simp only [MulAut.mul_apply] at this
    rw [f, f, map_mul, map_inv, this]
  have hcφ : ∀ h, M.ρ c (M.φ h) = M.φ (y * h) := fun h => by
    rw [hM.eqv c y false hc, mact_eq]
    rfl
  have hcd : ∀ i, M.ρ c (d i) = M.f b (M.φ (y * p i)) := fun i => by
    show M.ρ c (M.f b (M.φ (p i))) = _
    rw [hcf, hcφ]
  have hσ : ∀ i, ∃ j, M.ρ c (d i) = d j := by
    intro i
    rcases himg (M.φ (y * p i)) with h | h
    · exfalso
      apply hd1 i
      rw [← hcd] at h
      exact (MulEquiv.map_eq_one_iff _).mp h
    · obtain ⟨j, hj⟩ := h
      exact ⟨j, (hcd i).trans hj⟩
  choose σ hσ using hσ
  have hsq : ∀ i j, (p j)⁻¹ * (y * y * p i) ∈ unitriangular 4 (ZMod 2) → σ (σ i) = j := by
    intro i j hij
    apply hdinj
    rw [← hσ, ← hσ, hcd, hcf, hcφ, ← mul_assoc, phi_of_mem hM hij]
  apply no_sqrt σ
  refine ⟨hsq 0 0 ?_, hsq 1 2 ?_, hsq 2 1 ?_⟩
  · rw [p0]
    exact y₀
  · rw [p1, p2]
    exact y₁
  · rw [p1, p2]
    exact y₂

theorem false_of_two {B : Subgroup Γ} (hBe : ∀ b ∈ B, b * b = 1)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hBq : ∀ b ∈ B, ∀ b' ∈ B, ∀ q, M.ρ b' (M.f b q) = M.f b q)
    (hBR : ∀ b ∈ B, ∃ u ∈ unitriangular 4 (ZMod 2), ∃ e, R1 u e ∧ M.β b = autOf u e)
    {b₁ b₂ : Γ} (h₁ : b₁ ∈ B) (h₂ : b₂ ∈ B) (n₁ : M.β b₁ ≠ 1) (n₂ : M.β b₂ ≠ 1)
    (n₁₂ : M.β b₁ ≠ M.β b₂) : False := by
  obtain ⟨u₁, hu₁, e₁, r₁, hb₁⟩ := hBR b₁ h₁
  obtain ⟨u₂, hu₂, e₂, r₂, hb₂⟩ := hBR b₂ h₂
  have hne : ¬ (u₁ = u₂ ∧ e₁ = e₂) := by
    rintro ⟨rfl, rfl⟩
    exact n₁₂ (hb₁.trans hb₂.symm)
  have hc : u₁ * gamE e₁ u₂ = u₂ * gamE e₂ u₁ := by
    have := congrArg M.β (hBc b₁ h₁ b₂ h₂)
    rw [map_mul, map_mul, hb₁, hb₂, autOf_mul, autOf_mul] at this
    exact (autOf_inj this).1
  have hb₃ : M.β (b₁ * b₂) = autOf (u₁ * gamE e₁ u₂) (xor e₁ e₂) := by
    rw [map_mul, hb₁, hb₂, autOf_mul]
  obtain ⟨c, hcm, c', hcm', g, hsw, hne'⟩ := two_cases hu₁ hu₂ r₁ r₂
    (invol_of (hBe b₁ h₁) hb₁) (invol_of (hBe b₂ h₂) hb₂) (nontriv_of n₁ hb₁)
    (nontriv_of n₂ hb₂) hne hc
  have real : ∀ x ∈ [(u₁, e₁), (u₂, e₂), (u₁ * gamE e₁ u₂, xor e₁ e₂)],
      ∃ b ∈ B, M.β b = autOf x.1 x.2 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨b₁, h₁, hb₁⟩
    · exact ⟨b₂, h₂, hb₂⟩
    · exact ⟨b₁ * b₂, mul_mem h₁ h₂, hb₃⟩
  obtain ⟨b, hbB, hb⟩ := real c hcm
  obtain ⟨b', hbB', hb'⟩ := real c' hcm'
  have hfix : M.ρ b' (M.φ g) = M.φ g := by rw [phi_eq_f hM hb hsw, hBq b hbB b' hbB']
  rw [hM.eqv b' c'.1 c'.2 hb'] at hfix
  exact hne' (hM.inj _ _ hfix.symm)

theorem no_offender {B : Subgroup Γ} (hBe : ∀ b ∈ B, b * b = 1)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hBq : ∀ b ∈ B, ∀ b' ∈ B, ∀ q, M.ρ b' (M.f b q) = M.f b q)
    (hBR : ∀ b ∈ B, ∃ u ∈ unitriangular 4 (ZMod 2), ∃ e, R1 u e ∧ M.β b = autOf u e)
    (hcase : (∃ b ∈ B, M.β b ≠ 1 ∧ AtMost4 (M.f b)) ∨
      ∃ b₁ ∈ B, ∃ b₂ ∈ B, M.β b₁ ≠ 1 ∧ M.β b₂ ≠ 1 ∧ M.β b₁ ≠ M.β b₂) : False := by
  rcases hcase with ⟨b, hbB, hb1, hpig⟩ | ⟨b₁, h₁, b₂, h₂, n₁, n₂, n₁₂⟩
  · obtain ⟨u, hu, e, hr, hb⟩ := hBR b hbB
    rcases one_cases hu hr (invol_of (hBe b hbB) hb) (nontriv_of hb1 hb) with h4 | htr
    · exact false_of_four hM hb hpig h4
    · exact false_of_tr hM hb hpig htr
  · exact false_of_two hM hBe hBc hBq hBR h₁ h₂ n₁ n₂ n₁₂

end Model

end CFSG.Quasithin.H13.L32A.C.Levi
