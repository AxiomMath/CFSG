module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Trilinear
public import CFSG.LinearAlgebra.AltTrilinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.RankThree.GF2n CFSG.LinearAlgebra

section CubicForm

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

@[expose] def flagForm (M₀ : Tim79.QuadModel QF V K γ) (b : M₀.E)
    (Tx : M₀.E → (M₀.E ≃ₗ[K] M₀.E)) (x y z : LinearMap.ker (M₀.B.flip b)) : K :=
  M₀.B (Tx (x : M₀.E) (y : M₀.E) - (y : M₀.E)) (z : M₀.E)

variable {M₀ : Tim79.QuadModel QF V K γ} {b : M₀.E} {W : Submodule K M₀.E}
  {Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E)} {f₀ : M₀.E} {Tx : M₀.E → (M₀.E ≃ₗ[K] M₀.E)}

theorem flagForm_apply (x y z : LinearMap.ker (M₀.B.flip b)) :
    flagForm M₀ b Tx x y z = M₀.B (Tx (x : M₀.E) (y : M₀.E) - (y : M₀.E)) (z : M₀.E) := rfl

theorem mem_ker_B_flip_iff {y : M₀.E} : y ∈ LinearMap.ker (M₀.B.flip b) ↔ M₀.B y b = 0 := by
  rw [LinearMap.mem_ker, LinearMap.BilinForm.flip_apply]

theorem FlagData.flagForm_swap₁₃ (hΛ : FlagData M₀ b W Λ) (hf₀ : M₀.B f₀ b = 1)
    (hTx : ∀ x, M₀.B x b = 0 → Tx x ∈ Λ ∧ ∀ d ∈ W, flagPsi M₀ f₀ (Tx x) d = M₀.B d x)
    (x y z : LinearMap.ker (M₀.B.flip b)) :
    flagForm M₀ b Tx x y z = flagForm M₀ b Tx z y x := by
  have hy : M₀.B (y : M₀.E) b = 0 := mem_ker_B_flip_iff.mp y.2
  obtain ⟨hxΛ, hxψ⟩ := hTx x (mem_ker_B_flip_iff.mp x.2)
  obtain ⟨hzΛ, hzψ⟩ := hTx z (mem_ker_B_flip_iff.mp z.2)
  have h1 := hΛ.psi_comm hf₀ hzΛ hxΛ hy
  rw [hzψ _ (hΛ.flag2 _ hxΛ _ hy), hxψ _ (hΛ.flag2 _ hzΛ _ hy)] at h1
  exact h1

theorem FlagData.flagForm_self₂₃ (hΛ : FlagData M₀ b W Λ)
    (hTx : ∀ x, M₀.B x b = 0 → Tx x ∈ Λ ∧ ∀ d ∈ W, flagPsi M₀ f₀ (Tx x) d = M₀.B d x)
    (x y : LinearMap.ker (M₀.B.flip b)) : flagForm M₀ b Tx x y y = 0 := by
  have hy : M₀.B (y : M₀.E) b = 0 := mem_ker_B_flip_iff.mp y.2
  have hxΛ := (hTx x (mem_ker_B_flip_iff.mp x.2)).1
  have e := M₀.Qf_add (Tx (x : M₀.E) (y : M₀.E) - (y : M₀.E)) (y : M₀.E)
  rw [sub_add_cancel, hΛ.iso _ hxΛ, hΛ.hWs _ (hΛ.flag2 _ hxΛ _ hy), zero_add] at e
  rw [flagForm_apply]
  linear_combination -e

theorem FlagData.isAltTrilinForm_flagForm (hΛ : FlagData M₀ b W Λ) (hf₀ : M₀.B f₀ b = 1)
    (hTx : ∀ x, M₀.B x b = 0 → Tx x ∈ Λ ∧ ∀ d ∈ W, flagPsi M₀ f₀ (Tx x) d = M₀.B d x) :
    IsAltTrilinForm (flagForm M₀ b Tx) where
  add_left x x' y z := by
    rw [hΛ.flagForm_swap₁₃ hf₀ hTx (x + x'), hΛ.flagForm_swap₁₃ hf₀ hTx x,
      hΛ.flagForm_swap₁₃ hf₀ hTx x']
    simp only [flagForm_apply, Submodule.coe_add, map_add]
  smul_left c x y z := by
    rw [hΛ.flagForm_swap₁₃ hf₀ hTx (c • x), hΛ.flagForm_swap₁₃ hf₀ hTx x]
    simp only [flagForm_apply, Submodule.coe_smul, map_smul, smul_eq_mul]
  add_mid x y y' z := by
    simp only [flagForm_apply, Submodule.coe_add, map_add, add_sub_add_comm,
      LinearMap.add_apply]
  smul_mid c x y z := by
    simp only [flagForm_apply, Submodule.coe_smul, map_smul, ← smul_sub,
      LinearMap.smul_apply, smul_eq_mul]
  add_right x y z z' := by
    simp only [flagForm_apply, Submodule.coe_add, map_add]
  smul_right c x y z := by
    simp only [flagForm_apply, Submodule.coe_smul, map_smul, smul_eq_mul]
  self₁₂ x z := by
    rw [hΛ.flagForm_swap₁₃ hf₀ hTx]
    exact hΛ.flagForm_self₂₃ hTx z x
  self₂₃ x y := hΛ.flagForm_self₂₃ hTx x y

theorem FlagData.flagForm_eq_zero_of_mem (hΛ : FlagData M₀ b W Λ) (hf₀ : M₀.B f₀ b = 1)
    (hTx : ∀ x, M₀.B x b = 0 → Tx x ∈ Λ ∧ ∀ d ∈ W, flagPsi M₀ f₀ (Tx x) d = M₀.B d x)
    {r : LinearMap.ker (M₀.B.flip b)} (hr : (r : M₀.E) ∈ W)
    (y z : LinearMap.ker (M₀.B.flip b)) : flagForm M₀ b Tx r y z = 0 := by
  rw [hΛ.flagForm_swap₁₃ hf₀ hTx]
  exact hΛ.B_eq_zero (hΛ.flag2 _ (hTx z (mem_ker_B_flip_iff.mp z.2)).1 _
    (mem_ker_B_flip_iff.mp y.2)) hr

theorem FlagData.mem_of_flagForm_eq_zero (hΛ : FlagData M₀ b W Λ)
    (hTx : ∀ x, M₀.B x b = 0 → Tx x ∈ Λ ∧ ∀ d ∈ W, flagPsi M₀ f₀ (Tx x) d = M₀.B d x)
    (hN : ∀ T ∈ Λ, (∀ y, M₀.B y b = 0 → T y - y ∈ Submodule.span K {b}) → T = 1)
    {x : LinearMap.ker (M₀.B.flip b)} (hx : ∀ y z, flagForm M₀ b Tx x y z = 0) :
    (x : M₀.E) ∈ W := by
  obtain ⟨hxΛ, hxψ⟩ := hTx x (mem_ker_B_flip_iff.mp x.2)
  have h1 : Tx (x : M₀.E) = 1 := by
    refine hN _ hxΛ fun y hy => ?_
    obtain ⟨c, hc⟩ := Tim79.QuadModel.exists_smul_of_orthogonal hΛ.hb0
      (v := Tx (x : M₀.E) y - y)
      fun u hu => hx ⟨y, mem_ker_B_flip_iff.mpr hy⟩ ⟨u, mem_ker_B_flip_iff.mpr hu⟩
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  refine hΛ.hWperp _ fun u hu => ?_
  have e := hxψ u hu
  rw [h1] at e
  simp only [flagPsi, LinearEquiv.coe_one, id_eq, sub_self, map_zero] at e
  rw [Tim79.QuadModel.B_comm, ← e, neg_zero]

theorem FlagData.n_ne_three_five (hΛ : FlagData M₀ b W Λ) (hf₀ : M₀.B f₀ b = 1)
    (hsurj : ∀ φ : W →ₗ[K] K, φ ⟨b, hΛ.hbW⟩ = 0 →
      ∃ T ∈ Λ, ∀ d : W, flagPsi M₀ f₀ T d = φ d)
    (hN : ∀ T ∈ Λ, (∀ y, M₀.B y b = 0 → T y - y ∈ Submodule.span K {b}) → T = 1)
    {n : ℕ} (hE : Module.finrank K M₀.E = 2 * n) (hW : Module.finrank K W = n) :
    n ≠ 3 ∧ n ≠ 5 := by
  classical
  have hex : ∀ x : M₀.E, ∃ T : M₀.E ≃ₗ[K] M₀.E, M₀.B x b = 0 →
      T ∈ Λ ∧ ∀ d ∈ W, flagPsi M₀ f₀ T d = M₀.B d x := by
    intro x
    by_cases hx : M₀.B x b = 0
    · obtain ⟨T, hT, hTd⟩ := hsurj ((M₀.B.flip x).comp W.subtype)
        (by simp [Tim79.QuadModel.B_comm b x, hx])
      exact ⟨T, fun _ => ⟨hT, fun d hd => by simpa using hTd ⟨d, hd⟩⟩⟩
    · exact ⟨1, fun h => absurd h hx⟩
  choose Tx hTx using hex
  have hA := hΛ.isAltTrilinForm_flagForm hf₀ hTx
  have hWP : W ≤ LinearMap.ker (M₀.B.flip b) := fun w hw =>
    mem_ker_B_flip_iff.mpr (hΛ.B_eq_zero hw hΛ.hbW)
  have hPdim : Module.finrank K (LinearMap.ker (M₀.B.flip b)) + 1 =
      Module.finrank K M₀.E := by
    refine Module.Dual.finrank_ker_add_one_of_ne_zero (f := M₀.B.flip b) ?_
    intro h0
    have := LinearMap.congr_fun h0 f₀
    rw [LinearMap.BilinForm.flip_apply, hf₀, LinearMap.zero_apply] at this
    exact one_ne_zero this
  have hRdim : Module.finrank K (W.comap (LinearMap.ker (M₀.B.flip b)).subtype) = n := by
    rw [← hW]
    exact (Submodule.comapSubtypeEquivOfLe hWP).finrank_eq
  obtain ⟨h2, h4⟩ := hA.finrank_ne_add_two_four (W.comap (LinearMap.ker (M₀.B.flip b)).subtype)
    (fun r hr y z => hΛ.flagForm_eq_zero_of_mem hf₀ hTx hr y z)
    (fun x hx => hΛ.mem_of_flagForm_eq_zero hTx hN hx)
  constructor <;> rintro rfl <;> omega

end CubicForm

end CFSG.RankThree.GF2n.Stroth80
