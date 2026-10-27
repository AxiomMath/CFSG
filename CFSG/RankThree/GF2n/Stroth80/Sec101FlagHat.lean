module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Trilinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.RankThree.GF2n

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel QF V K γ} {b : M₀.E} {W : Submodule K M₀.E}
  {Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E)} {f₀ : M₀.E}

theorem FlagData.B_sub_self (hΛ : FlagData M₀ b W Λ) {T : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ)
    (y : M₀.E) : M₀.B (T y - y) b = 0 := by
  have h := Tim79.QuadModel.B_iso (T := (T : M₀.E →ₗ[K] M₀.E)) (hΛ.iso T hT) y b
  simp only [LinearEquiv.coe_coe] at h
  rw [hΛ.fix T hT] at h
  rw [map_sub, LinearMap.sub_apply, h, sub_self]

theorem FlagData.B_hat (hΛ : FlagData M₀ b W Λ) (hf₀ : M₀.B f₀ b = 1)
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ) {y : M₀.E} (hy : y ∈ W) :
    M₀.B (T f₀ - f₀) y = - flagPsi M₀ f₀ T y := by
  have h := Tim79.QuadModel.B_iso (T := (T : M₀.E →ₗ[K] M₀.E)) (hΛ.iso T hT) f₀ y
  simp only [LinearEquiv.coe_coe] at h
  have hTy : T y = y + flagPsi M₀ f₀ T y • b := by
    rw [← hΛ.sub_eq hf₀ hT hy]; abel
  have hTb : M₀.B (T f₀) b = 1 := by
    have h2 := Tim79.QuadModel.B_iso (T := (T : M₀.E →ₗ[K] M₀.E)) (hΛ.iso T hT) f₀ b
    simp only [LinearEquiv.coe_coe] at h2
    rw [hΛ.fix T hT, hf₀] at h2
    exact h2
  rw [hTy, map_add, map_smul, smul_eq_mul, hTb, mul_one] at h
  rw [map_sub (M₀.B) (T f₀) f₀, LinearMap.sub_apply]
  linear_combination h

theorem FlagData.sub_sub_smul_mem (hΛ : FlagData M₀ b W Λ) (hf₀ : M₀.B f₀ b = 1)
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ) (x : M₀.E) :
    T x - x - M₀.B x b • (T f₀ - f₀) ∈ W := by
  have hy : M₀.B (x - M₀.B x b • f₀) b = 0 := by
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hf₀, mul_one,
      sub_self]
  have h := hΛ.flag2 T hT _ hy
  have e : T (x - M₀.B x b • f₀) - (x - M₀.B x b • f₀) = T x - x - M₀.B x b • (T f₀ - f₀) := by
    rw [map_sub, map_smul, smul_sub]; abel
  rwa [e] at h

theorem FlagData.hat_mul_mem (hΛ : FlagData M₀ b W Λ) {T S : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ)
    (hS : S ∈ Λ) : (T * S) f₀ - f₀ - ((T f₀ - f₀) + (S f₀ - f₀)) ∈ W := by
  have h := hΛ.flag2 T hT (S f₀ - f₀) (hΛ.B_sub_self hS f₀)
  have hTS : (T * S) f₀ = T (S f₀) := rfl
  have e : (T * S) f₀ - f₀ - ((T f₀ - f₀) + (S f₀ - f₀)) = T (S f₀ - f₀) - (S f₀ - f₀) := by
    rw [hTS, map_sub]; abel
  rwa [e]

theorem FlagData.hat_inv_mem (hΛ : FlagData M₀ b W Λ) {T : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ) :
    T⁻¹ f₀ - f₀ + (T f₀ - f₀) ∈ W := by
  have h := hΛ.hat_mul_mem (f₀ := f₀) (Λ.inv_mem hT) hT
  rw [inv_mul_cancel] at h
  have e : (1 : M₀.E ≃ₗ[K] M₀.E) f₀ - f₀ - ((T⁻¹ f₀ - f₀) + (T f₀ - f₀)) =
      -(T⁻¹ f₀ - f₀ + (T f₀ - f₀)) := by
    rw [show (1 : M₀.E ≃ₗ[K] M₀.E) f₀ = f₀ from rfl]; abel
  rw [e] at h
  simpa using W.neg_mem h

theorem FlagData.eq_one_of_hat_mem (hΛ : FlagData M₀ b W Λ)
    (hinj : ∀ T ∈ Λ, (∀ e ∈ W, T e = e) → T = 1) (hf₀ : M₀.B f₀ b = 1)
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ) (h : T f₀ - f₀ ∈ W) : T = 1 := by
  refine hinj T hT fun e he => ?_
  have h1 := hΛ.B_hat hf₀ hT he
  rw [hΛ.B_eq_zero h he] at h1
  have h2 := hΛ.sub_eq hf₀ hT he
  rw [show flagPsi M₀ f₀ T e = 0 by linear_combination h1, zero_smul] at h2
  exact sub_eq_zero.mp h2

theorem FlagData.eq_of_hat_sub_mem (hΛ : FlagData M₀ b W Λ)
    (hinj : ∀ T ∈ Λ, (∀ e ∈ W, T e = e) → T = 1) (hf₀ : M₀.B f₀ b = 1)
    {T S : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ) (hS : S ∈ Λ)
    (h : (T f₀ - f₀) - (S f₀ - f₀) ∈ W) : T = S := by
  have h1 := hΛ.hat_mul_mem (f₀ := f₀) hT (Λ.inv_mem hS)
  have h2 := hΛ.hat_inv_mem (f₀ := f₀) hS
  have h3 : (T * S⁻¹) f₀ - f₀ ∈ W := by
    have := W.add_mem (W.add_mem h1 h2) h
    convert this using 1
    abel
  exact mul_inv_eq_one.mp (hΛ.eq_one_of_hat_mem hinj hf₀ (Λ.mul_mem hT (Λ.inv_mem hS)) h3)

theorem FlagData.exists_hat_sub_mem [Finite K] (hΛ : FlagData M₀ b W Λ)
    (hinj : ∀ T ∈ Λ, (∀ e ∈ W, T e = e) → T = 1) (hf₀ : M₀.B f₀ b = 1) {n : ℕ}
    (hWdim : Module.finrank K W = n) (hcard : Nat.card Λ = Nat.card K ^ (n - 1))
    {v : M₀.E} (hv : M₀.B v b = 0) : ∃ T ∈ Λ, T f₀ - f₀ - v ∈ W := by
  have hb : (⟨b, hΛ.hbW⟩ : W) ≠ 0 := fun h => hΛ.hb0 (congrArg Subtype.val h)
  have hHom0 := card_dual_ker_eval hWdim ⟨b, hΛ.hbW⟩ hb
  let φ : W →ₗ[K] K := (LinearMap.flip M₀.B v).comp W.subtype
  have hφ : φ ⟨b, hΛ.hbW⟩ = 0 := by
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.flip_apply]
    rw [Tim79.QuadModel.B_comm, hv, neg_zero]
  obtain ⟨T, hT, hTφ⟩ := hΛ.psi_surj hinj hf₀ hHom0 hcard φ hφ
  refine ⟨T, hT, hΛ.hWperp _ fun u hu => ?_⟩
  have h1 := hΛ.B_hat hf₀ hT hu
  have h2 := hTφ ⟨u, hu⟩
  simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.flip_apply] at h2
  rw [map_sub (M₀.B) (T f₀ - f₀) v, LinearMap.sub_apply, h1, h2, Tim79.QuadModel.B_comm u v]
  ring

theorem FlagData.hat_conj_mem (hΛ : FlagData M₀ b W Λ) (hf₀ : M₀.B f₀ b = 1)
    {g T : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ)
    (hgiso : ∀ e, M₀.Qf (g e) = M₀.Qf e) (hgb : g b = b) (hgW : ∀ x ∈ W, g x ∈ W) :
    (g * T * g⁻¹) f₀ - f₀ - g (T f₀ - f₀) ∈ W := by
  have hgu : g (g⁻¹ f₀) = f₀ := g.apply_symm_apply f₀
  have hub : M₀.B (g⁻¹ f₀ - f₀) b = 0 := by
    have h := Tim79.QuadModel.B_iso (T := (g : M₀.E →ₗ[K] M₀.E)) hgiso (g⁻¹ f₀) b
    simp only [LinearEquiv.coe_coe] at h
    rw [hgu, hgb, hf₀] at h
    rw [map_sub, LinearMap.sub_apply, ← h, hf₀, sub_self]
  have h1 := hgW _ (hΛ.flag2 T hT _ hub)
  have e : (g * T * g⁻¹) f₀ - f₀ - g (T f₀ - f₀) = g (T (g⁻¹ f₀ - f₀) - (g⁻¹ f₀ - f₀)) := by
    show g (T (g⁻¹ f₀)) - f₀ - g (T f₀ - f₀) = g (T (g⁻¹ f₀ - f₀) - (g⁻¹ f₀ - f₀))
    simp only [map_sub, hgu]
    abel
  rw [e]
  exact h1

theorem FlagData.fix_of_perp {d₀ : M₀.E} {Dd : Submodule K M₀.E}
    {Λd : Subgroup (M₀.E ≃ₗ[K] M₀.E)} (hd : FlagData M₀ d₀ Dd Λd) {W : AddSubgroup M₀.E}
    (hWDd : ∀ w ∈ W, w ∈ Dd → w = 0) {g : M₀.E ≃ₗ[K] M₀.E} (hg : g ∈ Λd)
    (hgW : ∀ w ∈ W, g w ∈ W) {w : M₀.E} (hw : w ∈ W) (hwd : M₀.B w d₀ = 0) : g w = w :=
  sub_eq_zero.mp (hWDd _ (W.sub_mem (hgW w hw) hw) (hd.flag2 g hg w hwd))

theorem FlagData.comm_apply_eq {c₀ : M₀.E} {Dc : Submodule K M₀.E}
    {Λc : Subgroup (M₀.E ≃ₗ[K] M₀.E)} (hc : FlagData M₀ c₀ Dc Λc)
    {l g : M₀.E ≃ₗ[K] M₀.E} (hl : l ∈ Λc) (hgc : g c₀ = c₀) {w : M₀.E} (hw : w ∈ Dc)
    (hgw : g w = w) : (l * g * l⁻¹ * g⁻¹) w = w := by
  have hgi : g⁻¹ w = w := by
    conv_lhs => rw [← hgw]
    exact g.symm_apply_apply w
  obtain ⟨κ, hκ⟩ := hc.flag3 l⁻¹ (Λc.inv_mem hl) w hw
  have hli : l⁻¹ w = w + κ • c₀ := by rw [← hκ]; abel
  have hgl : g (l⁻¹ w) = l⁻¹ w := by rw [hli, map_add, map_smul, hgw, hgc]
  show l (g (l⁻¹ (g⁻¹ w))) = w
  rw [hgi, hgl]
  exact l.apply_symm_apply w

end CFSG.RankThree.GF2n.Stroth80
