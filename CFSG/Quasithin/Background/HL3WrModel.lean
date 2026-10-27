module

public import CFSG.Quasithin.H13.StatementsCh7
public import CFSG.Quasithin.Background.HSL3Pair

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin.H13
open scoped Matrix

abbrev WMod : Type := Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))

abbrev SL32 : Subgroup (GL (Fin 3) (ZMod 2)) := StatedSL 3 (ZMod 2)

abbrev mat (g : ↥SL32) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))

theorem mat_mul (g h : ↥SL32) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat 1 = 1 := rfl

theorem mat_inv_mul (g : ↥SL32) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_mul_inv (g : ↥SL32) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem mem_SL32 (g : GL (Fin 3) (ZMod 2)) : g ∈ SL32 := by
  rw [SL3Pair.mem_statedSL_iff]
  have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det
    with h | h
  · rw [h] at hu
    exact absurd hu not_isUnit_zero
  · exact h

@[expose] def act (g : ↥SL32 × ↥SL32) (X : WMod) : WMod :=
  Multiplicative.ofAdd (mat g.1 * Multiplicative.toAdd X * (mat g.2)ᵀ)

theorem toAdd_act (g : ↥SL32 × ↥SL32) (X : WMod) :
    Multiplicative.toAdd (act g X) = mat g.1 * Multiplicative.toAdd X * (mat g.2)ᵀ := rfl

theorem act_mul (g h : ↥SL32 × ↥SL32) (X : WMod) : act (g * h) X = act g (act h X) := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_act, Prod.fst_mul, Prod.snd_mul, mat_mul, Matrix.transpose_mul,
    Matrix.mul_assoc]

theorem act_one (X : WMod) : act 1 X = X := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_act, Prod.fst_one, Prod.snd_one, mat_one, Matrix.transpose_one,
    Matrix.one_mul, Matrix.mul_one]

theorem act_mul_right (g : ↥SL32 × ↥SL32) (X Y : WMod) :
    act g (X * Y) = act g X * act g Y := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_act, toAdd_mul, Matrix.mul_add, Matrix.add_mul]

@[expose] def rho : ↥SL32 × ↥SL32 →* MulAut WMod where
  toFun g :=
    { toFun := act g
      invFun := act g⁻¹
      left_inv := fun X => by rw [← act_mul, inv_mul_cancel, act_one]
      right_inv := fun X => by rw [← act_mul, mul_inv_cancel, act_one]
      map_mul' := act_mul_right g }
  map_one' := MulEquiv.ext act_one
  map_mul' g h := MulEquiv.ext fun X => act_mul g h X

theorem rho_apply (g : ↥SL32 × ↥SL32) (X : WMod) : rho g X = act g X := rfl

theorem toAdd_rho (g : ↥SL32 × ↥SL32) (X : WMod) :
    Multiplicative.toAdd (rho g X) = mat g.1 * Multiplicative.toAdd X * (mat g.2)ᵀ := rfl

theorem tensorPairModel_act (g : ↥SL32 × ↥SL32) (X : WMod) :
    (tensorPairModel SL32 SL32).act g X = rho g X := rfl

theorem rho_injective : Function.Injective rho := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, h⟩ hγ
  have key : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), mat g * X * (mat h)ᵀ = X := fun X => by
    have := congrArg (fun φ : MulAut WMod => Multiplicative.toAdd (φ (Multiplicative.ofAdd X))) hγ
    simpa [toAdd_rho] using this
  have hinv : (mat h)ᵀ = mat g⁻¹ := by
    have h1 := key 1
    rw [Matrix.mul_one] at h1
    calc (mat h)ᵀ = mat g⁻¹ * (mat g * (mat h)ᵀ) := by
          rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
      _ = mat g⁻¹ := by rw [h1, Matrix.mul_one]
  have hcomm : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), Commute X (mat g) := by
    intro X
    have h1 := key X
    rw [hinv] at h1
    calc X * mat g = mat g * X * mat g⁻¹ * mat g := by rw [h1]
      _ = mat g * X := by rw [Matrix.mul_assoc _ (mat g⁻¹), mat_inv_mul, Matrix.mul_one]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single fun i j _ => hcomm _
  have hc1 : c = 1 := by
    have hdet := SL3Pair.mem_statedSL_iff.mp g.2
    change (mat g).det = 1 at hdet
    rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) c with rfl | rfl
    · simp at hdet
    · rfl
  have hg1 : g = 1 := by
    apply Subtype.ext
    apply Units.ext
    change mat g = 1
    rw [← hc, hc1]
    simp
  have hh1 : h = 1 := by
    rw [hg1, inv_one, mat_one] at hinv
    apply Subtype.ext
    apply Units.ext
    change mat h = 1
    rw [← Matrix.transpose_transpose (mat h), hinv, Matrix.transpose_one]
  rw [hg1, hh1]
  rfl

@[expose] def tau : MulAut WMod where
  toFun X := Multiplicative.ofAdd (Multiplicative.toAdd X)ᵀ
  invFun X := Multiplicative.ofAdd (Multiplicative.toAdd X)ᵀ
  left_inv X := by simp
  right_inv X := by simp
  map_mul' X Y := by
    apply Multiplicative.toAdd.injective
    simp [Matrix.transpose_add]

theorem toAdd_tau (X : WMod) :
    Multiplicative.toAdd (tau X) = (Multiplicative.toAdd X)ᵀ := rfl

theorem tau_mul_self : tau * tau = 1 := MulEquiv.ext fun X => by
  apply Multiplicative.toAdd.injective
  change ((Multiplicative.toAdd X)ᵀ)ᵀ = Multiplicative.toAdd X
  rw [Matrix.transpose_transpose]

theorem tau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right tau_mul_self

theorem tau_conj_rho (g : ↥SL32 × ↥SL32) : tau * rho g * tau⁻¹ = rho g.swap := by
  rw [tau_inv]
  refine MulEquiv.ext fun X => ?_
  apply Multiplicative.toAdd.injective
  change (mat g.1 * ((Multiplicative.toAdd X)ᵀ) * (mat g.2)ᵀ)ᵀ =
    mat g.2 * Multiplicative.toAdd X * (mat g.1)ᵀ
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.mul_assoc]

theorem tau_mul_rho (g : ↥SL32 × ↥SL32) : tau * rho g = rho g.swap * tau := by
  rw [← tau_conj_rho, inv_mul_cancel_right]

@[expose] def img : Subgroup (MulAut WMod) := rho.range

@[expose] def norm : Subgroup (MulAut WMod) := Subgroup.normalizer (img : Set (MulAut WMod))

theorem rho_mem_img (g : ↥SL32 × ↥SL32) : rho g ∈ img := ⟨g, rfl⟩

theorem img_le_norm : img ≤ norm := Subgroup.le_normalizer

theorem tau_mem_norm : tau ∈ norm := by
  rw [norm, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨g, rfl⟩
    rw [tau_conj_rho]
    exact rho_mem_img _
  · intro hx
    obtain ⟨g, hg⟩ := hx
    have : x = tau * rho g * tau⁻¹ := by
      rw [hg, tau_inv]
      calc x = (tau * tau) * x * (tau * tau) := by rw [tau_mul_self, one_mul, mul_one]
        _ = tau * (tau * x * tau) * tau := by simp only [mul_assoc]
    rw [this, tau_conj_rho]
    exact rho_mem_img _

theorem tau_not_mem_img : tau ∉ img := by
  rintro ⟨⟨a, b⟩, hab⟩
  have key : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), mat a * X * (mat b)ᵀ = Xᵀ := fun X => by
    have := congrArg (fun φ : MulAut WMod => Multiplicative.toAdd (φ (Multiplicative.ofAdd X))) hab
    simpa [toAdd_rho, toAdd_tau] using this
  have hinv : (mat b)ᵀ = mat a⁻¹ := by
    have h1 := key 1
    rw [Matrix.mul_one, Matrix.transpose_one] at h1
    calc (mat b)ᵀ = mat a⁻¹ * (mat a * (mat b)ᵀ) := by
          rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
      _ = mat a⁻¹ := by rw [h1, Matrix.mul_one]
  have hmul : ∀ X Y : Matrix (Fin 3) (Fin 3) (ZMod 2), (X * Y)ᵀ = Xᵀ * Yᵀ := by
    intro X Y
    rw [← key, ← key X, ← key Y, hinv]
    calc mat a * (X * Y) * mat a⁻¹ = mat a * X * (mat a⁻¹ * mat a) * Y * mat a⁻¹ := by
          rw [mat_inv_mul, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = mat a * X * mat a⁻¹ * (mat a * Y * mat a⁻¹) := by simp only [Matrix.mul_assoc]
  have h := hmul (Matrix.single 0 1 1) (Matrix.single 1 0 1)
  have h' := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply] at h'

theorem exists_model {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    (h : (tensorPairModel SL32 SL32).RealizesMod H) :
    ∃ e : V ≃* WMod, H.map (congrHom e) = img := by
  obtain ⟨π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let q : ↥(⊤ : Subgroup WMod) ⧸ (⊥ : Subgroup WMod).subgroupOf (⊤ : Subgroup WMod) ≃* WMod :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  let e : V ≃* WMod :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective β ⟨hβi, hβs⟩)).trans q
  have hqs : ∀ x, x = (QuotientGroup.mk ⟨q x, trivial⟩ : ↥(⊤ : Subgroup WMod) ⧸
      (⊥ : Subgroup WMod).subgroupOf (⊤ : Subgroup WMod)) := fun x => by
    induction x using QuotientGroup.induction_on with
    | H m => rfl
  have he : ∀ (γ : ↥SL32 × ↥SL32) (v : V), e (((π γ : ↥H) : MulAut V) v) = rho γ (e v) := by
    intro γ v
    have h1 : β ⟨v, trivial⟩ = QuotientGroup.mk ⟨e v, trivial⟩ := hqs _
    have h2 := hβe γ ⟨v, trivial⟩ ⟨e v, trivial⟩ trivial trivial h1
    exact congrArg q h2
  refine ⟨e, ?_⟩
  have hpair : ∀ γ : ↥SL32 × ↥SL32, congrHom e ((π γ : ↥H) : MulAut V) = rho γ := by
    intro γ
    refine MulEquiv.ext fun w => ?_
    show e (((π γ : ↥H) : MulAut V) (e.symm w)) = rho γ w
    rw [he, MulEquiv.apply_symm_apply]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    have hx' : ((π γ : ↥H) : MulAut V) = x := by rw [hγ]
    have h1 := hpair γ
    rw [hx'] at h1
    rw [h1]
    exact rho_mem_img γ
  · rintro ⟨γ, rfl⟩
    exact ⟨_, (π γ).2, hpair γ⟩

end L3Wr

end H

end CFSG.Quasithin
