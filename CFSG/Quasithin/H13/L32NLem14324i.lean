module

public import CFSG.Quasithin.H13.L32NLem14324h
public import CFSG.Quasithin.Background.SzG11SConcl
public import CFSG.Adapters.GeneralizedFitting

public section
namespace CFSG.Quasithin.H13.L14324

open Matrix CFSG.Quasithin.SzPS8 CFSG.Quasithin.SzPS8.L28 CFSG.Open
open scoped MatrixGroups

theorem card_le_two_mul {X : Type*} [Group X] [Finite X] (K : Subgroup X)
    (hK : ∀ x y : X, x ∉ K → y ∉ K → x * y ∈ K) : Nat.card X ≤ 2 * Nat.card K := by
  classical
  by_cases hall : ∀ x : X, x ∈ K
  · have : K = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [this, Subgroup.card_top]
    omega
  push Not at hall
  obtain ⟨a, ha⟩ := hall
  have hidx : K.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨a, fun b => ?_⟩
    by_cases hb : b ∈ K
    · refine Or.inr ⟨hb, fun hba => ha ?_⟩
      have := K.mul_mem (K.inv_mem hb) hba
      rwa [inv_mul_cancel_left] at this
    · exact Or.inl ⟨hK b a hb ha, hb⟩
  have := K.card_mul_index
  rw [hidx] at this
  omega


theorem exists_smul_sl {P : Matrix (Fin 2) (Fin 2) F4} (hP : IsUnit P.det) :
    ∃ (p : F4) (g : SL(2, F4)), p ≠ 0 ∧ P = p • (g : Matrix (Fin 2) (Fin 2) F4) := by
  obtain ⟨p, hp⟩ := exists_sq_eq (K := F4) P.det
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hp
    exact hP.ne_zero hp.symm
  refine ⟨p, ⟨p⁻¹ • P, ?_⟩, hp0, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin, ← hp, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hp0)]
  · show P = p • (p⁻¹ • P)
    rw [smul_smul, mul_inv_cancel₀ hp0, one_smul]

theorem card_sl2_f4 : Nat.card SL(2, F4) = 60 := by
  classical
  have : Fintype F4 := Fintype.ofFinite F4
  have hK : Fintype.card F4 = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  rw [Matrix.card_SL_field 2, hK, Fin.prod_univ_two]
  norm_num

theorem card_le_four_of_sq {E : Subgroup SL(2, F4)} (hE : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact hE _ x.2)⟩
  obtain ⟨k, hk⟩ := hE2.exists_card_eq
  have hdvd : 2 ^ k ∣ 2 ^ 2 * 15 := by
    rw [← hk, show 2 ^ 2 * 15 = 60 by norm_num, ← card_sl2_f4]
    exact Subgroup.card_subgroup_dvd_card E
  have hcop : Nat.Coprime (2 ^ k) 15 := Nat.Coprime.pow_left k (by norm_num)
  have hk2 : k ≤ 2 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd)
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

theorem center_sl2_f4 : Subgroup.center SL(2, F4) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr1 : r = 1 := by
    have h2 : (r - 1) ^ 2 = 0 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [Fintype.card_fin] at hr
      rw [sub_pow_char, one_pow, hr, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp [Matrix.one_apply]



theorem card_le_eight_of_two {X : Type*} [Group X] [Finite X] (N L : Subgroup X)
    (hN : ∀ x y : X, x ∉ N → y ∉ N → x * y ∈ N) (hL : ∀ x y : X, x ∉ L → y ∉ L → x * y ∈ L)
    (hne : ∃ x : X, ¬ (x ∈ N ∧ x ∈ L))
    (hB1 : (∃ x : X, x ∉ N) → Nat.card ↥(N ⊓ L) ≤ 4)
    (hB2 : (∃ y : X, y ∈ N ∧ y ∉ L) → Nat.card ↥(N ⊓ L) ≤ 4)
    (hB3 : (∃ x : X, x ∉ N) → (∃ y : X, y ∈ N ∧ y ∉ L) → Nat.card ↥(N ⊓ L) ≤ 2) :
    Nat.card X ≤ 8 := by
  have hXN := card_le_two_mul N hN
  have hNL : Nat.card N ≤ 2 * Nat.card ↥(N ⊓ L) := by
    have h := card_le_two_mul (L.subgroupOf N) (fun x y hx hy => by
      rw [Subgroup.mem_subgroupOf] at hx hy ⊢
      rw [Subgroup.coe_mul]
      exact hL _ _ hx hy)
    have e : Nat.card ↥(L.subgroupOf N) = Nat.card ↥(N ⊓ L) := by
      rw [← Subgroup.inf_subgroupOf_left]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [e] at h
    exact h
  by_cases hNtop : ∃ x : X, x ∉ N
  · have h1 := hB1 hNtop
    by_cases hNLle : ∃ y : X, y ∈ N ∧ y ∉ L
    · have h2 := hB3 hNtop hNLle
      omega
    · push Not at hNLle
      have : Nat.card N = Nat.card ↥(N ⊓ L) := by
        have hle : N ≤ N ⊓ L := fun y hy => ⟨hy, hNLle y hy⟩
        rw [le_antisymm inf_le_left hle]
      omega
  · push Not at hNtop
    obtain ⟨x, hx⟩ := hne
    have hxL : x ∉ L := fun hxL => hx ⟨hNtop x, hxL⟩
    have h2 := hB2 ⟨x, hNtop x, hxL⟩
    have : Nat.card X = Nat.card N := by
      rw [show N = ⊤ from eq_top_iff.mpr fun y _ => hNtop y, Subgroup.card_top]
    omega

namespace Model7

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (M : Model7 Γ)

theorem alpha_of_mem (γ : ↥Γ) (f : ↥(genFittingFStar ↥Γ)) (hγf : γ * f = f * γ) :
    M.alpha γ (M.θ f) = M.θ f := by
  rw [M.alpha_eq_iff, MulEquiv.symm_apply_apply, hγf]
  group

theorem alpha_mul_left (γ δ : ↥Γ) (z : Pr) : M.alpha (γ * δ) z = M.alpha γ (M.alpha δ z) := by
  rw [M.alpha_eq_iff, M.alpha_spec, M.alpha_spec]
  group

theorem alpha_injective (γ : ↥Γ) : Function.Injective (M.alpha γ) := by
  intro z w h
  have h1 := congrArg (M.alpha γ⁻¹) h
  have e : ∀ u, M.alpha γ⁻¹ (M.alpha γ u) = u := by
    intro u
    have := M.alpha_alpha_inv γ⁻¹ u
    rwa [inv_inv] at this
  rwa [e, e] at h1

theorem eq_of_hat_smul_act [Finite V] (x : ↥Γ) (c : F4) (z : Pr)
    (hx : ∀ X, hatOf M.e (x : V ≃ₗ[ZMod 2] V) X = c • act z X) :
    x = (M.θ.symm z : ↥Γ) := by
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  set f₀ : ↥(genFittingFStar ↥Γ) := M.θ.symm z with hf₀
  have hf₀act : ∀ X, hatOf M.e ((f₀ : ↥Γ) : V ≃ₗ[ZMod 2] V) X = act z X := fun X => by
    rw [M.hact, hf₀, MulEquiv.apply_symm_apply]
  set x' : ↥Γ := x * (f₀ : ↥Γ)⁻¹ with hx'
  have hx'hat : ∀ X, hatOf M.e (x' : V ≃ₗ[ZMod 2] V) X = c • X := by
    intro X
    rw [hx', Subgroup.coe_mul, hatOf_mul, hx, Subgroup.coe_inv]
    congr 1
    have := hf₀act (hatOf M.e ((f₀ : ↥Γ) : V ≃ₗ[ZMod 2] V)⁻¹ X)
    rw [hatOf_hatOf_inv] at this
    exact this.symm
  clear_value x'
  have hcomm : ∀ f ∈ genFittingFStar ↥Γ, x' * f = f * x' := by
    intro f hf
    apply Subtype.ext
    apply hatOf_injective M.e
    intro X
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hatOf_mul, hatOf_mul, hx'hat, hx'hat]
    have h1 := M.hact ⟨f, hf⟩
    simp only at h1
    rw [h1, h1, act_smul]
  have hx'F : x' ∈ genFittingFStar ↥Γ :=
    CFSG.Adapters.generalized_fitting_self_centralizing ↥Γ
      (Subgroup.mem_centralizer_iff.mpr fun f hf => (hcomm f hf).symm)
  have hθ : M.θ ⟨x', hx'F⟩ ∈ Subgroup.center Pr := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply act_injective
    intro X
    rw [act_mul, act_mul]
    have h1 := M.hact ⟨x', hx'F⟩
    simp only at h1
    rw [← h1, ← h1, hx'hat, hx'hat, act_smul]
  have hcen : Subgroup.center Pr = ⊥ := by
    rw [Subgroup.center_prod, center_sl2_f4, Subgroup.bot_prod_bot]
  rw [hcen, Subgroup.mem_bot] at hθ
  have hx'1 : x' = 1 := by
    have := congrArg Subtype.val (M.θ.injective (hθ.trans (map_one M.θ).symm))
    exact this
  calc x = x' * (f₀ : ↥Γ) := by rw [hx']; group
    _ = (f₀ : ↥Γ) := by rw [hx'1, one_mul]

@[expose] def LinP (ω : F4) (x : ↥Γ) : Prop :=
  ∀ Y, hatOf M.e (x : V ≃ₗ[ZMod 2] V) (ω • Y) = ω • hatOf M.e (x : V ≃ₗ[ZMod 2] V) Y

@[expose] def NrmP (x : ↥Γ) : Prop := ∀ g : SL(2, F4), (M.alpha x (g, 1)).2 = 1

theorem linP_mul {ω : F4} {x y : ↥Γ} (hx : M.LinP ω x) (hy : M.LinP ω y) : M.LinP ω (x * y) := by
  intro Y
  simp only [Subgroup.coe_mul, hatOf_mul]
  rw [hy, hx]

theorem linP_mul_not {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) {x y : ↥Γ} (hx : ¬ M.LinP ω x)
    (hy : ¬ M.LinP ω y) : M.LinP ω (x * y) := by
  have h2 : (2 : F4) = 0 := CharTwo.two_eq_zero
  have hc : ∀ z : ↥Γ, ¬ M.LinP ω z → ∀ Y, hatOf M.e (z : V ≃ₗ[ZMod 2] V) (ω • Y) =
      (ω + 1) • hatOf M.e (z : V ≃ₗ[ZMod 2] V) Y := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := M.exists_omega_conj hω z
    rcases hc with rfl | rfl
    · exact absurd hzc hz
    · exact hzc
  intro Y
  simp only [Subgroup.coe_mul, hatOf_mul]
  rw [hc y hy, add_smul, one_smul, map_add, hc x hx, add_smul, one_smul, add_assoc,
    ← two_smul F4, h2, zero_smul, add_zero]

theorem nrmP_one : M.NrmP 1 := by
  intro g
  have : M.alpha 1 (g, 1) = (g, 1) := by
    rw [M.alpha_eq_iff]
    group
  rw [this]

theorem nrmP_mul {x y : ↥Γ} (hx : M.NrmP x) (hy : M.NrmP y) : M.NrmP (x * y) := by
  intro g
  rw [M.alpha_mul_left]
  have : M.alpha y (g, 1) = ((M.alpha y (g, 1)).1, 1) := Prod.ext rfl (hy g)
  rw [this]
  exact hx _

theorem alpha_snd_of_not_nrmP {x : ↥Γ} (hx : ¬ M.NrmP x) (b : SL(2, F4)) :
    (M.alpha x (1, b)).2 = 1 := by
  have hR := (M.left_or_right x).resolve_left hx
  have hinj : Function.Injective fun g : SL(2, F4) => (M.alpha x (g, 1)).2 := by
    intro g g' h
    have : M.alpha x (g, 1) = M.alpha x (g', 1) := Prod.ext ((hR g).trans (hR g').symm) h
    exact congrArg Prod.fst (M.alpha_injective x this)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  have hc : ∀ h : SL(2, F4), (M.alpha x (1, b)).2 * h = h * (M.alpha x (1, b)).2 := by
    intro h
    obtain ⟨g, rfl⟩ := hsurj h
    have hcomm : M.alpha x (1, b) * M.alpha x (g, 1) = M.alpha x (g, 1) * M.alpha x (1, b) := by
      rw [← M.alpha_mul, ← M.alpha_mul]
      congr 1
      ext <;> simp
    exact congrArg Prod.snd hcomm
  have hcen : (M.alpha x (1, b)).2 ∈ Subgroup.center SL(2, F4) :=
    Subgroup.mem_center_iff.mpr fun h => (hc h).symm
  rw [center_sl2_f4, Subgroup.mem_bot] at hcen
  exact hcen

theorem nrmP_mul_not {x y : ↥Γ} (hx : ¬ M.NrmP x) (hy : ¬ M.NrmP y) : M.NrmP (x * y) := by
  intro g
  have hR := (M.left_or_right y).resolve_left hy
  rw [M.alpha_mul_left]
  have : M.alpha y (g, 1) = (1, (M.alpha y (g, 1)).2) := Prod.ext (hR g) rfl
  rw [this]
  exact M.alpha_snd_of_not_nrmP hx _

theorem mem_of_linP_nrmP [Finite V] {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) {x : ↥Γ} (hl : M.LinP ω x)
    (hn : M.NrmP x) : x ∈ genFittingFStar ↥Γ := by
  obtain ⟨P, Q, δ, ε, hP, hQ, hεiff, hδiff, hshape⟩ := M.exists_shape hω x
  have hε : ε = false := hεiff.mpr hl
  have hδ : δ = false := hδiff.mpr hn
  obtain ⟨p, g, -, rfl⟩ := exists_smul_sl hP
  obtain ⟨q, h, -, rfl⟩ := exists_smul_sl hQ
  have hx : ∀ X, hatOf M.e (x : V ≃ₗ[ZMod 2] V) X = (p * q) • act (g, h⁻¹) X := by
    intro X
    rw [hshape, hδ, hε]
    simp only [trIf, frobIf, Bool.false_eq_true, ↓reduceIte, act, inv_inv]
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [M.eq_of_hat_smul_act x (p * q) (g, h⁻¹) hx]
  exact (M.θ.symm (g, h⁻¹)).2

theorem sl_inv_mul_cancel_left (g : SL(2, F4)) (W : Matrix (Fin 2) (Fin 2) F4) :
    ((g⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) * ((g : Matrix (Fin 2) (Fin 2) F4) * W) =
      W := by
  rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

theorem sl_mul_inv_cancel_left (g : SL(2, F4)) (W : Matrix (Fin 2) (Fin 2) F4) :
    (g : Matrix (Fin 2) (Fin 2) F4) * (((g⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) * W) =
      W := by
  rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

theorem alpha_of_frob (y : ↥Γ) (p q : F4) (g h : SL(2, F4))
    (hy : ∀ X, hatOf M.e (y : V ≃ₗ[ZMod 2] V) X =
      (p • (g : Matrix (Fin 2) (Fin 2) F4)) * frobM X * (q • (h : Matrix (Fin 2) (Fin 2) F4)))
    (a b : SL(2, F4)) :
    M.alpha y (a, b) = (g * frobSL a * g⁻¹, h⁻¹ * frobSL b * h) := by
  apply act_injective
  intro Y
  obtain ⟨X, rfl⟩ : ∃ X, hatOf M.e (y : V ≃ₗ[ZMod 2] V) X = Y :=
    ⟨hatOf M.e (y : V ≃ₗ[ZMod 2] V)⁻¹ Y, hatOf_hatOf_inv _ _ _⟩
  rw [← M.hat_act, hy, hy]
  unfold act
  simp only [_root_.mul_inv_rev, inv_inv]
  rw [frobM_mul, frobM_mul, frobM_sl a, frobM_sl b⁻¹, map_inv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_assoc, sl_inv_mul_cancel_left, sl_mul_inv_cancel_left]

@[expose] noncomputable def pi2 : ↥(genFittingFStar ↥Γ) →* SL(2, F4) :=
  (MonoidHom.snd _ _).comp M.θ.toMonoidHom

@[expose] noncomputable def pi1 : ↥(genFittingFStar ↥Γ) →* SL(2, F4) :=
  (MonoidHom.fst _ _).comp M.θ.toMonoidHom

theorem pi2_injOn_of_not_nrmP {x : ↥Γ} (hx : ¬ M.NrmP x) (K : Subgroup ↥(genFittingFStar ↥Γ))
    (hK : ∀ f ∈ K, x * (f : ↥Γ) = (f : ↥Γ) * x) {f : ↥(genFittingFStar ↥Γ)} (hf : f ∈ K)
    (h1 : M.pi2 f = 1) : f = 1 := by
  have hR := (M.left_or_right x).resolve_left hx
  have hfix := M.alpha_of_mem x f (hK f hf)
  have hθ : M.θ f = ((M.θ f).1, 1) := Prod.ext rfl h1
  have h2 := hR (M.θ f).1
  rw [← hθ, hfix] at h2
  apply M.θ.injective
  rw [map_one]
  exact Prod.ext h2 h1

theorem card_le_four_of_injOn (K : Subgroup ↥(genFittingFStar ↥Γ)) (hsq : ∀ f ∈ K, f * f = 1)
    (hinj : ∀ f ∈ K, M.pi2 f = 1 → f = 1) : Nat.card K ≤ 4 := by
  have hker : (M.pi2.comp K.subtype).ker = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hf
    exact Subgroup.mem_bot.mpr (Subtype.ext (hinj f f.2 hf))
  have hinj' := (MonoidHom.ker_eq_bot_iff _).mp hker
  rw [Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv]
  refine card_le_four_of_sq fun e he => ?_
  obtain ⟨f, rfl⟩ := he
  have hff : f * f = 1 := Subtype.ext (hsq _ f.2)
  rw [← map_mul, hff, map_one]

theorem card_proj_le_two {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) {y : ↥Γ} (hn : M.NrmP y)
    (hl : ¬ M.LinP ω y) (K : Subgroup ↥(genFittingFStar ↥Γ)) (hsq : ∀ f ∈ K, f * f = 1)
    (hK : ∀ f ∈ K, y * (f : ↥Γ) = (f : ↥Γ) * y) :
    Nat.card ↥(K.map M.pi1) ≤ 2 ∧ Nat.card ↥(K.map M.pi2) ≤ 2 := by
  obtain ⟨P, Q, δ, ε, hP, hQ, hεiff, hδiff, hshape⟩ := M.exists_shape hω y
  have hδ : δ = false := hδiff.mpr hn
  have hε : ε = true := by
    by_contra h
    exact hl (hεiff.mp (by simpa using h))
  obtain ⟨p, g, -, rfl⟩ := exists_smul_sl hP
  obtain ⟨q, h, -, rfl⟩ := exists_smul_sl hQ
  have hy : ∀ X, hatOf M.e (y : V ≃ₗ[ZMod 2] V) X =
      (p • (g : Matrix (Fin 2) (Fin 2) F4)) * frobM X * (q • (h : Matrix (Fin 2) (Fin 2) F4)) := by
    intro X
    rw [hshape, hδ, hε]
    rfl
  have hfix : ∀ f ∈ K, M.θ f = (g * frobSL (M.θ f).1 * g⁻¹, h⁻¹ * frobSL (M.θ f).2 * h) := by
    intro f hf
    have h1 := M.alpha_of_mem y f (hK f hf)
    have h2 := M.alpha_of_frob y p q g h hy (M.θ f).1 (M.θ f).2
    exact h1.symm.trans h2
  constructor
  · refine card_le_two_of_fixed g _ ?_ ?_
    · rintro _ ⟨f, hf, rfl⟩
      rw [← map_mul, hsq f hf, map_one]
    · rintro _ ⟨f, hf, rfl⟩
      exact (congrArg Prod.fst (hfix f hf)).symm
  · refine card_le_two_of_fixed h⁻¹ _ ?_ ?_
    · rintro _ ⟨f, hf, rfl⟩
      rw [← map_mul, hsq f hf, map_one]
    · rintro _ ⟨f, hf, rfl⟩
      rw [inv_inv]
      exact (congrArg Prod.snd (hfix f hf)).symm

theorem card_le_mul_proj (K : Subgroup ↥(genFittingFStar ↥Γ)) :
    Nat.card K ≤ Nat.card ↥(K.map M.pi1) * Nat.card ↥(K.map M.pi2) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun f => (⟨M.pi1 f, f, f.2, rfl⟩, ⟨M.pi2 f, f, f.2, rfl⟩))
    fun f f' hff => ?_
  have h1 := congrArg (fun z => (z.1 : SL(2, F4))) hff
  have h2 := congrArg (fun z => (z.2 : SL(2, F4))) hff
  simp only at h1 h2
  apply Subtype.ext
  apply M.θ.injective
  exact Prod.ext h1 h2

end Model7

theorem card_le_eight_of_concl7S {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)} (hXΓ : X ≤ Γ) (hX : IsElemAbelian 2 X)
    (h7 : G11.SzG11S.G112Concl7S Γ X) : Nat.card X ≤ 8 := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  obtain ⟨⟨-, -, hXnot⟩, hnat⟩ := h7
  obtain ⟨θ, e, he⟩ := SzPS8.exists_model hnat
  let ι := Subgroup.equivMapOfInjective (genFittingFStar ↥Γ) Γ.subtype Γ.subtype_injective
  let M : Model7 Γ :=
    { e := e
      θ := ι.trans θ
      hact := fun f X => by
        have := he (ι f) (e.symm X)
        rw [AddEquiv.apply_symm_apply] at this
        rw [hatOf_apply]
        exact this }
  obtain ⟨ω, hω⟩ := exists_omega
  set Xg : Subgroup ↥Γ := X.subgroupOf Γ with hXg
  have hXgcard : Nat.card Xg = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXΓ).toEquiv
  have hsqΓ : ∀ x : ↥Xg, ((x : ↥Γ)) * x = 1 := fun x => Subtype.ext (by
    have := hX.2 _ (Subgroup.mem_subgroupOf.mp x.2)
    simpa [sq] using this)
  have hcommΓ : ∀ x y : ↥Xg, (x : ↥Γ) * y = y * x := fun x y => Subtype.ext (by
    have := hX.1
    have h := mul_comm' (⟨_, Subgroup.mem_subgroupOf.mp x.2⟩ : ↥X)
      ⟨_, Subgroup.mem_subgroupOf.mp y.2⟩
    have h2 := congrArg Subtype.val h
    exact h2)
  have hinv : ∀ x : ↥Xg, x⁻¹ = x := fun x => by
    apply Subtype.ext
    rw [Subgroup.coe_inv, inv_eq_of_mul_eq_one_right (hsqΓ x)]
  let N : Subgroup ↥Xg :=
    { carrier := {x | M.NrmP (x : ↥Γ)}
      mul_mem' := fun hx hy => M.nrmP_mul hx hy
      one_mem' := M.nrmP_one
      inv_mem' := fun {x} hx => by rw [Set.mem_ofPred_eq, hinv x]; exact hx }
  let L : Subgroup ↥Xg :=
    { carrier := {x | M.LinP ω (x : ↥Γ)}
      mul_mem' := fun hx hy => M.linP_mul hx hy
      one_mem' := fun Y => by simp [hatOf_one]
      inv_mem' := fun {x} hx => by rw [Set.mem_ofPred_eq, hinv x]; exact hx }
  set K : Subgroup ↥(genFittingFStar ↥Γ) := Xg.subgroupOf (genFittingFStar ↥Γ) with hK
  have hKsq : ∀ f ∈ K, f * f = 1 := fun f hf => Subtype.ext (hsqΓ ⟨_, hf⟩)
  have hKcomm : ∀ x : ↥Xg, ∀ f ∈ K, (x : ↥Γ) * (f : ↥Γ) = (f : ↥Γ) * x := fun x f hf =>
    hcommΓ x ⟨_, hf⟩
  have hNLK : Nat.card ↥(N ⊓ L) ≤ Nat.card K := by
    refine Nat.card_le_card_of_injective (fun z => ⟨⟨(z : ↥Xg), M.mem_of_linP_nrmP hω z.2.2 z.2.1⟩,
      Subgroup.mem_subgroupOf.mpr (z : ↥Xg).2⟩) fun z z' h => ?_
    have := congrArg (fun w : ↥K => ((w : ↥(genFittingFStar ↥Γ)) : ↥Γ)) h
    exact Subtype.ext (Subtype.ext this)
  have hB1 : (∃ x : ↥Xg, x ∉ N) → Nat.card K ≤ 4 := by
    rintro ⟨x, hx⟩
    exact M.card_le_four_of_injOn K hKsq fun f hf h1 =>
      M.pi2_injOn_of_not_nrmP hx K (hKcomm x) hf h1
  have hB2 : (∃ y : ↥Xg, y ∈ N ∧ y ∉ L) → Nat.card K ≤ 4 := by
    rintro ⟨y, hyN, hyL⟩
    obtain ⟨h1, h2⟩ := M.card_proj_le_two hω hyN hyL K hKsq (hKcomm y)
    have := M.card_le_mul_proj K
    nlinarith
  have hB3 : (∃ x : ↥Xg, x ∉ N) → (∃ y : ↥Xg, y ∈ N ∧ y ∉ L) → Nat.card K ≤ 2 := by
    rintro ⟨x, hx⟩ ⟨y, hyN, hyL⟩
    obtain ⟨-, h2⟩ := M.card_proj_le_two hω hyN hyL K hKsq (hKcomm y)
    have hinj : ∀ f ∈ K, M.pi2 f = 1 → f = 1 := fun f hf h1 =>
      M.pi2_injOn_of_not_nrmP hx K (hKcomm x) hf h1
    have hker : (M.pi2.comp K.subtype).ker = ⊥ := by
      rw [eq_bot_iff]
      intro f hf
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hf
      exact Subgroup.mem_bot.mpr (Subtype.ext (hinj f f.2 hf))
    have hinj' := (MonoidHom.ker_eq_bot_iff _).mp hker
    have e1 : Nat.card K = Nat.card ↥(M.pi2.comp K.subtype).range :=
      Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv
    have e2 : (M.pi2.comp K.subtype).range = K.map M.pi2 := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [e1, e2]
    exact h2
  have hne : ∃ x : ↥Xg, ¬ (x ∈ N ∧ x ∈ L) := by
    obtain ⟨x, hxX, hxF⟩ := Set.not_subset.mp hXnot
    refine ⟨⟨⟨x, hXΓ hxX⟩, Subgroup.mem_subgroupOf.mpr hxX⟩, fun ⟨hn, hl⟩ => hxF ?_⟩
    exact ⟨_, M.mem_of_linP_nrmP hω hl hn, rfl⟩
  have := card_le_eight_of_two N L
    (fun x y hx hy => M.nrmP_mul_not hx hy) (fun x y hx hy => M.linP_mul_not hω hx hy) hne
    (fun h => (hNLK.trans (hB1 h))) (fun h => (hNLK.trans (hB2 h)))
    (fun h h' => (hNLK.trans (hB3 h h')))
  rw [← hXgcard]
  exact this


end CFSG.Quasithin.H13.L14324
