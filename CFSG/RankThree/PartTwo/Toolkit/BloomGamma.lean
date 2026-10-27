module

public import CFSG.RankThree.PartTwo.Toolkit.Statements
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Toolkit

open Subgroup
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "GL33" => GL (Fin 3) (ZMod 3)

local notation "K27" => GaloisField 3 3

theorem natCard_K27 : Nat.card K27 = 27 := GaloisField.card 3 3 (by norm_num)

theorem finrank_K27 : Module.finrank (ZMod 3) K27 = 3 := GaloisField.finrank 3 (by norm_num)

theorem pow_27_K27 (x : K27) : x ^ 27 = x := by
  have : Fintype K27 := Fintype.ofFinite K27
  have h := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, natCard_K27] at h

theorem natCard_units_K27 : Nat.card K27ˣ = 26 := by
  rw [Nat.card_units, natCard_K27]

@[expose] noncomputable def frobL : K27 →ₗ[ZMod 3] K27 where
  toFun x := x ^ 3
  map_add' x y := add_pow_char (p := 3) x y
  map_smul' a x := by
    rw [RingHom.id_apply, smul_pow, ZMod.pow_card]

theorem frobL_apply (x : K27) : frobL x = x ^ 3 := rfl

theorem frobL_frobL_frobL (x : K27) : frobL (frobL (frobL x)) = x := by
  rw [frobL_apply, frobL_apply, frobL_apply, ← pow_mul, ← pow_mul]
  exact pow_27_K27 x

variable (e : (Fin 3 → ZMod 3) ≃ₗ[ZMod 3] K27)

@[expose] noncomputable def toV (f : K27 →ₗ[ZMod 3] K27) :
    (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 3 → ZMod 3) :=
  e.symm.toLinearMap ∘ₗ f ∘ₗ e.toLinearMap

theorem toV_apply (f : K27 →ₗ[ZMod 3] K27) (v : Fin 3 → ZMod 3) :
    toV e f v = e.symm (f (e v)) := rfl

theorem toV_comp (f g : K27 →ₗ[ZMod 3] K27) : toV e (f ∘ₗ g) = toV e f ∘ₗ toV e g := by
  ext v
  simp [toV_apply]

theorem toV_id : toV e LinearMap.id = LinearMap.id := by
  ext v
  simp [toV_apply]

@[expose] noncomputable def glPair (f g : K27 →ₗ[ZMod 3] K27) (h₁ : f ∘ₗ g = LinearMap.id)
    (h₂ : g ∘ₗ f = LinearMap.id) : GL33 :=
  ⟨LinearMap.toMatrix' (toV e f), LinearMap.toMatrix' (toV e g),
    by rw [← LinearMap.toMatrix'_mul, Module.End.mul_eq_comp, ← toV_comp, h₁, toV_id,
      LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_mul, Module.End.mul_eq_comp, ← toV_comp, h₂, toV_id,
      LinearMap.toMatrix'_id]⟩

theorem glPair_mulVec (f g : K27 →ₗ[ZMod 3] K27) (h₁ h₂) (v : Fin 3 → ZMod 3) :
    e (((glPair e f g h₁ h₂ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v) = f (e v) := by
  change e (LinearMap.toMatrix' (toV e f) *ᵥ v) = f (e v)
  rw [LinearMap.toMatrix'_mulVec, toV_apply, LinearEquiv.apply_symm_apply]

theorem mulVec_mul (g h : GL33) (v : Fin 3 → ZMod 3) :
    ((g * h : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ((h : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem mulVec_one (v : Fin 3 → ZMod 3) :
    ((1 : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v := by
  rw [Units.val_one, Matrix.one_mulVec]

theorem gl_ext_e {g h : GL33}
    (hgh : ∀ v, e ((g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v) =
      e ((h : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v)) : g = h := by
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact e.injective (hgh v)

@[expose] noncomputable def muE : K27ˣ →* GL33 where
  toFun c := glPair e (LinearMap.mulLeft (ZMod 3) (c : K27))
    (LinearMap.mulLeft (ZMod 3) ((c⁻¹ : K27ˣ) : K27))
    (LinearMap.ext fun x => by simp) (LinearMap.ext fun x => by simp)
  map_one' := gl_ext_e e fun v => by
    rw [glPair_mulVec, mulVec_one, LinearMap.mulLeft_apply, Units.val_one, one_mul]
  map_mul' c d := gl_ext_e e fun v => by
    rw [glPair_mulVec, mulVec_mul, glPair_mulVec, glPair_mulVec, LinearMap.mulLeft_apply,
      LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, Units.val_mul, mul_assoc]

theorem muE_apply (c : K27ˣ) (v : Fin 3 → ZMod 3) :
    e (((muE e c : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v) = (c : K27) * e v := by
  simp only [muE, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [glPair_mulVec, LinearMap.mulLeft_apply]

theorem muE_injective : Function.Injective (muE e) := by
  intro c d h
  have h1 := muE_apply e c (e.symm 1)
  rw [h, muE_apply, LinearEquiv.apply_symm_apply, mul_one, mul_one] at h1
  exact Units.ext h1.symm

@[expose] noncomputable def tauE : GL33 :=
  glPair e frobL (frobL ∘ₗ frobL) (by ext x; exact frobL_frobL_frobL x)
    (by ext x; exact frobL_frobL_frobL x)

theorem tauE_apply (v : Fin 3 → ZMod 3) :
    e (((tauE e : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v) = e v ^ 3 := by
  rw [tauE, glPair_mulVec, frobL_apply]

theorem tauE_pow_apply (n : ℕ) (v : Fin 3 → ZMod 3) :
    e (((tauE e ^ n : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v) = e v ^ (3 ^ n) := by
  induction n generalizing v with
  | zero => rw [pow_zero, mulVec_one, pow_zero, pow_one]
  | succ n ih =>
    rw [pow_succ', mulVec_mul, tauE_apply, ih, ← pow_mul, pow_succ]

theorem tauE_pow_three : tauE e ^ 3 = 1 := gl_ext_e e fun v => by
  rw [tauE_pow_apply, mulVec_one]
  exact pow_27_K27 _

theorem tauE_ne_one : tauE e ≠ 1 := by
  intro h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K27ˣ)
  have hord : orderOf g = 26 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, natCard_units_K27]
  have h1 := tauE_apply e (e.symm (g : K27))
  rw [h, mulVec_one, LinearEquiv.apply_symm_apply] at h1
  have h3 : g ^ 3 = g := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h1.symm)
  have h2 : g ^ 2 = 1 := by
    have : g ^ 2 * g = 1 * g := by rw [← pow_succ, one_mul, h3]
    exact mul_right_cancel this
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hord] at this
  norm_num at this

theorem orderOf_tauE : orderOf (tauE e) = 3 :=
  orderOf_eq_prime (tauE_pow_three e) (tauE_ne_one e)

theorem tauE_conj_muE (c : K27ˣ) : tauE e * muE e c * (tauE e)⁻¹ = muE e (c ^ 3) := by
  apply gl_ext_e e
  intro v
  rw [mulVec_mul, mulVec_mul, tauE_apply, muE_apply, muE_apply, mul_pow, Units.val_pow_eq_pow_val]
  congr 1
  have h := tauE_apply e ((((tauE e)⁻¹ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v)
  rw [← mulVec_mul, mul_inv_cancel, mulVec_one] at h
  exact h.symm

noncomputable def gen27 : K27ˣ := Classical.choose (IsCyclic.exists_generator (α := K27ˣ))

theorem gen27_spec (x : K27ˣ) : x ∈ zpowers gen27 :=
  Classical.choose_spec (IsCyclic.exists_generator (α := K27ˣ)) x

theorem orderOf_gen27 : orderOf gen27 = 26 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers gen27_spec, natCard_units_K27]

noncomputable def H13 : Subgroup K27ˣ := zpowers (gen27 ^ 2)

theorem card_H13 : Nat.card H13 = 13 := by
  rw [H13, Nat.card_zpowers, orderOf_pow' _ (by norm_num), orderOf_gen27]
  rfl

noncomputable def FE : Subgroup GL33 := H13.map (muE e)

theorem card_FE : Nat.card (FE e) = 13 := by
  rw [FE, Subgroup.card_map_of_injective (muE_injective e), card_H13]

theorem FE_le_range : FE e ≤ (muE e).range := map_le_range _ _

theorem range_comm {a b : GL33} (ha : a ∈ (muE e).range) (hb : b ∈ (muE e).range) :
    a * b = b * a := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨d, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

theorem range_le_normalizer : (muE e).range ≤ normalizer (FE e : Set GL33) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [range_comm e ha (FE_le_range e hh), mul_inv_cancel_right]
    exact hh
  · intro hh
    have h1 := range_comm e ((muE e).range.inv_mem ha) (FE_le_range e hh)
    have : h = a⁻¹ * (a * h * a⁻¹) * a := by group
    rw [this, h1, inv_mul_cancel_right]
    exact hh

theorem tauE_mem_normalizer : tauE e ∈ normalizer (FE e : Set GL33) := by
  rw [← closure_eq (FE e)]
  refine CFSG.RankThree.Asc83Table.mem_normalizer_closure_of_conj_mem ?_
  rintro _ ⟨c, hc, rfl⟩
  rw [closure_eq, tauE_conj_muE]
  exact ⟨c ^ 3, H13.pow_mem hc 3, rfl⟩

theorem tauE_mem_normalizer_range : tauE e ∈ normalizer ((muE e).range : Set GL33) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c ^ 3, (tauE_conj_muE e c).symm⟩
  · rintro ⟨c, hc⟩
    refine ⟨c ^ 9, ?_⟩
    calc muE e (c ^ 9) = tauE e * (tauE e * muE e c * (tauE e)⁻¹) * (tauE e)⁻¹ := by
          rw [tauE_conj_muE, tauE_conj_muE, ← pow_mul]
      _ = tauE e ^ 3 * h * (tauE e ^ 3)⁻¹ := by rw [hc, pow_three]; group
      _ = h := by rw [tauE_pow_three]; group

theorem range_inf_zpowers : (muE e).range ⊓ zpowers (tauE e) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨c, rfl⟩, hx⟩
  have hfin : IsOfFinOrder (tauE e) := orderOf_pos_iff.1 (by rw [orderOf_tauE]; norm_num)
  obtain ⟨n, -, hn⟩ := Finset.mem_image.1 (hfin.mem_zpowers_iff_mem_range_orderOf.1 hx)
  have h1 := muE_apply e c (e.symm 1)
  rw [← hn, tauE_pow_apply, LinearEquiv.apply_symm_apply, one_pow, mul_one] at h1
  rw [Subgroup.mem_bot, show c = 1 from Units.ext h1.symm, map_one]

theorem card_range : Nat.card (muE e).range = 26 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (muE_injective e)).toEquiv, natCard_units_K27]

theorem le_card_sup : 78 ≤ Nat.card ((muE e).range ⊔ zpowers (tauE e) : Subgroup GL33) := by
  let f : (muE e).range × zpowers (tauE e) → ((muE e).range ⊔ zpowers (tauE e) : Subgroup GL33) :=
    fun p => ⟨p.1.1 * p.2.1, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h1 : a * b = a' * b' := congrArg Subtype.val h
    have h2 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = b' * b⁻¹ := by rw [h1]; group
    have h3 : a'⁻¹ * a ∈ ((muE e).range ⊓ zpowers (tauE e) : Subgroup GL33) :=
      ⟨(muE e).range.mul_mem ((muE e).range.inv_mem ha') ha,
        h2 ▸ (zpowers _).mul_mem hb' ((zpowers _).inv_mem hb)⟩
    rw [range_inf_zpowers, Subgroup.mem_bot, inv_mul_eq_one] at h3
    subst h3
    have h4 : b = b' := mul_left_cancel h1
    subst h4
    rfl
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, card_range, Nat.card_zpowers, orderOf_tauE] at this

theorem isSemilinearNormalizer_FE (h78 : Nat.card (normalizer (FE e : Set GL33)) = 78) :
    IsSemilinearNormalizer (FE e) := by
  have hle : (muE e).range ⊔ zpowers (tauE e) ≤ normalizer (FE e : Set GL33) :=
    sup_le (range_le_normalizer e) ((zpowers_le).2 (tauE_mem_normalizer e))
  have heq : (muE e).range ⊔ zpowers (tauE e) = normalizer (FE e : Set GL33) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [h78]; exact le_card_sup e)
  have hnorm : normalizer (FE e : Set GL33) ≤ normalizer ((muE e).range : Set GL33) := by
    rw [← heq]
    exact sup_le le_normalizer ((zpowers_le).2 (tauE_mem_normalizer_range e))
  refine ⟨e, muE e, tauE e, muE_injective e, muE_apply e, tauE_apply e, ?_, card_range e,
    orderOf_tauE e, tauE_conj_muE e, FE_le_range e, range_le_normalizer e, ?_,
    range_inf_zpowers e, heq⟩
  · exact isCyclic_of_surjective (muE e).rangeRestrict (muE e).rangeRestrict_surjective
  · rw [normal_subgroupOf_iff (range_le_normalizer e)]
    intro h k hh hk
    exact (mem_normalizer_iff.1 (hnorm hk) h).1 hh

noncomputable def glEquiv (g : GL33) : (Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) (ZMod 3)))
    (Matrix.toLin' ((g⁻¹ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)))
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.toLin'_one])

theorem glEquiv_apply (g : GL33) (v : Fin 3 → ZMod 3) :
    glEquiv g v = (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v := Matrix.toLin'_apply _ _

theorem muE_conj (g : GL33) (c : K27ˣ) :
    muE ((glEquiv g⁻¹).trans e) c = g * muE e c * g⁻¹ := by
  apply gl_ext_e ((glEquiv g⁻¹).trans e)
  intro v
  rw [muE_apply]
  simp only [LinearEquiv.trans_apply, glEquiv_apply]
  rw [mulVec_mul, mulVec_mul, ← mulVec_mul, inv_mul_cancel, mulVec_one, muE_apply]

theorem FE_conj (g : GL33) :
    (FE e).map (MulAut.conj g).toMonoidHom = FE ((glEquiv g⁻¹).trans e) := by
  rw [FE, FE, Subgroup.map_map]
  congr 1
  ext c : 1
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact (muE_conj e g c).symm

noncomputable def eK : (Fin 3 → ZMod 3) ≃ₗ[ZMod 3] K27 :=
  LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_fin_fun, finrank_K27])

end CFSG.RankThree.PartTwo.Toolkit
