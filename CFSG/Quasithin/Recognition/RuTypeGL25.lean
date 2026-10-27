module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod


public section

namespace CFSG.Quasithin.RuType.GL25

abbrev W42 : Type := Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2)

instance : DecidableEq W42 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    (by
      constructor
      · rintro ⟨h1, h2⟩; exact RegularWreathProduct.ext h1 h2
      · rintro rfl; exact ⟨rfl, rfl⟩)

instance : Fintype W42 := Fintype.ofEquiv _ (RegularWreathProduct.equivProd _ _).symm

@[expose] def u4 (k : Multiplicative (ZMod 4)) : ZMod 5 := 2 ^ (Multiplicative.toAdd k).val

@[expose] def z2 (q : Multiplicative (ZMod 2)) : Fin 2 := Multiplicative.toAdd q

@[expose] def ofz2 (x : Fin 2) : Multiplicative (ZMod 2) := Multiplicative.ofAdd x

@[expose] def Ψ0 (a : W42) : Matrix (Fin 2) (Fin 2) (ZMod 5) :=
  Matrix.of fun x y => if x = z2 a.right + y then u4 (a.left (ofz2 x)) else 0

theorem Ψ0_mul : ∀ a b : W42, Ψ0 (a * b) = Ψ0 a * Ψ0 b := by decide +kernel

theorem Ψ0_one : Ψ0 1 = 1 := by decide +kernel

theorem Ψ0_inj : ∀ a b : W42, Ψ0 a = Ψ0 b → a = b := by decide +kernel

@[expose] def Ψm : W42 →* Matrix (Fin 2) (Fin 2) (ZMod 5) where
  toFun := Ψ0
  map_one' := Ψ0_one
  map_mul' := Ψ0_mul

@[expose] def Ψ : W42 →* GL (Fin 2) (ZMod 5) := Ψm.toHomUnits

theorem Ψ_injective : Function.Injective Ψ := fun a b h =>
  Ψ0_inj a b (congrArg Units.val h)

theorem card_W42 : Nat.card W42 = 32 := by
  rw [RegularWreathProduct.card]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem card_GL25 : Nat.card (GL (Fin 2) (ZMod 5)) = 480 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := Matrix.card_GL_field (𝔽 := ZMod 5) 2
  simp only [Fin.prod_univ_two, ZMod.card, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [h]
  norm_num

theorem nonempty_mulEquiv_W42 (K : Subgroup (GL (Fin 2) (ZMod 5))) (hK : Nat.card K = 32) :
    Nonempty (K ≃* W42) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : (Nat.card (GL (Fin 2) (ZMod 5))).factorization 2 = 5 := by
    rw [card_GL25, show (480 : ℕ) = 2 ^ 5 * 15 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 15 by norm_num)]
  have hΨc : Nat.card Ψ.range = 32 := by
    rw [← card_W42]
    exact Nat.card_congr (MonoidHom.ofInjective Ψ_injective).symm.toEquiv
  let SK : Sylow 2 (GL (Fin 2) (ZMod 5)) := Sylow.ofCard K (by rw [hK, hf]; norm_num)
  let SM : Sylow 2 (GL (Fin 2) (ZMod 5)) := Sylow.ofCard Ψ.range (by rw [hΨc, hf]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 2) (ZMod 5)) SM SK
  have hKe : K = Ψ.range.map (MulAut.conj g).toMonoidHom := by
    have h := congrArg (fun S : Sylow 2 (GL (Fin 2) (ZMod 5)) => S.toSubgroup) hg
    simp only [Sylow.coe_subgroup_smul] at h
    rw [Subgroup.pointwise_smul_def] at h
    exact h.symm
  refine ⟨(MulEquiv.subgroupCongr hKe).trans ?_⟩
  exact (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm.trans
    (MonoidHom.ofInjective Ψ_injective).symm

section Faithful

variable {V : Type*} [Group V] [Finite V]

@[expose] def coordHom (hcomm : ∀ u v : V, u * v = v * u) (h5 : ∀ v : V, v ^ 5 = 1)
    (v1 v2 : V) : Multiplicative (Fin 2 → ZMod 5) →* V where
  toFun w := v1 ^ (Multiplicative.toAdd w 0).val * v2 ^ (Multiplicative.toAdd w 1).val
  map_one' := by simp
  map_mul' w w' := by
    have hmod : ∀ (v : V) (a b : ZMod 5), v ^ (a + b).val = v ^ a.val * v ^ b.val := by
      intro v a b
      rw [ZMod.val_add, ← pow_add]
      conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) 5, pow_add, pow_mul, h5, one_pow, mul_one]
    simp only [toAdd_mul, Pi.add_apply, hmod]
    calc v1 ^ (Multiplicative.toAdd w 0).val * v1 ^ (Multiplicative.toAdd w' 0).val *
          (v2 ^ (Multiplicative.toAdd w 1).val * v2 ^ (Multiplicative.toAdd w' 1).val) =
        v1 ^ (Multiplicative.toAdd w 0).val *
          (v1 ^ (Multiplicative.toAdd w' 0).val * v2 ^ (Multiplicative.toAdd w 1).val) *
          v2 ^ (Multiplicative.toAdd w' 1).val := by group
      _ = v1 ^ (Multiplicative.toAdd w 0).val *
          (v2 ^ (Multiplicative.toAdd w 1).val * v1 ^ (Multiplicative.toAdd w' 0).val) *
          v2 ^ (Multiplicative.toAdd w' 1).val := by
            rw [hcomm (v1 ^ (Multiplicative.toAdd w' 0).val) (v2 ^ (Multiplicative.toAdd w 1).val)]
      _ = _ := by group

@[expose] def matOf (β : MulAut (Multiplicative (Fin 2 → ZMod 5))) :
    Matrix (Fin 2) (Fin 2) (ZMod 5) :=
  Matrix.of fun i j => Multiplicative.toAdd (β (Multiplicative.ofAdd (Pi.single j 1))) i

theorem matOf_apply (β : MulAut (Multiplicative (Fin 2 → ZMod 5))) (x : Fin 2 → ZMod 5) :
    Multiplicative.toAdd (β (Multiplicative.ofAdd x)) = (matOf β).mulVec x := by
  have hx : x = x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1 := by
    ext i; fin_cases i <;> simp
  have hsmul : ∀ (k : ZMod 5) (y : Fin 2 → ZMod 5),
      Multiplicative.toAdd (β (Multiplicative.ofAdd (k • y))) =
        k • Multiplicative.toAdd (β (Multiplicative.ofAdd y)) := by
    intro k y
    have e : k • y = k.val • y := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 5), ZMod.natCast_zmod_val]
    rw [e, ofAdd_nsmul, map_pow, toAdd_pow, ← Nat.cast_smul_eq_nsmul (ZMod 5),
      ZMod.natCast_zmod_val]
  conv_lhs => rw [hx, ofAdd_add, map_mul, toAdd_mul, hsmul, hsmul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, matOf, Matrix.of_apply]
  ring

theorem matOf_one : matOf 1 = 1 := by
  ext i j
  simp only [matOf, Matrix.of_apply, MulAut.one_apply, toAdd_ofAdd, Matrix.one_apply]
  rw [Pi.single_apply]

theorem matOf_mul (β γ : MulAut (Multiplicative (Fin 2 → ZMod 5))) :
    matOf (β * γ) = matOf β * matOf γ := by
  ext i j
  have h := matOf_apply β (Multiplicative.toAdd (γ (Multiplicative.ofAdd (Pi.single j 1))))
  rw [ofAdd_toAdd] at h
  have e : matOf (β * γ) i j =
      Multiplicative.toAdd (β (γ (Multiplicative.ofAdd (Pi.single j 1)))) i := rfl
  rw [e, h]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rfl

@[expose] def matHom : MulAut (Multiplicative (Fin 2 → ZMod 5)) →*
    Matrix (Fin 2) (Fin 2) (ZMod 5) where
  toFun := matOf
  map_one' := matOf_one
  map_mul' := matOf_mul

theorem matOf_injective : Function.Injective matOf := by
  intro β γ h
  apply MulEquiv.ext
  intro w
  apply Multiplicative.toAdd.injective
  have h1 := matOf_apply β (Multiplicative.toAdd w)
  have h2 := matOf_apply γ (Multiplicative.toAdd w)
  rw [ofAdd_toAdd] at h1 h2
  rw [h1, h2, h]

theorem nonempty_mulEquiv_W42_of_faithful (hcomm : ∀ u v : V, u * v = v * u)
    (hV : Nat.card V = 25) (h5 : ∀ v : V, v ^ 5 = 1) {R : Type*} [Group R]
    (act : R →* MulAut V) (hinj : Function.Injective act) (hR : Nat.card R = 32) :
    Nonempty (R ≃* W42) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hnt : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV]; norm_num)
  obtain ⟨v1, hv1⟩ := exists_ne (1 : V)
  have hv1o : orderOf v1 = 5 := orderOf_eq_prime (h5 v1) hv1
  have hlt : Subgroup.zpowers v1 ≠ ⊤ := by
    intro h
    have := Nat.card_congr (Subgroup.topEquiv (G := V)).toEquiv
    rw [← h, Nat.card_zpowers, hv1o, hV] at this
    norm_num at this
  obtain ⟨v2, hv2⟩ : ∃ v2 : V, v2 ∉ Subgroup.zpowers v1 := by
    by_contra hall
    push Not at hall
    exact hlt (eq_top_iff.mpr fun x _ => hall x)
  set e := coordHom hcomm h5 v1 v2
  have hpow : ∀ (v : V) (n : ℕ), v ^ (n % 5) = v ^ n := by
    intro v n
    conv_rhs => rw [← Nat.mod_add_div n 5, pow_add, pow_mul, h5, one_pow, mul_one]
  have he_inj : Function.Injective e := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hw' : v1 ^ (Multiplicative.toAdd w 0).val * v2 ^ (Multiplicative.toAdd w 1).val = 1 :=
      hw
    have h1 : (Multiplicative.toAdd w 1) = 0 := by
      by_contra hn
      apply hv2
      have hv2n : v2 ^ (Multiplicative.toAdd w 1).val ∈ Subgroup.zpowers v1 := by
        have : v2 ^ (Multiplicative.toAdd w 1).val = (v1 ^ (Multiplicative.toAdd w 0).val)⁻¹ :=
          eq_inv_of_mul_eq_one_right hw'
        rw [this]
        exact inv_mem (Subgroup.npow_mem_zpowers _ _)
      have hk : ((Multiplicative.toAdd w 1).val * ((Multiplicative.toAdd w 1)⁻¹).val) % 5 = 1 := by
        rw [← ZMod.val_mul, ZMod.mul_inv_of_unit _ (isUnit_iff_ne_zero.mpr hn)]
        rfl
      have := Subgroup.pow_mem _ hv2n ((Multiplicative.toAdd w 1)⁻¹).val
      rw [← pow_mul, ← hpow, hk, pow_one] at this
      exact this
    have h0 : (Multiplicative.toAdd w 0) = 0 := by
      rw [h1, ZMod.val_zero, pow_zero, mul_one] at hw'
      have hd := orderOf_dvd_of_pow_eq_one hw'
      rw [hv1o] at hd
      have hlt5 := ZMod.val_lt (Multiplicative.toAdd w 0)
      have : (Multiplicative.toAdd w 0).val = 0 := by
        rcases hd with ⟨c, hc⟩
        omega
      exact (ZMod.val_eq_zero _).mp this
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have he_bij : Function.Bijective e := by
    refine he_inj.bijective_of_nat_card_le ?_
    rw [hV]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  set eV := MulEquiv.ofBijective e he_bij
  let ρm : R →* Matrix (Fin 2) (Fin 2) (ZMod 5) :=
    matHom.comp ((MulAut.congr eV.symm).toMonoidHom.comp act)
  let ρ : R →* GL (Fin 2) (ZMod 5) := ρm.toHomUnits
  have hρ : Function.Injective ρ := by
    intro r r' h
    have h1 : matOf (MulAut.congr eV.symm (act r)) = matOf (MulAut.congr eV.symm (act r')) :=
      congrArg Units.val h
    have h2 := matOf_injective h1
    exact hinj ((MulAut.congr eV.symm).injective h2)
  have hcard : Nat.card ρ.range = 32 := by
    rw [← hR]
    exact Nat.card_congr (MonoidHom.ofInjective hρ).symm.toEquiv
  obtain ⟨φ⟩ := nonempty_mulEquiv_W42 ρ.range hcard
  exact ⟨(MonoidHom.ofInjective hρ).trans φ⟩

end Faithful

end CFSG.Quasithin.RuType.GL25
