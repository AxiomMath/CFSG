module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly

public section

namespace CFSG.RankThree.PartOne.Q1327T.R8

open Module

theorem card_dvd_of_free_perm {X : Type*} [Finite X] (σ : Equiv.Perm X) (h : ℕ) (hh : 0 < h)
    (h1 : σ ^ h = 1) (hfree : ∀ (x : X) (k : ℕ), 0 < k → k < h → (σ ^ k) x ≠ x) :
    h ∣ Nat.card X := by
  classical
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · simp
  set G : Subgroup (Equiv.Perm X) := Subgroup.zpowers σ with hGdef
  have hfin : IsOfFinOrder σ := isOfFinOrder_iff_pow_eq_one.2 ⟨h, hh, h1⟩
  have hpos : 0 < orderOf σ := hfin.orderOf_pos
  have hord : orderOf σ = h := by
    apply le_antisymm (Nat.le_of_dvd hh (orderOf_dvd_of_pow_eq_one h1))
    by_contra hlt
    push Not at hlt
    exact hfree x₀ (orderOf σ) hpos hlt (by rw [pow_orderOf_eq_one]; rfl)
  have hfreeG : ∀ x : X, MulAction.stabilizer G x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
    have hgx : (σ ^ m) x = x := by
      have := MulAction.mem_stabilizer_iff.1 hg
      rw [hm]
      exact this
    have hmod : σ ^ (m % (orderOf σ : ℤ)) = σ ^ m := zpow_mod_orderOf σ m
    have hnn : 0 ≤ m % (orderOf σ : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hpos.ne')
    have hlt : m % (orderOf σ : ℤ) < orderOf σ := Int.emod_lt_of_pos _ (by exact_mod_cast hpos)
    obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le hnn
    have hxr : (σ ^ r) x = x := by
      have h2 : σ ^ r = σ ^ m := by rw [← zpow_natCast, ← hr]; exact hmod
      rw [h2]
      exact hgx
    have hr0 : r = 0 := by
      by_contra hr0
      refine hfree x r (Nat.pos_of_ne_zero hr0) ?_ hxr
      rw [← hord]
      omega
    apply Subtype.ext
    rw [← hm, ← hmod, hr, hr0]
    simp
  have e := MulAction.selfEquivOrbitsQuotientProd hfreeG
  have hcard : Nat.card X = Nat.card (MulAction.orbitRel.Quotient G X) * Nat.card G := by
    rw [Nat.card_congr e, Nat.card_prod]
  have hG : Nat.card G = h := by rw [hGdef, Nat.card_zpowers, hord]
  rw [hcard, hG]
  exact Dvd.intro_left _ rfl

@[expose, reducible] def commGroupOfIs {E : Type*} [Group E] [IsMulCommutative E] : CommGroup E :=
  { ‹Group E› with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }

theorem exists_order_three_fixedFree {E : Type*} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) [hE : IsElementaryAbelian p E] (hcard : Nat.card E = p ^ 2)
    (W : Subgroup (MulAut E)) (φ : W ≃* Equiv.Perm (Fin 3)) :
    ∃ β ∈ W, orderOf β = 3 ∧ ∀ x : E, β x = x → x = 1 := by
  let _ : CommGroup E := commGroupOfIs
  have hpow : ∀ x : E, x ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p
  let _ : Module (ZMod p) (Additive E) :=
    AddCommGroup.zmodModule (n := p) (fun x => toMul_eq_one.mp (hpow x))
  have hfin : Module.Finite (ZMod p) (Additive E) := Module.Finite.of_finite
  have h2 : Module.finrank (ZMod p) (Additive E) = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive E)
    have h1 : Nat.card (Additive E) = p ^ 2 := hcard
    rw [h1, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  let lin : MulAut E →* Module.End (ZMod p) (Additive E) :=
    { toFun := fun β => AddMonoidHom.toZModLinearMap p (MulEquiv.toAdditive β).toAddMonoidHom
      map_one' := by ext x; rfl
      map_mul' := fun a b => by ext x; rfl }
  have hlin : ∀ (β : MulAut E) (x : E), lin β (Additive.ofMul x) = Additive.ofMul (β x) :=
    fun β x => rfl
  let detH : MulAut E →* ZMod p := LinearMap.det.comp lin
  let s₁ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let s₂ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  let c : Equiv.Perm (Fin 3) := s₁ * s₂ * s₁⁻¹ * s₂⁻¹
  have hc3 : c ^ 3 = 1 := by decide
  have hc1 : c ≠ 1 := by decide
  have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  set u₁ : W := φ.symm s₁ with hu₁
  set u₂ : W := φ.symm s₂ with hu₂
  set w : W := φ.symm c with hw
  have hwc : w = u₁ * u₂ * u₁⁻¹ * u₂⁻¹ := by simp [hw, hu₁, hu₂, c, map_mul, map_inv]
  have hdet : detH (w : MulAut E) = 1 := by
    have hinv : ∀ a : MulAut E, detH a⁻¹ * detH a = 1 := fun a => by
      rw [← map_mul, inv_mul_cancel, map_one]
    have hinv' : ∀ a : MulAut E, detH a * detH a⁻¹ = 1 := fun a => by
      rw [← map_mul, mul_inv_cancel, map_one]
    rw [hwc]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul]
    calc detH ↑u₁ * detH ↑u₂ * detH (↑u₁)⁻¹ * detH (↑u₂)⁻¹
        = (detH ↑u₁ * detH (↑u₁)⁻¹) * (detH ↑u₂ * detH (↑u₂)⁻¹) := by ring
      _ = 1 := by rw [hinv', hinv', one_mul]
  have hord : orderOf (w : MulAut E) = 3 := by
    rw [Subgroup.orderOf_coe, hw, MulEquiv.orderOf_eq, hcord]
  refine ⟨(w : MulAut E), w.2, hord, fun x hx => ?_⟩
  by_contra hx1
  set β : MulAut E := (w : MulAut E) with hβ
  set f : Module.End (ZMod p) (Additive E) := lin β with hf
  have hv0 : (Additive.ofMul x : Additive E) ≠ 0 := fun h => hx1 (ofMul_eq_zero.mp h)
  have hfv : f (Additive.ofMul x) = Additive.ofMul x := by rw [hf, hlin, hx]
  have hev : f.HasEigenvalue 1 :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (by rw [one_smul]; exact hfv), hv0⟩
  have hroot := (Module.End.hasEigenvalue_iff_isRoot_charpoly f 1).1 hev
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive E) h2
  set M := LinearMap.toMatrix b b f with hM
  have hMdet : M.det = 1 := by
    rw [hM, LinearMap.det_toMatrix]
    exact hdet
  have hchar : f.charpoly = M.charpoly := (LinearMap.charpoly_toMatrix f b).symm
  rw [hchar, Matrix.charpoly_fin_two] at hroot
  have htr : M.trace = 2 := by
    have h' : (1 : ZMod p) - M.trace + M.det = 0 := by
      simpa [Polynomial.IsRoot] using hroot
    rw [hMdet] at h'
    linear_combination -h'
  have hchar2 : f.charpoly = (Polynomial.X - 1) ^ 2 := by
    rw [hchar, Matrix.charpoly_fin_two, htr, hMdet]
    simp only [map_one]
    rw [show (Polynomial.C (2 : ZMod p)) = 2 from rfl]
    ring
  have hCH := LinearMap.aeval_self_charpoly f
  rw [hchar2] at hCH
  simp only [map_pow, map_sub, Polynomial.aeval_X, map_one] at hCH
  have hf3 : f ^ 3 = 1 := by
    have : β ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one β
    rw [hf, ← map_pow, this, map_one]
  have hpoly : (3 : Polynomial (ZMod p)) * (Polynomial.X - 1) =
      (Polynomial.X ^ 3 - 1) - (Polynomial.X + 2) * (Polynomial.X - 1) ^ 2 := by ring
  have h3 : (3 : Module.End (ZMod p) (Additive E)) * (f - 1) = 0 := by
    have := congrArg (Polynomial.aeval f) hpoly
    simp only [map_mul, map_sub, map_pow, map_add, Polynomial.aeval_X, map_one, map_ofNat] at this
    rw [hf3, hCH] at this
    simpa using this
  have h30 : (3 : ZMod p) ≠ 0 := by
    intro h0
    have := (ZMod.natCast_eq_zero_iff 3 p).1 (by exact_mod_cast h0)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hf1 : ∀ y : Additive E, f y = y := by
    intro y
    have h4 := LinearMap.congr_fun h3 y
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply, Module.End.ofNat_apply] at h4
    have h5 : ((3 : ℕ) : ZMod p) • (f y - y) = 0 := by
      rw [Nat.cast_smul_eq_nsmul]
      exact h4
    have h6 := (smul_eq_zero.1 h5).resolve_left (by exact_mod_cast h30)
    exact sub_eq_zero.1 h6
  have hβ1 : β = 1 := by
    ext x'
    have := hf1 (Additive.ofMul x')
    rw [hf, hlin] at this
    exact Additive.ofMul.injective this
  rw [hβ1, orderOf_one] at hord
  omega

section Chars

variable {E μ : Type*} [Group E] [CommGroup μ]

@[expose] def chPow (p : ℕ) (c : ZMod p) (χ : E →* μ) : E →* μ := χ ^ c.val

theorem chPow_apply (p : ℕ) (c : ZMod p) (χ : E →* μ) (e : E) : chPow p c χ e = χ e ^ c.val := by
  simp [chPow]

theorem chPow_mul {p : ℕ} [Fact p.Prime] (hμ : ∀ z : μ, z ^ p = 1) (a b : ZMod p) (χ : E →* μ) :
    chPow p (a * b) χ = chPow p a (chPow p b χ) := by
  ext e
  simp only [chPow_apply]
  rw [ZMod.val_mul, ← pow_eq_pow_mod _ (hμ _), ← pow_mul, mul_comm]

theorem chPow_one {p : ℕ} [Fact p.Prime] (χ : E →* μ) : chPow p 1 χ = χ := by
  ext e
  simp [chPow_apply, ZMod.val_one]

theorem eq_one_of_chPow_eq_self {p : ℕ} [Fact p.Prime] (hμ : ∀ z : μ, z ^ p = 1) {χ : E →* μ}
    (hχ : χ ≠ 1) {c : ZMod p} (h : chPow p c χ = χ) : c = 1 := by
  obtain ⟨e, he⟩ : ∃ e, χ e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hχ (MonoidHom.ext hcon)
  have hz : orderOf (χ e) = p := orderOf_eq_prime (hμ _) he
  have h1 : χ e ^ c.val = χ e ^ 1 := by
    rw [pow_one]
    simpa [chPow_apply] using DFunLike.congr_fun h e
  have h2 : c.val ≡ 1 [MOD p] := by
    have := pow_eq_pow_iff_modEq.1 h1
    rwa [hz] at this
  have h3 : ((c.val : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
  rwa [ZMod.natCast_zmod_val, Nat.cast_one] at h3

theorem exists_perm_of_stable {p : ℕ} [Fact p.Prime] (hμ : ∀ z : μ, z ^ p = 1)
    (X : Finset (E →* μ)) (c : (ZMod p)ˣ) (hc : ∀ χ ∈ X, chPow p (c : ZMod p) χ ∈ X) :
    ∃ σ : Equiv.Perm X, ∀ (k : ℕ) (χ : X), ((σ ^ k) χ).1 = chPow p ((c : ZMod p) ^ k) χ.1 := by
  classical
  have hinj : Function.Injective (chPow p (c : ZMod p) : (E →* μ) → (E →* μ)) := by
    intro χ ψ h
    have h1 := congrArg (chPow p ((c⁻¹ : (ZMod p)ˣ) : ZMod p)) h
    rwa [← chPow_mul hμ, ← chPow_mul hμ, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      chPow_one, chPow_one] at h1
  let f : X → X := fun χ => ⟨chPow p (c : ZMod p) χ.1, hc χ.1 χ.2⟩
  have hfinj : Function.Injective f := fun a b h => Subtype.ext (hinj (congrArg Subtype.val h))
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj), ?_⟩
  intro k
  induction k with
  | zero => intro χ; simp [chPow_one]
  | succ k ih =>
    intro χ
    rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, chPow_mul hμ]
    rfl

theorem exists_free_perm_of_stable {p : ℕ} [Fact p.Prime] (hμ : ∀ z : μ, z ^ p = 1)
    (X : Finset (E →* μ)) (hX1 : ∀ χ ∈ X, χ ≠ 1) (c : (ZMod p)ˣ)
    (hc : ∀ χ ∈ X, chPow p (c : ZMod p) χ ∈ X) :
    ∃ σ : Equiv.Perm X, (∀ (k : ℕ) (χ : X), ((σ ^ k) χ).1 = chPow p ((c : ZMod p) ^ k) χ.1) ∧
      σ ^ orderOf c = 1 ∧ ∀ (χ : X) (k : ℕ), 0 < k → k < orderOf c → (σ ^ k) χ ≠ χ := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_stable hμ X c hc
  refine ⟨σ, hσ, ?_, ?_⟩
  · refine Equiv.ext fun χ => Subtype.ext ?_
    rw [hσ]
    have : ((c : ZMod p)) ^ orderOf c = 1 := by
      rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    rw [this, chPow_one]
    rfl
  · intro χ k hk hk' hfix
    have h1 : chPow p ((c : ZMod p) ^ k) χ.1 = χ.1 := by
      rw [← hσ]
      exact congrArg Subtype.val hfix
    have h2 := eq_one_of_chPow_eq_self hμ (hX1 χ.1 χ.2) h1
    have h3 : c ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h2)
    exact absurd (Nat.le_of_dvd hk (orderOf_dvd_of_pow_eq_one h3)) (by omega)

theorem orderOf_dvd_card_of_stable {p : ℕ} [Fact p.Prime] (hμ : ∀ z : μ, z ^ p = 1)
    (X : Finset (E →* μ)) (hX1 : ∀ χ ∈ X, χ ≠ 1) (c : (ZMod p)ˣ)
    (hc : ∀ χ ∈ X, chPow p (c : ZMod p) χ ∈ X) : orderOf c ∣ X.card := by
  obtain ⟨σ, -, hσ1, hfree⟩ := exists_free_perm_of_stable hμ X hX1 c hc
  have := card_dvd_of_free_perm σ (orderOf c) (orderOf_pos c) hσ1 hfree
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this

theorem three_dvd_card_of_fixedFree [Finite E] (hcomm : ∀ a b : E, a * b = b * a) (β : MulAut E)
    (hβ : orderOf β = 3) (hfpf : ∀ x : E, β x = x → x = 1) (X : Finset (E →* μ))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (hβX : ∀ χ ∈ X, χ.comp β.toMonoidHom ∈ X) : 3 ∣ X.card := by
  classical
  have hβ3 : β ^ 3 = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
  have hinj : Function.Injective (fun χ : E →* μ => χ.comp β.toMonoidHom) := by
    intro χ ψ h
    ext e
    have := DFunLike.congr_fun h (β.symm e)
    simpa using this
  let f : X → X := fun χ => ⟨χ.1.comp β.toMonoidHom, hβX χ.1 χ.2⟩
  have hfinj : Function.Injective f := fun a b h => Subtype.ext (hinj (congrArg Subtype.val h))
  let σ : Equiv.Perm X := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj)
  have hσk : ∀ (k : ℕ) (χ : X), ((σ ^ k) χ).1 = χ.1.comp (β ^ k).toMonoidHom := by
    intro k
    induction k with
    | zero => intro χ; ext e; simp
    | succ k ih =>
      intro χ
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ']
      ext e
      rfl
  have key : ∀ γ : MulAut E, (∀ x : E, γ x = x → x = 1) → ∀ χ : E →* μ,
      χ.comp γ.toMonoidHom = χ → χ = 1 := by
    intro γ hγ χ hχ
    let _ : CommGroup E := { ‹Group E› with mul_comm := hcomm }
    let g : E →* E := γ.toMonoidHom * (MonoidHom.id E)⁻¹
    have hg : ∀ e, g e = γ e * e⁻¹ := fun e => by simp [g]
    have hginj : Function.Injective g := by
      rw [injective_iff_map_eq_one]
      intro e he
      rw [hg] at he
      exact hγ e (mul_inv_eq_one.1 he)
    have hgsurj : Function.Surjective g := Finite.injective_iff_surjective.1 hginj
    ext x
    obtain ⟨e, rfl⟩ := hgsurj x
    have h1 := DFunLike.congr_fun hχ e
    simp only [MonoidHom.comp_apply] at h1
    rw [hg]
    simp only [map_mul, map_inv, MonoidHom.one_apply]
    rw [show χ (γ e) = χ e from h1]
    simp
  have hβ2 : ∀ x : E, (β ^ 2) x = x → x = 1 := by
    intro x hx
    apply hfpf
    have h1 : β ((β ^ 2) x) = β x := by rw [hx]
    have h2 : β ((β ^ 2) x) = (β ^ 3) x := by
      rw [pow_succ' β 2]
      rfl
    rw [h2, hβ3] at h1
    exact h1.symm
  have hσ3 : σ ^ 3 = 1 := by
    refine Equiv.ext fun χ => Subtype.ext ?_
    rw [hσk, hβ3]
    ext e
    rfl
  have hfree : ∀ (χ : X) (k : ℕ), 0 < k → k < 3 → (σ ^ k) χ ≠ χ := by
    intro χ k hk hk3 hfix
    have h1 : χ.1.comp (β ^ k).toMonoidHom = χ.1 := by
      rw [← hσk]
      exact congrArg Subtype.val hfix
    interval_cases k
    · exact hX1 χ.1 χ.2 (key β hfpf χ.1 (by simpa using h1))
    · exact hX1 χ.1 χ.2 (key (β ^ 2) hβ2 χ.1 h1)
  have := card_dvd_of_free_perm σ 3 (by norm_num) hσ3 hfree
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this

end Chars

end CFSG.RankThree.PartOne.Q1327T.R8
