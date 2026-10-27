module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSubfieldCentralizer
public import CFSG.RankThree.Classical.SemilinearFixedBasis
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear

public section

namespace CFSG.RankThree.LinearTwo

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield mem_fixedSubfield)
open CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer
  (fieldExtension_mul_coordinatePGLAction)
open CFSG.ABGLocalTools (glNorm glNorm_succ iterate_semilinear_apply exists_prod_pow_eq
  iterate_smul_of_semilinear)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)

universe u

@[expose] def fixingSubgroup {K : Type u} [Field K] (σ : K ≃+* K) : Subgroup (K ≃+* K) where
  carrier := {τ | ∀ x, σ x = x → τ x = x}
  mul_mem' {τ ρ} hτ hρ x hx := by
    change τ (ρ x) = x
    rw [hρ x hx, hτ x hx]
  one_mem' _ _ := rfl
  inv_mem' {τ} hτ x hx := by
    change τ.symm x = x
    rw [RingEquiv.symm_apply_eq, hτ x hx]

theorem mem_zpowers_of_forall_fixed {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 1 ≤ n) {K : Type u}
    [Field K] (hK : Nat.card K = ℓ ^ n) (σ τ : K ≃+* K) (hτ : ∀ x, σ x = x → τ x = x) :
    τ ∈ Subgroup.zpowers σ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  obtain ⟨-, -, -, -, hcardAut, hA⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hn hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  obtain ⟨hAdvd, SA, hSA, hSAcard⟩ := hA (Subgroup.zpowers σ)
  obtain ⟨hBdvd, SB, hSB, hSBcard⟩ := hA (fixingSubgroup σ)
  have hle : (SA : Set K) ⊆ SB := by
    intro x hx
    rw [hSA] at hx
    rw [hSB]
    intro ρ hρ
    exact hρ x (hx σ (Subgroup.mem_zpowers σ))
  have hcardle : Nat.card SA ≤ Nat.card SB :=
    Nat.card_le_card_of_injective (fun x : SA => (⟨x.1, hle x.2⟩ : SB))
      fun x y h => Subtype.ext (Subtype.mk.inj h)
  rw [hSAcard, hSBcard] at hcardle
  have hdiv : n / Nat.card (Subgroup.zpowers σ) ≤ n / Nat.card (fixingSubgroup σ) :=
    (Nat.pow_le_pow_iff_right hℓ.one_lt).mp hcardle
  have hApos : 0 < Nat.card (Subgroup.zpowers σ) := Nat.card_pos
  have hBpos : 0 < Nat.card (fixingSubgroup σ) := Nat.card_pos
  have hAB : Subgroup.zpowers σ ≤ fixingSubgroup σ :=
    Subgroup.zpowers_le.mpr fun x hx => hx
  have hcard : Nat.card (fixingSubgroup σ) ≤ Nat.card (Subgroup.zpowers σ) := by
    obtain ⟨a, ha⟩ := hAdvd
    obtain ⟨b, hb⟩ := hBdvd
    have hna : n / Nat.card (Subgroup.zpowers σ) = a := by
      rw [ha, Nat.mul_div_cancel_left _ hApos]
    have hnb : n / Nat.card (fixingSubgroup σ) = b := by
      rw [hb, Nat.mul_div_cancel_left _ hBpos]
    rw [hna, hnb] at hdiv
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card (Subgroup.zpowers σ) * a < Nat.card (fixingSubgroup σ) * b := by
      have ha0 : 0 < a := by
        rcases Nat.eq_zero_or_pos a with h | h
        · rw [h, mul_zero] at ha
          omega
        · exact h
      calc Nat.card (Subgroup.zpowers σ) * a < Nat.card (fixingSubgroup σ) * a :=
            Nat.mul_lt_mul_of_pos_right hlt ha0
        _ ≤ Nat.card (fixingSubgroup σ) * b := Nat.mul_le_mul_left _ hdiv
    omega
  have heq : Subgroup.zpowers σ = fixingSubgroup σ := Subgroup.eq_of_le_of_card_ge hAB hcard
  rw [heq]
  exact hτ

theorem card_fixedSubfield {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 1 ≤ n) {K : Type u} [Field K]
    (hK : Nat.card K = ℓ ^ n) (σ : K ≃+* K) :
    orderOf σ ∣ n ∧ Nat.card (fixedSubfield K σ) = ℓ ^ (n / orderOf σ) := by
  obtain ⟨-, -, -, -, hcardAut, hA⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hn hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  obtain ⟨hdvd, S, hS, hScard⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at hdvd hScard
  refine ⟨hdvd, ?_⟩
  rw [← hScard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [mem_fixedSubfield, ← SetLike.mem_coe, hS]
  refine ⟨fun hx τ hτ => ?_, fun hx => hx σ (Subgroup.mem_zpowers σ)⟩
  have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) x :=
    Subgroup.zpowers_le.mpr hx
  exact hle hτ

section Hilbert

variable {K : Type u} [Field K]

@[expose] def twistedSemilinear (σ : K ≃+* K) (A : GL (Fin 2) K) (d : K) (v : Fin 2 → K) :
    Fin 2 → K :=
  d⁻¹ • ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (v i))

theorem twistedSemilinear_add (σ : K ≃+* K) (A : GL (Fin 2) K) (d : K) (v w : Fin 2 → K) :
    twistedSemilinear σ A d (v + w) = twistedSemilinear σ A d v + twistedSemilinear σ A d w := by
  simp only [twistedSemilinear, Pi.add_apply, map_add]
  rw [← smul_add, ← Matrix.mulVec_add]
  rfl

theorem twistedSemilinear_smul (σ : K ≃+* K) (A : GL (Fin 2) K) (d : K) (a : K)
    (v : Fin 2 → K) : twistedSemilinear σ A d (a • v) = σ a • twistedSemilinear σ A d v := by
  simp only [twistedSemilinear, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => σ a * σ (v i)) = σ a • fun i => σ (v i) from rfl, Matrix.mulVec_smul,
    smul_comm]

theorem exists_mul_map_eq_smul [Finite K] (σ : K ≃+* K) (A : GL (Fin 2) K) {c : K}
    (hc : ((glNorm σ A (orderOf σ) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.scalar (Fin 2) c) :
    ∃ (H : GL (Fin 2) K) (d : Kˣ), ∀ i j,
      ((A * GeneralLinearGroup.map σ.toRingHom H : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
        (d : K) * (H : Matrix (Fin 2) (Fin 2) K) i j := by
  classical
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun τ : K ≃+* K => (τ : K → K)) (fun _ _ h => RingEquiv.ext (congrFun h))
  set n := orderOf σ with hn
  have hpos : 0 < n := (isOfFinOrder_of_finite σ).orderOf_pos
  set φ : (Fin 2 → K) → (Fin 2 → K) :=
    fun w => (A : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun i => σ (w i)) with hφ
  have hφsmul : ∀ (a : K) (v : Fin 2 → K), φ (a • v) = σ a • φ v := by
    intro a v
    simp only [φ, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← Matrix.mulVec_smul]
    rfl
  have hφn : ∀ v, φ^[n] v = c • v := by
    intro v
    rw [hφ, iterate_semilinear_apply, hc, pow_orderOf_eq_one]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]
  set e₀ : Fin 2 → K := Pi.single 0 1 with he₀def
  have he₀ : φ e₀ ≠ 0 := by
    intro h
    have hσe : (fun i => σ (e₀ i)) = e₀ := by
      funext i
      fin_cases i <;> simp [e₀]
    simp only [φ, hσe] at h
    have h2 := congrArg (fun w => ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) h
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h2
    have h3 := congrFun h2 0
    simp [e₀] at h3
  have hσc : σ c = c := by
    have h1 : φ (φ^[n] e₀) = φ^[n] (φ e₀) :=
      (Function.iterate_succ_apply' φ n e₀).symm.trans (Function.iterate_succ_apply φ n e₀)
    rw [hφn, hφn, hφsmul] at h1
    exact smul_left_injective K he₀ h1
  have hc0 : c ≠ 0 := by
    intro h0
    have hdet := congrArg Matrix.det hc
    rw [h0, map_zero, Matrix.det_zero] at hdet
    exact (glNorm σ A n).det_ne_zero hdet
  obtain ⟨d, hd⟩ := exists_prod_pow_eq σ hσc
  rw [← hn] at hd
  have hd0 : d ≠ 0 := by
    intro h0
    apply hc0
    rw [← hd, h0, Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr hpos) (by simp)]
  set ψ := twistedSemilinear σ A d with hψ
  have hψφ : ∀ w, ψ w = d⁻¹ • φ w := fun w => rfl
  have hψiter : ∀ k v, ψ^[k] v = (∏ i ∈ Finset.range k, (σ ^ i) d)⁻¹ • φ^[k] v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply, hψφ,
        iterate_smul_of_semilinear σ hφsmul, smul_smul, Finset.prod_range_succ, map_inv₀,
        mul_inv]
  have hψn : ∀ v, ψ^[n] v = v := by
    intro v
    rw [hψiter, hd, hφn, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hψinj : Function.Injective ψ := by
    intro v w h
    have h' : ψ^[n] v = ψ^[n] w := by
      obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [hm, Function.iterate_succ_apply, Function.iterate_succ_apply, h]
    rwa [hψn, hψn] at h'
  have hψsurj : Function.Surjective ψ := by
    intro w
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨ψ^[m] w, ?_⟩
    have h := hψn w
    rw [hm, Function.iterate_succ_apply'] at h
    exact h
  let ψA : (Fin 2 → K) →+ (Fin 2 → K) :=
    AddMonoidHom.mk' ψ (twistedSemilinear_add σ A d)
  let a : (Fin 2 → K) ≃+ (Fin 2 → K) := AddEquiv.ofBijective ψA ⟨hψinj, hψsurj⟩
  have ha : ∀ (c : K) (v : Fin 2 → K), a (c • v) = σ c • a v :=
    twistedSemilinear_smul σ A d
  have hah : ∀ v, (⇑a)^[n] v = v := hψn
  have hspan := CFSG.RankThree.Classical.span_fixed_eq_top σ hpos hn.symm a ha hah
  obtain ⟨t, htsub, htspan, htli⟩ :=
    exists_linearIndependent K (CFSG.RankThree.Classical.fixedSet a)
  rw [hspan] at htspan
  let bt : Module.Basis t K (Fin 2 → K) := Module.Basis.mk htli (by rw [Subtype.range_coe, htspan])
  have : Finite t := Module.Finite.finite_basis bt
  have : Fintype t := Fintype.ofFinite t
  have hcard_t : Fintype.card t = 2 := by
    rw [← Module.finrank_eq_card_basis bt, Module.finrank_fin_fun]
  let b : Module.Basis (Fin 2) K (Fin 2 → K) := bt.reindex (Fintype.equivFinOfCardEq hcard_t)
  have hbfix : ∀ j, ψ (b j) = b j := fun j => by
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    exact htsub (Subtype.mem _)
  let L : LinearMap.GeneralLinearGroup K (Fin 2 → K) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun.symm
  let H : GL (Fin 2) K := Matrix.GeneralLinearGroup.toLin.symm L
  have hHcol (i j : Fin 2) : (H : Matrix (Fin 2) (Fin 2) K) i j = b j i := by
    let ej : Fin 2 → K := Pi.single j 1
    have hfun : Matrix.mulVec (H : Matrix (Fin 2) (Fin 2) K) ej = b j := by
      calc
        Matrix.mulVec (H : Matrix (Fin 2) (Fin 2) K) ej =
            (Matrix.GeneralLinearGroup.toLin H : (Fin 2 → K) → Fin 2 → K) ej := rfl
        _ = (L : (Fin 2 → K) → Fin 2 → K) ej := by
          rw [(Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := K)).apply_symm_apply]
        _ = b j := by
          simp [L, ej, LinearMap.GeneralLinearGroup.ofLinearEquiv]
    rw [Matrix.mulVec_single_one] at hfun
    exact congrFun hfun i
  refine ⟨H, Units.mk0 d hd0, fun i j => ?_⟩
  have hfix := congrFun (hbfix j) i
  simp only [ψ, twistedSemilinear, Pi.smul_apply, smul_eq_mul] at hfix
  have hcol : ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ fun k => σ (b j k)) i = d * b j i := by
    rw [← hfix, mul_inv_cancel_left₀ hd0]
  rw [Units.val_mk0, hHcol, ← hcol]
  simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    GeneralLinearGroup.map_apply, hHcol]
  rfl

end Hilbert

section Powers

variable {K : Type u} [Field K]

theorem pow_left_mk (σ : K ≃+* K) (A : GL (Fin 2) K) (n : ℕ) :
    ((SemidirectProduct.inl (ProjGenLinGroup.mk A) * SemidirectProduct.inr σ :
      PGammaL2 K) ^ n).left = ProjGenLinGroup.mk (glNorm σ A n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, SemidirectProduct.mul_left, ih, glNorm_succ, map_mul]
    congr 1
    have hright : ((SemidirectProduct.inl (ProjGenLinGroup.mk A) *
        SemidirectProduct.inr σ : PGammaL2 K) ^ n).right = σ ^ n := by
      rw [← SemidirectProduct.rightHom_eq_right, map_pow, map_mul,
        SemidirectProduct.rightHom_inl, SemidirectProduct.rightHom_inr, one_mul]
    rw [hright, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply, SemidirectProduct.left_inr,
      mul_one, pgl2FieldAut_apply]
    exact pgl2RingEquiv_mk (σ ^ n) A

end Powers

theorem linear_two_prime_semilinear_field_descent {ℓ p f : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime)
    (hf : 1 ≤ f) (K : Type u) [Field K] (hK : Nat.card K = ℓ ^ f) {a : Equiv.Perm (Omega K)}
    (haE : a ∈ coordinateE K) (haD : a ∉ coordinateD K) (hap : orderOf a = p) :
    p ∣ f ∧ ∃ σ : K ≃+* K, orderOf σ = p ∧
      (∃ h ∈ coordinateD K, a = h * fieldExtension K σ * h⁻¹) ∧
      Nat.card (fixedSubfield K σ) = ℓ ^ (f / p) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  rw [← coordinateSemilinearAction_range_eq_E] at haE
  obtain ⟨x, rfl⟩ := haE
  obtain ⟨A, hA⟩ := ProjGenLinGroup.mk_surjective x.left
  set σ := x.right with hσdef
  have hx : x = SemidirectProduct.inl (ProjGenLinGroup.mk A) * SemidirectProduct.inr σ := by
    rw [hA, hσdef, SemidirectProduct.inl_left_mul_inr_right]
  have hxa : coordinateSemilinearAction K x =
      coordinatePGLAction K (ProjGenLinGroup.mk A) * fieldExtension K σ := by
    rw [hx, map_mul, coordinateSemilinearAction_inl, coordinateSemilinearAction_inr]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply haD
    rw [hxa, h1, ← coordinateSemilinearAction_inr, map_one, map_one, mul_one,
      ← coordinatePGLAction_range_eq_D]
    exact ⟨_, rfl⟩
  have hxp : x ^ p = 1 := by
    apply coordinateSemilinearAction_injective K
    rw [map_pow, ← hap, pow_orderOf_eq_one, map_one]
  have hσp : σ ^ p = 1 := by
    have h := congrArg SemidirectProduct.rightHom hxp
    rwa [map_pow, map_one, SemidirectProduct.rightHom_eq_right] at h
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨hdvd, hcardk⟩ := card_fixedSubfield hℓ hf hK σ
  rw [hσord] at hdvd hcardk
  have hnorm : ProjGenLinGroup.mk (glNorm σ A p) = 1 := by
    rw [← pow_left_mk, ← hx, hxp]
    rfl
  obtain ⟨c, hc⟩ := (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar).mp
    (ProjGenLinGroup.mk_eq_one.mp hnorm)
  rw [← hσord] at hc
  obtain ⟨H, d, hHd⟩ := exists_mul_map_eq_smul σ A hc.symm
  have hAH : ProjGenLinGroup.mk A =
      ProjGenLinGroup.mk H * (ProjGenLinGroup.mk (GeneralLinearGroup.map σ.toRingHom H))⁻¹ := by
    have hmat : A * GeneralLinearGroup.map σ.toRingHom H =
        H * GeneralLinearGroup.scalar (Fin 2) d := by
      apply GeneralLinearGroup.ext
      intro i j
      rw [hHd i j, GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.mul_diagonal, mul_comm]
    have h := congrArg ProjGenLinGroup.mk hmat
    rw [map_mul, map_mul, ProjGenLinGroup.mk_scalar, mul_one] at h
    rw [← h, mul_inv_cancel_right]
  have hconj : fieldExtension K σ * coordinatePGLAction K (ProjGenLinGroup.mk H) =
      coordinatePGLAction K (ProjGenLinGroup.mk (GeneralLinearGroup.map σ.toRingHom H)) *
        fieldExtension K σ := by
    rw [fieldExtension_mul_coordinatePGLAction, pgl2FieldAut_apply]
    exact congrArg (fun g => coordinatePGLAction K g * fieldExtension K σ)
      (pgl2RingEquiv_mk σ H)
  refine ⟨hdvd, σ, hσord, ⟨coordinatePGLAction K (ProjGenLinGroup.mk H), ?_, ?_⟩, hcardk⟩
  · rw [← coordinatePGLAction_range_eq_D]
    exact ⟨_, rfl⟩
  · rw [hxa, hAH, map_mul, map_inv]
    have h2 : (coordinatePGLAction K (ProjGenLinGroup.mk
        (GeneralLinearGroup.map σ.toRingHom H)))⁻¹ * fieldExtension K σ =
        fieldExtension K σ * (coordinatePGLAction K (ProjGenLinGroup.mk H))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hconj, mul_inv_cancel_right]
    rw [mul_assoc, h2, ← mul_assoc]

end CFSG.RankThree.LinearTwo
