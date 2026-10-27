module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMvMoves
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEvenLabels
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus

public section

namespace CFSG.StandardType

open Multiplicative SpCoord NbrOrth Polynomial

theorem ggTorusEvenSignedPermEltSC_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {kP : ℕ → Prop} (h : GGTorusEvenSignedPermEltSC p R' kP) :
    GGTorusEvenSignedPermEltSC p R kP := by
  intro E hE h3 hsc
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  have hmem : ∀ x : R, e x ∈ E.map e.toMonoidHom ↔ x ∈ E := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hsc' : ∀ g : R', (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
    intro g hg hgp
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [hmem]
    refine hsc y (fun x hx => e.injective ?_) ?_
    · rw [map_mul, map_mul]
      exact hg _ ((hmem x).mpr hx)
    · apply e.injective
      rw [map_pow, hgp, map_one]
  obtain ⟨k, τ, hτinj, hτE, hk, hdinv, hperm, hnorm⟩ :=
    h (E.map e.toMonoidHom) (TableB.isElemAbelian_map hE _) (hcard ▸ h3) hsc'
  have hconj : ∀ (w : R') (f f' : Fin k → Multiplicative (ZMod p)),
      w * τ f * w⁻¹ = τ f' → e.symm w * e.symm (τ f) * (e.symm w)⁻¹ = e.symm (τ f') := by
    intro w f f' h
    rw [← map_inv, ← map_mul, ← map_mul, h]
  refine ⟨k, e.symm.toMonoidHom.comp τ, e.symm.injective.comp hτinj, ?_, hk, fun i j hij => ?_,
    fun σ => ?_, fun g hg => ?_⟩
  · ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      have : τ f ∈ τ.range := ⟨f, rfl⟩
      rw [hτE] at this
      rw [← hmem]
      simpa using this
    · intro hx
      have : e x ∈ τ.range := hτE ▸ (hmem x).mpr hx
      obtain ⟨f, hf⟩ := this
      exact ⟨f, by simp [hf]⟩
  · obtain ⟨w, hw⟩ := hdinv i j hij
    exact ⟨e.symm w, fun f => hconj w f _ (hw f)⟩
  · obtain ⟨w, hw⟩ := hperm σ
    exact ⟨e.symm w, fun f => hconj w f _ (hw f)⟩
  · have hg' : ∀ x ∈ E.map e.toMonoidHom, e g * x * (e g)⁻¹ ∈ E.map e.toMonoidHom := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨g * y * g⁻¹, hg y hy, ?_⟩
      simp
    obtain ⟨π, ε, hε, hrel⟩ := hnorm (e g) hg'
    refine ⟨π, ε, hε, fun f f' hff' => hrel f f' ?_⟩
    apply e.symm.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact hff'

namespace OrthTorus

section Coord

variable (r p : ℕ)

@[expose] def piMul : (Fin r → Multiplicative (ZMod p)) ≃* Multiplicative (Fin r → ZMod p) where
  toFun f := ofAdd fun i => toAdd (f i)
  invFun t i := ofAdd (toAdd t i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {r p}

theorem piMul_apply (f : Fin r → Multiplicative (ZMod p)) :
    piMul r p f = ofAdd fun i => toAdd (f i) :=
  rfl

theorem piMul_dinv {i j : Fin r} (hij : i ≠ j) (f : Fin r → Multiplicative (ZMod p)) :
    piMul r p (dinv i j f) = ofAdd fun k =>
      ((CoordOm.pairTw (-1 : (ZMod p)ˣ) i j k : (ZMod p)ˣ) : ZMod p) * toAdd (f k) := by
  rw [piMul_apply]
  congr 1
  funext k
  rw [OrthNs.dinv_apply_eq]
  simp only [CoordOm.pairTw, hij, ↓reduceIte, Units.val_mul]
  by_cases hki : k = i
  · subst hki
    simp [hij, toAdd_inv]
  · by_cases hkj : k = j
    · subst hkj
      simp [hki, toAdd_inv]
    · simp [hki, hkj]

theorem piMul_sgnAut (i : Fin r) (f : Fin r → Multiplicative (ZMod p)) :
    piMul r p (sgnAut i f) = ofAdd fun k =>
      ((CoordOm.singleTw (-1 : (ZMod p)ˣ) i k : (ZMod p)ˣ) : ZMod p) * toAdd (f k) := by
  rw [piMul_apply]
  congr 1
  funext k
  rw [sgnAut_apply]
  simp only [CoordOm.singleTw]
  by_cases hki : k = i
  · subst hki
    simp [toAdd_inv]
  · simp [hki]

theorem piMul_permAut (σ : Equiv.Perm (Fin r)) (f : Fin r → Multiplicative (ZMod p)) :
    piMul r p (permAut σ f) = ofAdd fun k =>
      (((1 : Fin r → (ZMod p)ˣ) k : (ZMod p)ˣ) : ZMod p) * toAdd (f (σ⁻¹ k)) := by
  rw [piMul_apply, permAut_apply]
  congr 1
  funext k
  simp

end Coord

section Realized

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

theorem exists_conj_of_realizedIn {F : SevOm.Frame Q p A r} {H : Subgroup (V ≃ₗ[K] V)}
    {π : Equiv.Perm (Fin r)} {η : Fin r → (ZMod p)ˣ} (h : CoordOm.RealizedIn F H π η) :
    ∃ w ∈ H, ∀ f : Fin r → Multiplicative (ZMod p), w * F.ι (piMul r p f) * w⁻¹ =
      F.ι (ofAdd fun k => (η k : ZMod p) * toAdd (f (π k))) := by
  obtain ⟨w, hw, hws⟩ := h
  refine ⟨w⁻¹, H.inv_mem (Subgroup.mem_inf.mp hw).1, fun f => ?_⟩
  rw [inv_inv]
  exact hws fun i => toAdd (f i)

end Realized

section Blocks

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}

theorem finrank_sd (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hgd : g ∣ cyclotomic p K)
    (hpq : p ∣ Nat.card K + 1) : Module.finrank K (AdjoinRoot g) = 2 := by
  rw [(CoordSL.rootPB g).finrank]
  exact SpNS.rootPB_dim_eq_two hp hp2 hpK hgd hpq

theorem eq_one_or_neg_one_sd (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hgd : g ∣ cyclotomic p K) (hpq : p ∣ Nat.card K + 1) (hζ0 : AdjoinRoot.root g ≠ 0)
    (a : ZMod p) (θ : AdjoinRoot g →ₗ[K] AdjoinRoot g) (hθ : Function.Injective θ)
    (hθc : ∀ x, θ (CoordSpNs.sdC hζ0 x) = (CoordSpNs.sdC hζ0 ^ a.val) (θ x)) :
    a = 1 ∨ a = -1 :=
  SpNS.eq_one_or_eq_neg_one_of_intertwine hp hp2 hpK hgd hpq a θ hθ fun u => by
    rw [← CoordSpNs.sdC_apply hζ0, hθc, CoordSpNs.sdC_pow_apply]

theorem natDegree_eq_one (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hgd : g ∣ cyclotomic p K) : g.natDegree = 1 := by
  classical
  obtain ⟨ζ, hζo, -, -, -⟩ := TableBOrth.exists_zeta hp hp2 hpq
  have hprim : IsPrimitiveRoot (ζ : K) p := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hζo]
    exact IsPrimitiveRoot.orderOf ζ
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hprim] at hgd
  have hg : Irreducible g := Fact.out
  obtain ⟨μ, -, hμ⟩ := (Prime.dvd_finsetProd_iff hg.prime _).mp hgd
  have h1 := natDegree_le_of_dvd hμ (X_sub_C_ne_zero μ)
  rw [natDegree_X_sub_C] at h1
  have h2 := hg.natDegree_pos
  omega

omit [Finite K] in
theorem eq_of_aeval_eq_zero {L : Type} [Field L] [Algebra K L] (h1 : g.natDegree = 1) {x y : L}
    (hx : aeval x g = 0) (hy : aeval y g = 0) : x = y := by
  have hg := eq_X_add_C_of_natDegree_le_one h1.le
  have hc : g.coeff 1 ≠ 0 := by
    have := leadingCoeff_ne_zero.mpr (Fact.out : Irreducible g).ne_zero
    rwa [leadingCoeff, h1] at this
  rw [hg] at hx hy
  simp only [map_add, map_mul, aeval_C, aeval_X] at hx hy
  have h2 : algebraMap K L (g.coeff 1) * (x - y) = 0 := by
    rw [mul_sub]
    linear_combination hx - hy
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd ((map_eq_zero_iff _ (algebraMap K L).injective).mp h3) hc
  · exact sub_eq_zero.mp h3

omit [Finite K] in
theorem aeval_root_self : aeval (AdjoinRoot.root g) g = 0 := by
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem aeval_pred_ne_zero (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hpq : p ∣ Nat.card K - 1) (hgd : g ∣ cyclotomic p K) :
    aeval (AdjoinRoot.root g ^ (p - 1)) g ≠ 0 := by
  intro h
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  have h1 := eq_of_aeval_eq_zero (natDegree_eq_one hp hp2 hpq hgd) h aeval_root_self
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h2 := hζ.pow_inj (by omega : p - 1 < p) (by omega : 1 < p) (by rw [pow_one]; exact h1)
  omega

theorem finrank_pr (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hgd : g ∣ cyclotomic p K) : Module.finrank K (AdjoinRoot g × AdjoinRoot g) = 2 := by
  rw [Module.finrank_prod, (CoordSL.rootPB g).finrank, CoordSL.rootPB,
    AdjoinRoot.powerBasis_dim, natDegree_eq_one hp hp2 hpq hgd]

theorem natCast_pred_eq_neg_one (hp : p.Prime) : ((p - 1 : ℕ) : ZMod p) = -1 := by
  rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, zero_sub, Nat.cast_one]

theorem eq_one_or_neg_one_pr (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hpq : p ∣ Nat.card K - 1) (hgd : g ∣ cyclotomic p K) (hζ0 : AdjoinRoot.root g ≠ 0)
    (hζ0' : AdjoinRoot.root g ^ (p - 1) ≠ 0) (a : ZMod p)
    (θ : (AdjoinRoot g × AdjoinRoot g) →ₗ[K] (AdjoinRoot g × AdjoinRoot g))
    (hθ : Function.Injective θ)
    (hθc : ∀ x, θ (CoordSpNs.prC hζ0 hζ0' x) = (CoordSpNs.prC hζ0 hζ0' ^ a.val) (θ x)) :
    a = 1 ∨ a = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  set ζ := AdjoinRoot.root g with hζdef
  have h1 := natDegree_eq_one hp hp2 hpq hgd
  have hgx := eq_X_add_C_of_natDegree_le_one h1.le
  have hc : g.coeff 1 ≠ 0 := by
    have := leadingCoeff_ne_zero.mpr (Fact.out : Irreducible g).ne_zero
    rwa [leadingCoeff, h1] at this
  set lam : K := -(g.coeff 0 / g.coeff 1) with hlam
  have hlamK : g.eval lam = 0 := by
    rw [hgx]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    rw [hlam]
    field_simp
    ring
  have hlamE : algebraMap K (AdjoinRoot g) lam = ζ := by
    refine eq_of_aeval_eq_zero h1 ?_ aeval_root_self
    rw [aeval_algebraMap_apply_eq_algebraMap_eval, hlamK, map_zero]
  have hsmul : ∀ y : AdjoinRoot g, lam • y = ζ * y := fun y => by
    rw [Algebra.smul_def, hlamE]
  rcases hyz : θ (1, 0) with ⟨y, z⟩
  have hne : ((y, z) : AdjoinRoot g × AdjoinRoot g) ≠ 0 := by
    intro h0
    have h2 : θ (1, 0) = θ 0 := by rw [hyz, h0, map_zero]
    have h3 := congrArg Prod.fst (hθ h2)
    exact one_ne_zero h3
  have hc10 : CoordSpNs.prC hζ0 hζ0' ((1 : AdjoinRoot g), (0 : AdjoinRoot g)) =
      lam • ((1 : AdjoinRoot g), (0 : AdjoinRoot g)) := by
    rw [CoordSpNs.prC_apply, Prod.smul_mk, hsmul, hsmul, mul_zero, mul_zero]
  have key := hθc (1, 0)
  rw [hc10, map_smul, hyz, CoordSpNs.prC_pow_apply, Prod.smul_mk, hsmul, hsmul,
    Prod.mk.injEq] at key
  obtain ⟨k1, k2⟩ := key
  by_cases hy : y = 0
  · have hz : z ≠ 0 := fun hz => hne (by rw [hy, hz]; rfl)
    have k3 : ζ = (ζ ^ (p - 1)) ^ a.val := mul_right_cancel₀ hz k2
    right
    have k4 : ζ ^ (a.val + 1) = 1 := by
      calc ζ ^ (a.val + 1) = ζ ^ a.val * ζ := pow_succ ζ a.val
        _ = ζ ^ a.val * (ζ ^ (p - 1)) ^ a.val := by rw [← k3]
        _ = (ζ * ζ ^ (p - 1)) ^ a.val := by rw [mul_pow]
        _ = (ζ ^ p) ^ a.val := by rw [← pow_succ', Nat.sub_add_cancel hp.one_le]
        _ = 1 := by rw [hζ.pow_eq_one, one_pow]
    have k5 := (hζ.pow_eq_one_iff_dvd _).mp k4
    have k6 : ((a.val + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr k5
    push_cast at k6
    rw [ZMod.natCast_zmod_val] at k6
    linear_combination k6
  · have k3 : ζ = ζ ^ a.val := mul_right_cancel₀ hy k1
    left
    have k4 : ζ ^ (a.val + (p - 1)) = 1 := by
      calc ζ ^ (a.val + (p - 1)) = ζ ^ a.val * ζ ^ (p - 1) := pow_add _ _ _
        _ = ζ * ζ ^ (p - 1) := by rw [← k3]
        _ = ζ ^ p := by rw [← pow_succ', Nat.sub_add_cancel hp.one_le]
        _ = 1 := hζ.pow_eq_one
    have k5 := (hζ.pow_eq_one_iff_dvd _).mp k4
    have k6 : ((a.val + (p - 1) : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr k5
    rw [Nat.cast_add, natCast_pred_eq_neg_one hp, ZMod.natCast_zmod_val] at k6
    linear_combination k6

end Blocks

end OrthTorus

end CFSG.StandardType

end
