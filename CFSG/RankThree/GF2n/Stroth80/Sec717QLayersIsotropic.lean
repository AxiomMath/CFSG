module

public import CFSG.RankThree.GF2n.Stroth80.Sec717QLayersProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem exists_smul_of_commute_sl4 {K : Type} [Field K] (f : (Fin 4 → K) →+ (Fin 4 → K))
    (hf : ∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) (v : Fin 4 → K), f (A • v) = A • f v) :
    ∃ c : K, ∀ v, f v = c • v := by
  refine addCommutantScalar_statedSL (K := K) (m := 4) (by norm_num) f fun A hA v => ?_
  have hdet : (A : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    have hle : StatedSL 4 K ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker := by
      refine (Subgroup.closure_le _).mpr fun B hB => ?_
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      exact Units.ext hB
    have h := hle hA
    rw [MonoidHom.mem_ker] at h
    exact congrArg Units.val h
  exact hf ⟨A, hdet⟩ v


variable {K E X : Type} [Field K] [AddCommGroup E] [Module K E] [Group X]
  {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V Nb Rb : Subgroup X}
  {T : Submodule K E}

namespace Sec717LayerData

theorem isotropic_of_layerModel [Finite K] [CharP K 2] [FiniteDimensional K E]
    (hNoInv : SL4NoInvFormStatement) (hK : 4 ≤ Nat.card K)
    (D : Sec717LayerData B φ V Nb Rb T) {L : Subgroup X} (hLN : L ≤ Nb) (hVL : V ≤ L)
    (hLR : ∀ r ∈ Rb, ∀ l ∈ L, r * l * r⁻¹ ∈ L) (hcent : ∀ r ∈ Rb, ∀ a ∈ V, r * a = a * r)
    {a₀ : X} (ha₀ : a₀ ∈ V) (ha₀1 : a₀ ≠ 1)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w)
    (η : ↥Rb →* Matrix.SpecialLinearGroup (Fin 4) K) (hη : Function.Surjective η)
    (θ : ↥L →* Multiplicative (Fin 4 → K)) (hθ : Function.Surjective θ)
    (hθker : ∀ l, θ l = 1 ↔ (l : X) ∈ V)
    (hθeq : ∀ (r : ↥Rb) (l l' : ↥L), (l' : X) = (r : X) * l * (r : X)⁻¹ →
      Multiplicative.toAdd (θ l') = η r • Multiplicative.toAdd (θ l))
    (ψ : ↥T ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K))
    (hψ : ∀ (r : ↥Rb) (w w' : ↥T), (w' : E) = φ (r : X) w →
      ψ w' = PartOne.K159.Klein.rho (η r) (ψ w)) :
    ∀ l₁ ∈ L, ∀ l₂ ∈ L, ∀ x y : E, B (opm (φ l₁) x) (opm (φ l₂) y) = 0 := by
  classical
  set P := B.orthogonal T with hP
  have hTP : ∀ t ∈ T, ∀ p ∈ P, B t p = 0 := fun t ht p hp =>
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hp) t ht
  have hPT : ∀ p ∈ P, ∀ t ∈ T, B p t = 0 := fun p hp t ht => D.refl _ _ (hTP t ht p hp)
  have hlow : ∀ n ∈ Nb, IsLayerLowering T P (opm (φ n)) := D.Nb_low
  have hΔmul : ∀ n ∈ Nb, ∀ m ∈ Nb, ∀ w ∈ P, opm (φ (n * m)) w = opm (φ n) w + opm (φ m) w :=
    fun n hn m hm w hw => by
      rw [map_mul, opm_mul_apply_layer, (hlow n hn).bot _ ((hlow m hm).mid w hw), add_zero]
  have hΔinv : ∀ n ∈ Nb, ∀ w ∈ P, opm (φ n⁻¹) w = -opm (φ n) w := fun n hn w hw => by
    rw [map_inv, opm_inv_apply_of_lowering (hlow n hn), (hlow n hn).bot _ ((hlow n hn).mid w hw),
      add_zero]
  have hVP : ∀ a ∈ V, ∀ w ∈ P, opm (φ a) w = 0 := fun a ha w hw => (D.V_corner a ha).mid w hw
  have hΔeq : ∀ n ∈ Nb, ∀ m ∈ Nb, (∀ w ∈ P, opm (φ n) w = opm (φ m) w) → n⁻¹ * m ∈ V := by
    intro n hn m hm h
    refine D.mem_of_eqOn_zero (Nb.mul_mem (Nb.inv_mem hn) hm) fun w hw => ?_
    rw [hΔmul _ (Nb.inv_mem hn) _ hm w hw, hΔinv n hn w hw, h w hw, neg_add_cancel]
  have hΔV : ∀ n ∈ Nb, ∀ a ∈ V, ∀ w ∈ P, opm (φ (n * a)) w = opm (φ n) w := fun n hn a ha w hw => by
    rw [hΔmul n hn a (hVL ha |> hLN) w hw, hVP a ha w hw, add_zero]
  have hθΔ : ∀ x y : ↥L, θ x = θ y → ∀ w ∈ P, opm (φ (x : X)) w = opm (φ (y : X)) w := by
    intro x y h w hw
    have hV : (x : X)⁻¹ * y ∈ V := by
      have h1 : θ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
      exact (hθker _).mp h1
    rw [show (y : X) = x * ((x : X)⁻¹ * y) by group, hΔV _ (hLN x.2) _ hV w hw]
  have hΔθ : ∀ x y : ↥L, (∀ w ∈ P, opm (φ (x : X)) w = opm (φ (y : X)) w) → θ x = θ y := by
    intro x y h
    have hV := hΔeq _ (hLN x.2) _ (hLN y.2) h
    have h1 : θ (x⁻¹ * y) = 1 := (hθker _).mpr hV
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have hL1 : ∀ x y : ↥L, θ x = θ y → ∀ e, ∀ z ∈ P,
      B (opm (φ (x : X)) e) z = B (opm (φ (y : X)) e) z := by
    intro x y h e z hz
    have hV : (x : X)⁻¹ * y ∈ V := by
      have h1 : θ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
      exact (hθker _).mp h1
    have e1 : opm (φ (y : X)) e = opm (φ (x : X)) e + opm (φ ((x : X)⁻¹ * y)) e := by
      conv_lhs => rw [show (y : X) = x * ((x : X)⁻¹ * y) by group]
      rw [map_mul, opm_mul_apply_layer, (hlow _ (hLN x.2)).bot _ ((D.V_corner _ hV).top e),
        add_zero]
    rw [e1, map_add, LinearMap.add_apply, hTP _ ((D.V_corner _ hV).top e) z hz, add_zero]
  have hR1 : ∀ x y : ↥L, θ x = θ y → ∀ e, ∀ z ∈ P,
      B z (opm (φ (x : X)) e) = B z (opm (φ (y : X)) e) := by
    intro x y h e z hz
    have hV : (x : X)⁻¹ * y ∈ V := by
      have h1 : θ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
      exact (hθker _).mp h1
    have e1 : opm (φ (y : X)) e = opm (φ (x : X)) e + opm (φ ((x : X)⁻¹ * y)) e := by
      conv_lhs => rw [show (y : X) = x * ((x : X)⁻¹ * y) by group]
      rw [map_mul, opm_mul_apply_layer, (hlow _ (hLN x.2)).bot _ ((D.V_corner _ hV).top e),
        add_zero]
    rw [e1, map_add, hPT z hz _ ((D.V_corner _ hV).top e), add_zero]
  have hL2 : ∀ x y : ↥L, ∀ e, ∀ z ∈ P,
      B (opm (φ ((x * y : ↥L) : X)) e) z = B (opm (φ (x : X)) e) z + B (opm (φ (y : X)) e) z := by
    intro x y e z hz
    rw [Subgroup.coe_mul, map_mul, opm_mul_apply_layer, map_add, map_add, LinearMap.add_apply,
      LinearMap.add_apply,
      hTP _ ((hlow _ (hLN x.2)).mid _ ((hlow _ (hLN y.2)).top e)) z hz, add_zero]
  have hR2 : ∀ x y : ↥L, ∀ e, ∀ z ∈ P,
      B z (opm (φ ((x * y : ↥L) : X)) e) = B z (opm (φ (x : X)) e) + B z (opm (φ (y : X)) e) := by
    intro x y e z hz
    rw [Subgroup.coe_mul, map_mul, opm_mul_apply_layer, map_add, map_add,
      hPT z hz _ ((hlow _ (hLN x.2)).mid _ ((hlow _ (hLN y.2)).top e)), add_zero]
  have hL3 : ∀ (x y : ↥L) (c : K), (∀ w ∈ P, opm (φ (y : X)) w = c • opm (φ (x : X)) w) →
      ∀ e, ∀ z ∈ P, B (opm (φ (y : X)) e) z = c * B (opm (φ (x : X)) e) z := by
    intro x y c h e z hz
    have hc := D.isLayerCorner_of_eqOn (hLN x.2) (hLN y.2) h
    have e1 : opm (φ (y : X)) e = (opm (φ (y : X)) - c • opm (φ (x : X))) e +
        c • opm (φ (x : X)) e := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, sub_add_cancel]
    rw [e1, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hTP _ (hc.top e) z hz,
      zero_add, smul_eq_mul]
  have hR3 : ∀ (x y : ↥L) (c : K), (∀ w ∈ P, opm (φ (y : X)) w = c • opm (φ (x : X)) w) →
      ∀ e, ∀ z ∈ P, B z (opm (φ (y : X)) e) = c * B z (opm (φ (x : X)) e) := by
    intro x y c h e z hz
    have hc := D.isLayerCorner_of_eqOn (hLN x.2) (hLN y.2) h
    have e1 : opm (φ (y : X)) e = (opm (φ (y : X)) - c • opm (φ (x : X))) e +
        c • opm (φ (x : X)) e := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, sub_add_cancel]
    rw [e1, map_add, map_smul, hPT z hz _ (hc.top e), zero_add, smul_eq_mul]
  have hL4 : ∀ (x : ↥L) (e e' : E), e - e' ∈ P → ∀ z ∈ P,
      B (opm (φ (x : X)) e) z = B (opm (φ (x : X)) e') z := by
    intro x e e' he z hz
    rw [← sub_eq_zero, ← LinearMap.sub_apply, ← map_sub, ← map_sub]
    exact hTP _ ((hlow _ (hLN x.2)).mid _ he) z hz
  have hR4 : ∀ (x : ↥L) (e e' : E), e - e' ∈ P → ∀ z ∈ P,
      B z (opm (φ (x : X)) e) = B z (opm (φ (x : X)) e') := by
    intro x e e' he z hz
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact hPT z hz _ ((hlow _ (hLN x.2)).mid _ he)
  have hΔ' : ∀ (c : K) (l : ↥L), ∃ l' : ↥L, ∀ w ∈ P, opm (φ (l' : X)) w = c • opm (φ (l : X)) w :=
    fun c l => by
      obtain ⟨l', hl', h⟩ := hΔ l l.2 c
      exact ⟨⟨l', hl'⟩, h⟩
  choose st hst using hΔ'
  choose xs hxs using fun v : Fin 4 → K => hθ (Multiplicative.ofAdd v)
  have hxsθ : ∀ v, Multiplicative.toAdd (θ (xs v)) = v := fun v => by rw [hxs]; rfl
  have hstθ : ∀ (c : K) (x y : ↥L), θ x = θ y → θ (st c x) = θ (st c y) := fun c x y h =>
    hΔθ _ _ fun w hw => by rw [hst c x w hw, hst c y w hw, hθΔ x y h w hw]
  have hstmul : ∀ (c : K) (x y : ↥L), θ (st c (x * y)) = θ (st c x * st c y) := fun c x y =>
    hΔθ _ _ fun w hw => by
      rw [hst c _ w hw, Subgroup.coe_mul, hΔmul _ (hLN x.2) _ (hLN y.2) w hw, Subgroup.coe_mul,
        hΔmul _ (hLN (st c x).2) _ (hLN (st c y).2) w hw, hst c x w hw, hst c y w hw, smul_add]
  set μ : K → (Fin 4 → K) → (Fin 4 → K) := fun c v => Multiplicative.toAdd (θ (st c (xs v)))
    with hμdef
  have hμadd : ∀ c v v₂, μ c (v + v₂) = μ c v + μ c v₂ := by
    intro c v v₂
    have h1 : θ (xs (v + v₂)) = θ (xs v * xs v₂) := by
      rw [hxs, map_mul, hxs, hxs]
      rfl
    simp only [hμdef]
    rw [hstθ c _ _ h1, hstmul, map_mul]
    rfl
  have hμeq : ∀ c (A : Matrix.SpecialLinearGroup (Fin 4) K) v, μ c (A • v) = A • μ c v := by
    intro c A v
    obtain ⟨r, rfl⟩ := hη A
    set x' : ↥L := ⟨(r : X) * (xs v : X) * (r : X)⁻¹, hLR _ r.2 _ (xs v).2⟩
    set y' : ↥L := ⟨(r : X) * (st c (xs v) : X) * (r : X)⁻¹, hLR _ r.2 _ (st c (xs v)).2⟩
    have h1 : θ (xs (η r • v)) = θ x' := by
      apply Multiplicative.toAdd.injective
      rw [hxsθ, hθeq r (xs v) x' rfl, hxsθ]
    have h2 : θ (st c x') = θ y' := hΔθ _ _ fun w hw => by
      have hw' : φ (r : X)⁻¹ w ∈ P := D.Rb_P _ (Rb.inv_mem r.2) w hw
      rw [hst c x' w hw]
      show c • opm (φ ((r : X) * (xs v : X) * (r : X)⁻¹)) w =
        opm (φ ((r : X) * (st c (xs v) : X) * (r : X)⁻¹)) w
      rw [opm_conj, opm_conj, hst c (xs v) _ hw', map_smul]
    simp only [hμdef]
    rw [hstθ c _ _ h1, h2, hθeq r (st c (xs v)) y' rfl]
  have hμ : ∀ c : K, ∃ k : K, ∀ v, μ c v = k • v := fun c =>
    exists_smul_of_commute_sl4 (AddMonoidHom.mk' (μ c) (hμadd c)) (hμeq c)
  choose τ hτ using hμ
  set e₀ : Fin 4 → K := Pi.single 0 1 with he₀
  have he₀0 : e₀ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [he₀] at this
  have hcoef : ∀ k k' : K, k • e₀ = k' • e₀ → k = k' := fun k k' h =>
    smul_left_injective K he₀0 h
  have hτadd : ∀ c c', τ (c + c') = τ c + τ c' := by
    intro c c'
    refine hcoef _ _ ?_
    rw [← hτ, add_smul, ← hτ, ← hτ]
    simp only [hμdef]
    have h : θ (st (c + c') (xs e₀)) = θ (st c (xs e₀) * st c' (xs e₀)) := hΔθ _ _ fun w hw => by
      rw [hst _ _ w hw, Subgroup.coe_mul, hΔmul _ (hLN (st c _).2) _ (hLN (st c' _).2) w hw,
        hst c _ w hw, hst c' _ w hw, add_smul]
    rw [h, map_mul]
    rfl
  have hτmul : ∀ c c', τ (c * c') = τ c * τ c' := by
    intro c c'
    refine hcoef _ _ ?_
    have h1 : θ (xs (μ c' e₀)) = θ (st c' (xs e₀)) := by
      rw [hxs]
      rfl
    have h : θ (st (c * c') (xs e₀)) = θ (st c (xs (μ c' e₀))) := hΔθ _ _ fun w hw => by
      rw [hst _ _ w hw, hst c _ w hw, hθΔ _ _ h1 w hw, hst c' _ w hw, smul_smul]
    have e1 : μ (c * c') e₀ = μ c (μ c' e₀) := by
      simp only [hμdef]
      rw [h]
    rw [← hτ, e1, hτ c, hτ c', smul_smul]
  have hτone : τ 1 = 1 := by
    refine hcoef _ _ ?_
    rw [← hτ, one_smul]
    simp only [hμdef]
    rw [hΔθ (st 1 (xs e₀)) (xs e₀) fun w hw => by rw [hst 1 _ w hw, one_smul], hxsθ]
  have hτzero : τ 0 = 0 := by
    have h := hτadd 0 0
    rw [add_zero] at h
    exact (add_eq_left.mp h.symm)
  let τh : K →+* K :=
    { toFun := τ, map_one' := hτone, map_mul' := hτmul, map_zero' := hτzero, map_add' := hτadd }
  let τe : K ≃+* K := RingEquiv.ofBijective τh
    ⟨τh.injective, Finite.injective_iff_surjective.mp τh.injective⟩
  have hτe : ∀ c, τe c = τ c := fun c => rfl
  set τv : (Fin 4 → K) → (Fin 4 → K) := fun v i => τe (v i) with hτv
  have hτvadd : ∀ v w, τv (v + w) = τv v + τv w := fun v w => by ext i; simp [hτv]
  have hτvsmul : ∀ (c : K) v, τv (c • v) = τ c • τv v := fun c v => by
    ext i
    simp only [hτv, hτe, Pi.smul_apply, smul_eq_mul]
    exact hτmul c (v i)
  have hτvmap : ∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) v,
      τv (Matrix.SpecialLinearGroup.map (τe.symm : K →+* K) A • v) = A • τv v := by
    intro A v
    ext i
    simp only [hτv, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec,
      dotProduct, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, map_sum, map_mul, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  have hτvinv : ∀ u, τv (fun i => τe.symm (u i)) = u := fun u => by
    ext i
    simp [hτv]
  set D₀ := opm (φ a₀) with hD₀
  have hmemT : ∀ x, D₀ x ∈ T := fun x => by
    rw [← D.range_V a₀ ha₀ ha₀1]
    exact LinearMap.mem_range_self _ x
  obtain ⟨sT, hsT⟩ : ∃ sT : ↥T →ₗ[K] E, ∀ t : ↥T, D₀ (sT t) = t := by
    obtain ⟨s', hs'⟩ := LinearMap.exists_rightInverse_of_surjective (D₀.codRestrict T hmemT)
      (LinearMap.range_eq_top.mpr fun t => by
        have ht : (t : E) ∈ LinearMap.range D₀ := by rw [D.range_V a₀ ha₀ ha₀1]; exact t.2
        obtain ⟨x, hx⟩ := ht
        exact ⟨x, Subtype.ext hx⟩)
    exact ⟨s', fun t => congrArg Subtype.val (LinearMap.congr_fun hs' t)⟩
  have hkerP : ∀ e e' : E, D₀ e = D₀ e' → e - e' ∈ P := fun e e' h => by
    rw [hP, ← D.ker_V a₀ ha₀ ha₀1, LinearMap.mem_ker, map_sub, h, sub_self]
  have hcomm₀ : ∀ r ∈ Rb, ∀ y, D₀ (φ r y) = φ r (D₀ y) := by
    intro r hr y
    have h := DFunLike.congr_fun (congrArg φ (hcent r hr a₀ ha₀)) y
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
    rw [hD₀, opm_apply, opm_apply, map_sub, h]
  have hxw : ∀ e : E, e - sT (ψ.symm (ψ ⟨D₀ e, hmemT e⟩)) ∈ P := fun e => by
    refine hkerP _ _ ?_
    rw [LinearEquiv.symm_apply_apply, hsT]
  have hρw : ∀ (r : ↥Rb) (w : Fin 3 ⊕ Fin 3 → K),
      φ (r : X) (sT (ψ.symm w)) - sT (ψ.symm (PartOne.K159.Klein.rho (η r) w)) ∈ P := by
    intro r w
    refine hkerP _ _ ?_
    have hrT : φ (r : X) (ψ.symm w) ∈ T := D.Rb_T _ r.2 _ (ψ.symm w).2
    have e1 : ψ.symm (PartOne.K159.Klein.rho (η r) w) = ⟨φ (r : X) (ψ.symm w), hrT⟩ := by
      rw [LinearEquiv.symm_apply_eq, hψ r (ψ.symm w) ⟨_, hrT⟩ rfl, LinearEquiv.apply_symm_apply]
    rw [hcomm₀ _ r.2, hsT, e1, hsT]
  set β₀ : (Fin 4 → K) → (Fin 3 ⊕ Fin 3 → K) → (Fin 4 → K) → (Fin 3 ⊕ Fin 3 → K) → K :=
    fun v w v' w' => B (opm (φ (xs v : X)) (sT (ψ.symm w))) (opm (φ (xs v' : X)) (sT (ψ.symm w')))
    with hβ₀
  have hzP : ∀ (x : ↥L) e, opm (φ (x : X)) e ∈ P := fun x e => (hlow _ (hLN x.2)).top e
  have hθxs : ∀ v v₂, θ (xs (v + v₂)) = θ (xs v * xs v₂) := fun v v₂ => by
    rw [hxs, map_mul, hxs, hxs]
    rfl
  have hθst : ∀ (c : K) u, θ (xs (τ c • u)) = θ (st c (xs u)) := fun c u => by
    apply Multiplicative.toAdd.injective
    rw [hxsθ]
    exact (hτ c u).symm
  have hβadd1 : ∀ v v₂ w v' w', β₀ (v + v₂) w v' w' = β₀ v w v' w' + β₀ v₂ w v' w' := by
    intro v v₂ w v' w'
    simp only [hβ₀]
    rw [hL1 _ _ (hθxs v v₂) _ _ (hzP _ _), hL2 _ _ _ _ (hzP _ _)]
  have hβsmul1 : ∀ (c : K) u w v' w', β₀ (τ c • u) w v' w' = c * β₀ u w v' w' := by
    intro c u w v' w'
    simp only [hβ₀]
    rw [hL1 _ _ (hθst c u) _ _ (hzP _ _), hL3 _ _ c (hst c (xs u)) _ _ (hzP _ _)]
  have hβadd3 : ∀ v w v' v₂ w', β₀ v w (v' + v₂) w' = β₀ v w v' w' + β₀ v w v₂ w' := by
    intro v w v' v₂ w'
    simp only [hβ₀]
    rw [hR1 _ _ (hθxs v' v₂) _ _ (hzP _ _), hR2 _ _ _ _ (hzP _ _)]
  have hβsmul3 : ∀ (c : K) v w u w', β₀ v w (τ c • u) w' = c * β₀ v w u w' := by
    intro c v w u w'
    simp only [hβ₀]
    rw [hR1 _ _ (hθst c u) _ _ (hzP _ _), hR3 _ _ c (hst c (xs u)) _ _ (hzP _ _)]
  have hβadd2 : ∀ v w w₂ v' w', β₀ v (w + w₂) v' w' = β₀ v w v' w' + β₀ v w₂ v' w' := by
    intro v w w₂ v' w'
    simp only [hβ₀, map_add, LinearMap.add_apply]
  have hβsmul2 : ∀ (c : K) v w v' w', β₀ v (c • w) v' w' = c * β₀ v w v' w' := by
    intro c v w v' w'
    simp only [hβ₀, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hβadd4 : ∀ v w v' w' w₂, β₀ v w v' (w' + w₂) = β₀ v w v' w' + β₀ v w v' w₂ := by
    intro v w v' w' w₂
    simp only [hβ₀, map_add]
  have hβsmul4 : ∀ (c : K) v w v' w', β₀ v w v' (c • w') = c * β₀ v w v' w' := by
    intro c v w v' w'
    simp only [hβ₀, map_smul, smul_eq_mul]
  have hβinv : ∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) v w v' w',
      β₀ (A • v) (PartOne.K159.Klein.rho A w) (A • v') (PartOne.K159.Klein.rho A w') =
        β₀ v w v' w' := by
    intro A v w v' w'
    obtain ⟨r, rfl⟩ := hη A
    set x₁ : ↥L := ⟨(r : X) * (xs v : X) * (r : X)⁻¹, hLR _ r.2 _ (xs v).2⟩
    set x₂ : ↥L := ⟨(r : X) * (xs v' : X) * (r : X)⁻¹, hLR _ r.2 _ (xs v').2⟩
    have h1 : θ (xs (η r • v)) = θ x₁ := by
      apply Multiplicative.toAdd.injective
      rw [hxsθ, hθeq r (xs v) x₁ rfl, hxsθ]
    have h2 : θ (xs (η r • v')) = θ x₂ := by
      apply Multiplicative.toAdd.injective
      rw [hxsθ, hθeq r (xs v') x₂ rfl, hxsθ]
    simp only [hβ₀]
    rw [hL1 _ _ h1 _ _ (hzP _ _), hL4 x₁ _ _ (by
        rw [← neg_mem_iff, neg_sub]
        exact hρw r w) _ (hzP _ _),
      hR1 _ _ h2 _ _ (hzP _ _), hR4 x₂ _ _ (by
        rw [← neg_mem_iff, neg_sub]
        exact hρw r w') _ (hzP _ _)]
    show B (opm (φ ((r : X) * (xs v : X) * (r : X)⁻¹)) (φ (r : X) (sT (ψ.symm w))))
        (opm (φ ((r : X) * (xs v' : X) * (r : X)⁻¹)) (φ (r : X) (sT (ψ.symm w')))) = _
    rw [opm_conj, opm_conj, phi_inv_apply_phi, phi_inv_apply_phi, D.isom]
  set f : (Fin 4 → K) → (Fin 3 ⊕ Fin 3 → K) → (Fin 4 → K) → (Fin 3 ⊕ Fin 3 → K) → K :=
    fun v w v' w' => β₀ (τv v) w (τv v') w' with hf
  let β' : (Fin 4 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 4 → K) →ₗ[K]
      (Fin 3 ⊕ Fin 3 → K) →ₗ[K] K :=
    LinearMap.mk₂ K (fun v w => LinearMap.mk₂ K (fun v' w' => f v w v' w')
        (fun v' v₂ w' => by simp only [hf, hτvadd, hβadd3])
        (fun c v' w' => by simp only [hf, hτvsmul, hβsmul3, smul_eq_mul])
        (fun v' w' w₂ => by simp only [hf, hβadd4])
        (fun c v' w' => by simp only [hf, hβsmul4, smul_eq_mul]))
      (fun v v₂ w => LinearMap.ext₂ fun v' w' => by
        simp only [LinearMap.mk₂_apply, LinearMap.add_apply, hf, hτvadd, hβadd1])
      (fun c v w => LinearMap.ext₂ fun v' w' => by
        simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, hf, hτvsmul, hβsmul1, smul_eq_mul])
      (fun v w w₂ => LinearMap.ext₂ fun v' w' => by
        simp only [LinearMap.mk₂_apply, LinearMap.add_apply, hf, hβadd2])
      (fun c v w => LinearMap.ext₂ fun v' w' => by
        simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, hf, hβsmul2, smul_eq_mul])
  have hβ'0 : β' = 0 := hNoInv K hK τe.symm β' fun A v v' w w' => by
    simp only [β', LinearMap.mk₂_apply, hf, hτvmap]
    exact hβinv A _ _ _ _
  intro l₁ hl₁ l₂ hl₂ x y
  set u₁ := Multiplicative.toAdd (θ ⟨l₁, hl₁⟩)
  set u₂ := Multiplicative.toAdd (θ ⟨l₂, hl₂⟩)
  have h1 : θ ⟨l₁, hl₁⟩ = θ (xs u₁) := by rw [hxs]; rfl
  have h2 : θ ⟨l₂, hl₂⟩ = θ (xs u₂) := by rw [hxs]; rfl
  have key : B (opm (φ l₁) x) (opm (φ l₂) y) =
      β₀ u₁ (ψ ⟨D₀ x, hmemT x⟩) u₂ (ψ ⟨D₀ y, hmemT y⟩) := by
    simp only [hβ₀]
    rw [show opm (φ l₁) x = opm (φ ((⟨l₁, hl₁⟩ : ↥L) : X)) x from rfl,
      show opm (φ l₂) y = opm (φ ((⟨l₂, hl₂⟩ : ↥L) : X)) y from rfl,
      hL1 _ _ h1 _ _ (hzP _ _), hL4 _ _ _ (hxw x) _ (hzP _ _), hR1 _ _ h2 _ _ (hzP _ _),
      hR4 _ _ _ (hxw y) _ (hzP _ _)]
  rw [key, ← hτvinv u₁, ← hτvinv u₂]
  have h0 := LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun
    hβ'0 (fun i => τe.symm (u₁ i))) (ψ ⟨D₀ x, hmemT x⟩)) (fun i => τe.symm (u₂ i)))
    (ψ ⟨D₀ y, hmemT y⟩)
  simpa [β', hf] using h0

end Sec717LayerData

end CFSG.RankThree.GF2n.Stroth80
