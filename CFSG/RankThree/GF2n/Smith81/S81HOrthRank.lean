module

public import CFSG.LinearAlgebra.SchurElemAbelianTwo
public import CFSG.HardMathSupport.Foote.ModuleExclusions.OrthCW
public import CFSG.RankThree.Classical.SemilinearFixedBasis
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthRank

open Module

variable {k : Type} [Field k] [Finite k] [CharP k 2]

theorem two_dvd_card_zero {U : Type} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (hU : 3 ≤ finrank k U) (Q : QuadraticForm k U) : 2 ∣ Nat.card {u : U // Q u = 0} := by
  classical
  have := Fintype.ofFinite k
  let b := Module.finBasis k U
  let B : LinearMap.BilinForm k U := Q.toBilin b
  have hB : ∀ u, B u u = Q u := fun u => by
    rw [← LinearMap.BilinMap.toQuadraticMap_apply, QuadraticMap.toQuadraticMap_toBilin]
  have hdeg : (HardMathSupport.Foote.ModuleExclusions.quadPoly B (fun i => b i)).totalDegree <
      Fintype.card (Fin (finrank k U)) := by
    have := HardMathSupport.Foote.ModuleExclusions.totalDegree_quadPoly_le B (fun i => b i)
    simp only [Fintype.card_fin]
    omega
  have hdvd := char_dvd_card_solutions 2 hdeg
  let e : {x : Fin (finrank k U) → k // MvPolynomial.eval x
      (HardMathSupport.Foote.ModuleExclusions.quadPoly B (fun i => b i)) = 0} ≃
      {u : U // Q u = 0} :=
    b.equivFun.symm.toEquiv.subtypeEquiv fun x => by
      rw [HardMathSupport.Foote.ModuleExclusions.eval_quadPoly, hB]
      simp [Basis.equivFun_symm_apply]
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  convert hdvd

theorem exists_fixed_singular {U : Type} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (hU : 3 ≤ finrank k U) (Q : QuadraticForm k U) {G : Type*} [Group G] (hG : IsPGroup 2 G)
    (ρ : Representation k G U) (hρ : ∀ g u, Q (ρ g u) = Q u) :
    ∃ u : U, u ≠ 0 ∧ Q u = 0 ∧ ∀ g, ρ g u = u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite U := Module.finite_of_finite k
  letI : MulAction G {u : U // Q u = 0} :=
    { smul := fun g u => ⟨ρ g u.1, (hρ g u.1).trans u.2⟩
      one_smul := fun u => Subtype.ext (by show ρ 1 u.1 = u.1; simp)
      mul_smul := fun g h u => Subtype.ext (by show ρ (g * h) u.1 = ρ g (ρ h u.1); simp) }
  have h0 : (⟨0, QuadraticMap.map_zero Q⟩ : {u : U // Q u = 0}) ∈
      MulAction.fixedPoints G {u : U // Q u = 0} := fun g => Subtype.ext (map_zero (ρ g))
  obtain ⟨u, hu, hne⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    {u : U // Q u = 0} (two_dvd_card_zero hU Q) h0
  exact ⟨u.1, fun h => hne (Subtype.ext h.symm), u.2, fun g => congrArg Subtype.val (hu g)⟩


section Pair

open QuadraticMap (polar polar_comm polar_smul_left polar_smul_right polar_sub_left
  polar_sub_right polar_add_left polar_add_right polar_self)

variable {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] {Q : QuadraticForm k V}
  {G : Type*} [Group G] {ρ : Representation k G V}

private theorem polar_iso (hiso : ∀ g v, Q (ρ g v) = Q v) (g : G) (x y : V) :
    polar Q (ρ g x) (ρ g y) = polar Q x y := by
  simp only [polar, ← map_add, hiso]

private theorem polar_self_eq_zero (x : V) : polar Q x x = 0 := by
  rw [polar_self, two_smul, CharTwo.add_self_eq_zero]

private theorem exists_polar_eq_one (hQ : Q.polarBilin.Nondegenerate) {x : V} (hx : x ≠ 0) :
    ∃ y, polar Q x y = 1 := by
  by_contra h
  push Not at h
  refine hx (hQ.1 x fun y => ?_)
  show polar Q x y = 0
  by_contra hy
  refine h ((polar Q x y)⁻¹ • y) ?_
  rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy]

private theorem exists_pair (hQ : Q.polarBilin.Nondegenerate) (hdim : 5 ≤ finrank k V)
    (hG : IsPGroup 2 G) (hiso : ∀ g v, Q (ρ g v) = Q v) :
    ∃ v w c₀ c₁ : V, Q v = 0 ∧ Q w = 0 ∧ polar Q v w = 0 ∧ polar Q v c₀ = 1 ∧
      polar Q w c₀ = 0 ∧ polar Q v c₁ = 0 ∧ polar Q w c₁ = 1 ∧ (∀ g, ρ g v = v) ∧
      ∀ g, ∃ a : k, ρ g w = w + a • v := by
  classical
  have hsymm : ∀ x y, polar Q x y = polar Q y x := fun x y => polar_comm _ x y
  obtain ⟨v, hv0, hQv, hρv⟩ := exists_fixed_singular (by omega) Q hG ρ hiso
  obtain ⟨c₀, hc₀⟩ := exists_polar_eq_one hQ hv0
  have hc₀v : polar Q c₀ v = 1 := by rw [hsymm]; exact hc₀
  have hpv : ∀ g x, polar Q (ρ g x) v = polar Q x v := fun g x => by
    calc polar Q (ρ g x) v = polar Q (ρ g x) (ρ g v) := by rw [hρv]
      _ = polar Q x v := polar_iso hiso g x v
  let Φ : V →ₗ[k] k × k := (Q.polarBilin.flip v).prod (Q.polarBilin c₀)
  let U := LinearMap.ker Φ
  have hmemU : ∀ x, x ∈ U ↔ polar Q x v = 0 ∧ polar Q c₀ x = 0 := fun x => by
    simp [U, Φ, Prod.ext_iff]
  have hUdim : 3 ≤ finrank k U := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    have h2 : finrank k (LinearMap.range Φ) ≤ 2 := by
      have := Submodule.finrank_le (LinearMap.range Φ)
      simpa using this
    show 3 ≤ finrank k (LinearMap.ker Φ)
    omega
  let T : G → (V →ₗ[k] V) := fun g => ρ g - (Q.polarBilin c₀ ∘ₗ ρ g).smulRight v
  have hTapp : ∀ g x, T g x = ρ g x - polar Q c₀ (ρ g x) • v := fun g x => by
    simp [T]
  have hT : ∀ g, ∀ x ∈ U, T g x ∈ U := by
    intro g x hx
    rw [hmemU] at hx ⊢
    rw [hTapp]
    refine ⟨?_, ?_⟩
    · rw [polar_sub_left, polar_smul_left, polar_self_eq_zero, smul_zero, sub_zero, hpv]
      exact hx.1
    · rw [polar_sub_right, polar_smul_right, hc₀v, smul_eq_mul, mul_one, sub_self]
  let ρU : Representation k G U :=
    { toFun := fun g => (T g).restrict (hT g)
      map_one' := by
        refine LinearMap.ext fun x => Subtype.ext ?_
        rw [LinearMap.coe_restrict_apply, hTapp, map_one, Module.End.one_apply,
          ((hmemU x).1 x.2).2, zero_smul, sub_zero]
        rfl
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => Subtype.ext ?_
        rw [Module.End.mul_apply, LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply,
          LinearMap.coe_restrict_apply, hTapp, hTapp, hTapp, map_sub, map_smul, hρv, map_mul,
          Module.End.mul_apply, polar_sub_right, polar_smul_right, hc₀v, smul_eq_mul, mul_one,
          sub_smul]
        abel }
  let QU : QuadraticForm k U := Q.comp U.subtype
  have hisoU : ∀ g u, QU (ρU g u) = QU u := fun g u => by
    show Q (T g u) = Q u
    rw [hTapp, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add (Q : V → k),
      QuadraticMap.map_smul, hQv, smul_zero, add_zero, polar_smul_right, hpv,
      ((hmemU u).1 u.2).1, smul_zero, add_zero, hiso]
  obtain ⟨u, hu0, hQu, hρu⟩ := exists_fixed_singular hUdim QU hG ρU hisoU
  have hwU := (hmemU u).1 u.2
  have hw0 : (u : V) ≠ 0 := fun h => hu0 (Subtype.ext h)
  obtain ⟨y, hy⟩ := exists_polar_eq_one hQ hw0
  refine ⟨v, u, c₀, y - polar Q v y • c₀, hQv, hQu, by rw [hsymm]; exact hwU.1, hc₀,
    by rw [hsymm]; exact hwU.2, ?_, ?_, hρv, fun g => ⟨polar Q c₀ (ρ g u), ?_⟩⟩
  · rw [polar_sub_right, polar_smul_right, hc₀, smul_eq_mul, mul_one, sub_self]
  · rw [polar_sub_right, polar_smul_right, hy, hsymm (u : V) c₀, hwU.2, smul_zero, sub_zero]
  · have := congrArg Subtype.val (hρu g)
    change T g u = u at this
    rw [hTapp, sub_eq_iff_eq_add] at this
    exact this

private theorem card_le_of_pair (hQ : Q.polarBilin.Nondegenerate) (hρ : Function.Injective ρ)
    (hiso : ∀ g v, Q (ρ g v) = Q v) (h2 : ∀ g : G, g * g = 1) {v w c₀ c₁ : V}
    (hQv : Q v = 0) (hQw : Q w = 0) (hvw : polar Q v w = 0) (hvc₀ : polar Q v c₀ = 1)
    (hwc₀ : polar Q w c₀ = 0) (hvc₁ : polar Q v c₁ = 0) (hwc₁ : polar Q w c₁ = 1)
    (hρv : ∀ g, ρ g v = v) (hρw : ∀ g, ∃ a : k, ρ g w = w + a • v) :
    Nat.card G ≤ Nat.card k ^ ((finrank k V - 2) * (finrank k V - 2) / 4 + 1) := by
  classical
  have hsymm : ∀ x y, polar Q x y = polar Q y x := fun x y => polar_comm _ x y
  obtain ⟨W, hmemW, hWdim⟩ : ∃ W : Submodule k V,
      (∀ x, x ∈ W ↔ polar Q v x = 0 ∧ polar Q w x = 0) ∧ finrank k W = finrank k V - 2 := by
    let Ψ : V →ₗ[k] k × k := (Q.polarBilin v).prod (Q.polarBilin w)
    refine ⟨LinearMap.ker Ψ, fun x => by simp [Ψ, Prod.ext_iff], ?_⟩
    have hsurj : Function.Surjective Ψ := fun p => ⟨p.1 • c₀ + p.2 • c₁, by
      ext <;> simp [Ψ, hvc₀, hvc₁, hwc₀, hwc₁]⟩
    have h1 := LinearMap.finrank_range_add_finrank_ker Ψ
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h1
    simp only [Module.finrank_prod, Module.finrank_self] at h1
    omega
  have hdec : ∀ x, x - polar Q v x • c₀ - polar Q w x • c₁ ∈ W := fun x => by
    rw [hmemW]
    constructor
    · rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right, hvc₀, hvc₁,
        smul_eq_mul, smul_eq_mul, mul_one, mul_zero, sub_self, sub_zero]
    · rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right, hwc₀, hwc₁,
        smul_eq_mul, smul_eq_mul, mul_one, mul_zero, sub_zero, sub_self]
  have hpv : ∀ g x, polar Q v (ρ g x) = polar Q v x := fun g x => by
    calc polar Q v (ρ g x) = polar Q (ρ g v) (ρ g x) := by rw [hρv]
      _ = polar Q v x := polar_iso hiso g v x
  have hρW : ∀ g, ∀ x ∈ W, ρ g x ∈ W := by
    intro g x hx
    rw [hmemW] at hx ⊢
    obtain ⟨a, ha⟩ := hρw g
    refine ⟨by rw [hpv]; exact hx.1, ?_⟩
    have hw : w = ρ g w - a • v := by rw [ha]; abel
    rw [hw, polar_sub_left, polar_smul_left, polar_iso hiso, hpv, hx.1, hx.2, smul_zero,
      sub_zero]
  obtain ⟨ρW, hρWapp⟩ : ∃ ρW : Representation k G W, ∀ g x, (ρW g x : V) = ρ g x :=
    ⟨{ toFun := fun g => (ρ g).restrict (hρW g)
       map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
       map_mul' := fun g h => LinearMap.ext fun x => Subtype.ext (by simp) }, fun _ _ => rfl⟩
  have hfixW : ∀ g ∈ ρW.asGroupHom.ker, ∀ x ∈ W, ρ g x = x := fun g hg x hx => by
    have h1 : ρW g = 1 := by
      rw [← Representation.asGroupHom_apply, (MonoidHom.mem_ker).1 hg, Units.val_one]
    rw [← hρWapp g ⟨x, hx⟩, h1, Module.End.one_apply]
  have hzero : ∀ z, (∀ y ∈ W, polar Q z y = 0) → polar Q z c₀ = 0 → polar Q z c₁ = 0 →
      z = 0 := by
    intro z hW h0 h1
    refine hQ.1 z fun y => ?_
    show polar Q z y = 0
    have hy := hW _ (hdec y)
    rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right, h0, h1,
      smul_zero, smul_zero, sub_zero, sub_zero] at hy
    exact hy
  have hsing : ∀ z, (∀ y ∈ W, polar Q z y = 0) → Q z = 0 := by
    intro z hz
    have hz' : z - polar Q z c₀ • v - polar Q z c₁ • w = 0 := by
      refine hzero _ (fun y hy => ?_) ?_ ?_
      · rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, hz y hy,
          ((hmemW y).1 hy).1, ((hmemW y).1 hy).2, smul_zero, smul_zero, sub_zero, sub_zero]
      · rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, hvc₀, hwc₀,
          smul_eq_mul, smul_eq_mul, mul_one, mul_zero, sub_self, sub_zero]
      · rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, hvc₁, hwc₁,
          smul_eq_mul, smul_eq_mul, mul_one, mul_zero, sub_zero, sub_self]
    have hz2 : z = polar Q z c₀ • v + polar Q z c₁ • w := by
      rw [sub_sub, sub_eq_zero] at hz'
      exact hz'
    rw [hz2, QuadraticMap.map_add (Q : V → k), QuadraticMap.map_smul, QuadraticMap.map_smul,
      hQv, hQw, polar_smul_left, polar_smul_right, hvw]
    simp
  have hβW : ∀ g ∈ ρW.asGroupHom.ker, ∀ x, ∀ y ∈ W, polar Q (ρ g x - x) y = 0 :=
    fun g hg x y hy => by
      have h := polar_iso hiso g x y
      rw [hfixW g hg y hy] at h
      rw [polar_sub_left, h, sub_self]
  have hβself : ∀ g ∈ ρW.asGroupHom.ker, ∀ x, polar Q (ρ g x - x) x = 0 := fun g hg x => by
    have h := hiso g x
    have e : ρ g x = x + (ρ g x - x) := by abel
    rw [e, QuadraticMap.map_add (Q : V → k), hsing _ (hβW g hg x), add_zero, add_eq_left] at h
    rw [hsymm]
    exact h
  have hβsymm : ∀ g ∈ ρW.asGroupHom.ker, ∀ x y, polar Q (ρ g x - x) y = polar Q (ρ g y - y) x :=
    fun g hg x y => by
      have h := hβself g hg (x + y)
      rw [map_add, show ρ g x + ρ g y - (x + y) = (ρ g x - x) + (ρ g y - y) by abel,
        polar_add_left, polar_add_right, polar_add_right, hβself g hg x, hβself g hg y,
        zero_add, add_zero, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
      exact h
  have hN : Nat.card ρW.asGroupHom.ker ≤ Nat.card k := by
    refine Nat.card_le_card_of_injective (fun g => polar Q (ρ g c₀ - c₀) c₁) ?_
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ hgg'
    simp only at hgg'
    have key : ∀ c, polar Q (ρ g c - c) c₀ = polar Q (ρ g' c - c) c₀ →
        polar Q (ρ g c - c) c₁ = polar Q (ρ g' c - c) c₁ → ρ g c = ρ g' c := by
      intro c h0 h1
      have hz : (ρ g c - c) - (ρ g' c - c) = 0 := by
        refine hzero _ (fun y hy => ?_) ?_ ?_
        · rw [polar_sub_left, hβW g hg c y hy, hβW g' hg' c y hy, sub_self]
        · rw [polar_sub_left, h0, sub_self]
        · rw [polar_sub_left, h1, sub_self]
      rw [sub_sub_sub_cancel_right, sub_eq_zero] at hz
      exact hz
    have h0 := key c₀ (by rw [hβself g hg, hβself g' hg']) hgg'
    have h1 := key c₁ (by rw [hβsymm g hg, hβsymm g' hg', hgg'])
      (by rw [hβself g hg, hβself g' hg'])
    have hx : ∀ x, ρ g x = ρ g' x := fun x => by
      have hxW := hdec x
      have e : x = (x - polar Q v x • c₀ - polar Q w x • c₁) + polar Q v x • c₀ +
          polar Q w x • c₁ := by abel
      rw [e, map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
        hfixW g hg _ hxW, hfixW g' hg' _ hxW, h0, h1]
    exact Subtype.ext (hρ (LinearMap.ext hx))
  have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
    have hinv : ∀ g : G, g⁻¹ = g := fun g => (eq_inv_of_mul_eq_one_left (h2 g)).symm
    have := mul_eq_one_iff_eq_inv.mp (h2 (a * b))
    rwa [mul_inv_rev, hinv, hinv] at this
  let ρQ : Representation k (G ⧸ ρW.asGroupHom.ker) W :=
    (Units.coeHom _).comp (QuotientGroup.kerLift ρW.asGroupHom)
  have hρQ : Function.Injective ρQ := fun a b h =>
    QuotientGroup.kerLift_injective ρW.asGroupHom (Units.ext h)
  have hquot := LinearAlgebra.SchurElemAbelianTwo.card_le_pow_of_mul_self_eq_one ρQ hρQ
    (fun a b => QuotientGroup.induction_on a fun a => QuotientGroup.induction_on b fun b => by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm])
    (fun a => QuotientGroup.induction_on a fun a => by
      rw [← QuotientGroup.mk_mul, h2, QuotientGroup.mk_one])
  calc Nat.card G = Nat.card (G ⧸ ρW.asGroupHom.ker) * Nat.card ρW.asGroupHom.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ ≤ Nat.card k ^ (finrank k W * finrank k W / 4) * Nat.card k := Nat.mul_le_mul hquot hN
    _ = _ := by rw [hWdim, pow_succ]

theorem card_le_of_isometry (hQ : Q.polarBilin.Nondegenerate) (hdim : 5 ≤ finrank k V)
    (hρ : Function.Injective ρ) (hiso : ∀ g v, Q (ρ g v) = Q v) (h2 : ∀ g : G, g * g = 1) :
    Nat.card G ≤ Nat.card k ^ ((finrank k V - 2) * (finrank k V - 2) / 4 + 1) := by
  have hG : IsPGroup 2 G := fun g => ⟨1, by rw [pow_one, pow_two, h2]⟩
  obtain ⟨v, w, c₀, c₁, hQv, hQw, hvw, hvc₀, hwc₀, hvc₁, hwc₁, hρv, hρw⟩ :=
    exists_pair hQ hdim hG hiso
  exact card_le_of_pair hQ hρ hiso h2 hQv hQw hvw hvc₀ hwc₀ hvc₁ hwc₁ hρv hρw

theorem card_le_pow_twentySix (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank k V = 12)
    (hρ : Function.Injective ρ) (hiso : ∀ g v, Q (ρ g v) = Q v) (h2 : ∀ g : G, g * g = 1) :
    Nat.card G ≤ Nat.card k ^ 26 := by
  have := card_le_of_isometry hQ (by omega) hρ hiso h2
  rwa [hdim] at this

end Pair

theorem card_le_of_semilinear_involution {K : Type} [Field K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hV : finrank K V = 12) {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate)
    (σ : K ≃+* K) (hσ : orderOf σ = 2) (T : V ≃+ V)
    (hT : ∀ (c : K) (v : V), T (c • v) = σ c • T v) (hTT : ∀ v, T (T v) = v)
    (hQT : ∀ v, Q (T v) = σ (Q v)) {G : Type*} [Group G] {ρ : Representation K G V}
    (hρ : Function.Injective ρ) (hiso : ∀ g v, Q (ρ g v) = Q v)
    (hcomm : ∀ g v, ρ g (T v) = T (ρ g v)) (h2 : ∀ g : G, g * g = 1) :
    Nat.card G ≤ 2 ^ (13 * f) := by
  classical
  have : Finite K := SeitzReduction.F4Pilot.finite_of_natCard_eq_two_pow hK
  obtain ⟨hdvd, S, hS, hScard, b, hb, C, hC, ⟨b₀, -⟩, hCfin, -⟩ :=
    RankThree.Classical.semilinear_fixed_basis Nat.prime_two hf hK σ hσ hV T hT fun v => hTT v
  have : FiniteDimensional S C := Module.Finite.of_basis b₀
  obtain ⟨e, rfl⟩ := hdvd
  have hScard' : Nat.card S = 2 ^ e := by
    rw [hScard, Nat.mul_div_cancel_left e (by norm_num : 0 < 2)]
  have : CharP S 2 := SeitzReduction.F4Pilot.charP_two_of_natCard_eq_two_pow hScard'
  have hmemS : ∀ c : K, σ c = c → c ∈ S := fun c hc => by
    rw [← SetLike.mem_coe, hS]
    exact hc
  have hmemC : ∀ v, v ∈ C ↔ T v = v := fun v => by
    rw [← SetLike.mem_coe, hC]
    rfl
  have hQS : ∀ v ∈ C, Q v ∈ S := fun v hv => hmemS _ (by rw [← hQT, (hmemC v).1 hv])
  have hbC : ∀ i, b i ∈ C := fun i => (hmemC _).2 (hb i)
  obtain ⟨π, hπ⟩ : ∃ π : K →ₗ[S] S, ∀ s : S, π (s : K) = s := by
    obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap S K)
      (LinearMap.ker_eq_bot.2 (algebraMap S K).injective)
    exact ⟨π, fun s => LinearMap.congr_fun hπ s⟩
  let Q₀ : QuadraticForm S C := (π.compQuadraticMap' Q).comp C.subtype
  have hQ₀ : ∀ v : C, (Q₀ v : K) = Q v := fun v => congrArg Subtype.val (hπ ⟨Q v, hQS v v.2⟩)
  have hpolar₀ : ∀ x y : C, ((QuadraticMap.polar Q₀ x y : S) : K) = QuadraticMap.polar Q x y := by
    intro x y
    rw [QuadraticMap.polar, QuadraticMap.polar, Subfield.coe_sub, Subfield.coe_sub, hQ₀, hQ₀, hQ₀,
      Submodule.coe_add]
  have hsep : ∀ x : C, (∀ y : C, QuadraticMap.polar Q₀ x y = 0) → x = 0 := by
    intro x hx
    have hx' : Q.polarBilin (x : V) = 0 := b.ext fun i => by
      have h := congrArg Subtype.val (hx ⟨b i, hbC i⟩)
      rw [hpolar₀] at h
      exact h
    exact Subtype.ext (hQ.1 _ fun y => LinearMap.congr_fun hx' y)
  have hQ₀nd : Q₀.polarBilin.Nondegenerate := by
    refine ⟨fun x hx => hsep x hx, fun y hy => hsep y fun x => ?_⟩
    rw [QuadraticMap.polar_comm]
    exact hy x
  have hρC : ∀ g, ∀ v ∈ C, ρ g v ∈ C := fun g v hv => by
    rw [hmemC] at hv ⊢
    rw [← hcomm, hv]
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : Representation S G C, ∀ g v, (ρ₀ g v : V) = ρ g v :=
    ⟨{ toFun := fun g => ((ρ g).restrictScalars S).restrict (hρC g)
       map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
       map_mul' := fun g h => LinearMap.ext fun v => Subtype.ext
         (show ρ (g * h) (v : V) = ρ g (ρ h v) by rw [map_mul]; rfl) }, fun _ _ => rfl⟩
  have hρ₀inj : Function.Injective ρ₀ := by
    intro g g' hgg'
    refine hρ (b.ext fun i => ?_)
    rw [← hρ₀ g ⟨b i, hbC i⟩, ← hρ₀ g' ⟨b i, hbC i⟩, hgg']
  have hiso₀ : ∀ g v, Q₀ (ρ₀ g v) = Q₀ v := fun g v => Subtype.ext (by
    rw [hQ₀, hQ₀, hρ₀, hiso])
  calc Nat.card G ≤ Nat.card S ^ 26 := card_le_pow_twentySix hQ₀nd hCfin hρ₀inj hiso₀ h2
    _ = 2 ^ (13 * (2 * e)) := by rw [hScard', ← pow_mul]; ring_nf

end CFSG.RankThree.GF2n.Smith81.OrthRank

