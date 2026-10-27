module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCells
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthIdentActs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxMat
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameStd
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMLin
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGQTwoDRootFrame

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType.OrthTorus CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)

variable {G : Type} [Group G] [Finite G]

private noncomputable def torusEquiv {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X) :
    (Fin Φ.r → Multiplicative (ZMod 3)) ≃* ↥Φ.A :=
  (MonoidHom.ofInjective Φ.Δ.τ_inj).trans (MulEquiv.subgroupCongr Φ.Δ.τ_range)

private theorem torusEquiv_apply {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (f : Fin Φ.r → Multiplicative (ZMod 3)) :
    ((torusEquiv Φ f : ↥Φ.A) : Φ.V ≃ₗ[Φ.F] Φ.V) = Φ.Δ.τ f := by
  simp [torusEquiv, MonoidHom.ofInjective_apply, MulEquiv.subgroupCongr_apply]

private theorem torusEquiv_symm_apply {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (a : ↥Φ.A) :
    Φ.Δ.τ ((torusEquiv Φ).symm a) = (a : Φ.V ≃ₗ[Φ.F] Φ.V) := by
  rw [← torusEquiv_apply Φ ((torusEquiv Φ).symm a), MulEquiv.apply_symm_apply]

private noncomputable def bOf {Bs : Subgroup G} (β : Additive ↥Bs ≃+ DVec 6)
    (v : DVec 6) : ↥Bs :=
  Additive.toMul (β.symm v)

private noncomputable def betaA {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (β : Additive ↥Bs ≃+ DVec 6) : ↥Bs →* ↥Φ.A where
  toFun b := ⟨(Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V), Φ.hβA b⟩
  map_one' := Subtype.ext (by simp)
  map_mul' b c := Subtype.ext (by simp)

private noncomputable def coordHom {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (β : Additive ↥Bs ≃+ DVec 6) : DVec 6 →+ (Fin Φ.r → ZMod 3) where
  toFun v := fun i =>
    Multiplicative.toAdd ((torusEquiv Φ).symm (betaA Φ β (bOf β v)) i)
  map_zero' := by
    funext i
    rw [show bOf β (0 : DVec 6) = 1 from by simp [bOf], map_one (betaA Φ β),
      map_one ((torusEquiv Φ).symm), Pi.zero_apply]
    simp
  map_add' v w := by
    funext i
    have hb : bOf β (v + w) = bOf β v * bOf β w := by
      simp [bOf, map_add, toMul_add]
    simp only [Pi.add_apply, hb, map_mul, Pi.mul_apply, toAdd_mul]

private theorem bOf_add {Bs : Subgroup G} (β : Additive ↥Bs ≃+ DVec 6) (v w : DVec 6) :
    bOf β (v + w) = bOf β v * bOf β w := by
  simp [bOf, map_add, toMul_add]

private theorem bOf_zero {Bs : Subgroup G} (β : Additive ↥Bs ≃+ DVec 6) :
    bOf β 0 = 1 := by
  simp [bOf]

private theorem bOf_neg {Bs : Subgroup G} (β : Additive ↥Bs ≃+ DVec 6) (v : DVec 6) :
    bOf β (-v) = (bOf β v)⁻¹ := by
  have h : bOf β v * bOf β (-v) = 1 := by
    rw [← bOf_add, add_neg_cancel, bOf_zero]
  exact eq_inv_of_mul_eq_one_right h

private theorem bOf_sub {Bs : Subgroup G} (β : Additive ↥Bs ≃+ DVec 6) (v w : DVec 6) :
    bOf β (v - w) = bOf β v * (bOf β w)⁻¹ := by
  rw [sub_eq_add_neg, bOf_add, bOf_neg]

private theorem beta_ofMul_bOf {Bs : Subgroup G} (β : Additive ↥Bs ≃+ DVec 6)
    (v : DVec 6) : β (Additive.ofMul (bOf β v)) = v := by
  simp [bOf]

private theorem ofAddFun_neg {r : ℕ} (w : Fin r → ZMod 3) :
    (fun i => Multiplicative.ofAdd ((-w) i)) =
      ((fun i => Multiplicative.ofAdd (w i)) : Fin r → Multiplicative (ZMod 3))⁻¹ := by
  funext i
  simp [Pi.neg_apply, Pi.inv_apply, ofAdd_neg]

private theorem ofAddFun_single {r : ℕ} (j : Fin r) (s : ZMod 3) :
    (fun i => Multiplicative.ofAdd ((Pi.single j s : Fin r → ZMod 3) i)) =
      Pi.mulSingle j (Multiplicative.ofAdd s) := by
  funext i
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.mulSingle_eq_of_ne h]
    rfl

private theorem zmod3_eq_one_or_neg_one (x : ZMod 3) (hx : x ≠ 0) : x = 1 ∨ x = -1 := by
  revert x
  decide

private theorem zmod3_eq_zero_of_eq_neg (x : ZMod 3) (h : x = -x) : x = 0 := by
  have h2 : (2 : ZMod 3) * x = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h]
    exact neg_add_cancel x
  exact (mul_eq_zero.mp h2).resolve_left (by decide)

private theorem coordHom_spec {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (β : Additive ↥Bs ≃+ DVec 6) (v : DVec 6) :
    Φ.Δ.τ (fun i => Multiplicative.ofAdd (coordHom Φ β v i)) =
      (Φ.β (bOf β v) : Φ.V ≃ₗ[Φ.F] Φ.V) := by
  calc Φ.Δ.τ (fun i => Multiplicative.ofAdd (coordHom Φ β v i))
      = Φ.Δ.τ ((torusEquiv Φ).symm (betaA Φ β (bOf β v))) := by
        congr 1
    _ = (Φ.β (bOf β v) : Φ.V ≃ₗ[Φ.F] Φ.V) := torusEquiv_symm_apply Φ _

private theorem ofAddFun_coordHom {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (β : Additive ↥Bs ≃+ DVec 6) (v : DVec 6) :
    (fun i => Multiplicative.ofAdd (coordHom Φ β v i)) =
      (torusEquiv Φ).symm (betaA Φ β (bOf β v)) := by
  funext i
  simp [coordHom, ofAdd_toAdd]

private theorem center_orthDerived_eq_bot_of_center {Bs X : Subgroup G}
    (Φ : OrthFrameCore 3 Bs X) (hZ : Subgroup.center ↥X = ⊥) :
    Subgroup.center ↥(orthDerived Φ.Q) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hψzX : Φ.ψ z ∈ X :=
    Φ.hrange.le (MonoidHom.mem_range.mpr ⟨z, rfl⟩)
  have hzX : (⟨Φ.ψ z, hψzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (Φ.hrange.symm.le g.2)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hy]
    have h := congrArg Φ.ψ (Subgroup.mem_center_iff.mp hz y)
    simpa [map_mul] using h
  have hz1 : Φ.ψ z = 1 := by
    have hmem : (⟨Φ.ψ z, hψzX⟩ : ↥X) ∈ (⊥ : Subgroup ↥X) := by
      rw [← hZ]
      exact hzX
    have h : (⟨Φ.ψ z, hψzX⟩ : ↥X) = 1 := by simpa using hmem
    simpa using congrArg (fun t : ↥X => (t : G)) h
  apply Φ.hinj
  simpa using hz1

private theorem psi_beta_of_mem_X {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (hZΩ : Subgroup.center ↥(orthDerived Φ.Q) = ⊥) {b : ↥Bs} (hb : (b : G) ∈ X) :
    Φ.ψ (Φ.β b) = (b : G) := by
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (Φ.hrange.symm.le hb)
  have hcenter : w⁻¹ * Φ.β b ∈ Subgroup.center ↥(orthDerived Φ.Q) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : Φ.β b * y * (Φ.β b)⁻¹ = w * y * w⁻¹ := by
      apply Φ.hinj
      rw [Φ.hcompat b y, map_mul, map_mul, map_inv, hw]
    have h2 : (w⁻¹ * Φ.β b) * y * (w⁻¹ * Φ.β b)⁻¹ = y := by
      calc (w⁻¹ * Φ.β b) * y * (w⁻¹ * Φ.β b)⁻¹ =
          w⁻¹ * (Φ.β b * y * (Φ.β b)⁻¹) * w := by group
        _ = w⁻¹ * (w * y * w⁻¹) * w := by rw [h1]
        _ = y := by group
    calc y * (w⁻¹ * Φ.β b) =
        ((w⁻¹ * Φ.β b) * y * (w⁻¹ * Φ.β b)⁻¹) * (w⁻¹ * Φ.β b) := by rw [h2]
      _ = (w⁻¹ * Φ.β b) * y := by group
  have h1 : w⁻¹ * Φ.β b = 1 := by
    have hmem : w⁻¹ * Φ.β b ∈ (⊥ : Subgroup ↥(orthDerived Φ.Q)) := by
      rw [← hZΩ]
      exact hcenter
    simpa using hmem
  have hbw : Φ.β b = w := by
    have h := congrArg (fun t => w * t) h1
    simpa using h
  rw [hbw]
  exact hw

private theorem beta_x_eq_one {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (hZΩ : Subgroup.center ↥(orthDerived Φ.Q) = ⊥) {x : G} (hx : x ∈ Bs)
    (hxX : X ≤ Subgroup.centralizer ({x} : Set G)) : Φ.β ⟨x, hx⟩ = 1 := by
  have hcenter : Φ.β ⟨x, hx⟩ ∈ Subgroup.center ↥(orthDerived Φ.Q) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hconj : Φ.β ⟨x, hx⟩ * y * (Φ.β ⟨x, hx⟩)⁻¹ = y := by
      apply Φ.hinj
      rw [Φ.hcompat ⟨x, hx⟩ y]
      have hyX : Φ.ψ y ∈ X :=
        Φ.hrange.le (MonoidHom.mem_range.mpr ⟨y, rfl⟩)
      have hcomm : x * Φ.ψ y = Φ.ψ y * x :=
        (Subgroup.mem_centralizer_iff.mp (hxX hyX)) x (Set.mem_singleton x)
      rw [hcomm]
      group
    calc y * Φ.β ⟨x, hx⟩ =
        (Φ.β ⟨x, hx⟩ * y * (Φ.β ⟨x, hx⟩)⁻¹) * Φ.β ⟨x, hx⟩ := by rw [hconj]
      _ = Φ.β ⟨x, hx⟩ * y := by group
  have hmem : Φ.β ⟨x, hx⟩ ∈ (⊥ : Subgroup ↥(orthDerived Φ.Q)) := by
    rw [← hZΩ]
    exact hcenter
  simpa using hmem

private theorem conj_mem_X {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X) (b : ↥Bs)
    {y : G} (hy : y ∈ X) : (b : G) * y * (b : G)⁻¹ ∈ X := by
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (Φ.hrange.symm.le hy)
  rw [← hw, ← Φ.hcompat b w]
  exact Φ.hrange.le
    (MonoidHom.mem_range.mpr ⟨Φ.β b * w * (Φ.β b)⁻¹, rfl⟩)

private theorem mem_normalizer_X {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X) (b : ↥Bs) :
    (b : G) ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact conj_mem_X Φ b
  · intro hy
    have h := conj_mem_X Φ b⁻¹ hy
    have h' : (b : G)⁻¹ * ((b : G) * y * (b : G)⁻¹) * ((b : G)⁻¹)⁻¹ ∈ X := by
      simpa using h
    rwa [show (b : G)⁻¹ * ((b : G) * y * (b : G)⁻¹) * ((b : G)⁻¹)⁻¹ = y by group] at h'

private theorem ggLin_dSign_bOf_single {Bs : Subgroup G}
    (β : Additive ↥Bs ≃+ DVec 6) {a k : Fin 6} {ρ : MulAut ↥Bs}
    (hρlin : ggLin (p := 3) β ρ = dSign 6 a k) :
    ρ (bOf β (Pi.single a (1 : ZMod 3))) =
      (bOf β (Pi.single a (1 : ZMod 3)))⁻¹ := by
  have hba' : Additive.ofMul (ρ (bOf β (Pi.single a (1 : ZMod 3)))) =
      Additive.ofMul ((bOf β (Pi.single a (1 : ZMod 3)))⁻¹) := by
    apply β.injective
    have h1 : β (Additive.ofMul (ρ (bOf β (Pi.single a (1 : ZMod 3))))) =
        dSign 6 a k (Pi.single a (1 : ZMod 3)) := by
      rw [← ggLin_apply_ofMul (p := 3) β ρ (bOf β (Pi.single a (1 : ZMod 3))),
        beta_ofMul_bOf β (Pi.single a (1 : ZMod 3)), hρlin]
    have h2 : dSign 6 a k (Pi.single a (1 : ZMod 3)) = -Pi.single a 1 := by
      rw [show Pi.single a (1 : ZMod 3) = dBasis 6 a from
        (Pi.basisFun_apply (ZMod 3) (Fin 6) a).symm, dSign_apply,
        if_pos (Or.inl rfl), neg_one_smul]
    have h3 : β (Additive.ofMul ((bOf β (Pi.single a (1 : ZMod 3)))⁻¹)) =
        -Pi.single a 1 := by
      rw [ofMul_inv, map_neg, beta_ofMul_bOf]
    rw [h1, h2, h3]
  exact Additive.ofMul.injective hba'

private theorem exists_mem_X_conj_bOf_single_eq_inv {Bs X : Subgroup G}
    (β : Additive ↥Bs ≃+ DVec 6) {i₀ a : Fin 6} (ha : a ≠ i₀)
    (hAe : dEvenStab 6 (Pi.single i₀ 1) ≤
      (ggAutomizer X Bs).map (ggLin (p := 3) β)) :
    ∃ n : G, n ∈ X ∧
      n * ((bOf β (Pi.single a (1 : ZMod 3)) : ↥Bs) : G) * n⁻¹ =
        (((bOf β (Pi.single a (1 : ZMod 3)))⁻¹ : ↥Bs) : G) := by
  classical
  obtain ⟨k, hka, hki⟩ := Fin.exists_ne_and_ne_of_two_lt a i₀ (by omega : 2 < 6)
  have hak : a ≠ k := Ne.symm hka
  have hfix : dSign 6 a k (Pi.single i₀ (1 : ZMod 3)) =
      Pi.single i₀ (1 : ZMod 3) := by
    rw [show Pi.single i₀ (1 : ZMod 3) = dBasis 6 i₀ from
      (Pi.basisFun_apply (ZMod 3) (Fin 6) i₀).symm, dSign_apply]
    rw [if_neg (by rintro (h | h); exacts [ha h.symm, hki h.symm]), one_smul]
  have hmem : dSign 6 a k ∈ dEvenStab 6 (Pi.single i₀ 1) :=
    ⟨dSign_mem_dEven hak, hfix⟩
  have hmem' : dSign 6 a k ∈ (ggAutomizer X Bs).map (ggLin (p := 3) β) :=
    hAe hmem
  obtain ⟨ρ, hρ, hρlin⟩ := Subgroup.mem_map.mp hmem'
  have hba := ggLin_dSign_bOf_single β hρlin
  obtain ⟨n, hnX, _, hnconj⟩ := mem_ggAutomizer_iff.mp hρ
  refine ⟨n, hnX, ?_⟩
  have h := hnconj (bOf β (Pi.single a (1 : ZMod 3)))
  rw [hba] at h
  exact h.symm

private theorem bOf_single_pow_three {Bs : Subgroup G}
    (β : Additive ↥Bs ≃+ DVec 6) (a : Fin 6) :
    (bOf β (Pi.single a (1 : ZMod 3))) ^ 3 = 1 := by
  have h3 : (3 : ℕ) • (Pi.single a (1 : ZMod 3) : DVec 6) = 0 := by
    funext j
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  calc (bOf β (Pi.single a 1)) ^ 3 =
      Additive.toMul ((3 : ℕ) • β.symm (Pi.single a (1 : ZMod 3))) := by
        rw [toMul_nsmul]
        rfl
    _ = Additive.toMul (β.symm ((3 : ℕ) • Pi.single a (1 : ZMod 3))) := by
        conv_rhs => rw [map_nsmul (β.symm)]
    _ = Additive.toMul (β.symm 0) := by rw [h3]
    _ = 1 := by simp

private theorem bOf_single_inv_mul_inv {Bs : Subgroup G}
    (β : Additive ↥Bs ≃+ DVec 6) (a : Fin 6) :
    (bOf β (Pi.single a (1 : ZMod 3)))⁻¹ * (bOf β (Pi.single a (1 : ZMod 3)))⁻¹ =
      bOf β (Pi.single a (1 : ZMod 3)) := by
  have hb3 := bOf_single_pow_three β a
  have hb3' : bOf β (Pi.single a 1) * bOf β (Pi.single a 1) *
      bOf β (Pi.single a 1) = 1 := by
    simpa [pow_succ, pow_two] using hb3
  have hsq' : bOf β (Pi.single a 1) =
      (bOf β (Pi.single a 1) * bOf β (Pi.single a 1))⁻¹ :=
    eq_inv_of_mul_eq_one_right hb3'
  have hsq : (bOf β (Pi.single a 1))⁻¹ = bOf β (Pi.single a 1) *
      bOf β (Pi.single a 1) := by
    have h := congrArg (fun z : ↥Bs => z⁻¹) hsq'
    simpa using h
  calc (bOf β (Pi.single a 1))⁻¹ * (bOf β (Pi.single a 1))⁻¹ =
      (bOf β (Pi.single a 1) * bOf β (Pi.single a 1)) *
        (bOf β (Pi.single a 1) * bOf β (Pi.single a 1)) := by rw [hsq]
    _ = (bOf β (Pi.single a 1)) ^ 4 := by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
    _ = bOf β (Pi.single a 1) := by
      rw [show (bOf β (Pi.single a 1)) ^ 4 =
        (bOf β (Pi.single a 1)) ^ 3 * bOf β (Pi.single a 1) by group, hb3, one_mul]

private theorem bOf_single_mem_X {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (β : Additive ↥Bs ≃+ DVec 6) {i₀ a : Fin 6} (ha : a ≠ i₀)
    (hAe : dEvenStab 6 (Pi.single i₀ 1) ≤ (ggAutomizer X Bs).map (ggLin (p := 3) β)) :
    (bOf β (Pi.single a (1 : ZMod 3)) : G) ∈ X := by
  obtain ⟨n, hnX, hnba⟩ := exists_mem_X_conj_bOf_single_eq_inv β ha hAe
  have hb_norm : ((bOf β (Pi.single a 1) : ↥Bs) : G) ∈
      Subgroup.normalizer (X : Set G) := mem_normalizer_X Φ _
  have hconjX : ((bOf β (Pi.single a 1) : ↥Bs) : G) * n⁻¹ *
      (((bOf β (Pi.single a 1) : ↥Bs) : G))⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp hb_norm n⁻¹).mp (X.inv_mem hnX)
  have hprodX : n * (((bOf β (Pi.single a 1) : ↥Bs) : G) * n⁻¹ *
      (((bOf β (Pi.single a 1) : ↥Bs) : G))⁻¹) ∈ X :=
    X.mul_mem hnX hconjX
  let bG : G := ((bOf β (Pi.single a (1 : ZMod 3)) : ↥Bs) : G)
  have hb2G : bG⁻¹ * bG⁻¹ = bG := by
    have h := congrArg (fun z : ↥Bs => (z : G)) (bOf_single_inv_mul_inv β a)
    simpa [bG] using h
  have hnbaG : n * bG * n⁻¹ = bG⁻¹ := by
    simpa [bG] using hnba
  have hcalc : bG = n * (bG * n⁻¹ * bG⁻¹) := by
    calc bG = bG⁻¹ * bG⁻¹ := hb2G.symm
      _ = (n * bG * n⁻¹) * bG⁻¹ := by rw [hnbaG]
      _ = n * (bG * n⁻¹ * bG⁻¹) := by group
  change bG ∈ X
  rw [hcalc]
  simpa [bG] using hprodX

private theorem bOf_dRootAB_mem_X {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (β : Additive ↥Bs ≃+ DVec 6) {i₀ : Fin 6}
    (hAe : dEvenStab 6 (Pi.single i₀ 1) ≤ (ggAutomizer X Bs).map (ggLin (p := 3) β))
    (ε : Bool) {a b : Fin 6} (ha : a ≠ i₀) (hb : b ≠ i₀) :
    (bOf β (dRootAB 6 ε a b) : G) ∈ X := by
  have hfalse : dRootAB 6 false a b =
      Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) := by
    simp [dRootAB, dSgn, dBasis, Pi.basisFun_apply]
  have htrue : dRootAB 6 true a b =
      Pi.single a (1 : ZMod 3) + Pi.single b (1 : ZMod 3) := by
    simp [dRootAB, dSgn, dBasis, Pi.basisFun_apply]
  cases ε
  · rw [hfalse, bOf_sub]
    exact X.mul_mem (bOf_single_mem_X Φ β ha hAe)
      (X.inv_mem (bOf_single_mem_X Φ β hb hAe))
  · rw [htrue, bOf_add]
    exact X.mul_mem (bOf_single_mem_X Φ β ha hAe) (bOf_single_mem_X Φ β hb hAe)

private theorem coordHom_ne_zero_of_mem_X {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (β : Additive ↥Bs ≃+ DVec 6)
    (hZΩ : Subgroup.center ↥(orthDerived Φ.Q) = ⊥) {v : DVec 6}
    (hvX : (bOf β v : G) ∈ X) (hv : v ≠ 0) : coordHom Φ β v ≠ 0 := by
  intro h0
  apply hv
  have hβ1 : Φ.β (bOf β v) = 1 := by
    have hspec := coordHom_spec Φ β v
    rw [h0] at hspec
    have h1 : (fun i => Multiplicative.ofAdd ((0 : Fin Φ.r → ZMod 3) i)) =
        (1 : Fin Φ.r → Multiplicative (ZMod 3)) := by
      funext i
      simp
    rw [h1, map_one] at hspec
    exact Subtype.ext hspec.symm
  have hb1 : bOf β v = 1 := by
    have hpsi := psi_beta_of_mem_X Φ hZΩ hvX
    exact Subtype.ext (by rw [← hpsi, hβ1]; simp)
  calc v = β (Additive.ofMul (bOf β v)) := (beta_ofMul_bOf β v).symm
    _ = β (Additive.ofMul 1) := by rw [hb1]
    _ = 0 := by simp

private theorem coordHom_single_i₀_eq_zero {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (β : Additive ↥Bs ≃+ DVec 6)
    (hZΩ : Subgroup.center ↥(orthDerived Φ.Q) = ⊥) {i₀ : Fin 6} {c : ZMod 3}
    (hc : c ≠ 0) {x : G} (hx : x ∈ Bs)
    (hxc : β (Additive.ofMul ⟨x, hx⟩) = c • Pi.single i₀ 1)
    (hxX : X ≤ Subgroup.centralizer ({x} : Set G)) :
    coordHom Φ β (Pi.single i₀ (1 : ZMod 3)) = 0 := by
  have hβx : Φ.β ⟨x, hx⟩ = 1 := beta_x_eq_one Φ hZΩ hx hxX
  have hbOf : bOf β (c • Pi.single i₀ (1 : ZMod 3)) = ⟨x, hx⟩ := by
    rw [bOf]
    have hsymm : β.symm (c • Pi.single i₀ (1 : ZMod 3)) = Additive.ofMul ⟨x, hx⟩ := by
      rw [AddEquiv.symm_apply_eq]
      exact hxc.symm
    rw [hsymm, toMul_ofMul]
  have hc0 : coordHom Φ β (c • Pi.single i₀ (1 : ZMod 3)) = 0 := by
    have hspec := coordHom_spec Φ β (c • Pi.single i₀ (1 : ZMod 3))
    rw [hbOf, hβx] at hspec
    have h1 : Φ.Δ.τ (fun i => Multiplicative.ofAdd
        (coordHom Φ β (c • Pi.single i₀ (1 : ZMod 3)) i)) = 1 := by
      simpa using hspec
    have h2 : Φ.Δ.τ (fun i => Multiplicative.ofAdd
        ((0 : Fin Φ.r → ZMod 3) i)) = 1 := by
      have hzero : (fun i => Multiplicative.ofAdd ((0 : Fin Φ.r → ZMod 3) i)) =
          (1 : Fin Φ.r → Multiplicative (ZMod 3)) := by
        funext i
        simp
      rw [hzero, map_one]
    have hfun := Φ.Δ.τ_inj (h1.trans h2.symm)
    funext i
    exact Multiplicative.ofAdd.injective (congrFun hfun i)
  rcases zmod3_eq_one_or_neg_one c hc with h1 | h1
  · rwa [h1, one_smul] at hc0
  · rw [h1, neg_one_smul, map_neg] at hc0
    exact neg_eq_zero.mp hc0

private theorem coordHom_surjective {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (β : Additive ↥Bs ≃+ DVec 6) : Function.Surjective (coordHom Φ β) := by
  intro w
  let g : Fin Φ.r → Multiplicative (ZMod 3) := fun i => Multiplicative.ofAdd (w i)
  have hgA : Φ.Δ.τ g ∈ Φ.A :=
    Φ.Δ.τ_range.le (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
  obtain ⟨b, hb⟩ := Φ.hβsurj (Φ.Δ.τ g) hgA
  refine ⟨β (Additive.ofMul b), ?_⟩
  have hbOf : bOf β (β (Additive.ofMul b)) = b := by simp [bOf]
  have hspec := coordHom_spec Φ β (β (Additive.ofMul b))
  rw [hbOf, hb] at hspec
  have hfun := Φ.Δ.τ_inj hspec
  funext i
  exact Multiplicative.ofAdd.injective (congrFun hfun i)

private theorem rank_le_five {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (β : Additive ↥Bs ≃+ DVec 6) {i₀ : Fin 6}
    (hMe : coordHom Φ β (Pi.single i₀ (1 : ZMod 3)) = 0) : Φ.r ≤ 5 := by
  let Mlin : DVec 6 →ₗ[ZMod 3] (Fin Φ.r → ZMod 3) :=
    (coordHom Φ β).toZModLinearMap 3
  have hsurj : Function.Surjective Mlin := by
    intro w
    obtain ⟨v, hv⟩ := coordHom_surjective Φ β w
    exact ⟨v, by simpa [Mlin, AddMonoidHom.coe_toZModLinearMap] using hv⟩
  have hspan : Submodule.span (ZMod 3) ({Pi.single i₀ (1 : ZMod 3)} : Set (DVec 6)) ≤
      LinearMap.ker Mlin := by
    rw [Submodule.span_le]
    rintro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    change Mlin (Pi.single i₀ (1 : ZMod 3)) = 0
    simpa [Mlin, AddMonoidHom.coe_toZModLinearMap] using hMe
  have hker1 : Module.finrank (ZMod 3) (Submodule.span (ZMod 3)
      ({Pi.single i₀ (1 : ZMod 3)} : Set (DVec 6))) = 1 := by
    apply finrank_span_singleton
    intro h
    have := congrFun h i₀
    simp at this
  have hker : (1 : ℕ) ≤ Module.finrank (ZMod 3) (LinearMap.ker Mlin) := by
    calc 1 = Module.finrank (ZMod 3) (Submodule.span (ZMod 3)
          ({Pi.single i₀ (1 : ZMod 3)} : Set (DVec 6))) := hker1.symm
      _ ≤ Module.finrank (ZMod 3) (LinearMap.ker Mlin) := Submodule.finrank_mono hspan
  have h6 : Module.finrank (ZMod 3) (DVec 6) = 6 := Module.finrank_fin_fun (ZMod 3)
  have hrk := LinearMap.finrank_range_add_finrank_ker Mlin
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    Module.finrank_fin_fun (ZMod 3), h6] at hrk
  omega

private theorem dTau_fix_single_of_ne {m : ℕ} (ε : Bool) {a b i : Fin m}
    (hai : i ≠ a) (hbi : i ≠ b) :
    dTau m ε a b (Pi.single i (1 : ZMod 3)) = Pi.single i (1 : ZMod 3) := by
  rw [show Pi.single i (1 : ZMod 3) = dBasis m i from
    (Pi.basisFun_apply (ZMod 3) (Fin m) i).symm, dTau_apply_of_ne m ε hai hbi]

private theorem dRootAB_false (a b : Fin 6) :
    dRootAB 6 false a b = Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) := by
  simp [dRootAB, dSgn, dBasis, Pi.basisFun_apply]

private theorem dRootAB_true (a b : Fin 6) :
    dRootAB 6 true a b = Pi.single a (1 : ZMod 3) + Pi.single b (1 : ZMod 3) := by
  simp [dRootAB, dSgn, dBasis, Pi.basisFun_apply]

private theorem dTau_dRootAB (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) :
    dTau m ε a b (dRootAB m ε a b) = -dRootAB m ε a b := by
  rw [dTau_apply_vec m ε hab, dFormAB_dRootAB m ε hab]
  have h2 : (2 : ZMod 3) = -1 := by decide
  have h3 : dRootAB m ε a b + dRootAB m ε a b = -dRootAB m ε a b := by
    rw [← two_smul (ZMod 3) (dRootAB m ε a b), h2, neg_one_smul]
  rw [h2, neg_one_smul, sub_neg_eq_add, h3]

private theorem isDRootVec_of_neg_eigen_false {r : ℕ} {w : Fin r → ZMod 3}
    {i j : Fin r} (hij : i ≠ j)
    (hzero : ∀ k, k ≠ i → k ≠ j → w k = 0)
    (hwj : w j = -w i) (hw : w ≠ 0) : IsDRootVec w := by
  have hwi0 : w i ≠ 0 := by
    intro h0
    apply hw
    funext k
    by_cases hki : k = i
    · subst hki
      exact h0
    · by_cases hkj : k = j
      · rw [hkj, hwj, h0]
        simp
      · exact hzero k hki hkj
  have hwipm := zmod3_eq_one_or_neg_one (w i) hwi0
  have hwjpm : w j = 1 ∨ w j = -1 := by
    rcases hwipm with h' | h' <;> rw [hwj, h'] <;> simp
  refine ⟨i, j, hij, w i, w j, hwipm, hwjpm, ?_⟩
  funext k
  by_cases hki : k = i
  · subst hki
    simp [Pi.single_eq_same, Pi.single_eq_of_ne hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)]
    · rw [hzero k hki hkj]
      simp [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]

private theorem isDRootVec_of_neg_eigen_true {r : ℕ} {w : Fin r → ZMod 3}
    {i j : Fin r} (hij : i ≠ j)
    (hzero : ∀ k, k ≠ i → k ≠ j → w k = 0)
    (hwj : w j = w i) (hw : w ≠ 0) : IsDRootVec w := by
  have hwi0 : w i ≠ 0 := by
    intro h0
    apply hw
    funext k
    by_cases hki : k = i
    · subst hki
      exact h0
    · by_cases hkj : k = j
      · rw [hkj, hwj, h0]
        simp
      · exact hzero k hki hkj
  have hwipm := zmod3_eq_one_or_neg_one (w i) hwi0
  have hwjpm : w j = 1 ∨ w j = -1 := by
    rw [hwj]
    exact hwipm
  refine ⟨i, j, hij, w i, w j, hwipm, hwjpm, ?_⟩
  funext k
  by_cases hki : k = i
  · subst hki
    simp [Pi.single_eq_same, Pi.single_eq_of_ne hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)]
    · rw [hzero k hki hkj]
      simp [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]

private theorem isDRootVec_of_neg_eigen {r : ℕ} {x : OmPlusIdx r} {w : Fin r → ZMod 3}
    (hw : w ≠ 0)
    (h : (fun i => Multiplicative.ofAdd (w i))⁻¹ =
      omPlusRefl 3 x (fun i => Multiplicative.ofAdd (w i))) :
    IsDRootVec w := by
  classical
  obtain ⟨⟨⟨i, j⟩, hij⟩, s⟩ := x
  have hij' : i ≠ j := ne_of_lt hij
  have hcoord : ∀ k, -w k = Multiplicative.toAdd
      (omPlusRefl 3 (⟨(i, j), hij⟩, s) (fun l => Multiplicative.ofAdd (w l)) k) := by
    intro k
    have hh := congrArg (fun f : Fin r → Multiplicative (ZMod 3) =>
      Multiplicative.toAdd (f k)) h
    rw [Pi.inv_apply, toAdd_inv, toAdd_ofAdd] at hh
    exact hh
  have hzero : ∀ k, k ≠ i → k ≠ j → w k = 0 := by
    intro k hki hkj
    have hk := hcoord k
    rw [omPlusRefl_apply_coord, if_neg hki, if_neg hkj] at hk
    exact zmod3_eq_zero_of_eq_neg (w k) (by simpa using hk.symm)
  cases s
  · have hwj : w j = -w i := by
      have hk := hcoord i
      rw [omPlusRefl_apply_coord, if_pos rfl] at hk
      exact (by simpa using hk.symm)
    exact isDRootVec_of_neg_eigen_false hij' hzero hwj hw
  · have hwj : w j = w i := by
      have hk := hcoord i
      rw [omPlusRefl_apply_coord, if_pos rfl] at hk
      exact (neg_injective (by simpa using hk)).symm
    exact isDRootVec_of_neg_eigen_true hij' hzero hwj hw

private theorem coordHom_dTau {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (β : Additive ↥Bs ≃+ DVec 6) {ε : Bool} {a b : Fin 6}
    {ρ : MulAut ↥Bs} (hlin : ggLin (p := 3) β ρ = dTau 6 ε a b)
    {x' : OmPlusIdx Φ.r} (hx' : Φ.Acts ρ x') (v : DVec 6) :
    (fun i => Multiplicative.ofAdd (coordHom Φ β (dTau 6 ε a b v) i)) =
      omPlusRefl 3 x' (fun i => Multiplicative.ofAdd (coordHom Φ β v i)) := by
  have hb : bOf β (dTau 6 ε a b v) = ρ (bOf β v) := by
    apply Additive.ofMul.injective
    apply β.injective
    have hv : β (Additive.ofMul (bOf β v)) = v := beta_ofMul_bOf β v
    have hdv : dTau 6 ε a b v = β (Additive.ofMul (ρ (bOf β v))) := by
      calc dTau 6 ε a b v = ggLin (p := 3) β ρ v := by rw [hlin]
        _ = ggLin (p := 3) β ρ (β (Additive.ofMul (bOf β v))) := by rw [hv]
        _ = β (Additive.ofMul (ρ (bOf β v))) := ggLin_apply_ofMul β ρ (bOf β v)
    rw [beta_ofMul_bOf β (dTau 6 ε a b v)]
    exact hdv
  have hf : (Φ.β (bOf β v) : Φ.V ≃ₗ[Φ.F] Φ.V) =
      Φ.Δ.τ ((torusEquiv Φ).symm (betaA Φ β (bOf β v))) := by
    rw [torusEquiv_symm_apply]
    rfl
  have hact := hx' (bOf β v) ((torusEquiv Φ).symm (betaA Φ β (bOf β v))) hf
  rw [← hb] at hact
  have hspec := coordHom_spec Φ β (dTau 6 ε a b v)
  rw [← hspec] at hact
  have heq := Φ.Δ.τ_inj hact
  rw [← ofAddFun_coordHom Φ β v] at heq
  exact heq

private theorem isDRootVec_dRootAB {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (hF : Nat.card Φ.F = 2) (hZ : Subgroup.center ↥X = ⊥)
    (β : Additive ↥Bs ≃+ DVec 6) {i₀ : Fin 6}
    (hAe : dEvenStab 6 (Pi.single i₀ 1) ≤ (ggAutomizer X Bs).map (ggLin (p := 3) β))
    (ε : Bool) {a b : Fin 6} (ha : a ≠ i₀) (hb : b ≠ i₀) (hab : a ≠ b) :
    IsDRootVec (coordHom Φ β (dRootAB 6 ε a b)) := by
  have hZΩ : Subgroup.center ↥(orthDerived Φ.Q) = ⊥ :=
    center_orthDerived_eq_bot_of_center Φ hZ
  have hfix : dTau 6 ε a b (Pi.single i₀ (1 : ZMod 3)) =
      Pi.single i₀ (1 : ZMod 3) :=
    dTau_fix_single_of_ne ε ha.symm hb.symm
  have hmem : dTau 6 ε a b ∈ dEvenStab 6 (Pi.single i₀ 1) :=
    ⟨dTau_mem_dEven 6 ε hab, hfix⟩
  have hmem' : dTau 6 ε a b ∈ (ggAutomizer X Bs).map (ggLin (p := 3) β) := by
    exact hAe hmem
  obtain ⟨ρ, hρ, hρlin⟩ := Subgroup.mem_map.mp hmem'
  have hrefl : ggLin (p := 3) β ρ = Module.reflection (dFormAB_dRootAB 6 ε hab) := by
    rw [hρlin]
    ext v
    rw [dTau_apply_vec 6 ε hab v, Module.reflection_apply]
  have hr : GGIsReflection 3 ρ :=
    ggIsReflection_of_eq_reflection (p := 3) (by decide) β
      (x := dRootAB 6 ε a b) (f := dFormAB 6 ε a b) (dFormAB_dRootAB 6 ε hab) hrefl
  obtain ⟨x', hx'⟩ := qtwoOrth_exists_acts_core Φ hF hρ hr
  have hcompat := coordHom_dTau Φ β hρlin hx' (dRootAB 6 ε a b)
  have hdt : dTau 6 ε a b (dRootAB 6 ε a b) = -dRootAB 6 ε a b :=
    dTau_dRootAB 6 ε hab
  rw [hdt, map_neg] at hcompat
  rw [ofAddFun_neg] at hcompat
  have hne : coordHom Φ β (dRootAB 6 ε a b) ≠ 0 :=
    coordHom_ne_zero_of_mem_X Φ β hZΩ
      (bOf_dRootAB_mem_X Φ β hAe ε ha hb) (dRootAB_ne_zero 6 ε hab)
  exact isDRootVec_of_neg_eigen hne hcompat

private theorem exists_equiv_coordHom_single {Bs X : Subgroup G}
    (Φ : OrthFrameCore 3 Bs X) (hF : Nat.card Φ.F = 2)
    (hZ : Subgroup.center ↥X = ⊥) (β : Additive ↥Bs ≃+ DVec 6) {i₀ : Fin 6}
    {c : ZMod 3} (hc : c ≠ 0) {x : G} (hx : x ∈ Bs)
    (hxc : β (Additive.ofMul ⟨x, hx⟩) = c • Pi.single i₀ 1)
    (hxX : X ≤ Subgroup.centralizer ({x} : Set G))
    (hAe : dEvenStab 6 (Pi.single i₀ 1) ≤ (ggAutomizer X Bs).map (ggLin (p := 3) β)) :
    ∃ (π : ↥(Finset.univ.erase i₀) ≃ Fin Φ.r) (s : ↥(Finset.univ.erase i₀) → ZMod 3),
      (∀ i, s i = 1 ∨ s i = -1) ∧
        ∀ (i : ↥(Finset.univ.erase i₀)),
          coordHom Φ β (Pi.single (i : Fin 6) (1 : ZMod 3)) = Pi.single (π i) (s i) := by
  classical
  have hZΩ : Subgroup.center ↥(orthDerived Φ.Q) = ⊥ :=
    center_orthDerived_eq_bot_of_center Φ hZ
  have hMe : coordHom Φ β (Pi.single i₀ (1 : ZMod 3)) = 0 :=
    coordHom_single_i₀_eq_zero Φ β hZΩ hc hx hxc hxX
  have hrle : Φ.r ≤ 5 := rank_le_five Φ β hMe
  let u : ↥(Finset.univ.erase i₀) → Fin Φ.r → ZMod 3 :=
    fun a => coordHom Φ β (Pi.single (a : Fin 6) (1 : ZMod 3))
  have hroots : ∀ a b : ↥(Finset.univ.erase i₀), a ≠ b →
      IsDRootVec (u a + u b) ∧ IsDRootVec (u a - u b) := by
    intro a b hab
    have ha : (a : Fin 6) ≠ i₀ := (Finset.mem_erase.mp a.2).1
    have hb : (b : Fin 6) ≠ i₀ := (Finset.mem_erase.mp b.2).1
    have hab' : (a : Fin 6) ≠ (b : Fin 6) := fun h => hab (Subtype.ext h)
    constructor
    · have h := isDRootVec_dRootAB Φ hF hZ β hAe (ε := true) ha hb hab'
      rw [dRootAB_true, map_add] at h
      exact h
    · have h := isDRootVec_dRootAB Φ hF hZ β hAe (ε := false) ha hb hab'
      rw [dRootAB_false, map_sub] at h
      exact h
  have hι : Fintype.card ↥(Finset.univ.erase i₀) = 5 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ i₀)]
    simp
  have hκ : Fintype.card (Fin Φ.r) ≤ 5 := by simpa using hrle
  obtain ⟨π, s, hs, hsingle⟩ := exists_equiv_of_isDRootVec_add_sub hι hκ u hroots
  refine ⟨π, s, hs, ?_⟩
  intro i
  simpa [u] using hsingle i

theorem qtwoFarSix_align_of_frameCore {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (hF : Nat.card Φ.F = 2) (hZ : Subgroup.center ↥X = ⊥)
    (β : Additive ↥Bs ≃+ DVec 6) {i₀ : Fin 6} {c : ZMod 3} (hc : c ≠ 0) {x : G} (hx : x ∈ Bs)
    (hxc : β (Additive.ofMul ⟨x, hx⟩) = c • Pi.single i₀ 1)
    (hxX : X ≤ Subgroup.centralizer ({x} : Set G))
    (hAe : dEvenStab 6 (Pi.single i₀ 1) ≤ (ggAutomizer X Bs).map (ggLin (p := 3) β)) :
    ∃ (π : ↥(Finset.univ.erase i₀) ≃ Fin Φ.r) (s : ↥(Finset.univ.erase i₀) → ZMod 3),
      (∀ i, s i = 1 ∨ s i = -1) ∧ ∀ (i : ↥(Finset.univ.erase i₀)) (y : ↥(orthDerived Φ.Q)),
        (y : Φ.V ≃ₗ[Φ.F] Φ.V) = Φ.Δ.τ (Pi.mulSingle (π i) (Multiplicative.ofAdd (s i))) →
          Φ.ψ y = ((Additive.toMul (β.symm (Pi.single (i : Fin 6) 1)) : ↥Bs) : G) := by
  classical
  have hZΩ : Subgroup.center ↥(orthDerived Φ.Q) = ⊥ :=
    center_orthDerived_eq_bot_of_center Φ hZ
  obtain ⟨π, s, hs, hsingle⟩ :=
    exists_equiv_coordHom_single Φ hF hZ β hc hx hxc hxX hAe
  refine ⟨π, s, hs, ?_⟩
  intro i y hy
  have hi : (i : Fin 6) ≠ i₀ := (Finset.mem_erase.mp i.2).1
  have hmemX : ((bOf β (Pi.single (i : Fin 6) (1 : ZMod 3)) : ↥Bs) : G) ∈ X :=
    bOf_single_mem_X Φ β hi hAe
  have hpsi := psi_beta_of_mem_X Φ hZΩ hmemX
  have hτ : Φ.Δ.τ (Pi.mulSingle (π i) (Multiplicative.ofAdd (s i))) =
      (Φ.β (bOf β (Pi.single (i : Fin 6) (1 : ZMod 3))) : Φ.V ≃ₗ[Φ.F] Φ.V) := by
    have hui : coordHom Φ β (Pi.single (i : Fin 6) (1 : ZMod 3)) =
        Pi.single (π i) (s i) := hsingle i
    have hspec := coordHom_spec Φ β (Pi.single (i : Fin 6) (1 : ZMod 3))
    rw [hui] at hspec
    rw [ofAddFun_single] at hspec
    exact hspec
  have hy' : y = Φ.β (bOf β (Pi.single (i : Fin 6) (1 : ZMod 3))) := by
    apply Subtype.ext
    rw [hy, hτ]
  rw [hy']
  exact hpsi

end CFSG.StandardType.QTwo

end
