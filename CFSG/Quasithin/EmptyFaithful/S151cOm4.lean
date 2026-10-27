module

public import CFSG.Quasithin.EmptyFaithful.S152O4Facts
public import CFSG.Quasithin.Background.D2Z19

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {U : Type} [CommGroup U] [Finite U]

section S3Mod

@[expose] noncomputable def S3modCoord (a t : MulAut U) :
    ↥(fixV (Subgroup.zpowers t)) × ↥(fixV (Subgroup.zpowers t)) →* U :=
  (fixV (Subgroup.zpowers t)).subtype.coprod
    (a.toMonoidHom.comp (fixV (Subgroup.zpowers t)).subtype)

omit [Finite U] in
theorem S3modCoord_apply (a t : MulAut U)
    (p : ↥(fixV (Subgroup.zpowers t)) × ↥(fixV (Subgroup.zpowers t))) :
    S3modCoord a t p = (p.1 : U) * a (p.2 : U) := by
  simp [S3modCoord]

variable (hU : ∀ u : U, u ^ 2 = 1) (hcard : Nat.card U = 16) {a t : MulAut U}
  (ha3 : a ^ 3 = 1) (ht2 : t ^ 2 = 1) (hta : t * a * t⁻¹ = a⁻¹)
  (hfix : ∀ u : U, a u = u → u = 1)

omit [Finite U] in
include hU ha3 hfix in
theorem S3mod_a_sq (u : U) : (a ^ 2) u = u * a u := by
  have e1 : a ((a ^ 2) u) = u := by
    have h3 : a * a ^ 2 = 1 := by rw [← pow_succ']; exact ha3
    have := congrArg (fun g : MulAut U => g u) h3
    simpa using this
  have e2 : a (a u) = (a ^ 2) u := by rw [pow_two]; rfl
  have h1 : u * a u * (a ^ 2) u = 1 := by
    apply hfix
    rw [map_mul, map_mul, e1, e2]
    ac_rfl
  have h2 : (a ^ 2) u = (u * a u)⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [h2, inv_eq_self_of_sq_eq_one hU]

omit [Finite U] in
include ha3 hta in
theorem S3mod_t_a (u : U) : t (a u) = (a ^ 2) (t u) := by
  have h2 : a⁻¹ = a ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact ha3)
  have h1 : t * a = a⁻¹ * t := mul_inv_eq_iff_eq_mul.mp hta
  rw [h2] at h1
  have := congrArg (fun g : MulAut U => g u) h1
  simpa using this

omit [Finite U] in
include hU ha3 hfix in
theorem S3mod_a_coord (x y : U) : a (x * a y) = y * a (x * y) := by
  rw [map_mul, map_mul]
  have e2 : a (a y) = (a ^ 2) y := by rw [pow_two]; rfl
  rw [e2, S3mod_a_sq hU ha3 hfix y]
  ac_rfl

omit [Finite U] in
include hU ha3 hta hfix in
theorem S3mod_t_coord {x y : U} (hx : t x = x) (hy : t y = y) :
    t (x * a y) = (x * y) * a y := by
  rw [map_mul, hx, S3mod_t_a ha3 hta, hy, S3mod_a_sq hU ha3 hfix y]
  ac_rfl

omit [Finite U] in
include hU ha3 hta hfix in
theorem S3mod_coord_injective : Function.Injective (S3modCoord a t) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨x, y⟩ h
  rw [S3modCoord_apply] at h
  have hx : t (x : U) = x := mem_fixV_zpowers_iff.mp x.2
  have hy : t (y : U) = y := mem_fixV_zpowers_iff.mp y.2
  have h1 : (x : U) = a y := by
    have := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_self_of_sq_eq_one hU]
  have h2 : (x : U) = y * a y := by
    calc (x : U) = t x := hx.symm
      _ = t (a y) := by rw [h1]
      _ = (a ^ 2) (t y) := S3mod_t_a ha3 hta _
      _ = (a ^ 2) y := by rw [hy]
      _ = y * a y := S3mod_a_sq hU ha3 hfix y
  have hy1 : (y : U) = 1 := mul_eq_right.mp (h2.symm.trans h1)
  have hx1 : (x : U) = 1 := by rw [h1, hy1, map_one]
  exact Prod.ext (Subtype.ext hx1) (Subtype.ext hy1)

include hU hcard ht2 in
theorem S3mod_two_le_rk : 2 ≤ rk ↥(fixV (Subgroup.zpowers t)) := by
  have h1 := rk_commV_add_rk_fixV t
  have h2 := rk_mono (commV_zpowers_le_fixV hU ht2)
  have h3 : rk U = 4 := S152O4.rk_V_eq_four hcard
  omega

include hU hcard ha3 hta hfix in
theorem S3mod_rk_le_two : rk ↥(fixV (Subgroup.zpowers t)) ≤ 2 := by
  have hle := Nat.card_le_card_of_injective _ (S3mod_coord_injective hU ha3 hta hfix)
  rw [Nat.card_prod, hcard, card_eq_two_pow hU] at hle
  by_contra hr
  push Not at hr
  have h8 : 2 ^ 3 ≤ 2 ^ rk ↥(fixV (Subgroup.zpowers t)) := Nat.pow_le_pow_right (by norm_num) hr
  nlinarith

include hU hcard ha3 ht2 hta hfix in
theorem S3mod_rk_fixV_t_aux : rk ↥(fixV (Subgroup.zpowers t)) = 2 :=
  le_antisymm (S3mod_rk_le_two hU hcard ha3 hta hfix) (S3mod_two_le_rk hU hcard ht2)

include hU hcard ha3 ht2 hta hfix in
theorem S3mod_coord_bijective : Function.Bijective (S3modCoord a t) := by
  refine Function.Injective.bijective_of_nat_card_le (S3mod_coord_injective hU ha3 hta hfix) ?_
  rw [Nat.card_prod, hcard, card_eq_two_pow hU, S3mod_rk_fixV_t_aux hU hcard ha3 ht2 hta hfix]
  norm_num

end S3Mod

section S3ModMain

theorem S3mod_rk_fixV_t (hU : ∀ u : U, u ^ 2 = 1) (hcard : Nat.card U = 16) {a t : MulAut U}
    (ha3 : a ^ 3 = 1) (_ha1 : a ≠ 1) (ht2 : t ^ 2 = 1) (_ht1 : t ≠ 1) (hta : t * a * t⁻¹ = a⁻¹)
    (hfix : ∀ u : U, a u = u → u = 1) : rk (fixV (Subgroup.zpowers t)) = 2 :=
  S3mod_rk_fixV_t_aux hU hcard ha3 ht2 hta hfix

theorem S3mod_eq_top_of_invariant (hU : ∀ u : U, u ^ 2 = 1) (hcard : Nat.card U = 16)
    {a t : MulAut U} (ha3 : a ^ 3 = 1) (_ha1 : a ≠ 1) (ht2 : t ^ 2 = 1) (_ht1 : t ≠ 1)
    (hta : t * a * t⁻¹ = a⁻¹) (hfix : ∀ u : U, a u = u → u = 1) {B : Subgroup U}
    (hBa : ∀ b ∈ B, a b ∈ B) (_hBt : ∀ b ∈ B, t b ∈ B) (hle : fixV (Subgroup.zpowers t) ≤ B) :
    B = ⊤ := by
  refine eq_top_iff.mpr fun u _ => ?_
  obtain ⟨⟨x, y⟩, rfl⟩ := (S3mod_coord_bijective hU hcard ha3 ht2 hta hfix).2 u
  rw [S3modCoord_apply]
  exact B.mul_mem (hle x.2) (hBa _ (hle y.2))

theorem S3mod_eq_one_of_commute (hU : ∀ u : U, u ^ 2 = 1) (hcard : Nat.card U = 16)
    {a t : MulAut U} (ha3 : a ^ 3 = 1) (_ha1 : a ≠ 1) (ht2 : t ^ 2 = 1) (_ht1 : t ≠ 1)
    (hta : t * a * t⁻¹ = a⁻¹) (hfix : ∀ u : U, a u = u → u = 1) {c : MulAut U}
    (hca : c * a = a * c) (_hct : c * t = t * c)
    (hc : ∀ u ∈ fixV (Subgroup.zpowers t), c u = u) : c = 1 := by
  ext u
  obtain ⟨⟨x, y⟩, rfl⟩ := (S3mod_coord_bijective hU hcard ha3 ht2 hta hfix).2 u
  rw [S3modCoord_apply]
  have hca' : c (a (y : U)) = a (c (y : U)) := by
    have := congrArg (fun g : MulAut U => g (y : U)) hca
    simpa using this
  rw [map_mul, hca', hc _ x.2, hc _ y.2]
  rfl

omit [Finite U] in
theorem S3modCoord_a (hU : ∀ u : U, u ^ 2 = 1) {a t : MulAut U} (ha3 : a ^ 3 = 1)
    (hfix : ∀ u : U, a u = u → u = 1)
    (p : ↥(fixV (Subgroup.zpowers t)) × ↥(fixV (Subgroup.zpowers t))) :
    a (S3modCoord a t p) = S3modCoord a t (p.2, p.1 * p.2) := by
  rw [S3modCoord_apply, S3modCoord_apply]
  exact S3mod_a_coord hU ha3 hfix _ _

omit [Finite U] in
theorem S3modCoord_t (hU : ∀ u : U, u ^ 2 = 1) {a t : MulAut U} (ha3 : a ^ 3 = 1)
    (hta : t * a * t⁻¹ = a⁻¹) (hfix : ∀ u : U, a u = u → u = 1)
    (p : ↥(fixV (Subgroup.zpowers t)) × ↥(fixV (Subgroup.zpowers t))) :
    t (S3modCoord a t p) = S3modCoord a t (p.1 * p.2, p.2) := by
  rw [S3modCoord_apply, S3modCoord_apply]
  exact S3mod_t_coord hU ha3 hta hfix (mem_fixV_zpowers_iff.mp p.1.2)
    (mem_fixV_zpowers_iff.mp p.2.2)

private noncomputable def s3Ext {a t : MulAut U} (hbij : Function.Bijective (S3modCoord a t))
    (φ : MulAut ↥(fixV (Subgroup.zpowers t))) : MulAut U :=
  (MulEquiv.ofBijective (S3modCoord a t) hbij).symm.trans
    ((MulEquiv.prodCongr φ φ).trans (MulEquiv.ofBijective (S3modCoord a t) hbij))

omit [Finite U] in
private theorem s3Ext_apply {a t : MulAut U} (hbij : Function.Bijective (S3modCoord a t))
    (φ : MulAut ↥(fixV (Subgroup.zpowers t)))
    (p : ↥(fixV (Subgroup.zpowers t)) × ↥(fixV (Subgroup.zpowers t))) :
    s3Ext hbij φ (S3modCoord a t p) = S3modCoord a t (φ p.1, φ p.2) := by
  have h : (MulEquiv.ofBijective (S3modCoord a t) hbij).symm (S3modCoord a t p) = p :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  simp only [s3Ext, MulEquiv.trans_apply, h]
  rfl

theorem S3mod_card_centralizer (hU : ∀ u : U, u ^ 2 = 1) (hcard : Nat.card U = 16)
    {a t : MulAut U} (ha3 : a ^ 3 = 1) (_ha1 : a ≠ 1) (ht2 : t ^ 2 = 1) (_ht1 : t ≠ 1)
    (hta : t * a * t⁻¹ = a⁻¹) (hfix : ∀ u : U, a u = u → u = 1) :
    Nat.card (Subgroup.centralizer ({a, t} : Set (MulAut U))) = 6 := by
  have hbij := S3mod_coord_bijective hU hcard ha3 ht2 hta hfix
  have hrk : rk ↥(fixV (Subgroup.zpowers t)) = 2 := S3mod_rk_fixV_t_aux hU hcard ha3 ht2 hta hfix
  have hV0sq : ∀ v : ↥(fixV (Subgroup.zpowers t)), v ^ 2 = 1 := fun v => Subtype.ext (hU v)
  have hCle : Subgroup.centralizer ({a, t} : Set (MulAut U)) ≤
      stabSub (fixV (Subgroup.zpowers t)) := by
    intro c hc u
    have hct : t * c = c * t := Subgroup.mem_centralizer_iff.mp hc t (by simp)
    have key : t (c u) = c (t u) := by
      have := congrArg (fun g : MulAut U => g u) hct
      simpa using this
    rw [mem_fixV_zpowers_iff, mem_fixV_zpowers_iff, key]
    exact c.injective.eq_iff
  let f : ↥(Subgroup.centralizer ({a, t} : Set (MulAut U))) →*
      MulAut ↥(fixV (Subgroup.zpowers t)) :=
    (resHom (fixV (Subgroup.zpowers t))).comp (Subgroup.inclusion hCle)
  have hfapply : ∀ c v, ((f c v : ↥(fixV (Subgroup.zpowers t))) : U) = (c : MulAut U) (v : U) :=
    fun c v => rfl
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_one]
      intro c hc1
      have hca : (c : MulAut U) * a = a * c :=
        (Subgroup.mem_centralizer_iff.mp c.2 a (by simp)).symm
      have hct : (c : MulAut U) * t = t * c :=
        (Subgroup.mem_centralizer_iff.mp c.2 t (by simp)).symm
      refine Subtype.ext (S3mod_eq_one_of_commute hU hcard ha3 _ha1 ht2 _ht1 hta hfix hca hct ?_)
      intro u hu
      have := congrArg (fun φ : MulAut ↥(fixV (Subgroup.zpowers t)) =>
        ((φ ⟨u, hu⟩ : ↥(fixV (Subgroup.zpowers t))) : U)) hc1
      simpa [hfapply] using this
    · intro φ
      have hmem : s3Ext hbij φ ∈ Subgroup.centralizer ({a, t} : Set (MulAut U)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
        rcases hh with rfl | rfl
        · ext u
          obtain ⟨p, rfl⟩ := hbij.2 u
          simp only [MulAut.mul_apply]
          rw [s3Ext_apply, S3modCoord_a hU ha3 hfix, S3modCoord_a hU ha3 hfix, s3Ext_apply,
            map_mul]
        · ext u
          obtain ⟨p, rfl⟩ := hbij.2 u
          simp only [MulAut.mul_apply]
          rw [s3Ext_apply, S3modCoord_t hU ha3 hta hfix, S3modCoord_t hU ha3 hta hfix,
            s3Ext_apply, map_mul]
      refine ⟨⟨s3Ext hbij φ, hmem⟩, ?_⟩
      ext v
      rw [hfapply]
      have hv : (v : U) = S3modCoord a t (v, 1) := by
        rw [S3modCoord_apply]
        simp
      show s3Ext hbij φ (v : U) = _
      rw [hv, s3Ext_apply, S3modCoord_apply]
      simp
  rw [Nat.card_congr (Equiv.ofBijective f hf), card_mulAut_of_rk_two hV0sq hrk]

end S3ModMain

namespace S151cOm4

open S152O4 CFSG.Quasithin.S1417

theorem detQ_isQuadratic : IsQuadraticFormOn detQ := by
  unfold IsQuadraticFormOn quadPolar
  decide +kernel

theorem detQ_nondeg : IsNondegQuadratic detQ := by
  unfold IsNondegQuadratic quadPolar
  decide +kernel

@[expose] def eVecCode (p : F2sq × F2sq) : ℕ :=
  let x0 := (Multiplicative.toAdd p.1 0).val
  let x1 := (Multiplicative.toAdd p.1 1).val
  let y0 := (Multiplicative.toAdd p.2 0).val
  let y1 := (Multiplicative.toAdd p.2 1).val
  (x0 + y0) % 2 + 2 * ((x1 + y1) % 2) + 4 * x0 + 8 * x1

@[expose] def eVecFun (p : F2sq × F2sq) : Vec := Vec.mk (eVecCode p)

theorem eVecFun_mul : ∀ p q : F2sq × F2sq, eVecFun (p * q) = eVecFun p * eVecFun q := by
  decide +kernel

theorem eVecFun_injective : Function.Injective eVecFun := by decide +kernel

@[expose] noncomputable def eVec : F2sq × F2sq ≃* Vec :=
  MulEquiv.ofBijective (MonoidHom.mk' eVecFun eVecFun_mul)
    (Function.Injective.bijective_of_nat_card_le eVecFun_injective
      (by rw [card_Vec, card_F2sq_prod]))

theorem eVec_apply (p : F2sq × F2sq) : eVec p = eVecFun p := rfl

theorem act_r_eVec : ∀ x y : F2sq,
    act (DihedralGroup.r 1, 1) (eVecFun (x, y)) = eVecFun (y, x * y) := by
  decide +kernel

theorem act_sr_eVec : ∀ x y : F2sq,
    act (DihedralGroup.sr 0, 1) (eVecFun (x, y)) = eVecFun (x * y, y) := by
  decide +kernel

theorem detQ_eVec_inl : ∀ x : F2sq, detQ (eVecFun (x, 1)) = 0 := by decide +kernel

noncomputable def vecW : Subgroup Vec :=
  (eVec.toMonoidHom.comp (MonoidHom.inl F2sq F2sq)).range

theorem detQ_plus : IsPlusType detQ := by
  refine ⟨vecW, ?_, ?_⟩
  · have hinj : Function.Injective (eVec.toMonoidHom.comp (MonoidHom.inl F2sq F2sq)) :=
      eVec.injective.comp (fun a b h => congrArg Prod.fst h)
    rw [vecW, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_F2sq]
  · rintro _ ⟨x, rfl⟩
    exact detQ_eVec_inl x

theorem trans_trans : ∀ m : Vec, transV (transV m) = m := by decide +kernel

theorem card_fix_trans_mul : ∀ γ : Gam, Fintype.card {m : Vec // act γ (transV m) = m} = 2 ∨
    Fintype.card {m : Vec // act γ (transV m) = m} = 8 := by
  decide +kernel

section Range

variable {U : Type} [CommGroup U] [Finite U]

omit [Finite U] in
theorem exp_of_equiv (c : U ≃* Vec) : ∀ w : U, w ^ 2 = 1 := fun w =>
  c.injective (by rw [map_pow, map_one, pow_two]; exact Vec.mul_self_eq_one _)

omit [Finite U] in
theorem card_of_equiv (c : U ≃* Vec) : Nat.card U = 16 :=
  (Nat.card_congr c.toEquiv).trans card_Vec

theorem rhoV_even_rk (c : U ≃* Vec) (γ : Gam) :
    Even (rk (commV (Subgroup.zpowers (rhoV c γ)))) := by
  apply even_rk_comm_of_card (exp_of_equiv c) (card_of_equiv c)
  have := card_fixV_conjBack c (rho γ)
  change Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho γ)))) = _ at this
  change Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho γ)))) = 1 ∨
    Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho γ)))) = 4 ∨
    Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho γ)))) = 16
  rw [this]
  exact nat_card_fix γ

theorem not_even_rk_rhoV_mul (c : U ≃* Vec) (γ : Gam) :
    ¬ Even (rk (commV (Subgroup.zpowers (rhoV c γ * conjBack c transV)))) := by
  have hmul : rhoV c γ * conjBack c transV = conjBack c (rho γ * transV) :=
    (conjBack_mul c (rho γ) transV).symm
  rw [hmul]
  have hsum := rk_commV_add_rk_fixV (conjBack c (rho γ * transV))
  rw [rk_V_eq_four (card_of_equiv c)] at hsum
  have hfix := card_fixV_conjBack c (rho γ * transV)
  have h28 : Nat.card {m : Vec // (rho γ * transV) m = m} = 2 ∨
      Nat.card {m : Vec // (rho γ * transV) m = m} = 8 := by
    simp only [Nat.card_eq_fintype_card]
    exact card_fix_trans_mul γ
  rw [Nat.even_iff]
  rcases h28 with h | h
  · have := S152O.rk_eq_of_card_eq (exp_of_equiv c) (n := 1)
      (H := fixV (Subgroup.zpowers (conjBack c (rho γ * transV)))) (by rw [hfix, h]; rfl)
    omega
  · have := S152O.rk_eq_of_card_eq (exp_of_equiv c) (n := 3)
      (H := fixV (Subgroup.zpowers (conjBack c (rho γ * transV)))) (by rw [hfix, h]; rfl)
    omega

theorem isOmegaFourPlus_range (c : U ≃* Vec) : IsOmegaFourPlus (rhoV c).range := by
  have hcard : Nat.card U = 16 := card_of_equiv c
  have hexp' : ∀ w : U, w ^ 2 = 1 := exp_of_equiv c
  have hexp : ∀ w : U, w * w = 1 := fun w => by rw [← pow_two]; exact hexp' w
  have hq1 : IsQuadraticFormOn (fun v => detQ (c v)) := isQuadratic_comp c detQ_isQuadratic
  have hq2 : IsNondegQuadratic (fun v => detQ (c v)) := isNondeg_comp c detQ_nondeg
  have hq3 : IsPlusType (fun v => detQ (c v)) := isPlus_comp c detQ_plus
  have hR : (rhoV c).range ≤ orthogonalGroupOf (fun v => detQ (c v)) := by
    rintro _ ⟨γ, rfl⟩ v
    show detQ (c (rhoV c γ v)) = detQ (c v)
    rw [rhoV_apply, detQ_act]
  refine ⟨hcard, fun v => detQ (c v), hq1, hq2, hq3, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · obtain ⟨γ, rfl⟩ := hg
    exact ⟨hR ⟨γ, rfl⟩, rhoV_even_rk c γ⟩
  · obtain ⟨hgO, hgE⟩ := hg
    by_contra hgR
    obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hcard hq1 hq2 hq3
    have hO72 : Nat.card (orthogonalGroupOf (fun v => detQ (c v))) = 72 := hS.card_X
    have hR36 : Nat.card (rhoV c).range = 36 := card_eq_36 c rfl
    set g₀ : MulAut U := conjBack c transV with hg₀
    have hg₀O : g₀ ∈ orthogonalGroupOf (fun v => detQ (c v)) := by
      intro v
      show detQ (c (conjBack c transV v)) = detQ (c v)
      rw [conjBack_apply, detQ_trans]
    have hg₀sq : g₀ * g₀ = 1 := by
      rw [hg₀, ← conjBack_mul]
      have : transV * transV = 1 := by
        ext m
        exact trans_trans m
      rw [this, conjBack_one]
    have hg₀inv : g₀⁻¹ = g₀ := inv_eq_of_mul_eq_one_right hg₀sq
    have hidx : ((rhoV c).range.subgroupOf
        (orthogonalGroupOf (fun v => detQ (c v)))).index = 2 := by
      have h := Subgroup.relIndex_mul_card (rhoV c).range
        (orthogonalGroupOf (fun v => detQ (c v)))
      rw [inf_eq_left.mpr hR, hR36, hO72] at h
      have h2 : (rhoV c).range.relIndex (orthogonalGroupOf (fun v => detQ (c v))) = 2 := by omega
      exact h2
    obtain ⟨a₀, ha₀⟩ := Subgroup.index_eq_two_iff.mp hidx
    have hg₀R : g₀ ∉ (rhoV c).range := by
      rintro ⟨γ, hγ⟩
      have hodd : ¬ Even (rk (commV (Subgroup.zpowers g₀))) := by
        have := not_even_rk_rhoV_mul c 1
        rwa [map_one, one_mul] at this
      apply hodd
      rw [← hγ]
      exact rhoV_even_rk c γ
    have h1 := ha₀ ⟨g, hgO⟩
    have h2 := ha₀ ⟨g₀, hg₀O⟩
    have hgR' : (⟨g, hgO⟩ : ↥(orthogonalGroupOf (fun v => detQ (c v)))) ∉
        (rhoV c).range.subgroupOf (orthogonalGroupOf (fun v => detQ (c v))) := hgR
    have hg₀R' : (⟨g₀, hg₀O⟩ : ↥(orthogonalGroupOf (fun v => detQ (c v)))) ∉
        (rhoV c).range.subgroupOf (orthogonalGroupOf (fun v => detQ (c v))) := hg₀R
    have h1' : (⟨g, hgO⟩ * a₀ : ↥(orthogonalGroupOf (fun v => detQ (c v)))) ∈
        (rhoV c).range.subgroupOf (orthogonalGroupOf (fun v => detQ (c v))) := by
      rcases h1 with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hgR'
    have h2' : (⟨g₀, hg₀O⟩ * a₀ : ↥(orthogonalGroupOf (fun v => detQ (c v)))) ∈
        (rhoV c).range.subgroupOf (orthogonalGroupOf (fun v => detQ (c v))) := by
      rcases h2 with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hg₀R'
    have h1'' : g * (a₀ : MulAut U) ∈ (rhoV c).range := h1'
    have h2'' : g₀ * (a₀ : MulAut U) ∈ (rhoV c).range := h2'
    have h3 : g * g₀⁻¹ ∈ (rhoV c).range := by
      have := Subgroup.mul_mem _ h1'' (Subgroup.inv_mem _ h2'')
      have e : g * (a₀ : MulAut U) * (g₀ * (a₀ : MulAut U))⁻¹ = g * g₀⁻¹ := by group
      rwa [e] at this
    obtain ⟨γ, hγ⟩ := h3
    have hgeq : g = rhoV c γ * g₀ := by
      rw [hγ, hg₀inv, mul_assoc, hg₀sq, mul_one]
    apply not_even_rk_rhoV_mul c γ
    rw [← hgeq]
    exact hgE

end Range

theorem card_fix_inv : ∀ β : Gam, β ^ 2 = 1 → β ≠ 1 →
    Fintype.card {m : Vec // act β m = m} = 4 := by
  decide +kernel

theorem card_fix_klein : ∀ β β' : Gam, β ^ 2 = 1 → β' ^ 2 = 1 → β ≠ 1 → β' ≠ 1 → β ≠ β' →
    β * β' = β' * β → Fintype.card {m : Vec // act β m = m ∧ act β' m = m} = 2 := by
  decide +kernel

theorem rk_eq_of_card_eq_pow {G : Type*} [Group G] {H : Subgroup G} {n : ℕ}
    (h : Nat.card H = 2 ^ n) : rk H = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rk
  rw [h, padicValNat.prime_pow]

section Qhat

variable {U : Type} [CommGroup U] [Finite U]

omit [Finite U] in
theorem rhoV_apply_eq_iff (c : U ≃* Vec) (γ : Gam) (v : U) :
    rhoV c γ v = v ↔ act γ (c v) = c v := by
  constructor
  · intro h
    have := rhoV_apply c γ v
    rw [h] at this
    exact this.symm
  · intro h
    apply c.injective
    rw [rhoV_apply]
    exact h

theorem card_two_or_four (c : U ≃* Vec) {A : Subgroup (MulAut U)}
    (hA : IsA2 (rhoV c).range A) : Nat.card A = 2 ∨ Nat.card A = 4 := by
  have hdvd : Nat.card A ∣ 36 := by
    have := Subgroup.card_dvd_of_le hA.le
    rwa [card_eq_36 c rfl] at this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hA.isElemAbelian2.isPGroup
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hA.ne_bot (Subgroup.card_eq_one.mp (by simpa using hk))
  have hk2 : k ≤ 2 := by
    by_contra h
    push Not at h
    have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 h
    rw [← hk] at h8
    have := h8.trans hdvd
    omega
  interval_cases k
  · omega
  · left; simpa using hk
  · right; simpa using hk

theorem rAV_of_card_two (c : U ≃* Vec) {A : Subgroup (MulAut U)}
    (hA : IsA2 (rhoV c).range A) (h2 : Nat.card A = 2) : rAV A = 2 := by
  obtain ⟨b, hbA, hb1, hbb, rfl⟩ := exists_eq_zpowers_of_card_two h2
  obtain ⟨β, rfl⟩ := exists_rhoV_eq c rfl (hA.le hbA)
  have hβ1 : β ≠ 1 := fun h => hb1 (by rw [h, map_one])
  have hβ2 : β ^ 2 = 1 := rhoV_injective c (by rw [map_pow, map_one, pow_two]; exact hbb)
  have hfix : Nat.card ↥(fixV (Subgroup.zpowers (rhoV c β))) = 4 := by
    have := card_fixV_conjBack c (rho β)
    change Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho β)))) = _ at this
    change Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho β)))) = 4
    rw [this]
    simp only [Nat.card_eq_fintype_card]
    exact card_fix_inv β hβ2 hβ1
  have hrkA : rk ↥(Subgroup.zpowers (rhoV c β)) = 1 :=
    rk_eq_of_card_eq_pow (n := 1) (by rw [h2]; rfl)
  have hrkF : rk ↥(fixV (Subgroup.zpowers (rhoV c β))) = 2 :=
    S152O.rk_eq_of_card_eq (exp_of_equiv c) (n := 2) (by rw [hfix]; rfl)
  have hsum := rk_add_rkIdx (fixV (Subgroup.zpowers (rhoV c β)))
  rw [rk_V_eq_four (card_of_equiv c), hrkF] at hsum
  have hidx : rkIdx (fixV (Subgroup.zpowers (rhoV c β))) = 2 := by omega
  unfold rAV
  rw [hidx, hrkA]
  norm_num

theorem rAV_of_card_four (c : U ≃* Vec) {A : Subgroup (MulAut U)}
    (hA : IsA2 (rhoV c).range A) (h4 : Nat.card A = 4) : rAV A = 3 / 2 := by
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hA.isElemAbelian2.2 x hx
  obtain ⟨s, hsA, s', hs'A, hs1, hs'1, hss', hcomm, hall⟩ := exists_klein_elements h4 hsq
  obtain ⟨β, rfl⟩ := exists_rhoV_eq c rfl (hA.le hsA)
  obtain ⟨β', rfl⟩ := exists_rhoV_eq c rfl (hA.le hs'A)
  have hβ2 : β ^ 2 = 1 := rhoV_injective c (by rw [map_pow, map_one, pow_two]; exact hsq _ hsA)
  have hβ'2 : β' ^ 2 = 1 := rhoV_injective c (by rw [map_pow, map_one, pow_two]; exact hsq _ hs'A)
  have hβ1 : β ≠ 1 := fun h => hs1 (by rw [h, map_one])
  have hβ'1 : β' ≠ 1 := fun h => hs'1 (by rw [h, map_one])
  have hββ' : β ≠ β' := fun h => hss' (by rw [h])
  have hcomm' : β * β' = β' * β := rhoV_injective c (by rw [map_mul, map_mul]; exact hcomm)
  have hfixA : ∀ v : U, v ∈ fixV A ↔ rhoV c β v = v ∧ rhoV c β' v = v := by
    intro v
    constructor
    · intro hv
      exact ⟨hv _ hsA, hv _ hs'A⟩
    · rintro ⟨h1, h2⟩ x hx
      rcases hall x hx with rfl | rfl | rfl | rfl
      · rfl
      · exact h1
      · exact h2
      · rw [MulAut.mul_apply, h2, h1]
  have hcardfix : Nat.card ↥(fixV A) = 2 := by
    have : Nat.card ↥(fixV A) = Nat.card {m : Vec // act β m = m ∧ act β' m = m} :=
      Nat.card_congr (Equiv.subtypeEquiv c.toEquiv (fun v => by
        rw [hfixA, rhoV_apply_eq_iff, rhoV_apply_eq_iff]
        rfl))
    rw [this]
    simp only [Nat.card_eq_fintype_card]
    exact card_fix_klein β β' hβ2 hβ'2 hβ1 hβ'1 hββ' hcomm'
  have hrkA : rk ↥A = 2 := rk_eq_of_card_eq_pow (n := 2) (by rw [h4]; rfl)
  have hrkF : rk ↥(fixV A) = 1 :=
    S152O.rk_eq_of_card_eq (exp_of_equiv c) (n := 1) (by rw [hcardfix]; rfl)
  have hsum := rk_add_rkIdx (fixV A)
  rw [rk_V_eq_four (card_of_equiv c), hrkF] at hsum
  have hidx : rkIdx (fixV A) = 3 := by omega
  unfold rAV
  rw [hidx, hrkA]
  norm_num

omit [Finite U] in
theorem exists_klein_of_rhoV (c : U ≃* Vec) {β β' : Gam} (hβ2 : β ^ 2 = 1) (hβ'2 : β' ^ 2 = 1)
    (hβ1 : β ≠ 1) (hβ'1 : β' ≠ 1) (hne : β ≠ β') (hcomm : β * β' = β' * β) :
    ∃ A : Subgroup (MulAut U), IsA2 (rhoV c).range A ∧ Nat.card A = 4 ∧ rhoV c β ∈ A ∧
      rhoV c β' ∈ A := by
  have htt : rhoV c β * rhoV c β = 1 := by rw [← map_mul, ← pow_two, hβ2, map_one]
  have hww : rhoV c β' * rhoV c β' = 1 := by rw [← map_mul, ← pow_two, hβ'2, map_one]
  have hwt : rhoV c β' * rhoV c β = rhoV c β * rhoV c β' := by
    rw [← map_mul, ← map_mul, hcomm]
  have ht1 : rhoV c β ≠ 1 := fun h => hβ1 (rhoV_injective c (by rw [h, map_one]))
  have hw1 : rhoV c β' ≠ 1 := fun h => hβ'1 (rhoV_injective c (by rw [h, map_one]))
  have htw : rhoV c β ≠ rhoV c β' := fun h => hne (rhoV_injective c h)
  refine ⟨klein (rhoV c β) (rhoV c β') htt hww hwt, ⟨?_, ?_, klein_isElemAbelian2 htt hww hwt⟩,
    card_klein htt hww hwt ht1 hw1 htw, mem_klein.mpr (Or.inr (Or.inl rfl)),
    mem_klein.mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
  · intro x hx
    rcases mem_klein.mp hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨β, rfl⟩
    · exact ⟨β', rfl⟩
    · exact Subgroup.mul_mem _ ⟨β, rfl⟩ ⟨β', rfl⟩
  · intro h
    have : rhoV c β ∈ klein (rhoV c β) (rhoV c β') htt hww hwt :=
      mem_klein.mpr (Or.inr (Or.inl rfl))
    rw [h] at this
    exact ht1 (Subgroup.mem_bot.mp this)

theorem qhat_range (c : U ≃* Vec) : qhatOf (rhoV c).range = ((3 / 2 : ℚ) : WithTop ℚ) := by
  show kq _ 3 = _
  rw [kq_eq_coe_iff]
  refine ⟨?_, ?_⟩
  · obtain ⟨A, hA, h4, -⟩ := exists_klein_of_rhoV c (β := (DihedralGroup.sr 0, 1))
      (β' := (1, DihedralGroup.sr 0)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    exact ⟨A, hA, commSeries_three_eq_bot_of_card_four (exp_of_equiv c) hA.isElemAbelian2 h4,
      rAV_of_card_four c hA h4⟩
  · intro A hA _
    rcases card_two_or_four c hA with h2 | h4
    · rw [rAV_of_card_two c hA h2]
      norm_num
    · rw [rAV_of_card_four c hA h4]

theorem mem_QhatStar_range_iff (c : U ≃* Vec) {A : Subgroup (MulAut U)} :
    A ∈ QhatStar (rhoV c).range ↔ IsA2 (rhoV c).range A ∧ Nat.card A = 4 := by
  constructor
  · rintro ⟨r, hr, -, ⟨⟨hA2, hAr⟩, -⟩, -⟩
    rw [qhat_range c] at hr
    have hr' : r = 3 / 2 := (WithTop.coe_injective hr).symm
    subst hr'
    refine ⟨hA2, ?_⟩
    rcases card_two_or_four c hA2 with h2 | h4
    · exfalso
      rw [rAV_of_card_two c hA2 h2] at hAr
      norm_num at hAr
    · exact h4
  · rintro ⟨hA2, h4⟩
    refine ⟨3 / 2, qhat_range c, by norm_num, ⟨⟨hA2, (rAV_of_card_four c hA2 h4).le⟩,
      commSeries_three_eq_bot_of_card_four (exp_of_equiv c) hA2.isElemAbelian2 h4⟩, ?_⟩
    rintro B ⟨⟨hB2, hBr⟩, -⟩ hBA
    rcases card_two_or_four c hB2 with h2 | h4'
    · exfalso
      rw [rAV_of_card_two c hB2 h2] at hBr
      norm_num at hBr
    · exact Subgroup.eq_of_le_of_card_ge hBA (by rw [h4, h4'])

theorem Jhat_range (c : U ≃* Vec) : Jhat (rhoV c).range = (rhoV c).range := by
  apply le_antisymm
  · exact iSup₂_le fun A hA => ((mem_QhatStar_range_iff c).mp hA).1.le
  · have hP : ∀ β β' : Gam, β ^ 2 = 1 → β' ^ 2 = 1 → β ≠ 1 → β' ≠ 1 → β ≠ β' →
        β * β' = β' * β → rhoV c β ∈ Jhat (rhoV c).range := by
      intro β β' h2 h2' h1 h1' hne hcomm
      obtain ⟨A, hA, h4, hβA, -⟩ := exists_klein_of_rhoV c h2 h2' h1 h1' hne hcomm
      exact (le_iSup₂_of_le A ((mem_QhatStar_range_iff c).mpr ⟨hA, h4⟩) le_rfl : A ≤ _) hβA
    have hfst : ∀ i : ZMod 3, rhoV c (DihedralGroup.sr i, 1) ∈ Jhat (rhoV c).range := by
      intro i
      refine hP (DihedralGroup.sr i, 1) (1, DihedralGroup.sr 0) ?_ ?_ ?_ ?_ ?_ ?_
      all_goals revert i; decide
    have hsnd : ∀ i : ZMod 3, rhoV c (1, DihedralGroup.sr i) ∈ Jhat (rhoV c).range := by
      intro i
      refine hP (1, DihedralGroup.sr i) (DihedralGroup.sr 0, 1) ?_ ?_ ?_ ?_ ?_ ?_
      all_goals revert i; decide
    have hgen : ∀ g : DihedralGroup 3, g = 1 ∨ (∃ i : ZMod 3, g = DihedralGroup.sr i) ∨
        ∃ i j : ZMod 3, g = DihedralGroup.sr i * DihedralGroup.sr j := by decide
    have hJ1 : ∀ g : DihedralGroup 3, rhoV c (g, 1) ∈ Jhat (rhoV c).range := by
      intro g
      rcases hgen g with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
      · rw [show ((1 : DihedralGroup 3), (1 : DihedralGroup 3)) = 1 from rfl, map_one]
        exact Subgroup.one_mem _
      · exact hfst i
      · have : ((DihedralGroup.sr i * DihedralGroup.sr j, 1) : Gam) =
            (DihedralGroup.sr i, 1) * (DihedralGroup.sr j, 1) := by simp
        rw [this, map_mul]
        exact Subgroup.mul_mem _ (hfst i) (hfst j)
    have hJ2 : ∀ g : DihedralGroup 3, rhoV c (1, g) ∈ Jhat (rhoV c).range := by
      intro g
      rcases hgen g with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
      · rw [show ((1 : DihedralGroup 3), (1 : DihedralGroup 3)) = 1 from rfl, map_one]
        exact Subgroup.one_mem _
      · exact hsnd i
      · have : ((1, DihedralGroup.sr i * DihedralGroup.sr j) : Gam) =
            (1, DihedralGroup.sr i) * (1, DihedralGroup.sr j) := by simp
        rw [this, map_mul]
        exact Subgroup.mul_mem _ (hsnd i) (hsnd j)
    rintro _ ⟨⟨g, h⟩, rfl⟩
    have : ((g, h) : Gam) = (g, 1) * (1, h) := by simp
    rw [this, map_mul]
    exact Subgroup.mul_mem _ (hJ1 g) (hJ2 h)

end Qhat

section Transvection

variable {U : Type} [CommGroup U] [Finite U]

theorem detQ_eq_one_iff : ∀ m : Vec, detQ m = 1 ↔ Fintype.card {γ : Gam // act γ m = m} = 6 := by
  decide +kernel

theorem zmod_two_eq_of_iff : ∀ x y : ZMod 2, (x = 1 ↔ y = 1) → x = y := by decide

omit [Finite U] in
theorem card_stab_range (c : U ≃* Vec) (u : U) :
    Nat.card {j : ↥(rhoV c).range // (j : MulAut U) u = u} =
      Nat.card {γ : Gam // act γ (c u) = c u} := by
  have hf : Function.Bijective (fun γ : {γ : Gam // act γ (c u) = c u} =>
      (⟨⟨rhoV c γ.1, γ.1, rfl⟩, (rhoV_apply_eq_iff c γ.1 u).mpr γ.2⟩ :
        {j : ↥(rhoV c).range // (j : MulAut U) u = u})) := by
    constructor
    · intro γ δ h
      have h1 := congrArg (fun j : {j : ↥(rhoV c).range // (j : MulAut U) u = u} =>
        (j.1 : MulAut U)) h
      exact Subtype.ext (rhoV_injective c h1)
    · rintro ⟨⟨x, γ, hγ⟩, hj⟩
      subst hγ
      exact ⟨⟨γ, (rhoV_apply_eq_iff c γ u).mp hj⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hf)).symm

omit [Finite U] in
theorem inv_apply_apply' (g : MulAut U) (u : U) : g⁻¹ (g u) = u := by
  simp

theorem card_stab_le {J : Subgroup (MulAut U)} {g : MulAut U}
    (hg : ∀ j ∈ J, g * j * g⁻¹ ∈ J) (u : U) :
    Nat.card {j : ↥J // (j : MulAut U) u = u} ≤
      Nat.card {j : ↥J // (j : MulAut U) (g u) = g u} := by
  refine Nat.card_le_card_of_injective
    (fun j => ⟨⟨g * (j.1 : MulAut U) * g⁻¹, hg _ j.1.2⟩, ?_⟩) ?_
  · show (g * (j.1 : MulAut U) * g⁻¹) (g u) = g u
    rw [MulAut.mul_apply, MulAut.mul_apply, inv_apply_apply', j.2]
  · intro j k h
    have h1 : g * (j.1 : MulAut U) * g⁻¹ = g * (k.1 : MulAut U) * g⁻¹ :=
      congrArg (fun x => (x.1 : MulAut U)) h
    exact Subtype.ext (Subtype.ext (mul_left_cancel (mul_right_cancel h1)))

theorem isometry_of_normalizes (c : U ≃* Vec) {g : MulAut U}
    (hg : ∀ j ∈ (rhoV c).range, g * j * g⁻¹ ∈ (rhoV c).range)
    (hg' : ∀ j ∈ (rhoV c).range, g⁻¹ * j * g⁻¹⁻¹ ∈ (rhoV c).range) (u : U) :
    detQ (c (g u)) = detQ (c u) := by
  have h1 := card_stab_le hg u
  have h2 := card_stab_le hg' (g u)
  rw [inv_apply_apply'] at h2
  have h3 : Nat.card {j : ↥(rhoV c).range // (j : MulAut U) (g u) = g u} =
      Nat.card {j : ↥(rhoV c).range // (j : MulAut U) u = u} := le_antisymm h2 h1
  rw [card_stab_range, card_stab_range] at h3
  simp only [Nat.card_eq_fintype_card] at h3
  apply zmod_two_eq_of_iff
  rw [detQ_eq_one_iff, detQ_eq_one_iff, h3]

omit [Finite U] in
theorem conjBack_trans_sq (c : U ≃* Vec) : conjBack c transV * conjBack c transV = 1 := by
  rw [← conjBack_mul]
  have : transV * transV = 1 := by
    ext m
    exact trans_trans m
  rw [this, conjBack_one]

omit [Finite U] in
theorem conjBack_trans_ne_one (c : U ≃* Vec) : conjBack c transV ≠ 1 := by
  intro h
  have hall : ∀ m : Vec, transV m = m := by
    intro m
    have := congrArg (fun g : MulAut U => c (g (c.symm m))) h
    simpa [conjBack_apply] using this
  have : ∃ m : Vec, transV m ≠ m := by decide +kernel
  obtain ⟨m, hm⟩ := this
  exact hm (hall m)

theorem rk_commV_conjBack_trans (c : U ≃* Vec) :
    rk (commV (Subgroup.zpowers (conjBack c transV))) = 1 := by
  have hsum := rk_commV_add_rk_fixV (conjBack c transV)
  rw [rk_V_eq_four (card_of_equiv c)] at hsum
  have hfix := card_fixV_conjBack c transV
  have h8 : Nat.card ↥(fixV (Subgroup.zpowers (conjBack c transV))) = 8 := by
    rw [hfix]
    simp only [Nat.card_eq_fintype_card]
    exact transCount
  have := S152O.rk_eq_of_card_eq (exp_of_equiv c) (n := 3)
    (H := fixV (Subgroup.zpowers (conjBack c transV))) (by rw [h8]; rfl)
  omega

end Transvection

end S151cOm4


open S152O4 S151cOm4 in
theorem S3mod_exists_iso (hU : ∀ u : U, u ^ 2 = 1) (hcard : Nat.card U = 16) {a t : MulAut U}
    (ha3 : a ^ 3 = 1) (ht2 : t ^ 2 = 1) (hta : t * a * t⁻¹ = a⁻¹)
    (hfix : ∀ u : U, a u = u → u = 1) :
    ∃ c : U ≃* Vec, (∀ u, c (a u) = act (DihedralGroup.r 1, 1) (c u)) ∧
      ∀ u, c (t u) = act (DihedralGroup.sr 0, 1) (c u) := by
  have hbij := S3mod_coord_bijective hU hcard ha3 ht2 hta hfix
  have hrk := S3mod_rk_fixV_t_aux hU hcard ha3 ht2 hta hfix
  have hcardV0 : Nat.card ↥(fixV (Subgroup.zpowers t)) = 4 := by
    rw [card_eq_two_pow hU, hrk]; norm_num
  have hV0 : ∀ v : ↥(fixV (Subgroup.zpowers t)), v * v = 1 := fun v =>
    Subtype.ext (by simpa [pow_two] using hU v)
  obtain ⟨ψ⟩ := exists_mulEquiv_F2sq hV0 hcardV0
  let eU := MulEquiv.ofBijective (S3modCoord a t) hbij
  let c : U ≃* Vec := eU.symm.trans ((MulEquiv.prodCongr ψ ψ).trans eVec)
  have hc : ∀ p, c (S3modCoord a t p) = eVecFun (ψ p.1, ψ p.2) := by
    intro p
    have h : eU.symm (S3modCoord a t p) = p := (MulEquiv.symm_apply_eq _).mpr rfl
    show eVec ((MulEquiv.prodCongr ψ ψ) (eU.symm (S3modCoord a t p))) = _
    rw [h]
    rfl
  refine ⟨c, fun u => ?_, fun u => ?_⟩
  · obtain ⟨p, rfl⟩ := hbij.2 u
    rw [S3modCoord_a hU ha3 hfix, hc, hc]
    simp only [map_mul]
    exact (act_r_eVec _ _).symm
  · obtain ⟨p, rfl⟩ := hbij.2 u
    rw [S3modCoord_t hU ha3 hta hfix, hc, hc]
    simp only [map_mul]
    exact (act_sr_eVec _ _).symm

theorem S3mod_exists_gen (hU : ∀ u : U, u ^ 2 = 1) (hcard : Nat.card U = 16)
    {L : Subgroup (MulAut U)} (e : ↥L ≃* DihedralGroup 3)
    (hfix : ∀ g ∈ L, orderOf g = 3 → ∀ u : U, g u = u → u = 1) :
    ∃ a t : MulAut U, a ∈ L ∧ t ∈ L ∧ a ^ 3 = 1 ∧ t ^ 2 = 1 ∧ t * a * t⁻¹ = a⁻¹ ∧
      (∀ u : U, a u = u → u = 1) ∧ L = Subgroup.closure {a, t} ∧
      Nat.card (Subgroup.centralizer (L : Set (MulAut U))) = 6 := by
  set a : MulAut U := ((e.symm (DihedralGroup.r 1) : ↥L) : MulAut U) with ha
  set t : MulAut U := ((e.symm (DihedralGroup.sr 0) : ↥L) : MulAut U) with ht
  have haL : a ∈ L := (e.symm (DihedralGroup.r 1)).2
  have htL : t ∈ L := (e.symm (DihedralGroup.sr 0)).2
  have hordA : orderOf a = 3 := by
    rw [ha, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact DihedralGroup.orderOf_r_one
  have hordT : orderOf t = 2 := by
    rw [ht, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact DihedralGroup.orderOf_sr 0
  have ha3 : a ^ 3 = 1 := by
    have := pow_orderOf_eq_one a
    rwa [hordA] at this
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hordT] at this
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hordA
    omega
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hordT
    omega
  have hta : t * a * t⁻¹ = a⁻¹ := by
    have hD : (DihedralGroup.sr 0 : DihedralGroup 3) * DihedralGroup.r 1 *
        (DihedralGroup.sr 0)⁻¹ = (DihedralGroup.r 1)⁻¹ := by decide
    have h1 : e.symm (DihedralGroup.sr 0) * e.symm (DihedralGroup.r 1) *
        (e.symm (DihedralGroup.sr 0))⁻¹ = (e.symm (DihedralGroup.r 1))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, hD]
    exact congrArg (fun x : ↥L => (x : MulAut U)) h1
  have hfixa : ∀ u : U, a u = u → u = 1 := fun u hu => hfix a haL hordA u hu
  have hgen : ∀ g : DihedralGroup 3, ∃ i : Fin 3, ∃ j : Fin 2,
      g = DihedralGroup.r 1 ^ (i : ℕ) * DihedralGroup.sr 0 ^ (j : ℕ) := by decide
  have hL : L = Subgroup.closure {a, t} := by
    apply le_antisymm
    · intro g hg
      obtain ⟨i, j, hij⟩ := hgen (e ⟨g, hg⟩)
      have h1 : (⟨g, hg⟩ : ↥L) =
          e.symm (DihedralGroup.r 1) ^ (i : ℕ) * e.symm (DihedralGroup.sr 0) ^ (j : ℕ) := by
        apply e.injective
        rw [hij, map_mul, map_pow, map_pow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      have hg' : g = a ^ (i : ℕ) * t ^ (j : ℕ) := by
        have := congrArg (fun x : ↥L => (x : MulAut U)) h1
        simpa [ha, ht] using this
      rw [hg']
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h
      · rw [h]; exact haL
      · rw [h]; exact htL
  have hC : Subgroup.centralizer (L : Set (MulAut U)) = Subgroup.centralizer {a, t} := by
    rw [hL, Subgroup.centralizer_closure]
  refine ⟨a, t, haL, htL, ha3, ht2, hta, hfixa, hL, ?_⟩
  rw [hC]
  exact S3mod_card_centralizer hU hcard ha3 ha1 ht2 ht1 hta hfixa

theorem S3mod_card_centralizer_of_equiv (hU : ∀ u : U, u ^ 2 = 1) (hcard : Nat.card U = 16)
    {L : Subgroup (MulAut U)} (e : ↥L ≃* DihedralGroup 3)
    (hfix : ∀ g ∈ L, orderOf g = 3 → ∀ u : U, g u = u → u = 1) :
    Nat.card (Subgroup.centralizer (L : Set (MulAut U))) = 6 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := S3mod_exists_gen hU hcard e hfix
  exact h

open S152O4 S151cOm4 in
theorem isOmegaFourPlus_of_S3_centralizer (hU : ∀ u : U, u ^ 2 = 1) (hcard : Nat.card U = 16)
    {L : Subgroup (MulAut U)} (e : ↥L ≃* DihedralGroup 3)
    (hfix : ∀ g ∈ L, orderOf g = 3 → ∀ u : U, g u = u → u = 1) :
    IsOmegaFourPlus (L ⊔ Subgroup.centralizer (L : Set (MulAut U))) := by
  obtain ⟨a, t, haL, htL, ha3, ht2, hta, hfixa, hL, hC6'⟩ := S3mod_exists_gen hU hcard e hfix
  have hgen : ∀ g : DihedralGroup 3, ∃ i : Fin 3, ∃ j : Fin 2,
      g = DihedralGroup.r 1 ^ (i : ℕ) * DihedralGroup.sr 0 ^ (j : ℕ) := by decide
  have hC : Subgroup.centralizer (L : Set (MulAut U)) = Subgroup.centralizer {a, t} := by
    rw [hL, Subgroup.centralizer_closure]
  have hC6 : Nat.card (Subgroup.centralizer ({a, t} : Set (MulAut U))) = 6 := by
    rw [← hC]
    exact hC6'
  obtain ⟨c, hca, hct⟩ := S3mod_exists_iso hU hcard ha3 ht2 hta hfixa
  have hρa : rhoV c (DihedralGroup.r 1, 1) = a := by
    ext u
    apply c.injective
    rw [rhoV_apply, hca]
  have hρt : rhoV c (DihedralGroup.sr 0, 1) = t := by
    ext u
    apply c.injective
    rw [rhoV_apply, hct]
  set D : Subgroup (MulAut U) :=
    ((rhoV c).comp (MonoidHom.inr (DihedralGroup 3) (DihedralGroup 3))).range with hD
  have hDC : D ≤ Subgroup.centralizer ({a, t} : Set (MulAut U)) := by
    rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with hh | hh
    · rw [hh]
      show a * rhoV c (1, g) = rhoV c (1, g) * a
      rw [← hρa, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (by simp) (by simp)
    · rw [hh]
      show t * rhoV c (1, g) = rhoV c (1, g) * t
      rw [← hρt, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (by simp) (by simp)
  have hinj : Function.Injective
      ((rhoV c).comp (MonoidHom.inr (DihedralGroup 3) (DihedralGroup 3))) :=
    (rhoV_injective c).comp (fun x y h => congrArg Prod.snd h)
  have hD6 : Nat.card D = 6 := by
    rw [hD, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, DihedralGroup.nat_card]
  have hDeq : D = Subgroup.centralizer ({a, t} : Set (MulAut U)) :=
    Subgroup.eq_of_le_of_card_ge hDC (by rw [hC6, hD6])
  have hrange : L ⊔ Subgroup.centralizer (L : Set (MulAut U)) = (rhoV c).range := by
    rw [hC, ← hDeq]
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rw [hL, Subgroup.closure_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with h | h
        · rw [h, ← hρa]; exact ⟨_, rfl⟩
        · rw [h, ← hρt]; exact ⟨_, rfl⟩
      · rintro _ ⟨g, rfl⟩
        exact ⟨(1, g), rfl⟩
    · rintro _ ⟨⟨g, h⟩, rfl⟩
      have h1 : rhoV c (g, h) = rhoV c (g, 1) * rhoV c (1, h) := by
        rw [← map_mul]
        congr 1
        exact Prod.ext (by simp) (by simp)
      rw [h1]
      refine Subgroup.mul_mem_sup ?_ ⟨h, rfl⟩
      obtain ⟨i, j, hij⟩ := hgen g
      have h2 : ((g, 1) : Gam) =
          (DihedralGroup.r 1, 1) ^ (i : ℕ) * (DihedralGroup.sr 0, 1) ^ (j : ℕ) :=
        Prod.ext (by simp [hij]) (by simp)
      rw [h2, map_mul, map_pow, map_pow, hρa, hρt]
      exact L.mul_mem (L.pow_mem haL _) (L.pow_mem htL _)
  rw [hrange]
  exact isOmegaFourPlus_range c


open S152O4 S151cOm4 in
theorem Jhat_eq_of_isOmegaFourPlus {Y : Subgroup (MulAut U)} (hY : IsOmegaFourPlus Y) :
    Jhat Y = Y := by
  obtain ⟨c, hc⟩ := om4_model hY
  subst hc
  exact Jhat_range c

open S152O4 S151cOm4 in
theorem mem_QhatStar_iff_of_isOmegaFourPlus {Y : Subgroup (MulAut U)} (hY : IsOmegaFourPlus Y)
    {A : Subgroup (MulAut U)} : A ∈ QhatStar Y ↔ IsA2 Y A ∧ Nat.card A = 4 := by
  obtain ⟨c, hc⟩ := om4_model hY
  subst hc
  exact mem_QhatStar_range_iff c

open S152O4 S151cOm4 in
theorem qhatOf_eq_of_isOmegaFourPlus {Y : Subgroup (MulAut U)} (hY : IsOmegaFourPlus Y) :
    qhatOf Y = ((3 / 2 : ℚ) : WithTop ℚ) := by
  obtain ⟨c, hc⟩ := om4_model hY
  subst hc
  exact qhat_range c


open S152O4 S151cOm4 CFSG.Quasithin.S1417 in
theorem exists_transvection_of_ne {J X : Subgroup (MulAut U)} (hJ : IsOmegaFourPlus J)
    (hJX : J ≤ X) (hnorm : ∀ x ∈ X, ∀ j ∈ J, x * j * x⁻¹ ∈ J) (hne : J ≠ X) :
    ∃ τ ∈ X, τ ≠ 1 ∧ τ ^ 2 = 1 ∧ rk (commV (Subgroup.zpowers τ)) = 1 := by
  obtain ⟨c, hc⟩ := om4_model hJ
  subst hc
  have hcard : Nat.card U = 16 := card_of_equiv c
  have hexp' : ∀ w : U, w ^ 2 = 1 := exp_of_equiv c
  have hexp : ∀ w : U, w * w = 1 := fun w => by rw [← pow_two]; exact hexp' w
  have hq1 : IsQuadraticFormOn (fun v => detQ (c v)) := isQuadratic_comp c detQ_isQuadratic
  have hq2 : IsNondegQuadratic (fun v => detQ (c v)) := isNondeg_comp c detQ_nondeg
  have hq3 : IsPlusType (fun v => detQ (c v)) := isPlus_comp c detQ_plus
  have hXO : X ≤ orthogonalGroupOf (fun v => detQ (c v)) := fun g hg v =>
    isometry_of_normalizes c (hnorm g hg) (fun j hj => by
      simpa using hnorm g⁻¹ (X.inv_mem hg) j hj) v
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hcard hq1 hq2 hq3
  have hO72 : Nat.card (orthogonalGroupOf (fun v => detQ (c v))) = 72 := hS.card_X
  have hJ36 : Nat.card (rhoV c).range = 36 := card_eq_36 c rfl
  have h1 : 36 ∣ Nat.card X := hJ36 ▸ Subgroup.card_dvd_of_le hJX
  have h2 : Nat.card X ∣ 72 := hO72 ▸ Subgroup.card_dvd_of_le hXO
  have hXcard : Nat.card X = 72 := by
    by_contra hne72
    have hle : Nat.card X ≤ 72 := Nat.le_of_dvd (by norm_num) h2
    have hpos : 0 < Nat.card X := Nat.card_pos
    obtain ⟨k, hk⟩ := h1
    have h36 : Nat.card X = 36 := by omega
    exact hne (Subgroup.eq_of_le_of_card_ge hJX (by rw [hJ36, h36]))
  have hXeq : X = orthogonalGroupOf (fun v => detQ (c v)) :=
    Subgroup.eq_of_le_of_card_ge hXO (by rw [hO72, hXcard])
  have hτO : conjBack c transV ∈ orthogonalGroupOf (fun v => detQ (c v)) := by
    intro v
    show detQ (c (conjBack c transV v)) = detQ (c v)
    rw [conjBack_apply, detQ_trans]
  refine ⟨conjBack c transV, hXeq ▸ hτO, conjBack_trans_ne_one c, ?_, rk_commV_conjBack_trans c⟩
  rw [pow_two]
  exact conjBack_trans_sq c

end CFSG.Quasithin
