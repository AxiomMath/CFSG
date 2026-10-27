module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Cfg
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79OrthGeo
public import CFSG.GH74.Filter.Orthogonal.OddReflections
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagAssembly

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Spin

private theorem nine3_matrixRank_eq_finrank_omegaInvSpace {ι F : Type} [Fintype ι]
    [DecidableEq ι] [Field F] (A : GL ι F) :
    Matrix.rank ((A : Matrix ι ι F) - 1) =
      Module.finrank F (omegaInvSpace (toLinEquiv ι F A)) := by
  have h : ((A : Matrix ι ι F) - 1).mulVecLin =
      (↑(toLinEquiv ι F A) : (ι → F) →ₗ[F] (ι → F)) - LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    simp [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, LinearMap.sub_apply,
      toLinEquiv_apply]
  rw [Matrix.rank, h, omegaInvSpace, omegaInvNil]

private theorem nine3_reflect_mul_ne_of_polar_ne_zero {F V : Type} [Field F] [CharP F 2]
    [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {x y : V}
    (hx : Q x ≠ 0) (hy : Q y ≠ 0) (hxy : polar Q x y ≠ 0) :
    reflect Q x * reflect Q y ≠ reflect Q y * reflect Q x := by
  intro hcomm
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, QuadraticMap.map_zero])
  have hxx : reflect Q x x = x := by
    rw [reflect_apply hx, QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero,
      zero_div, zero_smul, sub_zero]
  have hval : (reflect Q x * reflect Q y) x =
      x - (polar Q y x / Q y) • y +
        ((polar Q y x / Q y) * (polar Q x y / Q x)) • x := by
    rw [LinearEquiv.mul_apply, reflect_apply hy, map_sub, map_smul, hxx, reflect_apply hx,
      smul_sub, smul_smul]
    module
  have hval' : (reflect Q y * reflect Q x) x = x - (polar Q y x / Q y) • y := by
    rw [LinearEquiv.mul_apply, hxx, reflect_apply hy]
  have happ := congrArg (fun g : V ≃ₗ[F] V => g x) hcomm
  rw [hval, hval'] at happ
  have hzero : ((polar Q y x / Q y) * (polar Q x y / Q x)) • x = 0 := by
    have h2 : (x - (polar Q y x / Q y) • y) +
        ((polar Q y x / Q y) * (polar Q x y / Q x)) • x =
        (x - (polar Q y x / Q y) • y) + 0 := by
      rw [happ, add_zero]
    exact add_left_cancel h2
  rw [smul_eq_zero] at hzero
  have hc0 : polar Q y x / Q y ≠ 0 := div_ne_zero (by rwa [polar_comm]) hy
  have hd0 : polar Q x y / Q x ≠ 0 := div_ne_zero hxy hx
  rcases hzero with hzero | hzero
  · exact (mul_ne_zero hc0 hd0) hzero
  · exact hx0 hzero

private theorem nine3_reflect_smul {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {x : V} {c : F} (hc : c ≠ 0) (hx : Q x ≠ 0) :
    reflect Q (c • x) = reflect Q x := by
  have hcx : Q (c • x) ≠ 0 := by
    rw [QuadraticMap.map_smul, smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero hc hc) hx
  refine LinearEquiv.ext fun y => ?_
  rw [reflect_apply hcx, reflect_apply hx, QuadraticMap.polar_smul_left, QuadraticMap.map_smul]
  simp only [smul_eq_mul, smul_smul]
  congr 2
  field_simp

private theorem nine3_prop710_orthGen {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {Q : QuadraticForm F (ι → F)}
    (hQnd : (polarBilin Q).Nondegenerate) {O : Subgroup (GL ι F)}
    (hO : O = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
      (toLinEquiv ι F).toMonoidHom)
    {c a e a' v : ↥O} (hc : IsRankOneIn (c : GL ι F))
    (h : Nine3Config c a e a' v) :
    ∃ d : ↥O, IsConj c d ∧ d ≠ v ∧ d * a = a * d ∧ d * e = e * d := by
  have hmem : ∀ x : ↥O, toLinEquiv ι F (x : GL ι F) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro x
    have hx : (x : GL ι F) ∈ (TauCeti.QuadraticMap.orthogonalGroup Q).comap
        (toLinEquiv ι F).toMonoidHom := by
      rw [← hO]
      exact x.2
    exact Subgroup.mem_comap.mp hx
  have hc_sq : c * c = 1 := by
    obtain ⟨u, hu⟩ := isConj_iff.mp h.conj_a
    have h1 : (u * c * u⁻¹) * (u * c * u⁻¹) = 1 := by rw [hu, h.sq_a]
    calc c * c = u⁻¹ * ((u * c * u⁻¹) * (u * c * u⁻¹)) * u := by group
      _ = u⁻¹ * 1 * u := by rw [h1]
      _ = 1 := by group
  have hc_rank : Module.finrank F (omegaInvSpace (toLinEquiv ι F (c : GL ι F))) = 1 := by
    rw [← nine3_matrixRank_eq_finrank_omegaInvSpace]
    exact hc
  have hc_sq_lin : toLinEquiv ι F (c : GL ι F) * toLinEquiv ι F (c : GL ι F) = 1 := by
    rw [← map_mul, ← Subgroup.coe_mul, hc_sq, Subgroup.coe_one, map_one]
  obtain ⟨w, hw, hwc⟩ := exists_reflection_of_finrank_eq_one hQnd (hmem c) hc_sq_lin hc_rank
  have hc_reflect : toLinEquiv ι F (c : GL ι F) = reflect Q w := by
    refine LinearEquiv.ext fun y => ?_
    rw [hwc y, reflect_apply hw]
  have center_of_conj : ∀ x : ↥O, IsConj c x → ∃ p : ι → F, Q p ≠ 0 ∧
      toLinEquiv ι F (x : GL ι F) = reflect Q p := by
    intro x hx
    obtain ⟨u, hu⟩ := isConj_iff.mp hx
    refine ⟨toLinEquiv ι F (u : GL ι F) w, ?_, ?_⟩
    · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hmem u) w]
      exact hw
    · calc toLinEquiv ι F (x : GL ι F)
          = toLinEquiv ι F ((u * c * u⁻¹ : ↥O) : GL ι F) := by rw [← hu]
        _ = toLinEquiv ι F (u : GL ι F) * reflect Q w *
              (toLinEquiv ι F (u : GL ι F))⁻¹ := by
              rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul,
                map_inv, hc_reflect]
        _ = reflect Q (toLinEquiv ι F (u : GL ι F) w) :=
              reflect_conj (hmem u) w
  obtain ⟨p, hpQ, hp_lin⟩ := center_of_conj a h.conj_a
  obtain ⟨q, hqQ, hq_lin⟩ := center_of_conj e h.conj_e
  obtain ⟨p', hp'Q, hp'_lin⟩ := center_of_conj a' h.conj_a'
  obtain ⟨s, hsQ, hs_lin⟩ := center_of_conj v h.conj_v
  have hcomm_to_polar : ∀ {x y : ↥O} {x₀ y₀ : ι → F},
      toLinEquiv ι F (x : GL ι F) = reflect Q x₀ →
      toLinEquiv ι F (y : GL ι F) = reflect Q y₀ →
      Q x₀ ≠ 0 → Q y₀ ≠ 0 → x * y = y * x → polar Q x₀ y₀ = 0 := by
    intro x y x₀ y₀ hx hy hxQ hyQ hxy
    by_contra hpol
    apply nine3_reflect_mul_ne_of_polar_ne_zero hxQ hyQ hpol
    have h1 := congrArg (fun z : ↥O => toLinEquiv ι F (z : GL ι F)) hxy
    simpa [Subgroup.coe_mul, map_mul, hx, hy] using h1
  have hpq : polar Q p q ≠ 0 := by
    intro h0
    apply h.not_comm_ae
    apply Subtype.ext
    show (a : GL ι F) * (e : GL ι F) = (e : GL ι F) * (a : GL ι F)
    refine (toLinEquiv ι F).injective ?_
    rw [map_mul, map_mul, hp_lin, hq_lin]
    exact CFSG.GH74.Filter.reflect_comm h0
  have hp'q : polar Q p' q ≠ 0 := by
    intro h0
    have hcomm : e * a' = a' * e := by
      apply Subtype.ext
      show (e : GL ι F) * (a' : GL ι F) = (a' : GL ι F) * (e : GL ι F)
      refine (toLinEquiv ι F).injective ?_
      rw [map_mul, map_mul, hq_lin, hp'_lin]
      exact CFSG.GH74.Filter.reflect_comm (by rwa [polar_comm] at h0)
    have h2 : (e * a') ^ 2 = 1 := by
      rw [pow_two]
      calc (e * a') * (e * a') = e * (a' * e) * a' := by group
        _ = e * (e * a') * a' := by rw [← hcomm]
        _ = (e * e) * (a' * a') := by group
        _ = 1 := by simp [h.sq_e, h.sq_a']
    have h1 : e * a' = 1 := by
      calc e * a' = (e * a') ^ 3 * ((e * a') ^ 2)⁻¹ := by group
        _ = 1 := by rw [h.pow_ea', h2]; simp
    have hord := h.orderOf_ae.2
    rw [h1, orderOf_one] at hord
    exact absurd hord (by decide)
  have hne_aa' : a ≠ a' := by
    intro haa'
    apply h.ne_aa'
    rw [haa']
    exact h.sq_a'
  have hpp' : polar Q p p' = 0 :=
    hcomm_to_polar hp_lin hp'_lin hpQ hp'Q h.comm_aa'
  have hne : ∀ t : F, p' ≠ t • p := by
    intro t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [zero_smul] at ht
      exact hp'Q (by rw [ht, QuadraticMap.map_zero])
    · have haa' : a = a' := by
        apply Subtype.ext
        show (a : GL ι F) = (a' : GL ι F)
        refine (toLinEquiv ι F).injective ?_
        rw [hp_lin, hp'_lin, ht, nine3_reflect_smul ht0 hpQ]
      exact hne_aa' haa'
  have hsp : polar Q s p = 0 := hcomm_to_polar hs_lin hp_lin hsQ hpQ h.comm_va
  have hsq : polar Q s q = 0 := hcomm_to_polar hs_lin hq_lin hsQ hqQ h.comm_ve
  have hsp' : polar Q s p' = 0 := hcomm_to_polar hs_lin hp'_lin hsQ hp'Q h.comm_va'
  have hB : ∀ x : ι → F, (∀ y : ι → F, polar Q x y = 0) → x = 0 :=
    fun x hx => hQnd.1 x (fun y => by rw [polarBilin_apply_apply]; exact hx y)
  obtain ⟨s', hs'Q, hs'p, hs'q, hss'⟩ :=
    nine3_orth_exists_nonsing Q hB hpQ hqQ hp'Q hsQ hpq hp'q hpp' hne hsp hsq hsp'
  let hg : GL ι F := (toLinEquiv ι F).symm (reflect Q s')
  have hhg : hg ∈ O := by
    rw [hO]
    exact Subgroup.mem_comap.mpr (by
      show toLinEquiv ι F hg ∈ TauCeti.QuadraticMap.orthogonalGroup Q
      rw [show hg = (toLinEquiv ι F).symm (reflect Q s') from rfl]
      rw [MulEquiv.apply_symm_apply]
      exact reflect_mem_orthogonalGroup Q s')
  let hE : ↥O := ⟨hg, hhg⟩
  have hE_lin : toLinEquiv ι F (hE : GL ι F) = reflect Q s' := by
    show toLinEquiv ι F hg = reflect Q s'
    rw [show hg = (toLinEquiv ι F).symm (reflect Q s') from rfl]
    exact MulEquiv.apply_symm_apply _ _
  have hEa : hE * a = a * hE := by
    apply Subtype.ext
    show (hE : GL ι F) * (a : GL ι F) = (a : GL ι F) * (hE : GL ι F)
    refine (toLinEquiv ι F).injective ?_
    rw [map_mul, map_mul, hE_lin, hp_lin]
    exact CFSG.GH74.Filter.reflect_comm hs'p
  have hEe : hE * e = e * hE := by
    apply Subtype.ext
    show (hE : GL ι F) * (e : GL ι F) = (e : GL ι F) * (hE : GL ι F)
    refine (toLinEquiv ι F).injective ?_
    rw [map_mul, map_mul, hE_lin, hq_lin]
    exact CFSG.GH74.Filter.reflect_comm hs'q
  let d : ↥O := hE * v * hE⁻¹
  have hd_conj : IsConj c d := by
    obtain ⟨u, hu⟩ := isConj_iff.mp h.conj_v
    refine isConj_iff.mpr ⟨hE * u, ?_⟩
    show (hE * u) * c * (hE * u)⁻¹ = hE * v * hE⁻¹
    rw [← hu]
    group
  have hdv_ne : d ≠ v := by
    intro hdv
    have hcomm : hE * v = v * hE := by
      calc hE * v = (hE * v * hE⁻¹) * hE := by group
        _ = v * hE := by rw [show hE * v * hE⁻¹ = v from hdv]
    have hcommLin : reflect Q s' * reflect Q s = reflect Q s * reflect Q s' := by
      have h1 := congrArg (fun z : ↥O => toLinEquiv ι F (z : GL ι F)) hcomm
      simpa [Subgroup.coe_mul, map_mul, hE_lin, hs_lin] using h1
    exact nine3_reflect_mul_ne_of_polar_ne_zero hsQ hs'Q hss' hcommLin.symm
  have hd_a : d * a = a * d := by
    have hva : v * a = a * v := h.comm_va
    have hEa_inv : hE⁻¹ * a = a * hE⁻¹ := by
      calc hE⁻¹ * a = hE⁻¹ * a * (hE * hE⁻¹) := by group
        _ = hE⁻¹ * (a * hE) * hE⁻¹ := by group
        _ = hE⁻¹ * (hE * a) * hE⁻¹ := by rw [← hEa]
        _ = a * hE⁻¹ := by group
    show (hE * v * hE⁻¹) * a = a * (hE * v * hE⁻¹)
    calc (hE * v * hE⁻¹) * a = hE * v * (hE⁻¹ * a) := by group
      _ = hE * v * (a * hE⁻¹) := by rw [hEa_inv]
      _ = hE * (v * a) * hE⁻¹ := by group
      _ = hE * (a * v) * hE⁻¹ := by rw [hva]
      _ = (hE * a) * v * hE⁻¹ := by group
      _ = (a * hE) * v * hE⁻¹ := by rw [hEa]
      _ = a * (hE * v * hE⁻¹) := by group
  have hd_e : d * e = e * d := by
    have hve : v * e = e * v := h.comm_ve
    have hEe_inv : hE⁻¹ * e = e * hE⁻¹ := by
      calc hE⁻¹ * e = hE⁻¹ * e * (hE * hE⁻¹) := by group
        _ = hE⁻¹ * (e * hE) * hE⁻¹ := by group
        _ = hE⁻¹ * (hE * e) * hE⁻¹ := by rw [← hEe]
        _ = e * hE⁻¹ := by group
    show (hE * v * hE⁻¹) * e = e * (hE * v * hE⁻¹)
    calc (hE * v * hE⁻¹) * e = hE * v * (hE⁻¹ * e) := by group
      _ = hE * v * (e * hE⁻¹) := by rw [hEe_inv]
      _ = hE * (v * e) * hE⁻¹ := by group
      _ = hE * (e * v) * hE⁻¹ := by rw [hve]
      _ = (hE * e) * v * hE⁻¹ := by group
      _ = (e * hE) * v * hE⁻¹ := by rw [hEe]
      _ = e * (hE * v * hE⁻¹) := by group
  exact ⟨d, hd_conj, hdv_ne, hd_a, hd_e⟩

theorem nine3_prop710_orthPlus {k : ℕ} (hk : 2 ≤ k) {F : Type} [Field F] [Finite F]
    (hF : ∃ n : ℕ, 1 ≤ n ∧ Nat.card F = 2 ^ n)
    {c a e a' v : ↥(CFSG.PGLModel.orthogonalPlus k F)}
    (hc : IsRankOneIn (((c : ↥(CFSG.PGLModel.orthogonalPlus k F)) : GL (Fin k ⊕ Fin k) F)))
    (h : Nine3Config c a e a' v) :
    ∃ d, IsConj c d ∧ d ≠ v ∧ d * a = a * d ∧ d * e = e * d := by
  obtain ⟨n, hn, hcard⟩ := hF
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard' : Fintype.card F = 2 ^ n := by rwa [Nat.card_eq_fintype_card] at hcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hQnd : (polarBilin (quadPlus k F)).Nondegenerate :=
    nondegenerate_polarBilin_quadPlus k F
  have hcoeq : ⇑(quadPlus k F) = CFSG.PGLModel.plusQuadForm k (K := F) := by
    funext v
    rw [quadPlus_apply]
    rfl
  have hO : CFSG.PGLModel.orthogonalPlus k F =
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus k F)).comap
        (toLinEquiv (Fin k ⊕ Fin k) F).toMonoidHom := by
    have h := CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
      (ι := Fin k ⊕ Fin k) (K := F) hcoeq
    simpa [CFSG.PGLModel.orthogonalPlus, CFSG.PGLModel.orthogonalGroup,
      CFSG.MatrixModel.isometryCore] using h
  exact nine3_prop710_orthGen hQnd hO hc h

theorem nine3_prop710_orthMinus {k : ℕ} (hk : 1 ≤ k) {F : Type} [Field F] [Finite F]
    (hF : ∃ n : ℕ, 1 ≤ n ∧ Nat.card F = 2 ^ n) {b c' : F} (hbc : ∀ t : F, t ^ 2 + b * t + c' ≠ 0)
    {c a e a' v : ↥(CFSG.PGLModel.orthogonalMinus k F b c')}
    (hc : IsRankOneIn
      (((c : ↥(CFSG.PGLModel.orthogonalMinus k F b c')) : GL (Fin k ⊕ Fin k ⊕ Fin 2) F)))
    (h : Nine3Config c a e a' v) :
    ∃ d, IsConj c d ∧ d ≠ v ∧ d * a = a * d ∧ d * e = e * d := by
  obtain ⟨n, hn, hcard⟩ := hF
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard' : Fintype.card F = 2 ^ n := by rwa [Nat.card_eq_fintype_card] at hcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hQnd : (polarBilin (quadMinus (k + 1) F b c')).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite (n := k + 1) (K := F) hbc
  have hcoeq : ⇑(quadMinus (k + 1) F b c') = CFSG.PGLModel.minusQuadForm k (K := F) b c' := by
    funext v
    rw [quadMinus_apply]
    rfl
  have hO : CFSG.PGLModel.orthogonalMinus k F b c' =
      (TauCeti.QuadraticMap.orthogonalGroup (quadMinus (k + 1) F b c')).comap
        (toLinEquiv (Fin k ⊕ Fin k ⊕ Fin 2) F).toMonoidHom := by
    have h := CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
      (ι := Fin k ⊕ Fin k ⊕ Fin 2) (K := F) hcoeq
    simpa [CFSG.PGLModel.orthogonalMinus, CFSG.PGLModel.orthogonalGroup,
      CFSG.MatrixModel.isometryCore] using h
  exact nine3_prop710_orthGen hQnd hO hc h

end CFSG.LocalAnalysis.WeakClosure81
