module

public import CFSG.RankThree.PartTwo.KFacts.L34TwoElements
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSinger

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter
  (diagGL det_diagGL coe_diagGL conjAut_mem_range_conj_iff)
open CFSG.RankThree.PartTwo.Sec4
open Matrix
open scoped commutatorElement

variable {k : Type*} [Field k]

private theorem rM_mul_self :
    (rM * rM : Matrix (Fin 3) (Fin 3) k) = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rM, Matrix.mul_fin_three]

private theorem toGL_rSL_sq :
    (((Matrix.SpecialLinearGroup.toGL rSL) ^ 2 : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
  rw [show (((Matrix.SpecialLinearGroup.toGL rSL) ^ 2 : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) = (rM * rM) by
    rw [Units.val_pow_eq_pow_val, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_rSL',
      pow_two]]
  exact rM_mul_self

private theorem coe_diagGL_mul_rSL {u : kˣ} :
    (((diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ 1 : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k)) = !![0, 0, (u : k); 1, 0, 0; 0, 1, 0] := by
  ext i j
  rw [Units.val_mul, coe_diagGL, pow_one, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    coe_rSL']
  fin_cases i <;> fin_cases j <;> simp [rM, Matrix.mul_fin_three]

private theorem coe_diagGL_mul_rSL_sq {u : kˣ} :
    (((diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ 2 : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k)) = !![0, (u : k), 0; 0, 0, 1; 1, 0, 0] := by
  ext i j
  rw [Units.val_mul, coe_diagGL, toGL_rSL_sq]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_three]

private theorem cube_one (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) :
    (!![0, 0, (u : k); 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) k) ^ 3 =
      (u : k) • (1 : Matrix (Fin 3) (Fin 3) k) := by
  have huu : (u : k) * u = u + 1 :=
    LinearFieldFour.omega_mul_omega hk u.ne_zero (val_ne_one hu)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_fin_three, Matrix.one_apply, Matrix.smul_apply, huu] <;>
    ring_nf

private theorem cube_two (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) :
    (!![0, (u : k), 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) k) ^ 3 =
      (u : k) • (1 : Matrix (Fin 3) (Fin 3) k) := by
  have huu : (u : k) * u = u + 1 :=
    LinearFieldFour.omega_mul_omega hk u.ne_zero (val_ne_one hu)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_fin_three, Matrix.one_apply, Matrix.smul_apply, huu] <;>
    ring_nf

private theorem diagGL_mul_rSL_pow_three (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1)
    (j : ℕ) (hj : j = 1 ∨ j = 2) :
    (((diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ j : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) ^ 3) =
      (u : k) • (1 : Matrix (Fin 3) (Fin 3) k) := by
  rcases hj with rfl | rfl
  · rw [coe_diagGL_mul_rSL, cube_one hk hu]
  · rw [coe_diagGL_mul_rSL_sq, cube_two hk hu]

private theorem det_diagGL_mul_rSL_pow {u : kˣ} (j : ℕ) :
    GeneralLinearGroup.det (diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ j) = u := by
  rw [map_mul, map_pow, det_diagGL]
  have hR : GeneralLinearGroup.det
      (Matrix.SpecialLinearGroup.toGL (rSL : Matrix.SpecialLinearGroup (Fin 3) k)) = 1 := by
    refine Units.ext ?_
    rw [GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Units.val_one]
    exact rSL.prop
  rw [hR, one_pow, mul_one]

private theorem pow_three_ne (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) :
    ∀ μ : k, μ ^ 3 ≠ (u : k) := by
  intro μ hμ
  by_cases h0 : μ = 0
  · rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at hμ
    exact u.ne_zero hμ.symm
  · have h3 : μ ^ 3 = 1 := by
      have := LinearThreeFourOuter.units_pow_three hk (Units.mk0 μ h0)
      simpa using congrArg Units.val this
    rw [h3] at hμ
    exact val_ne_one hu hμ.symm

private theorem card_centralizer_eq_63 (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1)
    {Mt : GL (Fin 3) k}
    (hpow : (Mt : Matrix (Fin 3) (Fin 3) k) ^ 3 = (u : k) • 1) :
    Nat.card (Subgroup.centralizer {Mt}) = 63 := by
  haveI : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  haveI : Fintype k := Fintype.ofFinite k
  haveI : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra (ZMod 2) k := ZMod.algebra k 2
  let ψ : k ≃+* GaloisField 2 2 :=
    (GaloisField.algEquivGaloisFieldOfFintype 2 2 (K := k) (by
      rw [← Nat.card_eq_fintype_card, hk]
      norm_num)).toRingEquiv
  let Mt₀ : GL (Fin 3) (GaloisField 2 2) :=
    Matrix.GeneralLinearGroup.map ψ.toRingHom Mt
  have hMt₀ : ((Mt₀ : GL (Fin 3) (GaloisField 2 2)) :
      Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) =
      (Mt : Matrix (Fin 3) (Fin 3) k).map ψ.toRingHom := by
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  have hpow₀ : ((Mt₀ : GL (Fin 3) (GaloisField 2 2)) :
      Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) ^ 3 =
        (ψ u : GaloisField 2 2) • 1 := by
    rw [hMt₀, ← Matrix.map_pow, hpow]
    ext i j
    by_cases h : i = j <;>
      simp [h, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
  have hℓ₀ : ∀ μ : GaloisField 2 2, μ ^ 3 ≠ (ψ u : GaloisField 2 2) := by
    intro μ hμ
    apply pow_three_ne hk hu (ψ.symm μ)
    calc (ψ.symm μ) ^ 3 = ψ.symm (μ ^ 3) := (ψ.symm.map_pow μ 3).symm
      _ = ψ.symm (ψ u) := by rw [hμ]
      _ = u := ψ.symm_apply_apply u
  have hcyc := centralizer_cyclic_card (K := GaloisField 2 2)
    (ℓ := (ψ u : GaloisField 2 2)) (yG := Mt₀) hℓ₀ hpow₀
  have hcard₀ : Nat.card (Subgroup.centralizer {Mt₀}) = 63 := by
    have h := hcyc.2
    rw [GaloisField.card 2 2 (by norm_num)] at h
    norm_num at h
    exact h
  let e : GL (Fin 3) k ≃* GL (Fin 3) (GaloisField 2 2) :=
    { toFun := Matrix.GeneralLinearGroup.map ψ.toRingHom
      invFun := Matrix.GeneralLinearGroup.map ψ.symm.toRingHom
      left_inv := fun A => by
        apply Units.ext
        ext i j
        rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
        exact ψ.symm_apply_apply ((A : Matrix (Fin 3) (Fin 3) k) i j)
      right_inv := fun A => by
        apply Units.ext
        ext i j
        rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
        exact ψ.apply_symm_apply
          ((A : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) i j)
      map_mul' := map_mul _ }
  have hcent : (Subgroup.centralizer {Mt}).map e.toMonoidHom =
      Subgroup.centralizer {Mt₀} := by
    ext A
    constructor
    · rintro ⟨B, hB, rfl⟩
      have hB' : B * Mt = Mt * B := Subgroup.mem_centralizer_singleton_iff.mp hB
      rw [Subgroup.mem_centralizer_singleton_iff]
      change e B * e Mt = e Mt * e B
      rw [← map_mul, ← map_mul, hB']
    · intro hA
      have hA' : A * Mt₀ = Mt₀ * A := Subgroup.mem_centralizer_singleton_iff.mp hA
      refine ⟨e.symm A, ?_, e.apply_symm_apply A⟩
      change e.symm A ∈ Subgroup.centralizer {Mt}
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      show A * e Mt = e Mt * A
      exact hA'
  have hcard : Nat.card (Subgroup.centralizer {Mt}) =
      Nat.card (Subgroup.centralizer {Mt₀}) := by
    rw [← hcent]
    exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm
  exact hcard.trans hcard₀

private theorem card_ker_det_centralizer (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1)
    {Mt : GL (Fin 3) k}
    (hpow : (Mt : Matrix (Fin 3) (Fin 3) k) ^ 3 = (u : k) • 1)
    (hdet : GeneralLinearGroup.det Mt ≠ 1) :
    Nat.card ((GeneralLinearGroup.det.comp
      (Subgroup.centralizer {Mt}).subtype).ker) = 21 := by
  haveI := LinearFieldFour.finite_of_card_eq_four hk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup (GL (Fin 3) k) := Subgroup.centralizer {Mt} with hCdef
  have hCcard : Nat.card C = 63 := by
    rw [hCdef]
    exact card_centralizer_eq_63 hk hu hpow
  have hMtC : Mt ∈ C := by
    rw [hCdef]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hdetpow : (GeneralLinearGroup.det Mt) ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, GeneralLinearGroup.val_det_apply,
      ← Matrix.det_pow, hpow, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin]
    exact congrArg Units.val (LinearThreeFourOuter.units_pow_three hk u)
  have horder : orderOf (GeneralLinearGroup.det Mt) = 3 :=
    orderOf_eq_prime hdetpow hdet
  let detC : C →* kˣ := GeneralLinearGroup.det.comp C.subtype
  have hdet_range : Nat.card detC.range = 3 := by
    have hle : Subgroup.zpowers (GeneralLinearGroup.det Mt) ≤ detC.range := by
      rw [Subgroup.zpowers_le]
      exact ⟨⟨Mt, hMtC⟩, rfl⟩
    have hdiv1 : 3 ∣ Nat.card detC.range := by
      have h3 : Nat.card (Subgroup.zpowers (GeneralLinearGroup.det Mt)) = 3 := by
        rw [Nat.card_zpowers, horder]
      have hdiv := Subgroup.card_dvd_of_le hle
      rwa [h3] at hdiv
    have hdiv2 : Nat.card detC.range ∣ 3 := by
      have := Subgroup.card_subgroup_dvd_card detC.range
      rwa [LinearThreeFourOuter.card_units_eq_three hk] at this
    have := Nat.dvd_antisymm hdiv1 hdiv2
    omega
  have hquot : Nat.card (C ⧸ detC.ker) = 3 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange detC).toEquiv]
    exact hdet_range
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (detC.ker)
  rw [hCcard, hquot] at hcard
  have hcard' : Nat.card detC.ker = 21 := by
    have h63 : 3 * Nat.card detC.ker = 3 * 21 := by
      rw [← hcard]
    exact Nat.mul_left_cancel (by norm_num) h63
  exact hcard'

private theorem card_map_comap_centralizer (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1)
    {Mt : GL (Fin 3) k}
    (hpow : (Mt : Matrix (Fin 3) (Fin 3) k) ^ 3 = (u : k) • 1)
    (hdet : GeneralLinearGroup.det Mt ≠ 1) :
    Nat.card ↥(((Subgroup.centralizer {Mt}).comap Matrix.SpecialLinearGroup.toGL).map
      (proj 3 k)) = 7 := by
  haveI := LinearFieldFour.finite_of_card_eq_four hk
  have hker := card_ker_det_centralizer hk hu hpow hdet
  set C : Subgroup (GL (Fin 3) k) := Subgroup.centralizer {Mt} with hCdef
  set D : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k) :=
    C.comap Matrix.SpecialLinearGroup.toGL with hDdef
  have hker_sub : Nat.card ((GeneralLinearGroup.det.comp C.subtype).ker) =
      Nat.card ↥(C ⊓ GeneralLinearGroup.det.ker) := by
    have hkereq : (GeneralLinearGroup.det.comp C.subtype).ker =
        (C ⊓ GeneralLinearGroup.det.ker).subgroupOf C := by
      apply Subgroup.ext
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
      exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
    rw [hkereq]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ⊓ GeneralLinearGroup.det.ker ≤ C)).toEquiv
  have hDmap : D.map Matrix.SpecialLinearGroup.toGL =
      C ⊓ GeneralLinearGroup.det.ker := by
    rw [hDdef, Subgroup.map_comap_eq, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact inf_comm _ _
  have hcardD : Nat.card D = 21 := by
    have h1 : Nat.card (D.map Matrix.SpecialLinearGroup.toGL) = Nat.card D :=
      Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective
    have h2 : Nat.card (D.map Matrix.SpecialLinearGroup.toGL) = Nat.card
        ((GeneralLinearGroup.det.comp C.subtype).ker) := by
      rw [hDmap]
      exact hker_sub.symm
    omega
  have hscal_le_D : scalars 3 k ≤ D := by
    intro s hs
    rw [hDdef, Subgroup.mem_comap, hCdef, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp (toGL_mem_center hs) Mt).symm
  have hinf : D ⊓ (proj 3 k).ker = scalars 3 k := by
    rw [LinearFlag.ker_proj]
    exact inf_eq_right.mpr hscal_le_D
  let ψ : D →* projectiveSL 3 k := (proj 3 k).comp D.subtype
  have hrange : ψ.range = D.map (proj 3 k) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker_eq : ψ.ker = (D ⊓ (proj 3 k).ker).subgroupOf D := by
    apply Subgroup.ext
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have hkerψ : Nat.card ↥ψ.ker = Nat.card ↥(D ⊓ (proj 3 k).ker) := by
    rw [hker_eq]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : D ⊓ (proj 3 k).ker ≤ D)).toEquiv
  have hquot : Nat.card (D ⧸ ψ.ker) = Nat.card ↥(D.map (proj 3 k)) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange]
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := D) ψ.ker
  rw [hcardD, hquot, hkerψ, hinf, card_scalars hk] at hcard
  have hmain : Nat.card ↥(D.map (proj 3 k)) * 3 = 7 * 3 := by
    rw [← hcard]
  exact Nat.mul_right_cancel (by norm_num) hmain

private theorem map_comap_centralizer_le_autFixed {Mt : GL (Fin 3) k} :
    ((Subgroup.centralizer {Mt}).comap Matrix.SpecialLinearGroup.toGL).map (proj 3 k) ≤
      GL3TwoFixedModel.autFixed (conjAut 3 k Mt) := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
  rw [GL3TwoFixedModel.mem_autFixed, conjAut_proj]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  have hcomm : Matrix.SpecialLinearGroup.toGL g * Mt =
      Mt * Matrix.SpecialLinearGroup.toGL g :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  calc Mt * Matrix.SpecialLinearGroup.toGL g * Mt⁻¹
      = Matrix.SpecialLinearGroup.toGL g * Mt * Mt⁻¹ := by rw [← hcomm]
    _ = Matrix.SpecialLinearGroup.toGL g := by group

private theorem autFixed_le_normalizer_map_comap_centralizer {Mt : GL (Fin 3) k} :
    GL3TwoFixedModel.autFixed (conjAut 3 k Mt) ≤
      Subgroup.normalizer
        (((Subgroup.centralizer {Mt}).comap Matrix.SpecialLinearGroup.toGL).map (proj 3 k) :
          Set (projectiveSL 3 k)) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh n hn
  obtain ⟨x, rfl⟩ := proj_surjective 3 k h
  have hh' : conjAut 3 k Mt (proj 3 k x) = proj 3 k x := hh
  obtain ⟨s, hs, hsc⟩ := exists_scalars_of_conjAut (A := Mt) (g := x) (x := x) hh'
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hn
  have hxg : x * g * x⁻¹ ∈
      (Subgroup.centralizer {Mt}).comap Matrix.SpecialLinearGroup.toGL := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    set A : GL (Fin 3) k := Mt
    set X : GL (Fin 3) k := Matrix.SpecialLinearGroup.toGL x
    set G : GL (Fin 3) k := Matrix.SpecialLinearGroup.toGL g
    set S : GL (Fin 3) k := Matrix.SpecialLinearGroup.toGL s
    have hS : ∀ Y : GL (Fin 3) k, S * Y = Y * S :=
      fun Y => (Subgroup.mem_center_iff.mp (toGL_mem_center hs) Y).symm
    have hGA : G * A = A * G :=
      Subgroup.mem_centralizer_singleton_iff.mp hg
    have hAX : A * X = X * A * S := by
      have h := hsc
      calc A * X = A * X * A⁻¹ * A := by group
        _ = (X * S) * A := by rw [h]
        _ = X * (S * A) := by group
        _ = X * (A * S) := by rw [hS A]
        _ = X * A * S := by group
    rw [map_mul, map_mul, map_inv]
    change X * G * X⁻¹ * A = A * (X * G * X⁻¹)
    have hXinvA : X⁻¹ * A = A * S * X⁻¹ := by
      calc X⁻¹ * A = X⁻¹ * A * X * X⁻¹ := by group
        _ = X⁻¹ * (A * X) * X⁻¹ := by group
        _ = X⁻¹ * (X * A * S) * X⁻¹ := by rw [hAX]
        _ = A * S * X⁻¹ := by group
    have hAS : A * S = X⁻¹ * (A * X) := by
      rw [hAX]
      group
    calc X * G * X⁻¹ * A
        = X * G * (X⁻¹ * A) := by group
      _ = X * G * (A * S * X⁻¹) := by rw [hXinvA]
      _ = X * G * A * S * X⁻¹ := by group
      _ = X * (G * A) * S * X⁻¹ := by group
      _ = X * (A * G) * S * X⁻¹ := by rw [hGA]
      _ = X * A * (G * S) * X⁻¹ := by group
      _ = X * A * (S * G) * X⁻¹ := by rw [hS G]
      _ = X * A * S * G * X⁻¹ := by group
      _ = X * (A * S) * G * X⁻¹ := by group
      _ = X * (X⁻¹ * (A * X)) * G * X⁻¹ := by rw [hAS]
      _ = (A * X) * G * X⁻¹ := by group
      _ = A * (X * G * X⁻¹) := by group
  refine Subgroup.mem_map.mpr ⟨x * g * x⁻¹, hxg, ?_⟩
  simp only [map_mul, map_inv]

private theorem exists_singer_witness (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1)
    {Mt : GL (Fin 3) k}
    (hpow : (Mt : Matrix (Fin 3) (Fin 3) k) ^ 3 = (u : k) • 1)
    (hdet : GeneralLinearGroup.det Mt ≠ 1) :
    ∃ s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3)
        (GL3TwoFixedModel.autFixed (conjAut 3 k Mt)),
      aP u * s * (aP u)⁻¹ ≠ s := by
  haveI := LinearFieldFour.finite_of_card_eq_four hk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k) :=
    (Subgroup.centralizer {Mt}).comap Matrix.SpecialLinearGroup.toGL with hDdef
  set N : Subgroup (projectiveSL 3 k) := D.map (proj 3 k) with hNdef
  have hNle : N ≤ GL3TwoFixedModel.autFixed (conjAut 3 k Mt) := by
    rw [hNdef]
    exact map_comap_centralizer_le_autFixed
  have hNnorm : GL3TwoFixedModel.autFixed (conjAut 3 k Mt) ≤
      Subgroup.normalizer (N : Set (projectiveSL 3 k)) := by
    rw [hNdef]
    exact autFixed_le_normalizer_map_comap_centralizer
  have hNcard : Nat.card N = 7 := by
    rw [hNdef]
    exact card_map_comap_centralizer hk hu hpow hdet
  have hNcyc : IsCyclic N := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact isCyclic_of_prime_card hNcard
  have hNsolv : Group.IsSolvable N := by
    haveI := hNcyc
    exact Group.isSolvable_of_comm fun a b => mul_comm' a b
  have hnormSub : (N.subgroupOf (GL3TwoFixedModel.autFixed (conjAut 3 k Mt))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNnorm
  have hsolvSub : Group.IsSolvable
      ↥(N.subgroupOf (GL3TwoFixedModel.autFixed (conjAut 3 k Mt))) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNle).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNle).injective
  have hcardSub : Nat.card
      ↥(N.subgroupOf (GL3TwoFixedModel.autFixed (conjAut 3 k Mt))) = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv, hNcard]
  have hcore := (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
    (H := GL3TwoFixedModel.autFixed (conjAut 3 k Mt)) Nat.prime_three).2.2.2.1
      (N.subgroupOf (GL3TwoFixedModel.autFixed (conjAut 3 k Mt))) hnormSub hsolvSub
      (by rw [hcardSub]; norm_num)
  have hnotle : ¬ N ≤ eZero k := by
    intro hle
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hNcard, card_eZero hk] at hdvd
    norm_num at hdvd
  obtain ⟨s, hsN, hsE⟩ := Set.not_subset.mp hnotle
  have hsH : s ∈ GL3TwoFixedModel.autFixed (conjAut 3 k Mt) := hNle hsN
  refine ⟨s, Subgroup.mem_map.mpr ⟨⟨s, hsH⟩, hcore ?_, rfl⟩, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr hsN
  · intro heq
    have hcent : s ∈ Subgroup.centralizer ({aP u} : Set (projectiveSL 3 k)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : aP u * s = s * aP u := by
        calc aP u * s = aP u * s * (aP u)⁻¹ * aP u := by group
          _ = s * aP u := by rw [heq]
      exact this.symm
    rw [centralizer_aP hk hu] at hcent
    exact hsE hcent

private theorem pglSylowMax_singer_aux (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1)
    {j : ℕ} (hj : j = 1 ∨ j = 2) :
    conjAut 3 k (diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ j) ∈
        pglSylowMax u ⟨j + 1, by rcases hj with rfl | rfl <;> norm_num⟩ ∧
      (((diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ j : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) ^ 3) = (u : k) • 1 ∧
      GeneralLinearGroup.det (diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ j) ≠ 1 := by
  have hy : yInn (k := k) = conjAut 3 k (Matrix.SpecialLinearGroup.toGL rSL) := by
    rw [yInn, bP, ← conjAut_toGL]
  refine ⟨?_, diagGL_mul_rSL_pow_three hk hu j hj, ?_⟩
  · have hε : CFSG.RankThree.Asc83Table.ex27Rep (xDiag u) yInn
        ⟨j + 1, by rcases hj with rfl | rfl <;> norm_num⟩ =
        conjAut 3 k (diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ j) := by
      rcases hj with rfl | rfl
      · show xDiag u * yInn =
          conjAut 3 k (diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ 1)
        simp only [xDiag, hy]
        rw [pow_one, ← map_mul]
      · show xDiag u * yInn ^ 2 =
          conjAut 3 k (diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ 2)
        simp only [xDiag, hy]
        rw [← map_pow, ← map_mul]
    have hmem : CFSG.RankThree.Asc83Table.ex27Rep (xDiag u) yInn
        ⟨j + 1, by rcases hj with rfl | rfl <;> norm_num⟩ ∈
        pglSylowMax u ⟨j + 1, by rcases hj with rfl | rfl <;> norm_num⟩ := by
      simp only [pglSylowMax]
      exact Subgroup.subset_closure (by simp)
    rwa [hε] at hmem
  · rw [det_diagGL_mul_rSL_pow (u := u) j]
    exact hu

theorem pglSylowMax_singer (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) (i : Fin 4)
    (hi : i = 2 ∨ i = 3) :
    ∃ ε ∈ pglSylowMax u i,
      ε ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∧
      ∃ s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3)
          (GL3TwoFixedModel.autFixed ε),
        aP u * s * (aP u)⁻¹ ≠ s := by
  rcases hi with rfl | rfl
  · obtain ⟨hmem, hpow, hdet⟩ :=
      pglSylowMax_singer_aux (hk := hk) (hu := hu) (j := 1) (by norm_num)
    have houter : conjAut 3 k (diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ 1) ∉
        (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
      intro hmem'
      exact hdet ((conjAut_mem_range_conj_iff hk _).mp hmem')
    exact ⟨conjAut 3 k (diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ 1), hmem, houter,
      exists_singer_witness hk hu hpow hdet⟩
  · obtain ⟨hmem, hpow, hdet⟩ :=
      pglSylowMax_singer_aux (hk := hk) (hu := hu) (j := 2) (by norm_num)
    have houter : conjAut 3 k (diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ 2) ∉
        (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
      intro hmem'
      exact hdet ((conjAut_mem_range_conj_iff hk _).mp hmem')
    exact ⟨conjAut 3 k (diagGL u * (Matrix.SpecialLinearGroup.toGL rSL) ^ 2), hmem, houter,
      exists_singer_witness hk hu hpow hdet⟩

end CFSG.RankThree.PartTwo.KFacts.L34
