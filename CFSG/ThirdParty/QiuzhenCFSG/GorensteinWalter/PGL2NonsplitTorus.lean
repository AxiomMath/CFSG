module


public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27

namespace CFSG
end CFSG
open CFSG

/-!
# The nonsplit reflected torus in `PGL₂`

The multiplication representation of a quadratic finite-field extension,
modulo scalar matrices, gives a cyclic projective torus of order `|F| + 1`.
The quadratic Frobenius is an external projective involution and acts on that
torus by inversion.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- The standard nonsplit torus of `PGL₂(F)`, together with its Frobenius
reflection. -/
public theorem pgl2_nonsplit_torus_reflection_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ U : Subgroup (PGL2 F), ∃ w : PGL2 F,
      IsCyclic U ∧ Nat.card U = Nat.card F + 1 ∧
      w ∉ U ∧ w * w = 1 ∧
      (∀ t : PGL2 F, t ∈ U → w * t * w⁻¹ = t⁻¹) ∧
      (Odd (Nat.card F) →
        ¬ U ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL
          (n := Fin 2) (R := F)).range) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  let E := FiniteField.Extension F p 2
  let : Fintype E := Fintype.ofFinite E
  have hidx :
      Fintype.card (Module.Free.ChooseBasisIndex F E) =
        Fintype.card (Fin 2) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, Fintype.card_fin]
    simpa [E] using (FiniteField.finrank_extension F p 2)
  let eidx : Module.Free.ChooseBasisIndex F E ≃ Fin 2 :=
    Fintype.equivOfCardEq hidx
  let b : Module.Basis (Fin 2) F E :=
    (Module.Free.chooseBasis F E).reindex eidx
  let mulGL (x : Eˣ) : GL (Fin 2) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Algebra.leftMulMatrix b (x : E)) (by
        apply Matrix.det_ne_zero_of_left_inverse
          (B := Algebra.leftMulMatrix b ((x⁻¹ : Eˣ) : E))
        rw [← map_mul]
        simp)
  let mulHom : Eˣ →* GL (Fin 2) F :=
    { toFun := mulGL
      map_one' := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        simp [mulGL]
      map_mul' := by
        intro x y
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        simp [mulGL] }
  let torus : Eˣ →* PGL2 F :=
    Matrix.ProjGenLinGroup.mk.comp mulHom
  let scalarUnits : Fˣ →* Eˣ := Units.map (algebraMap F E)
  have hscalar_inj : Function.Injective scalarUnits := by
    intro x y hxy
    apply Units.ext
    apply (algebraMap F E).injective
    exact congrArg Units.val hxy
  have hker : torus.ker = scalarUnits.range := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro hx
      have hcenter : mulGL x ∈ Subgroup.center (GL (Fin 2) F) :=
        Matrix.ProjGenLinGroup.mk_eq_one.mp hx
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
      rcases hcenter with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      apply Units.ext
      apply Algebra.leftMulMatrix_injective b
      calc
        Algebra.leftMulMatrix b ((scalarUnits r : Eˣ) : E) =
            Algebra.leftMulMatrix b (algebraMap F E (r : F)) := rfl
        _ = algebraMap F (Matrix (Fin 2) (Fin 2) F) (r : F) :=
          (Algebra.leftMulMatrix b).commutes (r : F)
        _ = Matrix.scalar (Fin 2) (r : F) := rfl
        _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) r :
            Matrix (Fin 2) (Fin 2) F) := rfl
        _ = (mulGL x : Matrix (Fin 2) (Fin 2) F) := by rw [hr]
        _ = Algebra.leftMulMatrix b (x : E) := rfl
    · rintro ⟨r, rfl⟩
      apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      refine ⟨r, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change (Matrix.GeneralLinearGroup.scalar (Fin 2) r :
          Matrix (Fin 2) (Fin 2) F) i j =
        Algebra.leftMulMatrix b
          ((scalarUnits r : Eˣ) : E) i j
      rw [show ((scalarUnits r : Eˣ) : E) =
        algebraMap F E (r : F) by rfl]
      rw [(Algebra.leftMulMatrix b).commutes (r : F)]
      rfl
  have hker_card : Nat.card torus.ker = Nat.card F - 1 := by
    rw [hker]
    calc
      Nat.card scalarUnits.range = Nat.card Fˣ :=
        (Nat.card_congr (Equiv.ofInjective scalarUnits hscalar_inj)).symm
      _ = Nat.card F - 1 := by
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units F
  have hE_card : Nat.card E = Nat.card F ^ 2 :=
    FiniteField.natCard_extension F p 2
  have hq_factor :
      (Nat.card F - 1) * (Nat.card F + 1) = Nat.card F ^ 2 - 1 := by
    simpa [mul_comm] using
      (Nat.pow_two_sub_pow_two (Nat.card F) 1).symm
  have hdegree_exp :
      (Nat.card E - 1) / (Nat.card F - 1) = Nat.card F + 1 := by
    rw [hE_card, ← hq_factor]
    simpa [mul_comm] using Nat.mul_div_left (Nat.card F + 1)
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F)))
  have hrange_card : Nat.card torus.range = Nat.card F + 1 := by
    have hmul := torus.ker.index_mul_card
    rw [Subgroup.index_ker torus, hker_card] at hmul
    have hunits : Nat.card Eˣ = Nat.card E - 1 := by
      simpa [Nat.card_eq_fintype_card] using Fintype.card_units E
    rw [hunits, hE_card] at hmul
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F)))
    calc
      Nat.card torus.range * (Nat.card F - 1) =
          Nat.card F ^ 2 - 1 := hmul
      _ = (Nat.card F + 1) * (Nat.card F - 1) := by
        rw [← hq_factor]
        ac_rfl
  have hrange_cyclic : IsCyclic torus.range :=
    isCyclic_of_surjective torus.rangeRestrict
      torus.rangeRestrict_surjective
  let sigma : E ≃ₐ[F] E :=
    FiniteField.Extension.frob F p 2
  have hsigma_sq (x : E) : sigma (sigma x) = x := by
    change FiniteField.Extension.frob F p 2
      (FiniteField.Extension.frob F p 2 x) = x
    rw [FiniteField.Extension.frob_apply, FiniteField.Extension.frob_apply,
      ← pow_mul]
    have hcard : Nat.card F * Nat.card F = Fintype.card E := by
      rw [← pow_two, ← FiniteField.natCard_extension F p 2,
        Nat.card_eq_fintype_card]
    rw [hcard]
    exact FiniteField.pow_card x
  have hsigma_ne_one : sigma ≠ 1 := by
    intro hsigma
    change FiniteField.Extension.frob F p 2 = 1 at hsigma
    have hall : ∀ g : E ≃ₐ[F] E, g = 1 := by
      intro g
      obtain ⟨i, hi, hpow⟩ :=
        FiniteField.Extension.exists_frob_pow_eq
          (k := F) (p := p) (n := 2) g
      rw [← hpow, hsigma, one_pow]
    let : Subsingleton (E ≃ₐ[F] E) :=
      ⟨fun a d ↦ (hall a).trans (hall d).symm⟩
    have hone : Nat.card (E ≃ₐ[F] E) = 1 := Nat.card_unique
    have htwo : Nat.card (E ≃ₐ[F] E) = 2 :=
      FiniteField.natCard_algEquiv_extension F p 2
    omega
  let sigmaMat : Matrix (Fin 2) (Fin 2) F :=
    LinearMap.toMatrix b b sigma.toLinearEquiv
  have hsigmaMat_mul (x : E) :
      sigmaMat * Algebra.leftMulMatrix b x =
        Algebra.leftMulMatrix b (sigma x) * sigmaMat := by
    dsimp [sigmaMat]
    rw [Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
      ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp,
      (LinearMap.toMatrix b b).injective.eq_iff]
    ext y
    simp [LinearMap.comp_apply, Algebra.lmul]
  have hsigmaMat_sq : sigmaMat * sigmaMat = 1 := by
    dsimp [sigmaMat]
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id b,
      (LinearMap.toMatrix b b).injective.eq_iff]
    ext x
    exact hsigma_sq x
  have hsigma_det_unit : IsUnit (Matrix.det sigmaMat) := by
    simpa [sigmaMat] using
      (LinearEquiv.isUnit_det sigma.toLinearEquiv b b)
  have hsigma_det_ne : Matrix.det sigmaMat ≠ 0 :=
    hsigma_det_unit.ne_zero
  let wGL : GL (Fin 2) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero sigmaMat hsigma_det_ne
  let w : PGL2 F := Matrix.ProjGenLinGroup.mk wGL
  have hwGL_sq : wGL * wGL = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun (congrFun hsigmaMat_sq i) j
  have hw_sq : w * w = 1 := by
    change Matrix.ProjGenLinGroup.mk wGL *
      Matrix.ProjGenLinGroup.mk wGL = 1
    rw [← map_mul, hwGL_sq, map_one]
  have hw_inv : w⁻¹ = w := (eq_inv_of_mul_eq_one_right hw_sq).symm
  have hweyl_torus (x : Eˣ) :
      w * torus x * w⁻¹ = (torus x)⁻¹ := by
    rw [hw_inv]
    let sx : Eˣ := Units.map sigma.toRingEquiv.toMonoidHom x
    have hmat : wGL * mulHom x * wGL = mulGL sx := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change (sigmaMat * Algebra.leftMulMatrix b (x : E) * sigmaMat) i j =
        Algebra.leftMulMatrix b (sigma (x : E)) i j
      have hmatrix : sigmaMat * Algebra.leftMulMatrix b (x : E) * sigmaMat =
          Algebra.leftMulMatrix b (sigma (x : E)) := by
        calc
          sigmaMat * Algebra.leftMulMatrix b (x : E) * sigmaMat =
              (Algebra.leftMulMatrix b (sigma (x : E)) * sigmaMat) *
                sigmaMat := by rw [hsigmaMat_mul]
          _ = Algebra.leftMulMatrix b (sigma (x : E)) *
                (sigmaMat * sigmaMat) := by rw [Matrix.mul_assoc]
          _ = Algebra.leftMulMatrix b (sigma (x : E)) := by
                rw [hsigmaMat_sq, mul_one]
      exact congrFun (congrFun hmatrix i) j
    change Matrix.ProjGenLinGroup.mk wGL *
        Matrix.ProjGenLinGroup.mk (mulHom x) *
          Matrix.ProjGenLinGroup.mk wGL =
        (Matrix.ProjGenLinGroup.mk (mulHom x))⁻¹
    rw [← map_mul, ← map_mul, hmat]
    rw [← map_inv Matrix.ProjGenLinGroup.mk (mulHom x),
      ← map_inv mulHom x]
    apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
    have hnorm_ne : Algebra.norm F (x : E) ≠ 0 := by
      rw [Algebra.norm_eq_matrix_det b]
      apply Matrix.det_ne_zero_of_left_inverse
        (B := Algebra.leftMulMatrix b ((x⁻¹ : Eˣ) : E))
      rw [← map_mul]
      simp
    let n : Fˣ := Units.mk0 (Algebra.norm F (x : E)) hnorm_ne
    refine ⟨n⁻¹, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change (Algebra.leftMulMatrix b (sigma (x : E)) *
        Matrix.GeneralLinearGroup.scalar (Fin 2) n⁻¹) i j =
      Algebra.leftMulMatrix b ((x⁻¹ : Eˣ) : E) i j
    have hnorm_pow := FiniteField.algebraMap_norm_eq_pow
      (K := F) (K' := E) (x := (x : E))
    rw [hdegree_exp] at hnorm_pow
    have hxsigma :
        (x : E) * sigma (x : E) = algebraMap F E (Algebra.norm F (x : E)) := by
      calc
        (x : E) * sigma (x : E) =
            (x : E) * (x : E) ^ Nat.card F := by
              change (x : E) * FiniteField.Extension.frob F p 2 (x : E) = _
              rw [FiniteField.Extension.frob_apply]
        _ = (x : E) ^ (Nat.card F + 1) := by rw [pow_succ, mul_comm]
        _ = algebraMap F E (Algebra.norm F (x : E)) := hnorm_pow.symm
    have hfield :
        sigma (x : E) * algebraMap F E ((n⁻¹ : Fˣ) : F) =
          ((x⁻¹ : Eˣ) : E) := by
      apply mul_left_cancel₀ x.ne_zero
      calc
        (x : E) * (sigma (x : E) *
            algebraMap F E ((n⁻¹ : Fˣ) : F)) =
            ((x : E) * sigma (x : E)) *
              algebraMap F E ((n⁻¹ : Fˣ) : F) := by ac_rfl
        _ = algebraMap F E (Algebra.norm F (x : E)) *
              algebraMap F E ((n⁻¹ : Fˣ) : F) := by rw [hxsigma]
        _ = 1 := by simp [n]
        _ = (x : E) * ((x⁻¹ : Eˣ) : E) := by simp
    have hscalar :
        (Matrix.GeneralLinearGroup.scalar (Fin 2) n⁻¹ :
          Matrix (Fin 2) (Fin 2) F) =
        Algebra.leftMulMatrix b
          (algebraMap F E ((n⁻¹ : Fˣ) : F)) := by
      calc
        _ = algebraMap F (Matrix (Fin 2) (Fin 2) F)
            ((n⁻¹ : Fˣ) : F) := rfl
        _ = _ := ((Algebra.leftMulMatrix b).commutes
          ((n⁻¹ : Fˣ) : F)).symm
    rw [hscalar, ← map_mul, hfield]
  have hw_not_mem : w ∉ torus.range := by
    intro hw
    rcases hw with ⟨x, hx⟩
    change Matrix.ProjGenLinGroup.mk (mulHom x) =
      Matrix.ProjGenLinGroup.mk wGL at hx
    rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hx with ⟨a, ha⟩
    have hmatrix := congrArg (fun A : GL (Fin 2) F ↦
      (A : Matrix (Fin 2) (Fin 2) F)) ha
    change Algebra.leftMulMatrix b (x : E) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a :
          Matrix (Fin 2) (Fin 2) F) = sigmaMat at hmatrix
    have hscalar :
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a :
          Matrix (Fin 2) (Fin 2) F) =
        Algebra.leftMulMatrix b (algebraMap F E (a : F)) := by
      calc
        _ = algebraMap F (Matrix (Fin 2) (Fin 2) F) (a : F) := rfl
        _ = _ := ((Algebra.leftMulMatrix b).commutes (a : F)).symm
    rw [hscalar, ← map_mul] at hmatrix
    let c : E := (x : E) * algebraMap F E (a : F)
    have hlinear :
        (Algebra.lmul F E) c = sigma.toLinearEquiv.toLinearMap := by
      apply (LinearMap.toMatrix b b).injective
      rw [← Algebra.leftMulMatrix_apply]
      simpa [c, sigmaMat] using hmatrix
    have hc : c = 1 := by
      have h := LinearMap.congr_fun hlinear 1
      simpa [Algebra.lmul] using h
    apply hsigma_ne_one
    ext y
    have h := LinearMap.congr_fun hlinear y
    simpa [Algebra.lmul, hc] using h.symm
  refine ⟨torus.range, w, hrange_cyclic, hrange_card, hw_not_mem, hw_sq, ?_, ?_⟩
  · intro t ht
    rcases ht with ⟨x, rfl⟩
    exact hweyl_torus x
  · intro hodd hUle
    have hchar : ringChar F ≠ 2 := by
      intro hchar
      have heven : Fintype.card F % 2 = 0 :=
        FiniteField.even_card_of_char_two hchar
      have hodd' : Odd (Fintype.card F) := by
        simpa [Nat.card_eq_fintype_card] using hodd
      exact hodd'.not_two_dvd_nat (Nat.dvd_of_mod_eq_zero heven)
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
    have ha0 : a ≠ 0 := by
      intro ha0
      subst a
      exact ha IsSquare.zero
    obtain ⟨x, hxnorm⟩ := FiniteField.norm_surjective F E a
    have hx0 : x ≠ 0 := by
      intro hx0
      subst x
      rw [Algebra.norm_zero] at hxnorm
      exact ha0 hxnorm.symm
    let xu : Eˣ := Units.mk0 x hx0
    have hmemU : torus xu ∈ torus.range := ⟨xu, rfl⟩
    have hmemPSL := hUle hmemU
    have hsq : IsSquare ((mulHom xu).det : F) :=
      (pgl2_mk_mem_psl2_range_iff_det_isSquare (mulHom xu)).mp hmemPSL
    apply ha
    have hdet : ((mulHom xu).det : F) = Algebra.norm F x := by
      change Matrix.det (Algebra.leftMulMatrix b x) = Algebra.norm F x
      exact (Algebra.norm_eq_matrix_det b x).symm
    rw [hdet, hxnorm] at hsq
    exact hsq

end CFSG.GorensteinWalter
