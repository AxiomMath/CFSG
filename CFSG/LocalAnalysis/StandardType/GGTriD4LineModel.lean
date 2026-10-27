module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.StandardType

@[expose] noncomputable def triD4LineFibre (k K : Type) [Field k] [Field K] [Algebra k K] :
    Subgroup (GL (Fin 3) k × Kˣ) :=
  MonoidHom.eqLocus (Matrix.GeneralLinearGroup.det.comp (MonoidHom.fst _ _))
    ((Units.map (Algebra.norm k (S := K))).comp (MonoidHom.snd _ _))

@[expose] noncomputable def triD4LineDiag (k K : Type) [Field k] [Field K] [Algebra k K] :
    Subgroup (triD4LineFibre k K) :=
  Subgroup.comap (triD4LineFibre k K).subtype
    (MonoidHom.range (MonoidHom.prod
      (Units.map (Matrix.scalar (Fin 3) : k →+* Matrix (Fin 3) (Fin 3) k).toMonoidHom)
      (Units.map (algebraMap k K).toMonoidHom)))

theorem triD4LineDiag_le_center (k K : Type) [Field k] [Field K] [Algebra k K] :
    triD4LineDiag k K ≤ Subgroup.center (triD4LineFibre k K) := by
  rintro x ⟨μ, hμ⟩
  refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
  change (g : GL (Fin 3) k × Kˣ) * x = x * g
  rw [show (x : GL (Fin 3) k × Kˣ) = _ from hμ.symm]
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (mul_comm _ _)
  simp [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

instance triD4LineDiag_normal (k K : Type) [Field k] [Field K] [Algebra k K] :
    (triD4LineDiag k K).Normal :=
  Subgroup.normal_of_le_center (triD4LineDiag_le_center k K)

abbrev TriD4LineX (k K : Type) [Field k] [Field K] [Algebra k K] : Type :=
  triD4LineFibre k K ⧸ triD4LineDiag k K

@[expose] noncomputable def triD4LineProdSigma (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) : (GL (Fin 3) k × Kˣ) ≃* (GL (Fin 3) k × Kˣ) :=
  MulEquiv.prodCongr (MulEquiv.refl _) (Units.mapEquiv σ.toRingEquiv.toMulEquiv)

theorem triD4LineProdSigma_mem_fibre_iff (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (x : GL (Fin 3) k × Kˣ) :
    triD4LineProdSigma k K σ x ∈ triD4LineFibre k K ↔ x ∈ triD4LineFibre k K := by
  have h : Units.map (Algebra.norm k (S := K)) (Units.mapEquiv σ.toRingEquiv.toMulEquiv x.2) =
      Units.map (Algebra.norm k (S := K)) x.2 :=
    Units.ext (Algebra.norm_eq_of_algEquiv σ (x.2 : K))
  change Matrix.GeneralLinearGroup.det x.1 = Units.map (Algebra.norm k (S := K))
      (Units.mapEquiv σ.toRingEquiv.toMulEquiv x.2) ↔
    Matrix.GeneralLinearGroup.det x.1 = Units.map (Algebra.norm k (S := K)) x.2
  rw [h]

theorem triD4LineFibre_map_prodSigma (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) :
    (triD4LineFibre k K).map (triD4LineProdSigma k K σ).toMonoidHom = triD4LineFibre k K := by
  ext x
  rw [Subgroup.mem_map_equiv, ← triD4LineProdSigma_mem_fibre_iff k K σ, MulEquiv.apply_symm_apply]

@[expose] noncomputable def triD4LineFibreSigma (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) : triD4LineFibre k K ≃* triD4LineFibre k K :=
  ((triD4LineProdSigma k K σ).subgroupMap (triD4LineFibre k K)).trans
    (MulEquiv.subgroupCongr (triD4LineFibre_map_prodSigma k K σ))

theorem triD4LineFibreSigma_eq_of_mem_diag (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) {x : triD4LineFibre k K} (hx : x ∈ triD4LineDiag k K) :
    triD4LineFibreSigma k K σ x = x := by
  obtain ⟨μ, hμ⟩ := hx
  apply Subtype.ext
  change triD4LineProdSigma k K σ x = x
  rw [show (x : GL (Fin 3) k × Kˣ) = _ from hμ.symm]
  refine Prod.ext rfl (Units.ext ?_)
  change σ (algebraMap k K (μ : k)) = algebraMap k K (μ : k)
  exact σ.commutes _

theorem triD4LineDiag_map_fibreSigma (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) :
    (triD4LineDiag k K).map (triD4LineFibreSigma k K σ).toMonoidHom = triD4LineDiag k K := by
  ext x
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hx
    have h := triD4LineFibreSigma_eq_of_mem_diag k K σ hx
    rw [MulEquiv.apply_symm_apply] at h
    rw [h]
    exact hx
  · intro hx
    rw [← triD4LineFibreSigma_eq_of_mem_diag k K σ hx, MulEquiv.symm_apply_apply]
    exact hx

@[expose] noncomputable def triD4LineSigma (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) : TriD4LineX k K ≃* TriD4LineX k K :=
  QuotientGroup.congr (triD4LineDiag k K) (triD4LineDiag k K) (triD4LineFibreSigma k K σ)
    (triD4LineDiag_map_fibreSigma k K σ)

@[expose] noncomputable def triD4LineN0 (k K : Type) [Field k] [Field K] [Algebra k K] :
    Subgroup (TriD4LineX k K) :=
  ((MonoidHom.snd (GL (Fin 3) k) Kˣ).ker.comap (triD4LineFibre k K).subtype).map
    (QuotientGroup.mk' (triD4LineDiag k K))

@[expose] noncomputable def triD4LineMk (k K : Type) [Field k] [Field K] [Algebra k K]
    (g : GL (Fin 3) k) (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c) :
    TriD4LineX k K :=
  QuotientGroup.mk (⟨(g, c), h⟩ : triD4LineFibre k K)

theorem triD4LineMk_surjective (k K : Type) [Field k] [Field K] [Algebra k K]
    (x : TriD4LineX k K) :
    ∃ (g : GL (Fin 3) k) (c : Kˣ)
      (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c),
      triD4LineMk k K g c h = x := by
  obtain ⟨⟨⟨g, c⟩, h⟩, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨g, c, h, rfl⟩

theorem triD4LineMk_mul (k K : Type) [Field k] [Field K] [Algebra k K]
    (g g' : GL (Fin 3) k) (c c' : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c')
    (h'' : Matrix.GeneralLinearGroup.det (g * g') = Units.map (Algebra.norm k (S := K)) (c * c')) :
    triD4LineMk k K g c h * triD4LineMk k K g' c' h' = triD4LineMk k K (g * g') (c * c') h'' := by
  rfl

theorem triD4LineMk_inv (k K : Type) [Field k] [Field K] [Algebra k K]
    (g : GL (Fin 3) k) (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g⁻¹ = Units.map (Algebra.norm k (S := K)) c⁻¹) :
    (triD4LineMk k K g c h)⁻¹ = triD4LineMk k K g⁻¹ c⁻¹ h' := by
  rfl

theorem triD4LineMk_pow (k K : Type) [Field k] [Field K] [Algebra k K]
    (g : GL (Fin 3) k) (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c) (j : ℕ)
    (h' : Matrix.GeneralLinearGroup.det (g ^ j) = Units.map (Algebra.norm k (S := K)) (c ^ j)) :
    triD4LineMk k K g c h ^ j = triD4LineMk k K (g ^ j) (c ^ j) h' := by
  rfl

theorem triD4LineMk_one (k K : Type) [Field k] [Field K] [Algebra k K]
    (h : Matrix.GeneralLinearGroup.det (1 : GL (Fin 3) k) =
      Units.map (Algebra.norm k (S := K)) 1) :
    triD4LineMk k K 1 1 h = 1 := by
  rfl

theorem triD4LineMk_eq_mk_iff (k K : Type) [Field k] [Field K] [Algebra k K]
    (g g' : GL (Fin 3) k) (c c' : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c') :
    triD4LineMk k K g c h = triD4LineMk k K g' c' h' ↔
      ∃ μ : kˣ, g' = Matrix.GeneralLinearGroup.scalar (Fin 3) μ * g ∧
        c' = Units.map (algebraMap k K).toMonoidHom μ * c := by
  unfold triD4LineMk
  rw [QuotientGroup.eq]
  simp only [triD4LineDiag, Subgroup.mem_comap, MonoidHom.mem_range, MonoidHom.prod_apply,
    Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, Prod.inv_mk, Prod.mk_mul_mk,
    Prod.mk.injEq]
  refine exists_congr fun μ => and_congr ?_ ?_
  · change Matrix.GeneralLinearGroup.scalar (Fin 3) μ = g⁻¹ * g' ↔ _
    rw [eq_inv_mul_iff_mul_eq, ← Matrix.GeneralLinearGroup.scalar_commute, eq_comm]
  · rw [eq_inv_mul_iff_mul_eq, mul_comm, eq_comm]

theorem triD4LineMk_eq_one_iff (k K : Type) [Field k] [Field K] [Algebra k K]
    (g : GL (Fin 3) k) (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c) :
    triD4LineMk k K g c h = 1 ↔
      ∃ μ : kˣ, g = Matrix.GeneralLinearGroup.scalar (Fin 3) μ ∧
        c = Units.map (algebraMap k K).toMonoidHom μ := by
  unfold triD4LineMk
  rw [QuotientGroup.eq_one_iff]
  simp only [triD4LineDiag, Subgroup.mem_comap, MonoidHom.mem_range, MonoidHom.prod_apply,
    Subgroup.coe_subtype, Prod.mk.injEq]
  exact exists_congr fun μ => ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩

theorem triD4LineSigma_mk (k K : Type) [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (g : GL (Fin 3) k) (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g =
      Units.map (Algebra.norm k (S := K)) (Units.mapEquiv σ.toRingEquiv.toMulEquiv c)) :
    triD4LineSigma k K σ (triD4LineMk k K g c h) =
      triD4LineMk k K g (Units.mapEquiv σ.toRingEquiv.toMulEquiv c) h' := by
  rfl

theorem triD4LineSigma_mul_apply (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ τ : K ≃ₐ[k] K) (x : TriD4LineX k K) :
    triD4LineSigma k K (σ * τ) x = triD4LineSigma k K σ (triD4LineSigma k K τ x) := by
  induction x using QuotientGroup.induction_on
  rfl

theorem triD4LineSigma_one_apply (k K : Type) [Field k] [Field K] [Algebra k K]
    (x : TriD4LineX k K) : triD4LineSigma k K 1 x = x := by
  induction x using QuotientGroup.induction_on
  rfl

theorem triD4LineMk_mem_N0_iff (k K : Type) [Field k] [Field K] [Algebra k K]
    (hdeg : Module.finrank k K = 3) (g : GL (Fin 3) k) (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c) :
    triD4LineMk k K g c h ∈ triD4LineN0 k K ↔
      ∃ μ : kˣ, c = Units.map (algebraMap k K).toMonoidHom μ := by
  constructor
  · rintro ⟨⟨⟨g₀, c₀⟩, h₀⟩, hc₀, hy⟩
    obtain ⟨μ, -, hμ⟩ := (triD4LineMk_eq_mk_iff k K g₀ g c₀ c h₀ h).1 hy
    have hc₀1 : c₀ = 1 := hc₀
    exact ⟨μ, by rw [hμ, hc₀1, mul_one]⟩
  · rintro ⟨μ, rfl⟩
    have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * g) =
        Units.map (Algebra.norm k (S := K)) 1 := by
      refine Units.ext ?_
      rw [map_mul, h, Matrix.GeneralLinearGroup.det_scalar, map_one, Fintype.card_fin]
      simp [Algebra.norm_algebraMap, hdeg]
    refine ⟨⟨(_, 1), hdet⟩, rfl, ?_⟩
    refine (triD4LineMk_eq_mk_iff k K _ g 1 _ hdet h).2 ⟨μ, ?_, by rw [mul_one]⟩
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem mem_triD4LineN0_iff (k K : Type) [Field k] [Field K] [Algebra k K]
    (y : TriD4LineX k K) :
    y ∈ triD4LineN0 k K ↔ ∃ (g : GL (Fin 3) k)
      (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) 1),
      triD4LineMk k K g 1 h = y := by
  constructor
  · rintro ⟨⟨⟨g, c⟩, h⟩, hc, rfl⟩
    have hc1 : c = 1 := hc
    subst hc1
    exact ⟨g, h, rfl⟩
  · rintro ⟨g, h, rfl⟩
    exact ⟨⟨(g, 1), h⟩, rfl, rfl⟩

instance triD4LineN0_normal (k K : Type) [Field k] [Field K] [Algebra k K] :
    (triD4LineN0 k K).Normal := by
  exact ((MonoidHom.normal_ker _).comap _).map _ (QuotientGroup.mk'_surjective _)

theorem triD4LineSigma_eq_self_of_mem_N0 (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) {y : TriD4LineX k K} (hy : y ∈ triD4LineN0 k K) :
    triD4LineSigma k K σ y = y := by
  obtain ⟨g, h, rfl⟩ := (mem_triD4LineN0_iff k K y).1 hy
  have h1 : Units.mapEquiv σ.toRingEquiv.toMulEquiv 1 = 1 := map_one _
  rw [triD4LineSigma_mk k K σ g 1 h (by rw [h1]; exact h)]
  congr 1

theorem triD4LineMk_mem_center_iff (k K : Type) [Field k] [Field K] [Algebra k K]
    (g : GL (Fin 3) k) (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c) :
    triD4LineMk k K g c h ∈ Subgroup.center (TriD4LineX k K) ↔
      ∃ μ : kˣ, g = Matrix.GeneralLinearGroup.scalar (Fin 3) μ := by
  constructor
  · intro hz
    have hcomm : ∀ t : Matrix.TransvectionStruct (Fin 3) k,
        Commute t.toMatrix (g : Matrix (Fin 3) (Fin 3) k) := by
      intro t
      let T : GL (Fin 3) k := ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩
      have hT : Matrix.GeneralLinearGroup.det T = Units.map (Algebra.norm k (S := K)) 1 :=
        Units.ext (by rw [map_one]; exact t.det)
      have he := (Subgroup.mem_center_iff.mp hz) (triD4LineMk k K T 1 hT)
      rw [triD4LineMk_mul k K T g 1 c hT h (by rw [map_mul, map_mul, hT, h]),
        triD4LineMk_mul k K g T c 1 h hT (by rw [map_mul, map_mul, hT, h])] at he
      obtain ⟨μ, hμg, hμc⟩ := (triD4LineMk_eq_mk_iff k K _ _ _ _ _ _).1 he
      have hμ : μ = 1 := by
        have h1 : Units.map (algebraMap k K).toMonoidHom μ = 1 := by
          simpa [mul_comm] using hμc.symm
        exact Units.ext ((algebraMap k K).injective (by
          simpa using congrArg Units.val h1))
      rw [hμ, map_one, one_mul] at hμg
      exact congrArg Units.val hμg.symm
    obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm
    have hr0 : r ≠ 0 := by
      rintro rfl
      have := g.isUnit.map (Matrix.detMonoidHom (n := Fin 3) (R := k))
      simp [← hr] at this
    refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, ← hr]
    rfl
  · rintro ⟨μ, rfl⟩
    refine Subgroup.mem_center_iff.mpr fun x => ?_
    induction x using QuotientGroup.induction_on with | H a => ?_
    obtain ⟨⟨g', c'⟩, h₀⟩ := a
    have h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c' := h₀
    change triD4LineMk k K g' c' h' * triD4LineMk k K _ c h =
      triD4LineMk k K _ c h * triD4LineMk k K g' c' h'
    rw [triD4LineMk_mul k K _ _ _ _ h' h (by rw [map_mul, map_mul, h, h']),
      triD4LineMk_mul k K _ _ _ _ h h' (by rw [map_mul, map_mul, h, h'])]
    simp only [Matrix.GeneralLinearGroup.scalar_commute, mul_comm c' c]

private theorem exists_algebraMap_of_pow_three_aux (k K : Type) [Field k] [Field K] [Algebra k K]
    [Finite K] (h3 : 3 ∣ Nat.card k - 1) (c : K) (hc : c ^ 3 = 1) :
    ∃ a : k, algebraMap k K a = c := by
  have : Finite k := Finite.of_injective _ (algebraMap k K).injective
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := kˣ) 3 (by rwa [Nat.card_units])
  have hprim : IsPrimitiveRoot (ω : k) 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr (hω ▸ IsPrimitiveRoot.orderOf ω)
  obtain ⟨i, -, hi⟩ :=
    (hprim.map_of_injective (algebraMap k K).injective).eq_pow_of_pow_eq_one hc
  exact ⟨(ω : k) ^ i, by rw [map_pow, hi]⟩

theorem triD4Line_eq_mk_of_mem_center (k K : Type) [Field k] [Field K] [Algebra k K]
    [Finite K] (h3 : 3 ∣ Nat.card k - 1)
    {z : TriD4LineX k K} (hz : z ∈ Subgroup.center (TriD4LineX k K)) (hz3 : orderOf z = 3) :
    ∃ ζ : kˣ, ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧
      ∃ h : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ) =
        Units.map (Algebra.norm k (S := K)) 1,
        triD4LineMk k K (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ) 1 h = z := by
  obtain ⟨g, c, h, rfl⟩ := triD4LineMk_surjective k K z
  obtain ⟨μ, rfl⟩ := (triD4LineMk_mem_center_iff k K g c h).1 hz
  have hz1 :=
    pow_orderOf_eq_one (triD4LineMk k K (Matrix.GeneralLinearGroup.scalar (Fin 3) μ) c h)
  rw [hz3, triD4LineMk_pow k K _ c h 3 (by rw [map_pow, map_pow, h])] at hz1
  obtain ⟨ν, hν, hνc⟩ := (triD4LineMk_eq_one_iff k K _ _ _).1 hz1
  have hμν : μ ^ 3 = ν := by
    have hν' : Matrix.GeneralLinearGroup.scalar (Fin 3) (μ ^ 3) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ν := by
      rw [map_pow]
      exact hν
    have h00 := congrArg (fun A : GL (Fin 3) k => (A : Matrix (Fin 3) (Fin 3) k) 0 0) hν'
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h00
    exact Units.ext h00
  set m : Kˣ := Units.map (algebraMap k K).toMonoidHom μ with hm
  have hcube : (c * m⁻¹) ^ 3 = 1 := by
    rw [mul_pow, hνc, ← hμν, map_pow, inv_pow, mul_inv_cancel]
  obtain ⟨a, ha⟩ := exists_algebraMap_of_pow_three_aux k K h3 ((c * m⁻¹ : Kˣ) : K)
    (by rw [← Units.val_pow_eq_pow_val, hcube, Units.val_one])
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (c * m⁻¹).ne_zero ha.symm
  set u : kˣ := Units.mk0 a ha0 with hu
  have hu3 : u ^ 3 = 1 := by
    refine Units.ext ((algebraMap k K).injective ?_)
    rw [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one, hu, Units.val_mk0, ha,
      ← Units.val_pow_eq_pow_val, hcube, Units.val_one]
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹) =
      Units.map (Algebra.norm k (S := K)) 1 := by
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, hu3, inv_one, map_one]
  have heq : triD4LineMk k K (Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹) 1 hdet =
      triD4LineMk k K (Matrix.GeneralLinearGroup.scalar (Fin 3) μ) c h := by
    refine (triD4LineMk_eq_mk_iff k K _ _ 1 c hdet h).2 ⟨μ * u, ?_, ?_⟩
    · rw [← map_mul, mul_inv_cancel_right]
    · refine Units.ext ?_
      have hmv : ((m : Kˣ) : K) = algebraMap k K (μ : k) := rfl
      have hca : (c : K) = algebraMap k K (μ : k) * algebraMap k K a := by
        rw [ha, ← hmv, Units.val_mul, mul_comm (c : K), ← mul_assoc, Units.mul_inv, one_mul]
      simp [hca, hu]
  refine ⟨u⁻¹, by rw [inv_pow, hu3, inv_one], fun hu1 => ?_, hdet, heq⟩
  have h1 : triD4LineMk k K (Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹) 1 hdet = 1 :=
    (triD4LineMk_eq_one_iff k K _ _ _).2 ⟨1, by rw [hu1], by rw [map_one]⟩
  rw [heq] at h1
  rw [h1, orderOf_one] at hz3
  exact absurd hz3 (by norm_num)

private theorem triD4Line_pow_bijective (k K : Type) [Field k] [Field K] [Algebra k K] [Finite K]
    (hdeg : Module.finrank k K = 3) (σ : K ≃ₐ[k] K) (hσ : orderOf σ = 3) :
    Function.Bijective (fun i : Fin 3 => σ ^ (i : ℕ)) := by
  have : Finite k := Finite.of_injective _ (algebraMap k K).injective
  have : FiniteDimensional k K := Module.Finite.of_finite
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun i j hij => Fin.ext (pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hσ]; exact i.isLt)
    (by rw [Set.mem_Iio, hσ]; exact j.isLt) hij), ?_⟩
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdeg]

theorem triD4Line_algebraMap_norm (k K : Type) [Field k] [Field K] [Algebra k K] [Finite K]
    (hdeg : Module.finrank k K = 3) (σ : K ≃ₐ[k] K) (hσ : orderOf σ = 3) (c : K) :
    algebraMap k K (Algebra.norm k c) = c * σ c * (σ ^ 2) c := by
  have : Finite k := Finite.of_injective _ (algebraMap k K).injective
  have : FiniteDimensional k K := Module.Finite.of_finite
  rw [Algebra.norm_eq_prod_automorphisms, ← Fintype.prod_bijective _
    (triD4Line_pow_bijective k K hdeg σ hσ) (fun i : Fin 3 => (σ ^ (i : ℕ)) c) _ (fun _ => rfl),
    Fin.prod_univ_three]
  simp

theorem triD4Line_exists_algebraMap_of_sigma_eq (k K : Type) [Field k] [Field K] [Algebra k K]
    [Finite K] (hdeg : Module.finrank k K = 3) (σ : K ≃ₐ[k] K) (hσ : orderOf σ = 3) (c : K)
    (hc : σ c = c) : ∃ a : k, algebraMap k K a = c := by
  have : Finite k := Finite.of_injective _ (algebraMap k K).injective
  have : FiniteDimensional k K := Module.Finite.of_finite
  have key : ∀ n : ℕ, (σ ^ n) c = c := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hc, ih]
  refine (IsGalois.mem_range_algebraMap_iff_fixed c).2 fun τ => ?_
  obtain ⟨i, rfl⟩ := (triD4Line_pow_bijective k K hdeg σ hσ).2 τ
  exact key i

theorem triD4Line_exists_algebraMap_of_pow_three (k K : Type) [Field k] [Field K] [Algebra k K]
    [Finite K] (h3 : 3 ∣ Nat.card k - 1) (c : K) (hc : c ^ 3 = 1) :
    ∃ a : k, algebraMap k K a = c := by
  exact exists_algebraMap_of_pow_three_aux k K h3 c hc

instance triD4LineX_finite (k K : Type) [Field k] [Field K] [Algebra k K] [Finite K] :
    Finite (TriD4LineX k K) := by
  have : Finite k := Finite.of_injective _ (algebraMap k K).injective
  infer_instance

end CFSG.StandardType
