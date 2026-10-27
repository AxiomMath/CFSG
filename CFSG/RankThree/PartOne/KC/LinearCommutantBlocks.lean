module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import CFSG.RankThree.PartOne.KC.MatrixAlgebraCenter
public import CFSG.RankThree.PartOne.KC.LinearCommutantPiGL

public section

namespace CFSG.RankThree.PartOne.KCLinComm

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary

variable {n : ℕ} {K : Type} [Field K]

section Units

variable (x : Module.End K (Fin n → K))

@[expose] noncomputable def commutantToMat : commutant x →ₐ[K] Matrix (Fin n) (Fin n) K :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
    Module.End K (Fin n → K)).symm.toAlgHom.comp (commutant x).val

theorem commutantToMat_injective : Function.Injective (commutantToMat x) := fun _ _ h =>
  Subtype.ext (AlgEquiv.injective (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
    Module.End K (Fin n → K)).symm h)

@[expose] noncomputable def commutantUnitsToGL : (commutant x)ˣ →* GL (Fin n) K :=
  Units.map (commutantToMat x).toRingHom.toMonoidHom

theorem commutantUnitsToGL_injective : Function.Injective (commutantUnitsToGL x) :=
  Units.map_injective (commutantToMat_injective x)

theorem coe_commutantUnitsToGL (u : (commutant x)ˣ) :
    ((commutantUnitsToGL x u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      commutantToMat x (u : commutant x) := rfl

@[expose] noncomputable def centerUnitsToUnits :
    (Subring.center (commutant x))ˣ →* (commutant x)ˣ :=
  Units.map (Subring.center (commutant x)).subtype.toMonoidHom

theorem coe_centerUnitsToUnits (z : (Subring.center (commutant x))ˣ) :
    ((centerUnitsToUnits x z : (commutant x)ˣ) : commutant x) =
      ((z : Subring.center (commutant x)) : commutant x) := rfl

theorem centerUnitsToUnits_injective : Function.Injective (centerUnitsToUnits x) :=
  Units.map_injective Subtype.val_injective

@[expose] noncomputable def centerUnitsToGL : (Subring.center (commutant x))ˣ →* GL (Fin n) K :=
  (commutantUnitsToGL x).comp (centerUnitsToUnits x)

theorem centerUnitsToGL_injective : Function.Injective (centerUnitsToGL x) :=
  (commutantUnitsToGL_injective x).comp (centerUnitsToUnits_injective x)

variable {x}

theorem toLinAlgEquiv'_eq_toLin' (M : Matrix (Fin n) (Fin n) K) :
    (Matrix.toLinAlgEquiv' M : Module.End K (Fin n → K)) = Matrix.toLin' M :=
  LinearMap.ext fun v => by rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

@[expose] noncomputable def commutantUnitOfCommute (a g : GL (Fin n) K)
    (hax : Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) = x) (h : g * a = a * g) :
    (commutant x)ˣ where
  val := ⟨Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K), by
    rw [mem_commutant, ← hax, ← toLinAlgEquiv'_eq_toLin']
    change Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K) *
      Matrix.toLinAlgEquiv' (a : Matrix (Fin n) (Fin n) K) = _
    rw [← map_mul, ← map_mul]
    exact congrArg (fun t : GL (Fin n) K =>
      Matrix.toLinAlgEquiv' (t : Matrix (Fin n) (Fin n) K)) h⟩
  inv := ⟨Matrix.toLinAlgEquiv' ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), by
    rw [mem_commutant, ← hax, ← toLinAlgEquiv'_eq_toLin']
    change Matrix.toLinAlgEquiv' ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      Matrix.toLinAlgEquiv' (a : Matrix (Fin n) (Fin n) K) = _
    rw [← map_mul, ← map_mul]
    have h' : g⁻¹ * a = a * g⁻¹ := (Commute.inv_left (show Commute g a from h)).eq
    exact congrArg (fun t : GL (Fin n) K =>
      Matrix.toLinAlgEquiv' (t : Matrix (Fin n) (Fin n) K)) h'⟩
  val_inv := Subtype.ext (by
    change Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K) *
      Matrix.toLinAlgEquiv' ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
  inv_val := Subtype.ext (by
    change Matrix.toLinAlgEquiv' ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K) = 1
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one])

theorem commutantUnitsToGL_commutantUnitOfCommute (a g : GL (Fin n) K)
    (hax : Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) = x) (h : g * a = a * g) :
    commutantUnitsToGL x (commutantUnitOfCommute a g hax h) = g := by
  refine Units.ext ?_
  rw [coe_commutantUnitsToGL]
  change (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K)).symm
    (Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K)) = _
  exact AlgEquiv.symm_apply_apply _ _

theorem range_commutantUnitsToGL_eq_centralizer (a : GL (Fin n) K)
    (hax : Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) = x) :
    (commutantUnitsToGL x).range = Subgroup.centralizer ({a} : Set (GL (Fin n) K)) := by
  ext g
  rw [MonoidHom.mem_range, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    have hu : Commute (((u : commutant x) : Module.End K (Fin n → K))) x :=
      (mem_commutant x).mp (u : commutant x).2
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_commutantUnitsToGL]
    have hxa : (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
        Module.End K (Fin n → K)).symm x = (a : Matrix (Fin n) (Fin n) K) := by
      rw [← hax, ← toLinAlgEquiv'_eq_toLin']
      exact AlgEquiv.symm_apply_apply _ _
    change (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
        Module.End K (Fin n → K)).symm (((u : commutant x) : Module.End K (Fin n → K))) *
      (a : Matrix (Fin n) (Fin n) K) = (a : Matrix (Fin n) (Fin n) K) *
      (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
        Module.End K (Fin n → K)).symm (((u : commutant x) : Module.End K (Fin n → K)))
    rw [← hxa, ← map_mul, ← map_mul]
    exact congrArg _ hu.eq
  · intro h
    exact ⟨commutantUnitOfCommute a g hax h, commutantUnitsToGL_commutantUnitOfCommute a g hax h⟩

end Units


section Theta

open scoped _root_.Classical

variable (x : Module.End K (Fin n → K))

noncomputable abbrev Efac (a : primaryFactors x) : Type := AdjoinRoot (a : K[X])

noncomputable abbrev mult (a : primaryFactors x) : ℕ := primaryMultiplicity x (a : K[X])

variable {x}

@[expose] noncomputable def thetaEquivUnits (hx : Squarefree (minpoly K x)) :
    PiGL (Efac x) (mult x) ≃* (commutant x)ˣ :=
  MulEquiv.piUnits.symm.trans (Units.mapEquiv (commutantEquivMatrix hx).symm.toMulEquiv)

@[expose] noncomputable def blockTheta (hx : Squarefree (minpoly K x)) :
    PiGL (Efac x) (mult x) →* GL (Fin n) K :=
  (commutantUnitsToGL x).comp (thetaEquivUnits hx).toMonoidHom

theorem blockTheta_injective (hx : Squarefree (minpoly K x)) :
    Function.Injective (blockTheta hx) :=
  (commutantUnitsToGL_injective x).comp (thetaEquivUnits hx).injective

theorem range_blockTheta (hx : Squarefree (minpoly K x)) :
    (blockTheta hx).range = (commutantUnitsToGL x).range := by
  ext g
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨thetaEquivUnits hx w, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(thetaEquivUnits hx).symm u, by simp [blockTheta]⟩

theorem mem_center_of_ringEquiv {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) {r : R}
    (h : e r ∈ Subring.center S) : r ∈ Subring.center R := by
  rw [Subring.mem_center_iff] at h ⊢
  intro g
  apply e.injective
  rw [map_mul, map_mul]
  exact h (e g)

theorem commutantEquivMatrix_thetaEquivUnits (hx : Squarefree (minpoly K x))
    (w : PiGL (Efac x) (mult x)) :
    commutantEquivMatrix hx ((thetaEquivUnits hx w : (commutant x)ˣ) : commutant x) =
      fun b => ((w b : GL (Fin (mult x b)) (Efac x b)) :
        Matrix (Fin (mult x b)) (Fin (mult x b)) (Efac x b)) := by
  simp [thetaEquivUnits]
  rfl

theorem exists_centerUnit_of_mem_scalarGLPi (hx : Squarefree (minpoly K x))
    {w : PiGL (Efac x) (mult x)} (hw : w ∈ scalarGLPi (Efac x) (mult x)) :
    ∃ z : (Subring.center (commutant x))ˣ, centerUnitsToGL x z = blockTheta hx w := by
  set u : (commutant x)ˣ := thetaEquivUnits hx w with hu
  have hcen : (u : commutant x) ∈ Subring.center (commutant x) := by
    refine mem_center_of_ringEquiv (commutantEquivMatrix hx).toRingEquiv ?_
    change commutantEquivMatrix hx (u : commutant x) ∈ _
    rw [hu, commutantEquivMatrix_thetaEquivUnits, mem_center_iff_exists_scalarPi]
    choose c hc using mem_scalarGLPi.mp hw
    refine ⟨fun b => ((c b : (Efac x b)ˣ) : Efac x b), ?_⟩
    funext b
    rw [← hc b]
    rfl
  have hcen' : ((u⁻¹ : (commutant x)ˣ) : commutant x) ∈ Subring.center (commutant x) := by
    rw [Subring.mem_center_iff] at hcen ⊢
    intro g
    exact ((Commute.units_inv_right (show Commute g (u : commutant x) from hcen g)).eq)
  refine ⟨⟨⟨u, hcen⟩, ⟨↑u⁻¹, hcen'⟩, Subtype.ext u.val_inv, Subtype.ext u.inv_val⟩, ?_⟩
  rfl

@[expose] noncomputable def blockImage (hx : Squarefree (minpoly K x)) (a : primaryFactors x) :
    Subgroup (GL (Fin n) K) :=
  (blockSL (Efac x) (mult x) a).map (blockTheta hx)

theorem blockImage_le_range (hx : Squarefree (minpoly K x)) (a : primaryFactors x) :
    blockImage hx a ≤ (commutantUnitsToGL x).range := by
  rintro _ ⟨w, -, rfl⟩
  exact ⟨thetaEquivUnits hx w, rfl⟩

theorem mem_blockImage {hx : Squarefree (minpoly K x)} {a : primaryFactors x}
    {g : GL (Fin n) K} :
    g ∈ blockImage hx a ↔
      ∃ s : SpecialLinearGroup (Fin (mult x a)) (Efac x a),
        blockTheta hx (blockEmbed (Efac x) (mult x) a s) = g := by
  constructor
  · rintro ⟨w, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, ⟨s, rfl⟩, rfl⟩

theorem conj_mem_blockImage (hx : Squarefree (minpoly K x)) (a : primaryFactors x)
    {g : GL (Fin n) K} (hg : g ∈ (commutantUnitsToGL x).range) {f : GL (Fin n) K}
    (hf : f ∈ blockImage hx a) : g * f * g⁻¹ ∈ blockImage hx a := by
  rw [← range_blockTheta hx] at hg
  obtain ⟨w, rfl⟩ := hg
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  refine ⟨w * f₀ * w⁻¹, conj_mem_blockSL a w hf₀, ?_⟩
  simp [map_mul, map_inv]

theorem exists_finset_card_four [Finite K] (hK : 4 ≤ Nat.card K) (a : primaryFactors x) :
    ∃ s : Finset (Efac x a), s.card = 4 := by
  have : Module.Finite K (Efac x a) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible (a : K[X])).ne_zero).finite
  have : Finite (Efac x a) := Module.finite_of_finite K
  have hle : Nat.card K ≤ Nat.card (Efac x a) :=
    Nat.card_le_card_of_injective _ (algebraMap K (Efac x a)).injective
  have := Fintype.ofFinite (Efac x a)
  have h4 : 4 ≤ (Finset.univ : Finset (Efac x a)).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4
  exact ⟨t, ht⟩

theorem isQuasisimple_blockImage [Finite K] (hx : Squarefree (minpoly K x)) (hK : 4 ≤ Nat.card K)
    (a : primaryFactors x) (ha : 2 ≤ mult x a) : CFSG.IsQuasisimple (blockImage hx a) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective _ _ (blockTheta_injective hx))
    (isQuasisimple_blockSL a ha (Or.inr (exists_finset_card_four hK a)))

theorem isPerfect_blockImage [Finite K] (hx : Squarefree (minpoly K x)) (hK : 4 ≤ Nat.card K)
    (a : primaryFactors x) (ha : 2 ≤ mult x a) : Group.IsPerfect (blockImage hx a) :=
  (isQuasisimple_blockImage hx hK a ha).1

theorem blockImage_le_range_toGL [Finite K] (hx : Squarefree (minpoly K x))
    (hK : 4 ≤ Nat.card K) (a : primaryFactors x) (ha : 2 ≤ mult x a) :
    blockImage hx a ≤ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* _).range := by
  intro g hg
  rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
  have h := KCUnitary.eq_one_of_perfect_of_comm (isPerfect_blockImage hx hK a ha)
    (fun u v : Kˣ => mul_comm u v)
    ((GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).comp (blockImage hx a).subtype) ⟨g, hg⟩
  exact h

theorem mem_range_centerUnitsToGL_of_commute (hx : Squarefree (minpoly K x))
    (u : (commutant x)ˣ)
    (h : ∀ a : primaryFactors x, 2 ≤ mult x a → ∀ g ∈ blockImage hx a,
      commutantUnitsToGL x u * g = g * commutantUnitsToGL x u) :
    commutantUnitsToGL x u ∈ (centerUnitsToGL x).range := by
  set w : PiGL (Efac x) (mult x) := (thetaEquivUnits hx).symm u with hw
  have hθ : blockTheta hx w = commutantUnitsToGL x u := by
    simp [blockTheta, hw]
  have hsc : w ∈ scalarGLPi (Efac x) (mult x) := by
    refine mem_scalarGLPi_of_commute_blockEmbed fun a ha s => ?_
    apply blockTheta_injective hx
    rw [map_mul, map_mul, hθ]
    exact (h a ha _ (mem_blockImage.mpr ⟨s, rfl⟩)).symm
  obtain ⟨z, hz⟩ := exists_centerUnit_of_mem_scalarGLPi hx hsc
  exact ⟨z, hz.trans hθ⟩

theorem commutator_range_eq_iSup [Finite K] (hx : Squarefree (minpoly K x))
    (hK : 4 ≤ Nat.card K) :
    ⁅(commutantUnitsToGL x).range, (commutantUnitsToGL x).range⁆ =
      ⨆ b : {a : primaryFactors x // 2 ≤ mult x a}, blockImage hx b.1 := by
  rw [← range_blockTheta hx, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
    commutator_top_eq_iSup fun b _ => Or.inr (exists_finset_card_four hK b), Subgroup.map_iSup]
  rfl

end Theta

section Center

variable (x : Module.End K (Fin n → K))

theorem scalar_mem_range_centerUnitsToGL (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin n) c ∈ (centerUnitsToGL x).range := by
  have hc : algebraMap K (commutant x) (c : K) ∈ Subring.center (commutant x) := by
    rw [Subring.mem_center_iff]
    intro g
    exact (Algebra.commutes (c : K) g).symm
  have hc' : algebraMap K (commutant x) ((c⁻¹ : Kˣ) : K) ∈ Subring.center (commutant x) := by
    rw [Subring.mem_center_iff]
    intro g
    exact (Algebra.commutes ((c⁻¹ : Kˣ) : K) g).symm
  refine ⟨⟨⟨_, hc⟩, ⟨_, hc'⟩, Subtype.ext ?_, Subtype.ext ?_⟩, ?_⟩
  · change algebraMap K (commutant x) (c : K) * algebraMap K (commutant x) ((c⁻¹ : Kˣ) : K) = 1
    rw [← map_mul, Units.mul_inv, map_one]
  · change algebraMap K (commutant x) ((c⁻¹ : Kˣ) : K) * algebraMap K (commutant x) (c : K) = 1
    rw [← map_mul, Units.inv_mul, map_one]
  · refine Units.ext ?_
    change commutantToMat x (algebraMap K (commutant x) (c : K)) =
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [AlgHom.commutes, GeneralLinearGroup.coe_scalar]
    rfl

theorem units_center_commute {R : Type*} [Ring R] (z : (Subring.center R)ˣ) (u : Rˣ) :
    Units.map (Subring.center R).subtype.toMonoidHom z * u =
      u * Units.map (Subring.center R).subtype.toMonoidHom z := by
  refine Units.ext ?_
  have := Subring.mem_center_iff.mp (z : Subring.center R).2 (u : R)
  simpa using this.symm

theorem centerUnitsToGL_commute (z : (Subring.center (commutant x))ˣ) (u : (commutant x)ˣ) :
    centerUnitsToGL x z * commutantUnitsToGL x u =
      commutantUnitsToGL x u * centerUnitsToGL x z := by
  have h : centerUnitsToUnits x z * u = u * centerUnitsToUnits x z :=
    units_center_commute z u
  change commutantUnitsToGL x (centerUnitsToUnits x z) * commutantUnitsToGL x u = _
  rw [← map_mul, h, map_mul]
  rfl

end Center

end CFSG.RankThree.PartOne.KCLinComm
