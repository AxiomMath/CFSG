module

public import CFSG.RankThree.PartOne.KC.MatrixAlgebraFewBlocks
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi

public section

namespace CFSG.RankThree.PartOne.KCLinComm

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut SemiGL)

section Restrict

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def commutantAut (x : Module.End K V) (τ : RingAut (Module.End K V)) (hτ : τ x = x) :
    RingAut (commutant x) where
  toFun y := ⟨τ y.1, by
    rw [mem_commutant]
    have h := Commute.map ((mem_commutant x).mp y.2) τ
    rwa [hτ] at h⟩
  invFun y := ⟨τ.symm y.1, by
    rw [mem_commutant]
    have h := Commute.map ((mem_commutant x).mp y.2) τ.symm
    have hx : τ.symm x = x := by
      have := τ.symm_apply_apply x
      rwa [hτ] at this
    rwa [hx] at h⟩
  left_inv y := Subtype.ext (τ.symm_apply_apply y.1)
  right_inv y := Subtype.ext (τ.apply_symm_apply y.1)
  map_mul' y z := Subtype.ext (map_mul τ y.1 z.1)
  map_add' y z := Subtype.ext (map_add τ y.1 z.1)

@[simp] theorem coe_commutantAut (x : Module.End K V) (τ : RingAut (Module.End K V))
    (hτ : τ x = x) (y : commutant x) :
    ((commutantAut x τ hτ y : commutant x) : Module.End K V) = τ y.1 := rfl

@[expose] def stabilizerToCommutantAut (x : Module.End K V) :
    MulAction.stabilizer (RingAut (Module.End K V)) x →* RingAut (commutant x) where
  toFun τ := commutantAut x τ.1 τ.2
  map_one' := RingEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := RingEquiv.ext fun _ => Subtype.ext rfl

end Restrict


section Act

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def matRingAutToEnd :
    RingAut (Matrix (Fin n) (Fin n) K) →* RingAut (Module.End K (Fin n → K)) where
  toFun σ := ((Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).symm.toRingEquiv.trans σ).trans
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toRingEquiv
  map_one' := RingEquiv.ext fun y => by simp
  map_mul' σ σ' := RingEquiv.ext fun y => by simp

theorem matRingAutToEnd_apply (σ : RingAut (Matrix (Fin n) (Fin n) K))
    (y : Module.End K (Fin n → K)) :
    matRingAutToEnd σ y = Matrix.toLinAlgEquiv' (σ ((Matrix.toLinAlgEquiv' (R := K)
      (n := Fin n)).symm y)) := rfl

variable [Finite K]

@[expose] noncomputable def actEnd (hn : 3 ≤ n) :
    ↥(semilinPsi n K).range →* RingAut (Module.End K (Fin n → K)) :=
  matRingAutToEnd.comp (actE n K hn)

theorem actEnd_apply (hn : 3 ≤ n) (α : ↥(semilinPsi n K).range) (y : Module.End K (Fin n → K)) :
    actEnd hn α y = Matrix.toLinAlgEquiv' (actE n K hn α ((Matrix.toLinAlgEquiv' (R := K)
      (n := Fin n)).symm y)) := rfl

end Act


section ActCommutant

variable {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n)
  {A : Subgroup (MulAut (projectiveSL n K))} (hA : A ≤ (semilinPsi n K).range)
  {a : GL (Fin n) K}
  (hfix : ∀ α : ↥A, actE n K hn ⟨α, hA α.2⟩ (a : Matrix (Fin n) (Fin n) K) = a)

include hfix in
theorem actEnd_toLin'_fix (α : ↥A) :
    actEnd hn ⟨α, hA α.2⟩ (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) =
      Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) := by
  rw [actEnd_apply]
  have h1 : (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).symm
      (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) = (a : Matrix (Fin n) (Fin n) K) := by
    rw [← toLinAlgEquiv'_eq_toLin']
    exact AlgEquiv.symm_apply_apply _ _
  rw [h1, hfix α, toLinAlgEquiv'_eq_toLin']

@[expose] noncomputable def actCommutant (hn : 3 ≤ n) (hA : A ≤ (semilinPsi n K).range)
    (hfix : ∀ α : ↥A, actE n K hn ⟨α, hA α.2⟩ (a : Matrix (Fin n) (Fin n) K) = a) :
    ↥A →* RingAut (commutant (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) :=
  (stabilizerToCommutantAut _).comp
    (((actEnd hn).comp (Subgroup.inclusion hA)).codRestrict
      (MulAction.stabilizer (RingAut (Module.End K (Fin n → K)))
        (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) fun α => by
      rw [MulAction.mem_stabilizer_iff]
      exact actEnd_toLin'_fix hn hA hfix α)

theorem commutantToMat_actCommutant (α : ↥A)
    (y : commutant (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) :
    commutantToMat _ (actCommutant hn hA hfix α y) =
      actE n K hn ⟨α, hA α.2⟩ (commutantToMat _ y) := by
  change (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).symm
    (Matrix.toLinAlgEquiv' (actE n K hn ⟨α, hA α.2⟩ ((Matrix.toLinAlgEquiv' (R := K)
      (n := Fin n)).symm y.1))) = _
  exact AlgEquiv.symm_apply_apply _ _

theorem commutantToMat_actCommutant_psi (g : SemiGL (Fin n) K) (hg : semilinPsi n K g ∈ A)
    (y : commutant (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) :
    commutantToMat _ (actCommutant hn hA hfix ⟨semilinPsi n K g, hg⟩ y) =
      semilinAct n K g (commutantToMat _ y) := by
  rw [commutantToMat_actCommutant]
  exact congrArg (fun σ : RingAut (Matrix (Fin n) (Fin n) K) => σ (commutantToMat _ y))
    (actE_semilinPsi hn g)

theorem centerUnitsToGL_centerUnitsAut_actCommutant (g : SemiGL (Fin n) K)
    (hg : semilinPsi n K g ∈ A)
    (z : (Subring.center (commutant (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))ˣ) :
    centerUnitsToGL (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))
        (centerUnitsAut (actCommutant hn hA hfix ⟨semilinPsi n K g, hg⟩) z) =
      semilinGLAct n K g (centerUnitsToGL (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) z) := by
  refine Units.ext ?_
  rw [coe_semilinGLAct]
  change commutantToMat _ (((centerUnitsAut (actCommutant hn hA hfix ⟨semilinPsi n K g, hg⟩) z :
    (Subring.center (commutant (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))ˣ) :
      Subring.center (commutant (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)))) :
        commutant (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) = _
  rw [coe_coe_centerUnitsAut, commutantToMat_actCommutant_psi]
  rfl

end ActCommutant


section FewBlocks

variable {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n)
  {A : Subgroup (MulAut (projectiveSL n K))} (hA : A ≤ (semilinPsi n K).range)
  {a : GL (Fin n) K}
  (hfix : ∀ α : ↥A, actE n K hn ⟨α, hA α.2⟩ (a : Matrix (Fin n) (Fin n) K) = a)

omit [Finite K] in
theorem mult_pos {x : Module.End K (Fin n → K)} (hx : Squarefree (minpoly K x))
    (b : primaryFactors x) : 0 < mult x b := by
  have hne := primaryComponent_ne_bot hx b.2
  have : Nontrivial (primaryComponent x (b : K[X])) := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact Module.finrank_pos

omit [Finite K] in
theorem semilinGLAct_scalar (g : SemiGL (Fin n) K) (c : Kˣ) :
    semilinGLAct n K g (GeneralLinearGroup.scalar (Fin n) c) =
      GeneralLinearGroup.scalar (Fin n) (Units.map (g.right : K →* K) c) := by
  obtain ⟨M, σ⟩ := g
  rw [semilinGLAct_mk]
  have h : glAut σ (GeneralLinearGroup.scalar (Fin n) c) =
      GeneralLinearGroup.scalar (Fin n) (Units.map (σ : K →* K) c) := by
    refine Units.ext ?_
    rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply, hij]
  rw [h, (commute_scalar_gl _ M).symm.eq, mul_inv_cancel_right]

@[expose] noncomputable def commutantEquivFin {x : Module.End K (Fin n → K)}
    (hsq : Squarefree (minpoly K x)) :
    commutant x ≃+* ∀ i : Fin (Fintype.card (primaryFactors x)),
      Matrix (Fin (mult x ((Fintype.equivFin (primaryFactors x)).symm i)))
        (Fin (mult x ((Fintype.equivFin (primaryFactors x)).symm i)))
        (Efac x ((Fintype.equivFin (primaryFactors x)).symm i)) :=
  (commutantEquivMatrix hsq).toRingEquiv.trans
    (RingEquiv.piCongrLeft' (fun b => Matrix (Fin (mult x b)) (Fin (mult x b)) (Efac x b))
      (Fintype.equivFin (primaryFactors x)))

omit [Finite K] in
theorem centerUnitsAut_eq_of_pow_two_pow_subalgebra {V : Type*} [AddCommGroup V] [Module K V]
    {S : Subalgebra K (Module.End K V)} {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hrp : r < p)
    {F : Fin r → Type*} [∀ i, Field (F i)] {m : Fin r → ℕ} (hm : ∀ i, 0 < m i)
    (e : S ≃+* ∀ i, Matrix (Fin (m i)) (Fin (m i)) (F i)) {A : Type*} [Group A]
    (hAp : IsPGroup p A) (φ : A →* RingAut S) (α : A) {z : (Subring.center S)ˣ} {k : ℕ}
    (hz : z ^ 2 ^ k = 1) : centerUnitsAut (φ α) z = z :=
  KCMatrixAlgebra.centerUnitsAut_apply_eq_of_pow_two_pow_eq_one hp hp2 hrp hm e hAp φ α hz

theorem centerUnitsAut_actCommutant_eq_of_pow_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsq : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))
    (hr : Nat.card (primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) < p)
    (hAp : IsPGroup p A) (α : ↥A)
    {z : (Subring.center (commutant (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))ˣ} {k : ℕ}
    (hz : z ^ 2 ^ k = 1) : centerUnitsAut (actCommutant hn hA hfix α) z = z := by
  have hrp : Fintype.card (primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) < p := by
    rw [← Nat.card_eq_fintype_card]
    exact hr
  exact centerUnitsAut_eq_of_pow_two_pow_subalgebra hp hp2 hrp (fun i => mult_pos hsq _)
    (commutantEquivFin hsq) hAp (actCommutant hn hA hfix) α hz

omit [Finite K] in
theorem mul_inv_mem_center_units {V : Type*} [AddCommGroup V] [Module K V]
    {S : Subalgebra K (Module.End K V)} [Finite S] (σ : MulAut (Subring.center S)ˣ)
    (hσ : ∀ (w : (Subring.center S)ˣ) (k : ℕ), w ^ 2 ^ k = 1 → σ w = w)
    (C : Subgroup (Subring.center S)ˣ) (hC : ∀ w ∈ C, σ w ∈ C) {z : (Subring.center S)ˣ} {k : ℕ}
    (hz : z ^ 2 ^ k ∈ C) : σ z * z⁻¹ ∈ C := by
  have : Finite (Subring.center S) := Subtype.finite
  have : Finite (Subring.center S)ˣ := Finite.of_injective Units.val Units.val_injective
  exact KCMatrixAlgebra.mul_inv_mem_of_pow_two_pow_mem σ hσ C hC hz

omit [Finite K] in
@[expose] noncomputable def scalarCenterUnits (x : Module.End K (Fin n → K)) :
    Subgroup (Subring.center (commutant x))ˣ :=
  Subgroup.comap (centerUnitsToGL x) (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range

omit [Finite K] in
theorem mem_scalarCenterUnits {x : Module.End K (Fin n → K)}
    {z : (Subring.center (commutant x))ˣ} :
    z ∈ scalarCenterUnits x ↔
      centerUnitsToGL x z ∈ (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range :=
  Iff.rfl

include hn hA hfix in
theorem centerUnitsAut_actCommutant_mem_scalarCenterUnits (g : SemiGL (Fin n) K)
    (hg : semilinPsi n K g ∈ A)
    {w : (Subring.center (commutant (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))ˣ}
    (hw : w ∈ scalarCenterUnits (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) :
    centerUnitsAut (actCommutant hn hA hfix ⟨semilinPsi n K g, hg⟩) w ∈
      scalarCenterUnits (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨c, hc⟩ := mem_scalarCenterUnits.mp hw
  refine mem_scalarCenterUnits.mpr ⟨Units.map (g.right : K →* K) c, ?_⟩
  rw [centerUnitsToGL_centerUnitsAut_actCommutant hn hA hfix g hg, ← hc, semilinGLAct_scalar]

include hn hA hfix in
theorem centerUnitsAut_mul_inv_mem_scalarCenterUnits {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsq : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))
    (hr : Nat.card (primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) < p)
    (hAp : IsPGroup p A) (g : SemiGL (Fin n) K) (hg : semilinPsi n K g ∈ A)
    {z : (Subring.center (commutant (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))ˣ} {k : ℕ}
    (hz : z ^ 2 ^ k ∈ scalarCenterUnits (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) :
    centerUnitsAut (actCommutant hn hA hfix ⟨semilinPsi n K g, hg⟩) z * z⁻¹ ∈
      scalarCenterUnits (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) := by
  have hfin : Finite (Module.End K (Fin n → K)) := Module.finite_of_finite K
  have : Finite (commutant (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) := Subtype.finite
  exact mul_inv_mem_center_units _
    (fun w k hw => centerUnitsAut_actCommutant_eq_of_pow_two_pow hn hA hfix hp hp2 hsq hr hAp
      ⟨semilinPsi n K g, hg⟩ hw)
    _ (fun w hw => centerUnitsAut_actCommutant_mem_scalarCenterUnits hn hA hfix g hg hw) hz

omit [Finite K] in
theorem conj_eq_of_mul_inv_mem_comap {G H M : Type*} [Group G] [Group H] [Group M] (Z : G →* H)
    (ρ : H →* M) (T : Subgroup H) (hT : ∀ t ∈ T, ρ t = 1) {u v : G}
    (h : u * v⁻¹ ∈ T.comap Z) : ρ (Z u) = ρ (Z v) := by
  have h1 : ρ (Z (u * v⁻¹)) = 1 := hT _ h
  rw [map_mul, map_mul, map_inv, map_inv] at h1
  exact mul_inv_eq_one.mp h1

include hn hA hfix in
theorem conj_centerUnitsToGL_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsq : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))
    (hr : Nat.card (primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) < p)
    (hAp : IsPGroup p A) (α : ↥A)
    (z : (Subring.center (commutant (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))ˣ) {k : ℕ}
    (hz : z ^ 2 ^ k ∈ scalarCenterUnits (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) :
    (α : MulAut (projectiveSL n K)) *
        conjAut n K (centerUnitsToGL (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) z) *
        (α : MulAut (projectiveSL n K))⁻¹ =
      conjAut n K (centerUnitsToGL (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) z) := by
  obtain ⟨g, hg⟩ := hA α.2
  have hgA : semilinPsi n K g ∈ A := hg ▸ α.2
  have hαeq : α = ⟨semilinPsi n K g, hgA⟩ := Subtype.ext hg.symm
  have hmem := centerUnitsAut_mul_inv_mem_scalarCenterUnits hn hA hfix hp hp2 hsq hr hAp g hgA hz
  have hact := centerUnitsToGL_centerUnitsAut_actCommutant hn hA hfix g hgA z
  have h2 := conj_eq_of_mul_inv_mem_comap
    (centerUnitsToGL (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) (conjAut n K)
    (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range
    (fun t ⟨c, hc⟩ => hc ▸ conjAut_scalar c) hmem
  rw [hact] at h2
  rw [hαeq]
  exact (semilinPsi_conj_act g _).trans h2

end FewBlocks

end CFSG.RankThree.PartOne.KCLinComm
