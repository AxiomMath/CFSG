module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormE6PhiThree
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Chevalley.E6GraphRadicalCocycle
public import CFSG.LieType.Chevalley.E6GraphLeviRealization
public import CFSG.LieType.SeitzGeneration.ExcTorusTw
public import CFSG.RankThree.Lattice.SteinbergBIChecks
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.RankThree.PartOne.KE.CTLangData
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.ClassicalGroups.Unitary.SingerSU3
public import CFSG.ClassicalGroups.Unitary.Perfect
public import CFSG.HardMathSupport.Lang.TwE6Step3.SylowTorusSix
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8PowerMap

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice
open scoped Matrix MatrixGroups commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace TwE6PhiSix

@[expose] def e6W0Word : List (Fin TwistTag.E6.tag.rank) :=
  [0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5,
    4, 3, 2, 0]

@[expose] def e6W0Mat : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1], [0, -1, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0], [0, 0, 0, -1, 0, 0],
   [0, 0, -1, 0, 0, 0], [-1, 0, 0, 0, 0, 0]]

theorem e6W0_wordMat :
    wordMat TwistTag.E6.tag e6W0Word = toMat TwistTag.E6.tag.rank e6W0Mat :=
  wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)

theorem e6W0Mat_mul_perm :
    toMat TwistTag.E6.tag.rank e6W0Mat * toMat TwistTag.E6.tag.rank twE6PermList = -1 := by
  decide +kernel

@[expose] noncomputable def w0 : WeylGroup TwistTag.E6.tag :=
  (coxeterSystem TwistTag.E6.tag).wordProd e6W0Word


theorem e6W0_smul_permLattice (x : Fin TwistTag.E6.tag.rank → ℤ) :
    w0 • permLattice TwistTag.E6.perm x = -x := by
  rw [w0, wordProd_smul_eq_wordMat_mulVec, e6W0_wordMat, permLattice_E6_eq, Matrix.mulVec_mulVec,
    e6W0Mat_mul_perm, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem w0_twistHom_pinnedX {Ω : Type} [Field Ω] (h2 : (2 : Ω) = 0) (Fr : Ω →+* Ω)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (d : Ω) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w0 *
        twistHom TwistTag.E6 Ω Fr (pinnedX TwistTag.E6.tag Ω α d) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w0)⁻¹ =
      pinnedX TwistTag.E6.tag Ω (-α) (Fr d) := by
  rw [E6GraphRadical.twistHom_pinnedX_of_two h2 Fr hα,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w0
      (hα.permLattice fun i j => TwistTag.cartan_perm TwistTag.E6 i j) (Fr d),
    e6W0_smul_permLattice]


theorem sl3_transvection_commutator {L : Type} [Field L] {i j k : Fin 3} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) (s t : L) :
    Matrix.SpecialLinearGroup.transvection hij s * Matrix.SpecialLinearGroup.transvection hjk t *
        (Matrix.SpecialLinearGroup.transvection hij s)⁻¹ *
        (Matrix.SpecialLinearGroup.transvection hjk t)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hik (s * t) := by
  rw [Matrix.SpecialLinearGroup.transvection_inv, Matrix.SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (Matrix.SpecialLinearGroup.transvection hij s : Matrix (Fin 3) (Fin 3) L) *
      (Matrix.SpecialLinearGroup.transvection hjk t : Matrix (Fin 3) (Fin 3) L) *
      (Matrix.SpecialLinearGroup.transvection hij (-s) : Matrix (Fin 3) (Fin 3) L) *
      (Matrix.SpecialLinearGroup.transvection hjk (-t) : Matrix (Fin 3) (Fin 3) L) =
      (Matrix.SpecialLinearGroup.transvection hik (s * t) : Matrix (Fin 3) (Fin 3) L)
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hik.symm]
  simp only [zero_mul, add_zero, mul_neg, neg_mul, neg_neg, ← Matrix.single_neg]
  abel

theorem sl3_hom_ext {L : Type} [Field L] {G : Type*} [Group G] {ψ₁ ψ₂ : SL(3, L) →* G}
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) (c : L),
      ψ₁ (Matrix.SpecialLinearGroup.transvection hij c) =
        ψ₂ (Matrix.SpecialLinearGroup.transvection hij c)) : ψ₁ = ψ₂ := by
  have hle : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 3) L → SL(3, L))) ≤ ψ₁.eqLocus ψ₂ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    show ψ₁ (Matrix.TransvectionStruct.toSpecialLinearGroup ⟨i, j, hij, c⟩) =
      ψ₂ (Matrix.TransvectionStruct.toSpecialLinearGroup ⟨i, j, hij, c⟩)
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
    exact h i j hij c
  rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field] at hle
  exact MonoidHom.ext fun x => hle (Subgroup.mem_top x)

@[expose] def diagConj {L : Type} [Field L] (d : Fin 3 → Lˣ) : SL(3, L) →* SL(3, L) where
  toFun g := ⟨Matrix.diagonal (fun i => (d i : L)) * (g : Matrix (Fin 3) (Fin 3) L) *
      Matrix.diagonal (fun i => (((d i)⁻¹ : Lˣ) : L)), by
    rw [Matrix.det_mul, Matrix.det_mul, g.2, mul_one, ← Matrix.det_mul,
      Matrix.diagonal_mul_diagonal]
    simp⟩
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal (fun i => (d i : L)) * 1 *
      Matrix.diagonal (fun i => (((d i)⁻¹ : Lˣ) : L)) = 1
    rw [Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    simp
  map_mul' g h := by
    apply Subtype.ext
    change Matrix.diagonal (fun i => (d i : L)) * ((g : Matrix (Fin 3) (Fin 3) L) *
        (h : Matrix (Fin 3) (Fin 3) L)) * Matrix.diagonal (fun i => (((d i)⁻¹ : Lˣ) : L)) =
      Matrix.diagonal (fun i => (d i : L)) * (g : Matrix (Fin 3) (Fin 3) L) *
        Matrix.diagonal (fun i => (((d i)⁻¹ : Lˣ) : L)) *
      (Matrix.diagonal (fun i => (d i : L)) * (h : Matrix (Fin 3) (Fin 3) L) *
        Matrix.diagonal (fun i => (((d i)⁻¹ : Lˣ) : L)))
    have hD : Matrix.diagonal (fun i => (((d i)⁻¹ : Lˣ) : L)) *
        Matrix.diagonal (fun i => (d i : L)) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      simp
    calc _ = Matrix.diagonal (fun i => (d i : L)) * (g : Matrix (Fin 3) (Fin 3) L) *
          (Matrix.diagonal (fun i => (((d i)⁻¹ : Lˣ) : L)) *
            Matrix.diagonal (fun i => (d i : L))) * (h : Matrix (Fin 3) (Fin 3) L) *
          Matrix.diagonal (fun i => (((d i)⁻¹ : Lˣ) : L)) := by
            rw [hD, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem diagConj_transvection {L : Type} [Field L] (d : Fin 3 → Lˣ) {i j : Fin 3} (hij : i ≠ j)
    (c : L) : diagConj d (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij ((d i : L) * c * (((d j)⁻¹ : Lˣ) : L)) := by
  apply Subtype.ext
  change Matrix.diagonal (fun i => (d i : L)) *
      ((Matrix.SpecialLinearGroup.transvection hij c : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) *
      Matrix.diagonal (fun i => (((d i)⁻¹ : Lˣ) : L)) = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have hia : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [hia]
  · by_cases h' : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h'
      simp [hab]
    · simp [hab, h']

theorem diagConj_inv_apply {L : Type} [Field L] (d : Fin 3 → Lˣ) (g : SL(3, L)) :
    diagConj d (diagConj (fun i => (d i)⁻¹) g) = g := by
  apply Subtype.ext
  change Matrix.diagonal (fun i => (d i : L)) * (Matrix.diagonal (fun i => (((d i)⁻¹ : Lˣ) : L)) *
      (g : Matrix (Fin 3) (Fin 3) L) * Matrix.diagonal (fun i => ((((d i)⁻¹)⁻¹ : Lˣ) : L))) *
      Matrix.diagonal (fun i => (((d i)⁻¹ : Lˣ) : L)) = g
  simp only [inv_inv, ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  simp only [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  simp

theorem frame_eps_mul {L : Type} [Field L] (h2 : (2 : L) = 0) {ρ : SL(3, L) →* ModGL Tag.E6 L}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (h : IsSLFrame ρ σ)
    (hne : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → σ i j ≠ σ j k)
    (ε : ∀ i j : Fin 3, i ≠ j → Lˣ)
    (hε : ∀ i j (hij : i ≠ j) t, ρ (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E6 L (σ i j) ((ε i j hij : L) * t))
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (ε i k hik : L) = ε i j hij * ε j k hjk := by
  have hc := congrArg ρ (sl3_transvection_commutator hij hjk hik (1 : L) 1)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hε, hε, hε, mul_one, mul_one, mul_one,
    ← commutatorElement_def] at hc
  have hsum : σ i j + σ j k = σ i k := h.add i j k
  have hne' : σ i j ≠ -σ j k := by
    intro he
    have h0 : σ i k = 0 := by rw [← hsum, he, neg_add_cancel]
    exact (h.isRoot i k hik).ne_zero h0
  have hcomm :
      ⁅pinnedX Tag.E6 L (σ i j) (ε i j hij : L), pinnedX Tag.E6 L (σ j k) (ε j k hjk : L)⁆ =
      pinnedX Tag.E6 L (σ i k) ((ε i j hij : L) * ε j k hjk) := by
    have hr : IsRoot Tag.E6 (σ i j + σ j k) := by
      rw [hsum]
      exact h.isRoot i k hik
    have e : ⁅pinnedX Tag.E6 L (σ i j) (ε i j hij : L), pinnedX Tag.E6 L (σ j k) (ε j k hjk : L)⁆ =
        pinnedX Tag.E6 L (σ i j + σ j k) ((ε i j hij : L) * ε j k hjk) :=
      E6GraphLevi.commutator_pinnedX_of_two h2 (h.isRoot i j hij) (h.isRoot j k hjk)
        (hne i j k hij hjk hik) hne' hr (ε i j hij : L) (ε j k hjk : L)
    rw [hsum] at e
    exact e
  rw [hcomm, mul_one] at hc
  exact (pinnedX_injective Tag.E6 L (σ i k) hc).symm

theorem exists_pinned {L : Type} [Field L] (h2 : (2 : L) = 0) {ρ : SL(3, L) →* ModGL Tag.E6 L}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (h : IsSLFrame ρ σ)
    (hne : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → σ i j ≠ σ j k) :
    ∃ d : Fin 3 → Lˣ, ∀ i j (hij : i ≠ j) t,
      ρ (diagConj d (Matrix.SpecialLinearGroup.transvection hij t)) =
        pinnedX Tag.E6 L (σ i j) t := by
  classical
  let ε : ∀ i j : Fin 3, i ≠ j → Lˣ := fun i j hij => Classical.choose (h.transv i j hij)
  have hε : ∀ i j (hij : i ≠ j) t, ρ (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E6 L (σ i j) ((ε i j hij : L) * t) := fun i j hij =>
    Classical.choose_spec (h.transv i j hij)
  have hrel := fun {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) =>
    frame_eps_mul h2 h hne ε hε hij hjk hik
  have hinv : ∀ {i j : Fin 3} (hij : i ≠ j), (ε i j hij : L) * ε j i hij.symm = 1 := by
    intro i j hij
    obtain ⟨k, hik, hjk⟩ : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> decide
    have h1 := hrel hij hjk hik
    have h2' := hrel hij.symm hik hjk
    have hu : (ε i k hik : L) ≠ 0 := (ε i k hik).ne_zero
    rw [h2', ← mul_assoc] at h1
    exact (mul_eq_right₀ hu).mp h1.symm
  let d : Fin 3 → Lˣ := fun i => if hi : i = 0 then 1 else ε 0 i (Ne.symm hi)
  have hd : ∀ i j (hij : i ≠ j), (ε i j hij : L) * (d i : L) = d j := by
    intro i j hij
    by_cases hi : i = 0
    · subst hi
      have hj : j ≠ 0 := Ne.symm hij
      simp [d, hj]
    · by_cases hj : j = 0
      · subst hj
        simp only [d, hi, dite_false, dite_true, Units.val_one]
        exact hinv hij
      · have e := hrel (Ne.symm hi) hij (Ne.symm hj)
        simp only [d, hi, hj, dite_false]
        rw [e, mul_comm]
  refine ⟨d, fun i j hij t => ?_⟩
  rw [diagConj_transvection, hε]
  congr 1
  have hdj : ((d j : Lˣ) : L) * (((d j)⁻¹ : Lˣ) : L) = 1 := Units.mul_inv (d j)
  calc (ε i j hij : L) * ((d i : L) * t * (((d j)⁻¹ : Lˣ) : L)) =
      ((ε i j hij : L) * d i) * (((d j)⁻¹ : Lˣ) : L) * t := by ring
    _ = t := by rw [hd i j hij, hdj, one_mul]


@[expose] def unitaryFrob {L : Type} [Field L] (Fr : L →+* L) : SL(3, L) →* SL(3, L) where
  toFun g := ((Matrix.SpecialLinearGroup.map Fr g)⁻¹).transpose
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    simp only [map_mul, mul_inv_rev, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

theorem unitaryFrob_transvection {L : Type} [Field L] (h2 : (2 : L) = 0) (Fr : L →+* L)
    {i j : Fin 3} (hij : i ≠ j) (t : L) :
    unitaryFrob Fr (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection hij.symm (Fr t) := by
  have hneg : ∀ x : L, -x = x := fun x => by
    rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]
  have hmap : Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection hij (Fr t) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.transvection_coe]
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    split_ifs <;> simp
  apply Subtype.ext
  change (((Matrix.SpecialLinearGroup.map Fr
      (Matrix.SpecialLinearGroup.transvection hij t))⁻¹).transpose : Matrix (Fin 3) (Fin 3) L) = _
  rw [hmap, Matrix.SpecialLinearGroup.transvection_inv, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    hneg]
  ext a b
  simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    simp [and_comm]
  · have hba : ¬ b = a := fun h => hab h.symm
    simp [hab, hba, and_comm]

theorem w0_twistHom_frame {Ω : Type} [Field Ω] (h2 : (2 : Ω) = 0) (Fr : Ω →+* Ω)
    {ρ : SL(3, Ω) →* ModGL TwistTag.E6.tag Ω}
    {σ : Fin 3 → Fin 3 → Fin TwistTag.E6.tag.rank → ℤ}
    (hroot : ∀ i j, i ≠ j → IsRoot TwistTag.E6.tag (σ i j)) (hneg : ∀ i j, σ j i = -σ i j)
    (hpin : ∀ i j (hij : i ≠ j) t,
      ρ (Matrix.SpecialLinearGroup.transvection hij t) = pinnedX TwistTag.E6.tag Ω (σ i j) t)
    (g : SL(3, Ω)) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w0 * twistHom TwistTag.E6 Ω Fr (ρ g) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w0)⁻¹ = ρ (unitaryFrob Fr g) := by
  have key : (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w0)).toMonoidHom.comp
      ((twistHom TwistTag.E6 Ω Fr).comp ρ) = ρ.comp (unitaryFrob Fr) := by
    apply sl3_hom_ext
    intro i j hij c
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hpin, unitaryFrob_transvection h2, hpin, hneg i j,
      w0_twistHom_pinnedX h2 Fr (hroot i j hij) c]
  have e := DFunLike.congr_fun key g
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] at e
  exact e


theorem not_isRoot_add_self {v : Fin Tag.E6.rank → ℤ} (hv : IsRoot Tag.E6 v) :
    ¬ IsRoot Tag.E6 (v + v) := by
  have key : ∀ w ∈ rootFinset Tag.E6, w + w ∉ rootFinset Tag.E6 := by decide +kernel
  intro h
  exact key v (mem_rootFinset.mpr hv) (mem_rootFinset.mpr h)

theorem frame_ne {L : Type} [Field L] {ρ : SL(3, L) →* ModGL Tag.E6 L}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (h : IsSLFrame ρ σ) :
    ∀ i j k, i ≠ j → j ≠ k → i ≠ k → σ i j ≠ σ j k := by
  intro i j k hij hjk hik he
  have hsum := h.add i j k
  rw [← he] at hsum
  exact not_isRoot_add_self (h.isRoot i j hij) (hsum ▸ h.isRoot i k hik)

@[expose] def threeLines : Fin 3 → Fin 12 := ![0, 7, 11]

theorem threeLines_orth : ∀ k l : Fin 3, k ≠ l →
    e6ThreeLineX (threeLines k) ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineX (threeLines l)) = 0 ∧
    e6ThreeLineX (threeLines k) ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineY (threeLines l)) = 0 ∧
    e6ThreeLineY (threeLines k) ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineX (threeLines l)) = 0 ∧
    e6ThreeLineY (threeLines k) ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineY (threeLines l)) =
      0 := by
  decide +kernel

theorem exists_twisted_frames {Ω : Type} [Field Ω] (h2 : (2 : Ω) = 0) :
    ∃ ρ : Fin 3 → (SL(3, Ω) →* ModGL TwistTag.E6.tag Ω),
      (∀ k, Function.Injective (ρ k)) ∧ (∀ k g, ρ k g ∈ adjointGroup TwistTag.E6.tag Ω) ∧
      (∀ k l, k ≠ l → ∀ g g', Commute (ρ k g) (ρ l g')) ∧
      ∀ (Fr : Ω →+* Ω) k g, canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w0 *
        twistHom TwistTag.E6 Ω Fr (ρ k g) * (canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w0)⁻¹ =
          ρ k (unitaryFrob Fr g) := by
  have hfr : ∀ k : Fin 3, ∃ (ρ : SL(3, Ω) →* ModGL Tag.E6 Ω)
      (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ), IsSLFrame ρ σ ∧ Function.Injective ρ ∧
        σ 0 1 = e6ThreeLineX (threeLines k) ∧ σ 1 2 = e6ThreeLineY (threeLines k) :=
    fun k => e6ThreeLine_frame (L := Ω) (threeLines k)
  choose ρ₀ σ₀ hf hi h01 h12 using hfr
  have hpin : ∀ k, ∃ d : Fin 3 → Ωˣ, ∀ i j (hij : i ≠ j) t,
      ρ₀ k (diagConj d (Matrix.SpecialLinearGroup.transvection hij t)) =
        pinnedX Tag.E6 Ω (σ₀ k i j) t := fun k => exists_pinned h2 (hf k) (frame_ne (hf k))
  choose d hd using hpin
  let ρ : Fin 3 → (SL(3, Ω) →* ModGL TwistTag.E6.tag Ω) := fun k => (ρ₀ k).comp (diagConj (d k))
  have hρ : ∀ k g, ρ k g = ρ₀ k (diagConj (d k) g) := fun _ _ => rfl
  refine ⟨ρ, fun k => ?_, fun k g => ?_, fun k l hkl g g' => ?_, fun Fr k g => ?_⟩
  · intro g g' hgg'
    have h1 : diagConj (d k) g = diagConj (d k) g' := hi k hgg'
    have h3 := congrArg (diagConj fun i => (d k i)⁻¹) h1
    have e : ∀ x, diagConj (fun i => (d k i)⁻¹) (diagConj (d k) x) = x := fun x => by
      have := diagConj_inv_apply (fun i => (d k i)⁻¹) x
      simp only [inv_inv] at this
      exact this
    rwa [e, e] at h3
  · exact E6PhiThree.frame_mem (hf k) _
  · rw [hρ, hρ]
    exact E6PhiThree.frame_commute (hf k) (hf l) (h01 k) (h12 k) (h01 l) (h12 l)
      (threeLines_orth k l hkl) _ _
  · exact w0_twistHom_frame h2 Fr (fun i j hij => (hf k).isRoot i j hij) (fun i j => (hf k).neg i j)
      (fun i j hij t => hd k i j hij t) g


open CFSG.LieType.Universal.Unitary CFSG.RankThree.Classical2 in
theorem exists_twisted_reference {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    {τ ϖ : GL (Fin 3) K} (hτ : τ ∈ SUid (iterateFrobeniusEquiv K 2 n) 3)
    (hϖ : ϖ ∈ SUid (iterateFrobeniusEquiv K 2 n) 3) (hτp : orderOf τ = p)
    (hϖτ : ϖ * τ * ϖ⁻¹ = τ ^ Nat.card K)
    (hperf : commutator (SUid (iterateFrobeniusEquiv K 2 n) 3) = ⊤) :
    ∃ (t : Multiplicative (Fin 3 → ZMod p) →*
        graphFixedRootGroup TwistTag.E6 K (iterateFrobeniusEquiv K 2 n).toRingHom)
      (x : graphFixedRootGroup TwistTag.E6 K (iterateFrobeniusEquiv K 2 n).toRingHom),
      Function.Injective t ∧ ∀ v, x * t v * x⁻¹ =
        t (Multiplicative.ofAdd fun i =>
          diagWeight p (Nat.card K) i * Multiplicative.toAdd v i) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  set σ : K ≃+* K := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ n) := fun c => iterateFrobeniusEquiv_def K 2 n c
  let Ω := AlgebraicClosure K
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 n
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  have h2 : (2 : Ω) = 0 := by exact_mod_cast CharP.cast_eq_zero Ω 2
  have hισ : ∀ c : K, Fr (algebraMap K Ω c) = algebraMap K Ω (σ c) := fun c => by
    rw [hFr, ← map_pow]
    congr 1
  obtain ⟨-, -, hder, -, -, -, -⟩ :=
    twisted_E6_full_rational_fixed_group_order Nat.prime_two hn K hK σ.toRingHom hσ Ω Fr hFr
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := 2) (f := n) hn Ω w0
  obtain ⟨ρ, hρinj, hρmem, hρcomm, hρF⟩ := exists_twisted_frames (Ω := Ω) h2
  let toSLK : ↥(SUid σ 3) →* SL(3, K) :=
    { toFun := fun g => ⟨((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), g.2.1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let toSL : ↥(SUid σ 3) →* SL(3, Ω) :=
    (Matrix.SpecialLinearGroup.map (algebraMap K Ω)).comp toSLK
  have htoSL : ∀ g, ((toSL g : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map (algebraMap K Ω) := fun _ => rfl
  have htoSL_inj : Function.Injective toSL := by
    intro g g' h
    apply Subtype.ext
    apply Units.ext
    have h' := congrArg (fun A : SL(3, Ω) => (A : Matrix (Fin 3) (Fin 3) Ω)) h
    simp only [htoSL] at h'
    exact Matrix.map_injective (algebraMap K Ω).injective h'
  have htoSL_fix : ∀ g, unitaryFrob Fr (toSL g) = toSL g := by
    intro g
    have hg := g.2.2
    set A : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    have hA : A.map σ * Aᵀ = 1 := by
      have h1 : (A.map σ)ᵀ * A = 1 := hg
      have h3 : Aᵀ * A.map σ = 1 := by
        have := congrArg Matrix.transpose h1
        rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
      exact mul_eq_one_comm.mp h3
    have hX : Matrix.SpecialLinearGroup.map Fr (toSL g) * (toSL g).transpose = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe,
        Matrix.SpecialLinearGroup.coe_transpose, RingHom.mapMatrix_apply, htoSL,
        Matrix.map_map, Matrix.SpecialLinearGroup.coe_one]
      have e : (A.map (⇑Fr ∘ ⇑(algebraMap K Ω))) = (A.map σ).map (algebraMap K Ω) := by
        rw [Matrix.map_map]
        congr 1
        funext c
        exact hισ c
      rw [e, ← Matrix.transpose_map, ← Matrix.map_mul, hA,
        Matrix.map_one _ (map_zero _) (map_one _)]
    apply Subtype.ext
    change (((Matrix.SpecialLinearGroup.map Fr (toSL g))⁻¹).transpose :
      Matrix (Fin 3) (Fin 3) Ω) = _
    rw [inv_eq_of_mul_eq_one_right hX, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_transpose]
  let Y : Fin 3 → (↥(SUid σ 3) →* ModGL TwistTag.E6.tag Ω) := fun k =>
    (MulAut.conj g0).toMonoidHom.comp ((ρ k).comp toSL)
  have hY : ∀ k g, Y k g = g0 * ρ k (toSL g) * g0⁻¹ := fun _ _ => rfl
  have hYR : ∀ k g, Y k g ∈ twistedFixedGroup TwistTag.E6 Ω Fr := by
    intro k g
    rw [mem_twistedFixedGroup_iff_twistHom]
    refine ⟨?_, ?_⟩
    · rw [hY]
      exact mul_mem (mul_mem hg0C (hρmem k _)) (inv_mem hg0C)
    · have e := hρF Fr k (toSL g)
      rw [htoSL_fix] at e
      rw [hY, map_mul, map_mul, map_inv, hg0]
      calc g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w0 *
            twistHom TwistTag.E6 Ω Fr (ρ k (toSL g)) *
            (g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w0)⁻¹ =
          g0 * (canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w0 *
            twistHom TwistTag.E6 Ω Fr (ρ k (toSL g)) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w0)⁻¹) * g0⁻¹ := by group
        _ = g0 * ρ k (toSL g) * g0⁻¹ := by rw [e]
  have hYC : ∀ k g, Y k g ∈
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL (algebraMap K Ω)) := by
    intro k g
    have hrange : (Y k).range ≤ ⁅twistedFixedGroup TwistTag.E6 Ω Fr,
        twistedFixedGroup TwistTag.E6 Ω Fr⁆ := by
      rw [MonoidHom.range_eq_map, ← hperf, commutator_def, Subgroup.map_commutator]
      apply Subgroup.commutator_mono <;>
      · rintro _ ⟨g, -, rfl⟩
        exact hYR k g
    rw [← hder]
    exact hrange ⟨g, rfl⟩
  have hYcomm : ∀ k l, k ≠ l → ∀ g g', Commute (Y k g) (Y l g') := by
    intro k l hkl g g'
    rw [hY, hY]
    exact (hρcomm k l hkl _ _).conj g0
  have hYinj : ∀ k, Function.Injective (Y k) := by
    intro k g g' h
    rw [hY, hY, mul_left_inj, mul_right_inj] at h
    exact htoSL_inj (hρinj k h)
  let τS : ↥(SUid σ 3) := ⟨τ, hτ⟩
  let ϖS : ↥(SUid σ 3) := ⟨ϖ, hϖ⟩
  have hτS : orderOf τS = p := by rw [Subgroup.orderOf_mk]; exact hτp
  have hϖτS : ϖS * τS * ϖS⁻¹ = τS ^ Nat.card K := Subtype.ext hϖτ
  have hmod : ∀ m : ℕ, τS ^ (m % p) = τS ^ m := fun m => by
    rw [← hτS]
    exact pow_mod_orderOf τS m
  let u : Multiplicative (ZMod p) →* ↥(SUid σ 3) :=
    { toFun := fun a => τS ^ (Multiplicative.toAdd a).val
      map_one' := by simp
      map_mul' := fun a b => by
        rw [toAdd_mul, ZMod.val_add, hmod, pow_add] }
  have hu : ∀ a, u a = τS ^ (Multiplicative.toAdd a).val := fun _ => rfl
  let tΩ : Multiplicative (Fin 3 → ZMod p) →* ModGL TwistTag.E6.tag Ω :=
    { toFun := fun v => Y 0 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 0))) *
        Y 1 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 1))) *
        Y 2 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 2)))
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [toAdd_mul, Pi.add_apply, ofAdd_add, map_mul]
        exact E6PhiThree.mul_rearrange (hYcomm 0 1 (by decide) _ _) (hYcomm 0 2 (by decide) _ _)
          (hYcomm 1 2 (by decide) _ _) }
  have htΩ : ∀ v, tΩ v = Y 0 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 0))) *
      Y 1 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 1))) *
      Y 2 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 2))) := fun _ => rfl
  have hzero : ∀ a : ZMod p, (toSL (u (Multiplicative.ofAdd a))) ^ 3 = 1 → a = 0 := by
    intro a ha
    rw [← map_pow] at ha
    have ha' : (u (Multiplicative.ofAdd a)) ^ 3 = 1 := htoSL_inj (by rw [ha, map_one])
    rw [hu, toAdd_ofAdd, ← pow_mul] at ha'
    have hdvd := orderOf_dvd_of_pow_eq_one ha'
    rw [hτS] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h3
    · exact (ZMod.val_eq_zero a).mp (Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt a))
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3) hp3
  have hinj : Function.Injective tΩ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    rw [htΩ, hY, hY, hY] at hv
    set a0 := toSL (u (Multiplicative.ofAdd (Multiplicative.toAdd v 0)))
    set a1 := toSL (u (Multiplicative.ofAdd (Multiplicative.toAdd v 1)))
    set a2 := toSL (u (Multiplicative.ofAdd (Multiplicative.toAdd v 2)))
    have hv' : ρ 0 a0 * ρ 1 a1 * ρ 2 a2 = 1 := by
      have e1 : g0 * ρ 0 a0 * g0⁻¹ * (g0 * ρ 1 a1 * g0⁻¹) * (g0 * ρ 2 a2 * g0⁻¹) =
          g0 * (ρ 0 a0 * ρ 1 a1 * ρ 2 a2) * g0⁻¹ := by group
      rw [e1] at hv
      calc ρ 0 a0 * ρ 1 a1 * ρ 2 a2 = g0⁻¹ * (g0 * (ρ 0 a0 * ρ 1 a1 * ρ 2 a2) * g0⁻¹) * g0 := by
            group
        _ = 1 := by rw [hv]; group
    have e0 : ρ 0 a0 = (ρ 1 a1 * ρ 2 a2)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact hv')
    have hc0 : ∀ X, Commute (ρ 0 a0) (ρ 0 X) := fun X => by
      rw [e0]
      exact ((hρcomm 0 1 (by decide) X a1).symm.mul_left
        (hρcomm 0 2 (by decide) X a2).symm).inv_left
    have hv0 : Multiplicative.toAdd v 0 = 0 :=
      hzero _ (E6PhiThree.pow_three_eq_one_of_commute (hρinj 0) hc0)
    have ha0 : a0 = 1 := by simp only [a0, hv0, ofAdd_zero, map_one]
    rw [ha0, map_one, one_mul] at hv'
    have e1 : ρ 1 a1 = (ρ 2 a2)⁻¹ := eq_inv_of_mul_eq_one_left hv'
    have hc1 : ∀ X, Commute (ρ 1 a1) (ρ 1 X) := fun X => by
      rw [e1]
      exact (hρcomm 1 2 (by decide) X a2).symm.inv_left
    have hv1 : Multiplicative.toAdd v 1 = 0 :=
      hzero _ (E6PhiThree.pow_three_eq_one_of_commute (hρinj 1) hc1)
    have ha1 : a1 = 1 := by simp only [a1, hv1, ofAdd_zero, map_one]
    rw [ha1, map_one, one_mul] at hv'
    have ha2 : a2 = 1 := hρinj 2 (by rw [hv', map_one])
    have hv2 : Multiplicative.toAdd v 2 = 0 := by
      apply hzero
      show a2 ^ 3 = 1
      rw [ha2, one_pow]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact hv0
    · exact hv1
    · exact hv2
  have hw1 : diagWeight p (Nat.card K) 1 = 1 := if_neg (by decide)
  have hw2 : diagWeight p (Nat.card K) 2 = 1 := if_neg (by decide)
  have hw0 : diagWeight p (Nat.card K) 0 = (Nat.card K : ZMod p) := if_pos rfl
  have hϖu : ∀ a : ZMod p, ϖS * u (Multiplicative.ofAdd a) * ϖS⁻¹ =
      u (Multiplicative.ofAdd ((Nat.card K : ZMod p) * a)) := by
    intro a
    rw [hu, hu, toAdd_ofAdd, toAdd_ofAdd]
    calc ϖS * τS ^ a.val * ϖS⁻¹ = (ϖS * τS * ϖS⁻¹) ^ a.val := conj_pow.symm
      _ = τS ^ (Nat.card K * a.val) := by rw [hϖτS, ← pow_mul]
      _ = τS ^ ((Nat.card K * a.val) % p) := (hmod _).symm
      _ = τS ^ ((Nat.card K % p * a.val) % p) := by rw [Nat.mod_mul_mod]
      _ = τS ^ (((Nat.card K : ZMod p) * a).val) := by rw [ZMod.val_mul, ZMod.val_natCast]
  have hact : ∀ v, Y 0 ϖS * tΩ v * (Y 0 ϖS)⁻¹ = tΩ (Multiplicative.ofAdd fun i =>
      diagWeight p (Nat.card K) i * Multiplicative.toAdd v i) := by
    intro v
    rw [htΩ, htΩ]
    simp only [toAdd_ofAdd, hw0, hw1, hw2, one_mul]
    have c1 := (hYcomm 0 1 (by decide) ϖS
      (u (Multiplicative.ofAdd (Multiplicative.toAdd v 1)))).eq
    have c2 := (hYcomm 0 2 (by decide) ϖS
      (u (Multiplicative.ofAdd (Multiplicative.toAdd v 2)))).eq
    rw [← hϖu, map_mul, map_mul, map_inv]
    calc Y 0 ϖS * (Y 0 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 0))) *
          Y 1 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 1))) *
          Y 2 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 2)))) * (Y 0 ϖS)⁻¹ =
        Y 0 ϖS * Y 0 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 0))) * (Y 0 ϖS)⁻¹ *
          (Y 0 ϖS * Y 1 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 1))) * (Y 0 ϖS)⁻¹) *
          (Y 0 ϖS * Y 2 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 2))) * (Y 0 ϖS)⁻¹) := by
          group
      _ = _ := by rw [c1, c2, mul_inv_cancel_right, mul_inv_cancel_right]
  let C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  let ιC : ↥C →* ModGL TwistTag.E6.tag Ω := (baseChangeGL (algebraMap K Ω)).comp C.subtype
  have hιC : Function.Injective ιC :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hιCr : ιC.range = C.map (baseChangeGL (algebraMap K Ω)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have htmem : ∀ v, tΩ v ∈ ιC.range := fun v => by
    rw [hιCr, htΩ]
    exact mul_mem (mul_mem (hYC 0 _) (hYC 1 _)) (hYC 2 _)
  have hxmem : Y 0 ϖS ∈ ιC.range := by
    rw [hιCr]
    exact hYC 0 ϖS
  let eC := MonoidHom.ofInjective hιC
  let t : Multiplicative (Fin 3 → ZMod p) →* ↥C :=
    eC.symm.toMonoidHom.comp (tΩ.codRestrict ιC.range htmem)
  let x : ↥C := eC.symm ⟨Y 0 ϖS, hxmem⟩
  have hιe : ∀ y : ↥ιC.range, ιC (eC.symm y) = y := fun y => by
    rw [← MonoidHom.ofInjective_apply hιC, MulEquiv.apply_symm_apply]
  have hιt : ∀ v, ιC (t v) = tΩ v := fun v => hιe ⟨tΩ v, htmem v⟩
  have hιx : ιC x = Y 0 ϖS := hιe ⟨Y 0 ϖS, hxmem⟩
  refine ⟨t, x, fun v w hvw => hinj ?_, fun v => hιC ?_⟩
  · rw [← hιt, ← hιt, hvw]
  · rw [map_mul, map_mul, map_inv, hιt, hιt, hιx, hact]


theorem ggTorusWNormSC_recipe_twE6_phi6 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1) :
    GGTorusWNormSC p (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  classical
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  have hp3 : p ≠ 3 := by omega
  have hp2 : p ≠ 2 := by omega
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobeniusEquiv_def K 2 n c
  have he : orderOf (((2 ^ n : ℕ)) : ZMod p) = 6 :=
    E8PowerWNorm.orderOf_eq_six_of_dvd hp hp2 hp3 hpq
  have hpq' : ¬ p ∣ 2 ^ n := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n = 1 := by omega
    subst hn1
    have h3 : p ∣ 3 := by simpa using hpq
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  obtain ⟨τ, ϖ, hτ, hϖ, hτp, hϖτ⟩ :=
    CFSG.ClassicalGroups.Unitary.exists_singer_SUid σ (q := 2 ^ n) hK hσ hpq
  have hϖτ' : ϖ * τ * ϖ⁻¹ = τ ^ Nat.card K := by rw [hK]; exact hϖτ
  have hIU : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (p := 2) (f := n) hK
  have hnorm : 3 = 3 → ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1 := by
    intro _
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
    have hcardU : Nat.card Kˣ = Nat.card K - 1 := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
    refine ⟨g, g.ne_zero, fun h => ?_⟩
    have h1 : g ^ (2 ^ n + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, ← hσ]
      exact h
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hord, hcardU, hK] at hdvd
    have hle := Nat.le_of_dvd (by positivity) hdvd
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hsq : (2 ^ n) ^ 2 ≤ 2 ^ n + 2 := by
      have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    nlinarith
  have hperf := CFSG.ClassicalGroups.Unitary.commutator_SUid_eq_top hIU (le_refl 3) hnorm
  obtain ⟨t, x, htinj, hx⟩ := exists_twisted_reference hn hK hp3 hτ hϖ hτp hϖτ' hperf
  obtain ⟨ε, -⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  have hS : SylowTorus (twistedE6RootGroup K σ) p 3 :=
    CFSG.HardMathSupport.Lang.TwE6Step3.sylowTorus_twistedE6_six Nat.prime_two hn K hK σ hσ hp
      hp7 hpq' he
  have hQ0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
    rw [hK]
    intro hz
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at hz
    exact hpq' (hp.dvd_of_dvd_pow hz)
  have hQ : ((Nat.card K : ℕ) : ZMod p) ^ 2 ≠ 1 := by
    rw [hK]
    intro h4
    have h4' : (((2 ^ n : ℕ)) : ZMod p) ^ 4 = 1 := by
      rw [← h4]
      push_cast
      ring
    have hd := orderOf_dvd_of_pow_eq_one h4'
    rw [he] at hd
    norm_num at hd
  exact ggTorusWNormSC_of_reference hp (TwE6Delta.center_recipeR_eq_bot hn hK)
    (TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3) (TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3)
    ε.symm hS htinj hx hQ0 hQ

theorem largeEvenLabelAll_wnorm_twE6_phi6 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {lab : LargeEvenLabel} (htag : lab.tag = .twE6) (hn : 1 ≤ lab.n)
    (hpq : p ∣ (2 ^ lab.n) ^ 2 - 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag hn hpq ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_twE6_phi6 hn hK hp hp7 hpq

end TwE6PhiSix

end CFSG.StandardType

end
