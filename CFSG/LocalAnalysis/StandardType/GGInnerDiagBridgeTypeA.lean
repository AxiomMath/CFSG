module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix

namespace InnerDiagA

variable {m : ℕ} {F : Type} [Field F]

theorem exists_conj_transvection_eq {i j : Fin (m + 1)} (hij : i ≠ j)
    {h : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hh : h ∈ Subgroup.normalizer (SpecialLinear.rootSubgroup m F hij :
      Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F))) :
    ∃ χ : F, ∀ t : F, h * Matrix.SpecialLinearGroup.transvection hij t * h⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij (χ * t) := by
  obtain ⟨χ, hχ⟩ := (SpecialLinear.mem_rootSubgroup hij _).mp
    ((Subgroup.mem_normalizer_iff.mp hh _).mp (SpecialLinear.transvection_mem_rootSubgroup hij 1))
  refine ⟨χ, fun t => ?_⟩
  have hHH : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      ((h⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hE : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * single i j 1 *
      ((h⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      single i j χ := by
    have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin (m + 1)) F =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) hχ
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe] at h1
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hHH] at h1
    exact (add_left_cancel h1).symm
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hHH]
  congr 1
  rw [show (single i j t : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = t • single i j (1 : F) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one],
    Matrix.mul_smul, Matrix.smul_mul, hE, Matrix.smul_single, smul_eq_mul, mul_comm]

theorem eq_zero_of_transvection_mem_center {i j : Fin (m + 1)} (hij : i ≠ j) {t : F}
    (h : Matrix.SpecialLinearGroup.transvection hij t ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) : t = 0 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have h1 := congrFun (congrFun hr i) j
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hij,
    Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.single_apply_same, zero_add] at h1
  exact h1.symm

theorem eq_of_map_transvection_eq {G : Type*} [Group G]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) {i j : Fin (m + 1)}
    (hij : i ≠ j) {a b : F}
    (h : ψ (Matrix.SpecialLinearGroup.transvection hij a) =
      ψ (Matrix.SpecialLinearGroup.transvection hij b)) :
    a = b := by
  have hmem : Matrix.SpecialLinearGroup.transvection hij (-a + b) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, Matrix.SpecialLinearGroup.transvection_add,
      ← Matrix.SpecialLinearGroup.transvection_inv,
      map_mul, map_inv, h, inv_mul_cancel]
  have := eq_zero_of_transvection_mem_center hij (hker hmem)
  linear_combination -this

@[expose] def typeARoot (i j : Fin (m + 1)) : Fin m → ℤ := fun k =>
  (if i.val ≤ k.val then 1 else 0) - (if j.val ≤ k.val then 1 else 0)

theorem toStd_typeARoot (i j : Fin (m + 1)) :
    SpecialLinear.toStd m (typeARoot i j) = Pi.single i 1 - Pi.single j 1 := by
  funext a
  have ha := a.isLt
  have hi := i.isLt
  have hj := j.isLt
  simp only [SpecialLinear.toStd, typeARoot, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

variable (F) in
theorem typeARoot_mem_roots {i j : Fin (m + 1)} (hij : i ≠ j) :
    typeARoot i j ∈ (SpecialLinear.rootDatum m F).roots := by
  show typeARoot i j ∈ roots (SpecialLinear.isFiniteType_A m) ∅
  rw [SpecialLinear.roots_eq]
  exact ⟨i, j, hij, toStd_typeARoot i j⟩

theorem rootGroup_typeARoot {i j : Fin (m + 1)} (hij : i ≠ j) :
    SpecialLinear.rootGroup m F (typeARoot i j) = SpecialLinear.rootSubgroup m F hij :=
  SpecialLinear.rootGroup_eq m F hij (toStd_typeARoot i j)

theorem exists_chi_of_ggPsiInnerDiag {G : Type*} [Group G]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G) {c : G}
    (h : GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ c) :
    ∃ g ∈ ψ.range, ∃ χ : Fin (m + 1) → Fin (m + 1) → F,
      ∀ (i j : Fin (m + 1)) (hij : i ≠ j) (t : F),
        (c * g)⁻¹ * ψ (Matrix.SpecialLinearGroup.transvection hij t) * (c * g) =
          ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t)) := by
  obtain ⟨g, hg, hγ⟩ := h
  have key : ∀ (i j : Fin (m + 1)) (hij : i ≠ j), ∃ χ : F, ∀ t : F,
      (c * g)⁻¹ * ψ (Matrix.SpecialLinearGroup.transvection hij t) * (c * g) =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ * t)) := by
    intro i j hij
    obtain ⟨h, hh, hz⟩ := hγ _ (typeARoot_mem_roots F hij)
    have hN : h ∈ Subgroup.normalizer (SpecialLinear.rootSubgroup m F hij :
        Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) := by
      simp only [ggTorus, Subgroup.mem_iInf] at hh
      have h1 : h ∈ Subgroup.normalizer (SpecialLinear.rootGroup m F (typeARoot i j) :
          Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) := hh _ (typeARoot_mem_roots F hij)
      rwa [rootGroup_typeARoot] at h1
    obtain ⟨χ, hχ⟩ := exists_conj_transvection_eq hij hN
    have hmem : ∀ t : F, Matrix.SpecialLinearGroup.transvection hij t ∈
        SpecialLinear.rootGroup m F (typeARoot i j) := fun t => by
      rw [rootGroup_typeARoot]
      exact SpecialLinear.transvection_mem_rootSubgroup hij t
    refine ⟨χ, fun t => ?_⟩
    rw [hz _ (hmem t), hχ]
  choose! χ hχ using key
  exact ⟨g, hg, χ, hχ⟩

theorem chi_cocycle {G : Type*} [Group G] (ψ β : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {χ : Fin (m + 1) → Fin (m + 1) → F}
    (hχ : ∀ (i j : Fin (m + 1)) (hij : i ≠ j) (t : F),
      β (Matrix.SpecialLinearGroup.transvection hij t) =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t)))
    {i j k : Fin (m + 1)} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    χ i k = χ i j * χ j k := by
  have h1 := congrArg β
    (Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjk hik (1 : F) 1)
  rw [map_commutatorElement, hχ, hχ, hχ, ← map_commutatorElement,
    Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjk hik] at h1
  have h2 := eq_of_map_transvection_eq ψ hker hik h1
  linear_combination -h2

theorem exists_diag_of_cocycle (hm : 2 ≤ m) {χ : Fin (m + 1) → Fin (m + 1) → F}
    (hcoc : ∀ i j k : Fin (m + 1), i ≠ j → j ≠ k → i ≠ k → χ i k = χ i j * χ j k)
    (hne : ∀ i j : Fin (m + 1), i ≠ j → χ i j ≠ 0) :
    ∃ d : Fin (m + 1) → Fˣ, ∀ i j : Fin (m + 1), i ≠ j → (d i : F) = χ i j * d j := by
  classical
  have hinv : ∀ a b : Fin (m + 1), a ≠ b → χ a b * χ b a = 1 := by
    intro a b hab
    obtain ⟨c, hca, hcb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by omega)
    have h1 := hcoc c a b hca hab hcb
    have h2 := hcoc c b a hcb hab.symm hca
    have h3 : χ c b * (χ a b * χ b a - 1) = 0 := by
      linear_combination (-1 : F) * h1 - χ a b * h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h (hne c b hcb)
    · exact sub_eq_zero.mp h
  let d : Fin (m + 1) → Fˣ := fun i =>
    if h : i = Fin.last m then 1 else Units.mk0 (χ i (Fin.last m)) (hne i (Fin.last m) h)
  have hd1 : ∀ i, i = Fin.last m → (d i : F) = 1 := fun i hi => by simp [d, hi]
  have hd2 : ∀ i, i ≠ Fin.last m → (d i : F) = χ i (Fin.last m) := fun i hi => by simp [d, hi]
  refine ⟨d, fun i j hij => ?_⟩
  by_cases hi : i = Fin.last m <;> by_cases hj : j = Fin.last m
  · exact absurd (hi.trans hj.symm) hij
  · rw [hd1 i hi, hd2 j hj, hi, mul_comm]
    exact (hinv j (Fin.last m) hj).symm
  · rw [hd2 i hi, hd1 j hj, hj, mul_one]
  · rw [hd2 i hi, hd2 j hj]
    exact hcoc i j (Fin.last m) hij hj hi

@[expose] noncomputable def diagGL (d : Fin (m + 1) → Fˣ) : GL (Fin (m + 1)) F :=
  ⟨diagonal fun k => (d k : F), diagonal fun k => ((d k)⁻¹ : Fˣ),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

theorem coe_diagGL (d : Fin (m + 1) → Fˣ) :
    ((diagGL d : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      diagonal fun k => (d k : F) :=
  rfl

theorem coe_diagGL_inv (d : Fin (m + 1) → Fˣ) :
    (((diagGL d)⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      diagonal fun k => (((d k)⁻¹ : Fˣ) : F) :=
  rfl

variable (m F) in
@[expose] noncomputable def slEquiv :
    Matrix.SpecialLinearGroup (Fin (m + 1)) F ≃* ↥(LargeEvenSLGroup (Fin (m + 1)) F) :=
  Matrix.SpecialLinearGroup.toGLKerEquiv

theorem coe_slEquiv (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    ((slEquiv m F u : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
  rfl

@[expose] noncomputable def conjSL (A : GL (Fin (m + 1)) F) :
    Matrix.SpecialLinearGroup (Fin (m + 1)) F →* Matrix.SpecialLinearGroup (Fin (m + 1)) F :=
  (slEquiv m F).symm.toMonoidHom.comp
    ((MulAut.conjNormal A).toMonoidHom.comp (slEquiv m F).toMonoidHom)

theorem slEquiv_conjSL (A : GL (Fin (m + 1)) F) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    slEquiv m F (conjSL A u) = MulAut.conjNormal A (slEquiv m F u) := by
  simp [conjSL]

theorem coe_conjSL (A : GL (Fin (m + 1)) F) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    ((conjSL A u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
  have h := congrArg (fun x : ↥(LargeEvenSLGroup (Fin (m + 1)) F) =>
    ((x : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) (slEquiv_conjSL A u)
  simpa only [MulAut.conjNormal_apply, Units.val_mul, coe_slEquiv] using h

theorem conjSL_diagGL_transvection (d : Fin (m + 1) → Fˣ) {i j : Fin (m + 1)} (hij : i ≠ j)
    (t : F) :
    conjSL (diagGL d) (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection hij ((d i : F) * t * ((d j)⁻¹ : Fˣ)) := by
  apply Subtype.ext
  rw [coe_conjSL, coe_diagGL, coe_diagGL_inv, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.add_apply,
    Matrix.single_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have hne : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [hne]
  · by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hab]
    · simp [hab, h]

theorem exists_conj_eq_conjSL (hm : 2 ≤ m) {G : Type*} [Group G]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) {x : G}
    {χ : Fin (m + 1) → Fin (m + 1) → F}
    (hχ : ∀ (i j : Fin (m + 1)) (hij : i ≠ j) (t : F),
      x⁻¹ * ψ (Matrix.SpecialLinearGroup.transvection hij t) * x =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t))) :
    ∃ D : GL (Fin (m + 1)) F, ∀ u, x⁻¹ * ψ u * x = ψ (conjSL D u) := by
  let β : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G :=
    (MulAut.conj x⁻¹).toMonoidHom.comp ψ
  have hβ : ∀ u, β u = x⁻¹ * ψ u * x := fun u => by
    simp [β]
  have hχ' : ∀ (i j : Fin (m + 1)) (hij : i ≠ j) (t : F),
      β (Matrix.SpecialLinearGroup.transvection hij t) =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t)) :=
    fun i j hij t => (hβ _).trans (hχ i j hij t)
  have hne : ∀ i j : Fin (m + 1), i ≠ j → χ i j ≠ 0 := by
    intro i j hij h0
    have h1 := hχ i j hij 1
    rw [h0, zero_mul, Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one] at h1
    have h2 : ψ (Matrix.SpecialLinearGroup.transvection hij 1) = 1 := by
      calc ψ (Matrix.SpecialLinearGroup.transvection hij 1)
          = x * (x⁻¹ * ψ (Matrix.SpecialLinearGroup.transvection hij 1) * x) * x⁻¹ := by group
        _ = 1 := by rw [h1]; group
    exact one_ne_zero (eq_zero_of_transvection_mem_center hij (hker h2))
  obtain ⟨d, hd⟩ := exists_diag_of_cocycle (χ := χ) hm
    (fun _ _ _ hij hjk hik => chi_cocycle ψ β hker hχ' hij hjk hik) hne
  refine ⟨diagGL d, fun u => ?_⟩
  have hβψ : β = ψ.comp (conjSL (diagGL d)) := by
    refine MonoidHom.eq_of_eqOn_dense
      Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field ?_
    rintro _ ⟨⟨i, j, hij, t⟩, rfl⟩
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, hχ', MonoidHom.comp_apply,
      conjSL_diagGL_transvection, hd i j hij, Units.val_inv_eq_inv_val,
      mul_right_comm (χ i j), mul_assoc _ _ ((d j : F))⁻¹, mul_inv_cancel₀ (d j).ne_zero,
      mul_one]
  rw [← hβ, hβψ, MonoidHom.comp_apply]

theorem linConjAut_mem (A : GL (Fin (m + 1)) F) :
    TableB.linConjAut (Fin (m + 1)) F A ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (m + 1)) F)) Set.univ := by
  refine ⟨A, Set.mem_univ _, fun h h' hh' => ?_⟩
  show TableB.linConjAut (Fin (m + 1)) F A (h : LargeEvenProj _) = (h' : LargeEvenProj _)
  rw [TableB.linConjAut_mk]
  congr 1
  exact Subtype.ext (by rw [MulAut.conjNormal_apply, hh'])

theorem mem_center_of_rangeRestrict_mem_center {U G : Type*} [Group U] [Group G]
    (hU : commutator U = ⊤) (ψ : U →* G) (hker : ψ.ker ≤ Subgroup.center U) {u : U}
    (hu : ψ.rangeRestrict u ∈ Subgroup.center ψ.range) : u ∈ Subgroup.center U := by
  have key : (MulAut.conj u).toMonoidHom = MonoidHom.id U := by
    refine TypeA.eq_of_inv_mul_mem_center hU _ _ fun s => hker ?_
    have hc : ψ s * ψ u = ψ u * ψ s :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hu (ψ.rangeRestrict s))
    have h1 : ((MulAut.conj u).toMonoidHom s : U) = u * s * u⁻¹ := rfl
    rw [MonoidHom.mem_ker, h1, MonoidHom.id_apply, map_mul, map_inv, map_mul, map_mul, map_inv,
      ← hc]
    group
  rw [Subgroup.mem_center_iff]
  intro s
  have h1 : u * s * u⁻¹ = s := DFunLike.congr_fun key s
  calc s * u = u * s * u⁻¹ * u := by rw [h1]
    _ = u * s := by group

theorem largeEvenMarking_typeA (hm : 2 ≤ m) [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : 1 ≤ f) {G : Type} [Group G] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) :
    LargeEvenMarking ↥ψ.range (fun _ _ _ I _ θ => ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
      GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ c →
        ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ) := by
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin (m + 1)) F) = ⊤ :=
    CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (by omega)
  let H := LargeEvenSLGroup (Fin (m + 1)) F
  let q₁ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* ↥ψ.range ⧸ Subgroup.center ↥ψ.range :=
    (QuotientGroup.mk' _).comp ψ.rangeRestrict
  let q₂ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* LargeEvenProj H :=
    (LargeEvenProjMk H).comp (slEquiv m F).toMonoidHom
  have hq₁ : Function.Surjective q₁ :=
    (QuotientGroup.mk'_surjective _).comp ψ.rangeRestrict_surjective
  have hq₂ : Function.Surjective q₂ :=
    (QuotientGroup.mk'_surjective _).comp (slEquiv m F).surjective
  have hk₁ : q₁.ker = Subgroup.center _ := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (ψ.rangeRestrict u) : ↥ψ.range ⧸ Subgroup.center ↥ψ.range) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    refine ⟨mem_center_of_rangeRestrict_mem_center hperf ψ hker, fun hu => ?_⟩
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨s, rfl⟩ := ψ.rangeRestrict_surjective l
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu s]
  have hk₂ : q₂.ker = Subgroup.center _ := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (slEquiv m F u) : LargeEvenProj H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, largeEvenScalars_def,
      MonoidHom.mem_range]
    constructor
    · rintro ⟨c, hc⟩
      have hmat : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
          Matrix.scalar (Fin (m + 1)) (c : F) := by
        rw [← coe_slEquiv, ← hc, Matrix.GeneralLinearGroup.coe_scalar]
      rw [Subgroup.mem_center_iff]
      intro v
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hmat]
      exact (Matrix.scalar_commute (c : F) (fun r => Commute.all _ r) _).eq.symm
    · intro hu
      obtain ⟨r, hr, hru⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hu
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow (by simp)] at hr
        exact zero_ne_one hr
      exact ⟨Units.mk0 r hr0, Units.ext (by
        rw [Matrix.GeneralLinearGroup.coe_scalar, coe_slEquiv]
        exact hru)⟩
  let θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* LargeEvenProj H :=
    (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hk₁.trans hk₂.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective q₂ hq₂))
  have hθ : ∀ u, θ (q₁ u) = q₂ u := fun u => by
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm (q₁ u) =
        (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F ⧸ q₁.ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    simp only [θ, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  let e : LargeEvenProj H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F :=
    (QuotientGroup.quotientKerEquivOfSurjective q₂ hq₂).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hk₂)
  have hPSL : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 (m + 1) (by omega) (.inl (by omega))
      (.inl (by omega))
  have hsimple : IsSimpleGroup (LargeEvenProj H) := (MulEquiv.isSimpleGroup_congr e).mpr hPSL
  have hnonab : ∃ a b : LargeEvenProj H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_centerQuot_of_perfect hperf hPSL.toNontrivial
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  have hcomm : commutator ↥ψ.range = ⊤ := by
    have h1 := congrArg (Subgroup.map ψ.rangeRestrict) hperf
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ ψ.rangeRestrict_surjective] at h1
    rw [commutator_def]
    exact h1
  have key : ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
      GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ c →
        ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) Set.univ,
          LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ := by
    intro c hc hdiag
    obtain ⟨g, ⟨s, rfl⟩, χ, hχ⟩ := exists_chi_of_ggPsiInnerDiag ψ hdiag
    obtain ⟨D, hD⟩ := exists_conj_eq_conjSL hm ψ hker hχ
    refine ⟨TableB.linConjAut (Fin (m + 1)) F ((slEquiv m F s : GL (Fin (m + 1)) F) * D),
      linConjAut_mem _, ?_⟩
    intro l l' hl
    obtain ⟨u, rfl⟩ := ψ.rangeRestrict_surjective l
    have hl' : l' = ψ.rangeRestrict (s * conjSL D u * s⁻¹) := by
      apply Subtype.ext
      rw [hl]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        MonoidHom.coe_rangeRestrict]
      rw [← hD u]
      group
    rw [hl']
    change TableB.linConjAut _ _ _ (θ (q₁ u)) = θ (q₁ (s * conjSL D u * s⁻¹))
    rw [hθ, hθ]
    change TableB.linConjAut _ _ _ (slEquiv m F u : LargeEvenProj H) =
      (slEquiv m F (s * conjSL D u * s⁻¹) : LargeEvenProj H)
    rw [TableB.linConjAut_mk]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, map_mul, map_mul, map_inv, slEquiv_conjSL]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    group
  have hm1 : m = 1 → 2 ≤ f := fun h => by omega
  have hraw : LargeEvenRecipeLinear (m + 1) (2 ^ f) fun R _ I _ => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ ∃ θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* R,
        ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
          GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ c →
            ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ :=
    ⟨F, inferInstance, inferInstance, hF, hsimple, hnonab, θ, key⟩
  exact ⟨hcomm, ⟨.A, m, f⟩, ⟨hf, (by omega : 1 ≤ m), hm1⟩, hraw⟩

end InnerDiagA

section Genuine

theorem ggInnerDiagMarkingAt_PSL : GGInnerDiagMarkingAt .PSL := by
  intro G _ _ n f ψ G₀ hpres
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  obtain ⟨-, hf, hn, -⟩ := hadm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact InnerDiagA.largeEvenMarking_typeA (F := GaloisField 2 f) hrk
    (GaloisField.card 2 f (by omega)) hf ψ hker

end Genuine

section Assembly

theorem lc_gl_std_of_v2_steps_typeA
    (hHolt : CFSG.RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple)
    (ha : GGBstarInput) (ha₀ : GGLNoncyclicInput) (hb : GGStdSubPreInput)
    (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input) (hc₂ : GGCor42Input)
    (hc₃ : GGNoTransvectionInput) (hd : GGCoxeterLabelInput) (he : GGPropFiveTwentyOneV2Input)
    (hf : GGHypSixV2Input) (hg₁ : GGCorFiveTwentyInput) (hg₂ : GGOmegaOneInput)
    (hR : ∀ t, GGInnerDiagOpenTag t → GGInnerDiagMarkingAt t)
    (h1 : GGSixStepOneV2Input) (h2 : GGSixStepTwoV2Input) (h3a : GGSixStepThreeAInput)
    (h3b : GGSixStepThreeBInput) (h3c : GGSixStepThreeCInput) (h3d : GGSixStepThreeDInput)
    (hKG : GGRootInvolutionCentralInput)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he4 : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G :=
  lc_gl_std_of_v2_steps_mk hHolt ha ha₀ hb hc₀ hc₁ hc₂ hc₃ hd he hf hg₁ hg₂
    (ggInnerDiagMarkingInput_of_open ggInnerDiagMarkingAt_PSL hR) h1 h2 h3a h3b h3c h3d hKG
    G hnonab hK hchar he4 p hp B x L hS hst

end Assembly

end CFSG.StandardType
