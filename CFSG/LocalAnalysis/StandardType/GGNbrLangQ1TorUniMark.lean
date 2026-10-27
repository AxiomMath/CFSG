module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1RLevel
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGE0PSUFrame
public import CFSG.LocalAnalysis.StandardType.GGE0LiftGeneric

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.SemisimpleCentralizers CFSG.StandardType.S2MathAs51642Interfaces

open CFSG.Open (StatedSU StatedSL)
open CFSG.StandardType.ClassicalBlocks (GUFull)
open scoped commutatorElement

private theorem l02qu4_mem_statedSU_of_mem_unitaryFull {m Q p f : ℕ} {E : Type} [Field E]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E) (hQ : Q = p ^ f)
    {A : GL (Fin m) E} (hA : A ∈ GUFull m Q E)
    (hdet : (A : Matrix (Fin m) (Fin m) E).det = 1) : A ∈ StatedSU m Q E :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.mem_statedSU_of_mem_statedGU
    h hQ hA hdet

private theorem l02qu4_statedSU_eq_unitaryFull_inf_ker_det {m Q p f : ℕ} {E : Type} [Field E]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E) (hQ : Q = p ^ f) :
    StatedSU m Q E = GUFull m Q E ⊓
      (Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ).ker := by
  refine le_antisymm ?_ ?_
  · intro A hA
    refine ⟨?_, ?_⟩
    · exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.statedSU_le_statedGU
        (q := Q) (n := m) (L := E) hA
    · change (Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ) A = 1
      exact Units.ext (by
        simpa [Matrix.GeneralLinearGroup.val_det_apply] using
          CFSG.Open.StatedAPI.det_of_mem_statedSU hA)
  · intro A hA
    rw [Subgroup.mem_inf] at hA
    refine l02qu4_mem_statedSU_of_mem_unitaryFull h hQ hA.1 ?_
    have hdet : (Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ) A = 1 := hA.2
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using congrArg Units.val hdet

private theorem l02qu4_guFull_eq_primeFormUnitary {m Q p f : ℕ} {E : Type} [Field E]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E) (hQ : Q = p ^ f) :
    GUFull m Q E = CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (1 : Matrix (Fin m) (Fin m) E) := by
  rw [GUFull]
  have hset : {A : GL (Fin m) E | Matrix.transpose
      ((A : Matrix (Fin m) (Fin m) E).map (· ^ Q)) * (A : Matrix (Fin m) (Fin m) E) = 1} =
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        (1 : Matrix (Fin m) (Fin m) E) : Set (GL (Fin m) E)) := by
    ext A
    rw [Set.mem_setOf_eq, SetLike.mem_coe,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary]
    have hmap : (A : Matrix (Fin m) (Fin m) E).map (· ^ Q) =
        (A : Matrix (Fin m) (Fin m) E).map h.bar := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, hQ, h.bar_apply]
    rw [hmap]
    simp only [Matrix.mul_one]
  rw [hset, Subgroup.closure_eq]

private theorem l02qu4_guFull_subset_guSet {m Q p f : ℕ} {E : Type} [Field E]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E) (hQ : Q = p ^ f) :
    (GUFull m Q E : Set (GL (Fin m) E)) ⊆ LargeEvenGUSet (Fin m) E Q := by
  intro A hA
  rw [l02qu4_guFull_eq_primeFormUnitary h hQ] at hA
  rw [SetLike.mem_coe,
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary] at hA
  refine ⟨1, one_ne_zero, one_pow _, ?_⟩
  rw [one_smul]
  rw [show (A : Matrix (Fin m) (Fin m) E).map (· ^ Q) =
      (A : Matrix (Fin m) (Fin m) E).map h.bar by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, hQ, h.bar_apply]]
  simpa only [Matrix.mul_one] using hA

private theorem l02qu4_guFull_conj_mem_statedSU {m Q p f : ℕ} {E : Type} [Field E]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E) (hQ : Q = p ^ f)
    {A : GL (Fin m) E} (hA : A ∈ GUFull m Q E) :
    ∀ g ∈ StatedSU m Q E, A * g * A⁻¹ ∈ StatedSU m Q E := by
  intro g hg
  have hSU := l02qu4_statedSU_eq_unitaryFull_inf_ker_det (m := m) h hQ
  have hg' := hSU ▸ hg
  rw [Subgroup.mem_inf] at hg'
  rw [hSU, Subgroup.mem_inf]
  refine ⟨(GUFull m Q E).mul_mem ((GUFull m Q E).mul_mem hA hg'.1)
    ((GUFull m Q E).inv_mem hA), ?_⟩
  change (Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ) (A * g * A⁻¹) = 1
  have hdetg : (Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ) g = 1 := hg'.2
  rw [map_mul, map_mul, map_inv, hdetg, mul_one, mul_inv_cancel]

private theorem l02qu4_unitaryMarking_conj_mem_of_mem_unitaryFull {m Q p f : ℕ} {E : Type}
    [Field E] [Finite E] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E)
    (hQ : Q = p ^ f)
    (hcenter : Subgroup.center ↥(LargeEvenSUGroup (Fin m) E Q) =
      (LargeEvenScalars (Fin m) E).subgroupOf (LargeEvenSUGroup (Fin m) E Q))
    {ε : GL (Fin m) E} (hε : ε ∈ GUFull m Q E) :
    ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin m) E Q))
        (LargeEvenGUSet (Fin m) E Q),
      LargeEvenInduces (QuotientGroup.quotientMulEquivOfEq hcenter)
        (fun l l' : ↥(LargeEvenSUGroup (Fin m) E Q) =>
          (l' : GL (Fin m) E) = ε⁻¹ * l * ε) φ := by
  let SU := LargeEvenSUGroup (Fin m) E Q
  let Z := (LargeEvenScalars (Fin m) E).subgroupOf SU
  change ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk SU) (LargeEvenGUSet (Fin m) E Q),
    LargeEvenInduces (QuotientGroup.quotientMulEquivOfEq hcenter)
      (fun l l' : ↥SU => (l' : GL (Fin m) E) = ε⁻¹ * l * ε) φ
  have hcenter' : Subgroup.center ↥SU = Z := hcenter
  have : Z.Characteristic := hcenter' ▸ Subgroup.centerCharacteristic
  have hmem := l02qu4_guFull_conj_mem_statedSU (m := m) h hQ (A := ε⁻¹)
    ((GUFull m Q E).inv_mem hε)
  have hmem' := l02qu4_guFull_conj_mem_statedSU (m := m) h hQ (A := ε) hε
  let ψ : MulAut ↥SU :=
    { toFun := fun g => ⟨ε⁻¹ * (g : GL (Fin m) E) * ε, hmem g g.2⟩
      invFun := fun g => ⟨ε * (g : GL (Fin m) E) * ε⁻¹, hmem' g g.2⟩
      left_inv := fun g => Subtype.ext (by group)
      right_inv := fun g => Subtype.ext (by group)
      map_mul' := fun g₁ g₂ => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let φ : MulAut (LargeEvenProj SU) :=
    QuotientGroup.congr Z Z ψ (Subgroup.characteristic_iff_map_eq.mp inferInstance ψ)
  refine ⟨φ, ?_, ?_⟩
  · refine ⟨ε⁻¹, l02qu4_guFull_subset_guSet h hQ ((GUFull m Q E).inv_mem hε), ?_⟩
    intro g g' hrel
    simp only [LargeEvenProjMk, φ]
    apply congrArg (QuotientGroup.mk' Z)
    refine Subtype.ext ?_
    change ε⁻¹ * (g : GL (Fin m) E) * ε = (g' : GL (Fin m) E)
    rw [hrel]
    group
  · intro g g' hrel
    simp only [QuotientGroup.quotientMulEquivOfEq_mk, φ]
    refine congrArg (QuotientGroup.mk' Z) (Subtype.ext ?_)
    exact hrel.symm

private theorem l02qu4_largeEvenRawDatum_unitaryLabel_statedSU {m Q p f : ℕ} {E : Type} [Field E]
    [Finite E] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E)
    (hQ : Q = p ^ f) (hE : Nat.card E = Q ^ 2) (h2f : 2 ^ f = Q) (hm : 3 ≤ m)
    (hqs : CFSG.IsQuasisimple ↥(LargeEvenSUGroup (Fin m) E Q))
    (hcenter : Subgroup.center ↥(LargeEvenSUGroup (Fin m) E Q) =
      (LargeEvenScalars (Fin m) E).subgroupOf (LargeEvenSUGroup (Fin m) E Q)) :
    CFSG.Assembly.LargeEvenRawDatumLegacy (⟨.twA, m - 1, f⟩ : LargeEvenLabel)
      (fun R _ I _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥(LargeEvenSUGroup (Fin m) E Q) ⧸
            Subgroup.center ↥(LargeEvenSUGroup (Fin m) E Q) ≃* R,
          GGChevStTag (⟨.twA, m - 1, f⟩ : LargeEvenLabel) ∧
          ∀ ε ∈ GUFull m Q E, ∃ φ ∈ I, LargeEvenInduces θ
            (fun l l' : ↥(LargeEvenSUGroup (Fin m) E Q) =>
              (l' : GL (Fin m) E) = ε⁻¹ * l * ε) φ) := by
  simp only [CFSG.Assembly.LargeEvenRawDatumLegacy]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m), h2f]
  refine ⟨E, inferInstance, inferInstance, hE, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · have : IsSimpleGroup (↥(LargeEvenSUGroup (Fin m) E Q) ⧸
        Subgroup.center ↥(LargeEvenSUGroup (Fin m) E Q)) := hqs.2.1
    exact (QuotientGroup.quotientMulEquivOfEq hcenter).symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hqs.2.2
    refine ⟨(QuotientGroup.quotientMulEquivOfEq hcenter) a,
      (QuotientGroup.quotientMulEquivOfEq hcenter) b, ?_⟩
    intro h
    exact hab (by simpa using congrArg (QuotientGroup.quotientMulEquivOfEq hcenter).symm h)
  · refine ⟨QuotientGroup.quotientMulEquivOfEq hcenter, by simp [GGChevStTag], ?_⟩
    intro ε hε
    exact l02qu4_unitaryMarking_conj_mem_of_mem_unitaryFull h hQ hcenter hε

private theorem l02qu4_unitaryLabel_data {m Q p f : ℕ} {E : Type} [Field E] [Finite E]
    (hQ : Q = p ^ f) (hE : Nat.card E = Q ^ 2) (hp2 : p = 2) (hm : 3 ≤ m)
    (h32 : (m, Q) ≠ (3, 2)) :
    2 ^ f = Q ∧ LargeEvenInLambda2 (⟨.twA, m - 1, f⟩ : LargeEvenLabel) := by
  have h2f : 2 ^ f = Q := by rw [hQ, hp2]
  have hQ2 : 2 ≤ Q := by
    have h1 : 1 < Nat.card E := Finite.one_lt_card
    rw [hE] at h1
    by_contra hlt
    have hle : Q ≤ 1 := by omega
    have hsq : Q ^ 2 ≤ 1 := by
      have := Nat.pow_le_pow_left hle 2
      simpa using this
    omega
  have hf1 : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hQ
    omega
  refine ⟨h2f, ?_⟩
  simp only [LargeEvenInLambda2]
  refine ⟨hf1, by omega, ?_⟩
  intro hrank
  by_contra hf
  have hf1' : f = 1 := by omega
  rw [hf1', pow_one] at hQ
  exact h32 (by rw [show m = 3 by omega, hQ, hp2])

private theorem l02qu4_largeEvenMarking_unitaryFull_statedSU {m Q p f : ℕ} {E : Type} [Field E]
    [Finite E] [hchar2 : CharP E 2]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E)
    (hQ : Q = p ^ f) (hE : Nat.card E = Q ^ 2) (hm : 3 ≤ m)
    (h32 : (m, Q) ≠ (3, 2)) :
    LargeEvenMarking ↥(StatedSU m Q E) (fun lab _R _ I _ θ =>
      GGChevStTag lab ∧ ∀ ε ∈ GUFull m Q E,
        ∃ φ ∈ I, LargeEvenInduces θ
          (fun l l' : ↥(StatedSU m Q E) => (l' : GL (Fin m) E) = ε⁻¹ * l * ε) φ) := by
  let : Fact p.Prime := ⟨h.prime⟩
  have : CharP E p := h.charP
  let SU := LargeEvenSUGroup (Fin m) E Q
  have hSUeq : SU = StatedSU m Q E := rfl
  change LargeEvenMarking ↥SU (fun lab R _ I _ θ =>
    GGChevStTag lab ∧ ∀ ε ∈ GUFull m Q E,
      ∃ φ ∈ I, LargeEvenInduces θ
        (fun l l' : ↥SU => (l' : GL (Fin m) E) = ε⁻¹ * l * ε) φ)
  have hqs := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := p) (f := f) (F := E) (n := m) (by rw [← hQ]; exact hE) hm
    (by simpa [hQ] using h32))
  rw [← hQ, ← hSUeq] at hqs
  let Z := (LargeEvenScalars (Fin m) E).subgroupOf SU
  have hcenter : Subgroup.center ↥SU = Z := hqs.2
  have hperf : commutator ↥SU = ⊤ := Group.isPerfect_def.mp hqs.1.1
  have hp2 : p = 2 := CharP.eq E h.charP hchar2
  obtain ⟨h2f, hlab⟩ := l02qu4_unitaryLabel_data hQ hE hp2 hm h32
  refine ⟨hperf, ⟨.twA, m - 1, f⟩, hlab, ?_⟩
  exact l02qu4_largeEvenRawDatum_unitaryLabel_statedSU h hQ hE h2f hm hqs.1 hcenter

private noncomputable def l02qu4_statedSLCenterQuotEquivProjective {m : ℕ} {E : Type} [Field E] :
    StatedSL m E ⧸ Subgroup.center (StatedSL m E) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL m E :=
  (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq m)).trans
    ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center m E)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E)).symm

private theorem l02qu4_statedSLCenterQuotEquivProjective_mk {m : ℕ} {E : Type} [Field E]
    (l : StatedSL m E) :
    l02qu4_statedSLCenterQuotEquivProjective (m := m) (E := E) (QuotientGroup.mk l) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m E
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l) := by
  rw [l02qu4_statedSLCenterQuotEquivProjective]
  simp only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private theorem l02qu4_specialLinearGroupEquivStatedSL_symm_slConjugation {m : ℕ} {E : Type}
    [Field E] {A : GL (Fin m) E} {l l' : StatedSL m E}
    (h : (l' : GL (Fin m) E) = A * (l : GL (Fin m) E) * A⁻¹) :
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l' =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m E A
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l) := by
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  have hl : (l : GL (Fin m) E) =
      ((e.symm l : Matrix.SpecialLinearGroup (Fin m) E) : GL (Fin m) E) := by
    conv_lhs => rw [← MulEquiv.apply_symm_apply e l]
    exact Units.ext (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe m E (e.symm l))
  have h' := congrArg (fun u : GL (Fin m) E => (u : Matrix (Fin m) (Fin m) E)) h
  rw [hl] at h'
  rw [show ((e (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m E A
        (e.symm l)) : StatedSL m E) : GL (Fin m) E) =
      Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m E A
          (e.symm l)) from
    Units.ext (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe m E _)]
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  exact h'

private theorem l02qu4_largeEvenRawDatumLegacy_linear {m f : ℕ} {E : Type} [Field E] [Finite E]
    (hm : 1 ≤ m) (hcard : Nat.card E = 2 ^ f) (Q : LargeEvenRawCont)
    (hQ : Q (LargeEvenProj (LargeEvenSLGroup (Fin m) E))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin m) E)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin m) E)))) :
    LargeEvenRawDatumLegacy (⟨.A, m - 1, f⟩ : LargeEvenLabel) Q := by
  change LargeEvenRecipeLinear (m - 1 + 1) (2 ^ f) Q
  rw [show m - 1 + 1 = m from Nat.sub_add_cancel (by omega)]
  exact ⟨E, inferInstance, inferInstance, hcard, hQ⟩

private theorem l02qu4_largeEvenMarking_statedSL_linear {m f : ℕ} {E : Type} [Field E] [Finite E]
    (hcard : Nat.card E = 2 ^ f)
    (hperf : commutator (StatedSL m E) = ⊤)
    (hsimp : IsSimpleGroup (StatedSL m E ⧸ Subgroup.center (StatedSL m E)))
    (hm : 2 ≤ m) (hf : 1 ≤ f) (hmf : m = 2 → 2 ≤ f) :
    LargeEvenMarking (StatedSL m E)
      (fun lab _ _ I _ θ => GGChevStTag lab ∧
        ∀ ε ∈ (⊤ : Subgroup (GL (Fin m) E)), ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : GL (Fin m) E) = ε⁻¹ * l * ε) φ) := by
  refine ⟨hperf, ⟨⟨.A, m - 1, f⟩, ?_, ?_⟩⟩
  · refine ⟨hf, by show 1 ≤ m - 1; omega, ?_⟩
    intro h
    have h' : m - 1 = 1 := by simpa using h
    exact hmf (by omega)
  · refine l02qu4_largeEvenRawDatumLegacy_linear (by omega) hcard _ ?_
    let θ : StatedSL m E ⧸ Subgroup.center (StatedSL m E) ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin m) E) :=
      l02qu4_statedSLCenterQuotEquivProjective.trans
        (CFSG.StandardType.TypeA.recipeEquiv m E).symm
    have hnab : ∃ a b : StatedSL m E ⧸ Subgroup.center (StatedSL m E), a * b ≠ b * a :=
      exists_mul_ne_mul_centerQuot_of_perfect hperf inferInstance
    refine ⟨?_, ?_, θ, by simp [GGChevStTag], ?_⟩
    · exact θ.symm.isSimpleGroup_congr.mpr hsimp
    · exact nonabelian_of_mulEquiv θ hnab
    · intro ε _
      let A : GL (Fin m) E := ε⁻¹
      let φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin m) E)) :=
        (MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv m E)).symm
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut m E A)
      refine ⟨φ, CFSG.StandardType.NbrGraphLinear.symm_congr_conjAut_mem A, ?_⟩
      intro l l' hll'
      apply (CFSG.StandardType.TypeA.recipeEquiv m E).injective
      simp only [φ, MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [show CFSG.StandardType.TypeA.recipeEquiv m E
            (θ (QuotientGroup.mk l)) =
          l02qu4_statedSLCenterQuotEquivProjective (QuotientGroup.mk l) from rfl,
        show CFSG.StandardType.TypeA.recipeEquiv m E
            (θ (QuotientGroup.mk l')) =
          l02qu4_statedSLCenterQuotEquivProjective (QuotientGroup.mk l') from rfl]
      rw [l02qu4_statedSLCenterQuotEquivProjective_mk, l02qu4_statedSLCenterQuotEquivProjective_mk]
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
      rw [← l02qu4_specialLinearGroupEquivStatedSL_symm_slConjugation (A := A)
        (by simpa [A] using hll')]

private theorem l02qu4_isSolvable_statedSU_two_two {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = 2 ^ 2) : Group.IsSolvable ↥(StatedSU 2 2 E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (StatedSU 2 2 E) = 2 * (2 ^ 2 - 1) :=
    CFSG.RankThree.SubgroupLists.card_statedSU_two (K := E) (r := 2) (f := 1) (by
      rw [hE]; norm_num)
  exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
    (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [hcard]; norm_num)

private theorem l02qu4_isSolvable_statedSU_three_two {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = 2 ^ 2) : Group.IsSolvable ↥(StatedSU 3 2 E) := by
  have hcard' : Nat.card (StatedSU 3 (2 ^ 1) E) = 216 := by
    rw [CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two (F := E) (f := 1)
      (by rw [hE]; norm_num)]
    norm_num
  have hcard : Nat.card (StatedSU 3 2 E) = 216 := by simpa using hcard'
  exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
    (p := 2) (q := 3) (a := 3) (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [hcard]; norm_num)

private theorem l02qu4_mul_comm_GL_fin_of_le_one {F : Type} [Field F] {d : ℕ} (hd : d ≤ 1)
    (a b : GL (Fin d) F) : a * b = b * a := by
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
  · apply Units.ext
    exact Subsingleton.elim _ _
  · apply Units.ext
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, mul_comm]

private theorem l02qu4_mul_comm_statedSU_of_le_one {F : Type} [Field F] {k q : ℕ} (hk : k ≤ 1)
    (a b : StatedSU k q F) : a * b = b * a := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact l02qu4_mul_comm_GL_fin_of_le_one hk _ _

private theorem l02qu4_mul_comm_statedSL_of_le_one {F : Type} [Field F] {a : ℕ} (ha : a ≤ 1)
    (x y : StatedSL a F) : x * y = y * x := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact l02qu4_mul_comm_GL_fin_of_le_one ha _ _

private theorem l02qu4_two_le_of_isQuasisimple_statedSU {L : Type} [Field L] {k q : ℕ}
    (h : CFSG.Assembly.IsQuasisimple (StatedSU k q L)) : 2 ≤ k := by
  by_contra hk
  have hk1 : k ≤ 1 := by omega
  exact CFSG.LieType.SemisimpleCentralizers.Held.hct_not_isQuasisimple_of_comm
    (fun a b => l02qu4_mul_comm_statedSU_of_le_one hk1 a b) h

private theorem l02qu4_two_le_of_isQuasisimple_statedSL {L : Type} [Field L] {a : ℕ}
    (h : CFSG.Assembly.IsQuasisimple (StatedSL a L)) : 2 ≤ a := by
  by_contra ha
  have ha1 : a ≤ 1 := by omega
  exact CFSG.LieType.SemisimpleCentralizers.Held.hct_not_isQuasisimple_of_comm
    (fun x y => l02qu4_mul_comm_statedSL_of_le_one ha1 x y) h

private theorem l02qu4_exists_statedClassicalModel_statedSU_two {Q f : ℕ} {E : Type} [Field E]
    [Finite E] [CharP E 2] (hQ : Q = 2 ^ f) (hE : Nat.card E = Q ^ 2) (hf : 2 ≤ f) :
    CFSG.Open.StatedClassicalModel
      (↥(StatedSU 2 Q E) ⧸ Subgroup.center ↥(StatedSU 2 Q E)) .PSL 2 2 f := by
  subst Q
  let F := CFSG.LieType.Steinberg.fixedSubfield E 2 f
  have hcardF : Nat.card F = 2 ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield (p := 2) (f := f) (F := E) (by simpa using hE)
  have h4 : 4 ≤ 2 ^ f := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hf
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 2 2 f := by
    refine ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩
    · intro hpair
      have h2 : 2 ^ f = 2 := (Prod.mk.inj hpair).2
      omega
    · intro hpair
      have h3 : 2 ^ f = 3 := (Prod.mk.inj hpair).2
      omega
  obtain ⟨e1⟩ := SURepair.nonempty_sl2_mulEquiv_unitarySU_two (K := E) (f := f) hE
  let eSU : ↥(StatedSU 2 (2 ^ f) E) ≃* ↥(CFSG.Open.StatedSL 2 F) :=
    e1.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)
  let eZ : ↥(StatedSU 2 (2 ^ f) E) ⧸ Subgroup.center ↥(StatedSU 2 (2 ^ f) E) ≃*
      ↥(CFSG.Open.StatedSL 2 F) ⧸ Subgroup.center ↥(CFSG.Open.StatedSL 2 F) :=
    QuotientGroup.congr _ _ eSU (Subgroup.map_center_eq eSU)
  let e3 : ↥(CFSG.Open.StatedSL 2 F) ⧸ Subgroup.center ↥(CFSG.Open.StatedSL 2 F) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F) :=
    QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq 2)
  exact ⟨hadm, F, inferInstance, inferInstance, hcardF, ⟨eZ.trans e3⟩⟩

private theorem l02qu4_largeEvenMarking_heldSU {a Q : ℕ} {M : Type} [Field M] [Finite M]
    [CharP M 2] {τ : M ≃+* M} {hτ : ∀ x, τ (τ x) = x}
    (hτQ : ∀ x, τ x = x ^ Q) (hcard : Nat.card M = Q ^ 2)
    (hQpow : ∃ k, Q = 2 ^ k) (hqs : CFSG.Assembly.IsQuasisimple ↥(Held.heldSU a M τ hτ)) :
    LargeEvenMarking ↥(Held.heldSU a M τ hτ) (fun _ _ _ _ _ _ => True) := by
  have hSUeq : Held.heldSU a M τ hτ = StatedSU a Q M :=
    CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU (Q := Q) hτQ
  rw [hSUeq] at hqs ⊢
  obtain ⟨k, rfl⟩ := hQpow
  by_cases ha : 3 ≤ a
  · have h32 : (a, 2 ^ k) ≠ (3, 2) := by
      intro h
      have ha3 : a = 3 := congrArg Prod.fst h
      have hQ2 : 2 ^ k = 2 := congrArg Prod.snd h
      subst ha3
      rw [hQ2] at hqs
      have hcard3 : Nat.card M = 2 ^ 2 := by rw [hQ2] at hcard; exact hcard
      have hsolv : Group.IsSolvable ↥(StatedSU 3 2 M) :=
        l02qu4_isSolvable_statedSU_three_two hcard3
      haveI : Group.IsPerfect ↥(StatedSU 3 2 M) := ⟨hqs.1⟩
      haveI : Nontrivial (↥(StatedSU 3 2 M) ⧸ Subgroup.center ↥(StatedSU 3 2 M)) :=
        hqs.2.toNontrivial
      haveI : Nontrivial ↥(StatedSU 3 2 M) :=
        (QuotientGroup.mk'_surjective (Subgroup.center ↥(StatedSU 3 2 M))).nontrivial
      exact Group.IsPerfect.not_isSolvable ↥(StatedSU 3 2 M) hsolv
    letI : Fintype M := Fintype.ofFinite M
    obtain ⟨f, hQf, hUF⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData M (q := 2 ^ k)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
    exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (l02qu4_largeEvenMarking_unitaryFull_statedSU (Q := 2 ^ k) hUF hQf hcard ha h32)
  · have h2a : 2 ≤ a := l02qu4_two_le_of_isQuasisimple_statedSU hqs
    have ha2 : a = 2 := by omega
    subst ha2
    letI : Fintype M := Fintype.ofFinite M
    have hk2 : 2 ≤ k := by
      by_contra hk
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with hk0 | hk1
      · have h1 : 1 < Nat.card M := Finite.one_lt_card
        rw [hk0, pow_zero] at hcard
        rw [hcard] at h1
        norm_num at h1
      · have hcard2 : Nat.card M = 2 ^ 2 := by
          rw [hk1, pow_one] at hcard; exact hcard
        rw [hk1, pow_one] at hqs
        have hsolv : Group.IsSolvable ↥(StatedSU 2 2 M) :=
          l02qu4_isSolvable_statedSU_two_two hcard2
        haveI : Group.IsPerfect ↥(StatedSU 2 2 M) := ⟨hqs.1⟩
        haveI : Nontrivial (↥(StatedSU 2 2 M) ⧸ Subgroup.center ↥(StatedSU 2 2 M)) :=
          hqs.2.toNontrivial
        haveI : Nontrivial ↥(StatedSU 2 2 M) :=
          (QuotientGroup.mk'_surjective (Subgroup.center ↥(StatedSU 2 2 M))).nontrivial
        exact Group.IsPerfect.not_isSolvable ↥(StatedSU 2 2 M) hsolv
    exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (largeEvenMarking_inn_of_statedClassicalModel hqs
        (l02qu4_exists_statedClassicalModel_statedSU_two (Q := 2 ^ k) rfl hcard hk2))

private theorem l02qu4_component_group_iso {Q n : ℕ} {L : Type} [Field L] [Finite L]
    {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q)
    (hL : Nat.card L = Q ^ 2)
    (s : GL (Fin n) L) (hs : s ∈ Held.heldGU n L τ hτ) (hord : (orderOf s : L) ≠ 0)
    {C : Subgroup (GL (Fin n) L)}
    (hC : IsComponentOf C (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓
      Held.heldGU n L τ hτ)) :
    (∃ (a d : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ' : M ≃+* M)
      (hτ' : ∀ x, τ' (τ' x) = x),
      (∀ x : M, τ' x = x ^ (Q ^ d)) ∧ Nat.card M = (Q ^ d) ^ 2 ∧
        Nonempty (↥C ≃* ↥(Held.heldSU a M τ' hτ'))) ∨
    (∃ (b e : ℕ) (M : Type) (_ : Field M) (_ : Finite M), Nat.card M = Q ^ (2 * e) ∧
        Nonempty (↥C ≃* ↥(StatedSL b M))) := by
  have hCo : CFSG.Open.IsComponentOf C (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓
      Held.heldGU n L τ hτ) := isComponentOf_iff_open.mp hC
  obtain ⟨r, H, hgrp, hfinH, hblk, ⟨ε⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.centralizerDecomposition_gu
      hτ hτQ hL s hs hord
  letI : ∀ k, Group (H k) := hgrp
  letI : ∀ k, Finite (H k) := hfinH
  have hbl : ∀ k, ∃ S : Subgroup (H k), (∀ x y : H k, ⁅x, y⁆ ∈ S) ∧
      (∀ X : Subgroup S, CFSG.Open.IsComponentOf X ⊤ → X = ⊤) ∧ S.Normal ∧
      ((∃ (a d : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ : M ≃+* M)
          (hτ : ∀ x, τ (τ x) = x), (∀ x : M, τ x = x ^ (Q ^ d)) ∧
            Nat.card M = (Q ^ d) ^ 2 ∧ Nonempty (S ≃* Held.heldSU a M τ hτ)) ∨
        (∃ (b e : ℕ) (M : Type) (_ : Field M) (_ : Finite M), Nat.card M = Q ^ (2 * e) ∧
          Nonempty (S ≃* StatedSL b M))) := fun k =>
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_blockSub_sized
      CFSG.LieType.SemisimpleCentralizers.Held.SUComponentsTrivial_holds
      CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds (hblk k)
  choose S hS hSt hSn hty using hbl
  let C0 : Subgroup (GL (Fin n) L) :=
    Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ Held.heldGU n L τ hτ
  let ψ : (∀ k, H k) →* GL (Fin n) L := C0.subtype.comp ε.symm.toMonoidHom
  have hψinj : Function.Injective ψ := fun x y h => ε.symm.injective (Subtype.ext h)
  have hrange : ψ.range = C0 := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact (ε.symm w).2
    · intro hx
      refine ⟨ε ⟨x, hx⟩, ?_⟩
      simp [ψ]
  have hCle : C ≤ ψ.range := by rw [hrange]; exact hCo.1
  have hCmap : (C.comap ψ).map ψ = C := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hCle]
  have hC'top : CFSG.Open.IsComponentOf (C.comap ψ) ⊤ := by
    apply CFSG.LieType.SemisimpleCentralizers.Held.isComponentOf_of_map_injective ψ hψinj
    rw [hCmap, ← MonoidHom.range_eq_map, hrange]
    exact hCo
  obtain ⟨k, hk⟩ :=
    CFSG.LieType.SemisimpleCentralizers.Held.component_eq_factor_image S hS hSt hC'top
  have hCeq : C = ((S k).map (MonoidHom.mulSingle H k)).map ψ := by
    rw [← hk, hCmap]
  have hms := CFSG.LieType.SemisimpleCentralizers.Held.mulSingle_injective' (H := H) k
  have e1 : ↥C ≃* ↥(S k) :=
    (MulEquiv.subgroupCongr hCeq).trans
      (((Subgroup.equivMapOfInjective _ ψ hψinj).symm).trans
        ((Subgroup.equivMapOfInjective (S k) (MonoidHom.mulSingle H k) hms).symm))
  rcases hty k with huni | hlin
  · obtain ⟨a, d, M, hMF, hMfin, τM, hτM, hτMQ, hcardM, ⟨eS⟩⟩ := huni
    exact Or.inl ⟨a, d, M, hMF, hMfin, τM, hτM, hτMQ, hcardM, ⟨e1.trans eS⟩⟩
  · obtain ⟨b, ee, M, hMF, hMfin, hcardM, ⟨eS⟩⟩ := hlin
    exact Or.inr ⟨b, ee, M, hMF, hMfin, hcardM, ⟨e1.trans eS⟩⟩

private theorem l02qu4_component_marking {Q n : ℕ} {L : Type} [Field L] [Finite L]
    {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q)
    (hL : Nat.card L = Q ^ 2) (hQpow : ∃ k, Q = 2 ^ k)
    (s : GL (Fin n) L) (hs : s ∈ Held.heldGU n L τ hτ) (hord : (orderOf s : L) ≠ 0)
    {C : Subgroup (GL (Fin n) L)}
    (hC : IsComponentOf C (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓
      Held.heldGU n L τ hτ)) :
    LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) := by
  rcases l02qu4_component_group_iso hτ hτQ hL s hs hord hC with huni | hlin
  · obtain ⟨a, d, M, hMF, hMfin, τ', hτ', hτ'Q, hcardM, ⟨e⟩⟩ := huni
    letI : Field M := hMF
    letI : Finite M := hMfin
    obtain ⟨k, hk⟩ := hQpow
    have hcard2 : Nat.card M = 2 ^ (k * d * 2) := by
      calc Nat.card M = (Q ^ d) ^ 2 := hcardM
        _ = ((2 ^ k) ^ d) ^ 2 := by rw [hk]
        _ = 2 ^ (k * d * 2) := by rw [pow_mul, pow_mul]
    letI : Fintype M := Fintype.ofFinite M
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP M 2 := charP_of_card_eq_prime_pow (p := 2) (f := k * d * 2)
      (by rw [← Nat.card_eq_fintype_card, hcard2])
    haveI : Group.IsPerfect ↥C := ⟨hC.2.2.1⟩
    have hperfH : commutator ↥(Held.heldSU a M τ' hτ') = ⊤ := by
      have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥C)) (H₂ := ⊤) e.toMonoidHom
      rw [show (⁅(⊤ : Subgroup ↥C), ⊤⁆) = ⊤ from hC.2.2.1,
        Subgroup.map_top_of_surjective _ e.surjective] at h
      exact h.symm
    have hsimpleH : IsSimpleGroup
        (↥(Held.heldSU a M τ' hτ') ⧸ Subgroup.center ↥(Held.heldSU a M τ' hτ')) := by
      let eZ := QuotientGroup.congr (Subgroup.center ↥C)
        (Subgroup.center ↥(Held.heldSU a M τ' hτ')) e (Subgroup.map_center_eq e)
      exact eZ.isSimpleGroup_congr.mp hC.2.2.2
    have hqsH : CFSG.Assembly.IsQuasisimple ↥(Held.heldSU a M τ' hτ') := ⟨hperfH, hsimpleH⟩
    have hheld : LargeEvenMarking ↥(Held.heldSU a M τ' hτ') (fun _ _ _ _ _ _ => True) :=
      l02qu4_largeEvenMarking_heldSU hτ'Q hcardM ⟨k * d, by rw [hk, pow_mul]⟩ hqsH
    exact largeEvenMarking_congr e (fun _ _ _ _ _ _ _ => trivial) hheld
  · obtain ⟨b, ee, M, hMF, hMfin, hcardM, ⟨e⟩⟩ := hlin
    letI : Field M := hMF
    letI : Finite M := hMfin
    obtain ⟨k, hk⟩ := hQpow
    have hcard2 : Nat.card M = 2 ^ (k * (2 * ee)) := by
      calc Nat.card M = Q ^ (2 * ee) := hcardM
        _ = (2 ^ k) ^ (2 * ee) := by rw [hk]
        _ = 2 ^ (k * (2 * ee)) := by rw [← pow_mul]
    haveI : Group.IsPerfect ↥C := ⟨hC.2.2.1⟩
    have hperfH : commutator ↥(StatedSL b M) = ⊤ := by
      have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥C)) (H₂ := ⊤) e.toMonoidHom
      rw [show (⁅(⊤ : Subgroup ↥C), ⊤⁆) = ⊤ from hC.2.2.1,
        Subgroup.map_top_of_surjective _ e.surjective] at h
      exact h.symm
    have hsimpleH : IsSimpleGroup
        (↥(StatedSL b M) ⧸ Subgroup.center ↥(StatedSL b M)) := by
      let eZ := QuotientGroup.congr (Subgroup.center ↥C)
        (Subgroup.center ↥(StatedSL b M)) e (Subgroup.map_center_eq e)
      exact eZ.isSimpleGroup_congr.mp hC.2.2.2
    have hqsH : CFSG.Assembly.IsQuasisimple ↥(StatedSL b M) := ⟨hperfH, hsimpleH⟩
    have hm : 2 ≤ b := l02qu4_two_le_of_isQuasisimple_statedSL hqsH
    have hf : 1 ≤ k * (2 * ee) := by
      by_contra hf
      have h0 : k * (2 * ee) = 0 := by omega
      rw [h0, pow_zero] at hcard2
      have h1 : 1 < Nat.card M := Finite.one_lt_card
      omega
    have hmf : b = 2 → 2 ≤ k * (2 * ee) := by
      intro _
      have h : k * (2 * ee) = 2 * (k * ee) := by ring
      have hf' : 1 ≤ 2 * (k * ee) := by rwa [h] at hf
      omega
    have hlinmark := l02qu4_largeEvenMarking_statedSL_linear (m := b) (f := k * (2 * ee))
      hcard2 hperfH hsimpleH hm hf hmf
    exact largeEvenMarking_congr e (fun _ _ _ _ _ _ _ => trivial)
      (largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) hlinmark)

private theorem l02qu4_largeEvenMarking_of_central_surj_norm {A B : Type*} [Group A] [Group B]
    (g : A →* B) (hg : Function.Surjective g) (hker : g.ker ≤ Subgroup.center A)
    (hA : commutator A = ⊤) {Q0 : Prop} (hQ0 : Q0)
    {ιA ιB : Type*} (PA : ιA → Prop) (PB : ιB → Prop) (tag : LargeEvenLabel → Prop)
    (relA : ιA → A → A → Prop) (relB : ιB → B → B → Prop)
    (hrel : ∀ j, PB j → ∃ i, PA i ∧ ∀ b b' : B, relB j b b' →
      ∃ a a' : A, g a = b ∧ g a' = b' ∧ relA i a a')
    (h : LargeEvenMarking A (fun lab _ _ I _ θ => tag lab ∧ ∀ i, PA i → ∃ φ ∈ I,
      LargeEvenInduces θ (relA i) φ)) :
    LargeEvenMarking B (fun lab _ _ I _ θ => Q0 ∧ tag lab ∧ ∀ j, PB j → ∃ φ ∈ I,
      LargeEvenInduces θ (relB j) φ) := by
  have hperf : Group.IsPerfect A := ⟨hA⟩
  haveI : Group.IsPerfect A := hperf
  have hB : commutator B = ⊤ := (Group.IsPerfect.ofSurjective hg).commutator_eq_top
  have hcomap : (Subgroup.center B).comap g = Subgroup.center A :=
    CFSG.LocalCores.comap_center_eq_of_perfect hperf g hg hker
  let φ : A →* B ⧸ Subgroup.center B := (QuotientGroup.mk' (Subgroup.center B)).comp g
  have hφsurj : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective (Subgroup.center B)).comp hg
  have hφker : Subgroup.center A = φ.ker := by
    dsimp only [φ]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  let e : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
    QuotientGroup.liftEquiv (Subgroup.center A) (φ := φ) hφsurj hφker
  have he : ∀ a : A, e (QuotientGroup.mk a) = QuotientGroup.mk (g a) :=
    fun a => QuotientGroup.liftEquiv_mk (Subgroup.center A) (φ := φ) hφsurj hφker a
  obtain ⟨-, lab, hlab, hraw⟩ := h
  refine ⟨hB, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, htag, hforall⟩
  refine ⟨hs, hna, e.symm.trans θ, hQ0, htag, ?_⟩
  intro j hj
  obtain ⟨i, hi, hrelji⟩ := hrel j hj
  obtain ⟨φA, hφAI, hφA⟩ := hforall i hi
  refine ⟨φA, hφAI, ?_⟩
  intro b b' hbb'
  obtain ⟨a, a', hga, hga', hraa'⟩ := hrelji b b' hbb'
  have hb : e.symm (QuotientGroup.mk b) = QuotientGroup.mk a := by
    rw [← hga, ← he a, MulEquiv.symm_apply_apply]
  have hb' : e.symm (QuotientGroup.mk b') = QuotientGroup.mk a' := by
    rw [← hga', ← he a', MulEquiv.symm_apply_apply]
  calc φA ((e.symm.trans θ) (QuotientGroup.mk b))
      = φA (θ (e.symm (QuotientGroup.mk b))) := by rw [MulEquiv.trans_apply]
    _ = φA (θ (QuotientGroup.mk a)) := by rw [hb]
    _ = θ (QuotientGroup.mk a') := hφA a a' hraa'
    _ = θ (e.symm (QuotientGroup.mk b')) := by rw [hb']
    _ = (e.symm.trans θ) (QuotientGroup.mk b') := by rw [MulEquiv.trans_apply]

theorem q1TorUni_marking {d m : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 2)
    (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ m)
    (s : GL (Fin d) K) (hs : s ∈ Held.heldGU d K τ hτ) (hso : Odd (orderOf s))
    (C : Subgroup (GL (Fin d) K))
    (hC : CFSG.Assembly.IsComponentOf C
      (Subgroup.centralizer ({s} : Set (GL (Fin d) K)) ⊓ Held.heldGU d K τ hτ))
    (hCSU : C ≤ LargeEvenSUGroup (Fin d) K (2 ^ m))
    (J₀ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m))))
    (hJ₀ : J₀ = (C.subgroupOf (LargeEvenSUGroup (Fin d) K (2 ^ m))).map
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m)))) :
    CFSG.StandardType.LargeEvenMarking J₀ (fun _ _ _ IJ _ θJ =>
      ∀ (k : GL (Fin d) K)
        (hkN : k ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K))),
        k ∈ Held.heldGU d K τ hτ → k * s = s * k →
        (∀ j ∈ J₀, TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨k, hkN⟩ j ∈ J₀) ∧
        ∃ φ ∈ IJ, LargeEvenInduces θJ
          (fun j j' : ↥J₀ =>
            TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨k, hkN⟩ (j : _) = (j' : _)) φ) := by
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := m * 2) (by
    rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have hord : (orderOf s : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    exact (Nat.not_even_iff_odd.mpr hso) (even_iff_two_dvd.mpr h)
  have hQpow : ∃ k, 2 ^ m = 2 ^ k := ⟨m, rfl⟩
  have hE0 := ggE0Concl_centralizer_heldGU (N := d) (Q := 2 ^ m) (L := K)
    hτ hτQ hK s hs hso hC
  have hm0 : LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) :=
    l02qu4_component_marking hτ hτQ hK hQpow s hs hord hC
  have hmC := hE0.2 hm0
  let SU := LargeEvenSUGroup (Fin d) K (2 ^ m)
  let E0 : Subgroup (GL (Fin d) K) :=
    Subgroup.centralizer ({s} : Set (GL (Fin d) K)) ⊓ Held.heldGU d K τ hτ
  let g : ↥C →* ↥J₀ :=
    { toFun := fun c => ⟨LargeEvenProjMk SU ⟨(c : GL (Fin d) K), hCSU c.2⟩, by
        rw [hJ₀]
        exact Subgroup.mem_map.mpr ⟨⟨(c : GL (Fin d) K), hCSU c.2⟩, by
          rw [Subgroup.mem_subgroupOf]; exact c.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        exact map_one (LargeEvenProjMk SU)
      map_mul' := fun c c' => by
        apply Subtype.ext
        change LargeEvenProjMk SU ⟨((c * c' : ↥C) : GL (Fin d) K), hCSU (c * c').2⟩ =
          LargeEvenProjMk SU ⟨(c : GL (Fin d) K), hCSU c.2⟩ *
            LargeEvenProjMk SU ⟨(c' : GL (Fin d) K), hCSU c'.2⟩
        rw [← map_mul]
        rfl }
  have hg : Function.Surjective g := by
    intro b
    have hb : (b : LargeEvenProj SU) ∈ (C.subgroupOf SU).map (LargeEvenProjMk SU) := by
      rw [← hJ₀]; exact b.2
    obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb
    have hcC : (c : GL (Fin d) K) ∈ C := by
      rwa [Subgroup.mem_subgroupOf] at hc
    refine ⟨⟨(c : GL (Fin d) K), hcC⟩, ?_⟩
    apply Subtype.ext
    change LargeEvenProjMk SU ⟨(c : GL (Fin d) K), hCSU hcC⟩ = (b : LargeEvenProj SU)
    rw [show (⟨(c : GL (Fin d) K), hCSU hcC⟩ : ↥SU) = c from Subtype.ext rfl, hcb]
  have hker : g.ker ≤ Subgroup.center ↥C := by
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    rw [Subgroup.mem_center_iff]
    intro x
    have hc1 : LargeEvenProjMk SU ⟨(c : GL (Fin d) K), hCSU c.2⟩ = 1 := by
      have h := congrArg (fun z : ↥J₀ => (z : LargeEvenProj SU)) hc
      change (g c : LargeEvenProj SU) = 1 at h
      change LargeEvenProjMk SU ⟨(c : GL (Fin d) K), hCSU c.2⟩ = 1 at h
      exact h
    have hcZ : (c : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K := by
      have hmem : ⟨(c : GL (Fin d) K), hCSU c.2⟩ ∈
          (LargeEvenScalars (Fin d) K).subgroupOf SU := by
        have hker' : (LargeEvenProjMk SU).ker = (LargeEvenScalars (Fin d) K).subgroupOf SU := by
          rw [LargeEvenProjMk, QuotientGroup.ker_mk']
        rw [← hker']
        exact MonoidHom.mem_ker.mpr hc1
      exact Subgroup.mem_subgroupOf.mp hmem
    obtain ⟨u, hu⟩ := (Matrix.GeneralLinearGroup.scalar (Fin d)).mem_range.mp (by
      rwa [largeEvenScalars_def] at hcZ)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu]
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.scalar_comm_gl u (x : GL (Fin d) K)).symm
  have hQ0 : ∀ (k : GL (Fin d) K)
      (hkN : k ∈ Subgroup.normalizer (SU : Set (GL (Fin d) K))),
      k ∈ Held.heldGU d K τ hτ → k * s = s * k → ∀ j ∈ J₀,
        TableB.projConj SU ⟨k, hkN⟩ j ∈ J₀ := by
    intro k hkN hkGU hcomm j hj
    rw [hJ₀] at hj
    obtain ⟨c, hc, hcj⟩ := Subgroup.mem_map.mp hj
    rw [← hcj, hJ₀]
    change TableB.projConj SU ⟨k, hkN⟩ (c : LargeEvenProj SU) ∈
      (C.subgroupOf SU).map (LargeEvenProjMk SU)
    rw [TableB.projConj_mk]
    have hcC : (c : GL (Fin d) K) ∈ C := by
      rwa [Subgroup.mem_subgroupOf] at hc
    have hkE0 : k ∈ E0 :=
      Subgroup.mem_inf.mpr ⟨by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hcomm.symm, hkGU⟩
    have hkc : k * (c : GL (Fin d) K) * k⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hE0.1 hkE0) (c : GL (Fin d) K)).1 hcC
    have hkcSU : k * (c : GL (Fin d) K) * k⁻¹ ∈ SU := by
      have := Subgroup.mem_normalizer_iff.mp hkN (c : GL (Fin d) K)
      exact this.1 c.2
    rw [show (SU.normalizerMonoidHom ⟨k, hkN⟩ c : ↥SU) =
        ⟨k * (c : GL (Fin d) K) * k⁻¹, hkcSU⟩ from Subtype.ext rfl]
    refine Subgroup.mem_map.mpr ⟨(⟨k * (c : GL (Fin d) K) * k⁻¹, hkcSU⟩ : ↥SU), ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]; exact hkc
    · rfl
  have hrel : ∀ A : Subgroup.normalizer (SU : Set (GL (Fin d) K)),
      ((A : GL (Fin d) K) ∈ Held.heldGU d K τ hτ ∧ (A : GL (Fin d) K) * s = s * (A : GL (Fin d) K)) →
      ∃ i, i ∈ E0 ∧ ∀ b b' : ↥J₀, TableB.projConj SU A (b : LargeEvenProj SU) = (b' : LargeEvenProj SU) →
        ∃ a a' : ↥C, g a = b ∧ g a' = b' ∧
          (a' : GL (Fin d) K) = i⁻¹ * (a : GL (Fin d) K) * i := by
    rintro A ⟨hAGU, hAcomm⟩
    have hAcent : (A : GL (Fin d) K) ∈
        Subgroup.centralizer ({s} : Set (GL (Fin d) K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hAcomm.symm
    have hAE0 : (A : GL (Fin d) K) ∈ E0 := Subgroup.mem_inf.mpr ⟨hAcent, hAGU⟩
    have hAinvE0 : (A : GL (Fin d) K)⁻¹ ∈ E0 :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.centralizer _).inv_mem hAE0.1,
        (Held.heldGU d K τ hτ).inv_mem hAE0.2⟩
    refine ⟨(A : GL (Fin d) K)⁻¹, hAinvE0, ?_⟩
    intro b b' hbb'
    obtain ⟨a₀, ha₀⟩ := hg b
    have hmemC : (A : GL (Fin d) K) * (a₀ : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hE0.1 hAE0) (a₀ : GL (Fin d) K)).1 a₀.2
    refine ⟨a₀, ⟨(A : GL (Fin d) K) * (a₀ : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹, hmemC⟩,
      ha₀, ?_, ?_⟩
    · apply Subtype.ext
      have hstep : (g ⟨(A : GL (Fin d) K) * (a₀ : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹,
            hmemC⟩ : LargeEvenProj SU) = TableB.projConj SU A (b : LargeEvenProj SU) := by
        change LargeEvenProjMk SU
          ⟨(A : GL (Fin d) K) * (a₀ : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹, hCSU hmemC⟩
          = TableB.projConj SU A (b : LargeEvenProj SU)
        rw [← ha₀]
        have hga₀ : (g a₀ : LargeEvenProj SU) =
            ((⟨(a₀ : GL (Fin d) K), hCSU a₀.2⟩ : ↥SU) : LargeEvenProj SU) := rfl
        rw [hga₀, TableB.projConj_mk]
        apply congrArg (fun z : ↥SU => (z : LargeEvenProj SU))
        apply Subtype.ext
        show (A : GL (Fin d) K) * (a₀ : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹ =
          (SU.normalizerMonoidHom A ⟨(a₀ : GL (Fin d) K), hCSU a₀.2⟩ : GL (Fin d) K)
        rfl
      rw [hstep, hbb']
    · show (A : GL (Fin d) K) * (a₀ : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹ =
        ((A : GL (Fin d) K)⁻¹)⁻¹ * (a₀ : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹
      rw [inv_inv]
  have hfinal := l02qu4_largeEvenMarking_of_central_surj_norm g hg hker hC.2.2.1 hQ0
    (fun ε : GL (Fin d) K => ε ∈ E0)
    (fun A : Subgroup.normalizer (SU : Set (GL (Fin d) K)) =>
      (A : GL (Fin d) K) ∈ Held.heldGU d K τ hτ ∧
        (A : GL (Fin d) K) * s = s * (A : GL (Fin d) K))
    (fun lab => GGChevStTag lab)
    (fun ε l l' => (l' : GL (Fin d) K) = ε⁻¹ * l * ε)
    (fun A j j' => TableB.projConj SU A (j : LargeEvenProj SU) = (j' : LargeEvenProj SU))
    hrel hmC
  refine largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ?_) hfinal
  obtain ⟨hQ0', htag, hind⟩ := hP
  intro k hkN hkGU hcomm
  refine ⟨hQ0' k hkN hkGU hcomm, ?_⟩
  obtain ⟨φ, hφI, hφ⟩ := hind ⟨k, hkN⟩ ⟨hkGU, hcomm⟩
  exact ⟨φ, hφI, hφ⟩

end CFSG.StandardType
