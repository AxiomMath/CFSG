module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalCubeData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterDiag
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterTorus
import CFSG.HardMathSupport.Dickson.Bal207.UniFrame
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Assembly.QuasithinDefs
import CFSG.Foundations
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.StandardType.FF81.CatQ1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out

private theorem cq1_isDiag_mul_comm {n : ℕ} {F : Type} [Field F]
    {A B : Matrix (Fin n) (Fin n) F} (hA : A.IsDiag) (hB : B.IsDiag) : A * B = B * A := by
  rw [← IsDiag.diagonal_diag hA, ← IsDiag.diagonal_diag hB,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mul_comm]

private theorem cq1_conj_comm {G : Type*} [Group G] (a p t : G)
    (h : (p⁻¹ * a * p) * t = t * (p⁻¹ * a * p)) :
    a * (p * t * p⁻¹) = (p * t * p⁻¹) * a := by
  have h1 : a * (p * t * p⁻¹) = p * ((p⁻¹ * a * p) * t) * p⁻¹ := by group
  have h2 : (p * t * p⁻¹) * a = p * (t * (p⁻¹ * a * p)) * p⁻¹ := by group
  rw [h1, h2, h]

private theorem cq1_bar_mul_self_of_pow_three {ℓ f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (h3 : 3 ∣ ℓ ^ f + 1) {d : Fˣ} (hd : d ^ 3 = 1) :
    h.bar (d : F) * (d : F) = 1 := by
  have h3u : (d : F) ^ 3 = 1 := by
    have hh := congrArg (Units.val) hd
    simpa using hh
  obtain ⟨m, hm⟩ := h3
  calc h.bar (d : F) * (d : F)
      = (d : F) ^ (ℓ ^ f) * (d : F) := by rw [h.bar_apply]
    _ = (d : F) ^ (ℓ ^ f + 1) := by rw [pow_succ]
    _ = (d : F) ^ (3 * m) := by rw [hm]
    _ = ((d : F) ^ 3) ^ m := by rw [pow_mul]
    _ = 1 := by rw [h3u, one_pow]

private theorem cq1_diagGL_mem_gramSU {ℓ f n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (h3 : 3 ∣ ℓ ^ f + 1) (d : Fin n → Fˣ)
    (hd : ∀ j, d j ^ 3 = 1) (hdet : ∏ j, d j = 1) :
    diagGL d ∈ gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  rw [mem_gramSU]
  refine ⟨?_, ?_⟩
  · rw [coe_diagGL, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose]
    change ((diagonal fun m => h.bar (d m : F)) * 1 * diagonal fun j => (d j : F)) = 1
    rw [Matrix.mul_one, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    exact cq1_bar_mul_self_of_pow_three h h3 (hd j)
  · rw [coe_diagGL, Matrix.det_diagonal, ← Units.coe_prod, hdet, Units.val_one]

theorem exists_isDiag_torus_primeFormP {ℓ f n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (hn : 5 ≤ n) (h3 : 3 ∣ ℓ ^ f + 1) :
    ∃ T : (Fin 3 → Multiplicative (ZMod 3)) →*
        gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F),
      Function.Injective ((QuotientGroup.mk' (normOneScalars h
        (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) n)).comp T) ∧
      ∀ x, Matrix.IsDiag (((T x : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) := by
  have hcard : Nat.card F = (ℓ ^ f) ^ 2 := by
    rw [h.card, show 2 * f = f * 2 by omega, pow_mul]
  have hpK : 3 ∣ Nat.card F - 1 := by
    rw [hcard]
    have h2 : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      have := Nat.sq_sub_sq (ℓ ^ f) 1
      rwa [one_pow] at this
    rw [h2]
    exact h3.mul_right _
  obtain ⟨κ, hκp, hκdet, hκinj⟩ :=
    @exists_diag_torus F _ h.finite 3 n Nat.prime_three hn hpK
  let T : (Fin 3 → Multiplicative (ZMod 3)) →*
      gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
    (diagGL.comp κ).codRestrict _
      (fun x => cq1_diagGL_mem_gramSU h h3 (κ x) (hκp x) (hκdet x))
  refine ⟨T, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have hmem : T x ∈ normOneScalars h
        (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) n :=
      (QuotientGroup.eq_one_iff _).1 hx
    obtain ⟨c, -, -, hc⟩ := (mem_normOneScalars).1 hmem
    refine hκinj x c fun j => ?_
    have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin n) F =>
      (g : Matrix (Fin n) (Fin n) F)) hc) j) j
    change ((diagGL (κ x) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j =
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j at h1
    rw [coe_diagGL, diagonal_apply_eq, GeneralLinearGroup.coe_scalar, scalar_apply,
      diagonal_apply_eq] at h1
    exact Units.ext h1
  · intro x
    change ((diagGL (κ x) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag
    rw [coe_diagGL]
    exact isDiag_diagonal _

theorem exists_torus_primeFormP {ℓ f n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (hn : 5 ≤ n) (h3 : 3 ∣ ℓ ^ f + 1) :
    ∃ T : (Fin 3 → Multiplicative (ZMod 3)) →*
        primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), Function.Injective T := by
  obtain ⟨T, hT, -⟩ := exists_isDiag_torus_primeFormP h hn h3
  exact ⟨(QuotientGroup.mk' _).comp T, hT⟩

theorem exists_unitary_isDiag_conj_of_pow_three {ℓ f n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (h3 : 3 ∣ ℓ ^ f + 1) {A : Matrix (Fin n) (Fin n) F}
    (hA : (A.map h.bar)ᵀ * A = 1) (hA3 : A ^ 3 = 1) :
    ∃ P : GL (Fin n) F, ((P : Matrix (Fin n) (Fin n) F).map h.bar)ᵀ * P = 1 ∧
      Matrix.IsDiag (((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A *
        (P : Matrix (Fin n) (Fin n) F)) := by
  have h1 : A * A ^ 2 = 1 := (pow_succ' A 2).symm.trans hA3
  have h2 : A ^ 2 * A = 1 := (pow_succ A 2).symm.trans hA3
  let A' : GL (Fin n) F := ⟨A, A ^ 2, h1, h2⟩
  have hA'coe : (A' : Matrix (Fin n) (Fin n) F) = A := rfl
  have hEU : ∀ x ∈ ({A'} : Set (GL (Fin n) F)),
      x ∈ primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [mem_primeFormUnitary, hA'coe]
    simpa using hA
  have hEc : ∀ x ∈ ({A'} : Set (GL (Fin n) F)), ∀ y ∈ ({A'} : Set (GL (Fin n) F)),
      x * y = y * x := by
    intro x hx y hy
    rw [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy; rfl
  have hE3 : ∀ x ∈ ({A'} : Set (GL (Fin n) F)), x ^ 3 = 1 := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hA'coe, Units.val_one]
    exact hA3
  obtain ⟨P, hP, hPd⟩ := CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.exists_unitary_isDiag_conj
    h h3 ({A'} : Set (GL (Fin n) F)) hEU hEc hE3
  refine ⟨P, ?_, ?_⟩
  · have h := hP
    rw [mem_primeFormUnitary] at h
    simpa using h
  · have hcoe : ((P⁻¹ * A' * P : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A *
          (P : Matrix (Fin n) (Fin n) F) := by
      simp only [Units.val_mul, hA'coe, Matrix.mul_assoc]
    exact hcoe ▸ (hPd A' (Set.mem_singleton A'))

private theorem cq1_exists_smul_unit_unitary_of_primeForm {ℓ f n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (h3 : 3 ∣ ℓ ^ f + 1) (hn : 0 < n)
    {A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)} {b : F} (hb : b ≠ 0)
    (hA : ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ 3 =
      (b ^ 3) • (1 : Matrix (Fin n) (Fin n) F)) :
    ∃ Amat : Matrix (Fin n) (Fin n) F,
      Amat = b⁻¹ • ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ∧
        (Amat.map h.bar)ᵀ * Amat = 1 ∧ Amat ^ 3 = 1 := by
  have hAun : (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map h.bar)ᵀ *
      ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    have h := A.2
    rw [mem_primeFormUnitary] at h
    simpa using h
  have hc : h.bar (b ^ 3) * b ^ 3 = 1 :=
    bar_mul_self_eq_one_of_pow_three_eq_smul h.bar hn hAun hA
  have hb1 : h.bar b * b = 1 := bar_mul_self_eq_one_of_cube h h3 hc
  have hbarb : h.bar b = b⁻¹ := eq_inv_of_mul_eq_one_left hb1
  have hbarb' : h.bar b⁻¹ = b := by rw [map_inv₀, hbarb, inv_inv]
  refine ⟨b⁻¹ • ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), rfl, ?_, ?_⟩
  · rw [Matrix.map_smul' h.bar b⁻¹ _ (fun a₁ a₂ => map_mul h.bar a₁ a₂),
      Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hAun, smul_smul,
      show h.bar b⁻¹ * b⁻¹ = 1 by rw [hbarb', mul_inv_cancel₀ hb], one_smul]
  · rw [smul_pow, hA, smul_smul,
      show (b⁻¹) ^ 3 * b ^ 3 = 1 by rw [← mul_pow, inv_mul_cancel₀ hb, one_pow], one_smul]

private theorem cq1_conjHom_fixes_conj_torus {ℓ f n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (C : Matrix (Fin n) (Fin n) F)
    {A : primeFormUnitary h C} {P : GL (Fin n) F} (hPmem : P ∈ primeFormUnitary h C)
    {T₀ : (Fin 3 → Multiplicative (ZMod 3)) →* gramSU h C}
    (hT₀diag : ∀ x, Matrix.IsDiag ((T₀ x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (hA1diag : ((P⁻¹ * (A : GL (Fin n) F) * P : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F).IsDiag) :
    ∀ x, primeFormConjHom h C A
      (primeFormConjSU h C ⟨P, hPmem⟩ (T₀ x) : primeFormP h C) =
        (primeFormConjSU h C ⟨P, hPmem⟩ (T₀ x) : primeFormP h C) := by
  intro x
  let Ag : GL (Fin n) F := (A : GL (Fin n) F)
  let Tg : GL (Fin n) F := (T₀ x : GL (Fin n) F)
  let A₁ : GL (Fin n) F := P⁻¹ * Ag * P
  let S : gramSU h C := primeFormConjSU h C ⟨P, hPmem⟩ (T₀ x)
  have hScoe : (S : GL (Fin n) F) = P * Tg * P⁻¹ := rfl
  have hA1T : A₁ * Tg = Tg * A₁ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact cq1_isDiag_mul_comm hA1diag (hT₀diag x)
  have hAS : Ag * (S : GL (Fin n) F) = (S : GL (Fin n) F) * Ag := by
    rw [hScoe]
    exact cq1_conj_comm Ag P Tg hA1T
  have hconj : Ag * (S : GL (Fin n) F) * Ag⁻¹ = (S : GL (Fin n) F) := by
    rw [hAS, mul_assoc, mul_inv_cancel, mul_one]
  rw [primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  exact hconj

private theorem cq1_conj_isDiag_of_smul {n : ℕ} {F : Type} [Field F]
    {A : GL (Fin n) F} {b : F} {P : GL (Fin n) F} {D : Matrix (Fin n) (Fin n) F}
    (hA : (A : Matrix (Fin n) (Fin n) F) = b • D)
    (hD : (((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * D *
      (P : Matrix (Fin n) (Fin n) F)).IsDiag) :
    ((P⁻¹ * A * P : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag := by
  have heq : ((P⁻¹ * A * P : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      b • (((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * D *
        (P : Matrix (Fin n) (Fin n) F)) := by
    rw [Units.val_mul, Units.val_mul, hA, Matrix.mul_smul, Matrix.smul_mul]
  rw [heq]
  exact IsDiag.smul b hD

theorem exists_torus_fixed_of_cube_unitary {ℓ f n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (hn : 5 ≤ n) (h3 : 3 ∣ ℓ ^ f + 1)
    {A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)} {b : F} (hb : b ≠ 0)
    (hA : ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ 3 =
      (b ^ 3) • (1 : Matrix (Fin n) (Fin n) F)) :
    ∃ T : (Fin 3 → Multiplicative (ZMod 3)) →*
        primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F),
      Function.Injective T ∧
        ∀ x, primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A (T x) = T x := by
  let C : Matrix (Fin n) (Fin n) F := ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  obtain ⟨Amat, hAmat, hA'un, hA'3⟩ :=
    cq1_exists_smul_unit_unitary_of_primeForm h h3 (by omega) hb hA
  obtain ⟨P, hPU, hPd⟩ := exists_unitary_isDiag_conj_of_pow_three h h3 hA'un hA'3
  have hPmem : P ∈ primeFormUnitary h C := by
    rw [mem_primeFormUnitary]
    simpa [C] using hPU
  obtain ⟨T₀, hT₀inj, hT₀diag⟩ := exists_isDiag_torus_primeFormP h hn h3
  let PH : primeFormUnitary h C := ⟨P, hPmem⟩
  let T : (Fin 3 → Multiplicative (ZMod 3)) →* primeFormP h C :=
    (primeFormConjAut h C PH).toMonoidHom.comp
      ((QuotientGroup.mk' (normOneScalars h (gramSU h C) n)).comp T₀)
  have hbAm : ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = b • Amat := by
    rw [hAmat, smul_smul, mul_inv_cancel₀ hb, one_smul]
  refine ⟨T, ?_, ?_⟩
  · exact (primeFormConjAut h C PH).injective.comp hT₀inj
  · intro x
    have hTx : T x = (primeFormConjSU h C PH (T₀ x) : primeFormP h C) := by
      show primeFormConjAut h C PH ((T₀ x : gramSU h C) : primeFormP h C) = _
      rw [primeFormConjAut_mk]
    rw [hTx]
    exact cq1_conjHom_fixes_conj_torus h C hPmem hT₀diag
      (cq1_conj_isDiag_of_smul hbAm hPd) x

end CFSG.StandardType.FF81.CatQ1

end
