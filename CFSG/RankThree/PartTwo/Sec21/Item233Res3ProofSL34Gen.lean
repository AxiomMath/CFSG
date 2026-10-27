module

public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofSp44
public import CFSG.LinearAlgebra.LinearGroups.Generation
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFourCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.KF.R7Final
public import CFSG.RankThree.PartOne.KFOUT3.KtyD8
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx
public import CFSG.RankThree.PartOne.S12.InputsKF2
public import CFSG.RankThree.PartOne.S12.Sec1322Inputs
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Commute33
public import CFSG.RankThree.PartTwo.Sec21.Item223Gaps
public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofFour
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item233
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProof
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
public import CFSG.RankThree.PartTwo.Sec6.Item612
public import CFSG.Walter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Matrix
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.RankThree.PartTwo.Sec21.InnerDiagonal (F4 SL34 mem_inndiag_of_pow card_units_F4)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open CFSG.RankThree.PartTwo.Sec21.Tables (isBlockDiag_of_commute)

namespace Item233Res3Proof

local notation "M3" => Matrix (Fin 3) (Fin 3) F4

namespace SL34Gen

section Diag

theorem eq_diagonal_of {M : M3} (hM : ∀ i j, i ≠ j → M i j = 0) :
    M = diagonal fun i => M i i := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [diagonal_apply_eq]
  · rw [hM i j h, diagonal_apply_ne _ h]

theorem mul_comm_of_diag {M N : M3} (hM : ∀ i j, i ≠ j → M i j = 0)
    (hN : ∀ i j, i ≠ j → N i j = 0) : M * N = N * M := by
  rw [eq_diagonal_of hM, eq_diagonal_of hN, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem inv_offDiag {g : GL (Fin 3) F4} (hg : ∀ i j, i ≠ j → (g : M3) i j = 0) :
    ∀ i j, i ≠ j → ((g⁻¹ : GL (Fin 3) F4) : M3) i j = 0 := by
  set h := ((g⁻¹ : GL (Fin 3) F4) : M3) with hh
  have hgh : (g : M3) * h = 1 := by
    rw [hh, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hhg : h * (g : M3) = 1 := by
    rw [hh, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hgii : ∀ i, (g : M3) i i * h i i = 1 := by
    intro i
    have e := congrFun (congrFun hgh i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hg i k (Ne.symm hk),
      zero_mul]) (by simp), Matrix.one_apply_eq] at e
    exact e
  have hgi0 : ∀ i, (g : M3) i i ≠ 0 := fun i h0 => by
    have := hgii i
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  intro i j hij
  have e := congrFun (congrFun hhg i) j
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [hg k j hk, mul_zero])
    (by simp), Matrix.one_apply_ne hij] at e
  exact (mul_eq_zero.mp e).resolve_right (hgi0 j)

theorem conj_eq_of_mul_comm {g : GL (Fin 3) F4} {M : M3} (h : (g : M3) * M = M * g) :
    (g : M3) * M * ((g⁻¹ : GL (Fin 3) F4) : M3) = M := by
  rw [h, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

theorem mul_comm_of_conj_eq {g : GL (Fin 3) F4} {M : M3}
    (h : (g : M3) * M * ((g⁻¹ : GL (Fin 3) F4) : M3) = M) : (g : M3) * M = M * g := by
  calc (g : M3) * M = (g : M3) * M * (((g⁻¹ : GL (Fin 3) F4) : M3) * g) := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    _ = M * g := by rw [← mul_assoc, h]

theorem cube_eq_one {x : F4} (hx : x ≠ 0) : x ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := F4ˣ) (x := Units.mk0 x hx)
  rw [card_units_F4] at h
  have h' := congrArg Units.val h
  simpa using h'

theorem pow_three_of_diag {d : SL34} (hd : ∀ i j, i ≠ j → (d : M3) i j = 0) : d ^ 3 = 1 := by
  have hdet : (d : M3).det = 1 := d.2
  rw [eq_diagonal_of hd, det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : ∀ i, (d : M3) i i ≠ 0 := by
    intro i h
    have h' : (d : M3) 0 0 * (d : M3) 1 1 * (d : M3) 2 2 = 0 := by
      fin_cases i <;> simp_all
    rw [hdet] at h'
    exact one_ne_zero h'
  have hpow : (d : M3) ^ 3 = 1 := by
    rw [eq_diagonal_of hd, diagonal_pow, ← diagonal_one]
    congr 1
    funext i
    exact cube_eq_one (h0 i)
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  exact hpow

theorem slConjugation_diag {g : GL (Fin 3) F4} (hg : ∀ i j, i ≠ j → (g : M3) i j = 0)
    {d : SL34} (hd : ∀ i j, i ≠ j → (d : M3) i j = 0) : slConjugation 3 F4 g d = d := by
  apply Subtype.ext
  rw [slConjugation_matrix]
  exact conj_eq_of_mul_comm (mul_comm_of_diag hg hd)

theorem slConjugation_scalar {g : GL (Fin 3) F4} (hg : ∀ i j, i ≠ j → (g : M3) i j = 0)
    (h01 : (g : M3) 0 0 = (g : M3) 1 1) (h12 : (g : M3) 1 1 = (g : M3) 2 2) (x : SL34) :
    slConjugation 3 F4 g x = x := by
  apply Subtype.ext
  rw [slConjugation_matrix]
  apply conj_eq_of_mul_comm
  have hs : (g : M3) = diagonal fun _ => (g : M3) 0 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
      fin_cases i
      · rfl
      · exact h01.symm
      · exact (h01.trans h12).symm
    · rw [hg i j hij, diagonal_apply_ne _ hij]
  rw [hs]
  ext i j
  rw [diagonal_mul, mul_diagonal, mul_comm]

end Diag

section Root

@[expose] noncomputable def m12 (B : Matrix (Fin 2) (Fin 2) F4) : M3 :=
  !![1, 0, 0; 0, B 0 0, B 0 1; 0, B 1 0, B 1 1]

theorem det_m12 (B : Matrix (Fin 2) (Fin 2) F4) : (m12 B).det = B.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [m12]

theorem m12_mul (B C : Matrix (Fin 2) (Fin 2) F4) : m12 (B * C) = m12 B * m12 C := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m12, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem m12_one : m12 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m12]

@[expose] noncomputable def ι12 : SpecialLinearGroup (Fin 2) F4 →* SL34 where
  toFun B := ⟨m12 B, by rw [det_m12]; exact B.2⟩
  map_one' := Subtype.ext m12_one
  map_mul' B C := Subtype.ext (m12_mul _ _)

theorem ι12_injective : Function.Injective ι12 := by
  intro B C h
  have h' : m12 B = m12 C := congrArg Subtype.val h
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [m12] using congrFun₂ h' 1 1
  · simpa [m12] using congrFun₂ h' 1 2
  · simpa [m12] using congrFun₂ h' 2 1
  · simpa [m12] using congrFun₂ h' 2 2

theorem card_range_ι12 : Nat.card ι12.range = 60 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective ι12_injective).toEquiv]
  exact card_SL_two_F4

theorem mem_range_ι12 {x : SL34} (h00 : (x : M3) 0 0 = 1) (h01 : (x : M3) 0 1 = 0)
    (h02 : (x : M3) 0 2 = 0) (h10 : (x : M3) 1 0 = 0) (h20 : (x : M3) 2 0 = 0) :
    x ∈ ι12.range := by
  set B : Matrix (Fin 2) (Fin 2) F4 :=
    !![(x : M3) 1 1, (x : M3) 1 2; (x : M3) 2 1, (x : M3) 2 2] with hB
  have hx : (x : M3) = m12 B := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m12, hB, h00, h01, h02, h10, h20]
  have hdet : B.det = 1 := by rw [← det_m12, ← hx]; exact x.2
  exact ⟨⟨B, hdet⟩, Subtype.ext hx.symm⟩

@[expose] noncomputable def mat3 : SL34 →* M3 where
  toFun g := g
  map_one' := Matrix.SpecialLinearGroup.coe_one
  map_mul' := Matrix.SpecialLinearGroup.coe_mul

end Root

section Cycle

@[expose] noncomputable def cycM : M3 := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] noncomputable def cycM' : M3 := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] noncomputable def cyc : SL34 := ⟨cycM, by simp [cycM, Matrix.det_fin_three]⟩

@[expose] noncomputable def cyc' : SL34 := ⟨cycM', by simp [cycM', Matrix.det_fin_three]⟩

theorem cyc_inv : cyc⁻¹ = cyc' := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change cycM * cycM' = 1
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [cycM, cycM']

theorem cyc_conj_t12 (t : F4) :
    cyc * Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t * cyc⁻¹ =
      Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t := by
  rw [cyc_inv]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  change cycM * (1 + single 1 2 t) * cycM' = 1 + single 2 0 t
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [cycM, cycM']

theorem cyc_conj_t21 (t : F4) :
    cyc * Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t * cyc⁻¹ =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t := by
  rw [cyc_inv]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  change cycM * (1 + single 2 1 t) * cycM' = 1 + single 0 2 t
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [cycM, cycM']

theorem cycInv_conj_t12 (t : F4) :
    cyc⁻¹ * Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t * cyc =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t := by
  rw [cyc_inv]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  change cycM' * (1 + single 1 2 t) * cycM = 1 + single 0 1 t
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [cycM, cycM']

theorem cycInv_conj_t21 (t : F4) :
    cyc⁻¹ * Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t * cyc =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t := by
  rw [cyc_inv]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  change cycM' * (1 + single 2 1 t) * cycM = 1 + single 1 0 t
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [cycM, cycM']

theorem t12_mem (t : F4) :
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t ∈ ι12.range := by
  apply mem_range_ι12 <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe]

theorem t21_mem (t : F4) :
    Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t ∈ ι12.range := by
  apply mem_range_ι12 <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe]

theorem eq_top_of_ι12_cyc {S : Subgroup SL34} (h1 : ι12.range ≤ S) (h2 : cyc ∈ S) : S = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := F4),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, t, rfl⟩
  have h12 := fun t => h1 (t12_mem t)
  have h21 := fun t => h1 (t21_mem t)
  have hc' : cyc⁻¹ ∈ S := S.inv_mem h2
  have hcases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨
      (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h := S.mul_mem (S.mul_mem hc' (h12 t)) h2
    rwa [cycInv_conj_t12] at h
  · have h := S.mul_mem (S.mul_mem h2 (h21 t)) hc'
    rwa [cyc_conj_t21] at h
  · have h := S.mul_mem (S.mul_mem hc' (h21 t)) h2
    rwa [cycInv_conj_t21] at h
  · exact h12 t
  · have h := S.mul_mem (S.mul_mem h2 (h12 t)) hc'
    rwa [cyc_conj_t12] at h
  · exact h21 t

theorem cyc_mul_conj_offDiag {g : GL (Fin 3) F4} (hg : ∀ i j, i ≠ j → (g : M3) i j = 0) :
    ∀ i j, i ≠ j → ((cyc * slConjugation 3 F4 g cyc⁻¹ : SL34) : M3) i j = 0 := by
  have hh := inv_offDiag hg
  have g01 := hg 0 1 (by decide)
  have g02 := hg 0 2 (by decide)
  have g10 := hg 1 0 (by decide)
  have g12 := hg 1 2 (by decide)
  have g20 := hg 2 0 (by decide)
  have g21 := hg 2 1 (by decide)
  have h01 := hh 0 1 (by decide)
  have h02 := hh 0 2 (by decide)
  have h10 := hh 1 0 (by decide)
  have h12 := hh 1 2 (by decide)
  have h20 := hh 2 0 (by decide)
  have h21 := hh 2 1 (by decide)
  intro i j hij
  rw [Matrix.SpecialLinearGroup.coe_mul, slConjugation_matrix, cyc_inv]
  change (cycM * ((g : M3) * cycM' * ((g⁻¹ : GL (Fin 3) F4) : M3))) i j = 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | simp [cycM, cycM', g01, g02, g10, g12, g20, g21, h01, h02, h10, h12, h20, h21]

end Cycle

end SL34Gen

open SL34Lines SL34Gen

variable {G : Type} [Group G]

theorem mem_of_commute_of_max [Finite G] {A : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A) {x : G} (hx : x ^ 3 = 1)
    (hxA : ∀ a ∈ A, a * x = x * a) : x ∈ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hxn
  have h := (Sec5.isElemAbelian_sup_zpowers hAe hxn hx hxA).1
  have heq := hAmax _ h le_sup_left
  have hmem : x ∈ A ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rw [heq] at hmem
  exact hxn hmem

theorem exists_diag_model [Finite G] {A Z : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hAN : A ≤ Subgroup.normalizer (Z : Set G)) (eZ : Z ≃* SL34)
    {ρ : MulAut A} (hρZ : ρ ∈ starOf A Z) (hρ : IsReflectionOn ρ) :
    ∃ (e : Z ≃* SL34) (w : G) (hwZ : w ∈ Z), (∀ a : A, ((ρ a : A) : G) = w * a * w⁻¹) ∧
      ((e ⟨w, hwZ⟩ : SL34) : M3) 1 2 ≠ 0 ∧
      ∀ a ∈ A, ∃ g : GL (Fin 3) F4, (∀ i j, i ≠ j → (g : M3) i j = 0) ∧
        ∀ z : Z, ((e.symm (slConjugation 3 F4 g (e z)) : Z) : G) = a * z * a⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  obtain ⟨⟨w, hwN⟩, hwZ, hρw⟩ := hρZ
  have hwZ' : w ∈ Z := Subgroup.mem_subgroupOf.mp hwZ
  have hρapp : ∀ a : A, ((ρ a : A) : G) = w * a * w⁻¹ := fun a => by rw [← hρw]; rfl
  have hρ2 := apply_apply_of_orderOf_eq_two hρ.1
  have hc3 : Nat.card (commOf ρ) = 3 := hρ.2
  have : Nontrivial (commOf ρ) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc3]; norm_num)
  obtain ⟨u0, hu0⟩ := exists_ne (1 : commOf ρ)
  have hu0' : (u0 : A) ≠ 1 := fun h => hu0 (Subtype.ext h)
  have hu0Z : ((u0 : A) : G) ∈ Z := by
    have hmem : (u0 : A) ∈ (commHom hAc ρ).range := (range_commHom hAc ρ).symm ▸ u0.2
    obtain ⟨a, ha⟩ := hmem
    rw [← ha, commHom_apply, Subgroup.coe_mul, Subgroup.coe_inv, hρapp]
    have haN : (a : G)⁻¹ ∈ Subgroup.normalizer (Z : Set G) := Subgroup.inv_mem _ (hAN a.2)
    have h1 : (a : G)⁻¹ * w * ((a : G)⁻¹)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp haN w).mp hwZ'
    have e : (a : G)⁻¹ * (w * a * w⁻¹) = ((a : G)⁻¹ * w * ((a : G)⁻¹)⁻¹) * w⁻¹ := by group
    rw [e]
    exact Z.mul_mem h1 (Z.inv_mem hwZ')
  set u : Z := ⟨((u0 : A) : G), hu0Z⟩ with hu
  have hρu : ρ (u0 : A) = (u0 : A)⁻¹ := inv_of_mem_commOf hAc hρ2 u0.2
  have hu3 : u ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 _ (u0 : A).2)
  have hcommC : ∀ y : A, y ∈ commOf ρ → (y : G) ∈ Subgroup.centralizer (Z : Set G) → y = 1 := by
    intro y hy hyC
    have hfix : ρ y = y := by
      apply Subtype.ext
      rw [hρapp, Subgroup.mem_centralizer_iff.mp hyC w hwZ', mul_inv_cancel_right]
    have hinv : ρ y = y⁻¹ := inv_of_mem_commOf hAc hρ2 hy
    have hy2 : y * y = 1 := by
      calc y * y = y * ρ y := by rw [hfix]
        _ = 1 := by rw [hinv, mul_inv_cancel]
    calc y = y ^ 3 * (y * y)⁻¹ := by group
      _ = 1 := by rw [hA3, hy2, inv_one, one_mul]
  have hucen : u ∉ Subgroup.center Z := by
    intro h
    apply hu0'
    refine hcommC _ u0.2 (Subgroup.mem_centralizer_iff.mpr fun z hz => ?_)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h ⟨z, hz⟩)
  obtain ⟨ω, hωo⟩ := exists_prime_orderOf_dvd_card' (G := F4ˣ) 3 (by rw [card_units_F4])
  have hω3 : ω ^ 3 = 1 := by rw [← hωo]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hωo
    norm_num at hωo
  obtain ⟨e, he⟩ := exists_equiv_x0 eZ hu3 hucen hω3 hω1
  set τ : Subgroup.normalizer (Z : Set G) →* MulAut SL34 :=
    (MulAut.congr e).toMonoidHom.comp Z.normalizerMonoidHom with hτ
  have hτapp : ∀ (b : Subgroup.normalizer (Z : Set G)) (z : Z),
      τ b (e z) = e (Z.normalizerMonoidHom b z) := by
    intro b z
    simp [hτ, MulAut.congr_apply]
  set W : SL34 := e ⟨w, hwZ'⟩ with hW
  have hWx : W * x0 ω * W⁻¹ = x0' ω := by
    rw [← x0_inv, ← he, hW, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    apply Subtype.ext
    change w * ((u0 : A) : G) * w⁻¹ = (((u0 : A) : G))⁻¹
    rw [← hρapp, hρu, Subgroup.coe_inv]
  have hWx' : W * x0 ω = x0' ω * W := by
    rw [← hWx]
    group
  have hWpat := pattern_of hω3 hω1 (W := (W : M3)) (by
    have h := congrArg (fun y : SL34 => (y : M3)) hWx'
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using h)
  have hdiag : ∀ a (ha : a ∈ A), ∃ g : GL (Fin 3) F4, τ ⟨a, hAN ha⟩ = slConjugation 3 F4 g ∧
      ∀ i j, i ≠ j → (g : M3) i j = 0 := by
    intro a ha
    have h3 : τ ⟨a, hAN ha⟩ ^ 3 ^ 1 = 1 := by
      rw [pow_one, ← map_pow]
      have : (⟨a, hAN ha⟩ : Subgroup.normalizer (Z : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hAe.2 a ha)
      rw [this, map_one]
    obtain ⟨g, hg⟩ := mem_inndiag_of_pow _ ⟨1, h3⟩
    refine ⟨g, hg.symm, ?_⟩
    have hfix : τ ⟨a, hAN ha⟩ (x0 ω) = x0 ω := by
      rw [← he, hτapp]
      congr 1
      apply Subtype.ext
      change a * ((u0 : A) : G) * a⁻¹ = ((u0 : A) : G)
      have hcom : a * ((u0 : A) : G) = ((u0 : A) : G) * a :=
        congrArg Subtype.val (hAc ⟨a, ha⟩ (u0 : A))
      rw [hcom, mul_inv_cancel_right]
    rw [← hg] at hfix
    have hm := congrArg (fun y : SL34 => (y : M3)) hfix
    simp only [slConjugation_matrix] at hm
    apply offDiag_eq_zero_of_commute hω3 hω1
    exact mul_comm_of_conj_eq hm
  refine ⟨e, w, hwZ', hρapp, ?_, ?_⟩
  · obtain ⟨h01, h02, h10, h11, h20, h22⟩ := hWpat
    intro h12
    have hdet : (W : M3).det = 1 := W.2
    rw [Matrix.det_fin_three, h01, h02, h10, h11, h20, h22, h12] at hdet
    simp at hdet
  · intro a ha
    obtain ⟨g, hg, hgd⟩ := hdiag a ha
    refine ⟨g, hgd, fun z => ?_⟩
    rw [← hg, hτapp, MulEquiv.symm_apply_apply]
    rfl

end Item233Res3Proof

open Item233Res3Proof Item233Res3Proof.SL34Gen

local notation "M3" => Matrix (Fin 3) (Fin 3) F4

theorem item233ZRootGenSL34_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (hKW : KOfWellDefinedAll) : Item233ZRootGenSL34 := by
  intro G _ _ A E U c L hpair _ hA27 φ hφ Z hZ hKZ _ _ heK hZsl
  classical
  obtain ⟨eK⟩ := heK
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hK := hKW G A E U c L hpair
  obtain ⟨z, hzA, hz1, hZz⟩ := mem_thetaComponentFamily_iff.mp hZ.1
  have hAN : A ≤ Subgroup.normalizer (Z : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hzA hz1
      Z hZz
  have hC3 := Item221ResProof.card_inf_centralizer_eq_three h66 hpair.standing hpair.mem_S hZ
  obtain ⟨eZ⟩ := hZsl
  have hφZ : φ ∈ starOf A Z := starOf_mono A hKZ (mem_starOf_kOf h222 hpair hK hφ)
  obtain ⟨e, w, hwZ, hφw, hW12, hact⟩ := exists_diag_model hAe hAN eZ hφZ hφ.1
  have hdiagA : ∀ d : SL34, (∀ i j, i ≠ j → (d : M3) i j = 0) → ((e.symm d : Z) : G) ∈ A := by
    intro d hd
    refine mem_of_commute_of_max hAe hAF.2.1 ?_ fun a ha => ?_
    · rw [← Subgroup.coe_pow, ← map_pow, pow_three_of_diag hd, map_one, Subgroup.coe_one]
    · obtain ⟨g, hgd, hg⟩ := hact a ha
      have h1 := hg (e.symm d)
      rw [MulEquiv.apply_symm_apply, slConjugation_diag hgd hd] at h1
      calc a * ((e.symm d : Z) : G) = a * ((e.symm d : Z) : G) * a⁻¹ * a := by group
        _ = ((e.symm d : Z) : G) * a := by rw [← h1]
  have hcycN : ((e.symm cyc : Z) : G) ∈ Subgroup.normalizer (A : Set G) := by
    apply mem_normalizer_of_forall_conj_mem
    intro a ha
    obtain ⟨g, hgd, hg⟩ := hact a ha
    have h1 := hg (e.symm cyc⁻¹)
    rw [MulEquiv.apply_symm_apply] at h1
    have hy := hdiagA _ (cyc_mul_conj_offDiag hgd)
    rw [map_mul, Subgroup.coe_mul, h1, map_inv, Subgroup.coe_inv] at hy
    have e1 : ((e.symm cyc : Z) : G) * a * ((e.symm cyc : Z) : G)⁻¹ =
        ((e.symm cyc : Z) : G) * (a * ((e.symm cyc : Z) : G)⁻¹ * a⁻¹) * a := by group
    rw [e1]
    exact A.mul_mem hy ha
  have hB9 := Item228ResProof.card_fixedInG_eq_nine hAc hA27 hφ.1
  obtain ⟨a₁, ha₁F, ha₁C⟩ : ∃ a₁ ∈ fixedInG A φ, a₁ ∉ Subgroup.centralizer (Z : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : fixedInG A φ ≤ A ⊓ Subgroup.centralizer (Z : Set G) :=
      fun x hx => ⟨Subgroup.map_subtype_le _ hx, hcon x hx⟩
    have h := Subgroup.card_le_of_le hle
    rw [hB9, hC3] at h
    norm_num at h
  obtain ⟨b, hbfix, rfl⟩ := ha₁F
  have hbφ : φ b = b := (mem_fixedSubgroupOf φ b).mp hbfix
  have hbw : (b : G) * w * (b : G)⁻¹ = w := by
    have h := hφw b
    rw [hbφ] at h
    calc (b : G) * w * (b : G)⁻¹ = (w * b * w⁻¹) * w * (b : G)⁻¹ := by rw [← h]
      _ = w := by group
  obtain ⟨g, hgd, hg⟩ := hact b b.2
  have hgW : slConjugation 3 F4 g (e ⟨w, hwZ⟩) = e ⟨w, hwZ⟩ := by
    apply e.symm.injective
    apply Subtype.ext
    rw [hg ⟨w, hwZ⟩, MulEquiv.symm_apply_apply]
    exact hbw
  have hgW' := congrArg (fun y : SL34 => (y : M3)) hgW
  simp only [slConjugation_matrix] at hgW'
  have hcomW := mul_comm_of_conj_eq hgW'
  rw [eq_diagonal_of hgd] at hcomW
  have h12 : (g : M3) 1 1 = (g : M3) 2 2 := by
    by_contra hne
    exact hW12 (isBlockDiag_of_commute hcomW.symm 1 2 hne)
  have h01 : (g : M3) 0 0 ≠ (g : M3) 1 1 := by
    intro h01
    apply ha₁C
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hg ⟨x, hx⟩
    rw [slConjugation_scalar hgd h01 h12, MulEquiv.symm_apply_apply] at h1
    change x = (b : G) * x * (b : G)⁻¹ at h1
    change x * (b : G) = (b : G) * x
    calc x * (b : G) = (b : G) * x * (b : G)⁻¹ * b := by rw [← h1]
      _ = b * x := by group
  have h02 : (g : M3) 0 0 ≠ (g : M3) 2 2 := by
    rw [← h12]
    exact h01
  have hKC : kOf A φ ≤ Subgroup.centralizer (fixedInG A φ : Set G) :=
    (kOf_le_kZero hK hφ).trans (kZero_le_centralizer A φ)
  have hbF : (b : G) ∈ fixedInG A φ := ⟨b, hbfix, rfl⟩
  set K' : Subgroup SL34 := ((kOf A φ).subgroupOf Z).map e.toMonoidHom with hK'
  have eK' : K' ≃* projSL 2 (GaloisField 2 2) :=
    (Subgroup.equivMapOfInjective _ _ e.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hKZ).trans eK)
  have hK'p : Group.IsPerfect K' := isPerfect_of_mulEquiv_projSL (le_refl 2) eK'
  have hK'60 : Nat.card K' = 60 := by
    rw [Nat.card_congr eK'.toEquiv, card_projSL_two 2 (by norm_num)]
    norm_num
  have hblk : ∀ x ∈ K', ∀ i j, (g : M3) i i ≠ (g : M3) j j → (x : M3) i j = 0 := by
    rintro _ ⟨k, hk, rfl⟩ i j hij
    have hkK : (k : G) ∈ kOf A φ := Subgroup.mem_subgroupOf.mp hk
    have hkb : (b : G) * k * (b : G)⁻¹ = k := by
      have h := Subgroup.mem_centralizer_iff.mp (hKC hkK) (b : G) hbF
      rw [h, mul_inv_cancel_right]
    have h2 : slConjugation 3 F4 g (e k) = e k := by
      apply e.symm.injective
      apply Subtype.ext
      rw [hg k, MulEquiv.symm_apply_apply]
      exact hkb
    have h3 := congrArg (fun y : SL34 => (y : M3)) h2
    simp only [slConjugation_matrix] at h3
    have h4 := mul_comm_of_conj_eq h3
    rw [eq_diagonal_of hgd] at h4
    exact isBlockDiag_of_commute h4.symm i j hij
  have h00 := entry_eq_one_of_isPerfect mat3 hK'p 0 fun x hx l hl => by
    fin_cases l
    · exact absurd rfl hl
    · exact hblk x hx 0 1 h01
    · exact hblk x hx 0 2 h02
  have hle : K' ≤ ι12.range := fun x hx => mem_range_ι12 (h00 x hx) (hblk x hx 0 1 h01)
    (hblk x hx 0 2 h02) (hblk x hx 1 0 (Ne.symm h01)) (hblk x hx 2 0 (Ne.symm h02))
  have hKeq : K' = ι12.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_range_ι12, hK'60])
  set RHS := (Z ⊓ Subgroup.normalizer (A : Set G)) ⊔
    ⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ with hRHS
  have hKR : kOf A φ ≤ RHS := le_trans (le_iSup_of_le φ (le_iSup_of_le hφ
    (le_iSup (fun _ : φ ∈ starOf A Z => kOf A φ) hφZ))) le_sup_right
  set S0 : Subgroup SL34 := RHS.comap (Z.subtype.comp e.symm.toMonoidHom) with hS0
  have hS0top : S0 = ⊤ := by
    apply eq_top_of_ι12_cyc
    · rw [← hKeq]
      rintro _ ⟨k, hk, rfl⟩
      change ((e.symm (e k) : Z) : G) ∈ RHS
      rw [MulEquiv.symm_apply_apply]
      exact hKR (Subgroup.mem_subgroupOf.mp hk)
    · change ((e.symm cyc : Z) : G) ∈ RHS
      exact Subgroup.mem_sup_left ⟨(e.symm cyc).2, hcycN⟩
  intro x hx
  have h : e ⟨x, hx⟩ ∈ S0 := by
    rw [hS0top]
    exact Subgroup.mem_top _
  change ((e.symm (e ⟨x, hx⟩) : Z) : G) ∈ RHS at h
  rwa [MulEquiv.symm_apply_apply] at h

end CFSG.RankThree.PartTwo.Sec21
