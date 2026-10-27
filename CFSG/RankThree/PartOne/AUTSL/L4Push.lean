module

public import CFSG.RankThree.PartOne.AUTSL.PushShared
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.RankThree.PartOne.AUTSL.L4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

@[expose] def cornerM (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, X 0 0, X 0 1; 0, 1, X 1 0, X 1 1; 0, 0, 1, 0; 0, 0, 0, 1]

theorem cornerM_zero : cornerM (0 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cornerM]

theorem cornerM_add (X Y : Matrix (Fin 2) (Fin 2) K) :
    cornerM X * cornerM Y = cornerM (X + Y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cornerM, Matrix.mul_apply, Fin.sum_univ_four, add_comm]

theorem det_cornerM (X : Matrix (Fin 2) (Fin 2) K) : (cornerM X).det = 1 := by
  have h : (cornerM X).BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [cornerM] at hij ⊢
  rw [Matrix.det_of_isUpperTriangular h]
  simp [cornerM, Fin.prod_univ_four]

@[expose] def corner (X : Matrix (Fin 2) (Fin 2) K) : SpecialLinearGroup (Fin 4) K :=
  ⟨cornerM X, det_cornerM X⟩

theorem coe_corner (X : Matrix (Fin 2) (Fin 2) K) :
    ((corner X : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = cornerM X := rfl

theorem coe_corner_mul (X Y : Matrix (Fin 2) (Fin 2) K) :
    ((corner X * corner Y : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      cornerM (X + Y) := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact cornerM_add X Y

theorem corner_add (X Y : Matrix (Fin 2) (Fin 2) K) : corner X * corner Y = corner (X + Y) :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by rw [coe_corner_mul]; rfl

@[expose] def cornerHom (K : Type) [Field K] : Multiplicative (Matrix (Fin 2) (Fin 2) K) →*
    SpecialLinearGroup (Fin 4) K where
  toFun X := corner (Multiplicative.toAdd X)
  map_one' := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    show cornerM (0 : Matrix (Fin 2) (Fin 2) K) i j = (1 : Matrix (Fin 4) (Fin 4) K) i j
    rw [cornerM_zero]
  map_mul' X Y := (corner_add _ _).symm

theorem cornerHom_injective : Function.Injective (cornerHom K) := by
  intro X Y h
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) h
  simp only [cornerHom, MonoidHom.coe_mk, OneHom.coe_mk, coe_corner] at h1
  apply Multiplicative.toAdd.injective
  ext i j
  have := congrFun₂ h1 (Fin.castAdd 2 i) (Fin.natAdd 2 j)
  fin_cases i <;> fin_cases j <;> simpa [cornerM] using this


abbrev Uge (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 4) K) :=
  LinearFlag.unitriangular 4 K

@[expose] def Vge (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 4) K) :=
  (cornerHom K).range

theorem mem_Vge {g : SpecialLinearGroup (Fin 4) K} :
    g ∈ Vge K ↔ ∃ X : Matrix (Fin 2) (Fin 2) K, g = corner X :=
  ⟨fun ⟨X, hX⟩ => ⟨Multiplicative.toAdd X, hX.symm⟩,
    fun ⟨X, hX⟩ => ⟨Multiplicative.ofAdd X, hX.symm⟩⟩

theorem corner_mem_Vge (X : Matrix (Fin 2) (Fin 2) K) : corner X ∈ Vge K := mem_Vge.2 ⟨X, rfl⟩

theorem mem_Uge_iff {g : SpecialLinearGroup (Fin 4) K} :
    g ∈ Uge K ↔ ((g : Matrix (Fin 4) (Fin 4) K) 1 0 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 2 0 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 2 1 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 3 0 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 3 1 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 3 2 = 0) ∧
      (g : Matrix (Fin 4) (Fin 4) K) 0 0 = 1 ∧ (g : Matrix (Fin 4) (Fin 4) K) 1 1 = 1 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 2 2 = 1 ∧ (g : Matrix (Fin 4) (Fin 4) K) 3 3 = 1 := by
  rw [LinearFlag.mem_unitriangular]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1 1 0 (by decide), h1 2 0 (by decide), h1 2 1 (by decide), h1 3 0 (by decide),
      h1 3 1 (by decide), h1 3 2 (by decide)⟩, h2 0, h2 1, h2 2, h2 3⟩
  · rintro ⟨⟨a, b, c, d, e, f⟩, h0, h1, h2, h3⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> assumption
    · fin_cases i <;> assumption

theorem Vge_le_Uge : Vge K ≤ Uge K := by
  rintro g hg
  obtain ⟨X, rfl⟩ := mem_Vge.1 hg
  rw [mem_Uge_iff]
  simp [coe_corner, cornerM]


@[simp] theorem cornerM_00 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 0 0 = 1 := rfl
@[simp] theorem cornerM_01 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 0 1 = 0 := rfl
@[simp] theorem cornerM_02 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 0 2 = X 0 0 := rfl
@[simp] theorem cornerM_03 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 0 3 = X 0 1 := rfl
@[simp] theorem cornerM_10 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 1 0 = 0 := rfl
@[simp] theorem cornerM_11 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 1 1 = 1 := rfl
@[simp] theorem cornerM_12 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 1 2 = X 1 0 := rfl
@[simp] theorem cornerM_13 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 1 3 = X 1 1 := rfl
@[simp] theorem cornerM_20 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 2 0 = 0 := rfl
@[simp] theorem cornerM_21 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 2 1 = 0 := rfl
@[simp] theorem cornerM_22 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 2 2 = 1 := rfl
@[simp] theorem cornerM_23 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 2 3 = 0 := rfl
@[simp] theorem cornerM_30 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 3 0 = 0 := rfl
@[simp] theorem cornerM_31 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 3 1 = 0 := rfl
@[simp] theorem cornerM_32 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 3 2 = 0 := rfl
@[simp] theorem cornerM_33 (X : Matrix (Fin 2) (Fin 2) K) : cornerM X 3 3 = 1 := rfl

theorem coe_mul_apply (g h : SpecialLinearGroup (Fin 4) K) (i j : Fin 4) :
    ((g * h : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j =
      ∑ k, (g : Matrix (Fin 4) (Fin 4) K) i k * (h : Matrix (Fin 4) (Fin 4) K) k j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]

local macro "l4simp" : tactic =>
  `(tactic| simp only [coe_mul_apply, Fin.sum_univ_four, coe_corner, cornerM_00, cornerM_01,
    cornerM_02, cornerM_03, cornerM_10, cornerM_11, cornerM_12, cornerM_13, cornerM_20, cornerM_21,
    cornerM_22, cornerM_23, cornerM_30, cornerM_31, cornerM_32, cornerM_33, Fin.zero_eta,
    Fin.mk_one, Fin.reduceFinMk, Fin.isValue])

local macro "l4simp_at " hs:(ppSpace colGt ident)+ : tactic =>
  `(tactic| simp only [coe_mul_apply, Fin.sum_univ_four, coe_corner, cornerM_00, cornerM_01,
    cornerM_02, cornerM_03, cornerM_10, cornerM_11, cornerM_12, cornerM_13, cornerM_20, cornerM_21,
    cornerM_22, cornerM_23, cornerM_30, cornerM_31, cornerM_32, cornerM_33, Fin.zero_eta,
    Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at $hs*)

theorem mul_corner_eq_iff {u : SpecialLinearGroup (Fin 4) K} (hu : u ∈ Uge K)
    (X : Matrix (Fin 2) (Fin 2) K) :
    u * corner X = corner X * u ↔
      ((u : Matrix (Fin 4) (Fin 4) K) 0 1 * X 1 0 = 0 ∧
        (u : Matrix (Fin 4) (Fin 4) K) 2 3 * X 1 0 = 0 ∧
        (u : Matrix (Fin 4) (Fin 4) K) 0 1 * X 1 1 =
          (u : Matrix (Fin 4) (Fin 4) K) 2 3 * X 0 0) := by
  obtain ⟨⟨h10, h20, h21, h30, h31, h32⟩, h00, h11, h22, h33⟩ := mem_Uge_iff.1 hu
  constructor
  · intro h
    have e02 := congrArg (fun g : SpecialLinearGroup (Fin 4) K =>
      (g : Matrix (Fin 4) (Fin 4) K) 0 2) h
    have e03 := congrArg (fun g : SpecialLinearGroup (Fin 4) K =>
      (g : Matrix (Fin 4) (Fin 4) K) 0 3) h
    have e13 := congrArg (fun g : SpecialLinearGroup (Fin 4) K =>
      (g : Matrix (Fin 4) (Fin 4) K) 1 3) h
    l4simp_at e02 e03 e13
    simp only [h00, h10, h11, h22, h32, h33] at e02 e03 e13
    refine ⟨by linear_combination e02, by linear_combination -e13, ?_⟩
    linear_combination e03
  · rintro ⟨e1, e2, e3⟩
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> l4simp <;>
      simp only [h00, h10, h11, h20, h21, h22, h30, h31, h32, h33] <;>
      first | ring1 | linear_combination e1 | linear_combination -e1 | linear_combination e2 |
        linear_combination -e2 | linear_combination e3

theorem Vge_comm {x y : SpecialLinearGroup (Fin 4) K} (hx : x ∈ Vge K) (hy : y ∈ Vge K) :
    x * y = y * x := by
  obtain ⟨X, rfl⟩ := mem_Vge.1 hx
  obtain ⟨Y, rfl⟩ := mem_Vge.1 hy
  rw [corner_add, corner_add, add_comm]

theorem corner_zero : corner (0 : Matrix (Fin 2) (Fin 2) K) = 1 :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    show cornerM (0 : Matrix (Fin 2) (Fin 2) K) i j = (1 : Matrix (Fin 4) (Fin 4) K) i j
    rw [cornerM_zero]

theorem Vge_sq [CharP K 2] {x : SpecialLinearGroup (Fin 4) K} (hx : x ∈ Vge K) : x ^ 2 = 1 := by
  obtain ⟨X, rfl⟩ := mem_Vge.1 hx
  have h : X + X = 0 := by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  rw [pow_two, corner_add, h, corner_zero]

theorem card_Vge [Finite K] : Nat.card (Vge K) = Nat.card K ^ 4 := by
  have h1 : Nat.card (Vge K) = Nat.card (Multiplicative (Matrix (Fin 2) (Fin 2) K)) :=
    Nat.card_range_of_injective (cornerHom_injective (K := K))
  rw [h1]
  change Nat.card (Fin 2 → Fin 2 → K) = _
  rw [Nat.card_fun, Nat.card_fun]
  simp [← pow_mul]

theorem mem_Vge_iff {u : SpecialLinearGroup (Fin 4) K} (hu : u ∈ Uge K) :
    u ∈ Vge K ↔ ((u : Matrix (Fin 4) (Fin 4) K) 0 1 = 0 ∧
      (u : Matrix (Fin 4) (Fin 4) K) 2 3 = 0) := by
  obtain ⟨⟨h10, h20, h21, h30, h31, h32⟩, h00, h11, h22, h33⟩ := mem_Uge_iff.1 hu
  constructor
  · intro h
    obtain ⟨X, rfl⟩ := mem_Vge.1 h
    simp [coe_corner]
  · rintro ⟨h01, h23⟩
    refine mem_Vge.2 ⟨!![(u : Matrix (Fin 4) (Fin 4) K) 0 2, (u : Matrix (Fin 4) (Fin 4) K) 0 3;
      (u : Matrix (Fin 4) (Fin 4) K) 1 2, (u : Matrix (Fin 4) (Fin 4) K) 1 3], ?_⟩
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [coe_corner, h00, h01, h10, h11, h20, h21, h22, h23, h30,
      h31, h32, h33]

@[expose] def piHom (K : Type) [Field K] : Uge K →* Multiplicative (K × K) where
  toFun u := Multiplicative.ofAdd
    (((u : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 1,
      ((u : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 3)
  map_one' := by
    show Multiplicative.ofAdd _ = 1
    simp
  map_mul' u v := by
    obtain ⟨⟨-, hu20, hu21, -, -, -⟩, hu00, -, hu22, -⟩ := mem_Uge_iff.1 u.2
    obtain ⟨⟨-, -, hv21, -, hv31, -⟩, -, hv11, -, hv33⟩ := mem_Uge_iff.1 v.2
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add]
    congr 1
    simp only [Subgroup.coe_mul, coe_mul_apply, Fin.sum_univ_four, hu00, hu20, hu21, hu22, hv11,
      hv21, hv31, hv33]
    ext <;> simp <;> ring

theorem centralizer_Uge_Vge {u : SpecialLinearGroup (Fin 4) K} (hu : u ∈ Uge K)
    (h : ∀ v ∈ Vge K, v * u = u * v) : u ∈ Vge K := by
  have h1 := h (corner !![0, 0; 1, 0]) (corner_mem_Vge _)
  have h2 := (mul_corner_eq_iff hu !![0, 0; 1, 0]).1 h1.symm
  simp at h2
  exact (mem_Vge_iff hu).2 ⟨h2.1, h2.2⟩

section Bound

variable [Finite K]

theorem inner_bound {F : Subgroup (SpecialLinearGroup (Fin 4) K)} (hF : F ≤ Uge K)
    (hFV : ¬ F ≤ Vge K) :
    (F ⊓ Vge K).relIndex F *
      Nat.card ↥(Vge K ⊓ Subgroup.centralizer (F : Set (SpecialLinearGroup (Fin 4) K))) ≤
        Nat.card K ^ 3 := by
  classical
  set φ : ↥F →* Multiplicative (K × K) := (piHom K).comp (Subgroup.inclusion hF) with hφ
  have hker : φ.ker = (F ⊓ Vge K).subgroupOf F := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [and_iff_right x.2, mem_Vge_iff (hF x.2)]
    have : φ x = Multiplicative.ofAdd
        (((x : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 1,
          ((x : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 3) := rfl
    rw [this, ofAdd_eq_one, Prod.ext_iff]
    simp
  have hidx : (F ⊓ Vge K).relIndex F = Nat.card φ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  obtain ⟨u₀, hu₀F, hu₀V⟩ := IsConcreteLE.not_le_iff_exists.1 hFV
  have hne : ¬ ((u₀ : Matrix (Fin 4) (Fin 4) K) 0 1 = 0 ∧
      (u₀ : Matrix (Fin 4) (Fin 4) K) 2 3 = 0) := fun h => hu₀V ((mem_Vge_iff (hF hu₀F)).2 h)
  set a := (u₀ : Matrix (Fin 4) (Fin 4) K) 0 1 with ha
  set d := (u₀ : Matrix (Fin 4) (Fin 4) K) 2 3 with hd
  set C := Vge K ⊓ Subgroup.centralizer (F : Set (SpecialLinearGroup (Fin 4) K)) with hC
  let Xof : ↥C → Matrix (Fin 2) (Fin 2) K := fun c => Classical.choose (mem_Vge.1 c.2.1)
  have hXof : ∀ c : ↥C, (c : SpecialLinearGroup (Fin 4) K) = corner (Xof c) :=
    fun c => Classical.choose_spec (mem_Vge.1 c.2.1)
  have hXinj : ∀ c c' : ↥C, Xof c = Xof c' → c = c' :=
    fun c c' h => Subtype.ext (by rw [hXof c, hXof c', h])
  have hcond : ∀ c : ↥C, ∀ u ∈ F,
      ((u : Matrix (Fin 4) (Fin 4) K) 0 1 * Xof c 1 0 = 0 ∧
        (u : Matrix (Fin 4) (Fin 4) K) 2 3 * Xof c 1 0 = 0 ∧
        (u : Matrix (Fin 4) (Fin 4) K) 0 1 * Xof c 1 1 =
          (u : Matrix (Fin 4) (Fin 4) K) 2 3 * Xof c 0 0) := by
    intro c u hu
    rw [← mul_corner_eq_iff (hF hu), ← hXof c]
    exact Subgroup.mem_centralizer_iff.1 c.2.2 u hu
  have hX10 : ∀ c : ↥C, Xof c 1 0 = 0 := by
    intro c
    obtain ⟨h1, h2, -⟩ := hcond c u₀ hu₀F
    by_contra h
    exact hne ⟨(mul_eq_zero.1 h1).resolve_right h, (mul_eq_zero.1 h2).resolve_right h⟩
  have hcardK : Nat.card (Multiplicative (K × K)) = Nat.card K ^ 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, sq]
  have hXext : ∀ X Y : Matrix (Fin 2) (Fin 2) K, X 0 0 = Y 0 0 → X 0 1 = Y 0 1 →
      X 1 0 = Y 1 0 → X 1 1 = Y 1 1 → X = Y := by
    intro X Y h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j <;> assumption
  by_cases hline : ∀ u ∈ F, a * (u : Matrix (Fin 4) (Fin 4) K) 2 3 =
      (u : Matrix (Fin 4) (Fin 4) K) 0 1 * d
  ·
    have hS : Nat.card φ.range ≤ Nat.card K := by
      have hr : ∀ x ∈ φ.range, a * (Multiplicative.toAdd x).2 = (Multiplicative.toAdd x).1 * d := by
        rintro _ ⟨w, rfl⟩
        exact hline w w.2
      refine Nat.card_le_card_of_injective
        (fun x : φ.range => if a = 0 then (Multiplicative.toAdd x.1).2 / d
          else (Multiplicative.toAdd x.1).1 / a) ?_
      rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      have hx' := hr x hx
      have hy' := hr y hy
      refine Subtype.ext (Multiplicative.toAdd.injective ?_)
      by_cases ha0 : a = 0
      · have hd0 : d ≠ 0 := fun h => hne ⟨ha0, h⟩
        simp only [ha0, ite_true] at hxy hx' hy'
        have h1 : (Multiplicative.toAdd x).1 = 0 := by
          have := hx'
          rw [zero_mul] at this
          exact ((mul_eq_zero.1 this.symm).resolve_right hd0)
        have h2 : (Multiplicative.toAdd y).1 = 0 := by
          have := hy'
          rw [zero_mul] at this
          exact ((mul_eq_zero.1 this.symm).resolve_right hd0)
        refine Prod.ext (by rw [h1, h2]) ?_
        exact (div_left_inj' hd0).1 hxy
      · simp only [ha0, ite_false] at hxy
        have h1 : (Multiplicative.toAdd x).1 = (Multiplicative.toAdd y).1 :=
          (div_left_inj' ha0).1 hxy
        refine Prod.ext h1 ?_
        have : a * (Multiplicative.toAdd x).2 = a * (Multiplicative.toAdd y).2 := by
          rw [hx', hy', h1]
        exact mul_left_cancel₀ ha0 this
    have hCle : Nat.card ↥C ≤ Nat.card K ^ 2 := by
      have h := Nat.card_le_card_of_injective
        (fun c : ↥C => ((if a = 0 then Xof c 1 1 else Xof c 0 0, Xof c 0 1) : K × K)) ?_
      · rwa [Nat.card_prod, ← sq] at h
      · intro c c' hcc
        apply hXinj
        have h1 : Xof c 0 1 = Xof c' 0 1 := (Prod.ext_iff.1 hcc).2
        have h2 : (if a = 0 then Xof c 1 1 else Xof c 0 0) =
            (if a = 0 then Xof c' 1 1 else Xof c' 0 0) := (Prod.ext_iff.1 hcc).1
        have e : a * Xof c 1 1 = d * Xof c 0 0 := (hcond c u₀ hu₀F).2.2
        have e' : a * Xof c' 1 1 = d * Xof c' 0 0 := (hcond c' u₀ hu₀F).2.2
        by_cases ha0 : a = 0
        · have hd0 : d ≠ 0 := fun h => hne ⟨ha0, h⟩
          simp only [ha0, ite_true] at h2
          rw [ha0, zero_mul] at e e'
          have x00 : Xof c 0 0 = 0 := (mul_eq_zero.1 e.symm).resolve_left hd0
          have x00' : Xof c' 0 0 = 0 := (mul_eq_zero.1 e'.symm).resolve_left hd0
          exact hXext _ _ (by rw [x00, x00']) h1 (by rw [hX10 c, hX10 c']) h2
        · simp only [ha0, ite_false] at h2
          have : a * Xof c 1 1 = a * Xof c' 1 1 := by rw [e, e', h2]
          exact hXext _ _ h2 h1 (by rw [hX10 c, hX10 c']) (mul_left_cancel₀ ha0 this)
    rw [hidx]
    calc Nat.card φ.range * Nat.card ↥C ≤ Nat.card K * Nat.card K ^ 2 := Nat.mul_le_mul hS hCle
      _ = Nat.card K ^ 3 := by ring
  ·
    push Not at hline
    obtain ⟨u₁, hu₁F, hu₁⟩ := hline
    have hdet : (a * (u₁ : Matrix (Fin 4) (Fin 4) K) 2 3 -
        (u₁ : Matrix (Fin 4) (Fin 4) K) 0 1 * d) ≠ 0 := sub_ne_zero.2 hu₁
    have hX : ∀ c : ↥C, Xof c 0 0 = 0 ∧ Xof c 1 1 = 0 := by
      intro c
      have e : a * Xof c 1 1 = d * Xof c 0 0 := (hcond c u₀ hu₀F).2.2
      have e' := (hcond c u₁ hu₁F).2.2
      refine ⟨?_, ?_⟩
      · have : (a * (u₁ : Matrix (Fin 4) (Fin 4) K) 2 3 -
            (u₁ : Matrix (Fin 4) (Fin 4) K) 0 1 * d) * Xof c 0 0 = 0 := by
          linear_combination (u₁ : Matrix (Fin 4) (Fin 4) K) 0 1 * e - a * e'
        exact (mul_eq_zero.1 this).resolve_left hdet
      · have : (a * (u₁ : Matrix (Fin 4) (Fin 4) K) 2 3 -
            (u₁ : Matrix (Fin 4) (Fin 4) K) 0 1 * d) * Xof c 1 1 = 0 := by
          linear_combination (u₁ : Matrix (Fin 4) (Fin 4) K) 2 3 * e - d * e'
        exact (mul_eq_zero.1 this).resolve_left hdet
    have hCle : Nat.card ↥C ≤ Nat.card K := by
      refine Nat.card_le_card_of_injective (fun c : ↥C => Xof c 0 1) ?_
      intro c c' hcc
      apply hXinj
      exact hXext _ _ (by rw [(hX c).1, (hX c').1]) hcc (by rw [hX10 c, hX10 c'])
        (by rw [(hX c).2, (hX c').2])
    have hS : Nat.card φ.range ≤ Nat.card K ^ 2 := by
      rw [← hcardK]
      exact Subgroup.card_le_card_group _
    rw [hidx]
    calc Nat.card φ.range * Nat.card ↥C ≤ Nat.card K ^ 2 * Nat.card K := Nat.mul_le_mul hS hCle
      _ = Nat.card K ^ 3 := by ring

theorem pushingUpS_Uge [CharP K 2] {f : ℕ} (hq : Nat.card K = 2 ^ f) :
    pushingUpS (Uge K) = Vge K := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  refine pushingUpS_eq_of_bounds (n := 4 * f) (m := 1) (B₁ := Nat.card K ^ 3) (B₂ := 0)
    Vge_le_Uge Vge_le_Uge (fun x hx y hy => Vge_comm hx hy) (fun x hx => Vge_sq hx) ?_
    (fun t ht h => centralizer_Uge_Vge ht h) le_rfl
    (fun F hF _ _ => by rw [inf_eq_left.2 hF, Subgroup.relIndex_self])
    (fun F hF _ _ hFV => inner_bound hF hFV) (fun t ht h => absurd ht h) ?_ ?_
  · rw [card_Vge, hq, ← pow_mul, mul_comm]
  · rw [card_Vge, one_mul]
    exact Nat.pow_lt_pow_right hq1 (by norm_num)
  · rw [card_Vge]
    positivity

end Bound

end CFSG.RankThree.PartOne.AUTSL.L4
