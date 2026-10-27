module

public import CFSG.Quasithin.Vol2.Lie2ParabolicRadicalSp4
public import CFSG.Quasithin.Vol2.Lie2ParabolicRadical

public section

namespace CFSG.Quasithin.H13.Ch4.Sp4M

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.H13.NQCat.Sp4
  CFSG.Quasithin.Lie2Parabolic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (unitri isUnitriangular_unitri inv_unitri)
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.Open (pCoreOf)
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] def rootSub (x : F → StatedSp 2 F) (hx : ∀ s t, x s * x t = x (s + t)) :
    Subgroup (StatedSp 2 F) where
  carrier := Set.range x
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, (hx s t).symm⟩
  one_mem' := ⟨0, by
    have h := hx 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h⟩
  inv_mem' := by
    rintro _ ⟨s, rfl⟩
    refine ⟨-s, eq_inv_of_mul_eq_one_right ?_⟩
    rw [hx, add_neg_cancel]
    have h := hx 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h

theorem card_rootSub {x : F → StatedSp 2 F} (hx : ∀ s t, x s * x t = x (s + t))
    (hinj : Function.Injective x) : Nat.card ↥(rootSub x hx) = Nat.card F :=
  Nat.card_range_of_injective hinj

variable (F) in
@[expose] def XAB : Subgroup (StatedSp 2 F) := rootSub xAB xAB_mul

variable (F) in
@[expose] def XC : Subgroup (StatedSp 2 F) := rootSub xC xC_mul

theorem xAB_mem_XAB (t : F) : xAB t ∈ XAB F := ⟨t, rfl⟩
theorem xC_mem_XC (t : F) : xC t ∈ XC F := ⟨t, rfl⟩

theorem xA_zero : xA (0 : F) = 1 := by
  have h := xA_mul (0 : F) 0
  rw [add_zero] at h
  exact mul_eq_left.mp h

theorem xB_zero : xB (0 : F) = 1 := by
  have h := xB_mul (0 : F) 0
  rw [add_zero] at h
  exact mul_eq_left.mp h

theorem xAB_zero : xAB (0 : F) = 1 := by
  have h := xAB_mul (0 : F) 0
  rw [add_zero] at h
  exact mul_eq_left.mp h

theorem xC_zero : xC (0 : F) = 1 := by
  have h := xC_mul (0 : F) 0
  rw [add_zero] at h
  exact mul_eq_left.mp h

theorem xAB_injective : Function.Injective (xAB : F → StatedSp 2 F) := fun s t h => by
  have := congrArg (fun g : StatedSp 2 F => spMat g (Sum.inl 1) (Sum.inr 0)) h
  simpa [spMat_xAB, single_apply] using this

theorem xC_injective : Function.Injective (xC : F → StatedSp 2 F) := fun s t h => by
  have := congrArg (fun g : StatedSp 2 F => spMat g (Sum.inl 0) (Sum.inr 0)) h
  simpa [spMat_xC, single_apply] using this

theorem card_XAB : Nat.card ↥(XAB F) = Nat.card F := card_rootSub _ xAB_injective

theorem card_XC : Nat.card ↥(XC F) = Nat.card F := card_rootSub _ xC_injective

theorem xC_comm_xAB (a b : F) : xC a * xAB b = xAB b * xC a := by
  apply statedSp_ext
  change spMat (xC a) * spMat (xAB b) = spMat (xAB b) * spMat (xC a)
  rw [spMat_xC, spMat_xAB]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, single_apply, Matrix.one_apply]

theorem xA_comm_xC (a b : F) : xA a * xC b = xC b * xA a := by
  apply statedSp_ext
  change spMat (xA a) * spMat (xC b) = spMat (xC b) * spMat (xA a)
  rw [spMat_xA, spMat_xC]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, single_apply, Matrix.one_apply]

theorem xA_comm_xAB [CharP F 2] (a b : F) : xA a * xAB b = xAB b * xA a := by
  apply statedSp_ext
  change spMat (xA a) * spMat (xAB b) = spMat (xAB b) * spMat (xA a)
  rw [spMat_xA, spMat_xAB]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, single_apply, Matrix.one_apply,
      CharTwo.neg_eq]
  all_goals ring

theorem spMat_prod (x c₀ c₁ c₂ : F) :
    spMat (xA x * xC c₀ * xAB c₁ * xB c₂) = blockMat (unitri x) !![c₀, c₁; c₁, c₂] := by
  simp only [spMat_mul, spMat_xA, spMat_xC, spMat_xAB, spMat_xB]
  rw [blockMat, inv_unitri]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [unitri, single_apply, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_sum_type,
      Matrix.one_apply] <;> ring

theorem prod_apply (x c₀ c₁ c₂ : F) :
    spMat (xA x * xC c₀ * xAB c₁ * xB c₂) (Sum.inl 0) (Sum.inl 1) = x ∧
      spMat (xA x * xC c₀ * xAB c₁ * xB c₂) (Sum.inl 0) (Sum.inr 0) = c₀ + x * c₁ ∧
      spMat (xA x * xC c₀ * xAB c₁ * xB c₂) (Sum.inl 1) (Sum.inr 0) = c₁ ∧
      spMat (xA x * xC c₀ * xAB c₁ * xB c₂) (Sum.inl 1) (Sum.inr 1) = c₂ := by
  rw [spMat_prod]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [blockMat, unitri]

theorem prod_inj {x c₀ c₁ c₂ x' c₀' c₁' c₂' : F}
    (h : xA x * xC c₀ * xAB c₁ * xB c₂ = xA x' * xC c₀' * xAB c₁' * xB c₂') :
    x = x' ∧ c₀ = c₀' ∧ c₁ = c₁' ∧ c₂ = c₂' := by
  have e := prod_apply x c₀ c₁ c₂
  have e' := prod_apply x' c₀' c₁' c₂'
  rw [h] at e
  have hx : x = x' := e.1.symm.trans e'.1
  have h1 : c₁ = c₁' := e.2.2.1.symm.trans e'.2.2.1
  have h2 : c₂ = c₂' := e.2.2.2.symm.trans e'.2.2.2
  have h0 : c₀ + x * c₁ = c₀' + x' * c₁' := e.2.1.symm.trans e'.2.1
  rw [hx, h1] at h0
  exact ⟨hx, add_right_cancel h0, h1, h2⟩

theorem prod_mem_unipotent (x c₀ c₁ c₂ : F) : xA x * xC c₀ * xAB c₁ * xB c₂ ∈ unipotent 2 F :=
  mul_mem (mul_mem (mul_mem (xA_mem x) (xC_mem c₀)) (xAB_mem c₁)) (xB_mem c₂)

theorem spMat_rad1 (c₀ c₁ c₂ : F) :
    spMat (xC c₀ * xAB c₁ * xB c₂) = fromBlocks 1 !![c₀, c₁; c₁, c₂] 0 1 := by
  have e : xC c₀ * xAB c₁ * xB c₂ = xA 0 * xC c₀ * xAB c₁ * xB c₂ := by rw [xA_zero, one_mul]
  rw [e, spMat_prod, blockMat]
  have hu : unitri (0 : F) = 1 := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [unitri]
  rw [hu]
  simp

theorem rad1_inj {c₀ c₁ c₂ d₀ d₁ d₂ : F} (h : xC c₀ * xAB c₁ * xB c₂ = xC d₀ * xAB d₁ * xB d₂) :
    c₀ = d₀ ∧ c₁ = d₁ ∧ c₂ = d₂ := by
  have h' : xA 0 * xC c₀ * xAB c₁ * xB c₂ = xA 0 * xC d₀ * xAB d₁ * xB d₂ := by
    simp only [xA_zero, one_mul]
    exact h
  exact (prod_inj h').2

theorem rad0_inj {x c₀ c₁ y d₀ d₁ : F} (h : xA x * xC c₀ * xAB c₁ = xA y * xC d₀ * xAB d₁) :
    x = y ∧ c₀ = d₀ ∧ c₁ = d₁ := by
  have h' : xA x * xC c₀ * xAB c₁ * xB 0 = xA y * xC d₀ * xAB d₁ * xB 0 := by
    simp only [xB_zero, mul_one]
    exact h
  obtain ⟨h1, h2, h3, -⟩ := prod_inj h'
  exact ⟨h1, h2, h3⟩

theorem rad1_mul (c₀ c₁ c₂ d₀ d₁ d₂ : F) :
    xC c₀ * xAB c₁ * xB c₂ * (xC d₀ * xAB d₁ * xB d₂) =
      xC (c₀ + d₀) * xAB (c₁ + d₁) * xB (c₂ + d₂) := by
  apply statedSp_ext
  change spMat (xC c₀ * xAB c₁ * xB c₂) * spMat (xC d₀ * xAB d₁ * xB d₂) = spMat _
  rw [spMat_rad1, spMat_rad1, spMat_rad1, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add]
  congr 1
  ext i k
  fin_cases i <;> fin_cases k <;> simp [add_comm]

theorem blkIdx_prod (x c₀ c₁ c₂ : F) :
    blkIdx (sigma2 1) (spMat (xA x * xC c₀ * xAB c₁ * xB c₂)) = unitri x ∧
      blkIdx (sigma2 0) (spMat (xA x * xC c₀ * xAB c₁ * xB c₂)) = unitri c₂ := by
  rw [spMat_prod, blockMat, inv_unitri]
  constructor <;>
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [blkIdx, sigma2, unitri]

theorem unitri_eq_one_iff (x : F) : unitri x = 1 ↔ x = 0 := by
  constructor
  · intro h
    have := congrFun₂ h 0 1
    simpa [unitri] using this
  · rintro rfl
    ext i k
    fin_cases i <;> fin_cases k <;> simp [unitri]

theorem commute_xA_xA (s t : F) : Commute (xA s) (xA t) := by
  rw [Commute, SemiconjBy, xA_mul, xA_mul, add_comm]

theorem commute_xC_xC (s t : F) : Commute (xC s) (xC t) := by
  rw [Commute, SemiconjBy, xC_mul, xC_mul, add_comm]

theorem commute_xAB_xAB (s t : F) : Commute (xAB s) (xAB t) := by
  rw [Commute, SemiconjBy, xAB_mul, xAB_mul, add_comm]

theorem commute_rad0 [CharP F 2] (x c₀ c₁ y d₀ d₁ : F) :
    Commute (xA x * xC c₀ * xAB c₁) (xA y * xC d₀ * xAB d₁) := by
  have hAC : ∀ s t : F, Commute (xA s) (xC t) := fun s t => xA_comm_xC s t
  have hAAB : ∀ s t : F, Commute (xA s) (xAB t) := fun s t => xA_comm_xAB s t
  have hCAB : ∀ s t : F, Commute (xC s) (xAB t) := fun s t => xC_comm_xAB s t
  refine Commute.mul_left (Commute.mul_left ?_ ?_) ?_
  · exact ((commute_xA_xA x y).mul_right (hAC x d₀)).mul_right (hAAB x d₁)
  · exact (((hAC y c₀).symm).mul_right (commute_xC_xC c₀ d₀)).mul_right (hCAB c₀ d₁)
  · exact (((hAAB y c₁).symm).mul_right (hCAB d₀ c₁).symm).mul_right (commute_xAB_xAB c₁ d₁)

variable [Finite F] [CharP F 2] {n : ℕ}

theorem mem_perfectCore_of_mem_unipotent (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (j : Fin 2)
    {g : StatedSp 2 F} (hg : g ∈ unipotent 2 F) : g ∈ perfectCore (Q2 F j) :=
  unipotent_le_perfectCore (NQCat.exists_finset_card_four_of_card hn hF) j hg

theorem mem_R1_iff (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) {g : StatedSp 2 F} :
    g ∈ pCoreOf 2 (perfectCore (Q2 F 1)) ↔ ∃ c₀ c₁ c₂ : F, g = xC c₀ * xAB c₁ * xB c₂ := by
  constructor
  · intro hg
    have hgC : g ∈ perfectCore (Q2 F 1) := Subgroup.map_subtype_le _ hg
    have hblk := (mem_pCoreOf_perfectCore_Q2 hn hF 1 hgC).mp hg
    obtain ⟨x, c₀, c₁, c₂, rfl⟩ :=
      exists_eq_prod_of_mem_unipotent (blkN_ker 1 ⟨_, hgC⟩ (Subtype.ext hblk))
    rw [(blkIdx_prod x c₀ c₁ c₂).1, unitri_eq_one_iff] at hblk
    subst hblk
    exact ⟨c₀, c₁, c₂, by rw [xA_zero, one_mul]⟩
  · rintro ⟨c₀, c₁, c₂, rfl⟩
    have e : xC c₀ * xAB c₁ * xB c₂ = xA 0 * xC c₀ * xAB c₁ * xB c₂ := by rw [xA_zero, one_mul]
    rw [e]
    have hL := mem_perfectCore_of_mem_unipotent hn hF 1 (prod_mem_unipotent 0 c₀ c₁ c₂)
    refine (mem_pCoreOf_perfectCore_Q2 hn hF 1 hL).mpr ?_
    rw [(blkIdx_prod 0 c₀ c₁ c₂).1, unitri_eq_one_iff]

theorem mem_R0_iff (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) {g : StatedSp 2 F} :
    g ∈ pCoreOf 2 (perfectCore (Q2 F 0)) ↔ ∃ x c₀ c₁ : F, g = xA x * xC c₀ * xAB c₁ := by
  constructor
  · intro hg
    have hgC : g ∈ perfectCore (Q2 F 0) := Subgroup.map_subtype_le _ hg
    have hblk := (mem_pCoreOf_perfectCore_Q2 hn hF 0 hgC).mp hg
    obtain ⟨x, c₀, c₁, c₂, rfl⟩ :=
      exists_eq_prod_of_mem_unipotent (blkN_ker 0 ⟨_, hgC⟩ (Subtype.ext hblk))
    rw [(blkIdx_prod x c₀ c₁ c₂).2, unitri_eq_one_iff] at hblk
    subst hblk
    exact ⟨x, c₀, c₁, by rw [xB_zero, mul_one]⟩
  · rintro ⟨x, c₀, c₁, rfl⟩
    have e : xA x * xC c₀ * xAB c₁ = xA x * xC c₀ * xAB c₁ * xB 0 := by rw [xB_zero, mul_one]
    rw [e]
    have hL := mem_perfectCore_of_mem_unipotent hn hF 0 (prod_mem_unipotent x c₀ c₁ 0)
    refine (mem_pCoreOf_perfectCore_Q2 hn hF 0 hL).mpr ?_
    rw [(blkIdx_prod x c₀ c₁ 0).2, unitri_eq_one_iff]

theorem mem_R1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (c₀ c₁ c₂ : F) :
    xC c₀ * xAB c₁ * xB c₂ ∈ pCoreOf 2 (perfectCore (Q2 F 1)) :=
  (mem_R1_iff hn hF).mpr ⟨c₀, c₁, c₂, rfl⟩

theorem mem_R0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (x c₀ c₁ : F) :
    xA x * xC c₀ * xAB c₁ ∈ pCoreOf 2 (perfectCore (Q2 F 0)) :=
  (mem_R0_iff hn hF).mpr ⟨x, c₀, c₁, rfl⟩

theorem xC_mem_R1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (t : F) :
    xC t ∈ pCoreOf 2 (perfectCore (Q2 F 1)) := by
  have := mem_R1 hn hF t 0 0
  rwa [xAB_zero, xB_zero, mul_one, mul_one] at this

theorem xAB_mem_R1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (t : F) :
    xAB t ∈ pCoreOf 2 (perfectCore (Q2 F 1)) := by
  have := mem_R1 hn hF 0 t 0
  rwa [xC_zero, xB_zero, mul_one, one_mul] at this

theorem xB_mem_R1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (t : F) :
    xB t ∈ pCoreOf 2 (perfectCore (Q2 F 1)) := by
  have := mem_R1 hn hF 0 0 t
  rwa [xC_zero, xAB_zero, one_mul, one_mul] at this

theorem xA_mem_R0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (t : F) :
    xA t ∈ pCoreOf 2 (perfectCore (Q2 F 0)) := by
  have := mem_R0 hn hF t 0 0
  rwa [xC_zero, xAB_zero, mul_one, mul_one] at this

theorem xC_mem_R0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (t : F) :
    xC t ∈ pCoreOf 2 (perfectCore (Q2 F 0)) := by
  have := mem_R0 hn hF 0 t 0
  rwa [xA_zero, xAB_zero, mul_one, one_mul] at this

theorem xAB_mem_R0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (t : F) :
    xAB t ∈ pCoreOf 2 (perfectCore (Q2 F 0)) := by
  have := mem_R0 hn hF 0 0 t
  rwa [xA_zero, xC_zero, one_mul, one_mul] at this

theorem XC_le_R1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    XC F ≤ pCoreOf 2 (perfectCore (Q2 F 1)) := by
  rintro _ ⟨t, rfl⟩
  exact xC_mem_R1 hn hF t

theorem XAB_le_R1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    XAB F ≤ pCoreOf 2 (perfectCore (Q2 F 1)) := by
  rintro _ ⟨t, rfl⟩
  exact xAB_mem_R1 hn hF t

theorem XC_le_R0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    XC F ≤ pCoreOf 2 (perfectCore (Q2 F 0)) := by
  rintro _ ⟨t, rfl⟩
  exact xC_mem_R0 hn hF t

theorem XAB_le_R0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    XAB F ≤ pCoreOf 2 (perfectCore (Q2 F 0)) := by
  rintro _ ⟨t, rfl⟩
  exact xAB_mem_R0 hn hF t

theorem card_R1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    Nat.card ↥(pCoreOf 2 (perfectCore (Q2 F 1))) = 2 ^ (3 * n) := by
  have hset : ((pCoreOf 2 (perfectCore (Q2 F 1)) : Subgroup (StatedSp 2 F)) :
      Set (StatedSp 2 F)) = Set.range (fun c : F × F × F => xC c.1 * xAB c.2.1 * xB c.2.2) := by
    ext g
    rw [SetLike.mem_coe, mem_R1_iff hn hF]
    constructor
    · rintro ⟨c₀, c₁, c₂, rfl⟩
      exact ⟨(c₀, c₁, c₂), rfl⟩
    · rintro ⟨⟨c₀, c₁, c₂⟩, rfl⟩
      exact ⟨c₀, c₁, c₂, rfl⟩
  have hinj : Function.Injective (fun c : F × F × F => xC c.1 * xAB c.2.1 * xB c.2.2) := by
    rintro ⟨c₀, c₁, c₂⟩ ⟨d₀, d₁, d₂⟩ h
    obtain ⟨h0, h1, h2⟩ := rad1_inj (show xC c₀ * xAB c₁ * xB c₂ = xC d₀ * xAB d₁ * xB d₂ from h)
    rw [h0, h1, h2]
  change Nat.card ↥((pCoreOf 2 (perfectCore (Q2 F 1)) : Subgroup (StatedSp 2 F)) :
    Set (StatedSp 2 F)) = _
  rw [hset, Nat.card_range_of_injective hinj, Nat.card_prod, Nat.card_prod, hF]
  ring

theorem card_R0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    Nat.card ↥(pCoreOf 2 (perfectCore (Q2 F 0))) = 2 ^ (3 * n) := by
  have hset : ((pCoreOf 2 (perfectCore (Q2 F 0)) : Subgroup (StatedSp 2 F)) :
      Set (StatedSp 2 F)) = Set.range (fun c : F × F × F => xA c.1 * xC c.2.1 * xAB c.2.2) := by
    ext g
    rw [SetLike.mem_coe, mem_R0_iff hn hF]
    constructor
    · rintro ⟨x, c₀, c₁, rfl⟩
      exact ⟨(x, c₀, c₁), rfl⟩
    · rintro ⟨⟨x, c₀, c₁⟩, rfl⟩
      exact ⟨x, c₀, c₁, rfl⟩
  have hinj : Function.Injective (fun c : F × F × F => xA c.1 * xC c.2.1 * xAB c.2.2) := by
    rintro ⟨x, c₀, c₁⟩ ⟨y, d₀, d₁⟩ h
    obtain ⟨h0, h1, h2⟩ := rad0_inj (show xA x * xC c₀ * xAB c₁ = xA y * xC d₀ * xAB d₁ from h)
    rw [h0, h1, h2]
  change Nat.card ↥((pCoreOf 2 (perfectCore (Q2 F 0)) : Subgroup (StatedSp 2 F)) :
    Set (StatedSp 2 F)) = _
  rw [hset, Nat.card_range_of_injective hinj, Nat.card_prod, Nat.card_prod, hF]
  ring

theorem R1_comm (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) {a b : StatedSp 2 F}
    (ha : a ∈ pCoreOf 2 (perfectCore (Q2 F 1))) (hb : b ∈ pCoreOf 2 (perfectCore (Q2 F 1))) :
    a * b = b * a := by
  obtain ⟨c₀, c₁, c₂, rfl⟩ := (mem_R1_iff hn hF).mp ha
  obtain ⟨d₀, d₁, d₂, rfl⟩ := (mem_R1_iff hn hF).mp hb
  rw [rad1_mul, rad1_mul, add_comm c₀, add_comm c₁, add_comm c₂]

theorem R0_comm (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) {a b : StatedSp 2 F}
    (ha : a ∈ pCoreOf 2 (perfectCore (Q2 F 0))) (hb : b ∈ pCoreOf 2 (perfectCore (Q2 F 0))) :
    a * b = b * a := by
  obtain ⟨x, c₀, c₁, rfl⟩ := (mem_R0_iff hn hF).mp ha
  obtain ⟨y, d₀, d₁, rfl⟩ := (mem_R0_iff hn hF).mp hb
  exact commute_rad0 x c₀ c₁ y d₀ d₁

theorem R1_le_unipotent (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    pCoreOf 2 (perfectCore (Q2 F 1)) ≤ unipotent 2 F := by
  intro g hg
  obtain ⟨c₀, c₁, c₂, rfl⟩ := (mem_R1_iff hn hF).mp hg
  exact mul_mem (mul_mem (xC_mem c₀) (xAB_mem c₁)) (xB_mem c₂)

theorem R0_le_unipotent (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    pCoreOf 2 (perfectCore (Q2 F 0)) ≤ unipotent 2 F := by
  intro g hg
  obtain ⟨x, c₀, c₁, rfl⟩ := (mem_R0_iff hn hF).mp hg
  exact mul_mem (mul_mem (xA_mem x) (xC_mem c₀)) (xAB_mem c₁)

theorem unipotent_eq_sup (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    unipotent 2 F = pCoreOf 2 (perfectCore (Q2 F 1)) ⊔ pCoreOf 2 (perfectCore (Q2 F 0)) := by
  refine le_antisymm (fun u hu => ?_) (sup_le (R1_le_unipotent hn hF) (R0_le_unipotent hn hF))
  obtain ⟨x, c₀, c₁, c₂, rfl⟩ := exists_eq_prod_of_mem_unipotent hu
  rw [mul_assoc, mul_assoc, ← mul_assoc (xC c₀)]
  refine mul_mem (Subgroup.mem_sup_right (xA_mem_R0 hn hF x))
    (Subgroup.mem_sup_left (mem_R1 hn hF c₀ c₁ c₂))

theorem R1_inf_R0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    pCoreOf 2 (perfectCore (Q2 F 1)) ⊓ pCoreOf 2 (perfectCore (Q2 F 0)) = XC F ⊔ XAB F := by
  refine le_antisymm (fun g hg => ?_) (sup_le (le_inf (XC_le_R1 hn hF) (XC_le_R0 hn hF))
    (le_inf (XAB_le_R1 hn hF) (XAB_le_R0 hn hF)))
  obtain ⟨c₀, c₁, c₂, rfl⟩ := (mem_R1_iff hn hF).mp hg.1
  obtain ⟨x, d₀, d₁, h⟩ := (mem_R0_iff hn hF).mp hg.2
  have h' : xA 0 * xC c₀ * xAB c₁ * xB c₂ = xA x * xC d₀ * xAB d₁ * xB 0 := by
    rw [xA_zero, one_mul, xB_zero, mul_one]
    exact h
  obtain ⟨-, -, -, hc₂⟩ := prod_inj h'
  rw [hc₂, xB_zero, mul_one]
  exact mul_mem (Subgroup.mem_sup_left (xC_mem_XC c₀)) (Subgroup.mem_sup_right (xAB_mem_XAB c₁))

theorem mem_XC_sup_XAB {g : StatedSp 2 F} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hg : g ∈ XC F ⊔ XAB F) : ∃ a b : F, g = xC a * xAB b := by
  rw [← R1_inf_R0 hn hF] at hg
  obtain ⟨c₀, c₁, c₂, rfl⟩ := (mem_R1_iff hn hF).mp hg.1
  obtain ⟨x, d₀, d₁, h⟩ := (mem_R0_iff hn hF).mp hg.2
  have h' : xA 0 * xC c₀ * xAB c₁ * xB c₂ = xA x * xC d₀ * xAB d₁ * xB 0 := by
    rw [xA_zero, one_mul, xB_zero, mul_one]
    exact h
  obtain ⟨-, -, -, hc₂⟩ := prod_inj h'
  exact ⟨c₀, c₁, by rw [hc₂, xB_zero, mul_one]⟩

theorem card_XC_sup_XAB (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    Nat.card ↥(XC F ⊔ XAB F) = 2 ^ (2 * n) := by
  have hset : ((XC F ⊔ XAB F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)) =
      Set.range (fun c : F × F => xC c.1 * xAB c.2) := by
    ext g
    rw [SetLike.mem_coe]
    constructor
    · intro hg
      obtain ⟨a, b, rfl⟩ := mem_XC_sup_XAB hn hF hg
      exact ⟨(a, b), rfl⟩
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact mul_mem (Subgroup.mem_sup_left (xC_mem_XC a)) (Subgroup.mem_sup_right (xAB_mem_XAB b))
  have hinj : Function.Injective (fun c : F × F => xC c.1 * xAB c.2) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : xC a * xAB b * xB 0 = xC a' * xAB b' * xB 0 := by
      simp only [xB_zero, mul_one]
      exact (show xC a * xAB b = xC a' * xAB b' from h)
    obtain ⟨h0, h1, -⟩ := rad1_inj h'
    rw [h0, h1]
  change Nat.card ↥((XC F ⊔ XAB F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)) = _
  rw [hset, Nat.card_range_of_injective hinj, Nat.card_prod, hF]
  ring

omit [Finite F] [CharP F 2] in
theorem XC_inf_XAB : XC F ⊓ XAB F = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  have h' : xA 0 * xC a * xAB 0 * xB 0 = xA 0 * xC 0 * xAB b * xB 0 := by
    rw [xA_zero, xAB_zero, xB_zero, xC_zero, hb]
    group
  obtain ⟨-, ha, -, -⟩ := prod_inj h'
  rw [Subgroup.mem_bot, ha, xC_zero]

theorem R1_inf_centralizer_R0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    pCoreOf 2 (perfectCore (Q2 F 1)) ⊓
        Subgroup.centralizer (pCoreOf 2 (perfectCore (Q2 F 0)) : Set (StatedSp 2 F)) =
      pCoreOf 2 (perfectCore (Q2 F 1)) ⊓ pCoreOf 2 (perfectCore (Q2 F 0)) := by
  apply le_antisymm
  · intro g hg
    refine ⟨hg.1, ?_⟩
    obtain ⟨c₀, c₁, c₂, rfl⟩ := (mem_R1_iff hn hF).mp hg.1
    have hcomm := Subgroup.mem_centralizer_iff.mp hg.2 (xA 1) (xA_mem_R0 hn hF 1)
    have he : (spMat (xA 1) * spMat (xC c₀ * xAB c₁ * xB c₂) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Sum.inl 0) (Sum.inr 1) =
        (spMat (xC c₀ * xAB c₁ * xB c₂) * spMat (xA 1) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Sum.inl 0) (Sum.inr 1) :=
      congrArg (fun g : StatedSp 2 F => spMat g (Sum.inl 0) (Sum.inr 1)) hcomm
    rw [spMat_rad1, spMat_xA] at he
    have hc₂ : c₂ = 0 := by
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, single_apply,
        Matrix.one_apply] using he
    rw [hc₂, xB_zero, mul_one]
    exact mul_mem (xC_mem_R0 hn hF c₀) (xAB_mem_R0 hn hF c₁)
  · intro g hg
    exact ⟨hg.1, Subgroup.mem_centralizer_iff.mpr fun h hh => R0_comm hn hF hh hg.2⟩

theorem R0_inf_centralizer_R1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    pCoreOf 2 (perfectCore (Q2 F 0)) ⊓
        Subgroup.centralizer (pCoreOf 2 (perfectCore (Q2 F 1)) : Set (StatedSp 2 F)) =
      pCoreOf 2 (perfectCore (Q2 F 1)) ⊓ pCoreOf 2 (perfectCore (Q2 F 0)) := by
  apply le_antisymm
  · intro g hg
    refine ⟨?_, hg.1⟩
    obtain ⟨x, c₀, c₁, rfl⟩ := (mem_R0_iff hn hF).mp hg.1
    have hcomm := Subgroup.mem_centralizer_iff.mp hg.2 (xB 1) (xB_mem_R1 hn hF 1)
    have e : xA x * xC c₀ * xAB c₁ = xA x * xC c₀ * xAB c₁ * xB 0 := by rw [xB_zero, mul_one]
    rw [e] at hcomm
    have he : (spMat (xB 1) * spMat (xA x * xC c₀ * xAB c₁ * xB 0) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Sum.inl 0) (Sum.inr 1) =
        (spMat (xA x * xC c₀ * xAB c₁ * xB 0) * spMat (xB 1) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Sum.inl 0) (Sum.inr 1) :=
      congrArg (fun g : StatedSp 2 F => spMat g (Sum.inl 0) (Sum.inr 1)) hcomm
    rw [spMat_prod, spMat_xB] at he
    have hx : x = 0 := by
      simpa [blockMat, unitri, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        single_apply, Matrix.one_apply] using he
    rw [hx, xA_zero, one_mul]
    exact mul_mem (xC_mem_R1 hn hF c₀) (xAB_mem_R1 hn hF c₁)
  · intro g hg
    exact ⟨hg.2, Subgroup.mem_centralizer_iff.mpr fun h hh => R1_comm hn hF hh hg.1⟩

theorem relIndex_R1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    (pCoreOf 2 (perfectCore (Q2 F 1)) ⊓ pCoreOf 2 (perfectCore (Q2 F 0))).relIndex
      (pCoreOf 2 (perfectCore (Q2 F 1))) = 2 ^ n := by
  rw [R1_inf_R0 hn hF]
  have h := Subgroup.relIndex_mul_card (XC F ⊔ XAB F) (pCoreOf 2 (perfectCore (Q2 F 1)))
  rw [inf_eq_left.mpr (sup_le (XC_le_R1 hn hF) (XAB_le_R1 hn hF)), card_XC_sup_XAB hn hF,
    card_R1 hn hF, show 3 * n = n + 2 * n by ring, pow_add] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem relIndex_R0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    (pCoreOf 2 (perfectCore (Q2 F 1)) ⊓ pCoreOf 2 (perfectCore (Q2 F 0))).relIndex
      (pCoreOf 2 (perfectCore (Q2 F 0))) = 2 ^ n := by
  rw [R1_inf_R0 hn hF]
  have h := Subgroup.relIndex_mul_card (XC F ⊔ XAB F) (pCoreOf 2 (perfectCore (Q2 F 0)))
  rw [inf_eq_left.mpr (sup_le (XC_le_R0 hn hF) (XAB_le_R0 hn hF)), card_XC_sup_XAB hn hF,
    card_R0 hn hF, show 3 * n = n + 2 * n by ring, pow_add] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

end CFSG.Quasithin.H13.Ch4.Sp4M
