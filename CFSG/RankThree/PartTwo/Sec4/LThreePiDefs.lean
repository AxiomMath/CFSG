module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

@[expose] def piCard (π : Bool) (q : ℕ) : ℕ := cond π q (q ^ 2)

structure PiField (π : Bool) (p f : ℕ) (K : Type) [Field K] : Prop where
  prime : p.Prime
  one_le : 1 ≤ f
  card : Nat.card K = piCard π (p ^ f)

@[expose] def ModThree (π : Bool) (q : ℕ) : Prop := cond π (q % 3 = 1) (q % 3 = 2)

@[expose] def glPi (π : Bool) (n q : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  cond π ⊤ (Subgroup.closure {A | ((A : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ *
    (A : Matrix (Fin n) (Fin n) K) = 1})

@[expose] def slPi (π : Bool) (n q : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  cond π (StatedSL n K) (StatedSU n q K)

@[expose] def zPi (π : Bool) (n q : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  (Subgroup.center (glPi π n q K)).map (glPi π n q K).subtype

namespace PiField

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem finite (h : PiField π p f K) : Finite K :=
  Nat.finite_of_card_ne_zero (by
    rw [h.card]
    cases π
    · exact pow_ne_zero _ (pow_ne_zero _ h.prime.ne_zero)
    · exact pow_ne_zero _ h.prime.ne_zero)

theorem unitary (h : PiField false p f K) : UnitaryFieldData p f K :=
  ⟨h.prime, h.one_le, by rw [h.card, piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩

end PiField

section Membership

variable {K : Type} [Field K] {n : ℕ}

theorem mem_glPi_true (q : ℕ) (A : GL (Fin n) K) : A ∈ glPi true n q K :=
  Subgroup.mem_top A

theorem mem_slPi_true (q : ℕ) {A : GL (Fin n) K} :
    A ∈ slPi true n q K ↔ (A : Matrix (Fin n) (Fin n) K).det = 1 := by
  change A ∈ StatedSL n K ↔ _
  rw [statedSL_eq_range_toGL]
  constructor
  · rintro ⟨B, rfl⟩
    exact B.2
  · intro hA
    exact ⟨⟨A, hA⟩, Units.ext rfl⟩

variable {p f : ℕ}

@[expose] def guSubgroup (h : UnitaryFieldData p f K) (n : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {A | ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1}
  mul_mem' {A B} hA hB := by
    change (((A * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((A * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    calc ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
          ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
          ((A : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K))
        = ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
          (((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K)) *
            (B : Matrix (Fin n) (Fin n) K) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [show ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) =
            1 from hA, Matrix.mul_one]
          exact hB
  one_mem' := by
    change (((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [Units.val_one, Matrix.map_one (h.bar : K → K) (map_zero _) (map_one _),
      Matrix.transpose_one, Matrix.mul_one]
  inv_mem' {A} hA := by
    change (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    have hA' : ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1 :=
      hA
    have hinv : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ := by
      calc ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          = ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) *
              ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hA', Matrix.one_mul]
        _ = ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ := by
            rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    have hbb : ((A : Matrix (Fin n) (Fin n) K).map h.bar).map h.bar =
        (A : Matrix (Fin n) (Fin n) K) := by
      ext i j
      simp [h.bar_bar]
    rw [hinv, Matrix.transpose_map, hbb, Matrix.transpose_transpose, ← hinv, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]

theorem mem_guSubgroup (h : UnitaryFieldData p f K) {A : GL (Fin n) K} :
    A ∈ guSubgroup h n ↔
      ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1 :=
  Iff.rfl

theorem glPi_false_eq (h : UnitaryFieldData p f K) : glPi false n (p ^ f) K = guSubgroup h n := by
  change Subgroup.closure _ = _
  have hset : {A : GL (Fin n) K | ((A : Matrix (Fin n) (Fin n) K).map (· ^ p ^ f))ᵀ *
      (A : Matrix (Fin n) (Fin n) K) = 1} = (guSubgroup h n : Set (GL (Fin n) K)) := rfl
  rw [hset, Subgroup.closure_eq]

theorem mem_glPi_false (h : UnitaryFieldData p f K) {A : GL (Fin n) K} :
    A ∈ glPi false n (p ^ f) K ↔
      ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [glPi_false_eq h]
  rfl

theorem mem_slPi_false (h : UnitaryFieldData p f K) {A : GL (Fin n) K} :
    A ∈ slPi false n (p ^ f) K ↔ (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1 :=
  CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h

theorem slPi_le_glPi {π : Bool} (hπ : π = false → UnitaryFieldData p f K) :
    slPi π n (p ^ f) K ≤ glPi π n (p ^ f) K := by
  cases π
  · intro A hA
    exact (mem_glPi_false (hπ rfl)).2 ((mem_slPi_false (hπ rfl)).1 hA).2
  · intro A _
    exact mem_glPi_true _ A

theorem mem_slPi_iff {π : Bool} (hπ : π = false → UnitaryFieldData p f K) {A : GL (Fin n) K} :
    A ∈ slPi π n (p ^ f) K ↔
      A ∈ glPi π n (p ^ f) K ∧ (A : Matrix (Fin n) (Fin n) K).det = 1 := by
  cases π
  · rw [mem_slPi_false (hπ rfl), mem_glPi_false (hπ rfl), and_comm]
  · rw [mem_slPi_true]
    exact ⟨fun h => ⟨mem_glPi_true _ A, h⟩, fun h => h.2⟩

end Membership

section Elements

variable {K : Type} [Field K]

theorem pow_succ_eq_one_of_modThree {q : ℕ} (hq : ModThree false q) {τ : K} (hτ : τ ^ 3 = 1) :
    τ ^ (q + 1) = 1 := by
  have h3 : 3 ∣ q + 1 := by
    change q % 3 = 2 at hq
    omega
  obtain ⟨k, hk⟩ := h3
  rw [hk, pow_mul, hτ, one_pow]

@[expose] def diagTau {τ : K} (hτ : τ ^ 3 = 1) : GL (Fin 3) K :=
  ⟨!![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1], !![τ ^ 2, 0, 0; 0, τ, 0; 0, 0, 1],
    by
      have h : τ * τ ^ 2 = 1 := by rw [← pow_succ']; exact hτ
      have h' : τ ^ 2 * τ = 1 := by rw [← pow_succ]; exact hτ
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h, h'],
    by
      have h : τ * τ ^ 2 = 1 := by rw [← pow_succ']; exact hτ
      have h' : τ ^ 2 * τ = 1 := by rw [← pow_succ]; exact hτ
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h, h']⟩

theorem coe_diagTau {τ : K} (hτ : τ ^ 3 = 1) :
    ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1] :=
  rfl

@[expose] def cycThree : GL (Fin 3) K :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_cycThree :
    ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 1, 0, 0; 0, 1, 0] :=
  rfl

variable {p f : ℕ}

theorem diagTau_mem_slPi {π : Bool} (hπ : π = false → UnitaryFieldData p f K)
    (hq : π = false → ModThree false (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) :
    diagTau hτ ∈ slPi π 3 (p ^ f) K := by
  have hdet : ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_diagTau, det_fin_three]
    simp
    linear_combination hτ
  cases π
  · have h := hπ rfl
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    have hn := pow_succ_eq_one_of_modThree (hq rfl) hτ
    have h1 : h.bar τ * τ = 1 := by rw [h.bar_apply, ← pow_succ]; exact hn
    have h2 : h.bar τ ^ 2 * τ ^ 2 = 1 := by
      rw [← mul_pow, h1, one_pow]
    rw [coe_diagTau]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, transpose_apply, h1, h2]
  · rw [mem_slPi_true]
    exact hdet

theorem cycThree_mem_slPi {π : Bool} (hπ : π = false → UnitaryFieldData p f K) :
    cycThree ∈ slPi π 3 (p ^ f) K := by
  have hdet : ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_cycThree, det_fin_three]
    simp
  cases π
  · have h := hπ rfl
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    rw [coe_cycThree]
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, transpose_apply]
  · rw [mem_slPi_true]
    exact hdet

theorem eq_smul_one_of_commute {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {M : Matrix (Fin 3) (Fin 3) K}
    (h1 : M * ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M)
    (h2 : M * ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M) :
    M = M 0 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  have hττ2 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  rw [coe_diagTau] at h1
  rw [coe_cycThree] at h2
  have e : ∀ i j, (M * !![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1]) i j =
      (!![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1] * M) i j := fun i j => by rw [h1]
  have c : ∀ i j, (M * (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K)) i j =
      ((!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) * M) i j := fun i j => by
    rw [h2]
  have aux : ∀ {X a b : K}, a ≠ b → X * a = b * X → X = 0 := fun {X a b} hab h => by
    have h' : X * (a - b) = 0 := by rw [mul_sub, h, mul_comm, sub_self]
    exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr hab)
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have c02 := c 0 2
  have c10 := c 1 0
  simp [mul_apply, Fin.sum_univ_three] at e01 e02 e10 e12 e20 e21 c02 c10
  have m01 : M 0 1 = 0 := aux (Ne.symm hττ2) e01
  have m02 : M 0 2 = 0 := aux (Ne.symm hτ1) (by rw [mul_one]; exact e02)
  have m10 : M 1 0 = 0 := aux hττ2 e10
  have m12 : M 1 2 = 0 := aux (Ne.symm hτ2) (by rw [mul_one]; exact e12)
  have m20 : M 2 0 = 0 := aux hτ1 (by rw [one_mul]; exact e20)
  have m21 : M 2 1 = 0 := aux hτ2 (by rw [one_mul]; exact e21)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m01, m02, m10, m12, m20, m21, c02, c10]

end Elements

section Centralizers

variable {K : Type} [Field K]

theorem mem_statedScalars_of_eq_smul {n : ℕ} {g : GL (Fin n) K} {a : K}
    (hg : (g : Matrix (Fin n) (Fin n) K) = a • (1 : Matrix (Fin n) (Fin n) K)) (ha : a ≠ 0) :
    g ∈ StatedScalars (Fin n) K := by
  refine ⟨Units.mk0 a ha, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, hg, Matrix.smul_one_eq_diagonal]
  rfl

theorem commute_of_mem_statedScalars {n : ℕ} {z : GL (Fin n) K}
    (hz : z ∈ StatedScalars (Fin n) K) (g : GL (Fin n) K) : g * z = z * g := by
  obtain ⟨c, rfl⟩ := hz
  exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c g).eq

theorem statedScalars_le_centralizer {n : ℕ} (S : Subgroup (GL (Fin n) K)) :
    StatedScalars (Fin n) K ≤ Subgroup.centralizer (S : Set (GL (Fin n) K)) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro g _
  exact commute_of_mem_statedScalars hz g

variable {p f : ℕ}

theorem mem_statedScalars_of_commute {π : Bool} (hπ : π = false → UnitaryFieldData p f K)
    (hq : π = false → ModThree false (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {g : GL (Fin 3) K} (hg : ∀ x ∈ slPi π 3 (p ^ f) K, g * x = x * g) :
    g ∈ StatedScalars (Fin 3) K := by
  have h1 := congrArg (fun y : GL (Fin 3) K => (y : Matrix (Fin 3) (Fin 3) K))
    (hg _ (diagTau_mem_slPi hπ hq hτ))
  have h2 := congrArg (fun y : GL (Fin 3) K => (y : Matrix (Fin 3) (Fin 3) K))
    (hg _ (cycThree_mem_slPi hπ))
  simp only [Units.val_mul] at h1 h2
  have hM := eq_smul_one_of_commute hτ hτ1 h1 h2
  refine mem_statedScalars_of_eq_smul hM fun h0 => ?_
  have hdet := congrArg Matrix.det hM
  rw [h0, zero_smul, det_zero] at hdet
  exact (g.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero hdet

theorem centralizer_slPi {π : Bool} (hπ : π = false → UnitaryFieldData p f K)
    (hq : π = false → ModThree false (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    Subgroup.centralizer (slPi π 3 (p ^ f) K : Set (GL (Fin 3) K)) =
      StatedScalars (Fin 3) K := by
  refine le_antisymm (fun g hg => ?_) (statedScalars_le_centralizer _)
  rw [Subgroup.mem_centralizer_iff] at hg
  exact mem_statedScalars_of_commute hπ hq hτ hτ1 fun x hx => (hg x hx).symm

theorem zPi_eq {π : Bool} (hπ : π = false → UnitaryFieldData p f K)
    (hq : π = false → ModThree false (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    zPi π 3 (p ^ f) K = glPi π 3 (p ^ f) K ⊓ StatedScalars (Fin 3) K := by
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, mem_statedScalars_of_commute hπ hq hτ hτ1 fun x hx => ?_⟩
    have hx' : x ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hx
    have := (Subgroup.mem_center_iff.mp hz) ⟨x, hx'⟩
    exact (congrArg Subtype.val this).symm
  · rintro ⟨hgH, hgZ⟩
    refine ⟨⟨g, hgH⟩, Subgroup.mem_center_iff.mpr fun x => Subtype.ext ?_, rfl⟩
    exact commute_of_mem_statedScalars hgZ (x : GL (Fin 3) K)

@[expose] def centMod {n : ℕ} (L : Subgroup (GL (Fin n) K)) (y : GL (Fin n) K) :
    Subgroup (GL (Fin n) K) :=
  L ⊓ (Subgroup.centralizer
    {(QuotientGroup.mk y : GL (Fin n) K ⧸ StatedScalars (Fin n) K)}).comap
      (QuotientGroup.mk' (StatedScalars (Fin n) K))

theorem mem_centMod_iff_scalar {n : ℕ} {L : Subgroup (GL (Fin n) K)} {y l : GL (Fin n) K} :
    l ∈ centMod L y ↔ l ∈ L ∧ ∃ z ∈ StatedScalars (Fin n) K, l * y * l⁻¹ = z * y := by
  have e : ∀ a b : GL (Fin n) K,
      QuotientGroup.mk' (StatedScalars (Fin n) K) a * QuotientGroup.mk' _ b =
        QuotientGroup.mk' _ b * QuotientGroup.mk' _ a ↔
      a * b * a⁻¹ * b⁻¹ ∈ StatedScalars (Fin n) K := fun a b => by
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, commutatorElement_def]
  rw [centMod, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun _ => ?_
  rw [show (QuotientGroup.mk y : GL (Fin n) K ⧸ StatedScalars (Fin n) K) =
    QuotientGroup.mk' _ y from rfl, e]
  constructor
  · intro h
    exact ⟨l * y * l⁻¹ * y⁻¹, h, by group⟩
  · rintro ⟨z, hz, hzy⟩
    rw [hzy, mul_inv_cancel_right]
    exact hz

theorem mem_centMod_iff {π : Bool} (hπ : π = false → UnitaryFieldData p f K)
    (hq : π = false → ModThree false (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {y l : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K) :
    l ∈ centMod (slPi π 3 (p ^ f) K) y ↔
      l ∈ slPi π 3 (p ^ f) K ∧ ∃ z ∈ zPi π 3 (p ^ f) K, l * y * l⁻¹ = z * y := by
  rw [mem_centMod_iff_scalar, zPi_eq hπ hq hτ hτ1]
  refine and_congr_right fun hl => ⟨fun ⟨z, hz, hzy⟩ => ⟨z, Subgroup.mem_inf.mpr ⟨?_, hz⟩, hzy⟩,
    fun ⟨z, hz, hzy⟩ => ⟨z, (Subgroup.mem_inf.mp hz).2, hzy⟩⟩
  have hl' := slPi_le_glPi hπ hl
  have : z = l * y * l⁻¹ * y⁻¹ := by rw [hzy, mul_inv_cancel_right]
  rw [this]
  exact mul_mem (mul_mem (mul_mem hl' hy) (inv_mem hl')) (inv_mem hy)

theorem inducesInner_iff {π : Bool} (hπ : π = false → UnitaryFieldData p f K)
    (hq : π = false → ModThree false (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {x : GL (Fin 3) K} (hx : x ∈ glPi π 3 (p ^ f) K) :
    (∃ l ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K, x * m * x⁻¹ = l * m * l⁻¹) ↔
      ∃ l ∈ slPi π 3 (p ^ f) K, ∃ z ∈ zPi π 3 (p ^ f) K, x = l * z := by
  rw [zPi_eq hπ hq hτ hτ1]
  constructor
  · rintro ⟨l, hl, hlx⟩
    refine ⟨l, hl, l⁻¹ * x, Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (slPi_le_glPi hπ hl)) hx, ?_⟩,
      by group⟩
    refine mem_statedScalars_of_commute hπ hq hτ hτ1 fun m hm => ?_
    have h := hlx m hm
    calc l⁻¹ * x * m = l⁻¹ * (x * m * x⁻¹) * x := by group
      _ = l⁻¹ * (l * m * l⁻¹) * x := by rw [h]
      _ = m * (l⁻¹ * x) := by group
  · rintro ⟨l, hl, z, hz, rfl⟩
    refine ⟨l, hl, fun m _ => ?_⟩
    have hc := commute_of_mem_statedScalars (Subgroup.mem_inf.mp hz).2 m
    calc l * z * m * (l * z)⁻¹ = l * (z * m) * z⁻¹ * l⁻¹ := by group
      _ = l * (m * z) * z⁻¹ * l⁻¹ := by rw [hc]
      _ = l * m * l⁻¹ := by group

end Centralizers

end CFSG.RankThree.PartTwo.Sec4
