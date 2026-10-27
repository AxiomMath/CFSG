module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniLift
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeU6Cube
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniSplit
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeU6Par
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOutCube
import CFSG.Assembly.GL83StatedBridge
import CFSG.LieType.BorelTits.UnitaryForm
import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockRestrict
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

section Helpers

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups


private theorem isHermIsometry_iff_stdHermForm {K : Type} [Field K] {f n : ℕ}
    (h : UnitaryFieldData 2 f K) {A : Matrix (Fin n) (Fin n) K} :
    IsHermIsometry (2 ^ f) A ↔
      ∀ x y, stdHermForm h n (A *ᵥ x) (A *ᵥ y) = stdHermForm h n x y := by
  simp only [IsHermIsometry, stdHermForm_apply, h.bar_apply]

private theorem isHermIsometry_mul {K : Type} [Field K] {q n : ℕ}
    {A B : Matrix (Fin n) (Fin n) K} (hA : IsHermIsometry q A) (hB : IsHermIsometry q B) :
    IsHermIsometry q (A * B) := by
  intro v w
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact (hA (B *ᵥ v) (B *ᵥ w)).trans (hB v w)

private theorem isHermIsometry_of_mem_SU {K : Type} [Field K] [Finite K] [CharP K 2]
    {q n : ℕ} (hK : Nat.card K = q ^ 2) {g : GL (Fin n) K}
    (hg : g ∈ LargeEvenSUGroup (Fin n) K q) :
    IsHermIsometry q (g : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  have h : UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  rw [isHermIsometry_iff_stdHermForm h]
  have hgU : g ∈ unitarySU 2 f K n := by
    rw [unitarySU, ← CFSG.Assembly.largeEvenSUGroup_eq_statedSU]
    exact hg
  exact ((mem_unitarySU_iff_isometry h).mp hgU).2

private theorem isHermIsometry_inv {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ}
    (hK : Nat.card K = q ^ 2) {g : GL (Fin n) K}
    (hg : IsHermIsometry q (g : Matrix (Fin n) (Fin n) K)) :
    IsHermIsometry q ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  have h : UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  rw [isHermIsometry_iff_stdHermForm h] at hg ⊢
  intro x y
  have h1 := hg ((g⁻¹ : GL (Fin n) K) *ᵥ x) ((g⁻¹ : GL (Fin n) K) *ᵥ y)
  have e1 : (g : Matrix (Fin n) (Fin n) K) *ᵥ ((g⁻¹ : GL (Fin n) K) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have e2 : (g : Matrix (Fin n) (Fin n) K) *ᵥ ((g⁻¹ : GL (Fin n) K) *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  rw [e1, e2] at h1
  exact h1.symm

private theorem isHermIsometry_mem_normalizer {K : Type} [Field K] [Finite K] [CharP K 2]
    {q n : ℕ} (hK : Nat.card K = q ^ 2) {g : GL (Fin n) K}
    (hg : IsHermIsometry q (g : Matrix (Fin n) (Fin n) K)) :
    g ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin n) K q : Set (GL (Fin n) K)) := by
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  have h : UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  have hgStd := (isHermIsometry_iff_stdHermForm h).mp hg
  have hbar : (⇑h.bar : K → K) = fun x => x ^ (2 ^ f) := funext fun x => h.bar_apply x
  have hmat : ((g : Matrix (Fin n) (Fin n) K).map (· ^ (2 ^ f)))ᵀ *
      (g : Matrix (Fin n) (Fin n) K) = 1 := by
    have hmap := CFSG.StandardType.SUTB.map_bar_transpose_mul_of_isometry h hgStd
    simpa only [hbar] using hmap
  have hgu : g ∈ LargeEvenGUSet (Fin n) K (2 ^ f) := by
    refine ⟨1, one_ne_zero, by simp, ?_⟩
    simpa using hmat
  exact CFSG.StandardType.TableBUE.gu_subset_normalizer (n := f) (d := n) h hgu

private theorem scalar_mulVec {K : Type} [Field K] {n : ℕ} (c : K) (v : Fin n → K) :
    Matrix.scalar (Fin n) c *ᵥ v = c • v := by
  ext i
  rw [Matrix.mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply]; simp
  · intro b _ hb
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    simp [Ne.symm hb]

private theorem isHermIsometry_scalar {K : Type} [Field K] {q n : ℕ} {c : K}
    (hc : c ^ q * c = 1) :
    IsHermIsometry q (Matrix.scalar (Fin n) c) := by
  intro v w
  rw [scalar_mulVec, scalar_mulVec]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_pow,
    show c ^ q * v i ^ q * (c * w i) = (c ^ q * c) * (v i ^ q * w i) by ring,
    hc, one_mul]

private theorem smul_eq_scalar_mul {K : Type} [Field K] {n : ℕ} (c : K)
    (A : Matrix (Fin n) (Fin n) K) : c • A = Matrix.scalar (Fin n) c * A := by
  rw [Matrix.smul_eq_diagonal_mul, Matrix.scalar_apply]

private theorem scalar_eq_smul_one {K : Type} [Field K] {n : ℕ} (c : K) :
    Matrix.scalar (Fin n) c = c • (1 : Matrix (Fin n) (Fin n) K) := by
  rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul, Matrix.mul_one]

private theorem isHermIsometry_smul {K : Type} [Field K] {q n : ℕ} {c : K}
    (hc : c ^ q * c = 1) {A : Matrix (Fin n) (Fin n) K} (hA : IsHermIsometry q A) :
    IsHermIsometry q (c • A) := by
  rw [smul_eq_scalar_mul]
  exact isHermIsometry_mul (isHermIsometry_scalar hc) hA

private theorem smul_pow_mat {K : Type} [Field K] {n : ℕ} (c : K)
    (d : Matrix (Fin n) (Fin n) K) (k : ℕ) : (c • d) ^ k = c ^ k • d ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ, pow_succ]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm c (c ^ k)]

private theorem mul_inv_mul_inv_central {G : Type} [Group G] {x y z w : G}
    (hz : ∀ a, z * a = a * z) (hw : ∀ a, w * a = a * w) :
    x * z * (y * w) * (x * z)⁻¹ * (y * w)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
  have h1 : z * y = y * z := hz y
  have h2 : z * w = w * z := hz w
  have h3 : w * x⁻¹ = x⁻¹ * w := hw x⁻¹
  calc x * z * (y * w) * (z⁻¹ * x⁻¹) * (w⁻¹ * y⁻¹)
      = x * (z * y) * w * z⁻¹ * x⁻¹ * w⁻¹ * y⁻¹ := by group
    _ = x * (y * z) * w * z⁻¹ * x⁻¹ * w⁻¹ * y⁻¹ := by rw [h1]
    _ = x * y * (z * w) * z⁻¹ * x⁻¹ * w⁻¹ * y⁻¹ := by group
    _ = x * y * (w * z) * z⁻¹ * x⁻¹ * w⁻¹ * y⁻¹ := by rw [h2]
    _ = x * y * w * x⁻¹ * w⁻¹ * y⁻¹ := by group
    _ = x * y * (w * x⁻¹) * w⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * w) * w⁻¹ * y⁻¹ := by rw [h3]
    _ = x * y * x⁻¹ * y⁻¹ := by group

private theorem isConjBy_mul {n q : ℕ} {K : Type} [Field K] {g g' : GL (Fin n) K}
    {a a' : MulAut (PSUg n K q)}
    (hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q,
      g' * k * g'⁻¹ ∈ LargeEvenSUGroup (Fin n) K q)
    (h1 : IsConjBy g a) (h2 : IsConjBy g' a') : IsConjBy (g * g') (a * a') := by
  intro x x' hx
  let x'' : ↥(LargeEvenSUGroup (Fin n) K q) :=
    ⟨g' * (x : GL (Fin n) K) * g'⁻¹, hnorm x x.2⟩
  have hx'' : (x'' : GL (Fin n) K) = g' * (x : GL (Fin n) K) * g'⁻¹ := rfl
  have h2' : a' (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x'' := h2 x x'' hx''
  have h1' : a (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x'') =
      LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x' :=
    h1 x'' x' (by
      show (x' : GL (Fin n) K) = g * (x'' : GL (Fin n) K) * g⁻¹
      rw [hx, hx'']
      group)
  calc (a * a') (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x)
      = a (a' (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x)) := rfl
    _ = a (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x'') := by rw [h2']
    _ = LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x' := h1'

private theorem isConjBy_inv {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a : MulAut (PSUg n K q)} (h1 : IsConjBy g a) : IsConjBy g⁻¹ a⁻¹ := by
  intro x x' hx
  have hrel : (x : GL (Fin n) K) = g * (x' : GL (Fin n) K) * g⁻¹ := by rw [hx]; group
  have h := h1 x' x hrel
  calc a⁻¹ (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x)
      = a⁻¹ (a (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x')) := by rw [← h]
    _ = LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x' := by
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

private theorem isConjBy_one {n q : ℕ} {K : Type} [Field K] :
    IsConjBy (1 : GL (Fin n) K) (1 : MulAut (PSUg n K q)) := by
  intro x x' hx
  have hxx : x' = x := Subtype.ext (by simpa using hx)
  subst hxx
  rw [MulAut.one_apply]

private theorem isConjBy_pow {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a : MulAut (PSUg n K q)}
    (hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q,
      g * k * g⁻¹ ∈ LargeEvenSUGroup (Fin n) K q)
    (h : IsConjBy g a) : ∀ m : ℕ, IsConjBy (g ^ m) (a ^ m)
  | 0 => by simpa using (isConjBy_one (n := n) (q := q) (K := K))
  | m + 1 => by
      have ih := isConjBy_pow hnorm h m
      simpa [pow_succ] using isConjBy_mul hnorm ih h

private theorem isConjBy_zpow {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a : MulAut (PSUg n K q)}
    (hN : g ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin n) K q : Set (GL (Fin n) K)))
    (h : IsConjBy g a) (m : ℤ) : IsConjBy (g ^ m) (a ^ m) := by
  have hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q,
      g * k * g⁻¹ ∈ LargeEvenSUGroup (Fin n) K q :=
    fun k hk => (Subgroup.mem_normalizer_iff.mp hN k).mp hk
  have hnorm_inv : ∀ k ∈ LargeEvenSUGroup (Fin n) K q,
      g⁻¹ * k * (g⁻¹)⁻¹ ∈ LargeEvenSUGroup (Fin n) K q :=
    fun k hk => (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) k).mp hk
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg m
  · rw [hk, zpow_natCast, zpow_natCast]
    exact isConjBy_pow hnorm h k
  · rw [hk, _root_.zpow_neg, zpow_natCast, _root_.zpow_neg, zpow_natCast]
    exact isConjBy_inv (isConjBy_pow hnorm h k)

private theorem isConjBy_mul_central_iff {n q : ℕ} {K : Type} [Field K] {s : GL (Fin n) K}
    (hs : ∀ x : GL (Fin n) K, s * x = x * s) {A : GL (Fin n) K}
    {a : MulAut (PSUg n K q)} : IsConjBy (s * A) a ↔ IsConjBy A a := by
  have hrel_eq : ∀ x : GL (Fin n) K, (s * A) * x * (s * A)⁻¹ = A * x * A⁻¹ := by
    intro x
    rw [_root_.mul_inv_rev]
    calc (s * A) * x * (A⁻¹ * s⁻¹) = s * (A * x * A⁻¹) * s⁻¹ := by group
      _ = A * x * A⁻¹ := by rw [hs]; group
  constructor
  · intro h x x' hx
    exact h x x' (by
      show (x' : GL (Fin n) K) = (s * A) * (x : GL (Fin n) K) * (s * A)⁻¹
      rw [hx, hrel_eq x])
  · intro h x x' hx
    exact h x x' (by
      show (x' : GL (Fin n) K) = A * (x : GL (Fin n) K) * A⁻¹
      rw [hx, ← hrel_eq x])

private theorem isConjBy_eq {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a a' : MulAut (PSUg n K q)}
    (hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q,
      g * k * g⁻¹ ∈ LargeEvenSUGroup (Fin n) K q)
    (h : IsConjBy g a) (h' : IsConjBy g a') : a = a' := by
  ext y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin n) K).subgroupOf (LargeEvenSUGroup (Fin n) K q)) y
  subst hx
  let x' : ↥(LargeEvenSUGroup (Fin n) K q) :=
    ⟨g * (x : GL (Fin n) K) * g⁻¹, hnorm x x.2⟩
  have hx' : (x' : GL (Fin n) K) = g * (x : GL (Fin n) K) * g⁻¹ := rfl
  rw [h x x' hx', h' x x' hx']

private theorem isConjBy_scalar_one {n q : ℕ} {K : Type} [Field K] (c : Kˣ) :
    IsConjBy (Matrix.GeneralLinearGroup.scalar (Fin n) c)
      (1 : MulAut (PSUg n K q)) := by
  have hs : ∀ x : GL (Fin n) K, Matrix.GeneralLinearGroup.scalar (Fin n) c * x =
      x * Matrix.GeneralLinearGroup.scalar (Fin n) c :=
    fun x => Matrix.GeneralLinearGroup.scalar_commute c x
  simpa using (isConjBy_mul_central_iff (n := n) (q := q)
    (s := Matrix.GeneralLinearGroup.scalar (Fin n) c) hs
    (A := (1 : GL (Fin n) K)) (a := (1 : MulAut (PSUg n K q)))).mpr
    (isConjBy_one (n := n) (q := q) (K := K))

private theorem ker_projMk_le_center {K : Type} [Field K] {n q : ℕ} :
    (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q)).ker ≤
      Subgroup.center ↥(LargeEvenSUGroup (Fin n) K q) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hx' : x ∈ (LargeEvenScalars (Fin n) K).subgroupOf (LargeEvenSUGroup (Fin n) K q) := by
    have := hx
    rwa [show (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q)).ker =
        (LargeEvenScalars (Fin n) K).subgroupOf (LargeEvenSUGroup (Fin n) K q) from
      QuotientGroup.ker_mk' _] at this
  have hx'' : (x : GL (Fin n) K) ∈ LargeEvenScalars (Fin n) K :=
    Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨c, hc⟩ := hx''
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
  exact (Matrix.GeneralLinearGroup.scalar_commute c (y : GL (Fin n) K)).symm

end Helpers

theorem uni6_kg7_on_R_holds : Uni6KG7OnR := by
  unfold Uni6KG7OnR
  intro K _ _ _ q hK hq3 Ā δ' J' hR hAcard hĀI hA1
  rintro ⟨U, hUne, hU2, hUnorm⟩
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨Ahat, hL, hAcardAhat⟩ := uni_lift hK (by norm_num : 4 ≤ 6) hĀI
  let SU : Subgroup (GL (Fin 6) K) := LargeEvenSUGroup (Fin 6) K q
  have hiso : ∀ a ∈ Ahat, IsHermIsometry q (a : Matrix (Fin 6) (Fin 6) K) := hL.iso
  have hscal : ∀ c : Kˣ, c ^ (q + 1) = 1 →
      Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ Ahat := hL.scalars
  have hnorm_of : ∀ {g : GL (Fin 6) K}, IsHermIsometry q (g : Matrix (Fin 6) (Fin 6) K) →
      ∀ k ∈ SU, g * k * g⁻¹ ∈ SU :=
    fun {g} hg k hk =>
      (Subgroup.mem_normalizer_iff.mp (isHermIsometry_mem_normalizer hK hg) k).mp hk
  obtain ⟨d, hdA, hdconj⟩ := hL.onto δ' hR.mem
  have hδ3 : δ' ^ 3 = 1 := hR.elem.2 δ' hR.mem
  have hd3conj : IsConjBy (d ^ 3) (1 : MulAut (PSUg 6 K q)) := by
    have h := isConjBy_pow (hnorm_of (hiso d hdA)) hdconj 3
    rwa [hδ3] at h
  obtain ⟨c0, hc0norm, hd3eq⟩ :=
    hL.ker (d ^ 3) (Subgroup.pow_mem _ hdA 3) hd3conj
  let lam : K := (c0 : K)
  have hlamnorm : lam ^ (q + 1) = 1 := by
    have h : ((c0 : K)) ^ (q + 1) = 1 := by
      simpa using congrArg (fun x : Kˣ => (x : K)) hc0norm
    exact h
  have hd3mat : (d : Matrix (Fin 6) (Fin 6) K) ^ 3 =
      lam • (1 : Matrix (Fin 6) (Fin 6) K) := by
    have hthis : (d : Matrix (Fin 6) (Fin 6) K) ^ 3 =
        Matrix.scalar (Fin 6) (c0 : K) := by
      have := congrArg (fun x : GL (Fin 6) K => (x : Matrix (Fin 6) (Fin 6) K)) hd3eq
      simpa [Matrix.GeneralLinearGroup.coe_scalar] using this
    rw [hthis]
    change Matrix.scalar (Fin 6) (c0 : K) = (c0 : K) • (1 : Matrix (Fin 6) (Fin 6) K)
    exact scalar_eq_smul_one (c0 : K)
  have hlam : ∀ μ : K, μ ^ 3 ≠ lam := by
    intro μ hμ
    have hlam0 : lam ≠ 0 := by
      intro hl0
      rw [hl0, zero_pow (by omega : q + 1 ≠ 0)] at hlamnorm
      exact zero_ne_one hlamnorm
    have hμ0 : μ ≠ 0 := by
      intro h0
      apply hlam0
      rw [← hμ, h0, zero_pow (by norm_num : 3 ≠ 0)]
    have hμq2 : μ ^ (q ^ 2) = μ := by
      have hcard : μ ^ (q ^ 2 - 1) = 1 := by
        have h := FiniteField.pow_card_sub_one_eq_one μ hμ0
        rw [Fintype.card_eq_nat_card, hK] at h
        exact h
      have hq1 : 1 ≤ q ^ 2 := by
        have hpos : 0 < Nat.card K := Nat.card_pos
        rw [hK] at hpos
        exact hpos
      calc μ ^ (q ^ 2) = μ ^ (q ^ 2 - 1 + 1) := by rw [Nat.sub_add_cancel hq1]
        _ = μ ^ (q ^ 2 - 1) * μ := by rw [pow_succ]
        _ = μ := by rw [hcard, one_mul]
    have hx3 : (μ ^ (q + 1)) ^ 3 = 1 := by
      rw [← pow_mul, show (q + 1) * 3 = 3 * (q + 1) by ring, pow_mul, hμ, hlamnorm]
    have hxq : (μ ^ (q + 1)) ^ q = μ ^ (q + 1) := by
      rw [← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add, hμq2, ← pow_succ']
    have hq2 : 2 ≤ q := by
      have h2 : 2 ≤ Nat.card K := by
        have := Finite.one_lt_card (α := K)
        omega
      by_contra hcon
      have hqle : q ≤ 1 := by omega
      have : q ^ 2 ≤ 1 := by nlinarith [Nat.zero_le q]
      omega
    obtain ⟨k, hk⟩ : ∃ k : ℕ, q = 3 * k + 2 := by
      obtain ⟨m, hm⟩ := hq3
      exact ⟨m - 1, by omega⟩
    have hx1 : μ ^ (q + 1) = 1 := by
      have hx2 : μ ^ (q + 1) = (μ ^ (q + 1)) ^ 2 := by
        calc μ ^ (q + 1) = (μ ^ (q + 1)) ^ q := hxq.symm
          _ = (μ ^ (q + 1)) ^ (3 * k + 2) := by rw [hk]
          _ = ((μ ^ (q + 1)) ^ 3) ^ k * (μ ^ (q + 1)) ^ 2 := by rw [pow_add, pow_mul]
          _ = (μ ^ (q + 1)) ^ 2 := by rw [hx3, one_pow, one_mul]
      have hx0 : μ ^ (q + 1) ≠ 0 := by
        intro h0
        rw [h0] at hx3
        have h01 : (0 : K) = 1 := by simpa using hx3
        exact zero_ne_one h01
      have hcancel : μ ^ (q + 1) * 1 = μ ^ (q + 1) * μ ^ (q + 1) := by
        rw [mul_one]
        exact hx2.trans (pow_two _)
      exact (mul_left_cancel₀ hx0 hcancel).symm
    let u : Kˣ := Units.mk0 μ hμ0
    have hu : (u : K) = μ := rfl
    let d' : GL (Fin 6) K := Matrix.GeneralLinearGroup.scalar (Fin 6) u⁻¹ * d
    have hd'mat : (d' : Matrix (Fin 6) (Fin 6) K) =
        (↑u⁻¹ : K) • (d : Matrix (Fin 6) (Fin 6) K) := by
      show ((Matrix.GeneralLinearGroup.scalar (Fin 6) u⁻¹ * d : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = (↑u⁻¹ : K) • (d : Matrix (Fin 6) (Fin 6) K)
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        smul_eq_scalar_mul]
    have huinv : (↑u⁻¹ : K) = μ⁻¹ := by simp [u]
    have hc : (↑u⁻¹ : K) ^ q * (↑u⁻¹ : K) = 1 := by
      rw [huinv, inv_pow, ← _root_.mul_inv_rev, ← pow_succ', hx1, inv_one]
    have hd'iso : IsHermIsometry q (d' : Matrix (Fin 6) (Fin 6) K) := by
      rw [hd'mat]
      exact isHermIsometry_smul hc (hiso d hdA)
    have hd'3 : d' ^ 3 = 1 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one]
      rw [hd'mat, smul_pow_mat, hd3mat, smul_smul]
      have hc3 : (↑u⁻¹ : K) ^ 3 * lam = 1 := by
        rw [huinv, inv_pow, hμ]
        exact inv_mul_cancel₀ hlam0
      rw [hc3, one_smul]
    have hd'conj : IsConjBy d' δ' := by
      show IsConjBy (Matrix.GeneralLinearGroup.scalar (Fin 6) u⁻¹ * d) δ'
      exact (isConjBy_mul_central_iff
        (s := Matrix.GeneralLinearGroup.scalar (Fin 6) u⁻¹)
        (fun x => Matrix.GeneralLinearGroup.scalar_commute u⁻¹ x)).mpr hdconj
    have hd'n : ∀ c : K, (d' : Matrix (Fin 6) (Fin 6) K) ≠
        c • (1 : Matrix (Fin 6) (Fin 6) K) := by
      intro c hc
      have hc0 : c ≠ 0 := by
        intro h0
        have hzero : (d' : Matrix (Fin 6) (Fin 6) K) = 0 := by rw [hc, h0, zero_smul]
        have h01 : (1 : Matrix (Fin 6) (Fin 6) K) = 0 := by
          have hmul := mul_inv_cancel d'
          have hcongr := congrArg (fun z : GL (Fin 6) K =>
            (z : Matrix (Fin 6) (Fin 6) K)) hmul
          rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv,
            hzero, zero_mul, Units.val_one] at hcongr
          exact hcongr.symm
        exact one_ne_zero h01
      let w : Kˣ := Units.mk0 c hc0
      have hd'eq : d' = Matrix.GeneralLinearGroup.scalar (Fin 6) w := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_eq_smul_one]
        exact hc
      have h1 : IsConjBy d' (1 : MulAut (PSUg 6 K q)) :=
        hd'eq ▸ isConjBy_scalar_one w
      exact hR.ne_one (isConjBy_eq (hnorm_of hd'iso) hd'conj h1)
    obtain ⟨F, hFfield, hFfinite, hFcard, hA1iso⟩ := hA1
    letI : Field F := hFfield
    letI : Finite F := hFfinite
    exact uni6_cube_impossible hK hq3 hd'iso hd'3 hd'n hd'conj hR.comp hR.uniq hFcard hA1iso
  have hcomm : ∀ a ∈ Ahat, ∀ b ∈ Ahat, ∃ c : Kˣ, c ^ (q + 1) = 1 ∧
      a * b * a⁻¹ * b⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    intro a ha b hb
    obtain ⟨ā, hā, haconj⟩ := hL.induces a ha
    obtain ⟨bhat, hbhat, hbconj⟩ := hL.induces b hb
    have h1 : IsConjBy (a * b) (ā * bhat) :=
      isConjBy_mul (hnorm_of (hiso b hb)) haconj hbconj
    have h2 : IsConjBy (a * b * a⁻¹) (ā * bhat * ā⁻¹) :=
      isConjBy_mul (hnorm_of (isHermIsometry_inv hK (hiso a ha))) h1 (isConjBy_inv haconj)
    have h3 : IsConjBy (a * b * a⁻¹ * b⁻¹) (ā * bhat * ā⁻¹ * bhat⁻¹) :=
      isConjBy_mul (hnorm_of (isHermIsometry_inv hK (hiso b hb))) h2 (isConjBy_inv hbconj)
    have hcommĀ : ā * bhat * ā⁻¹ * bhat⁻¹ = 1 := by
      have hcm : ā * bhat = bhat * ā :=
        congrArg Subtype.val (hR.elem.1.is_comm.comm ⟨ā, hā⟩ ⟨bhat, hbhat⟩)
      calc ā * bhat * ā⁻¹ * bhat⁻¹ = bhat * ā * ā⁻¹ * bhat⁻¹ := by rw [hcm]
        _ = 1 := by group
    rw [hcommĀ] at h3
    exact hL.ker _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)) h3
  have hcube : ∀ a ∈ Ahat, ∃ c : Kˣ, c ^ (q + 1) = 1 ∧
      a ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    intro a ha
    obtain ⟨ā, hā, haconj⟩ := hL.induces a ha
    have hā3 : ā ^ 3 = 1 := hR.elem.2 ā hā
    have h3 : IsConjBy (a ^ 3) (1 : MulAut (PSUg 6 K q)) := by
      have h := isConjBy_pow (hnorm_of (hiso a ha)) haconj 3
      rwa [hā3] at h
    exact hL.ker (a ^ 3) (Subgroup.pow_mem _ ha 3) h3
  have hcard : 3 ^ 3 * (q + 1) ≤ Nat.card Ahat := by
    rw [hAcardAhat, hAcard]
  have hker : ∀ a ∈ Ahat, (∀ g : GL (Fin 6) K,
      IsHermIsometry q (g : Matrix (Fin 6) (Fin 6) K) → g * d = d * g → a * g = g * a) →
      ∃ (k : ℤ) (c : Kˣ), c ^ (q + 1) = 1 ∧
        a = d ^ k * Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    intro a ha hacomm
    obtain ⟨ā, hā, haconj⟩ := hL.induces a ha
    let π : ↥SU →* PSUg 6 K q := LargeEvenProjMk SU
    let cR : Subgroup (PSUg 6 K q) := ggAutFixedSubgroup δ'
    let H : Subgroup ↥SU := cR.comap π
    let conjHom : ↥SU →* ↥SU :=
      { toFun := fun x => ⟨d * (x : GL (Fin 6) K) * d⁻¹, hnorm_of (hiso d hdA) x x.2⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := by
          intro x y
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subtype.coe_mk]
          group }
    let Cd : Subgroup ↥SU :=
      { carrier := {h | d * (h : GL (Fin 6) K) * d⁻¹ = (h : GL (Fin 6) K)}
        one_mem' := by simp
        mul_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [Subgroup.coe_mul]
          calc d * ((x : GL (Fin 6) K) * (y : GL (Fin 6) K)) * d⁻¹
              = (d * (x : GL (Fin 6) K) * d⁻¹) * (d * (y : GL (Fin 6) K) * d⁻¹) := by
                group
            _ = (x : GL (Fin 6) K) * (y : GL (Fin 6) K) := by rw [hx, hy]
        inv_mem' := by
          intro x hx
          simp only [Set.mem_setOf_eq] at hx ⊢
          rw [Subgroup.coe_inv]
          calc d * (x : GL (Fin 6) K)⁻¹ * d⁻¹ = (d * (x : GL (Fin 6) K) * d⁻¹)⁻¹ := by
                group
            _ = (x : GL (Fin 6) K)⁻¹ := by rw [hx] }
    have hψVal_mem : ∀ h : H, (h : ↥SU)⁻¹ * conjHom (h : ↥SU) ∈ π.ker := by
      intro h
      rw [MonoidHom.mem_ker]
      show π ((h : ↥SU)⁻¹ * conjHom (h : ↥SU)) = 1
      rw [map_mul, map_inv]
      have hconj : π (conjHom (h : ↥SU)) = π (h : ↥SU) := by
        have hmem : π (h : ↥SU) ∈ cR := Subgroup.mem_comap.mp h.2
        have hfix := (mem_ggAutFixedSubgroup δ' (π (h : ↥SU))).mp hmem
        have hcc := hdconj (h : ↥SU) (conjHom (h : ↥SU)) (by rfl)
        rw [← hcc, hfix]
      rw [hconj, inv_mul_cancel]
    have hψVal_center : ∀ h : H, (h : ↥SU)⁻¹ * conjHom (h : ↥SU) ∈
        Subgroup.center ↥SU := fun h => ker_projMk_le_center (hψVal_mem h)
    have hHmap : H.map π = cR := by
      ext x
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact Subgroup.mem_comap.mp hh
      · intro hx
        obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
          ((LargeEvenScalars (Fin 6) K).subgroupOf SU) x
        exact Subgroup.mem_map.mpr ⟨h, Subgroup.mem_comap.mpr hx, rfl⟩
    have hCd : ⁅H, H⁆ ≤ Cd := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [commutatorElement_def]
      have hxker : x⁻¹ * conjHom x ∈ π.ker := hψVal_mem ⟨x, hx⟩
      have hyker : y⁻¹ * conjHom y ∈ π.ker := hψVal_mem ⟨y, hy⟩
      have hxcent : x⁻¹ * conjHom x ∈ Subgroup.center ↥SU := ker_projMk_le_center hxker
      have hycent : y⁻¹ * conjHom y ∈ Subgroup.center ↥SU := ker_projMk_le_center hyker
      have hxeq : conjHom x = x * (x⁻¹ * conjHom x) := by group
      have hyeq : conjHom y = y * (y⁻¹ * conjHom y) := by group
      have hcomm : conjHom x * conjHom y * (conjHom x)⁻¹ * (conjHom y)⁻¹
          = x * y * x⁻¹ * y⁻¹ := by
        rw [hxeq, hyeq]
        exact mul_inv_mul_inv_central
          (fun a => (Subgroup.mem_center_iff.mp hxcent a).symm)
          (fun a => (Subgroup.mem_center_iff.mp hycent a).symm)
      have hconj_eq : conjHom (x * y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ := by
        simp only [map_mul, map_inv]
        exact hcomm
      show d * ((x * y * x⁻¹ * y⁻¹ : ↥SU) : GL (Fin 6) K) * d⁻¹ =
        ((x * y * x⁻¹ * y⁻¹ : ↥SU) : GL (Fin 6) K)
      simpa [conjHom] using congrArg Subtype.val hconj_eq
    have hJcomm : ⁅J', J'⁆ = J' := by
      rw [← Subgroup.map_subtype_commutator J', hR.comp.2.2.1, Subgroup.map_top,
        Subgroup.subtype_range]
    have hJle : J' ≤ Cd.map π := by
      calc J' = ⁅J', J'⁆ := hJcomm.symm
        _ ≤ ⁅cR, cR⁆ := Subgroup.commutator_mono hR.comp.1 hR.comp.1
        _ = ⁅H.map π, H.map π⁆ := by rw [hHmap]
        _ = (⁅H, H⁆).map π := (Subgroup.map_commutator H H π).symm
        _ ≤ Cd.map π := Subgroup.map_mono hCd
    have hfix : ∀ x ∈ J', ā x = x := by
      intro x hx
      obtain ⟨h, hhCd, hπh⟩ := Subgroup.mem_map.mp (hJle hx)
      have hcomm_dh : (h : GL (Fin 6) K) * d = d * (h : GL (Fin 6) K) := by
        have := congrArg (fun z : GL (Fin 6) K => z * d) hhCd
        simpa [mul_assoc] using this.symm
      have hh_iso : IsHermIsometry q ((h : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) :=
        isHermIsometry_of_mem_SU hK h.2
      have hah : a * (h : GL (Fin 6) K) = (h : GL (Fin 6) K) * a :=
        hacomm (h : GL (Fin 6) K) hh_iso hcomm_dh
      let h' : ↥SU := ⟨a * (h : GL (Fin 6) K) * a⁻¹, hnorm_of (hiso a ha) h h.2⟩
      have hπh' : ā (π h) = π h' := haconj h h' rfl
      have hh'val : (h' : GL (Fin 6) K) = (h : GL (Fin 6) K) := by
        show a * (h : GL (Fin 6) K) * a⁻¹ = (h : GL (Fin 6) K)
        rw [hah]; group
      calc ā x = ā (π h) := by rw [← hπh]
        _ = π h' := hπh'
        _ = π h := by
              apply congrArg π
              apply Subtype.ext
              exact hh'val
        _ = x := hπh
    have hāzp : ā ∈ Subgroup.zpowers δ' := hR.ker ā hā hfix
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hāzp
    have hdk : IsConjBy (d ^ k) ā := by
      have h := isConjBy_zpow (isHermIsometry_mem_normalizer hK (hiso d hdA)) hdconj k
      rwa [hk] at h
    have hnorm_dk_inv : ∀ x ∈ SU, ((d ^ k)⁻¹) * x * ((d ^ k)⁻¹)⁻¹ ∈ SU := by
      intro x hx
      have hN : (d ^ k)⁻¹ ∈ Subgroup.normalizer (SU : Set (GL (Fin 6) K)) :=
        Subgroup.inv_mem _ (zpow_mem
          (isHermIsometry_mem_normalizer hK (hiso d hdA)) k)
      exact (Subgroup.mem_normalizer_iff.mp hN x).mp hx
    have hprod : IsConjBy (a * (d ^ k)⁻¹) (1 : MulAut (PSUg 6 K q)) := by
      have h := isConjBy_mul hnorm_dk_inv haconj (isConjBy_inv hdk)
      simpa using h
    obtain ⟨c, hc, hceq⟩ := hL.ker (a * (d ^ k)⁻¹)
      (Subgroup.mul_mem _ ha (Subgroup.inv_mem _ (zpow_mem hdA k))) hprod
    refine ⟨k, c, hc, ?_⟩
    calc a = (a * (d ^ k)⁻¹) * (d ^ k) := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) c * (d ^ k) := by rw [hceq]
      _ = (d ^ k) * Matrix.GeneralLinearGroup.scalar (Fin 6) c :=
            Matrix.GeneralLinearGroup.scalar_commute c (d ^ k)
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  let φ : K →+* K := CFSG.LieType.BorelTits.unitaryInvolution K 2 f
  have hφ : ∀ x, φ x = x ^ q := by
    intro x
    rw [hq]
    exact CFSG.LieType.BorelTits.unitaryInvolution_apply K 2 f x
  rcases uni_split hK (by norm_num : 4 ≤ 6) φ hφ hĀI hL hUne hU2 hUnorm with hpar | hout
  · obtain ⟨W, hWne, hWiso, hWstab⟩ := hpar
    exact u6_par_impossible hK hq3 Ahat hiso hscal hcomm hcube hcard d hdA lam hd3mat
      hlam hker ⟨W, hWne, hWiso, hWstab⟩
  · obtain ⟨B, hBiso, hBconj⟩ := hout
    obtain ⟨c, hc, hconj⟩ := hBconj d hdA
    obtain ⟨μ, hμ⟩ := outCube_of_conj (q := q) (n := 6) (by norm_num) φ hφ hlamnorm
      hd3mat ⟨B, rfl⟩ (by
        simpa only [Matrix.GeneralLinearGroup.coe_mul,
          CFSG.SeitzReduction.F4Pilot.coe_map_GL φ d,
          Matrix.GeneralLinearGroup.coe_inv, Matrix.GeneralLinearGroup.coe_scalar,
          ← smul_eq_scalar_mul] using
          congrArg (fun z : GL (Fin 6) K => (z : Matrix (Fin 6) (Fin 6) K)) hconj)
    exact hlam μ hμ

end CFSG.StandardType.TablePThreeKG

end
