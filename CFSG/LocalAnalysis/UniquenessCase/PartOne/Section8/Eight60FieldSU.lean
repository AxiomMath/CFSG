module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldAutOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldMatrix
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldSU2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldSUArith
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.CGT.Stroth77.L4Sylow.Sylow
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5SU2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix
open CFSG.Open (StatedProj StatedSL StatedSU StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

private theorem ringAut_eq_one_of_fixes_zeta {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hf : 1 ≤ f) (hK : Nat.card K = p ^ (2 * f))
    {ζ : K} (hζ : orderOf ζ = p ^ f + 1) (σ : RingAut K) (hσ : σ ζ = ζ) : σ = 1 := by
  let R := FixedPoints.subfield (Subgroup.zpowers σ) K
  have hcardeq : Nat.card K = Nat.card R ^ orderOf σ :=
    CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf K σ
  have hζR : ζ ∈ R := by
    show ζ ∈ MulAction.fixedPoints (Subgroup.zpowers σ) K
    intro g
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (RingAut K) ζ :=
      Subgroup.zpowers_le.mpr (by simpa using hσ)
    exact MulAction.mem_stabilizer_iff.mp (hle g.2)
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, orderOf_zero] at hζ
    omega
  have hdiv : p ^ f + 1 ∣ Nat.card R - 1 := by
    have : Fintype R := Fintype.ofFinite R
    have h1 : (⟨ζ, hζR⟩ : R) ^ (Fintype.card R - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one _ (by intro h; exact hζ0 (congrArg Subtype.val h))
    have h2 : (ζ : K) ^ (Fintype.card R - 1) = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    have hpow : ζ ^ (Nat.card R - 1) = 1 := by
      rw [Nat.card_eq_fintype_card]; exact h2
    have hdvd : orderOf ζ ∣ Nat.card R - 1 := orderOf_dvd_of_pow_eq_one hpow
    rwa [hζ] at hdvd
  have : Fintype R := Fintype.ofFinite R
  have : CharP R p := Subfield.charP R p
  obtain ⟨m, -, hRm⟩ := FiniteField.card R p
  have hRcard : Nat.card R = p ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hRm
  have hexp : 2 * f = (m : ℕ) * orderOf σ := by
    have h := hcardeq
    rw [hRcard, hK, ← pow_mul] at h
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h
  have hmdvd : (m : ℕ) ∣ 2 * f := ⟨orderOf σ, hexp⟩
  have hbound : f < (m : ℕ) := by
    by_contra hle
    push Not at hle
    have h1 : p ^ (m : ℕ) ≤ p ^ f := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hle
    have h2 : p ^ f + 1 ≤ p ^ (m : ℕ) - 1 := by
      have h := hdiv
      rw [hRcard] at h
      have hpos : 0 < p ^ (m : ℕ) - 1 := by
        have : 1 < p ^ (m : ℕ) := Nat.one_lt_pow m.ne_zero (Fact.out : p.Prime).one_lt
        omega
      exact Nat.le_of_dvd hpos h
    omega
  have hm_eq : (m : ℕ) = 2 * f := by
    obtain ⟨k, hk⟩ := hmdvd
    have hmpos : 0 < (m : ℕ) := m.pos
    have hklt : k < 2 := by
      have hlt : (m : ℕ) * k < (m : ℕ) * 2 := by
        have : 2 * f < 2 * (m : ℕ) := by omega
        rw [← hk]; omega
      exact (Nat.mul_lt_mul_left hmpos).mp hlt
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h
      · exfalso; rw [h0, mul_zero] at hk; omega
      · exact h
    have hk1 : k = 1 := by omega
    rw [hk1, mul_one] at hk
    omega
  have hord1 : orderOf σ = 1 := by
    have h := hexp
    rw [hm_eq] at h
    have h1 : 2 * f * 1 = 2 * f * orderOf σ := by rw [mul_one]; exact h
    exact (Nat.mul_left_cancel (by omega : 0 < 2 * f) h1).symm
  exact orderOf_eq_one_iff.mp hord1

private theorem exists_zeta {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ ζ : K, ζ ≠ 0 ∧ orderOf ζ = p ^ f + 1 ∧ ζ ^ (p ^ f + 1) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    charP_of_card_eq_prime_pow (f := 2 * f) (by rwa [Nat.card_eq_fintype_card] at hcard)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hne : p ^ f - 1 ≠ 0 := by
    have h2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    omega
  have hs : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
    simpa [pow_two] using Nat.mul_self_sub_mul_self_eq (p ^ f) 1
  have hdvd : p ^ f - 1 ∣ (p ^ f) ^ 2 - 1 := ⟨p ^ f + 1, by rw [hs, mul_comm]⟩
  have hgord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [hg, Nat.card_units, hK]
  let ζu : Kˣ := g ^ (p ^ f - 1)
  have hord : orderOf ζu = p ^ f + 1 := by
    dsimp only [ζu]
    rw [orderOf_pow' g hne, hgord, Nat.gcd_eq_right hdvd, hs,
      Nat.mul_div_cancel (p ^ f + 1) (Nat.pos_of_ne_zero hne)]
  refine ⟨(ζu : K), Units.ne_zero ζu, ?_, ?_⟩
  · exact (orderOf_injective (Units.coeHom K) Units.val_injective ζu).trans hord
  · rw [← hord]
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun u : Kˣ => (u : K)) (pow_orderOf_eq_one ζu)

private theorem exists_diag_mem_statedSU {m p f : ℕ} (hp : p.Prime)
    {K : Type} [Field K] [Finite K] {ζ : K}
    (hζ0 : ζ ≠ 0) (hroot : ζ ^ (p ^ f + 1) = 1) :
    ∃ A₀ : StatedSU (m + 2) (p ^ f) K,
      Matrix.trace ((A₀ : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) =
        ζ + ζ⁻¹ + (m : K) := by
  let v : Fin (m + 2) → K :=
    fun i => if i = 0 then ζ else if i = 1 then ζ⁻¹ else 1
  have hv0 : v 0 = ζ := by simp [v]
  have hv1 : v 1 = ζ⁻¹ := by simp [v]
  have hsucc0 : v ((0 : Fin (m + 1)).succ) = ζ⁻¹ := by
    rw [show ((0 : Fin (m + 1)).succ : Fin (m + 2)) = 1 from by ext; simp]
    exact hv1
  have hpoint : ∀ i, (v i) ^ (p ^ f) * v i = 1 := by
    intro i
    rw [← pow_succ]
    by_cases h0 : i = 0
    · have : v i = ζ := by simp [v, h0]
      rw [this, hroot]
    · by_cases h1 : i = 1
      · have : v i = ζ⁻¹ := by simp [v, h1]
        rw [this, inv_pow, hroot, inv_one]
      · have : v i = 1 := by simp [v, h0, h1]
        rw [this, one_pow]
  have htail : ∏ i : Fin m, v i.succ.succ = 1 := by
    apply Finset.prod_eq_one
    intro i _
    have h1 : (i.succ.succ : Fin (m + 2)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_zero] at this
      omega
    have h2 : (i.succ.succ : Fin (m + 2)) ≠ 1 := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_one] at this
      omega
    simp [v, h1, h2]
  have hprod : ∏ i : Fin (m + 2), v i = 1 := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, hv0, hsucc0, htail, mul_one,
      mul_inv_cancel₀ hζ0]
  have hdet : (diagonal v).det = 1 := by rw [det_diagonal, hprod]
  have hunit : ((diagonal v).map (· ^ (p ^ f)))ᵀ * diagonal v = 1 := by
    rw [diagonal_map (f := fun x : K => x ^ (p ^ f))
        (by exact zero_pow (pow_ne_zero f hp.ne_zero)), diagonal_transpose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact hpoint i
  have htrace : Matrix.trace (diagonal v) = ζ + ζ⁻¹ + (m : K) := by
    rw [Matrix.trace_diagonal, Fin.sum_univ_succ, Fin.sum_univ_succ]
    have hsum_tail : ∑ i : Fin m, v i.succ.succ = (m : K) := by
      have h1 : ∀ i : Fin m, v i.succ.succ = (1 : K) := by
        intro i
        have h0 : (i.succ.succ : Fin (m + 2)) ≠ 0 := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_succ, Fin.val_zero] at this
          omega
        have h2 : (i.succ.succ : Fin (m + 2)) ≠ 1 := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_succ, Fin.val_one] at this
          omega
        simp [v, h0, h2]
      rw [Finset.sum_congr rfl (fun i _ => h1 i)]
      simp
    rw [hv0, hsucc0, hsum_tail]
    ring
  refine ⟨⟨GeneralLinearGroup.mkOfDetNeZero (diagonal v) (by rw [hdet]; exact one_ne_zero),
    ?_⟩, ?_⟩
  · unfold StatedSU
    exact Subgroup.subset_closure ⟨hdet, hunit⟩
  · change Matrix.trace (diagonal v) = ζ + ζ⁻¹ + (m : K)
    exact htrace

open CFSG.Open (StatedScalars)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.GH71.S55.C5U
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Phan

private noncomputable def testBlocksHomSU {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : 4 ≤ m) :
    StatedSU 2 (p ^ f) K × StatedSU 2 (p ^ f) K →* StatedSU m (p ^ f) K :=
  MonoidHom.noncommCoprod (blkSU h 0 (by omega : 0 + 2 ≤ m)) (blkSU h 2 (by omega : 2 + 2 ≤ m))
    (fun A B => Subtype.ext (Units.ext (by
      change blockMat m 0 ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          blockMat m 2 ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          blockMat m 2 ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          blockMat m 0 ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      exact blockMat_comm (Or.inl (by omega : 0 + 2 ≤ 2)) _ _)))

private theorem testBlocksHomSU_apply {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : 4 ≤ m) (A B : StatedSU 2 (p ^ f) K) :
    testBlocksHomSU h hm (A, B) =
      blkSU h 0 (by omega : 0 + 2 ≤ m) A * blkSU h 2 (by omega : 2 + 2 ≤ m) B :=
  rfl

private theorem testBlocksHomSU_eq_one {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : 4 ≤ m) {A B : StatedSU 2 (p ^ f) K}
    (hAB : testBlocksHomSU h hm (A, B) = 1) : A = 1 ∧ B = 1 := by
  have e : blockGL m 0 (by omega : 0 + 2 ≤ m) (A : GL (Fin 2) K) *
      blockGL m 2 (by omega : 2 + 2 ≤ m) (B : GL (Fin 2) K) = 1 := by
    have := congrArg (fun x : StatedSU m (p ^ f) K => (x : GL (Fin m) K)) hAB
    simpa only [testBlocksHomSU_apply, Subgroup.coe_mul, Subgroup.coe_one, coe_blkSU,
      coe_blockGL] using this
  rw [mul_eq_one_iff_eq_inv, ← map_inv] at e
  have hA : (A : GL (Fin 2) K) = 1 := Units.ext (eq_one_of_blockMat_eq (by omega) le_rfl
    (congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) e))
  rw [hA, map_one, eq_comm, map_inv, inv_eq_one] at e
  have e' : blockMat m 2 ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      blockMat m 2 (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [blockMat_one]
    exact congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) e
  have hB : (B : GL (Fin 2) K) = 1 := Units.ext (blockMat_injective (by omega : 2 + 2 ≤ m) e')
  exact ⟨Subtype.ext hA, Subtype.ext hB⟩

private theorem testBlocksHomSU_injective {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : 4 ≤ m) :
    Function.Injective (testBlocksHomSU h hm) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨A, B⟩ hAB
  obtain ⟨hA, hB⟩ := testBlocksHomSU_eq_one h hm hAB
  exact Prod.ext hA hB

private theorem blockMat_map_SU {F F' : Type*} [Field F] [Field F'] (f : F →+* F') {m k i : ℕ}
    (A : Matrix (Fin k) (Fin k) F) : (blockMat m i A).map f = blockMat m i (A.map f) := by
  have hL : (blockSel F m k i).map f = blockSel F' m k i := by
    ext a j
    simp only [Matrix.map_apply, blockSel_apply]
    split_ifs <;> simp
  have hLt : ((blockSel F m k i)ᵀ).map f = (blockSel F' m k i)ᵀ := by
    rw [Matrix.transpose_map, hL]
  have hN : (A - 1).map f = A.map f - 1 := by
    rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]
  unfold blockMat
  rw [Matrix.map_add _ (map_add f), Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_mul,
    Matrix.map_mul, hL, hLt, hN]

private theorem map_blkSU {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m k i : ℕ} (hk : i + k ≤ m)
    (φ : K →+* K) {s : ℕ} (A : StatedSU k (p ^ f) K)
    (hA : Matrix.GeneralLinearGroup.map (n := Fin k) φ (A : GL (Fin k) K) =
      (A : GL (Fin k) K) ^ s) :
    Matrix.GeneralLinearGroup.map (n := Fin m) φ
        ((blkSU h i hk A : StatedSU m (p ^ f) K) : GL (Fin m) K) =
      (((blkSU h i hk A : StatedSU m (p ^ f) K) : GL (Fin m) K)) ^ s := by
  set M : Matrix (Fin k) (Fin k) K := ((A : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)
  have hAm : M.map φ = M ^ s := by
    ext a b
    have h1 := congrArg (fun z : GL (Fin k) K => (z : Matrix (Fin k) (Fin k) K) a b) hA
    rw [Matrix.GeneralLinearGroup.map_apply] at h1
    simpa only [Matrix.map_apply, Units.val_pow_eq_pow_val, M] using h1
  have hx : (((blkSU h i hk A : StatedSU m (p ^ f) K) : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) = blockMat m i M := by
    rw [coe_blkSU, coe_blockGL]
  apply Units.ext
  ext a b
  rw [Matrix.GeneralLinearGroup.map_apply, hx]
  change φ (blockMat m i M a b) = (blockMat m i M ^ s) a b
  have hpow : (blockMat m i M) ^ s = blockMat m i (M ^ s) :=
    (map_pow (blockMatHom m i hk) M s).symm
  rw [← Matrix.map_apply (M := blockMat m i M) (f := φ), blockMat_map_SU φ, hAm, hpow]

private theorem map_testBlocksHomSU {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : 4 ≤ m) (φ : K →+* K) {s : ℕ}
    {A B : StatedSU 2 (p ^ f) K}
    (hA : Matrix.GeneralLinearGroup.map (n := Fin 2) φ (A : GL (Fin 2) K) =
      (A : GL (Fin 2) K) ^ s)
    (hB : Matrix.GeneralLinearGroup.map (n := Fin 2) φ (B : GL (Fin 2) K) =
      (B : GL (Fin 2) K) ^ s) :
    Matrix.GeneralLinearGroup.map (n := Fin m) φ
        ((testBlocksHomSU h hm (A, B) : StatedSU m (p ^ f) K) : GL (Fin m) K) =
      (((testBlocksHomSU h hm (A, B) : StatedSU m (p ^ f) K) : GL (Fin m) K)) ^ s := by
  have h1 := map_blkSU h (by omega : 0 + 2 ≤ m) φ A hA
  have h2 := map_blkSU h (by omega : 2 + 2 ≤ m) φ B hB
  have hcomm : Commute ((blkSU h 0 (by omega : 0 + 2 ≤ m) A : StatedSU m (p ^ f) K) :
        GL (Fin m) K)
      ((blkSU h 2 (by omega : 2 + 2 ≤ m) B : StatedSU m (p ^ f) K) : GL (Fin m) K) := by
    refine Units.ext ?_
    rw [Units.val_mul, coe_blkSU, coe_blockGL]
    exact blockMat_comm (Or.inl (by omega : 0 + 2 ≤ 2)) _ _
  rw [testBlocksHomSU_apply, Subgroup.coe_mul, map_mul, h1, h2, hcomm.mul_pow s]

private noncomputable def testBHomSU {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : 4 ≤ m)
    {C : Subgroup (GL (Fin 2) K)} (hC : C ≤ StatedSU 2 (p ^ f) K) :
    C × C →* StatedSU m (p ^ f) K :=
  (testBlocksHomSU h hm).comp
    (((Subgroup.inclusion hC).comp (MonoidHom.fst C C)).prod
      ((Subgroup.inclusion hC).comp (MonoidHom.snd C C)))

private theorem testBHomSU_injective {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : 4 ≤ m)
    {C : Subgroup (GL (Fin 2) K)} (hC : C ≤ StatedSU 2 (p ^ f) K) :
    Function.Injective (testBHomSU h hm hC) := by
  intro x y hxy
  have h1 := testBlocksHomSU_injective h hm hxy
  exact Prod.ext (Subgroup.inclusion_injective hC (Prod.ext_iff.mp h1).1)
    (Subgroup.inclusion_injective hC (Prod.ext_iff.mp h1).2)

private theorem map_testBHomSU {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : 4 ≤ m) (φ : K →+* K)
    {C : Subgroup (GL (Fin 2) K)} (hC : C ≤ StatedSU 2 (p ^ f) K) {s : ℕ}
    (hCmap : ∀ g ∈ C, Matrix.GeneralLinearGroup.map (n := Fin 2) φ g = g ^ s) (x : C × C) :
    Matrix.GeneralLinearGroup.map (n := Fin m) φ
        ((testBHomSU h hm hC x : StatedSU m (p ^ f) K) : GL (Fin m) K) =
      (((testBHomSU h hm hC x : StatedSU m (p ^ f) K) : GL (Fin m) K)) ^ s :=
  map_testBlocksHomSU h hm φ (hCmap x.1 x.1.2) (hCmap x.2 x.2.2)

theorem exists_abelian_sylow_power_map_statedSU {n p f : ℕ} (hn : n = 4 ∨ n = 5)
    (hp : p.Prime) (hf : 1 ≤ f) (hq : p ^ f % 3 = 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (φ : RingAut K)
    (hφ : ∀ x : K, φ x = x ^ ((p ^ (f / 3 ^ (f.factorization 3))) ^ 2)) :
    ∃ (Q : Sylow 3 (StatedProj (StatedSU n (p ^ f) K))) (s : ℕ),
      (∀ x ∈ (Q : Subgroup (StatedProj (StatedSU n (p ^ f) K))),
        ∀ y ∈ (Q : Subgroup (StatedProj (StatedSU n (p ^ f) K))), x * y = y * x) ∧
      s % 3 = 1 ∧
      ∀ τ : MulAut (StatedProj (StatedSU n (p ^ f) K)),
        IsFieldMapQuot (StatedSU n (p ^ f) K) φ τ →
        ∀ x ∈ (Q : Subgroup (StatedProj (StatedSU n (p ^ f) K))), τ x = x ^ s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨C, s, hCsyl, hCcyc, hs, hCmap⟩ :=
    exists_stable_cyclic_sylow_three_statedSU_two hp hf hq hK φ hφ
  have : IsMulCommutative C := hCcyc.isMulCommutative
  have hCcard : Nat.card C = 3 ^ (Nat.card (StatedSU 2 (p ^ f) K)).factorization 3 :=
    hCsyl.card_eq
  rcases hn with rfl | rfl
  · let hm4 : 4 ≤ 4 := by omega
    have hcard : Nat.card (C × C) =
        3 ^ (Nat.card (StatedSU 4 (p ^ f) K)).factorization 3 := by
      rw [Nat.card_prod, hCcard, ← pow_add,
        factorization_three_card_statedSU_eq_two_mul (Or.inl rfl) hp hf hq hK]
      congr 1
      ring
    have hbHinj : Function.Injective (testBHomSU h hm4 hCsyl.le) :=
      testBHomSU_injective h hm4 hCsyl.le
    let N : Subgroup (StatedSU 4 (p ^ f) K) :=
      (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K)
    have : N.Normal := inferInstance
    obtain ⟨Q, hQ⟩ :=
      CFSG.CGT.Stroth77.L4Sylow.exists_sylow_quotient_eq_range N
        (testBHomSU h hm4 hCsyl.le) hbHinj hcard
    refine ⟨Q, s, ?_, hs, ?_⟩
    · intro x hx y hy
      rw [hQ] at hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      rw [← map_mul, ← map_mul]
      have : IsMulCommutative (C × C) := inferInstance
      exact congrArg ((QuotientGroup.mk' N).comp (testBHomSU h hm4 hCsyl.le)) (mul_comm' a b)
    · intro τ hτ x hx
      rw [hQ] at hx
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨h', hh', hτh⟩ := hτ (testBHomSU h hm4 hCsyl.le a)
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hτh]
      have hhpow : h' = (testBHomSU h hm4 hCsyl.le a) ^ s := by
        apply Subtype.ext
        rw [Subgroup.coe_pow]
        apply Units.ext
        rw [hh', Units.val_pow_eq_pow_val]
        exact congrArg (fun z : GL (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K))
          (map_testBHomSU h hm4 (φ : K →+* K) hCsyl.le hCmap a)
      rw [hhpow]
      exact map_pow (QuotientGroup.mk' N) (testBHomSU h hm4 hCsyl.le a) s
  · let hm5 : 4 ≤ 5 := by omega
    have hcard : Nat.card (C × C) =
        3 ^ (Nat.card (StatedSU 5 (p ^ f) K)).factorization 3 := by
      rw [Nat.card_prod, hCcard, ← pow_add,
        factorization_three_card_statedSU_eq_two_mul (Or.inr rfl) hp hf hq hK]
      congr 1
      ring
    have hbHinj : Function.Injective (testBHomSU h hm5 hCsyl.le) :=
      testBHomSU_injective h hm5 hCsyl.le
    let N : Subgroup (StatedSU 5 (p ^ f) K) :=
      (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (p ^ f) K)
    have : N.Normal := inferInstance
    obtain ⟨Q, hQ⟩ :=
      CFSG.CGT.Stroth77.L4Sylow.exists_sylow_quotient_eq_range N
        (testBHomSU h hm5 hCsyl.le) hbHinj hcard
    refine ⟨Q, s, ?_, hs, ?_⟩
    · intro x hx y hy
      rw [hQ] at hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      rw [← map_mul, ← map_mul]
      have : IsMulCommutative (C × C) := inferInstance
      exact congrArg ((QuotientGroup.mk' N).comp (testBHomSU h hm5 hCsyl.le)) (mul_comm' a b)
    · intro τ hτ x hx
      rw [hQ] at hx
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨h', hh', hτh⟩ := hτ (testBHomSU h hm5 hCsyl.le a)
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hτh]
      have hhpow : h' = (testBHomSU h hm5 hCsyl.le a) ^ s := by
        apply Subtype.ext
        rw [Subgroup.coe_pow]
        apply Units.ext
        rw [hh', Units.val_pow_eq_pow_val]
        exact congrArg (fun z : GL (Fin 5) K => (z : Matrix (Fin 5) (Fin 5) K))
          (map_testBHomSU h hm5 (φ : K →+* K) hCsyl.le hCmap a)
      rw [hhpow]
      exact map_pow (QuotientGroup.mk' N) (testBHomSU h hm5 hCsyl.le a) s

theorem exists_test_element_statedSU {n p f : ℕ} (hn : n = 4 ∨ n = 5) (hp : p.Prime)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ a : K, (∀ σ : RingAut K, σ a = a → σ = 1) ∧
      ∃ A₀ : StatedSU n (p ^ f) K,
        Matrix.trace (((A₀ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
          a + a⁻¹ + ((n - 2 : ℕ) : K) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    charP_of_card_eq_prime_pow (f := 2 * f) (by rwa [Nat.card_eq_fintype_card] at hK')
  obtain ⟨ζ, hζ0, hζord, hroot⟩ := exists_zeta hp hf hK
  refine ⟨ζ, fun σ hσ => ringAut_eq_one_of_fixes_zeta hf hK' hζord σ hσ, ?_⟩
  rcases hn with rfl | rfl
  · obtain ⟨A₀, hA₀⟩ := exists_diag_mem_statedSU (m := 2) hp hζ0 hroot
    exact ⟨A₀, by simpa using hA₀⟩
  · obtain ⟨A₀, hA₀⟩ := exists_diag_mem_statedSU (m := 3) hp hζ0 hroot
    exact ⟨A₀, by simpa using hA₀⟩

theorem three_pow_dvd_of_pow_mem_inner_statedSU {n p f : ℕ} (hn : n = 4 ∨ n = 5)
    (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (φ : RingAut K)
    (hφ : ∀ x : K, φ x = x ^ ((p ^ (f / 3 ^ (f.factorization 3))) ^ 2))
    (τ : MulAut (StatedProj (StatedSU n (p ^ f) K)))
    (hτ : IsFieldMapQuot (StatedSU n (p ^ f) K) φ τ)
    (j : ℕ) (hj : τ ^ j ∈ inner (StatedProj (StatedSU n (p ^ f) K))) :
    3 ^ (f.factorization 3) ∣ j := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    charP_of_card_eq_prime_pow (f := 2 * f) (by rwa [Nat.card_eq_fintype_card] at hK')
  let b := f.factorization 3
  let f₀ := f / 3 ^ b
  let A := (p ^ f₀) ^ 2
  have h3dvd : 3 ^ b ∣ f := by
    dsimp only [b]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega : f ≠ 0)).mpr le_rfl
  have hb : 3 ^ b * f₀ = f := by
    dsimp only [f₀]
    exact Nat.mul_div_cancel' h3dvd
  have hAe : f₀ * 2 * 3 ^ b = 2 * f := by
    rw [Nat.mul_assoc, Nat.mul_comm 2 (3 ^ b), ← Nat.mul_assoc, Nat.mul_comm f₀ (3 ^ b), hb,
      Nat.mul_comm f 2]
  have hA : A ^ 3 ^ b = p ^ (2 * f) := by
    dsimp only [A]
    rw [← pow_mul, ← pow_mul, ← Nat.mul_assoc, hAe]
  have hperf : Group.IsPerfect (StatedSU n (p ^ f) K) := by
    rcases hn with rfl | rfl
    · exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by norm_num)
        (by intro hh; exact absurd (congrArg Prod.fst hh) (by norm_num))
    · exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by norm_num)
        (by intro hh; exact absurd (congrArg Prod.fst hh) (by norm_num))
  have hφpow : ∀ k : ℕ, ∀ x : K, (φ ^ k) x = x ^ (A ^ k) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ]
        change (φ ^ k) (φ x) = x ^ (A ^ (k + 1))
        rw [ih (φ x), hφ x, ← pow_mul]
        congr 1
        rw [mul_comm, ← pow_succ]
  have hxpow : ∀ x : K, x ^ (p ^ f) ^ 2 = x := by
    intro x
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hφ3 : φ ^ 3 ^ b = 1 := by
    ext x
    rw [hφpow (3 ^ b) x, hA]
    have hx2 : x ^ p ^ (2 * f) = x := by
      rw [show p ^ (2 * f) = (p ^ f) ^ 2 by rw [← pow_mul, mul_comm]]
      exact hxpow x
    simpa using hx2
  have hφodd : Odd (orderOf φ) :=
    Odd.of_dvd_nat (Odd.pow (by norm_num : Odd 3)) (orderOf_dvd_of_pow_eq_one hφ3)
  obtain ⟨a, ha, A₀, hA₀⟩ := exists_test_element_statedSU hn hp hf hK
  have hφj : φ ^ j = 1 :=
    pow_eq_one_of_pow_mem_inner (StatedSU n (p ^ f) K) hperf φ hφodd a ha (n - 2) A₀ hA₀ τ hτ j hj
  have hfix : ∀ x : K, x ^ (A ^ j) = x := by
    intro x
    have := hφpow j x
    rw [hφj] at this
    exact this.symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hgord : orderOf g = (p ^ f) ^ 2 - 1 := by rw [hg, Nat.card_units, hK]
  have hgunit : g ^ (A ^ j) = g := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val] using hfix (g : K)
  have hf0pos : 0 < f₀ := by
    by_contra h
    rw [Nat.not_lt, Nat.le_zero] at h
    rw [h, mul_zero] at hb
    omega
  have hA2 : 2 ≤ A := by
    have h2 : 2 ≤ p ^ f₀ := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    dsimp only [A]
    nlinarith
  have hA1 : 1 ≤ A := by omega
  have hgunit' : g ^ (A ^ j - 1) = 1 := by
    have h2 : g ^ (A ^ j - 1) * g = 1 * g := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow j A hA1), hgunit, one_mul]
    exact mul_right_cancel h2
  have hdvd : orderOf g ∣ A ^ j - 1 := orderOf_dvd_iff_pow_eq_one.mpr hgunit'
  have hA' : A ^ 3 ^ b = (p ^ f) ^ 2 := by rw [hA, ← pow_mul, mul_comm]
  have hdiv : A ^ 3 ^ b - 1 ∣ A ^ j - 1 := by
    rw [hA', ← hgord]
    exact hdvd
  have hres := dvd_of_pow_sub_one_dvd_pow_sub_one (q₀ := A) (m := 3 ^ b) (j := j) hA2
    (Nat.pow_pos (by norm_num)) hdiv
  change 3 ^ b ∣ j
  exact hres

private theorem phi_pow_factorization_eq_one {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (φ : RingAut K)
    (hφ : ∀ x : K, φ x = x ^ ((p ^ (f / 3 ^ (f.factorization 3))) ^ 2)) :
    φ ^ 3 ^ (f.factorization 3) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  let b := f.factorization 3
  let f₀ := f / 3 ^ b
  let A := (p ^ f₀) ^ 2
  have h3dvd : 3 ^ b ∣ f := by
    dsimp only [b]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega : f ≠ 0)).mpr le_rfl
  have hb : 3 ^ b * f₀ = f := by
    dsimp only [f₀]
    exact Nat.mul_div_cancel' h3dvd
  have hAe : f₀ * 2 * 3 ^ b = 2 * f := by
    rw [Nat.mul_assoc, Nat.mul_comm 2 (3 ^ b), ← Nat.mul_assoc, Nat.mul_comm f₀ (3 ^ b), hb,
      Nat.mul_comm f 2]
  have hA : A ^ 3 ^ b = p ^ (2 * f) := by
    dsimp only [A]
    rw [← pow_mul, ← pow_mul, ← Nat.mul_assoc, hAe]
  have hφpow : ∀ k : ℕ, ∀ x : K, (φ ^ k) x = x ^ (A ^ k) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ]
        change (φ ^ k) (φ x) = x ^ (A ^ (k + 1))
        rw [ih (φ x), hφ x, ← pow_mul]
        congr 1
        rw [mul_comm, ← pow_succ]
  have hxpow : ∀ x : K, x ^ (p ^ f) ^ 2 = x := by
    intro x
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  ext x
  rw [hφpow (3 ^ b) x, hA]
  have hx2 : x ^ p ^ (2 * f) = x := by
    rw [show p ^ (2 * f) = (p ^ f) ^ 2 by rw [← pow_mul, mul_comm]]
    exact hxpow x
  simpa using hx2

theorem fieldSylowData_statedSU {n p f : ℕ} (hn : n = 4 ∨ n = 5) (hp : p.Prime) (hf : 1 ≤ f)
    (hq : p ^ f % 3 = 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) :
    FieldSylowData (StatedProj (StatedSU n (p ^ f) K)) (f.factorization 3) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    charP_of_card_eq_prime_pow (f := 2 * f) (by rwa [Nat.card_eq_fintype_card] at hK')
  obtain ⟨φ, hφ0⟩ := exists_ringAut_pow_of_charP (K := K) (p := p) (2 * (f / 3 ^ (f.factorization 3)))
  have hφ : ∀ x : K, φ x = x ^ ((p ^ (f / 3 ^ (f.factorization 3))) ^ 2) := by
    intro x
    rw [hφ0 x]
    congr 1
    rw [← pow_mul]
    congr 1
    ring
  have hmap : Subgroup.map (Matrix.GeneralLinearGroup.map φ.toRingHom) (StatedSU n (p ^ f) K) ≤
      StatedSU n (p ^ f) K := by
    unfold StatedSU
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro A ⟨B, hB, rfl⟩
    apply Subgroup.subset_closure
    constructor
    · have hdetB : Matrix.GeneralLinearGroup.det B = 1 := by
        ext; simpa using hB.1
      have h := Matrix.GeneralLinearGroup.map_det (f := φ.toRingHom) B
      rw [hdetB] at h
      have h2 := congrArg (fun u : Kˣ => (u : K)) h
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using h2
    · have hcoe : ((Matrix.GeneralLinearGroup.map φ.toRingHom B : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K).map φ := rfl
      rw [hcoe]
      have hmat : (((B : Matrix (Fin n) (Fin n) K).map φ).map (· ^ (p ^ f)))ᵀ *
          (B : Matrix (Fin n) (Fin n) K).map φ =
          (((B : Matrix (Fin n) (Fin n) K).map (· ^ (p ^ f)))ᵀ *
            (B : Matrix (Fin n) (Fin n) K)).map φ := by
        rw [Matrix.map_mul, Matrix.transpose_map]
        congr 2
        ext i j
        simp [map_pow]
      rw [hmat, hB.2, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hH : ∀ g ∈ StatedSU n (p ^ f) K, Matrix.GeneralLinearGroup.map φ.toRingHom g ∈
      StatedSU n (p ^ f) K :=
    fun g hg => hmap (Subgroup.mem_map_of_mem _ hg)
  obtain ⟨τ, hτ⟩ := exists_isFieldMapQuot (StatedSU n (p ^ f) K) φ hH
  obtain ⟨Q, s, hQab, hs, hQmap⟩ :=
    exists_abelian_sylow_power_map_statedSU hn hp hf hq hK φ hφ
  have hφ3 : φ ^ 3 ^ (f.factorization 3) = 1 := phi_pow_factorization_eq_one hf hK φ hφ
  have hτ3 : τ ^ 3 ^ (f.factorization 3) = 1 := by
    have h := isFieldMapQuot_pow hτ (3 ^ (f.factorization 3))
    rw [hφ3] at h
    exact eq_one_of_isFieldMapQuot_one h
  refine ⟨Q, τ, s, hQab, hs, ?_, hτ3, ?_⟩
  · intro x hx
    exact hQmap τ hτ x hx
  · intro j hj
    exact three_pow_dvd_of_pow_mem_inner_statedSU hn hp hf hK φ hφ τ hτ j hj

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
