module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddModel
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFour
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.Adapters.RankTwoModelTransports
import CFSG.Adapters.LinearFieldTransport
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.SubgroupLists.FieldThreeFamilies
import CFSG.RankThree.SubgroupLists.ThreeSquareExclusion
import CFSG.RankThree.SubgroupLists.CentralThreeLift
import CFSG.RankThree.SubgroupLists2.SpectralBounds
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LieType.Steinberg.CentralExt.UnitaryField
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedScalars StatedProj StatedSU StatedSL
  projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

theorem nonempty_projSL_of_statedClassicalModel {G : Type} [Group G] {n p f : ℕ} [Fact p.Prime]
    (h : StatedClassicalModel G .PSL n p f) : Nonempty (G ≃* projSL n (GaloisField p f)) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have hf : 0 < f := hadm.2.1
  let φ : K ≃+* GaloisField p f := CFSG.ClassicalModels.finiteFieldEquivGaloisField K p f hf hK
  exact ⟨e.trans (CFSG.RankThree.PartOne.statedProjEquivOfGLEquiv
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSL φ n)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
    (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL n _))⟩

theorem nonempty_projSU_of_statedClassicalModel {G : Type} [Group G] {n p f : ℕ} [Fact p.Prime]
    (h : StatedClassicalModel G .PSU n p f) : Nonempty (G ≃* projSU n p f) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have hf1 : 1 ≤ f := hadm.2.1
  have hf : 0 < 2 * f := by omega
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let φ : K ≃+* GaloisField p (2 * f) :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField K p (2 * f) hf hK'
  exact ⟨e.trans (CFSG.RankThree.PartOne.statedProjEquivOfGLEquiv
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ n (p ^ f))
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
    (CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU n p f))⟩

theorem false_of_rational {K : Type*} [Field K] [Finite K] {H : Subgroup (GL (Fin 3) K)}
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1) {r : ℕ} [Fact r.Prime] (hr5 : 5 ≤ r)
    (hrK : (r : K) ≠ 0) {s : H ⧸ Subgroup.center H} (hs : s ^ r = 1) (hs1 : s ≠ 1)
    (hconj : ∀ n : ℕ, 1 ≤ n → n < r → IsConj s (s ^ n)) : False := by
  have hr : r.Prime := Fact.out
  have hn : Nat.Coprime r 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h3
    omega
  obtain ⟨x, hxs, hxr⟩ := SubgroupLists.exists_lift_pow_eq_one le_rfl hZ3 hn s hs
  set X : GL (Fin 3) K := (x : GL (Fin 3) K) with hX
  have hXr : X ^ r = 1 := by rw [hX, ← Subgroup.coe_pow, hxr, Subgroup.coe_one]
  have hX1 : X ≠ 1 := by
    intro h
    apply hs1
    rw [← hxs, show x = 1 from Subtype.ext h, QuotientGroup.mk_one]
  have hXc : ∀ n : ℕ, 1 ≤ n → n < r → IsConj X (X ^ n) := by
    intro n hn1 hnr
    have hxn : (x ^ n) ^ r = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxr, one_pow]
    have h := SubgroupLists.isConj_of_isConj_mk le_rfl hZ3 hn hxr hxn
      (by rw [QuotientGroup.mk_pow, hxs]; exact hconj n hn1 hnr)
    have h' := H.subtype.map_isConj h
    rwa [map_pow] at h'
  set Q : Finset (ZMod r) := Finset.univ.erase 0 with hQ
  have hQc : Q.card = r - 1 := by
    rw [hQ, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hle := SubgroupLists.card_le_three_of_isConj_pow hrK hXr hX1 Q (fun k hk => by
    have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
    refine ⟨hk0, hXc k.val ?_ (ZMod.val_lt k)⟩
    rcases Nat.eq_zero_or_pos k.val with h | h
    · exact absurd ((ZMod.val_eq_zero k).mp h) hk0
    · exact h)
  omega

theorem exists_rational_psl3 {F : Type} [Field F] {r : ℕ} [Fact r.Prime] [CharP F r] :
    ∃ s : ProjectiveSpecialLinearGroup (Fin 3) F, s ^ r = 1 ∧ s ≠ 1 ∧
      ∀ n : ℕ, 1 ≤ n → n < r → IsConj s (s ^ n) := by
  have hr : r.Prime := Fact.out
  let T : F → SL(3, F) := fun c => ⟨!![1, 0, c; 0, 1, 0; 0, 0, 1], by
    simp [Matrix.det_fin_three]⟩
  have hTmul : ∀ a b : F, T a * T b = T (a + b) := by
    intro a b
    apply Subtype.ext
    change !![(1 : F), 0, a; 0, 1, 0; 0, 0, 1] * !![(1 : F), 0, b; 0, 1, 0; 0, 0, 1] =
      !![1, 0, a + b; 0, 1, 0; 0, 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]
  have hT0 : T 0 = 1 := by
    apply Subtype.ext
    change !![(1 : F), 0, 0; 0, 1, 0; 0, 0, 1] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hTpow : ∀ n : ℕ, T 1 ^ n = T n := by
    intro n
    induction n with
    | zero => rw [pow_zero, Nat.cast_zero, hT0]
    | succ n ih => rw [pow_succ, ih, hTmul, Nat.cast_succ]
  set π := QuotientGroup.mk' (Subgroup.center SL(3, F)) with hπ
  refine ⟨π (T 1), ?_, ?_, ?_⟩
  · rw [← map_pow, hTpow, CharP.cast_eq_zero, hT0, map_one]
  · intro h
    have hc : T 1 ∈ Subgroup.center SL(3, F) := (QuotientGroup.eq_one_iff _).mp h
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at hc
    obtain ⟨c, -, hc⟩ := hc
    have h1 := congrFun (congrFun hc 0) 2
    simp [T] at h1
  · intro n hn1 hnr
    have hn0 : (n : F) ≠ 0 := by
      intro h
      have := (CharP.cast_eq_zero_iff F r n).mp h
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    let D : SL(3, F) := ⟨!![(n : F), 0, 0; 0, (n : F)⁻¹, 0; 0, 0, 1], by
      simp [Matrix.det_fin_three, hn0]⟩
    refine isConj_iff.mpr ⟨π D, ?_⟩
    rw [← map_pow, hTpow, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    change !![(n : F), 0, 0; 0, (n : F)⁻¹, 0; 0, 0, 1] * !![(1 : F), 0, 1; 0, 1, 0; 0, 0, 1] =
      !![(1 : F), 0, (n : F); 0, 1, 0; 0, 0, 1] * !![(n : F), 0, 0; 0, (n : F)⁻¹, 0; 0, 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

section Unitary

variable {K : Type} [Field K] [Finite K] {r f : ℕ} [Fact r.Prime] [CharP K r]

@[expose] noncomputable def diagSU (σ : K ≃+* K) (l : Kˣ) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mk'' (diagonal ![(l : K), σ l / l, (σ l)⁻¹]) (by
    have h0 : (l : K) ≠ 0 := l.ne_zero
    have h1 : σ (l : K) ≠ 0 := (map_ne_zero σ).mpr h0
    simp [det_diagonal, Fin.prod_univ_three, h0, h1])

theorem coe_diagSU (σ : K ≃+* K) (l : Kˣ) :
    ((diagSU σ l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(l : K), σ l / l, (σ l)⁻¹] :=
  rfl

theorem diagSU_mem_SU (σ : K ≃+* K) (hσ : ∀ x, σ (σ x) = x) (l : Kˣ) : diagSU σ l ∈ SU σ 3 := by
  have h0 : (l : K) ≠ 0 := l.ne_zero
  have h1 : σ (l : K) ≠ 0 := (map_ne_zero σ).mpr h0
  refine ⟨?_, ?_⟩
  · rw [coe_diagSU, det_diagonal, Fin.prod_univ_three]
    simp
    field_simp
  · rw [coe_diagSU, SubgroupLists.antidiag_three]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_three, diagonal, hσ, map_div₀, map_inv₀] <;>
      field_simp

theorem diagSU_mul_unipGL (σ : K ≃+* K) (l : Kˣ) (c : K) :
    diagSU σ l * SubgroupLists.unipGL σ 0 c =
      SubgroupLists.unipGL σ 0 (σ l * l * c) * diagSU σ l := by
  have h0 : (l : K) ≠ 0 := l.ne_zero
  have h1 : σ (l : K) ≠ 0 := (map_ne_zero σ).mpr h0
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagSU, SubgroupLists.coe_unipGL,
    SubgroupLists.coe_unipGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SubgroupLists.unipMat, Matrix.mul_apply, Fin.sum_univ_three, diagonal] <;> field_simp

theorem exists_unitaryInvolution_ne (hf : 1 ≤ f) (hK : Nat.card K = (r ^ f) ^ 2) :
    ∃ b : K, unitaryInvolution K r f b ≠ b := by
  by_contra hno
  push Not at hno
  have hcard := CFSG.LieType.Steinberg.card_fixedSubfield (F := K) (p := r) (f := f) hK
  have hall : ∀ w : K, w ∈ CFSG.LieType.Steinberg.fixedSubfield K r f := fun w => hno w
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), hK] at hcard
  have h1 : 1 < r ^ f := Nat.one_lt_pow (by omega) (Fact.out : r.Prime).one_lt
  nlinarith

theorem exists_rational_psu3 (hf : 1 ≤ f) (hK : Nat.card K = (r ^ f) ^ 2) :
    ∃ s : StatedProj (StatedSU 3 (r ^ f) K), s ^ r = 1 ∧ s ≠ 1 ∧
      ∀ n : ℕ, 1 ≤ n → n < r → IsConj s (s ^ n) := by
  classical
  have hr : r.Prime := Fact.out
  set σ := unitaryInvolution K r f with hσdef
  have hσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hK
  obtain ⟨b, hb⟩ := exists_unitaryInvolution_ne hf hK
  set c₀ := σ b - b with hc₀
  have hc₀0 : c₀ ≠ 0 := sub_ne_zero.mpr hb
  have hz : ∀ k : ℕ, (k : K) * c₀ + σ ((k : K) * c₀) + 0 * σ 0 = 0 := by
    intro k
    rw [map_mul, map_natCast, hc₀, map_sub, hσ, zero_mul, add_zero]
    ring
  let Z : ℕ → SU σ 3 := fun k =>
    ⟨SubgroupLists.unipGL σ 0 ((k : K) * c₀), SubgroupLists.unipGL_mem_SU σ hσ (hz k)⟩
  have hZpow : ∀ k : ℕ, Z 1 ^ k = Z k := by
    intro k
    induction k with
    | zero =>
      apply Subtype.ext
      rw [pow_zero, Subgroup.coe_one]
      change 1 = SubgroupLists.unipGL σ 0 (((0 : ℕ) : K) * c₀)
      rw [Nat.cast_zero, zero_mul, SubgroupLists.unipGL_zero_zero]
    | succ k ih =>
      apply Subtype.ext
      rw [pow_succ, ih, Subgroup.coe_mul]
      change SubgroupLists.unipGL σ 0 ((k : K) * c₀) * SubgroupLists.unipGL σ 0 (((1 : ℕ) : K) * c₀) =
        SubgroupLists.unipGL σ 0 (((k + 1 : ℕ) : K) * c₀)
      rw [SubgroupLists.unipGL_mul]
      exact SubgroupLists.unipGL_congr σ (by ring) (by push_cast; ring)
  set e := equivStatedSU (p := r) (f := f) hK 3 with he
  set π := QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (r ^ f) K))
    with hπ
  set Φ : SU σ 3 →* StatedProj (StatedSU 3 (r ^ f) K) := π.comp e.toMonoidHom with hΦ
  refine ⟨Φ (Z 1), ?_, ?_, ?_⟩
  · rw [← map_pow, hZpow]
    have : Z r = 1 := by
      apply Subtype.ext
      change SubgroupLists.unipGL σ 0 ((r : K) * c₀) = 1
      rw [CharP.cast_eq_zero, zero_mul, SubgroupLists.unipGL_zero_zero]
    rw [this, map_one]
  · intro h
    change π (e (Z 1)) = 1 at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    obtain ⟨μ, hμ⟩ := h
    have hpow : ((e (Z 1) : StatedSU 3 (r ^ f) K) : GL (Fin 3) K) ^ r = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, hZpow]
      have : Z r = 1 := by
        apply Subtype.ext
        change SubgroupLists.unipGL σ 0 ((r : K) * c₀) = 1
        rw [CharP.cast_eq_zero, zero_mul, SubgroupLists.unipGL_zero_zero]
      rw [this, map_one, Subgroup.coe_one]
    rw [← hμ, ← map_pow] at hpow
    have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hpow
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val, Units.val_one,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h00
    have hμ1 : μ = 1 := by
      have hsub : ((μ : K) - 1) ^ r = 0 := by
        rw [sub_pow_char, one_pow, h00, sub_self]
      have hμ0 : (μ : K) - 1 = 0 := pow_eq_zero_iff (n := r) hr.ne_zero |>.mp hsub
      exact Units.ext (by rw [Units.val_one]; linear_combination hμ0)
    rw [hμ1, map_one] at hμ
    have hM1 : Z 1 = 1 := e.injective (by rw [map_one]; exact Subtype.ext hμ.symm)
    have h02 := congrArg (fun g : SU σ 3 => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2)
      hM1
    simp only [Z, SubgroupLists.coe_unipGL, SubgroupLists.unipMat, Subgroup.coe_one,
      Units.val_one] at h02
    simp at h02
    exact hc₀0 h02
  · intro n hn1 hnr
    have hn0 : (n : K) ≠ 0 := by
      intro h
      have := (CharP.cast_eq_zero_iff K r n).mp h
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    obtain ⟨l, hl⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hK
      (map_natCast σ n) hn0
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hl
      exact hn0 hl.symm
    set L : Kˣ := Units.mk0 l hl0 with hL
    let D : SU σ 3 := ⟨diagSU σ L, diagSU_mem_SU σ hσ L⟩
    refine isConj_iff.mpr ⟨Φ D, ?_⟩
    rw [← map_pow, hZpow, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    change diagSU σ L * SubgroupLists.unipGL σ 0 (((1 : ℕ) : K) * c₀) =
      SubgroupLists.unipGL σ 0 ((n : K) * c₀) * diagSU σ L
    rw [diagSU_mul_unipGL, hL, Units.val_mk0, hl, Nat.cast_one, one_mul]

end Unitary

theorem exists_three_square_psu3_three {K : Type} [Field K] [Finite K] [CharP K 3] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = (3 ^ f) ^ 2) :
    ∃ e₁ e₂ g h : StatedProj (StatedSU 3 (3 ^ f) K), e₁ ^ 3 = 1 ∧ e₂ ^ 3 = 1 ∧
      e₁ * e₂ = e₂ * e₁ ∧ e₁ ≠ 1 ∧ g * e₁ * g⁻¹ = e₁ ∧ g * e₂ * g⁻¹ = e₂⁻¹ ∧
      h * e₁ * h⁻¹ = e₁ ∧ h * e₂ * h⁻¹ = e₂ * e₁ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ := unitaryInvolution K 3 f with hσdef
  have hσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hK
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  obtain ⟨b, hb⟩ := exists_unitaryInvolution_ne (K := K) (r := 3) hf hK
  obtain ⟨d, hd⟩ := exists_add_unitaryInvolution_eq (K := K) (p := 3) (f := f) hK
    (a := -(b * σ b)) (by rw [map_neg, map_mul, hσ, mul_comm])
  set c₀ := σ b - b with hc₀
  have hc₀0 : c₀ ≠ 0 := sub_ne_zero.mpr hb
  have hz : c₀ + σ c₀ + 0 * σ 0 = 0 := by
    rw [hc₀, map_sub, hσ, zero_mul, add_zero]
    ring
  have hu : (1 : K) + σ 1 + 1 * σ 1 = 0 := by
    rw [map_one]
    linear_combination h3
  have hui : (1 : K) + σ 1 + (-1) * σ (-1) = 0 := by
    rw [map_neg, map_one]
    linear_combination h3
  have hh : d + σ d + b * σ b = 0 := by
    rw [hd]
    ring
  set e := equivStatedSU (p := 3) (f := f) hK 3
  set π := QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (3 ^ f) K))
  let E1 : SU σ 3 := ⟨SubgroupLists.unipGL σ 0 c₀, SubgroupLists.unipGL_mem_SU σ hσ hz⟩
  let E2 : SU σ 3 := ⟨SubgroupLists.unipGL σ 1 1, SubgroupLists.unipGL_mem_SU σ hσ hu⟩
  let E2i : SU σ 3 := ⟨SubgroupLists.unipGL σ (-1) 1, SubgroupLists.unipGL_mem_SU σ hσ hui⟩
  let D : SU σ 3 := ⟨SubgroupLists.negOuterGL3 K, SubgroupLists.negOuterGL3_mem_SU σ⟩
  let Hh : SU σ 3 := ⟨SubgroupLists.unipGL σ b d, SubgroupLists.unipGL_mem_SU σ hσ hh⟩
  set Φ : SU σ 3 →* StatedProj (StatedSU 3 (3 ^ f) K) := π.comp e.toMonoidHom with hΦ
  have hΦe : ∀ M, π (e M) = Φ M := fun M => rfl
  have hval : ∀ M N : SU σ 3, (M : GL (Fin 3) K) = N → M = N := fun M N h => Subtype.ext h
  have cE1 : (E1 : GL (Fin 3) K) = SubgroupLists.unipGL σ 0 c₀ := rfl
  have cE2 : (E2 : GL (Fin 3) K) = SubgroupLists.unipGL σ 1 1 := rfl
  have cE2i : (E2i : GL (Fin 3) K) = SubgroupLists.unipGL σ (-1) 1 := rfl
  have cD : (D : GL (Fin 3) K) = SubgroupLists.negOuterGL3 K := rfl
  have cHh : (Hh : GL (Fin 3) K) = SubgroupLists.unipGL σ b d := rfl
  have hpow3 : ∀ M : SU σ 3, (∃ a c : K, (M : GL (Fin 3) K) = SubgroupLists.unipGL σ a c) →
      M ^ 3 = 1 := by
    rintro M ⟨a, c, hM⟩
    apply hval
    rw [Subgroup.coe_pow, hM, SubgroupLists.unipGL_pow_three σ h3, Subgroup.coe_one]
  have hnsc : Φ E1 ≠ 1 := by
    intro h
    rw [← hΦe, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    obtain ⟨μ, hμ⟩ := h
    have hcube : ((e E1 : StatedSU 3 (3 ^ f) K) : GL (Fin 3) K) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, hpow3 E1 ⟨0, c₀, cE1⟩, map_one, Subgroup.coe_one]
    rw [← hμ, ← map_pow] at hcube
    have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hcube
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val, Units.val_one,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h00
    have hμ1 : μ = 1 := by
      have hcu : ((μ : K) - 1) ^ 3 = 0 := by
        linear_combination h00 + (1 - (μ : K)) * (μ : K) * h3
      have hμ0 : (μ : K) - 1 = 0 := (pow_eq_zero_iff (n := 3) (by norm_num)).mp hcu
      exact Units.ext (by rw [Units.val_one]; linear_combination hμ0)
    rw [hμ1, map_one] at hμ
    have hM1 : E1 = 1 := e.injective (by rw [map_one]; exact Subtype.ext hμ.symm)
    have h02 := congrArg (fun g : SU σ 3 => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2)
      hM1
    simp only [cE1, SubgroupLists.coe_unipGL, SubgroupLists.unipMat, Subgroup.coe_one,
      Units.val_one] at h02
    simp at h02
    exact hc₀0 h02
  have hcomm : ∀ M N P : SU σ 3, M * N = P * M → Φ M * Φ N * (Φ M)⁻¹ = Φ P := by
    intro M N P h
    rw [← map_inv, ← map_mul, ← map_mul, h, mul_inv_cancel_right]
  refine ⟨Φ E1, Φ E2, Φ D, Φ Hh, ?_, ?_, ?_, hnsc, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hpow3 E1 ⟨0, c₀, cE1⟩, map_one]
  · rw [← map_pow, hpow3 E2 ⟨1, 1, cE2⟩, map_one]
  · rw [← map_mul, ← map_mul]
    congr 1
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cE1, cE2, SubgroupLists.unipGL_mul,
      SubgroupLists.unipGL_mul]
    exact SubgroupLists.unipGL_congr σ (by ring) (by rw [map_zero, map_one]; ring)
  · apply hcomm
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cD, cE1, SubgroupLists.negOuterGL3_mul_unipGL, neg_zero]
  · have hE2i : E2⁻¹ = E2i := by
      apply inv_eq_of_mul_eq_one_right
      apply hval
      rw [Subgroup.coe_mul, cE2, cE2i, SubgroupLists.unipGL_mul, Subgroup.coe_one,
        ← SubgroupLists.unipGL_zero_zero σ]
      exact SubgroupLists.unipGL_congr σ (by ring)
        (by rw [map_neg, map_one]; linear_combination h3)
    rw [show (Φ E2)⁻¹ = Φ E2i by rw [← map_inv, hE2i]]
    apply hcomm
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cD, cE2, cE2i, SubgroupLists.negOuterGL3_mul_unipGL]
  · apply hcomm
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cHh, cE1, SubgroupLists.unipGL_mul,
      SubgroupLists.unipGL_mul]
    exact SubgroupLists.unipGL_congr σ (by ring) (by rw [map_zero]; ring)
  · rw [show Φ E2 * Φ E1 = Φ (E2 * E1) from (map_mul Φ E2 E1).symm]
    apply hcomm
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, cHh, cE1, cE2,
      SubgroupLists.unipGL_mul, SubgroupLists.unipGL_mul, SubgroupLists.unipGL_mul]
    exact SubgroupLists.unipGL_congr σ (by ring) (by rw [map_zero, map_one, hc₀]; ring)

theorem le_of_pow_dvd_card {X : Type} [Group X] {p e f : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi X p e) (h : p ^ (3 * f) ∣ Nat.card X) : f ≤ e := by
  have hp : p.Prime := Fact.out
  obtain ⟨π, F, _, hF, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
  have hc := Sec13.card_projImage_slPi_mul_three hF hq
  rw [← Nat.card_congr φ.toEquiv] at hc
  set q := p ^ e with hqdef
  have hpq : p ∣ q := dvd_pow_self p (by omega)
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hp.pos
  have hcop : ∀ {m : ℕ} (k : ℕ), 1 ≤ k → 1 ≤ q ^ k → Nat.Coprime p (q ^ k - 1) := by
    intro m k hk hqk
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have h1 : p ∣ q ^ k := dvd_pow hpq (by omega)
    have h2 : p ∣ q ^ k - (q ^ k - 1) := Nat.dvd_sub h1 hd
    rw [Nat.sub_sub_self hqk] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have hcop' : Nat.Coprime p (q ^ 3 + 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have h1 : p ∣ q ^ 3 := dvd_pow hpq (by norm_num)
    have h2 : p ∣ q ^ 3 + 1 - q ^ 3 := Nat.dvd_sub hd h1
    rw [Nat.add_sub_cancel_left] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have hm : Nat.Coprime p ((q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1)) := by
    refine Nat.Coprime.mul_right (hcop (m := 0) 2 (by norm_num) (Nat.one_le_pow _ _ hq1)) ?_
    cases π
    · exact hcop'
    · exact hcop (m := 0) 3 (by norm_num) (Nat.one_le_pow _ _ hq1)
  have h' : p ^ (3 * f) ∣ q ^ 3 * ((q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1)) := by
    rw [← mul_assoc, ← hc]
    exact h.trans (dvd_mul_right _ _)
  have h'' := (Nat.Coprime.pow_left (3 * f) hm).dvd_of_dvd_mul_right h'
  rw [hqdef, ← pow_mul] at h''
  have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h''
  omega

theorem false_of_three_square_hom {K : Type*} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    {H : Subgroup (GL (Fin 3) K)} (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1) {G : Type*} [Group G]
    (χ : G →* H ⧸ Subgroup.center H) (hχ : Function.Injective χ) {e₁ e₂ g h : G}
    (he₁ : e₁ ^ 3 = 1) (he₂ : e₂ ^ 3 = 1) (he₁₂ : e₁ * e₂ = e₂ * e₁) (he₁1 : e₁ ≠ 1)
    (hg₁ : g * e₁ * g⁻¹ = e₁) (hg₂ : g * e₂ * g⁻¹ = e₂⁻¹) (hh₁ : h * e₁ * h⁻¹ = e₁)
    (hh₂ : h * e₂ * h⁻¹ = e₂ * e₁) : False :=
  SubgroupLists.false_of_three_square h3 hdet hZ3 (e₁ := χ e₁) (e₂ := χ e₂) (g := χ g) (h := χ h)
    (by rw [← map_pow, he₁, map_one]) (by rw [← map_pow, he₂, map_one])
    (by rw [← map_mul, ← map_mul, he₁₂])
    (fun h1 => he₁1 (hχ (h1.trans (map_one χ).symm)))
    (by rw [← map_inv, ← map_mul, ← map_mul, hg₁])
    (by rw [← map_inv, ← map_mul, ← map_mul, hg₂, map_inv])
    (by rw [← map_inv, ← map_mul, ← map_mul, hh₁])
    (by rw [← map_inv, ← map_mul, ← map_mul, hh₂, map_mul])

theorem false_of_rational_hom {K : Type*} [Field K] [Finite K] {H : Subgroup (GL (Fin 3) K)}
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1) {r : ℕ} [Fact r.Prime] (hr5 : 5 ≤ r)
    (hrK : (r : K) ≠ 0) {G : Type*} [Group G] (χ : G →* H ⧸ Subgroup.center H)
    (hχ : Function.Injective χ) {s : G} (hs : s ^ r = 1) (hs1 : s ≠ 1)
    (hconj : ∀ n : ℕ, 1 ≤ n → n < r → IsConj s (s ^ n)) : False :=
  false_of_rational hZ3 hr5 hrK (s := χ s) (by rw [← map_pow, hs, map_one])
    (fun h1 => hs1 (hχ (h1.trans (map_one χ).symm)))
    (fun n hn1 hnr => by
      have := χ.map_isConj (hconj n hn1 hnr)
      rwa [map_pow] at this)

theorem oddL3U3 : OddL3U3 := by
  intro X _ _ p e _ hp2 he he2 hiso K hKs r f hr hr2 hf hM
  have hp : p.Prime := Fact.out
  obtain ⟨π, F, _, hF, hq, ⟨φ⟩⟩ := exists_slPi_quotient he hiso
  have := hF.finite
  have := charP_of_piField hF
  set H := slPi π 3 (p ^ e) F with hH
  have hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) F).det = 1 := fun x hx =>
    det_eq_one_of_mem_slPi hF hx
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center_slPi hF hq hz
  have hp3 : p ≠ 3 := by
    rintro rfl
    have : (3 ^ e) % 3 = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
      rw [pow_succ, Nat.mul_mod_left]
    cases π
    · change (3 ^ e) % 3 = 2 at hq
      omega
    · change (3 ^ e) % 3 = 1 at hq
      omega
  have h3 : (3 : F) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : F) = 0 := by exact_mod_cast h
    have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff F p 3).mp h'
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd)
  set ι : K →* H ⧸ Subgroup.center H := φ.toMonoidHom.comp K.subtype with hιdef
  have hι : Function.Injective ι := φ.injective.comp K.subtype_injective
  have hrp : r = p := by
    by_contra hrp
    have : Fact r.Prime := ⟨hr⟩
    have hrF : (r : F) ≠ 0 := by
      intro h
      have := (CharP.cast_eq_zero_iff F p r).mp h
      exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp this).symm
    by_cases hr3 : r = 3
    · subst hr3
      rcases hM with hM | hM
      · obtain ⟨-, F', _, _, hF', ⟨ψ⟩⟩ := hM
        have : CharP F' 3 :=
          CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_three hF'
        have hF3 : (3 : F') = 0 := by exact_mod_cast CharP.cast_eq_zero F' 3
        obtain ⟨e₁, e₂, g, h, he₁, he₂, he₁₂, he₁1, hg₁, hg₂, hh₁, hh₂⟩ :=
          SubgroupLists.exists_three_square_psl33 hF3
        exact false_of_three_square_hom h3 hdet hZ3
          (ι.comp (ψ.symm.toMonoidHom.comp
            (projectiveSpecialLinearGroupEquivStatedProj 3 F').toMonoidHom))
          (hι.comp (ψ.symm.injective.comp (MulEquiv.injective _)))
          he₁ he₂ he₁₂ he₁1 hg₁ hg₂ hh₁ hh₂
      · obtain ⟨-, K', _, _, hK', ⟨ψ⟩⟩ := hM
        have : CharP K' 3 :=
          CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_three
            (by rw [hK', ← pow_mul])
        obtain ⟨e₁, e₂, g, h, he₁, he₂, he₁₂, he₁1, hg₁, hg₂, hh₁, hh₂⟩ :=
          exists_three_square_psu3_three hf hK'
        exact false_of_three_square_hom h3 hdet hZ3 (ι.comp ψ.symm.toMonoidHom)
          (hι.comp ψ.symm.injective) he₁ he₂ he₁₂ he₁1 hg₁ hg₂ hh₁ hh₂
    · have hr5 : 5 ≤ r := by
        have h2 := hr.two_le
        have h4 : r ≠ 4 := by
          rintro rfl
          norm_num at hr
        omega
      rcases hM with hM | hM
      · obtain ⟨-, F', _, _, hF', ⟨ψ⟩⟩ := hM
        have : CharP F' r := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow hr hF'
        obtain ⟨s, hs, hs1, hsc⟩ := exists_rational_psl3 (F := F') (r := r)
        exact false_of_rational_hom hZ3 hr5 hrF
          (ι.comp (ψ.symm.toMonoidHom.comp
            (projectiveSpecialLinearGroupEquivStatedProj 3 F').toMonoidHom))
          (hι.comp (ψ.symm.injective.comp (MulEquiv.injective _))) hs hs1 hsc
      · obtain ⟨-, K', _, _, hK', ⟨ψ⟩⟩ := hM
        have : CharP K' r := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow hr
          (by rw [hK', ← pow_mul])
        obtain ⟨s, hs, hs1, hsc⟩ := exists_rational_psu3 (K := K') (r := r) hf hK'
        exact false_of_rational_hom hZ3 hr5 hrF (ι.comp ψ.symm.toMonoidHom)
          (hι.comp ψ.symm.injective) hs hs1 hsc
  rw [hrp] at hM
  have hfe : f ≤ e := by
    refine le_of_pow_dvd_card he hiso ((?_ : p ^ (3 * f) ∣ Nat.card K).trans
      (Subgroup.card_subgroup_dvd_card K))
    have hp3' : Nat.Coprime (p ^ (3 * f)) 3 := Nat.Coprime.pow_left _
      ((Nat.coprime_primes hp Nat.prime_three).mpr hp3)
    rcases hM with hM | hM
    · obtain ⟨-, F', _, _, hF', ⟨ψ⟩⟩ := hM
      have hc := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := F')
      rw [← Nat.card_congr ψ.toEquiv, hF'] at hc
      have h1 : p ^ (3 * f) ∣ Nat.card K * Nat.gcd 3 (p ^ f - 1) := by
        rw [hc, pow_mul, ← pow_mul p f 3, mul_comm f 3, ← pow_mul, mul_assoc]
        exact dvd_mul_right _ _
      exact (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _) hp3').dvd_of_dvd_mul_right h1
    · obtain ⟨-, K', _, _, hK', ⟨ψ⟩⟩ := hM
      have hU : UnitaryFieldData p f K' := ⟨hp, hf, by rw [hK', ← pow_mul, mul_comm]⟩
      have hc := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul hU
      rw [← Nat.card_congr ψ.toEquiv] at hc
      have h1 : p ^ (3 * f) ∣ Nat.card K * Nat.gcd 3 (p ^ f + 1) := by
        rw [hc, mul_comm 3 f, pow_mul, mul_assoc]
        exact dvd_mul_right _ _
      exact (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _) hp3').dvd_of_dvd_mul_right h1
  have hfe' : f * (e / f) = e := by
    interval_cases e <;> interval_cases f <;> rfl
  have he' : 1 ≤ e / f := by
    interval_cases e <;> interval_cases f <;> norm_num
  have hiso' : Sec4.IsoLThreePi X p (f * (e / f)) := by rw [hfe']; exact hiso
  refine Or.inr (Or.inr ⟨p, f, e / f, inferInstance, hf, he', hiso', ?_⟩)
  rcases hM with hM | hM
  · exact Or.inl (nonempty_projSL_of_statedClassicalModel hM)
  · refine Or.inr ⟨?_, nonempty_projSU_of_statedClassicalModel hM⟩
    have h3p : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 2 < 3 := by norm_num
      _ ≤ p := h3p
      _ ≤ p ^ f := Nat.le_self_pow (by omega) p

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
