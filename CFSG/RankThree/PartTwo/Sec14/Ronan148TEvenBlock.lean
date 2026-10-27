module

public import CFSG.RankThree.PartTwo.Sec16.KL3SubProofSL2
public import CFSG.RankThree.PartTwo.Sec16.KL3SubProofElat
import CFSG.HardMathSupport.Solomon.Coordinator.BGLSL2Witness
import CFSG.Walter.PSL2Facts.OddMaximal
import CFSG.GH74.Uniqueness.Bender.Dickson

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open Matrix CFSG.RankThree.PartOne.CTP
open CFSG.BenderSuzuki.MatrixGroups (PSL2MatrixGroup)

variable {F : Type} [Field F]

theorem card_le_of_pow_eq_self [Finite F] {n : ℕ} (hn : 1 < n) (S : Set F)
    (hS : ∀ z ∈ S, z ^ n = z) : Nat.card S ≤ n := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_card_toFinset]
  calc S.toFinset.card ≤ (Polynomial.X ^ n - Polynomial.X : Polynomial F).natDegree := by
        apply Polynomial.card_le_degree_of_subset_roots
        intro z hz
        rw [Finset.mem_val, Set.mem_toFinset] at hz
        rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero F hn)]
        simp [Polynomial.IsRoot, hS z hz]
    _ = n := FiniteField.X_pow_card_sub_X_natDegree_eq F hn

theorem coe_sl_pow {n : Type} [Fintype n] [DecidableEq n] (A : SpecialLinearGroup n F) (k : ℕ) :
    ((A ^ k : SpecialLinearGroup n F) : Matrix n n F) = (A : Matrix n n F) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem eq_u2_of_commute [CharP F 2] {g : SpecialLinearGroup (Fin 2) F} {ν : F} (hν : ν ≠ 0)
    (h : g * u2 ν = u2 ν * g) : ∃ x, g = u2 x := by
  have e00 := congrArg (fun g : SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have e01 := congrArg (fun g : SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [u2_coe, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := e00.resolve_left hν
  have had : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (g : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have : ν * ((g : Matrix (Fin 2) (Fin 2) F) 0 0 - (g : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
      linear_combination e01
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hν)
  have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [hc, mul_zero, sub_zero, ← had] at hdet
    have h2 : ((g : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) ^ 2 = 0 := by
      linear_combination hdet + ((g : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) *
        (CharTwo.two_eq_zero : (2 : F) = 0)
    have h3 := pow_eq_zero_iff (two_ne_zero) |>.mp h2
    linear_combination h3 - (CharTwo.two_eq_zero : (2 : F) = 0)
  refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u2_coe, ha, hc, ← had]

@[expose] def uSub (F : Type) [Field F] : Subgroup (SpecialLinearGroup (Fin 2) F) where
  carrier := {g | ∃ x, g = u2 x}
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, (u2_add x y).symm⟩
  one_mem' := ⟨0, u2_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, SpecialLinearGroup.transvection_inv _ x⟩

theorem card_upper [Finite F] [CharP F 2] (Y : Subgroup (SpecialLinearGroup (Fin 2) F)) {x₀ : F}
    (hx₀ : x₀ ≠ 0) (hx₀Y : u2 x₀ ∈ Y) :
    Nat.card {x : F | u2 x ∈ Y} = 2 ^ (Nat.card Y).factorization 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup Y := (uSub F).subgroupOf Y with hQdef
  have hcardQ : Nat.card {x : F | u2 x ∈ Y} = Nat.card Q := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x => (⟨⟨u2 x.1, x.2⟩, ⟨x.1, rfl⟩⟩ : Q)) ⟨?_, ?_⟩)
    · intro a b hab
      apply Subtype.ext
      exact u2_injective (congrArg (fun q : Q => ((q : Y) : SpecialLinearGroup (Fin 2) F)) hab)
    · rintro ⟨⟨g, hg⟩, x, hx⟩
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change u2 x ∈ Y
        rw [← hx]
        exact hg
      · apply Subtype.ext
        apply Subtype.ext
        exact hx.symm
  have hQ2 : IsPGroup 2 Q := by
    intro q
    obtain ⟨x, hx⟩ := q.2
    have hx' : ((q : Y) : SpecialLinearGroup (Fin 2) F) = u2 x := hx
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (((q : Y) : SpecialLinearGroup (Fin 2) F)) ^ 2 = 1
    rw [hx', pow_two, u2_mul_self]
  obtain ⟨S, hQS⟩ := hQ2.exists_le_sylow
  have hSQ : (S : Subgroup Y) ≤ Q := by
    have hq₀ : (⟨u2 x₀, hx₀Y⟩ : Y) ∈ (S : Subgroup Y) := hQS ⟨x₀, rfl⟩
    have hne : (⟨⟨u2 x₀, hx₀Y⟩, hq₀⟩ : (S : Subgroup Y)) ≠ 1 := by
      intro h
      apply hx₀
      apply u2_injective
      rw [u2_zero]
      exact congrArg (fun s : (S : Subgroup Y) => ((s : Y) : SpecialLinearGroup (Fin 2) F)) h
    haveI : Nontrivial (S : Subgroup Y) := ⟨⟨_, 1, hne⟩⟩
    haveI := S.isPGroup'.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center (S : Subgroup Y))
    have hzc := Subgroup.mem_center_iff.mp z.2 ⟨⟨u2 x₀, hx₀Y⟩, hq₀⟩
    have hzc' : ((((z : (S : Subgroup Y)) : Y)) : SpecialLinearGroup (Fin 2) F) * u2 x₀ =
        u2 x₀ * (((z : (S : Subgroup Y)) : Y) : SpecialLinearGroup (Fin 2) F) :=
      (congrArg (fun s : (S : Subgroup Y) => ((s : Y) : SpecialLinearGroup (Fin 2) F)) hzc).symm
    obtain ⟨ν, hν⟩ := eq_u2_of_commute hx₀ hzc'
    have hν0 : ν ≠ 0 := by
      rintro rfl
      apply hz1
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rw [hν, u2_zero]
      rfl
    intro s hs
    have hsc := Subgroup.mem_center_iff.mp z.2 ⟨s, hs⟩
    have hsc' : ((s : Y) : SpecialLinearGroup (Fin 2) F) * u2 ν =
        u2 ν * ((s : Y) : SpecialLinearGroup (Fin 2) F) := by
      rw [← hν]
      exact congrArg (fun s : (S : Subgroup Y) => ((s : Y) : SpecialLinearGroup (Fin 2) F)) hsc
    obtain ⟨x, hx⟩ := eq_u2_of_commute hν0 hsc'
    exact ⟨x, hx⟩
  rw [hcardQ, ← le_antisymm hSQ hQS, Sylow.card_eq_multiplicity]

@[expose] def swapSL (F : Type) [Field F] [CharP F 2] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    simp only [mul_zero, mul_one, zero_sub]
    exact CharTwo.neg_eq 1⟩

theorem swapSL_conj_u2 [CharP F 2] (x : F) : swapSL F * u2 x * swapSL F = l2 x := by
  apply Subtype.ext
  show (swapSL F : Matrix (Fin 2) (Fin 2) F) * (u2 x : Matrix (Fin 2) (Fin 2) F) *
    (swapSL F : Matrix (Fin 2) (Fin 2) F) = (l2 x : Matrix (Fin 2) (Fin 2) F)
  rw [u2_coe, l2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem swapSL_conj_l2 [CharP F 2] (x : F) : swapSL F * l2 x * swapSL F = u2 x := by
  apply Subtype.ext
  show (swapSL F : Matrix (Fin 2) (Fin 2) F) * (l2 x : Matrix (Fin 2) (Fin 2) F) *
    (swapSL F : Matrix (Fin 2) (Fin 2) F) = (u2 x : Matrix (Fin 2) (Fin 2) F)
  rw [u2_coe, l2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem swapSL_mul_self [CharP F 2] : swapSL F * swapSL F = 1 := by
  apply Subtype.ext
  show (swapSL F : Matrix (Fin 2) (Fin 2) F) * (swapSL F : Matrix (Fin 2) (Fin 2) F) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem card_lower [Finite F] [CharP F 2] (Y : Subgroup (SpecialLinearGroup (Fin 2) F)) {y₀ : F}
    (hy₀ : y₀ ≠ 0) (hy₀Y : l2 y₀ ∈ Y) :
    Nat.card {y : F | l2 y ∈ Y} = 2 ^ (Nat.card Y).factorization 2 := by
  set w := swapSL F with hw
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right swapSL_mul_self
  set Y' := Y.map (MulAut.conj w).toMonoidHom with hY'
  have hmem : ∀ y, l2 y ∈ Y ↔ u2 y ∈ Y' := by
    intro y
    constructor
    · intro hy
      refine ⟨l2 y, hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwinv]
      exact swapSL_conj_l2 y
    · rintro ⟨g, hg, hgy⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwinv] at hgy
      have hww : w * w = 1 := by rw [hw]; exact swapSL_mul_self
      have : g = l2 y := by
        calc g = (w * w) * g * (w * w) := by rw [hww, one_mul, mul_one]
          _ = w * (w * g * w) * w := by simp only [mul_assoc]
          _ = w * u2 y * w := by rw [hgy]
          _ = l2 y := by rw [hw]; exact swapSL_conj_u2 y
      rwa [← this]
  have hcard : Nat.card Y' = Nat.card Y :=
    Subgroup.card_map_of_injective (MulAut.conj w).injective
  rw [show {y : F | l2 y ∈ Y} = {y : F | u2 y ∈ Y'} from Set.ext hmem,
    card_upper Y' hy₀ ((hmem y₀).1 hy₀Y), hcard]

theorem pow_four_of_pow [CharP F 2] {x y : F}
    (h : (u2 x * l2 y) ^ 2 = 1 ∨ (u2 x * l2 y) ^ 3 = 1 ∨ (u2 x * l2 y) ^ 5 = 1) :
    (x * y) ^ 4 = x * y := by
  by_cases hx : x = 0
  · simp [hx]
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have hM := coe_u2_mul_l2 x y
  have key : ∀ n : ℕ, (u2 x * l2 y) ^ n = 1 →
      (!![1 + x * y, x; y, 1] : Matrix (Fin 2) (Fin 2) F) ^ n = 1 := by
    intro n hn
    have h1 : (((u2 x * l2 y) ^ n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        1 := by rw [hn]; rfl
    rw [coe_sl_pow, hM] at h1
    exact h1
  rcases h with h | h | h
  · have e := congrFun (congrFun (key 2 h) 0) 1
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at e
    have h1 : x * (x * y) = 0 := by linear_combination e - x * two
    rw [(mul_eq_zero.mp h1).resolve_left hx]
    ring
  · have e := congrFun (congrFun (key 3 h) 0) 1
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at e
    have h1 : x * ((x * y) ^ 2 + 1) = 0 := by
      linear_combination e - x * (2 * (x * y) + 1) * two
    have h2 : (x * y + 1) ^ 2 = 0 := by
      linear_combination (mul_eq_zero.mp h1).resolve_left hx + (x * y) * two
    have h3 : x * y = 1 := by
      have := pow_eq_zero_iff two_ne_zero |>.mp h2
      linear_combination this - two
    rw [h3]
    ring
  · have e := congrFun (congrFun (key 5 h) 0) 1
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at e
    have h1 : x * ((x * y) ^ 4 + (x * y) ^ 2 + 1) = 0 := by
      linear_combination e - x * (4 * (x * y) ^ 3 + 10 * (x * y) ^ 2 + 10 * (x * y) + 2) * two
    have h2 : ((x * y) ^ 2 + x * y + 1) ^ 2 = 0 := by
      linear_combination (mul_eq_zero.mp h1).resolve_left hx +
        ((x * y) ^ 3 + (x * y) ^ 2 + x * y) * two
    have h3 := pow_eq_zero_iff two_ne_zero |>.mp h2
    linear_combination ((x * y) ^ 2 - x * y) * h3

theorem factorization_two_psl2 {m : ℕ} (hm : 1 ≤ m) :
    (2 ^ m * ((2 ^ m) ^ 2 - 1)).factorization 2 = m := by
  have h1 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hodd : ¬ 2 ∣ (2 ^ m) ^ 2 - 1 := by
    have h2 : 2 ∣ (2 ^ m) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    omega
  have hne : (2 ^ m) ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ (2 ^ m) ^ 2 := by
      have : 2 ≤ 2 ^ m := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      nlinarith
    omega
  rw [Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero, Nat.Prime.factorization_pow Nat.prime_two]
  simp

theorem block_two [Finite F] [CharP F 2]
    {Y : Subgroup (SpecialLinearGroup (Fin 2) F)} {x₁ x₂ y₀ : F} (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hx₁₂ : x₁ ≠ x₂) (hy₀ : y₀ ≠ 0) (hu₁ : u2 x₁ ∈ Y) (hu₂ : u2 x₂ ∈ Y) (hl : l2 y₀ ∈ Y) :
    ∃ K₁ : Subfield F, (∀ x y, u2 x ∈ Y → l2 y ∈ Y → x * y ∈ K₁) ∧
      Nat.card {x : F | u2 x ∈ Y} = Nat.card K₁ ∧ Nat.card {y : F | l2 y ∈ Y} = Nat.card K₁ := by
  classical
  obtain ⟨f, hf1, hF⟩ := exists_card_eq_two_pow F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := mkPSL_injective (F := F)
  set H : Subgroup (PSL2MatrixGroup F) := Y.map (mkPSL F) with hHdef
  have hHcard : Nat.card H = Nat.card Y := Subgroup.card_map_of_injective hinj
  have hU := card_upper Y hx₁ hu₁
  have hL := card_lower Y hy₀ hl
  suffices key : ∃ K₁ : Subfield F, (∀ x y, u2 x ∈ Y → l2 y ∈ Y → x * y ∈ K₁) ∧
      2 ^ (Nat.card Y).factorization 2 = Nat.card K₁ by
    obtain ⟨K₁, h1, h2⟩ := key
    exact ⟨K₁, h1, hU.trans h2, hL.trans h2⟩
  have h4 : 4 ∣ Nat.card Y :=
    CFSG.RankThree.PartTwo.Sec16.KL3SubProof.four_dvd_card_of_root_pair hx₁ hx₂ hx₁₂ hu₁ hu₂
  have hFodd : Odd (2 ^ f - 1) := by
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rcases h1 with ⟨c, hc⟩
    exact ⟨c - 1, by omega⟩
  have hFodd' : Odd (2 ^ f + 1) := by
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    rcases h1 with ⟨c, hc⟩
    exact ⟨c, by omega⟩
  have hg : Nat.gcd (2 ^ f - 1) 2 = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hFodd.not_two_dvd_nat)
  let x : H := ⟨mkPSL F (u2 x₁), Subgroup.mem_map_of_mem _ hu₁⟩
  let y : H := ⟨mkPSL F (l2 y₀), Subgroup.mem_map_of_mem _ hl⟩
  have hxy : x * y ≠ y * x := by
    intro h
    have h' := congrArg Subtype.val h
    apply u2_mul_l2_ne (mul_ne_zero hx₁ hy₀)
    apply hinj
    rw [map_mul, map_mul]
    exact h'
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    simp [x, pow_two, ← map_mul, u2_mul_self]
  have hy2 : y ^ 2 = 1 := by
    apply Subtype.ext
    simp [y, pow_two, ← map_mul, l2_mul_self]
  have hcomm : ∀ {z : ℕ}, z ∣ 2 ^ f - 1 ∨ z ∣ 2 ^ f + 1 → Odd z := fun {z} hz =>
    hz.elim (fun h => Odd.of_dvd_nat hFodd h) (fun h => Odd.of_dvd_nat hFodd' h)
  have hwit : ∀ {m : ℕ} (W : CFSG.Glauberman.Dickson.SubfieldConjugacyWitness 2 m H),
      ∀ x y, u2 x ∈ Y → l2 y ∈ Y → x * y ∈ W.K := by
    intro m W x y hx hy
    have hmem : (QuotientGroup.mk (u2 x * l2 y) :
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∈ H :=
      Subgroup.mem_map_of_mem _ (Y.mul_mem hx hy)
    have h := CFSG.HardMathSupport.Solomon.Coordinator.BGL.trace_sq_mem_of_witness H W _ hmem
    rw [trace_u2_mul_l2] at h
    exact mem_subfield_of_sq_mem W.K h
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield
      (p := 2) (f := f) hF H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hcard, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, -⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m', t, -, ht, N, C, hN, hNel, hNcard, hCcyc, hCcard, hdisj, hsup⟩ |
      ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩ | ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩
  · exact absurd (hEl.toIsMulCommutative.is_comm.comm x y) hxy
  · have : IsCyclic H := hcyc
    exact absurd (IsCyclic.isMulCommutative.is_comm.comm x y) hxy
  ·
    exfalso
    have hzodd : Odd z := by
      simp only [hF, hg, Nat.div_one] at hz
      exact hcomm hz
    have h42 : 4 ∣ 2 * z := by rw [← hcard, hHcard]; exact h4
    obtain ⟨c, hc⟩ := hzodd
    omega
  · exact absurd (by
      have := alternating_four_involutions_comm (e x) (e y) (by rw [← map_pow, hx2, map_one])
        (by rw [← map_pow, hy2, map_one])
      exact e.injective (by rw [map_mul, map_mul]; exact this)) hxy
  · exfalso
    have h1 : 2 ∣ 2 ^ (2 * f) := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ (2 * f) := Nat.one_le_two_pow
    omega
  ·
    set K₁ : Subfield F := ((frobenius F 2).comp (frobenius F 2)).eqLocusField (RingHom.id F)
      with hK₁
    have hmemK : ∀ z : F, z ∈ K₁ ↔ z ^ 4 = z := by
      intro z
      rw [hK₁, RingHom.mem_eqLocusField]
      simp only [RingHom.comp_apply, frobenius_def, RingHom.id_apply]
      rw [← pow_mul]
    have hprod : ∀ x y, u2 x ∈ Y → l2 y ∈ Y → x * y ∈ K₁ := by
      intro x y hx hy
      rw [hmemK]
      apply pow_four_of_pow
      have hgH : mkPSL F (u2 x * l2 y) ∈ H := Subgroup.mem_map_of_mem _ (Y.mul_mem hx hy)
      have htr : ∀ k : ℕ, e ⟨mkPSL F (u2 x * l2 y), hgH⟩ ^ k = 1 → (u2 x * l2 y) ^ k = 1 := by
        intro k hk
        rw [← map_pow, map_eq_one_iff _ e.injective] at hk
        have h1 := congrArg Subtype.val hk
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow] at h1
        exact hinj (by rw [h1, map_one])
      rcases CFSG.Walter.alternatingGroup_five_pow_eq_one (e ⟨mkPSL F (u2 x * l2 y), hgH⟩) with
        h | h | h
      · exact Or.inl (htr 2 h)
      · exact Or.inr (Or.inl (htr 3 h))
      · exact Or.inr (Or.inr (htr 5 h))
    refine ⟨K₁, hprod, ?_⟩
    have h60 : Nat.card Y = 60 := by
      rw [← hHcard, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Fintype.card_fin]
      decide
    have hf60 : (Nat.card Y).factorization 2 = 2 := by
      rw [h60, show (60 : ℕ) = 2 ^ 2 * 15 by norm_num, Nat.factorization_mul (by norm_num)
        (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 15 by norm_num)]
      simp
    rw [hf60]
    apply le_antisymm
    ·
      have hUcard : Nat.card {x : F | u2 x ∈ Y} = 4 := by rw [hU, hf60]; norm_num
      have hsub : (fun x => x * y₀) '' {x : F | u2 x ∈ Y} ⊆ (K₁ : Set F) := by
        rintro _ ⟨x, hx, rfl⟩
        exact hprod x y₀ hx hl
      have h1 := Nat.card_mono (Set.toFinite (K₁ : Set F)) hsub
      rw [Nat.card_image_of_injective (mul_left_injective₀ hy₀), hUcard] at h1
      exact h1
    · exact card_le_of_pow_eq_self (by norm_num) (K₁ : Set F) (fun z hz => (hmemK z).1 hz)
  ·
    exfalso
    have htodd : Odd t :=
      Odd.of_dvd_nat hFodd (ht.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)))
    have := hN
    have hxN : x ∈ N := mem_of_sq_eq_one_of_sup hdisj hsup (hCcard ▸ htodd) hx2
    have hyN : y ∈ N := mem_of_sq_eq_one_of_sup hdisj hsup (hCcard ▸ htodd) hy2
    have hcN := hNel.toIsMulCommutative.is_comm.comm (⟨x, hxN⟩ : N) ⟨y, hyN⟩
    exact hxy (congrArg Subtype.val hcN)
  ·
    refine ⟨W.K, hwit W, ?_⟩
    rw [W.card_eq, ← hHcard, Nat.card_congr eP.toEquiv,
      CFSG.GH74.Uniqueness.Bender.card_psl2_even m (by omega), factorization_two_psl2 (by omega)]
  ·
    obtain ⟨eG⟩ := CFSG.GH74.Uniqueness.Bender.nonempty_pgl2_mulEquiv_psl2 m (by omega)
    refine ⟨W.K, hwit W, ?_⟩
    rw [W.card_eq, ← hHcard, Nat.card_congr (eP.trans eG).toEquiv,
      CFSG.GH74.Uniqueness.Bender.card_psl2_even m (by omega), factorization_two_psl2 (by omega)]

@[expose] def IsFrame (e f : Fin 3 → Fin 3 → F) : Prop :=
  ∀ i j, f i ⬝ᵥ e j = if i = j then 1 else 0

@[expose] def frameMat (e : Fin 3 → Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.of fun r c => e c r

@[expose] def frameInv (f : Fin 3 → Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.of fun r c => f r c

theorem frameInv_mul_frameMat {e f : Fin 3 → Fin 3 → F} (h : IsFrame e f) :
    frameInv f * frameMat e = 1 := by
  ext i j
  have := h i j
  simp only [dotProduct] at this
  simp only [frameInv, frameMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, this]

theorem frameMat_mul_frameInv {e f : Fin 3 → Fin 3 → F} (h : IsFrame e f) :
    frameMat e * frameInv f = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (Fin 3) (Fin 3) F rfl).mp (frameInv_mul_frameMat h)

theorem frameMat_mul_single_mul_frameInv (e f : Fin 3 → Fin 3 → F) (i j : Fin 3) (c : F) :
    frameMat e * Matrix.single i j c * frameInv f = c • vecMulVec (e i) (f j) := by
  ext r s
  simp only [frameMat, frameInv, Matrix.mul_apply, Matrix.of_apply, Matrix.single_apply,
    Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  simp [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp <;> ring

@[expose] noncomputable def frameUnit {e f : Fin 3 → Fin 3 → F} (h : IsFrame e f) :
    GL (Fin 3) F :=
  ⟨frameMat e, frameInv f, frameMat_mul_frameInv h, frameInv_mul_frameMat h⟩

theorem frame_conj_transvection {e f : Fin 3 → Fin 3 → F} (h : IsFrame e f) (i j : Fin 3)
    (c : F) : frameMat e * (1 + Matrix.single i j c) * frameInv f =
      1 + c • vecMulVec (e i) (f j) := by
  rw [mul_add, add_mul, mul_one, frameMat_mul_frameInv h, frameMat_mul_single_mul_frameInv]

@[expose] def blkEmbMat (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem blkEmbMat_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    blkEmbMat (A * B) = blkEmbMat A * blkEmbMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkEmbMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blkEmbMat_one : blkEmbMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkEmbMat]

theorem sl_mul_inv {n : Type} [Fintype n] [DecidableEq n] (A : SpecialLinearGroup n F) :
    (A : Matrix n n F) * ((A⁻¹ : SpecialLinearGroup n F) : Matrix n n F) = 1 := by
  simp [Matrix.mul_adjugate]

theorem sl_inv_mul {n : Type} [Fintype n] [DecidableEq n] (A : SpecialLinearGroup n F) :
    ((A⁻¹ : SpecialLinearGroup n F) : Matrix n n F) * (A : Matrix n n F) = 1 := by
  simp [Matrix.adjugate_mul]

theorem sl_coe_mul {n : Type} [Fintype n] [DecidableEq n] (A B : SpecialLinearGroup n F) :
    ((A * B : SpecialLinearGroup n F) : Matrix n n F) =
      (A : Matrix n n F) * (B : Matrix n n F) := by
  simp

@[expose] noncomputable def blkEmb (F : Type) [Field F] :
    SpecialLinearGroup (Fin 2) F →* GL (Fin 3) F where
  toFun A := ⟨blkEmbMat (A : Matrix (Fin 2) (Fin 2) F),
    blkEmbMat ((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
      rw [← blkEmbMat_mul, sl_mul_inv, blkEmbMat_one], by
      rw [← blkEmbMat_mul, sl_inv_mul, blkEmbMat_one]⟩
  map_one' := Units.ext (by
    show blkEmbMat ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    simp [blkEmbMat_one])
  map_mul' A B := Units.ext (by
    show blkEmbMat ((A * B : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      blkEmbMat (A : Matrix (Fin 2) (Fin 2) F) * blkEmbMat (B : Matrix (Fin 2) (Fin 2) F)
    rw [sl_coe_mul, blkEmbMat_mul])

theorem blkEmbMat_u2 (x : F) :
    blkEmbMat (u2 x : Matrix (Fin 2) (Fin 2) F) = 1 + Matrix.single 0 1 x := by
  rw [u2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkEmbMat, Matrix.single_apply]

theorem blkEmbMat_l2 (x : F) :
    blkEmbMat (l2 x : Matrix (Fin 2) (Fin 2) F) = 1 + Matrix.single 1 0 x := by
  rw [l2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkEmbMat, Matrix.single_apply]

@[expose] def rootSet (D : Subgroup (GL (Fin 3) F)) (p ℓ : Fin 3 → F) : Set F :=
  {c | ∃ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) = 1 + c • vecMulVec p ℓ}

theorem isFrame_block {p ℓ b ψ : Fin 3 → F} (hℓp : ℓ ⬝ᵥ p = 0) (hψb : ψ ⬝ᵥ b = 0)
    (hℓb : ℓ ⬝ᵥ b ≠ 0) (hψp : ψ ⬝ᵥ p ≠ 0) :
    IsFrame ![p, b, crossProduct ℓ ψ]
      ![(ψ ⬝ᵥ p)⁻¹ • ψ, (ℓ ⬝ᵥ b)⁻¹ • ℓ,
        ((crossProduct p b) ⬝ᵥ (crossProduct ℓ ψ))⁻¹ • crossProduct p b] := by
  have hpℓ : p ⬝ᵥ ℓ = 0 := by rw [dotProduct_comm]; exact hℓp
  have hbψ : b ⬝ᵥ ψ = 0 := by rw [dotProduct_comm]; exact hψb
  have hdet : (crossProduct p b) ⬝ᵥ (crossProduct ℓ ψ) ≠ 0 := by
    rw [cross_dot_cross, hpℓ, hbψ, zero_mul, zero_sub, neg_ne_zero, dotProduct_comm p ψ,
      dotProduct_comm b ℓ]
    exact mul_ne_zero hψp hℓb
  have hc3 : (crossProduct p b) ⬝ᵥ p = 0 := by rw [dotProduct_comm]; exact dot_self_cross p b
  have hc4 : (crossProduct p b) ⬝ᵥ b = 0 := by rw [dotProduct_comm]; exact dot_cross_self p b
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [smul_dotProduct, hψb, hℓp, dot_self_cross, dot_cross_self, hψp, hℓb, hdet, hc3, hc4]

theorem block_three [Finite F] [CharP F 2]
    (D : Subgroup (GL (Fin 3) F)) {p ℓ b ψ : Fin 3 → F} (hℓp : ℓ ⬝ᵥ p = 0) (hψb : ψ ⬝ᵥ b = 0)
    (hℓb : ℓ ⬝ᵥ b ≠ 0) (hψp : ψ ⬝ᵥ p ≠ 0) {c₁ c₂ d₀ : F} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hc₁₂ : c₁ ≠ c₂) (hd₀ : d₀ ≠ 0) (h₁ : c₁ ∈ rootSet D p ℓ) (h₂ : c₂ ∈ rootSet D p ℓ)
    (h₀ : d₀ ∈ rootSet D b ψ) :
    ∃ K₁ : Subfield F, (∀ c ∈ rootSet D p ℓ, ∀ d ∈ rootSet D b ψ,
        c * d * ((ℓ ⬝ᵥ b) * (ψ ⬝ᵥ p)) ∈ K₁) ∧
      Nat.card (rootSet D p ℓ) = Nat.card K₁ ∧ Nat.card (rootSet D b ψ) = Nat.card K₁ := by
  have hfr := isFrame_block hℓp hψb hℓb hψp
  set e : Fin 3 → Fin 3 → F := ![p, b, crossProduct ℓ ψ] with he
  set f : Fin 3 → Fin 3 → F := ![(ψ ⬝ᵥ p)⁻¹ • ψ, (ℓ ⬝ᵥ b)⁻¹ • ℓ,
    ((crossProduct p b) ⬝ᵥ (crossProduct ℓ ψ))⁻¹ • crossProduct p b] with hf
  set φ : SpecialLinearGroup (Fin 2) F →* GL (Fin 3) F :=
    (MulAut.conj (frameUnit hfr)).toMonoidHom.comp (blkEmb F) with hφ
  have hφmat : ∀ A, (φ A : Matrix (Fin 3) (Fin 3) F) =
      frameMat e * blkEmbMat (A : Matrix (Fin 2) (Fin 2) F) * frameInv f := fun A => rfl
  set Y := D.comap φ with hY
  have hmemU : ∀ c : F, c ∈ rootSet D p ℓ ↔ u2 (c * (ℓ ⬝ᵥ b)) ∈ Y := by
    intro c
    have hmat : (φ (u2 (c * (ℓ ⬝ᵥ b))) : Matrix (Fin 3) (Fin 3) F) = 1 + c • vecMulVec p ℓ := by
      rw [hφmat, blkEmbMat_u2, frame_conj_transvection hfr]
      simp only [he, hf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        vecMulVec_smul, smul_smul]
      rw [mul_assoc, mul_inv_cancel₀ hℓb, mul_one]
    constructor
    · rintro ⟨g, hg, hgm⟩
      change φ (u2 (c * (ℓ ⬝ᵥ b))) ∈ D
      have : φ (u2 (c * (ℓ ⬝ᵥ b))) = g := Units.ext (by rw [hmat, hgm])
      rw [this]
      exact hg
    · intro h
      exact ⟨_, h, hmat⟩
  have hmemL : ∀ d : F, d ∈ rootSet D b ψ ↔ l2 (d * (ψ ⬝ᵥ p)) ∈ Y := by
    intro d
    have hmat : (φ (l2 (d * (ψ ⬝ᵥ p))) : Matrix (Fin 3) (Fin 3) F) = 1 + d • vecMulVec b ψ := by
      rw [hφmat, blkEmbMat_l2, frame_conj_transvection hfr]
      simp only [he, hf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        vecMulVec_smul, smul_smul]
      rw [mul_assoc, mul_inv_cancel₀ hψp, mul_one]
    constructor
    · rintro ⟨g, hg, hgm⟩
      change φ (l2 (d * (ψ ⬝ᵥ p))) ∈ D
      have : φ (l2 (d * (ψ ⬝ᵥ p))) = g := Units.ext (by rw [hmat, hgm])
      rw [this]
      exact hg
    · intro h
      exact ⟨_, h, hmat⟩
  obtain ⟨K₁, hprod, hU, hL⟩ := block_two (Y := Y) (mul_ne_zero hc₁ hℓb) (mul_ne_zero hc₂ hℓb)
    (fun h => hc₁₂ (mul_right_cancel₀ hℓb h)) (mul_ne_zero hd₀ hψp) ((hmemU c₁).1 h₁)
    ((hmemU c₂).1 h₂) ((hmemL d₀).1 h₀)
  refine ⟨K₁, fun c hc d hd => ?_, ?_, ?_⟩
  · have := hprod _ _ ((hmemU c).1 hc) ((hmemL d).1 hd)
    rwa [show c * (ℓ ⬝ᵥ b) * (d * (ψ ⬝ᵥ p)) = c * d * ((ℓ ⬝ᵥ b) * (ψ ⬝ᵥ p)) by ring] at this
  · rw [← hU]
    have : {x : F | u2 x ∈ Y} = (fun c => c * (ℓ ⬝ᵥ b)) '' rootSet D p ℓ := by
      ext x
      constructor
      · intro hx
        refine ⟨x / (ℓ ⬝ᵥ b), (hmemU _).2 ?_, div_mul_cancel₀ x hℓb⟩
        rwa [div_mul_cancel₀ x hℓb]
      · rintro ⟨c, hc, rfl⟩
        exact (hmemU c).1 hc
    rw [this, Nat.card_image_of_injective (mul_left_injective₀ hℓb)]
  · rw [← hL]
    have : {y : F | l2 y ∈ Y} = (fun d => d * (ψ ⬝ᵥ p)) '' rootSet D b ψ := by
      ext y
      constructor
      · intro hy
        refine ⟨y / (ψ ⬝ᵥ p), (hmemL _).2 ?_, div_mul_cancel₀ y hψp⟩
        rwa [div_mul_cancel₀ y hψp]
      · rintro ⟨d, hd, rfl⟩
        exact (hmemL d).1 hd
    rw [this, Nat.card_image_of_injective (mul_left_injective₀ hψp)]

theorem conj_one_add_smul_vecMulVec (g : GL (Fin 3) F) (c : F) (p ℓ : Fin 3 → F) :
    (g : Matrix (Fin 3) (Fin 3) F) * (1 + c • vecMulVec p ℓ) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 + c • vecMulVec ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ p)
        (ℓ ᵥ* ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
  have hgg : (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgg, Matrix.mul_smul, Matrix.smul_mul,
    mul_vecMulVec, vecMulVec_mul]

theorem one_mem_rootSet {D : Subgroup (GL (Fin 3) F)} {z : GL (Fin 3) F} (hz : z ∈ D)
    {p ℓ : Fin 3 → F} (h : CFSG.RankThree.PartTwo.Sec16.KL3SubProof.IsElat z p ℓ) :
    (1 : F) ∈ rootSet D p ℓ :=
  ⟨z, hz, by rw [one_smul]; exact h.2.2.2⟩

theorem rootSet_conj {D : Subgroup (GL (Fin 3) F)} {g : GL (Fin 3) F} (hg : g ∈ D)
    (p ℓ : Fin 3 → F) :
    rootSet D ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ p)
      (ℓ ᵥ* ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) = rootSet D p ℓ := by
  have hgg : ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)
      = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  ext c
  constructor
  · rintro ⟨h, hh, hhm⟩
    refine ⟨g⁻¹ * h * g⁻¹⁻¹, D.mul_mem (D.mul_mem (D.inv_mem hg) hh) (D.inv_mem (D.inv_mem hg)),
      ?_⟩
    rw [Units.val_mul, Units.val_mul, hhm]
    have := conj_one_add_smul_vecMulVec g⁻¹ c ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ p)
      (ℓ ᵥ* ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    rw [this, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, inv_inv, Matrix.vecMul_vecMul, hgg,
      Matrix.vecMul_one]
  · rintro ⟨h, hh, hhm⟩
    refine ⟨g * h * g⁻¹, D.mul_mem (D.mul_mem hg hh) (D.inv_mem hg), ?_⟩
    rw [Units.val_mul, Units.val_mul, hhm, conj_one_add_smul_vecMulVec]

theorem block_field [Finite F] [CharP F 2]
    (D : Subgroup (GL (Fin 3) F)) {p ℓ b ψ : Fin 3 → F} (hℓp : ℓ ⬝ᵥ p = 0) (hψb : ψ ⬝ᵥ b = 0)
    (hℓb : ℓ ⬝ᵥ b ≠ 0) (hψp : ψ ⬝ᵥ p ≠ 0) (h1 : (1 : F) ∈ rootSet D p ℓ) {c : F} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) (hc : c ∈ rootSet D p ℓ) (h1' : (1 : F) ∈ rootSet D b ψ) :
    ∃ K₁ : Subfield F, rootSet D p ℓ = K₁ ∧ rootSet D b ψ = K₁ ∧ (ℓ ⬝ᵥ b) * (ψ ⬝ᵥ p) ∈ K₁ := by
  obtain ⟨K₁, hprod, hc₁, hc₂⟩ := block_three D hℓp hψb hℓb hψp one_ne_zero hc0 (Ne.symm hc1)
    one_ne_zero h1 hc h1'
  have hν : (ℓ ⬝ᵥ b) * (ψ ⬝ᵥ p) ∈ K₁ := by simpa using hprod 1 h1 1 h1'
  have hν0 : (ℓ ⬝ᵥ b) * (ψ ⬝ᵥ p) ≠ 0 := mul_ne_zero hℓb hψp
  have hdiv : ∀ x : F, x * ((ℓ ⬝ᵥ b) * (ψ ⬝ᵥ p)) ∈ K₁ → x ∈ K₁ := by
    intro x hx
    have := K₁.div_mem hx hν
    rwa [mul_div_cancel_right₀ x hν0] at this
  have hfin : (K₁ : Set F).Finite := Set.toFinite _
  have hK : Nat.card (K₁ : Set F) = Nat.card K₁ := rfl
  refine ⟨K₁, ?_, ?_, hν⟩
  · refine Set.eq_of_subset_of_ncard_le (fun x hx => hdiv x (by simpa using hprod x hx 1 h1'))
      ?_ hfin
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hK, hc₁]
  · refine Set.eq_of_subset_of_ncard_le (fun y hy => hdiv y (by simpa using hprod 1 h1 y hy))
      ?_ hfin
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hK, hc₂]

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
