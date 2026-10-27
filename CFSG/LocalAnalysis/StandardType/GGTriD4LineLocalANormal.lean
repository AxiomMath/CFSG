module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineModel
import CFSG.LocalAnalysis.StandardType.GGTriD4LineDiagonalize

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] noncomputable def triD4LineSL3 (k K : Type) [Field k] [Field K] [Algebra k K] :
    Matrix.SpecialLinearGroup (Fin 3) k →* TriD4LineX k K :=
  (QuotientGroup.mk' (triD4LineDiag k K)).comp
    ((MonoidHom.prod Matrix.SpecialLinearGroup.toGL 1).codRestrict (triD4LineFibre k K)
      fun m => by
        change Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL m) =
          Units.map (Algebra.norm k (S := K)) 1
        rw [map_one]
        exact Matrix.SpecialLinearGroup.coeToGL_det m)

private lemma triD4Line_det_scalar_three (k : Type) [Field k] (μ : k) :
    (Matrix.scalar (Fin 3) μ : Matrix (Fin 3) (Fin 3) k).det = μ ^ 3 := by
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three]
  ring

private lemma triD4Line_det_diag_three (k : Type) [Field k] (ω : k) (hω : ω ^ 3 = 1) :
    (Matrix.diagonal ![1, ω, ω ^ 2] : Matrix (Fin 3) (Fin 3) k).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, one_mul]
  rw [← pow_succ', hω]

private lemma triD4Line_pow_mod_three {M : Type*} [Monoid M] {x : M} (hx : x ^ 3 = 1) (n : ℕ) :
    x ^ n = x ^ (n % 3) := by
  have h : x ^ n = x ^ (n / 3 * 3) * x ^ (n % 3) := by
    rw [← pow_add, Nat.div_add_mod']
  rw [h, mul_comm (n / 3) 3, pow_mul, hx, one_pow, one_mul]

private lemma triD4Line_isPrimitiveRoot_cube (k : Type) [Field k] (ω : k) (hω : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) : IsPrimitiveRoot ω 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hω, fun l hl => ?_⟩
  rw [← orderOf_eq_prime (p := 3) hω hω1]
  exact orderOf_dvd_iff_pow_eq_one.mpr hl

private lemma triD4Line_pow_eq_of_mod_three {M : Type*} [Monoid M] {x : M} (hx : x ^ 3 = 1)
    {m n : ℕ} (h : m % 3 = n % 3) : x ^ m = x ^ n := by
  rw [triD4Line_pow_mod_three hx m, triD4Line_pow_mod_three hx n, h]

private lemma triD4Line_zpow_eq_pow_mod {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) (i : ℤ) :
    x ^ i = x ^ (i % 3).toNat := by
  rw [zpow_eq_zpow_emod i (n := 3)
      (by rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact hx),
    ← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num : (3 : ℤ) ≠ 0))]

private lemma triD4Line_exists_pow_mul_of_mem {G : Type*} [Group G] (E : Subgroup G)
    (hEcomm : IsMulCommutative E) (z s : G) (hzE : z ∈ E) (hsE : s ∈ E)
    (hcard : Nat.card E = 9) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hs3 : s ^ 3 = 1)
    (hzs : s ∉ Subgroup.zpowers z) :
    ∀ e ∈ E, ∃ i j : ℕ, e = z ^ i * s ^ j := by
  intro e he
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  letI : CommGroup E := { (inferInstance : Group E) with
    mul_comm := (isMulCommutative_iff.mp hEcomm) }
  let zE : E := ⟨z, hzE⟩
  let sE : E := ⟨s, hsE⟩
  have hz3E : zE ^ 3 = 1 := Subtype.ext (by simpa using hz3)
  have hz1E : zE ≠ 1 := fun h => hz1 (Subtype.ext_iff.mp h)
  have hs3E : sE ^ 3 = 1 := Subtype.ext (by simpa using hs3)
  have hzcard : Nat.card (Subgroup.zpowers zE) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 3) hz3E hz1E]
  have hlt : Subgroup.zpowers zE < Subgroup.zpowers zE ⊔ Subgroup.zpowers sE := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    have hmem : sE ∈ Subgroup.zpowers zE := by
      rw [heq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers sE)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact hzs (Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩)
  have hcard_gt : 3 < Nat.card ↥(Subgroup.zpowers zE ⊔ Subgroup.zpowers sE) := by
    have h := Subgroup.card_lt_of_lt hlt
    rwa [hzcard] at h
  have hdiv : Nat.card ↥(Subgroup.zpowers zE ⊔ Subgroup.zpowers sE) ∣ 9 := by
    have h := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers zE ⊔ Subgroup.zpowers sE)
    rwa [hcard] at h
  have hcardS : Nat.card ↥(Subgroup.zpowers zE ⊔ Subgroup.zpowers sE) = 9 := by
    have hdiv' : Nat.card ↥(Subgroup.zpowers zE ⊔ Subgroup.zpowers sE) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hdiv
    obtain ⟨k, hk, hkS⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv'
    have hk2 : k = 2 := by
      interval_cases k
      · rw [hkS] at hcard_gt; norm_num at hcard_gt
      · rw [hkS] at hcard_gt; norm_num at hcard_gt
      · rfl
    rw [hk2] at hkS
    simpa using hkS
  have htop : Subgroup.zpowers zE ⊔ Subgroup.zpowers sE = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hcardS, hcard])
  have he' : (⟨e, he⟩ : E) ∈ Subgroup.zpowers zE ⊔ Subgroup.zpowers sE := by
    rw [htop]; trivial
  rw [Subgroup.mem_sup] at he'
  obtain ⟨y, hy, w, hw, hyw⟩ := he'
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hw
  refine ⟨(i % 3).toNat, (j % 3).toNat, ?_⟩
  have h : (⟨e, he⟩ : E) = zE ^ i * sE ^ j := by rw [← hyw, hi, hj]
  have hval : e = z ^ i * s ^ j := by simpa using congrArg Subtype.val h
  rw [hval, triD4Line_zpow_eq_pow_mod hz3 i, triD4Line_zpow_eq_pow_mod hs3 j]

theorem triD4LineSL3_apply (k K : Type) [Field k] [Field K] [Algebra k K]
    (m : Matrix.SpecialLinearGroup (Fin 3) k)
    (h : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL m) =
      Units.map (Algebra.norm k (S := K)) 1) :
    triD4LineSL3 k K m = triD4LineMk k K (Matrix.SpecialLinearGroup.toGL m) 1 h := by
  rfl

private lemma triD4LineSL3_eq_one_iff (k K : Type) [Field k] [Field K] [Algebra k K]
    (m : Matrix.SpecialLinearGroup (Fin 3) k) :
    triD4LineSL3 k K m = 1 ↔ m = 1 := by
  constructor
  · intro hm
    rw [triD4LineSL3_apply k K m
      (by rw [map_one]; exact Matrix.SpecialLinearGroup.coeToGL_det m)] at hm
    obtain ⟨μ, hμ, hc⟩ := (triD4LineMk_eq_one_iff k K _ 1 _).1 hm
    have hμ1 : μ = 1 := by
      have hval : algebraMap k K (μ : k) = 1 := (congrArg Units.val hc).symm
      exact Units.ext ((algebraMap k K).injective
        (by simpa [hval] using (map_one (algebraMap k K)).symm))
    rw [hμ1, map_one] at hμ
    refine (Matrix.SpecialLinearGroup.toGL_inj m 1).1 ?_
    rwa [map_one]
  · rintro rfl
    exact map_one _

theorem triD4LineSL3_injective (k K : Type) [Field k] [Field K] [Algebra k K] :
    Function.Injective (triD4LineSL3 k K) := by
  intro m m' h
  have h1 : triD4LineSL3 k K (m * m'⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : m * m'⁻¹ = 1 := (triD4LineSL3_eq_one_iff k K (m * m'⁻¹)).1 h1
  exact mul_inv_eq_one.mp h2

theorem triD4LineSL3_range (k K : Type) [Field k] [Field K] [Algebra k K] :
    (triD4LineSL3 k K).range = triD4LineN0 k K := by
  ext y
  rw [MonoidHom.mem_range, mem_triD4LineN0_iff]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨Matrix.SpecialLinearGroup.toGL m,
      by rw [map_one]; exact Matrix.SpecialLinearGroup.coeToGL_det m,
      (triD4LineSL3_apply k K m
        (by rw [map_one]; exact Matrix.SpecialLinearGroup.coeToGL_det m)).symm⟩
  · rintro ⟨g, h, rfl⟩
    have hg : Matrix.GeneralLinearGroup.det g = 1 := by rw [h, map_one]
    let m : Matrix.SpecialLinearGroup (Fin 3) k :=
      ⟨(g : Matrix (Fin 3) (Fin 3) k), by
        have := congrArg Units.val hg
        simpa using this⟩
    have hSL3 : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL m) =
        Units.map (Algebra.norm k (S := K)) 1 := by
      rw [map_one]; exact Matrix.SpecialLinearGroup.coeToGL_det m
    have htoGL : Matrix.SpecialLinearGroup.toGL m = g := Units.ext rfl
    refine ⟨m, ?_⟩
    rw [triD4LineSL3_apply k K m hSL3]
    refine (triD4LineMk_eq_mk_iff k K (Matrix.SpecialLinearGroup.toGL m) g 1 1 hSL3 h).2
      ⟨1, ?_, ?_⟩
    · rw [map_one, one_mul]; exact htoGL.symm
    · rw [map_one, one_mul]

private lemma triD4Line_det_mul_norm (k K : Type) [Field k] [Field K] [Algebra k K]
    (g g' : GL (Fin 3) k) (c c' : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c') :
    Matrix.GeneralLinearGroup.det (g * g') =
      Units.map (Algebra.norm k (S := K)) (c * c') := by
  rw [map_mul, map_mul, h, h']

private lemma triD4Line_det_mul_one_norm (k K : Type) [Field k] [Field K] [Algebra k K]
    (g g' : GL (Fin 3) k) (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (hg' : Matrix.GeneralLinearGroup.det g' = 1) :
    Matrix.GeneralLinearGroup.det (g * g') =
      Units.map (Algebra.norm k (S := K)) (c * 1) := by
  rw [map_mul, map_mul, hg', h, mul_one, map_one, mul_one]

private lemma triD4Line_det_inv_norm (k K : Type) [Field k] [Field K] [Algebra k K]
    (g : GL (Fin 3) k) (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c) :
    Matrix.GeneralLinearGroup.det g⁻¹ =
      Units.map (Algebra.norm k (S := K)) c⁻¹ := by
  rw [map_inv, map_inv, h]

theorem triD4LineMk_mul_SL3_mul_inv (k K : Type) [Field k] [Field K] [Algebra k K]
    (g : GL (Fin 3) k) (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (m m' : Matrix.SpecialLinearGroup (Fin 3) k)
    (hm : Matrix.SpecialLinearGroup.toGL m' = g * Matrix.SpecialLinearGroup.toGL m * g⁻¹) :
    triD4LineMk k K g c h * triD4LineSL3 k K m * (triD4LineMk k K g c h)⁻¹ =
      triD4LineSL3 k K m' := by
  have hSL3 : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL m) =
      Units.map (Algebra.norm k (S := K)) 1 := by
    rw [map_one]; exact Matrix.SpecialLinearGroup.coeToGL_det m
  have hdet1 := triD4Line_det_mul_one_norm k K g (Matrix.SpecialLinearGroup.toGL m) c h
    (Matrix.SpecialLinearGroup.coeToGL_det m)
  rw [triD4LineSL3_apply k K m hSL3]
  rw [triD4LineMk_inv k K g c h (triD4Line_det_inv_norm k K g c h)]
  rw [triD4LineMk_mul k K g (Matrix.SpecialLinearGroup.toGL m) c 1 h hSL3 hdet1]
  rw [triD4LineMk_mul k K (g * Matrix.SpecialLinearGroup.toGL m) g⁻¹ (c * 1) c⁻¹ hdet1
    (triD4Line_det_inv_norm k K g c h)
    (triD4Line_det_mul_norm k K (g * Matrix.SpecialLinearGroup.toGL m) g⁻¹ (c * 1) c⁻¹ hdet1
      (triD4Line_det_inv_norm k K g c h))]
  rw [triD4LineSL3_apply k K m'
    (by rw [map_one]; exact Matrix.SpecialLinearGroup.coeToGL_det m')]
  rw [triD4LineMk_eq_mk_iff]
  refine ⟨1, ?_, ?_⟩
  · rw [map_one, one_mul]; exact hm
  · rw [map_one]; simp

theorem triD4LineSL3_mem_center_iff (k K : Type) [Field k] [Field K] [Algebra k K]
    (m : Matrix.SpecialLinearGroup (Fin 3) k) :
    triD4LineSL3 k K m ∈ Subgroup.center (TriD4LineX k K) ↔
      ∃ μ : k, (m : Matrix (Fin 3) (Fin 3) k) = Matrix.scalar (Fin 3) μ := by
  rw [triD4LineSL3_apply k K m
    (by rw [map_one]; exact Matrix.SpecialLinearGroup.coeToGL_det m),
    triD4LineMk_mem_center_iff]
  constructor
  · rintro ⟨μ, hμ⟩
    exact ⟨(μ : k), congrArg (fun A : GL (Fin 3) k => (A : Matrix (Fin 3) (Fin 3) k)) hμ⟩
  · rintro ⟨μ, hμ⟩
    have hμ3 : μ ^ 3 = 1 := by
      have h := m.2
      rw [hμ, triD4Line_det_scalar_three] at h
      exact h
    have hμ0 : μ ≠ 0 := by rintro rfl; norm_num at hμ3
    refine ⟨Units.mk0 μ hμ0, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro p q
    have hmat : (m : Matrix (Fin 3) (Fin 3) k) =
        (Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0) :
          Matrix (Fin 3) (Fin 3) k) := by
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
      exact hμ
    simpa using congrFun (congrFun hmat p) q

theorem triD4Line_diagonal_eq_scalar_mul_pow (k : Type) [Field k] (ω : k) (hω : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (t : Fin 3 → k) (ht : ∀ i, t i ^ 3 = 1) (hdet : t 0 * t 1 * t 2 = 1) :
    ∃ a b : ℕ, Matrix.diagonal t =
      Matrix.scalar (Fin 3) (ω ^ a) * Matrix.diagonal ![1, ω, ω ^ 2] ^ b := by
  have hprim := triD4Line_isPrimitiveRoot_cube k ω hω hω1
  obtain ⟨a0, ha0lt, ha0⟩ := hprim.eq_pow_of_pow_eq_one (ht 0)
  obtain ⟨a1, ha1lt, ha1⟩ := hprim.eq_pow_of_pow_eq_one (ht 1)
  obtain ⟨a2, ha2lt, ha2⟩ := hprim.eq_pow_of_pow_eq_one (ht 2)
  have ht_eq : t = ![ω ^ a0, ω ^ a1, ω ^ a2] := by
    funext i; fin_cases i <;> simp [ha0, ha1, ha2]
  have hprod : ω ^ (a0 + a1 + a2) = 1 := by
    have h := hdet
    rw [ht_eq] at h
    simpa [← pow_add] using h
  have hdvd : 3 ∣ a0 + a1 + a2 := (hprim.pow_eq_one_iff_dvd (a0 + a1 + a2)).1 hprod
  refine ⟨a0, (a1 + 3 - a0) % 3, ?_⟩
  rw [ht_eq]
  simp only [Matrix.scalar_apply, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_eq_diagonal_iff]
  intro i
  fin_cases i
  · simp
  · simp only [Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Nat.succ_eq_add_one, Nat.reduceAdd]
    rw [← pow_add]
    exact triD4Line_pow_eq_of_mod_three hω (show a1 % 3 = (a0 + (a1 + 3 - a0) % 3) % 3 by omega)
  · simp only [Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Nat.succ_eq_add_one, Nat.reduceAdd]
    rw [← pow_mul, ← pow_add]
    exact triD4Line_pow_eq_of_mod_three hω
      (show a2 % 3 = (a0 + 2 * ((a1 + 3 - a0) % 3)) % 3 by omega)

theorem triD4LineX_exists_conj_diagonal_of_le_N0 (k K : Type) [Field k] [Field K] [Algebra k K]
    (z₀ : TriD4LineX k K) (hz₀ : orderOf z₀ = 3) (hzc : z₀ ∈ Subgroup.center (TriD4LineX k K))
    (E : Subgroup (TriD4LineX k K)) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hzE : z₀ ∈ E) (hEN : E ≤ triD4LineN0 k K) :
    ∃ (ω : k) (zz d : Matrix.SpecialLinearGroup (Fin 3) k) (s y : TriD4LineX k K),
      ω ^ 3 = 1 ∧ ω ≠ 1 ∧ (zz : Matrix (Fin 3) (Fin 3) k) = Matrix.scalar (Fin 3) ω ∧
      z₀ = triD4LineSL3 k K zz ∧
      (d : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal ![1, ω, ω ^ 2] ∧
      s ∈ E ∧ s ∉ Subgroup.zpowers z₀ ∧ (∀ e ∈ E, ∃ i j : ℕ, e = z₀ ^ i * s ^ j) ∧
      y ∈ triD4LineN0 k K ∧ y * s * y⁻¹ = triD4LineSL3 k K d := by
  have hz3 : z₀ ^ 3 = 1 := by simpa [hz₀] using pow_orderOf_eq_one z₀
  obtain ⟨zz, hzz⟩ : ∃ zz : Matrix.SpecialLinearGroup (Fin 3) k,
      triD4LineSL3 k K zz = z₀ := by
    have h : z₀ ∈ (triD4LineSL3 k K).range := by
      rw [triD4LineSL3_range]; exact hEN hzE
    simpa [MonoidHom.mem_range] using h
  have hzc' : triD4LineSL3 k K zz ∈ Subgroup.center (TriD4LineX k K) := by rwa [hzz]
  obtain ⟨ω, hω_mat⟩ := (triD4LineSL3_mem_center_iff k K zz).1 hzc'
  have hω3 : ω ^ 3 = 1 := by
    have h := zz.2
    rw [hω_mat, triD4Line_det_scalar_three] at h
    exact h
  have hω1 : ω ≠ 1 := by
    intro h1
    have hzz1 : zz = 1 := by
      apply Subtype.ext
      rw [hω_mat, h1]
      simp
    have hz1 : z₀ = 1 := by rw [← hzz, hzz1, map_one]
    rw [hz1, orderOf_one] at hz₀
    norm_num at hz₀
  have hprim := triD4Line_isPrimitiveRoot_cube k ω hω3 hω1
  have hz0card : Nat.card ↥(Subgroup.zpowers z₀) = 3 := by rw [Nat.card_zpowers, hz₀]
  haveI : Finite ↥(Subgroup.zpowers z₀) :=
    Nat.finite_of_card_ne_zero (by rw [hz0card]; norm_num)
  have hnotle : ¬ E ≤ Subgroup.zpowers z₀ := by
    intro hle
    have hcard := Subgroup.card_le_of_le hle
    rw [hEc, hz0card] at hcard
    omega
  obtain ⟨s, hsE, hsz⟩ : ∃ s ∈ E, s ∉ Subgroup.zpowers z₀ := by
    by_contra h
    push Not at h
    exact hnotle h
  have hs3 : s ^ 3 = 1 := hE.2 s hsE
  have hz1 : z₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₀
    norm_num at hz₀
  have hgen : ∀ e ∈ E, ∃ i j : ℕ, e = z₀ ^ i * s ^ j :=
    triD4Line_exists_pow_mul_of_mem E hE.1 z₀ s hzE hsE hEc hz3 hz1 hs3 hsz
  obtain ⟨m, hm⟩ : ∃ m : Matrix.SpecialLinearGroup (Fin 3) k,
      triD4LineSL3 k K m = s := by
    have h : s ∈ (triD4LineSL3 k K).range := by
      rw [triD4LineSL3_range]; exact hEN hsE
    simpa [MonoidHom.mem_range] using h
  have hm3SL : m ^ 3 = 1 := by
    apply triD4LineSL3_injective k K
    rw [map_pow, hm, hs3, map_one]
  have hm3m : (m : Matrix (Fin 3) (Fin 3) k) ^ 3 = 1 := by
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) k =>
      (x : Matrix (Fin 3) (Fin 3) k)) hm3SL
    simpa using this
  have hnotscalar : ∀ μ : k, (m : Matrix (Fin 3) (Fin 3) k) ≠ Matrix.scalar (Fin 3) μ := by
    intro μ hμ
    have hμ3 : μ ^ 3 = 1 := by
      have h := m.2
      rw [hμ, triD4Line_det_scalar_three] at h
      exact h
    obtain ⟨i, _hi3, hi⟩ := hprim.eq_pow_of_pow_eq_one hμ3
    have hmzz : m = zz ^ i := by
      apply (Matrix.SpecialLinearGroup.toGL_inj m (zz ^ i)).1
      apply Matrix.GeneralLinearGroup.ext
      intro p q
      have hmat : (m : Matrix (Fin 3) (Fin 3) k) =
          ((zz : Matrix (Fin 3) (Fin 3) k)) ^ i := by
        rw [hμ, ← hi, hω_mat, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_pow,
          Matrix.diagonal_eq_diagonal_iff]
        intro r
        simp [Pi.pow_apply]
      simpa using congrFun (congrFun hmat p) q
    have hmem : s ∈ Subgroup.zpowers z₀ := by
      rw [← hm, hmzz, map_pow, hzz]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z₀) i
    exact hsz hmem
  obtain ⟨h, hdet_h, hconj⟩ :=
    triD4Line_exists_conj_diagonal k ω hω3 hω1 (m : Matrix (Fin 3) (Fin 3) k) hm3m m.2
      hnotscalar
  have hdetD : (Matrix.diagonal ![1, ω, ω ^ 2] : Matrix (Fin 3) (Fin 3) k).det = 1 :=
    triD4Line_det_diag_three k ω hω3
  let d : Matrix.SpecialLinearGroup (Fin 3) k := ⟨_, hdetD⟩
  let hh : Matrix.SpecialLinearGroup (Fin 3) k := ⟨h, hdet_h⟩
  let y : TriD4LineX k K := triD4LineSL3 k K hh
  have hconjSL : hh * m * hh⁻¹ = d := by
    apply (Matrix.SpecialLinearGroup.toGL_inj _ _).1
    have hHMDg : Matrix.SpecialLinearGroup.toGL hh * Matrix.SpecialLinearGroup.toGL m =
        Matrix.SpecialLinearGroup.toGL d * Matrix.SpecialLinearGroup.toGL hh := by
      apply Matrix.GeneralLinearGroup.ext
      intro p q
      have hmat : (Matrix.SpecialLinearGroup.toGL hh : Matrix (Fin 3) (Fin 3) k) *
          (Matrix.SpecialLinearGroup.toGL m : Matrix (Fin 3) (Fin 3) k) =
          (Matrix.SpecialLinearGroup.toGL d : Matrix (Fin 3) (Fin 3) k) *
          (Matrix.SpecialLinearGroup.toGL hh : Matrix (Fin 3) (Fin 3) k) := by
        simpa using hconj
      exact congrFun (congrFun hmat p) q
    rw [map_mul, map_mul, map_inv, hHMDg, mul_assoc, mul_inv_cancel, mul_one]
  have hyconj : y * s * y⁻¹ = triD4LineSL3 k K d := by
    rw [← hm, ← hconjSL]
    show triD4LineSL3 k K hh * triD4LineSL3 k K m * (triD4LineSL3 k K hh)⁻¹ =
      triD4LineSL3 k K (hh * m * hh⁻¹)
    rw [map_mul, map_mul, map_inv]
  have hyN0 : y ∈ triD4LineN0 k K := by
    rw [← triD4LineSL3_range]
    exact ⟨hh, rfl⟩
  exact ⟨ω, zz, d, s, y, hω3, hω1, hω_mat, hzz.symm, rfl, hsE, hsz, hgen, hyN0, hyconj⟩

end CFSG.StandardType
