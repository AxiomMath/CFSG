module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrArith
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType.SpJoinRefl



section Pure

variable {G : Type} [Group G] [Finite G]

theorem card_le_pow_of_weylOfType {p : ℕ} {Bs : Subgroup G} {ι : Type} [Fintype ι]
    {M : CoxeterMatrix ι} {A : Subgroup (MulAut ↥Bs)} (hW : GGWeylOfType p M A)
    (hfix : ∀ b : ↥Bs, (∀ ψ ∈ A, ψ b = b) → b = 1) : Nat.card Bs ≤ p ^ Fintype.card ι := by
  obtain ⟨e, he⟩ := hW
  let φ : ι → MulAut ↥Bs := fun i => ((e (M.simple i) : ↥A) : MulAut ↥Bs)
  let F : ι → Subgroup ↥Bs := fun i =>
    { carrier := {b | φ i b = b}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        exact map_one (φ i)
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  have hFcard : ∀ i, Nat.card (F i) * p = Nat.card ↥Bs := fun i => (he i).2
  have hFpos : ∀ i, 0 < Nat.card (F i) := fun i => by
    haveI : Nonempty ↥(F i) := ⟨⟨1, by simp [F]⟩⟩
    exact Nat.card_pos
  have hindex : ∀ i, (F i).index = p := fun i => by
    have h1 : Nat.card (F i) * (F i).index = Nat.card ↥Bs := Subgroup.card_mul_index (F i)
    exact Nat.mul_left_cancel (hFpos i) (by rw [h1, hFcard i])
  have hbot : (⨅ i, F i) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    refine hfix b ?_
    let f : M.Group →* MulAut ↥Bs := A.subtype.comp e.toMonoidHom
    have hbfix : ∀ i, φ i b = b := fun i => by
      simpa [F] using Subgroup.mem_iInf.mp hb i
    have hHsimple : ∀ i, M.simple i ∈
        (MulAction.stabilizer (MulAut ↥Bs) b).comap f := by
      intro i
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
      simpa [f, MulAut.smul_def] using hbfix i
    have htop : (MulAction.stabilizer (MulAut ↥Bs) b).comap f = ⊤ := by
      rw [eq_top_iff, ← M.toCoxeterSystem.subgroup_closure_range_simple]
      exact (Subgroup.closure_le _).mpr (by rintro x ⟨i, rfl⟩; exact hHsimple i)
    intro ψ hψ
    have hmem : e.symm ⟨ψ, hψ⟩ ∈ (MulAction.stabilizer (MulAut ↥Bs) b).comap f := by
      rw [htop]; exact Subgroup.mem_top _
    have hfixb : f (e.symm ⟨ψ, hψ⟩) • b = b :=
      MulAction.mem_stabilizer_iff.mp (Subgroup.mem_comap.mp hmem)
    simpa [f, MulAut.smul_def] using hfixb
  calc Nat.card Bs = (⊥ : Subgroup ↥Bs).index := by rw [Subgroup.index_bot]
    _ = (⨅ i, F i).index := by rw [hbot]
    _ ≤ ∏ i, (F i).index := Subgroup.index_iInf_le F
    _ = ∏ _i : ι, p := Finset.prod_congr rfl (fun i _ => hindex i)
    _ = p ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]

theorem card_orbit_mul_card_le {Bs : Subgroup G} {H R : Subgroup (MulAut ↥Bs)} (hRH : R ≤ H)
    (b : ↥Bs) (hfix : ∀ ψ ∈ R, ψ b = b) :
    Nat.card (MulAction.orbit H b) * Nat.card R ≤ Nat.card H := by
  have hstab : R.subgroupOf H ≤ MulAction.stabilizer H b := by
    intro ψ hψ
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, MulAut.smul_def]
    exact hfix (ψ : MulAut ↥Bs) (Subgroup.mem_subgroupOf.mp hψ)
  have hcardR : Nat.card (R.subgroupOf H) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv
  have hos : Nat.card (MulAction.orbit H b) * Nat.card (MulAction.stabilizer H b) =
      Nat.card H := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H b)
  calc Nat.card (MulAction.orbit H b) * Nat.card R
      = Nat.card (MulAction.orbit H b) * Nat.card (R.subgroupOf H) := by rw [hcardR]
    _ ≤ Nat.card (MulAction.orbit H b) * Nat.card (MulAction.stabilizer H b) :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hstab)
    _ = Nat.card H := hos

end Pure

section Pairing

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

private noncomputable def alg_unitGauge {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
    (P : ι → ι → K) (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) : ι → K
  | i => if _ : i = root then 1
      else -(alg_unitGauge P par root depth hdepth (par i)) * P i (par i)
termination_by i => depth i
decreasing_by exact hdepth i ‹i ≠ root›

private theorem alg_unitGauge_eq_of_ne_root {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
    (P : ι → ι → K) (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) {i : ι} (hi : i ≠ root) :
    alg_unitGauge P par root depth hdepth i =
      -(alg_unitGauge P par root depth hdepth (par i)) * P i (par i) := by
  rw [alg_unitGauge.eq_1, dif_neg hi]

private theorem alg_unitGauge_ne_zero {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
    (A : ι → ι → ℤ) (P : ι → ι → K) (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hP1 : ∀ i j, A i j = -1 → P i j * P j i = 1)
    (hpar : ∀ i j, i ≠ j →
      (A i j = -1 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) :
    ∀ i, alg_unitGauge P par root depth hdepth i ≠ 0 := by
  intro i
  induction hd : depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [alg_unitGauge.eq_1]
    split
    · exact one_ne_zero
    · rename_i hi
      have hine : i ≠ par i := by
        intro heq
        have h1 : depth (par i) < depth i := hdepth i hi
        have h2 : depth (par i) = depth i := congrArg depth heq.symm
        omega
      have hA : A i (par i) = -1 := (hpar i (par i) hine).mpr (Or.inl ⟨hi, rfl⟩)
      have hPne : P i (par i) ≠ 0 := by
        intro h0
        have := hP1 i (par i) hA
        rw [h0, zero_mul] at this
        exact one_ne_zero this.symm
      have hlt : depth (par i) < n := by rw [← hd]; exact hdepth i hi
      have ih' := ih (depth (par i)) hlt (par i) rfl
      exact mul_ne_zero (neg_ne_zero.mpr ih') hPne

private theorem alg_unitGauge_inv_mul_of_par {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
    (A : ι → ι → ℤ) (P : ι → ι → K) (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hP1 : ∀ i j, A i j = -1 → P i j * P j i = 1)
    (hpar : ∀ i j, i ≠ j →
      (A i j = -1 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i)
    {i j : ι} (hA : A i j = -1) (hir : i ≠ root) (hpi : par i = j) :
    (alg_unitGauge P par root depth hdepth i)⁻¹ *
      alg_unitGauge P par root depth hdepth j * P i j = -1 := by
  have hci : alg_unitGauge P par root depth hdepth i =
      -(alg_unitGauge P par root depth hdepth j * P i j) := by
    rw [alg_unitGauge_eq_of_ne_root P par root depth hdepth hir, hpi, neg_mul]
  have hcjne : alg_unitGauge P par root depth hdepth j ≠ 0 :=
    alg_unitGauge_ne_zero A P par root depth hP1 hpar hdepth j
  have hPne : P i j ≠ 0 := by
    intro h0
    have := hP1 i j hA
    rw [h0, zero_mul] at this
    exact one_ne_zero this.symm
  rw [hci, inv_neg]
  calc -(alg_unitGauge P par root depth hdepth j * P i j)⁻¹ *
        alg_unitGauge P par root depth hdepth j * P i j
      = -((alg_unitGauge P par root depth hdepth j * P i j)⁻¹ *
          (alg_unitGauge P par root depth hdepth j * P i j)) := by ring
    _ = -1 := by rw [inv_mul_cancel₀ (mul_ne_zero hcjne hPne)]

private theorem alg_unitGauge_inv_mul_of_par_symm {K : Type*} [Field K] {ι : Type*}
    [DecidableEq ι]
    (A : ι → ι → ℤ) (P : ι → ι → K) (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hP1 : ∀ i j, A i j = -1 → P i j * P j i = 1)
    (hpar : ∀ i j, i ≠ j →
      (A i j = -1 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i)
    {i j : ι} (hA : A i j = -1) (hjr : j ≠ root) (hpj : par j = i) :
    (alg_unitGauge P par root depth hdepth i)⁻¹ *
      alg_unitGauge P par root depth hdepth j * P i j = -1 := by
  have hcj : alg_unitGauge P par root depth hdepth j =
      -(alg_unitGauge P par root depth hdepth i * P j i) := by
    rw [alg_unitGauge_eq_of_ne_root P par root depth hdepth hjr, hpj, neg_mul]
  have hcine : alg_unitGauge P par root depth hdepth i ≠ 0 :=
    alg_unitGauge_ne_zero A P par root depth hP1 hpar hdepth i
  rw [hcj]
  calc (alg_unitGauge P par root depth hdepth i)⁻¹ *
        (-(alg_unitGauge P par root depth hdepth i * P j i)) * P i j
      = -((alg_unitGauge P par root depth hdepth i)⁻¹ *
          alg_unitGauge P par root depth hdepth i * (P j i * P i j)) := by ring
    _ = -1 := by
          rw [inv_mul_cancel₀ hcine, one_mul, mul_comm (P j i) (P i j), hP1 i j hA]

theorem exists_unit_gauge_of_tree {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
    (A : ι → ι → ℤ) (P : ι → ι → K) (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hAoff : ∀ i j, i ≠ j → A i j = 0 ∨ A i j = -1)
    (hP0 : ∀ i j, i ≠ j → A i j = 0 → P i j = 0)
    (hP1 : ∀ i j, A i j = -1 → P i j * P j i = 1)
    (hpar : ∀ i j, i ≠ j → (A i j = -1 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) :
    ∃ c : ι → K, (∀ i, c i ≠ 0) ∧ ∀ i j, i ≠ j → (c i)⁻¹ * c j * P i j = (A i j : K) := by
  refine ⟨alg_unitGauge P par root depth hdepth,
    alg_unitGauge_ne_zero A P par root depth hP1 hpar hdepth, ?_⟩
  intro i j hij
  rcases hAoff i j hij with h0 | h1
  · rw [hP0 i j hij h0, h0]
    simp
  · rcases (hpar i j hij).mp h1 with ⟨hir, hpi⟩ | ⟨hjr, hpj⟩
    · rw [h1]
      simpa using
        alg_unitGauge_inv_mul_of_par A P par root depth hP1 hpar hdepth h1 hir hpi
    · rw [h1]
      simpa using
        alg_unitGauge_inv_mul_of_par_symm A P par root depth hP1 hpar hdepth h1 hjr hpj

private theorem alg_linearIndependent_of_det_ne_zero {K V Γ : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype Γ] [DecidableEq Γ] (h : Γ → V) (α : Γ → Module.Dual K V)
    (hdet : (Matrix.of fun i j => α i (h j)).det ≠ 0) : LinearIndependent K h := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hv : Matrix.mulVec (Matrix.of fun i j => α i (h j)) g = 0 := by
    ext i
    have hi := congrArg (α i) hg
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hi
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← hi]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hv) i

theorem le_finrank_add_one_of_cartanA {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {r : ℕ} (h : Fin r → V) (α : Fin r → Module.Dual (ZMod p) V)
    (hP : ∀ i j, α i (h j) = (CartanMatrix.A r i j : ZMod p)) :
    r ≤ Module.finrank (ZMod p) V + 1 := by
  by_cases hp : p ∣ r + 1
  · have hr1 : 1 ≤ r := by
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have := Nat.le_of_dvd (by omega : 0 < r + 1) hp
      omega
    let e : Fin (r - 1) → Fin r := fun i => ⟨i.1, by omega⟩
    have hsub : (CartanMatrix.A r).submatrix e e = CartanMatrix.A (r - 1) := by
      ext i j
      simp only [Matrix.submatrix_apply, CartanMatrix.A, Matrix.of_apply]
      split_ifs with h1 h2 h3 <;> simp_all [Fin.ext_iff, e] <;> omega
    have hP' : ∀ i j : Fin (r - 1),
        α (e i) (h (e j)) = (CartanMatrix.A (r - 1) i j : ZMod p) := by
      intro i j
      rw [hP]
      congr 1
      exact congrFun (congrFun hsub i) j
    have hdet : (Matrix.of fun i j : Fin (r - 1) => α (e i) (h (e j))).det ≠ 0 := by
      have hmap : (Matrix.of fun i j : Fin (r - 1) => α (e i) (h (e j))) =
          (CartanMatrix.A (r - 1)).map (fun x : ℤ => (x : ZMod p)) := by
        ext i j; simp [Matrix.map_apply, hP']
      rw [hmap, ← Int.cast_det (CartanMatrix.A (r - 1)), CartanMatrix.A_det]
      intro h0
      have hdvd : p ∣ r := by
        have h1 : (p : ℤ) ∣ ((r - 1 : ℕ) : ℤ) + 1 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (((r - 1 : ℕ) : ℤ) + 1) p).mp h0
        have h2 : ((r - 1 : ℕ) : ℤ) + 1 = ((r : ℕ) : ℤ) := by
          have h3 : (r - 1 : ℕ) + 1 = r := by omega
          exact_mod_cast h3
        rw [h2] at h1
        exact Int.natCast_dvd_natCast.mp h1
      have h1 : p ∣ 1 := by
        have := Nat.dvd_sub hp hdvd
        simpa using this
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have := Nat.le_of_dvd (by norm_num : 0 < 1) h1
      omega
    have hli := alg_linearIndependent_of_det_ne_zero (fun i : Fin (r - 1) => h (e i))
      (fun i : Fin (r - 1) => α (e i)) (by simpa using hdet)
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    omega
  · have hdet : (Matrix.of fun i j => α i (h j)).det ≠ 0 := by
      have hmap : (Matrix.of fun i j => α i (h j)) =
          (CartanMatrix.A r).map (fun x : ℤ => (x : ZMod p)) := by
        ext i j; simp [Matrix.map_apply, hP]
      rw [hmap, ← Int.cast_det (CartanMatrix.A r), CartanMatrix.A_det]
      intro h0
      refine hp ?_
      have h1 : (p : ℤ) ∣ ((r : ℤ) + 1) :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd ((r : ℤ) + 1) p).mp h0
      have h2 : ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [h2] at h1
      exact Int.natCast_dvd_natCast.mp h1
    have hli := alg_linearIndependent_of_det_ne_zero h α hdet
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    omega

theorem le_finrank_of_cartanD (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {r : ℕ} (hr : 2 ≤ r) (h : Fin r → V)
    (α : Fin r → Module.Dual (ZMod p) V)
    (hP : ∀ i j, α i (h j) = (CartanMatrix.D r i j : ZMod p)) :
    r ≤ Module.finrank (ZMod p) V := by
  have hdet : (Matrix.of fun i j => α i (h j)).det ≠ 0 := by
    have hmap : (Matrix.of fun i j => α i (h j)) =
        (CartanMatrix.D r).map (fun x : ℤ => (x : ZMod p)) := by
      ext i j; simp [Matrix.map_apply, hP]
    rw [hmap, ← Int.cast_det (CartanMatrix.D r), CartanMatrix.D_det hr]
    intro h4
    have hdvd : (p : ℤ) ∣ (4 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd 4 p).mp h4
    have hdvd' : p ∣ 4 := Int.natCast_dvd_natCast.mp hdvd
    have hpprime : p.Prime := Fact.out
    have h2 : p ∣ 2 := by
      apply hpprime.dvd_of_dvd_pow (n := 2)
      simpa using hdvd'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp h2)
  have hli := alg_linearIndependent_of_det_ne_zero h α hdet
  have := hli.fintype_card_le_finrank
  simpa using this

end Pairing

section Arithmetic

private theorem alg_cubic_lt_pow {n : ℕ} (hn : 15 ≤ n) :
    (n + 1) * (n + 2) * (n + 3) < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    have hk2 : k + 4 < 2 * (k + 1) := by omega
    have hpos : 0 < (k + 2) * (k + 3) := by positivity
    calc (k + 1 + 1) * (k + 1 + 2) * (k + 1 + 3)
        = (k + 2) * (k + 3) * (k + 4) := by ring
      _ < (k + 2) * (k + 3) * (2 * (k + 1)) := Nat.mul_lt_mul_of_pos_left hk2 hpos
      _ = 2 * ((k + 1) * (k + 2) * (k + 3)) := by ring
      _ < 2 * 2 ^ k := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
      _ = 2 ^ k * 2 := by ring

private theorem alg_not_dvd_prod {n : ℕ} (hn : 4 ≤ n) :
    ¬ 2 ^ n ∣ (n + 1) * (n + 2) * (n + 3) := by
  by_cases hn15 : 15 ≤ n
  · have hlt := alg_cubic_lt_pow hn15
    intro h
    have := Nat.le_of_dvd (by positivity) h
    omega
  · interval_cases n <;> norm_num

private theorem alg_not_dvd_three {n : ℕ} (hn : 4 ≤ n) :
    ¬ 2 ^ n * n.factorial ∣ (n + 3).factorial := by
  intro h
  have h1 : (n + 3).factorial = (n + 3) * (n + 2) * (n + 1) * n.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]; ring
  rw [h1] at h
  have h2 : 2 ^ n ∣ (n + 3) * (n + 2) * (n + 1) :=
    Nat.dvd_of_mul_dvd_mul_right (Nat.factorial_pos n) h
  exact alg_not_dvd_prod hn (by simpa [mul_assoc, mul_comm, mul_left_comm] using h2)

theorem not_two_pow_mul_factorial_dvd {n k : ℕ} (hn : 4 ≤ n) (hk : k ≤ 3) :
    ¬ 2 ^ n * n.factorial ∣ (n + k).factorial := by
  by_cases hk2 : k ≤ 2
  · intro h
    exact not_dvd_two_pow_mul_factorial_C (by omega)
      (dvd_trans h (Nat.factorial_dvd_factorial (by omega)))
  · have hk3 : k = 3 := by omega
    subst hk3
    exact alg_not_dvd_three hn

end Arithmetic

end CFSG.StandardType.SpJoinRefl
