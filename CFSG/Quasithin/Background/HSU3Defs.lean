module

public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.Quasithin

namespace H

namespace SU3

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K] {q : ℕ}

theorem mem_statedSU {A : GL (Fin 3) K} (h1 : (A : Matrix (Fin 3) (Fin 3) K).det = 1)
    (h2 : ((A : Matrix (Fin 3) (Fin 3) K).map (· ^ q))ᵀ * (A : Matrix (Fin 3) (Fin 3) K) = 1) :
    A ∈ StatedSU 3 q K :=
  Subgroup.subset_closure ⟨h1, h2⟩

@[expose] noncomputable def glOfDetOne (A : Matrix (Fin 3) (Fin 3) K) (h : A.det = 1) :
    GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [h]; exact one_ne_zero)

theorem coe_glOfDetOne (A : Matrix (Fin 3) (Fin 3) K) (h : A.det = 1) :
    (glOfDetOne A h : Matrix (Fin 3) (Fin 3) K) = A :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero A _

@[expose] def swapMat : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def cycMat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem swapMat_mulVec (v : Fin 3 → K) : swapMat *ᵥ v = ![v 1, v 0, v 2] := by
  ext i
  fin_cases i <;> simp [swapMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem cycMat_mulVec (v : Fin 3 → K) : cycMat *ᵥ v = ![v 2, v 0, v 1] := by
  ext i
  fin_cases i <;> simp [cycMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

variable [CharP K 2]

theorem neg_one_eq_one : (-1 : K) = 1 := CharTwo.neg_eq 1

theorem det_swapMat : (swapMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [swapMat, Matrix.det_fin_three]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
    cons_val_fin_one, head_cons, tail_cons, head_fin_const]
  ring_nf
  exact neg_one_eq_one

omit [CharP K 2] in
theorem det_cycMat : (cycMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [cycMat, Matrix.det_fin_three]
  simp

omit [CharP K 2] in
theorem map_pow_of_zero_one (hq : q ≠ 0) (A : Matrix (Fin 3) (Fin 3) K)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) : A.map (· ^ q) = A := by
  ext i j
  rcases hA i j with h | h <;> simp [h, zero_pow hq]

omit [CharP K 2] in
theorem swapMat_unitary (hq : q ≠ 0) :
    ((swapMat : Matrix (Fin 3) (Fin 3) K).map (· ^ q))ᵀ * swapMat = 1 := by
  rw [map_pow_of_zero_one hq]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [swapMat]

omit [CharP K 2] in
theorem cycMat_unitary (hq : q ≠ 0) :
    ((cycMat : Matrix (Fin 3) (Fin 3) K).map (· ^ q))ᵀ * cycMat = 1 := by
  rw [map_pow_of_zero_one hq]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [cycMat]

@[expose] noncomputable def swapSU : GL (Fin 3) K := glOfDetOne swapMat det_swapMat

@[expose] noncomputable def cycSU : GL (Fin 3) K := glOfDetOne cycMat det_cycMat

theorem swapSU_mem (hq : q ≠ 0) : (swapSU : GL (Fin 3) K) ∈ StatedSU 3 q K := by
  refine mem_statedSU ?_ ?_ <;> rw [swapSU, coe_glOfDetOne]
  · exact det_swapMat
  · exact swapMat_unitary hq

omit [CharP K 2] in
theorem cycSU_mem (hq : q ≠ 0) : (cycSU : GL (Fin 3) K) ∈ StatedSU 3 q K := by
  refine mem_statedSU ?_ ?_ <;> rw [cycSU, coe_glOfDetOne]
  · exact det_cycMat
  · exact cycMat_unitary hq

omit [CharP K 2] in
theorem diagonal_unitary {a b c : K} (ha : a ^ (q + 1) = 1) (hb : b ^ (q + 1) = 1)
    (hc : c ^ (q + 1) = 1) (hq : q ≠ 0) :
    ((Matrix.diagonal ![a, b, c]).map (· ^ q))ᵀ * Matrix.diagonal ![a, b, c] = 1 := by
  have hmap :
      (Matrix.diagonal ![a, b, c]).map (· ^ q) = Matrix.diagonal ![a ^ q, b ^ q, c ^ q] := by
    ext i j
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp
    · simp [Matrix.diagonal_apply_ne _ hij, zero_pow hq]
  rw [hmap, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp [← pow_succ, ha, hb, hc]

@[expose] noncomputable def diagSU (a b c : K) (h : a * b * c = 1) : GL (Fin 3) K :=
  glOfDetOne (Matrix.diagonal ![a, b, c]) (by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using h)

omit [CharP K 2] in
theorem diagSU_mem {a b c : K} (h : a * b * c = 1) (ha : a ^ (q + 1) = 1) (hb : b ^ (q + 1) = 1)
    (hc : c ^ (q + 1) = 1) (hq : q ≠ 0) : diagSU a b c h ∈ StatedSU 3 q K := by
  refine mem_statedSU ?_ ?_ <;> rw [diagSU, coe_glOfDetOne]
  · rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using h
  · exact diagonal_unitary ha hb hc hq

omit [CharP K 2] in
theorem diagSU_mulVec {a b c : K} (h : a * b * c = 1) (v : Fin 3 → K) :
    (diagSU a b c h : Matrix (Fin 3) (Fin 3) K) *ᵥ v = ![a * v 0, b * v 1, c * v 2] := by
  rw [diagSU, coe_glOfDetOne]
  ext i
  fin_cases i <;> simp [Matrix.mulVec_diagonal]

variable [Finite K]

omit [CharP K 2] in
theorem exists_orderOf_eq_succ (hK : Nat.card K = q ^ 2) (hq : 2 ≤ q) :
    ∃ ζ : Kˣ, orderOf ζ = q + 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = q ^ 2 - 1 := by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have : 1 ≤ q := by omega
    zify [Nat.one_le_pow 2 q (by omega), this]
    ring
  refine ⟨g ^ (q - 1), ?_⟩
  rw [orderOf_pow_of_dvd (by omega) (by rw [hord, hfac]; exact dvd_mul_right _ _), hord, hfac,
    Nat.mul_div_cancel_left _ (by omega)]

omit [CharP K 2] in
theorem subring_eq_top_of_lt_card (hK : Nat.card K = q ^ 2) (S : Subring K)
    (hS : q < Nat.card S) : S = ⊤ := by
  have hinv : ∀ s ∈ S, s⁻¹ ∈ S := by
    intro s hs
    by_cases h0 : s = 0
    · rw [h0, _root_.inv_zero]
      exact S.zero_mem
    · let u : Kˣ := Units.mk0 s h0
      have hu : u ^ orderOf u = 1 := pow_orderOf_eq_one u
      have hpos : 0 < orderOf u := orderOf_pos u
      have h1 : s * s ^ (orderOf u - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hpos]
        have h2 : (u : K) ^ orderOf u = 1 := by
          rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
        exact h2
      have : s⁻¹ = s ^ (orderOf u - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ h0]
        rwa [mul_comm] at h1
      rw [this]
      exact S.pow_mem hs _
  let T : Subfield K := { S with inv_mem' := hinv }
  have hT : (T : Set K) = S := rfl
  have : Finite T := Finite.of_injective _ Subtype.val_injective
  have hcard : Nat.card K = Nat.card T ^ Module.finrank T K := Module.natCard_eq_pow_finrank
  have hTS : Nat.card T = Nat.card S := rfl
  have hpos : 0 < Module.finrank T K := Module.finrank_pos
  have h1 : Module.finrank T K = 1 := by
    by_contra hne
    have h2 : 2 ≤ Module.finrank T K := by omega
    have h3 : Nat.card T ^ 2 ≤ Nat.card T ^ Module.finrank T K :=
      Nat.pow_le_pow_right Nat.card_pos h2
    have h4 : q ^ 2 < Nat.card T ^ 2 := Nat.pow_lt_pow_left (hTS ▸ hS) (by norm_num)
    omega
  rw [h1, pow_one] at hcard
  have htop : S.toAddSubgroup = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by
      change Nat.card ↥S = Nat.card K
      rw [← hTS, ← hcard])
  ext x
  constructor
  · intro _
    trivial
  · intro _
    have : x ∈ S.toAddSubgroup := by rw [htop]; trivial
    exact this

theorem hasScalarCommutant (hK : Nat.card K = q ^ 2) (hq : 2 ≤ q) :
    HasScalarCommutant (StatedSU 3 q K) := by
  intro f hf
  have hq0 : q ≠ 0 := by omega
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_succ hK hq
  have hζq : (ζ : K) ^ (q + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hζ, pow_orderOf_eq_one, Units.val_one]
  have hζ1 : (ζ : K) ≠ 1 := by
    intro h
    have : ζ = 1 := Units.ext h
    rw [this, orderOf_one] at hζ
    omega
  have hζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
  have hζinv : (ζ : K) * (ζ : K) ^ q = 1 := by rw [← pow_succ', hζq]
  have hζqq : ((ζ : K) ^ q) ^ (q + 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζq, one_pow]
  have hζq1 : (ζ : K) ^ q ≠ 1 := by
    intro h
    apply hζ1
    calc (ζ : K) = ζ * ζ ^ q := by rw [h, mul_one]
      _ = 1 := hζinv
  let D := diagSU (ζ : K) ((ζ : K) ^ q) 1 (by rw [mul_one, hζinv])
  have hD : D ∈ StatedSU 3 q K := diagSU_mem _ hζq hζqq (one_pow _) hq0
  have hline : ∀ c : K, ∃ d : K, f (Pi.single 2 c) = Pi.single 2 d := by
    intro c
    have hDv : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 2 c : Fin 3 → K) = Pi.single 2 c := by
      rw [diagSU_mulVec]
      ext i
      fin_cases i <;> simp
    have h1 := hf D hD (Pi.single 2 c)
    rw [hDv] at h1
    set w := f (Pi.single 2 c) with hw
    have hD' := diagSU_mulVec (a := (ζ : K)) (b := (ζ : K) ^ q) (c := 1)
      (by rw [mul_one, hζinv]) w
    have h0 := congrFun (h1.trans hD') 0
    have h1' := congrFun (h1.trans hD') 1
    simp only [Fin.isValue, cons_val_zero, cons_val_one] at h0 h1'
    refine ⟨w 2, ?_⟩
    ext i
    fin_cases i
    · have : (1 - (ζ : K)) * w 0 = 0 := by rw [sub_mul, one_mul, ← h0, sub_self]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h).symm hζ1
      · simp [h]
    · have : (1 - (ζ : K) ^ q) * w 1 = 0 := by rw [sub_mul, one_mul, ← h1', sub_self]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h).symm hζq1
      · simp [h]
    · simp
  choose φ hφ using hline
  have hφadd : ∀ c d, φ (c + d) = φ c + φ d := by
    intro c d
    have h1 : f (Pi.single 2 (c + d)) = f (Pi.single 2 c) + f (Pi.single 2 d) := by
      rw [← map_add, Pi.single_add]
    rw [hφ, hφ, hφ, ← Pi.single_add] at h1
    simpa using congrFun h1 2
  have hφ0 : φ 0 = 0 := by
    have := hφadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this |>.symm ▸ rfl
  have hC : cycSU ∈ StatedSU 3 q K := cycSU_mem hq0
  have hcyc : ∀ v, ((cycSU : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = ![v 2, v 0, v 1] := by
    intro v
    rw [cycSU, coe_glOfDetOne, cycMat_mulVec]
  have hφ0' : ∀ c, f (Pi.single 0 c) = Pi.single 0 (φ c) := by
    intro c
    have h1 := hf _ hC (Pi.single 2 c)
    rw [hcyc, hφ, hcyc] at h1
    have e1 : ∀ x : K, (![(Pi.single 2 x : Fin 3 → K) 2, (Pi.single 2 x : Fin 3 → K) 0,
        (Pi.single 2 x : Fin 3 → K) 1] : Fin 3 → K) = Pi.single 0 x := by
      intro x; ext i; fin_cases i <;> simp
    rw [e1, e1] at h1
    exact h1
  have hφ1' : ∀ c, f (Pi.single 1 c) = Pi.single 1 (φ c) := by
    intro c
    have h1 := hf _ hC (Pi.single 0 c)
    rw [hcyc, hφ0', hcyc] at h1
    have e1 : ∀ x : K, (![(Pi.single 0 x : Fin 3 → K) 2, (Pi.single 0 x : Fin 3 → K) 0,
        (Pi.single 0 x : Fin 3 → K) 1] : Fin 3 → K) = Pi.single 1 x := by
      intro x; ext i; fin_cases i <;> simp
    rw [e1, e1] at h1
    exact h1
  have hφν : ∀ ν : K, ν ^ (q + 1) = 1 → ∀ c, φ (ν * c) = ν * φ c := by
    intro ν hν c
    have hνq : ν ^ q * 1 * ν = 1 := by rw [mul_one, ← pow_succ, hν]
    have hνqq : (ν ^ q) ^ (q + 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hν, one_pow]
    have hE := diagSU_mem hνq hνqq (one_pow _) hν hq0
    have h1 := hf _ hE (Pi.single 2 c)
    rw [diagSU_mulVec, diagSU_mulVec, hφ] at h1
    have e1 : ∀ x : K, (![ν ^ q * (Pi.single 2 x : Fin 3 → K) 0, 1 * (Pi.single 2 x : Fin 3 → K) 1,
        ν * (Pi.single 2 x : Fin 3 → K) 2] : Fin 3 → K) = Pi.single 2 (ν * x) := by
      intro x; ext i; fin_cases i <;> simp
    rw [e1, e1, hφ] at h1
    simpa using congrFun h1 2
  let S : Subring K :=
    { carrier := {z | ∀ c, φ (z * c) = z * φ c}
      mul_mem' := fun {a b} ha hb c => by
        change φ (a * b * c) = a * b * φ c
        rw [mul_assoc, ha, hb, mul_assoc]
      one_mem' := fun c => by simp
      add_mem' := fun {a b} ha hb c => by
        change φ ((a + b) * c) = (a + b) * φ c
        rw [add_mul, hφadd, ha, hb, add_mul]
      zero_mem' := fun c => by simp [hφ0]
      neg_mem' := fun {a} ha => by rwa [CharTwo.neg_eq] }
  have hζS : ∀ i : ℕ, (ζ : K) ^ i ∈ S := fun i => hφν _ (by
    rw [← pow_mul, mul_comm, pow_mul, hζq, one_pow])
  have hSq : q < Nat.card S := by
    have hinj : Function.Injective (fun i : Option (Fin (q + 1)) =>
        (⟨match i with | none => 0 | some j => (ζ : K) ^ (j : ℕ), by
          cases i with
          | none => exact S.zero_mem
          | some j => exact hζS j⟩ : S)) := by
      intro i j hij
      have hij' := congrArg Subtype.val hij
      cases i with
      | none =>
        cases j with
        | none => rfl
        | some j => exact absurd hij'.symm (pow_ne_zero _ hζ0)
      | some i =>
        cases j with
        | none => exact absurd hij' (pow_ne_zero _ hζ0)
        | some j =>
          simp only at hij'
          have h1 : ζ ^ (i : ℕ) = ζ ^ (j : ℕ) := Units.ext (by simpa using hij')
          have := pow_injOn_Iio_orderOf (by rw [hζ]; exact i.isLt) (by rw [hζ]; exact j.isLt) h1
          exact congrArg some (Fin.ext this)
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at this
    omega
  have hStop := subring_eq_top_of_lt_card hK S hSq
  have hlin : ∀ z c, φ (z * c) = z * φ c := fun z => by
    have : z ∈ S := by rw [hStop]; trivial
    exact this
  have hlin' : ∀ z, φ z = φ 1 * z := fun z => by
    have := hlin z 1
    rw [mul_one] at this
    rw [this, mul_comm]
  refine ⟨φ 1, fun v => ?_⟩
  have hv : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) + Pi.single 2 (v 2) := by
    ext i; fin_cases i <;> simp
  rw [hv, map_add, map_add, hφ0', hφ1', hφ, hlin' (v 0), hlin' (v 1), hlin' (v 2)]
  ext i
  fin_cases i <;> simp

end SU3

end H

end CFSG.Quasithin
