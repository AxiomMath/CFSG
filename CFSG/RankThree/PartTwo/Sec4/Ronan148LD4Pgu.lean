module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.Open.PGLModelStated

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.Assembly.RankThreeEven (projImage projSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open Matrix (ProjGenLinGroup)
open Matrix

section Mat

variable {K : Type} [Field K]

@[expose] def nswap12 : GL (Fin 3) K :=
  ⟨!![-1, 0, 0; 0, 0, -1; 0, -1, 0], !![-1, 0, 0; 0, 0, -1; 0, -1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

@[expose] def nswap01 : GL (Fin 3) K :=
  ⟨!![0, -1, 0; -1, 0, 0; 0, 0, -1], !![0, -1, 0; -1, 0, 0; 0, 0, -1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_nswap12 :
    ((nswap12 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![-1, 0, 0; 0, 0, -1; 0, -1, 0] :=
  rfl

theorem coe_nswap01 :
    ((nswap01 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, -1, 0; -1, 0, 0; 0, 0, -1] :=
  rfl

theorem nswap12_sq : (nswap12 : GL (Fin 3) K) ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_nswap12, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [sq, mul_apply, Fin.sum_univ_three]

variable {p f : ℕ}

theorem nswap12_mem_slPi (h : UnitaryFieldData p f K) : nswap12 ∈ slPi false 3 (p ^ f) K := by
  rw [mem_slPi_false h]
  refine ⟨by rw [coe_nswap12, det_fin_three]; simp, ?_⟩
  rw [coe_nswap12]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, transpose_apply]

theorem nswap01_mem_slPi (h : UnitaryFieldData p f K) : nswap01 ∈ slPi false 3 (p ^ f) K := by
  rw [mem_slPi_false h]
  refine ⟨by rw [coe_nswap01, det_fin_three]; simp, ?_⟩
  rw [coe_nswap01]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, transpose_apply]

theorem diagE_mem_glPi (h : UnitaryFieldData p f K) {e : Kˣ} (he : (e : K) ^ (p ^ f + 1) = 1) :
    diagE e ∈ glPi false 3 (p ^ f) K := by
  rw [mem_glPi_false h, coe_diagE, diagonal_map (map_zero _), diagonal_transpose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i
  · change h.bar (e : K) * (e : K) = 1
    rw [UnitaryFieldData.bar_apply, ← pow_succ]
    exact he
  · simp
  · simp

theorem diagE_mul_nswap12 (e : Kˣ) : diagE e * (nswap12 : GL (Fin 3) K) = nswap12 * diagE e := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagE, coe_nswap12]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, diagonal]

theorem diagE_mul_diagTau (e : Kˣ) {τ : K} (hτ : τ ^ 3 = 1) :
    diagE e * diagTau hτ = diagTau hτ * diagE e := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagE, coe_diagTau]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, diagonal, mul_comm]

theorem diagE_pow_three {e : Kˣ} (he : e ^ 3 = 1) : diagE e ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_diagE, diagonal_pow, Units.val_one, ← diagonal_one]
  congr 1
  funext i
  fin_cases i
  · change (e : K) ^ 3 = 1
    rw [← Units.val_pow_eq_pow_val, he, Units.val_one]
  · simp
  · simp

theorem eq_one_of_mk_diagE_nswap01 {e : Kˣ}
    (h : ProjGenLinGroup.mk (diagE e * nswap01) = ProjGenLinGroup.mk (nswap01 * diagE e)) :
    e = 1 := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hu
  simp only [Units.val_mul, coe_diagE, coe_nswap01, GeneralLinearGroup.coe_scalar] at h'
  have h22 := congrFun (congrFun h' 2) 2
  have h01 := congrFun (congrFun h' 0) 1
  simp [mul_apply, Fin.sum_univ_three, diagonal, Matrix.scalar_apply] at h22 h01
  apply Units.ext
  rw [Units.val_one]
  rw [h22, Units.val_one, mul_one] at h01
  exact h01

theorem false_of_mk_diagTau_nswap12 {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (h : ProjGenLinGroup.mk (diagTau hτ * nswap12) =
      ProjGenLinGroup.mk (nswap12 * diagTau hτ)) : False := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hu
  simp only [Units.val_mul, coe_diagTau, coe_nswap12, GeneralLinearGroup.coe_scalar] at h'
  have h00 := congrFun (congrFun h' 0) 0
  have h12 := congrFun (congrFun h' 1) 2
  simp [mul_apply, Fin.sum_univ_three, Matrix.scalar_apply] at h00 h12
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hu1 : (u : K) = 1 := mul_left_cancel₀ hτ0 (by rw [mul_one]; exact h00)
  rw [hu1] at h12
  simp at h12
  rcases h12 with h | h
  · exact hτ1 h
  · apply hτ1
    rw [h] at hτ ⊢
    have h3 : (-1 : K) ^ 3 = -1 := by ring
    rw [h3] at hτ
    exact hτ

end Mat

section PSU

variable {p f : ℕ} {K : Type} [Field K]

theorem commutator_mem_psu (h : UnitaryFieldData p f K) {a b : ProjGenLinGroup (Fin 3) K}
    (ha : a ∈ projImage (glPi false 3 (p ^ f) K)) (hb : b ∈ projImage (glPi false 3 (p ^ f) K)) :
    a * b * a⁻¹ * b⁻¹ ∈ projImage (slPi false 3 (p ^ f) K) := by
  obtain ⟨A, hA, rfl⟩ := ha
  obtain ⟨B, hB, rfl⟩ := hb
  refine ⟨A * B * A⁻¹ * B⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  have hA' : A ∈ glPi false 3 (p ^ f) K := hA
  have hB' : B ∈ glPi false 3 (p ^ f) K := hB
  show A * B * A⁻¹ * B⁻¹ ∈ slPi false 3 (p ^ f) K
  rw [mem_slPi_iff (fun _ => h)]
  refine ⟨mul_mem (mul_mem (mul_mem hA' hB') (inv_mem hA')) (inv_mem hB'), ?_⟩
  have h1 : Matrix.GeneralLinearGroup.det (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (Matrix.GeneralLinearGroup.det A),
      mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
  rw [← Matrix.GeneralLinearGroup.val_det_apply, h1, Units.val_one]

theorem conj_mem_psu (h : UnitaryFieldData p f K) {a s : ProjGenLinGroup (Fin 3) K}
    (ha : a ∈ projImage (glPi false 3 (p ^ f) K)) (hs : s ∈ projImage (slPi false 3 (p ^ f) K)) :
    a * s * a⁻¹ ∈ projImage (slPi false 3 (p ^ f) K) := by
  obtain ⟨A, hA, rfl⟩ := ha
  obtain ⟨S, hS, rfl⟩ := hs
  refine ⟨A * S * A⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  have hA' : A ∈ glPi false 3 (p ^ f) K := hA
  have hS' : S ∈ slPi false 3 (p ^ f) K := hS
  show A * S * A⁻¹ ∈ slPi false 3 (p ^ f) K
  rw [mem_slPi_iff (fun _ => h)] at hS' ⊢
  refine ⟨mul_mem (mul_mem hA' hS'.1) (inv_mem hA'), ?_⟩
  have hdS : Matrix.GeneralLinearGroup.det S = 1 := Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hS'.2, Units.val_one])
  have h1 : Matrix.GeneralLinearGroup.det (A * S * A⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hdS, mul_one, mul_inv_cancel]
  rw [← Matrix.GeneralLinearGroup.val_det_apply, h1, Units.val_one]

theorem psu_le_pgu (h : UnitaryFieldData p f K) :
    projImage (slPi false 3 (p ^ f) K) ≤ projImage (glPi false 3 (p ^ f) K) :=
  Subgroup.map_mono (slPi_le_glPi (fun _ => h))

theorem card_projImage_slPi_false_mul (h : UnitaryFieldData p f K) :
    Nat.card (projImage (slPi false 3 (p ^ f) K)) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  rw [Nat.card_congr (psuEquivUnitary h).toEquiv, ← card_unitaryScalars h (by norm_num),
    ← KFacts.card_unitarySU_three h]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

theorem card_psu_eq_card_projSU {n : ℕ} (h : UnitaryFieldData 2 n K) :
    Nat.card (projImage (slPi false 3 (2 ^ n) K)) = Nat.card (projSU 3 2 n) := by
  have hGF : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
    ⟨Nat.prime_two, h.one_le, GaloisField.card 2 (2 * n) (by have := h.one_le; omega)⟩
  have h1 := card_projImage_slPi_false_mul h
  have h2 := card_projImage_slPi_false_mul hGF
  rw [← CFSG.PGLModel.projImage_statedSU 3 2 n]
  have hg : 0 < Nat.gcd 3 (2 ^ n + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  exact Nat.eq_of_mul_eq_mul_right hg (h1.trans h2.symm)

end PSU

section Triple

variable {n : ℕ} {K : Type} [Field K]

theorem pgu3_triple (hn : Odd n) (h : UnitaryFieldData 2 n K)
    {Y : Subgroup ↥(projImage (glPi false 3 (2 ^ n) K))} (hYp : Group.IsPerfect Y)
    (π : Y →* projSU 3 2 n) (hπ : Function.Surjective π) :
    ∃ (u : ↥(projImage (glPi false 3 (2 ^ n) K))) (d t w : Y), u ^ 3 = 1 ∧ d ^ 3 = 1 ∧
      t ^ 2 = 1 ∧ u * (d : ↥(projImage (glPi false 3 (2 ^ n) K))) = d * u ∧
      u * (t : ↥(projImage (glPi false 3 (2 ^ n) K))) = t * u ∧
      u ∈ Subgroup.normalizer (Y : Set ↥(projImage (glPi false 3 (2 ^ n) K))) ∧
      π (d * t) ≠ π (t * d) ∧
      ∀ w' : Y, (w' : ↥(projImage (glPi false 3 (2 ^ n) K))) = u * w * u⁻¹ → π w' ≠ π w := by
  classical
  have := h.finite
  haveI : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  haveI : Finite (ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * n))) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  set S : Subgroup ↥(projImage (glPi false 3 (2 ^ n) K)) :=
    (projImage (slPi false 3 (2 ^ n) K)).subgroupOf (projImage (glPi false 3 (2 ^ n) K)) with hS
  have hYS : Y ≤ S := by
    intro y hy
    have h1 : (⟨y, hy⟩ : Y) ∈ commutator Y := by
      rw [hYp.commutator_eq_top]
      exact Subgroup.mem_top _
    have h2 : y ∈ (commutator Y).map Y.subtype := ⟨_, h1, rfl⟩
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h2
    refine (Subgroup.commutator_le.mpr fun a _ b _ => ?_) h2
    rw [hS, Subgroup.mem_subgroupOf, commutatorElement_def]
    exact commutator_mem_psu h a.2 b.2
  have hScard : Nat.card S = Nat.card (projSU 3 2 n) := by
    rw [hS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (psu_le_pgu h)).toEquiv]
    exact card_psu_eq_card_projSU h
  have hYcard : Nat.card (projSU 3 2 n) ≤ Nat.card Y := Nat.card_le_card_of_surjective _ hπ
  have hYeq : Y = S := Subgroup.eq_of_le_of_card_ge hYS (by rw [hScard]; exact hYcard)
  have hπi : Function.Injective π := by
    have hc : Nat.card Y = Nat.card (projSU 3 2 n) := le_antisymm
      (by rw [hYeq, hScard]) hYcard
    obtain ⟨e⟩ := (Finite.card_eq (α := Y) (β := projSU 3 2 n)).mp hc
    exact (Finite.injective_iff_surjective_of_equiv e).mpr hπ
  have hmemS : ∀ (g : GL (Fin 3) K) (hg : g ∈ slPi false 3 (2 ^ n) K),
      (⟨ProjGenLinGroup.mk g, psu_le_pgu h ⟨g, hg, rfl⟩⟩ :
        ↥(projImage (glPi false 3 (2 ^ n) K))) ∈ Y := by
    intro g hg
    rw [hYeq]
    exact ⟨g, hg, rfl⟩
  have hq3 : (2 ^ n) % 3 = 2 := by
    obtain ⟨r, rfl⟩ := hn
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hPi : PiField false 2 n K := ⟨Nat.prime_two, h.one_le, by
    rw [h.card, piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩
  obtain ⟨τ, hτ3, hτ1⟩ := exists_tau hPi hq3
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ3
  set e : Kˣ := Units.mk0 τ hτ0 with he
  have he3 : e ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, he, Units.val_mk0, hτ3,
    Units.val_one])
  have he1 : e ≠ 1 := fun h1 => hτ1 (by rw [← Units.val_mk0 hτ0, ← he, h1, Units.val_one])
  have heq : (e : K) ^ (2 ^ n + 1) = 1 := by
    rw [he, Units.val_mk0]
    exact pow_succ_eq_one_of_modThree hq3 hτ3
  have hdT : diagTau hτ3 ∈ slPi false 3 (2 ^ n) K :=
    diagTau_mem_slPi (fun _ => h) (fun _ => hq3) hτ3
  set u : ↥(projImage (glPi false 3 (2 ^ n) K)) :=
    ⟨ProjGenLinGroup.mk (diagE e), ⟨_, diagE_mem_glPi h heq, rfl⟩⟩ with hu
  set d : Y := ⟨_, hmemS _ hdT⟩ with hd
  set t : Y := ⟨_, hmemS _ (nswap12_mem_slPi h)⟩ with ht
  set w : Y := ⟨_, hmemS _ (nswap01_mem_slPi h)⟩ with hw
  refine ⟨u, d, t, w, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show ProjGenLinGroup.mk (diagE e) ^ 3 = 1
    rw [← map_pow, diagE_pow_three he3, map_one]
  · apply Subtype.ext
    apply Subtype.ext
    show ProjGenLinGroup.mk (diagTau hτ3) ^ 3 = 1
    rw [← map_pow, diagTau_pow_three hτ3, map_one]
  · apply Subtype.ext
    apply Subtype.ext
    show ProjGenLinGroup.mk (nswap12 : GL (Fin 3) K) ^ 2 = 1
    rw [← map_pow, nswap12_sq, map_one]
  · apply Subtype.ext
    show ProjGenLinGroup.mk (diagE e) * ProjGenLinGroup.mk (diagTau hτ3) =
      ProjGenLinGroup.mk (diagTau hτ3) * ProjGenLinGroup.mk (diagE e)
    rw [← map_mul, ← map_mul, diagE_mul_diagTau e hτ3]
  · apply Subtype.ext
    show ProjGenLinGroup.mk (diagE e) * ProjGenLinGroup.mk (nswap12 : GL (Fin 3) K) =
      ProjGenLinGroup.mk (nswap12 : GL (Fin 3) K) * ProjGenLinGroup.mk (diagE e)
    rw [← map_mul, ← map_mul, diagE_mul_nswap12 e]
  · apply Subgroup.mem_normalizer_fintype
    intro y hy
    rw [hYeq] at hy ⊢
    exact conj_mem_psu h u.2 hy
  · intro hπdt
    have h1 := hπi hπdt
    have h2 := congrArg (fun z : Y =>
      ((z : ↥(projImage (glPi false 3 (2 ^ n) K))) : ProjGenLinGroup (Fin 3) K)) h1
    simp only [Subgroup.coe_mul] at h2
    exact false_of_mk_diagTau_nswap12 hτ3 hτ1 (by rw [map_mul, map_mul]; exact h2)
  · intro w' hw' hπw
    have h1 := hπi hπw
    rw [h1] at hw'
    have h2 := congrArg (fun z : ↥(projImage (glPi false 3 (2 ^ n) K)) =>
      (z : ProjGenLinGroup (Fin 3) K)) hw'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    apply he1
    apply eq_one_of_mk_diagE_nswap01
    rw [map_mul, map_mul]
    change ProjGenLinGroup.mk (diagE e) * ProjGenLinGroup.mk (nswap01 : GL (Fin 3) K) =
      ProjGenLinGroup.mk (nswap01 : GL (Fin 3) K) * ProjGenLinGroup.mk (diagE e)
    calc ProjGenLinGroup.mk (diagE e) * ProjGenLinGroup.mk (nswap01 : GL (Fin 3) K)
        = (ProjGenLinGroup.mk (diagE e) * ProjGenLinGroup.mk (nswap01 : GL (Fin 3) K) *
            (ProjGenLinGroup.mk (diagE e))⁻¹) * ProjGenLinGroup.mk (diagE e) := by group
      _ = ProjGenLinGroup.mk (nswap01 : GL (Fin 3) K) * ProjGenLinGroup.mk (diagE e) := by
          rw [← h2]

end Triple

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
