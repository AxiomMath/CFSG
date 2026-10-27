module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Open.StatedDefs
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.Open CFSG.Assembly.LowTwoRank

section Torus

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def diagGL (n : ℕ) (K : Type) [Field K] :
    (Fin n → Kˣ) →* GL (Fin n) K :=
  (Units.map (diagonalRingHom (Fin n) K : (Fin n → K) →* Matrix (Fin n) (Fin n) K)).comp
    (MulEquiv.piUnits (M := fun _ : Fin n => K)).symm.toMonoidHom

theorem diagGL_coe (n : ℕ) (a : Fin n → Kˣ) :
    ((diagGL n K a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal (fun i => (a i : K)) :=
  rfl

@[expose] def unitaryTorus (p f : ℕ) (n : ℕ) (K : Type) [Field K] : Subgroup (Fin n → Kˣ) where
  carrier := {a | (∀ i, a i ^ (p ^ f + 1) = 1) ∧ ∏ i, a i = 1}
  one_mem' := ⟨fun i => one_pow _, Finset.prod_const_one⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun i => by rw [Pi.mul_apply, mul_pow, ha, hb, one_mul], ?_⟩
    show ∏ i, a i * b i = 1
    rw [Finset.prod_mul_distrib, ha', hb', one_mul]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun i => by rw [Pi.inv_apply, inv_pow, ha, inv_one], ?_⟩
    show ∏ i, (a i)⁻¹ = 1
    rw [Finset.prod_inv_distrib, ha', inv_one]

theorem diagGL_mem_unitarySU (h : UnitaryFieldData p f K) {n : ℕ} {a : Fin n → Kˣ}
    (ha : a ∈ unitaryTorus p f n K) : diagGL n K a ∈ unitarySU p f K n := by
  obtain ⟨ha1, ha2⟩ := ha
  rw [mem_unitarySU_iff h, diagGL_coe, det_diagonal]
  refine ⟨?_, ?_⟩
  · have := congrArg (fun x : Kˣ => (x : K)) ha2
    simpa using this
  · rw [diagonal_map (by simp), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have := congrArg (fun x : Kˣ => (x : K)) (ha1 i)
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [h.bar_apply, ← pow_succ, this]

theorem mulSingle_two_mem {n : ℕ} {j k : Fin n} (hjk : j ≠ k) {x y : Kˣ}
    (hx : x ^ (p ^ f + 1) = 1) (hy : y ^ (p ^ f + 1) = 1) (hxy : x * y = 1) :
    (Pi.mulSingle j x * Pi.mulSingle k y : Fin n → Kˣ) ∈ unitaryTorus p f n K := by
  refine ⟨fun i => ?_, ?_⟩
  · by_cases hi : i = j
    · subst hi
      simp [Pi.mulSingle_apply, hjk, hx]
    · by_cases hk : i = k
      · subst hk
        simp [Pi.mulSingle_apply, hi, hy]
      · simp [Pi.mulSingle_apply, hi, hk]
  · rw [show (∏ i, (Pi.mulSingle j x * Pi.mulSingle k y : Fin n → Kˣ) i) =
        (∏ i, (Pi.mulSingle j x : Fin n → Kˣ) i) * ∏ i, (Pi.mulSingle k y : Fin n → Kˣ) i from
      Finset.prod_mul_distrib]
    simp [Pi.mulSingle_apply, hxy]

theorem diagGL_eq_scalar {n : ℕ} {a : Fin n → Kˣ} {c : Kˣ}
    (hc : diagGL n K a = Matrix.GeneralLinearGroup.scalar (Fin n) c) (i : Fin n) : a i = c := by
  have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i i) hc
  simpa [diagGL_coe, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, Units.ext_iff] using this

end Torus

section Proj

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

@[expose] noncomputable def torusSU (n : ℕ) : unitaryTorus p f n K →* unitarySU p f K n :=
  (((diagGL n K).comp (unitaryTorus p f n K).subtype).codRestrict (unitarySU p f K n)
    fun a => diagGL_mem_unitarySU h a.2)

@[expose] noncomputable def torusPSU (n : ℕ) : unitaryTorus p f n K →* unitaryPSU h n :=
  (unitaryProj h n).comp (torusSU h n)

theorem torusSU_coe (x : unitaryTorus p f n K) :
    ((torusSU h n x : unitarySU p f K n) : GL (Fin n) K) = diagGL n K x :=
  rfl

theorem exists_scalar_of_proj_eq_one {g : unitarySU p f K n} (hg : unitaryProj h n g = 1) :
    ∃ c : Kˣ, (g : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have : g ∈ unitaryScalars h n := by rw [← ker_unitaryProj, MonoidHom.mem_ker]; exact hg
  obtain ⟨c, -, -, hc⟩ := this
  exact ⟨c, hc⟩

theorem torusPSU_eq_one {x : unitaryTorus p f n K} (hx : torusPSU h n x = 1) (i j : Fin n) :
    (x : Fin n → Kˣ) i = (x : Fin n → Kˣ) j := by
  obtain ⟨c, hc⟩ := exists_scalar_of_proj_eq_one h hx
  rw [torusSU_coe] at hc
  rw [diagGL_eq_scalar hc i, diagGL_eq_scalar hc j]

theorem mulSingle_two_pow_three {n : ℕ} (j k : Fin n) {x y : Kˣ} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    (Pi.mulSingle j x * Pi.mulSingle k y : Fin n → Kˣ) ^ 3 = 1 := by
  rw [mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, hx, hy, Pi.mulSingle_one, Pi.mulSingle_one,
    one_mul]

theorem three_commuting_core (h : UnitaryFieldData p f K) (hn : 5 ≤ n) {w : Kˣ} (hw3 : w ^ 3 = 1)
    (hw1 : w ≠ 1) (hwq : w ^ (p ^ f + 1) = 1) {t : unitaryPSU h n} (ht : orderOf t = 2)
    (htc : ∀ x : unitaryTorus p f n K, ∀ i j : Fin n, i.val = 0 → j.val = 1 →
      (x : Fin n → Kˣ) i = (x : Fin n → Kˣ) j → Commute t (torusPSU h n x)) :
    ∃ u v : unitaryPSU h n, Commute t u ∧ Commute t v ∧ Commute u v ∧ orderOf u = 3 ∧
      orderOf v = 3 ∧ v ∉ Subgroup.zpowers u := by
  have _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  let i4 : Fin n := ⟨4, by omega⟩
  have hw2q : (w ^ 2) ^ (p ^ f + 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hwq, one_pow]
  have hw23 : (w ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hw3, one_pow]
  have hww : w * w ^ 2 = 1 := by rw [← pow_succ']; exact hw3
  have hau : (Pi.mulSingle i2 w * Pi.mulSingle i3 (w ^ 2) : Fin n → Kˣ) ∈ unitaryTorus p f n K :=
    mulSingle_two_mem (by simp [i2, i3, Fin.ext_iff]) hwq hw2q hww
  have hav : (Pi.mulSingle i3 w * Pi.mulSingle i4 (w ^ 2) : Fin n → Kˣ) ∈ unitaryTorus p f n K :=
    mulSingle_two_mem (by simp [i3, i4, Fin.ext_iff]) hwq hw2q hww
  let xu : unitaryTorus p f n K := ⟨_, hau⟩
  let xv : unitaryTorus p f n K := ⟨_, hav⟩
  have hu3 : xu ^ 3 = 1 := Subtype.ext (mulSingle_two_pow_three _ _ hw3 hw23)
  have hv3 : xv ^ 3 = 1 := Subtype.ext (mulSingle_two_pow_three _ _ hw3 hw23)
  have hu01 : (xu : Fin n → Kˣ) i0 = (xu : Fin n → Kˣ) i1 := by
    simp [xu, Pi.mulSingle_apply, i0, i1, i2, i3, Fin.ext_iff]
  have hv01 : (xv : Fin n → Kˣ) i0 = (xv : Fin n → Kˣ) i1 := by
    simp [xv, Pi.mulSingle_apply, i0, i1, i3, i4, Fin.ext_iff]
  refine ⟨torusPSU h n xu, torusPSU h n xv, htc xu i0 i1 rfl rfl hu01, htc xv i0 i1 rfl rfl hv01,
    (Commute.all xu xv).map (torusPSU h n), ?_, ?_, ?_⟩
  · refine orderOf_eq_prime (by rw [← map_pow, hu3, map_one]) fun h1 => hw1 ?_
    have := torusPSU_eq_one h h1 i2 i0
    simpa [xu, Pi.mulSingle_apply, i0, i2, i3, Fin.ext_iff] using this
  · refine orderOf_eq_prime (by rw [← map_pow, hv3, map_one]) fun h1 => hw1 ?_
    have := torusPSU_eq_one h h1 i3 i0
    simpa [xv, Pi.mulSingle_apply, i0, i3, i4, Fin.ext_iff] using this
  · rintro ⟨k, hk⟩
    have h1 : torusPSU h n ((xu ^ k)⁻¹ * xv) = 1 := by
      rw [map_mul, map_inv, map_zpow]
      change (_ ^ k)⁻¹ * _ = _
      have hk' : torusPSU h n xu ^ k = torusPSU h n xv := hk
      rw [hk', inv_mul_cancel]
    have := torusPSU_eq_one h h1 i0 i4
    simp [xu, xv, Pi.mulSingle_apply, i0, i2, i3, i4, Fin.ext_iff] at this
    apply hw1
    have h3 : w ^ 3 = w := by rw [pow_succ, ← this, one_mul]
    rwa [h3] at hw3

end Proj

section Involution

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem exists_involution_diag (hn : 5 ≤ n) (h2 : (2 : K) ≠ 0) (hq : Odd (p ^ f)) :
    ∃ t : unitaryPSU h n, orderOf t = 2 ∧
      ∀ x : unitaryTorus p f n K, Commute t (torusPSU h n x) := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have hm1 : (-1 : Kˣ) ^ (p ^ f + 1) = 1 := (Even.neg_one_pow (by simpa using hq.add_one))
  have hne : (-1 : Kˣ) ≠ 1 := by
    intro e
    apply h2
    have := congrArg (fun x : Kˣ => (x : K)) e
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this
  have hx : (Pi.mulSingle i0 (-1) * Pi.mulSingle i1 (-1) : Fin n → Kˣ) ∈ unitaryTorus p f n K :=
    mulSingle_two_mem (by simp [i0, i1, Fin.ext_iff]) hm1 hm1 (by rw [neg_mul_neg, one_mul])
  let x : unitaryTorus p f n K := ⟨_, hx⟩
  refine ⟨torusPSU h n x, orderOf_eq_prime ?_ fun h1 => hne ?_, fun y => (Commute.all x y).map _⟩
  · rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by
      rw [Subgroup.coe_pow, mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, neg_one_sq,
        Pi.mulSingle_one, Pi.mulSingle_one, one_mul]; rfl), map_one]
  · have := torusPSU_eq_one h h1 i0 i2
    simpa [x, Pi.mulSingle_apply, i0, i1, i2, Fin.ext_iff] using this

@[expose] def swapGL (n : ℕ) (K : Type) [Field K] (i j : Fin n) : GL (Fin n) K :=
  ⟨(Equiv.swap i j).permMatrix K, (Equiv.swap i j).permMatrix K, by
    rw [← permMatrix_mul, Equiv.swap_mul_self, permMatrix_one], by
    rw [← permMatrix_mul, Equiv.swap_mul_self, permMatrix_one]⟩

theorem swapGL_coe (i j : Fin n) :
    ((swapGL n K i j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Equiv.swap i j).permMatrix K := rfl

theorem swapGL_mul_self (i j : Fin n) : swapGL n K i j * swapGL n K i j = 1 :=
  Units.ext (by rw [Units.val_mul, swapGL_coe, ← permMatrix_mul, Equiv.swap_mul_self,
    permMatrix_one, Units.val_one])

theorem swapGL_mem (h : UnitaryFieldData p f K) (hK2 : (2 : K) = 0) {i j : Fin n} (hij : i ≠ j) :
    swapGL n K i j ∈ unitarySU p f K n := by
  rw [mem_unitarySU_iff h, swapGL_coe]
  refine ⟨?_, ?_⟩
  · rw [det_permutation, Equiv.Perm.sign_swap hij]
    have : (-1 : K) = 1 := by linear_combination -hK2
    simpa using this
  · have hm : ((Equiv.swap i j).permMatrix K).map h.bar = (Equiv.swap i j).permMatrix K := by
      ext a b
      simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      split_ifs <;> simp
    rw [hm, transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]

theorem swapGL_mul_diagGL (a : Fin n → Kˣ) {i j : Fin n} (hij : a i = a j) :
    swapGL n K i j * diagGL n K a = diagGL n K a * swapGL n K i j := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, swapGL_coe, diagGL_coe]
  ext r c
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq]
  by_cases hrc : Equiv.swap i j r = c
  · subst hrc
    have : a (Equiv.swap i j r) = a r := by
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · subst h1; exact hij.symm
      · subst h2; exact hij
      · rfl
    simp [this]
  · simp [hrc]

theorem exists_involution_swap (hn : 5 ≤ n) (hK2 : (2 : K) = 0) :
    ∃ t : unitaryPSU h n, orderOf t = 2 ∧ ∀ x : unitaryTorus p f n K, ∀ i j : Fin n, i.val = 0 →
      j.val = 1 → (x : Fin n → Kˣ) i = (x : Fin n → Kˣ) j → Commute t (torusPSU h n x) := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  let s : unitarySU p f K n := ⟨swapGL n K i0 i1, swapGL_mem h hK2 h01⟩
  refine ⟨unitaryProj h n s, orderOf_eq_prime ?_ fun h1 => ?_, ?_⟩
  · rw [← map_pow, show s ^ 2 = 1 from Subtype.ext (by
      rw [Subgroup.coe_pow, pow_two]; exact swapGL_mul_self _ _), map_one]
  · obtain ⟨c, hc⟩ := exists_scalar_of_proj_eq_one h h1
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i0 i1) hc
    simp [s, swapGL_coe, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, scalar_apply, diagonal_apply,
      h01, Matrix.GeneralLinearGroup.coe_scalar] at this
  · intro x i j hi hj hij
    have hi' : i = i0 := Fin.ext hi
    have hj' : j = i1 := Fin.ext hj
    subst hi' hj'
    have hc : Commute s (torusSU h n x) := by
      show s * torusSU h n x = torusSU h n x * s
      exact Subtype.ext (swapGL_mul_diagGL _ hij)
    exact hc.map (unitaryProj h n)

end Involution

section Main

theorem exists_unit_order_three {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hQ : p ^ f = 2 ∨ p ^ f = 5) :
    ∃ w : Kˣ, w ^ 3 = 1 ∧ w ≠ 1 ∧ w ^ (p ^ f + 1) = 1 := by
  have _ := h.finite
  have _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by
    rw [Nat.card_units, h.card, pow_mul']
  have hd : 3 ∣ Nat.card Kˣ := by
    rw [hc]; rcases hQ with e | e <;> rw [e] <;> decide
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 hd
  refine ⟨w, hw ▸ pow_orderOf_eq_one w, fun e => by simp [e] at hw, ?_⟩
  rw [← orderOf_dvd_iff_pow_eq_one, hw]
  rcases hQ with e | e <;> rw [e] <;> decide

theorem exists_three_rank_two_psu {S : Type} [Group S] {n p f : ℕ}
    (hM : StatedClassicalModel S .PSU n p f) (hn : 5 ≤ n) (hQ : p ^ f = 2 ∨ p ^ f = 5) :
    ∃ t u v : S, orderOf t = 2 ∧ t * u = u * t ∧ t * v = v * t ∧ u * v = v * u ∧
      orderOf u = 3 ∧ orderOf v = 3 ∧ v ∉ Subgroup.zpowers u := by
  obtain ⟨⟨hp, hf, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hcp : CharP K p := h.charP
  have e' : S ≃* unitaryPSU h n := e.trans (unitaryPSUEquiv h (by omega)).symm
  obtain ⟨w, hw3, hw1, hwq⟩ := exists_unit_order_three h hQ
  have hpp : p ∣ p ^ f := dvd_pow_self p (by omega)
  have key : ∃ t : unitaryPSU h n, orderOf t = 2 ∧ ∀ x : unitaryTorus p f n K, ∀ i j : Fin n,
      i.val = 0 → j.val = 1 → (x : Fin n → Kˣ) i = (x : Fin n → Kˣ) j →
        Commute t (torusPSU h n x) := by
    rcases hQ with hq | hq
    · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hq ▸ hpp)
      subst hp2
      exact exists_involution_swap h hn (by exact_mod_cast CharP.cast_eq_zero K 2)
    · have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hq ▸ hpp)
      subst hp5
      have h2 : (2 : K) ≠ 0 := fun h0 => by
        have := (CharP.cast_eq_zero_iff K 5 2).1 (by exact_mod_cast h0)
        omega
      obtain ⟨t, ht, htc⟩ := exists_involution_diag h hn h2 (by rw [hq]; decide)
      exact ⟨t, ht, fun x _ _ _ _ _ => htc x⟩
  obtain ⟨t, ht, htc⟩ := key
  obtain ⟨u, v, htu, htv, huv, hu, hv, huv'⟩ := three_commuting_core h hn hw3 hw1 hwq ht htc
  refine ⟨e'.symm t, e'.symm u, e'.symm v, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact ht
  · rw [← map_mul, ← map_mul]; exact congrArg e'.symm htu.eq
  · rw [← map_mul, ← map_mul]; exact congrArg e'.symm htv.eq
  · rw [← map_mul, ← map_mul]; exact congrArg e'.symm huv.eq
  · rw [MulEquiv.orderOf_eq]; exact hu
  · rw [MulEquiv.orderOf_eq]; exact hv
  · rintro ⟨k, hk⟩
    apply huv'
    refine ⟨k, ?_⟩
    have := congrArg e' hk
    simpa [map_zpow] using this

end Main

end CFSG.RankThree.PartTwo.Sec21.FF79
