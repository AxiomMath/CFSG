module

public import CFSG.RankThree.CentralLiftU.UnitaryBorelLift
public import CFSG.RankThree.CentralLiftU.UnitaryTorusWeylEven
public import CFSG.RankThree.CentralLiftU.UnitaryTorusWeylOdd
public import CFSG.RankThree.CentralLiftU.UnitaryTriRoots

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.CentralExt (liftSubgroup mem_liftSubgroup_iff sylow_map_eq_liftSubgroup
  exists_orderOf_eq_pow_of_pow_eq_one)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm sl2W sl2Diag
  coe_sl2W coe_sl2Diag)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (simpleRefl simpleRefl_inv)
open CFSG.LieType.Chevalley (uSL vSL coe_uSL coe_vSL)
open CFSG.RankThree.CentralLift.LinearRoots (uSL_add uSL_zero)

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K} {r ε : ℕ}

section Unipotent

theorem vSL_add {k : Type} [Field k] (a b : k) : vSL (a + b) = vSL a * vSL b := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_vSL, coe_vSL, coe_vSL]
  fin_cases x <;> fin_cases y <;> simp [mul_apply, Fin.sum_univ_two, add_comm]

theorem vSL_zero {k : Type} [Field k] : vSL (0 : k) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [coe_vSL]
  fin_cases x <;> fin_cases y <;> simp

theorem uSL_pow {k : Type} [Field k] (t : k) (n : ℕ) : uSL t ^ n = uSL ((n : k) * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, uSL_zero]
  | succ n ih => rw [pow_succ, ih, ← uSL_add, Nat.cast_succ, add_mul, one_mul]

theorem vSL_pow {k : Type} [Field k] (t : k) (n : ℕ) : vSL t ^ n = vSL ((n : k) * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, vSL_zero]
  | succ n ih => rw [pow_succ, ih, ← vSL_add, Nat.cast_succ, add_mul, one_mul]

theorem uSL_mul_sl2W {k : Type} [Field k] {t : k} (ht : t ≠ 0) :
    uSL t * (sl2W : SpecialLinearGroup (Fin 2) k) =
      vSL t⁻¹ * sl2Diag (Units.mk0 t ht) * uSL (-t⁻¹) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_sl2W, coe_sl2Diag,
    Units.val_mk0, Units.val_inv_eq_inv_val]
  fin_cases x <;> fin_cases y <;> simp [mul_apply, Fin.sum_univ_two, ht]

theorem natCast_char_eq_zero (h : UnitaryFieldData ℓ f K) : (ℓ : K) = 0 := by
  have := h.charP
  exact CharP.cast_eq_zero K ℓ

theorem natCast_char_eq_zero_fixed (h : UnitaryFieldData ℓ f K) : (ℓ : h.fixedField) = 0 :=
  Subtype.ext (by simp [natCast_char_eq_zero h])

theorem orderOf_map_uSL [Fact ℓ.Prime] {k : Type} [Field k] (hk : (ℓ : k) = 0) {G : Type*}
    [Group G] (ψ : SpecialLinearGroup (Fin 2) k →* G) (t : k) :
    ∃ n : ℕ, orderOf (ψ (uSL t)) = ℓ ^ n := by
  refine exists_orderOf_eq_pow_of_pow_eq_one (n := 1) ?_
  rw [pow_one, ← map_pow, uSL_pow, hk, zero_mul, uSL_zero, map_one]

theorem orderOf_map_vSL [Fact ℓ.Prime] {k : Type} [Field k] (hk : (ℓ : k) = 0) {G : Type*}
    [Group G] (ψ : SpecialLinearGroup (Fin 2) k →* G) (t : k) :
    ∃ n : ℕ, orderOf (ψ (vSL t)) = ℓ ^ n := by
  refine exists_orderOf_eq_pow_of_pow_eq_one (n := 1) ?_
  rw [pow_one, ← map_pow, vSL_pow, hk, zero_mul, vSL_zero, map_one]

theorem heisUMat_mul (u v u' v' : K) :
    heisUMat h u v * heisUMat h u' v' = heisUMat h (u + u') (v + v' - u * h.bar u') := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [heisUMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem heisLMat_mul (z t z' t' : K) :
    heisLMat h z t * heisLMat h z' t' = heisLMat h (z + z') (t + t' - h.bar z * z') := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [heisLMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem heisUMat_pow (u v : K) (n : ℕ) :
    heisUMat h u v ^ n = heisUMat h (n * u) (n * v - (n.choose 2 : ℕ) * (u * h.bar u)) := by
  induction n with
  | zero =>
    ext a b
    fin_cases a <;> fin_cases b <;> simp [heisUMat, one_apply]
  | succ n ih =>
    rw [pow_succ, ih, heisUMat_mul, Nat.choose_succ_succ, Nat.choose_one_right]
    congr 1
    · push_cast
      ring
    · push_cast
      ring

theorem heisLMat_pow (z t : K) (n : ℕ) :
    heisLMat h z t ^ n = heisLMat h (n * z) (n * t - (n.choose 2 : ℕ) * (h.bar z * z)) := by
  induction n with
  | zero =>
    ext a b
    fin_cases a <;> fin_cases b <;> simp [heisLMat, one_apply]
  | succ n ih =>
    rw [pow_succ, ih, heisLMat_mul, Nat.choose_succ_succ, Nat.choose_one_right]
    congr 1
    · push_cast
      ring
    · push_cast
      simp only [map_mul, map_natCast]
      ring

theorem heisUMat_char_pow (hℓ : ℓ ≠ 2) (u v : K) : heisUMat h u v ^ ℓ = 1 := by
  have hp := h.prime
  have h3 : 2 < ℓ := lt_of_le_of_ne hp.two_le (Ne.symm hℓ)
  have hc : ((ℓ.choose 2 : ℕ) : K) = 0 := by
    obtain ⟨m, hm⟩ := hp.dvd_choose_self (by norm_num : (2 : ℕ) ≠ 0) h3
    rw [hm, Nat.cast_mul, natCast_char_eq_zero h, zero_mul]
  rw [heisUMat_pow, natCast_char_eq_zero h, hc]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [heisUMat, one_apply]

theorem heisLMat_char_pow (hℓ : ℓ ≠ 2) (z t : K) : heisLMat h z t ^ ℓ = 1 := by
  have hp := h.prime
  have h3 : 2 < ℓ := lt_of_le_of_ne hp.two_le (Ne.symm hℓ)
  have hc : ((ℓ.choose 2 : ℕ) : K) = 0 := by
    obtain ⟨m, hm⟩ := hp.dvd_choose_self (by norm_num : (2 : ℕ) ≠ 0) h3
    rw [hm, Nat.cast_mul, natCast_char_eq_zero h, zero_mul]
  rw [heisLMat_pow, natCast_char_eq_zero h, hc]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [heisLMat, one_apply]

theorem gramSU_pow_eq_one {X : gramSU h (gramJ3 K)} {n : ℕ}
    (hX : ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ n = 1) : X ^ n = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hX, OneMemClass.coe_one, Units.val_one]

theorem orderOf_map_heisUpper [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) {G : Type*} [Group G]
    (ψ : gramSU h (gramJ3 K) →* G) {X : gramSU h (gramJ3 K)} (hX : X ∈ heisUpper h) :
    ∃ n : ℕ, orderOf (ψ X) = ℓ ^ n := by
  obtain ⟨u, v, -, hXm⟩ := hX
  refine exists_orderOf_eq_pow_of_pow_eq_one (n := 1) ?_
  rw [pow_one, ← map_pow, gramSU_pow_eq_one (by rw [hXm]; exact heisUMat_char_pow hℓ u v),
    map_one]

theorem orderOf_map_heisLower [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) {G : Type*} [Group G]
    (ψ : gramSU h (gramJ3 K) →* G) {X : gramSU h (gramJ3 K)} (hX : X ∈ heisLower h) :
    ∃ n : ℕ, orderOf (ψ X) = ℓ ^ n := by
  obtain ⟨z, t, -, hXm⟩ := hX
  refine exists_orderOf_eq_pow_of_pow_eq_one (n := 1) ?_
  rw [pow_one, ← map_pow, gramSU_pow_eq_one (by rw [hXm]; exact heisLMat_char_pow hℓ z t),
    map_one]

end Unipotent

section RootSets

variable {R : Type*} [Group R] {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)

variable (h) in
@[expose] noncomputable def xPlusEven (π : R →* hypSU h r 0) (i : Fin r) : Set R :=
  if hi : i.val + 1 < r then Set.range fun t : K => rhoLift h π (ne_succ_of_lt hi) (uSL t)
  else Set.range fun t : h.fixedField => iotaLift h π hc hc0 i (uSL t)

variable (h) in
@[expose] noncomputable def xMinusEven (π : R →* hypSU h r 0) (i : Fin r) : Set R :=
  if hi : i.val + 1 < r then Set.range fun t : K => rhoLift h π (ne_succ_of_lt hi) (vSL t)
  else Set.range fun t : h.fixedField => iotaLift h π hc hc0 i (vSL t)

variable (h) in
@[expose] noncomputable def xPlusOdd (π : R →* hypSU h r 1) (i : Fin r) : Set R :=
  if hi : i.val + 1 < r then Set.range fun t : K => rhoLift h π (ne_succ_of_lt hi) (uSL t)
  else kappaLift h π i '' heisUpper h

variable (h) in
@[expose] noncomputable def xMinusOdd (π : R →* hypSU h r 1) (i : Fin r) : Set R :=
  if hi : i.val + 1 < r then Set.range fun t : K => rhoLift h π (ne_succ_of_lt hi) (vSL t)
  else kappaLift h π i '' heisLower h

end RootSets

section Normalize

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r ε} (hS : UHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) [Fact ℓ.Prime] (hε : ε ≤ 1)
include hS hε

theorem sLift_mem_normalizer_liftSimpleKer (i : Fin r) :
    sLift h π hc hc0 i ∈
      Subgroup.normalizer (liftSubgroup ℓ π (simpleKerU h r ε i) : Set R) := by
  have hg := isLinePerm_pi_sLift h hS hc hc0 i
  have hg' : IsLinePerm (weylPerm (ε := ε) (simpleRefl r i))
      ((((π (sLift h π hc hc0 i))⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    have := hg.inv
    rwa [← weylPerm_inv, simpleRefl_inv] at this
  refine mem_normalizer_liftSubgroup hS.large.cen (isPGroup_simpleKerU hε i)
    (fun u hu => conj_mem_simpleKerU_of_isLinePerm hg hu) fun u hu => ?_
  have := conj_mem_simpleKerU_of_isLinePerm hg' hu
  rwa [inv_inv] at this

end Normalize

section Even

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r 0} (hS : UHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) [Fact ℓ.Prime]
include hS

theorem xPlusEven_mem_liftU {i : Fin r} {x : R} (hx : x ∈ xPlusEven h hc hc0 π i) :
    x ∈ liftSubgroup ℓ π (hypUnitriangular h r 0) := by
  unfold xPlusEven at hx
  split_ifs at hx with hi
  · obtain ⟨t, rfl⟩ := hx
    refine mem_liftSubgroup_of hS.large.cen (isPGroup_hypUnitriangular (Nat.zero_le 1)) ?_
      (orderOf_map_uSL (natCast_char_eq_zero h) _ t)
    rw [pi_rhoLift h hS]
    exact rhoU_uSL_mem _ (by simp) t
  · obtain ⟨t, rfl⟩ := hx
    refine mem_liftSubgroup_of hS.large.cen (isPGroup_hypUnitriangular (Nat.zero_le 1)) ?_
      (orderOf_map_uSL (natCast_char_eq_zero_fixed h) _ t)
    rw [pi_iotaLift h hS hc hc0]
    exact iotaU_uSL_mem hc hc0 i t

omit [Fact ℓ.Prime] in
theorem exists_xPlusEven_mul_mem {i : Fin r} {u : hypSU h r 0}
    (hu : u ∈ hypUnitriangular h r 0) :
    ∃ x ∈ xPlusEven h hc hc0 π i, (π x)⁻¹ * u ∈ simpleKerU h r 0 i := by
  by_cases hi : i.val + 1 < r
  · obtain ⟨t, ht⟩ := exists_rhoU_mul_mem_simpleKerU hi hu
    refine ⟨rhoLift h π (ne_succ_of_lt hi) (uSL t), ?_, ?_⟩
    · rw [xPlusEven, dite_eq_left hi]
      exact ⟨t, rfl⟩
    · rw [pi_rhoLift h hS]
      exact ht
  · obtain ⟨t, ht⟩ := exists_iotaU_mul_mem_simpleKerU hc hc0 hi hu
    refine ⟨iotaLift h π hc hc0 i (uSL t), ?_, ?_⟩
    · rw [xPlusEven, dite_eq_right hi]
      exact ⟨t, rfl⟩
    · rw [pi_iotaLift h hS hc hc0]
      exact ht

omit [Finite R] hS [Fact ℓ.Prime] in
theorem xPlusEven_mul_sLift {i : Fin r} {x : R} (hx : x ∈ xPlusEven h hc hc0 π i)
    (hx1 : x ≠ 1) :
    ∃ y ∈ xMinusEven h hc hc0 π i, ∃ z ∈ torusEven h π hc hc0,
      ∃ x' ∈ xPlusEven h hc hc0 π i, x * sLift h π hc hc0 i = y * z * x' := by
  by_cases hi : i.val + 1 < r
  · rw [xPlusEven, dite_eq_left hi] at hx
    obtain ⟨t, rfl⟩ := hx
    have ht : t ≠ 0 := by
      rintro rfl
      exact hx1 (by beta_reduce; rw [uSL_zero, map_one])
    refine ⟨rhoLift h π (ne_succ_of_lt hi) (vSL t⁻¹), by
        rw [xMinusEven, dite_eq_left hi]
        exact ⟨_, rfl⟩,
      hRho h π (ne_succ_of_lt hi) (Units.mk0 t ht), hRho_mem_torusEven h π hc hc0 _ _,
      rhoLift h π (ne_succ_of_lt hi) (uSL (-t⁻¹)), by
        rw [xPlusEven, dite_eq_left hi]
        exact ⟨_, rfl⟩, ?_⟩
    rw [sLift_of_lt h π hc hc0 hi, vRho, ← map_mul, uSL_mul_sl2W ht, map_mul, map_mul]
    rfl
  · rw [xPlusEven, dite_eq_right hi] at hx
    obtain ⟨t, rfl⟩ := hx
    have ht : t ≠ 0 := by
      rintro rfl
      exact hx1 (by beta_reduce; rw [uSL_zero, map_one])
    refine ⟨iotaLift h π hc hc0 i (vSL t⁻¹), by
        rw [xMinusEven, dite_eq_right hi]
        exact ⟨_, rfl⟩,
      hIota h π hc hc0 i (Units.mk0 t ht), hIota_mem_torusEven h π hc hc0 _ _,
      iotaLift h π hc hc0 i (uSL (-t⁻¹)), by
        rw [xPlusEven, dite_eq_right hi]
        exact ⟨_, rfl⟩, ?_⟩
    rw [sLift_of_not_lt h π hc hc0 hi, vIota, ← map_mul, uSL_mul_sl2W ht, map_mul, map_mul]
    rfl

theorem conj_xEven_or {v : R} (hv : v ∈ liftWeylU h π hc hc0 (torusEven h π hc hc0))
    (i : Fin r) :
    (∀ x ∈ xPlusEven h hc hc0 π i, v * x * v⁻¹ ∈ liftSubgroup ℓ π (hypUnitriangular h r 0)) ∨
      ∀ x ∈ xMinusEven h hc hc0 π i,
        v * x * v⁻¹ ∈ liftSubgroup ℓ π (hypUnitriangular h r 0) := by
  have hT := torusHyp_even h hS hc hc0
  have hw := (weylHomU h hS hc hc0 hT ⟨v, hv⟩).2
  have hg := isLinePerm_weylHomU h hS hc hc0 hT ⟨v, hv⟩
  have hU := isPGroup_hypUnitriangular (h := h) (r := r) (Nat.zero_le 1)
  have horder : ∀ x : R, (∃ m : ℕ, orderOf x = ℓ ^ m) →
      ∃ m : ℕ, orderOf (v * x * v⁻¹) = ℓ ^ m := fun x ⟨m, hm⟩ =>
    ⟨m, by rw [← hm]; exact MulEquiv.orderOf_eq (MulAut.conj v) x⟩
  by_cases hi : i.val + 1 < r
  · rcases conj_rhoU_or (Nat.zero_le 1) hw hg (ne_succ_of_lt hi) with hc' | hc'
    · left
      intro x hx
      rw [xPlusEven, dite_eq_left hi] at hx
      obtain ⟨t, rfl⟩ := hx
      refine mem_liftSubgroup_of hS.large.cen hU ?_
        (horder _ (orderOf_map_uSL (natCast_char_eq_zero h) _ t))
      rw [map_mul, map_mul, map_inv, pi_rhoLift h hS]
      exact hc' t
    · right
      intro x hx
      rw [xMinusEven, dite_eq_left hi] at hx
      obtain ⟨t, rfl⟩ := hx
      refine mem_liftSubgroup_of hS.large.cen hU ?_
        (horder _ (orderOf_map_vSL (natCast_char_eq_zero h) _ t))
      rw [map_mul, map_mul, map_inv, pi_rhoLift h hS]
      exact hc' t
  · rcases conj_iotaU_or hc hc0 (Nat.zero_le 1) hw hg i with hc' | hc'
    · left
      intro x hx
      rw [xPlusEven, dite_eq_right hi] at hx
      obtain ⟨t, rfl⟩ := hx
      refine mem_liftSubgroup_of hS.large.cen hU ?_
        (horder _ (orderOf_map_uSL (natCast_char_eq_zero_fixed h) _ t))
      rw [map_mul, map_mul, map_inv, pi_iotaLift h hS hc hc0]
      exact hc' t
    · right
      intro x hx
      rw [xMinusEven, dite_eq_right hi] at hx
      obtain ⟨t, rfl⟩ := hx
      refine mem_liftSubgroup_of hS.large.cen hU ?_
        (horder _ (orderOf_map_vSL (natCast_char_eq_zero_fixed h) _ t))
      rw [map_mul, map_mul, map_inv, pi_iotaLift h hS hc hc0]
      exact hc' t

end Even

section Odd

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r 1} (hS : UHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) [Fact ℓ.Prime]
include hS

theorem xPlusOdd_mem_liftU {i : Fin r} {x : R} (hx : x ∈ xPlusOdd h π i) :
    x ∈ liftSubgroup ℓ π (hypUnitriangular h r 1) := by
  unfold xPlusOdd at hx
  split_ifs at hx with hi
  · obtain ⟨t, rfl⟩ := hx
    refine mem_liftSubgroup_of hS.large.cen (isPGroup_hypUnitriangular le_rfl) ?_
      (orderOf_map_uSL (natCast_char_eq_zero h) _ t)
    rw [pi_rhoLift h hS]
    exact rhoU_uSL_mem _ (by simp) t
  · obtain ⟨X, hX, rfl⟩ := hx
    refine mem_liftSubgroup_of hS.large.cen (isPGroup_hypUnitriangular le_rfl) ?_
      (orderOf_map_heisUpper hS.odd _ hX)
    rw [pi_kappaLift h hS]
    exact kappaU_mem_of_heisUpper i hX

omit [Fact ℓ.Prime] in
theorem exists_xPlusOdd_mul_mem {i : Fin r} {u : hypSU h r 1}
    (hu : u ∈ hypUnitriangular h r 1) :
    ∃ x ∈ xPlusOdd h π i, (π x)⁻¹ * u ∈ simpleKerU h r 1 i := by
  by_cases hi : i.val + 1 < r
  · obtain ⟨t, ht⟩ := exists_rhoU_mul_mem_simpleKerU hi hu
    refine ⟨rhoLift h π (ne_succ_of_lt hi) (uSL t), ?_, ?_⟩
    · rw [xPlusOdd, dite_eq_left hi]
      exact ⟨t, rfl⟩
    · rw [pi_rhoLift h hS]
      exact ht
  · obtain ⟨X, hX, ht⟩ := exists_kappaU_mul_mem_simpleKerU hi hu
    refine ⟨kappaLift h π i X, ?_, ?_⟩
    · rw [xPlusOdd, dite_eq_right hi]
      exact ⟨X, hX, rfl⟩
    · rw [pi_kappaLift h hS]
      exact ht

omit [Fact ℓ.Prime] in
theorem xPlusOdd_mul_sLift {i : Fin r} {x : R} (hx : x ∈ xPlusOdd h π i) (hx1 : x ≠ 1) :
    ∃ y ∈ xMinusOdd h π i, ∃ z ∈ torusOdd h π,
      ∃ x' ∈ xPlusOdd h π i, x * sLift h π hc hc0 i = y * z * x' := by
  by_cases hi : i.val + 1 < r
  · rw [xPlusOdd, dite_eq_left hi] at hx
    obtain ⟨t, rfl⟩ := hx
    have ht : t ≠ 0 := by
      rintro rfl
      exact hx1 (by beta_reduce; rw [uSL_zero, map_one])
    refine ⟨rhoLift h π (ne_succ_of_lt hi) (vSL t⁻¹), by
        rw [xMinusOdd, dite_eq_left hi]
        exact ⟨_, rfl⟩,
      hRho h π (ne_succ_of_lt hi) (Units.mk0 t ht), (torusHyp_odd h hS hc hc0).rho _ _ _ _,
      rhoLift h π (ne_succ_of_lt hi) (uSL (-t⁻¹)), by
        rw [xPlusOdd, dite_eq_left hi]
        exact ⟨_, rfl⟩, ?_⟩
    rw [sLift_of_lt h π hc hc0 hi, vRho, ← map_mul, uSL_mul_sl2W ht, map_mul, map_mul]
    rfl
  · rw [xPlusOdd, dite_eq_right hi] at hx
    obtain ⟨X, hX, rfl⟩ := hx
    have hX1 : X ≠ 1 := by
      rintro rfl
      exact hx1 (map_one _)
    obtain ⟨u, v, huv, rfl, hv⟩ := heisU_v_ne_zero h hX hX1
    obtain ⟨hzt, huv', e⟩ := heisU_mul_iota3_sl2W h hc hc0 huv hv
    refine ⟨kappaLift h π i (heisL h hzt), by
        rw [xMinusOdd, dite_eq_right hi]
        exact ⟨_, heisL_mem h hzt, rfl⟩,
      hKappa h π i (Units.mk0 (c * v) (mul_ne_zero hc0 hv)), hKappa_mem_torusOdd h π i _,
      kappaLift h π i (heisU h huv'), by
        rw [xPlusOdd, dite_eq_right hi]
        exact ⟨_, heisU_mem h huv', rfl⟩, ?_⟩
    rw [sLift_of_not_lt h π hc hc0 hi, vIota, iotaLift_eq_kappaLift_comp h hS hc hc0,
      MonoidHom.comp_apply, ← map_mul, e, map_mul, map_mul]
    rfl

theorem conj_xOdd_or {v : R} (hv : v ∈ liftWeylU h π hc hc0 (torusOdd h π)) (i : Fin r) :
    (∀ x ∈ xPlusOdd h π i, v * x * v⁻¹ ∈ liftSubgroup ℓ π (hypUnitriangular h r 1)) ∨
      ∀ x ∈ xMinusOdd h π i, v * x * v⁻¹ ∈ liftSubgroup ℓ π (hypUnitriangular h r 1) := by
  have hT := torusHyp_odd h hS hc hc0
  have hw := (weylHomU h hS hc hc0 hT ⟨v, hv⟩).2
  have hg := isLinePerm_weylHomU h hS hc hc0 hT ⟨v, hv⟩
  have hU := isPGroup_hypUnitriangular (h := h) (r := r) (ε := 1) le_rfl
  have horder : ∀ x : R, (∃ m : ℕ, orderOf x = ℓ ^ m) →
      ∃ m : ℕ, orderOf (v * x * v⁻¹) = ℓ ^ m := fun x ⟨m, hm⟩ =>
    ⟨m, by rw [← hm]; exact MulEquiv.orderOf_eq (MulAut.conj v) x⟩
  by_cases hi : i.val + 1 < r
  · rcases conj_rhoU_or le_rfl hw hg (ne_succ_of_lt hi) with hc' | hc'
    · left
      intro x hx
      rw [xPlusOdd, dite_eq_left hi] at hx
      obtain ⟨t, rfl⟩ := hx
      refine mem_liftSubgroup_of hS.large.cen hU ?_
        (horder _ (orderOf_map_uSL (natCast_char_eq_zero h) _ t))
      rw [map_mul, map_mul, map_inv, pi_rhoLift h hS]
      exact hc' t
    · right
      intro x hx
      rw [xMinusOdd, dite_eq_left hi] at hx
      obtain ⟨t, rfl⟩ := hx
      refine mem_liftSubgroup_of hS.large.cen hU ?_
        (horder _ (orderOf_map_vSL (natCast_char_eq_zero h) _ t))
      rw [map_mul, map_mul, map_inv, pi_rhoLift h hS]
      exact hc' t
  · rcases conj_kappaU_or hw hg i with hc' | hc'
    · left
      intro x hx
      rw [xPlusOdd, dite_eq_right hi] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      refine mem_liftSubgroup_of hS.large.cen hU ?_
        (horder _ (orderOf_map_heisUpper hS.odd _ hX))
      rw [map_mul, map_mul, map_inv, pi_kappaLift h hS]
      exact hc' X hX
    · right
      intro x hx
      rw [xMinusOdd, dite_eq_right hi] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      refine mem_liftSubgroup_of hS.large.cen hU ?_
        (horder _ (orderOf_map_heisLower hS.odd _ hX))
      rw [map_mul, map_mul, map_inv, pi_kappaLift h hS]
      exact hc' X hX

end Odd


theorem not_dvd_card_ker {R : Type*} [Group R] [Finite R] {G : Type*} [Group G] {π : R →* G}
    {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ) (hpk : IsPGroup p π.ker) :
    ¬ℓ ∣ Nat.card π.ker := by
  obtain ⟨m, hm⟩ := hpk.exists_card_dvd_pow
  intro hdvd
  exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow (hdvd.trans hm))).symm

theorem odd_unitary_higher_cross_characteristic_central_prime_triangular_factorization_even
    {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hℓ : Odd ℓ) {r : ℕ}
    (hr : 2 ≤ r) {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) {R : Type*} [Group R] [Finite R]
    (π : R →* hypSU h r 0) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center R) (hpk : IsPGroup p π.ker) :
    (∀ P : Sylow ℓ ((hypUnitriangular h r 0).comap π),
      (P : Subgroup ((hypUnitriangular h r 0).comap π)).map
        ((hypUnitriangular h r 0).comap π).subtype =
        liftSubgroup ℓ π (hypUnitriangular h r 0)) ∧
    torusEven h π hc hc0 ≤
      Subgroup.normalizer (liftSubgroup ℓ π (hypUnitriangular h r 0) : Set R) ∧
    (∀ x : R, x ∈ liftSubgroup ℓ π (hypUnitriangular h r 0) ⊔ torusEven h π hc hc0 ↔
      ∃ u ∈ liftSubgroup ℓ π (hypUnitriangular h r 0), ∃ y ∈ torusEven h π hc hc0,
        x = u * y) ∧
    (liftSubgroup ℓ π (hypUnitriangular h r 0) ⊔ torusEven h π hc hc0).map π =
      hypBorel h r 0 ∧
    Function.Injective
      (π.comp (liftSubgroup ℓ π (hypUnitriangular h r 0) ⊔ torusEven h π hc hc0).subtype) ∧
    ∀ i : Fin r,
      (∀ g : hypSU h r 0, g ∈ simpleKerU h r 0 i ↔ ∃ A C : Matrix (Fin r) (Fin r) K,
        IsUnitriangular A ∧ C + (C.map h.bar)ᵀ = 0 ∧
        ((g : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) =
          evenMat h A C ∧
        if hi : i.val + 1 < r then A i ⟨i.val + 1, hi⟩ = 0 else C i i = 0) ∧
      (∀ P : Sylow ℓ ((simpleKerU h r 0 i).comap π),
        (P : Subgroup ((simpleKerU h r 0 i).comap π)).map
          ((simpleKerU h r 0 i).comap π).subtype =
          liftSubgroup ℓ π (simpleKerU h r 0 i)) ∧
      (∀ x : R, x ∈ liftSubgroup ℓ π (hypUnitriangular h r 0) ⊔ torusEven h π hc hc0 ↔
        ∃ x' ∈ xPlusEven h hc hc0 π i, ∃ u ∈ liftSubgroup ℓ π (simpleKerU h r 0 i),
          ∃ y ∈ torusEven h π hc hc0, x = x' * u * y) ∧
      sLift h π hc hc0 i ∈
        Subgroup.normalizer (liftSubgroup ℓ π (simpleKerU h r 0 i) : Set R) ∧
      sLift h π hc hc0 i ∈ Subgroup.normalizer (torusEven h π hc hc0 : Set R) ∧
      (∀ x ∈ xPlusEven h hc hc0 π i, x ≠ 1 →
        ∃ y ∈ xMinusEven h hc hc0 π i, ∃ z ∈ torusEven h π hc hc0,
          ∃ x' ∈ xPlusEven h hc hc0 π i, x * sLift h π hc hc0 i = y * z * x') ∧
      ∀ v ∈ liftWeylU h π hc hc0 (torusEven h π hc hc0),
        (∀ x ∈ xPlusEven h hc hc0 π i,
          v * x * v⁻¹ ∈ liftSubgroup ℓ π (hypUnitriangular h r 0)) ∨
        ∀ x ∈ xMinusEven h hc hc0 π i,
          v * x * v⁻¹ ∈ liftSubgroup ℓ π (hypUnitriangular h r 0) := by
  have hℓ2 : ℓ ≠ 2 := fun e => by
    rw [e] at hℓ
    exact absurd hℓ (by decide)
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have hS : UHyp h π := ⟨hℓ2, ⟨hπ, hcen, ⟨p, hp, hp3, hpk⟩⟩⟩
  have hT := torusHyp_even h hS hc hc0
  have hC := not_dvd_card_ker hp h.prime hpℓ hpk
  have hε : (0 : ℕ) ≤ 1 := Nat.zero_le 1
  have hHT : ∀ y ∈ torusEven h π hc hc0, π y ∈ hypTorus h r 0 := fun y hy => hT.diag hy
  have hTH : ∀ t ∈ hypTorus h r 0, ∃ y ∈ torusEven h π hc hc0, π y = t := by
    intro t ht
    refine ⟨thetaEvenEquiv h hS hc hc0 ⟨t, ht⟩, (thetaEvenEquiv h hS hc hc0 ⟨t, ht⟩).2, ?_⟩
    rw [coe_thetaEvenEquiv, pi_thetaEven]
  refine ⟨sylow_map_eq_liftSubgroup hcen (isPGroup_hypUnitriangular hε),
    le_normalizer_liftU hcen hε hHT, fun x => mem_liftBorel_iff hcen hε hHT,
    map_liftBorel hcen hε hHT hπ hC (by omega) hTH,
    injective_pi_liftBorel hcen hε hHT hC (injOn_pi_torusEven h hS hc hc0),
    fun i => ⟨fun g => mem_simpleKerU_iff_even,
      sylow_map_eq_liftSubgroup hcen (isPGroup_simpleKerU hε i),
      fun x => mem_liftBorel_iff_root hcen hε hHT i (fun _ hx => xPlusEven_mem_liftU hS hc hc0 hx)
        (fun u hu => exists_xPlusEven_mul_mem hS hc hc0 hu),
      sLift_mem_normalizer_liftSimpleKer hS hc hc0 hε i,
      liftWeylU_le_normalizer h hS hc hc0 hT (sLift_mem_liftWeylU h π hc hc0 _ i),
      fun x hx hx1 => xPlusEven_mul_sLift hc hc0 hx hx1,
      fun v hv => conj_xEven_or hS hc hc0 hv i⟩⟩

theorem odd_unitary_higher_cross_characteristic_central_prime_triangular_factorization_odd
    {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hℓ : Odd ℓ) {r : ℕ}
    (hr : 2 ≤ r) {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) {R : Type*} [Group R] [Finite R]
    (π : R →* hypSU h r 1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center R) (hpk : IsPGroup p π.ker) :
    (∀ P : Sylow ℓ ((hypUnitriangular h r 1).comap π),
      (P : Subgroup ((hypUnitriangular h r 1).comap π)).map
        ((hypUnitriangular h r 1).comap π).subtype =
        liftSubgroup ℓ π (hypUnitriangular h r 1)) ∧
    torusOdd h π ≤ Subgroup.normalizer (liftSubgroup ℓ π (hypUnitriangular h r 1) : Set R) ∧
    (∀ x : R, x ∈ liftSubgroup ℓ π (hypUnitriangular h r 1) ⊔ torusOdd h π ↔
      ∃ u ∈ liftSubgroup ℓ π (hypUnitriangular h r 1), ∃ y ∈ torusOdd h π, x = u * y) ∧
    (liftSubgroup ℓ π (hypUnitriangular h r 1) ⊔ torusOdd h π).map π = hypBorel h r 1 ∧
    Function.Injective
      (π.comp (liftSubgroup ℓ π (hypUnitriangular h r 1) ⊔ torusOdd h π).subtype) ∧
    ∀ i : Fin r,
      (∀ g : hypSU h r 1, g ∈ simpleKerU h r 1 i ↔
        ∃ (A C : Matrix (Fin r) (Fin r) K) (x : Fin r → K), IsUnitriangular A ∧
          C + (C.map h.bar)ᵀ = -vecMulVec x (fun j => h.bar (x j)) ∧
          ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
            oddDiag h A 1 * oddUni h x C ∧
          if hi : i.val + 1 < r then A i ⟨i.val + 1, hi⟩ = 0 else x i = 0 ∧ C i i = 0) ∧
      (∀ P : Sylow ℓ ((simpleKerU h r 1 i).comap π),
        (P : Subgroup ((simpleKerU h r 1 i).comap π)).map
          ((simpleKerU h r 1 i).comap π).subtype =
          liftSubgroup ℓ π (simpleKerU h r 1 i)) ∧
      (∀ x : R, x ∈ liftSubgroup ℓ π (hypUnitriangular h r 1) ⊔ torusOdd h π ↔
        ∃ x' ∈ xPlusOdd h π i, ∃ u ∈ liftSubgroup ℓ π (simpleKerU h r 1 i),
          ∃ y ∈ torusOdd h π, x = x' * u * y) ∧
      sLift h π hc hc0 i ∈
        Subgroup.normalizer (liftSubgroup ℓ π (simpleKerU h r 1 i) : Set R) ∧
      sLift h π hc hc0 i ∈ Subgroup.normalizer (torusOdd h π : Set R) ∧
      (∀ x ∈ xPlusOdd h π i, x ≠ 1 →
        ∃ y ∈ xMinusOdd h π i, ∃ z ∈ torusOdd h π,
          ∃ x' ∈ xPlusOdd h π i, x * sLift h π hc hc0 i = y * z * x') ∧
      ∀ v ∈ liftWeylU h π hc hc0 (torusOdd h π),
        (∀ x ∈ xPlusOdd h π i, v * x * v⁻¹ ∈ liftSubgroup ℓ π (hypUnitriangular h r 1)) ∨
        ∀ x ∈ xMinusOdd h π i, v * x * v⁻¹ ∈ liftSubgroup ℓ π (hypUnitriangular h r 1) := by
  have hℓ2 : ℓ ≠ 2 := fun e => by
    rw [e] at hℓ
    exact absurd hℓ (by decide)
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have hS : UHyp h π := ⟨hℓ2, ⟨hπ, hcen, ⟨p, hp, hp3, hpk⟩⟩⟩
  have hT := torusHyp_odd h hS hc hc0
  have hC := not_dvd_card_ker hp h.prime hpℓ hpk
  have hε : (1 : ℕ) ≤ 1 := le_rfl
  have hHT : ∀ y ∈ torusOdd h π, π y ∈ hypTorus h r 1 := fun y hy => hT.diag hy
  have hTH : ∀ t ∈ hypTorus h r 1, ∃ y ∈ torusOdd h π, π y = t := by
    intro t ht
    refine ⟨thetaOddEquiv h hS ⟨t, ht⟩, (thetaOddEquiv h hS ⟨t, ht⟩).2, ?_⟩
    rw [coe_thetaOddEquiv, pi_thetaOdd]
  refine ⟨sylow_map_eq_liftSubgroup hcen (isPGroup_hypUnitriangular hε),
    le_normalizer_liftU hcen hε hHT, fun x => mem_liftBorel_iff hcen hε hHT,
    map_liftBorel hcen hε hHT hπ hC (by omega) hTH,
    injective_pi_liftBorel hcen hε hHT hC (injOn_pi_torusOdd h hS),
    fun i => ⟨fun g => mem_simpleKerU_iff_odd,
      sylow_map_eq_liftSubgroup hcen (isPGroup_simpleKerU hε i),
      fun x => mem_liftBorel_iff_root hcen hε hHT i (fun _ hx => xPlusOdd_mem_liftU hS hx)
        (fun u hu => exists_xPlusOdd_mul_mem hS hu),
      sLift_mem_normalizer_liftSimpleKer hS hc hc0 hε i,
      liftWeylU_le_normalizer h hS hc hc0 hT (sLift_mem_liftWeylU h π hc hc0 _ i),
      fun x hx hx1 => xPlusOdd_mul_sLift hS hc hc0 hx hx1,
      fun v hv => conj_xOdd_or hS hc hc0 hv i⟩⟩

end CFSG.RankThree.CentralLiftU
