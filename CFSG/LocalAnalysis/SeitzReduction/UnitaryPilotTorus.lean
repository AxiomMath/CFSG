module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTorusBasic
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHsyl
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOddCore

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section Matrix

variable {K : Type*} [Field K] {n : ℕ}

theorem det_eq_zero_of_apply_eq_zero_of_lt {M : Matrix (Fin n) (Fin n) K} {J : Finset (Fin n)}
    (hJ : n < 2 * J.card) (h0 : ∀ i ∈ J, ∀ j ∈ J, M i j = 0) : M.det = 0 := by
  rw [Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  obtain ⟨i, hi, hσi⟩ : ∃ i ∈ J, σ i ∈ J := by
    by_contra hcon
    push Not at hcon
    have hsub : J.map σ.toEmbedding ⊆ Jᶜ := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hx
      exact Finset.mem_compl.2 (hcon i hi)
    have := Finset.card_le_card hsub
    rw [Finset.card_map, Finset.card_compl, Fintype.card_fin] at this
    omega
  rw [Finset.prod_eq_zero (f := fun j => M (σ j) j) (Finset.mem_univ i) (h0 _ hσi _ hi),
    smul_zero]

theorem eq_one_of_mul_eq_smul_mul {I : Finset (Fin n)} (hI : n < 2 * Iᶜ.card)
    {x A : Matrix (Fin n) (Fin n) K}
    (hx : ∀ i j, (i ∉ I ∨ j ∉ I) → x i j = (1 : Matrix (Fin n) (Fin n) K) i j)
    (hA : A.det ≠ 0) {c : K} (h : x * A = c • (A * x)) : c = 1 := by
  by_contra hc
  refine hA (det_eq_zero_of_apply_eq_zero_of_lt hI fun i hi j hj => ?_)
  have hi' : i ∉ I := Finset.mem_compl.1 hi
  have hj' : j ∉ I := Finset.mem_compl.1 hj
  have hxA : (x * A) i j = A i j := by
    rw [mul_apply, Finset.sum_eq_single i (fun k _ hki => by
      rw [hx i k (Or.inl hi'), one_apply_ne (Ne.symm hki), zero_mul]) (by simp),
      hx i i (Or.inl hi'), one_apply_eq, one_mul]
  have hAx : (A * x) i j = A i j := by
    rw [mul_apply, Finset.sum_eq_single j (fun k _ hkj => by
      rw [hx k j (Or.inr hj'), one_apply_ne hkj, mul_zero]) (by simp),
      hx j j (Or.inr hj'), one_apply_eq, mul_one]
  have h1 := congrFun (congrFun h i) j
  rw [hxA, Matrix.smul_apply, hAx, smul_eq_mul] at h1
  have h2 : (1 - c) * A i j = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hc))

theorem submatrix_pow_of_rows {r : ℕ} {e : Fin r → Fin n} (he : Function.Injective e)
    {J : Finset (Fin n)} (hJ : ∀ i, i ∈ J ↔ i ∈ Set.range e) {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i ∈ J, ∀ k ∉ J, M i k = 0) (m : ℕ) :
    (M ^ m).submatrix e e = (M.submatrix e e) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, submatrix_one _ he]
  | succ m ih => rw [pow_succ', pow_succ', LinearPilot.submatrix_mul_of_rows he hJ hM, ih]

theorem agrees_one_compl_of_submatrix_eq_one {r : ℕ} {e : Fin r → Fin n}
    (he : Function.Injective e) {J : Finset (Fin n)} (hJ : ∀ i, i ∈ J ↔ i ∈ Set.range e)
    {M : Matrix (Fin n) (Fin n) K} (hM : ∀ i j, (i ∈ J ↔ j ∉ J) → M i j = 0)
    (h1 : M.submatrix e e = 1) :
    ∀ i j, (i ∉ Jᶜ ∨ j ∉ Jᶜ) → M i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  intro i j hij
  simp only [Finset.mem_compl, not_not] at hij
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
  · obtain ⟨k, rfl⟩ := (hJ i).1 hi
    obtain ⟨l, rfl⟩ := (hJ j).1 hj
    have := congrFun (congrFun h1 k) l
    rw [submatrix_apply] at this
    rw [this]
    by_cases hkl : k = l
    · subst hkl
      simp
    · rw [one_apply_ne hkl, one_apply_ne (he.ne hkl)]
  · rw [hM i j (by tauto), one_apply_ne (fun h : i = j => hj (h ▸ hi))]
  · rw [hM i j (by tauto), one_apply_ne (fun h : i = j => hi (h ▸ hj))]
  · tauto

end Matrix

section Twist

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem mul_eq_mul_of_unitaryProj_commute {I : Finset (Fin n)} (hI : n < 2 * Iᶜ.card)
    {x A : unitarySU p f K n} (hx : x ∈ unitaryBlock h I)
    (hAx : unitaryProj h n A * unitaryProj h n x = unitaryProj h n x * unitaryProj h n A) :
    A * x = x * A := by
  rw [← map_mul, ← map_mul] at hAx
  obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq (s := unitaryScalars h n)).mp hAx
  have h1 : ((x * A : unitarySU p f K n) : GL (Fin n) K) =
      ((A * x : unitarySU p f K n) : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c := by
    rw [← hc, ← Subgroup.coe_mul, mul_inv_cancel_left]
  have hmat : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (c : K) • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h1
    simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at h2
    rw [h2, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hdet : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    rw [((mem_unitarySU_iff h).1 A.2).1]
    exact one_ne_zero
  have hc1 := eq_one_of_mul_eq_smul_mul hI ((mem_unitaryBlock h).1 hx) hdet hmat
  rw [hc1, one_smul] at hmat
  exact Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
    exact hmat.symm))

theorem blockSU_compl_le_centralizer_of_le_rootSU2 {a b : Fin n} {X : Subgroup (unitaryPSU h n)}
    (hX : X ≤ rootSU2 h a b) :
    blockSU h ({a, b}ᶜ : Finset (Fin n)) ≤ centralizer (X : Set (unitaryPSU h n)) := by
  intro d hd
  rw [mem_centralizer_iff]
  intro x hx
  exact (commute_blockSU_of_disjoint h disjoint_compl_left d hd x (hX hx)).symm

end Twist

section Even

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

omit [Field K] in
theorem lt_two_mul_card_compl_pair (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    n < 2 * ({a, b}ᶜ : Finset (Fin n)).card := by
  rw [card_compl_pair hab]
  omega

theorem commutator_mem_unitaryBlock_compl {a b : Fin n} (hab : a ≠ b) {y : unitarySU 2 f K n}
    (hy : y ∈ unitaryBlock h {a, b}) (hyy : y * y ≠ 1) {A B : unitarySU 2 f K n}
    (hA : A * y = y * A) (hB : B * y = y * B) :
    A * B * A⁻¹ * B⁻¹ ∈ unitaryBlock h ({a, b}ᶜ : Finset (Fin n)) := by
  have := h.charP
  rw [mem_unitaryBlock_iff_toSL, map_mul, map_mul, map_mul, map_inv, map_inv]
  refine LinearPilot.commutator_agrees_one_of_mem_centralizer hab (x := toSL h n y)
    ((mem_unitaryBlock_iff_toSL h).1 hy)
    (fun h' => hyy (toSL_injective h (by rw [map_mul, h', map_one]))) ?_ ?_
  · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hA]
  · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hB]

theorem exists_lift_of_le_rootSU2 {a b : Fin n} {X : Subgroup (unitaryPSU h n)}
    (hX : X ≤ rootSU2 h a b) (hXo : Odd (Nat.card X)) (hX1 : X ≠ ⊥) :
    ∃ x ∈ X, ∃ y : unitarySU 2 f K n, y ∈ unitaryBlock h {a, b} ∧ unitaryProj h n y = x ∧
      x ≠ 1 ∧ Odd (orderOf x) ∧ ∀ k : ℕ, y ^ 2 ^ k ≠ 1 := by
  obtain ⟨⟨x, hxX⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hX1
  have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
  have hxo : Odd (orderOf x) := by
    have := orderOf_dvd_natCard (⟨x, hxX⟩ : X)
    rw [orderOf_mk] at this
    exact hXo.of_dvd_nat this
  obtain ⟨y, hy, rfl⟩ := (mem_blockSU h).1 (hX hxX)
  refine ⟨_, hxX, y, hy, rfl, hx1', hxo, fun k hk => hx1' ?_⟩
  have h1 : unitaryProj h n y ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  exact orderOf_eq_one_iff.1
    ((Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hxo)).eq_one_of_dvd
      (orderOf_dvd_of_pow_eq_one h1))

theorem mul_self_ne_one_of_forall_pow_ne_one {G : Type*} [Group G] {y : G}
    (hy : ∀ k : ℕ, y ^ 2 ^ k ≠ 1) : y * y ≠ 1 := by
  have := hy 1
  rwa [pow_one, pow_two] at this

theorem commutator_mem_blockSU_of_mem_centralizer (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {X : Subgroup (unitaryPSU h n)} (hX : X ≤ rootSU2 h a b) (hXo : Odd (Nat.card X))
    (hX1 : X ≠ ⊥) {g g' : unitaryPSU h n} (hg : g ∈ centralizer (X : Set (unitaryPSU h n)))
    (hg' : g' ∈ centralizer (X : Set (unitaryPSU h n))) :
    g * g' * g⁻¹ * g'⁻¹ ∈ blockSU h ({a, b}ᶜ : Finset (Fin n)) := by
  obtain ⟨x, hxX, y, hy, rfl, -, -, hyk⟩ := exists_lift_of_le_rootSU2 h hX hXo hX1
  have hlift : ∀ g ∈ centralizer (X : Set (unitaryPSU h n)),
      ∃ A : unitarySU 2 f K n, unitaryProj h n A = g ∧ A * y = y * A := by
    intro g hg
    obtain ⟨A, rfl⟩ := unitaryProj_surjective h n g
    exact ⟨A, rfl, mul_eq_mul_of_unitaryProj_commute h (lt_two_mul_card_compl_pair hn hab) hy
      (mem_centralizer_iff.1 hg _ hxX).symm⟩
  obtain ⟨A, rfl, hA⟩ := hlift g hg
  obtain ⟨B, rfl, hB⟩ := hlift g' hg'
  have := unitaryProj_mem_blockSU h (commutator_mem_unitaryBlock_compl h hab hy
    (mul_self_ne_one_of_forall_pow_ne_one hyk) hA hB)
  simpa only [map_mul, map_inv] using this

theorem odd_card_ker_unitaryProj (hn : 1 ≤ n) : Odd (Nat.card (unitaryProj h n).ker) := by
  rw [ker_unitaryProj, card_unitaryScalars h hn]
  exact (odd_two_pow_add_one_of_unitaryFieldData h).of_dvd_nat (Nat.gcd_dvd_right _ _)

theorem mem_blockSU_of_isPGroup_of_le_rootSU2_of_five_le (hn : 5 ≤ n) {a b : Fin n}
    (hab : a ≠ b) {X : Subgroup (unitaryPSU h n)} (hX : X ≤ rootSU2 h a b)
    (hXo : Odd (Nat.card X)) (hX1 : X ≠ ⊥) {z : unitaryPSU h n} (hz : IsPGroup 2 (zpowers z))
    (hzX : z ∈ centralizer (X : Set (unitaryPSU h n))) :
    z ∈ blockSU h ({a, b}ᶜ : Finset (Fin n)) := by
  have := h.charP
  have := h.finite
  obtain ⟨x, hxX, y, hy, rfl, -, -, hyk⟩ := exists_lift_of_le_rootSU2 h hX hXo hX1
  obtain ⟨k, hk⟩ := hz ⟨z, mem_zpowers z⟩
  have hzk : z ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨Z, rfl, hZk⟩ := LinearPilot.exists_lift_pow_two_pow_eq_one (unitaryProj h n)
    (unitaryProj_surjective h n) (odd_card_ker_unitaryProj h (by omega)) hzk
  have hZy : Z * y = y * Z := mul_eq_mul_of_unitaryProj_commute h
    (lt_two_mul_card_compl_pair hn hab) hy (mem_centralizer_iff.1 hzX _ hxX).symm
  set Zm : Matrix (Fin n) (Fin n) K := ((Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hZm
  set Y : Matrix (Fin n) (Fin n) K := ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hY
  have hYa : ∀ i j, (i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) →
      Y i j = (1 : Matrix (Fin n) (Fin n) K) i j := (mem_unitaryBlock h).1 hy
  have hdetY : Y.det = 1 := ((mem_unitarySU_iff h).1 y.2).1
  have hYY : Y * Y ≠ 1 := fun hYY => mul_self_ne_one_of_forall_pow_ne_one hyk
    (Subtype.ext (Units.ext (by rw [Subgroup.coe_mul, Units.val_mul]; exact hYY)))
  have hZYm : Zm * Y = Y * Zm := by
    have := congrArg
      (fun g : unitarySU 2 f K n => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hZy
    simpa only [Subgroup.coe_mul, Units.val_mul] using this
  have hdiag := LinearPilot.blockDiag_of_mul_eq_mul hab hYa hdetY hYY hZYm
  have he := LinearPilot.pair_injective (n := n) hab
  have hJ := LinearPilot.mem_pair_iff_mem_range (a := a) (b := b)
  have hrowsZ : ∀ i ∈ ({a, b} : Finset (Fin n)), ∀ k ∉ ({a, b} : Finset (Fin n)),
      Zm i k = 0 := fun i hi k hk => hdiag i k (by tauto)
  have hrowsY : ∀ i ∈ ({a, b} : Finset (Fin n)), ∀ k ∉ ({a, b} : Finset (Fin n)),
      Y i k = 0 := fun i hi k hk => LinearPilot.row_eq_zero_of_agrees_one hYa hi k hk
  have hblock : Zm.submatrix ![a, b] ![a, b] * Y.submatrix ![a, b] ![a, b] =
      Y.submatrix ![a, b] ![a, b] * Zm.submatrix ![a, b] ![a, b] := by
    rw [← LinearPilot.submatrix_mul_of_rows he hJ hrowsZ,
      ← LinearPilot.submatrix_mul_of_rows he hJ hrowsY, hZYm]
  have hY0 := LinearPilot.not_scalar_submatrix_pair hab hYa hdetY hYY
  have hdet0 : (Y.submatrix ![a, b] ![a, b]).det = 1 := by
    rw [LinearPilot.det_submatrix_of_agrees_one he hJ hYa, hdetY]
  have hZ0k : (Zm.submatrix ![a, b] ![a, b]) ^ 2 ^ k = 1 := by
    have hZkm : Zm ^ 2 ^ k = 1 := by
      have := congrArg
        (fun g : unitarySU 2 f K n => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hZk
      simpa only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one] using this
    rw [← submatrix_pow_of_rows he hJ hrowsZ, hZkm, submatrix_one _ he]
  rcases LinearPilot.eq_one_or_pow_eq_one_of_mul_eq_mul hY0 hdet0 hblock hZ0k with h0 | h0
  · exact unitaryProj_mem_blockSU h ((mem_unitaryBlock h).2
      (agrees_one_compl_of_submatrix_eq_one he hJ hdiag h0))
  · exfalso
    apply hyk k
    have hYk : Y ^ 2 ^ k = 1 := LinearPilot.eq_one_of_agrees_one_of_submatrix_eq_one he hJ
      (LinearPilot.agrees_one_pow hYa _)
      (by rw [LinearPilot.submatrix_pow_of_agrees_one he hJ hYa, h0])
    exact Subtype.ext (Units.ext (by
      rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
      exact hYk))

end Even

end CFSG.SeitzReduction.UnitaryPilot
