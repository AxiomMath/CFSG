module

public import CFSG.Quasithin.Background.A1cRank
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped Pointwise

namespace C41Pf

section Generic

theorem exists_elemAbelian_sq {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) {a b : X}
    (ha : orderOf a = p) (hb : orderOf b = p) (hab : Commute a b) (hbn : b ∉ Subgroup.zpowers a) :
    ∃ E : Subgroup X, IsElemAbelian p E ∧ Nat.card ↥E = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hE0 : IsElemAbelian p (Subgroup.zpowers a) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · apply Subtype.ext
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp y.2
      show (x : X) * y = y * x
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    · intro x hx
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ha,
        pow_orderOf_eq_one, one_zpow]
  have hcomm : ∀ e ∈ Subgroup.zpowers a, Commute e b := by
    intro e he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact hab.zpow_left i
  obtain ⟨hE, hEc⟩ := exists_elemAbelian_sup_zpowers hE0 hb hcomm hbn
  refine ⟨_, hE, ?_⟩
  rw [hEc, Nat.card_zpowers, ha]
  ring

theorem exists_elemAbelian_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p k : ℕ}
    (h : ∃ E : Subgroup Y, IsElemAbelian p E ∧ Nat.card ↥E = p ^ k) :
    ∃ E : Subgroup X, IsElemAbelian p E ∧ Nat.card ↥E = p ^ k := by
  obtain ⟨E, hE, hEc⟩ := h
  refine ⟨E.map e.symm.toMonoidHom, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨x', hx', hxx⟩ := x.2
    obtain ⟨y', hy', hyy⟩ := y.2
    apply Subtype.ext
    show (x : X) * y = y * x
    rw [← hxx, ← hyy, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  · rw [← hEc]
    exact Nat.card_congr (Subgroup.equivMapOfInjective E e.symm.toMonoidHom
      e.symm.injective).toEquiv.symm

end Generic

section Alt

theorem exists_elemAbelian_alt7 :
    ∃ E : Subgroup (alternatingGroup (Fin 7)), IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 2 := by
  have hc1 : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hc2 : (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 4 5) ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have h1 : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) ^ 3 = 1 := by decide
  have h2 : (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 4 5) ^ 3 = 1 := by decide
  have h1' : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) ≠ 1 := by decide
  have h2' : (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 4 5) ≠ 1 := by decide
  have h12 : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) * (Equiv.swap (3 : Fin 7) 4 *
      Equiv.swap 4 5) = (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 4 5) *
      (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) := by decide
  have hpow : ∀ k < 3, (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) ^ k ≠
      Equiv.swap (3 : Fin 7) 4 * Equiv.swap 4 5 := by decide
  set a : alternatingGroup (Fin 7) := ⟨_, hc1⟩ with ha_def
  set b : alternatingGroup (Fin 7) := ⟨_, hc2⟩ with hb_def
  have ha : orderOf a = 3 :=
    orderOf_eq_prime (Subtype.ext h1) (fun h => h1' (congrArg Subtype.val h))
  have hb : orderOf b = 3 :=
    orderOf_eq_prime (Subtype.ext h2) (fun h => h2' (congrArg Subtype.val h))
  have hab : Commute a b := Subtype.ext h12
  have hbn : b ∉ Subgroup.zpowers a := by
    rw [mem_zpowers_iff_mem_range_orderOf, ha]
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro k hk hkb
    exact hpow k hk (congrArg Subtype.val hkb)
  exact exists_elemAbelian_sq Nat.prime_three ha hb hab hbn

theorem exists_elemAbelian_alt8 :
    ∃ E : Subgroup (alternatingGroup (Fin 8)), IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 2 := by
  have hc1 : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hc2 : (Equiv.swap (3 : Fin 8) 4 * Equiv.swap 4 5) ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have h1 : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) ^ 3 = 1 := by decide
  have h2 : (Equiv.swap (3 : Fin 8) 4 * Equiv.swap 4 5) ^ 3 = 1 := by decide
  have h1' : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) ≠ 1 := by decide
  have h2' : (Equiv.swap (3 : Fin 8) 4 * Equiv.swap 4 5) ≠ 1 := by decide
  have h12 : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) * (Equiv.swap (3 : Fin 8) 4 *
      Equiv.swap 4 5) = (Equiv.swap (3 : Fin 8) 4 * Equiv.swap 4 5) *
      (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) := by decide
  have hpow : ∀ k < 3, (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) ^ k ≠
      Equiv.swap (3 : Fin 8) 4 * Equiv.swap 4 5 := by decide
  set a : alternatingGroup (Fin 8) := ⟨_, hc1⟩ with ha_def
  set b : alternatingGroup (Fin 8) := ⟨_, hc2⟩ with hb_def
  have ha : orderOf a = 3 :=
    orderOf_eq_prime (Subtype.ext h1) (fun h => h1' (congrArg Subtype.val h))
  have hb : orderOf b = 3 :=
    orderOf_eq_prime (Subtype.ext h2) (fun h => h2' (congrArg Subtype.val h))
  have hab : Commute a b := Subtype.ext h12
  have hbn : b ∉ Subgroup.zpowers a := by
    rw [mem_zpowers_iff_mem_range_orderOf, ha]
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro k hk hkb
    exact hpow k hk (congrArg Subtype.val hkb)
  exact exists_elemAbelian_sq Nat.prime_three ha hb hab hbn

end Alt

section Diag

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] noncomputable def diagUnits : (ι → Fˣ) →* GL ι F where
  toFun v := ⟨Matrix.diagonal (fun i => (v i : F)), Matrix.diagonal (fun i => ((v i)⁻¹ : Fˣ)),
    by rw [Matrix.diagonal_mul_diagonal]; simp, by rw [Matrix.diagonal_mul_diagonal]; simp⟩
  map_one' := by
    ext : 1
    simp
  map_mul' v w := by
    ext : 1
    simp [Matrix.diagonal_mul_diagonal]

theorem coe_diagUnits (v : ι → Fˣ) :
    ((diagUnits v : GL ι F) : Matrix ι ι F) = Matrix.diagonal (fun i => (v i : F)) := rfl

theorem diagUnits_injective : Function.Injective (diagUnits : (ι → Fˣ) →* GL ι F) := by
  intro v w h
  funext i
  have h1 := congrArg (fun A : GL ι F => (A : Matrix ι ι F) i i) h
  simp only [coe_diagUnits, Matrix.diagonal_apply_eq] at h1
  exact Units.ext h1

end Diag

section SL3

theorem exists_elemAbelian_sl3 {F : Type} [Field F] [Fintype F] {r : ℕ} (hr : r.Prime)
    (hrF : r ∣ Fintype.card F - 1) :
    ∃ E : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F), IsElemAbelian r E ∧
      Nat.card ↥E = r ^ 2 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, orderOf u = r := by
    apply exists_prime_orderOf_dvd_card
    rw [Fintype.card_units]
    exact hrF
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    exact hr.one_lt.ne hu
  have hur : u ^ r = 1 := hu ▸ pow_orderOf_eq_one u
  set v₁ : Fin 3 → Fˣ := ![u, u⁻¹, 1] with hv₁
  set v₂ : Fin 3 → Fˣ := ![1, u, u⁻¹] with hv₂
  have hmem : ∀ v : Fin 3 → Fˣ, ∏ i, v i = 1 →
      (diagUnits v : GL (Fin 3) F) ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 F := by
    intro v hv
    apply Subgroup.subset_closure
    show (Matrix.diagonal (fun i => (v i : F))).det = 1
    rw [Matrix.det_diagonal]
    have := congrArg Units.val hv
    simpa [Units.coe_prod] using this
  have h1 : ∏ i, v₁ i = 1 := by simp [hv₁, Fin.prod_univ_three]
  have h2 : ∏ i, v₂ i = 1 := by simp [hv₂, Fin.prod_univ_three]
  set a : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) := ⟨_, hmem v₁ h1⟩ with ha_def
  set b : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) := ⟨_, hmem v₂ h2⟩ with hb_def
  have hv₁r : v₁ ^ r = 1 := by
    funext i
    fin_cases i <;> simp [hv₁, hur, inv_pow]
  have hv₂r : v₂ ^ r = 1 := by
    funext i
    fin_cases i <;> simp [hv₂, hur, inv_pow]
  have hv₁1 : v₁ ≠ 1 := fun h => hu1 (by simpa [hv₁] using congrFun h 0)
  have hv₂1 : v₂ ≠ 1 := fun h => hu1 (by simpa [hv₂] using congrFun h 1)
  have ha : orderOf a = r := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      show (diagUnits v₁ : GL (Fin 3) F) ^ r = 1
      rw [← map_pow, hv₁r, map_one]
    · intro h
      apply hv₁1
      apply diagUnits_injective (F := F)
      rw [map_one]
      exact congrArg Subtype.val h
  have hb : orderOf b = r := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      show (diagUnits v₂ : GL (Fin 3) F) ^ r = 1
      rw [← map_pow, hv₂r, map_one]
    · intro h
      apply hv₂1
      apply diagUnits_injective (F := F)
      rw [map_one]
      exact congrArg Subtype.val h
  have hab : Commute a b := by
    apply Subtype.ext
    show diagUnits v₁ * diagUnits v₂ = diagUnits v₂ * (diagUnits v₁ : GL (Fin 3) F)
    rw [← map_mul, ← map_mul, mul_comm]
  have hbn : b ∉ Subgroup.zpowers a := by
    intro hmem'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem'
    have hk' : (diagUnits (v₁ ^ k) : GL (Fin 3) F) = diagUnits v₂ := by
      rw [map_zpow]
      exact congrArg Subtype.val hk
    have := congrFun (diagUnits_injective hk') 2
    simp [hv₁, hv₂] at this
    exact hu1 this
  exact exists_elemAbelian_sq hr ha hb hab hbn

end SL3

section Sp4

theorem exists_elemAbelian_sp4 {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) :
    ∃ E : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F), IsElemAbelian 3 E ∧
      Nat.card ↥E = 3 ^ 2 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, orderOf u = 3 := by
    apply exists_prime_orderOf_dvd_card
    rw [Fintype.card_units, hF]
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hu3 : u ^ 3 = 1 := hu ▸ pow_orderOf_eq_one u
  let sd : (Fin 2 → Fˣ) → (Fin 2 ⊕ Fin 2 → Fˣ) := fun w => Sum.elim w (fun i => (w i)⁻¹)
  have hsd : ∀ w w' : Fin 2 → Fˣ, sd (w * w') = sd w * sd w' := by
    intro w w'
    funext i
    rcases i with i | i <;> simp [sd, mul_comm]
  have hmem : ∀ w : Fin 2 → Fˣ,
      (diagUnits (sd w) : GL (Fin 2 ⊕ Fin 2) F) ∈ CFSG.Assembly.LowTwoRank.StatedSp 2 F := by
    intro w
    apply Subgroup.subset_closure
    show Matrix.transpose (Matrix.diagonal fun i => ((sd w i : Fˣ) : F)) *
        Matrix.fromBlocks 0 1 (-1) 0 * Matrix.diagonal (fun i => ((sd w i : Fˣ) : F)) =
      Matrix.fromBlocks 0 1 (-1) 0
    rw [Matrix.diagonal_transpose]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [sd, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.one_apply] <;> split_ifs <;> simp_all
  set w₁ : Fin 2 → Fˣ := ![u, 1] with hw₁
  set w₂ : Fin 2 → Fˣ := ![1, u] with hw₂
  set a : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := ⟨_, hmem w₁⟩ with ha_def
  set b : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := ⟨_, hmem w₂⟩ with hb_def
  have hpow : ∀ (w : Fin 2 → Fˣ) (k : ℕ), sd w ^ k = sd (w ^ k) := by
    intro w k
    induction k with
    | zero =>
      funext i
      rcases i with i | i <;> simp [sd]
    | succ k ih => rw [pow_succ, ih, pow_succ, hsd]
  have hzpow : ∀ (w : Fin 2 → Fˣ) (k : ℤ), sd w ^ k = sd (w ^ k) := by
    intro w k
    funext i
    rcases i with i | i <;> simp [sd]
  have hw₁3 : w₁ ^ 3 = 1 := by funext i; fin_cases i <;> simp [hw₁, hu3]
  have hw₂3 : w₂ ^ 3 = 1 := by funext i; fin_cases i <;> simp [hw₂, hu3]
  have hsd1 : ∀ w : Fin 2 → Fˣ, sd w = 1 → w = 1 := fun w h => by
    funext i
    have := congrFun h (Sum.inl i)
    simpa [sd] using this
  have hsd1' : sd 1 = 1 := by funext i; rcases i with i | i <;> simp [sd]
  have ha : orderOf a = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      show (diagUnits (sd w₁) : GL (Fin 2 ⊕ Fin 2) F) ^ 3 = 1
      rw [← map_pow, hpow, hw₁3, hsd1', map_one]
    · intro h
      have h1 : sd w₁ = 1 :=
        diagUnits_injective (F := F) (by rw [map_one]; exact congrArg Subtype.val h)
      have := congrFun (hsd1 _ h1) 0
      exact hu1 (by simpa [hw₁] using this)
  have hb : orderOf b = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      show (diagUnits (sd w₂) : GL (Fin 2 ⊕ Fin 2) F) ^ 3 = 1
      rw [← map_pow, hpow, hw₂3, hsd1', map_one]
    · intro h
      have h1 : sd w₂ = 1 :=
        diagUnits_injective (F := F) (by rw [map_one]; exact congrArg Subtype.val h)
      have := congrFun (hsd1 _ h1) 1
      exact hu1 (by simpa [hw₂] using this)
  have hab : Commute a b := by
    apply Subtype.ext
    show diagUnits (sd w₁) * diagUnits (sd w₂) =
      diagUnits (sd w₂) * (diagUnits (sd w₁) : GL (Fin 2 ⊕ Fin 2) F)
    rw [← map_mul, ← map_mul, mul_comm]
  have hbn : b ∉ Subgroup.zpowers a := by
    intro hmem'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem'
    have hk' : (diagUnits (sd w₁ ^ k) : GL (Fin 2 ⊕ Fin 2) F) = diagUnits (sd w₂) := by
      rw [map_zpow]
      exact congrArg Subtype.val hk
    have h1 := diagUnits_injective hk'
    rw [hzpow] at h1
    have h0 := congrFun h1 (Sum.inl 0)
    have h1' := congrFun h1 (Sum.inl 1)
    simp [sd, hw₁, hw₂] at h0 h1'
    exact hu1 h1'.symm
  exact exists_elemAbelian_sq Nat.prime_three ha hb hab hbn

end Sp4

section SLTwo

theorem statedSL_eq_top_of_card_two {n : ℕ} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) : CFSG.Assembly.LowTwoRank.StatedSL n F = ⊤ :=
  CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two (by rw [Nat.card_eq_fintype_card, hF]) n

theorem exists_elemAbelian_sl4_two :
    ∃ E : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)), IsElemAbelian 3 E ∧
      Nat.card ↥E = 3 ^ 2 := by
  have htop := statedSL_eq_top_of_card_two (n := 4) (F := ZMod 2) (by simp)
  set A : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] with hA
  set B : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1] with hB
  have hA3 : A * (A * A) = 1 := by rw [hA]; decide
  have hA3' : (A * A) * A = 1 := by rw [hA]; decide
  have hB3 : B * (B * B) = 1 := by rw [hB]; decide
  have hB3' : (B * B) * B = 1 := by rw [hB]; decide
  have hA1 : A ≠ 1 := by rw [hA]; decide
  have hB1 : B ≠ 1 := by rw [hB]; decide
  have hAB : A * B = B * A := by rw [hA, hB]; decide
  have hpow : ∀ k < 3, A ^ k ≠ B := by rw [hA, hB]; decide
  set uA : GL (Fin 4) (ZMod 2) := ⟨A, A * A, hA3, hA3'⟩ with huA
  set uB : GL (Fin 4) (ZMod 2) := ⟨B, B * B, hB3, hB3'⟩ with huB
  set a : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) := ⟨uA, by rw [htop]; trivial⟩
  set b : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) := ⟨uB, by rw [htop]; trivial⟩
  have ha : orderOf a = 3 := by
    refine orderOf_eq_prime (Subtype.ext (Units.ext ?_)) ?_
    · show A ^ 3 = 1
      rw [pow_succ, pow_two, hA3']
    · intro h
      exact hA1 (congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) =>
        ((x : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) h)
  have hb : orderOf b = 3 := by
    refine orderOf_eq_prime (Subtype.ext (Units.ext ?_)) ?_
    · show B ^ 3 = 1
      rw [pow_succ, pow_two, hB3']
    · intro h
      exact hB1 (congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) =>
        ((x : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) h)
  have hab : Commute a b := Subtype.ext (Units.ext hAB)
  have hbn : b ∉ Subgroup.zpowers a := by
    rw [mem_zpowers_iff_mem_range_orderOf, ha]
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro k hk hkb
    apply hpow k hk
    have := congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) =>
      ((x : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) hkb
    simpa [Units.val_pow_eq_pow_val] using this
  exact exists_elemAbelian_sq Nat.prime_three ha hb hab hbn

theorem exists_elemAbelian_sl5_two :
    ∃ E : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)), IsElemAbelian 3 E ∧
      Nat.card ↥E = 3 ^ 2 := by
  have htop := statedSL_eq_top_of_card_two (n := 5) (F := ZMod 2) (by simp)
  set A : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
    !![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] with hA
  set B : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1] with hB
  have hA3 : A * (A * A) = 1 := by rw [hA]; decide
  have hA3' : (A * A) * A = 1 := by rw [hA]; decide
  have hB3 : B * (B * B) = 1 := by rw [hB]; decide
  have hB3' : (B * B) * B = 1 := by rw [hB]; decide
  have hA1 : A ≠ 1 := by rw [hA]; decide
  have hB1 : B ≠ 1 := by rw [hB]; decide
  have hAB : A * B = B * A := by rw [hA, hB]; decide
  have hpow : ∀ k < 3, A ^ k ≠ B := by rw [hA, hB]; decide
  set uA : GL (Fin 5) (ZMod 2) := ⟨A, A * A, hA3, hA3'⟩ with huA
  set uB : GL (Fin 5) (ZMod 2) := ⟨B, B * B, hB3, hB3'⟩ with huB
  set a : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) := ⟨uA, by rw [htop]; trivial⟩
  set b : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) := ⟨uB, by rw [htop]; trivial⟩
  have ha : orderOf a = 3 := by
    refine orderOf_eq_prime (Subtype.ext (Units.ext ?_)) ?_
    · show A ^ 3 = 1
      rw [pow_succ, pow_two, hA3']
    · intro h
      exact hA1 (congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) =>
        ((x : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) h)
  have hb : orderOf b = 3 := by
    refine orderOf_eq_prime (Subtype.ext (Units.ext ?_)) ?_
    · show B ^ 3 = 1
      rw [pow_succ, pow_two, hB3']
    · intro h
      exact hB1 (congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) =>
        ((x : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) h)
  have hab : Commute a b := Subtype.ext (Units.ext hAB)
  have hbn : b ∉ Subgroup.zpowers a := by
    rw [mem_zpowers_iff_mem_range_orderOf, ha]
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro k hk hkb
    apply hpow k hk
    have := congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) =>
      ((x : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) hkb
    simpa [Units.val_pow_eq_pow_val] using this
  exact exists_elemAbelian_sq Nat.prime_three ha hb hab hbn

end SLTwo

end C41Pf

end CFSG.Quasithin
