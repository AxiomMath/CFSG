module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25U
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13

namespace Lem25

section D8

variable {X : Type*} [Group X]

@[expose] def dihSubgroup (a c : X) (ha : a * a = 1) (hac : a * c * a = c⁻¹) : Subgroup X where
  carrier := {x | ∃ k : ℤ, x = c ^ k ∨ x = a * c ^ k}
  mul_mem' := by
    have hca : ∀ k : ℤ, c ^ k * a = a * c ^ (-k) := by
      intro k
      have h1 : a * c ^ k * a = (c ^ k)⁻¹ := by
        have : a * c ^ k * a = (a * c * a) ^ k := by
          rw [show a * c * a = a * c * a⁻¹ by rw [inv_eq_of_mul_eq_one_right ha]]
          rw [conj_zpow]
          rw [inv_eq_of_mul_eq_one_right ha]
        rw [this, hac, inv_zpow]
      calc c ^ k * a = a * (a * c ^ k * a) := by
            rw [← mul_assoc, ← mul_assoc, ha, one_mul]
        _ = a * c ^ (-k) := by rw [h1, zpow_neg]
    rintro x y ⟨k, rfl | rfl⟩ ⟨l, rfl | rfl⟩
    · exact ⟨k + l, Or.inl (zpow_add c k l).symm⟩
    · refine ⟨-k + l, Or.inr ?_⟩
      rw [← mul_assoc, hca, mul_assoc, ← zpow_add]
    · exact ⟨k + l, Or.inr (by rw [mul_assoc, ← zpow_add])⟩
    · refine ⟨-k + l, Or.inl ?_⟩
      rw [mul_assoc, ← mul_assoc (c ^ k), hca, ← mul_assoc, ← mul_assoc, ha, one_mul,
        ← zpow_add]
  one_mem' := ⟨0, Or.inl (zpow_zero c).symm⟩
  inv_mem' := by
    have hca : ∀ k : ℤ, c ^ k * a = a * c ^ (-k) := by
      intro k
      have h1 : a * c ^ k * a = (c ^ k)⁻¹ := by
        have : a * c ^ k * a = (a * c * a) ^ k := by
          rw [show a * c * a = a * c * a⁻¹ by rw [inv_eq_of_mul_eq_one_right ha]]
          rw [conj_zpow]
          rw [inv_eq_of_mul_eq_one_right ha]
        rw [this, hac, inv_zpow]
      calc c ^ k * a = a * (a * c ^ k * a) := by
            rw [← mul_assoc, ← mul_assoc, ha, one_mul]
        _ = a * c ^ (-k) := by rw [h1, zpow_neg]
    rintro x ⟨k, rfl | rfl⟩
    · exact ⟨-k, Or.inl (zpow_neg c k).symm⟩
    · refine ⟨k, Or.inr ?_⟩
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, ← zpow_neg, hca, neg_neg]

theorem isPGroup_closure_of_D8 [Finite X] {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (h4 : (a * b) ^ 4 = 1) (h2 : (a * b) ^ 2 ≠ 1) :
    IsPGroup 2 (Subgroup.closure {a, b}) ∧ 8 ≤ Nat.card (Subgroup.closure {a, b}) := by
  set c := a * b with hc
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hac : a * c * a = c⁻¹ := by
    rw [hc, mul_inv_rev, ha', hb', ← mul_assoc, ha, one_mul]
  have hbac : b = a * c := by rw [hc, ← mul_assoc, ha, one_mul]
  set D := dihSubgroup a c ha hac with hD
  have hle : Subgroup.closure {a, b} ≤ D := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨0, Or.inr (by rw [zpow_zero, mul_one])⟩
    · exact ⟨1, Or.inr (by rw [zpow_one, hbac])⟩
  have haD : a ∈ Subgroup.closure ({a, b} : Set X) :=
    Subgroup.subset_closure (Set.mem_insert a {b})
  have hbD : b ∈ Subgroup.closure ({a, b} : Set X) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton b))
  have habD : c ∈ Subgroup.closure ({a, b} : Set X) := Subgroup.mul_mem _ haD hbD
  have hcD : ∀ k : ℤ, c ^ k ∈ Subgroup.closure ({a, b} : Set X) := fun k =>
    Subgroup.zpow_mem _ habD k
  have hc4 : c ^ 4 = 1 := h4
  have hcz : ∀ k : ℤ, (c ^ k) ^ 4 = 1 := fun k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc4, one_zpow]
  have hD4 : ∀ x ∈ D, x ^ 4 = 1 := by
    rintro x ⟨k, rfl | rfl⟩
    · exact hcz k
    · have hsq : (a * c ^ k) * (a * c ^ k) = 1 := by
        have h1 : a * c ^ k * a = c ^ (-k) := by
          have : a * c ^ k * a = (a * c * a) ^ k := by
            rw [show a * c * a = a * c * a⁻¹ by rw [ha'], conj_zpow, ha']
          rw [this, hac, inv_zpow', zpow_neg]
        calc (a * c ^ k) * (a * c ^ k) = (a * c ^ k * a) * c ^ k := by group
          _ = 1 := by rw [h1, ← zpow_add, neg_add_cancel, zpow_zero]
      have hsq' : (a * c ^ k) ^ 2 = 1 := by rw [pow_two, hsq]
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq', one_pow]
  refine ⟨fun x => ⟨2, Subtype.ext (hD4 x (hle x.2))⟩, ?_⟩
  have hco : orderOf c = 4 := by
    have hd : orderOf c ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by rw [← hc4]; norm_num)
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    interval_cases k
    · rw [pow_zero, orderOf_eq_one_iff] at hk'
      exact absurd (by rw [hk', one_pow]) h2
    · rw [pow_one] at hk'
      exact absurd (by rw [← hk']; exact pow_orderOf_eq_one c) h2
    · rw [hk']
      norm_num
  have haC : ∀ k : ℕ, a ≠ c ^ k := by
    intro k hk
    have hk' : a = c ^ (k % 4) := by rw [hk, ← hco, pow_mod_orderOf]
    have hlt : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    apply h2
    interval_cases hr : k % 4
    · rw [pow_zero] at hk'
      rw [hc, hk', one_mul, pow_two, hb]
    · rw [pow_one] at hk'
      have hb1 : b = 1 := by
        have h := hc
        rw [hk'] at h
        exact mul_eq_left.mp h.symm
      rw [← hk', pow_two, ha]
    · have hb3 : b = c ^ 3 := by rw [hbac, hk', ← pow_succ]
      have h6 : b * b = c ^ 2 := by
        rw [hb3, ← pow_add, show 3 + 3 = 4 + 2 by rfl, pow_add, hc4, one_mul]
      rw [← h6, hb]
    · have h6 : a * a = c ^ 2 := by
        rw [hk', ← pow_add, show 3 + 3 = 4 + 2 by rfl, pow_add, hc4, one_mul]
      rw [← h6, ha]
  have hinv : ∀ n : ℕ, n < 4 → (c ^ n)⁻¹ = c ^ (4 - n) := by
    intro n hn
    rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_cancel' hn.le, hc4]
  have hpow : ∀ m n : ℕ, m < 4 → n < 4 → c ^ m = c ^ n → m = n := by
    intro m n hm hn h
    have := pow_inj_mod.mp h
    rw [hco] at this
    rwa [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at this
  let f : Fin 8 → Subgroup.closure ({a, b} : Set X) := fun i =>
    if i.val < 4 then ⟨c ^ (i.val : ℤ), hcD _⟩
    else ⟨a * c ^ ((i.val - 4 : ℕ) : ℤ), Subgroup.mul_mem _ haD (hcD _)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hv : (f i : X) = f j := congrArg Subtype.val hij
    apply Fin.ext
    have hi8 := i.isLt
    have hj8 := j.isLt
    simp only [f] at hv
    split_ifs at hv with hi hj hj <;> simp only [zpow_natCast] at hv
    · exact hpow _ _ hi hj hv
    · exfalso
      apply haC (i.val + (4 - (j.val - 4)))
      rw [pow_add, ← hinv _ (by omega), hv, mul_inv_cancel_right]
    · exfalso
      apply haC (j.val + (4 - (i.val - 4)))
      rw [pow_add, ← hinv _ (by omega), ← hv, mul_inv_cancel_right]
    · have := hpow _ _ (by omega) (by omega) (mul_left_cancel hv)
      omega
  have := Nat.card_le_card_of_injective f hf
  simpa using this

end D8

section Coord

variable {G : Type} [Group G]

@[expose] def bpow (e : G) (b : Bool) : G := if b then e else 1

theorem bpow_false (x : G) : bpow x false = 1 := rfl

theorem bpow_true (x : G) : bpow x true = x := rfl

@[expose] def ofCoord (e : Fin 5 → G) (c : Fin 5 → Bool) : G :=
  bpow (e 0) (c 0) * bpow (e 1) (c 1) * bpow (e 2) (c 2) * bpow (e 3) (c 3) * bpow (e 4) (c 4)

@[expose] def bmulVec (M : B5) (c : Fin 5 → Bool) : Fin 5 → Bool := fun i =>
  (M i 0 && c 0) ^^ (M i 1 && c 1) ^^ (M i 2 && c 2) ^^ (M i 3 && c 3) ^^ (M i 4 && c 4)

structure IsBasis5 (R : Subgroup G) (e : Fin 5 → G) : Prop where
  mem : ∀ i, e i ∈ R
  comm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x
  sq : ∀ x ∈ R, x * x = 1
  indep : ∀ c, ofCoord e c = 1 → c = fun _ => false
  card : Nat.card R = 32

namespace IsBasis5

variable {R : Subgroup G} {e : Fin 5 → G}

theorem bpow_mem (hB : IsBasis5 R e) (i : Fin 5) (b : Bool) : bpow (e i) b ∈ R := by
  unfold bpow; split_ifs
  · exact hB.mem i
  · exact R.one_mem

theorem ofCoord_mem (hB : IsBasis5 R e) (c : Fin 5 → Bool) : ofCoord e c ∈ R := by
  unfold ofCoord
  exact R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem (hB.bpow_mem 0 _) (hB.bpow_mem 1 _))
    (hB.bpow_mem 2 _)) (hB.bpow_mem 3 _)) (hB.bpow_mem 4 _)

theorem bpow_xor (hB : IsBasis5 R e) (i : Fin 5) (b b' : Bool) :
    bpow (e i) (b ^^ b') = bpow (e i) b * bpow (e i) b' := by
  cases b <;> cases b' <;> simp [bpow, hB.sq _ (hB.mem i)]

theorem ofCoord_xor (hB : IsBasis5 R e) (c d : Fin 5 → Bool) :
    ofCoord e (fun i => c i ^^ d i) = ofCoord e c * ofCoord e d := by
  let _ : CommGroup R := { (inferInstance : Group R) with
    mul_comm := fun x y => Subtype.ext (hB.comm x x.2 y y.2) }
  have key : ∀ c : Fin 5 → Bool, ofCoord e c = ((⟨bpow (e 0) (c 0), hB.bpow_mem 0 _⟩ : R) *
      ⟨bpow (e 1) (c 1), hB.bpow_mem 1 _⟩ * ⟨bpow (e 2) (c 2), hB.bpow_mem 2 _⟩ *
      ⟨bpow (e 3) (c 3), hB.bpow_mem 3 _⟩ * ⟨bpow (e 4) (c 4), hB.bpow_mem 4 _⟩ : R) := fun c => rfl
  have hx : ∀ i : Fin 5, (⟨bpow (e i) (c i ^^ d i), hB.bpow_mem i _⟩ : R) =
      ⟨bpow (e i) (c i), hB.bpow_mem i _⟩ * ⟨bpow (e i) (d i), hB.bpow_mem i _⟩ := fun i =>
    Subtype.ext (hB.bpow_xor i _ _)
  rw [key, key c, key d, ← Subgroup.coe_mul]
  congr 1
  rw [hx 0, hx 1, hx 2, hx 3, hx 4]
  ac_rfl

theorem ofCoord_injective (hB : IsBasis5 R e) : Function.Injective (ofCoord e) := by
  intro c d h
  have h1 : ofCoord e (fun i => c i ^^ d i) = 1 := by
    rw [hB.ofCoord_xor, h, hB.sq _ (hB.ofCoord_mem d)]
  have h2 := hB.indep _ h1
  funext i
  have := congrFun h2 i
  simpa using this

theorem ofCoord_surjective (hB : IsBasis5 R e) {r : G} (hr : r ∈ R) : ∃ c, ofCoord e c = r := by
  have : Finite R := Nat.finite_of_card_ne_zero (by rw [hB.card]; norm_num)
  let F : (Fin 5 → Bool) → R := fun c => ⟨ofCoord e c, hB.ofCoord_mem c⟩
  have hF : Function.Injective F := fun c d h => hB.ofCoord_injective (congrArg Subtype.val h)
  have hbij := hF.bijective_of_nat_card_le (by rw [hB.card]; simp)
  obtain ⟨c, hc⟩ := hbij.2 ⟨r, hr⟩
  exact ⟨c, congrArg Subtype.val hc⟩

end IsBasis5

noncomputable def coord (e : Fin 5 → G) (r : G) : Fin 5 → Bool := Function.invFun (ofCoord e) r

@[expose] noncomputable def matB (e : Fin 5 → G) (x : G) : B5 :=
  fun i j => coord e (x * e j * x⁻¹) i

theorem matB_apply (e : Fin 5 → G) (x : G) (i j : Fin 5) :
    matB e x i j = coord e (x * e j * x⁻¹) i :=
  rfl

theorem conj_bpow (x e' : G) (b : Bool) : x * bpow e' b * x⁻¹ = bpow (x * e' * x⁻¹) b := by
  cases b <;> simp [bpow]

namespace IsBasis5

variable {R : Subgroup G} {e : Fin 5 → G}

theorem ofCoord_coord (hB : IsBasis5 R e) {r : G} (hr : r ∈ R) : ofCoord e (coord e r) = r :=
  Function.invFun_eq (hB.ofCoord_surjective hr)

theorem coord_ofCoord (hB : IsBasis5 R e) (c : Fin 5 → Bool) : coord e (ofCoord e c) = c :=
  Function.leftInverse_invFun hB.ofCoord_injective c

theorem bpow_ofCoord (b : Bool) (d : Fin 5 → Bool) :
    bpow (ofCoord e d) b = ofCoord e (fun i => b && d i) := by
  cases b
  · simp [bpow, ofCoord]
  · simp [bpow]

theorem conj_ofCoord (hB : IsBasis5 R e) {x : G} (hx : x ∈ Subgroup.normalizer (R : Set G))
    (c : Fin 5 → Bool) : x * ofCoord e c * x⁻¹ = ofCoord e (bmulVec (matB e x) c) := by
  have hcol : ∀ j, x * e j * x⁻¹ = ofCoord e (fun i => matB e x i j) := fun j =>
    (hB.ofCoord_coord ((Subgroup.mem_normalizer_iff.mp hx _).mp (hB.mem j))).symm
  have e1 : x * ofCoord e c * x⁻¹ = bpow (x * e 0 * x⁻¹) (c 0) * bpow (x * e 1 * x⁻¹) (c 1) *
      bpow (x * e 2 * x⁻¹) (c 2) * bpow (x * e 3 * x⁻¹) (c 3) * bpow (x * e 4 * x⁻¹) (c 4) := by
    simp only [ofCoord, ← conj_bpow]
    group
  rw [e1, hcol 0, hcol 1, hcol 2, hcol 3, hcol 4, bpow_ofCoord, bpow_ofCoord, bpow_ofCoord,
    bpow_ofCoord, bpow_ofCoord, ← hB.ofCoord_xor, ← hB.ofCoord_xor, ← hB.ofCoord_xor,
    ← hB.ofCoord_xor]
  congr 1
  funext i
  simp only [bmulVec, Bool.and_comm (c _)]

theorem matB_mul (hB : IsBasis5 R e) {x y : G} (hx : x ∈ Subgroup.normalizer (R : Set G))
    (hy : y ∈ Subgroup.normalizer (R : Set G)) : matB e (x * y) = bmul (matB e x) (matB e y) := by
  funext i j
  have h1 : x * y * e j * (x * y)⁻¹ = x * (y * e j * y⁻¹) * x⁻¹ := by group
  have h2 : y * e j * y⁻¹ = ofCoord e (fun k => matB e y k j) :=
    (hB.ofCoord_coord ((Subgroup.mem_normalizer_iff.mp hy _).mp (hB.mem j))).symm
  show coord e (x * y * e j * (x * y)⁻¹) i = _
  rw [h1, h2, hB.conj_ofCoord hx, hB.coord_ofCoord]
  rfl

theorem ofCoord_single (j : Fin 5) : ofCoord e (fun i => decide (i = j)) = e j := by
  fin_cases j <;> simp [ofCoord, bpow]

theorem matB_eq_bone_iff (hB : IsBasis5 R e) {x : G}
    (hx : x ∈ Subgroup.normalizer (R : Set G)) :
    matB e x = bone ↔ x ∈ Subgroup.centralizer (R : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := hB.conj_ofCoord hx (coord e r)
    rw [hB.ofCoord_coord hr, h] at h1
    have h2 : bmulVec bone (coord e r) = coord e r := by
      funext i
      fin_cases i <;> simp [bmulVec, bone]
    rw [h2, hB.ofCoord_coord hr] at h1
    calc r * x = x * r * x⁻¹ * x := by rw [h1]
      _ = x * r := by group
  · intro h
    funext i j
    have h1 : x * e j * x⁻¹ = e j := by
      rw [← Subgroup.mem_centralizer_iff.mp h (e j) (hB.mem j), mul_inv_cancel_right]
    show coord e (x * e j * x⁻¹) i = _
    rw [h1, ← ofCoord_single (e := e) j, hB.coord_ofCoord]
    rfl

theorem matB_eq_of_cols (hB : IsBasis5 R e) {x : G} {M : B5}
    (h : ∀ j, x * e j * x⁻¹ = ofCoord e (fun i => M i j)) : matB e x = M := by
  funext i j
  show coord e (x * e j * x⁻¹) i = M i j
  rw [h j, hB.coord_ofCoord]

end IsBasis5

end Coord

end Lem25

end CFSG.Quasithin.H13
