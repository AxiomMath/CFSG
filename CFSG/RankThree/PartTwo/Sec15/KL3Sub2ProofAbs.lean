module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.Group
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace KL3Sub2Proof

variable {X : Type*} [Group X]

@[expose] def conjOn (M : Subgroup X) {u : X} (hu : u ∈ Subgroup.normalizer (M : Set X)) :
    MulAut ↥M where
  toFun m := ⟨u * m * u⁻¹, (Subgroup.mem_normalizer_iff.mp hu m).mp m.2⟩
  invFun m := ⟨u⁻¹ * m * u, (Subgroup.mem_normalizer_iff''.mp hu m).mp m.2⟩
  left_inv m := Subtype.ext (by simp [mul_assoc])
  right_inv m := Subtype.ext (by simp [mul_assoc])
  map_mul' m n := Subtype.ext (by simp [mul_assoc])

theorem coe_conjOn (M : Subgroup X) {u : X} (hu : u ∈ Subgroup.normalizer (M : Set X))
    (m : ↥M) : ((conjOn M hu m : ↥M) : X) = u * m * u⁻¹ := rfl

theorem conjOn_mul (M : Subgroup X) {u v : X} (hu : u ∈ Subgroup.normalizer (M : Set X))
    (hv : v ∈ Subgroup.normalizer (M : Set X)) :
    conjOn M (Subgroup.mul_mem _ hu hv) = conjOn M hu * conjOn M hv := by
  ext m
  simp [coe_conjOn, mul_assoc]

theorem coe_conjOn_pow_apply (M : Subgroup X) {u : X} (hu : u ∈ Subgroup.normalizer (M : Set X))
    (n : ℕ) (m : ↥M) : (((conjOn M hu ^ n) m : ↥M) : X) = u ^ n * m * (u ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, coe_conjOn, ih]
    group

theorem conjOn_pow (M : Subgroup X) {u : X} (hu : u ∈ Subgroup.normalizer (M : Set X))
    (n : ℕ) : conjOn M (Subgroup.pow_mem _ hu n) = conjOn M hu ^ n := by
  ext m
  rw [coe_conjOn, coe_conjOn_pow_apply]

theorem conjOn_inv (M : Subgroup X) {u : X} (hu : u ∈ Subgroup.normalizer (M : Set X)) :
    conjOn M (Subgroup.inv_mem _ hu) = (conjOn M hu)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← conjOn_mul]
  ext m
  simp [coe_conjOn]

theorem conjOn_of_mem (M : Subgroup X) (m : ↥M) :
    conjOn M (Subgroup.le_normalizer m.2) = MulAut.conj m := by
  ext x
  rfl

theorem conjOn_eq_one_iff (M : Subgroup X) {u : X} (hu : u ∈ Subgroup.normalizer (M : Set X)) :
    conjOn M hu = 1 ↔ ∀ m ∈ M, u * m = m * u := by
  constructor
  · intro h m hm
    have := congrArg Subtype.val (congrArg (fun f : MulAut ↥M => f ⟨m, hm⟩) h)
    simp only [coe_conjOn, MulAut.one_apply] at this
    calc u * m = u * m * u⁻¹ * u := by group
      _ = m * u := by rw [this]
  · intro h
    ext m
    simp only [coe_conjOn, MulAut.one_apply]
    rw [h m m.2, mul_inv_cancel_right]

theorem congr_apply_eq {M P : Type*} [Group M] [Group P] (e : M ≃* P) (f : MulAut M) (p : P) :
    MulAut.congr e f p = e (f (e.symm p)) := rfl

theorem congr_conj {M P : Type*} [Group M] [Group P] (e : M ≃* P) (m : M) :
    MulAut.congr e (MulAut.conj m) = MulAut.conj (e m) := by
  ext p
  rw [congr_apply_eq, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem exists_sq_eq_one_card_gt_four [Finite X] {V : Subgroup X} (hV2 : ∀ v ∈ V, v * v = 1)
    (hV3 : 2 < Nat.card V) {w : X} (hw2 : w * w = 1) (hwV : w ∉ V)
    (hcomm : ∀ v ∈ V, w * v = v * w) :
    ∃ E : Subgroup X, (∀ x ∈ E, x * x = 1) ∧ 4 < Nat.card E := by
  classical
  set S : Set X := (V : Set X) ∪ {w} with hS
  have hSsq : ∀ x ∈ S, x * x = 1 := by
    rintro x (hx | hx)
    · exact hV2 x hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hw2
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have hab := hV2 _ (V.mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hV2 a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hV2 b hb)
    have : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
    rw [mul_inv_rev, ha', hb'] at this
    exact this.symm
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro x (hx | hx) y (hy | hy)
    · exact hVcomm x hx y hy
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (hcomm x hx).symm
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hcomm y hy
    · rw [Set.mem_singleton_iff] at hx hy
      rw [hx, hy]
  have hcl1 : ∀ x ∈ S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {x} := by
      rw [Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hScomm x hx z hz).symm
    have := hle hy
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this.symm
  have hcl : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {y} := by
      rw [Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hcl1 z hz y hy
    have := hle hx
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  refine ⟨Subgroup.closure S, fun x hx => ?_, ?_⟩
  · induction hx using Subgroup.closure_induction with
    | mem x hx => exact hSsq x hx
    | one => exact one_mul 1
    | mul x y hx hy ihx ihy =>
      calc x * y * (x * y) = x * x * (y * y) := by
            rw [mul_assoc, ← mul_assoc y x y, ← hcl x hx y hy]
            group
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]
  · have hVE : V ≤ Subgroup.closure S := fun v hv => Subgroup.subset_closure (Or.inl hv)
    have hwE : w ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inr rfl)
    have hdvd := Subgroup.card_dvd_of_le hVE
    have hne : Nat.card V ≠ Nat.card (Subgroup.closure S) := by
      intro h
      have := Subgroup.eq_of_le_of_card_ge hVE h.symm.le
      exact hwV (this ▸ hwE)
    obtain ⟨k, hk⟩ := hdvd
    have hpos : 0 < Nat.card (Subgroup.closure S) := Nat.card_pos
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · rw [mul_zero] at hk
        omega
      · rw [zero_add, mul_one] at hk
        exact absurd hk.symm hne
      · omega
    rw [hk]
    nlinarith

theorem mem_of_pow_two_pow_eq_one [Finite X] {P : Type*} [Group P] {M : Subgroup X}
    (e : ↥M ≃* P) (hE : ∀ E : Subgroup X, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 4)
    {V : Subgroup P} (hV2 : ∀ v ∈ V, v * v = 1) (hV3 : 2 < Nat.card V)
    (hZ : ∀ m : ↥M, (∀ x : ↥M, m * x = x * m) → m = 1)
    (hAut : ∀ α : MulAut P, (∃ y : P, α ^ 3 = MulAut.conj y) ∨
      ∃ y : P, ((MulAut.conj y)⁻¹ * α) ^ 2 = 1 ∧ (∀ v ∈ V, ((MulAut.conj y)⁻¹ * α) v = v) ∧
        ∀ z : P, (MulAut.conj y)⁻¹ * α ≠ MulAut.conj z)
    {u : X} (hu : u ∈ Subgroup.normalizer (M : Set X)) {j : ℕ} (huj : u ^ 2 ^ j = 1) :
    u ∈ M := by
  classical
  set T : MulAut ↥M ≃* MulAut P := MulAut.congr e with hT
  set W : Subgroup X := (V.map e.symm.toMonoidHom).map M.subtype with hWdef
  have hWM : W ≤ M := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hW2 : ∀ x ∈ W, x * x = 1 := by
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have h := hV2 v hv
    change ((e.symm v : ↥M) : X) * (e.symm v : ↥M) = 1
    rw [← Subgroup.coe_mul, ← map_mul, h, map_one, Subgroup.coe_one]
  have hW3 : 2 < Nat.card W := by
    rw [hWdef, Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
    exact hV3
  have hWv : ∀ v ∈ V, ((e.symm v : ↥M) : X) ∈ W := fun v hv => ⟨e.symm v, ⟨v, hv, rfl⟩, rfl⟩
  have hC : ∀ c : X, (∀ m ∈ M, c * m = m * c) → c * c = 1 → c = 1 := by
    intro c hcM hc2
    by_contra hc1
    have hcM' : c ∉ M := by
      intro hcm
      apply hc1
      have := hZ ⟨c, hcm⟩ (fun x => Subtype.ext (hcM x x.2))
      exact congrArg Subtype.val this
    obtain ⟨E, hE2, hE4⟩ := exists_sq_eq_one_card_gt_four hW2 hW3 hc2
      (fun h => hcM' (hWM h)) (fun v hv => hcM v (hWM hv))
    have := hE E hE2
    omega
  have hβ : ∀ (w : X) (hw : w ∈ Subgroup.normalizer (M : Set X)) (β : MulAut P),
      T (conjOn M hw) = β → β ^ 2 = 1 → (∀ v ∈ V, β v = v) →
        (∀ z : P, β ≠ MulAut.conj z) → False := by
    intro w hw β hwβ hβ2 hβV hβinn
    have hwact : ∀ x : ↥M, conjOn M hw x = e.symm (β (e x)) := by
      intro x
      rw [← hwβ, hT, congr_apply_eq, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    have hwM : ∀ (w' : X) (hw' : w' ∈ Subgroup.normalizer (M : Set X)),
        T (conjOn M hw') = β → w' ∉ M := by
      intro w' hw' hw'β hw'M
      apply hβinn (e ⟨w', hw'M⟩)
      rw [← hw'β, ← congr_conj, ← conjOn_of_mem M ⟨w', hw'M⟩]
    have hwV : ∀ (w' : X) (hw' : w' ∈ Subgroup.normalizer (M : Set X)),
        T (conjOn M hw') = β → ∀ x ∈ W, w' * x = x * w' := by
      intro w' hw' hw'β x hx
      obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := hx
      have hact : conjOn M hw' (e.symm v) = e.symm v := by
        have : ∀ y : ↥M, conjOn M hw' y = e.symm (β (e y)) := by
          intro y
          rw [← hw'β, hT, congr_apply_eq, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
        rw [this, MulEquiv.apply_symm_apply, hβV v hv]
      have h1 := congrArg Subtype.val hact
      rw [coe_conjOn] at h1
      change w' * ((e.symm v : ↥M) : X) = ((e.symm v : ↥M) : X) * w'
      calc w' * ((e.symm v : ↥M) : X) = w' * ((e.symm v : ↥M) : X) * w'⁻¹ * w' := by group
        _ = ((e.symm v : ↥M) : X) * w' := by rw [h1]
    have hw2 : ∀ m ∈ M, w ^ 2 * m = m * w ^ 2 := by
      have h := conjOn_pow M hw 2
      have h1 : conjOn M hw ^ 2 = 1 := by
        apply T.injective
        rw [map_pow, hwβ, hβ2, map_one]
      rw [h1] at h
      exact (conjOn_eq_one_iff M _).mp h
    set k := orderOf (w ^ 2) with hk
    have hk0 : 0 < k := orderOf_pos (w ^ 2)
    have hkodd : Odd k := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨i, hi⟩ := hev
      have hi0 : i ≠ 0 := by
        rintro rfl
        omega
      have hc : (w ^ 2) ^ i * (w ^ 2) ^ i = 1 := by
        rw [← pow_add, ← hi, hk, pow_orderOf_eq_one]
      have hcne : (w ^ 2) ^ i ≠ 1 := pow_ne_one_of_lt_orderOf hi0 (by omega)
      apply hcne
      apply hC _ _ hc
      intro m hm
      have hcomm : Commute (w ^ 2) m := hw2 m hm
      exact (hcomm.pow_left i).eq
    obtain ⟨i, hi⟩ := hkodd
    have hwk : w ^ k ∈ Subgroup.normalizer (M : Set X) := Subgroup.pow_mem _ hw k
    have hwkβ : T (conjOn M hwk) = β := by
      rw [conjOn_pow M hw k, map_pow, hwβ, hi, pow_succ, pow_mul, hβ2, one_pow, one_mul]
    have hwk2 : w ^ k * w ^ k = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, hk, pow_orderOf_eq_one]
    obtain ⟨E, hE2, hE4⟩ := exists_sq_eq_one_card_gt_four hW2 hW3 hwk2
      (fun h => hwM _ hwk hwkβ (hWM h)) (hwV _ hwk hwkβ)
    have := hE E hE2
    omega
  set α := T (conjOn M hu) with hα
  have hα2 : α ^ 2 ^ j = 1 := by
    rw [hα, ← map_pow, ← conjOn_pow M hu]
    have : conjOn M (Subgroup.pow_mem _ hu (2 ^ j)) = 1 := by
      rw [conjOn_eq_one_iff]
      intro m _
      rw [huj, one_mul, mul_one]
    rw [this, map_one]
  rcases hAut α with ⟨y, hy⟩ | ⟨y, hy2, hyV, hyinn⟩
  ·
    obtain ⟨s, t, hst⟩ := (Nat.Coprime.pow_right j (by decide : Nat.Coprime 3 2)).isCoprime
    have hαy : α = MulAut.conj (y ^ s) := by
      have h1 : α = α ^ (s * (3 : ℕ) + t * ((2 ^ j : ℕ) : ℤ)) := by
        rw [show s * ((3 : ℕ) : ℤ) + t * ((2 ^ j : ℕ) : ℤ) = 1 by exact_mod_cast hst, zpow_one]
      rw [h1, zpow_add, mul_comm s, mul_comm t, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast,
        hy, hα2, one_zpow, mul_one, map_zpow]
    set m : ↥M := e.symm (y ^ s) with hm
    set c : X := (m : X)⁻¹ * u with hc
    have hcN : c ∈ Subgroup.normalizer (M : Set X) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer m.2)) hu
    have hcM : ∀ x ∈ M, c * x = x * c := by
      have h1 : conjOn M hcN = 1 := by
        have h2 : conjOn M hcN = conjOn M (Subgroup.inv_mem _ (Subgroup.le_normalizer m.2)) *
            conjOn M hu := conjOn_mul M _ hu
        rw [h2, conjOn_inv M (Subgroup.le_normalizer m.2), conjOn_of_mem M m]
        apply T.injective
        rw [map_mul, map_inv, congr_conj, ← hα, hαy, hm, MulEquiv.apply_symm_apply, map_one,
          inv_mul_cancel]
      exact (conjOn_eq_one_iff M hcN).mp h1
    have hum : u = (m : X) * c := by rw [hc, mul_inv_cancel_left]
    have hcm : Commute (m : X) c := (hcM m m.2).symm
    have hcj : c ^ 2 ^ j = 1 := by
      have h1 : (m : X) ^ 2 ^ j * c ^ 2 ^ j = 1 := by
        rw [← hcm.mul_pow, ← hum, huj]
      have hmem : c ^ 2 ^ j ∈ M := by
        have : c ^ 2 ^ j = ((m : X) ^ 2 ^ j)⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]
        exact M.inv_mem (M.pow_mem m.2 _)
      have := hZ ⟨c ^ 2 ^ j, hmem⟩ (fun x => Subtype.ext ((Commute.pow_left (hcM x x.2) _).eq))
      exact congrArg Subtype.val this
    have hc1 : c = 1 := by
      by_contra hc1
      have hord : orderOf c ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hcj
      obtain ⟨i, hij, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
      have hi0 : i ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hi
        exact hc1 (orderOf_eq_one_iff.mp hi)
      obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      have hc' : c ^ 2 ^ i' * c ^ 2 ^ i' = 1 := by
        rw [← pow_add, ← two_mul, ← pow_succ', ← hi, pow_orderOf_eq_one]
      have hne : c ^ 2 ^ i' ≠ 1 := by
        apply pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero)
        rw [hi]
        exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self i')
      exact hne (hC _ (fun x hx => (Commute.pow_left (hcM x hx) _).eq) hc')
    rw [hum, hc1, mul_one]
    exact m.2
  ·
    exfalso
    set m : ↥M := e.symm y with hm
    have hwN : (m : X)⁻¹ * u ∈ Subgroup.normalizer (M : Set X) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer m.2)) hu
    refine hβ _ hwN _ ?_ hy2 hyV hyinn
    rw [conjOn_mul M (Subgroup.inv_mem _ (Subgroup.le_normalizer m.2)) hu,
      conjOn_inv M (Subgroup.le_normalizer m.2), conjOn_of_mem M m, map_mul, map_inv, congr_conj,
      hm, MulEquiv.apply_symm_apply]

end KL3Sub2Proof

end CFSG.RankThree.PartTwo.Sec15
