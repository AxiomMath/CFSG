module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.GF2n.Tim78

variable {G : Type*} [Group G]

@[expose] def dlt (y v : G) : G := v⁻¹ * (y * v * y⁻¹)

theorem dlt_eq_one_iff {y v : G} : dlt y v = 1 ↔ y * v = v * y := by
  unfold dlt
  constructor
  · intro h
    have : y * v * y⁻¹ = v := by
      have := congrArg (fun t => v * t) h
      simpa [mul_assoc] using this
    calc y * v = y * v * y⁻¹ * y := by group
      _ = v * y := by rw [this]
  · intro h
    rw [h]
    group

theorem dlt_mem {S : Subgroup G} {y : G} (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S) {v : G}
    (hv : v ∈ S) : dlt y v ∈ S :=
  S.mul_mem (S.inv_mem hv) (hyS v hv)

theorem dlt_sq {S : Subgroup G} (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {y : G}
    (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S) {v : G} (hv : v ∈ S) (hv2 : v ^ 2 = 1) :
    dlt y v ^ 2 = 1 := by
  unfold dlt
  have hw : y * v * y⁻¹ ∈ S := hyS v hv
  have hw2 : (y * v * y⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hv2]
    group
  rw [Commute.mul_pow (hSc _ (S.inv_mem hv) _ hw), inv_pow, hv2, hw2]
  group

theorem dlt_dlt {S : Subgroup G} (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {y : G}
    (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S) {v : G} (hv : v ∈ S) (hv2 : v ^ 2 = 1) :
    dlt y (dlt y v) = dlt (y ^ 2) v := by
  unfold dlt
  set w := y * v * y⁻¹ with hw
  have hwS : w ∈ S := hyS v hv
  have hw2 : w ^ 2 = 1 := by
    rw [hw, conj_pow, hv2]
    group
  have hw' : y * w * y⁻¹ = y ^ 2 * v * (y ^ 2)⁻¹ := by
    rw [hw, pow_two]
    group
  have hyvinv : y * (v⁻¹ * w) * y⁻¹ = w⁻¹ * (y * w * y⁻¹) := by
    rw [hw]
    group
  rw [hyvinv, ← hw']
  set u := y * w * y⁻¹
  have hvinv : v⁻¹ = v := by
    have : v * v = 1 := by rw [← sq]; exact hv2
    exact inv_eq_of_mul_eq_one_right this
  have hwinv : w⁻¹ = w := by
    have : w * w = 1 := by rw [← sq]; exact hw2
    exact inv_eq_of_mul_eq_one_right this
  rw [mul_inv_rev, inv_inv, hvinv, hwinv]
  have hvw : v * w = w * v := hSc v hv w hwS
  calc w * v * (w * u) = w * (v * w) * u := by group
    _ = w * (w * v) * u := by rw [hvw]
    _ = (w * w) * v * u := by group
    _ = v * u := by rw [← sq, hw2, one_mul]

theorem conj_pow_mem {S : Subgroup G} {y : G} (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (n : ℕ) :
    ∀ s ∈ S, y ^ n * s * (y ^ n)⁻¹ ∈ S := by
  induction n with
  | zero => intro s hs; simpa using hs
  | succ n ihn =>
    intro s hs
    have := hyS _ (ihn s hs)
    rw [pow_succ']
    simpa [mul_assoc] using this

theorem dlt_iterate_mem {S : Subgroup G} (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {y : G}
    (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (n : ℕ) :
    ∀ v ∈ S, v ^ 2 = 1 → (dlt y)^[n] v ∈ S ∧ ((dlt y)^[n] v) ^ 2 = 1 := by
  induction n with
  | zero => intro v hv hv2; exact ⟨hv, hv2⟩
  | succ n ih =>
    intro v hv hv2
    rw [Function.iterate_succ_apply]
    exact ih _ (dlt_mem hyS hv) (dlt_sq hSc hyS hv hv2)

theorem dlt_iterate {S : Subgroup G} (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {y : G}
    (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (j : ℕ) :
    ∀ v ∈ S, v ^ 2 = 1 → (dlt y)^[2 ^ j] v = dlt (y ^ 2 ^ j) v := by
  induction j with
  | zero => intro v _ _; simp
  | succ j ih =>
    intro v hv hv2
    have hyjS := conj_pow_mem hyS (2 ^ j)
    have h1 : (dlt y)^[2 ^ (j + 1)] v = (dlt y)^[2 ^ j] ((dlt y)^[2 ^ j] v) := by
      rw [pow_succ, mul_two, Function.iterate_add_apply]
    obtain ⟨hm, hm2⟩ := dlt_iterate_mem hSc hyS (2 ^ j) v hv hv2
    rw [h1, ih _ hm hm2, ih v hv hv2, dlt_dlt hSc hyjS hv hv2, ← pow_mul, ← pow_succ]

theorem commute_of_sq_eq_one {S : Subgroup G} (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {x : G}
    (hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S) (hx : ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hC : ∀ s ∈ S, x * s = s * x ↔ x ^ 2 * s = s * x ^ 2) :
    ∀ v ∈ S, v ^ 2 = 1 → x * v = v * x := by
  obtain ⟨k, hk⟩ := hx
  have key : ∀ n : ℕ, ∀ v ∈ S, v ^ 2 = 1 → (dlt x)^[n + 1] v = 1 → dlt x v = 1 := by
    intro n
    induction n with
    | zero => intro v _ _ h; simpa using h
    | succ n ih =>
      intro v hv hv2 h
      rw [Function.iterate_succ_apply] at h
      have h' : dlt x (dlt x v) = 1 := ih _ (dlt_mem hxS hv) (dlt_sq hSc hxS hv hv2) h
      rw [dlt_dlt hSc hxS hv hv2, dlt_eq_one_iff, ← hC v hv, ← dlt_eq_one_iff] at h'
      exact h'
  intro v hv hv2
  have h2k : (dlt x)^[2 ^ k] v = 1 := by
    rw [dlt_iterate hSc hxS k v hv hv2, hk, dlt]
    group
  have hpos : 2 ^ k = (2 ^ k - 1) + 1 := by
    have := Nat.one_le_two_pow (n := k)
    omega
  rw [hpos] at h2k
  exact dlt_eq_one_iff.mp (key _ v hv hv2 h2k)

theorem tim78_2_1 {S : Subgroup G} (hSc : IsMulCommutative S) (hS2 : IsPGroup 2 S) {x : G}
    (hxS : x ∈ Subgroup.normalizer (S : Set G)) (hx : ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hC : S ⊓ Subgroup.centralizer ({x} : Set G) = S ⊓ Subgroup.centralizer ({x ^ 2} : Set G)) :
    S ≤ Subgroup.centralizer ({x} : Set G) := by
  have hSc' : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hSc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hxS' : ∀ s ∈ S, x * s * x⁻¹ ∈ S := fun s hs =>
    (Subgroup.mem_normalizer_iff.mp hxS s).mp hs
  have hC' : ∀ s ∈ S, x * s = s * x ↔ x ^ 2 * s = s * x ^ 2 := by
    intro s hs
    have h1 : s ∈ S ⊓ Subgroup.centralizer ({x} : Set G) ↔
        s ∈ S ⊓ Subgroup.centralizer ({x ^ 2} : Set G) := by rw [hC]
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, hs, true_and] at h1
    constructor
    · intro h; exact (h1.mp h.symm).symm
    · intro h; exact (h1.mpr h.symm).symm
  have base := commute_of_sq_eq_one hSc' hxS' hx hC'
  have step : ∀ i : ℕ, ∀ s ∈ S, s ^ 2 ^ (i + 1) = 1 → x * s = s * x := by
    intro i
    induction i with
    | zero => intro s hs h; exact base s hs (by simpa using h)
    | succ i ih =>
      intro s hs hsi
      have hs2 : x * s ^ 2 = s ^ 2 * x :=
        ih _ (S.pow_mem hs 2) (by rw [← pow_mul, ← pow_succ']; exact hsi)
      set z := s⁻¹ * (x * s * x⁻¹) with hzdef
      have hzS : z ∈ S := S.mul_mem (S.inv_mem hs) (hxS' s hs)
      have hxs : x * s * x⁻¹ = s * z := by rw [hzdef]; group
      have hsz : s * z = z * s := hSc' s hs z hzS
      have hz2 : z ^ 2 = 1 := by
        have h1 : (x * s * x⁻¹) ^ 2 = s ^ 2 := by
          rw [conj_pow, hs2]
          group
        rw [hxs, Commute.mul_pow hsz] at h1
        exact mul_left_cancel (h1.trans (mul_one _).symm)
      have hzc : x * z = z * x := ih z hzS (by rw [pow_succ', pow_mul, hz2, one_pow])
      have hx2 : x ^ 2 * s = s * x ^ 2 := by
        have hxz : x * z * x⁻¹ = z := by rw [hzc]; group
        have : x ^ 2 * s * (x ^ 2)⁻¹ = s := by
          calc x ^ 2 * s * (x ^ 2)⁻¹ = x * (x * s * x⁻¹) * x⁻¹ := by rw [pow_two]; group
            _ = x * (s * z) * x⁻¹ := by rw [hxs]
            _ = (x * s * x⁻¹) * (x * z * x⁻¹) := by group
            _ = s * z * z := by rw [hxs, hxz]
            _ = s := by rw [mul_assoc, ← sq, hz2, mul_one]
        calc x ^ 2 * s = x ^ 2 * s * (x ^ 2)⁻¹ * x ^ 2 := by group
          _ = s * x ^ 2 := by rw [this]
      exact (hC' s hs).mpr hx2
  intro s hs
  obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
  have hm' : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (step m s hs (by rw [pow_succ, pow_mul, hm', one_pow])).symm

end CFSG.RankThree.GF2n.Tim78
