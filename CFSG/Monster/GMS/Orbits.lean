module

import CFSG.Monster.GMS.FinalStep
public import CFSG.Monster.GMS.Facts.Leech
public import CFSG.Monster.GMS.Facts.TableV

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type*} [Group G]

section Helpers

theorem mul_comm_of_mul_self_eq_one {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) * (x * y) = 1) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  rw [mul_inv_rev, hx', hy'] at h
  exact h.symm

theorem orderOf_eq_two_of_mul_self {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) :
    orderOf x = 2 :=
  orderOf_eq_prime (by rw [sq]; exact hx) hx1

theorem mul_self_eq_one_of_orderOf {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  rw [← sq, ← hx, pow_orderOf_eq_one]

theorem ne_one_of_orderOf {x : G} (hx : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  simp at hx

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem orderOf_eq_of_isConj {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact (orderOf_conj_eq c x).symm

theorem conj_mul_of_mem_centralizer {g a : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G)) (x : G) :
    g * (a * x) * g⁻¹ = a * (g * x * g⁻¹) := by
  have h : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  calc g * (a * x) * g⁻¹ = (g * a) * x * g⁻¹ := by group
    _ = a * g * x * g⁻¹ := by rw [h]
    _ = a * (g * x * g⁻¹) := by group

theorem conj_mul_conj (c x y : G) : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by
  group

theorem index_subgroupOf_centralizer_eq_ncard (H : Subgroup G) (x : G) :
    ((Subgroup.centralizer ({x} : Set G)).subgroupOf H).index =
      {y : G | ∃ h ∈ H, h * x * h⁻¹ = y}.ncard := by
  rw [← MulAction.stabilizer_comap_conj_eq_centralizer_singleton, ← Subgroup.relIndex,
    Subgroup.relIndex_comap, Subgroup.relIndex, MulAction.stabilizer_subgroupOf,
    MulAction.index_stabilizer]
  congr 1
  ext y
  simp [MulAction.mem_orbit_iff, Subgroup.smul_def]

theorem card_inf_centralizer_mul_ncard {H : Subgroup G} {Y : Set G}
    (hcl : ∀ g ∈ H, ∀ q ∈ Y, g * q * g⁻¹ ∈ Y)
    (htr : ∀ q ∈ Y, ∀ q' ∈ Y, ∃ g ∈ H, g * q * g⁻¹ = q') {q : G} (hq : q ∈ Y) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({q} : Set G)) * Y.ncard = Nat.card H := by
  have hY : {y : G | ∃ h ∈ H, h * q * h⁻¹ = y} = Y := by
    ext y
    exact ⟨fun ⟨h, hh, e⟩ => e ▸ hcl h hh q hq, fun hy => htr q hq y hy⟩
  rw [← hY, ← index_subgroupOf_centralizer_eq_ncard, inf_comm, mul_comm]
  exact Subgroup.relIndex_mul_card (Subgroup.centralizer ({q} : Set G)) H

theorem card_inf_centralizer_conj {H : Subgroup G} {g : G} (hg : g ∈ H) (x : G) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({g * x * g⁻¹} : Set G)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({x} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨g⁻¹ * y.1 * g, ?_⟩
      invFun := fun y => ⟨g * y.1 * g⁻¹, ?_⟩
      left_inv := fun y => Subtype.ext (by group)
      right_inv := fun y => Subtype.ext (by group) }
  · obtain ⟨hyH, hyC⟩ := Subgroup.mem_inf.mp y.2
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem (H.inv_mem hg) hyH) hg, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
    calc g⁻¹ * y.1 * g * x = g⁻¹ * (y.1 * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y.1) * g := by rw [hyC]
      _ = x * (g⁻¹ * y.1 * g) := by group
  · obtain ⟨hyH, hyC⟩ := Subgroup.mem_inf.mp y.2
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hg hyH) (H.inv_mem hg), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
    calc g * y.1 * g⁻¹ * (g * x * g⁻¹) = g * (y.1 * x) * g⁻¹ := by group
      _ = g * (x * y.1) * g⁻¹ := by rw [hyC]
      _ = g * x * g⁻¹ * (g * y.1 * g⁻¹) := by group

theorem card_centralizer_inf_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x y : X) :
    Nat.card ↥(Subgroup.centralizer ({e x} : Set Y) ⊓ Subgroup.centralizer ({e y} : Set Y)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set X) ⊓ Subgroup.centralizer ({y} : Set X)) := by
  rw [← map_centralizer_singleton e x, ← map_centralizer_singleton e y,
    ← Subgroup.map_inf _ _ e.toMonoidHom e.injective,
    Subgroup.card_map_of_injective e.injective]

theorem card_centralizer_inf_conj (g x y : G) :
    Nat.card ↥(Subgroup.centralizer ({g * x * g⁻¹} : Set G) ⊓
        Subgroup.centralizer ({g * y * g⁻¹} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) :=
  card_centralizer_inf_map (MulAut.conj g) x y

theorem isConj_of_involutions_of_odd_orderOf_mul {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hodd : Odd (orderOf (x * y))) : IsConj x y := by
  obtain ⟨k, hk⟩ := hodd
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hrx : (x * y) * x = x * (x * y)⁻¹ := by
    rw [mul_inv_rev, hx', hy', mul_assoc]
  have hpow : ∀ n : ℕ, (x * y) ^ n * x = x * ((x * y) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (x * y) ^ (n + 1) * x = (x * y) ^ n * ((x * y) * x) := by rw [pow_succ, mul_assoc]
        _ = (x * y) ^ n * x * (x * y)⁻¹ := by rw [hrx, mul_assoc]
        _ = x * ((x * y) ^ n)⁻¹ * (x * y)⁻¹ := by rw [ih]
        _ = x * ((x * y) ^ (n + 1))⁻¹ := by simp only [pow_succ', mul_inv_rev, mul_assoc]
  have h1 : (x * y) ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one (x * y)
  refine isConj_iff.mpr ⟨(x * y) ^ k, ?_⟩
  calc (x * y) ^ k * x * ((x * y) ^ k)⁻¹ = x * ((x * y) ^ k)⁻¹ * ((x * y) ^ k)⁻¹ := by
        rw [hpow]
    _ = x * ((x * y) ^ (2 * k))⁻¹ := by rw [mul_assoc, ← mul_inv_rev, ← pow_add, two_mul]
    _ = x * (x * y) := by
        congr 1
        rw [inv_eq_iff_mul_eq_one, ← pow_succ, h1]
    _ = y := by rw [← mul_assoc, hx, one_mul]

theorem dihedral_central_involution {r x : G} {k : ℕ} (hr : r * r = 1) (hx : x * x = 1)
    (hk : orderOf (r * x) = 2 * k) (hk0 : 0 < k) :
    (r * x) ^ k * (r * x) ^ k = 1 ∧ (r * x) ^ k ≠ 1 ∧
      (r * x) ^ k * r = r * (r * x) ^ k ∧ (r * x) ^ k * x = x * (r * x) ^ k ∧
      (IsConj r ((r * x) ^ k * r) ∨ IsConj r ((r * x) ^ k * x)) := by
  generalize hs : r * x = s at hk ⊢
  have hr' : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hs2k : s ^ (2 * k) = 1 := hk ▸ pow_orderOf_eq_one s
  have hz1 : s ^ k * s ^ k = 1 := by rw [← pow_add, ← two_mul, hs2k]
  have hzinv : (s ^ k)⁻¹ = s ^ k := inv_eq_of_mul_eq_one_right hz1
  have hne : s ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0.ne' (by omega)
  have hrs : r * s * r = s⁻¹ := by
    rw [← hs, mul_inv_rev, hx', hr']
    calc r * (r * x) * r = (r * r) * x * r := by group
      _ = x * r := by rw [hr, one_mul]
  have hxs : x * s * x = s⁻¹ := by
    rw [← hs, mul_inv_rev, hx', hr']
    calc x * (r * x) * x = x * r * (x * x) := by group
      _ = x * r := by rw [hx, mul_one]
  have hpowr : ∀ n : ℕ, r * s ^ n * r = (s ^ n)⁻¹ := by
    intro n
    have := conj_pow (a := r) (b := s) (i := n)
    rw [hr'] at this
    rw [← this, hrs, inv_pow]
  have hpowx : ∀ n : ℕ, x * s ^ n * x = (s ^ n)⁻¹ := by
    intro n
    have := conj_pow (a := x) (b := s) (i := n)
    rw [hx'] at this
    rw [← this, hxs, inv_pow]
  have hzr : s ^ k * r = r * s ^ k := by
    have h := hpowr k
    rw [hzinv] at h
    calc s ^ k * r = r * s ^ k * r * r := by rw [h]
      _ = r * s ^ k := by rw [mul_assoc (r * s ^ k) r r, hr, mul_one]
  have hzx : s ^ k * x = x * s ^ k := by
    have h := hpowx k
    rw [hzinv] at h
    calc s ^ k * x = x * s ^ k * x * x := by rw [h]
      _ = x * s ^ k := by rw [mul_assoc (x * s ^ k) x x, hx, mul_one]
  refine ⟨hz1, hne, hzr, hzx, ?_⟩
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
  all_goals
    have hconj : s ^ j * r * (s ^ j)⁻¹ = s ^ (2 * j) * r := by
      rw [← hpowr j]
      calc s ^ j * r * (r * s ^ j * r) = s ^ j * (r * r) * s ^ j * r := by group
        _ = s ^ (2 * j) * r := by rw [hr, mul_one, ← pow_add, two_mul]
  · left
    exact isConj_iff.mpr ⟨s ^ j, by rw [hconj, hj]⟩
  · right
    refine isConj_iff.mpr ⟨s ^ j, ?_⟩
    rw [hconj, hj]
    have hsx : s * x = r := by rw [← hs, mul_assoc, hx, mul_one]
    calc s ^ (2 * j) * r = s ^ (2 * j) * (s * x) := by rw [hsx]
      _ = s ^ (2 * j + 1) * x := by rw [pow_succ, mul_assoc]

end Helpers

section TableVFacts

theorem TableV.cover {a b z u : G} (h : TableV a b z u) :
    ∀ t ∈ Subgroup.centralizer ({a} : Set G), orderOf t = 2 → t ≠ a →
      ∃ g ∈ Subgroup.centralizer ({a} : Set G),
        g * t * g⁻¹ = b ∨ g * t * g⁻¹ = z ∨ g * t * g⁻¹ = a * z ∨ g * t * g⁻¹ = u := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := h
  exact h

theorem TableV.card_centralizer {a b z u : G} (h : TableV a b z u) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) = twoBabyOrder := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := h
  exact h

theorem TableV.card_b {a b z u : G} (h : TableV a b z u) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {b}) = tableVOrderB := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h
  exact h

theorem TableV.card_z {a b z u : G} (h : TableV a b z u) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {z}) = tableVOrderZ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h
  exact h

theorem TableV.card_u {a b z u : G} (h : TableV a b z u) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {u}) = tableVOrderU := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h
  exact h

theorem TableV.mem_z {a b z u : G} (h : TableV a b z u) :
    z ∈ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨-, h, -⟩ := h
  exact h

theorem TableV.mem_u {a b z u : G} (h : TableV a b z u) :
    u ∈ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨-, -, h, -⟩ := h
  exact h

theorem TableV.orderOf_z {a b z u : G} (h : TableV a b z u) : orderOf z = 2 := by
  obtain ⟨-, -, -, -, h, -⟩ := h
  exact h

theorem TableV.orderOf_u {a b z u : G} (h : TableV a b z u) : orderOf u = 2 := by
  obtain ⟨-, -, -, -, -, h, -⟩ := h
  exact h

theorem TableV.ne_z {a b z u : G} (h : TableV a b z u) : z ≠ a := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := h
  exact h

theorem TableV.ne_u {a b z u : G} (h : TableV a b z u) : u ≠ a := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := h
  exact h

theorem mem_centralizer_singleton_map_iff {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (a x : X) :
    e x ∈ Subgroup.centralizer ({e a} : Set Y) ↔ x ∈ Subgroup.centralizer ({a} : Set X) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← map_mul,
    ← map_mul, e.injective.eq_iff]

theorem TableV.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {a b z u : X}
    (h : TableV a b z u) : TableV (e a) (e b) (e z) (e u) := by
  obtain ⟨hb, hz, hu, hb2, hz2, hu2, hba, hza, hua, hcov, hcard, hcb, hcz, hcu, hcen⟩ := h
  have hcard' : ∀ x : X, Nat.card (Subgroup.centralizer ({e x} : Set Y)) =
      Nat.card (Subgroup.centralizer ({x} : Set X)) := fun x =>
    (Nat.card_congr (centralizerMulEquiv e x).toEquiv).symm
  refine ⟨(mem_centralizer_singleton_map_iff e a b).mpr hb,
    (mem_centralizer_singleton_map_iff e a z).mpr hz,
    (mem_centralizer_singleton_map_iff e a u).mpr hu,
    by rw [MulEquiv.orderOf_eq]; exact hb2, by rw [MulEquiv.orderOf_eq]; exact hz2,
    by rw [MulEquiv.orderOf_eq]; exact hu2, fun hh => hba (e.injective hh),
    fun hh => hza (e.injective hh), fun hh => hua (e.injective hh), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht ht2 hta
    set t₀ : X := e.symm t with ht₀
    have ht₀' : t = e t₀ := by rw [ht₀, MulEquiv.apply_symm_apply]
    rw [ht₀'] at ht ht2 hta
    obtain ⟨g, hg, hgt⟩ := hcov t₀ ((mem_centralizer_singleton_map_iff e a t₀).mp ht)
      (by rwa [MulEquiv.orderOf_eq] at ht2) (fun hh => hta (by rw [hh]))
    refine ⟨e g, (mem_centralizer_singleton_map_iff e a g).mpr hg, ?_⟩
    rw [ht₀']
    have hmap : ∀ y : X, e g * e t₀ * (e g)⁻¹ = e y ↔ g * t₀ * g⁻¹ = y := fun y => by
      rw [← map_inv, ← map_mul, ← map_mul, e.injective.eq_iff]
    rw [show e a * e z = e (a * z) from (map_mul e a z).symm]
    simp only [hmap]
    exact hgt
  · rw [hcard' a]; exact hcard
  · rw [card_centralizer_inf_map e a b]; exact hcb
  · rw [card_centralizer_inf_map e a z]; exact hcz
  · rw [card_centralizer_inf_map e a u]; exact hcu
  · intro T hT hTcard x
    set T' : Subgroup X := T.map e.symm.toMonoidHom with hT'
    have hT'le : T' ≤ Subgroup.centralizer ({a} : Set X) ⊓ Subgroup.centralizer {z} := by
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp (hT ht)
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (mem_centralizer_singleton_map_iff e a (e.symm t)).mp (by simpa using h1)
      · exact (mem_centralizer_singleton_map_iff e z (e.symm t)).mp (by simpa using h2)
    have hT'card : Nat.card T' = 2 ^ 42 := by
      rw [hT', Subgroup.card_map_of_injective e.symm.injective]
      exact hTcard
    have hmemT : ∀ y : X, e y ∈ T ↔ y ∈ T' := fun y => by
      rw [hT', Subgroup.mem_map_equiv]
      simp
    obtain ⟨x₀, rfl⟩ := e.surjective x
    have key := hcen T' hT'le hT'card x₀
    rw [hmemT]
    have hall : (∀ s ∈ T, e x₀ * s = s * e x₀) ↔ ∀ s ∈ T', x₀ * s = s * x₀ := by
      constructor
      · intro hs s hs'
        have := hs (e s) ((hmemT s).mpr hs')
        rw [← map_mul, ← map_mul, e.injective.eq_iff] at this
        exact this
      · intro hs s hs'
        obtain ⟨s₀, rfl⟩ := e.surjective s
        have := hs s₀ ((hmemT s₀).mp hs')
        rw [← map_mul, ← map_mul, this]
    rw [hall, key]
    simp only [e.injective.eq_iff, ← map_mul, e.map_eq_one_iff]

theorem TableV.conj {a b z u : G} (h : TableV a b z u) (c : G) :
    TableV (c * a * c⁻¹) (c * b * c⁻¹) (c * z * c⁻¹) (c * u * c⁻¹) :=
  h.of_mulEquiv (MulAut.conj c)

end TableVFacts

section LeechQ

theorem leechQ_le_centralizer (z : G) : leechQ z ≤ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.map_subtype_le _

theorem leechQ_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (z : X) :
    (leechQ z).map e.toMonoidHom = leechQ (e z) := by
  have hcore := CFSG.pCore_map_iso 2 (centralizerMulEquiv e z)
  unfold leechQ
  rw [Subgroup.map_map, ← hcore, Subgroup.map_map]
  congr 1

theorem mem_leechQ_conj_iff (c z y : G) : y ∈ leechQ (c * z * c⁻¹) ↔ c⁻¹ * y * c ∈ leechQ z := by
  have h := leechQ_map (MulAut.conj c) z
  simp only [MulAut.conj_apply] at h
  rw [← h, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem conj_mem_leechQ_conj {c z y : G} (hy : y ∈ leechQ z) :
    c * y * c⁻¹ ∈ leechQ (c * z * c⁻¹) := by
  rw [mem_leechQ_conj_iff]
  simpa [mul_assoc] using hy

theorem card_leechQ_inf_centralizer_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (z y : X) :
    Nat.card ↥(leechQ (e z) ⊓ Subgroup.centralizer ({e y} : Set Y)) =
      Nat.card ↥(leechQ z ⊓ Subgroup.centralizer ({y} : Set X)) := by
  rw [← leechQ_map e z, ← map_centralizer_singleton e y,
    ← Subgroup.map_inf _ _ e.toMonoidHom e.injective,
    Subgroup.card_map_of_injective e.injective]

theorem card_leechQ_inf_centralizer_conj (c z y : G) :
    Nat.card ↥(leechQ (c * z * c⁻¹) ⊓ Subgroup.centralizer ({c * y * c⁻¹} : Set G)) =
      Nat.card ↥(leechQ z ⊓ Subgroup.centralizer ({y} : Set G)) :=
  card_leechQ_inf_centralizer_map (MulAut.conj c) z y

theorem conj_mem_leechQ {z g q : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G))
    (hq : q ∈ leechQ z) : g * q * g⁻¹ ∈ leechQ z := by
  obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.mp hq
  exact Subgroup.mem_map.mpr
    ⟨⟨g, hg⟩ * q' * ⟨g, hg⟩⁻¹, (CFSG.pCore_normal).conj_mem q' hq' ⟨g, hg⟩, rfl⟩

theorem exists_orderOf_eq_two_pow_of_mem_leechQ {z q : G} (hq : q ∈ leechQ z) :
    ∃ k : ℕ, orderOf q = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.mp hq
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp CFSG.pCore_isPGroup ⟨q', hq'⟩
  refine ⟨k, ?_⟩
  have h1 : orderOf (q' : G) = orderOf q' := Subgroup.orderOf_coe q'
  have h2 : orderOf (⟨q', hq'⟩ : CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))) =
      orderOf q' := Subgroup.orderOf_mk q' hq'
  show orderOf (q' : G) = 2 ^ k
  rw [h1, ← h2, hk]

end LeechQ

section Leech

structure LeechOrbits (z : G) (T₂ T₃ T₄ : Set G) : Prop where
  cover : ∀ q ∈ leechQ z, q ≠ 1 → q ≠ z → q ∈ T₂ ∨ q ∈ T₃ ∨ q ∈ T₄
  two_sub : T₂ ⊆ leechQ z
  four_sub : T₄ ⊆ leechQ z
  two : ∀ q ∈ T₂, q ≠ 1 ∧ q ≠ z ∧ q * q = 1 ∧ q * z ∈ T₂
  four : ∀ q ∈ T₄, q ≠ 1 ∧ q ≠ z ∧ q * q = 1 ∧ q * z ∈ T₄
  three : ∀ q ∈ T₃, q * q = z
  conj_two : ∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ q ∈ T₂, g * q * g⁻¹ ∈ T₂
  conj_four : ∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ q ∈ T₄, g * q * g⁻¹ ∈ T₄
  trans_two : ∀ q ∈ T₂, ∀ q' ∈ T₂, ∃ g ∈ Subgroup.centralizer ({z} : Set G), g * q * g⁻¹ = q'
  trans_four : ∀ q ∈ T₄, ∀ q' ∈ T₄, ∃ g ∈ Subgroup.centralizer ({z} : Set G), g * q * g⁻¹ = q'
  card_four : T₄.ncard = 16584750
  pair_a : ∀ q ∈ T₂, ∃ q' ∈ T₂, q * q' ∈ T₂ ∧
    3 ^ 6 * 11 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {q} ⊓
      Subgroup.centralizer {q'})
  pair_b : ∀ q ∈ T₂, ∃ q' ∈ T₄, q * q' ∈ T₂ ∧
    2 ^ 41 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {q} ⊓
      Subgroup.centralizer {q'})
  pair_c : ∀ q ∈ T₂, ∃ q' ∈ T₄, q * q' ∈ T₄

theorem LeechData.exists_orbits {z : G} (h : LeechData z) :
    ∃ T₂ T₃ T₄ : Set G, LeechOrbits z T₂ T₃ T₄ := by
  obtain ⟨T₂, T₃, T₄, hcov, s2, -, s4, -, -, -, h2, h4, h3, c2, -, c4, t2, -, t4, -, -, n4, p1, p2,
    p3, -, -⟩ := h
  exact ⟨T₂, T₃, T₄, ⟨hcov, s2, s4, h2, h4, h3, c2, c4, t2, t4, n4, p1, p2, p3⟩⟩

theorem LeechData.card_le {z : G} (h : LeechData z) :
    ∀ t ∈ Subgroup.centralizer ({z} : Set G), orderOf t = 2 → t ∉ leechQ z →
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t}) ≤
        2 ^ 46 * 3 ^ 5 * 5 ^ 2 * 7 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h
  exact h

theorem LeechData.card_eq {z : G} (h : LeechData z) :
    ∀ t ∈ Subgroup.centralizer ({z} : Set G), orderOf t = 2 → t ∉ leechQ z →
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t}) =
        2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 →
        Nat.card ↥(leechQ z ⊓ Subgroup.centralizer {t}) = 2 ^ 17 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := h
  exact h

theorem GMSLeechCentralizer.of_isConj {z₀ z : G} (h : GMSLeechCentralizer z₀)
    (hc : IsConj z₀ z) : GMSLeechCentralizer z := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  exact h.of_mulEquiv (MulAut.conj c)

theorem mem_leechQ_of_card {z a : G} (h : LeechData z) (ha : orderOf a = 2)
    (haC : a ∈ Subgroup.centralizer ({z} : Set G))
    (hcard : Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {a}) =
      tableVOrderZ) : a ∈ leechQ z := by
  by_contra hQ
  have := h.card_le a haC ha hQ
  rw [hcard] at this
  norm_num [tableVOrderZ] at this

theorem LeechOrbits.isConj_mul {z : G} {T₂ T₃ T₄ : Set G} (h : LeechOrbits z T₂ T₃ T₄)
    (hz : z ≠ 1) {t : G} (ht : t ∈ leechQ z) (ht1 : t ≠ 1) (htz : t ≠ z) (htt : t * t = 1) :
    IsConj t (t * z) := by
  rcases h.cover t ht ht1 htz with h2 | h3 | h4
  · obtain ⟨g, -, hg⟩ := h.trans_two t h2 _ (h.two t h2).2.2.2
    exact isConj_iff.mpr ⟨g, hg⟩
  · exact absurd ((h.three t h3).symm.trans htt) hz
  · obtain ⟨g, -, hg⟩ := h.trans_four t h4 _ (h.four t h4).2.2.2
    exact isConj_iff.mpr ⟨g, hg⟩

theorem LeechData.isConj_mul {z : G} (h : LeechData z) (hz : z ≠ 1) {t : G}
    (ht : t ∈ leechQ z) (ht1 : t ≠ 1) (htz : t ≠ z) (htt : t * t = 1) : IsConj t (t * z) := by
  obtain ⟨T₂, T₃, T₄, hT⟩ := h.exists_orbits
  exact hT.isConj_mul hz ht ht1 htz htt

theorem LeechOrbits.mem_two {z a : G} {T₂ T₃ T₄ : Set G} (h : LeechOrbits z T₂ T₃ T₄)
    (hcz : Nat.card (Subgroup.centralizer ({z} : Set G)) = 2 ^ 46 * 1982582476875) (hz : z ≠ 1)
    (ha : a ∈ leechQ z) (ha1 : a ≠ 1) (haz : a ≠ z) (haa : a * a = 1)
    (hcard : Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {a}) =
      tableVOrderZ) : a ∈ T₂ := by
  rcases h.cover a ha ha1 haz with h2 | h3 | h4
  · exact h2
  · exact absurd ((h.three a h3).symm.trans haa) hz
  · exfalso
    have := card_inf_centralizer_mul_ncard h.conj_four h.trans_four h4
    rw [hcard, h.card_four, hcz] at this
    norm_num [tableVOrderZ] at this

end Leech

section Classes

theorem LeechOrbits.isConj_b {a b z u : G} {T₂ T₃ T₄ : Set G} (h : LeechOrbits z T₂ T₃ T₄)
    (hTV : TableV a b z u) (ha : orderOf a = 2) (hnc : ¬ IsConj a z) (haT : a ∈ T₂) :
    IsConj a b ∧ IsConj a (a * b) := by
  obtain ⟨b₀, hb₀, hab₀, hdvd⟩ := h.pair_a a haT
  have haa : a * a = 1 := mul_self_eq_one_of_orderOf ha
  have hbb : b₀ * b₀ = 1 := (h.two b₀ hb₀).2.2.1
  have hcomm : a * b₀ = b₀ * a :=
    mul_comm_of_mul_self_eq_one haa hbb (h.two _ hab₀).2.2.1
  have hb₀C : b₀ ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hb₀a : b₀ ≠ a := by
    rintro rfl
    exact (h.two _ hab₀).1 haa
  have hb₀2 : orderOf b₀ = 2 := orderOf_eq_two_of_mul_self hbb (h.two b₀ hb₀).1
  have h1 : IsConj a b₀ := by
    obtain ⟨g, -, hg⟩ := h.trans_two a haT b₀ hb₀
    exact isConj_iff.mpr ⟨g, hg⟩
  have h2 : IsConj a (a * b₀) := by
    obtain ⟨g, -, hg⟩ := h.trans_two a haT _ hab₀
    exact isConj_iff.mpr ⟨g, hg⟩
  obtain ⟨g, hg, hcase⟩ := hTV.cover b₀ hb₀C hb₀2 hb₀a
  have hgab : g * (a * b₀) * g⁻¹ = a * (g * b₀ * g⁻¹) := conj_mul_of_mem_centralizer hg b₀
  have haaz : a * (a * z) = z := by rw [← mul_assoc, haa, one_mul]
  rcases hcase with e | e | e | e
  · refine ⟨h1.trans (isConj_iff.mpr ⟨g, e⟩), ?_⟩
    rw [e] at hgab
    exact h2.trans (isConj_iff.mpr ⟨g, hgab⟩)
  · exact absurd (h1.trans (isConj_iff.mpr ⟨g, e⟩)) hnc
  · rw [e, haaz] at hgab
    exact absurd (h2.trans (isConj_iff.mpr ⟨g, hgab⟩)) hnc
  · exfalso
    have hc := card_inf_centralizer_conj hg b₀
    rw [e, hTV.card_u] at hc
    have hd : 3 ^ 6 * 11 ∣ tableVOrderU := by
      rw [hc]
      exact hdvd.trans (Subgroup.card_dvd_of_le (inf_le_inf_right _ inf_le_right))
    norm_num [tableVOrderU] at hd

theorem LeechOrbits.isConj_of_mem_four {a b z u : G} {T₂ T₃ T₄ : Set G}
    (h : LeechOrbits z T₂ T₃ T₄) (hTV : TableV a b z u) (ha : orderOf a = 2)
    (hcz : Nat.card (Subgroup.centralizer ({z} : Set G)) = 2 ^ 46 * 1982582476875)
    (haT : a ∈ T₂) (hacz : IsConj a (a * z)) : ∀ q ∈ T₄, IsConj z q := by
  obtain ⟨z₂, hz₂, haz₂, hdvd⟩ := h.pair_b a haT
  have haa : a * a = 1 := mul_self_eq_one_of_orderOf ha
  have hzz : z₂ * z₂ = 1 := (h.four z₂ hz₂).2.2.1
  have hcomm : a * z₂ = z₂ * a :=
    mul_comm_of_mul_self_eq_one haa hzz (h.two _ haz₂).2.2.1
  have hz₂C : z₂ ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hz₂a : z₂ ≠ a := by
    rintro rfl
    exact (h.two _ haz₂).1 haa
  have hz₂2 : orderOf z₂ = 2 := orderOf_eq_two_of_mul_self hzz (h.four z₂ hz₂).1
  obtain ⟨g, hg, hcase⟩ := hTV.cover z₂ hz₂C hz₂2 hz₂a
  have hdvd' : 2 ^ 41 ∣ Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓
      Subgroup.centralizer {z₂}) :=
    hdvd.trans (Subgroup.card_dvd_of_le (inf_le_inf_right _ inf_le_right))
  have hz₂z : IsConj z z₂ := by
    rcases hcase with e | e | e | e
    · exfalso
      have hc := card_inf_centralizer_conj hg z₂
      rw [e, hTV.card_b] at hc
      rw [← hc] at hdvd'
      norm_num [tableVOrderB] at hdvd'
    · exact (isConj_iff.mpr ⟨g, e⟩).symm
    · exfalso
      have hz₂A : IsConj a z₂ := hacz.trans (isConj_iff.mpr ⟨g, e⟩).symm
      have h1 := card_centralizer_eq_of_isConj hz₂A
      rw [hTV.card_centralizer] at h1
      have h2 := card_inf_centralizer_mul_ncard h.conj_four h.trans_four hz₂
      rw [h.card_four, hcz] at h2
      have h3 : Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {z₂}) =
          2 ^ 45 * 239085 := by
        norm_num at h2 ⊢
        omega
      have h4 : 2 ^ 45 * 239085 ∣ twoBabyOrder := by
        rw [← h3, h1]
        exact Subgroup.card_dvd_of_le inf_le_right
      norm_num [twoBabyOrder] at h4
    · exfalso
      have hc := card_inf_centralizer_conj hg z₂
      rw [e, hTV.card_u] at hc
      rw [← hc] at hdvd'
      norm_num [tableVOrderU] at hdvd'
  intro q hq
  obtain ⟨g', -, e'⟩ := h.trans_four z₂ hz₂ q hq
  exact hz₂z.trans (isConj_iff.mpr ⟨g', e'⟩)

theorem LeechOrbits.isConj_u {a b z u : G} {T₂ T₃ T₄ : Set G} (h : LeechOrbits z T₂ T₃ T₄)
    (hTV : TableV a b z u) (ha : orderOf a = 2) (hnc : ¬ IsConj a z) (haT : a ∈ T₂)
    (hacz : IsConj a (a * z)) (hab : IsConj a b) (hT₄ : ∀ q ∈ T₄, IsConj z q) :
    IsConj z u ∧ IsConj z (a * u) := by
  obtain ⟨u₀, hu₀, hau₀⟩ := h.pair_c a haT
  have haa : a * a = 1 := mul_self_eq_one_of_orderOf ha
  have huu : u₀ * u₀ = 1 := (h.four u₀ hu₀).2.2.1
  have hcomm : a * u₀ = u₀ * a :=
    mul_comm_of_mul_self_eq_one haa huu (h.four _ hau₀).2.2.1
  have hu₀C : u₀ ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hu₀a : u₀ ≠ a := by
    rintro rfl
    exact (h.four _ hau₀).1 haa
  have hu₀2 : orderOf u₀ = 2 := orderOf_eq_two_of_mul_self huu (h.four u₀ hu₀).1
  have h1 : IsConj z u₀ := hT₄ u₀ hu₀
  have h2 : IsConj z (a * u₀) := hT₄ _ hau₀
  obtain ⟨g, hg, hcase⟩ := hTV.cover u₀ hu₀C hu₀2 hu₀a
  have hgau : g * (a * u₀) * g⁻¹ = a * (g * u₀ * g⁻¹) := conj_mul_of_mem_centralizer hg u₀
  rcases hcase with e | e | e | e
  · exact absurd ((hab.trans (isConj_iff.mpr ⟨g, e⟩).symm).trans h1.symm) hnc
  · rw [e] at hgau
    exact absurd (hacz.trans (h2.trans (isConj_iff.mpr ⟨g, hgau⟩)).symm) hnc
  · exact absurd ((hacz.trans (isConj_iff.mpr ⟨g, e⟩).symm).trans h1.symm) hnc
  · rw [e] at hgau
    exact ⟨h1.trans (isConj_iff.mpr ⟨g, e⟩), h2.trans (isConj_iff.mpr ⟨g, hgau⟩)⟩

end Classes

end CFSG.Monster.GMS
