module

public import CFSG.Milestones.ASVolI.A1

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChA

namespace ChA

section A6Vocabulary

variable {G : Type} [Group G]

@[expose] def conjClass (x : G) : Set G :=
  {y | ∃ g : G, y = g⁻¹ * x * g}

structure HasTwoInvolutionClasses (G : Type) [Group G] (z t : G) : Prop where
  z_inv : z ≠ 1 ∧ z ^ 2 = 1
  t_inv : t ≠ 1 ∧ t ^ 2 = 1
  distinct : t ∉ conjClass z
  all : ∀ x : G, x ≠ 1 → x ^ 2 = 1 → x ∈ conjClass z ∨ x ∈ conjClass t

@[expose] def pairSet (z t x : G) : Set (G × G) :=
  {p | p.1 ∈ conjClass z ∧ p.2 ∈ conjClass t ∧ x ∈ Subgroup.zpowers (p.1 * p.2)}

@[expose] noncomputable def aCount (z t x : G) : ℕ :=
  Nat.card (pairSet z t x)

@[expose] def pairSetI (z t x : G) (i : ℕ) : Set (G × G) :=
  {p | p ∈ pairSet z t x ∧ orderOf (p.1 * p.2) % 4 = (if i = 1 then 0 else 2)}

@[expose] noncomputable def aiCount (z t x : G) (i : ℕ) : ℕ :=
  Nat.card (pairSetI z t x i)

@[expose] def bSet (x : G) (i : ℕ) : Set G :=
  {u | u ∈ conjClass x ∧ u ∈ Subgroup.centralizer ({x} : Set G) ∧
    ((u * x ∈ conjClass u) ↔ i = 1)}

@[expose] noncomputable def bCount (x : G) (i : ℕ) : ℕ :=
  Nat.card (bSet x i)

@[expose] def cSet (x : G) (i : ℕ) : Set G :=
  {u | u ≠ 1 ∧ u ^ 2 = 1 ∧ u ∉ conjClass x ∧ u ∈ Subgroup.centralizer ({x} : Set G) ∧
    ((u * x ∈ conjClass u) ↔ i = 1)}

@[expose] noncomputable def cCount (x : G) (i : ℕ) : ℕ :=
  Nat.card (cSet x i)

end A6Vocabulary

end ChA

@[expose] def A_6_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G), HasTwoInvolutionClasses G z t →
    Nat.card G = Nat.card (Subgroup.centralizer ({z} : Set G)) * aCount z t t +
      Nat.card (Subgroup.centralizer ({t} : Set G)) * aCount z t z

section BurnsideA6

section A6Basic

variable {G : Type} [Group G]

private theorem a6_mem_conjClass_iff {x y : G} : y ∈ conjClass x ↔ IsConj x y := by
  rw [isConj_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c⁻¹, by simp⟩

private theorem a6_card_class_mul_card_centralizer [Finite G] (x : G) :
    Nat.card (conjClass x) * Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card G := by
  have hset : conjClass x = MulAction.orbit (ConjAct G) x := by
    ext y
    rw [a6_mem_conjClass_iff, ConjAct.mem_orbit_conjAct, isConj_comm]
  rw [hset, Subgroup.nat_card_centralizer_nat_card_stabilizer, ← Nat.card_prod,
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) x)]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

private theorem a6_conj_mem_conjClass_iff {x y : G} (g : G) :
    g * y * g⁻¹ ∈ conjClass x ↔ y ∈ conjClass x := by
  rw [a6_mem_conjClass_iff, a6_mem_conjClass_iff]
  have h : IsConj y (g * y * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  exact ⟨fun h' => h'.trans h.symm, fun h' => h'.trans h⟩

private theorem a6_conjClass_eq_of_mem {x y : G} (h : y ∈ conjClass x) : conjClass y =
    conjClass x := by
  ext w
  rw [a6_mem_conjClass_iff, a6_mem_conjClass_iff]
  have h' : IsConj x y := a6_mem_conjClass_iff.mp h
  exact ⟨fun hw => h'.trans hw, fun hw => h'.symm.trans hw⟩

private theorem a6_self_mem_conjClass (x : G) : x ∈ conjClass x := ⟨1, by simp⟩

private theorem a6_involution_in_zpowers [Finite G] {w x : G} (hx1 : x ≠ 1) (hx2 : x * x = 1)
    (hxw : x ∈ Subgroup.zpowers w) :
    ∃ m : ℕ, 0 < m ∧ orderOf w = 2 * m ∧ x = w ^ m := by
  have hpow : x ∈ Submonoid.powers w := mem_powers_iff_mem_zpowers.mpr hxw
  obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff _ _ |>.mp hpow
  have hn : 0 < orderOf w := orderOf_pos w
  set n := orderOf w with hn_def
  have hkx : w ^ (k % n) = x := by rw [pow_mod_orderOf]; exact hk
  have hlt : k % n < n := Nat.mod_lt _ hn
  have hk0 : k % n ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hkx
    exact hx1 hkx.symm
  have h2k : w ^ (2 * (k % n)) = 1 := by
    rw [two_mul, pow_add, hkx, hx2]
  have hdvd : n ∣ 2 * (k % n) := orderOf_dvd_iff_pow_eq_one.mpr h2k
  obtain ⟨c, hc⟩ := hdvd
  have hc1 : c = 1 := by
    rcases c with _ | _ | c
    · omega
    · rfl
    · nlinarith
  subst hc1
  refine ⟨k % n, Nat.pos_of_ne_zero hk0, by omega, hkx.symm⟩

end A6Basic

section A6Dihedral

variable {G : Type} [Group G]

private theorem a6_isConj_conj_iff (g a b : G) :
    IsConj (g * a * g⁻¹) (g * b * g⁻¹) ↔ IsConj a b := by
  have h1 : IsConj a (g * a * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have h2 : IsConj b (g * b * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  exact ⟨fun h => h1.trans (h.trans h2.symm), fun h => h1.symm.trans (h.trans h2)⟩

private theorem a6_zpowers_conj_iff (g w x : G) :
    x ∈ Subgroup.zpowers (g⁻¹ * w * g) ↔ g * x * g⁻¹ ∈ Subgroup.zpowers w := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h := conj_zpow (i := k) (a := g⁻¹) (b := w)
    rw [inv_inv] at h
    rw [h] at hk
    rw [← hk]
    group
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h := conj_zpow (i := k) (a := g⁻¹) (b := w)
    rw [inv_inv] at h
    rw [h, hk]
    group

private theorem a6_invol_mul_pow {u w : G} (hu : u * u = 1) (huw : u * w * u = w⁻¹) (j : ℕ) :
    u * w ^ j * u = (w ^ j)⁻¹ := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have h := conj_pow (i := j) (a := u) (b := w)
  rw [hu', huw, inv_pow] at h
  exact h.symm

private theorem a6_conj_pow {u w : G} (hu : u * u = 1) (huw : u * w * u = w⁻¹) (j : ℕ) :
    (w ^ j)⁻¹ * u * w ^ j = u * w ^ (2 * j) := by
  have h1 := a6_invol_mul_pow hu huw j
  calc (w ^ j)⁻¹ * u * w ^ j = (u * w ^ j * u) * u * w ^ j := by rw [h1]
    _ = u * w ^ j * (u * u) * w ^ j := by simp only [mul_assoc]
    _ = u * w ^ (2 * j) := by rw [hu, mul_one, mul_assoc, ← pow_add, two_mul]

private theorem a6_invert_prod {u v : G} (hu : u * u = 1) (hv : v * v = 1) :
    u * (u * v) * u = (u * v)⁻¹ ∧ v * (u * v) * v = (u * v)⁻¹ := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  rw [mul_inv_rev, hu', hv']
  constructor
  · rw [← mul_assoc, hu, one_mul]
  · rw [mul_assoc, mul_assoc, hv, mul_one]

private theorem a6_comm_pow {u v x : G} {m : ℕ} (hu : u * u = 1) (hv : v * v = 1)
    (hw : (u * v) ^ (2 * m) = 1) (hx : x = (u * v) ^ m) : u * x = x * u ∧ v * x = x * v := by
  have hxx : x⁻¹ = x := by
    rw [hx]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, ← two_mul]
    exact hw
  obtain ⟨h1, h2⟩ := a6_invert_prod hu hv
  have key : ∀ y : G, y * y = 1 → y * (u * v) * y = (u * v)⁻¹ → y * x = x * y := by
    intro y hy hyw
    have h := a6_invol_mul_pow hy hyw m
    rw [← hx, hxx] at h
    calc y * x = y * x * y * y := by rw [mul_assoc _ y y, hy, mul_one]
      _ = x * y := by rw [h]
  exact ⟨key u hu h1, key v hv h2⟩

private theorem a6_dihedral_even {u v x : G} {m j : ℕ} (hu : u * u = 1) (hv : v * v = 1)
    (hm : m = 2 * j) (hx : x = (u * v) ^ m) : IsConj u (u * x) ∧ IsConj v (v * x) := by
  obtain ⟨h1, h2⟩ := a6_invert_prod hu hv
  have hc1 := a6_conj_pow hu h1 j
  have hc2 := a6_conj_pow hv h2 j
  rw [← hm, ← hx] at hc1 hc2
  refine ⟨isConj_iff.mpr ⟨((u * v) ^ j)⁻¹, ?_⟩, isConj_iff.mpr ⟨((u * v) ^ j)⁻¹, ?_⟩⟩
  · rw [inv_inv]; exact hc1
  · rw [inv_inv]; exact hc2

private theorem a6_dihedral_odd {u v x : G} {m j : ℕ} (hu : u * u = 1) (hv : v * v = 1)
    (hxx : x * x = 1) (hm : m = 2 * j + 1) (hx : x = (u * v) ^ m) :
    IsConj u (v * x) ∧ IsConj (u * x) v := by
  obtain ⟨h1, h2⟩ := a6_invert_prod hu hv
  have hc1 := a6_conj_pow hu h1 (j + 1)
  have e1 : u * (u * v) ^ (2 * (j + 1)) = v * x := by
    have : (u * v) ^ (2 * (j + 1)) = (u * v) * x := by
      rw [hx, hm, ← pow_succ']
      congr 1
    rw [this, ← mul_assoc, ← mul_assoc, hu, one_mul]
  rw [e1] at hc1
  have hcomm : x * (u * v) ^ (j + 1) = (u * v) ^ (j + 1) * x := by
    rw [hx]; exact (Commute.pow_pow_self (u * v) m (j + 1)).eq.symm ▸ rfl
  generalize (u * v) ^ (j + 1) = g at hc1 hcomm
  refine ⟨isConj_iff.mpr ⟨g⁻¹, ?_⟩, isConj_iff.mpr ⟨g⁻¹, ?_⟩⟩
  · rw [inv_inv]; exact hc1
  · rw [inv_inv]
    calc g⁻¹ * (u * x) * g = g⁻¹ * u * (x * g) := by simp only [mul_assoc]
      _ = g⁻¹ * u * (g * x) := by rw [hcomm]
      _ = (g⁻¹ * u * g) * x := by simp only [mul_assoc]
      _ = (v * x) * x := by rw [hc1]
      _ = v := by rw [mul_assoc, hxx, mul_one]

end A6Dihedral

section A6Pairs

variable {G : Type} [Group G]

private theorem a6_invol_of_mem_conjClass {x y : G} (hx1 : x ≠ 1) (hx2 : x * x = 1)
    (hy : y ∈ conjClass x) : y ≠ 1 ∧ y * y = 1 := by
  obtain ⟨g, rfl⟩ := hy
  refine ⟨fun h => hx1 ?_, ?_⟩
  · calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hx2]; group

private theorem a6_mem_z_invol {z t : G} (h : HasTwoInvolutionClasses G z t) {u : G}
    (hu : u ∈ conjClass z) : u ≠ 1 ∧ u * u = 1 :=
  a6_invol_of_mem_conjClass h.z_inv.1 (by rw [← pow_two]; exact h.z_inv.2) hu

private theorem a6_mem_t_invol {z t : G} (h : HasTwoInvolutionClasses G z t) {u : G}
    (hu : u ∈ conjClass t) : u ≠ 1 ∧ u * u = 1 :=
  a6_invol_of_mem_conjClass h.t_inv.1 (by rw [← pow_two]; exact h.t_inv.2) hu

private theorem a6_not_isConj {z t : G} (h : HasTwoInvolutionClasses G z t) {a b : G}
    (ha : a ∈ conjClass z) (hb : b ∈ conjClass t) : ¬ IsConj a b := by
  intro hab
  apply h.distinct
  rw [a6_mem_conjClass_iff]
  exact (a6_mem_conjClass_iff.mp ha).trans (hab.trans (a6_mem_conjClass_iff.mp hb).symm)

private theorem a6_swap {z t : G} (h : HasTwoInvolutionClasses G z t) : HasTwoInvolutionClasses
    G t z where
  z_inv := h.t_inv
  t_inv := h.z_inv
  distinct := fun hz => h.distinct (a6_mem_conjClass_iff.mpr (a6_mem_conjClass_iff.mp hz).symm)
  all := fun x hx hx2 => (h.all x hx hx2).symm

private theorem a6_pair_even [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t) {u v : G}
    (hu : u ∈ conjClass z) (hv : v ∈ conjClass t) :
    ∃ m : ℕ, 0 < m ∧ orderOf (u * v) = 2 * m := by
  obtain ⟨hu1, hu2⟩ := a6_mem_z_invol h hu
  obtain ⟨hv1, hv2⟩ := a6_mem_t_invol h hv
  have hn : 0 < orderOf (u * v) := orderOf_pos _
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (orderOf (u * v))
  · exact ⟨k, by omega, hk⟩
  · exfalso
    obtain ⟨h1, h2⟩ := a6_invert_prod hu2 hv2
    have hc := a6_conj_pow hu2 h1 (k + 1)
    have hw : (u * v) ^ (2 * (k + 1)) = u * v := by
      rw [show 2 * (k + 1) = orderOf (u * v) + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
    rw [hw] at hc
    have : IsConj u v := isConj_iff.mpr ⟨((u * v) ^ (k + 1))⁻¹, by
      rw [inv_inv, hc, ← mul_assoc, hu2, one_mul]⟩
    exact a6_not_isConj h hu hv this

private theorem a6_pair_facts [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t) {u v x :
    G} {i : ℕ}
    (hi : i = 1 ∨ i = 2) (hp : (u, v) ∈ pairSetI z t x i) (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    u * x = x * u ∧ v * x = x * v ∧ ((u * x ∈ conjClass u) ↔ i = 1) ∧
      ((v * x ∈ conjClass v) ↔ i = 1) := by
  obtain ⟨⟨hu, hv, hxw⟩, hord⟩ := hp
  obtain ⟨m, hm0, hord2, hxm⟩ := a6_involution_in_zpowers hx1 hx2 hxw
  obtain ⟨hu1, hu2⟩ := a6_mem_z_invol h hu
  obtain ⟨hv1, hv2⟩ := a6_mem_t_invol h hv
  have hw : (u * v) ^ (2 * m) = 1 := by rw [← hord2]; exact pow_orderOf_eq_one _
  obtain ⟨hc1, hc2⟩ := a6_comm_pow hu2 hv2 hw hxm
  refine ⟨hc1, hc2, ?_⟩
  simp only at hord
  rcases hi with rfl | rfl
  · obtain ⟨j, hj⟩ : ∃ j, m = 2 * j := ⟨m / 2, by rw [hord2] at hord; simp at hord; omega⟩
    obtain ⟨c1, c2⟩ := a6_dihedral_even hu2 hv2 hj hxm
    exact ⟨iff_of_true (a6_mem_conjClass_iff.mpr c1) rfl,
      iff_of_true (a6_mem_conjClass_iff.mpr c2) rfl⟩
  · obtain ⟨j, hj⟩ : ∃ j, m = 2 * j + 1 :=
      ⟨m / 2, by rw [hord2] at hord; simp at hord; omega⟩
    obtain ⟨c1, c2⟩ := a6_dihedral_odd hu2 hv2 hx2 hj hxm
    refine ⟨iff_of_false ?_ (by norm_num), iff_of_false ?_ (by norm_num)⟩
    · intro hux
      exact a6_not_isConj h hu hv ((a6_mem_conjClass_iff.mp hux).trans c2)
    · intro hvx
      exact a6_not_isConj h hu hv (c1.trans (a6_mem_conjClass_iff.mp hvx).symm)

private theorem a6_aCount_split [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t) {x : G}
    (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    aCount z t x = aiCount z t x 1 + aiCount z t x 2 := by
  have hU : pairSet z t x = pairSetI z t x 1 ∪ pairSetI z t x 2 := by
    ext ⟨u, v⟩
    constructor
    · intro hp
      obtain ⟨hu, hv, hxw⟩ := hp
      obtain ⟨m, hm0, hord⟩ := a6_pair_even h hu hv
      have hord' : orderOf (u * v) = 2 * m := hord
      rcases Nat.even_or_odd' m with ⟨j, hj | hj⟩
      · left
        refine ⟨⟨hu, hv, hxw⟩, ?_⟩
        show orderOf (u * v) % 4 = (if (1 : ℕ) = 1 then 0 else 2)
        rw [if_pos rfl]; omega
      · right
        refine ⟨⟨hu, hv, hxw⟩, ?_⟩
        show orderOf (u * v) % 4 = (if (2 : ℕ) = 1 then 0 else 2)
        rw [if_neg (by norm_num)]; omega
    · rintro (hp | hp)
      · exact hp.1
      · exact hp.1
  have hD : Disjoint (pairSetI z t x 1) (pairSetI z t x 2) := by
    rw [Set.disjoint_left]
    rintro ⟨u, v⟩ h1 h2
    have e1 : orderOf (u * v) % 4 = (if (1 : ℕ) = 1 then 0 else 2) := h1.2
    have e2 : orderOf (u * v) % 4 = (if (2 : ℕ) = 1 then 0 else 2) := h2.2
    rw [if_pos rfl] at e1
    rw [if_neg (by norm_num)] at e2
    omega
  unfold aCount aiCount
  rw [hU, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Set.ncard_union_eq hD (Set.toFinite _) (Set.toFinite _)]

private theorem a6_mem_bc {x a b : G} {i : ℕ} (ha : a ∈ conjClass x) (hb1 : b ≠ 1) (hb2 : b * b = 1)
    (hbx : b ∉ conjClass x) (hax : a * x = x * a) (hbx' : b * x = x * b)
    (hai : (a * x ∈ conjClass a) ↔ i = 1) (hbi : (b * x ∈ conjClass b) ↔ i = 1) :
    a ∈ bSet x i ∧ b ∈ cSet x i := by
  refine ⟨⟨ha, ?_, hai⟩, hb1, by rw [pow_two]; exact hb2, hbx, ?_, hbi⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hax.symm
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hbx'.symm

private theorem a6_ai_le [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t) {x : G}
    (hx1 : x ≠ 1) (hx2 : x * x = 1) {i : ℕ} (hi : i = 1 ∨ i = 2) :
    aiCount z t x i ≤ bCount x i * cCount x i := by
  unfold aiCount bCount cCount
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← Set.ncard_prod]
  by_cases hxz : x ∈ conjClass z
  · refine Set.ncard_le_ncard_of_injOn id ?_ Function.injective_id.injOn (Set.toFinite _)
    rintro ⟨u, v⟩ hp
    obtain ⟨hc1, hc2, hi1, hi2⟩ := a6_pair_facts h hi hp hx1 hx2
    obtain ⟨⟨hu, hv, _⟩, _⟩ := hp
    obtain ⟨hv1, hv2⟩ := a6_mem_t_invol h hv
    have hux : u ∈ conjClass x :=
      a6_mem_conjClass_iff.mpr
        ((a6_mem_conjClass_iff.mp hxz).symm.trans (a6_mem_conjClass_iff.mp hu))
    have hvx : v ∉ conjClass x := fun hvx =>
      a6_not_isConj h hxz hv (a6_mem_conjClass_iff.mp hvx)
    exact a6_mem_bc hux hv1 hv2 hvx hc1 hc2 hi1 hi2
  · have hxt : x ∈ conjClass t := by
      rcases h.all x hx1 (by rw [pow_two]; exact hx2) with h' | h'
      · exact absurd h' hxz
      · exact h'
    refine Set.ncard_le_ncard_of_injOn Prod.swap ?_ Prod.swap_injective.injOn (Set.toFinite _)
    rintro ⟨u, v⟩ hp
    obtain ⟨hc1, hc2, hi1, hi2⟩ := a6_pair_facts h hi hp hx1 hx2
    obtain ⟨⟨hu, hv, _⟩, _⟩ := hp
    obtain ⟨hu1, hu2⟩ := a6_mem_z_invol h hu
    have hvx : v ∈ conjClass x :=
      a6_mem_conjClass_iff.mpr
        ((a6_mem_conjClass_iff.mp hxt).symm.trans (a6_mem_conjClass_iff.mp hv))
    have hux : u ∉ conjClass x := fun hux =>
      a6_not_isConj h hu hxt (a6_mem_conjClass_iff.mp hux).symm
    exact a6_mem_bc hvx hu1 hu2 hux hc2 hc1 hi2 hi1

end A6Pairs

section A6Count

variable {G : Type} [Group G]

private theorem a6_natCard_set {α : Type} [Fintype α] (S : Set α) [DecidablePred (· ∈ S)] :
    Nat.card S = (Finset.univ.filter (· ∈ S)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private theorem a6_zpowers_conj_iff' (g w x : G) :
    x ∈ Subgroup.zpowers (g * w * g⁻¹) ↔ g⁻¹ * x * g ∈ Subgroup.zpowers w := by
  simpa using a6_zpowers_conj_iff g⁻¹ w x

private theorem a6_aCount_conj {z t : G} (g x : G) : aCount z t (g⁻¹ * x * g) = aCount z t x := by
  unfold aCount
  refine Nat.card_congr (Equiv.subtypeEquiv
    { toFun := fun p => (g * p.1 * g⁻¹, g * p.2 * g⁻¹)
      invFun := fun p => (g⁻¹ * p.1 * g, g⁻¹ * p.2 * g)
      left_inv := fun p => by simp [mul_assoc]
      right_inv := fun p => by simp [mul_assoc] } ?_)
  rintro ⟨u, v⟩
  show (u ∈ conjClass z ∧ v ∈ conjClass t ∧ g⁻¹ * x * g ∈ Subgroup.zpowers (u * v)) ↔
    (g * u * g⁻¹ ∈ conjClass z ∧ g * v * g⁻¹ ∈ conjClass t ∧
      x ∈ Subgroup.zpowers (g * u * g⁻¹ * (g * v * g⁻¹)))
  rw [a6_conj_mem_conjClass_iff, a6_conj_mem_conjClass_iff]
  have e : g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
  rw [e, a6_zpowers_conj_iff']

private theorem a6_aCount_eq_of_mem {z t c x : G} (hx : x ∈ conjClass c) :
    aCount z t x = aCount z t c := by
  obtain ⟨g, rfl⟩ := hx
  exact a6_aCount_conj g c

private theorem a6_invo_spec [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t) {u v : G}
    (hu : u ∈ conjClass z) (hv : v ∈ conjClass t) :
    (u * v) ^ (orderOf (u * v) / 2) ≠ 1 ∧
      (u * v) ^ (orderOf (u * v) / 2) * (u * v) ^ (orderOf (u * v) / 2) = 1 := by
  obtain ⟨m, hm0, hord⟩ := a6_pair_even h hu hv
  have : orderOf (u * v) / 2 = m := by omega
  rw [this]
  refine ⟨?_, ?_⟩
  · exact pow_ne_one_of_lt_orderOf hm0.ne' (by omega)
  · rw [← pow_add, ← two_mul, ← hord, pow_orderOf_eq_one]

private theorem a6_arith {N Z T Cz Ct a_z a_t : ℕ} (hZ : Z * Cz = N) (hT : T * Ct = N) (hZpos :
    0 < Z)
    (hTpos : 0 < T) (hsum : Z * T = Z * a_z + T * a_t) : N = Cz * a_t + Ct * a_z := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hZpos hTpos)
  calc Z * T * N = N * (Z * T) := by ring
    _ = N * (Z * a_z + T * a_t) := by rw [hsum]
    _ = (Z * Cz) * (T * a_t) + (T * Ct) * (Z * a_z) := by rw [hZ, hT]; ring
    _ = Z * T * (Cz * a_t + Ct * a_z) := by ring

private theorem a6_thompson [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t) :
    Nat.card G = Nat.card (Subgroup.centralizer ({z} : Set G)) * aCount z t t +
      Nat.card (Subgroup.centralizer ({t} : Set G)) * aCount z t z := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hZc : Nat.card (conjClass z) = (Finset.univ.filter (· ∈ conjClass z)).card :=
    a6_natCard_set _
  have hTc : Nat.card (conjClass t) = (Finset.univ.filter (· ∈ conjClass t)).card :=
    a6_natCard_set _
  have hZ := a6_card_class_mul_card_centralizer z
  have hT := a6_card_class_mul_card_centralizer t
  rw [hZc] at hZ
  rw [hTc] at hT
  generalize hZs : (Finset.univ.filter (· ∈ conjClass z)) = Zs at hZ
  generalize hTs : (Finset.univ.filter (· ∈ conjClass t)) = Ts at hT
  have hmemZ : ∀ a, a ∈ Zs ↔ a ∈ conjClass z := by
    intro a; rw [← hZs]; simp
  have hmemT : ∀ a, a ∈ Ts ↔ a ∈ conjClass t := by
    intro a; rw [← hTs]; simp
  let invo : G × G → G := fun p => (p.1 * p.2) ^ (orderOf (p.1 * p.2) / 2)
  have hmaps : ∀ p ∈ Zs ×ˢ Ts, invo p ∈ Zs ∪ Ts := by
    intro p hp
    rw [Finset.mem_product, hmemZ, hmemT] at hp
    obtain ⟨hne, hsq⟩ := a6_invo_spec h hp.1 hp.2
    rw [Finset.mem_union, hmemZ, hmemT]
    exact h.all _ hne (by rw [pow_two]; exact hsq)
  have hfib : (Zs ×ˢ Ts).card =
      ∑ x ∈ Zs ∪ Ts, ((Zs ×ˢ Ts).filter (fun p => invo p = x)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p hp =>
      Finset.mem_coe.mpr (hmaps p (Finset.mem_coe.mp hp)))
  have hfiber : ∀ x ∈ Zs ∪ Ts, ((Zs ×ˢ Ts).filter (fun p => invo p = x)).card = aCount z t x := by
    intro x hx
    have hxinv : x ≠ 1 ∧ x * x = 1 := by
      rw [Finset.mem_union, hmemZ, hmemT] at hx
      rcases hx with hx | hx
      · exact a6_mem_z_invol h hx
      · exact a6_mem_t_invol h hx
    unfold aCount
    rw [a6_natCard_set]
    congr 1
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_product, hmemZ, hmemT, Finset.mem_univ, true_and]
    change ((u ∈ conjClass z ∧ v ∈ conjClass t) ∧ (u * v) ^ (orderOf (u * v) / 2) = x) ↔
      (u ∈ conjClass z ∧ v ∈ conjClass t ∧ x ∈ Subgroup.zpowers (u * v))
    constructor
    · rintro ⟨⟨hu, hv⟩, hx'⟩
      exact ⟨hu, hv, hx' ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _⟩
    · rintro ⟨hu, hv, hxw⟩
      obtain ⟨m, hm0, hord, hxm⟩ := a6_involution_in_zpowers hxinv.1 hxinv.2 hxw
      refine ⟨⟨hu, hv⟩, ?_⟩
      rw [hord, hxm]
      congr 1
      omega
  have hsum : (Zs ×ˢ Ts).card = ∑ x ∈ Zs ∪ Ts, aCount z t x := by
    rw [hfib]; exact Finset.sum_congr rfl hfiber
  have hdisj : Disjoint Zs Ts := by
    rw [Finset.disjoint_left]
    intro a haz hat
    rw [hmemZ] at haz
    rw [hmemT] at hat
    exact a6_not_isConj h haz (a6_self_mem_conjClass t) (a6_mem_conjClass_iff.mp hat).symm
  rw [Finset.sum_union hdisj] at hsum
  have hz : ∑ x ∈ Zs, aCount z t x = Zs.card * aCount z t z := by
    rw [Finset.sum_congr rfl (fun x hx =>
      a6_aCount_eq_of_mem (z := z) (t := t) (c := z) ((hmemZ x).mp hx))]
    rw [Finset.sum_const, smul_eq_mul]
  have ht : ∑ x ∈ Ts, aCount z t x = Ts.card * aCount z t t := by
    rw [Finset.sum_congr rfl (fun x hx =>
      a6_aCount_eq_of_mem (z := z) (t := t) (c := t) ((hmemT x).mp hx))]
    rw [Finset.sum_const, smul_eq_mul]
  rw [hz, ht, Finset.card_product] at hsum
  have hZpos : 0 < Zs.card := Finset.card_pos.mpr ⟨z, (hmemZ z).mpr (a6_self_mem_conjClass z)⟩
  have hTpos : 0 < Ts.card := Finset.card_pos.mpr ⟨t, (hmemT t).mpr (a6_self_mem_conjClass t)⟩
  exact a6_arith hZ hT hZpos hTpos hsum

end A6Count

section A6C

variable {G : Type} [Group G]

private theorem a6_natCard_subtype {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {a // p a} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private theorem a6_mem_cSet_iff {z t : G} (h : HasTwoInvolutionClasses G z t) {u : G} {i : ℕ} :
    u ∈ cSet t i ↔ u ∈ conjClass z ∧ u * t = t * u ∧ ((u * t ∈ conjClass u) ↔ i = 1) := by
  constructor
  · rintro ⟨hu1, hu2, hut, hc, hi⟩
    refine ⟨?_, ?_, hi⟩
    · rcases h.all u hu1 hu2 with h' | h'
      · exact h'
      · exact absurd h' hut
    · exact ((Subgroup.mem_centralizer_iff.mp hc) t (Set.mem_singleton t)).symm
  · rintro ⟨hu, hc, hi⟩
    obtain ⟨hu1, hu2⟩ := a6_mem_z_invol h hu
    refine ⟨hu1, by rw [pow_two]; exact hu2, ?_, ?_, hi⟩
    · intro hut
      exact a6_not_isConj h hu (a6_self_mem_conjClass t) (a6_mem_conjClass_iff.mp hut).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hc.symm

private theorem a6_card_fiber_conj (z : G) (i : ℕ) (g w : G) :
    Nat.card {u // u ∈ conjClass z ∧ u * (g * w * g⁻¹) = (g * w * g⁻¹) * u ∧
        ((u * (g * w * g⁻¹) ∈ conjClass u) ↔ i = 1)} =
      Nat.card {u // u ∈ conjClass z ∧ u * w = w * u ∧ ((u * w ∈ conjClass u) ↔ i = 1)} := by
  refine Nat.card_congr (Equiv.subtypeEquiv
    { toFun := fun u => g⁻¹ * u * g
      invFun := fun u => g * u * g⁻¹
      left_inv := fun u => by group
      right_inv := fun u => by group } ?_)
  intro u
  show (u ∈ conjClass z ∧ u * (g * w * g⁻¹) = (g * w * g⁻¹) * u ∧
      ((u * (g * w * g⁻¹) ∈ conjClass u) ↔ i = 1)) ↔
    (g⁻¹ * u * g ∈ conjClass z ∧ g⁻¹ * u * g * w = w * (g⁻¹ * u * g) ∧
      ((g⁻¹ * u * g * w ∈ conjClass (g⁻¹ * u * g)) ↔ i = 1))
  have h1 : g⁻¹ * u * g ∈ conjClass z ↔ u ∈ conjClass z := by
    simpa using a6_conj_mem_conjClass_iff (x := z) (y := u) g⁻¹
  have h2 : u * (g * w * g⁻¹) = (g * w * g⁻¹) * u ↔ g⁻¹ * u * g * w = w * (g⁻¹ * u * g) := by
    constructor
    · intro hc
      calc g⁻¹ * u * g * w = g⁻¹ * (u * (g * w * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * w * g⁻¹) * u) * g := by rw [hc]
        _ = w * (g⁻¹ * u * g) := by group
    · intro hc
      calc u * (g * w * g⁻¹) = g * (g⁻¹ * u * g * w) * g⁻¹ := by group
        _ = g * (w * (g⁻¹ * u * g)) * g⁻¹ := by rw [hc]
        _ = (g * w * g⁻¹) * u := by group
  have h3 : u * (g * w * g⁻¹) ∈ conjClass u ↔ g⁻¹ * u * g * w ∈ conjClass (g⁻¹ * u * g) := by
    rw [a6_mem_conjClass_iff, a6_mem_conjClass_iff]
    have h4 := a6_isConj_conj_iff g⁻¹ u (u * (g * w * g⁻¹))
    rw [inv_inv] at h4
    have e : g⁻¹ * (u * (g * w * g⁻¹)) * g = g⁻¹ * u * g * w := by group
    rw [e] at h4
    exact h4.symm
  rw [h1, h2, h3]

private theorem a6_card_fiber {z t : G} (h : HasTwoInvolutionClasses G z t) {v : G} (hv : v ∈
    conjClass t)
    (i : ℕ) :
    Nat.card {u // u ∈ conjClass z ∧ u * v = v * u ∧ ((u * v ∈ conjClass u) ↔ i = 1)} =
      cCount t i := by
  obtain ⟨g, rfl⟩ := hv
  have h1 := a6_card_fiber_conj z i g⁻¹ t
  rw [inv_inv] at h1
  rw [h1]
  unfold cCount
  exact Nat.card_congr (Equiv.subtypeEquivRight fun u => (a6_mem_cSet_iff h).symm)

private theorem a6_cond_swap {z t : G} (h : HasTwoInvolutionClasses G z t) {u v : G}
    (hu : u ∈ conjClass z) (hv : v ∈ conjClass t) (hc : u * v = v * u) {i : ℕ}
    (hi : i = 1 ∨ i = 2) :
    ((u * v ∈ conjClass u) ↔ i = 1) ↔ ((v * u ∈ conjClass v) ↔ 3 - i = 1) := by
  obtain ⟨hu1, hu2⟩ := a6_mem_z_invol h hu
  obtain ⟨hv1, hv2⟩ := a6_mem_t_invol h hv
  have hw1 : u * v ≠ 1 := by
    intro h1
    have h2 : v = u⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [inv_eq_of_mul_eq_one_right hu2] at h2
    exact a6_not_isConj h hu hv (h2 ▸ IsConj.refl u)
  have hw2 : u * v * (u * v) = 1 := by
    calc u * v * (u * v) = u * (v * u) * v := by simp only [mul_assoc]
      _ = u * (u * v) * v := by rw [← hc]
      _ = (u * u) * (v * v) := by simp only [mul_assoc]
      _ = 1 := by rw [hu2, hv2, mul_one]
  have key : (u * v ∈ conjClass u) ↔ ¬ (v * u ∈ conjClass v) := by
    rw [a6_conjClass_eq_of_mem hu, a6_conjClass_eq_of_mem hv, ← hc]
    constructor
    · intro hz ht
      exact h.distinct (a6_mem_conjClass_iff.mpr
        ((a6_mem_conjClass_iff.mp hz).trans (a6_mem_conjClass_iff.mp ht).symm))
    · intro hnt
      rcases h.all _ hw1 (by rw [pow_two]; exact hw2) with h' | h'
      · exact h'
      · exact absurd h' hnt
  rcases hi with rfl | rfl
  · simp [key]
  · simp [key]

private theorem a6_arith2 {N Z T Cz Ct m n : ℕ} (hZ : Z * Cz = N) (hT : T * Ct = N) (hN : 0 < N)
    (hZm : Z * m = T * n) : n * Cz = Ct * m := by
  apply Nat.eq_of_mul_eq_mul_left hN
  calc N * (n * Cz) = (T * Ct) * (n * Cz) := by rw [hT]
    _ = (T * n) * (Ct * Cz) := by ring
    _ = (Z * m) * (Ct * Cz) := by rw [hZm]
    _ = (Z * Cz) * (Ct * m) := by ring
    _ = N * (Ct * m) := by rw [hZ]

private theorem a6_c_mul [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t) {i : ℕ}
    (hi : i = 1 ∨ i = 2) :
    cCount t i * Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Nat.card (Subgroup.centralizer ({t} : Set G)) * cCount z (3 - i) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hZc : Nat.card (conjClass z) = (Finset.univ.filter (· ∈ conjClass z)).card :=
    a6_natCard_set _
  have hTc : Nat.card (conjClass t) = (Finset.univ.filter (· ∈ conjClass t)).card :=
    a6_natCard_set _
  have hZ := a6_card_class_mul_card_centralizer z
  have hT := a6_card_class_mul_card_centralizer t
  rw [hZc] at hZ
  rw [hTc] at hT
  generalize hZs : (Finset.univ.filter (· ∈ conjClass z)) = Zs at hZ
  generalize hTs : (Finset.univ.filter (· ∈ conjClass t)) = Ts at hT
  have hmemZ : ∀ a, a ∈ Zs ↔ a ∈ conjClass z := by
    intro a; rw [← hZs]; simp
  have hmemT : ∀ a, a ∈ Ts ↔ a ∈ conjClass t := by
    intro a; rw [← hTs]; simp
  let r : G → G → Prop := fun u v => u * v = v * u ∧ ((u * v ∈ conjClass u) ↔ i = 1)
  have hm : ∀ u ∈ Zs, (Ts.bipartiteAbove r u).card = cCount z (3 - i) := by
    intro u hu
    rw [hmemZ] at hu
    rw [← a6_card_fiber (a6_swap h) hu (3 - i), a6_natCard_subtype]
    congr 1
    ext v
    simp only [Finset.mem_bipartiteAbove, hmemT, Finset.mem_filter, Finset.mem_univ, true_and, r]
    constructor
    · rintro ⟨hv, hc, hcond⟩
      exact ⟨hv, hc.symm, (a6_cond_swap h hu hv hc hi).mp hcond⟩
    · rintro ⟨hv, hc, hcond⟩
      exact ⟨hv, hc.symm, (a6_cond_swap h hu hv hc.symm hi).mpr hcond⟩
  have hn : ∀ v ∈ Ts, (Zs.bipartiteBelow r v).card = cCount t i := by
    intro v hv
    rw [hmemT] at hv
    rw [← a6_card_fiber h hv i, a6_natCard_subtype]
    congr 1
    ext u
    simp only [Finset.mem_bipartiteBelow, hmemZ, Finset.mem_filter, Finset.mem_univ, true_and, r]
  have hcount := Finset.card_mul_eq_card_mul r hm hn
  have hN : 0 < Nat.card G := Nat.card_pos
  exact a6_arith2 hZ hT hN hcount

private theorem a6_c_rat [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t) {i : ℕ}
    (hi : i = 1 ∨ i = 2) :
    (cCount t i : ℚ) = (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℚ) * cCount z (3 - i) /
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  have hpos : (0 : ℚ) < Nat.card (Subgroup.centralizer ({z} : Set G)) := by
    exact_mod_cast Nat.card_pos
  rw [eq_div_iff hpos.ne']
  exact_mod_cast a6_c_mul h hi

end A6C

section A6D

variable {G : Type} [Group G]

private theorem a6_index_le [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t) :
    (Subgroup.centralizer ({z} : Set G)).index ≤
      cCount t 1 * (bCount t 1 + bCount z 2) + cCount t 2 * (bCount t 2 + bCount z 1) := by
  have hz : z ≠ 1 ∧ z * z = 1 := ⟨h.z_inv.1, by rw [← pow_two]; exact h.z_inv.2⟩
  have ht : t ≠ 1 ∧ t * t = 1 := ⟨h.t_inv.1, by rw [← pow_two]; exact h.t_inv.2⟩
  have h1 := a6_thompson h
  have hidx : Nat.card (Subgroup.centralizer ({z} : Set G)) *
      (Subgroup.centralizer ({z} : Set G)).index = Nat.card G := Subgroup.card_mul_index _
  have haz := a6_aCount_split h hz.1 hz.2
  have hat := a6_aCount_split h ht.1 ht.2
  have b1t := a6_ai_le h ht.1 ht.2 (i := 1) (Or.inl rfl)
  have b2t := a6_ai_le h ht.1 ht.2 (i := 2) (Or.inr rfl)
  have b1z := a6_ai_le h hz.1 hz.2 (i := 1) (Or.inl rfl)
  have b2z := a6_ai_le h hz.1 hz.2 (i := 2) (Or.inr rfl)
  have c1 : cCount t 1 * Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Nat.card (Subgroup.centralizer ({t} : Set G)) * cCount z 2 := a6_c_mul h (i := 1) (Or.inl rfl)
  have c2 : cCount t 2 * Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Nat.card (Subgroup.centralizer ({t} : Set G)) * cCount z 1 := a6_c_mul h (i := 2) (Or.inr rfl)
  have hCz : 0 < Nat.card (Subgroup.centralizer ({z} : Set G)) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hCz
  rw [hidx, h1, hat, haz]
  have e1 : bCount z 1 * (Nat.card (Subgroup.centralizer ({t} : Set G)) * cCount z 1) =
      bCount z 1 * (cCount t 2 * Nat.card (Subgroup.centralizer ({z} : Set G))) := by rw [c2]
  have e2 : bCount z 2 * (Nat.card (Subgroup.centralizer ({t} : Set G)) * cCount z 2) =
      bCount z 2 * (cCount t 1 * Nat.card (Subgroup.centralizer ({z} : Set G))) := by rw [c1]
  calc Nat.card (Subgroup.centralizer ({z} : Set G)) * (aiCount z t t 1 + aiCount z t t 2) +
        Nat.card (Subgroup.centralizer ({t} : Set G)) * (aiCount z t z 1 + aiCount z t z 2)
      ≤ Nat.card (Subgroup.centralizer ({z} : Set G)) *
          (bCount t 1 * cCount t 1 + bCount t 2 * cCount t 2) +
        Nat.card (Subgroup.centralizer ({t} : Set G)) *
          (bCount z 1 * cCount z 1 + bCount z 2 * cCount z 2) := by
        gcongr
    _ = Nat.card (Subgroup.centralizer ({z} : Set G)) *
          (bCount t 1 * cCount t 1 + bCount t 2 * cCount t 2) +
        (bCount z 1 * (Nat.card (Subgroup.centralizer ({t} : Set G)) * cCount z 1) +
          bCount z 2 * (Nat.card (Subgroup.centralizer ({t} : Set G)) * cCount z 2)) := by ring
    _ = Nat.card (Subgroup.centralizer ({z} : Set G)) *
          (bCount t 1 * cCount t 1 + bCount t 2 * cCount t 2) +
        (bCount z 1 * (cCount t 2 * Nat.card (Subgroup.centralizer ({z} : Set G))) +
          bCount z 2 * (cCount t 1 * Nat.card (Subgroup.centralizer ({z} : Set G)))) := by
        rw [e1, e2]
    _ = Nat.card (Subgroup.centralizer ({z} : Set G)) *
          (cCount t 1 * (bCount t 1 + bCount z 2) + cCount t 2 * (bCount t 2 + bCount z 1)) := by
        ring

private theorem a6_cCount_one [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t)
    (hstar : ∀ u v : G, u ∈ conjClass z → v ∈ conjClass z → u * v = v * u → u * v ≠ 1 →
      u * v ∈ conjClass z) : cCount t 1 = 0 := by
  unfold cCount
  have : cSet t 1 = ∅ := by
    ext u
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hu
    obtain ⟨huz, hut, hcond⟩ := (a6_mem_cSet_iff h).mp hu
    have hux : u * t ∈ conjClass u := hcond.mpr rfl
    rw [a6_conjClass_eq_of_mem huz] at hux
    obtain ⟨hu1, hu2⟩ := a6_mem_z_invol h huz
    have hcomm : u * (u * t) = (u * t) * u := by
      calc u * (u * t) = u * (t * u) := by rw [← hut]
        _ = u * t * u := by rw [mul_assoc]
    have hprod : u * (u * t) = t := by rw [← mul_assoc, hu2, one_mul]
    have hne : u * (u * t) ≠ 1 := by rw [hprod]; exact h.t_inv.1
    have := hstar u (u * t) huz hux hcomm hne
    rw [hprod] at this
    exact h.distinct this
  rw [this]
  simp

private theorem a6_cCount_two_le [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t) :
    cCount t 2 ≤
      Nat.card ↥(conjClass z ∩ (Subgroup.centralizer ({t} : Set G) : Set G) : Set G) := by
  unfold cCount
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  intro u hu
  exact ⟨((a6_mem_cSet_iff h).mp hu).1, hu.2.2.2.1⟩

private theorem a6_bCount_two_le [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t) :
    bCount t 2 ≤
      Nat.card ↥(conjClass z ∩ (Subgroup.centralizer ({t} : Set G) : Set G) : Set G) + 1 := by
  unfold bCount
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  calc (bSet t 2).ncard
      ≤ ((conjClass z ∩ (Subgroup.centralizer ({t} : Set G) : Set G)) ∪ ({1} : Set G)).ncard := by
        refine Set.ncard_le_ncard_of_injOn (fun u => u * t) ?_ ?_ (Set.toFinite _)
        · intro u hu
          obtain ⟨hut, hc, hcond⟩ := hu
          by_cases hu1 : u * t = 1
          · right
            exact hu1
          · left
            have hc' : t * u = u * t :=
              Subgroup.mem_centralizer_iff.mp hc t (Set.mem_singleton t)
            obtain ⟨hv1, hv2⟩ := a6_mem_t_invol h hut
            have ht2 : t * t = 1 := by rw [← pow_two]; exact h.t_inv.2
            have hsq : u * t * (u * t) = 1 := by
              calc u * t * (u * t) = u * (t * u) * t := by simp only [mul_assoc]
                _ = u * (u * t) * t := by rw [hc']
                _ = (u * u) * (t * t) := by simp only [mul_assoc]
                _ = 1 := by rw [hv2, ht2, mul_one]
            rcases h.all _ hu1 (by rw [pow_two]; exact hsq) with h' | h'
            · refine ⟨h', ?_⟩
              rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
              intro y hy
              rw [Set.mem_singleton_iff] at hy
              subst hy
              calc y * (u * y) = (y * u) * y := by rw [mul_assoc]
                _ = (u * y) * y := by rw [hc']
            · exfalso
              rw [a6_conjClass_eq_of_mem hut] at hcond
              have := hcond.mp h'
              omega
        · intro u _ u' _ huu
          exact mul_right_cancel huu
    _ ≤ (conjClass z ∩ (Subgroup.centralizer ({t} : Set G) : Set G)).ncard +
          ({1} : Set G).ncard := Set.ncard_union_le _ _
    _ = _ := by rw [Set.ncard_singleton]

private theorem a6_bCount_one_le [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t) :
    bCount z 1 + 1 ≤
      Nat.card ↥(conjClass z ∩ (Subgroup.centralizer ({z} : Set G) : Set G) : Set G) := by
  unfold bCount
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  have hzn : z ∉ bSet z 1 := by
    rintro ⟨_, _, hcond⟩
    have h1 : z * z ∈ conjClass z := hcond.mpr rfl
    have hzz : z * z = 1 := by rw [← pow_two]; exact h.z_inv.2
    rw [hzz] at h1
    exact (a6_mem_z_invol h h1).1 rfl
  calc (bSet z 1).ncard + 1 = (insert z (bSet z 1)).ncard :=
        (Set.ncard_insert_of_notMem hzn (Set.toFinite _)).symm
    _ ≤ _ := by
      apply Set.ncard_le_ncard _ (Set.toFinite _)
      intro u hu
      rcases hu with rfl | hu
      · refine ⟨a6_self_mem_conjClass u, ?_⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
      · exact ⟨hu.1, hu.2.1⟩

private theorem a6_index_le_five [Finite G] {z t : G} (h : HasTwoInvolutionClasses G z t)
    (hstar : ∀ u v : G, u ∈ conjClass z → v ∈ conjClass z → u * v = v * u → u * v ≠ 1 →
      u * v ∈ conjClass z) :
    (Subgroup.centralizer ({z} : Set G)).index ≤
      Nat.card ↥(conjClass z ∩ (Subgroup.centralizer ({t} : Set G) : Set G) : Set G) *
        (Nat.card ↥(conjClass z ∩ (Subgroup.centralizer ({t} : Set G) : Set G) : Set G) +
          Nat.card ↥(conjClass z ∩ (Subgroup.centralizer ({z} : Set G) : Set G) : Set G)) := by
  have h4 := a6_index_le h
  rw [a6_cCount_one h hstar, zero_mul, zero_add] at h4
  have hc2 := a6_cCount_two_le h
  have hb2 := a6_bCount_two_le h
  have hb1 := a6_bCount_one_le h
  exact h4.trans (Nat.mul_le_mul hc2 (by omega))

end A6D

end BurnsideA6

theorem as_A_6_1 : A_6_1 := by
  intro G _ _ z t h
  exact a6_thompson h

@[expose] def A_6_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G), HasTwoInvolutionClasses G z t →
    ∀ x : G, x ≠ 1 → x ^ 2 = 1 → ∀ i : ℕ, (i = 1 ∨ i = 2) →
      aiCount z t x i ≤ bCount x i * cCount x i

theorem as_A_6_2 : A_6_2 := by
  intro G _ _ z t h x hx1 hx2 i hi
  exact a6_ai_le h hx1 (by rw [← pow_two]; exact hx2) hi

@[expose] def A_6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G), HasTwoInvolutionClasses G z t →
    ∀ i : ℕ, (i = 1 ∨ i = 2) →
      (cCount t i : ℚ) = (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℚ) * cCount z (3 - i) /
        Nat.card (Subgroup.centralizer ({z} : Set G))

theorem as_A_6_3 : A_6_3 := by
  intro G _ _ z t h i hi
  exact a6_c_rat h hi

@[expose] def A_6_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G), HasTwoInvolutionClasses G z t →
    (Subgroup.centralizer ({z} : Set G)).index ≤
      cCount t 1 * (bCount t 1 + bCount z 2) + cCount t 2 * (bCount t 2 + bCount z 1)

theorem as_A_6_4 : A_6_4 := by
  intro G _ _ z t h
  exact a6_index_le h

@[expose] def A_6_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G), HasTwoInvolutionClasses G z t →
    (∀ u v : G, u ∈ conjClass z → v ∈ conjClass z → u * v = v * u → u * v ≠ 1 →
      u * v ∈ conjClass z) →
    (Subgroup.centralizer ({z} : Set G)).index ≤
      Nat.card (conjClass z ∩ (Subgroup.centralizer ({t} : Set G) : Set G) : Set G) *
        (Nat.card (conjClass z ∩ (Subgroup.centralizer ({t} : Set G) : Set G) : Set G) +
          Nat.card (conjClass z ∩ (Subgroup.centralizer ({z} : Set G) : Set G) : Set G))

theorem as_A_6_5 : A_6_5 := by
  intro G _ _ z t h hstar
  exact a6_index_le_five h hstar

end CFSG.ASVolI
