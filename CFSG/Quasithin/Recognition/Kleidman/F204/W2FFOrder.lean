module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.Kleidman.F204

open Subgroup


theorem card_modEq_fix_five {X : Type*} [Finite X] (σ : Equiv.Perm X) (hσ : σ ^ 5 = 1) :
    Nat.card X ≡ Nat.card {x : X // σ x = x} [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let H : Subgroup (Equiv.Perm X) := Subgroup.zpowers σ
  have hH : IsPGroup 5 H := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hm, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, hσ, one_zpow]
  have key := hH.card_modEq_card_fixedPoints X
  have hfix : Nat.card (MulAction.fixedPoints H X) = Nat.card {x : X // σ x = x} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun x => ?_
    constructor
    · intro hx
      have : σ ∈ H := Subgroup.mem_zpowers σ
      exact hx ⟨σ, this⟩
    · intro hx g
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
      show (g : Equiv.Perm X) x = x
      rw [← hm]
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx m
  rw [hfix] at key
  exact key

theorem four_dvd_of_two_pow_mod_five (d : ℕ) (h : 2 ^ d % 5 = 1) : 4 ∣ d := by
  have key : ∀ q r : ℕ, 2 ^ (4 * q + r) % 5 = 2 ^ r % 5 := by
    intro q r
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hd : 2 ^ (d % 4) % 5 = 1 := by
    have := key (d / 4) (d % 4)
    rw [Nat.div_add_mod] at this
    omega
  have hr : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hr0 : d % 4 = 0 := by
    interval_cases hm : d % 4 <;> first | rfl | (norm_num at hd)
  exact Nat.dvd_of_mod_eq_zero hr0

theorem sixteen_le_card_of_fix {W : Type*} [Group W] [Finite W] (hW : IsPGroup 2 W)
    (σ : Equiv.Perm W) (hσ5 : σ ^ 5 = 1) (hσ : σ ≠ 1) (C : Subgroup W)
    (hC : ∀ w, w ∈ C ↔ σ w = w) : 16 ≤ Nat.card W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := W)).mp hW
  have hdvd : Nat.card C ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.card_subgroup_dvd_card C
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hfixeq : Nat.card {x : W // σ x = x} = Nat.card C := by
    apply Nat.card_congr
    exact (Equiv.subtypeEquivRight fun w => (hC w).symm)
  have hcong : 2 ^ n ≡ 2 ^ k [MOD 5] := by
    have h := card_modEq_fix_five σ hσ5
    rw [hfixeq, hk, hn] at h
    exact h
  have hkle : k ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
    (by rw [← hk]; exact hdvd)
  have hkn : k < n := by
    by_contra hle
    have hkn' : k = n := by omega
    have hCtop : C = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hk, hn, hkn']
    apply hσ
    ext w
    have := (hC w).mp (by rw [hCtop]; exact Subgroup.mem_top w)
    simpa using this
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hmod : 2 ^ d % 5 = 1 := by
    have h1 : 2 ^ k * 2 ^ d ≡ 2 ^ k * 1 [MOD 5] := by
      rw [mul_one, ← pow_add]
      exact hcong
    have hcop : Nat.Coprime (2 ^ k) 5 := by
      apply Nat.Coprime.pow_left
      norm_num
    have h2 := Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hcop) h1
    exact h2
  have h4 : 4 ∣ d := four_dvd_of_two_pow_mod_five d hmod
  rw [hn]
  have hpow : 2 ^ 4 ≤ 2 ^ (k + d) := Nat.pow_le_pow_right (by norm_num) (by
    obtain ⟨c, rfl⟩ := h4
    omega)
  norm_num at hpow
  exact hpow


def centV {G : Type*} [Group G] {V L : Subgroup G} : Subgroup L where
  carrier := {l | ∀ v ∈ V, Commute (l : G) v}
  mul_mem' := by
    intro a b ha hb v hv
    exact (Commute.mul_left (ha v hv) (hb v hv))
  one_mem' := by
    intro v hv
    exact Commute.one_left v
  inv_mem' := by
    intro a ha v hv
    exact (ha v hv).inv_left

theorem centV_normal {G : Type*} [Group G] {V L : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) : (@centV G _ V L).Normal := by
  constructor
  intro n hn l v hv
  obtain ⟨w, hwdef⟩ : ∃ w : G, w = (l : G)⁻¹ * v * (l : G) := ⟨_, rfl⟩
  have hw : w ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (hLV (inv_mem l.2))) v
    rw [hwdef]
    simpa [inv_inv] using this.mp hv
  have hcomm : (n : G) * w = w * (n : G) := hn w hw
  have hv' : v = (l : G) * w * (l : G)⁻¹ := by rw [hwdef]; group
  show _ = _
  rw [hv']
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc (l : G) * (n : G) * (l : G)⁻¹ * ((l : G) * w * (l : G)⁻¹)
      = (l : G) * ((n : G) * w) * (l : G)⁻¹ := by group
    _ = (l : G) * (w * (n : G)) * (l : G)⁻¹ := by rw [hcomm]
    _ = ((l : G) * w * (l : G)⁻¹) * ((l : G) * (n : G) * (l : G)⁻¹) := by group

theorem exists_five_noncentral {G : Type*} [Group G] {V L : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (φ : L →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    (hnc : ∃ l : L, ∃ v ∈ V, ¬ Commute (l : G) v) :
    ∃ x : L, φ x ^ 5 = 1 ∧ φ x ≠ 1 ∧ ∃ v ∈ V, ¬ Commute (x : G) v := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hcyc : (finRotate 5 : Equiv.Perm (Fin 5)) ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  set y : alternatingGroup (Fin 5) := ⟨finRotate 5, hcyc⟩ with hy
  have hy5 : y ^ 5 = 1 := by
    apply Subtype.ext
    show (finRotate 5) ^ 5 = 1
    decide
  have hy1 : y ≠ 1 := by
    intro h
    have := congrArg Subtype.val h
    change finRotate 5 = 1 at this
    revert this
    decide
  obtain ⟨x0, hx0⟩ := hφ y
  refine ⟨x0, by rw [hx0]; exact hy5, by rw [hx0]; exact hy1, ?_⟩
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hx0c : x0 ∈ (@centV G _ V L) := fun v hv => hcon v hv
  have hM : (@centV G _ V L).map φ = ⊤ := by
    haveI : ((@centV G _ V L).map φ).Normal := (centV_normal hLV).map φ hφ
    refine (Subgroup.Normal.eq_bot_or_eq_top _).resolve_left ?_
    intro h
    have hmem : φ x0 ∈ (@centV G _ V L).map φ := mem_map_of_mem φ hx0c
    rw [h, mem_bot, hx0] at hmem
    exact hy1 hmem
  have hall : ∀ l : L, l ∈ (@centV G _ V L) := by
    intro l
    have hl : φ l ∈ (@centV G _ V L).map φ := by rw [hM]; exact mem_top _
    obtain ⟨n, hn, hφn⟩ := mem_map.mp hl
    have hk : φ (n⁻¹ * l) = 1 := by rw [map_mul, map_inv, hφn, inv_mul_cancel]
    have hkc := hker _ hk
    have hl' : (l : G) = (n : G) * ((n⁻¹ * l : L) : G) := by simp
    intro v hv
    rw [hl']
    exact Commute.mul_left (hn v hv) ((Subgroup.mem_centralizer_iff.mp hkc) v hv).symm
  obtain ⟨l0, v, hv, hnot⟩ := hnc
  exact hnot (hall l0 v hv)

def conjPerm {G : Type*} [Group G] {V : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) : Equiv.Perm V where
  toFun v := ⟨x * v * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx v).mp v.2⟩
  invFun w := ⟨x⁻¹ * w * x⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (inv_mem hx) w).mp w.2⟩
  left_inv v := Subtype.ext (by simp [mul_assoc])
  right_inv w := Subtype.ext (by simp [mul_assoc])

theorem conjPerm_pow_apply {G : Type*} [Group G] {V : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (n : ℕ) (v : V) :
    (((conjPerm hx) ^ n) v : G) = x ^ n * v * (x ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    change x * (((conjPerm hx) ^ k) v : G) * x⁻¹ = _
    rw [ih]
    group

theorem conjPerm_five {G : Type*} [Group G] {V : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (h5 : ∀ v ∈ V, Commute (x ^ 5) v) :
    (conjPerm hx) ^ 5 = 1 := by
  ext v
  rw [conjPerm_pow_apply, Equiv.Perm.one_apply]
  have hc := h5 v v.2
  change x ^ 5 * (v : G) * (x ^ 5)⁻¹ = v
  rw [hc]
  group

theorem sixteen_le_card_of_five {G : Type*} [Group G] [Finite G] {V : Subgroup G} {x : G}
    (hV2 : ∀ a ∈ V, a * a = 1) (hx : x ∈ Subgroup.normalizer (V : Set G))
    (h5 : ∀ v ∈ V, Commute (x ^ 5) v) (v0 : G) (hv0 : v0 ∈ V) (hnot : ¬ Commute x v0) :
    16 ≤ Nat.card V := by
  have hVp : IsPGroup 2 V := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext (by simpa using hV2 g.1 g.2)
  have hσ1 : conjPerm hx ≠ 1 := by
    intro h
    have h' : ((conjPerm hx ⟨v0, hv0⟩ : V) : G) = v0 := by rw [h]; rfl
    change x * v0 * x⁻¹ = v0 at h'
    apply hnot
    change x * v0 = v0 * x
    calc x * v0 = (x * v0 * x⁻¹) * x := by group
      _ = v0 * x := by rw [h']
  let C : Subgroup V := (Subgroup.centralizer ({x} : Set G)).subgroupOf V
  have hC : ∀ w : V, w ∈ C ↔ conjPerm hx w = w := by
    intro w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subtype.ext_iff]
    change _ ↔ x * (w : G) * x⁻¹ = w
    constructor
    · intro h
      rw [h x (Set.mem_singleton x)]
      group
    · intro h y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      calc y * (w : G) = (y * w * y⁻¹) * y := by group
        _ = w * y := by rw [h]
  exact sixteen_le_card_of_fix hVp (conjPerm hx) (conjPerm_five hx h5) hσ1 C hC

theorem sixteen_le_card_V {G : Type*} [Group G] [Finite G] {V L : Subgroup G}
    (hV2 : ∀ a ∈ V, a * a = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (φ : L →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    (hnc : ∃ l : L, ∃ v ∈ V, ¬ Commute (l : G) v) :
    16 ≤ Nat.card V := by
  obtain ⟨x, hx5, -, v0, hv0, hnot⟩ := exists_five_noncentral hLV φ hφ hker hnc
  have h5 : ∀ v ∈ V, Commute ((x : G) ^ 5) v := by
    intro v hv
    have h := (Subgroup.mem_centralizer_iff.mp (hker (x ^ 5) (by rw [map_pow, hx5]))) v hv
    push_cast at h
    exact h.symm
  exact sixteen_le_card_of_five hV2 (hLV x.2) h5 v0 hv0 hnot

end CFSG.Quasithin.Kleidman.F204

end
