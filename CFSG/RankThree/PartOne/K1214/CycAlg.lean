module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartOne.K1214

variable {G : Type*} [Group G]

theorem zpowers_eq_of_card_prime [Finite G] {p : ℕ} (hp : p.Prime) {U : Subgroup G}
    (hU : Nat.card U = p) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) : Subgroup.zpowers u = U := by
  have : Fact p.Prime := ⟨hp⟩
  have hup : u ^ p = 1 := by
    have h : (⟨u, hu⟩ : ↥U) ^ Nat.card U = 1 := pow_card_eq_one'
    rw [hU] at h
    exact congrArg Subtype.val h
  have hord : orderOf u = p := orderOf_eq_prime hup hu1
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hu) ?_
  rw [Nat.card_zpowers, hord, hU]

theorem conj_eq_of_card_prime [Finite G] {p m : ℕ} (hp : p.Prime) {D : Subgroup G}
    (hD : Nat.card D = p) {c : G} (hcD : ∀ d ∈ D, c * d * c⁻¹ ∈ D) (hcp : c ^ (p ^ m) = 1) :
    ∀ d ∈ D, c * d * c⁻¹ = d := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hD1 : D ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hD
    exact hp.one_lt.ne hD
  obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD1
  have hg1' : (g : G) ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hDg : Subgroup.zpowers (g : G) = D := zpowers_eq_of_card_prime hp hD g.2 hg1'
  have hgp : (g : G) ^ p = 1 := by
    have h : g ^ Nat.card D = 1 := pow_card_eq_one'
    rw [hD] at h
    exact congrArg Subtype.val h
  have hord : orderOf (g : G) = p := orderOf_eq_prime hgp hg1'
  have hcg : c * (g : G) * c⁻¹ ∈ Subgroup.zpowers (g : G) := by
    rw [hDg]
    exact hcD g g.2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcg
  have hpow : ∀ n : ℕ, c ^ n * (g : G) * (c ^ n)⁻¹ = (g : G) ^ ((k : ℤ) ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc c ^ (n + 1) * (g : G) * (c ^ (n + 1))⁻¹
          = c * (c ^ n * (g : G) * (c ^ n)⁻¹) * c⁻¹ := by rw [pow_succ']; group
        _ = c * (g : G) ^ ((k : ℤ) ^ n) * c⁻¹ := by rw [ih]
        _ = (c * (g : G) * c⁻¹) ^ ((k : ℤ) ^ n) := (conj_zpow).symm
        _ = ((g : G) ^ k) ^ ((k : ℤ) ^ n) := by rw [← hk]
        _ = (g : G) ^ ((k : ℤ) ^ (n + 1)) := by rw [← zpow_mul, pow_succ']
  have h1 : (g : G) = (g : G) ^ ((k : ℤ) ^ (p ^ m)) := by
    have := hpow (p ^ m)
    rwa [hcp, one_mul, inv_one, mul_one] at this
  have h2 : (g : G) ^ (((k : ℤ) ^ (p ^ m)) - 1) = 1 := by
    rw [zpow_sub_one, ← h1, mul_inv_cancel]
  have h3 : (p : ℤ) ∣ (k : ℤ) ^ (p ^ m) - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h2
    rwa [hord] at this
  have h4 : ((k : ℤ) : ZMod p) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h3
    push_cast at this
    rw [ZMod.pow_card_pow, sub_eq_zero] at this
    exact this
  have h5 : (p : ℤ) ∣ k - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
    push_cast
    rw [h4, sub_self]
  have h6 : (g : G) ^ (k - 1) = 1 :=
    orderOf_dvd_iff_zpow_eq_one.1 (by rw [hord]; exact h5)
  have h7 : c * (g : G) * c⁻¹ = (g : G) := by
    rw [← hk]
    have : (g : G) ^ k = (g : G) ^ (k - 1) * (g : G) := by
      rw [← zpow_add_one]
      congr 1
      ring
    rw [this, h6, one_mul]
  intro d hd
  rw [← hDg] at hd
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
  rw [← conj_zpow, h7]

section Torsion

@[expose] def torsionSub (Y : Subgroup G) (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) (n : ℕ) :
    Subgroup G where
  carrier := {y | y ∈ Y ∧ y ^ n = 1}
  mul_mem' := fun {a b} ha hb => ⟨Y.mul_mem ha.1 hb.1, by
    rw [(Commute.mul_pow (hcomm a ha.1 b hb.1 : Commute a b)), ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨Y.one_mem, one_pow n⟩
  inv_mem' := fun {a} ha => ⟨Y.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem mem_torsionSub {Y : Subgroup G} {hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x} {n : ℕ}
    {y : G} : y ∈ torsionSub Y hcomm n ↔ y ∈ Y ∧ y ^ n = 1 := Iff.rfl

variable [Finite G]

omit [Finite G] in
theorem torsionSub_le_succ {Y : Subgroup G} (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) {p : ℕ}
    (k : ℕ) : torsionSub Y hcomm (p ^ k) ≤ torsionSub Y hcomm (p ^ (k + 1)) := fun y hy => by
  rw [mem_torsionSub] at hy ⊢
  refine ⟨hy.1, ?_⟩
  rw [pow_succ, pow_mul, hy.2, one_pow]

theorem card_torsionSub_succ_le {p : ℕ} {Y : Subgroup G}
    (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) {B : Subgroup G} (hB : Nat.card B ≤ p)
    (h : ∀ y ∈ Y, y ^ p = 1 → y ∈ B) (k : ℕ) :
    Nat.card (torsionSub Y hcomm (p ^ (k + 1))) ≤ Nat.card (torsionSub Y hcomm (p ^ k)) * p := by
  have hT1 : Nat.card (torsionSub Y hcomm (p ^ 1)) ≤ p := by
    refine le_trans (Subgroup.card_le_of_le ?_) hB
    intro y hy
    rw [mem_torsionSub, pow_one] at hy
    exact h y hy.1 hy.2
  let ψ : ↥(torsionSub Y hcomm (p ^ (k + 1))) →* G :=
    { toFun := fun a => (a : G) ^ (p ^ k)
      map_one' := by simp
      map_mul' := fun a b => by
        have hab : Commute (a : G) (b : G) := hcomm a (a.2.1) b (b.2.1)
        show ((a : G) * b) ^ (p ^ k) = (a : G) ^ (p ^ k) * (b : G) ^ (p ^ k)
        exact hab.mul_pow _ }
  have hker : ψ.ker = (torsionSub Y hcomm (p ^ k)).subgroupOf (torsionSub Y hcomm (p ^ (k + 1))) := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_torsionSub]
    exact ⟨fun h => ⟨a.2.1, h⟩, fun h => h.2⟩
  have hrange : ψ.range ≤ torsionSub Y hcomm (p ^ 1) := by
    rintro _ ⟨a, rfl⟩
    rw [mem_torsionSub, pow_one]
    refine ⟨?_, ?_⟩
    · exact Y.pow_mem a.2.1 _
    · show ((a : G) ^ (p ^ k)) ^ p = 1
      rw [← pow_mul, ← pow_succ]
      exact a.2.2
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have h2 : Nat.card ψ.ker = Nat.card (torsionSub Y hcomm (p ^ k)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (torsionSub_le_succ hcomm k)).toEquiv
  have h3 : Nat.card ψ.range ≤ p := (Subgroup.card_le_of_le hrange).trans hT1
  rw [← h1, h2]
  exact Nat.mul_le_mul_left _ h3

theorem isCyclic_of_torsion_le {p : ℕ} (hp : p.Prime) {Y : Subgroup G}
    (hY : IsPGroup p ↥Y) (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) {B : Subgroup G}
    (hB : Nat.card B ≤ p) (h : ∀ y ∈ Y, y ^ p = 1 → y ∈ B) : IsCyclic ↥Y := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype ↥Y := Fintype.ofFinite _
  have hTcard : ∀ k, Nat.card (torsionSub Y hcomm (p ^ k)) ≤ p ^ k := by
    intro k
    induction k with
    | zero =>
      have : torsionSub Y hcomm (p ^ 0) = ⊥ := by
        ext y
        rw [mem_torsionSub, Subgroup.mem_bot, pow_zero, pow_one]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ Y.one_mem, h⟩⟩
      rw [this, Subgroup.card_bot]
      simp
    | succ k ih =>
      calc Nat.card (torsionSub Y hcomm (p ^ (k + 1)))
          ≤ Nat.card (torsionSub Y hcomm (p ^ k)) * p := card_torsionSub_succ_le hcomm hB h k
        _ ≤ p ^ k * p := Nat.mul_le_mul_right _ ih
        _ = p ^ (k + 1) := (pow_succ p k).symm
  refine isCyclic_of_card_pow_eq_one_le (fun n hn => ?_)
  set k := n.factorization p with hk
  have hpk : p ^ k ∣ n := Nat.ordProj_dvd n p
  have hpkn : p ^ k ≤ n := Nat.le_of_dvd hn hpk
  have hsub : ∀ a : ↥Y, a ^ n = 1 → (a : G) ∈ torsionSub Y hcomm (p ^ k) := by
    intro a ha
    obtain ⟨j, hj⟩ := hY a
    have h1 : orderOf a ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).1 h1
    have h2 : orderOf a ∣ n := orderOf_dvd_of_pow_eq_one ha
    rw [hi'] at h2
    have h3 : i ≤ k := (hp.pow_dvd_iff_le_factorization hn.ne').1 h2
    have h4 : orderOf a ∣ p ^ k := by
      rw [hi']
      exact pow_dvd_pow p h3
    rw [mem_torsionSub]
    refine ⟨a.2, ?_⟩
    have h5 : a ^ (p ^ k) = 1 := orderOf_dvd_iff_pow_eq_one.1 h4
    exact congrArg Subtype.val h5
  have hcard : Nat.card {a : ↥Y // a ^ n = 1} ≤ Nat.card (torsionSub Y hcomm (p ^ k)) := by
    refine Nat.card_le_card_of_injective
      (fun a => (⟨(a.1 : G), hsub a.1 a.2⟩ : torsionSub Y hcomm (p ^ k))) ?_
    intro a b hab
    have h1 : ((a.1 : ↥Y) : G) = ((b.1 : ↥Y) : G) :=
      congrArg (fun t : ↥(torsionSub Y hcomm (p ^ k)) => (t : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  calc (Finset.univ.filter (fun a : ↥Y => a ^ n = 1)).card
      = Nat.card {a : ↥Y // a ^ n = 1} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ Nat.card (torsionSub Y hcomm (p ^ k)) := hcard
    _ ≤ p ^ k := hTcard k
    _ ≤ n := hpkn

end Torsion

section Arith

theorem exists_dvd_add_mul {p : ℕ} (hp : p.Prime) {s t : ℤ} (ht : ¬ (p : ℤ) ∣ t) :
    ∃ k : ℤ, (p : ℤ) ∣ s + t * k := by
  have : Fact p.Prime := ⟨hp⟩
  have hne : (t : ZMod p) ≠ 0 := fun h0 => ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t p).1 h0)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ((k : ℤ) : ZMod p) = -(s : ZMod p) * (t : ZMod p)⁻¹ :=
    ⟨((-(s : ZMod p) * (t : ZMod p)⁻¹).val : ℤ), by simp⟩
  refine ⟨k, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
  push_cast
  rw [hk]
  have h1 : (t : ZMod p) * (t : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hne
  calc (s : ZMod p) + (t : ZMod p) * (-(s : ZMod p) * (t : ZMod p)⁻¹)
      = s - s * ((t : ZMod p) * (t : ZMod p)⁻¹) := by ring
    _ = 0 := by rw [h1]; ring

end Arith

end CFSG.RankThree.PartOne.K1214
