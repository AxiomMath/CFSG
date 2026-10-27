module

public import CFSG.Timmesfeld.RootSubgroupClosure

public section

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem rootGroup_inf_eq_bot_of_opposite (hD : IsRootInvolutionSet D) (hrc : RootClosure D)
    {d c : G} (hd : d ∈ D) (hcD : c ∈ D) (hdc : ¬ Commute d c) :
    rootGroup D d ⊓ rootGroup D c = ⊥ := by
  refine rootGroup_inf_eq_bot_of_rootClosure hD hrc hd hcD fun h => hdc ?_
  have hc : c ∈ rootSet D d := h ▸ mem_rootSet_self hcD
  exact commute_of_mem_rootSet hd (mem_rootSet_self hd) hc

theorem odd_orderOf_mul_of_mem_rootGroup (hD : IsRootInvolutionSet D) (hrc : RootClosure D)
    {d c a b : G} (hd : d ∈ D) (hcD : c ∈ D) (hdc : ¬ Commute d c)
    (hodd : Odd (orderOf (d * c))) (ha : a ∈ rootGroup D d) (ha1 : a ≠ 1)
    (hb : b ∈ rootGroup D c) (hb1 : b ≠ 1) : Odd (orderOf (a * b)) ∧ ¬ Commute a b := by
  have ha' := (mem_rootSet_iff_mem_rootGroup_of_rootClosure hD hrc hd).2 ⟨ha, ha1⟩
  have hb' := (mem_rootSet_iff_mem_rootGroup_of_rootClosure hD hrc hcD).2 ⟨hb, hb1⟩
  exact odd_orderOf_mul_of_mem_rootSet hD hd hcD ha' hb' hodd hdc

theorem opposite_conj_self (hD : IsRootInvolutionSet D) {d x : G} (hd : d ∈ D) (hx : x * x = 1)
    (hdx : ¬ Commute d x) (hodd : Odd (orderOf (d * x))) :
    ¬ Commute d (x * d * x⁻¹) ∧ Odd (orderOf (d * (x * d * x⁻¹))) := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hdd := hD.mul_self_eq_one hd
  have hsq : d * (x * d * x⁻¹) = (d * x) ^ 2 := by rw [hxinv, pow_two]; group
  have hord : orderOf (d * (x * d * x⁻¹)) = orderOf (d * x) := by
    rw [hsq, orderOf_pow' _ two_ne_zero, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1
      ((Nat.coprime_two_left).2 hodd)), Nat.div_one]
  refine ⟨fun h => hdx ?_, hord ▸ hodd⟩
  have hee : x * d * x⁻¹ * (x * d * x⁻¹) = 1 := by
    rw [show x * d * x⁻¹ * (x * d * x⁻¹) = x * (d * d) * x⁻¹ by group, hdd, mul_one,
      mul_inv_cancel]
  have h2 := (commute_iff_mul_sq_eq_one hdd hee).1 h
  rw [hsq, ← pow_mul] at h2
  have h4 := orderOf_dvd_of_pow_eq_one h2
  have hle := Nat.le_of_dvd (by norm_num) h4
  have h1 : orderOf (d * x) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    interval_cases h : orderOf (d * x) <;> omega
  have : d * x = 1 := orderOf_eq_one_iff.mp h1
  rw [eq_inv_of_mul_eq_one_left this, hxinv]

theorem opposite_conj_of_mem_rootGroup (hD : IsRootInvolutionSet D) (hrc : RootClosure D)
    {d c b b' : G} (hd : d ∈ D) (hcD : c ∈ D) (hdc : ¬ Commute d c)
    (hodd : Odd (orderOf (d * c))) (hb : b ∈ rootGroup D c) (hb' : b' ∈ rootGroup D c)
    (hbb : b ≠ b') :
    ¬ Commute (b * d * b⁻¹) (b' * d * b'⁻¹) ∧
      Odd (orderOf (b * d * b⁻¹ * (b' * d * b'⁻¹))) := by
  set x := b'⁻¹ * b with hx
  have hxB : x ∈ rootGroup D c := (rootGroup D c).mul_mem ((rootGroup D c).inv_mem hb') hb
  have hx1 : x ≠ 1 := fun h => hbb (by rw [hx] at h; exact (inv_mul_eq_one.mp h).symm)
  have hxx : x * x = 1 := mul_self_eq_one_of_mem_rootGroup hD hcD hxB
  obtain ⟨hoddx, hcx⟩ := odd_orderOf_mul_of_mem_rootGroup hD hrc hd hcD hdc hodd
    (rootSet_subset_rootGroup D d (mem_rootSet_self hd)) (hD.ne_one hd) hxB hx1
  obtain ⟨h1, h2⟩ := opposite_conj_self hD hd hxx hcx hoddx
  have e1 : b' * (x * d * x⁻¹) * b'⁻¹ = b * d * b⁻¹ := by rw [hx]; group
  refine ⟨fun h => h1 ?_, ?_⟩
  · rw [← Commute.conj_iff b', e1]
    exact h.symm
  · rw [orderOf_mul_comm_eq, ← orderOf_conj_eq b'⁻¹,
      show b'⁻¹ * (b' * d * b'⁻¹ * (b * d * b⁻¹)) * b'⁻¹⁻¹ = d * (x * d * x⁻¹) by rw [hx]; group]
    exact h2

theorem rootSet_conj_ne_of_mem_rootGroup (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hrc : RootClosure D) {d c b b' : G} (hd : d ∈ D)
    (hcD : c ∈ D) (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c)))
    (hb : b ∈ rootGroup D c) (hb' : b' ∈ rootGroup D c) (hbb : b ≠ b') :
    rootSet D (b * d * b⁻¹) ≠ rootSet D (b' * d * b'⁻¹) := by
  intro h
  have hbD := conj_mem_of_isClass hclass b hd
  have hmem : b' * d * b'⁻¹ ∈ rootSet D (b * d * b⁻¹) :=
    h ▸ mem_rootSet_self (conj_mem_of_isClass hclass b' hd)
  exact (opposite_conj_of_mem_rootGroup hD hrc hd hcD hdc hodd hb hb' hbb).1
    (commute_of_mem_rootSet hbD (mem_rootSet_self hbD) hmem)

theorem ncard_image_rootSet_conj [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hrc : RootClosure D) {d c : G} (hd : d ∈ D) (hcD : c ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) :
    ((fun b => rootSet D (b * d * b⁻¹)) '' (rootGroup D c : Set G)).ncard =
      Nat.card (rootGroup D c) := by
  have hinj : Set.InjOn (fun b => rootSet D (b * d * b⁻¹)) (rootGroup D c : Set G) := by
    intro b hb b' hb' h
    by_contra hbb
    exact rootSet_conj_ne_of_mem_rootGroup hclass hD hrc hd hcD hdc hodd hb hb' hbb h
  rw [hinj.ncard_image, ← Nat.card_coe_set_eq]
  rfl

@[expose] noncomputable def dihedralSwap (t s : G) : G :=
  t * (t * s) ^ (orderOf (t * s) / 2 + 1)

theorem mul_pow_mul_eq_inv {t s : G} (ht : t * t = 1) (hs : s * s = 1) (m : ℕ) :
    t * (t * s) ^ m * t = ((t * s) ^ m)⁻¹ := by
  have h := mul_zpow_mul_eq_zpow_neg_mul ht hs (m : ℤ)
  rw [zpow_natCast, zpow_neg, zpow_natCast] at h
  rw [h, mul_assoc, ht, mul_one]

theorem dihedralSwap_mul_self {t s : G} (ht : t * t = 1) (hs : s * s = 1) :
    dihedralSwap t s * dihedralSwap t s = 1 := by
  rw [dihedralSwap]
  set m := orderOf (t * s) / 2 + 1
  rw [show t * (t * s) ^ m * (t * (t * s) ^ m) = t * (t * s) ^ m * t * (t * s) ^ m by group,
    mul_pow_mul_eq_inv ht hs, inv_mul_cancel]

theorem dihedralSwap_conj {t s : G} (ht : t * t = 1) (hs : s * s = 1)
    (hodd : Odd (orderOf (t * s))) : dihedralSwap t s * t * (dihedralSwap t s)⁻¹ = s := by
  obtain ⟨k, hk⟩ := hodd
  have hinv : (dihedralSwap t s)⁻¹ = dihedralSwap t s :=
    inv_eq_of_mul_eq_one_right (dihedralSwap_mul_self ht hs)
  have hk2 : orderOf (t * s) / 2 = k := by omega
  rw [hinv, dihedralSwap, hk2]
  have h1 : t * (t * s) ^ (k + 1) * t * (t * (t * s) ^ (k + 1)) =
      t * (t * s) ^ (k + 1) * (t * s) ^ (k + 1) := by
    rw [show t * (t * s) ^ (k + 1) * t * (t * (t * s) ^ (k + 1)) =
      t * (t * s) ^ (k + 1) * (t * t) * (t * s) ^ (k + 1) by group, ht, mul_one]
  rw [h1, mul_assoc, ← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk,
    pow_orderOf_eq_one, one_mul, ← mul_assoc, ht, one_mul]

theorem dihedralSwap_conj' {t s : G} (ht : t * t = 1) (hs : s * s = 1)
    (hodd : Odd (orderOf (t * s))) : dihedralSwap t s * s * (dihedralSwap t s)⁻¹ = t := by
  have h := dihedralSwap_conj ht hs hodd
  have hrr := dihedralSwap_mul_self ht hs
  set r := dihedralSwap t s
  have hinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  rw [← h, hinv, show r * (r * t * r) * r = (r * r) * t * (r * r) by group, hrr, one_mul,
    mul_one]

theorem dihedralSwap_mem (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    {t s : G} (ht : t ∈ D) (hs : s ∈ D) (hodd : Odd (orderOf (t * s))) : dihedralSwap t s ∈ D := by
  have ht2 := hD.mul_self_eq_one ht
  have hs2 := hD.mul_self_eq_one hs
  have hodd' : Odd (orderOf (t * dihedralSwap t s)) := by
    rw [dihedralSwap, ← mul_assoc, ht2, one_mul]
    exact Odd.of_dvd_nat hodd (orderOf_pow_dvd _)
  obtain ⟨g, -, hg⟩ := exists_conj_of_odd_orderOf_mul ht2 (dihedralSwap_mul_self ht2 hs2) hodd'
  rw [← hg]
  exact conj_mem_of_isClass hclass g ht

theorem dihedralSwap_conj_rootSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d c t s : G} (hd : d ∈ D) (hcD : c ∈ D)
    (ht : t ∈ rootSet D d) (hs : s ∈ rootSet D c) (hodd : Odd (orderOf (t * s))) :
    dihedralSwap t s * d * (dihedralSwap t s)⁻¹ ∈ rootSet D c ∧
      dihedralSwap t s * c * (dihedralSwap t s)⁻¹ ∈ rootSet D d := by
  have ht2 := hD.mul_self_eq_one ht.1
  have hs2 := hD.mul_self_eq_one hs.1
  have e1 := rootSet_conj hclass (dihedralSwap t s) t
  have e2 := rootSet_conj hclass (dihedralSwap t s) s
  rw [dihedralSwap_conj ht2 hs2 hodd, rootSet_eq_of_mem ht, rootSet_eq_of_mem hs] at e1
  rw [dihedralSwap_conj' ht2 hs2 hodd, rootSet_eq_of_mem ht, rootSet_eq_of_mem hs] at e2
  refine ⟨?_, ?_⟩
  · rw [e1]; exact ⟨d, mem_rootSet_self hd, rfl⟩
  · rw [e2]; exact ⟨c, mem_rootSet_self hcD, rfl⟩

theorem exists_conj_eq_of_mem_rootSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d c a a' : G} (hd : d ∈ D) (hcD : c ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (ha : a ∈ rootSet D d)
    (ha' : a' ∈ rootSet D d) :
    ∃ h : G, h * a * h⁻¹ = a' ∧ h * d * h⁻¹ ∈ rootSet D d ∧ h * c * h⁻¹ ∈ rootSet D c := by
  have hc := mem_rootSet_self hcD
  have hoa := (odd_orderOf_mul_of_mem_rootSet hD hd hcD ha hc hodd hdc).1
  have hoa' := (odd_orderOf_mul_of_mem_rootSet hD hd hcD ha' hc hodd hdc).1
  have ha2 := hD.mul_self_eq_one ha.1
  have ha'2 := hD.mul_self_eq_one ha'.1
  have hc2 := hD.mul_self_eq_one hcD
  set r := dihedralSwap a c
  set r' := dihedralSwap a' c
  obtain ⟨hr1, hr2⟩ := dihedralSwap_conj_rootSet hclass hD hd hcD ha hc hoa
  obtain ⟨hr'1, hr'2⟩ := dihedralSwap_conj_rootSet hclass hD hd hcD ha' hc hoa'
  refine ⟨r' * r, ?_, ?_, ?_⟩
  · rw [mul_inv_rev, show r' * r * a * (r⁻¹ * r'⁻¹) = r' * (r * a * r⁻¹) * r'⁻¹ by group,
      dihedralSwap_conj ha2 hc2 hoa, dihedralSwap_conj' ha'2 hc2 hoa']
  ·
    have h1 : r' * (r * d * r⁻¹) * r'⁻¹ ∈ rootSet D (r' * c * r'⁻¹) := by
      rw [rootSet_conj hclass, ← rootSet_eq_of_mem hr1]
      exact ⟨_, mem_rootSet_self hr1.1, rfl⟩
    rw [rootSet_eq_of_mem hr'2] at h1
    rwa [mul_inv_rev, show r' * r * d * (r⁻¹ * r'⁻¹) = r' * (r * d * r⁻¹) * r'⁻¹ by group]
  ·
    have h1 : r' * (r * c * r⁻¹) * r'⁻¹ ∈ rootSet D (r' * d * r'⁻¹) := by
      rw [rootSet_conj hclass, ← rootSet_eq_of_mem hr2]
      exact ⟨_, mem_rootSet_self hr2.1, rfl⟩
    rw [rootSet_eq_of_mem hr'1] at h1
    rwa [mul_inv_rev, show r' * r * c * (r⁻¹ * r'⁻¹) = r' * (r * c * r⁻¹) * r'⁻¹ by group]

end CFSG.Timmesfeld
