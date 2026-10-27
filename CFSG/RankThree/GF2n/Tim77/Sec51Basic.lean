module

public import CFSG.RankThree.GF2n.Tim77.Sec48
public import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

section Dihedral

theorem sec51_dih_conj_inv {G : Type} [Group G] {c d : G} (hc : c * c = 1) (hd : d * d = 1) :
    d * (c * d) * d = (c * d)⁻¹ ∧ c * (c * d) * c = (c * d)⁻¹ := by
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hd' : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  rw [mul_inv_rev, hc', hd']
  constructor
  · calc d * (c * d) * d = d * c * (d * d) := by simp only [mul_assoc]
      _ = d * c := by rw [hd, mul_one]
  · calc c * (c * d) * c = c * c * d * c := by simp only [mul_assoc]
      _ = d * c := by rw [hc, one_mul]

theorem sec51_dih_conj_mul {G : Type} [Group G] {c : G} (hc : c * c = 1) (x y : G) :
    c * (x * y) * c = (c * x * c) * (c * y * c) := by
  have h : (c * x * c) * (c * y * c) = c * x * (c * c) * y * c := by
    simp only [mul_assoc]
  rw [h, hc]
  simp only [mul_one, mul_assoc]

theorem sec51_dih_conj_pow {G : Type} [Group G] {c r : G} (hc : c * c = 1)
    (hr : c * r * c = r⁻¹) (k : ℕ) : c * r ^ k * c = r⁻¹ ^ k := by
  induction k with
  | zero => simpa using hc
  | succ k ih =>
    rw [pow_succ', pow_succ', sec51_dih_conj_mul hc, hr, ih]

theorem sec51_dih_comm_of_conj {G : Type} [Group G] {c z : G} (hc : c * c = 1)
    (h : c * z * c = z) : z * c = c * z := by
  calc z * c = c * z * c * c := by rw [h]
    _ = c * z * (c * c) := by simp only [mul_assoc]
    _ = c * z := by rw [hc, mul_one]

theorem sec51_dih_sq_of_conj {G : Type} [Group G] {c z : G} (h : c * z * c = z⁻¹) :
    (z * c) * (z * c) = 1 := by
  calc (z * c) * (z * c) = z * (c * z * c) := by simp only [mul_assoc]
    _ = z * z⁻¹ := by rw [h]
    _ = 1 := by simp

theorem sec51_dih_conj_aux {G : Type} [Group G] {a β r g z : G} (ha : a * a = 1)
    (hβ : β = r * a) (hg : a * g * a = g⁻¹) (hz : g⁻¹ * r * g⁻¹ = z) :
    g⁻¹ * β * g = z * a := by
  have hag : a * g = g⁻¹ * a := by
    calc a * g = a * g * (a * a) := by rw [ha, mul_one]
      _ = a * g * a * a := by simp only [mul_assoc]
      _ = g⁻¹ * a := by rw [hg]
  subst hβ
  calc g⁻¹ * (r * a) * g = g⁻¹ * r * (a * g) := by simp only [mul_assoc]
    _ = g⁻¹ * r * (g⁻¹ * a) := by rw [hag]
    _ = g⁻¹ * r * g⁻¹ * a := by simp only [mul_assoc]
    _ = z * a := by rw [hz]

theorem sec51_sandwich {G : Type} [Group G] (g x : G) :
    g⁻¹ * (g * x * g) * g⁻¹ = x := by
  simp [mul_assoc]

theorem sec51_dih_pow_key {G : Type} [Group G] {r : G} {n j : ℕ} (hj : 2 * j = n + 1)
    (hn : r ^ n * r ^ n = 1) : (r ^ j)⁻¹ * r * (r ^ j)⁻¹ = r ^ n := by
  have h1 : r ^ j * r ^ n * r ^ j = r := by
    have e : j + n + j = n + n + 1 := by omega
    rw [← pow_add, ← pow_add, e, pow_succ, pow_add, hn, one_mul]
  calc (r ^ j)⁻¹ * r * (r ^ j)⁻¹
      = (r ^ j)⁻¹ * (r ^ j * r ^ n * r ^ j) * (r ^ j)⁻¹ := by rw [h1]
    _ = r ^ n := sec51_sandwich _ _

theorem sec51_dih_odd {G : Type} [Group G] {β a : G} (hβ : β * β = 1) (ha : a * a = 1) {n : ℕ}
    (hn : Odd n) (hord : orderOf ((β * a) * (β * a)) = n) :
    (β * a) ^ n * (β * a) ^ n = 1 ∧ (β * a) ^ n * a = a * (β * a) ^ n ∧
      (β * a) ^ n * β = β * (β * a) ^ n ∧
      ((β * a) ^ n * a) * ((β * a) ^ n * a) = 1 ∧
      ((β * a) ^ ((n + 1) / 2))⁻¹ * β * (β * a) ^ ((n + 1) / 2) = (β * a) ^ n * a := by
  have hra : a * (β * a) * a = (β * a)⁻¹ := (sec51_dih_conj_inv hβ ha).1
  have hrb : β * (β * a) * β = (β * a)⁻¹ := (sec51_dih_conj_inv hβ ha).2
  have hsq : (β * a) ^ n * (β * a) ^ n = 1 := by
    rw [← (Commute.refl (β * a)).mul_pow n, ← hord, pow_orderOf_eq_one]
  have hz' : ((β * a) ^ n)⁻¹ = (β * a) ^ n := inv_eq_of_mul_eq_one_right hsq
  have hca' : a * (β * a) ^ n * a = ((β * a) ^ n)⁻¹ := by
    rw [sec51_dih_conj_pow ha hra n, inv_pow]
  have hcb' : β * (β * a) ^ n * β = ((β * a) ^ n)⁻¹ := by
    rw [sec51_dih_conj_pow hβ hrb n, inv_pow]
  have hca : a * (β * a) ^ n * a = (β * a) ^ n := hca'.trans hz'
  have hcb : β * (β * a) ^ n * β = (β * a) ^ n := hcb'.trans hz'
  refine ⟨hsq, sec51_dih_comm_of_conj ha hca, sec51_dih_comm_of_conj hβ hcb,
    sec51_dih_sq_of_conj hca', ?_⟩
  have hj : 2 * ((n + 1) / 2) = n + 1 := by
    obtain ⟨m, hm⟩ := hn
    omega
  have hg : a * (β * a) ^ ((n + 1) / 2) * a = ((β * a) ^ ((n + 1) / 2))⁻¹ := by
    rw [sec51_dih_conj_pow ha hra, inv_pow]
  have hβ' : β = β * a * a := by
    rw [mul_assoc, ha, mul_one]
  exact sec51_dih_conj_aux ha hβ' hg (sec51_dih_pow_key hj hsq)

theorem sec51_conj_of_odd {G : Type} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hodd : Odd (orderOf (x * y))) :
    ∃ k : ℕ, ((x * y) ^ k)⁻¹ * x * (x * y) ^ k = y := by
  obtain ⟨m, hm⟩ := hodd
  have hrn : (x * y) ^ orderOf (x * y) = 1 := pow_orderOf_eq_one _
  have hsq : (x * y) ^ orderOf (x * y) * (x * y) ^ orderOf (x * y) = 1 := by
    rw [hrn, one_mul]
  have hj : 2 * ((orderOf (x * y) + 1) / 2) = orderOf (x * y) + 1 := by
    omega
  have hyy : y * (x * y) * y = (x * y)⁻¹ := (sec51_dih_conj_inv hx hy).1
  have hg : y * (x * y) ^ ((orderOf (x * y) + 1) / 2) * y
      = ((x * y) ^ ((orderOf (x * y) + 1) / 2))⁻¹ := by
    rw [sec51_dih_conj_pow hy hyy, inv_pow]
  have hxr : x = x * y * y := by
    rw [mul_assoc, hy, mul_one]
  refine ⟨(orderOf (x * y) + 1) / 2, ?_⟩
  have key := sec51_dih_conj_aux hy hxr hg (sec51_dih_pow_key hj hsq)
  rw [key, hrn, one_mul]

theorem sec51_mem_of_conj_mem {G : Type} [Group G] {S U₀ : Subgroup G} (hU : U₀ ≤ S) {h x : G}
    (hh : h ∈ S) (hx : x ∈ conjSubgroup h U₀) : x ∈ S := by
  obtain ⟨y, hy, rfl⟩ := (mem_conjSubgroup_exists_t77 h U₀ x).1 hx
  exact S.mul_mem (S.mul_mem hh (hU hy)) (S.inv_mem hh)

theorem sec51_sq_of_mem_conj {G : Type} [Group G] {U₀ : Subgroup G} (hel : IsElemAbelian 2 U₀)
    {h x : G} (hx : x ∈ conjSubgroup h U₀) : x * x = 1 := by
  rw [← sq]
  exact (isElemAbelian_conj hel h).2 x hx

theorem sec51_conj_mem_conj {G : Type} [Group G] {U₀ : Subgroup G} {h₁ a : G}
    (ha : a ∈ conjSubgroup h₁ U₀) (r : G) :
    r⁻¹ * a * r ∈ conjSubgroup (r⁻¹ * h₁) U₀ := by
  rw [mem_conjSubgroup] at ha ⊢
  have e : (r⁻¹ * h₁)⁻¹ * (r⁻¹ * a * r) * (r⁻¹ * h₁) = h₁⁻¹ * a * h₁ := by group
  rw [e]
  exact ha

theorem sec51_dih_key {G : Type} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1) :
    a * ((a * b)⁻¹ * a * (a * b)) = a * b * (a * b) ∧
      ((a * b)⁻¹ * a * (a * b)) * ((a * b)⁻¹ * a * (a * b)) = 1 := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hk : a * (a * b)⁻¹ * a = a * b := by
    calc a * (a * b)⁻¹ * a = a * b⁻¹ * (a⁻¹ * a) := by group
      _ = a * b := by rw [hbinv, inv_mul_cancel, mul_one]
  refine ⟨?_, ?_⟩
  · calc a * ((a * b)⁻¹ * a * (a * b)) = a * (a * b)⁻¹ * a * (a * b) := by group
      _ = a * b * (a * b) := by rw [hk]
  · calc (a * b)⁻¹ * a * (a * b) * ((a * b)⁻¹ * a * (a * b))
        = (a * b)⁻¹ * (a * a) * (a * b) := by group
      _ = 1 := by rw [ha, mul_one, inv_mul_cancel]

theorem sec51_dih_claim {G : Type} [Group G] {S U₀ : Subgroup G} (hU : U₀ ≤ S)
    (hno : ¬ ∃ h ∈ S, ∃ a ∈ conjSubgroup h U₀, ∃ b ∈ U₀, a * a = 1 ∧ b * b = 1 ∧
      orderOf (a * b) = 4) (m : ℕ) :
    ∀ h₁ ∈ S, ∀ h₂ ∈ S, ∀ a ∈ conjSubgroup h₁ U₀, ∀ b ∈ conjSubgroup h₂ U₀,
      a * a = 1 → b * b = 1 → orderOf (a * b) = 2 ^ (m + 2) → False := by
  induction m with
  | zero =>
    intro h₁ hh₁ h₂ hh₂ a ha b hb ha1 hb1 hord
    have hord4 : orderOf (a * b) = 4 := by simpa using hord
    apply hno
    have e : h₂⁻¹ * a * h₂ * (h₂⁻¹ * b * h₂) = h₂⁻¹ * (a * b) * (h₂⁻¹)⁻¹ := by
      group
    refine ⟨h₂⁻¹ * h₁, S.mul_mem (S.inv_mem hh₂) hh₁, h₂⁻¹ * a * h₂,
      sec51_conj_mem_conj ha h₂, h₂⁻¹ * b * h₂, mem_conjSubgroup.1 hb, ?_, ?_, ?_⟩
    · have e1 : h₂⁻¹ * a * h₂ * (h₂⁻¹ * a * h₂) = h₂⁻¹ * (a * a) * h₂ := by group
      rw [e1, ha1, mul_one, inv_mul_cancel]
    · have e2 : h₂⁻¹ * b * h₂ * (h₂⁻¹ * b * h₂) = h₂⁻¹ * (b * b) * h₂ := by group
      rw [e2, hb1, mul_one, inv_mul_cancel]
    · rw [e, orderOf_conjugate_t77]
      exact hord4
  | succ m ih =>
    intro h₁ hh₁ h₂ hh₂ a ha b hb ha1 hb1 hord
    have hrS : a * b ∈ S := S.mul_mem (sec51_mem_of_conj_mem hU hh₁ ha)
      (sec51_mem_of_conj_mem hU hh₂ hb)
    obtain ⟨hk1, hk2⟩ := sec51_dih_key ha1 hb1
    have h2dvd : (2 : ℕ) ∣ orderOf (a * b) := by
      rw [hord]
      exact dvd_pow_self 2 (by omega)
    have hsq : orderOf (a * b * (a * b)) = 2 ^ (m + 2) := by
      rw [← pow_two, orderOf_pow_of_dvd (by norm_num) h2dvd, hord,
        show (2 : ℕ) ^ (m + 1 + 2) = 2 ^ (m + 2) * 2 by ring,
        Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    have hord' : orderOf (a * ((a * b)⁻¹ * a * (a * b))) = 2 ^ (m + 2) := by
      rw [hk1]
      exact hsq
    have hh3 : (a * b)⁻¹ * h₁ ∈ S := S.mul_mem (S.inv_mem hrS) hh₁
    exact ih h₁ hh₁ ((a * b)⁻¹ * h₁) hh3 a ha _ (sec51_conj_mem_conj ha (a * b)) ha1 hk2 hord'

theorem sec51_dih_comm {G : Type} [Group G] {S U₀ : Subgroup G} (hS : IsPGroup 2 S)
    (hU : U₀ ≤ S)
    (hno : ¬ ∃ h ∈ S, ∃ a ∈ conjSubgroup h U₀, ∃ b ∈ U₀, a * a = 1 ∧ b * b = 1 ∧
      orderOf (a * b) = 4)
    {h₁ h₂ a b : G} (hh₁ : h₁ ∈ S) (hh₂ : h₂ ∈ S) (ha : a ∈ conjSubgroup h₁ U₀)
    (hb : b ∈ conjSubgroup h₂ U₀) (ha1 : a * a = 1) (hb1 : b * b = 1) :
    a * b = b * a := by
  by_contra hne
  have hrS : a * b ∈ S := S.mul_mem (sec51_mem_of_conj_mem hU hh₁ ha)
      (sec51_mem_of_conj_mem hU hh₂ hb)
  obtain ⟨k, hk⟩ := hS ⟨a * b, hrS⟩
  have hpow : (a * b) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hpow)
  rcases Nat.lt_or_ge i 2 with hi2 | hi2
  · interval_cases i
    · rw [pow_zero] at hi
      have h1 : a * b = 1 := orderOf_eq_one_iff.1 hi
      exact hne (h1.trans (mul_eq_one_comm.1 h1).symm)
    · rw [pow_one] at hi
      have h2 := pow_orderOf_eq_one (a * b)
      rw [hi, pow_two] at h2
      exact hne (sec48_comm_of_sq ha1 hb1 h2)
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    exact sec51_dih_claim hU hno j h₁ hh₁ h₂ hh₂ a ha b hb ha1 hb1 hi

theorem sec51_dih_reduce {G : Type} [Group G] {S U₀ : Subgroup G} (hS : IsPGroup 2 S)
    (hU : U₀ ≤ S) (hel : IsElemAbelian 2 U₀)
    (hno : ¬ ∃ h ∈ S, ∃ a ∈ conjSubgroup h U₀, ∃ b ∈ U₀, a * a = 1 ∧ b * b = 1 ∧
      orderOf (a * b) = 4) :
    IsElemAbelian 2 (⨆ h ∈ S, conjSubgroup h U₀) := by
  have hcomm : ∀ x ∈ {x : G | ∃ h ∈ S, x ∈ conjSubgroup h U₀},
      ∀ y ∈ {x : G | ∃ h ∈ S, x ∈ conjSubgroup h U₀}, x * y = y * x := by
    rintro x ⟨h₁, hh₁, hx⟩ y ⟨h₂, hh₂, hy⟩
    exact sec51_dih_comm hS hU hno hh₁ hh₂ hx hy (sec51_sq_of_mem_conj hel hx)
      (sec51_sq_of_mem_conj hel hy)
  have hsq : ∀ x ∈ {x : G | ∃ h ∈ S, x ∈ conjSubgroup h U₀}, x * x = 1 := by
    rintro x ⟨h₁, _, hx⟩
    exact sec51_sq_of_mem_conj hel hx
  have hclos : (⨆ h ∈ S, conjSubgroup h U₀) =
      Subgroup.closure {x : G | ∃ h ∈ S, x ∈ conjSubgroup h U₀} := by
    apply le_antisymm
    · refine iSup₂_le fun h hh => ?_
      intro x hx
      have hx' : x ∈ {x : G | ∃ h ∈ S, x ∈ conjSubgroup h U₀} := ⟨h, hh, hx⟩
      exact Subgroup.subset_closure hx'
    · rw [Subgroup.closure_le]
      rintro x ⟨h, hh, hx⟩
      exact (le_iSup₂ (f := fun h (_ : h ∈ S) => conjSubgroup h U₀) h hh) hx
  rw [hclos]
  exact sec48_closure_elemAbelian hcomm hsq

end Dihedral

section Equational

theorem sec51_h0_inv {G : Type} [Group G] {a β : G} (ha : a * a = 1) (hβ : β * β = 1) :
    (β * (a * β * a))⁻¹ = a * β * a * β := by
  apply inv_eq_of_mul_eq_one_right
  calc β * (a * β * a) * (a * β * a * β)
      = β * (a * β * (a * a) * β * a) * β := by simp only [mul_assoc]
    _ = β * (a * β * 1 * β * a) * β := by rw [ha]
    _ = β * (a * (β * β) * a) * β := by simp only [mul_assoc, mul_one]
    _ = β * (a * 1 * a) * β := by rw [hβ]
    _ = β * (a * a) * β := by simp only [mul_one]
    _ = β * 1 * β := by rw [ha]
    _ = β * β := by simp only [mul_one]
    _ = 1 := hβ

theorem sec51_h0_conj {G : Type} [Group G] {a β a₀ ε : G} (ha : a * a = 1)
    (haa₀ : a * a₀ = a₀ * a) (hβa₀ : β * a₀ * β = ε * a₀) :
    a * β * a * a₀ * (a * β * a) = a * ε * a * a₀ := by
  have h1 : a * a₀ * a = a₀ := by
    rw [haa₀, mul_assoc, ha, mul_one]
  calc a * β * a * a₀ * (a * β * a)
      = a * (β * (a * a₀ * a) * β) * a := by simp only [mul_assoc]
    _ = a * (β * a₀ * β) * a := by rw [h1]
    _ = a * (ε * a₀) * a := by rw [hβa₀]
    _ = a * ε * (a₀ * a) := by simp only [mul_assoc]
    _ = a * ε * (a * a₀) := by rw [haa₀]
    _ = a * ε * a * a₀ := by simp only [mul_assoc]

theorem sec51_claim1 {G : Type} [Group G] {a α e κ z : G}
    (ha : a * a = 1) (hα : α * α = 1) (hz : z * z = 1)
    (hαe : α * e * α = κ * e) (haα : a * α * a = z * α)
    (hκe : κ * e = e * κ) (hze : z * e = e * z) (hzκ : z * κ = κ * z)
    (haκ : a * κ = κ * a) (hαz : α * z = z * α) :
    α * (a * e * a) * α = κ * (a * e * a) := by
  have hαa : α * a = a * z * α := by
    calc α * a = (a * a) * (α * a) := by rw [ha, one_mul]
      _ = a * (a * α * a) := by simp only [mul_assoc]
      _ = a * (z * α) := by rw [haα]
      _ = a * z * α := by simp only [mul_assoc]
  have haα' : a * α = z * α * a := by
    calc a * α = a * α * (a * a) := by rw [ha, mul_one]
      _ = (a * α * a) * a := by simp only [mul_assoc]
      _ = (z * α) * a := by rw [haα]
      _ = z * α * a := rfl
  have hαzα : α * z * α = z := by
    rw [hαz, mul_assoc, hα, mul_one]
  have hzκez : z * κ * e * z = κ * e := by
    calc z * κ * e * z = κ * z * e * z := by rw [hzκ]
      _ = κ * (z * e) * z := by simp only [mul_assoc]
      _ = κ * (e * z) * z := by rw [hze]
      _ = κ * e * (z * z) := by simp only [mul_assoc]
      _ = κ * e := by rw [hz, mul_one]
  have hαez : α * e * z * α = κ * e * z := by
    calc α * e * z * α = α * e * (α * α) * z * α := by rw [hα, mul_one]
      _ = (α * e * α) * (α * z * α) := by simp only [mul_assoc]
      _ = (κ * e) * z := by rw [hαe, hαzα]
  calc α * (a * e * a) * α = (α * a) * e * (a * α) := by simp only [mul_assoc]
    _ = (a * z * α) * e * (z * α * a) := by rw [hαa, haα']
    _ = a * z * (α * e * z * α) * a := by simp only [mul_assoc]
    _ = a * z * (κ * e * z) * a := by rw [hαez]
    _ = a * (z * κ * e * z) * a := by simp only [mul_assoc]
    _ = a * (κ * e) * a := by rw [hzκez]
    _ = (a * κ) * e * a := by simp only [mul_assoc]
    _ = (κ * a) * e * a := by rw [haκ]
    _ = κ * (a * e * a) := by simp only [mul_assoc]

theorem sec51_h0_kappa {G : Type} [Group G] {a ε κ : G}
    (haκ : a * κ = κ * a) (h2 : κ * ε = ε * κ) :
    κ * (a * ε * a) = a * ε * a * κ := by
  calc κ * (a * ε * a) = (κ * a) * ε * a := by simp only [mul_assoc]
    _ = (a * κ) * ε * a := by rw [haκ]
    _ = a * (κ * ε) * a := by simp only [mul_assoc]
    _ = a * (ε * κ) * a := by rw [h2]
    _ = a * ε * (κ * a) := by simp only [mul_assoc]
    _ = a * ε * (a * κ) := by rw [haκ]
    _ = a * ε * a * κ := by simp only [mul_assoc]

theorem sec51_h0_alpha {G : Type} [Group G] {α a₀ : G} (hα : α * α = 1)
    (h5 : α * a₀ = a₀ * α) : α * a₀ * α = a₀ := by
  rw [h5, mul_assoc, hα, mul_one]

theorem sec51_h0_centralizes {G : Type} [Group G] {a β α a₀ ε κ z : G}
    (ha : a * a = 1) (hβ : β * β = 1) (hα : α * α = 1) (hκ : κ * κ = 1) (hz : z * z = 1)
    (haa₀ : a * a₀ = a₀ * a) (haκ : a * κ = κ * a) (hβa₀ : β * a₀ * β = ε * a₀)
    (hαε : α * ε * α = κ * ε) (haα : a * α * a = z * α)
    (h2 : κ * ε = ε * κ) (h3 : z * ε = ε * z) (h4 : z * κ = κ * z)
    (h5 : α * a₀ = a₀ * α) (h6 : α * z = z * α)
    (hβε : β * (a * ε * a) = (a * ε * a) * β) :
    α * ((β * (a * β * a)) * a₀ * (β * (a * β * a))⁻¹) =
      ((β * (a * β * a)) * a₀ * (β * (a * β * a))⁻¹) * α := by
  have hinv : (β * (a * β * a))⁻¹ = a * β * a * β := sec51_h0_inv ha hβ
  rw [hinv]
  have hx : β * (a * β * a) * a₀ * (a * β * a * β) = a * ε * a * (ε * a₀) := by
    calc β * (a * β * a) * a₀ * (a * β * a * β)
        = β * (a * β * a * a₀ * (a * β * a)) * β := by simp only [mul_assoc]
      _ = β * (a * ε * a * a₀) * β := by rw [sec51_h0_conj ha haa₀ hβa₀]
      _ = β * (a * ε * a) * a₀ * β := by simp only [mul_assoc]
      _ = a * ε * a * β * a₀ * β := by rw [hβε]
      _ = a * ε * a * (β * a₀ * β) := by simp only [mul_assoc]
      _ = a * ε * a * (ε * a₀) := by rw [hβa₀]
  rw [hx]
  have hL1 : α * (a * ε * a) * α = κ * (a * ε * a) :=
    sec51_claim1 ha hα hz hαε haα h2 h3 h4 haκ h6
  have hL2 : κ * (a * ε * a) = a * ε * a * κ := sec51_h0_kappa haκ h2
  have hL3 : α * a₀ * α = a₀ := sec51_h0_alpha hα h5
  have hcancel : (α * (a * ε * a) * α) * (α * ε * α) * (α * a₀ * α) =
      α * (a * ε * a * (ε * a₀)) * α := by
    calc (α * (a * ε * a) * α) * (α * ε * α) * (α * a₀ * α)
        = α * (a * ε * a) * (α * α) * ε * (α * α) * a₀ * α := by simp only [mul_assoc]
      _ = α * (a * ε * a) * 1 * ε * 1 * a₀ * α := by rw [hα]
      _ = α * (a * ε * a) * ε * a₀ * α := by simp only [mul_one]
      _ = α * (a * ε * a * (ε * a₀)) * α := by simp only [mul_assoc]
  have hkey : α * (a * ε * a * (ε * a₀)) * α = a * ε * a * (ε * a₀) := by
    rw [← hcancel, hL1, hαε, hL3, hL2]
    calc a * ε * a * κ * (κ * ε) * a₀
        = a * ε * a * (κ * κ) * ε * a₀ := by simp only [mul_assoc]
      _ = a * ε * a * 1 * ε * a₀ := by rw [hκ]
      _ = a * ε * a * (ε * a₀) := by simp only [mul_one, mul_assoc]
  calc α * (a * ε * a * (ε * a₀))
      = α * (a * ε * a * (ε * a₀)) * α * α := by simp only [mul_assoc, hα, mul_one]
    _ = a * ε * a * (ε * a₀) * α := by rw [hkey]

theorem sec51_fixed_decomp {G : Type} [Group G] {L L' : Subgroup G} {a : G}
    (ha : a * a = 1)
    (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) (hinf : L ⊓ L' = ⊥)
    (hLL' : ∀ x ∈ L, a * x * a ∈ L') (hL'L : ∀ y ∈ L', a * y * a ∈ L)
    {t : G} (ht : t ∈ L ⊔ L') (hat : a * t = t * a) :
    ∃ e ∈ L, t = e * (a * e * a) := by
  have hle : L' ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.RankThree.GF2n.le_normalizer_of_comm (fun x hx y hy => (hcomm y hy x hx).symm)
  obtain ⟨e, he, f, hf, rfl⟩ := CFSG.RankThree.GF2n.exists_mul_of_mem_sup hle ht
  have he' : a * f * a ∈ L := hL'L f hf
  have hg : a * e * a ∈ L' := hLL' e he
  have hcomm' : (a * f * a) * (a * e * a) = (a * e * a) * (a * f * a) :=
    hcomm _ he' _ hg
  have h1 : a * (e * f) * a = (a * e * a) * (a * f * a) := by
    calc a * (e * f) * a = a * e * (a * a) * f * a := by rw [ha]; group
      _ = (a * e * a) * (a * f * a) := by group
  have h2 : a * (e * f) * a = e * f := by
    calc a * (e * f) * a = e * f * a * a := by rw [hat]
      _ = e * f * (a * a) := by group
      _ = e * f := by rw [ha, mul_one]
  have h3 : e * f = (a * e * a) * (a * f * a) := h2.symm.trans h1
  have h4 : (a * f * a)⁻¹ * e = (a * e * a) * f⁻¹ := by
    calc (a * f * a)⁻¹ * e = (a * f * a)⁻¹ * (e * f) * f⁻¹ := by group
      _ = (a * f * a)⁻¹ * ((a * f * a) * (a * e * a)) * f⁻¹ := by rw [h3, hcomm']
      _ = (a * e * a) * f⁻¹ := by group
  have hmemL : (a * f * a)⁻¹ * e ∈ L := L.mul_mem (L.inv_mem he') he
  have hmemL' : (a * f * a)⁻¹ * e ∈ L' := by
    rw [h4]
    exact L'.mul_mem hg (L'.inv_mem hf)
  have h5 : (a * f * a)⁻¹ * e ∈ (⊥ : Subgroup G) := by
    rw [← hinf]
    exact Subgroup.mem_inf.mpr ⟨hmemL, hmemL'⟩
  rw [Subgroup.mem_bot] at h5
  have h6 : a * f * a = e := inv_mul_eq_one.mp h5
  have h7 : a * e * a = f := by
    calc a * e * a = a * (a * f * a) * a := by rw [h6]
      _ = (a * a) * f * (a * a) := by group
      _ = f := by rw [ha]; group
  refine ⟨e, he, ?_⟩
  rw [h7]

end Equational

section Transvection

variable {G : Type} [Group G]

theorem sec51_normalizer_le [Finite G] {A T : Subgroup G} (hTI : IsTI A) (hTA : T ≤ A)
    (hT : T ≠ ⊥) : normalizer (T : Set G) ≤ normalizer (A : Set G) := by
  intro g hg
  rw [← conjSubgroup_eq_self_iff]
  refine conjSubgroup_eq_of_isTI hTI fun h => hT ?_
  have hTg : conjSubgroup g T = T := conjSubgroup_eq_self_iff.mpr hg
  have hle : T ≤ A ⊓ conjSubgroup g A := le_inf hTA (by
    calc T = conjSubgroup g T := hTg.symm
      _ ≤ conjSubgroup g A := (conjSubgroup_le_conj_iff g).2 hTA)
  rw [h] at hle
  exact le_bot_iff.mp hle

structure Sec51Tr (A A₀ : Subgroup G) (a : G) : Prop where
  mem_normalizer : a ∈ normalizer (A : Set G)
  comm_zero : ∀ y ∈ A₀, a * y = y * a
  commutator_mem : ∀ x ∈ A, a * x * a⁻¹ * x⁻¹ ∈ A₀

namespace Sec51Tr

variable {A A₀ : Subgroup G}

theorem conj {b : G} (hb : Sec51Tr A A₀ b) {h : G} (hhA : h ∈ normalizer (A : Set G))
    (hhA₀ : h ∈ normalizer (A₀ : Set G)) : Sec51Tr A A₀ (h * b * h⁻¹) where
  mem_normalizer := Subgroup.mul_mem _ (Subgroup.mul_mem _ hhA hb.mem_normalizer)
    (Subgroup.inv_mem _ hhA)
  comm_zero := by
    intro y hy
    have hy' : h⁻¹ * y * h ∈ A₀ := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhA₀) y).mp hy
      simpa using this
    have h1 := hb.comm_zero _ hy'
    calc h * b * h⁻¹ * y = h * (b * (h⁻¹ * y * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * y * h) * b) * h⁻¹ := by rw [h1]
      _ = y * (h * b * h⁻¹) := by group
  commutator_mem := by
    intro x hx
    have hx' : h⁻¹ * x * h ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhA) x).mp hx
      simpa using this
    have h1 := hb.commutator_mem _ hx'
    have h2 := (Subgroup.mem_normalizer_iff.mp hhA₀ _).mp h1
    have e : h * (b * (h⁻¹ * x * h) * b⁻¹ * (h⁻¹ * x * h)⁻¹) * h⁻¹ =
        h * b * h⁻¹ * x * (h * b * h⁻¹)⁻¹ * x⁻¹ := by group
    rw [← e]
    exact h2

theorem mul_conj_comm (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA₀ : A₀ ≤ A) {a b : G}
    (ha : Sec51Tr A A₀ a) (hb : Sec51Tr A A₀ b) {x : G} (hx : x ∈ A) :
    a * b * x * (a * b)⁻¹ = b * a * x * (b * a)⁻¹ := by
  have hcb : b * x * b⁻¹ * x⁻¹ ∈ A₀ := hb.commutator_mem x hx
  have hca : a * x * a⁻¹ * x⁻¹ ∈ A₀ := ha.commutator_mem x hx
  have h1 : a * (b * x * b⁻¹ * x⁻¹) = (b * x * b⁻¹ * x⁻¹) * a := ha.comm_zero _ hcb
  have h2 : b * (a * x * a⁻¹ * x⁻¹) = (a * x * a⁻¹ * x⁻¹) * b := hb.comm_zero _ hca
  have h3 : (b * x * b⁻¹ * x⁻¹) * (a * x * a⁻¹ * x⁻¹) =
      (a * x * a⁻¹ * x⁻¹) * (b * x * b⁻¹ * x⁻¹) := hA _ (hA₀ hcb) _ (hA₀ hca)
  calc a * b * x * (a * b)⁻¹
      = a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) * x := by group
    _ = (b * x * b⁻¹ * x⁻¹) * (a * x * a⁻¹ * x⁻¹) * x := by rw [h1]; group
    _ = (a * x * a⁻¹ * x⁻¹) * (b * x * b⁻¹ * x⁻¹) * x := by rw [h3]
    _ = b * (a * x * a⁻¹ * x⁻¹) * b⁻¹ * (b * x * b⁻¹ * x⁻¹) * x := by rw [h2]; group
    _ = b * a * x * (b * a)⁻¹ := by group

theorem sq_comm (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA₀ : A₀ ≤ A) {a b : G}
    (ha2 : a * a = 1) (hb2 : b * b = 1) (ha : Sec51Tr A A₀ a) (hb : Sec51Tr A A₀ b) {x : G}
    (hx : x ∈ A) : (a * b) * (a * b) * x = x * ((a * b) * (a * b)) := by
  have hui : (a * b)⁻¹ = b * a := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hb2]
  have E := mul_conj_comm hA hA₀ ha hb hx
  rw [← hui, inv_inv] at E
  calc (a * b) * (a * b) * x = (a * b) * ((a * b) * x * (a * b)⁻¹) * (a * b) := by group
    _ = (a * b) * ((a * b)⁻¹ * x * (a * b)) * (a * b) := by rw [E]
    _ = x * ((a * b) * (a * b)) := by group

end Sec51Tr

theorem sec51_dih4 {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hord : orderOf (a * b) = 4) :
    (a * b) * (a * b) ≠ 1 ∧ ((a * b) * (a * b)) * ((a * b) * (a * b)) = 1 ∧
      a * ((a * b) * (a * b)) = ((a * b) * (a * b)) * a ∧
      b * ((a * b) * (a * b)) = ((a * b) * (a * b)) * b ∧
      a * b * a = ((a * b) * (a * b)) * b := by
  have hw1 : (a * b) * (a * b) ≠ 1 := by
    intro h
    have h2 : (a * b) ^ 2 = 1 := by rw [pow_two]; exact h
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at this
    omega
  have hww : ((a * b) * (a * b)) * ((a * b) * (a * b)) = 1 := by
    have h4 : (a * b) ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    calc ((a * b) * (a * b)) * ((a * b) * (a * b)) = (a * b) ^ 4 := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h4
  have hwi : ((a * b) * (a * b))⁻¹ = (a * b) * (a * b) := inv_eq_of_mul_eq_one_right hww
  have hui : (a * b)⁻¹ = b * a := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
  have hwi' : (b * a) * (b * a) = (a * b) * (a * b) := by
    rw [← hwi, mul_inv_rev, hui]
  refine ⟨hw1, hww, ?_, ?_, ?_⟩
  · have e : a * ((a * b) * (a * b)) * a = (a * b) * (a * b) := by
      calc a * ((a * b) * (a * b)) * a = (a * a) * b * (a * b) * a := by group
        _ = (b * a) * (b * a) := by rw [ha, one_mul]; group
        _ = (a * b) * (a * b) := hwi'
    calc a * ((a * b) * (a * b)) = a * ((a * b) * (a * b)) * a * a := by
          rw [mul_assoc _ a a, ha, mul_one]
      _ = ((a * b) * (a * b)) * a := by rw [e]
  · have e : b * ((a * b) * (a * b)) * b = (a * b) * (a * b) := by
      calc b * ((a * b) * (a * b)) * b = b * a * b * a * (b * b) := by group
        _ = (b * a) * (b * a) := by rw [hb, mul_one]; group
        _ = (a * b) * (a * b) := hwi'
    calc b * ((a * b) * (a * b)) = b * ((a * b) * (a * b)) * b * b := by
          rw [mul_assoc _ b b, hb, mul_one]
      _ = ((a * b) * (a * b)) * b := by rw [e]
  · calc a * b * a = a * b * a * (b * b) := by rw [hb, mul_one]
      _ = ((a * b) * (a * b)) * b := by group

theorem sec51_bender_aux {K : Type} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) {p w u : K}
    (hp : orderOf p = 2) (hw : orderOf w = 2) (hu : orderOf u = 2) (hwu : Commute w u)
    (hpw : Commute p (w * p * w)) (hnc : ¬ Commute p u) : False := by
  have hsq : ∀ x : K, orderOf x = 2 → x * x = 1 := fun x hx => by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hpp := hsq p hp
  have hww := hsq w hw
  by_cases hfix : w * p * w = p
  · have hpw' : Commute p w := by
      show p * w = w * p
      calc p * w = (w * p * w) * w := by rw [hfix]
        _ = w * p := by rw [mul_assoc, hww, mul_one]
    exact hnc (CFSG.Timmesfeld.Bridge.OddLocal.IsBenderGroup.commute_trans hK hp hw hu hpw' hwu)
  · obtain ⟨p', hp'⟩ : ∃ p', p' = w * p * w := ⟨_, rfl⟩
    rw [← hp'] at hpw hfix
    have hp'2 : p' * p' = 1 := by
      calc p' * p' = w * p * (w * w) * p * w := by rw [hp']; group
        _ = w * (p * p) * w := by rw [hww, mul_one]; group
        _ = 1 := by rw [hpp, mul_one, hww]
    have hpp' : p * p' = p' * p := hpw.eq
    have hne' : p ≠ p' := fun h => hfix h.symm
    obtain ⟨e, he⟩ : ∃ e, e = p * p' := ⟨_, rfl⟩
    have hee : e * e = 1 := by
      calc e * e = p * (p' * p) * p' := by rw [he]; group
        _ = p * (p * p') * p' := by rw [← hpp']
        _ = (p * p) * (p' * p') := by group
        _ = 1 := by rw [hpp, hp'2, one_mul]
    have he1 : e ≠ 1 := by
      intro h
      apply hne'
      calc p = p * (p' * p') := by rw [hp'2, mul_one]
        _ = (p * p') * p' := by group
        _ = p' := by rw [← he, h, one_mul]
    have heo : orderOf e = 2 := orderOf_eq_prime (by rw [pow_two]; exact hee) he1
    have hpe : Commute p e := by
      show p * e = e * p
      rw [he]
      calc p * (p * p') = p * (p' * p) := by rw [hpp']
        _ = (p * p') * p := by group
    have hwp' : w * p' * w = p := by
      calc w * p' * w = (w * w) * p * (w * w) := by rw [hp']; group
        _ = p := by rw [hww, one_mul, mul_one]
    have hwe : Commute e w := by
      show e * w = w * e
      have h1 : w * e * w = e := by
        calc w * e * w = (w * p * w) * (w * p' * w) := by
              rw [he]
              calc w * (p * p') * w = w * p * (w * w) * p' * w := by
                    rw [hww, mul_one]
                    group
                _ = (w * p * w) * (w * p' * w) := by group
          _ = p' * p := by rw [← hp', hwp']
          _ = e := by rw [he, hpp']
      calc e * w = w * e * w * w := by rw [h1]
        _ = w * e := by rw [mul_assoc, hww, mul_one]
    have hpw2 : Commute p w :=
      CFSG.Timmesfeld.Bridge.OddLocal.IsBenderGroup.commute_trans hK hp heo hw hpe hwe
    exact hnc (CFSG.Timmesfeld.Bridge.OddLocal.IsBenderGroup.commute_trans hK hp hw hu hpw2 hwu)

theorem sec51_bender_contra {K : Type} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) {p u v : K}
    (hp : orderOf p = 2) (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huv : Commute u v) (hne : u ≠ v)
    (hpw : Commute p ((u * v) * p * (u * v)⁻¹)) (hnc : ¬ Commute p u) : False := by
  have hsq : ∀ x : K, orderOf x = 2 → x * x = 1 := fun x hx => by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have huu := hsq u hu
  have hvv := hsq v hv
  have huv' : u * v = v * u := huv.eq
  have hww : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [← huv']
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [huu, hvv, one_mul]
  have hw1 : u * v ≠ 1 := by
    intro h
    apply hne
    calc u = u * (v * v) := by rw [hvv, mul_one]
      _ = (u * v) * v := by group
      _ = v := by rw [h, one_mul]
  have hw : orderOf (u * v) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
  have hwi : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right hww
  have hwu : Commute (u * v) u := by
    show u * v * u = u * (u * v)
    calc u * v * u = u * (v * u) := by group
      _ = u * (u * v) := by rw [← huv']
  rw [hwi] at hpw
  exact sec51_bender_aux hK hp hw hu hwu hpw hnc

theorem sec51_eq_one_of_odd {S : Subgroup G} (hS : IsPGroup 2 S) {x : G} (hx : x ∈ S)
    (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨x, hx⟩
  have hpow : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hpow)
  rcases i with _ | i
  · exact orderOf_eq_one_iff.1 (by simpa using hi)
  · rw [hi, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.not_odd_iff_even])

theorem sec51_isElemAbelian_of_le {E E₀ : Subgroup G} (hE : IsElemAbelian 2 E) (h : E₀ ≤ E) :
    IsElemAbelian 2 E₀ :=
  ⟨⟨⟨fun x y => Subtype.ext (congrArg (fun z : ↥E => (z : G))
    (hE.1.is_comm.comm ⟨x, h x.2⟩ ⟨y, h y.2⟩))⟩⟩, fun x hx => hE.2 x (h hx)⟩

theorem sec51_cancel_comm {c a x : G} (hca : a * c = c * a) (h : a * (c * x) = (c * x) * a) :
    a * x = x * a := by
  apply mul_left_cancel (a := c)
  calc c * (a * x) = (c * a) * x := (mul_assoc _ _ _).symm
    _ = (a * c) * x := by rw [hca]
    _ = a * (c * x) := mul_assoc _ _ _
    _ = (c * x) * a := h
    _ = c * (x * a) := mul_assoc _ _ _

theorem sec51_swap_L {Abar L L' M' : Subgroup G} {a : G} (ha2 : a * a = 1)
    (P : Prop24Setup Abar (conjSubgroup a Abar) L L' M') :
    (∀ x ∈ L, a * x * a ∈ L') ∧ (∀ y ∈ L', a * y * a ∈ L) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  constructor
  · intro x hx
    obtain ⟨hxA, hxN⟩ := P.mem_L.mp hx
    rw [P.mem_Lb]
    refine ⟨?_, ?_⟩
    · have := (mem_conjSubgroup_conj_t77 a x Abar).2 hxA
      rwa [hai] at this
    · rw [← conjSubgroup_map_normalizer, mem_conjSubgroup] at hxN
      rwa [hai] at hxN
  · intro y hy
    obtain ⟨hyC, hyN⟩ := P.mem_Lb.mp hy
    rw [P.mem_L]
    refine ⟨?_, ?_⟩
    · have := mem_conjSubgroup.mp hyC
      rwa [hai] at this
    · have h1 : a * y * a⁻¹ ∈ conjSubgroup a (normalizer (Abar : Set G)) :=
        (mem_conjSubgroup_conj_t77 a y _).2 hyN
      rw [conjSubgroup_map_normalizer, hai] at h1
      exact h1

theorem sec51_swap_M [Finite G] {Abar L L' M' : Subgroup G} {a : G} (ha2 : a * a = 1)
    (P : Prop24Setup Abar (conjSubgroup a Abar) L L' M') :
    a ∈ normalizer (M' : Set G) := by
  obtain ⟨hLL', hL'L⟩ := sec51_swap_L ha2 P
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have key : ∀ m ∈ M', a * m * a⁻¹ ∈ M' := by
    intro m hm
    obtain ⟨e, he, f, hf, rfl⟩ := P.exists_mul_of_mem_M hm
    have e1 : a * (e * f) * a⁻¹ = (a * e * a) * (a * f * a) := by
      rw [hai]
      calc a * (e * f) * a = a * e * (a * a) * f * a := by rw [ha2]; group
        _ = (a * e * a) * (a * f * a) := by group
    rw [e1]
    exact M'.mul_mem (P.Lb_le_M (hLL' e he)) (P.L_le_M (hL'L f hf))
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key x, fun hx => ?_⟩
  have := key _ hx
  rwa [show a * (a * x * a⁻¹) * a⁻¹ = x by
    rw [hai]; calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
      _ = x := by rw [ha2]; group] at this

theorem sec51_conj_of_conj {X Y : Subgroup G} {k : G} (h : Y = conjSubgroup k X) :
    ∃ k' : G, X = conjSubgroup k' Y := ⟨k⁻¹, by rw [h, conjSubgroup_inv_conj_cancel]⟩

theorem sec51_comm_of_le_normalizer [Finite G] {T U : Subgroup G} (hTel : IsElemAbelian 2 T)
    (hTTI : IsTI T) (hU : ∃ k : G, U = conjSubgroup k T) (hUN : U ≤ normalizer (T : Set G)) :
    ∀ x ∈ T, ∀ y ∈ U, x * y = y * x := by
  obtain ⟨k, rfl⟩ := hU
  have hel := tim77_2_3 hTel hTTI hUN
  intro x hx y hy
  exact congrArg (fun z : ↥(T ⊔ conjSubgroup k T) => (z : G))
    (hel.1.is_comm.comm ⟨x, Subgroup.mem_sup_left hx⟩ ⟨y, Subgroup.mem_sup_right hy⟩)

end Transvection

end CFSG.RankThree.GF2n.Tim77
