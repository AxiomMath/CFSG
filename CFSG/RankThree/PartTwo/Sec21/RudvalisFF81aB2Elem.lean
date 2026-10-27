module

public import CFSG.RankThree.Transfer.WeaklyClosedPrime
import CFSG.RankThree.PartOne.NF7J.EvenCount

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem

open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h x
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have := (MulAut.conj g).injective (hyx.trans rfl)
      simpa using this
    exact this ▸ hy

theorem exists_pow_eq_zpow {x : G} (hx : x ^ 3 = 1) (k : ℤ) : ∃ n : ℕ, n < 3 ∧ x ^ k = x ^ n := by
  refine ⟨(k % 3).toNat, ?_, ?_⟩
  · have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
    have h3 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  · rw [zpow_eq_zpow_emod' k hx, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    rfl

section Coords

variable {b₁ b₂ b₃ : G}

@[expose] def coord (b₁ b₂ b₃ : G) (v : Fin 3 × Fin 3 × Fin 3) : G :=
  b₁ ^ (v.1 : ℕ) * b₂ ^ (v.2.1 : ℕ) * b₃ ^ (v.2.2 : ℕ)

theorem coord_mem (v : Fin 3 × Fin 3 × Fin 3) :
    coord b₁ b₂ b₃ v ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) := by
  have h1 : b₁ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) := Subgroup.subset_closure (by simp)
  have h2 : b₂ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) := Subgroup.subset_closure (by simp)
  have h3 : b₃ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) := Subgroup.subset_closure (by simp)
  exact mul_mem (mul_mem (pow_mem h1 _) (pow_mem h2 _)) (pow_mem h3 _)

variable (h12 : b₁ * b₂ = b₂ * b₁) (h13 : b₁ * b₃ = b₃ * b₁) (h23 : b₂ * b₃ = b₃ * b₂)
  (h1 : b₁ ^ 3 = 1) (h2 : b₂ ^ 3 = 1) (h3 : b₃ ^ 3 = 1)
include h12 h13 h23 h1 h2 h3

theorem exists_coord {z : G} (hz : z ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G)) :
    ∃ v, coord b₁ b₂ b₃ v = z := by
  obtain ⟨v, hv⟩ := CFSG.RankThree.PartOne.NF7J.mem_range_of_closure b₁ b₂ b₃ h12 h13 h23 h1 h2
    h3 hz
  exact ⟨v, hv⟩

theorem coord_injective (hcard : Nat.card (Subgroup.closure ({b₁, b₂, b₃} : Set G)) = 27) :
    Function.Injective (coord b₁ b₂ b₃) := by
  set B₁ := Subgroup.closure ({b₁, b₂, b₃} : Set G)
  let f : Fin 3 × Fin 3 × Fin 3 → B₁ := fun v => ⟨coord b₁ b₂ b₃ v, coord_mem v⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨v, hv⟩ := exists_coord h12 h13 h23 h1 h2 h3 hz
    exact ⟨v, Subtype.ext hv⟩
  have hbij := hf.bijective_of_nat_card_le (by rw [hcard]; simp)
  intro v w hvw
  exact hbij.1 (Subtype.ext hvw)

end Coords

theorem card_cen_cycle_le {b₁ b₂ b₃ c : G} (h12 : b₁ * b₂ = b₂ * b₁) (h13 : b₁ * b₃ = b₃ * b₁)
    (h23 : b₂ * b₃ = b₃ * b₂) (h1 : b₁ ^ 3 = 1) (h2 : b₂ ^ 3 = 1) (h3 : b₃ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.closure ({b₁, b₂, b₃} : Set G)) = 27)
    (hc₁ : c * b₁ * c⁻¹ = b₂) (hc₂ : c * b₂ * c⁻¹ = b₃) (hc₃ : c * b₃ * c⁻¹ = b₁)
    {r : ℕ} (hr : r = 1 ∨ r = 2) :
    Nat.card ↥(Subgroup.closure ({b₁, b₂, b₃} : Set G) ⊓
      Subgroup.centralizer ({c ^ r} : Set G)) ≤ 3 := by
  have hinj := coord_injective h12 h13 h23 h1 h2 h3 hcard
  have hconj : ∀ v : Fin 3 × Fin 3 × Fin 3,
      c * coord b₁ b₂ b₃ v * c⁻¹ = coord b₁ b₂ b₃ (v.2.2, v.1, v.2.1) := by
    rintro ⟨l, m, n⟩
    have e := congrArg (fun x => x) (rfl : (MulAut.conj c) (coord b₁ b₂ b₃ (l, m, n)) =
      (MulAut.conj c) (coord b₁ b₂ b₃ (l, m, n)))
    have key : (MulAut.conj c) (coord b₁ b₂ b₃ (l, m, n)) =
        b₂ ^ (l : ℕ) * b₃ ^ (m : ℕ) * b₁ ^ (n : ℕ) := by
      simp only [coord, map_mul, map_pow, MulAut.conj_apply, hc₁, hc₂, hc₃]
    rw [MulAut.conj_apply] at key
    rw [key]
    simp only [coord]
    have c12 : Commute b₁ b₂ := h12
    have c13 : Commute b₁ b₃ := h13
    have c23 : Commute b₂ b₃ := h23
    have e1 : Commute (b₁ ^ (n : ℕ)) (b₂ ^ (l : ℕ)) := (c12.pow_pow _ _)
    have e2 : Commute (b₁ ^ (n : ℕ)) (b₃ ^ (m : ℕ)) := (c13.pow_pow _ _)
    calc b₂ ^ (l : ℕ) * b₃ ^ (m : ℕ) * b₁ ^ (n : ℕ)
        = b₂ ^ (l : ℕ) * (b₁ ^ (n : ℕ) * b₃ ^ (m : ℕ)) := by rw [mul_assoc, e2.eq]
      _ = b₁ ^ (n : ℕ) * b₂ ^ (l : ℕ) * b₃ ^ (m : ℕ) := by
        rw [← mul_assoc, ← e1.eq]
  have hfix : ∀ v : Fin 3 × Fin 3 × Fin 3, c ^ r * coord b₁ b₂ b₃ v * (c ^ r)⁻¹ =
      coord b₁ b₂ b₃ v → v.1 = v.2.1 ∧ v.2.1 = v.2.2 := by
    rintro ⟨l, m, n⟩ hv
    rcases hr with rfl | rfl
    · rw [pow_one, hconj] at hv
      have := hinj hv
      simp only [Prod.mk.injEq] at this
      exact ⟨this.2.1, this.2.2⟩
    · have e2 : c ^ 2 * coord b₁ b₂ b₃ (l, m, n) * (c ^ 2)⁻¹ = coord b₁ b₂ b₃ (m, n, l) := by
        calc c ^ 2 * coord b₁ b₂ b₃ (l, m, n) * (c ^ 2)⁻¹
            = c * (c * coord b₁ b₂ b₃ (l, m, n) * c⁻¹) * c⁻¹ := by
              simp only [pow_two, mul_inv_rev, mul_assoc]
          _ = coord b₁ b₂ b₃ (m, n, l) := by rw [hconj, hconj]
      rw [e2] at hv
      have := hinj hv
      simp only [Prod.mk.injEq] at this
      exact ⟨this.1.symm, this.2.1.symm⟩
  have hsub : ∀ z ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) ⊓
      Subgroup.centralizer ({c ^ r} : Set G),
      z ∈ Set.range (fun l : Fin 3 => coord b₁ b₂ b₃ (l, l, l)) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨⟨l, m, n⟩, rfl⟩ := exists_coord h12 h13 h23 h1 h2 h3 hz1
    have hcz : c ^ r * coord b₁ b₂ b₃ (l, m, n) * (c ^ r)⁻¹ = coord b₁ b₂ b₃ (l, m, n) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hz2
      rw [← this, mul_inv_cancel_right]
    obtain ⟨hlm, hmn⟩ := hfix _ hcz
    simp only at hlm hmn
    subst hmn
    subst hlm
    exact ⟨l, rfl⟩
  calc Nat.card ↥(Subgroup.closure ({b₁, b₂, b₃} : Set G) ⊓
        Subgroup.centralizer ({c ^ r} : Set G))
      ≤ Nat.card (Set.range (fun l : Fin 3 => coord b₁ b₂ b₃ (l, l, l))) :=
        Nat.card_mono (Set.toFinite _) fun z hz => hsub z hz
    _ ≤ Nat.card (Fin 3) := Finite.card_range_le _
    _ = 3 := Nat.card_fin 3

section Cube

variable {b : G} {W B₂ : Subgroup G}

theorem pow_mul_cube (hb3 : b ^ 3 = 1) (hbW : ∀ y ∈ W, b * y = y * b) (hWB₂ : W ≤ B₂)
    (hW3 : ∀ y ∈ W, y ^ 3 = 1) (hB₂ab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x)
    (hbB₂ : ∀ x ∈ B₂, b * x * b⁻¹ * x⁻¹ ∈ W) {x : G} (hx : x ∈ B₂) (n : ℕ) :
    (b ^ n * x) ^ 3 = x ^ 3 := by
  set d := b * x * b⁻¹ * x⁻¹ with hd
  have hdW : d ∈ W := hbB₂ x hx
  have hbx : b * x * b⁻¹ = d * x := by rw [hd, inv_mul_cancel_right]
  have hbd : b * d = d * b := hbW d hdW
  have key : ∀ k : ℕ, b ^ k * x * (b ^ k)⁻¹ = d ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hbdk : b * d ^ k * b⁻¹ = d ^ k := by
        rw [(Commute.pow_right hbd k).eq, mul_inv_cancel_right]
      calc b ^ (k + 1) * x * (b ^ (k + 1))⁻¹ = b * (b ^ k * x * (b ^ k)⁻¹) * b⁻¹ := by
            rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
        _ = b * (d ^ k * x) * b⁻¹ := by rw [ih]
        _ = (b * d ^ k * b⁻¹) * (b * x * b⁻¹) := by group
        _ = d ^ (k + 1) * x := by rw [hbdk, hbx, pow_succ, ← mul_assoc]
  have hs3 : (b ^ n) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hb3, one_pow]
  have hid : (b ^ n * x) ^ 3 = (b ^ n * x * (b ^ n)⁻¹) * ((b ^ n) ^ 2 * x * ((b ^ n) ^ 2)⁻¹) *
      ((b ^ n) ^ 3 * x) := by
    set s := b ^ n
    rw [pow_three, pow_two, pow_three]
    group
  have hdB₂ : ∀ k : ℕ, d ^ k ∈ B₂ := fun k => pow_mem (hWB₂ hdW) k
  have hcomm : ∀ k : ℕ, d ^ k * x = x * d ^ k := fun k => hB₂ab _ (hdB₂ k) x hx
  rw [hid, hs3, one_mul, key n, ← pow_mul, key (n * 2)]
  have hd3 : d ^ (n + n * 2) = 1 := by
    rw [show n + n * 2 = 3 * n by ring, pow_mul, hW3 d hdW, one_pow]
  have e1 : x * d ^ (n * 2) = d ^ (n * 2) * x := (hcomm (n * 2)).symm
  calc d ^ n * x * (d ^ (n * 2) * x) * x
      = d ^ n * (x * d ^ (n * 2)) * x * x := by simp only [mul_assoc]
    _ = d ^ n * (d ^ (n * 2) * x) * x * x := by rw [e1]
    _ = d ^ n * d ^ (n * 2) * (x * x * x) := by simp only [mul_assoc]
    _ = x ^ 3 := by rw [← pow_add, hd3, one_mul, pow_three, mul_assoc]

end Cube

theorem zpowers_le_normalizer {H : Subgroup G} {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    Subgroup.zpowers g ≤ Subgroup.normalizer (H : Set G) :=
  (Subgroup.zpowers_le).2 (mem_normalizer_of_conj_mem h)

theorem exists_of_mem_A {b : G} {B₂ : Subgroup G} (hb3 : b ^ 3 = 1)
    (hbn : ∀ x ∈ B₂, b * x * b⁻¹ ∈ B₂) {y : G} (hy : y ∈ Subgroup.zpowers b ⊔ B₂) :
    ∃ n : ℕ, n < 3 ∧ ∃ x ∈ B₂, y = b ^ n * x := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers b) B₂
    (zpowers_le_normalizer hbn)
  have hy' : y ∈ ((Subgroup.zpowers b : Set G) * (B₂ : Set G)) := by
    rw [← hset]; exact hy
  obtain ⟨u, hu, x, hx, rfl⟩ := Set.mem_mul.mp hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨n, hn, e⟩ := exists_pow_eq_zpow hb3 k
  exact ⟨n, hn, x, hx, by rw [e]⟩

theorem exists_of_mem_P {c : G} {A : Subgroup G} (hcn : ∀ x ∈ A, c * x * c⁻¹ ∈ A)
    (hc3 : c ^ 3 ∈ A) {y : G} (hy : y ∈ A ⊔ Subgroup.zpowers c) :
    ∃ r : ℕ, r < 3 ∧ ∃ a ∈ A, y = c ^ r * a := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers c) A
    (zpowers_le_normalizer hcn)
  have hy' : y ∈ ((Subgroup.zpowers c : Set G) * (A : Set G)) := by
    rw [← hset, sup_comm]; exact hy
  obtain ⟨u, hu, a, ha, rfl⟩ := Set.mem_mul.mp hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hr0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have hr3 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  refine ⟨(k % 3).toNat, by omega, (c ^ 3) ^ (k / 3) * a, mul_mem (zpow_mem hc3 _) ha, ?_⟩
  have e1 : c ^ k = c ^ (k % 3) * (c ^ 3) ^ (k / 3) := by
    rw [← zpow_natCast c 3, ← zpow_mul, ← zpow_add, Nat.cast_ofNat, Int.emod_add_mul_ediv]
  rw [e1, mul_assoc]
  congr 1
  rw [← zpow_natCast, Int.toNat_of_nonneg hr0]

section Main

variable {b b₁ b₂ b₃ c : G} {B₂ : Subgroup G}

theorem B₁_le_B : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤
    Subgroup.closure ({b, b₁, b₂, b₃} : Set G) :=
  Subgroup.closure_mono (by intro x hx; simp only [Set.mem_insert_iff] at hx ⊢; tauto)

theorem b_mem_B : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem mem_B_of_cube (hb3 : b ^ 3 = 1)
    (hbB₁ : ∀ y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), b * y = y * b)
    (hB₁B₂ : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ B₂)
    (hB₁3 : ∀ y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), y ^ 3 = 1)
    (hB₂ab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x)
    (hbB₂ : ∀ x ∈ B₂, b * x * b⁻¹ * x⁻¹ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hΩ : ∀ x ∈ B₂, x ^ 3 = 1 → x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    {y : G} (hy : y ∈ Subgroup.zpowers b ⊔ B₂) (hy3 : y ^ 3 = 1) :
    y ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G) := by
  have hbn : ∀ x ∈ B₂, b * x * b⁻¹ ∈ B₂ := fun x hx => by
    have := mul_mem (hB₁B₂ (hbB₂ x hx)) hx
    rwa [inv_mul_cancel_right] at this
  obtain ⟨n, -, x, hx, rfl⟩ := exists_of_mem_A hb3 hbn hy
  rw [pow_mul_cube hb3 hbB₁ hB₁B₂ hB₁3 hB₂ab hbB₂ hx n] at hy3
  exact mul_mem (pow_mem b_mem_B n) (B₁_le_B (hΩ x hx hy3))

end Main

section Inputs

variable {b b₁ b₂ b₃ c : G}

theorem cube_mem_centralizer (hcb : c * b * c⁻¹ = b) (hc₁ : c * b₁ * c⁻¹ = b₂)
    (hc₂ : c * b₂ * c⁻¹ = b₃) (hc₃ : c * b₃ * c⁻¹ = b₁) :
    c ^ 3 ∈ Subgroup.centralizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G) := by
  have e : ∀ x : G, c ^ 3 * x * (c ^ 3)⁻¹ = c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ := by
    intro x
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
  have key : ∀ x ∈ ({b, b₁, b₂, b₃} : Set G), x * c ^ 3 = c ^ 3 * x := by
    intro x hx
    have h : c ^ 3 * x * (c ^ 3)⁻¹ = x := by
      rcases hx with rfl | rfl | rfl | rfl
      · rw [e, hcb, hcb, hcb]
      · rw [e, hc₁, hc₂, hc₃]
      · rw [e, hc₂, hc₃, hc₁]
      · rw [e, hc₃, hc₁, hc₂]
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hle : Subgroup.closure ({b, b₁, b₂, b₃} : Set G) ≤
      Subgroup.centralizer ({c ^ 3} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (key x hx)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem exists_pow_isPGroup (hcb : c * b * c⁻¹ = b) (hc₁ : c * b₁ * c⁻¹ = b₂)
    (hc₂ : c * b₂ * c⁻¹ = b₃) (hc₃ : c * b₃ * c⁻¹ = b₁) :
    ∃ m : ℕ, IsPGroup 3 (Subgroup.zpowers (c ^ m)) ∧ c ^ m * b * (c ^ m)⁻¹ = b ∧
      c ^ m * b₁ * (c ^ m)⁻¹ = b₂ ∧ c ^ m * b₂ * (c ^ m)⁻¹ = b₃ ∧
      c ^ m * b₃ * (c ^ m)⁻¹ = b₁ := by
  obtain ⟨a, k, hk3, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' 3 (by norm_num)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (k * j) % 3 = 1 := by
    rcases (by omega : k % 3 = 1 ∨ k % 3 = 2) with h | h
    · exact ⟨1, by rw [mul_one]; exact h⟩
    · exact ⟨2, by rw [Nat.mul_mod, h]⟩
  have hcm : (c ^ (k * j)) ^ (3 ^ a) = 1 := by
    rw [← pow_mul, show k * j * 3 ^ a = (3 ^ a * k) * j by ring, pow_mul, ← hk,
      pow_orderOf_eq_one, one_pow]
  have hcen := cube_mem_centralizer hcb hc₁ hc₂ hc₃
  have hconj : ∀ x ∈ ({b, b₁, b₂, b₃} : Set G),
      c ^ (k * j) * x * (c ^ (k * j))⁻¹ = c * x * c⁻¹ := by
    intro x hx
    have hxc : Commute x (c ^ 3) :=
      Subgroup.mem_centralizer_iff.mp hcen x (Subgroup.subset_closure hx)
    have hm : k * j = 3 * (k * j / 3) + 1 := by omega
    rw [hm, pow_succ', pow_mul]
    set y := (c ^ 3) ^ (k * j / 3)
    have hy : y * x = x * y := (hxc.symm.pow_left (k * j / 3)).eq
    calc c * y * x * (c * y)⁻¹ = c * (y * x) * y⁻¹ * c⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = c * (x * y) * y⁻¹ * c⁻¹ := by rw [hy]
      _ = c * x * c⁻¹ := by simp only [mul_assoc, mul_inv_cancel_left]
  refine ⟨k * j, fun g => ⟨a, ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hz, ← zpow_natCast, ← zpow_mul, mul_comm z,
      zpow_mul, zpow_natCast, hcm, one_zpow]
  · rw [hconj b (by simp), hcb]
  · rw [hconj b₁ (by simp), hc₁]
  · rw [hconj b₂ (by simp), hc₂]
  · rw [hconj b₃ (by simp), hc₃]

theorem cube_mem_A {B₂ : Subgroup G} (hB₁B₂ : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ B₂)
    (hcb : c * b * c⁻¹ = b) (hc₁ : c * b₁ * c⁻¹ = b₂) (hc₂ : c * b₂ * c⁻¹ = b₃)
    (hc₃ : c * b₃ * c⁻¹ = b₁) (hcp : IsPGroup 3 (Subgroup.zpowers c))
    (hCB : ∀ x ∈ Subgroup.centralizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G),
      IsPGroup 3 (Subgroup.zpowers x) → x ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) :
    c ^ 3 ∈ Subgroup.zpowers b ⊔ B₂ := by
  have hmem := hCB _ (cube_mem_centralizer hcb hc₁ hc₂ hc₃)
    (hcp.to_le (Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers c) 3)))
  refine (Subgroup.closure_le _).2 ?_ hmem
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · exact Subgroup.mem_sup_right (hB₁B₂ (Subgroup.subset_closure (by simp)))
  · exact Subgroup.mem_sup_right (hB₁B₂ (Subgroup.subset_closure (by simp)))
  · exact Subgroup.mem_sup_right (hB₁B₂ (Subgroup.subset_closure (by simp)))

end Inputs

theorem exists_cube_eq {B₁ B₂ : Subgroup G} (hB₁B₂ : B₁ ≤ B₂)
    (hB₂ab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x) (hB₂3 : ∀ x ∈ B₂, x ^ 3 ∈ B₁)
    (hB₁3 : ∀ y ∈ B₁, y ^ 3 = 1) (hΩ : ∀ x ∈ B₂, x ^ 3 = 1 → x ∈ B₁)
    (hcard : Nat.card B₂ = Nat.card B₁ * Nat.card B₁) {y : G} (hy : y ∈ B₁) :
    ∃ x ∈ B₂, x ^ 3 = y := by
  let φ : ↥B₂ →* ↥B₂ :=
    { toFun := fun x => x ^ 3
      map_one' := one_pow 3
      map_mul' := fun x y => (Commute.mul_pow (Subtype.ext (hB₂ab x x.2 y y.2)) 3) }
  have hker : φ.ker = B₁.subgroupOf B₂ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change x ^ 3 = 1 ↔ (x : G) ∈ B₁
    constructor
    · intro hx
      exact hΩ x x.2 (by simpa using congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext (by simpa using hB₁3 x hx)
  have hrange : φ.range ≤ B₁.subgroupOf B₂ := by
    rintro _ ⟨x, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (hB₂3 x x.2)
  have hc1 : Nat.card φ.range * Nat.card φ.ker = Nat.card B₂ := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker).symm
  have hsub : Nat.card (B₁.subgroupOf B₂) = Nat.card B₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁B₂).toEquiv
  rw [hker, hsub, hcard] at hc1
  have hpos : 0 < Nat.card B₁ := Nat.card_pos
  have hr : Nat.card φ.range = Nat.card B₁ := Nat.eq_of_mul_eq_mul_right hpos hc1
  have heq : φ.range = B₁.subgroupOf B₂ :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hr, hsub])
  have hmem : (⟨y, hB₁B₂ hy⟩ : ↥B₂) ∈ φ.range := by
    rw [heq, Subgroup.mem_subgroupOf]
    exact hy
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem conj_cube_eq {B₁ B₂ : Subgroup G} (hB₁B₂ : B₁ ≤ B₂)
    (hB₂ab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x) (hB₁3 : ∀ y ∈ B₁, y ^ 3 = 1) {s : G}
    (hs : ∀ x ∈ B₂, s * x * s⁻¹ * x⁻¹ ∈ B₁) {x : G} (hx : x ∈ B₂) :
    s * x ^ 3 * s⁻¹ = x ^ 3 := by
  have hw := hs x hx
  set w := s * x * s⁻¹ * x⁻¹ with hwdef
  have hsx : s * x * s⁻¹ = w * x := by rw [hwdef, inv_mul_cancel_right]
  have hwx : Commute w x := hB₂ab w (hB₁B₂ hw) x hx
  rw [show s * x ^ 3 * s⁻¹ = (s * x * s⁻¹) ^ 3 by
    rw [show s * x * s⁻¹ = s * x * s⁻¹ by rfl, conj_pow], hsx, hwx.mul_pow, hB₁3 w hw, one_mul]

structure Setup (b b₁ b₂ b₃ c : G) (B₂ : Subgroup G) : Prop where
  Bab : ∀ x ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G),
    ∀ y ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G), x * y = y * x
  B3 : ∀ x ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G), x ^ 3 = 1
  Bcard : Nat.card (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) = 81
  B₁card : Nat.card (Subgroup.closure ({b₁, b₂, b₃} : Set G)) = 27
  B₁B₂ : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ B₂
  B₂ab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x
  B₂3 : ∀ x ∈ B₂, x ^ 3 ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G)
  B₂N : B₂ ≤ Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G)
  bB₂ : ∀ x ∈ B₂, b * x * b⁻¹ * x⁻¹ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G)
  cN : c ∈ Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G)
  cb : c * b * c⁻¹ = b
  c₁ : c * b₁ * c⁻¹ = b₂
  c₂ : c * b₂ * c⁻¹ = b₃
  c₃ : c * b₃ * c⁻¹ = b₁
  cB₂ : ∀ x ∈ B₂, c * x * c⁻¹ ∈ B₂
  c3 : c ^ 3 ∈ Subgroup.zpowers b ⊔ B₂
  Pmax : ∀ R : Subgroup G,
    R ≤ Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G) →
    IsPGroup 3 R → Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c ≤ R →
    R = Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c

namespace Setup

variable {b b₁ b₂ b₃ c : G} {B₂ : Subgroup G} (h : Setup b b₁ b₂ b₃ c B₂)
include h

theorem mem₁ : b₁ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) := Subgroup.subset_closure (by simp)
theorem mem₂ : b₂ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) := Subgroup.subset_closure (by simp)
theorem mem₃ : b₃ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) := Subgroup.subset_closure (by simp)

theorem b3 : b ^ 3 = 1 := h.B3 b b_mem_B

theorem B₁3 : ∀ y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), y ^ 3 = 1 :=
  fun y hy => h.B3 y (B₁_le_B hy)

theorem bB₁ : ∀ y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), b * y = y * b :=
  fun y hy => h.Bab b b_mem_B y (B₁_le_B hy)

theorem B₁comm : ∀ x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G),
    ∀ y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), x * y = y * x :=
  fun x hx y hy => h.Bab x (B₁_le_B hx) y (B₁_le_B hy)

theorem bn : ∀ x ∈ B₂, b * x * b⁻¹ ∈ B₂ := fun x hx => by
  have := mul_mem (h.B₁B₂ (h.bB₂ x hx)) hx
  rwa [inv_mul_cancel_right] at this

theorem A_cen : ∀ a ∈ Subgroup.zpowers b ⊔ B₂, ∀ z ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G),
    a * z = z * a := by
  have hle : Subgroup.zpowers b ⊔ B₂ ≤
      Subgroup.centralizer (Subgroup.closure ({b₁, b₂, b₃} : Set G) : Set G) := by
    refine sup_le ((Subgroup.zpowers_le).2 ?_) fun x hx => ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (h.bB₁ z hz).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact h.B₂ab z (h.B₁B₂ hz) x hx
  intro a ha z hz
  exact ((Subgroup.mem_centralizer_iff.mp (hle ha)) z hz).symm

theorem cA : ∀ x ∈ Subgroup.zpowers b ⊔ B₂, c * x * c⁻¹ ∈ Subgroup.zpowers b ⊔ B₂ := by
  have hmap : (Subgroup.zpowers b ⊔ B₂).map (MulAut.conj c).toMonoidHom ≤
      Subgroup.zpowers b ⊔ B₂ := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      show c * b * c⁻¹ ∈ _
      rw [h.cb]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_sup_right (h.cB₂ x hx)
  intro x hx
  exact hmap ⟨x, hx, rfl⟩

theorem card_cen_le {y : G} (hy : y ∈ Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c)
    (hyA : y ∉ Subgroup.zpowers b ⊔ B₂) :
    Nat.card ↥(Subgroup.closure ({b₁, b₂, b₃} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) ≤
      3 := by
  obtain ⟨r, hr, a, ha, rfl⟩ := exists_of_mem_P h.cA h.c3 hy
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hyA
    rwa [pow_zero, one_mul]
  have hr12 : r = 1 ∨ r = 2 := by omega
  have hle : Subgroup.closure ({b₁, b₂, b₃} : Set G) ⊓
      Subgroup.centralizer ({c ^ r * a} : Set G) ≤
      Subgroup.closure ({b₁, b₂, b₃} : Set G) ⊓ Subgroup.centralizer ({c ^ r} : Set G) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨hz1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hz2 ⊢
    have haz : a * z = z * a := h.A_cen a ha z hz1
    apply mul_right_cancel (b := a)
    calc z * c ^ r * a = z * (c ^ r * a) := mul_assoc _ _ _
      _ = c ^ r * a * z := hz2
      _ = c ^ r * z * a := by rw [mul_assoc, haz, ← mul_assoc]
  refine (Subgroup.card_le_of_le hle).trans ?_
  have h12 : b₁ * b₂ = b₂ * b₁ := h.B₁comm _ h.mem₁ _ h.mem₂
  have h13 : b₁ * b₃ = b₃ * b₁ := h.B₁comm _ h.mem₁ _ h.mem₃
  have h23 : b₂ * b₃ = b₃ * b₂ := h.B₁comm _ h.mem₂ _ h.mem₃
  exact card_cen_cycle_le h12 h13 h23 (h.B₁3 _ h.mem₁) (h.B₁3 _ h.mem₂) (h.B₁3 _ h.mem₃)
    h.B₁card h.c₁ h.c₂ h.c₃ hr12

theorem relIndex_A_le :
    (Subgroup.zpowers b ⊔ B₂).relIndex (Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c) ≤ 3 := by
  set A := Subgroup.zpowers b ⊔ B₂
  set P := A ⊔ Subgroup.zpowers c
  have hcP : ∀ r : ℕ, c ^ r ∈ P := fun r =>
    pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)) r
  rw [Subgroup.relIndex, Subgroup.index]
  let f : Fin 3 → ↥P ⧸ A.subgroupOf P := fun r => QuotientGroup.mk ⟨c ^ (r : ℕ), hcP r⟩
  have hf : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨r, hr, a, ha, hya⟩ := exists_of_mem_P h.cA h.c3 y.2
      refine ⟨⟨r, hr⟩, ?_⟩
      show (QuotientGroup.mk _ : ↥P ⧸ A.subgroupOf P) = QuotientGroup.mk y
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hya]
      simpa using ha
  calc Nat.card (↥P ⧸ A.subgroupOf P) ≤ Nat.card (Fin 3) := Nat.card_le_card_of_surjective f hf
    _ = 3 := Nat.card_fin 3

theorem eq_B_of_elemAb (hΩ : ∀ x ∈ B₂, x ^ 3 = 1 → x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    {E : Subgroup G} (hEP : E ≤ Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hE81 : Nat.card E = 81) : E = Subgroup.closure ({b, b₁, b₂, b₃} : Set G) := by
  set A := Subgroup.zpowers b ⊔ B₂ with hAdef
  set B := Subgroup.closure ({b, b₁, b₂, b₃} : Set G) with hBdef
  set B₁ := Subgroup.closure ({b₁, b₂, b₃} : Set G) with hB₁def
  have hAE : ∀ x ∈ A ⊓ E, x ∈ B := fun x hx =>
    mem_B_of_cube h.b3 h.bB₁ h.B₁B₂ h.B₁3 h.B₂ab h.bB₂ hΩ (Subgroup.mem_inf.mp hx).1
      (hE3 x (Subgroup.mem_inf.mp hx).2)
  by_cases hle : E ≤ A
  · have hEB : E ≤ B := fun x hx => hAE x (Subgroup.mem_inf.mpr ⟨hle hx, hx⟩)
    exact Subgroup.eq_of_le_of_card_ge hEB (by rw [h.Bcard, hE81])
  · exfalso
    obtain ⟨y, hyE, hyA⟩ := Set.not_subset.mp hle
    have hP0 : A.relIndex (A ⊔ Subgroup.zpowers c) ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_mul_card A (A ⊔ Subgroup.zpowers c)
      rw [h0, zero_mul] at this
      exact Nat.card_pos.ne' this.symm
    have hiE : A.relIndex E ≤ 3 :=
      (Subgroup.relIndex_le_of_le_right hEP hP0).trans h.relIndex_A_le
    have hcE := Subgroup.relIndex_mul_card A E
    have hAE27 : 27 ≤ Nat.card ↥(A ⊓ E) := by
      rw [hE81] at hcE
      nlinarith
    have hXB : A ⊓ E ≤ B := hAE
    have hB₁B : B₁ ≤ B := B₁_le_B
    have hB0 : B₁.relIndex B = 3 := by
      have := Subgroup.relIndex_mul_card B₁ B
      rw [inf_eq_left.mpr hB₁B, h.B₁card, h.Bcard] at this
      omega
    have hiX : B₁.relIndex (A ⊓ E) ≤ 3 :=
      (Subgroup.relIndex_le_of_le_right hXB (by rw [hB0]; norm_num)).trans hB0.le
    have hcX := Subgroup.relIndex_mul_card B₁ (A ⊓ E)
    have h9 : 9 ≤ Nat.card ↥(B₁ ⊓ (A ⊓ E)) := by nlinarith
    have hsub : B₁ ⊓ (A ⊓ E) ≤ B₁ ⊓ Subgroup.centralizer ({y} : Set G) := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
      refine Subgroup.mem_inf.mpr ⟨hz1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact hEab z (Subgroup.mem_inf.mp hz2).2 y hyE
    have h3 := h.card_cen_le (hEP hyE) hyA
    have := (Subgroup.card_le_of_le hsub).trans h3
    omega

theorem isPGroup_P : IsPGroup 3 ↥(Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c : Subgroup G) := by
  have hB₂p : IsPGroup 3 B₂ := by
    intro g
    refine ⟨2, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, show 3 ^ 2 = 3 * 3 by norm_num, pow_mul]
    exact h.B₁3 _ (h.B₂3 g g.2)
  have hbp : IsPGroup 3 (Subgroup.zpowers b) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, ← hk, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, h.b3, one_zpow]
  have hA : IsPGroup 3 ↥(Subgroup.zpowers b ⊔ B₂ : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hbp hB₂p (zpowers_le_normalizer h.bn)
  obtain ⟨k, hk⟩ := hA ⟨c ^ 3, h.c3⟩
  have hck : c ^ 3 ^ (k + 1) = 1 := by
    have := congrArg Subtype.val hk
    rw [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [pow_succ', pow_mul]
    exact this
  have hcp : IsPGroup 3 (Subgroup.zpowers c) := by
    intro g
    refine ⟨k + 1, Subtype.ext ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hck, one_zpow]
  exact IsPGroup.to_sup_of_normal_left' hA hcp (zpowers_le_normalizer h.cA)

theorem B_le_P : Subgroup.closure ({b, b₁, b₂, b₃} : Set G) ≤
    Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (h.B₁B₂ h.mem₁))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (h.B₁B₂ h.mem₂))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (h.B₁B₂ h.mem₃))

theorem P_le_N : Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c ≤
    Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G) := by
  refine sup_le (sup_le ((Subgroup.zpowers_le).2 ?_) h.B₂N) ((Subgroup.zpowers_le).2 h.cN)
  exact Subgroup.le_normalizer b_mem_B

theorem conj_eq_B (hΩ : ∀ x ∈ B₂, x ^ 3 = 1 → x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (g : G) (hg : conjSubgroup g (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) ≤
      Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c) :
    conjSubgroup g (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) =
      Subgroup.closure ({b, b₁, b₂, b₃} : Set G) := by
  set B := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  refine h.eq_B_of_elemAb hΩ hg ?_ ?_ ?_
  · intro x hx y hy
    rw [mem_conjSubgroup] at hx hy
    have e := h.Bab _ hx _ hy
    calc x * y = g * (g⁻¹ * x * g * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * (g⁻¹ * x * g)) * g⁻¹ := by rw [e]
      _ = y * x := by group
  · intro x hx
    rw [mem_conjSubgroup] at hx
    have e := h.B3 _ hx
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, conj_pow, e, mul_one, mul_inv_cancel]
  · rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g).injective, h.Bcard]

theorem normalizer_P_le (hΩ : ∀ x ∈ B₂, x ^ 3 = 1 → x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    {g : G} (hg : g ∈ Subgroup.normalizer
      ((Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G) := by
  set B := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  set P := Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c
  have hle : conjSubgroup g B ≤ P := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have hx' := h.B_le_P hx
    have := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mp hx'
    simpa [mul_assoc] using this
  have heq := h.conj_eq_B hΩ g hle
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have e : g * y * g⁻¹ ∈ conjSubgroup g B ↔ y ∈ B := by
    rw [mem_conjSubgroup]
    simp [mul_assoc]
  rw [heq] at e
  exact e.symm

theorem exists_sylow (hΩ : ∀ x ∈ B₂, x ^ 3 = 1 → x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G)) :
    ∃ S : Sylow 3 G, (S : Subgroup G) = Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c with hPdef
  obtain ⟨S, hPS⟩ := h.isPGroup_P.exists_le_sylow
  refine ⟨S, le_antisymm ?_ hPS⟩
  haveI : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  have hNC := normalizerCondition_of_isNilpotent (G := ↥(S : Subgroup G))
  rw [normalizerCondition_iff_only_full_group_self_normalizing] at hNC
  have hH := hNC (P.subgroupOf S) ?_
  · intro x hx
    have : (⟨x, hx⟩ : ↥(S : Subgroup G)) ∈ P.subgroupOf S := by rw [hH]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  refine le_antisymm (fun s hs => ?_) Subgroup.le_normalizer
  have hsP : (s : G) ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 := (Subgroup.mem_normalizer_iff.mp hs ⟨y, hPS hy⟩).mp
        (Subgroup.mem_subgroupOf.mpr hy)
      exact Subgroup.mem_subgroupOf.mp h1
    · intro hy
      have hyS : y ∈ (S : Subgroup G) := by
        have h1 : (s : G) * y * (s : G)⁻¹ ∈ (S : Subgroup G) := hPS hy
        have : y = (s : G)⁻¹ * ((s : G) * y * (s : G)⁻¹) * s := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem s.2) h1) s.2
      have h1 := (Subgroup.mem_normalizer_iff.mp hs ⟨y, hyS⟩).mpr
        (Subgroup.mem_subgroupOf.mpr hy)
      exact Subgroup.mem_subgroupOf.mp h1
  have hsN := h.normalizer_P_le hΩ hsP
  have hsp : IsPGroup 3 (Subgroup.zpowers (s : G)) :=
    (S.isPGroup'.to_le (Subgroup.zpowers_le.2 s.2))
  have hR := h.Pmax (P ⊔ Subgroup.zpowers (s : G))
    (sup_le h.P_le_N ((Subgroup.zpowers_le).2 hsN))
    (IsPGroup.to_sup_of_normal_left' h.isPGroup_P hsp ((Subgroup.zpowers_le).2 hsP))
    le_sup_left
  have hs' : (s : G) ∈ P := by
    have hsR : (s : G) ∈ P ⊔ Subgroup.zpowers (s : G) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rw [hR] at hsR
    exact hsR
  exact Subgroup.mem_subgroupOf.mpr hs'

theorem b₁_ne_one : b₁ ≠ 1 := by
  intro h1
  have hinj := coord_injective (h.B₁comm _ h.mem₁ _ h.mem₂) (h.B₁comm _ h.mem₁ _ h.mem₃)
    (h.B₁comm _ h.mem₂ _ h.mem₃) (h.B₁3 _ h.mem₁) (h.B₁3 _ h.mem₂) (h.B₁3 _ h.mem₃) h.B₁card
  have e : coord b₁ b₂ b₃ (1, 0, 0) = coord b₁ b₂ b₃ (0, 0, 0) := by
    simp [coord, h1]
  exact absurd (hinj e) (by decide)

theorem not_mem_commutator
    (hΩ : ∀ x ∈ B₂, x ^ 3 = 1 → x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hB₂card : Nat.card B₂ = 3 ^ 6)
    (hbN' : ∀ hb : b ∈ Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G),
      (⟨b, hb⟩ : ↥(Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G))) ∈
        commutator ↥(Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G)) →
      ∃ s : G, s * b₁ * s⁻¹ = b₁⁻¹ ∧
        ∀ x ∈ B₂, s * x * s⁻¹ * x⁻¹ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G)) :
    ∀ hb : b ∈ Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G),
      (⟨b, hb⟩ : ↥(Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G))) ∉
        commutator ↥(Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G)) := by
  intro hb hmem
  obtain ⟨s, hs1, hs⟩ := hbN' hb hmem
  obtain ⟨x, hx, hxb⟩ := exists_cube_eq h.B₁B₂ h.B₂ab h.B₂3 h.B₁3 hΩ
    (by rw [hB₂card, h.B₁card]; norm_num) h.mem₁
  have hfix : s * b₁ * s⁻¹ = b₁ := by
    rw [← hxb]
    exact conj_cube_eq h.B₁B₂ h.B₂ab h.B₁3 hs hx
  have hsq : b₁ * b₁ = 1 := by
    rw [hs1] at hfix
    calc b₁ * b₁ = b₁⁻¹ * b₁ := by rw [hfix]
      _ = 1 := inv_mul_cancel b₁
  apply h.b₁_ne_one
  calc b₁ = b₁ * (b₁ * b₁) * (b₁ * b₁)⁻¹ := (mul_inv_cancel_right b₁ (b₁ * b₁)).symm
    _ = b₁ ^ 3 * (b₁ * b₁)⁻¹ := by rw [pow_three]
    _ = 1 := by rw [h.B₁3 _ h.mem₁, hsq, inv_one, one_mul]

end Setup

theorem false_of_omega {b b₁ b₂ b₃ c : G} {B₂ : Subgroup G} (h : Setup b b₁ b₂ b₃ c B₂)
    (hΩ : ∀ x ∈ B₂, x ^ 3 = 1 → x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hbN : ∀ hb : b ∈ Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G),
      (⟨b, hb⟩ : ↥(Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G))) ∉
        commutator ↥(Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G)))
    (hbG : b ∈ commutator G) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := h.exists_sylow hΩ
  have hBS : Subgroup.closure ({b, b₁, b₂, b₃} : Set G) ≤ S := hS ▸ h.B_le_P
  have hSN : (S : Subgroup G) ≤
      Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G) := hS ▸ h.P_le_N
  have hwc : ∀ g : G, conjSubgroup g (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) ≤ S →
      conjSubgroup g (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) =
        Subgroup.closure ({b, b₁, b₂, b₃} : Set G) := fun g hg =>
    h.conj_eq_B hΩ g (hS ▸ hg)
  exact hbN _ (CFSG.RankThree.Transfer.WCP.mem_commutator_of_weaklyClosed S hBS hSN hwc h.Bab
    b_mem_B h.b3 hbG)

theorem exp_three_of_irreducible_of {b b₁ b₂ b₃ c : G} {B₂ : Subgroup G}
    (h : Setup b b₁ b₂ b₃ c B₂) {T : Set G} (hT : ∀ g ∈ T, ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂)
    (hirr : ∀ U : Subgroup G, Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ U → U ≤ B₂ →
      (∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) →
        U = Subgroup.closure ({b₁, b₂, b₃} : Set G) ∨ U = B₂)
    (hfalse : (∀ x ∈ B₂, x ^ 3 = 1 → x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G)) → False) :
    ∀ x ∈ B₂, x ^ 3 = 1 := by
  let Ω : Subgroup G :=
    { carrier := {x | x ∈ B₂ ∧ x ^ 3 = 1}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        rw [(Commute.mul_pow (h.B₂ab x hx.1 y hy.1) 3), hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow 3⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hB₁Ω : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ Ω := fun x hx =>
    ⟨h.B₁B₂ hx, h.B₁3 x hx⟩
  have hΩB₂ : Ω ≤ B₂ := fun x hx => hx.1
  have hΩT : ∀ g ∈ T, ∀ u ∈ Ω, g * u * g⁻¹ ∈ Ω := fun g hg u hu =>
    ⟨hT g hg u hu.1, by rw [conj_pow, hu.2, mul_one, mul_inv_cancel]⟩
  rcases hirr Ω hB₁Ω hΩB₂ hΩT with hΩ | hΩ
  · exfalso
    refine hfalse fun x hx hx3 => ?_
    have : x ∈ Ω := ⟨hx, hx3⟩
    rwa [hΩ] at this
  · intro x hx
    have : x ∈ Ω := by rw [hΩ]; exact hx
    exact this.2

theorem false_of_omega' {b b₁ b₂ b₃ c : G} {B₂ : Subgroup G} (h : Setup b b₁ b₂ b₃ c B₂)
    (hΩ : ∀ x ∈ B₂, x ^ 3 = 1 → x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hB₂card : Nat.card B₂ = 3 ^ 6)
    (hbN' : ∀ hb : b ∈ Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G),
      (⟨b, hb⟩ : ↥(Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G))) ∈
        commutator ↥(Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G)) →
      ∃ s : G, s * b₁ * s⁻¹ = b₁⁻¹ ∧
        ∀ x ∈ B₂, s * x * s⁻¹ * x⁻¹ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hbG : b ∈ commutator G) : False :=
  false_of_omega h hΩ (h.not_mem_commutator hΩ hB₂card hbN') hbG

theorem exp_three_of_irreducible' {b b₁ b₂ b₃ c : G} {B₂ : Subgroup G}
    (h : Setup b b₁ b₂ b₃ c B₂) {T : Set G} (hT : ∀ g ∈ T, ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂)
    (hirr : ∀ U : Subgroup G, Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ U → U ≤ B₂ →
      (∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) →
        U = Subgroup.closure ({b₁, b₂, b₃} : Set G) ∨ U = B₂)
    (hB₂card : Nat.card B₂ = 3 ^ 6)
    (hbN' : ∀ hb : b ∈ Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G),
      (⟨b, hb⟩ : ↥(Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G))) ∈
        commutator ↥(Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G)) →
      ∃ s : G, s * b₁ * s⁻¹ = b₁⁻¹ ∧
        ∀ x ∈ B₂, s * x * s⁻¹ * x⁻¹ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hbG : b ∈ commutator G) : ∀ x ∈ B₂, x ^ 3 = 1 :=
  exp_three_of_irreducible_of h hT hirr fun hΩ => false_of_omega' h hΩ hB₂card hbN' hbG

end CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem
