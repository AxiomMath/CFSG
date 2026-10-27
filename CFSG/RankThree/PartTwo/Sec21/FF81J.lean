module

import CFSG.RankThree.PartTwo.Sec21.FF81S0
public import CFSG.RankThree.PartTwo.Sec21.FF81Prop33

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

variable {G : Type} [Group G]

theorem card_closure_pair_le [Finite G] {c₁ c₂ : G} (h1 : c₁ ^ 3 = 1) (h2 : c₂ ^ 3 = 1)
    (hc : c₁ * c₂ = c₂ * c₁) : Nat.card (Subgroup.closure ({c₁, c₂} : Set G)) ≤ 9 := by
  have hcl : Subgroup.closure ({c₁, c₂} : Set G) = Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂ := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hN : Subgroup.zpowers c₁ ≤ Subgroup.normalizer (Subgroup.zpowers c₂ : Set G) := by
    rw [Subgroup.zpowers_le]
    have hcomm : Commute c₁ c₂ := hc
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      simp only
      rw [(hcomm.zpow_right k).eq, mul_inv_cancel_right]
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simp only at hk ⊢
      have e : c₁ * c₂ ^ k * c₁⁻¹ = c₂ ^ k := by
        rw [(hcomm.zpow_right k).eq, mul_inv_cancel_right]
      have h' : c₁ * y * c₁⁻¹ = c₁ * c₂ ^ k * c₁⁻¹ := by rw [e, hk]
      exact (mul_left_cancel (mul_right_cancel h')).symm
  have hset : ((Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂ : Subgroup G) : Set G) =
      (Subgroup.zpowers c₁ : Set G) * Subgroup.zpowers c₂ :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN
  rw [hcl]
  calc Nat.card ↥(Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂)
      = Nat.card ↥((Subgroup.zpowers c₁ : Set G) * Subgroup.zpowers c₂) := by
        rw [← hset]; rfl
    _ ≤ Nat.card ↥(Subgroup.zpowers c₁ : Set G) * Nat.card ↥(Subgroup.zpowers c₂ : Set G) :=
        Set.natCard_mul_le
    _ ≤ 3 * 3 := by
        have e1 : Nat.card ↥(Subgroup.zpowers c₁ : Set G) = orderOf c₁ := Nat.card_zpowers c₁
        have e2 : Nat.card ↥(Subgroup.zpowers c₂ : Set G) = orderOf c₂ := Nat.card_zpowers c₂
        rw [e1, e2]
        exact Nat.mul_le_mul (orderOf_le_of_pow_eq_one (by norm_num) h1)
          (orderOf_le_of_pow_eq_one (by norm_num) h2)
    _ = 9 := by norm_num

theorem triple_facts {c₁ c₂ c₃ : G} (hE : IsElemAb 3 3 (Subgroup.closure ({c₁, c₂, c₃} : Set G))) :
    (c₁ ^ 3 = 1 ∧ c₂ ^ 3 = 1 ∧ c₃ ^ 3 = 1) ∧
      (c₁ * c₂ = c₂ * c₁ ∧ c₁ * c₃ = c₃ * c₁ ∧ c₂ * c₃ = c₃ * c₂) := by
  have m1 : c₁ ∈ Subgroup.closure ({c₁, c₂, c₃} : Set G) := Subgroup.subset_closure (by simp)
  have m2 : c₂ ∈ Subgroup.closure ({c₁, c₂, c₃} : Set G) := Subgroup.subset_closure (by simp)
  have m3 : c₃ ∈ Subgroup.closure ({c₁, c₂, c₃} : Set G) := Subgroup.subset_closure (by simp)
  have hc : ∀ x ∈ Subgroup.closure ({c₁, c₂, c₃} : Set G),
      ∀ y ∈ Subgroup.closure ({c₁, c₂, c₃} : Set G), x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.toIsMulCommutative.is_comm.comm
      (⟨x, hx⟩ : Subgroup.closure ({c₁, c₂, c₃} : Set G)) ⟨y, hy⟩)
  exact ⟨⟨pow_three_eq_one_of_isElemAb hE m1, pow_three_eq_one_of_isElemAb hE m2,
    pow_three_eq_one_of_isElemAb hE m3⟩, ⟨hc _ m1 _ m2, hc _ m1 _ m3, hc _ m2 _ m3⟩⟩

theorem not_mem_closure_pair [Finite G] {c₁ c₂ c₃ : G}
    (hE : IsElemAb 3 3 (Subgroup.closure ({c₁, c₂, c₃} : Set G))) :
    c₃ ∉ Subgroup.closure ({c₁, c₂} : Set G) := by
  intro h
  obtain ⟨⟨h1, h2, -⟩, ⟨h12, -, -⟩⟩ := triple_facts hE
  have hle : Subgroup.closure ({c₁, c₂, c₃} : Set G) ≤ Subgroup.closure ({c₁, c₂} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact h
  have := (Subgroup.card_le_of_le hle).trans (card_closure_pair_le h1 h2 h12)
  rw [hE.2] at this
  norm_num at this

theorem isElemAb_perm {c₁ c₂ c₃ : G}
    (hE : IsElemAb 3 3 (Subgroup.closure ({c₁, c₂, c₃} : Set G))) :
    IsElemAb 3 3 (Subgroup.closure ({c₂, c₁, c₃} : Set G)) ∧
      IsElemAb 3 3 (Subgroup.closure ({c₁, c₃, c₂} : Set G)) ∧
      IsElemAb 3 3 (Subgroup.closure ({c₃, c₁, c₂} : Set G)) := by
  have e1 : ({c₂, c₁, c₃} : Set G) = {c₁, c₂, c₃} := by
    ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have e2 : ({c₁, c₃, c₂} : Set G) = {c₁, c₂, c₃} := by
    ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have e3 : ({c₃, c₁, c₂} : Set G) = {c₁, c₂, c₃} := by
    ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  exact ⟨e1 ▸ hE, e2 ▸ hE, e3 ▸ hE⟩

theorem ne_of_basis [Finite G] {c₁ c₂ c₃ : G}
    (hE : IsElemAb 3 3 (Subgroup.closure ({c₁, c₂, c₃} : Set G))) :
    ¬ (c₁ = c₂ ∨ c₁ = c₂⁻¹) := by
  have e : ({c₂, c₃, c₁} : Set G) = {c₁, c₂, c₃} := by
    ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hE' : IsElemAb 3 3 (Subgroup.closure ({c₂, c₃, c₁} : Set G)) := e ▸ hE
  have := not_mem_closure_pair hE'
  rintro (h | h) <;> apply this <;> rw [h]
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

theorem ne_one_of_basis [Finite G] {c₁ c₂ c₃ : G}
    (hE : IsElemAb 3 3 (Subgroup.closure ({c₁, c₂, c₃} : Set G))) : c₁ ≠ 1 := by
  have e : ({c₂, c₃, c₁} : Set G) = {c₁, c₂, c₃} := by
    ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hE' : IsElemAb 3 3 (Subgroup.closure ({c₂, c₃, c₁} : Set G)) := e ▸ hE
  intro h
  exact not_mem_closure_pair hE' (h ▸ Subgroup.one_mem _)

theorem zpowers_ne [Finite G] {c₁ c₂ c₃ : G}
    (hE : IsElemAb 3 3 (Subgroup.closure ({c₁, c₂, c₃} : Set G))) :
    Subgroup.zpowers c₁ ≠ Subgroup.zpowers c₂ := by
  have e : ({c₂, c₃, c₁} : Set G) = {c₁, c₂, c₃} := by
    ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hE' : IsElemAb 3 3 (Subgroup.closure ({c₂, c₃, c₁} : Set G)) := e ▸ hE
  intro h
  apply not_mem_closure_pair hE'
  have : c₁ ∈ Subgroup.zpowers c₂ := h ▸ Subgroup.mem_zpowers c₁
  exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) this

theorem conjBy_mul (g h : G) (H : Subgroup G) : conjBy (g * h) H = conjBy g (conjBy h H) := by
  ext y
  simp only [conjBy, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨h * z * h⁻¹, ⟨z, hz, rfl⟩, by group⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by group⟩

theorem conjBy_one (H : Subgroup G) : conjBy 1 H = H := by
  ext y; simp [conjBy, Subgroup.mem_map]

theorem conjBy_inv_conjBy (g : G) (H : Subgroup G) : conjBy g⁻¹ (conjBy g H) = H := by
  rw [← conjBy_mul, inv_mul_cancel, conjBy_one]

theorem conjBy_conjBy_inv (g : G) (H : Subgroup G) : conjBy g (conjBy g⁻¹ H) = H := by
  rw [← conjBy_mul, mul_inv_cancel, conjBy_one]

theorem conjBy_cube {x : G} (hx : x ^ 3 = 1) (H : Subgroup G) :
    conjBy x (conjBy x (conjBy x H)) = H := by
  rw [← conjBy_mul, ← conjBy_mul, show x * x * x = x ^ 3 by rw [pow_three, mul_assoc], hx,
    conjBy_one]

theorem not_inv_of_cube {x y : G} (hx : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (h : x * y * x⁻¹ = y⁻¹) : False := by
  have h2 : x * y⁻¹ * x⁻¹ = y := by
    rw [show x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ by group, h, inv_inv]
  have h3 : x ^ 3 * y * (x ^ 3)⁻¹ = y⁻¹ := by
    calc x ^ 3 * y * (x ^ 3)⁻¹ = x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ := by
          rw [pow_three]; group
      _ = y⁻¹ := by rw [h, h2, h]
  rw [hx] at h3
  have hyy : y = y⁻¹ := by simpa using h3
  have hy2 : y ^ 2 = 1 := by rw [sq]; exact mul_eq_one_iff_eq_inv.mpr hyy
  apply hy1
  calc y = y ^ 3 * (y ^ 2)⁻¹ := by group
    _ = 1 := by rw [hy3, hy2]; group

theorem line_cases {x y c c' : G} (hx : x ^ 3 = 1) (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1)
    (h : x * y * x⁻¹ = y ∨ x * y * x⁻¹ = y⁻¹ ∨ x * y * x⁻¹ = c ∨ x * y * x⁻¹ = c⁻¹ ∨
      x * y * x⁻¹ = c' ∨ x * y * x⁻¹ = c'⁻¹) :
    (x * y * x⁻¹ = y ∧ conjBy x (Subgroup.zpowers y) = Subgroup.zpowers y) ∨
      conjBy x (Subgroup.zpowers y) = Subgroup.zpowers c ∨
      conjBy x (Subgroup.zpowers y) = Subgroup.zpowers c' := by
  rw [conjBy_zpowers]
  rcases h with h | h | h | h | h | h <;> rw [h]
  · exact Or.inl ⟨rfl, rfl⟩
  · exact (not_inv_of_cube hx hy3 hy1 h).elim
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl Subgroup.zpowers_inv)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inr Subgroup.zpowers_inv)

theorem mono3 [Finite G] {b₁ b₂ b₃ x : G}
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G))) (hx : x ^ 3 = 1)
    (hs : ∀ y ∈ ({b₁, b₂, b₃} : Set G),
      x * y * x⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G)) :
    (x * b₁ * x⁻¹ = b₁ ∧ x * b₂ * x⁻¹ = b₂ ∧ x * b₃ * x⁻¹ = b₃) ∨
      (conjBy x (Subgroup.zpowers b₁) = Subgroup.zpowers b₂ ∧
        conjBy x (Subgroup.zpowers b₂) = Subgroup.zpowers b₃ ∧
        conjBy x (Subgroup.zpowers b₃) = Subgroup.zpowers b₁) ∨
      (conjBy x (Subgroup.zpowers b₁) = Subgroup.zpowers b₃ ∧
        conjBy x (Subgroup.zpowers b₂) = Subgroup.zpowers b₁ ∧
        conjBy x (Subgroup.zpowers b₃) = Subgroup.zpowers b₂) := by
  obtain ⟨hE213, hE132, hE312⟩ := isElemAb_perm hE
  have hE231 : IsElemAb 3 3 (Subgroup.closure ({b₂, b₃, b₁} : Set G)) := by
    have e : ({b₂, b₃, b₁} : Set G) = {b₁, b₂, b₃} := by
      ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    exact e ▸ hE
  obtain ⟨⟨c1, c2, c3⟩, -⟩ := triple_facts hE
  have n12 := zpowers_ne hE
  have n13 := zpowers_ne hE132
  have n23 := zpowers_ne hE231
  have hc1 := conjBy_cube hx (Subgroup.zpowers b₁)
  have hc2 := conjBy_cube hx (Subgroup.zpowers b₂)
  have hc3 := conjBy_cube hx (Subgroup.zpowers b₃)
  have m1 := hs b₁ (by simp)
  have m2 := hs b₂ (by simp)
  have m3 := hs b₃ (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m1 m2 m3
  have l1 := line_cases (c := b₂) (c' := b₃) hx (ne_one_of_basis hE) c1 m1
  have l2 := line_cases (c := b₁) (c' := b₃) hx (ne_one_of_basis hE213) c2 (by
    rcases m2 with h | h | h | h | h | h <;> simp only [h, true_or, or_true])
  have l3 := line_cases (c := b₁) (c' := b₂) hx (ne_one_of_basis hE312) c3 (by
    rcases m3 with h | h | h | h | h | h <;> simp only [h, true_or, or_true])
  rcases l1 with ⟨e1, k1⟩ | k1 | k1 <;> rcases l2 with ⟨e2, k2⟩ | k2 | k2 <;>
    rcases l3 with ⟨e3, k3⟩ | k3 | k3 <;> simp only [k1, k2, k3] at hc1 hc2 hc3 <;>
    first
    | exact Or.inl ⟨e1, e2, e3⟩
    | exact Or.inr (Or.inl ⟨k1, k2, k3⟩)
    | exact Or.inr (Or.inr ⟨k1, k2, k3⟩)
    | exact absurd hc1 (Ne.symm n12)
    | exact absurd hc1 (Ne.symm n13)
    | exact absurd hc2 n12
    | exact absurd hc2 (Ne.symm n23)
    | exact absurd hc3 n13
    | exact absurd hc3 n23

theorem card_sup_le_mul [Finite G] (H K : Subgroup G)
    (h : H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right H K h
  calc Nat.card ↥(H ⊔ K) = Nat.card ↥((H : Set G) * K) := by rw [← hset]; rfl
    _ ≤ _ := Set.natCard_mul_le

theorem card_sup_mul_card_inf [Finite G] (H K : Subgroup G)
    (h : H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have hHM : H ≤ H ⊔ K := le_sup_left
  have hKM : K ≤ H ⊔ K := le_sup_right
  have hMN : H ⊔ K ≤ Subgroup.normalizer (K : Set G) := sup_le h Subgroup.le_normalizer
  haveI : (K.subgroupOf (H ⊔ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMN
  have htop : H.subgroupOf (H ⊔ K) ⊔ K.subgroupOf (H ⊔ K) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hHM hKM, Subgroup.subgroupOf_self]
  have e1 := Subgroup.relIndex_sup_right (H := H.subgroupOf (H ⊔ K)) (K := K.subgroupOf (H ⊔ K))
  rw [htop, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hHM] at e1
  have e2 := Subgroup.relIndex_mul_card K (H ⊔ K)
  rw [inf_of_le_left hKM] at e2
  have e3 := Subgroup.relIndex_mul_card K H
  rw [inf_comm] at e3
  have e1' : K.relIndex (H ⊔ K) = K.relIndex H := e1
  rw [← e2, ← e3, e1']
  ring

theorem nine_le_card [Finite G] {B : Subgroup G} (hB : IsElemAb 3 4 B) {u v : G} (hu : u ∈ B)
    (hv : v ∈ B) (hu1 : u ≠ 1) (hvu : v ∉ Subgroup.zpowers u) :
    9 ≤ Nat.card (Subgroup.closure ({u, v} : Set G)) := by
  have hle : Subgroup.closure ({u, v} : Set G) ≤ B := by
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    rcases hy with rfl | rfl
    · exact hu
    · exact hv
  have hZ : Subgroup.zpowers u ≤ Subgroup.closure ({u, v} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hvK : v ∈ Subgroup.closure ({u, v} : Set G) := Subgroup.subset_closure (by simp)
  have hou : orderOf u = 3 :=
    orderOf_eq_prime (pow_three_eq_one_of_isElemAb hB hu) hu1
  have hcZ : Nat.card (Subgroup.zpowers u) = 3 := by rw [Nat.card_zpowers, hou]
  have hd := Subgroup.card_dvd_of_le hle
  rw [hB.2] at hd
  have hd3 := Subgroup.card_dvd_of_le hZ
  rw [hcZ] at hd3
  have hne : Nat.card (Subgroup.closure ({u, v} : Set G)) ≠ 3 := by
    intro h3
    have := Subgroup.eq_of_le_of_card_ge hZ (by rw [h3, hcZ])
    exact hvu (this ▸ hvK)
  obtain ⟨m, hm, e⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  rw [e] at hd3 hne ⊢
  interval_cases m <;> simp_all <;> omega

theorem card_inf_cen_le_nine [Finite G] {B : Subgroup G} {c₁ c₂ c₃ x : G}
    (hB : IsElemAb 3 4 B) (hE : IsElemAb 3 3 (Subgroup.closure ({c₁, c₂, c₃} : Set G)))
    (h1B : c₁ ∈ B) (h2B : c₂ ∈ B) (hx : x ∈ Nor B)
    (k1 : conjBy x (Subgroup.zpowers c₁) = Subgroup.zpowers c₂)
    (k2 : conjBy x (Subgroup.zpowers c₂) = Subgroup.zpowers c₃) :
    Nat.card ↥(B ⊓ Cen x) ≤ 9 := by
  have hcomm : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (hB.1.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : B) ⟨c, hc⟩)
  have hconj : ∀ y ∈ B, x * y * x⁻¹ ∈ B := fun y hy => (Subgroup.mem_normalizer_iff.mp hx y).mp hy
  let f : B →* B :=
    { toFun := fun y => ⟨x * y * x⁻¹ * (y : G)⁻¹, B.mul_mem (hconj _ y.2) (B.inv_mem y.2)⟩
      map_one' := by ext; simp
      map_mul' := fun y z => by
        ext
        simp only [Subgroup.coe_mul]
        have := hcomm _ (B.inv_mem y.2) _ (B.mul_mem (hconj _ z.2) (B.inv_mem z.2))
        calc x * (↑y * ↑z) * x⁻¹ * (↑y * ↑z)⁻¹
            = (x * ↑y * x⁻¹) * ((x * ↑z * x⁻¹ * (↑z)⁻¹) * (↑y)⁻¹) := by group
          _ = (x * ↑y * x⁻¹) * ((↑y)⁻¹ * (x * ↑z * x⁻¹ * (↑z)⁻¹)) := by rw [this]
          _ = x * ↑y * x⁻¹ * (↑y)⁻¹ * (x * ↑z * x⁻¹ * (↑z)⁻¹) := by group }
  have hf : ∀ y : B, (f y : G) = x * y * x⁻¹ * (y : G)⁻¹ := fun _ => rfl
  have hker : B ⊓ Cen x ≤ f.ker.map B.subtype := by
    intro y hy
    obtain ⟨hyB, hyx0⟩ := Subgroup.mem_inf.mp hy
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hyx0
    refine ⟨⟨y, hyB⟩, ?_, rfl⟩
    change f ⟨y, hyB⟩ = 1
    ext
    rw [hf]
    simp only [Subgroup.coe_one]
    rw [← hyx]; group
  have hcker : Nat.card ↥(B ⊓ Cen x) ≤ Nat.card f.ker :=
    (Subgroup.card_le_of_le hker).trans
      (Subgroup.card_map_of_injective B.subtype_injective).le
  have k1' : Subgroup.zpowers (x * c₁ * x⁻¹) = Subgroup.zpowers c₂ := by
    rw [← conjBy_zpowers]; exact k1
  have k2' : Subgroup.zpowers (x * c₂ * x⁻¹) = Subgroup.zpowers c₃ := by
    rw [← conjBy_zpowers]; exact k2
  have hc12 : ∀ y ∈ ({c₁, c₂} : Set G), y ∈ Subgroup.closure ({c₁, c₂} : Set G) :=
    fun y hy => Subgroup.subset_closure hy
  set u := x * c₁ * x⁻¹ * c₁⁻¹ with hu
  set v := x * c₂ * x⁻¹ * c₂⁻¹ with hv
  have hxc1 : x * c₁ * x⁻¹ ∈ Subgroup.closure ({c₁, c₂} : Set G) :=
    (Subgroup.zpowers_le.mpr (hc12 c₂ (by simp))) (k1' ▸ Subgroup.mem_zpowers _)
  have huC : u ∈ Subgroup.closure ({c₁, c₂} : Set G) :=
    Subgroup.mul_mem _ hxc1 (Subgroup.inv_mem _ (hc12 c₁ (by simp)))
  have hu1 : u ≠ 1 := by
    intro h
    have : x * c₁ * x⁻¹ = c₁ := mul_inv_eq_one.mp h
    rw [this] at k1'
    exact zpowers_ne hE k1'
  have hvu : v ∉ Subgroup.zpowers u := by
    intro h
    have hvC : v ∈ Subgroup.closure ({c₁, c₂} : Set G) := (Subgroup.zpowers_le.mpr huC) h
    have hxc2 : x * c₂ * x⁻¹ ∈ Subgroup.closure ({c₁, c₂} : Set G) := by
      have : x * c₂ * x⁻¹ = v * c₂ := by rw [hv]; group
      rw [this]
      exact Subgroup.mul_mem _ hvC (hc12 c₂ (by simp))
    apply not_mem_closure_pair hE
    have : Subgroup.zpowers c₃ ≤ Subgroup.closure ({c₁, c₂} : Set G) := by
      rw [← k2']; exact Subgroup.zpowers_le.mpr hxc2
    exact this (Subgroup.mem_zpowers c₃)
  have huB : u ∈ B := (f ⟨c₁, h1B⟩).2
  have hvB : v ∈ B := (f ⟨c₂, h2B⟩).2
  have h9 := nine_le_card hB huB hvB hu1 hvu
  have hrange : Subgroup.closure ({u, v} : Set G) ≤ f.range.map B.subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    rcases hy with rfl | rfl
    · exact ⟨f ⟨c₁, h1B⟩, ⟨_, rfl⟩, rfl⟩
    · exact ⟨f ⟨c₂, h2B⟩, ⟨_, rfl⟩, rfl⟩
  have hcr : 9 ≤ Nat.card f.range :=
    h9.trans ((Subgroup.card_le_of_le hrange).trans
      (Subgroup.card_map_of_injective B.subtype_injective).le)
  have hkr := Subgroup.card_ker_mul_card_range f
  rw [hB.2] at hkr
  nlinarith

end CFSG.RankThree.PartTwo.Sec21.FF81
