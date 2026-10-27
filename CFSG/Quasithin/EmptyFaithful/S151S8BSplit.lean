module

public import CFSG.Quasithin.EmptyFaithful.S151S8B
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.S151S8

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.GammaExtra

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_sup_of_comm {E F : Subgroup G} (hE : IsPGroup 2 ↥E) (hF : IsPGroup 2 ↥F)
    (hc : ∀ x ∈ E, ∀ y ∈ F, x * y = y * x) (hEF : E ⊓ F = ⊥) : IsPGroup 2 ↥(E ⊔ F) := by
  obtain ⟨a, ha⟩ := hE.exists_card_eq
  obtain ⟨b, hb⟩ := hF.exists_card_eq
  exact IsPGroup.of_card (n := a + b) (by rw [card_sup_of_comm hc hEF, ha, hb, pow_add])

omit [Finite G] in
theorem isPGroup_part {X Y A : Subgroup G} (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hbot : X ⊓ Y = ⊥) (hA : A ≤ X ⊔ Y) (hA2 : IsPGroup 2 ↥A) : IsPGroup 2 ↥(part X Y A) := by
  rintro ⟨x, hx⟩
  obtain ⟨hxX, y, hy, hxy⟩ := (mem_part_iff hc hA).mp hx
  obtain ⟨k, hk⟩ := hA2 ⟨x * y, hxy⟩
  have h1 : (x * y) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [Commute.mul_pow (hc x hxX y hy)] at h1
  have h2 : x ^ 2 ^ k = (y ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hmem : x ^ 2 ^ k ∈ X ⊓ Y := ⟨X.pow_mem hxX _, h2 ▸ Y.inv_mem (Y.pow_mem hy _)⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact ⟨k, Subtype.ext hmem⟩

theorem sylow_split {H L C S : Subgroup G} (hc : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l)
    (hbot : L ⊓ C = ⊥) (hLH : L ≤ H) (hCH : C ≤ H) (hS : IsSylowTwoOf S H)
    (hSL : IsSylowTwoOf (S ⊓ L) L) (hSLC : S ≤ L ⊔ C) : S ≤ (S ⊓ L) ⊔ (S ⊓ C) := by
  have hc' : ∀ y ∈ C, ∀ x ∈ L, y * x = x * y := fun y hy x hx => (hc x hx y hy).symm
  have hbot' : C ⊓ L = ⊥ := by rw [inf_comm]; exact hbot
  have hS2 : IsPGroup 2 ↥S := hS.isPGroup
  have hSCL : S ≤ C ⊔ L := by rwa [sup_comm] at hSLC
  have hP2 : IsPGroup 2 ↥(part C L S) := isPGroup_part hc' hbot' hSCL hS2
  have hQ2 : IsPGroup 2 ↥(part L C S) := isPGroup_part hc hbot hSLC hS2
  have hSLQ : S ⊓ L ≤ part L C S := fun x hx =>
    (mem_part_iff hc hSLC).mpr ⟨hx.2, 1, C.one_mem, by simpa using hx.1⟩
  have hQeq : part L C S = S ⊓ L := hSL.eq_of_le hSLQ (part_le_left _) hQ2
  have hSle : S ≤ part L C S ⊔ part C L S := le_part_sup hc hSLC
  have hcQP : ∀ x ∈ part L C S, ∀ y ∈ part C L S, x * y = y * x := fun x hx y hy =>
    hc x (part_le_left _ hx) y (part_le_left _ hy)
  have hQPbot : part L C S ⊓ part C L S = ⊥ := by
    rw [eq_bot_iff, ← hbot]
    exact inf_le_inf (part_le_left _) (part_le_left _)
  have hT2 : IsPGroup 2 ↥(part L C S ⊔ part C L S) := isPGroup_sup_of_comm hQ2 hP2 hcQP hQPbot
  have hTH : part L C S ⊔ part C L S ≤ H :=
    sup_le ((part_le_left _).trans hLH) ((part_le_left _).trans hCH)
  have hTeq : part L C S ⊔ part C L S = S := hS.eq_of_le hSle hTH hT2
  have hPS : part C L S ≤ S := le_sup_right.trans hTeq.le
  calc S ≤ part L C S ⊔ part C L S := hSle
    _ ≤ (S ⊓ L) ⊔ (S ⊓ C) := by
        rw [hQeq]
        exact sup_le_sup_left (le_inf hPS (part_le_left _)) _

omit [Finite G] in
theorem eq_one_of_odd_orderOf_of_isPGroup {K : Subgroup G} (hK : IsPGroup 2 ↥K) {x : G}
    (hx : x ∈ K) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hK ⟨x, hx⟩
  have h1 : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact hj

theorem oTwoUpper_normalizer_le_centralizer {H L C S : Subgroup G}
    (hc : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) (hbot : L ⊓ C = ⊥) (hHLC : H ≤ L ⊔ C)
    (hsplit : S ≤ (S ⊓ L) ⊔ (S ⊓ C))
    (hN : IsPGroup 2 ↥(L ⊓ Subgroup.normalizer (thompsonJ (S ⊓ L) : Set G))) :
    oTwoUpper (H ⊓ Subgroup.normalizer (thompsonJ S : Set G)) ≤
      Subgroup.centralizer (L : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro n ⟨⟨hnH, hnN⟩, hodd⟩
  obtain ⟨l, hl, c, hcC, rfl⟩ := mem_sup_comm hc (hHLC hnH)
  have hJeq : thompsonJ S ⊓ L = thompsonJ (S ⊓ L) := thompsonJ_inf_eq hc hbot hsplit
  have hJle : thompsonJ (S ⊓ L) ≤ L := (thompsonJ_le_self (S ⊓ L)).trans inf_le_right
  have hlodd : Odd (orderOf l) := by
    have h1 : (l * c) ^ orderOf (l * c) = 1 := pow_orderOf_eq_one _
    rw [Commute.mul_pow (hc l hl c hcC)] at h1
    have h2 : l ^ orderOf (l * c) = (c ^ orderOf (l * c))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmem : l ^ orderOf (l * c) ∈ L ⊓ C :=
      ⟨L.pow_mem hl _, h2 ▸ C.inv_mem (C.pow_mem hcC _)⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hmem)
  have hJmem : ∀ y : G, y ∈ thompsonJ (S ⊓ L) ↔ y ∈ thompsonJ S ∧ y ∈ L := fun y => by
    rw [← hJeq]
    exact Iff.rfl
  have hlN : l ∈ Subgroup.normalizer (thompsonJ (S ⊓ L) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    by_cases hxL : x ∈ L
    · have hconj : l * c * x * (l * c)⁻¹ = l * x * l⁻¹ := by
        have hcx : x * c = c * x := hc x hxL c hcC
        calc l * c * x * (l * c)⁻¹ = l * (c * x) * c⁻¹ * l⁻¹ := by group
          _ = l * (x * c) * c⁻¹ * l⁻¹ := by rw [hcx]
          _ = l * x * l⁻¹ := by group
      have hxlL : l * x * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl)
      have hn := Subgroup.mem_normalizer_iff.mp hnN x
      rw [hconj] at hn
      constructor
      · intro hx
        exact (hJmem _).mpr ⟨hn.mp ((hJmem x).mp hx).1, hxlL⟩
      · intro hx
        exact (hJmem x).mpr ⟨hn.mpr ((hJmem _).mp hx).1, hxL⟩
    · constructor
      · intro hx
        exact absurd (hJle hx) hxL
      · intro hx
        have hxl : l * x * l⁻¹ ∈ L := hJle hx
        have h3 := L.mul_mem (L.mul_mem (L.inv_mem hl) hxl) hl
        have e : l⁻¹ * (l * x * l⁻¹) * l = x := by group
        rw [e] at h3
        exact absurd h3 hxL
  have hl1 : l = 1 :=
    eq_one_of_odd_orderOf_of_isPGroup hN ⟨hl, hlN⟩ hlodd
  rw [hl1, one_mul]
  exact Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx c hcC

end CFSG.Quasithin.S151S8
