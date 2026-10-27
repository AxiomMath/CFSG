module

public import CFSG.RankThree.PartOne.S12.LinAlg

public section

namespace CFSG.RankThree.PartOne.N143

open scoped Pointwise

section Card

variable {A B : Type*} [Group A] [Group B]

theorem card_eq_range_mul_ker (f : A →* B) : Nat.card A = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem card_eq_map_mul_inf_ker (π : A →* B) (S : Subgroup A) :
    Nat.card S = Nat.card (S.map π) * Nat.card (S ⊓ π.ker : Subgroup A) := by
  have h := card_eq_range_mul_ker (π.domRestrict S)
  have h1 : (π.domRestrict S).range = S.map π := by
    ext b
    simp [Subgroup.mem_map]
  have h2 : Nat.card (π.domRestrict S).ker = Nat.card (S ⊓ π.ker : Subgroup A) := by
    rw [MonoidHom.ker_domRestrict, ← Subgroup.card_map_of_injective S.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [h1, h2] at h
  exact h

end Card

theorem card_subgroupOf_of_le {H : Type*} [Group H] {S T : Subgroup H} (h : S ≤ T) :
    Nat.card (S.subgroupOf T) = Nat.card S := by
  rw [← Subgroup.card_map_of_injective T.subtype_injective, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 h]

theorem pow_apply_of_apply {G : Type*} [Group G] {A : Subgroup G} {z : MulAut A} {k : ℕ}
    (hz : ∀ a : A, z a = a ^ k) (n : ℕ) (a : A) : (z ^ n) a = a ^ (k ^ n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, hz, map_pow, ih, ← pow_mul, pow_succ]

section ElemNine

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem card_mulAut_dvd_forty_eight (E : Subgroup G) [CFSG.IsElementaryAbelian 3 E]
    (hcard : Nat.card E = 9) : Nat.card (MulAut E) ∣ 48 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f⟩ := LinAlg.exists_coords (p := 3) E (n := 2) (by rw [hcard]; norm_num)
  have hinj := LinAlg.coordGL_injective f
  have h1 : Nat.card (MulAut E) ∣ Nat.card (GL (Fin 2) (ZMod 3)) :=
    Subgroup.card_dvd_of_injective _ hinj
  have h2 : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
    rw [Matrix.card_GL_field]
    simp [Fin.prod_univ_two, ZMod.card]
  rwa [h2] at h1

theorem three_subgroup_card_le (E : Subgroup G) [CFSG.IsElementaryAbelian 3 E]
    (hcard : Nat.card E = 9) (S : Subgroup (MulAut E)) (hS : IsPGroup 3 S) : Nat.card S ≤ 3 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS
  have hd : Nat.card S ∣ 48 :=
    (Subgroup.card_subgroup_dvd_card S).trans (card_mulAut_dvd_forty_eight E hcard)
  rw [hk] at hd ⊢
  by_contra hlt
  have : 2 ≤ k := by
    by_contra h2
    have : k ≤ 1 := by omega
    interval_cases k <;> simp_all
  have h9 : 9 ∣ 3 ^ k := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le this
    exact ⟨3 ^ m, by ring⟩
  have := h9.trans hd
  omega

theorem card_le_three_mul_ker (E : Subgroup G) [CFSG.IsElementaryAbelian 3 E]
    (hcard : Nat.card E = 9) {P : Type*} [Group P] [Finite P] (hP : IsPGroup 3 P)
    (ρ : P →* MulAut E) : Nat.card P ≤ 3 * Nat.card ρ.ker := by
  have h := card_eq_range_mul_ker ρ
  have hr : IsPGroup 3 ρ.range := by
    have := hP.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    exact this
  have h3 := three_subgroup_card_le E hcard ρ.range hr
  rw [h]
  exact Nat.mul_le_mul_right _ h3

end ElemNine

theorem closure_comm_exp' {G : Type*} [Group G] {p : ℕ} (S : Set G)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hexp : ∀ a ∈ S, a ^ p = 1) :
    (∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a) ∧
      ∀ a ∈ Subgroup.closure S, a ^ p = 1 := by
  have h1 : ∀ a ∈ Subgroup.closure S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {b} :=
      (Subgroup.closure_le _).mpr fun x hx y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hcomm y hb x hx
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b rfl).symm
  have h2 : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    intro a ha b hb
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {a} :=
      (Subgroup.closure_le _).mpr fun x hx y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact h1 y ha x hx
    exact (Subgroup.mem_centralizer_iff.mp (hle hb) a rfl)
  refine ⟨h2, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hexp x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := h2 x hx y hy
    rw [hc.mul_pow, ihx, ihy, mul_one]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]


end CFSG.RankThree.PartOne.N143
