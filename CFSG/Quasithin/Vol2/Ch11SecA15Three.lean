module

public import CFSG.Quasithin.Vol2.Ch11SecA15Theta
public import CFSG.Quasithin.Vol2.Ch11SecA15Inner

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped Matrix

theorem exists_noncentral_order_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) K, orderOf g = 3 ∧
      g ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hK'] at this
    have h2 := Finset.card_le_two (a := (0 : K)) (b := 1)
    omega
  have hω3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω hω0
    rwa [hK'] at this
  let v : Fin 3 → K := ![ω, ω ^ 2, 1]
  have hdet : (Matrix.diagonal v).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, mul_one]
    rw [← pow_succ', hω3]
  set g : Matrix.SpecialLinearGroup (Fin 3) K := ⟨Matrix.diagonal v, hdet⟩ with hg
  have hg00 : (g : Matrix (Fin 3) (Fin 3) K) 0 0 = ω := by
    simp [hg, v]
  have hg22 : (g : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    simp [hg, v]
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨g, orderOf_eq_prime ?_ ?_, ?_⟩
  · ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hg]
    simp only [Matrix.diagonal_pow, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;>
      simp [v, Pi.pow_apply, ← pow_mul, hω3]
    · rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  · intro h1
    apply hω1
    rw [← hg00, h1]
    simp
  · intro hc
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    have h1 := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A 0 0) hr
    have h2 := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A 2 2) hr
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, hg00, hg22] at h1 h2
    exact hω1 (h1.symm.trans h2)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem eq_closure_order_three (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hk : KindSL3 L (fsuV T I) n) (hn : n = 2) :
    L = Subgroup.closure {x : G | x ∈ L ∧ orderOf x = 3} := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := hk
  obtain ⟨_, -, -, ⟨eL⟩, -⟩ := h1102 G T L I n h
  have hK4 : Nat.card K = 4 := by rw [hK, hn]; norm_num
  obtain ⟨g, hg3, hgc⟩ := exists_noncentral_order_three hK4
  set φ := eL.trans eK with hφ
  set gb := φ.symm g with hgb
  have hgb3 : orderOf gb = 3 := by rw [hgb, MulEquiv.orderOf_eq]; exact hg3
  have hgbc : ∀ j : ℕ, gb ^ (2 ^ j) ∉ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro j hc
    have hpow : (gb ^ (2 ^ j)) ^ (2 ^ j) = gb := by
      rw [← pow_mul, ← pow_mod_orderOf, hgb3, ← pow_add, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    have hgbz : gb ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rw [← hpow]
      exact Subgroup.pow_mem _ hc _
    apply hgc
    rw [Subgroup.mem_center_iff] at hgbz ⊢
    intro x
    apply φ.symm.injective
    rw [map_mul, map_mul, ← hgb]
    exact hgbz (φ.symm x)
  obtain ⟨x₁, hx₁⟩ := QuotientGroup.mk_surjective gb
  have h3 : x₁ ^ 3 ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hx₁, ← hgb3, pow_orderOf_eq_one]
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, h3⟩
  have hj' : (x₁ ^ 3) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  set x₀ := x₁ ^ (2 ^ j) with hx₀
  have hx₀3 : x₀ ^ 3 = 1 := by rw [hx₀, ← pow_mul, mul_comm, pow_mul, hj']
  have hmk : (QuotientGroup.mk x₀ : ↥L ⧸ CFSG.pCore 2 ↥L) = gb ^ (2 ^ j) := by
    rw [hx₀, QuotientGroup.mk_pow, hx₁]
  have hne : gb ^ (2 ^ j) ≠ 1 := by
    intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hgb3] at h2
    have := (Nat.prime_three.dvd_of_dvd_pow h2)
    omega
  have hx₀o : orderOf (x₀ : G) = 3 := by
    have hfact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Subgroup.orderOf_coe]
    refine orderOf_eq_prime hx₀3 fun h1 => hne ?_
    rw [← hmk, h1, QuotientGroup.mk_one]
  set N := Subgroup.closure {x : G | x ∈ L ∧ orderOf x = 3} with hN
  have hNL : N ≤ L := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := by
    have hconj : ∀ l ∈ L, ∀ k ∈ N, l * k * l⁻¹ ∈ N := by
      intro l hl k hk
      have hmem : (MulAut.conj l).toMonoidHom k ∈ N.map (MulAut.conj l).toMonoidHom := ⟨k, hk, rfl⟩
      rw [hN, map_conj_closure] at hmem
      refine (Subgroup.closure_le N).mpr ?_ hmem
      rintro _ ⟨x, ⟨hxL, hx3⟩, rfl⟩
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · simpa using L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl)
      · rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hx3]
    intro l hl
    exact mem_normalizer_of_conj_le (hconj l hl) (hconj l⁻¹ (L.inv_mem hl))
  have hNn : (N.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  have hNbn : ((N.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  have hNbtop : (N.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
    by_contra hne'
    have hle := le_center_of_normal_ne_top h.fsu.quasisimple hne'
    apply hgbc j
    rw [← hmk]
    have hx₀N : x₀ ∈ N.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.subset_closure ⟨x₀.2, hx₀o⟩
    exact hle ⟨x₀, hx₀N, rfl⟩
  refine (h.fsu.faithful.2.1 N hNL hNn fun x hx => ?_).symm
  have hxmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hx⟩ ∈
      (N.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := hNbtop ▸ Subgroup.mem_top _
  obtain ⟨m, hmN, hmx⟩ := hxmem
  have hq : m⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥L := QuotientGroup.eq.mp hmx
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hq⟩
  have hk' : (m⁻¹ * ⟨x, hx⟩) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, ?_⟩
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ ^ 2 ^ k) : ↥L ⧸ N.subgroupOf L) = 1 := by
    have e1 : (QuotientGroup.mk ⟨x, hx⟩ : ↥L ⧸ N.subgroupOf L) =
        QuotientGroup.mk (m⁻¹ * ⟨x, hx⟩) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff _).mpr hmN,
        inv_one, one_mul]
    rw [QuotientGroup.mk_pow, e1, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  rw [Subgroup.mem_subgroupOf] at h2
  simpa using h2

end CFSG.Quasithin.Vol2.Ch11.SecA
