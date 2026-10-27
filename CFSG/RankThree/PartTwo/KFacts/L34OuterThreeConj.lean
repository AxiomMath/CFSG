module

public import CFSG.RankThree.PartTwo.KFacts.L34TwoElements

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {k : Type*} [Field k]

section Generic

variable {G : Type*} [Group G] {x y : G}

private theorem conj_eq_inv_of_conj_inv_eq {a b c : G} (h : a * b⁻¹ * a⁻¹ = c) :
    a * b * a⁻¹ = c⁻¹ := by
  rw [← h]
  group

private theorem conj_pow_mul_normalForm (hx : x ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) (j k : ℕ) :
    y ^ k * (x * y ^ j * ⁅x, y⁆ ^ k) * (y ^ k)⁻¹ = x * y ^ j := by
  have hz3 : ⁅x, y⁆ ^ 3 = 1 := CFSG.RankThree.Asc83Table.commutator_pow_three hx hzx
  have h1 : y ^ k * x = x * y ^ k * ⁅x, y⁆ ^ (2 * k) := by
    simpa using CFSG.RankThree.Asc83Table.y_pow_mul_x_pow hx hzx hzy 1 k
  have hc : Commute (⁅x, y⁆ ^ (2 * k)) (y ^ j) := (hzy.pow_left _).pow_right _
  have hz3k : ⁅x, y⁆ ^ (2 * k) * ⁅x, y⁆ ^ k = 1 := by
    rw [← pow_add, show 2 * k + k = 3 * k by ring, pow_mul, hz3, one_pow]
  rw [mul_inv_eq_iff_eq_mul]
  calc y ^ k * (x * y ^ j * ⁅x, y⁆ ^ k)
      = (y ^ k * x) * y ^ j * ⁅x, y⁆ ^ k := by simp only [mul_assoc]
    _ = x * y ^ k * (⁅x, y⁆ ^ (2 * k) * y ^ j) * ⁅x, y⁆ ^ k := by
        rw [h1]
        simp only [mul_assoc]
    _ = x * y ^ k * (y ^ j * ⁅x, y⁆ ^ (2 * k)) * ⁅x, y⁆ ^ k := by rw [hc.eq]
    _ = x * (y ^ k * y ^ j) * (⁅x, y⁆ ^ (2 * k) * ⁅x, y⁆ ^ k) := by simp only [mul_assoc]
    _ = x * y ^ j * y ^ k := by
        rw [hz3k, mul_one, (Commute.pow_pow_self y k j).eq]
        simp only [mul_assoc]

private theorem exists_conj_eq_x_mul_y_pow_of_not_mem (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) {H : Subgroup G} (hyH : y ∈ H)
    (hzH : ⁅x, y⁆ ∈ H) {β : G} (hβ : β ∈ Subgroup.closure ({x, y} : Set G)) (hβH : β ∉ H) :
    ∃ (h : G) (j : ℕ), h * β * h⁻¹ = x * y ^ j ∨ h * β * h⁻¹ = (x * y ^ j)⁻¹ := by
  obtain ⟨i, j, k, hi, -, -, rfl⟩ :=
    CFSG.SectionRank.LocalWitness.mem_closure_normalForm (by norm_num) hx hy hzx hzy hβ
  interval_cases i
  · exact (hβH (by
      rw [pow_zero, one_mul]
      exact H.mul_mem (H.pow_mem hyH j) (H.pow_mem hzH k))).elim
  · exact ⟨y ^ k, j, Or.inl (by
      rw [pow_one]
      exact conj_pow_mul_normalForm hx hzx hzy j k)⟩
  · have hβ3 := CFSG.RankThree.Asc83Table.pow_three_eq_one_of_mem hx hzx hzy hy hβ
    have hc : Commute (⁅x, y⁆ ^ k) (x ^ 2 * y ^ j) :=
      ((hzx.pow_left k).pow_right 2).mul_right ((hzy.pow_left k).pow_right j)
    have hx4 : x ^ (2 * 2) = x := by
      rw [show 2 * 2 = 3 + 1 by rfl, pow_add, hx, one_mul, pow_one]
    have hsq : (x ^ 2 * y ^ j * ⁅x, y⁆ ^ k)⁻¹ =
        x * y ^ (2 * j) * ⁅x, y⁆ ^ (2 * 2 * j + k * 2) := by
      rw [← sq_eq_inv_of_pow_three hβ3, hc.symm.mul_pow,
        CFSG.RankThree.Asc83Table.sq_x_pow_mul_y_pow hx hzx hzy 2 j, hx4, ← pow_mul, pow_add]
      simp only [mul_assoc]
    refine ⟨y ^ (2 * 2 * j + k * 2), 2 * j, Or.inr (conj_eq_inv_of_conj_inv_eq ?_)⟩
    rw [hsq]
    exact conj_pow_mul_normalForm hx hzx hzy (2 * j) (2 * 2 * j + k * 2)

private theorem mul_pow_mem_three (hy : y ^ 3 = 1) (j : ℕ) :
    x * y ^ j ∈ ({x, x * y, x * y ^ 2} : Set G) := by
  have hj : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rw [pow_eq_pow_mod j hy]
  rcases hj with h | h | h <;> rw [h] <;> simp

end Generic

section Aut

theorem exists_conj_mem_pglSylow (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1)
    {α : MulAut (projectiveSL 3 k)} (hα : orderOf α = 3) :
    ∃ g : MulAut (projectiveSL 3 k), g * α * g⁻¹ ∈ pglSylow u := by
  haveI : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  haveI : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card (MulAut (projectiveSL 3 k))).factorization 3 = 3 := by
    rw [card_mulAut hk]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 241920 = 3 ^ 3 * 8960 by norm_num) (by norm_num)
  have hP : Nat.card (pglSylow (k := k) u) =
      3 ^ (Nat.card (MulAut (projectiveSL 3 k))).factorization 3 := by
    rw [(pglSylow_transposition hk hu).1, hfac]
    norm_num
  have hα3 : IsPGroup 3 (Subgroup.zpowers α) :=
    IsPGroup.of_card (p := 3) (n := 1) (by rw [Nat.card_zpowers, hα]; norm_num)
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_map_conj_le
    (L := MulAut (projectiveSL 3 k)) (p := 3) (P := pglSylow (k := k) u) hP hα3
  have hmem : MulAut.conj g α ∈ pglSylow (k := k) u :=
    hg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (Subgroup.mem_zpowers α))
  exact ⟨g, by rwa [MulAut.conj_apply] at hmem⟩

theorem exists_conj_eq_of_outer (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1)
    {α : MulAut (projectiveSL 3 k)} (hα : orderOf α = 3)
    (hout : α ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range) :
    ∃ g : MulAut (projectiveSL 3 k), ∃ w ∈ ({xDiag u, xDiag u * yInn, xDiag u * yInn ^ 2} :
      Set (MulAut (projectiveSL 3 k))), g * α * g⁻¹ = w ∨ g * α * g⁻¹ = w⁻¹ := by
  obtain ⟨g, hgS⟩ := exists_conj_mem_pglSylow hk hu hα
  obtain ⟨hx, hy, hz, hzx, hzy, -⟩ := sylowGen_props hk hu
  change xDiag u ^ 3 = 1 at hx
  change yInn ^ 3 = 1 at hy
  change ⁅xDiag u, yInn⁆ = MulAut.conj (aP u)⁻¹ at hz
  change Commute ⁅xDiag u, yInn⁆ (xDiag u) at hzx
  change Commute ⁅xDiag u, yInn⁆ yInn at hzy
  have hβ : g * α * g⁻¹ ∈ Subgroup.closure ({xDiag u, yInn} :
      Set (MulAut (projectiveSL 3 k))) := hgS
  have hβout : g * α * g⁻¹ ∉
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range :=
    fun h => hout ((CFSG.RankThree.PartTwo.KFacts.isInnerAut_conj_iff g α).mp h)
  obtain ⟨h, j, hj⟩ := exists_conj_eq_x_mul_y_pow_of_not_mem hx hy hzx hzy
    (H := (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range)
    ⟨bP, rfl⟩ ⟨(aP u)⁻¹, hz.symm⟩ hβ hβout
  refine ⟨h * g, xDiag u * yInn ^ j, mul_pow_mem_three hy j, ?_⟩
  have e : h * g * α * (h * g)⁻¹ = h * (g * α * g⁻¹) * h⁻¹ := by group
  rwa [e]

theorem exists_orderOf_five_or_seven_fixed_of_witnesses (hk : Nat.card k = 4)
    (h5 : ∀ u : kˣ, u ≠ 1 → ∃ y : projectiveSL 3 k, orderOf y = 5 ∧ xDiag u y = y)
    (h7 : ∀ u : kˣ, u ≠ 1 → ∃ y : projectiveSL 3 k, orderOf y = 7 ∧
      (xDiag u * yInn : MulAut (projectiveSL 3 k)) y = y)
    (h7' : ∀ u : kˣ, u ≠ 1 → ∃ y : projectiveSL 3 k, orderOf y = 7 ∧
      (xDiag u * yInn ^ 2 : MulAut (projectiveSL 3 k)) y = y)
    {X : Type*} [Group X] (χ : X ≃* projectiveSL 3 k) {α : MulAut X} (hα : orderOf α = 3)
    (hout : α ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ y : X, (orderOf y = 5 ∨ orderOf y = 7) ∧ α y = y := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have hα' : orderOf (MulAut.congr χ α) = 3 := by rw [MulEquiv.orderOf_eq, hα]
  have hout' : MulAut.congr χ α ∉
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range :=
    fun h => hout ((CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr χ α).mp h)
  obtain ⟨g, w, hw, hgw⟩ := exists_conj_eq_of_outer hk hu hα' hout'
  obtain ⟨t, hto, hwt⟩ : ∃ t : projectiveSL 3 k, (orderOf t = 5 ∨ orderOf t = 7) ∧ w t = t := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · obtain ⟨t, ht, htf⟩ := h5 u hu
      exact ⟨t, Or.inl ht, htf⟩
    · obtain ⟨t, ht, htf⟩ := h7 u hu
      exact ⟨t, Or.inr ht, htf⟩
    · obtain ⟨t, ht, htf⟩ := h7' u hu
      exact ⟨t, Or.inr ht, htf⟩
  have hwinv : w⁻¹ t = t := by
    have := MulAut.inv_apply_self _ w t
    rwa [hwt] at this
  have hfix : (g * MulAut.congr χ α * g⁻¹) t = t := by
    rcases hgw with h | h
    · rw [h]
      exact hwt
    · rw [h]
      exact hwinv
  have hfix' : MulAut.congr χ α (g⁻¹ t) = g⁻¹ t := by
    have h1 : g (MulAut.congr χ α (g⁻¹ t)) = t := by
      have := hfix
      rwa [MulAut.mul_apply, MulAut.mul_apply] at this
    calc MulAut.congr χ α (g⁻¹ t) = g⁻¹ (g (MulAut.congr χ α (g⁻¹ t))) :=
          (MulAut.inv_apply_self _ g _).symm
      _ = g⁻¹ t := by rw [h1]
  refine ⟨χ.symm (g⁻¹ t), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
    exact hto
  · apply χ.injective
    rw [MulEquiv.apply_symm_apply]
    simpa [MulAut.congr_apply] using hfix'

end Aut

end CFSG.RankThree.PartTwo.KFacts.L34
