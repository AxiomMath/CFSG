module

public import CFSG.Sporadic.Fi24.ExtClass
public import CFSG.Sporadic.Fi24.ExtFi23

public section

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G] {x y : G}
    (hxy : x * y ≠ y * x) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    have hy : y ∈ Subgroup.center G := by rw [h]; trivial
    exact hxy (Subgroup.mem_center_iff.1 hy x)

theorem commutator_eq_top_of_simple {G : Type*} [Group G] [IsSimpleGroup G] {x y : G}
    (hxy : x * y ≠ y * x) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    have hc : ⁅x, y⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hxy hc
  · exact h

theorem mul_ne_mul_of_orders {G : Type*} [Group G] {x y : G} {m n p : ℕ} (hx : x ^ m = 1)
    (hy : y ^ n = 1) (hp : orderOf (x * y) = p) (hdvd : ¬p ∣ m * n) : x * y ≠ y * x := by
  intro h
  apply hdvd
  rw [← hp]
  apply orderOf_dvd_of_pow_eq_one
  rw [(Commute.mul_pow h (m * n)), pow_mul, hx, one_pow, mul_comm m n, pow_mul, hy, one_pow,
    one_mul]

theorem a_mul_b_ne : a * b ≠ b * a :=
  mul_ne_mul_of_orders (G := J) a_sq b_cube orderOf_ab (by norm_num)

theorem center_J : Subgroup.center J = ⊥ := by
  have := isSimpleGroup_J
  exact center_eq_bot_of_simple (G := J) a_mul_b_ne

theorem commutator_J : commutator J = ⊤ := by
  have := isSimpleGroup_J
  exact commutator_eq_top_of_simple (G := J) a_mul_b_ne

theorem fi23_a_mul_y_ne : Fi23.a * Fi23.y ≠ Fi23.y * Fi23.a :=
  mul_ne_mul_of_orders (G := Fi23.J) Fi23.a_sq Fi23.y_pow Fi23.orderOf_ay (by norm_num)

theorem center_M :
    Subgroup.center M = ⊥ := by
  have := isSimpleGroup_M
  refine center_eq_bot_of_simple (G := M) (x := fi23EquivM.symm Fi23.a)
    (y := fi23EquivM.symm Fi23.y) ?_
  rw [← map_mul, ← map_mul, Ne, fi23EquivM.symm.injective.eq_iff]
  exact fi23_a_mul_y_ne

noncomputable abbrev MR :
    Subgroup R := M.map jR

@[expose] noncomputable def mREquiv :
    MR ≃* M := (M.equivMapOfInjective jR jR_injective).symm

@[expose] noncomputable def fi23EquivMR :
    MR ≃* Blueprint.NativeSporadic.Fi23 :=
  mREquiv.trans fi23Equiv

theorem commute_tR_iff
    (g : J) : jR g * tR = tR * jR g ↔ g ∈ M := by
  rw [mem_M_iff]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    exact h'
  · intro h; exact Subtype.ext h

theorem centralizer_tR :
    Subgroup.centralizer {tR} = Subgroup.zpowers tR ⊔ MR := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    obtain ⟨g, rfl | rfl⟩ := eq_jR_or x
    · exact Subgroup.mem_sup_right ⟨g, (commute_tR_iff g).1 hx, rfl⟩
    · have hg : g ∈ M := by
        apply (commute_tR_iff g).1
        calc jR g * tR = jR g * tR * tR * tR := by
              rw [mul_assoc (jR g * tR), tR_mul_tR, mul_one]
          _ = tR * (jR g * tR) * tR := by rw [hx]
          _ = tR * jR g := by simp only [mul_assoc, tR_mul_tR, mul_one]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨g, hg, rfl⟩)
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers tR))
  · rw [sup_le_iff, Subgroup.zpowers_le]
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 ((commute_tR_iff g).2 hg)

theorem tR_zpow
    (k : ℤ) : tR ^ k = 1 ∨ tR ^ k = tR := by
  have h2 : tR ^ (2 : ℤ) = 1 := by rw [zpow_two, tR_mul_tR]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem zpowers_tR_inf_MR :
    Subgroup.zpowers tR ⊓ MR = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx1
  rcases tR_zpow k with h | h
  · exact h
  · exfalso
    rw [h] at hx2
    obtain ⟨g, -, hg⟩ := hx2
    exact tR_not_mem_JR (hg ▸ jR_mem_JR g)

theorem zpowers_tR_le_centralizer_MR :
    Subgroup.zpowers tR ≤ Subgroup.centralizer (MR : Set R) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  rintro _ ⟨g, hg, rfl⟩
  exact (commute_tR_iff g).2 hg

theorem center_R :
    Subgroup.center R = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_center_iff] at hz
  rw [Subgroup.mem_bot]
  obtain ⟨j, rfl | rfl⟩ := eq_jR_or z
  · have hj : j ∈ Subgroup.center J := Subgroup.mem_center_iff.2 fun g =>
      jR_injective (by rw [map_mul, map_mul]; exact hz (jR g))
    rw [center_J, Subgroup.mem_bot] at hj
    rw [hj, map_one]
  · exfalso
    have hjM : j ∈ M := by
      apply (commute_tR_iff j).1
      have h := hz tR
      calc jR j * tR = tR * (jR j * tR) * tR := by
            rw [h, mul_assoc, tR_mul_tR, mul_one]
        _ = tR * jR j := by simp only [mul_assoc, tR_mul_tR, mul_one]
    have hjc : (⟨j, hjM⟩ : M) ∈ Subgroup.center M := Subgroup.mem_center_iff.2 fun g => by
      apply Subtype.ext
      apply jR_injective
      have h := hz (jR g)
      have hg := (commute_tR_iff g).2 g.2
      show jR (g * j) = jR (j * g)
      rw [map_mul, map_mul]
      calc jR g * jR j = jR g * (jR j * tR) * tR := by
            rw [mul_assoc (jR g), mul_assoc (jR j), tR_mul_tR, mul_one]
        _ = jR j * tR * jR g * tR := by rw [h]
        _ = jR j * jR g := by rw [mul_assoc (jR j), ← hg]; simp only [mul_assoc, tR_mul_tR, mul_one]
    rw [center_M, Subgroup.mem_bot] at hjc
    have hj1 : j = 1 := by have := congrArg Subtype.val hjc; exact this
    subst hj1
    have h := hz (jR a)
    rw [map_one, one_mul] at h
    have haM : a ∈ M := (commute_tR_iff a).1 h
    exact p1_ne_root haM

theorem commutator_R :
    commutator R = JR := by
  apply le_antisymm
  · have : JR.Normal := normal_JR
    have hc : Nat.card (R ⧸ JR) = 2 := index_JR
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := isCyclic_of_prime_card hc
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply,
      map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (IsCyclic.commGroup).mul_comm _ _
  · rw [← range_jR, MonoidHom.range_eq_map, ← commutator_J, commutator_def, commutator_def,
      Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top

end CFSG.Sporadic.Fi24
