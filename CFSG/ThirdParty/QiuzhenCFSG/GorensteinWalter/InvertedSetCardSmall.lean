module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Small cardinalities of inverted sets

For an outside involution `y`, the inverted set `I_H(y) = {x ∈ H |
y * x * y⁻¹ = x⁻¹}` has size at most four in the first-case count.  This
module pins the structure needed when that size is two or three:

* size two: the non-identity element is an involution;
* size three: every non-identity element has order three, so `I_H(y)` is
  the cyclic subgroup of order three, and no two external involutions
  `i * y`, `j * y` commute.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem inverted_pow_mem
    {G : Type u} [Group G] (H : Subgroup G) {y : G} (hy : IsInvolution y)
    {x : G} (hx : x ∈ invertedElements H y) (n : ℕ) :
    x ^ n ∈ invertedElements H y := by
  refine ⟨H.pow_mem hx.1 n, ?_⟩
  calc
    y * x ^ n * y⁻¹ = (y * x * y⁻¹) ^ n :=
      (conj_pow (a := y) (b := x) (i := n)).symm
    _ = (x⁻¹) ^ n := by rw [hx.2]
    _ = (x ^ n)⁻¹ := by exact inv_pow (a := x) (n := n)

private theorem inverted_mul_of_commute
    {G : Type u} [Group G] (H : Subgroup G) {y a b : G} (hy : IsInvolution y)
    (ha : a ∈ invertedElements H y) (hb : b ∈ invertedElements H y)
    (hab : a * b = b * a) :
    a * b ∈ invertedElements H y := by
  refine ⟨H.mul_mem ha.1 hb.1, ?_⟩
  calc
    y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    _ = a⁻¹ * b⁻¹ := by rw [ha.2, hb.2]
    _ = (a * b)⁻¹ := by
      have hInvEq : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
        rw [← mul_inv_rev (a := a) (b := b), ← mul_inv_rev (a := b) (b := a)]
        exact congrArg (fun z : G => z⁻¹) hab
      rw [mul_inv_rev]
      exact hInvEq.symm

/-- A two-element set containing `a` is `{a, b}` for some `b ≠ a`. -/
private lemma set_ncard_two_of_mem {G : Type u} [Group G] {S : Set G}
    (hS : S.ncard = 2) {a : G} (ha : a ∈ S) :
    ∃ b : G, a ≠ b ∧ S = ({a, b} : Set G) := by
  classical
  rcases (Set.ncard_eq_two.mp hS) with ⟨x, y, hxy, hS⟩
  have ha_mem : a ∈ ({x, y} : Set G) := by
    rw [← hS]
    exact ha
  rcases (by simpa using ha_mem) with h | h
  · subst x
    exact ⟨y, hxy, hS⟩
  · subst y
    refine ⟨x, hxy.symm, ?_⟩
    ext z
    rw [hS]
    simp <;> tauto

/-- A three-element set containing `a` is `{a, b, c}` for distinct
`b, c ≠ a`. -/
private lemma set_ncard_three_of_mem {G : Type u} [Group G] {S : Set G}
    (hS : S.ncard = 3) {a : G} (ha : a ∈ S) :
    ∃ b c : G, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ S = ({a, b, c} : Set G) := by
  classical
  rcases (Set.ncard_eq_three.mp hS) with ⟨x, y, z, hxy, hxz, hyz, hS⟩
  have ha_mem : a ∈ ({x, y, z} : Set G) := by
    rw [← hS]
    exact ha
  rcases (by simpa using ha_mem) with h | h | h
  · subst x
    exact ⟨y, z, hxy, hxz, hyz, hS⟩
  · subst y
    refine ⟨x, z, hxy.symm, hyz, hxz, ?_⟩
    ext w
    rw [hS]
    simp <;> tauto
  · subst z
    refine ⟨x, y, hxz.symm, hyz.symm, hxy, ?_⟩
    ext w
    rw [hS]
    simp <;> tauto

/-- Four pairwise-distinct elements form a set of cardinality four. -/
private lemma ncard_four_of_pairwise {G : Type u} [Group G]
    (a b c d : G)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Set G).ncard = 4 := by
  rw [Set.ncard_eq_four]
  exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩

/-- A set containing four pairwise-distinct elements has cardinality at
least four. -/
public theorem ncard_ge_four_of_mem {G : Type u} [Group G] [Finite G]
    (S : Set G) {a b c d : G}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    4 ≤ S.ncard := by
  have hsub : ({a, b, c, d} : Set G) ⊆ S := by
    intro x hx
    rcases (by simpa using hx) with h | h | h | h
    all_goals
      first | simpa [h] using ha | simpa [h] using hb |
             simpa [h] using hc | simpa [h] using hd
  have hle := Set.ncard_le_ncard hsub
  have h4 : ({a, b, c, d} : Set G).ncard = 4 :=
    ncard_four_of_pairwise a b c d hab hac had hbc hbd hcd
  omega

/-- In a three-element set with three pairwise-distinct members, every
member is one of the three. -/
public theorem set_ncard_three_forall_mem_cases {G : Type u} [Group G]
    [Finite G] {S : Set G} (hS : S.ncard = 3)
    {a b c : G} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ x : G, x ∈ S → x = a ∨ x = b ∨ x = c := by
  classical
  intro x hx
  by_cases hxa : x = a
  · exact Or.inl hxa
  by_cases hxb : x = b
  · exact Or.inr (Or.inl hxb)
  · right
    right
    by_contra hxc
    have h4 : 4 ≤ S.ncard := ncard_ge_four_of_mem S ha hb hc hx
      hab hac (Ne.symm hxa) hbc (Ne.symm hxb) (Ne.symm hxc)
    have hS3 : S.ncard = 3 := hS
    omega

/-- If `|I_H(y)| = 2`, every inverted element squares to one. -/
public theorem inverted_card_two_mul_self
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {y t : G} (hy : IsInvolution y)
    (htI : t ∈ invertedElements H y)
    (hcard : Nat.card {x : G // x ∈ invertedElements H y} = 2) :
    t * t = 1 := by
  classical
  by_cases ht1 : t = 1
  · simp [ht1]
  · let S : Set G := invertedElements H y
    have hS : S.ncard = 2 := by
      simpa [S] using hcard
    have hone : (1 : G) ∈ S := ⟨H.one_mem, by simp⟩
    obtain ⟨b, hbne, hS'⟩ := set_ncard_two_of_mem hS hone
    have ht : t ∈ ({1, b} : Set G) := by
      rw [← hS']
      exact htI
    have htb : t = b := by
      rcases (by simpa using ht) with h | h
      · exact False.elim (ht1 h)
      · exact h
    have ht2 : t ^ 2 ∈ S := inverted_pow_mem H hy htI 2
    have ht2mem : t ^ 2 ∈ ({1, b} : Set G) := by
      rw [← hS']
      exact ht2
    rcases (by simpa [htb] using ht2mem) with h | h
    · simpa [← htb, pow_two] using h
    · have hEq' : t ^ 2 = t := by simpa [← htb] using h
      have htEq : t * t = t := by
        simpa [pow_two] using hEq'
      exfalso
      apply ht1
      calc
        t = t * t * t⁻¹ := by group
        _ = t * t⁻¹ := by rw [htEq]
        _ = 1 := by simp

/-- The order-three core: with a distinguished third element `u`, a
three-element inverted set forces every non-identity element to have order
three. -/
private theorem order_eq_three_of_card_three
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {y t u : G} (hy : IsInvolution y)
    (htI : t ∈ invertedElements H y) (htne : t ≠ 1)
    (huS : u ∈ invertedElements H y) (hu_ne_1 : u ≠ 1) (hu_ne_t : u ≠ t)
    (hcases : ∀ x : G, x ∈ invertedElements H y →
      x = 1 ∨ x = t ∨ x = u)
    (hS : (invertedElements H y : Set G).ncard = 3) :
    orderOf t = 3 := by
  classical
  let S : Set G := invertedElements H y
  have hpowT : ∀ n : ℕ, t ^ n ∈ S := fun n => inverted_pow_mem H hy htI n
  have hpowU : ∀ n : ℕ, u ^ n ∈ S := fun n => inverted_pow_mem H hy huS n
  have htInvI : t⁻¹ ∈ S := by
    refine ⟨H.inv_mem htI.1, ?_⟩
    have h1 : y * t⁻¹ * y⁻¹ = (y * t * y⁻¹)⁻¹ := by group
    have h2 : (y * t * y⁻¹)⁻¹ = (t⁻¹)⁻¹ := by rw [htI.2]
    exact h1.trans h2
  have huInvI : u⁻¹ ∈ S := by
    refine ⟨H.inv_mem huS.1, ?_⟩
    have h1 : y * u⁻¹ * y⁻¹ = (y * u * y⁻¹)⁻¹ := by group
    have h2 : (y * u * y⁻¹)⁻¹ = (u⁻¹)⁻¹ := by rw [huS.2]
    exact h1.trans h2
  have hpowTZ : ∀ n : ℤ, t ^ n ∈ S := by
    intro n
    by_cases hn : 0 ≤ n
    · have hz : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
      have h := hpowT n.toNat
      have hEq : t ^ n = t ^ n.toNat := by
        conv_lhs => rw [← hz]
        rw [zpow_natCast]
      rw [hEq]
      exact h
    · have hn' : n = -(n.natAbs : ℤ) := by omega
      have h := inverted_pow_mem H hy htInvI n.natAbs
      have hEq : t ^ n = (t⁻¹) ^ n.natAbs := by
        conv_lhs => rw [hn']
        rw [zpow_neg]
        rw [zpow_natCast, ← inv_pow]
      rw [hEq]
      exact h
  have hpowUZ : ∀ n : ℤ, u ^ n ∈ S := by
    intro n
    by_cases hn : 0 ≤ n
    · have hz : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
      have h := hpowU n.toNat
      have hEq : u ^ n = u ^ n.toNat := by
        conv_lhs => rw [← hz]
        rw [zpow_natCast]
      rw [hEq]
      exact h
    · have hn' : n = -(n.natAbs : ℤ) := by omega
      have h := inverted_pow_mem H hy huInvI n.natAbs
      have hEq : u ^ n = (u⁻¹) ^ n.natAbs := by
        conv_lhs => rw [hn']
        rw [zpow_neg]
        rw [zpow_natCast, ← inv_pow]
      rw [hEq]
      exact h
  have hordT_le : orderOf t ≤ 3 := by
    have hle := Nat.card_le_card_of_injective
      (fun z : ↥(Subgroup.zpowers t) =>
        (⟨(z : G), by
          rcases Subgroup.mem_zpowers_iff.mp z.2 with ⟨n, hn⟩
          rw [← hn]
          exact hpowTZ n⟩ : {x : G // x ∈ S}))
      (by
        intro a b h
        apply Subtype.ext
        simpa using congrArg Subtype.val h)
    rw [Nat.card_zpowers] at hle
    simpa [S, hS] using hle
  have hordT_ne_one : orderOf t ≠ 1 := by
    intro h
    apply htne
    exact orderOf_eq_one_iff.mp h
  have hordT_pos : 0 < orderOf t := orderOf_pos t
  have hordT23 : orderOf t = 2 ∨ orderOf t = 3 := by omega
  rcases hordT23 with hordT2 | hordT3
  · exfalso
    have ht2' : t * t = 1 := by
      have h := pow_orderOf_eq_one t
      rw [hordT2] at h
      simpa [pow_two] using h
    have htInv : t⁻¹ = t := (eq_inv_of_mul_eq_one_right ht2').symm
    have hordU_le : orderOf u ≤ 3 := by
      have hle := Nat.card_le_card_of_injective
        (fun z : ↥(Subgroup.zpowers u) =>
          (⟨(z : G), by
            rcases Subgroup.mem_zpowers_iff.mp z.2 with ⟨n, hn⟩
            rw [← hn]
            exact hpowUZ n⟩ : {x : G // x ∈ S}))
        (by
          intro a b h
          apply Subtype.ext
          simpa using congrArg Subtype.val h)
      rw [Nat.card_zpowers] at hle
      simpa [S, hS] using hle
    have hordU_ne_one : orderOf u ≠ 1 := by
      intro h
      apply hu_ne_1
      exact orderOf_eq_one_iff.mp h
    have hordU_pos : 0 < orderOf u := orderOf_pos u
    have hordU23 : orderOf u = 2 ∨ orderOf u = 3 := by omega
    have hu2S : u ^ 2 ∈ S := hpowU 2
    have hu2cases := hcases (u ^ 2) hu2S
    rcases hu2cases with hu2_1 | hu2_t | hu2_u
    · -- `u` is an involution; `t, u` are distinct involutions
      have hu2' : u * u = 1 := by
        change u ^ 2 = 1 at hu2_1
        simpa [pow_two] using hu2_1
      have huInv : u⁻¹ = u := (eq_inv_of_mul_eq_one_right hu2').symm
      by_cases hcomm : t * u = u * t
      · have htuS : t * u ∈ S := inverted_mul_of_commute H hy htI huS hcomm
        have htu_ne_1 : t * u ≠ 1 := by
          intro h
          apply hu_ne_t
          calc
            u = t⁻¹ * (t * u) := by group
            _ = t⁻¹ * 1 := by rw [h]
            _ = t⁻¹ := by simp
            _ = t := htInv
        have htu_ne_t : t * u ≠ t := by
          intro h
          apply hu_ne_1
          calc
            u = t⁻¹ * (t * u) := by group
            _ = t⁻¹ * t := by rw [h]
            _ = 1 := by simp
        have htu_ne_u : t * u ≠ u := by
          intro h
          apply htne
          calc
            t = (t * u) * u⁻¹ := by group
            _ = u * u⁻¹ := by rw [h]
            _ = 1 := by simp
        have h4 : 4 ≤ S.ncard := ncard_ge_four_of_mem S
          (⟨H.one_mem, by simp⟩) htI huS htuS
          (Ne.symm htne) (Ne.symm hu_ne_1) (Ne.symm htu_ne_1)
          (Ne.symm hu_ne_t) (Ne.symm htu_ne_t) (Ne.symm htu_ne_u)
        have hS3 : S.ncard = 3 := by simpa [S] using hS
        omega
      · -- non-commuting involutions give the third involution `t * u * t`
        let w : G := t * u * t
        have hwH : w ∈ H := H.mul_mem (H.mul_mem htI.1 huS.1) htI.1
        have hwSq : w * w = 1 := by
          dsimp [w]
          calc
            (t * u * t) * (t * u * t) = t * (u * (t * t) * u) * t := by group
            _ = t * (u * 1 * u) * t := by rw [ht2']
            _ = t * (u * u) * t := by simp
            _ = t * 1 * t := by rw [hu2']
            _ = 1 := by
              simp [ht2']
        have hwS : w ∈ S := by
          refine ⟨hwH, ?_⟩
          calc
            y * w * y⁻¹ = (y * t * y⁻¹) * (y * u * y⁻¹) * (y * t * y⁻¹) := by
              dsimp [w]
              group
            _ = t * u * t := by rw [htI.2, huS.2, htInv, huInv]
            _ = w := by rfl
            _ = w⁻¹ := by
              exact eq_inv_of_mul_eq_one_left hwSq
        have hw_ne_1 : w ≠ 1 := by
          intro h
          apply hu_ne_1
          calc
            u = t * (t * u * t) * t := by
              symm
              calc
                t * (t * u * t) * t = (t * t) * u * (t * t) := by group
                _ = u := by rw [ht2']; simp
            _ = t * 1 * t := by
              change t * w * t = t * 1 * t
              rw [h]
            _ = 1 := by
              simp [ht2']
        have hw_ne_t : w ≠ t := by
          intro h
          apply hu_ne_t
          calc
            u = t * (t * u * t) * t := by
              symm
              calc
                t * (t * u * t) * t = (t * t) * u * (t * t) := by group
                _ = u := by rw [ht2']; simp
            _ = t * t * t := by
              change t * w * t = t * t * t
              rw [h]
            _ = t := by
              simp [ht2']
        have hw_ne_u : w ≠ u := by
          intro h
          have hEq : t * u * t = u := by simpa [w] using h
          have hComm : t * u = u * t := by
            have hEq' : t * u * t * t = u * t := by rw [hEq]
            simpa [ht2', mul_assoc] using hEq'
          exact hcomm hComm
        have h4 : 4 ≤ S.ncard := ncard_ge_four_of_mem S
          (⟨H.one_mem, by simp⟩) htI huS hwS
          (Ne.symm htne) (Ne.symm hu_ne_1) (Ne.symm hw_ne_1)
          (Ne.symm hu_ne_t) (Ne.symm hw_ne_t) (Ne.symm hw_ne_u)
        have hS3 : S.ncard = 3 := by simpa [S] using hS
        omega
    · -- `u² = t`: order mismatch
      have hordU2_3 : orderOf (u ^ 2) = 3 := by
        rcases hordU23 with hordU2' | hordU3
        · have hu2one : u ^ 2 = 1 := by
            have h := pow_orderOf_eq_one u
            rwa [hordU2'] at h
          rw [hu2one] at hu2_t
          exact False.elim (htne hu2_t.symm)
        · rw [orderOf_pow' (x := u) (n := 2) (by norm_num), hordU3]
          norm_num
      have hordT2' : orderOf (u ^ 2) = 2 := by
        change u ^ 2 = t at hu2_t
        rw [hu2_t, hordT2]
      omega
    · -- `u² = u` forces `u = 1`
      exfalso
      apply hu_ne_1
      have hEq : u * u = u := by
        change u ^ 2 = u at hu2_u
        simpa [pow_two] using hu2_u
      calc
        u = u * u * u⁻¹ := by group
        _ = u * u⁻¹ := by rw [hEq]
        _ = 1 := by simp
  · exact hordT3

/-- If `|I_H(y)| = 3`, every non-identity inverted element has order
three. -/
public theorem inverted_card_three_orderOf_eq_three
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {y t : G} (hy : IsInvolution y)
    (htI : t ∈ invertedElements H y) (htne : t ≠ 1)
    (hcard : Nat.card {x : G // x ∈ invertedElements H y} = 3) :
    orderOf t = 3 := by
  classical
  let S : Set G := invertedElements H y
  have hS : S.ncard = 3 := by
    simpa [S] using hcard
  have hone : (1 : G) ∈ S := ⟨H.one_mem, by simp⟩
  obtain ⟨b, c, h1b, h1c, hbc, hS'⟩ := set_ncard_three_of_mem hS hone
  have ht : t ∈ ({1, b, c} : Set G) := by
    rw [← hS']
    exact htI
  rcases (by simpa using ht) with ht1 | htb | htc
  · exact False.elim (htne ht1)
  · -- `t = b`, `u = c`
    let u : G := c
    have huS : u ∈ S := by
      rw [hS']
      simp [u]
    have hu_ne_1 : u ≠ 1 := h1c.symm
    have hu_ne_t : u ≠ t := by
      simpa [u, htb] using hbc.symm
    have hcases : ∀ x : G, x ∈ S → x = 1 ∨ x = t ∨ x = u := by
      intro x hx
      have hmem : x ∈ ({1, b, c} : Set G) := by
        rw [← hS']
        exact hx
      rcases (by simpa using hmem) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by simpa [htb] using h))
      · exact Or.inr (Or.inr (by simpa [u] using h))
    exact order_eq_three_of_card_three H hy htI htne huS hu_ne_1 hu_ne_t
      (by intro x hx; exact hcases x hx) hS
  · -- `t = c`, `u = b`
    let u : G := b
    have huS : u ∈ S := by
      rw [hS']
      simp [u]
    have hu_ne_1 : u ≠ 1 := h1b.symm
    have hu_ne_t : u ≠ t := by
      simpa [u, htc] using hbc
    have hcases : ∀ x : G, x ∈ S → x = 1 ∨ x = t ∨ x = u := by
      intro x hx
      have hmem : x ∈ ({1, b, c} : Set G) := by
        rw [← hS']
        exact hx
      rcases (by simpa using hmem) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (by simpa [u, h] using htc.symm))
      · exact Or.inr (Or.inl (by simpa [htc] using h))
    exact order_eq_three_of_card_three H hy htI htne huS hu_ne_1 hu_ne_t
      (by intro x hx; exact hcases x hx) hS

/-- If `|I_H(y)| = 3`, no two external involutions `i * y`, `j * y`
commute for distinct `i, j ∈ I_H(y)`. -/
public theorem inverted_card_three_no_commuting_fiber_pair
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {y : G} (hy : IsInvolution y) (_hyH : y ∉ H)
    (hcard : Nat.card {x : G // x ∈ invertedElements H y} = 3) :
    ∀ i j : G, i ∈ invertedElements H y → j ∈ invertedElements H y → i ≠ j →
      ¬ Commute (i * y) (j * y) := by
  classical
  let I : Type u := {x : G // x ∈ invertedElements H y}
  let : Fintype I := Fintype.ofFinite I
  have hIcard : Fintype.card I = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have honeI : (1 : G) ∈ invertedElements H y := ⟨H.one_mem, by simp⟩
  let a0 : I := ⟨1, honeI⟩
  obtain ⟨t0, ht0⟩ := Fintype.exists_ne_of_one_lt_card
    (by omega : 1 < Fintype.card I) a0
  let t : G := t0.1
  have htI : t ∈ invertedElements H y := t0.2
  have htne : t ≠ 1 := by
    intro h
    apply ht0
    apply Subtype.ext
    exact h
  have hord : orderOf t = 3 :=
    inverted_card_three_orderOf_eq_three H hy htI htne hcard
  have hpowI : ∀ n : ℕ, t ^ n ∈ invertedElements H y :=
    inverted_pow_mem H hy htI
  have hInvT : t⁻¹ = t ^ 2 := by
    exact (eq_inv_of_mul_eq_one_right (by
      calc
        t * t ^ 2 = t ^ 3 := by group
        _ = 1 := by
          rw [← hord]
          exact pow_orderOf_eq_one t)).symm
  have hInvT2 : (t ^ 2)⁻¹ = t := by
    have hEq : t ^ 2 = t⁻¹ := eq_inv_of_mul_eq_one_left (by
      calc
        t ^ 2 * t = t ^ 3 := by group
        _ = 1 := by
          rw [← hord]
          exact pow_orderOf_eq_one t)
    have h1 : (t ^ 2)⁻¹ = (t⁻¹)⁻¹ := by rw [hEq]
    exact h1.trans (inv_inv t)
  have hcase : ∀ x : G, x ∈ invertedElements H y →
      x = 1 ∨ x = t ∨ x = t ^ 2 := by
    intro x hx
    -- the three elements `1, t, t²` are distinct members of the
    -- three-element set, so every member is one of them
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    by_cases hxt : x = t
    · exact Or.inr (Or.inl hxt)
    · right
      right
      by_contra hx2
      let S : Set G := invertedElements H y
      have hS : S.ncard = 3 := by
        simpa [S] using hcard
      have h1S : (1 : G) ∈ S := ⟨H.one_mem, by simp⟩
      have htS : t ∈ S := htI
      have ht2S : t ^ 2 ∈ S := hpowI 2
      have h12 : (1 : G) ≠ t := htne.symm
      have h1t2 : (1 : G) ≠ t ^ 2 := by
        intro h
        have hord' : orderOf (t ^ 2) = 1 := by
          rw [← h, orderOf_one]
        have hord'' : orderOf (t ^ 2) = 3 := by
          rw [orderOf_pow' (x := t) (n := 2) (by norm_num), hord]
          norm_num
        omega
      have ht2t : t ^ 2 ≠ t := by
        intro h
        have hEq : t * t = t := by simpa [pow_two] using h.symm
        apply htne
        calc
          t = t * t * t⁻¹ := by group
          _ = t * t⁻¹ := by rw [hEq]
          _ = 1 := by simp
      -- `1, t, t², x` are four distinct members of the three-element set
      have hx_ne_1 : (1 : G) ≠ x := Ne.symm hx1
      have hx_ne_t : t ≠ x := Ne.symm hxt
      have hx_ne_t2 : t ^ 2 ≠ x := Ne.symm hx2
      have h4 : 4 ≤ S.ncard := ncard_ge_four_of_mem S
        h1S htS ht2S hx
        h12 h1t2 hx_ne_1 (Ne.symm ht2t) hx_ne_t hx_ne_t2
      omega
  have hdiff : ∀ i j : G, i ∈ invertedElements H y → j ∈ invertedElements H y →
      i ≠ j → orderOf (i * j⁻¹) = 3 := by
    intro i j hi hj hij
    rcases hcase i hi with rfl | rfl | rfl <;>
      rcases hcase j hj with rfl | rfl | rfl
    · contradiction
    · calc
        orderOf (1 * t⁻¹) = orderOf (t ^ 2) := by rw [hInvT]; simp
        _ = 3 := by
          rw [orderOf_pow' (x := t) (n := 2) (by norm_num), hord]
          norm_num
    · calc
        orderOf (1 * (t ^ 2)⁻¹) = orderOf t := by
          rw [hInvT2]
          simp
        _ = 3 := hord
    · calc
        orderOf (t * 1⁻¹) = orderOf t := by simp
        _ = 3 := hord
    · contradiction
    · calc
        orderOf (t * (t ^ 2)⁻¹) = orderOf (t * t) := by rw [hInvT2]
        _ = orderOf (t ^ 2) := by
          rw [← pow_two]
        _ = 3 := by
          rw [orderOf_pow' (x := t) (n := 2) (by norm_num), hord]
          norm_num
    · calc
        orderOf ((t ^ 2) * 1⁻¹) = orderOf (t ^ 2) := by simp
        _ = 3 := by
          rw [orderOf_pow' (x := t) (n := 2) (by norm_num), hord]
          norm_num
    · calc
        orderOf ((t ^ 2) * t⁻¹) = orderOf (t ^ 2 * t ^ 2) := by rw [hInvT]
        _ = orderOf (t ^ 4) := by
          rw [← pow_add (n := 2) (m := 2)]
        _ = orderOf t := by
          rw [show t ^ 4 = t by
            calc
              t ^ 4 = t ^ (3 + 1) := by norm_num
              _ = t ^ 3 * t := by
                rw [pow_add]
                simp
              _ = t := by
                rw [show t ^ 3 = 1 by
                  rw [← hord]
                  exact pow_orderOf_eq_one t]
                simp]
        _ = 3 := hord
    · contradiction
  intro i j hi hj hij
  intro hcomm
  have hEq : i * j⁻¹ = j * i⁻¹ := by
    have hyy : y⁻¹ = y := inv_eq_of_mul_eq_one_right
      (by simpa [pow_two] using hy.2)
    have hprod1 : (i * y) * (j * y) = i * j⁻¹ := by
      calc
        (i * y) * (j * y) = i * (y * j * y) := by group
        _ = i * j⁻¹ := by
          have hjy : y * j * y = j⁻¹ := by
            simpa [hyy] using hj.2
          rw [hjy]
    have hprod2 : (j * y) * (i * y) = j * i⁻¹ := by
      calc
        (j * y) * (i * y) = j * (y * i * y) := by group
        _ = j * i⁻¹ := by
          have hiy : y * i * y = i⁻¹ := by
            simpa [hyy] using hi.2
          rw [hiy]
    calc
      i * j⁻¹ = (i * y) * (j * y) := hprod1.symm
      _ = (j * y) * (i * y) := hcomm.eq
      _ = j * i⁻¹ := hprod2
  have hsq : (i * j⁻¹) * (i * j⁻¹) = 1 := by
    calc
      (i * j⁻¹) * (i * j⁻¹) = (i * j⁻¹) * (j * i⁻¹) := by rw [hEq]
      _ = 1 := by group
  have hne : i * j⁻¹ ≠ 1 := by
    intro h
    apply hij
    calc
      i = (i * j⁻¹) * j := by group
      _ = 1 * j := by rw [h]
      _ = j := by simp
  have hord3 : orderOf (i * j⁻¹) = 3 := hdiff i j hi hj hij
  have hord2' : orderOf (i * j⁻¹) = 2 := by
    have hdvd : orderOf (i * j⁻¹) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact False.elim (hne (orderOf_eq_one_iff.mp h1))
    · exact h2
  omega

end CFSG.GorensteinWalter
