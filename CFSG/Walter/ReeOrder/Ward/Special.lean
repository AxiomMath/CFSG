module

public import CFSG.CharacterTheory.SmallDefect.Exceptional
public import CFSG.Walter.ReeOrder.Ward.Sections

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers

theorem mem_zpowers_of_orderOf_eq' {α : Type*} [Group α] [Fintype α] [IsCyclic α] {x y : α}
    (h : orderOf x = orderOf y) : y ∈ Subgroup.zpowers x := by
  by_contra hy
  have hd0 : 0 < orderOf x := orderOf_pos x
  have hle := IsCyclic.card_pow_eq_one_le (α := α) hd0
  have hsub : insert y (Subgroup.zpowers x : Set α).toFinset ⊆
      Finset.univ.filter (fun a : α => a ^ orderOf x = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Set.mem_toFinset, SetLike.mem_coe] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | ⟨k, rfl⟩
    · rw [h]; exact pow_orderOf_eq_one a
    · simp only
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simpa using hy), Set.toFinset_card] at hcard
  have : Fintype.card (Subgroup.zpowers x) = orderOf x := Fintype.card_zpowers
  have h2 : Fintype.card ↑(Subgroup.zpowers x : Set α) = Fintype.card (Subgroup.zpowers x) := rfl
  omega

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} (S : WardSetup G L q e IV)

theorem Ro_odd : Odd (Nat.card S.W.Ro) := by
  have h1 := S.W.Ro_card
  have h2 := S.W.q_mod
  rcases S.W.e_eq with rfl | rfl
  · have : (Nat.card S.W.Ro : ℤ) % 2 = 1 := by omega
    exact Nat.odd_iff.mpr (by exact_mod_cast this)
  · have : (Nat.card S.W.Ro : ℤ) % 2 = 1 := by omega
    exact Nat.odd_iff.mpr (by exact_mod_cast this)

theorem orderOf_Ro_odd {r : L} (hr : r ∈ S.W.Ro) : Odd (orderOf r) := by
  have hdvd : orderOf r ∣ Nat.card S.W.Ro := by
    rw [← Subgroup.orderOf_mk r hr]
    exact orderOf_dvd_natCard _
  exact Odd.of_dvd_nat S.Ro_odd hdvd

@[expose] def Kset : Set G :=
  {x | ∃ y : L, (∃ g : L, g⁻¹ * y * g ∈ S.W.Ro ∧ g⁻¹ * y * g ≠ 1) ∧
    (x = S.κ y ∨ x = S.J * S.κ y)}

theorem one_not_Kset : (1 : G) ∉ S.Kset := by
  rintro ⟨y, ⟨g, -, hg1⟩, h | h⟩
  · have hy : y = 1 := S.κ_inj (by rw [← h, map_one])
    exact hg1 (by rw [hy]; group)
  · exact S.J_mul_ne y 1 (by rw [← h, map_one])

theorem κ_eq_pow {x : G} {y : L} (hy : Odd (orderOf y)) (hx : x = S.κ y ∨ x = S.J * S.κ y) :
    x ^ (orderOf y + 1) = S.κ y := by
  rcases hx with rfl | rfl
  · rw [← map_pow, pow_succ, pow_orderOf_eq_one, one_mul]
  · exact S.pow_J_mul' hy

theorem Kset_special (S : WardSetup G L q e) :
    IsSpecialSet (Subgroup.centralizer ({S.J} : Set G)) S.Kset := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨y, -, rfl | rfl⟩
    · exact S.κ_mem_centralizer y
    · exact Subgroup.mul_mem _ S.J_mem_centralizer (S.κ_mem_centralizer y)
  · rintro x ⟨y, ⟨g, hg, hg1⟩, hx⟩ h hh
    obtain ⟨w, rfl | rfl⟩ := (S.mem_centralizer_iff h).mp hh
    · refine ⟨w⁻¹ * y * w, ⟨w⁻¹ * g, ?_, ?_⟩, ?_⟩
      · rw [show (w⁻¹ * g)⁻¹ * (w⁻¹ * y * w) * (w⁻¹ * g) = g⁻¹ * y * g by group]
        exact hg
      · rw [show (w⁻¹ * g)⁻¹ * (w⁻¹ * y * w) * (w⁻¹ * g) = g⁻¹ * y * g by group]
        exact hg1
      · rcases hx with rfl | rfl
        · left
          rw [map_mul, map_mul, map_inv]
        · right
          rw [map_mul, map_mul, map_inv]
          calc (S.κ w)⁻¹ * (S.J * S.κ y) * S.κ w = S.J * ((S.κ w)⁻¹ * S.κ y * S.κ w) := by
                rw [← map_inv]
                calc S.κ w⁻¹ * (S.J * S.κ y) * S.κ w = (S.κ w⁻¹ * S.J) * S.κ y * S.κ w := by
                      group
                  _ = (S.J * S.κ w⁻¹) * S.κ y * S.κ w := by rw [S.κ_comm]
                  _ = S.J * (S.κ w⁻¹ * S.κ y * S.κ w) := by group
            _ = S.J * ((S.κ w)⁻¹ * S.κ y * S.κ w) := rfl
    · refine ⟨w⁻¹ * y * w, ⟨w⁻¹ * g, ?_, ?_⟩, ?_⟩
      · rw [show (w⁻¹ * g)⁻¹ * (w⁻¹ * y * w) * (w⁻¹ * g) = g⁻¹ * y * g by group]
        exact hg
      · rw [show (w⁻¹ * g)⁻¹ * (w⁻¹ * y * w) * (w⁻¹ * g) = g⁻¹ * y * g by group]
        exact hg1
      · have hconj : ∀ z : G, (S.J * S.κ w)⁻¹ * z * (S.J * S.κ w) =
            (S.κ w)⁻¹ * (S.J * z * S.J) * S.κ w := by
          intro z
          rw [mul_inv_rev, S.J_inv]
          group
        have hJ : ∀ y' : L, S.J * S.κ y' * S.J = S.κ y' := by
          intro y'
          rw [mul_assoc, S.κ_comm y', ← mul_assoc, S.J_mul, one_mul]
        rcases hx with rfl | rfl
        · left
          rw [hconj, hJ, map_mul, map_mul, map_inv]
        · right
          rw [hconj, show S.J * (S.J * S.κ y) * S.J = S.J * S.κ y by
            rw [← mul_assoc, S.J_mul, one_mul, S.κ_comm]]
          rw [map_mul, map_mul, map_inv]
          calc (S.κ w)⁻¹ * (S.J * S.κ y) * S.κ w = (S.κ w)⁻¹ * S.J * S.κ y * S.κ w := by group
            _ = S.J * (S.κ w)⁻¹ * S.κ y * S.κ w := by
                rw [← map_inv, S.κ_comm]
            _ = S.J * ((S.κ w)⁻¹ * S.κ y * S.κ w) := by group
  · rintro x ⟨y, ⟨g, hg, hg1⟩, hx⟩ a ha
    set r : L := g⁻¹ * y * g with hr
    have hodd : Odd (orderOf y) := by
      have h := S.orderOf_Ro_odd hg
      rwa [show orderOf (g⁻¹ * y * g) = orderOf y by
        rw [show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by rw [inv_inv]]
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]] at h
    have hpow := S.κ_eq_pow hodd hx
    have hconjpow : ∀ n : ℕ, (a⁻¹ * x * a) ^ n = a⁻¹ * x ^ n * a := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ih, pow_succ]; group
    have hC : a⁻¹ * S.κ y * a ∈ Subgroup.centralizer ({S.J} : Set G) := by
      rw [← hpow, ← hconjpow]
      exact Subgroup.pow_mem _ ha _
    have hCc : a⁻¹ * S.κ y * a * S.J = S.J * (a⁻¹ * S.κ y * a) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hC
      exact hC
    have hord : orderOf (a⁻¹ * S.κ y * a) = orderOf y := by
      rw [show a⁻¹ * S.κ y * a = a⁻¹ * S.κ y * a⁻¹⁻¹ by rw [inv_inv],
        ← MulAut.conj_apply, MulEquiv.orderOf_eq, S.orderOf_κ]
    obtain ⟨y', hy'⟩ := S.odd_mem_κ hCc (by rw [hord]; exact hodd)
    have hy'ord : orderOf y' = orderOf y := by rw [← S.orderOf_κ, ← hy', hord]
    have hdvd : orderOf y' ∣ Nat.card S.W.Ro := by
      rw [hy'ord]
      have : orderOf y = orderOf r := by
        rw [hr, show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
          MulEquiv.orderOf_eq]
      rw [this, ← Subgroup.orderOf_mk r hg]
      exact orderOf_dvd_natCard _
    obtain ⟨g', hg'⟩ := S.W.Ro_conj y' hdvd
    set r' : L := g'⁻¹ * y' * g' with hr'
    have hrr' : orderOf (⟨r, hg⟩ : S.W.Ro) = orderOf (⟨r', hg'⟩ : S.W.Ro) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hr, hr',
        show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by rw [inv_inv],
        show g'⁻¹ * y' * g' = g'⁻¹ * y' * g'⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
        MulEquiv.orderOf_eq, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hy'ord]
    have hcyc : IsCyclic S.W.Ro := S.W.Ro_cyclic
    have hmem : (⟨r', hg'⟩ : S.W.Ro) ∈ Subgroup.zpowers (⟨r, hg⟩ : S.W.Ro) :=
      mem_zpowers_of_orderOf_eq' hrr'
    obtain ⟨k, hk⟩ := hmem
    have hk' : r ^ k = r' := by
      have := congrArg Subtype.val hk
      simpa using this
    set B : G := (S.κ g)⁻¹ * a * S.κ g' with hB
    have hBr : B⁻¹ * S.κ r * B = S.κ r' := by
      have h1 : B⁻¹ * S.κ r * B = (S.κ g')⁻¹ * (a⁻¹ * S.κ y * a) * S.κ g' := by
        rw [hB, hr, map_mul, map_mul, map_inv]
        group
      rw [h1, hy', hr', map_mul, map_mul, map_inv]
    have hBmem : B⁻¹ * S.κ r * B ∈ Subgroup.zpowers (S.κ r) := by
      rw [hBr, ← hk', map_zpow]
      exact Subgroup.zpow_mem_zpowers _ _
    have hBC := S.normalizer rfl r hg hg1 B hBmem
    have haeq : a = S.κ g * B * (S.κ g')⁻¹ := by rw [hB]; group
    rw [haeq]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (S.κ_mem_centralizer g) ?_)
      (Subgroup.inv_mem _ (S.κ_mem_centralizer g'))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hBC

end WardSetup

end CFSG.Walter.Ward
