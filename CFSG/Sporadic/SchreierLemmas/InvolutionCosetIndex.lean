module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.FixedPoints

public section

namespace CFSG.Sporadic.SchreierLemmas

open MulAction

variable {G : Type*} [Group G]

theorem eq_one_of_involution_smul_eq {L : Subgroup G} {z : G}
    (hC : Subgroup.centralizer {z} ≤ L)
    (hconj : ∀ t ∈ L, orderOf t = 2 → ∃ l ∈ L, l * z * l⁻¹ = t) {t : G} (htL : t ∈ L)
    (ht : orderOf t = 2) {x : G ⧸ L} (hx : t • x = x) : x = ((1 : G) : G ⧸ L) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    have h1 : g⁻¹ * t * g ∈ L := by
      have h := inv_mem (QuotientGroup.eq.1 (show ((t * g : G) : G ⧸ L) = (g : G ⧸ L) from hx))
      rwa [show ((t * g)⁻¹ * g)⁻¹ = g⁻¹ * t * g by group] at h
    have h2 : orderOf (g⁻¹ * t * g) = 2 := by
      rw [← ht]
      exact (SemiconjBy.orderOf_eq g⁻¹ (by
        change g⁻¹ * t = g⁻¹ * t * g * g⁻¹
        group)).symm
    obtain ⟨l, hl, hlz⟩ := hconj _ h1 h2
    obtain ⟨l', hl', hl'z⟩ := hconj t htL ht
    have hc : l⁻¹ * g⁻¹ * l' ∈ Subgroup.centralizer {z} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : (l⁻¹ * g⁻¹ * l') * z * (l⁻¹ * g⁻¹ * l')⁻¹ = z := by
        calc (l⁻¹ * g⁻¹ * l') * z * (l⁻¹ * g⁻¹ * l')⁻¹ = l⁻¹ * (g⁻¹ * (l' * z * l'⁻¹) * g) * l := by
              group
          _ = z := by rw [hl'z, ← hlz]; group
      calc (l⁻¹ * g⁻¹ * l') * z = (l⁻¹ * g⁻¹ * l') * z * (l⁻¹ * g⁻¹ * l')⁻¹ *
            (l⁻¹ * g⁻¹ * l') := by group
        _ = z * (l⁻¹ * g⁻¹ * l') := by rw [e]
    have hg : g⁻¹ ∈ L := by
      have := L.mul_mem (L.mul_mem hl (hC hc)) (L.inv_mem hl')
      rwa [show l * (l⁻¹ * g⁻¹ * l') * l'⁻¹ = g⁻¹ by group] at this
    exact QuotientGroup.eq.2 (by simpa using inv_mem hg)

theorem involution_coset_index_generation [Finite G] (S : Sylow 2 G) {L : Subgroup G}
    (hSL : (S : Subgroup G) ≤ L) {z : G} (hC : Subgroup.centralizer {z} ≤ L)
    (hconj : ∀ t ∈ L, orderOf t = 2 → ∃ l ∈ L, l * z * l⁻¹ = t) :
    L.index ∣ (Subgroup.centralizer {z}).index ∧ L.index ≡ 1 [MOD Nat.card S] ∧
      ((∀ d, 0 < d → d ∣ (Subgroup.centralizer {z}).index → d ≡ 1 [MOD Nat.card S] → d = 1) →
        L = ⊤) := by
  classical
  have hfix : ∀ s : (S : Subgroup G), s ≠ 1 → ∀ x : G ⧸ L, s • x = x →
      x = ((1 : G) : G ⧸ L) := by
    intro s hs x hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 S.isPGroup' s
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hs (orderOf_eq_one_iff.1 (by rw [hk, pow_zero]))
    have hdvd : 2 ^ (k - 1) ∣ orderOf (s : G) := by
      rw [Subgroup.orderOf_coe, hk]
      exact pow_dvd_pow 2 (Nat.sub_le k 1)
    have ht : orderOf ((s : G) ^ (2 ^ (k - 1))) = 2 := by
      rw [orderOf_pow_of_dvd (by positivity) hdvd, Subgroup.orderOf_coe, hk,
        Nat.pow_div (Nat.sub_le k 1) two_pos, show k - (k - 1) = 1 by omega, pow_one]
    have hst : (s : G) ∈ stabilizer G x := hx
    exact eq_one_of_involution_smul_eq hC hconj (L.pow_mem (hSL s.2) _) ht
      (Subgroup.pow_mem _ hst _)
  have hindex : L.index ≡ 1 [MOD Nat.card S] := by
    have : Fintype (S : Subgroup G) := Fintype.ofFinite _
    have : Fintype (G ⧸ L) := Fintype.ofFinite _
    have : ∀ s : (S : Subgroup G), Fintype (fixedBy (G ⧸ L) s) := fun _ => Fintype.ofFinite _
    have : Fintype (Quotient (orbitRel (S : Subgroup G) (G ⧸ L))) := Fintype.ofFinite _
    have hB := sum_card_fixedBy_eq_card_orbits_mul_card_group (S : Subgroup G) (G ⧸ L)
    have hterm : ∀ s : (S : Subgroup G), s ≠ 1 → Fintype.card (fixedBy (G ⧸ L) s) = 1 := by
      intro s hs
      have e : fixedBy (G ⧸ L) s = {((1 : G) : G ⧸ L)} := by
        ext x
        refine ⟨fun hx => hfix s hs x hx, ?_⟩
        rintro rfl
        change ((s * 1 : G) : G ⧸ L) = ((1 : G) : G ⧸ L)
        exact QuotientGroup.eq.2 (by simpa using inv_mem (hSL s.2))
      rw [Fintype.card_eq_nat_card, e, Nat.card_unique]
    rw [Fintype.sum_eq_add_sum_compl 1, Finset.sum_congr rfl fun s hs =>
      hterm s (Finset.mem_compl.1 hs ∘ Finset.mem_singleton.2), Finset.sum_const,
      Finset.card_compl, Finset.card_singleton, smul_eq_mul, mul_one, Fintype.card_eq_nat_card,
      fixedBy_one_eq_univ, Nat.card_univ, Fintype.card_eq_nat_card (α := (S : Subgroup G))]
      at hB
    change L.index + _ = _ at hB
    have hpos : 0 < Nat.card (S : Subgroup G) := Nat.card_pos
    have hL : 0 < L.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    refine (Nat.modEq_iff_dvd' hL).2 ?_ |>.symm
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card (Quotient (orbitRel (S : Subgroup G) (G ⧸ L))) = m + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
    refine ⟨m, ?_⟩
    rw [hm, add_mul, one_mul] at hB
    rw [mul_comm]
    omega
  refine ⟨Subgroup.index_dvd_of_le hC, hindex, fun h => ?_⟩
  exact Subgroup.index_eq_one.1 (h _ (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le hC) hindex)

end CFSG.Sporadic.SchreierLemmas
