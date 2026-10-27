module

public import CFSG.Walter.ReeOrder.Ward.Columns4
public import CFSG.Walter.ReeOrder.Ward.Parity

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  (S : WardSetup G L q e)

include S in
theorem no_order_four (y : L) : orderOf y ≠ 4 := by
  intro h4
  obtain ⟨g, ρ, hρ, hg⟩ := S.W.even_conj y (by rw [h4]; exact even_iff_two_dvd.mpr (by norm_num))
  have ho : orderOf (g⁻¹ * y * g) = 4 := by
    rw [show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, h4]
  rw [hg] at ho
  have hcomm : Commute S.W.J' ρ := (S.W.So_comm ρ hρ).symm
  have hJ2 : S.W.J' ^ 2 = 1 := by rw [← S.W.orderOf_J']; exact pow_orderOf_eq_one _
  have hsq : (S.W.J' * ρ) ^ 2 = ρ ^ 2 := by rw [hcomm.mul_pow, hJ2, one_mul]
  have hρ4 : ρ ^ 4 = 1 := by
    have : (S.W.J' * ρ) ^ 4 = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, ← pow_mul] at this
    exact this
  have hodd : orderOf ρ ∣ Nat.card S.W.So := by
    have := orderOf_dvd_natCard (⟨ρ, hρ⟩ : S.W.So)
    rwa [Subgroup.orderOf_mk] at this
  have hSo : Odd (Nat.card S.W.So) := by rw [← Fintype.card_eq_nat_card]; exact S.So_odd
  have h1 : orderOf ρ = 1 := by
    have hd4 : orderOf ρ ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hρ4
    have hodd' : Odd (orderOf ρ) := Odd.of_dvd_nat hSo hodd
    exact (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd')).eq_one_of_dvd hd4
  rw [orderOf_eq_one_iff.mp h1, mul_one, S.W.orderOf_J'] at ho
  norm_num at ho

include S in
theorem exists_V : ∃ V : Subgroup L, Nat.card V = 4 ∧ ∀ v ∈ V, v * v = 1 := by
  set C := Subgroup.centralizer ({S.W.J'} : Set L) with hC
  have h4 : 2 ^ 2 ∣ Nat.card C := by
    have h1 := S.W.card_centralizer_J'
    have h2 := S.W.So_card
    refine ⟨Nat.card S.W.So, ?_⟩
    have : (Nat.card C : ℤ) = 4 * Nat.card S.W.So := by rw [hC, h1, ← h2]
    exact_mod_cast this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
  refine ⟨K.map C.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
    norm_num
  · rintro v ⟨k, hk, rfl⟩
    have hdvd : orderOf k ∣ 4 := by
      have := orderOf_dvd_natCard (⟨k, hk⟩ : K)
      rw [Subgroup.orderOf_mk, hK] at this
      exact this
    have hne : orderOf (k : L) ≠ 4 := S.no_order_four _
    rw [show orderOf k = orderOf (k : L) from (Subgroup.orderOf_coe k).symm] at hdvd
    have h2 : orderOf (k : L) ∣ 2 := by
      have : orderOf (k : L) ∣ 2 ^ 2 := hdvd
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp this
      interval_cases i
      · rw [hi']; norm_num
      · rw [hi']; norm_num
      · exact absurd hi' (by simpa using hne)
    rw [← sq]
    simp only [Subgroup.coe_subtype]
    exact orderOf_dvd_iff_pow_eq_one.mp h2

theorem sylow8 {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {t : ℤ} (ht : χ S.J = t) :
    (8 : ℤ) ∣ deg χ + 7 * t := by
  obtain ⟨V, hV4, hV⟩ := S.exists_V
  set φ : Subgroup.zpowers S.J × V →* G :=
    S.ι.comp ((MonoidHom.id _).prodMap V.subtype) with hφ
  have hclass : BlocksIsClassFunction χ :=
    blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ)
  obtain ⟨n, hn⟩ := exists_natCast_restrict φ hχ (one_mem_blocksIrr _)
  have hval : ∀ p : Subgroup.zpowers S.J × V, p ≠ 1 → χ (φ p) = t := by
    intro p hp
    have hφp : φ p = (p.1 : G) * S.κ p.2 := rfl
    have hsq : φ p * φ p = 1 := by
      rw [hφp]
      have hz : ((p.1 : G)) * p.1 = 1 := by
        rcases S.Z_cases p.1 with h | h
        · rw [h]; simp
        · rw [h]; exact S.J_mul
      have hv : (p.2 : L) * p.2 = 1 := hV _ p.2.2
      calc (p.1 : G) * S.κ p.2 * ((p.1 : G) * S.κ p.2)
          = ((p.1 : G) * p.1) * (S.κ p.2 * S.κ p.2) := by
            rw [mul_assoc, ← mul_assoc (S.κ _), ← (S.commute_zpowers p.1 p.2).eq]
            group
        _ = 1 := by rw [hz, ← map_mul, hv, map_one, mul_one]
    have hne : φ p ≠ 1 := by
      intro h1
      apply hp
      have hinj : Function.Injective φ := by
        rw [hφ]
        exact S.ι_injective.comp (Prod.map_injective.mpr ⟨Function.injective_id,
          Subgroup.subtype_injective _⟩)
      exact hinj (by rw [h1, map_one])
    have hord : orderOf (φ p) = 2 := orderOf_eq_prime (by rw [sq, hsq]) hne
    obtain ⟨c, hc⟩ := isConj_iff.mp (S.involution_conj _ hord)
    rw [← ht]
    calc χ (φ p) = χ (c * φ p * c⁻¹) := (hclass (φ p) c).symm
      _ = χ S.J := by rw [hc]
  have hcard : Nat.card (Subgroup.zpowers S.J × V) = 8 := by
    rw [Nat.card_prod, S.card_Z, hV4]
  have hsum : ∑ p : Subgroup.zpowers S.J × V, χ (φ p) = (deg χ : ℂ) + 7 * t := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1), map_one, ← deg_eq hχ,
      Finset.sum_congr rfl fun p hp => hval p (Finset.ne_of_mem_erase hp),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_eq_nat_card, hcard]
    push_cast
    ring
  have hinner : BlocksInnerProduct (χ ∘ φ) (1 : Subgroup.zpowers S.J × V → ℂ) =
      (8 : ℂ)⁻¹ * ((deg χ : ℂ) + 7 * t) := by
    unfold BlocksInnerProduct
    rw [hcard, ← hsum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    simp
  rw [hinner] at hn
  refine ⟨n, ?_⟩
  have : ((deg χ + 7 * t : ℤ) : ℂ) = ((8 * n : ℤ) : ℂ) := by
    push_cast
    linear_combination 8 * hn
  exact_mod_cast this

end WardSetup

end CFSG.Walter.Ward
