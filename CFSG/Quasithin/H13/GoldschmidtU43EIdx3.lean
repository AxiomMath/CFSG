module

public import CFSG.Dihedral.BrauerSuzuki.Helpers

public section

namespace CFSG.Quasithin.H13.U43

theorem u43_isPGroup_two_of_complement {K : Type} [Group K] [Finite K]
    (hO : CFSG.oddCore K = ⊥) {J : Subgroup K} (hJ : J.index = 2)
    (hcompl : CFSG.HasNormalPComplement 2 ↥J) : IsPGroup 2 K := by
  obtain ⟨L, hLn, hLcop, hJL⟩ := hcompl
  have hJn : J.Normal := Subgroup.normal_of_index_eq_two hJ
  have hLodd : Odd (Nat.card L) := Nat.coprime_two_left.mp hLcop
  have hmem : ∀ x : ↥J, Odd (orderOf x) → x ∈ L := by
    intro x hodd
    obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hJL) (QuotientGroup.mk x)
    have h2 : (QuotientGroup.mk x : ↥J ⧸ L) ^ orderOf x = 1 := by
      rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]
      rfl
    have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    have hord : orderOf (QuotientGroup.mk x : ↥J ⧸ L) = 1 := by
      have h3 : orderOf (QuotientGroup.mk x : ↥J ⧸ L) ∣ Nat.gcd (2 ^ k) (orderOf x) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one h2)
      rw [hcop.gcd_eq_one] at h3
      exact Nat.dvd_one.mp h3
    exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp hord)
  have hL'card : Nat.card (L.map J.subtype) = Nat.card L :=
    Subgroup.card_map_of_injective J.subtype_injective
  have hL'odd : Odd (Nat.card (L.map J.subtype)) := by rw [hL'card]; exact hLodd
  have hL'normal : (L.map J.subtype).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨l, hl, rfl⟩ := hn
    have hgJ : g * (l : K) * g⁻¹ ∈ J := hJn.conj_mem _ l.2 g
    have hodd : Odd (orderOf (⟨g * (l : K) * g⁻¹, hgJ⟩ : ↥J)) := by
      rw [Subgroup.orderOf_mk]
      have h1 : orderOf (g * (l : K) * g⁻¹) = orderOf (l : K) :=
        orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (l : K)
      rw [h1, Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat hLodd (by
        have := orderOf_dvd_natCard (⟨l, hl⟩ : L)
        rwa [Subgroup.orderOf_mk] at this)
    exact ⟨_, hmem _ hodd, rfl⟩
  have hle : L.map J.subtype ≤ CFSG.oddCore K :=
    CFSG.BrauerSuzuki.Helpers.normal_odd_le_oddCore _ hL'normal hL'odd
  rw [hO] at hle
  have hL0 : L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective L J.subtype_injective).mp (le_bot_iff.mp hle)
  subst hL0
  have hJp : IsPGroup 2 ↥J := hJL.of_equiv QuotientGroup.quotientBot
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hJp
  have h1 : Nat.card J * J.index = Nat.card K := Subgroup.card_mul_index _
  exact IsPGroup.of_card (n := j + 1) (by rw [← h1, hj, hJ, pow_succ])

open DihedralGroup in
theorem D8_centralizer : ∀ c : DihedralGroup 4, c * c = 1 → c ≠ 1 → c ≠ r 2 →
    ∀ d : DihedralGroup 4, d * c = c * d → d = 1 ∨ d = r 2 ∨ d = c ∨ d = r 2 * c := by
  decide

open DihedralGroup in
theorem D8_noncentral : ∀ c : DihedralGroup 4, c * c = 1 → c ≠ 1 → c ≠ r 2 →
    c = sr 0 ∨ c = r 2 * sr 0 ∨ c = sr 0 * r 1 ∨ c = r 2 * (sr 0 * r 1) := by
  decide

end CFSG.Quasithin.H13.U43
