module

public import CFSG.Quasithin.EmptyFaithful.S1421QA12Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

namespace QA12

@[expose] def LieBorelCoincide : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → IsRankTwoLie n X →
    ∀ U P P' : Subgroup X, IsSylowTwoOf U ⊤ → IsTwoParabolicsOver U P P' →
      Subgroup.normalizer (U : Set X) ⊓ perfectCore P =
          Subgroup.normalizer (U : Set X) ⊓ perfectCore P' →
        IsPSL 3 2 2 X ∧ Subgroup.normalizer (U : Set X) ≤ perfectCore P ⊓ perfectCore P' ∧
          Nat.card (Subgroup.normalizer (U : Set X)) = 3 * Nat.card U

section Hall

variable {X : Type} [Group X]

theorem odd_relIndex_of_isSylowTwoOf {U N : Subgroup X} (hU : IsSylowTwoOf U ⊤) (hUN : U ≤ N) :
    Odd (U.relIndex N) := by
  have h := Subgroup.relIndex_mul_relIndex U N ⊤ hUN le_top
  have hodd : Odd (U.relIndex ⊤) :=
    Nat.not_even_iff_odd.mp fun he => hU.2.2 (even_iff_two_dvd.mp he)
  exact hodd.of_dvd_nat (Dvd.intro _ h)

theorem sup_eq_of_isHallOdd {U B : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (hB : S1421.IsHallOdd B (Subgroup.normalizer (U : Set X))) :
    B ⊔ U = Subgroup.normalizer (U : Set X) :=
  S1421.sup_eq_of_relIndex_two_pow_of_odd hB.1 Subgroup.le_normalizer hB.2.2
    (odd_relIndex_of_isSylowTwoOf hU Subgroup.le_normalizer)

theorem exists_mul_of_isHallOdd {U B : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (hB : S1421.IsHallOdd B (Subgroup.normalizer (U : Set X))) {x : X}
    (hx : x ∈ Subgroup.normalizer (U : Set X)) : ∃ b ∈ B, ∃ u ∈ U, x = b * u := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right B U hB.1
  rw [sup_eq_of_isHallOdd hU hB] at h
  have hx' : x ∈ (↑(Subgroup.normalizer (U : Set X)) : Set X) := hx
  rw [h] at hx'
  obtain ⟨b, hb, u, hu, rfl⟩ := hx'
  exact ⟨b, hb, u, hu, rfl⟩

theorem card_mul_relIndex {B N : Subgroup X} (hBN : B ≤ N) :
    Nat.card B * B.relIndex N = Nat.card N := by
  have h := Subgroup.card_mul_index (B.subgroupOf N)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv] at h

theorem card_mul_card_of_isHallOdd [Finite X] {U B : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (hB : S1421.IsHallOdd B (Subgroup.normalizer (U : Set X))) :
    Nat.card B * Nat.card U = Nat.card (Subgroup.normalizer (U : Set X)) := by
  obtain ⟨k, hk⟩ := hB.2.2
  obtain ⟨a, ha⟩ := hU.2.1.exists_card_eq
  have h1 := card_mul_relIndex hB.1
  have h2 := card_mul_relIndex (Subgroup.le_normalizer : U ≤ Subgroup.normalizer (U : Set X))
  have hr := odd_relIndex_of_isSylowTwoOf hU
    (Subgroup.le_normalizer : U ≤ Subgroup.normalizer (U : Set X))
  rw [hk] at h1
  rw [ha] at h2
  have e : Nat.card B * 2 ^ k = 2 ^ a * U.relIndex (Subgroup.normalizer (U : Set X)) := by
    rw [h1, ← h2, mul_comm]
  have hcopB : Nat.Coprime (2 ^ a) (Nat.card B) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hB.2.1)
  have hcopR : Nat.Coprime (2 ^ k) (U.relIndex (Subgroup.normalizer (U : Set X))) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hr)
  have hka : 2 ^ k ∣ 2 ^ a := hcopR.dvd_of_dvd_mul_right ⟨_, e.symm.trans (mul_comm _ _)⟩
  have hak : 2 ^ a ∣ 2 ^ k := hcopB.dvd_of_dvd_mul_left ⟨_, e⟩
  have hk_eq : 2 ^ k = 2 ^ a := Nat.dvd_antisymm hka hak
  rw [← h1, hk_eq, ha, mul_comm]

theorem normalizer_inf_le_of_isHallOdd {U B L L' : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (hB : S1421.IsHallOdd B (Subgroup.normalizer (U : Set X))) (hUL : U ≤ L) (hUL' : U ≤ L')
    (h : B ⊓ L ≤ B ⊓ L') : Subgroup.normalizer (U : Set X) ⊓ L ≤
      Subgroup.normalizer (U : Set X) ⊓ L' := by
  rintro x ⟨hxN, hxL⟩
  obtain ⟨b, hb, u, hu, rfl⟩ := exists_mul_of_isHallOdd hU hB hxN
  have hbL : b ∈ L := by
    have : b = b * u * u⁻¹ := by group
    rw [this]
    exact L.mul_mem hxL (L.inv_mem (hUL hu))
  exact ⟨hxN, L'.mul_mem (h ⟨hb, hbL⟩).2 (hUL' hu)⟩

theorem card_mul_card_of_mul_eq {N U R : Subgroup X} (hUN : U ≤ N) (hRN : R ≤ N)
    (hdisj : U ⊓ R = ⊥) (hmul : ∀ n ∈ N, ∃ v ∈ U, ∃ r ∈ R, n = v * r) :
    Nat.card U * Nat.card R = Nat.card N := by
  have hd : Disjoint (U.subgroupOf N) (R.subgroupOf N) := by
    rw [Subgroup.disjoint_def]
    intro x hxU hxR
    have : (x : X) ∈ U ⊓ R := ⟨hxU, hxR⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hm : (↑(U.subgroupOf N) : Set ↥N) * (↑(R.subgroupOf N) : Set ↥N) = Set.univ := by
    refine Set.eq_univ_of_forall fun n => ?_
    obtain ⟨v, hv, r, hr, hnvr⟩ := hmul n.1 n.2
    refine ⟨⟨v, hUN hv⟩, hv, ⟨r, hRN hr⟩, hr, Subtype.ext hnvr.symm⟩
  have h := (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd hm).card_mul_card
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv] at h

end Hall

theorem lieTorusCoincide_of_borel (hR1 : LieSylowLePerfectCore) (h : LieBorelCoincide) :
    LieTorusCoincide := by
  intro X _ _ n hn hX U P P' B hU hPar hB heq
  obtain ⟨hUP, hUP'⟩ := hR1 X n hn hX U P P' hU hPar
  have hN : Subgroup.normalizer (U : Set X) ⊓ perfectCore P =
      Subgroup.normalizer (U : Set X) ⊓ perfectCore P' :=
    le_antisymm (normalizer_inf_le_of_isHallOdd hU hB hUP hUP' heq.le)
      (normalizer_inf_le_of_isHallOdd hU hB hUP' hUP heq.ge)
  obtain ⟨hpsl, hNle, hcard⟩ := h X n hn hX U P P' hU hPar hN
  refine ⟨hpsl, hB.1.trans hNle, ?_⟩
  have h3 := card_mul_card_of_isHallOdd hU hB
  rw [hcard] at h3
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h3

end QA12

end CFSG.Quasithin
