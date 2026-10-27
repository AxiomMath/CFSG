module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyTwoFull
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySevenTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoAutInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem exists_primitive_prime_of_odd {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ n - 1 ∧ 7 ≤ r ∧ ¬ r ∣ 3 * n := by
  obtain ⟨r, hprim⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (by omega : 2 ≤ n)
    (by rintro rfl; norm_num at hodd)
  have hr : r.Prime := hprim.prime
  have hrd : r ∣ 2 ^ n - 1 := hprim.dvd
  have hnr : n < r := uc22p22i_lt_of_primitive hprim (by omega)
  have hr7 : 7 ≤ r := s13_seven_le_of_dvd hodd hr hrd
  refine ⟨r, hr, hrd, hr7, fun h => ?_⟩
  rcases hr.dvd_mul.mp h with h | h
  · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)

theorem exists_elemAbelian_le_normalizer_of_is3D4_odd (D : Data G) (hK : K_3D4CartanRank)
    (hAI : Inputs1719.K_3D4TwoAutInner) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal) (hZ : Subgroup.center (Bar2 L) = ⊥) {n r : ℕ}
    (h3D4 : Is3D4 (Bar2 L) n) (hodd : Odd n) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrd : r ∣ 2 ^ n - 1) :
    ∃ R : Subgroup G, R ≤ L ∧ R ≤ normalizer (D.T : Set G) ∧ IsElemAbelian r R ∧
      Nat.card R = r ^ 2 := by
  classical
  have hLM : L ≤ D.M := hL.1.le
  have hLN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN
  have hTL : D.T ≤ Subgroup.normalizer (L : Set G) := D.sylowM.le.trans hLN
  let S : Subgroup G := D.T ⊓ L
  let B : Subgroup G := L ⊓ Subgroup.normalizer (S : Set G)
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf S L := isSylowTwoOf_inf_of_mem_calC hL
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hS2 : IsPGroup 2 S := hT2.to_le inf_le_left
  have hTU : D.T ≤ Subgroup.normalizer (S : Set G) := by
    have h := (le_inf hTL (Subgroup.le_normalizer (H := D.T))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
    simpa only [S, inf_comm] using h
  have hin : ∀ m : ↥(Subgroup.normalizer (L : Set G)), (m : G) ∈ D.T →
      UC6S846.rhoL L m ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) := by
    intro m hm
    obtain ⟨k, hk⟩ := exists_rhoL_pow_two_pow_eq_one hT2 m hm
    obtain ⟨g, hg⟩ := hAI (Bar2 L) n h3D4 hodd (UC6S846.rhoL L m) ⟨k, hk⟩
    refine ⟨g, ?_⟩
    apply MulEquiv.ext
    intro x
    rw [MulAut.conj_apply]
    exact (hg x).symm
  have hpow : ∀ t ∈ D.T, ∃ j : ℕ, ∀ b ∈ B,
      t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ S :=
    powerMap_of_rhoL_mem_inner hTL hT2 hSyl hZ hin
  have hrankB : 2 ≤ CFSG.Open.pRank r B := by
    have h := two_le_pRank_borel_of_is3D4 D hK hL hN h3D4 hr hr2 hrd
    simpa only [B, S, inf_comm] using h
  obtain ⟨E, hEB, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hr.one_lt B
  have hEcard' : Nat.card E = r ^ CFSG.Open.pRank r E :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hr hEel
  have hErank : CFSG.Open.pRank r E = CFSG.Open.pRank r B := by
    apply Nat.pow_right_injective hr.two_le
    change r ^ CFSG.Open.pRank r E = r ^ CFSG.Open.pRank r B
    rw [← hEcard', ← hEcard]
  have hErank2 : 2 ≤ CFSG.Open.pRank r E := by
    rw [hErank]
    exact hrankB
  obtain ⟨z, hzE, hzord⟩ :=
    CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank (H := E) hr (by omega)
  have hXcard : Nat.card (Subgroup.zpowers z) = r := by
    rw [Nat.card_zpowers, hzord]
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨R, -, hRE, hRel, hRcard⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime
      (B := E) (X := Subgroup.zpowers z) hEel.isPGroup hErank2
      (Subgroup.zpowers_le.mpr hzE) hXcard
  have hRB : R ≤ B := hRE.trans hEB
  have hRL : R ≤ L := hRB.trans inf_le_left
  have hRN : R ≤ Subgroup.normalizer (S : Set G) := hRB.trans inf_le_right
  have hXr : ∀ x ∈ R, x ≠ 1 → orderOf x = r := by
    intro x hx hx1
    have hxdvd : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one (hRel.2 x hx)
    rcases (Nat.dvd_prime hr).mp hxdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hRT : R ≤ Subgroup.normalizer (D.T : Set G) :=
    le_normalizer_of_powerMap (X := R) (B := B) (T := D.T) (U := S)
      hRB hRN hTU inf_le_left hS2 hT2 hpow hodd hr hrd hXr
  exact ⟨R, hRL, hRT, hRel, hRcard⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
