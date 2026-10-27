module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09f
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_pCoreOf_of_isAlt_bar2 {L X : Subgroup G} (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) : pCoreOf 2 X ≤ pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_isAlt_bar2 hXL hcov hA5
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXL) ?_
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).exists_card_eq
  rw [hn]
  exact fun h => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)

theorem inf_pCoreOf_eq_of_isAlt_bar2 {L X : Subgroup G} (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) : X ⊓ pCoreOf 2 L = pCoreOf 2 X :=
  le_antisymm (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hXL)
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
      (pCoreOf_le_pCoreOf_of_isAlt_bar2 hXL hcov hA5))

theorem ker_bar2_eq {L X : Subgroup G} (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L)
    (hA5 : IsAlt (Bar2 L) 5) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hXL)).ker =
      CFSG.pCore 2 ↥X := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    ← CFSG.mem_openPCoreOf_iff, ← CFSG.mem_openPCoreOf_iff,
    ← inf_pCoreOf_eq_of_isAlt_bar2 hXL hcov hA5, Subgroup.coe_inclusion, Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem isAlt_bar2_of_isAlt_bar2 {L X : Subgroup G} (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) : IsAlt (Bar2 X) 5 := by
  have hker := ker_bar2_eq hXL hcov hA5
  obtain ⟨e⟩ := hA5
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (surjective_bar2 hXL hcov))).trans e⟩

theorem exists_card_eq_three_mul {L X : Subgroup G} (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) :
    ∃ m : ℕ, Nat.card X = 3 * m ∧ ¬ 3 ∣ m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).exists_card_eq
  refine ⟨20 * 2 ^ n, ?_, fun h => ?_⟩
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X), hn,
      card_bar2_of_isAlt (isAlt_bar2_of_isAlt_bar2 hXL hcov hA5)]
    ring
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · norm_num at h
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)

theorem isSylowOf_of_card_eq_three {L X D : Subgroup G} (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) (hDX : D ≤ X)
    (hD : Nat.card D = 3) : IsSylowOf 3 D X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm, hm3⟩ := exists_card_eq_three_mul hXL hcov hA5
  refine CFSG.ABGLocalTools.isSylowOf_iff.2
    ⟨hDX, IsPGroup.of_card (n := 1) (hD.trans (pow_one 3).symm), ?_⟩
  have h := Subgroup.relIndex_mul_card D X
  rw [inf_eq_left.2 hDX, hD, hm] at h
  have h' : D.relIndex X = m := by omega
  rwa [h']

theorem exists_card_eq_three {L X : Subgroup G} (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L)
    (hA5 : IsAlt (Bar2 L) 5) : ∃ D : Subgroup G, D ≤ X ∧ Nat.card D = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3
    (three_dvd_card_of_isAlt_bar2 hXL hcov hA5)
  exact ⟨Subgroup.zpowers (x : G), Subgroup.zpowers_le.2 x.2,
    by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]⟩

theorem opp_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {X D K : Subgroup G}
    (hD : IsSylowOf p D X) (hK : ∀ x ∈ X, D.map (MulAut.conj x).toMonoidHom ≤ K) :
    Opp p X ≤ K := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  rw [Subgroup.closure_le]
  rintro y ⟨hyX, k, hk⟩
  have hy : IsPGroup p (Subgroup.zpowers (⟨y, hyX⟩ : ↥X)) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hk])
  obtain ⟨Q, hQ⟩ := hy.exists_le_sylow
  obtain ⟨g, hgX, hg⟩ := hD.exists_mem_conj (P' := (Q : Subgroup ↥X).map X.subtype) ⟨Q, rfl⟩
  refine hK g hgX ⟨g⁻¹ * y * g, (hg y).1 ⟨⟨y, hyX⟩, hQ (Subgroup.mem_zpowers _), rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem le_of_forall_map_conj_le {L X D K : Subgroup G} (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) (hX : Opp 3 X = X) (hDX : D ≤ X)
    (hD : Nat.card D = 3) (hK : ∀ x ∈ X, D.map (MulAut.conj x).toMonoidHom ≤ K) : X ≤ K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact hX.symm.le.trans
    (opp_le_of_isSylowOf (isSylowOf_of_card_eq_three hXL hcov hA5 hDX hD) hK)

theorem le_pCoreOf_or_le_of_le_normalizer {L X C : Subgroup G} (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) (hX : Opp 3 X = X) (hCX : C ≤ X)
    (hXC : X ≤ normalizer (C : Set G)) : C ≤ pCoreOf 2 X ∨ X ≤ C := by
  by_cases h3 : 3 ∣ Nat.card C
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 3 h3
    have hDC : Subgroup.zpowers (c : G) ≤ C := Subgroup.zpowers_le.2 c.2
    refine Or.inr (le_of_forall_map_conj_le hXL hcov hA5 hX (hDC.trans hCX)
      (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hc]) fun x hx => ?_)
    exact (Subgroup.map_mono hDC).trans (Subgroup.mem_normalizer_iff_map_conj_eq.1 (hXC hx)).le
  · exact Or.inl ((le_inf hCX (le_pCoreOf_of_isAlt_bar2 hXL hcov hA5 (hCX.trans hXL) h3
      hXC)).trans (inf_pCoreOf_eq_of_isAlt_bar2 hXL hcov hA5).le)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
