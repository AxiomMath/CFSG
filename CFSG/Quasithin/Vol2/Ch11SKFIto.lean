module

public import CFSG.GroupTheory.FrobeniusNormalComplement
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.KF

open Subgroup CFSG.GroupTheory

variable {p : ℕ} [hp : Fact p.Prime]

theorem isPGroup_automizer_of_central {G : Type*} [Group G] [Finite G] (hp2 : p ≠ 2)
    (hcen : ∀ x : G, x ^ p = 1 → x ∈ center G) {Q : Subgroup G} (hQ : IsPGroup p Q) :
    IsPGroup p (normalizer (Q : Set G) ⧸
      (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))) := by
  have hrange : IsPGroup p Q.normalizerMonoidHom.range := by
    by_cases hnt : Nontrivial Q
    · obtain ⟨D, -, -, -, hDp, hfix⟩ :=
        CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 hQ
      refine hfix.to_le ?_
      rintro _ ⟨n, rfl⟩
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      have hd1 : (d : G) ^ p = 1 := by
        rw [← Subgroup.coe_pow, hDp d hd, Subgroup.coe_one]
      have hc := mem_center_iff.mp (hcen (d : G) hd1) (n : G)
      change ((Q.normalizerMonoidHom n) d : G) = d
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hc, mul_inv_cancel_right]
    · have : Subsingleton Q := not_nontrivial_iff_subsingleton.mp hnt
      have : Subsingleton (MulAut Q) := ⟨fun σ τ => MulEquiv.ext fun _ => Subsingleton.elim _ _⟩
      exact fun g => ⟨0, Subsingleton.elim _ _⟩
  exact hrange.of_equiv ((QuotientGroup.quotientMulEquivOfEq (normalizerMonoidHom_ker Q).symm).trans
    (QuotientGroup.quotientKerEquivRange Q.normalizerMonoidHom)).symm

theorem ito_normalPComplement {G : Type*} [Group G] [Finite G] (hp2 : p ≠ 2)
    (hcen : ∀ x : G, x ^ p = 1 → x ∈ center G) : ∃ N : Subgroup G, IsNormalPComplement p N :=
  (frobenius_normal_p_complement p).1.2 fun _ hQ => isPGroup_automizer_of_central hp2 hcen hQ

theorem exists_pow_eq_one_not_mem_center {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (hp2 : p ≠ 2) (hpL : p ∣ Nat.card L) : ∃ x : L, x ^ p = 1 ∧ x ∉ center L := by
  by_contra hcon
  push Not at hcon
  obtain ⟨N, hN, hcop, k, hk⟩ := ito_normalPComplement hp2 hcon
  have hNtop : N = ⊤ := by
    by_contra hne
    have : Nontrivial (L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    have hpg : IsPGroup p (L ⧸ N) := IsPGroup.of_card (n := k) hk
    have : Group.IsPerfect (L ⧸ N) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    exact Group.IsPerfect.not_isNilpotent (G := L ⧸ N) hpg.isNilpotent
  rw [hNtop, Subgroup.card_top] at hcop
  exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm hpL)

end CFSG.Quasithin.Vol2.Ch11.SecS.KF
