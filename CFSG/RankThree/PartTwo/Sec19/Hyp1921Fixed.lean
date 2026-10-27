module

public import CFSG.RankThree.PartTwo.Sec3.Sims321Action
public import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.RankThree.PartTwo.Sec12.Item124Bar

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

theorem mem_map_inf_of_fixed {M L : Subgroup G} (hO2M : CFSG.Open.pCoreOf 2 L ≤ M)
    {X : Subgroup G} (hXN : X ≤ Subgroup.normalizer (L : Set G)) (hX3 : IsPGroup 3 X)
    (hXM : Subgroup.normalizer (X : Set G) ≤ M) {y : ↥L ⧸ CFSG.pCore 2 ↥L}
    (hy : ∀ (x : G) (hx : x ∈ X), Sec3.Sims321.barAut L ⟨x, hXN hx⟩ y = y) :
    y ∈ ((L ⊓ M).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  have hl : ∀ x ∈ X, (l : G)⁻¹ * (x * (l : G) * x⁻¹) ∈ CFSG.Open.pCoreOf 2 L := by
    intro x hx
    have h1 := hy x hx
    rw [Sec3.Sims321.barAut_mk, QuotientGroup.eq] at h1
    convert (CFSG.mem_openPCoreOf_iff _).mpr (Subgroup.inv_mem _ h1) using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 L) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hinv : ∀ d ∈ X, ∀ n ∈ CFSG.Open.pCoreOf 2 L, ∃ n' ∈ CFSG.Open.pCoreOf 2 L,
      d * ((l : G) * n) * d⁻¹ = (l : G) * n' := by
    intro d hd n hn
    have hdK : d ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hXN hd)
    exact ⟨(l : G)⁻¹ * (d * (l : G) * d⁻¹) * (d * n * d⁻¹),
      Subgroup.mul_mem _ (hl d hd) ((Subgroup.mem_normalizer_iff.mp hdK n).mp hn), by group⟩
  obtain ⟨n, hn, hfix⟩ := Sec12.exists_fixed_mem_coset hX3 hN3 (l : G) hinv
  have hgL : (l : G) * n ∈ L := L.mul_mem l.2 (CFSG.openPCoreOf_le 2 L hn)
  have hgC : (l : G) * n ∈ Subgroup.centralizer (X : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => mul_inv_eq_iff_eq_mul.mp (hfix x hx)
  have hgM : (l : G) * n ∈ M := hXM (Subgroup.centralizer_le_normalizer _ hgC)
  refine Subgroup.mem_map.mpr ⟨⟨(l : G) * n, hgL⟩,
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hgL, hgM⟩), ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
  refine (CFSG.mem_openPCoreOf_iff _).mp ?_
  convert Subgroup.inv_mem _ hn using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_mul_cancel_right]

end CFSG.RankThree.PartTwo.Late
