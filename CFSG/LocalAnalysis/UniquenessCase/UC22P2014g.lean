module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20l
import CFSG.LocalAnalysis.UniquenessCase.UC22P2014f
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2014d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)


variable {G : Type} [Group G] [Finite G]

theorem uc22p2014g_le (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D) (h207 : S20_7 D)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hsp : IsStronglyPEmbedded p D.M) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) {Y : Subgroup G} (hY : IsPGroup p Y) (hYM : Y ≤ D.M)
    (hYL : Y ≤ normalizer (L : Set G)) : Y ≤ L := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro y hyY
  by_contra hyL
  obtain ⟨B₀, N₀, hBN⟩ := uc22p20l_splitBN_of_shape D h207 h1930 hL
  obtain ⟨S, hS⟩ := uc22p2014d_isParabolicTwo D hB h1930 hL
  obtain ⟨a, haM, haL, hfix⟩ := uc22p2014f_exists_map_eq D S hS (hYL hyY) (hYM hyY)
  set n : ↥(normalizer (L : Set G)) := ⟨a, Subgroup.le_normalizer haL⟩ * ⟨y, hYL hyY⟩ with hn
  have hnM : (n : G) ∈ D.M := D.M.mul_mem haM (hYM hyY)
  set π := QuotientGroup.mk' (L.subgroupOf (normalizer (L : Set G))) with hπ
  have hπL : ∀ z : ↥(normalizer (L : Set G)), π z = 1 ↔ (z : G) ∈ L := fun z => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπn : π n = π ⟨y, hYL hyY⟩ := by
    rw [hn, map_mul, (hπL ⟨a, Subgroup.le_normalizer haL⟩).2 haL, one_mul]
  obtain ⟨e, he⟩ := hY ⟨y, hyY⟩
  have hpe : π n ^ p ^ e = 1 := by
    rw [hπn, ← map_pow]
    have h1 : (⟨y, hYL hyY⟩ : ↥(normalizer (L : Set G))) ^ p ^ e = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val he)
    rw [h1, map_one]
  have ho : orderOf n ≠ 0 := (orderOf_pos n).ne'
  set k := ordCompl[p] (orderOf n) with hk
  have hcop : Nat.Coprime (p ^ e) k := (Nat.coprime_ordCompl hp ho).pow_left e
  have hβL : ((n ^ k : ↥(normalizer (L : Set G))) : G) ∉ L := by
    intro h
    have h1 : π n ^ k = 1 := by
      rw [← map_pow]
      exact (hπL _).2 h
    have h2 : orderOf (π n) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hpe) (orderOf_dvd_of_pow_eq_one h1)
    refine hyL ?_
    have hy : y = a⁻¹ * (n : G) := by
      rw [hn]
      simp
    rw [hy]
    exact L.mul_mem (L.inv_mem haL) ((hπL n).1 (orderOf_eq_one_iff.1 h2))
  have hβ1 : (n ^ k) ^ p ^ (orderOf n).factorization p = 1 := by
    rw [← pow_mul, mul_comm, hk, Nat.ordProj_mul_ordCompl_eq_self, pow_orderOf_eq_one]
  have hβp : IsPGroup p (zpowers ((n ^ k : ↥(normalizer (L : Set G))) : G)) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hβ1)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hi])
  have hβ1' : ((n ^ k : ↥(normalizer (L : Set G))) : G) ≠ 1 := fun h => hβL (h ▸ L.one_mem)
  have hβM : ((n ^ k : ↥(normalizer (L : Set G))) : G) ∈ D.M := by
    rw [Subgroup.coe_pow]
    exact D.M.pow_mem hnM k
  have hφS : (S : Subgroup (Bar2 L)).map (UC6S846.rhoL L (n ^ k)).toMonoidHom = S := by
    rw [map_pow, ← zpow_natCast]
    exact uc22p2014f_map_zpow hfix k
  have hφ : ∃ f : ℕ, UC6S846.rhoL L (n ^ k) ^ p ^ f = 1 :=
    ⟨(orderOf n).factorization p, by rw [← map_pow, hβ1, map_one]⟩
  obtain ⟨w, hw, hwS⟩ := uc22p2014f_exists_fixed hBN hp hp2 (uc22p2014d_barImage_ne_top D hL) S
    hS _ hφ hφS
  exact hw (uc22p2014d_mem_of_inv_mul_mem D hp hsp hL (n ^ k).2 hβM hβp hβ1' w (hS hwS))

end CFSG.LocalAnalysis.UniquenessCase.UC22
