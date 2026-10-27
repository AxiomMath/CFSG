module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65Z0
public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Sporadic.Suz.Simple
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem le_of_isExtraspecialExpP_of_gamma
    {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G}
    {Q O : Subgroup G}
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M)
    (hQO : Q ≤ Subgroup.normalizer (O : Set G))
    (hO3' : Nat.Coprime 3 (Nat.card O))
    (hQext : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q) :
    O ≤ D.M := by
  classical
  obtain ⟨E, hEQ, hEel, hEcard⟩ :=
    exists_elemAbelian_nine_le_of_isExtraspecialExpP (G := G) (Q := Q) hQext
  have hEN : E ≤ Subgroup.normalizer (O : Set G) := hEQ.trans hQO
  haveI hNorm : Subgroup.Normalizes E O := ⟨hEN⟩
  haveI : Finite ↥E := Subtype.finite
  haveI : IsMulCommutative ↥E := hEel.1
  letI : CommGroup ↥E := IsMulCommutative.instCommGroup
  haveI : Fact (IsPGroup 3 ↥E) := ⟨hEel.isPGroup⟩
  have hncyc : ¬ IsCyclic ↥E := by
    intro hcyc
    have hexp : Monoid.exponent ↥E ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hEel.2 (x : ↥E) x.2)
    rw [hcyc.exponent_eq_card, hEcard] at hexp
    norm_num at hexp
  have htop : (⨆ (a : ↥E) (_ : a ≠ 1),
      fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥O) = ⊤ :=
    iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
      (G := ↥O) (A := ↥E) (p := 3) hO3' hncyc
  have hle : ∀ (a : ↥E), a ≠ 1 →
      (fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥O).map O.subtype ≤ D.M := by
    intro a ha
    have h3a : (a : G) ^ 3 = 1 := by
      have h := hEel.2 (a : ↥E) a.2
      simpa using h
    have hne : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hord : orderOf (a : G) = 3 := orderOf_eq_prime h3a hne
    have hcard : Nat.card (Subgroup.zpowers (a : G)) = 3 := by
      rw [Nat.card_zpowers, hord]
    have hrank : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers (a : G)) :=
      CFSG.SectionRank.le_pRank (p := 3) (k := 1) (by norm_num) le_rfl
        (CFSG.Open.isElemAbelian_zpowers (p := 3) h3a) (by simpa using hcard)
    have hPaQ : Subgroup.zpowers (a : G) ≤ Q := Subgroup.zpowers_le.mpr (hEQ a.2)
    have hN : Subgroup.normalizer (↑(Subgroup.zpowers (a : G)) : Set G) ≤ D.M :=
      (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore (p := 3) (k := 1)
        (Q := Subgroup.zpowers (a : G)) (P := Q) hPaQ hrank).trans hΓ
    refine (Subgroup.map_le_iff_le_comap).mpr ?_
    intro o ho
    have hfix : (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) • o = o :=
      ho ⟨a, Subgroup.mem_zpowers a⟩
    have hconj : (a : G) * (o : G) * (a : G)⁻¹ = (o : G) := by
      have hcoe := congrArg (fun t : ↥O => (t : G)) hfix
      simpa [Subgroup.smul_def] using hcoe
    have hcent : (o : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
    have hcent' : (o : G) ∈ Subgroup.centralizer (↑(Subgroup.zpowers (a : G)) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hcent
    exact hN (Subgroup.centralizer_le_normalizer _ hcent')
  have hmap : (⨆ (a : ↥E) (_ : a ≠ 1),
      fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥O).map O.subtype ≤ D.M := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun ha => hle a ha
  rw [htop] at hmap
  have htopmap : (⊤ : Subgroup ↥O).map O.subtype = O := by
    simpa [MonoidHom.range_eq_map] using Subgroup.range_subtype (H := O)
  rwa [htopmap] at hmap

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
