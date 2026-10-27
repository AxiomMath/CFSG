module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofField
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec11.Item112
public import CFSG.RankThree.PartTwo.Sec11.Notation
import CFSG.RankThree.PartTwo.Sec4.Item413Setup

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)


namespace Res611Res7

variable {G : Type} [Group G] [Finite G]

theorem sec11K_mem_thetaComponentsIn_centralizer {L : Subgroup G} {c a : G}
    (hL : L ∈ thetaComponentsAt 3 c) (haN : a ∈ Subgroup.normalizer (L : Set G))
    (ha3 : a ^ 3 = 1)
    (hQ : IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    (hZ : Subgroup.center ((Sec4.thetaQuotMulAut L
      (Sec4.compAction L ⟨a, haN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥) :
    Sec11.sec11K L a ∈ thetaComponentsIn
      (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) := by
  set K := Sec11.sec11K L a with hK
  obtain ⟨hLc, hL'⟩ := mem_thetaComponentsIn_iff.mp hL
  set Z := Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) with hZdef
  have hKLa : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) := Subgroup.map_subtype_le _
  have hKZ : K ≤ Z := le_inf (hKLa.trans inf_le_right) ((hKLa.trans inf_le_left).trans hLc)
  set T := K.subgroupOf Z with hT
  set e : T ≃* K := Subgroup.subgroupOfEquivOfLe hKZ with he
  refine mem_thetaComponentsIn_iff.mpr ⟨hKZ, ?_, ?_, ?_⟩
  · have hKp : Group.IsPerfect K := Sec6.isPerfect_inSubgroup_perfectResidual _
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · set ι : Z →* Subgroup.centralizer ({c} : Set G) :=
      Z.subtype.codRestrict _ (fun z => z.2.2) with hι
    set MD := (L.subgroupOf (Subgroup.centralizer ({c} : Set G))).comap ι with hMD
    have hMDsn : MD.IsSubnormal := hL'.2.1.comap ι
    have hTMD : T ≤ MD := by
      intro t ht
      rw [hT, Subgroup.mem_subgroupOf] at ht
      rw [hMD, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact (hKLa ht).1
    have hTn : (T.subgroupOf MD).Normal := by
      constructor
      intro t ht m
      rw [Subgroup.mem_subgroupOf] at ht ⊢
      rw [hT, Subgroup.mem_subgroupOf] at ht ⊢
      have hmL : ((m : Z) : G) ∈ L := m.2
      have hmM : ((m : Z) : G) ∈ L ⊓ Subgroup.centralizer ({a} : Set G) := ⟨hmL, (m : Z).2.1⟩
      have := GroupTheory.conj_mem_inSubgroup_perfectResidual hmM ht
      simpa [hK, Sec11.sec11K] using this
    exact Subgroup.IsSubnormal.trans hTMD hTn.isSubnormal hMDsn
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three e)).symm (Sec11.isQuasisimple_sec11K_quotient haN ha3 hQ hZ)

end Res611Res7

open Res611Res7

section Certs


theorem Res611Res7.fieldCent_facts {G : Type} [Group G] [Finite G] {L : Subgroup G} {d : G}
    {m : ℕ} (hm : 2 < m) (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * m)))
    (hdF : KFacts.InducesStdKind L d .field) (hd3 : d ^ 3 = 1) :
    ∃ hdN : d ∈ Subgroup.normalizer (L : Set G),
      IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) ∧
      Subgroup.center ((Sec4.thetaQuotMulAut L
        (Sec4.compAction L ⟨d, hdN⟩)).toMonoidHom.eqLocus
          (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥ := by
  obtain ⟨hdN, hnot⟩ := KFacts.InducesStdKind.inducesOuterTheta L hdF (by decide)
  set α := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩) with hα
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [hα, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hcard : Nat.card (GaloisField 3 (3 * m)) = (3 ^ m) ^ 3 := by
    rw [GaloisField.card 3 (3 * m) (by omega), ← pow_mul, mul_comm]
  have hq : 4 ≤ 3 ^ m :=
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm.le
  obtain ⟨hZ, hQ, -, -⟩ := KFacts.fixedPoints_facts_of_mulEquiv_psl2
    (φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * m)))) hq hcard hα3 hnot
  exact ⟨hdN, hQ, hZ⟩

theorem item611FieldL2KExists_holds (h48 : Sec4.Item4_8) : Item611FieldL2KExists := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ he hcE d hd hdc hdF
  obtain ⟨-, -, m, hm, ⟨φ⟩, -⟩ := he
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1.1
  have hdA : d ∈ A := hE.2 hd.1
  have hd1 : d ≠ 1 := fun h => hdc (h ▸ Subgroup.one_mem _)
  obtain ⟨hdN, hQ, hZ⟩ := Res611Res7.fieldCent_facts hm φ hdF (hAe.2 d hdA)
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hL
  have hY := sec11K_mem_thetaComponentsIn_centralizer hLc hdN (hAe.2 d hdA) hQ hZ
  have hM : SectionFourHyp (Subgroup.centralizer ({d} : Set G)) :=
    hst.toTheoremFourHyp.sectionFourHyp (centralizer_ne_top_of_ne_one hst.toTheoremFourHyp hd1)
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨d, hdA⟩))
  obtain ⟨n, hn5, hAcard⟩ := Sec4.exists_card_eq_of_four_lt_pRank hAe hrank
  obtain ⟨K, hK, hYK⟩ := exists_le_mem_thetaComponentsIn h48 hM hAd hAe ⟨n, by omega, hAcard⟩
    hcA hc1 hY
  exact ⟨K, hK, hYK⟩

end Certs

end CFSG.RankThree.PartTwo.Sec6
