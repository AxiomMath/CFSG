module

public import CFSG.RankThree.PartOne.S8.QuotientTransfer
public import CFSG.RankThree.PartOne.S8.Preparation
public import CFSG.RankThree.PartOne.S8.CatalogAssembly
public import CFSG.RankThree.PartOne.S9.StatementsSylow
import CFSG.RankThree.GroupTheory.SteinbergCDComponentActionInjection

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.S8
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Blueprint (Catalog)
open CFSG.SectionRank (IsKGroupCat)
open scoped Pointwise

theorem catalog_of_comm_simple (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hcomm : ∀ a b : S, a * b = b * a) : Catalog S :=
  CFSG.SectionRank.catalog_containsAbelianSimple S hcomm

theorem isKGroupCat_of_isKGroup (hbridge : TauCetiCatalogBridge) {X : Type} [Group X] [Finite X]
    (hK : CFSG.IsKGroup X) : IsKGroupCat X :=
  KCore.KGroupAllSimple.mono_of_nonab CFSG.SectionRank.catalog_containsAbelianSimple hbridge hK

theorem card_range_normalizerMonoidHom {G : Type*} [Group G] {L W : Subgroup G}
    (hW : W ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (L.normalizerMonoidHom.comp (Subgroup.inclusion hW)).range =
      (Subgroup.centralizer (L : Set G)).relIndex W := by
  have hker : (L.normalizerMonoidHom.comp (Subgroup.inclusion hW)).ker =
      (Subgroup.centralizer (L : Set G)).subgroupOf W := by
    ext w
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h x hx
      have := congrArg (fun φ : MulAut L => ((φ ⟨x, hx⟩ : L) : G)) h
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
        MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    · intro h
      ext x
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
        MulAut.one_apply]
      rw [mul_inv_eq_iff_eq_mul]
      exact (h x x.2).symm
  have h := Subgroup.index_ker (L.normalizerMonoidHom.comp (Subgroup.inclusion hW))
  rw [hker] at h
  exact h.symm

theorem twoPrimeResidual_localCoreProduct_le_of_quotient
    (hprep : OriginalThetaFreeQuotientComponentActionPreparation)
    (hcat : OriginalCatalogComponentLocalCoreOddAction)
    {X : Type} [Group X] [Finite X] (hKcat : IsKGroupCat X) (hX : evenRank X ≤ 3)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal]
    (hNs : Group.IsSolvable N) (hNp : ¬ p ∣ Nat.card N)
    (hθ : aschbacherSolvableCore p (X ⧸ N) = ⊥) {E : Subgroup X} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : X} (ht : t ∈ E) (ht1 : t ≠ 1) :
    CFSG.Quasithin.twoPrimeResidual
      (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set X)), E⁆ ⊔
        thetaT p E) ≤ N := by
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
  have hdisj := disjoint_of_isPGroup_of_not_dvd hp hEp N hNp
  have hĒ : IsElementaryAbelian p (E.map (QuotientGroup.mk' N)) := IsElementaryAbelian.map _
  have hĒc : Nat.card (E.map (QuotientGroup.mk' N)) = p ^ 2 :=
    (card_map_mk'_of_disjoint N E hdisj).trans hEcard
  have htĒ : (t : X ⧸ N) ∈ E.map (QuotientGroup.mk' N) := Subgroup.mem_map_of_mem _ ht
  have ht1' : (t : X ⧸ N) ≠ 1 := by
    intro h
    have htN : t ∈ N := (QuotientGroup.eq_one_iff t).mp h
    have : t ∈ E ⊓ N := ⟨ht, htN⟩
    rw [hdisj.eq_bot] at this
    exact ht1 (by simpa using this)
  obtain ⟨-, -, -, -, -, -, -, -, hDF, hcopr, -⟩ :=
    hprep X hKcat hX p hp hp3 N hNp hθ _ hĒ hĒc _ htĒ ht1'
  obtain ⟨-, hcatQ⟩ := hcat X hKcat hX p hp hp3 N hNp hθ _ hĒ hĒc _ htĒ ht1'
  have hnorm : ∀ L : Subgroup (X ⧸ N), IsComponent L →
      localCoreProduct p (E.map (QuotientGroup.mk' N)) (t : X ⧸ N) ≤
        Subgroup.normalizer (L : Set (X ⧸ N)) :=
    fun L hL => (hcatQ L hL).1.2.1
  have hDodd : Odd (Nat.card (localCoreProduct p (E.map (QuotientGroup.mk' N)) (t : X ⧸ N))) := by
    obtain ⟨-, -, -, hoddD, -⟩ :=
      coprime_fitting_centralizer_component_action_injection _ hDF hcopr hnorm
    refine hoddD ?_
    intro L hL
    rw [card_range_normalizerMonoidHom (hnorm L hL)]
    have h2 : ¬ 2 ∣ (Subgroup.centralizer (L : Set (X ⧸ N))).relIndex
        (localCoreProduct p (E.map (QuotientGroup.mk' N)) (t : X ⧸ N)) := (hcatQ L hL).1.2.2
    exact Nat.odd_iff.mpr (by omega)
  have hWD := map_localCoreProduct_le hp N hNs hNp hEp ht
  have hWodd : Odd (Nat.card ((⁅inSubgroup (aschbacherSolvableCore p)
      (Subgroup.centralizer ({t} : Set X)), E⁆ ⊔ thetaT p E).map (QuotientGroup.mk' N))) :=
    Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hWD)
  exact twoPrimeResidual_le_of_odd_card_map N hWodd

theorem sectionEightResidualBound_of_catalog (hbridge : TauCetiCatalogBridge)
    (hprep : OriginalThetaFreeQuotientComponentActionPreparation)
    (hcat : OriginalCatalogComponentLocalCoreOddAction) : SectionEightResidualBound := by
  intro X _ _ hK hX p hp hp3 E hE hEcard t ht ht1
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hNs, -, hNp, -⟩ := solvable_prime_complement_core_characterization hp (H := X)
  obtain ⟨-, -, hθQ, -⟩ := solvable_prime_complement_core_quotient_centralizers hp
    (aschbacherSolvableCore p X) hNs hNp
  exact ⟨(SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t ht ht1,
    twoPrimeResidual_localCoreProduct_le_of_quotient hprep hcat (isKGroupCat_of_isKGroup hbridge hK)
      hX hp hp3 _ hNs hNp hθQ hE hEcard ht ht1⟩

theorem sectionEightResidualBound_of_families (hbridge : TauCetiCatalogBridge)
    (hlin : OriginalLinearComponentLocalCoreOddAction)
    (hunit : OriginalUnitaryComponentLocalCoreOddAction)
    (hsymp : OriginalSymplecticOrthogonalComponentLocalCoreOddAction)
    (hspor : OriginalSporadicComponentLocalCoreOddAction)
    (hexc : OriginalExceptionalComponentLocalCoreOddAction)
    (hcop : OriginalCoprimeCatalogComponentLocalCoreCentralization)
    (halt : AlternatingComponentSelectedPrimeLocalCoreCentralization) :
    SectionEightResidualBound :=
  sectionEightResidualBound_of_catalog hbridge
    original_theta_free_quotient_component_action_preparation
    (original_catalog_component_local_core_odd_action_of_families hlin hunit hsymp hspor hexc hcop
      halt original_theta_free_quotient_component_action_preparation)

end CFSG.RankThree.PartOne
