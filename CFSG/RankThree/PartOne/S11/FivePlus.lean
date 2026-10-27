module

public import CFSG.RankThree.PartOne.S11.FivePlusLocal
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Assembly.CatalogTransport
import CFSG.RankThree.PartOne.S11.SecTenSeven
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.SectionTenFiveNormalPCoreWitness
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem inCatalog_quotient_center_of_thetaComponent {G : Type} [Group G] (hKP : CFSG.IsKProper G)
    {C : Subgroup G} (hC : C ≠ ⊤) {p : ℕ} {L : Subgroup C}
    (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore p L)) :
    InCatalog ((L ⧸ aschbacherSolvableCore p L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore p L)) := by
  set φ : L →* (L ⧸ aschbacherSolvableCore p L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore p L) :=
    (QuotientGroup.mk' (Subgroup.center (L ⧸ aschbacherSolvableCore p L))).comp
      (QuotientGroup.mk' (aschbacherSolvableCore p L)) with hφ
  have hsurj : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hsurj
  have hs : IsSimpleGroup (L ⧸ φ.ker) := e.isSimpleGroup_congr.mpr hq.2.1
  obtain ⟨i, ⟨ψ⟩⟩ := hKP C hC L φ.ker hs
  exact ⟨i, ⟨e.symm.trans ψ⟩⟩

theorem inSec10FivePlus_of_inspections
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hK : CatalogPrimeTwoAutomorphismsInner) : InSec10FivePlus := by
  intro G _ _ p A hS a haA ha1
  have hp := sectionTenSetup_prime hS
  have hp3 := sectionTenSetup_three_lt hS
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS).le
  obtain ⟨hsimple, hnonab, hKP, -, -, -, hAe, hAcard, -, -⟩ := id hS
  obtain ⟨b, hbA, hbna, Q, hQ2, hAQ, hQC, hQA, hQne, hker⟩ :=
    section_ten_five_normal_p_core_two_group_witness_frontier G p A hS a haA ha1
  have hb1 : b ≠ 1 := fun h => hbna (h ▸ Subgroup.one_mem _)
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hAC : A ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hAe.is_comm.comm (⟨x, hx⟩ : A) ⟨b, hbA⟩)
  set A' : Subgroup C := A.subgroupOf C with hA'
  set Q' : Subgroup C := Q.subgroupOf C with hQ'
  have hmapA : A'.map C.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAC
  have hmapQ : Q'.map C.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQC
  have hevenC : evenRank C ≤ 3 := (Sec9A.evenRank_subgroup_le C).trans he
  have hA'p : IsPGroup p A' := (IsElementaryAbelian.isPGroup p A).comap_subtype
  have hA'Q' : A' ≤ normalizer (Q' : Set C) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hQ', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hAQ (Subgroup.mem_subgroupOf.mp hx)) (h : G)
  have hQA' : ⁅Q', A'⁆ = Q' := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, hmapQ, hmapA]
    exact hQA
  have hθ : ⁅A', Q' ⊓ aschbacherSolvableCore p C⁆ = ⊥ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, hmapA, Subgroup.map_bot,
      Subgroup.map_inf_eq _ _ C.subtype C.subtype_injective, hmapQ]
    have hAθ : A ≤ normalizer ((inSubgroup (aschbacherSolvableCore p) C : Subgroup G) : Set G) :=
      le_normalizer_theta_of_le_normalizer hp (hAC.trans Subgroup.le_normalizer)
    have h := vanishing_centralizes_invariant_two_subgroups hp (sectionTenSetup_vanishing hS) hAe
      hAcard hbA hb1 (U := Q ⊓ inSubgroup (aschbacherSolvableCore p) C) inf_le_right
      (hQ2.to_le inf_le_left) (le_normalizer_inf_of_le_normalizer hAQ hAθ)
    rw [Subgroup.commutator_comm]
    exact h
  have haC : a ∈ C := hAC haA
  have ha' : (⟨a, haC⟩ : C) ∈ A' := Subgroup.mem_subgroupOf.mpr haA
  have hz : (Subgroup.zpowers (⟨a, haC⟩ : C)).map C.subtype = Subgroup.zpowers a := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hne : ⁅Q', Subgroup.zpowers (⟨a, haC⟩ : C)⁆ ≠ ⊥ := by
    intro h
    apply hQne
    have h2 := congrArg (Subgroup.map C.subtype) h
    rw [Subgroup.map_commutator, hmapQ, hz, Subgroup.map_bot] at h2
    exact h2
  have hCtop : C ≠ ⊤ := centralizer_singleton_ne_top_of_simple hnonab hb1
  have hcat : ∀ L ∈ thetaComponents p ↥C, Catalog ((L ⧸ aschbacherSolvableCore p L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore p L)) := by
    intro L hL
    have hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore p L) := hL.2.2
    have : IsSimpleGroup ((L ⧸ aschbacherSolvableCore p L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore p L)) := hq.2.1
    exact hbridge _ hq.2.2 (inCatalog_quotient_center_of_thetaComponent hKP hCtop hq)
  obtain ⟨L', hL', hA'L', hcomm, T', hT'L, hT'1, hT'2, hA'T', hT'A⟩ :=
    exists_zero_thetaComponent_of_inner selected_prime_elements_normalize_theta_components hK
      hevenC hp hp3 hcat hA'p (hQ2.comap_subtype) hA'Q' hQA' hθ hker ha' hne
  have hLmem : L'.map C.subtype ∈ thetaComponentFamily p A :=
    mem_thetaComponentFamily_iff.mpr ⟨b, hbA, hb1, ⟨L', hL', rfl⟩⟩
  have hnormalizes : ∀ {K : Subgroup C}, A' ≤ normalizer (K : Set C) →
      A ≤ normalizer ((K.map C.subtype : Subgroup G) : Set G) := by
    intro K hK' x hx
    have hxC : x ∈ C := hAC hx
    have h1 : (⟨x, hxC⟩ : C) ∈ normalizer (K : Set C) :=
      hK' (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.le_normalizer_map C.subtype ⟨⟨x, hxC⟩, h1, rfl⟩
  refine ⟨L'.map C.subtype, ⟨hLmem, T'.map C.subtype, Subgroup.map_mono hT'L, ?_,
    hT'2.map _, hnormalizes hA'T', ?_⟩, hnormalizes hA'L', ?_⟩
  · intro h
    exact hT'1 ((Subgroup.map_eq_bot_iff_of_injective T' C.subtype_injective).mp h)
  · rw [← hmapA, ← Subgroup.map_commutator, hT'A]
  · rw [← hz, ← Subgroup.map_commutator, hcomm]

end CFSG.RankThree.PartOne
