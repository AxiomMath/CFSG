module

public import CFSG.RankThree.PartOne.S11d.Sec109Common
public import CFSG.RankThree.PartOne.S11d.Facts
public import CFSG.RankThree.PartOne.S11d.FivePlusC
import CFSG.RankThree.PartOne.S11.FivePlus
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S10.NormalPCoreTwoCommutatorThetaComponent

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace Sec109

theorem componentExists_of
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hK : CatalogPrimeTwoAutomorphismsInner) (hBend : BenderPCore) : ComponentExists := by
  intro G _ _ p A c L B n h b S hW
  have hS := h.setup
  have hp : p.Prime := h.prime
  have hp3 : 3 < p := sectionTenSetup_three_lt hS
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS).le
  obtain ⟨hsimple, hnonab, hKP, -, -, -, hAe, hAcard, -, -⟩ := id hS
  have hbB : b ∈ B := hW.b_mem
  have hbA : b ∈ A := h.B_le_A hbB
  have hb1 : b ≠ 1 := hW.b_ne_one
  have hcA : c ∈ A := h.c_mem
  set C := centralizer ({b} : Set G) with hC
  have hAC : A ≤ C := fun x hx => mem_centralizer_singleton_iff.mpr (h.A_comm x hx b hbA)
  have hSC : S ≤ C := hW.S_le
  have hcC : c ∈ C := hAC hcA
  set A' : Subgroup C := A.subgroupOf C with hA'
  set Q' : Subgroup C := S.subgroupOf C with hQ'
  have hmapA : A'.map C.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAC
  have hmapQ : Q'.map C.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSC
  have hevenC : evenRank C ≤ 3 := (Sec9A.evenRank_subgroup_le C).trans he
  have hA'p : IsPGroup p A' := (IsElementaryAbelian.isPGroup p A).comap_subtype
  have hA'comm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := fun x hx y hy =>
    Subtype.ext (h.A_comm x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  have hA'Q' : A' ≤ normalizer (Q' : Set C) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [hQ', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hW.S_norm (Subgroup.mem_subgroupOf.mp hx)) (g : G)
  have hzc : (Subgroup.zpowers (⟨c, hcC⟩ : C)).map C.subtype = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hQc' : ⁅Q', Subgroup.zpowers (⟨c, hcC⟩ : C)⁆ = Q' := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, hmapQ, hzc]
    exact hW.S_comm.symm
  have hθ : ⁅A', Q' ⊓ aschbacherSolvableCore p C⁆ = ⊥ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, hmapA, Subgroup.map_bot,
      Subgroup.map_inf_eq _ _ C.subtype C.subtype_injective, hmapQ]
    have hAθ : A ≤ normalizer ((inSubgroup (aschbacherSolvableCore p) C : Subgroup G) : Set G) :=
      le_normalizer_theta_of_le_normalizer hp (hAC.trans Subgroup.le_normalizer)
    have hcomm := vanishing_centralizes_invariant_two_subgroups hp (sectionTenSetup_vanishing hS)
      hAe hAcard hbA hb1 (U := S ⊓ inSubgroup (aschbacherSolvableCore p) C) inf_le_right
      (hW.S_two.to_le inf_le_left) (le_normalizer_inf_of_le_normalizer hW.S_norm hAθ)
    rw [Subgroup.commutator_comm]
    exact hcomm
  have hCtop : C ≠ ⊤ := centralizer_singleton_ne_top_of_simple hnonab hb1
  have hcat : ∀ L ∈ thetaComponents p ↥C, Catalog ((L ⧸ aschbacherSolvableCore p L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore p L)) := by
    intro L hL
    have hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore p L) := hL.2.2
    have : IsSimpleGroup ((L ⧸ aschbacherSolvableCore p L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore p L)) := hq.2.1
    exact hbridge _ hq.2.2 (inCatalog_quotient_center_of_thetaComponent hKP hCtop hq)
  have hQO := hBend G p A c L B n h b S hW
  have hQ'2 : IsPGroup 2 Q' := hW.S_two.comap_subtype
  have hQ'1 : Q' ≠ ⊥ := by
    intro h0
    apply hW.S_ne_bot
    rw [← hmapQ, h0, Subgroup.map_bot]
  obtain ⟨L', hL', hA'L', hcomm, T, hTL, hT1, hT2, hA'T, hTc⟩ :=
    S11d.exists_zero_thetaComponent_of_inner_c selected_prime_elements_normalize_theta_components hK
      hevenC hp hp3 hcat hA'p hA'comm hQ'2 hQ'1 hA'Q' hθ hQO (a := ⟨c, hcC⟩)
      (Subgroup.mem_subgroupOf.mpr hcA) hQc'
  have hnormalizes : ∀ {K : Subgroup C}, A' ≤ normalizer (K : Set C) →
      A ≤ normalizer ((K.map C.subtype : Subgroup G) : Set G) := by
    intro K hK' x hx
    have hxC : x ∈ C := hAC hx
    have h1 : (⟨x, hxC⟩ : C) ∈ normalizer (K : Set C) :=
      hK' (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.le_normalizer_map C.subtype ⟨⟨x, hxC⟩, h1, rfl⟩
  have hSle : T.map C.subtype ≤ L'.map C.subtype := Subgroup.map_mono hTL
  have hS'ne : T.map C.subtype ≠ ⊥ := fun h0 =>
    hT1 ((Subgroup.map_eq_bot_iff_of_injective T C.subtype_injective).mp h0)
  have hS'comm : T.map C.subtype = ⁅T.map C.subtype, Subgroup.zpowers c⁆ := by
    rw [← hzc, ← Subgroup.map_commutator, hTc]
  have hS'norm : A ≤ normalizer ((T.map C.subtype : Subgroup G) : Set G) := hnormalizes hA'T
  have hS'A : T.map C.subtype = ⁅T.map C.subtype, A⁆ := by
    refine le_antisymm ?_ (commutator_le_left_of_normalizes hS'norm)
    calc T.map C.subtype = ⁅T.map C.subtype, Subgroup.zpowers c⁆ := hS'comm
      _ ≤ ⁅T.map C.subtype, A⁆ :=
        Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcA)
  have hLmem : L'.map C.subtype ∈ thetaComponentFamily p A :=
    mem_thetaComponentFamily_iff.mpr ⟨b, hbA, hb1, ⟨L', hL', rfl⟩⟩
  refine ⟨T.map C.subtype, L'.map C.subtype, ⟨hbB, hb1, Subgroup.map_subtype_le _, hS'ne,
    hT2.map _, hS'norm, hS'comm⟩, ⟨⟨hLmem, T.map C.subtype, hSle, hS'ne, hT2.map _, hS'norm,
    hS'A⟩, ⟨L', hL', rfl⟩⟩, hSle⟩

end Sec109

end CFSG.RankThree.PartOne
