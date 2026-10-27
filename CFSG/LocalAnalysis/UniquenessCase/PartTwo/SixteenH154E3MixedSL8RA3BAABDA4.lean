module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_normalizer_index_two
    (D : Data G) (S : s16h_Std D) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    Mbar D.M ⊥ V h.hyp151.isElemAbelian ≤
        Subgroup.normalizer (((Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
          Subgroup.normalizer (lBar ⊥ V h.hyp151.isElemAbelian L)) :
            Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) : Set _) ∧
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
          Subgroup.normalizer (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤
        Subgroup.normalizer ((barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) :
          Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) : Set _) := by
  classical
  have hV : IsElemAbelian 2 V := h.hyp151.isElemAbelian
  let Mb : Subgroup (MulAut (Vtil ⊥ V hV)) := Mbar D.M ⊥ V hV
  let Lb : Subgroup (MulAut (Vtil ⊥ V hV)) := lBar ⊥ V hV L
  let B : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV (conjSubgroup L x)
  let N : Subgroup (MulAut (Vtil ⊥ V hV)) := Mb ⊓ Subgroup.normalizer (Lb : Set _)
  change Mb ≤ Subgroup.normalizer (N : Set _) ∧ N ≤ Subgroup.normalizer (B : Set _)
  have hBne : B ≠ Lb := by
    intro hBL
    have hc : barSub ⊥ V hV (conjSubgroup L x) = barSub ⊥ V hV L := by
      change B = Lb
      exact hBL
    exact hxn ((s15_Infra_mem_nBar_iff h.hyp151.hyp125 hV hxM).2 hc)
  refine ⟨?_, ?_⟩
  · letI : MulAction ↥Mb (Subgroup (MulAut (Vtil ⊥ V hV))) :=
      MulAction.compHom (Subgroup (MulAut (Vtil ⊥ V hV)))
        ((MulAut.conj : MulAut (Vtil ⊥ V hV) →* MulAut (MulAut (Vtil ⊥ V hV))).comp
          Mb.subtype)
    have hsmulM : ∀ m : ↥Mb, m • Lb =
        Lb.map (MulAut.conj (m : MulAut (Vtil ⊥ V hV))).toMonoidHom := by
      intro m
      show (MulAut.conj (m : MulAut (Vtil ⊥ V hV))) • Lb =
        Lb.map (MulAut.conj (m : MulAut (Vtil ⊥ V hV))).toMonoidHom
      rw [Subgroup.pointwise_smul_def]
      rfl
    have hstabM : MulAction.stabilizer ↥Mb Lb = N.subgroupOf Mb := by
      ext m
      rw [MulAction.mem_stabilizer_iff, hsmulM, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        Subgroup.mem_normalizer_iff_map_conj_eq]
      simp
    have horbM : MulAction.orbit ↥Mb Lb =
        {X : Subgroup (MulAut (Vtil ⊥ V hV)) |
          ∃ φ ∈ Mb, X = Lb.map (MulAut.conj φ).toMonoidHom} := by
      ext X
      constructor
      · intro hX
        rw [MulAction.mem_orbit_iff] at hX
        obtain ⟨m, hm⟩ := hX
        exact ⟨(m : MulAut (Vtil ⊥ V hV)), m.2, hm.symm.trans (hsmulM m)⟩
      · rintro ⟨φ, hφ, rfl⟩
        exact ⟨⟨φ, hφ⟩, hsmulM ⟨φ, hφ⟩⟩
    have hidx : (MulAction.stabilizer ↥Mb Lb).index = 2 := by
      have h := MulAction.index_stabilizer (G := ↥Mb) (x := Lb)
      rw [horbM] at h
      rw [h]
      exact hs2
    have hNnorm : (N.subgroupOf Mb).Normal := by
      rw [← hstabM]
      exact Subgroup.normal_of_index_eq_two hidx
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : N ≤ Mb)).1 hNnorm
  · intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hnMb : n ∈ Mb := (Subgroup.mem_inf.1 hn).1
    have hnL : Lb.map (MulAut.conj n).toMonoidHom = Lb :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).1 (Subgroup.mem_inf.1 hn).2
    obtain ⟨g, hgM, hgn⟩ := (mem_barSub ⊥ V hV D.M n).1 hnMb
    have hgstab : (g : G) ∈ stabTil ⊥ V := g.2
    have hgt : actTil ⊥ V hV ⟨(g : G)⁻¹, (stabTil ⊥ V).inv_mem hgstab⟩ =
        (actTil ⊥ V hV g)⁻¹ := by
      rw [show (⟨(g : G)⁻¹, (stabTil ⊥ V).inv_mem hgstab⟩ : stabTil ⊥ V) = g⁻¹ from
        Subtype.ext rfl, map_inv]
    have hBmap : B.map (MulAut.conj n).toMonoidHom =
        barSub ⊥ V hV (conjSubgroup L (x * (g : G)⁻¹)) := by
      change (barSub ⊥ V hV (conjSubgroup L x)).map (MulAut.conj n).toMonoidHom =
        barSub ⊥ V hV (conjSubgroup L (x * (g : G)⁻¹))
      have h1 := s15_Infra_barSub_conjSubgroup ⊥ V hV
        ((stabTil ⊥ V).inv_mem hgstab) (conjSubgroup L x)
      rw [hgt, inv_inv, conjSubgroup_conjSubgroup] at h1
      rw [h1, ← hgn]
    rcases c23_barSub_conj_cases D h.hyp151 hV hs2 hxM hxn
      (m := x * (g : G)⁻¹) (D.M.mul_mem hxM (D.M.inv_mem hgM)) with hcase | hcase
    · exfalso
      exact hBne (Subgroup.map_injective (MulAut.conj n).injective
        ((hBmap.trans hcase).trans hnL.symm))
    · exact hBmap.trans hcase

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
