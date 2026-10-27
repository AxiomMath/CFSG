module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.StandardType.GGStructSOneCompHolds
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClQuot

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem ggSixRootCommKnown_marking
    (X : Type) [Group X] [Finite X] (p : ℕ) (G₀ A D J : Subgroup X)
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : IsElemAbelian p A) (hDA : D ≤ A)
    (hAN : A ≤ Subgroup.normalizer (G₀ : Set X))
    (hmk : LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ))
    (hJ : IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀)) :
    LargeEvenMarking ↥J (fun _ _ _ _ _ _ => True) := by
  have hDG : D ≤ Subgroup.normalizer (G₀ : Set X) := hDA.trans hAN
  let ι : ↥D →* MulAut ↥G₀ :=
    (Subgroup.normalizerMonoidHom (H := G₀)).comp (Subgroup.inclusion hDG)
  have hι : ∀ (d : ↥D) (g : ↥G₀), ((ι d) g : X) = (d : X) * (g : X) * (d : X)⁻¹ :=
    fun d g => Subgroup.normalizerMonoidHom_apply_apply_coe G₀ (Subgroup.inclusion hDG d) g
  let E : Subgroup (MulAut ↥G₀) := ι.range
  let Y : Subgroup ↥G₀ := CFSG.ComponentClassification.GSThmB.QPUCl.fixedBy E
  have hYeq : Y.map G₀.subtype = Subgroup.centralizer (D : Set X) ⊓ G₀ := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨?_, h.2⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      intro a ha
      have hfix : (ι ⟨a, ha⟩) h = h :=
        (CFSG.ComponentClassification.GSThmB.QPUCl.mem_fixedBy.1 hh) _
          (MonoidHom.mem_range.2 ⟨⟨a, ha⟩, rfl⟩)
      have h1 : (a : X) * (h : X) * (a : X)⁻¹ = (h : X) := by
        simpa [hι] using congrArg (Subtype.val) hfix
      calc (a : X) * (h : X) = ((a : X) * (h : X) * (a : X)⁻¹) * (a : X) := by group
        _ = (h : X) * (a : X) := by rw [h1]
    · rintro ⟨hgC, hgG⟩
      refine ⟨⟨g, hgG⟩, ?_, rfl⟩
      refine CFSG.ComponentClassification.GSThmB.QPUCl.mem_fixedBy.2 ?_
      rintro e he
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 he
      apply Subtype.ext
      rw [hι]
      have hcomm : (a : X) * g = g * (a : X) := Subgroup.mem_centralizer_iff.1 hgC a a.2
      rw [hcomm]
      group
  have hJG0 : J ≤ G₀ := hJ.1.trans inf_le_right
  let J₀ : Subgroup ↥G₀ := J.subgroupOf G₀
  have hJ₀ : IsComponentOf J₀ Y := by
    have h2 : IsComponentOf (J₀.map G₀.subtype) (Y.map G₀.subtype) := by
      rw [Subgroup.map_subgroupOf_eq_of_le hJG0, hYeq]
      exact hJ
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (f := G₀.subtype)
      G₀.subtype_injective).1 h2
  have hJ₀open : CFSG.Open.IsComponentOf J₀ Y :=
    CFSG.Assembly.isComponentOf_iff_open.1 hJ₀
  let π : ↥G₀ →* (↥G₀ ⧸ Subgroup.center ↥G₀) := QuotientGroup.mk' (Subgroup.center ↥G₀)
  let K : Subgroup (↥G₀ ⧸ Subgroup.center ↥G₀) := J₀.map π
  have hker : ∀ g : ↥G₀, π g = 1 → g ∈ Subgroup.center ↥G₀ :=
    fun g hg => (QuotientGroup.eq_one_iff g).1 hg
  have hK : CFSG.Open.IsComponentOf K (Y.map π) :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map π hker hJ₀open
  let Ē : Subgroup (MulAut (↥G₀ ⧸ Subgroup.center ↥G₀)) :=
    E.map (CFSG.ComponentClassification.GSThmB.QPUCl.quotAut ↥G₀)
  have hEel : IsElemAbelian p E := by
    refine CFSG.LocalAnalysis.GLTheoremA.I142N.isElemAbelian_range p ι ?_ ?_
    · intro a b
      apply Subtype.ext
      simpa using congrArg (fun z : ↥A => (z : X))
        (hA.1.is_comm.comm ⟨a.1, hDA a.2⟩ ⟨b.1, hDA b.2⟩)
    · intro a
      apply Subtype.ext
      simpa using hA.2 a.1 (hDA a.2)
  have hEbel : IsElemAbelian p Ē :=
    CFSG.Open.IsElemAbelian.map hEel (CFSG.ComponentClassification.GSThmB.QPUCl.quotAut ↥G₀)
  have hYle : Y.map π ≤ CFSG.ComponentClassification.GSThmB.QPUCl.fixedBy Ē :=
    CFSG.ComponentClassification.GSThmB.QPUCl.map_fixedBy_le E
  have hN : ((Y.map π).subgroupOf
      (CFSG.ComponentClassification.GSThmB.QPUCl.fixedBy Ē)).Normal :=
    CFSG.ComponentClassification.GSThmB.QPUCl.normal_map_fixedBy E
  have hsub : CFSG.Open.IsSubnormal (Y.map π)
      (CFSG.ComponentClassification.GSThmB.QPUCl.fixedBy Ē) :=
    CFSG.Open.IsSubnormal.step hYle hN (CFSG.Open.IsSubnormal.refl _)
  have hKfixed : CFSG.Open.IsComponentOf K
      (CFSG.ComponentClassification.GSThmB.QPUCl.fixedBy Ē) :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_trans hK hsub
  have hcent : CFSG.ComponentClassification.GSThmB.QPUCl.fixedBy Ē =
      CFSG.LocalAnalysis.GLTheoremA.I142.centFix Ē := by
    ext x
    rw [CFSG.ComponentClassification.GSThmB.QPUCl.mem_fixedBy,
      CFSG.LocalAnalysis.GLTheoremA.I142.mem_centFix]
  have hKcent : CFSG.Open.IsComponentOf K (CFSG.LocalAnalysis.GLTheoremA.I142.centFix Ē) := by
    rwa [← hcent]
  have hQsimple : IsSimpleGroup (↥G₀ ⧸ Subgroup.center ↥G₀) := by
    obtain ⟨-, lab, hlab, hraw⟩ := hmk
    obtain ⟨R, _, I, F, hprop⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨hs, hna, θ, hP⟩ := hprop
    haveI : IsSimpleGroup R := hs
    exact θ.isSimpleGroup
  have hQna : ∃ a b : ↥G₀ ⧸ Subgroup.center ↥G₀, a * b ≠ b * a := by
    obtain ⟨-, lab, hlab, hraw⟩ := hmk
    obtain ⟨R, _, I, F, hprop⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨hs, hna, θ, hP⟩ := hprop
    exact nonabelian_of_mulEquiv θ.symm hna
  have hQchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2
      (↥G₀ ⧸ Subgroup.center ↥G₀) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo
      (isChevTwo_of_largeEvenMarking hmk)
  have hKchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2
      (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.LocalAnalysis.GLTheoremA.I142T.compTypesElem_holds
      (↥G₀ ⧸ Subgroup.center ↥G₀) hQsimple hQna hQchev p hp hp2 Ē hEbel K hKcent
  let g : J₀ →* K :=
    (π.comp J₀.subtype).codRestrict K (fun x => Subgroup.mem_map_of_mem π x.2)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hgker : g.ker ≤ Subgroup.center J₀ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : π x.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have hc : x.1 ∈ Subgroup.center ↥G₀ := (QuotientGroup.eq_one_iff x.1).1 hx1
    exact Subgroup.mem_center_iff.1 hc y.1
  have hJ0q : CFSG.IsQuasisimple ↥J₀ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J₀).1 hJ₀.2.2
  obtain ⟨e₁⟩ := CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective
    hJ0q g hg hgker
  have hJ0chev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2
      (↥J₀ ⧸ Subgroup.center ↥J₀) :=
    (CFSG.LocalAnalysis.GLTheoremA.S9.isChevSimple_congr e₁).2 hKchev
  have hJchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2
      (↥J ⧸ Subgroup.center ↥J) :=
    (CFSG.LocalAnalysis.GLTheoremA.S9.isChevSimple_congr
      (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv
        (Subgroup.subgroupOfEquivOfLe hJG0))).1 hJ0chev
  exact CFSG.StandardType.ChevTwo.ys08_holds_legacy ↥J hJ.2.2 hJchev

end CFSG.StandardType
