module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.Certificates.CosetTableShort

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section LocalHypC

structure LocalTwoA5 {Y : Type} [Group Y] (Λ : Set Y) (d : Y) : Prop where
  transitive : ∀ x ∈ commSet Λ d, ∀ y ∈ commSet Λ d,
    ∃ g ∈ Subgroup.closure (commSet Λ d), g * x * g⁻¹ = y
  mem : d ∈ Subgroup.closure (commSet Λ d)
  center : ∀ x ∈ Subgroup.closure (commSet Λ d),
    (∀ y ∈ Subgroup.closure (commSet Λ d), Commute x y) → x = 1 ∨ x = d
  bender : Nonempty (Subgroup.closure (commSet Λ d) ⧸
    Subgroup.center (Subgroup.closure (commSet Λ d)) ≃* CFSG.Theory.Comparator.PSL2Model 2)

theorem LocalTwoA5.of_injective {Y₀ Y : Type} [Group Y₀] [Group Y] {Λ₀ : Set Y₀} {Λ : Set Y}
    (φ : Y₀ →* Y) (hφ : Function.Injective φ) {d : Y₀}
    (himage : φ '' commSet Λ₀ d = commSet Λ (φ d)) (hL : LocalTwoA5 Λ (φ d)) :
    LocalTwoA5 Λ₀ d := by
  let L₀ : Subgroup Y₀ := Subgroup.closure (commSet Λ₀ d)
  let L : Subgroup Y := Subgroup.closure (commSet Λ (φ d))
  have hLmap : L₀.map φ = L := by
    change (Subgroup.closure (commSet Λ₀ d)).map φ = Subgroup.closure (commSet Λ (φ d))
    rw [MonoidHom.map_closure, himage]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    have hx' : φ x ∈ commSet Λ (φ d) := by rw [← himage]; exact ⟨x, hx, rfl⟩
    have hy' : φ y ∈ commSet Λ (φ d) := by rw [← himage]; exact ⟨y, hy, rfl⟩
    obtain ⟨g, hg, hgxy⟩ := hL.transitive (φ x) hx' (φ y) hy'
    have hgL : g ∈ L₀.map φ := by rw [hLmap]; exact hg
    obtain ⟨g₀, hg₀, hg₀eq⟩ := hgL
    refine ⟨g₀, hg₀, ?_⟩
    apply hφ
    rw [map_mul, map_mul, map_inv, hg₀eq, hgxy]
  · have hmem : φ d ∈ L₀.map φ := by rw [hLmap]; exact hL.mem
    obtain ⟨g₀, hg₀, hg₀eq⟩ := hmem
    have hg₀d : g₀ = d := hφ hg₀eq
    rw [hg₀d] at hg₀
    exact hg₀
  · intro x hx hxcent
    have hxL : φ x ∈ L := by rw [← hLmap]; exact ⟨x, hx, rfl⟩
    have hcentφ : ∀ y ∈ L, Commute (φ x) y := by
      intro y hy
      rw [← hLmap] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      exact (hxcent y₀ hy₀).map φ
    rcases hL.center (φ x) hxL hcentφ with h | h
    · left
      apply hφ
      rw [h, map_one]
    · right
      apply hφ
      exact h
  · let e : L₀ ≃* L :=
      (Subgroup.equivMapOfInjective L₀ φ hφ).trans (MulEquiv.subgroupCongr hLmap)
    have hcenter : (Subgroup.center L₀).map e.toMonoidHom = Subgroup.center L :=
      Subgroup.map_center_eq e
    have hiso : L₀ ⧸ Subgroup.center L₀ ≃* L ⧸ Subgroup.center L :=
      QuotientGroup.congr (Subgroup.center L₀) (Subgroup.center L) e hcenter
    exact ⟨hiso.trans hL.bender.some⟩

private theorem solvableRadical_eq_center_of_centerQuot_psl2 {L : Type} [Group L] [Finite L]
    (hZ : Nonempty (L ⧸ Subgroup.center L ≃* CFSG.Theory.Comparator.PSL2Model 2)) :
    CFSG.solvableRadical L = Subgroup.center L := by
  obtain ⟨e⟩ := hZ
  haveI hB : CFSG.BenderSuzuki.IsBenderGroup (L ⧸ Subgroup.center L) :=
    CFSG.BenderSuzuki.IsBenderGroup.isPSL2 2 (by norm_num) e
  haveI hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hB
  have hns : ¬ Group.IsSolvable (L ⧸ Subgroup.center L) := by
    intro hs
    obtain ⟨a, b, hab⟩ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hB
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hs a b)
  have hcenter_le : Subgroup.center L ≤ CFSG.solvableRadical L := by
    have hsolv : Group.IsSolvable (Subgroup.center L) :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
    exact le_sSup (show Subgroup.center L ∈ {N : Subgroup L | N.Normal ∧
      Group.IsSolvable N} from ⟨inferInstance, hsolv⟩)
  refine le_antisymm ?_ hcenter_le
  let R : Subgroup L := CFSG.solvableRadical L
  let π : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  have hRnorm : R.Normal := inferInstance
  haveI hRsolv : Group.IsSolvable R := CFSG.ABGLocalTools.solvableRadical_isSolvable
  have hmapnorm : (R.map π).Normal :=
    hRnorm.map π (QuotientGroup.mk'_surjective (Subgroup.center L))
  haveI : (R.map π).Normal := hmapnorm
  have hmapsolv : Group.IsSolvable (R.map π) :=
    Group.isSolvable_of_surjective (π.subgroupMap_surjective R)
  have hbot : R.map π = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (R.map π) with h | h
    · exact h
    · exfalso
      have htop : Group.IsSolvable (⊤ : Subgroup (L ⧸ Subgroup.center L)) := h ▸ hmapsolv
      haveI := htop
      exact hns (Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≃*
          (L ⧸ Subgroup.center L)).toMonoidHom)
        (Subgroup.topEquiv : (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≃*
          (L ⧸ Subgroup.center L)).surjective)
  have hle : R ≤ π.ker := by
    intro r hr
    have hmem : π r ∈ R.map π := ⟨r, hr, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  rwa [QuotientGroup.ker_mk'] at hle

theorem exists_hypC_of_localTwoA5 {Y : Type} [Group Y] [Finite Y] {Λ : Set Y} (hS : Setup Y Λ)
    (hconn : ¬ Disconnected Λ) {d : Y} (hd : d ∈ Λ) (hL : LocalTwoA5 Λ d) :
    ∃ hC₁ : HypothesisC Λ, hC₁.d = d ∧ hC₁.alpha = {d} ∧
      CFSG.solvableRadical (Halpha Λ hC₁.alpha) = Subgroup.center (Halpha Λ hC₁.alpha) ∧
      CFSG.BenderSuzuki.IsBenderGroup
        (Halpha Λ hC₁.alpha ⧸ Subgroup.center (Halpha Λ hC₁.alpha)) := by
  classical
  have hne : (commSet Λ d).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hd1 : d = 1 := by
      have hmem : d ∈ Subgroup.closure (commSet Λ d) := hL.mem
      rw [h, Subgroup.closure_empty, Subgroup.mem_bot] at hmem
      exact hmem
    exact hS.oddT.ne_one hd hd1
  obtain ⟨e, he⟩ := hne
  have hE : IsMaxOrbit Λ d (commSet Λ d) := by
    refine ⟨e, he, ?_, ?_⟩
    · apply Eq.symm
      exact Set.Subset.antisymm
        (OddLocal.orbitIn_subset_commSet hS.normal he)
        (fun x hx => by
          obtain ⟨g, hg, hgx⟩ := hL.transitive x hx e he
          exact ⟨g⁻¹, Subgroup.inv_mem _ hg, by rw [← hgx]; group⟩)
    · intro e' he'
      exact Set.ncard_le_ncard (OddLocal.orbitIn_subset_commSet hS.normal he')
        (Set.toFinite _)
  let hC₁ : HypothesisC Λ :=
    { setup := hS
      conn := hconn
      d := d
      hd := hd
      E := commSet Λ d
      hE := hE }
  have halpha : hC₁.alpha = {d} := by
    ext x
    constructor
    · intro hx
      by_contra hxd
      rcases hx with ⟨hxnorm, hxnot⟩
      obtain ⟨hxΛ, hxN⟩ := hxnorm
      let L : Subgroup Y := Subgroup.closure (commSet Λ d)
      have hxNL : x ∈ Subgroup.normalizer L :=
        Subgroup.normalizer_le_normalizer_closure (commSet Λ d) hxN
      have hxdL : x * d * x⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hxNL d).mp hL.mem
      have hcomm : ∀ y ∈ L, Commute (x * d * x⁻¹) y := by
        intro y hy
        have hy' : x⁻¹ * y * x ∈ L :=
          (Subgroup.mem_normalizer_iff''.mp hxNL y).mp hy
        have hcy : Commute (x⁻¹ * y * x) d :=
          OddLocal.commute_of_mem_closure_commSet hy'
        have h1 : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
        have h2 := (hcy.conj x).symm
        rwa [h1] at h2
      rcases hL.center (x * d * x⁻¹) hxdL hcomm with h1 | h1
      · have hd1 : d = 1 := by
          calc d = x⁻¹ * (x * d * x⁻¹) * x := by group
            _ = x⁻¹ * 1 * x := by rw [h1]
            _ = 1 := by group
        exact hS.oddT.ne_one hd hd1
      · have hxd' : Commute x d := by
          show x * d = d * x
          calc x * d = x * d * x⁻¹ * x := by group
            _ = d * x := by rw [h1]
        exact hxnot ⟨hxΛ, hxd', hxd⟩
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact OddLocal.self_mem_F hS.normal hd hE
  have hL_eq : Halpha Λ hC₁.alpha = Subgroup.closure (commSet Λ d) := by
    change Subgroup.closure (DalphaStar Λ hC₁.alpha) = Subgroup.closure (commSet Λ d)
    rw [hC₁.DalphaStar_alpha]
  refine ⟨hC₁, rfl, halpha, ?_, ?_⟩
  · rw [hL_eq]
    exact solvableRadical_eq_center_of_centerQuot_psl2 hL.bender
  · rw [hL_eq]
    exact CFSG.BenderSuzuki.IsBenderGroup.isPSL2 2 (by norm_num) hL.bender.some

end LocalHypC

end CFSG.OddTranspositions.PartThree
