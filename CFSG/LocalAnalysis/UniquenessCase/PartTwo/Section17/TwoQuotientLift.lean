module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentPermutesGeneric
public import CFSG.GroupTheory.TwoQuotientSY

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.GroupTheory
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section TwoQuotientNormal

variable {D : Data G} {L : Subgroup G}

local instance : (CFSG.GroupTheory.twoQuotientC (K1Nine D L) (S1Nine D L)).Normal :=
  CFSG.GroupTheory.twoQuotientC_normal
    (inf_le_right : S1Nine D L ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)))

theorem twoQuotientKYForm_of_calC {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    Inputs1719.KYForm
        (CFSG.GroupTheory.twoQuotientY (K1Nine D L) (S1Nine D L)
          (CFSG.GroupTheory.twoQuotientC_normal
            (inf_le_right : S1Nine D L ≤
              Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)))))
        (CFSG.GroupTheory.twoQuotientKY (K1Nine D L) (S1Nine D L)
          (CFSG.GroupTheory.twoQuotientC_normal
            (inf_le_right : S1Nine D L ≤
              Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)))))
        (CFSG.GroupTheory.twoQuotientSY (K1Nine D L) (S1Nine D L)
          (CFSG.GroupTheory.twoQuotientC_normal
            (inf_le_right : S1Nine D L ≤
              Subgroup.normalizer (K1Nine D L : Set (Mbar9 D))))) ∧
      Nonempty (↥(CFSG.GroupTheory.twoQuotientKY (K1Nine D L) (S1Nine D L)
          (CFSG.GroupTheory.twoQuotientC_normal
            (inf_le_right : S1Nine D L ≤
              Subgroup.normalizer (K1Nine D L : Set (Mbar9 D))))) ≃* Bar2 L) ∧
      ∀ n : ℕ,
        (∀ s ∈ S1Nine D L, s ^ n ∈ Subgroup.centralizer (K1Nine D L : Set (Mbar9 D))) →
        ∀ s ∈ CFSG.GroupTheory.twoQuotientSY (K1Nine D L) (S1Nine D L)
          (CFSG.GroupTheory.twoQuotientC_normal
            (inf_le_right : S1Nine D L ≤
              Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)))), s ^ n = 1 := by
  have hSK : S1Nine D L ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)) := inf_le_right
  have hZ := odd_card_center_K1Nine hL
  have hKq : CFSG.Open.IsQuasisimple ↥(K1Nine D L) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp (isComponent_K1 hL).1
  have hS : IsPGroup 2 (S1Nine D L) :=
    (isSylowOf_Tbar (D := D)).isPGroup.to_le inf_le_left
  have hSyl := isSylowOf_S1_inf_K1 hL
  refine ⟨?_, ?_, ?_⟩
  · exact kyForm_twoQuotient hKq hZ hS hSK hSyl
  · obtain ⟨e⟩ := CFSG.GroupTheory.twoQuotientK_nonempty_equiv_K hZ hS hSK
    obtain ⟨e2⟩ := nonempty_bar2_mulEquiv_K1 hL
    exact ⟨e.trans e2.symm⟩
  · intro n hn
    exact CFSG.GroupTheory.twoQuotientSY_pow_eq_one hn
      (hC := CFSG.GroupTheory.twoQuotientC_normal hSK)

theorem exists_twoQuotient_lift {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnorm : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D))) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (KY SY : Subgroup Y)
      (f : ↥(L ⊔ D.T) →* Y),
      Inputs1719.KYForm Y KY SY ∧ Nonempty (↥KY ≃* Bar2 L) ∧ Function.Surjective f ∧
        IsPGroup 2 f.ker ∧ f.ker ≤ D.T.subgroupOf (L ⊔ D.T) ∧
        (D.T.subgroupOf (L ⊔ D.T)).map f = SY ∧
        ∀ n : ℕ,
          (∀ s ∈ S1Nine D L, s ^ n ∈ Subgroup.centralizer (K1Nine D L : Set (Mbar9 D))) →
          ∀ s ∈ SY, s ^ n = 1 := by
  have hSK : S1Nine D L ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)) := inf_le_right
  let Y := CFSG.GroupTheory.twoQuotientY (K1Nine D L) (S1Nine D L)
    (CFSG.GroupTheory.twoQuotientC_normal hSK)
  let KY := CFSG.GroupTheory.twoQuotientKY (K1Nine D L) (S1Nine D L)
    (CFSG.GroupTheory.twoQuotientC_normal hSK)
  let SY := CFSG.GroupTheory.twoQuotientSY (K1Nine D L) (S1Nine D L)
    (CFSG.GroupTheory.twoQuotientC_normal hSK)
  obtain ⟨hky, hKYe, hexp⟩ := twoQuotientKYForm_of_calC hL
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hHM : L ⊔ D.T ≤ D.M := sup_le hLM hTM
  have hS1eq : S1Nine D L = Tbar9 D := by rw [S1Nine, inf_eq_left.mpr hnorm]
  let H : Subgroup G := L ⊔ D.T
  let π : ↥D.M →* Mbar9 D := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)
  let φ : ↥H →* Mbar9 D := π.comp (Subgroup.inclusion hHM)
  have hφrange : φ.range = (H.subgroupOf D.M).map π := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hφeq : φ.range = K1Nine D L ⊔ S1Nine D L := by
    rw [hφrange, hS1eq]
    have hHs : H.subgroupOf D.M = L.subgroupOf D.M ⊔ D.T.subgroupOf D.M :=
      Subgroup.subgroupOf_sup hLM hTM
    rw [hHs, Subgroup.map_sup]
    rfl
  let f : ↥H →* ↥(K1Nine D L ⊔ S1Nine D L) :=
    φ.codRestrict _ fun x => by rw [← hφeq]; exact ⟨x, rfl⟩
  let g : ↥(K1Nine D L ⊔ S1Nine D L) →* Y :=
    QuotientGroup.mk' (CFSG.GroupTheory.twoQuotientC (K1Nine D L) (S1Nine D L))
  let f' : ↥H →* Y := g.comp f
  have hfsurj : Function.Surjective f := by
    intro y
    have hy : (y : Mbar9 D) ∈ φ.range := by
      rw [hφeq]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hf'surj : Function.Surjective f' :=
    (QuotientGroup.mk'_surjective _).comp hfsurj
  have hker_le : f'.ker ≤ D.T.subgroupOf H := by
    intro x hx
    have hgx : g (f x) = 1 := by simpa [f'] using hx
    have hxC : f x ∈ CFSG.GroupTheory.twoQuotientC (K1Nine D L) (S1Nine D L) :=
      (QuotientGroup.eq_one_iff (f x)).mp hgx
    have hCS : ((f x : ↥(K1Nine D L ⊔ S1Nine D L)) : Mbar9 D) ∈ S1Nine D L :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hxC)).1
    have hCS' : φ x ∈ S1Nine D L := hCS
    have hxTbar : φ x ∈ Tbar9 D := hS1eq ▸ hCS'
    let xM : ↥D.M := ⟨(x : G), hHM x.2⟩
    obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.mp hxTbar
    have htx' : π (t⁻¹ * xM) = 1 := by
      rw [map_mul, map_inv, htx]
      show (φ x)⁻¹ * φ x = 1
      simp
    have hmemKer : ((t⁻¹ * xM : ↥D.M) : G) ∈ CFSG.Open.pCoreOf 2 D.M :=
      (mk_eq_one_iff_mem_pCoreOf (t⁻¹ * xM)).mp htx'
    have hTmem : ((t⁻¹ * xM : ↥D.M) : G) ∈ D.T :=
      s16c7_pCoreOf_le_of_isSylowOf D.sylowM hmemKer
    refine Subgroup.mem_subgroupOf.mpr ?_
    have h1 : (t : G) * (((t⁻¹ * xM : ↥D.M) : G)) ∈ D.T :=
      D.T.mul_mem (Subgroup.mem_subgroupOf.mp ht) hTmem
    rwa [show (t : G) * (((t⁻¹ * xM : ↥D.M) : G)) = (x : G) by
      simp [xM]] at h1
  have hST : IsPGroup 2 (D.T.subgroupOf H) :=
    D.sylowM.isPGroup.comap_subtype (K := H)
  have hker2 : IsPGroup 2 f'.ker := hST.to_le hker_le
  have hTmapφ : (D.T.subgroupOf H).map φ = Tbar9 D := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      have htT : ((t : ↥H) : G) ∈ D.T := Subgroup.mem_subgroupOf.mp ht
      exact Subgroup.mem_map.mpr ⟨⟨((t : ↥H) : G), hHM t.2⟩,
        Subgroup.mem_subgroupOf.mpr htT, rfl⟩
    · intro hy
      obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.mp hy
      have htH : (t : G) ∈ H := Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp ht)
      refine Subgroup.mem_map.mpr ⟨⟨(t : G), htH⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp ht)
      · show π t = (y : Mbar9 D)
        exact hty
  have hTmapf : (D.T.subgroupOf H).map f =
      (S1Nine D L).subgroupOf (K1Nine D L ⊔ S1Nine D L) := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hmem : φ t ∈ Tbar9 D := by
        rw [← hTmapφ]
        exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      rw [← hS1eq] at hmem
      exact Subgroup.mem_subgroupOf.mpr hmem
    · intro hy
      have hyT : (y : Mbar9 D) ∈ Tbar9 D :=
        hS1eq ▸ Subgroup.mem_subgroupOf.mp hy
      have hy' : (y : Mbar9 D) ∈ (D.T.subgroupOf H).map φ := by
        rwa [hTmapφ]
      obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.mp hy'
      exact Subgroup.mem_map.mpr ⟨t, ht, Subtype.ext hty⟩
  have hTmap : (D.T.subgroupOf H).map f' = SY := by
    have hcomp : f' = g.comp f := rfl
    rw [hcomp, ← Subgroup.map_map, hTmapf]
  exact ⟨Y, inferInstance, inferInstance, KY, SY, f', hky, hKYe, hf'surj, hker2, hker_le,
    hTmap, hexp⟩

end TwoQuotientNormal

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
