module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModel
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveChart
public import CFSG.OddTranspositions.PartThree.Twelve.FiveDefs
public import CFSG.OddTranspositions.PartThree.Twelve.SixPivot
public import CFSG.OddTranspositions.PartThree.Twelve.Four
public import CFSG.OddTranspositions.PartThree.Nine.Setup
public import CFSG.OddTranspositions.PartFour.LinePolar
public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockFive
public import CFSG.Mathlib.GroupTheory.ClosureSubgroupOf
import CFSG.OddTranspositions.PartThree.CommSetConj

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.PartFour Matrix

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem isFiveReflectionModel_of_markingData (hC : HypothesisC D) {k : ℕ} {ε π : Bool}
    {φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      fiveProjective k ε π}
    (h : ∀ x, x ∈ imageClass hC ↔ ∃ r : fiveReflectionGroup k ε π,
      (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π ∧
        (QuotientGroup.mk r : fiveProjective k ε π) = φ x) :
    IsFiveReflectionModel k ε π (imageClass hC) := by
  refine ⟨φ, fun g => (h g).trans ?_⟩
  constructor
  · rintro ⟨r, hr, hφr⟩
    exact ⟨r, hr, hφr.symm⟩
  · rintro ⟨r, hr, hφr⟩
    exact ⟨r, hr, hφr.symm⟩

theorem alpha_eq_singleton_of_markingData (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    {φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      fiveProjective k ε π}
    (h : ∀ x, x ∈ imageClass hC ↔ ∃ r : fiveReflectionGroup k ε π,
      (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π ∧
        (QuotientGroup.mk r : fiveProjective k ε π) = φ x) :
    hC.alpha = {hC.d} := by
  have h5 := isFiveReflectionModel_of_markingData hC h
  have hcls := imageClass_isClass hC
  obtain ⟨s, hs⟩ := imageClass_nonempty hC
  obtain ⟨hb1, hne⟩ := subset_rootBlock_and_ne_of_isFiveReflectionModel hcls hk h5 hs
  exact alpha_eq_singleton_of_rootBlock_eq_singleton hC hMZ hs hb1 hne
    (rootBlock_eq_singleton_of_isFiveReflectionModel hcls hk h5 hs)

theorem perpMem_inter_perpMem_eq_commSet_inter {x y : G} (h : ¬ Commute x y) :
    perpMem D x ∩ perpMem D y = commSet D x ∩ commSet D y := by
  ext z
  constructor
  · rintro ⟨hzx, hzy⟩
    refine ⟨⟨hzx.1, hzx.2, ?_⟩, ⟨hzy.1, hzy.2, ?_⟩⟩
    · rintro rfl
      exact h hzy.2
    · rintro rfl
      exact h hzx.2.symm
  · rintro ⟨hzx, hzy⟩
    exact ⟨⟨hzx.1, hzx.2.1⟩, ⟨hzy.1, hzy.2.1⟩⟩

theorem self_mem_lineMem_left {d w : G} (hd : d ∈ D) : d ∈ lineMem D d w :=
  mem_lineMem.mpr ⟨hd, fun _ hz => hz.1⟩

theorem self_mem_lineMem_right {d w : G} (hw : w ∈ D) : w ∈ lineMem D d w :=
  mem_lineMem.mpr ⟨hw, fun _ hz => hz.2⟩

theorem fiveLines_apply (hfl : FiveLines D) {v d w : G}
    (hvD : v ∈ D) (hdD : d ∈ D) (hwD : w ∈ D)
    (hvd : v ∈ commSet D d) (hvw : v ∈ commSet D w) (hwd : ¬ Commute d w) :
    (orderOf (d * w) = 3 ∨ orderOf (d * w) = 5) ∧
      (lineMem D d w).ncard = orderOf (d * w) ∧
        ∀ x ∈ lineMem D d w, x ≠ d → ¬ Commute x d ∧ lineMem D d x = lineMem D d w := by
  have hdv : d ∈ commSet D v := ⟨hdD, hvd.2.1.symm, fun h => hvd.2.2 h.symm⟩
  have hwv : w ∈ commSet D v := ⟨hwD, hvw.2.1.symm, fun h => hvw.2.2 h.symm⟩
  exact hfl v hvD d hdv w hwv hwd

theorem perpMem_inter_eq_of_lineMem {d w x : G} (hwD : w ∈ D) (hwd : ¬ Commute d w)
    (hxE : x ∈ lineMem D d w) (hxnc : ¬ Commute x d)
    (hxline : lineMem D d x = lineMem D d w) :
    perpMem D d ∩ perpMem D x = perpMem D d ∩ perpMem D w := by
  have hxwSub : perpMem D d ∩ perpMem D w ⊆ perpMem D x := hxE.2
  have hxwMem : perpMem D d ∩ perpMem D x ⊆ perpMem D w := by
    have hwmem : w ∈ lineMem D d x := by rw [hxline]; exact self_mem_lineMem_right hwD
    exact hwmem.2
  exact Set.Subset.antisymm (fun z hz => ⟨hz.1, hxwMem hz⟩) (fun z hz => ⟨hz.1, hxwSub hz⟩)

theorem commSet_inter_eq_of_lineMem {d w x : G} (hwD : w ∈ D) (hwd : ¬ Commute d w)
    (hxE : x ∈ lineMem D d w) (hxnc : ¬ Commute x d)
    (hxline : lineMem D d x = lineMem D d w) :
    commSet D d ∩ commSet D x = commSet D d ∩ commSet D w := by
  have hperp := perpMem_inter_eq_of_lineMem hwD hwd hxE hxnc hxline
  rw [← perpMem_inter_perpMem_eq_commSet_inter (fun h => hxnc h.symm),
    ← perpMem_inter_perpMem_eq_commSet_inter hwd, hperp]

theorem mem_normalizer_hypLineGroup_of_mem_Halpha_of_commute (hC : HypothesisC D) {g w : G}
    (hgH : g ∈ Halpha D hC.alpha) (hgw : Commute g w) :
    g ∈ Subgroup.normalizer (hypLineGroup D hC.d w : Set G) := by
  have hN : IsNormalSet D := hC.setup.normal
  have hgd : Commute g hC.d := Subgroup.mem_centralizer_singleton_iff.mp
    (Halpha_le_centralizer_of_mem_alpha hC hC.d_mem_alpha hgH)
  have hconj : ∀ a : G, Commute a hC.d → Commute a w →
      ∀ y ∈ hypLineGroup D hC.d w, a * y * a⁻¹ ∈ hypLineGroup D hC.d w := by
    intro a had haw y hy
    have hsub : (MulAut.conj a) '' (commSet D hC.d ∩ commSet D w) ⊆
        commSet D hC.d ∩ commSet D w := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨conj_mem_commSet_of_commute hN had hz.1,
        conj_mem_commSet_of_commute hN haw hz.2⟩
    have hmap : (hypLineGroup D hC.d w).map (MulAut.conj a).toMonoidHom ≤
        hypLineGroup D hC.d w := by
      rw [MonoidHom.map_closure]
      exact Subgroup.closure_mono hsub
    exact hmap ⟨y, hy, rfl⟩
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨hconj g hgd hgw y, fun hy => ?_⟩
  have h1 := hconj g⁻¹ hgd.inv_left hgw.inv_left _ hy
  rwa [inv_inv, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1

theorem mem_inf_normalizer_of_mem_hypLineGroup_conj (hC : HypothesisC D)
    (hα : hC.alpha = {hC.d}) {v w x g : G} (hwD : w ∈ D) (hwd : ¬ Commute hC.d w)
    (hxE : x ∈ lineMem D hC.d w) (hxnc : ¬ Commute x hC.d)
    (hxline : lineMem D hC.d x = lineMem D hC.d w)
    (hgLv : g ∈ hypLineGroup D hC.d v) (hgwx : g * w * g⁻¹ = x) :
    g ∈ Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G) := by
  have hN : IsNormalSet D := hC.setup.normal
  have hgH : g ∈ Halpha D hC.alpha :=
    (Subgroup.closure_le _).mpr (fun y hy => mem_Halpha_of_mem_commSet hC hα hy.1) hgLv
  have hgd : Commute g hC.d := Subgroup.mem_centralizer_singleton_iff.mp
    ((Subgroup.closure_le _).mpr
      (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr hy.1.2.1) hgLv)
  have hS : commSet D hC.d ∩ commSet D x = commSet D hC.d ∩ commSet D w :=
    commSet_inter_eq_of_lineMem hwD hwd hxE hxnc hxline
  have hconj_g : (MulAut.conj g) '' (commSet D hC.d ∩ commSet D w) ⊆
      commSet D hC.d ∩ commSet D w := by
    rintro _ ⟨z, hz, rfl⟩
    have h1 : g * z * g⁻¹ ∈ commSet D x := by
      have h := conj_mem_commSet hN g hz.2
      rwa [hgwx] at h
    have h2 : g * z * g⁻¹ ∈ commSet D hC.d ∩ commSet D x :=
      ⟨conj_mem_commSet_of_commute hN hgd hz.1, h1⟩
    rw [hS] at h2
    exact h2
  have hconj_ginv : (MulAut.conj g⁻¹) '' (commSet D hC.d ∩ commSet D w) ⊆
      commSet D hC.d ∩ commSet D w := by
    rintro _ ⟨z, hz, rfl⟩
    have hzx : z ∈ commSet D x := by
      have hz' : z ∈ commSet D hC.d ∩ commSet D x := by
        rw [hS]; exact hz
      exact hz'.2
    refine ⟨conj_mem_commSet_of_commute hN hgd.inv_left hz.1, ?_⟩
    have h := conj_mem_commSet hN g⁻¹ hzx
    have hxw : (g⁻¹) * x * (g⁻¹)⁻¹ = w := by rw [inv_inv, ← hgwx]; group
    rwa [hxw] at h
  have hmap_g : (hypLineGroup D hC.d w).map (MulAut.conj g).toMonoidHom ≤
      hypLineGroup D hC.d w := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono hconj_g
  have hmap_ginv : (hypLineGroup D hC.d w).map (MulAut.conj g⁻¹).toMonoidHom ≤
      hypLineGroup D hC.d w := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono hconj_ginv
  refine ⟨hgH, Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hmap_g ⟨y, hy, rfl⟩,
    fun hy => ?_⟩⟩
  have h1 := hmap_ginv ⟨g * y * g⁻¹, hy, rfl⟩
  change g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ ∈ hypLineGroup D hC.d w at h1
  rwa [inv_inv, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1

theorem fiveReflectionsFixing_subset_fiveReflectionGroup {k : ℕ} (ε π : Bool)
    (z : Fin (k + 1) → ZMod 5) :
    fiveReflectionsFixing k ε π z ⊆ fiveReflectionGroup k ε π :=
  fun _ hg => Subgroup.subset_closure hg.1

theorem map_hypLineGroup_eq_fiveReflectionsFixing (hC : HypothesisC D)
    (hα : hC.alpha = {hC.d}) {k : ℕ} {ε π : Bool}
    (θ : Halpha D hC.alpha ≃* fiveReflectionGroup k ε π)
    (hθ : ∀ x, x ∈ DstarH hC ↔ (θ x : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π)
    (c : FiveChart hC (k + 1)) (hcb : c.b = fiveBilin k ε π)
    (hact : ∀ y (hy : y ∈ commSet D hC.d) (x : Fin (k + 1) → ZMod 5),
      ((θ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩ : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x =
        x - (2 * fiveBilin k ε π x (c.vec y)) • c.vec y)
    {w : G} (hwD : w ∈ D) (hwd : ¬ Commute hC.d w)
    {z : Fin (k + 1) → ZMod 5} (hz : IsFiveHyperplane c w z) :
    ((hypLineGroup D hC.d w).subgroupOf (Halpha D hC.alpha)).map θ.toMonoidHom =
      (Subgroup.closure (fiveReflectionsFixing k ε π z)).subgroupOf
        (fiveReflectionGroup k ε π) := by
  have hLH : hypLineGroup D hC.d w ≤ Halpha D hC.alpha :=
    (Subgroup.closure_le _).mpr fun y hy => mem_Halpha_of_mem_commSet hC hα hy.1
  have hgen : θ.toMonoidHom '' ((Halpha D hC.alpha).subtype ⁻¹'
      (commSet D hC.d ∩ commSet D w)) =
      {x : ↥(fiveReflectionGroup k ε π) |
        (x : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionsFixing k ε π z} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(hθ y).mp ?_, ?_⟩
      · exact (mem_DstarH_iff hC).mpr (by
          rw [Nine.DalphaStar_eq_commSet hC hα]; exact hy.1)
      · have h1 := hact (y : G) hy.1 z
        have hy_eq : (⟨(y : G), mem_Halpha_of_mem_commSet hC hα hy.1⟩ :
            Halpha D hC.alpha) = y := Subtype.ext rfl
        rw [hy_eq] at h1
        have hzero : fiveBilin k ε π z (c.vec (y : G)) = 0 := by
          rw [fiveBilin_comm, ← hcb]
          exact (hz.2.2 (y : G) hy.1).mp hy.2.2.1
        rw [hzero, mul_zero, zero_smul] at h1
        have hsub : z - (0 : Fin (k + 1) → ZMod 5) = z := sub_zero z
        rw [hsub] at h1
        exact h1
    · rintro ⟨hxrefl, hxfix⟩
      obtain ⟨y, rfl⟩ := θ.surjective x
      refine ⟨y, ?_, rfl⟩
      have hd : (y : G) ∈ commSet D hC.d := by
        have hyD : y ∈ DstarH hC := (hθ y).mpr hxrefl
        have h := (mem_DstarH_iff hC).mp hyD
        rwa [Nine.DalphaStar_eq_commSet hC hα] at h
      have horth : c.b (c.vec (y : G)) z = 0 := by
        have h1 := hact (y : G) hd z
        have hy_eq : (⟨(y : G), mem_Halpha_of_mem_commSet hC hα hd⟩ :
            Halpha D hC.alpha) = y := Subtype.ext rfl
        rw [hy_eq] at h1
        rw [hxfix] at h1
        have ht : (2 * fiveBilin k ε π z (c.vec (y : G))) • c.vec (y : G) = 0 :=
          sub_eq_self.mp h1.symm
        have hvec : c.vec (y : G) ≠ 0 := by
          intro h0
          have hnorm := c.norm_vec (y : G) hd
          rw [h0] at hnorm
          simpa using hnorm
        have hb0 : fiveBilin k ε π z (c.vec (y : G)) = 0 := by
          rcases smul_eq_zero.mp ht with h | h
          · exact (mul_eq_zero.mp h).resolve_left (by decide : (2 : ZMod 5) ≠ 0)
          · exact absurd h hvec
        rwa [fiveBilin_comm, ← hcb] at hb0
      refine ⟨hd, hd.1, (hz.2.2 (y : G) hd).mpr horth, ?_⟩
      intro hyw
      have hyw' : (y : G) = w := hyw
      exact hwd (hyw' ▸ hd.2.1).symm
  rw [Subgroup.closure_subgroupOf (H := Halpha D hC.alpha)
        (S := commSet D hC.d ∩ commSet D w)
        (fun x hx => hLH (Subgroup.subset_closure hx)),
      MonoidHom.map_closure, hgen,
    Subgroup.closure_subgroupOf (fiveReflectionsFixing_subset_fiveReflectionGroup ε π z)]
  rfl

theorem map_inf_normalizer_eq (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    {k : ℕ} {ε π : Bool}
    (θ : Halpha D hC.alpha ≃* fiveReflectionGroup k ε π)
    {w : G} {z : Fin (k + 1) → ZMod 5}
    (hmapL : ((hypLineGroup D hC.d w).subgroupOf (Halpha D hC.alpha)).map θ.toMonoidHom =
      (Subgroup.closure (fiveReflectionsFixing k ε π z)).subgroupOf
        (fiveReflectionGroup k ε π)) :
    ((Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)).subgroupOf
        (Halpha D hC.alpha)).map θ.toMonoidHom =
      (fiveReflectionGroup k ε π ⊓ Subgroup.normalizer
        (Subgroup.closure (fiveReflectionsFixing k ε π z) :
          Set (GL (Fin (k + 1)) (ZMod 5)))).subgroupOf
        (fiveReflectionGroup k ε π) := by
  have hLH : hypLineGroup D hC.d w ≤ Halpha D hC.alpha :=
    (Subgroup.closure_le _).mpr fun y hy => mem_Halpha_of_mem_commSet hC hα hy.1
  have hK : (Halpha D hC.alpha ⊓
      Subgroup.normalizer (hypLineGroup D hC.d w : Set G)).subgroupOf (Halpha D hC.alpha) =
      Subgroup.normalizer ((hypLineGroup D hC.d w).subgroupOf (Halpha D hC.alpha) :
        Set (Halpha D hC.alpha)) := by
    rw [Subgroup.inf_subgroupOf_left
        (Subgroup.normalizer (hypLineGroup D hC.d w : Set G)) (Halpha D hC.alpha),
      Subgroup.subgroupOf_normalizer_eq hLH]
  rw [hK, Subgroup.map_normalizer_eq_of_bijective
        ((hypLineGroup D hC.d w).subgroupOf (Halpha D hC.alpha)) θ.bijective, hmapL,
    ← Subgroup.subgroupOf_normalizer_eq
      ((Subgroup.closure_le (fiveReflectionGroup k ε π)).mpr
        (fiveReflectionsFixing_subset_fiveReflectionGroup ε π z)),
    Subgroup.inf_subgroupOf_left
      (Subgroup.normalizer (Subgroup.closure (fiveReflectionsFixing k ε π z) :
        Set (GL (Fin (k + 1)) (ZMod 5)))) (fiveReflectionGroup k ε π)]

theorem fiveForm_ite_eq_orderOf_sub_one (hC : HypothesisC D) {k : ℕ} {ε π : Bool}
    {c : FiveChart hC (k + 1)} {w : G} {z : Fin (k + 1) → ZMod 5}
    (hcb : c.b = fiveBilin k ε π) (hz : IsFiveHyperplane c w z)
    (hord : orderOf (hC.d * w) = 3 ∨ orderOf (hC.d * w) = 5) :
    (if fiveForm k ε z z = 0 then 4 else 2) = orderOf (hC.d * w) - 1 := by
  have hzero : fiveForm k ε z z = 0 ↔ fiveBilin k ε π z z = 0 := by
    rw [fiveBilin_apply]
    constructor
    · intro h
      rw [h, mul_zero]
    · intro h
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (fiveSignRep_ne_zero π))
  have hb : (if orderOf (hC.d * w) = 5 then fiveBilin k ε π z z = 0
      else fiveBilin k ε π z z = 2) := by
    simpa [hcb] using hz.2.1
  rcases hord with h3 | h5
  · have hb' : fiveBilin k ε π z z = 2 := by rw [h3] at hb; simpa using hb
    have hf : fiveForm k ε z z ≠ 0 := fun h => by
      have h0 : fiveBilin k ε π z z = 0 := hzero.mp h
      rw [h0] at hb'
      exact (by decide : (0 : ZMod 5) ≠ 2) hb'
    rw [if_neg hf, h3]
  · have hb' : fiveBilin k ε π z z = 0 := by rw [h5] at hb; simpa using hb
    rw [if_pos (hzero.mpr hb'), h5]

theorem relIndex_subgroupOf_hypLineGroup (hC : HypothesisC D) {w : G} :
    (hypLineGroup D hC.d w).relIndex
        (Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)) =
      ((hypLineGroup D hC.d w).subgroupOf (Halpha D hC.alpha)).relIndex
        ((Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)).subgroupOf
          (Halpha D hC.alpha)) :=
  (Subgroup.relIndex_subgroupOf (H := hypLineGroup D hC.d w)
    (K := Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G))
    (L := Halpha D hC.alpha) inf_le_left).symm

theorem relIndex_map_transport_hypLineGroup (hC : HypothesisC D) {k : ℕ} {ε π : Bool}
    (θ : Halpha D hC.alpha ≃* fiveReflectionGroup k ε π) {w : G} :
    ((hypLineGroup D hC.d w).subgroupOf (Halpha D hC.alpha)).relIndex
        ((Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)).subgroupOf
          (Halpha D hC.alpha)) =
      (((hypLineGroup D hC.d w).subgroupOf (Halpha D hC.alpha)).map θ.toMonoidHom).relIndex
        (((Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)).subgroupOf
          (Halpha D hC.alpha)).map θ.toMonoidHom) :=
  (Subgroup.relIndex_map_map_of_injective
    ((hypLineGroup D hC.d w).subgroupOf (Halpha D hC.alpha))
    ((Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)).subgroupOf
      (Halpha D hC.alpha)) θ.injective).symm

theorem relIndex_mapped_hypLineGroup_eq_ite (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (θ : Halpha D hC.alpha ≃* fiveReflectionGroup k ε π)
    (hθ : ∀ x, x ∈ DstarH hC ↔ (θ x : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π)
    (c : FiveChart hC (k + 1)) (hcb : c.b = fiveBilin k ε π)
    (hact : ∀ y (hy : y ∈ commSet D hC.d) (x : Fin (k + 1) → ZMod 5),
      ((θ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩ : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x =
        x - (2 * fiveBilin k ε π x (c.vec y)) • c.vec y)
    {w : G} (hwD : w ∈ D) (hwd : ¬ Commute hC.d w)
    {z : Fin (k + 1) → ZMod 5} (hz : IsFiveHyperplane c w z) :
    (((hypLineGroup D hC.d w).subgroupOf (Halpha D hC.alpha)).map θ.toMonoidHom).relIndex
        (((Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)).subgroupOf
          (Halpha D hC.alpha)).map θ.toMonoidHom) =
      (if fiveForm k ε z z = 0 then 4 else 2) := by
  have hmapL := map_hypLineGroup_eq_fiveReflectionsFixing hC hα θ hθ c hcb hact hwD hwd hz
  have hmapK := map_inf_normalizer_eq hC hα θ hmapL
  rw [hmapL, hmapK,
    Subgroup.relIndex_subgroupOf
      (H := Subgroup.closure (fiveReflectionsFixing k ε π z))
      (K := fiveReflectionGroup k ε π ⊓ Subgroup.normalizer
        (Subgroup.closure (fiveReflectionsFixing k ε π z) : Set (GL (Fin (k + 1)) (ZMod 5))))
      (L := fiveReflectionGroup k ε π) inf_le_left]
  exact relIndex_normalizer_fiveReflectionsFixing hk ε π hz.1

theorem relIndex_hypLineGroup_eq_ncard_sub_one (hC : HypothesisC D)
    (hα : hC.alpha = {hC.d}) {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (θ : Halpha D hC.alpha ≃* fiveReflectionGroup k ε π)
    (hθ : ∀ x, x ∈ DstarH hC ↔ (θ x : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π)
    (c : FiveChart hC (k + 1)) (hcb : c.b = fiveBilin k ε π)
    (hact : ∀ y (hy : y ∈ commSet D hC.d) (x : Fin (k + 1) → ZMod 5),
      ((θ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩ : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x =
        x - (2 * fiveBilin k ε π x (c.vec y)) • c.vec y)
    {w : G} (hwD : w ∈ D) (hwd : ¬ Commute hC.d w)
    {z : Fin (k + 1) → ZMod 5} (hz : IsFiveHyperplane c w z)
    (hE : (lineMem D hC.d w).ncard = orderOf (hC.d * w))
    (hord : orderOf (hC.d * w) = 3 ∨ orderOf (hC.d * w) = 5) :
    (hypLineGroup D hC.d w).relIndex
        (Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)) =
      (lineMem D hC.d w).ncard - 1 := by
  rw [relIndex_subgroupOf_hypLineGroup, relIndex_map_transport_hypLineGroup,
    relIndex_mapped_hypLineGroup_eq_ite hC hα hk θ hθ c hcb hact hwD hwd hz,
    fiveForm_ite_eq_orderOf_sub_one hC hcb hz hord, ← hE]

theorem relIndex_centralizer_bound (hC : HypothesisC D) {w : G}
    (htrans : ∀ x ∈ lineMem D hC.d w, x ≠ hC.d →
      ∃ g ∈ Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G),
        g * w * g⁻¹ = x) :
    (lineMem D hC.d w).ncard - 1 ≤
      (Halpha D hC.alpha ⊓ Subgroup.centralizer ({w} : Set G)).relIndex
        (Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)) := by
  classical
  have hEd : hC.d ∈ lineMem D hC.d w := self_mem_lineMem_left hC.hd
  let K := Halpha D hC.alpha ⊓ Subgroup.centralizer ({w} : Set G)
  let N := Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)
  let E := lineMem D hC.d w
  let gx : ↥(E \ {hC.d}) → G := fun x => Classical.choose (htrans x.1 x.2.1 x.2.2)
  have hgxN : ∀ x, gx x ∈ N := fun x => (Classical.choose_spec (htrans x.1 x.2.1 x.2.2)).1
  have hgxwx : ∀ x, gx x * w * (gx x)⁻¹ = x.1 := fun x =>
    (Classical.choose_spec (htrans x.1 x.2.1 x.2.2)).2
  let f : ↥(E \ {hC.d}) → ↥N ⧸ K.subgroupOf N := fun x =>
    QuotientGroup.mk (s := K.subgroupOf N) ⟨gx x, hgxN x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hdiv : (⟨gx x, hgxN x⟩ : ↥N)⁻¹ * ⟨gx y, hgxN y⟩ ∈ K.subgroupOf N :=
      QuotientGroup.eq.mp hxy
    have hzK : (gx x)⁻¹ * gx y ∈ K := hdiv
    have hzw : Commute ((gx x)⁻¹ * gx y) w :=
      Subgroup.mem_centralizer_singleton_iff.mp hzK.2
    apply Subtype.ext
    calc x.1 = gx x * w * (gx x)⁻¹ := (hgxwx x).symm
      _ = gx y * w * (gx y)⁻¹ := by
            rw [show gx y = gx x * ((gx x)⁻¹ * gx y) by group,
              mul_assoc (gx x) ((gx x)⁻¹ * gx y) w, hzw.eq]
            group
      _ = y.1 := hgxwx y
  have hcard : (E \ {hC.d}).ncard ≤ K.relIndex N := by
    have h := Nat.card_le_card_of_injective f hf
    rw [show K.relIndex N = Nat.card (↥N ⧸ K.subgroupOf N) from rfl]
    exact h
  rwa [Set.ncard_sdiff_singleton_of_mem hEd] at hcard

theorem centralizer_eq_hypLineGroup (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    {w : G} (hwd : ¬ Commute hC.d w)
    (hrel : (hypLineGroup D hC.d w).relIndex
        (Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)) =
      (lineMem D hC.d w).ncard - 1)
    (htrans : ∀ x ∈ lineMem D hC.d w, x ≠ hC.d →
      ∃ g ∈ Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G),
        g * w * g⁻¹ = x) :
    Halpha D hC.alpha ⊓ Subgroup.centralizer ({w} : Set G) = hypLineGroup D hC.d w := by
  let K := Halpha D hC.alpha ⊓ Subgroup.centralizer ({w} : Set G)
  let N := Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)
  have hLH : hypLineGroup D hC.d w ≤ Halpha D hC.alpha :=
    (Subgroup.closure_le _).mpr fun y hy => mem_Halpha_of_mem_commSet hC hα hy.1
  have hLw : hypLineGroup D hC.d w ≤ Subgroup.centralizer ({w} : Set G) :=
    (Subgroup.closure_le _).mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr hy.2.2.1.eq
  have hLK : hypLineGroup D hC.d w ≤ K := le_inf hLH hLw
  have hKN : K ≤ N := by
    rintro g ⟨hgH, hgw⟩
    exact ⟨hgH, mem_normalizer_hypLineGroup_of_mem_Halpha_of_commute hC hgH
      (Subgroup.mem_centralizer_singleton_iff.mp hgw)⟩
  have hbound := relIndex_centralizer_bound hC htrans
  have hKle : K.relIndex N ≤ (hypLineGroup D hC.d w).relIndex N := by
    have hLrelK : (hypLineGroup D hC.d w).relIndex K ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    calc K.relIndex N = 1 * K.relIndex N := (one_mul _).symm
      _ ≤ (hypLineGroup D hC.d w).relIndex K * K.relIndex N :=
          Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr hLrelK)
      _ = (hypLineGroup D hC.d w).relIndex N :=
          Subgroup.relIndex_mul_relIndex (H := hypLineGroup D hC.d w) (K := K) (L := N) hLK hKN
  have hKeq : K.relIndex N = (hypLineGroup D hC.d w).relIndex N :=
    le_antisymm hKle (by rw [hrel]; exact hbound)
  have hLrelK1 : (hypLineGroup D hC.d w).relIndex K = 1 := by
    have hKNrel : K.relIndex N ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hmul : (hypLineGroup D hC.d w).relIndex K * K.relIndex N = 1 * K.relIndex N := by
      rw [Subgroup.relIndex_mul_relIndex (H := hypLineGroup D hC.d w) (K := K) (L := N) hLK hKN,
        hKeq, one_mul]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hKNrel) hmul
  exact (le_antisymm hLK (Subgroup.relIndex_eq_one.mp hLrelK1)).symm

end CFSG.OddTranspositions.PartThree
