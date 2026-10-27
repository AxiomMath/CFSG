module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
import CFSG.RankThree.GF2n.Tim81.Sec6.M0Basic
import CFSG.RankThree.GF2n.Tim81.Sec6.M0Setup
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

theorem imgQ_iSup {ι : Sort*} (s : ι → Subgroup G) (hs : ∀ i, s i ≤ M) :
    imgQ M (⨆ i, s i) = ⨆ i, imgQ M (s i) := by
  have hsub : (⨆ i, s i).subgroupOf M = ⨆ i, (s i).subgroupOf M := by
    apply Subgroup.map_injective (f := M.subtype) M.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (iSup_le hs), Subgroup.map_iSup]
    rw [show (⨆ i, ((s i).subgroupOf M).map M.subtype) = ⨆ i, s i from
      iSup_congr fun i => Subgroup.map_subgroupOf_eq_of_le (hs i)]
  rw [imgQ, hsub, Subgroup.map_iSup]

private theorem imgQ_biSup {ι : Sort*} (s : ι → Subgroup G) (p : ι → Prop)
    (hs : ∀ i, p i → s i ≤ M) :
    imgQ M (⨆ i, ⨆ (_ : p i), s i) = ⨆ i, ⨆ (_ : p i), imgQ M (s i) := by
  rw [iSup_subtype' (f := fun i (_ : p i) => s i),
    iSup_subtype' (f := fun i (_ : p i) => imgQ M (s i))]
  exact imgQ_iSup (fun i : Subtype p => s i) (fun i => hs i.1 i.2)

theorem Sec6Hyp.sup_inf_Pc_eq_bot (hS : Sec6Hyp M V) {C D : Subgroup G}
    (hC : C ∈ sigmaSet M V) (hD : D ∈ sigmaSet M V) (hCD : IsL2Gen C D) :
    (C ⊔ D) ⊓ Pc M V = ⊥ := by
  have hCM : C ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hC).1
  have hDM : D ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD).1
  have hHle : C ⊔ D ≤ M := _root_.sup_le hCM hDM
  have hN : C ⊔ D ≤ Subgroup.normalizer (Pc M V : Set G) :=
    hHle.trans hS.sec5.toRootHyp.toHyp.le_normalizer_Pc
  have hnormal : (((C ⊔ D) ⊓ Pc M V).subgroupOf (C ⊔ D)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun x hx =>
      mem_normalizer_inf (show x ∈ Subgroup.normalizer ((C ⊔ D : Subgroup G) : Set G) from
        Subgroup.le_normalizer hx) (hN hx)
  have h4C : 4 ≤ Nat.card C := by
    obtain ⟨g, rfl, -⟩ := hC
    rw [card_conjSubgroup]
    exact hS.sec5.toRootHyp.four_le_card
  haveI : IsSimpleGroup ↥(C ⊔ D) := hCD.isSimpleGroup h4C
  have hbot : ((C ⊔ D) ⊓ Pc M V).subgroupOf (C ⊔ D) = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top
      (((C ⊔ D) ⊓ Pc M V).subgroupOf (C ⊔ D)) with h | h
    · exact h
    · exfalso
      have hC_le : C ≤ (C ⊔ D) ⊓ Pc M V := by
        intro c hc
        have hcH : c ∈ C ⊔ D := Subgroup.mem_sup_left hc
        have hmem : (⟨c, hcH⟩ : ↥(C ⊔ D)) ∈
            ((C ⊔ D) ⊓ Pc M V).subgroupOf (C ⊔ D) := by
          rw [h]
          exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp hmem
      have hCP : C ≤ Pc M V := hC_le.trans inf_le_right
      have hCbot : C = ⊥ := by
        rw [← hS.sec5.inf_Pc_eq_bot hC, inf_eq_left.mpr hCP]
      have hcard : Nat.card C = 1 := by rw [hCbot, Subgroup.card_bot]
      omega
  refine le_bot_iff.mp ?_
  intro x hx
  have hxH : x ∈ C ⊔ D := hx.1
  have hmem : (⟨x, hxH⟩ : ↥(C ⊔ D)) ∈
      ((C ⊔ D) ⊓ Pc M V).subgroupOf (C ⊔ D) := Subgroup.mem_subgroupOf.mpr hx
  rw [hbot] at hmem
  have hx1 : (⟨x, hxH⟩ : ↥(C ⊔ D)) = 1 := Subgroup.mem_bot.mp hmem
  exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hx1)

theorem imgQ_sup {C D : Subgroup G} (hC : C ≤ M) (hD : D ≤ M) :
    imgQ M (C ⊔ D) = imgQ M C ⊔ imgQ M D := by
  rw [imgQ, Subgroup.subgroupOf_sup hC hD, Subgroup.map_sup]

theorem Sec6Hyp.mk_mem_centralizer_imgQ_iff (hS : Sec6Hyp M V) {Y : Subgroup G} (hY : Y ≤ M)
    (x : ↥M) :
    QuotientGroup.mk' (pCore 2 ↥M) x ∈
        Subgroup.centralizer (imgQ M Y : Set (MBar M)) ↔
      ∀ y ∈ Y, ⁅(x : G), y⁆ ∈ Pc M V := by
  constructor
  · intro hx y hy
    have hmem : QuotientGroup.mk' (pCore 2 ↥M) (⟨y, hY hy⟩ : ↥M) ∈ imgQ M Y := mk_mem_imgQ hy
    have hcomm : ⁅QuotientGroup.mk' (pCore 2 ↥M) x,
        QuotientGroup.mk' (pCore 2 ↥M) (⟨y, hY hy⟩ : ↥M)⁆ = 1 :=
      (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hx) _ hmem
    have hmap : QuotientGroup.mk' (pCore 2 ↥M) (⁅x, ⟨y, hY hy⟩⁆ : ↥M) = 1 := by
      rw [map_commutatorElement]
      exact hcomm
    have hmemP := (Sec6Hyp.mk_eq_one_iff hS ⁅x, ⟨y, hY hy⟩⁆).mp hmap
    simpa [commutatorElement_def] using hmemP
  · intro hx
    refine Subgroup.mem_centralizer_iff_commutator_eq_one'.mpr ?_
    intro z hz
    obtain ⟨y, hy, rfl⟩ := mem_imgQ_iff.mp hz
    have hmem : ⁅(x : G), (y : G)⁆ ∈ Pc M V := hx (y : G) hy
    have h1 : QuotientGroup.mk' (pCore 2 ↥M) (⁅x, y⁆ : ↥M) = 1 := by
      refine (Sec6Hyp.mk_eq_one_iff hS ⁅x, y⁆).mpr ?_
      simpa [commutatorElement_def] using hmem
    rw [← map_commutatorElement, h1]

theorem L2Datum.orderOf_mk (hS : Sec6Hyp M V) (hD : L2Datum M V A B h) (hhM : h ∈ M) :
    orderOf (QuotientGroup.mk' (pCore 2 ↥M) ⟨h, hhM⟩) = Nat.card V + 1 := by
  have hAM : A ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
  have hBM : B ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  have hHle : A ⊔ B ≤ M := _root_.sup_le hAM hBM
  let f : ↥(A ⊔ B) →* MBar M :=
    (QuotientGroup.mk' (pCore 2 ↥M)).comp (Subgroup.inclusion hHle)
  have hker : f.ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    intro x y hxy
    have h1 : f (x⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hP : (((x⁻¹ * y : ↥(A ⊔ B)) : G)) ∈ Pc M V := by
      have hsubM : (((x⁻¹ * y : ↥(A ⊔ B)) : G)) ∈ M :=
        _root_.sup_le hAM hBM (x⁻¹ * y).2
      have h2 : QuotientGroup.mk' (pCore 2 ↥M)
          (⟨((x⁻¹ * y : ↥(A ⊔ B)) : G), hsubM⟩ : ↥M) = 1 := h1
      exact (Sec6Hyp.mk_eq_one_iff hS _).mp h2
    have h4 : (((x⁻¹ * y : ↥(A ⊔ B)) : G)) ∈ (⊥ : Subgroup G) := by
      rw [← hS.sup_inf_Pc_eq_bot hD.memA hD.memB hD.l2]
      exact Subgroup.mem_inf.mpr ⟨(x⁻¹ * y).2, hP⟩
    have h5 : x⁻¹ * y = 1 := Subtype.ext (Subgroup.mem_bot.mp h4)
    have h6 : y = x := by
      calc y = x * (x⁻¹ * y) := by group
        _ = x * 1 := by rw [h5]
        _ = x := mul_one x
    exact h6.symm
  have hinj : Function.Injective f := MonoidHom.ker_eq_bot_iff f |>.mp hker
  have h1 : orderOf (f ⟨h, hD.mem⟩) = orderOf (⟨h, hD.mem⟩ : ↥(A ⊔ B)) :=
    orderOf_injective f hinj _
  have h2 : orderOf (⟨h, hD.mem⟩ : ↥(A ⊔ B)) = orderOf h :=
    (Subgroup.orderOf_coe _).symm
  have h3 : f ⟨h, hD.mem⟩ = QuotientGroup.mk' (pCore 2 ↥M) ⟨h, hhM⟩ := rfl
  rw [← h3, h1, h2, hD.order]

theorem imgQ_le_centralizer_of_le_cenOf {C D : Subgroup G} (h : C ≤ cenOf D) :
    imgQ M C ≤ Subgroup.centralizer (imgQ M D : Set (MBar M)) := by
  intro z hz
  obtain ⟨c, hc, rfl⟩ := mem_imgQ_iff.mp hz
  refine Subgroup.mem_centralizer_iff_commutator_eq_one'.mpr fun w hw => ?_
  obtain ⟨d, hd, rfl⟩ := mem_imgQ_iff.mp hw
  have hcd : (d : G) * (c : G) = (c : G) * (d : G) :=
    Subgroup.mem_centralizer_iff.mp (h hc) (d : G) hd
  have h1 : (⁅c, d⁆ : ↥M) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_one]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcd.symm
  rw [← map_commutatorElement, h1, map_one]

theorem Sec6Hyp.commutator_eq_bot_of_imgQ (hS : Sec6Hyp M V) {C D : Subgroup G}
    (hC : C ∈ sigmaSet M V) (hD : D ∈ sigmaSet M V) (h : ⁅imgQ M C, imgQ M D⁆ = ⊥) :
    ⁅C, D⁆ = ⊥ := by
  rcases hS.res.s513 M V hS.sec5 C hC D hD with ⟨hCD, -⟩ | ⟨hL2, -⟩
  · exact hCD
  · exact absurd h (hS.isL2Gen_imgQ hC hD hL2).commutator_ne_bot

theorem L2Datum.le_cenOf_of_imgQ_le (hS : Sec6Hyp M V) (hD : L2Datum M V A B h)
    {C : Subgroup G} (hC : C ∈ sigmaSet M V)
    (h : imgQ M C ≤ Subgroup.centralizer
      ((imgQ M A ⊔ imgQ M B : Subgroup (MBar M)) : Set (MBar M))) :
    C ≤ cenOf (A ⊔ B) := by
  have hCA : ⁅imgQ M C, imgQ M A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
  have hCB : ⁅imgQ M C, imgQ M B⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))
  rw [show cenOf (A ⊔ B) = cenOf A ⊓ cenOf B from centralizer_sup_eq A B]
  exact le_inf
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (hS.commutator_eq_bot_of_imgQ hC hD.memA hCA))
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (hS.commutator_eq_bot_of_imgQ hC hD.memB hCB))

theorem L2Datum.perpRoots_eq (hS : Sec6Hyp M V) (hD : L2Datum M V A B h) :
    perpRoots (imgQ M '' sigmaSet M V) (imgQ M A ⊔ imgQ M B) =
      imgQ M (r0Of M V (A ⊔ B)) := by
  have hImg : imgQ M (r0Of M V (A ⊔ B)) =
      ⨆ C ∈ {C : Subgroup G | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}, imgQ M C := by
    unfold r0Of
    exact imgQ_biSup (fun C : Subgroup G => C) _
      (fun C hC => (hS.sec5.le_M_of_mem_sigmaSet hC.1).1)
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun D hDmem => ?_
    obtain ⟨hDimg, hDcen⟩ := hDmem
    obtain ⟨C, hC, hCD⟩ := hDimg
    have hCAB : C ≤ cenOf (A ⊔ B) :=
      L2Datum.le_cenOf_of_imgQ_le hS hD hC (hCD.symm ▸ hDcen)
    rw [← hCD, hImg]
    exact le_iSup₂_of_le C ⟨hC, hCAB⟩ le_rfl
  · rw [hImg]
    refine iSup₂_le fun C hC => ?_
    have hAsub : ((A : Subgroup G) : Set G) ⊆ ((A ⊔ B : Subgroup G) : Set G) :=
      SetLike.coe_subset_coe.mpr le_sup_left
    have hBsub : ((B : Subgroup G) : Set G) ⊆ ((A ⊔ B : Subgroup G) : Set G) :=
      SetLike.coe_subset_coe.mpr le_sup_right
    have hCA : imgQ M C ≤ Subgroup.centralizer (imgQ M A : Set (MBar M)) :=
      imgQ_le_centralizer_of_le_cenOf (hC.2.trans (Subgroup.centralizer_le hAsub))
    have hCB : imgQ M C ≤ Subgroup.centralizer (imgQ M B : Set (MBar M)) :=
      imgQ_le_centralizer_of_le_cenOf (hC.2.trans (Subgroup.centralizer_le hBsub))
    have hcen : imgQ M C ≤
        Subgroup.centralizer ((imgQ M A ⊔ imgQ M B : Subgroup (MBar M)) : Set (MBar M)) :=
      (le_inf hCA hCB).trans
        (le_of_eq (centralizer_sup_eq (imgQ M A) (imgQ M B)).symm)
    exact le_iSup₂_of_le (imgQ M C)
      (show imgQ M C ∈ {D : Subgroup (MBar M) | D ∈ imgQ M '' sigmaSet M V ∧
        D ≤ Subgroup.centralizer
          ((imgQ M A ⊔ imgQ M B : Subgroup (MBar M)) : Set (MBar M))}
        from ⟨⟨C, hC.1, rfl⟩, hcen⟩) le_rfl

end CFSG.RankThree.GF2n.Tim81
