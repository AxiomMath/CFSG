module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped commutatorElement Pointwise

@[expose] def Zc {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  (Subgroup.center ↥L).map L.subtype

variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}

theorem w135c2_Zc_le (L : Subgroup (MulAut W)) : Zc L ≤ L := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

private theorem w135c2_Zc_central (L : Subgroup (MulAut W)) :
    Zc L ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
  intro z hz
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h := Subgroup.mem_center_iff.mp hz' (⟨l, hl⟩ : ↥L)
  simpa using congrArg Subtype.val h

theorem w135c2_Zc_normal_in (hctx : Is135Context Y L) : ((Zc L).subgroupOf Y).Normal := by
  have hN : (L.subgroupOf Y).Normal := w135_normal_of_ctx hctx
  have hLY : L ≤ Y := hctx.2.2.1
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨z, hz, hzn⟩ := Subgroup.mem_map.mp hn
  have hnL : (n : MulAut W) ∈ L := w135c2_Zc_le L hn
  have hnz : (n : MulAut W) = (z : MulAut W) := by rw [← hzn]; rfl
  have hzcomm : ∀ l' : ↥L,
      (z : MulAut W) * (l' : MulAut W) = (l' : MulAut W) * (z : MulAut W) :=
    fun l' => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz l')).symm
  have hconjL : (g : MulAut W) * (n : MulAut W) * (g : MulAut W)⁻¹ ∈ L := by
    have hmem : g * n * g⁻¹ ∈ L.subgroupOf Y :=
      hN.conj_mem n (Subgroup.mem_subgroupOf.mpr hnL) g
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
  have hconjLz : (g : MulAut W) * (z : MulAut W) * (g : MulAut W)⁻¹ ∈ L := by
    simpa only [hnz] using hconjL
  change ↑(g * n * g⁻¹) ∈ (Subgroup.center ↥L).map L.subtype
  rw [Subgroup.mem_map]
  refine ⟨⟨(g : MulAut W) * (z : MulAut W) * (g : MulAut W)⁻¹, hconjLz⟩, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    have hmem : (g : MulAut W)⁻¹ * (l : MulAut W) * (g : MulAut W) ∈ L := by
      have hmemY : (⟨(l : MulAut W), hLY l.2⟩ : ↥Y) ∈ L.subgroupOf Y :=
        Subgroup.mem_subgroupOf.mpr l.2
      have := hN.conj_mem' (⟨(l : MulAut W), hLY l.2⟩ : ↥Y) hmemY g
      simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using this
    have hz' : ((g : MulAut W)⁻¹ * (l : MulAut W) * (g : MulAut W)) * (z : MulAut W)
        = (z : MulAut W) * ((g : MulAut W)⁻¹ * (l : MulAut W) * (g : MulAut W)) :=
      (hzcomm ⟨_, hmem⟩).symm
    calc (l : MulAut W) * ((g : MulAut W) * (z : MulAut W) * (g : MulAut W)⁻¹)
        = (g : MulAut W) * (((g : MulAut W)⁻¹ * (l : MulAut W) * (g : MulAut W))
            * (z : MulAut W)) * (g : MulAut W)⁻¹ := by group
      _ = (g : MulAut W) * ((z : MulAut W)
            * ((g : MulAut W)⁻¹ * (l : MulAut W) * (g : MulAut W))) * (g : MulAut W)⁻¹ := by
          rw [hz']
      _ = ((g : MulAut W) * (z : MulAut W) * (g : MulAut W)⁻¹) * (l : MulAut W) := by group
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnz]
    rfl

private def w135c2_commZcSub (hZY : Zc L ≤ Y) (hZnorm : ((Zc L).subgroupOf Y).Normal) :
    Subgroup (MulAut W) where
  carrier := {g | g ∈ Y ∧ ∀ l ∈ L, ⁅g, l⁆ ∈ Zc L}
  one_mem' := ⟨Y.one_mem, by intro l _; simp⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨Y.mul_mem ha.1 hb.1, ?_⟩
    intro l hl
    rw [commutatorElement_mul_left_eq_conj_mul]
    refine (Zc L).mul_mem ?_ (ha.2 l hl)
    have hblY : ⁅b, l⁆ ∈ Y := hZY (hb.2 l hl)
    have hmem : (⟨a, ha.1⟩ : ↥Y) * ⟨⁅b, l⁆, hblY⟩ * (⟨a, ha.1⟩ : ↥Y)⁻¹
        ∈ (Zc L).subgroupOf Y :=
      hZnorm.conj_mem ⟨⁅b, l⁆, hblY⟩ (Subgroup.mem_subgroupOf.mpr (hb.2 l hl)) ⟨a, ha.1⟩
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
  inv_mem' := by
    intro a ha
    refine ⟨Y.inv_mem ha.1, ?_⟩
    intro l hl
    rw [commutatorElement_inv_left]
    have hlaZ : ⁅l, a⁆ ∈ Zc L := by
      simpa using (Zc L).inv_mem (ha.2 l hl)
    have hlaY : ⁅l, a⁆ ∈ Y := hZY hlaZ
    have hmem : (⟨a, ha.1⟩ : ↥Y)⁻¹ * ⟨⁅l, a⁆, hlaY⟩ * (⟨a, ha.1⟩ : ↥Y)
        ∈ (Zc L).subgroupOf Y :=
      hZnorm.conj_mem' ⟨⁅l, a⁆, hlaY⟩ (Subgroup.mem_subgroupOf.mpr hlaZ) (⟨a, ha.1⟩ : ↥Y)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using hmem

private lemma w135c2_commZcSub_mem {hZY : Zc L ≤ Y}
    {hZnorm : ((Zc L).subgroupOf Y).Normal} {g : MulAut W} :
    g ∈ w135c2_commZcSub (Y := Y) (L := L) hZY hZnorm ↔
      g ∈ Y ∧ ∀ l ∈ L, ⁅g, l⁆ ∈ Zc L :=
  Iff.rfl

theorem w135c2_mem_Zc_of_comm (hctx : Is135Context Y L) {y : MulAut W} (hy : y ∈ Y)
    (h : ∀ l ∈ L, ⁅y, l⁆ ∈ Zc L) : y ∈ Zc L := by
  have hZY : Zc L ≤ Y := (w135c2_Zc_le L).trans hctx.2.2.1
  have hZnorm : ((Zc L).subgroupOf Y).Normal := w135c2_Zc_normal_in hctx
  have hy0 : y ∈ w135c2_commZcSub (Y := Y) (L := L) hZY hZnorm :=
    w135c2_commZcSub_mem.mpr ⟨hy, h⟩
  have hH3le : Subgroup.zpowers y ≤ w135c2_commZcSub (Y := Y) (L := L) hZY hZnorm :=
    Subgroup.zpowers_le.mpr hy0
  have hLH3 : ⁅L, Subgroup.zpowers y⁆ ≤ Zc L :=
    (Subgroup.commutator_mono_right hH3le).trans
      (Subgroup.commutator_le.mpr fun p hp q hq => by
        have hq' : ⁅q, p⁆ ∈ Zc L := (w135c2_commZcSub_mem.mp hq).2 p hp
        simpa using (Zc L).inv_mem hq')
  have hH3L : ⁅Subgroup.zpowers y, L⁆ ≤ Zc L :=
    Subgroup.commutator_le.mpr fun p hp q hq =>
      (w135c2_commZcSub_mem.mp (hH3le hp)).2 q hq
  have hZL : ⁅Zc L, L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (w135c2_Zc_central L)
  have h1 : ⁅⁅L, Subgroup.zpowers y⁆, L⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono_left hLH3).trans (le_of_eq hZL))
  have h2 : ⁅⁅Subgroup.zpowers y, L⁆, L⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono_left hH3L).trans (le_of_eq hZL))
  have h3 : ⁅⁅L, L⁆, Subgroup.zpowers y⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hLL : ⁅L, L⁆ = L := by
    haveI : Group.IsPerfect ↥L := hctx.2.2.2.2.1.1
    exact Subgroup.commutator_eq_self
  have hLH3bot : ⁅L, Subgroup.zpowers y⁆ = ⊥ := by
    rwa [hLL] at h3
  have hcent : L ≤ Subgroup.centralizer (Subgroup.zpowers y : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLH3bot
  have hy_comm : ∀ l : ↥L, (l : MulAut W) * y = y * (l : MulAut W) := by
    intro l
    exact (Subgroup.mem_centralizer_iff.mp (hcent l.2) y (Subgroup.mem_zpowers y)).symm
  have hyF : (⟨y, hy⟩ : ↥Y) ∈ genFittingFStar ↥Y := by
    refine CFSG.Adapters.generalized_fitting_self_centralizing ↥Y ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    have hfL : (f : MulAut W) ∈ L := by
      have hfF : (f : MulAut W) ∈ Fstar Y := ⟨f, hf, rfl⟩
      rwa [hctx.2.2.2.1] at hfF
    exact hy_comm ⟨(f : MulAut W), hfL⟩
  have hyFstar : y ∈ Fstar Y := ⟨⟨y, hy⟩, hyF, rfl⟩
  have hyL : y ∈ L := by rwa [hctx.2.2.2.1] at hyFstar
  have hycenter : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact hy_comm l
  exact Subgroup.mem_map.mpr ⟨⟨y, hyL⟩, hycenter, rfl⟩

theorem w135c2_not_mem_Zc_of_order_two (hctx : Is135Context Y L) {t : MulAut W}
    (ht2 : orderOf t = 2) : t ∉ Zc L := by
  intro ht
  obtain ⟨z, hz, hzt⟩ := Subgroup.mem_map.mp ht
  have hz2 : orderOf z = 2 := by
    have h1 : orderOf (L.subtype z) = orderOf z := Subgroup.orderOf_coe z
    have h2 : orderOf (L.subtype z) = orderOf t := congrArg orderOf hzt
    exact (h1.symm.trans h2).trans ht2
  have hdvd : 2 ∣ Nat.card (Subgroup.center ↥L) := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hz
    rwa [hz2] at this
  exact (Nat.not_even_iff_odd.mpr (w135_odd_card_center hctx)) (even_iff_two_dvd.mpr hdvd)

end CFSG.LocalAnalysis.WeakClosure81
