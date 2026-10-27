module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bPlan
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec10.Sec10XProofThirteen
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem mem_lA_map_subtype {G : Type} [Group G] [Finite G] {F : Subgroup G} {b : G}
    (hbF : b ∈ F) (hb3 : Nat.card (Subgroup.zpowers b) = 3) (h27 : Nat.card F = 27)
    (C : Subgroup G) (hC : C = Subgroup.centralizer ({b} : Set G)) (hFC : F ≤ C)
    {L' : Subgroup C} (hL' : L' ∈ thetaComponents 3 C)
    (hA'N : F.subgroupOf C ≤ Subgroup.normalizer (L' : Set C))
    (h9 : Nat.card (Sec4.autThetaQuot (F.subgroupOf C) L') = 9)
    (hα : thetaAlpha 3
      ((Sec4.autThetaQuot (F.subgroupOf C) L').subgroupOf (Sec4.autThetaQuot ⊤ L')) ≠ ⊥) :
    L'.map C.subtype ∈ lA F b := by
  have hLc : L'.map C.subtype ∈ thetaComponentsAt 3 b := by
    subst hC
    exact ⟨L', hL', rfl⟩
  set A' := F.subgroupOf C with hA'def
  have hA'map : A'.map C.subtype = F := by
    rw [hA'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hFC]
  set L := L'.map C.subtype with hLdef
  have hAN : F ≤ Subgroup.normalizer (L : Set G) := by
    intro a ha
    have hmem : (⟨a, hFC ha⟩ : C) ∈ A' := Subgroup.mem_subgroupOf.mpr ha
    exact (coe_mem_normalizer_map_iff C).mpr (hA'N hmem)
  have hAut : Nat.card (Sec4.autThetaQuot F L) = 9 := by
    rw [← hA'map, hLdef, ← map_autThetaQuot_sub C A' L',
      Subgroup.card_map_of_injective (MulAut.congr (thetaQuotEquivSub C L')).injective, h9]
  have hcT : b ∈ Sec4.thetaQuotCentralizer L :=
    Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLc
  have hsc : Late.sectionCentralizer F L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers b : Set G) := by
    rw [sectionCentralizer_eq_inf hAN]
    congr 1
    have h3 : Nat.card (F ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 := by
      have := card_inf_mul_card_autThetaQuot hAN
      rw [hAut, h27] at this
      omega
    have hbmem : b ∈ F ⊓ Sec4.thetaQuotCentralizer L := Subgroup.mem_inf.mpr ⟨hbF, hcT⟩
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbmem)
      (by rw [h3, hb3])).symm
  have hαC : thetaAlpha 3 ((Sec4.autThetaQuot F L).subgroupOf (Sec4.autThetaQuot C L)) ≠ ⊥ := by
    have hC' : (⊤ : Subgroup C).map C.subtype = C := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← (thetaAlpha_subgroupOf_map_ne_bot_iff (MulAut.congr (thetaQuotEquivSub C L'))
      (Sec4.autThetaQuot A' L') (Sec4.autThetaQuot ⊤ L'))] at hα
    rwa [map_autThetaQuot_sub, map_autThetaQuot_sub, hA'map, hC'] at hα
  have hCH : C ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    hC ▸ centralizer_le_normalizer_zpowers b
  have hNorm : ((Sec4.autThetaQuot C L).subgroupOf
      (Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers b : Set G)) L)).Normal :=
    hC ▸ autThetaQuot_centralizer_normal b L
  exact ⟨hLc, hAN, hsc, thetaAlpha_ne_bot_of_le (autThetaQuot_mono hFC L)
    (autThetaQuot_mono hCH L) hNorm hαC⟩

theorem maximal_subgroupOf_of_le {G : Type} [Group G] {A C : Subgroup G}
    (hA : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hAC : A ≤ C) :
    Maximal (fun B : Subgroup C => CFSG.Assembly.IsElemAbelian 3 B) (A.subgroupOf C) := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  refine ⟨⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp x.2) _
      (Subgroup.mem_subgroupOf.mp y.2)))⟩⟩,
      fun x hx => Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp hx))⟩, fun B hB hAB => ?_⟩
  have hBe : CFSG.Assembly.IsElemAbelian 3 (B.map C.subtype) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := x
      obtain ⟨_, y, hy, rfl⟩ := y
      apply Subtype.ext
      change (x : G) * y = y * x
      exact congrArg Subtype.val (congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    · rintro _ ⟨x, hx, rfl⟩
      simpa using congrArg Subtype.val (hB.2 x hx)
  have hAB' : A ≤ B.map C.subtype := fun a ha =>
    ⟨⟨a, hAC ha⟩, hAB (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hBA := hA _ hBe hAB'
  intro x hx
  have : (x : G) ∈ A := hBA ▸ ⟨x, hx, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr this

theorem list463_map_subtype {G : Type} [Group G] [Finite G] (C : Subgroup G) {L' : Subgroup C}
    (h : List463 L') : List463 (L'.map C.subtype) := by
  haveI : (solvableRadical L').Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  haveI : (solvableRadical (L'.map C.subtype)).Normal :=
    Subgroup.normal_sSup _ fun _ hN => hN.1
  let e : L' ≃* L'.map C.subtype := L'.equivMapOfInjective C.subtype C.subtype_injective
  have hrad : (solvableRadical L').map e.toMonoidHom = solvableRadical (L'.map C.subtype) :=
    CFSG.SignalizerFunctorTheorem.McBride.solvableRadical_map_mulEquiv e
  let q : (L'.map C.subtype) ⧸ solvableRadical (L'.map C.subtype) ≃* L' ⧸ solvableRadical L' :=
    (QuotientGroup.congr _ _ e hrad).symm
  unfold List463 at h ⊢
  rcases h with h | h | h | h | ⟨p, f, hp, h3, h1, h2, h⟩ | h
  · exact Or.inl (h.map fun g => q.trans g)
  · exact Or.inr (Or.inl (h.map fun g => q.trans g))
  · exact Or.inr (Or.inr (Or.inl (h.map fun g => q.trans g)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h.map fun g => q.trans g))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, f, hp, h3, h1, h2, Sec10.Sec10XProof.isoLThreePi_of_mulEquiv q h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.map fun g => q.trans g)))))

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
