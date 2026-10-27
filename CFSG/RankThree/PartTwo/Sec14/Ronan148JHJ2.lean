module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJ
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_inf_centralizer_eq_three_of_j2
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    {J Yd : Subgroup G} {d : G} (hJ : J ∈ thetaComponentsIn Y)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G))) (hYdJ : Yd ≤ J)
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)))
    (hθ : ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y) (hdA : d ∈ A)
    (hdYd : d ∈ Yd) (hdc : d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) :
    letI := ker148_normal hY.2
    Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) →
    Nat.card ↥(img148 A Y A ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) = 3 ∧
      img148 A Y A ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊔
        img148 A Y A ⊓ img148 A Y J = img148 A Y A := by
  intro hJ2
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  obtain ⟨φ⟩ := hJ2
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hJs : IsSimpleGroup ↥(img148 A Y J) := MulEquiv.isSimpleGroup φ
  obtain ⟨-, hJZ⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  have hAJα : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hJZ' : img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hz : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hJZ, Subgroup.mem_bot] at hz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hz
  have hCD := sup_eq_of_forall_inner hAab hA3 hF3 hJZ' hAJα
    (fun a ha => exists_inner_of_j2 φ (hAJα ha) (hA3 a ha))
  set dα := alpha148 A Y d hdA with hdαdef
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hdα3 : dα ^ 3 = 1 := hA3 _ hdαA
  have hdJα : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ hdYd, rfl⟩
  have hdnc : ∃ y ∈ img148 A Y J, dα * y ≠ y * dα := by
    by_contra hcon
    push Not at hcon
    apply hdc
    refine HJRes148.mem_sectionCentralizer_of_le_centralizer hJM hdA fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcon x hx).symm
  have hdα1 : dα ≠ 1 := by
    intro h
    obtain ⟨y, -, hy⟩ := hdnc
    exact hy (by rw [h, one_mul, mul_one])
  obtain ⟨hYdeq, hYd6, hYdp, hYdZ, -⟩ :=
    img148_yd_facts_of_j2 hY.2 hdA hd3 hYd hJ hYdJ hAJ hA6 hθ φ hdYd hdα1 hdα3
  have hYdJα : img148 A Y Yd ≤ img148 A Y J := img148_mono hYdJ
  have hYdC : img148 A Y Yd ≤ Subgroup.centralizer {dα} := hYdeq ▸ inf_le_right
  have hAJYd : img148 A Y A ⊓ img148 A Y J ≤ img148 A Y Yd := by
    intro x hx
    rw [hYdeq]
    exact Subgroup.mem_inf.mpr ⟨hx.2,
      Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx.1 dα hdαA)⟩
  obtain ⟨j, hjAJ, hjd⟩ : ∃ j ∈ img148 A Y A ⊓ img148 A Y J, j ∉ Subgroup.zpowers dα := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx3, hxZ⟩ := Sec19.Item19Res4Proof.exists_noncentral_of_isTripleA6 hYd6
    have hx3' : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
    have hxJ : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y J := hYdJα x.2
    have hxd : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) * dα = dα * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYdC x.2)
    have hAx : img148 A Y A ≤ Subgroup.centralizer {(x : ↥(Y ⊔ A) ⧸ ker148 A Y)} := by
      rw [← hCD]
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp ha.2 x hxJ).symm
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hcon a ha)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Commute.zpow_left hxd.symm k).eq
    have hxA : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y A := by
      refine hF3 _ ?_ hx3'
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hAx ha)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcon _ ⟨hxA, hxJ⟩)
    apply hxZ
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgd : (g : ↥(Y ⊔ A) ⧸ ker148 A Y) * dα = dα * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYdC g.2)
    change (g : ↥(Y ⊔ A) ⧸ ker148 A Y) * x = x * g
    rw [← hk]
    exact (Commute.zpow_right hgd k).eq
  have hjA : j ∈ img148 A Y A := hjAJ.1
  have hj3 : j ^ 3 = 1 := hA3 j hjA
  have hdj : dα * j = j * dα := hAab dα hdαA j hjA
  have h9 : Nat.card ↥(Subgroup.zpowers dα ⊔ Subgroup.zpowers j) = 9 :=
    card_zpowers_sup_zpowers_eq_nine hdj hdα3 hdα1 hj3 hjd
  have hle9 : Nat.card ↥(img148 A Y A ⊓ img148 A Y J) ≤ 9 :=
    card_le_nine_of_le_tripleCover hYd6 hYdp hAJYd (fun a ha b hb => hAab a ha.1 b hb.1)
      (fun a ha => hA3 a ha.1)
  have hdjle : Subgroup.zpowers dα ⊔ Subgroup.zpowers j ≤ img148 A Y A ⊓ img148 A Y J :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hdαA, hdJα⟩) (Subgroup.zpowers_le.mpr hjAJ)
  have hAJeq : img148 A Y A ⊓ img148 A Y J = Subgroup.zpowers dα ⊔ Subgroup.zpowers j :=
    (Subgroup.eq_of_le_of_card_ge hdjle (by rw [h9]; exact hle9)).symm
  refine ⟨?_, hCD⟩
  have hCJ : (img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) ⊓
        (img148 A Y A ⊓ img148 A Y J) = ⊥ := by
    rw [eq_bot_iff, ← hJZ']
    exact fun x hx => ⟨hx.2.2, hx.1.2⟩
  have h1 := card_sup_eq_mul_of_commute
    (U := img148 A Y A ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (V := img148 A Y A ⊓ img148 A Y J) (fun u hu v hv => hAab u hu.1 v hv.1) hCJ
  rw [hCD, hAE.2, hAJeq, h9] at h1
  omega

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
