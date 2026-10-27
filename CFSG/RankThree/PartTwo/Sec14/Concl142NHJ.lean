module

public import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
public import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec12.Item128Bar
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Inspect142At (A : Subgroup G) (c : G) : Prop :=
  ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3),
    ∀ B : Subgroup G, IsHyperplane A B → c ∈ B →
      ⁅Q ⊓ Subgroup.centralizer (B : Set G), A⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))

theorem mem_scriptQ_of_inspect142At {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hLB : ∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥) (hins : Inspect142At A c) :
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3), Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({c} : Set G)) := by
  intro Q hQ
  have hD := h.toSec13Data
  have hQc := le_centralizer_of_mem_invariantPiSubgroups hD.mem_A hD.orderOf_eq hQ.prop
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.prop.2.1
  refine ⟨⟨⟨le_top, hQ.prop.2.1, hQ.prop.2.2⟩, fun B hB => ?_⟩, hQc⟩
  have hfac := inf_centralizer_le_commutator_sup h.isE27' h.maximal_isElemAbelian hQ3
    hQ.prop.2.2 hB.1
  rw [qBound, hLB B hB, sup_bot_eq]
  by_cases hcB : c ∈ B
  · exact hfac.trans (sup_le_sup_right (hins Q hQ B hB hcB) _)
  · have hAle := le_sup_zpowers_of_not_mem h.isE27' hB hD.mem_A hcB
    have hCA : Q ⊓ Subgroup.centralizer (B : Set G) ≤ Q ⊓ Subgroup.centralizer (A : Set G) :=
      fun x hx => ⟨hx.1, mem_centralizer_of_le_sup hAle hx.2 (hQc hx.1)⟩
    exact hCA.trans ((inf_centralizer_le_xA h.maximal_isElemAbelian hQ3).trans le_sup_right)

@[expose] def Step142LThreePi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
      (∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥) → Inspect142At A c

@[expose] def Step142A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      (∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥) → Inspect142At A c

@[expose] def Step142M22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) →
      (∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥) → Inspect142At A c

@[expose] def Step142M12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) →
      (∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥) → Inspect142At A c

theorem concl142_of_inspect (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (hL3 : Step142LThreePi) (hA7 : Step142A7) (hM22 : Step142M22) (hM12 : Step142M12)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hLB : ∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥)
    (hnoHJ : ∀ (e : G) (Le : Subgroup G), Sec14Std G A e Le →
      ¬ Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Concl142 A (lB A) := by
  intro e he Q hQ
  have hD := h.toSec13Data
  have heA : e ∈ A := (zpowers_mem_omegaA_iff.mp he).1
  have hAe : A ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx heA)
  obtain ⟨Le, hLe⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
    hD.card_eq he
  have hS : Sec14Std G A e Le :=
    { h with zpowers_mem_omegaA := he, mem_lA := Sec12.mem_lA_of_mem_lA422 hAe hLe }
  have hins : Inspect142At A e := by
    rcases (h.chosen136.2 e he Le hS.toSec13Data.mem_lA).1 with hJ | hL | hA | hM | hM'
    · exact absurd hJ (hnoHJ e Le hS)
    · exact hL3 G A e Le hS hL hLB
    · exact hA7 G A e Le hS hA hLB
    · exact hM22 G A e Le hS hM hLB
    · exact hM12 G A e Le hS hM' hLB
  exact mem_scriptQ_of_inspect142At hS hLB hins Q hQ

section Certificates


theorem concl142_of_not_allPointsHJ (h134 : Item134) (h48 : Sec4.Item4_8)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (hL3 : Step142LThreePi) (hA7 : Step142A7)
    (hM22 : Step142M22) (hM12 : Step142M12) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hNHJ : ¬ AllPointsHJ A) : Concl142 A (lB A) :=
  concl142_of_inspect h422 h45 hL3 hA7 hM22 hM12 h
    (fun _ hB => lB_eq_bot_of_not_allPointsHJ' h134 h48 h hNHJ hB)
    (fun _ _ hS hJ => hNHJ (allPointsHJ_of_j2 h134 h48 hS hJ))

end Certificates

end CFSG.RankThree.PartTwo.Sec14
