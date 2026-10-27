module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Orbit
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Bridge
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Bender
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.TheoremTwo
import CFSG.OddTranspositions.PartThree.EightEight.ThirdKind
import CFSG.OddTranspositions.PartFour.SeventeenTwo

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem eq_alpha_of_mem_kOrbit {hC : HypothesisC D} {β : Set G}
    (hconst : ∀ β' ∈ Dalpha D hC.alpha, kOrbit D β' hC.alpha = kOrbit D β hC.alpha)
    {δ : Set G} (hδ : δ ∈ kOrbit D β hC.alpha) : δ = hC.alpha := by
  obtain ⟨k, hk, rfl⟩ := hδ
  have hδclass : cimg k hC.alpha ∈ blockClass hC.alpha :=
    cimg_mem_blockClass_iff.mpr (mem_blockClass_self hC.alpha)
  have hsub : Dalpha D hC.alpha ⊆ Dalpha D (cimg k hC.alpha) := by
    intro β' hβ'
    have hmem : cimg k hC.alpha ∈ kOrbit D β' hC.alpha := by
      rw [hconst β' hβ']
      exact ⟨k, hk, rfl⟩
    obtain ⟨k', hk', hkc⟩ := hmem
    obtain ⟨k'H, hk'H, rfl⟩ := Subgroup.mem_map.mp hk'
    have hkcg : cimg (k'H : G) hC.alpha = cimg k hC.alpha := hkc
    have hδclass' : cimg (k'H : G) hC.alpha ∈ blockClass hC.alpha := by rw [hkcg]; exact hδclass
    have hδDβ' : cimg (k'H : G) hC.alpha ∈ Dalpha D β' := by
      refine mem_Dalpha_iff.mpr ⟨?_, ?_, ?_, ?_⟩
      · exact mem_blockClass_of_mem_blockClass hβ'.1 hδclass'
      · exact subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hδclass'
      · intro heq
        have hkc' : cimg (k'H : G) hC.alpha = β' := heq
        have hfix : cimg (k'H : G)⁻¹ β' = β' :=
          cimg_eq_self_of_mem_normalizer
            (Halpha_le_normalizer_block D β' (Subgroup.inv_mem _ k'H.2))
        have hαβ : hC.alpha = β' := by
          calc hC.alpha = cimg (k'H : G)⁻¹ (cimg (k'H : G) hC.alpha) :=
                (cimg_inv_cimg (k'H : G) hC.alpha).symm
            _ = cimg (k'H : G)⁻¹ β' := by rw [hkc']
            _ = β' := hfix
        exact hβ'.2.2.1 hαβ.symm
      · intro a ha b hb
        obtain ⟨a₀, ha₀, rfl⟩ := hb
        have haa₀ : Commute a a₀ :=
          (mem_Dalpha_iff.mp (mem_Dalpha_symm hβ' hC.isBlock_alpha.subset)).2.2.2 a ha a₀ ha₀
        have hk'a : Commute a (k'H : G) :=
          (commute_iff_eq a (k'H : G)).mpr
            (Subgroup.mem_centralizer_iff.mp
              ((Halpha_le_centralizer D β') k'H.2) a ha)
        exact (hk'a.mul_right haa₀).mul_right hk'a.inv_right
    have hsymm := mem_Dalpha_symm hδDβ' hβ'.2.1
    rwa [hkcg] at hsymm
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hδclass
  have hncard : (Dalpha D (cimg k hC.alpha)).ncard = (Dalpha D hC.alpha).ncard := by
    rw [hg]
    exact ncard_Dalpha_conj hC.setup.normal g hC.alpha
  have heqD : Dalpha D (cimg k hC.alpha) = Dalpha D hC.alpha :=
    (Set.eq_of_subset_of_ncard_le hsub (le_of_eq hncard)
      (Set.toFinite (Dalpha D (cimg k hC.alpha)))).symm
  have hδW : cimg k hC.alpha ∈ Walpha D hC.alpha :=
    mem_Walpha_iff.mpr ⟨hδclass, heqD⟩
  simpa [Walpha_alpha_eq_singleton hC] using hδW


namespace MainHyp

variable {hC : HypothesisC D}

private theorem kOrbit_eq_of_reach (h86 : Lemma8_6) (h87 : Theorem8_7) (h : MainHyp hC)
    (hIH : Theorem11_3Below (Nat.card G)) (hconn : ¬ Disconnected (imageClass hC)) :
    ∀ x y : G, Reach (DalphaStar D hC.alpha) x y →
      ∀ {A B : Set G}, A ∈ Dalpha D hC.alpha → B ∈ Dalpha D hC.alpha →
      x ∈ A → y ∈ B → kOrbit D B hC.alpha = kOrbit D A hC.alpha := by
  intro x y hxy
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro A B hA hB hx hy
    have hAB : A = B := eq_of_mem_of_mem_blockClass hC.isBlock_alpha hA.1 hB.1 ⟨y, hx, hy⟩
    rw [hAB]
  | head hstep h' ih =>
    intro A B hA hB hx hy
    obtain ⟨C, hCmem, hcC⟩ := mem_DalphaStar_iff.mp hstep.2.1
    by_cases hAC : A = C
    · simpa [hAC] using ih hCmem hB hcC hy
    · have hCA : C ∈ Dalpha D A :=
        mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha
          hA.1 hCmem.1 hAC hx hcC hstep.2.2
      exact (ih hCmem hB hcC hy).trans
        (kOrbit_eq h86 h87 h hIH hconn hA hCmem hCA)

private theorem kOrbit_const_of_reach (h86 : Lemma8_6) (h87 : Theorem8_7) (h : MainHyp hC)
    (hIH : Theorem11_3Below (Nat.card G)) (hconn : ¬ Disconnected (imageClass hC))
    (hreach : ∀ x ∈ DalphaStar D hC.alpha, ∀ y ∈ DalphaStar D hC.alpha,
      Reach (DalphaStar D hC.alpha) x y) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    ∀ β' ∈ Dalpha D hC.alpha, kOrbit D β' hC.alpha = kOrbit D β hC.alpha := by
  intro β' hβ'
  obtain ⟨u, hu⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ'.1
  obtain ⟨w, hw⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
  exact (kOrbit_eq_of_reach h86 h87 h hIH hconn u w
    (hreach u (subset_DalphaStar hβ' hu) w (subset_DalphaStar hβ hw))
    hβ' hβ hu hw).symm

theorem kOrbit_eq_singleton (h86 : Lemma8_6) (h87 : Theorem8_7) (h : MainHyp hC)
    (hIH : Theorem11_3Below (Nat.card G)) (hcon : ¬ Disconnected (DstarH hC)) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) : kOrbit D β hC.alpha = {hC.alpha} := by
  classical
  have hconn : ¬ Disconnected (imageClass hC) := by
    rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩
    exact hab (CFSG.Timmesfeld.Bridge.OddLocal.reach_map _
      (CFSG.OddTranspositions.reach_of_not_disconnected hcon ha hb))
  have hreach : ∀ x ∈ DalphaStar D hC.alpha, ∀ y ∈ DalphaStar D hC.alpha,
      Reach (DalphaStar D hC.alpha) x y := by
    intro x hx y hy
    have hxH : (⟨x, Subgroup.subset_closure hx⟩ : Halpha D hC.alpha) ∈ DstarH hC := hx
    have hyH : (⟨y, Subgroup.subset_closure hy⟩ : Halpha D hC.alpha) ∈ DstarH hC := hy
    exact (CFSG.OddTranspositions.PartThree.EightEight.reach_DstarH_iff hC).mp
      (reach_of_not_disconnected hcon hxH hyH)
  have hconst := kOrbit_const_of_reach h86 h87 h hIH hconn hreach hβ
  refine Set.Subset.antisymm ?_ ?_
  · intro δ hδ
    simpa using eq_alpha_of_mem_kOrbit hconst hδ
  · intro δ hδ
    rw [Set.mem_singleton_iff] at hδ
    subst δ
    exact ⟨1, Subgroup.one_mem _, cimg_one _⟩

theorem disconnected_DstarH (h86 : Lemma8_6) (h87 : Theorem8_7) (h : MainHyp hC)
    (hIH : Theorem11_3Below (Nat.card G)) : Disconnected (DstarH hC) := by
  classical
  by_contra hcon
  obtain ⟨β, hβ⟩ := exists_mem_Dalpha hC
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβ.1
  let hC' : HypothesisC D := hC.conj g
  have hα' : hC'.alpha = β := (HypothesisC.conj_alpha hC g).trans hg.symm
  have h' : MainHyp hC' := h.conj g
  have hβ' : hC'.alpha ∈ Dalpha D hC.alpha := by
    rw [hα']
    exact hβ
  have hη : hC.alpha ∈ Dalpha D hC'.alpha := by
    rw [hα']
    exact mem_Dalpha_symm hβ hC.isBlock_alpha.subset
  obtain ⟨k, hk, -, hkv⟩ := exists_conj_not_commute h' hη hC.d_mem_alpha
  have hko := kOrbit_eq_singleton h86 h87 h hIH hcon hβ'
  have hkblock : (k : G) ∈ kBlock D hC'.alpha := Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
  have hmem : cimg (k : G) hC.alpha ∈ kOrbit D hC'.alpha hC.alpha :=
    ⟨(k : G), hkblock, rfl⟩
  rw [hko] at hmem
  have heq : cimg (k : G) hC.alpha = hC.alpha := Set.mem_singleton_iff.mp hmem
  exact hkv (heq ▸ ⟨hC.d, hC.d_mem_alpha, rfl⟩)

theorem isBenderGroup (h86 : Lemma8_6) (h87 : Theorem8_7) (h88 : Theorem8_8Quot)
    (h : MainHyp hC) (hIH : Theorem11_3Below (Nat.card G)) :
    CFSG.BenderSuzuki.IsBenderGroup
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
  isBenderGroup_quotient_of_disconnected h88 hC h.rad h.not_three h.not_wreath h.not_isSolvable
    (disconnected_imageClass_of_disconnected_DstarH hC h.not_isSolvable
      (h.disconnected_DstarH h86 h87 hIH))

end MainHyp

end CFSG.OddTranspositions.PartThree.ElevenThree
