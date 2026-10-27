module

public import CFSG.LocalAnalysis.WeakClosure81.TimTI.DegenBasic
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.DegenLift
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.BenderRoot
public import CFSG.StronglyEmbedded.BenderCentre
public import CFSG.CGT.Timmesfeld75.BenderInputs3
public import CFSG.GH74.Bender.Suzuki
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsGrp
import CFSG.LocalAnalysis.WeakClosure81.TimTI.BenderGenAux1
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.Quot

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender (rootCenter)

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

namespace Hyp

theorem bender_gen
    (h : Hyp X S) (hdeg : ∀ d ∈ dSet S, ∀ e ∈ dSet S, orderOf (d * e) ≠ 4)
    (hdisc : CFSG.Timmesfeld.Connectivity.Disconnected
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S))
    {s : X} (hs : s ∈ S) (hs1 : s ≠ 1) {n : ℕ}
    (hcard : Nat.card (CFSG.Timmesfeld.rootGroup (dSet S) s) = 2 ^ n) :
    ∃ g : X, SevenK.IsL2OrSz ↥(CFSG.Timmesfeld.rootGroup (dSet S) s ⊔
      conjSubgroup (CFSG.Timmesfeld.rootGroup (dSet S) s) g) n := by
  classical
  have hsD : s ∈ dSet S := mem_dSet_of_mem hs hs1
  have hSleW : S ≤ CFSG.Timmesfeld.rootGroup (dSet S) s := h.le_rootGroup hdeg hs hs1
  have hn2 : 2 ≤ n := by
    have hcardS : Nat.card S ≤ 2 ^ n := by
      rw [← hcard]
      exact Nat.card_mono (Set.toFinite _) hSleW
    have h4 : 2 < 2 ^ n := lt_of_lt_of_le h.card hcardS
    have h1 : 1 < n := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h4)
    omega
  have hsetup : CFSG.Timmesfeld.Bridge.Asc72.Setup (X ⧸ Subgroup.center X)
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S) := h.setup_quot hdeg
  have hKq : CFSG.BenderSuzuki.IsBenderGroup (X ⧸ Subgroup.center X) :=
    CFSG.Timmesfeld.Bridge.OddTransp.oddTranspBender
      (X ⧸ Subgroup.center X) (QuotientGroup.mk' (Subgroup.center X) '' dSet S) hsetup
      h.eq_bot_of_normal_isSolvable_quot h.meetsSq_quot hdisc
  have hpsD : QuotientGroup.mk' (Subgroup.center X) s ∈
      QuotientGroup.mk' (Subgroup.center X) '' dSet S := ⟨s, hsD, rfl⟩
  have hWqcard : Nat.card (CFSG.Timmesfeld.rootGroup
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
      (QuotientGroup.mk' (Subgroup.center X) s)) = 2 ^ n := by
    rw [← h.map_rootGroup hsD]
    exact (h.card_map_rootGroup hsD).trans hcard
  have hWqElem : IsElemAbelian 2 (CFSG.Timmesfeld.rootGroup
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
      (QuotientGroup.mk' (Subgroup.center X) s)) :=
    h.map_rootGroup hsD ▸ CFSG.Open.IsElemAbelian.map (h.isElemAbelian_rootGroup hsD)
      (QuotientGroup.mk' (Subgroup.center X))
  obtain ⟨T, hpsT, hrootT⟩ := rootGroup_eq_sylowCenter_of_isBenderGroup hsetup hKq hpsD
  have hTeq : rootCenter (T : Subgroup (X ⧸ Subgroup.center X)) =
      CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
        (QuotientGroup.mk' (Subgroup.center X) s) := hrootT.symm
  have hTcard : Nat.card (rootCenter (T : Subgroup (X ⧸ Subgroup.center X))) = 2 ^ n := by
    rw [hTeq]
    exact hWqcard
  have hWq_ne_bot : CFSG.Timmesfeld.rootGroup
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
      (QuotientGroup.mk' (Subgroup.center X) s) ≠ ⊥ := by
    intro hbot
    have h1 : (2 : ℕ) ^ n = 1 := by rw [← hWqcard, hbot, Subgroup.card_bot]
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hWq_not_normal : ¬ (CFSG.Timmesfeld.rootGroup
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
      (QuotientGroup.mk' (Subgroup.center X) s)).Normal := by
    intro hN
    have hsol : Group.IsSolvable ↥(CFSG.Timmesfeld.rootGroup
        (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
        (QuotientGroup.mk' (Subgroup.center X) s)) := by
      have hp : IsPGroup 2 ↥(CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s)) :=
        CFSG.Timmesfeld.isPGroup_rootGroup h.isRootInvolutionSet_image hpsD
      haveI : Group.IsNilpotent ↥(CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s)) := IsPGroup.isNilpotent hp
      infer_instance
    exact hWq_ne_bot (h.eq_bot_of_normal_isSolvable_quot _ hN hsol)
  have h_exists_conj : ∃ g : X ⧸ Subgroup.center X,
      conjSubgroup (CFSG.Timmesfeld.rootGroup
        (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
        (QuotientGroup.mk' (Subgroup.center X) s)) g ≠
      CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
        (QuotientGroup.mk' (Subgroup.center X) s) := by
    by_contra hcon
    push Not at hcon
    apply hWq_not_normal
    apply Subgroup.normalizer_eq_top_iff.mp
    rw [Subgroup.eq_top_iff']
    intro g
    exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp (hcon g)
  have hXq : ∃ g : X ⧸ Subgroup.center X,
      SevenK.IsL2OrSz ↥(CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s) ⊔
        conjSubgroup (CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s)) g) n := by
    rcases hKq with ⟨m, hm, e⟩ | ⟨a, ha, e⟩ | ⟨m, hm, e⟩
    · have hcardm : Nat.card (rootCenter (T : Subgroup (X ⧸ Subgroup.center X))) = 2 ^ m := by
        have h := CFSG.StronglyEmbedded.BenderCentre.card_sylowCenter_psl2 (K := X ⧸
          Subgroup.center X) hm e T
        rw [show CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
            (T : Subgroup (X ⧸ Subgroup.center X)) =
            rootCenter (T : Subgroup (X ⧸ Subgroup.center X)) from rfl] at h
        exact h
      have hnm : n = m :=
        Nat.pow_right_injective (by norm_num : 2 ≤ 2) (hTcard.symm.trans hcardm)
      have hL2 : SevenK.IsL2OrSz (X ⧸ Subgroup.center X) m :=
        Or.inl (CFSG.CGT.Timmesfeld75.statedClassicalModel_psl2_of_mulEquiv hm e)
      obtain ⟨g, hg⟩ := h_exists_conj
      have hcard_m : Nat.card (CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s)) = 2 ^ m := by
        rw [hWqcard, hnm]
      have hsup := CFSG.LocalAnalysis.WeakClosure81.sup_conj_eq_top_of_card_eq_two_pow
        (S := X ⧸ Subgroup.center X) (n := m) (by omega) hL2 hWqElem hcard_m hg
      refine ⟨g, ?_⟩
      have htop : SevenK.IsL2OrSz ↥(⊤ : Subgroup (X ⧸ Subgroup.center X)) m :=
        isL2OrSz_of_mulEquiv hL2 (Subgroup.topEquiv.symm)
      have hres : SevenK.IsL2OrSz ↥(CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s) ⊔
          conjSubgroup (CFSG.Timmesfeld.rootGroup
            (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
            (QuotientGroup.mk' (Subgroup.center X) s)) g) m :=
        isL2OrSz_of_mulEquiv htop (MulEquiv.subgroupCongr hsup).symm
      rwa [hnm]
    · have hcardm : Nat.card (rootCenter (T : Subgroup (X ⧸ Subgroup.center X))) =
          2 ^ (2 * a + 1) := by
        have h := CFSG.StronglyEmbedded.BenderCentre.card_sylowCenter_sz (K := X ⧸
          Subgroup.center X) ha e T
        rw [show CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
            (T : Subgroup (X ⧸ Subgroup.center X)) =
            rootCenter (T : Subgroup (X ⧸ Subgroup.center X)) from rfl] at h
        exact h
      have hnm : n = 2 * a + 1 :=
        Nat.pow_right_injective (by norm_num : 2 ≤ 2) (hTcard.symm.trans hcardm)
      have e' : X ⧸ Subgroup.center X ≃* CFSG.Open.Sz a :=
        e.trans (MulEquiv.subgroupCongr (CFSG.GH74.Bender.szModel_eq_sz a))
      have hL2 : SevenK.IsL2OrSz (X ⧸ Subgroup.center X) (2 * a + 1) :=
        Or.inr (CFSG.GH74.Bender.suzukiModel_of_mulEquiv_sz ha e')
      obtain ⟨g, hg⟩ := h_exists_conj
      have hcard_m : Nat.card (CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s)) = 2 ^ (2 * a + 1) := by
        rw [hWqcard, hnm]
      have hsup := CFSG.LocalAnalysis.WeakClosure81.sup_conj_eq_top_of_card_eq_two_pow
        (S := X ⧸ Subgroup.center X) (n := 2 * a + 1) (by omega) hL2 hWqElem hcard_m hg
      refine ⟨g, ?_⟩
      have htop : SevenK.IsL2OrSz ↥(⊤ : Subgroup (X ⧸ Subgroup.center X)) (2 * a + 1) :=
        isL2OrSz_of_mulEquiv hL2 (Subgroup.topEquiv.symm)
      have hres : SevenK.IsL2OrSz ↥(CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s) ⊔
          conjSubgroup (CFSG.Timmesfeld.rootGroup
            (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
            (QuotientGroup.mk' (Subgroup.center X) s)) g) (2 * a + 1) :=
        isL2OrSz_of_mulEquiv htop (MulEquiv.subgroupCongr hsup).symm
      rwa [hnm]
    · have hcardm : Nat.card (rootCenter (T : Subgroup (X ⧸ Subgroup.center X))) = 2 ^ m := by
        have h := CFSG.StronglyEmbedded.BenderCentre.card_sylowCenter_psu3 (K := X ⧸
          Subgroup.center X) hm e T
        rw [show CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
            (T : Subgroup (X ⧸ Subgroup.center X)) =
            rootCenter (T : Subgroup (X ⧸ Subgroup.center X)) from rfl] at h
        exact h
      have hnm : n = m :=
        Nat.pow_right_injective (by norm_num : 2 ≤ 2) (hTcard.symm.trans hcardm)
      have hKq : CFSG.BenderSuzuki.IsBenderGroup (X ⧸ Subgroup.center X) :=
        CFSG.BenderSuzuki.IsBenderGroup.isPSU3 m hm e
      obtain ⟨g, hg⟩ := h_exists_conj
      have hWgElem : IsElemAbelian 2 (conjSubgroup (CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s)) g) :=
        CFSG.Open.IsElemAbelian.map hWqElem (MulAut.conj g⁻¹).toMonoidHom
      obtain ⟨T', hWgZ⟩ :=
        CFSG.StronglyEmbedded.BenderCentre.exists_le_sylowCenter hKq hWgElem
      have hcardg : Nat.card (conjSubgroup (CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s)) g) = 2 ^ m := by
        change Nat.card ((CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s)).map (MulAut.conj g⁻¹).toMonoidHom) = 2 ^ m
        rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hWqcard, hnm]
      have hcardT' : Nat.card (rootCenter (T' : Subgroup (X ⧸ Subgroup.center X))) = 2 ^ m := by
        have h := CFSG.StronglyEmbedded.BenderCentre.card_sylowCenter_psu3 (K := X ⧸
          Subgroup.center X) hm e T'
        rw [show CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
            (T' : Subgroup (X ⧸ Subgroup.center X)) =
            rootCenter (T' : Subgroup (X ⧸ Subgroup.center X)) from rfl] at h
        exact h
      have hWg_eq : conjSubgroup (CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s)) g =
          rootCenter (T' : Subgroup (X ⧸ Subgroup.center X)) :=
        Subgroup.eq_of_le_of_card_ge hWgZ (le_of_eq (by rw [hcardT', hcardg]))
      have hTT'_ne : T ≠ T' := by
        intro hTT'
        apply hg
        rw [hWg_eq, ← hTT', hTeq]
      obtain ⟨ψ⟩ := timti_isPSL2_sup_rootCenter_of_ne hm e hTT'_ne
      have hsup_eq : CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s) ⊔
          conjSubgroup (CFSG.Timmesfeld.rootGroup
            (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
            (QuotientGroup.mk' (Subgroup.center X) s)) g =
          rootCenter (T : Subgroup (X ⧸ Subgroup.center X)) ⊔
            rootCenter (T' : Subgroup (X ⧸ Subgroup.center X)) := by
        rw [hTeq, hWg_eq]
      refine ⟨g, ?_⟩
      have hPSL : SevenK.IsL2OrSz ↥(rootCenter (T : Subgroup (X ⧸ Subgroup.center X)) ⊔
          rootCenter (T' : Subgroup (X ⧸ Subgroup.center X))) m :=
        Or.inl (CFSG.CGT.Timmesfeld75.statedClassicalModel_psl2_of_mulEquiv hm ψ)
      have hres : SevenK.IsL2OrSz ↥(CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s) ⊔
          conjSubgroup (CFSG.Timmesfeld.rootGroup
            (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
            (QuotientGroup.mk' (Subgroup.center X) s)) g) m :=
        isL2OrSz_of_mulEquiv hPSL (MulEquiv.subgroupCongr hsup_eq).symm
      rwa [hnm]
  obtain ⟨gq, hgq⟩ := hXq
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) gq
  refine ⟨g, ?_⟩
  have hmap_eq : (CFSG.Timmesfeld.rootGroup (dSet S) s ⊔
      conjSubgroup (CFSG.Timmesfeld.rootGroup (dSet S) s) g).map
        (QuotientGroup.mk' (Subgroup.center X)) =
      CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s) ⊔
        conjSubgroup (CFSG.Timmesfeld.rootGroup
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s)) gq := by
    rw [Subgroup.map_sup, map_conjSubgroup_mk, h.map_rootGroup hsD, hg]
  have hmapL : SevenK.IsL2OrSz ↥((CFSG.Timmesfeld.rootGroup (dSet S) s ⊔
      conjSubgroup (CFSG.Timmesfeld.rootGroup (dSet S) s) g).map
        (QuotientGroup.mk' (Subgroup.center X))) n :=
    isL2OrSz_of_mulEquiv hgq (MulEquiv.subgroupCongr hmap_eq).symm
  exact h.isL2OrSz_of_map
    (CFSG.Timmesfeld.isPGroup_rootGroup h.root hsD)
    (show IsPGroup 2 (conjSubgroup (CFSG.Timmesfeld.rootGroup (dSet S) s) g) from
      IsPGroup.map (CFSG.Timmesfeld.isPGroup_rootGroup h.root hsD)
        (MulAut.conj g⁻¹).toMonoidHom)
    hmapL

end Hyp

end CFSG.LocalAnalysis.WeakClosure81.TimTI
