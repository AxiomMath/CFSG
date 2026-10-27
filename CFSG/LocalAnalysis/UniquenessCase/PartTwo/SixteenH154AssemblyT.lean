module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyTA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UElem
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_component_isComponent_subgroupOf {A : Type} [Group A] {H K : Subgroup A}
    (h : CFSG.Open.IsComponentOf K H) : CFSG.IsComponent (K.subgroupOf H) := by
  rw [CFSG.isComponent_iff_open]
  exact ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib h.2.1.subgroupOf,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.2⟩

private theorem s16h_component_eq_or_commute {A : Type} [Group A] [Finite A]
    {H K L : Subgroup A} (hK : CFSG.Open.IsComponentOf K H)
    (hL : CFSG.Open.IsComponentOf L H) :
    K = L ∨ ∀ x ∈ K, ∀ y ∈ L, x * y = y * x := by
  rcases CFSG.LocalCores.distinct_components_commute (s16h_component_isComponent_subgroupOf hK)
    (s16h_component_isComponent_subgroupOf hL) with h | h
  · left
    have h' := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hK.1, inf_eq_left.mpr hL.1] at h'
  · right
    intro a ha b hb
    have ha' : (⟨a, hK.1 ha⟩ : ↥H) ∈ K.subgroupOf H := Subgroup.mem_subgroupOf.mpr ha
    have hb' : (⟨b, hL.1 hb⟩ : ↥H) ∈ L.subgroupOf H := Subgroup.mem_subgroupOf.mpr hb
    have hc := Subgroup.commutator_mem_commutator ha' hb'
    rw [h, Subgroup.mem_bot] at hc
    have hcomm : Commute (⟨a, hK.1 ha⟩ : ↥H) ⟨b, hL.1 hb⟩ :=
      commutatorElement_eq_one_iff_commute.mp hc
    exact congrArg Subtype.val hcomm.eq

private theorem s16h_isComponentOf_map_mulEquiv_apply {A B : Type} [Group A] [Group B]
    (e : A ≃* B) {L H : Subgroup A} (h : CFSG.Open.IsComponentOf L H) :
    CFSG.Open.IsComponentOf (L.map e.toMonoidHom) (H.map e.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, CFSG.Open.IsSubnormal.map e.toMonoidHom h.2.1,
    CFSG.Open.IsQuasisimple.of_mulEquiv (L.equivMapOfInjective e.toMonoidHom e.injective).symm
      h.2.2⟩

theorem s16h_hyp154_of_tensor (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hnot : ¬ Concl164 D V₀ V h.hyp151.isElemAbelian L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L < gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t (lBar V₀ V h.hyp151.isElemAbelian L))
    {K : Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian))}
    (hK : IsComponentOf K (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    {g : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (hg : g ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (hne : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hL : (lBar V₀ V h.hyp151.isElemAbelian L) = K ⊔ K.map (MulAut.conj g).toMonoidHom)
    (hT : (IsL3 ↥K 1 ∧
        NatTensor (lBar V₀ V h.hyp151.isElemAbelian L)
          (commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L)) ⊥ 3 1) ∨
      (UC22.IsL2 ↥K 2 ∧
        NatTensor (lBar V₀ V h.hyp151.isElemAbelian L)
          (commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L)) ⊥ 2 2) ∨
      (UC22.IsL2 ↥K 3 ∧
        NatTensor (lBar V₀ V h.hyp151.isElemAbelian L)
          (commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L)) ⊥ 2 3)) :
    Hyp154 D V₀ V L := by
  have hV := h.hyp151.isElemAbelian
  set Kb : Subgroup (MulAut (Vtil V₀ V hV)) := K.map (MulAut.conj g).toMonoidHom with hKbdef
  haveI : Finite (MulAut (Vtil V₀ V hV)) :=
    Finite.of_injective (fun e : MulAut (Vtil V₀ V hV) => (e : Vtil V₀ V hV → Vtil V₀ V hV))
      fun _ _ h => MulEquiv.ext (congrFun h)
  have h3K : 3 ∣ Nat.card ↥K := by
    rcases hT with ⟨h3, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩
    · exact s16h_three_dvd_of_lieFactor (K := ↥K) (Or.inl h3)
    · exact s16h_three_dvd_of_lieFactor (K := ↥K) (Or.inr (Or.inl h2))
    · exact s16h_three_dvd_of_lieFactor (K := ↥K) (Or.inr (Or.inr h2))
  have hMbar : (Mbar D.M V₀ V hV).map (MulAut.conj g).toMonoidHom = Mbar D.M V₀ V hV :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (H := Mbar D.M V₀ V hV) hg)
  have hKb : IsComponentOf Kb (Mbar D.M V₀ V hV) := by
    rw [hKbdef]
    exact hMbar ▸ s16h_isComponentOf_map_mulEquiv_apply (MulAut.conj g) hK
  have hKs : IsSimpleGroup ↥K := by
    rcases hT with ⟨h3, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h3
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h2
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h2
  haveI := hKs
  haveI hKbs : IsSimpleGroup ↥Kb := by
    rw [hKbdef]
    exact (K.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.isSimpleGroup
  have hcomm : ⁅K, Kb⁆ = ⊥ := by
    rcases s16h_component_eq_or_commute hK hKb with heq | hcomm
    · exact absurd heq hne
    · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcomm x hx y hy).symm
  have hNK : K ≤ Subgroup.normalizer (Kb : Set (MulAut (Vtil V₀ V hV))) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hNKb : Kb ≤ Subgroup.normalizer (K : Set (MulAut (Vtil V₀ V hV))) := by
    rw [Subgroup.commutator_comm] at hcomm
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hinf : K ⊓ Kb = ⊥ :=
    CFSG.ComponentClassification.AS76b.Lemma34.inf_eq_bot_of_isSimpleGroup hNK hNKb hne
  have h3Kb : 3 ∣ Nat.card ↥Kb := by
    rw [hKbdef, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h3K
  have hr : 2 ≤ CFSG.Open.pRank 3 (lBar V₀ V hV L) := by
    rw [hL]
    exact s16h_two_le_pRank_sup Nat.prime_three hcomm hinf h3K h3Kb
  have hgood : ∀ w ∈ V, w ∉ V₀ → ∀ P : Subgroup G, IsPGroup 3 P → ¬ IsCyclic ↥P →
      P ≤ F11.CElt D.M V₀ w → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
    intro w hwV hw0 P hPp hPc hPC
    rcases s16h_four_or_strong_of_tensor D S hσ h hs ht ht2 ht1 htr hW hK hg hne hL hT with
      h4 | hk
    · exact s16c34_uniqueMax_cent_of_cElt D S.h61 S.h127 h.hyp16
        (S.hSig.four_mem 3 Nat.prime_three (by norm_num) h4) hPp hPc hwV hw0 hPC
    · exact s16h_uniqueMax_cent_of_cElt_three D S.h61 S.h63 S.h127 hk h.hyp16 hPp hPc hwV hw0 hPC
  have hU : s16h_CondU D V₀ V L hV := s16h_condU_of_noncyclic D h Nat.prime_three hgood hr
  have hσ3 : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M := by
    obtain ⟨q, hq⟩ := S.hx.sig_nonempty
    exact ⟨q, hq, S.hSig.three_le q hq⟩
  exact s16h_hyp154_of_condU D S.h61 h hσ3 hU hs hδ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
