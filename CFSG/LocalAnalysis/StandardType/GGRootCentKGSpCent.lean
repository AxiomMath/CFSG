module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSp
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmBasic
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpHolds
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.Core

public section

namespace CFSG.StandardType.KGSp

open Subgroup CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic
open CFSG.LieType.Universal.Symplectic.SpExtras (elt)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped commutatorElement

private theorem card_eq_two_or_four_le (F : Type) [Field F] [Finite F] [CharP F 2] :
    Nat.card F = 2 ∨ 4 ≤ Nat.card F := by
  have := Fintype.ofFinite F
  obtain ⟨k, -, hk⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hk]
  rcases Nat.lt_or_ge (k : ℕ) 2 with h | h
  · left
    have hk1 : (k : ℕ) = 1 := by have := k.pos; omega
    rw [hk1, pow_one]
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k : ℕ) := Nat.pow_le_pow_right (by norm_num) h

theorem pCoreOf_centralizer_siegDiag {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hm : 3 ≤ m) (i : Fin (m + 1)) :
    pCoreOf 2 (Subgroup.centralizer ({siegDiag F i 1} : Set (StatedSp (m + 1) F))) =
      transvRadical F i := by
  rw [centralizer_siegDiag_eq_sup]
  refine ggRCST_pCoreOf_eq rfl isPGroup_transvRadical complSp_le_normalizer_transvRadical ?_
  intro N hN hN2 hMN
  set N' : Subgroup ↥(complSp F i) := N.subgroupOf (complSp F i) with hN'def
  have hN' : N'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hMN
  have hN'2 : IsPGroup 2 N' :=
    hN2.comap_of_injective (complSp F i).subtype (complSp F i).subtype_injective
  have hbot : N' = ⊥ := by
    rcases card_eq_two_or_four_le F with h2 | h
    · exact eq_bot_of_normal_of_isPGroup_of_mulEquiv_two h2 hm
        (complSpEquiv (K := F) i).symm N' hN' hN'2
    · haveI := hN'
      exact eq_bot_of_normal_of_isPGroup_complSp h (le_trans (by norm_num) hm) N' hN'2
  exact RCSTOm.eq_bot_of_subgroupOf_eq_bot hN hbot

theorem ggRCSOmSummand_shortBlock {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F) :
    RCSTOm.GGRCSOmSummand (shortBlock F (one_ne_two_fin (n := n))).range := by
  have h12 := one_ne_two_fin (n := n)
  set S := (shortBlock F h12).range with hS
  have eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (MonoidHom.ofInjective (shortBlock_injective h12)).symm
  rcases hK with hK | hK
  · obtain ⟨e3⟩ := RCSPSL.nonempty_sl2_equiv_perm (F := F) hK
    exact RCSTOm.ggRCSOmSummand_of_perm (eS.trans e3)
  · have hq : CFSG.IsQuasisimple S :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eS.symm
        (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl
          (Or.inr hK))
    have hZ : Subgroup.center S = ⊥ := by
      have e : S ≃* StatedSp 1 F := eS.trans (longBlockEquivOne F)
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e.symm,
        center_statedSp_eq_bot, Subgroup.map_bot]
    exact RCSTOm.ggRCSOmSummand_of_isQuasisimple hq hZ

theorem ggRCSOmSummand_spCompl12 {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F) :
    RCSTOm.GGRCSOmSummand (spCompl12 F m) := by
  set T := spCompl12 F m with hT
  have eT : T ≃* StatedSp (m + 1) F := (spCompl12Equiv F m).symm
  have hZ : Subgroup.center T = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eT.symm,
      center_statedSp_eq_bot, Subgroup.map_bot]
  rcases hK with hK | hK
  · rcases Nat.lt_or_ge m 2 with hm2 | hm2
    ·
      interval_cases m
      have hO2 : ∀ M : Subgroup (⁅spCompl12 F 1, spCompl12 F 1⁆ :
          Subgroup (StatedSp (1 + 3) F)), M.Normal → IsPGroup 2 M → M = ⊥ := by
        intro M hM hM2
        have : IsSimpleGroup (⁅spCompl12 F 1, spCompl12 F 1⁆ :
            Subgroup (StatedSp (1 + 3) F)) :=
          isSimpleGroup_commutator_spCompl12_one hK
        have hy : orderOf (⟨nsElt (K := F) 0,
            nsTorusSp_le_commutator_spCompl12 (nsElt_mem_nsTorusSp 0)⟩ :
            (⁅spCompl12 F 1, spCompl12 F 1⁆ : Subgroup (StatedSp (1 + 3) F))) = 3 := by
          rw [Subgroup.orderOf_mk, orderOf_nsElt]
        exact eq_bot_of_normal_of_isPGroup_of_orderOf_three hy M hM hM2
      refine ⟨fun x hx hc => RCSTOm.eq_one_of_center_eq_bot hZ hx hc, ?_⟩
      intro N hNT hN2 hTN
      set NT : Subgroup (StatedSp (1 + 3) F) := ⁅N, T⁆ with hNTdef
      have hcomm_le_N : NT ≤ N := by
        rw [hNTdef]
        refine (Subgroup.commutator_le).mpr ?_
        intro n hn t ht
        have hconj : t * n⁻¹ * t⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.mp (hTN ht) n⁻¹).mp (N.inv_mem hn)
        rw [commutatorElement_def]
        simpa only [mul_assoc] using N.mul_mem hn hconj
      have hcomm_le_T' : NT ≤ ⁅T, T⁆ := by
        rw [hNTdef]
        exact Subgroup.commutator_mono hNT le_rfl
      have hcomm2 : IsPGroup 2 NT := hN2.to_le hcomm_le_N
      have hcommN : (NT.subgroupOf T).Normal := by
        have h := CFSG.commutator_normal_in_sup N T
        rw [sup_eq_right.mpr hNT] at h
        simpa [hNTdef] using h
      have hcomm_le_T : NT ≤ T := hcomm_le_T'.trans (Subgroup.commutator_le_self T)
      have hTnorm : T ≤ Subgroup.normalizer (NT : Set (StatedSp (1 + 3) F)) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hcomm_le_T).mp hcommN
      have hM : (NT.subgroupOf ⁅T, T⁆).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hcomm_le_T').mpr
          ((Subgroup.commutator_le_self T).trans hTnorm)
      have hM2 : IsPGroup 2 (NT.subgroupOf ⁅T, T⁆) :=
        hcomm2.comap_of_injective (⁅T, T⁆).subtype (⁅T, T⁆).subtype_injective
      have hMbot : NT.subgroupOf ⁅T, T⁆ = ⊥ := hO2 _ hM hM2
      have hcomm_bot : NT = ⊥ :=
        RCSTOm.eq_bot_of_subgroupOf_eq_bot hcomm_le_T' hMbot
      have hcent : N ≤ Subgroup.centralizer (T : Set (StatedSp (1 + 3) F)) := by
        rw [hNTdef] at hcomm_bot
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm_bot
      have hNcenter : N.subgroupOf T ≤ Subgroup.center T := by
        intro n hn
        rw [Subgroup.mem_center_iff]
        intro g
        have hnN : (n : StatedSp (1 + 3) F) ∈ N := Subgroup.mem_subgroupOf.mp hn
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent hnN)
          (g : StatedSp (1 + 3) F) g.2)
      have hNsub : N.subgroupOf T = ⊥ := le_bot_iff.mp (hNcenter.trans (le_of_eq hZ))
      exact RCSTOm.eq_bot_of_subgroupOf_eq_bot hNT hNsub
    · have hq : CFSG.IsQuasisimple T :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (spCompl12Equiv F m)
          (CFSG.LieType.Universal.Symplectic.isQuasisimple (m + 1) F (by omega)
            (Or.inr (Or.inr ⟨hK, by omega⟩)))
      exact RCSTOm.ggRCSOmSummand_of_isQuasisimple hq hZ
  · have hq : CFSG.IsQuasisimple T :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (spCompl12Equiv F m)
        (CFSG.LieType.Universal.Symplectic.isQuasisimple (m + 1) F (by omega)
          (Or.inl (Or.inr hK)))
    exact RCSTOm.ggRCSOmSummand_of_isQuasisimple hq hZ

theorem pCoreOf_centralizer_twoCentralElt {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 1 ≤ m) :
    pCoreOf 2 (Subgroup.centralizer
      ({twoCentralElt (m + 3) 1 2 (0 : F) 1} : Set (StatedSp (m + 3) F))) =
      wRadical F (1 : Fin (m + 3)) 2 := by
  have hcard := card_eq_two_or_four_le F
  obtain ⟨hC, hSQ, hTQ, hST⟩ := RCSTSp.centralizer_a2_facts (F := F) (n := m)
  have hX : Subgroup.centralizer ({twoCentralElt (m + 3) 1 2 (0 : F) 1} :
      Set (StatedSp (m + 3) F)) =
      wRadical F (1 : Fin (m + 3)) 2 ⊔
        ((shortBlock F (one_ne_two_fin (n := m))).range ⊔ spCompl12 F m ⊔ ⊥) := by
    rw [hC, sup_bot_eq]
  have hcentbot : Subgroup.centralizer ((⊥ : Subgroup (StatedSp (m + 3) F)) :
      Set (StatedSp (m + 3) F)) = ⊤ := by
    ext x
    simp [Subgroup.mem_centralizer_iff]
  exact RCSTOm.pCoreOf_eq_of_three_summands hX (isPGroup_wRadical one_ne_two_fin) hSQ hTQ
    bot_le hST (by rw [hcentbot]; exact le_top) (by rw [hcentbot]; exact le_top)
    (ggRCSOmSummand_shortBlock (F := F) (n := m) hcard)
    (ggRCSOmSummand_spCompl12 (F := F) hm hcard) RCSTOm.ggRCSOmSummand_bot

theorem commutator_wRadical_sup_shortBlock {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hK : 4 ≤ Nat.card F) :
    ⁅wRadical F (1 : Fin (m + 3)) 2 ⊔ (shortBlock F (one_ne_two_fin (n := m))).range,
      wRadical F (1 : Fin (m + 3)) 2 ⊔ (shortBlock F (one_ne_two_fin (n := m))).range⁆ =
      wRadical F (1 : Fin (m + 3)) 2 ⊔ (shortBlock F (one_ne_two_fin (n := m))).range := by
  have h12 := one_ne_two_fin (n := m)
  set P := wRadical F (1 : Fin (m + 3)) 2 ⊔ (shortBlock F h12).range with hP
  have hSq : CFSG.IsQuasisimple (shortBlock F h12).range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (shortBlock_injective h12))
      (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl
        (Or.inr hK))
  have hSperf : ⁅(shortBlock F h12).range, (shortBlock F h12).range⁆ = (shortBlock F h12).range :=
    Subgroup.isPerfect_iff.mp hSq.1
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  refine sup_le RCSTSp.wRadical_le_commutator_shortBlock ?_
  calc (shortBlock F h12).range = ⁅(shortBlock F h12).range, (shortBlock F h12).range⁆ :=
        hSperf.symm
    _ ≤ ⁅P, P⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem exists_std_of_rootInvolution {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    {G : Type*} [Group G] {ψ : StatedSp (m + 3) K →* G} {t : StatedLieTag} {r : G}
    (hr : GGRootInvolution (rootDatum (m + 3) K) t ψ r) :
    ∃ u : StatedSp (m + 3) K, (∃ i : Fin (m + 3), r = ψ (u * siegDiag K i 1 * u⁻¹)) ∨
      r = ψ (u * twoCentralElt (m + 3) 1 2 (0 : K) 1 * u⁻¹) := by
  obtain ⟨ρ, w, hw⟩ := AutPSp.exists_conj_elt_of_rootInvolution hr
  rcases RCSTSp.elt_one_eq_conj (F := K) ρ with ⟨g, i, hgi⟩ | ⟨g, i, j, hij, hgij⟩
  · refine ⟨w * g, Or.inl ⟨i, ?_⟩⟩
    have h2 : (w * g) * siegDiag K i 1 * (w * g)⁻¹ = w * elt ρ 1 * w⁻¹ := by
      calc (w * g) * siegDiag K i 1 * (w * g)⁻¹
          = w * (g * siegDiag K i 1 * g⁻¹) * w⁻¹ := by group
        _ = w * elt ρ 1 * w⁻¹ := by rw [← hgi]
    rw [h2, hw, map_mul, map_mul, map_inv]
  · obtain ⟨g', hg'⟩ := RCSTSp.exists_conj_one_two (F := K) (n := m) hij
    refine ⟨w * g * g', Or.inr ?_⟩
    have h2 : (w * g * g') * twoCentralElt (m + 3) 1 2 (0 : K) 1 * (w * g * g')⁻¹ =
        w * elt ρ 1 * w⁻¹ := by
      calc (w * g * g') * twoCentralElt (m + 3) 1 2 (0 : K) 1 * (w * g * g')⁻¹
          = w * (g * (g' * twoCentralElt (m + 3) 1 2 (0 : K) 1 * g'⁻¹) * g⁻¹) * w⁻¹ := by
            group
        _ = w * (g * twoCentralElt (m + 3) i j (0 : K) 1 * g⁻¹) * w⁻¹ := by rw [hg']
        _ = w * elt ρ 1 * w⁻¹ := by rw [← hgij]
    rw [h2, hw, map_mul, map_mul, map_inv]

private theorem pCoreOf_map_injective {G G' : Type*} [Group G] [Group G'] (r : ℕ) (f : G →* G')
    (hf : Function.Injective f) (H : Subgroup G) :
    pCoreOf r (H.map f) = (pCoreOf r H).map f := by
  unfold pCoreOf
  let φ : ↥H ≃* ↥(H.map f) := H.equivMapOfInjective f hf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv r φ, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem pCoreOf_range_inf_centralizer {U : Type*} [Group U] {G : Type} [Group G] {ψ : U →* G}
    (hψ : Function.Injective ψ) (x : U) :
    pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer {ψ x}) =
      (pCoreOf 2 (Subgroup.centralizer {x})).map ψ := by
  rw [RCSTSp.range_inf_centralizer_of_injective hψ]
  exact pCoreOf_map_injective 2 ψ hψ _

end CFSG.StandardType.KGSp
