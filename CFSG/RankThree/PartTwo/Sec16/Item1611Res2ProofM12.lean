module

public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofList
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
import CFSG.RankThree.PartTwo.Sec16.Item1611Res2ProofModel
import CFSG.RankThree.PartTwo.Sec16.Item1611Res2ProofPoint
import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesM12
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJM12
import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaRankThree

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

namespace Proof1611Res2M12

open CFSG.GH74.M12.Hyp (G12)
open CFSG.RankThree.PartTwo.Toolkit.M12 (basisA basisE basisF)
open CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig (V ai card_V V_le_C isPGroup_V V_ne
  A_le_normalizer_V le_V_of_mem_invariant)

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem exists_conj_mem_A_of_alpha
    (hD : Sec13Data G A c L) (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hE9 : Nat.card (((A ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 9)
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* G12) :
    ∃ g : G12, ∀ x ∈ ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
      ∃ p ∈ Toolkit.M12.A, g * p * g⁻¹ = φ x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Eb := ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
    with hEb
  have hEbe : CFSG.Assembly.IsElemAbelian 3 Eb := by
    rw [hEb]
    exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 (A ⊓ L) L
        ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩,
          fun x hx => hD.isElemAbelian.2 x hx.1⟩)
  set T := Eb.map φ.toMonoidHom with hT
  have hT9 : Nat.card T = 9 := by rw [hT, Subgroup.card_map_of_injective φ.injective, hE9]
  have hTe : CFSG.Assembly.IsElemAbelian 3 T := Sec4.Res423Two.isElemAbelian_map' _ hEbe
  have hT3 : IsPGroup 3 T := IsPGroup.of_card (n := 2) (by rw [hT9]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_le_P0_m12 hT3
  set T' := T.map (MulAut.conj g).toMonoidHom with hT'
  have hT'e : CFSG.Assembly.IsElemAbelian 3 T' := Sec4.Res423Two.isElemAbelian_map' _ hTe
  have hmem : T' ∈ ({Toolkit.M12.E, Toolkit.M12.F, Toolkit.M12.A, Toolkit.M12.A'} :
      Set (Subgroup G12)) := by
    rw [← Toolkit.M12.nine_eq]
    exact ⟨hg, by rw [hT', Subgroup.card_map_of_injective (MulAut.conj g).injective, hT9]⟩
  have hTT' : T = T'.map (MulAut.conj g⁻¹).toMonoidHom := by
    have h1 := Sec4.Item434AltPerm.map_conj_map_conj_inv T g⁻¹
    rw [inv_inv] at h1
    exact h1.symm
  have hEbc := Sec4.Res423Two.comm_of_isElemAbelian hEbe
  have hEb1 := Sec4.Res423Two.ne_bot_of_card_nine hE9
  have hnot : ∀ B : Subgroup G12, T' = B → Sec4.Item434SporGen.NoSignalizer B → False := by
    intro B hB hNS
    have hNST : Sec4.Item434SporGen.NoSignalizer T := by
      rw [hTT', hB]
      exact hNS.map_conj g⁻¹
    exact Proof1611Res2.false_of_alpha_eq_bot hD hAc
      (Sec4.Res423Two.alphaVanishes_of_noSignalizer_mulEquiv hZ φ hEbc hEb1 hNST)
  rcases hmem with hE | hF | hA | hA'
  · have hEe : CFSG.Assembly.IsElemAbelian 3 basisE.sub := by
      have h1 := hT'e
      rw [hE] at h1
      exact h1
    exact (hnot _ hE (Sec4.Item434SporGen.noSignalizer_E hEe)).elim
  · have hFe : CFSG.Assembly.IsElemAbelian 3 basisF.sub := by
      have h1 := hT'e
      rw [hF] at h1
      exact h1
    exact (hnot _ hF (Sec4.Item434SporGen.noSignalizer_F hFe)).elim
  · refine ⟨g⁻¹, fun x hx => ⟨g * φ x * g⁻¹, ?_, by group⟩⟩
    rw [← hA]
    exact ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩
  · refine ⟨(Toolkit.M12.g0 * g)⁻¹, fun x hx => ⟨(Toolkit.M12.g0 * g) * φ x *
      (Toolkit.M12.g0 * g)⁻¹, ?_, by group⟩⟩
    rw [← Toolkit.M12.map_g0_A', ← hA']
    refine ⟨g * φ x * g⁻¹, ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    change Toolkit.M12.g0 * (g * φ x * g⁻¹) * Toolkit.M12.g0⁻¹ =
      Toolkit.M12.g0 * g * φ x * (Toolkit.M12.g0 * g)⁻¹
    group

theorem two_subgroup_facts :
    (∀ X : Subgroup G12, IsPGroup 2 X → basisA.sub ≤ Subgroup.normalizer (X : Set G12) →
      V 0 ≤ X → X ⊓ Subgroup.centralizer ({ai 1} : Set G12) = ⊥) ∧
    V 1 ⊓ Subgroup.centralizer ({ai 1} : Set G12) ≠ ⊥ := by
  have hV0 : V 0 ≠ ⊥ := by
    intro h0
    have h4 := card_V 0
    rw [h0, Subgroup.card_bot] at h4
    omega
  refine ⟨fun X hX2 hAX hVX => ?_, fun hbot => ?_⟩
  · have hXne : X ≠ ⊥ := fun h0 => hV0 (le_bot_iff.mp (h0 ▸ hVX))
    obtain ⟨i, hi⟩ := le_V_of_mem_invariant
      ((mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hX2, hAX⟩) hXne
    have hi0 : i = 0 := by
      have heq : V 0 = V i :=
        Subgroup.eq_of_le_of_card_ge (hVX.trans hi) (by rw [card_V, card_V])
      exact (V_ne 0 i heq).symm
    subst hi0
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgX, hgC⟩ := Subgroup.mem_inf.mp hg
    have hgV : g ∈ V 0 := hi hgX
    have h0 : Commute g (ai 0) := Subgroup.mem_centralizer_singleton_iff.mp (V_le_C 0 hgV)
    have h1 : Commute g (ai 1) := Subgroup.mem_centralizer_singleton_iff.mp hgC
    have hz := commute_z_of_commute_ai (by decide) h0 h1
    have hgA : g ∈ basisA.sub := by
      rw [← centralizer_basisA]
      exact mem_centralizer_A_of_commute hz h1
    exact Subgroup.mem_bot.mpr (eq_one_of_mem_basisA
      (Proof1611Res2.not_three_dvd_card_of_isPGroup_two (isPGroup_V 0)) hgA hgV)
  · rw [inf_eq_left.mpr (V_le_C 1)] at hbot
    have h4 := card_V 1
    rw [hbot, Subgroup.card_bot] at h4
    omega

end Proof1611Res2M12

open Proof1611Res2M12 CFSG.RankThree.PartTwo.Toolkit.M12
  CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig in
theorem ks1611M12NotTrans :
    KS1611M12NotTrans := by
  intro G _ _ A c L h hM hAab hcA h142
  have : (ker142 A (lB A) c).Normal := ker142_normal hAab hcA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS14 := h.toSec14Std
  have hD := h.toSec13Data
  have hX := KFacts.ks18M12 (↥L ⧸ aschbacherSolvableCore 3 ↥L) hM
  obtain ⟨-, h9, hAc⟩ := Proof1611Res2.point_facts_of_inner_aut hD hX.2.1
    (fun σ hσ => hX.2.2.1 σ ⟨1, by rw [pow_one]; exact hσ⟩)
  obtain ⟨φ⟩ := hM
  have hE9 := Res5Gen.card_image_inf hS14 h9
  obtain ⟨g, hg⟩ := exists_conj_mem_A_of_alpha hD hAc hE9 hX.2.1 φ
  obtain ⟨φ', hφ'⟩ := Res5Types.exists_equiv_map_eq_of_conj φ hg
    (by rw [basisA.card, hE9])
  have hLK := Proof1611Res2.le_k142_of_item142 hS14 h142
    (by rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM12]; norm_num)
  obtain ⟨h1, h2⟩ := two_subgroup_facts
  exact Proof1611Res2.not_transOn_of_model sporadicModels131 hS14 hLK
    (fun Q hQ => (h142 Q hQ).1) hAc φ' hφ' (Res5TypesM12.ai_mem_A 1) (isPGroup_V 0)
    (A_le_normalizer_V 0) (isPGroup_V 1) (A_le_normalizer_V 1) h1 h2

end CFSG.RankThree.PartTwo.Sec16
