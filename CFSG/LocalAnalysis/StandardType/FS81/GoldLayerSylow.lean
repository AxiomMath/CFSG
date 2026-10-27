module

public import CFSG.LocalAnalysis.StandardType.FS81.GoldLayerComp
import CFSG.GroupTheory.SylowInfSup

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Goldschmidt

variable {Y : Type} [Group Y] [Finite Y] {S : Sylow 2 Y} {B : Subgroup Y}

theorem goldLayer_sylow_eq_sup
    (hgen : CFSG.Open.pCore 2 Y ⊔ goldschmidtLayer Y = ⊤)
    (hcen : CFSG.Open.pCore 2 Y ≤ Subgroup.center Y) (P : Sylow 2 Y) :
    (P : Subgroup Y) = CFSG.Open.pCore 2 Y ⊔
      ⨆ L : {L : Subgroup Y // IsComponentOf L ⊤}, (P : Subgroup Y) ⊓ (L : Subgroup Y) := by
  let 𝓕 : Set (Subgroup Y) := {L : Subgroup Y | IsComponentOf L ⊤}
  set Q : Subgroup Y := CFSG.Open.pCore 2 Y ⊔
    ⨆ L : {L : Subgroup Y // IsComponentOf L ⊤}, (P : Subgroup Y) ⊓ (L : Subgroup Y)
    with hQdef
  change (P : Subgroup Y) = Q
  have hPtop : CFSG.ABGLocalTools.IsSylowOf 2 (P : Subgroup Y) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  have hEnorm : (goldschmidtLayer Y).Normal := by
    rw [goldschmidtLayer.eq_sSup]
    exact Subgroup.sSup_normal _ fun L hL => G3a.component_normal_of_gen hgen hcen hL
  have hEsub : IsSubnormal (goldschmidtLayer Y) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib hEnorm.isSubnormal
  have hle : ∀ L ∈ 𝓕, L ≤ goldschmidtLayer Y := by
    intro L hL
    rw [goldschmidtLayer.eq_sSup]
    exact le_sSup hL
  have hn : ∀ L ∈ 𝓕, goldschmidtLayer Y ≤ Subgroup.normalizer (L : Set Y) := by
    intro L hL
    have : L.Normal := G3a.component_normal_of_gen hgen hcen hL
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hA_le_Q : CFSG.Open.pCore 2 Y ≤ Q := by
    rw [hQdef]
    exact le_sup_left
  have hmain : (P : Subgroup Y) ⊓ goldschmidtLayer Y ≤ Q := by
    have hEeq : goldschmidtLayer Y = ⨆ L ∈ 𝓕, L := by
      rw [goldschmidtLayer.eq_sSup, sSup_eq_iSup]
    rw [hEeq]
    refine CFSG.GroupTheory.inf_iSup_le_of_normal_family (p := 2)
      hPtop hEsub 𝓕 hle hn ?_
    intro L hL
    rw [hQdef]
    exact le_sup_of_le_right
      (le_iSup (fun L : {L : Subgroup Y // IsComponentOf L ⊤} =>
        (P : Subgroup Y) ⊓ (L : Subgroup Y)) ⟨L, hL⟩)
  have hA_le_P : CFSG.Open.pCore 2 Y ≤ (P : Subgroup Y) := by
    haveI : (CFSG.Open.pCore 2 Y).Normal := CFSG.pCore_normal
    exact (CFSG.pCore_isPGroup (p := 2) (G := Y)).le_sylow_of_normal P
  have hP_le_Q : (P : Subgroup Y) ≤ Q := by
    have hP_le : (P : Subgroup Y) ≤
        CFSG.Open.pCore 2 Y ⊔ ((P : Subgroup Y) ⊓ goldschmidtLayer Y) := by
      intro p hp
      have hpE : p ∈ CFSG.Open.pCore 2 Y ⊔ goldschmidtLayer Y := by
        rw [hgen]
        exact Subgroup.mem_top p
      haveI : (CFSG.Open.pCore 2 Y).Normal := CFSG.pCore_normal
      rcases (Subgroup.mem_sup_of_normal_left.mp hpE) with ⟨a, ha, e, he, hae⟩
      have heP : e ∈ (P : Subgroup Y) := by
        have h1 : a⁻¹ * p = e := by rw [← hae]; group
        rw [← h1]
        exact (P : Subgroup Y).mul_mem ((P : Subgroup Y).inv_mem (hA_le_P ha)) hp
      exact Subgroup.mem_sup_of_normal_left.mpr ⟨a, ha, e, ⟨heP, he⟩, hae⟩
    calc (P : Subgroup Y) ≤
          CFSG.Open.pCore 2 Y ⊔ ((P : Subgroup Y) ⊓ goldschmidtLayer Y) := hP_le
      _ ≤ CFSG.Open.pCore 2 Y ⊔ Q := sup_le le_sup_left (hmain.trans le_sup_right)
      _ = Q := sup_eq_right.mpr hA_le_Q
  have hQ_le_P : Q ≤ (P : Subgroup Y) := by
    rw [hQdef]
    exact sup_le hA_le_P (iSup_le fun L => inf_le_left)
  exact le_antisymm hP_le_Q hQ_le_P

theorem goldLayer_unique_sylow
    (D : GoldLayerFacts Y S B) {P : Sylow 2 Y} (hBP : B ≤ P) : P = S := by
  have h7 := goldLayer_sylow_eq_sup D.gen D.central
  apply Sylow.ext
  rw [h7 P, h7 S]
  congr 2
  funext L
  exact goldLayer_inf_eq D L.2 hBP

theorem goldLayer_exists_component (hL : goldschmidtLayer Y ≠ ⊥) :
    ∃ L : Subgroup Y, IsComponentOf L ⊤ := by
  by_contra hno
  push Not at hno
  apply hL
  have : {K : Subgroup Y | IsComponentOf K ⊤} = ∅ := Set.eq_empty_of_forall_notMem hno
  rw [goldschmidtLayer.eq_sSup, this, sSup_empty]

theorem goldLayer_normalizer
    (hcore : CoreStatement) {Y : Type} [Group Y] [Finite Y] (S : Sylow 2 Y) (B : Subgroup Y)
    (hBS : B ≤ (S : Subgroup Y)) (hBc : IsMulCommutative B)
    (hcl : fusionStronglyClosed (B : Set Y) (S : Subgroup Y))
    (hgen : Subgroup.normalClosure (B : Set Y) = ⊤) (hO : goldschmidtOddCore Y = ⊥)
    (hC : CoreConclusion Y S B) (hL : goldschmidtLayer Y ≠ ⊥) :
    (∀ n ∈ Subgroup.normalizer (B : Set Y), ∀ s ∈ (S : Subgroup Y),
        n * s * n⁻¹ ∈ (S : Subgroup Y)) ∧
      ¬ Subgroup.normalizer (B : Set Y) ≤ (S : Subgroup Y) := by
  have D := goldLayer_facts hcore (S := S) (B := B) ⟨hBS, hBc, hcl, hgen, hO⟩ hC
  refine ⟨fun n hn s hs => ?_, fun hle => ?_⟩
  ·
    have hBP : B ≤ ((n • S : Sylow 2 Y) : Subgroup Y) := by
      intro b hb
      have hb' : n⁻¹ * b * n ∈ B := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) b).mp hb
        simpa using this
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨n⁻¹ * b * n, hBS hb', by simp [MulAut.conj_apply, mul_assoc]⟩
    have hP := goldLayer_unique_sylow D hBP
    have hs' : n * s * n⁻¹ ∈ ((n • S : Sylow 2 Y) : Subgroup Y) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨s, hs, by simp [MulAut.conj_apply]⟩
    rw [hP] at hs'
    exact hs'
  · obtain ⟨L, hLc⟩ := goldLayer_exists_component hL
    obtain ⟨y, -, hyN, hy1, hyodd⟩ := goldLayer_exists_odd_normalizer D hLc
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨y, hle hyN⟩
    have hk' : y ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hdvd : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h1 : orderOf y = 1 := by
      have := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      obtain ⟨j, -, hj⟩ := this
      rcases j with _ | j
      · simpa using hj
      · exfalso
        rw [hj] at hyodd
        exact (Nat.not_even_iff_odd.mpr hyodd) (by simp [pow_succ])
    exact hy1 (orderOf_eq_one_iff.mp h1)

end CFSG.StandardType.FrameRoute.FS81

end
