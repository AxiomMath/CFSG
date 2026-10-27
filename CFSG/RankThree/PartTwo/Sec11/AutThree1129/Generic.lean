module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofSpor
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
import CFSG.Sporadic.Schreier.MathieuOddCoreM24
import CFSG.Sporadic.Schreier.PairHePairs
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

@[expose] def AutThreeAut (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z],
    (∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X)) →
    ∀ (α : MulAut Z) (J : Subgroup Z), α ^ 3 = 1 →
      J ∈ thetaComponentsIn (Item426.fixSub α) →
      IsType424 (J ⧸ aschbacherSolvableCore 3 J) → (Nat.card J).factorization 3 = 1 →
      ∀ P : Subgroup (MulAut Z), IsPGroup 3 P → Nat.card P ≤ 27

@[expose] def AutThree1129For (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y K : Subgroup G) (c : G),
    (∃ (X : Type) (_ : Group X), F X ∧
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X)) →
    c ∈ Subgroup.normalizer (Y : Set G) → c ^ 3 = 1 →
    K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) →
    IsType424 (K ⧸ aschbacherSolvableCore 3 K) → (Nat.card K).factorization 3 = 1 →
    ∀ Q : Subgroup G, IsPGroup 3 Q → Q ≤ Subgroup.normalizer (Y : Set G) →
      Nat.card Q ≤ 27 * Nat.card (Q ⊓ Sec4.thetaQuotCentralizer Y : Subgroup G)

theorem autThree1129For_of_autThree {F : ∀ (X : Type) [Group X], Prop} (h : AutThreeAut F) :
    AutThree1129For F := by
  intro G _ _ Y K c hX hcN hc3 hK hT hK3 Q hQ hQN
  have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hπ
  set J := (K.subgroupOf Y).map π with hJdef
  have hJ : J ∈ thetaComponentsIn (Item426.fixSub (Item426.thetaAut Y hcN)) :=
    Item426.map_mem_thetaComponentsIn_fixSub Y hcN hc3 hK
  obtain ⟨eK⟩ := Item426.nonempty_quotTheta_map_equiv Y hKY
  have hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J) := isType424_of_mulEquiv eK.symm hT
  have hdvd : 3 ∣ Nat.card J := by
    have hq : Nat.card (J ⧸ aschbacherSolvableCore 3 J) ∣ Nat.card J :=
      ⟨Nat.card (aschbacherSolvableCore 3 J),
        Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
    exact (KS11LieProof.three_dvd_card_of_isType424 hJT).trans hq
  have hJK : Nat.card J ∣ Nat.card K := by
    have h1 := Subgroup.card_map_dvd (K.subgroupOf Y) π
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv] at h1
  have hJ3 : (Nat.card J).factorization 3 = 1 := by
    have hpos : 0 < (Nat.card J).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hdvd
    have hle : (Nat.card J).factorization 3 ≤ (Nat.card K).factorization 3 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hJK 3
    omega
  have hα3 : Item426.thetaAut Y hcN ^ 3 = 1 := Item426.thetaAut_pow_eq_one Y hcN hc3
  let ρ : Subgroup.normalizer (Y : Set G) →* MulAut (Y ⧸ aschbacherSolvableCore 3 Y) :=
    (Sec4.thetaQuotMulAut Y).comp Y.normalizerMonoidHom
  let Ψ : Q →* MulAut (Y ⧸ aschbacherSolvableCore 3 Y) := ρ.comp (Subgroup.inclusion hQN)
  have hPgrp : IsPGroup 3 Ψ.range := by
    rintro ⟨g, hg⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
    obtain ⟨k, hk⟩ := hQ x
    exact ⟨k, Subtype.ext (by change Ψ x ^ 3 ^ k = 1; rw [← map_pow, hk, map_one])⟩
  have hP : Nat.card Ψ.range ≤ 27 :=
    h (Y ⧸ aschbacherSolvableCore 3 Y) hX (Item426.thetaAut Y hcN) J hα3 hJ hJT hJ3 Ψ.range
      hPgrp
  have hcard : Nat.card Q = Nat.card Ψ.ker * Nat.card Ψ.range := by
    have h1 := Subgroup.card_mul_index Ψ.ker
    rw [Subgroup.index_ker] at h1
    exact h1.symm
  have hker : Ψ.ker.map Q.subtype = Q ⊓ Sec4.thetaQuotCentralizer Y := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Sec4.thetaQuotCentralizer, Subgroup.mem_map]
      exact ⟨Subgroup.inclusion hQN x, hx, rfl⟩
    · rintro ⟨hgQ, hg⟩
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp
        (show _ ∈ Subgroup.map (Subgroup.normalizer (Y : Set G)).subtype
          (((Sec4.thetaQuotMulAut Y).comp Y.normalizerMonoidHom).ker) from hg)
      exact Subgroup.mem_map.mpr ⟨⟨_, hgQ⟩, hn, rfl⟩
  have hk : Nat.card Ψ.ker = Nat.card (Q ⊓ Sec4.thetaQuotCentralizer Y : Subgroup G) := by
    rw [← hker]
    exact Nat.card_congr (Subgroup.equivMapOfInjective Ψ.ker Q.subtype Q.subtype_injective).toEquiv
  rw [hcard, hk, mul_comm (27 : ℕ)]
  exact Nat.mul_le_mul_left _ hP

theorem card_le_27_of_isPGroup {W : Type} [Group W] [Finite W] (hZ : Subgroup.center W = ⊥)
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer W) ≤ 2)
    (h3 : (Nat.card W).factorization 3 ≤ 3)
    (P : Subgroup (MulAut W)) (hP : IsPGroup 3 P) : Nat.card P ≤ 27 := by
  have hPin : P ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner W := by
    intro β hβ
    obtain ⟨k, hk⟩ := hP ⟨β, hβ⟩
    exact KS11Lie2Proof.mem_inner_of_card_outer_le_two hout ⟨k, congrArg Subtype.val hk⟩
  have hinj : Function.Injective (MulAut.conj : W →* MulAut W) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center W := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h1 := congrArg (fun φ : MulAut W => φ w) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    rw [hZ, Subgroup.mem_bot] at hgc
    exact hgc
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup W, Q = P.comap (MulAut.conj : W →* MulAut W) := ⟨_, rfl⟩
  have hmap : Q.map (MulAut.conj : W →* MulAut W) = P := by
    rw [hQdef, Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hPin
  have hQcard : Nat.card P = Nat.card Q := by
    rw [← hmap, Subgroup.card_map_of_injective hinj]
  have hQp : IsPGroup 3 Q := by
    rintro ⟨g, hg⟩
    have hgP : MulAut.conj g ∈ P := by
      rw [hQdef] at hg
      exact hg
    obtain ⟨k, hk⟩ := hP ⟨MulAut.conj g, hgP⟩
    refine ⟨k, Subtype.ext ?_⟩
    change g ^ 3 ^ k = 1
    apply hinj
    rw [map_pow, map_one]
    exact congrArg Subtype.val hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
  have hdvd : 3 ^ n ∣ Nat.card W := by
    rw [← hn]
    exact Subgroup.card_subgroup_dvd_card Q
  have hle : n ≤ (Nat.card W).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp hdvd
  rw [hQcard, hn]
  calc 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (hle.trans h3)
    _ = 27 := by norm_num

theorem card_le_27_of_equiv {Z W : Type} [Group Z] [Group W] (g : Z ≃* W)
    (hW : ∀ Q : Subgroup (MulAut W), IsPGroup 3 Q → Nat.card Q ≤ 27)
    (P : Subgroup (MulAut Z)) (hP : IsPGroup 3 P) : Nat.card P ≤ 27 := by
  have hinj : Function.Injective (MulAut.congr g).toMonoidHom := (MulAut.congr g).injective
  have hcard : Nat.card (P.map (MulAut.congr g).toMonoidHom) = Nat.card P :=
    Subgroup.card_map_of_injective hinj
  rw [← hcard]
  apply hW
  rintro ⟨β, hβ⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hβ
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hk' : x ^ 3 ^ k = 1 := congrArg Subtype.val hk
  change (MulAut.congr g).toMonoidHom x ^ 3 ^ k = 1
  rw [← map_pow, hk', map_one]

theorem isPerfect_of_mulEquiv {X W : Type} [Group X] [Group W] (hW : Group.IsPerfect W)
    (f : X ≃* W) : Group.IsPerfect X :=
  Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective

theorem nonempty_mulEquiv_of_commutator {X Z W : Type} [Group X] [Group Z] [Group W]
    (hW : Group.IsPerfect W) (f : X ≃* W) (e : Z ≃* _root_.commutator X) :
    Nonempty (Z ≃* W) := by
  have hX : Group.IsPerfect X := isPerfect_of_mulEquiv hW f
  exact ⟨e.trans (((MulEquiv.subgroupCongr hX.commutator_eq_top).trans Subgroup.topEquiv).trans f)⟩

section Spor

theorem autThreeAut_spor : AutThreeAut (fun (X : Type) [Group X] =>
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.He)) := by
  intro Z _ _ hZ _ _ _ _ _ _ P hP
  obtain ⟨X, _, hF, ⟨e⟩⟩ := hZ
  rcases hF with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · obtain ⟨x, y, -, -, -, hz, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
    have hs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M24 :=
      CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    have hpf : Group.IsPerfect CFSG.Blueprint.NativeSporadic.M24 :=
      KS11Lie2Proof.isPerfect_of_isSimpleGroup hz
    have hfin : Finite CFSG.Blueprint.NativeSporadic.M24 :=
      Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num)
    have h3 : (Nat.card CFSG.Blueprint.NativeSporadic.M24).factorization 3 ≤ 3 := by
      rw [CFSG.Sporadic.Mathieu.card_M24, show (244823040 : ℕ) = 3 ^ 3 * 9067520 by norm_num,
        Sec4.Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
    have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        CFSG.Blueprint.NativeSporadic.M24) ≤ 2 := by
      have hinner : CFSG.ComponentClassification.OuterAutomorphisms.inner
          CFSG.Blueprint.NativeSporadic.M24 = ⊤ :=
        CFSG.Sporadic.Schreier.inner_eq_top_of_card_le CFSG.Sporadic.Schreier.m24_center_eq_bot'
          CFSG.Sporadic.Schreier.m24_mulAut_card
      change (CFSG.ComponentClassification.OuterAutomorphisms.inner
        CFSG.Blueprint.NativeSporadic.M24).index ≤ 2
      rw [hinner, Subgroup.index_top]
      norm_num
    obtain ⟨g⟩ := nonempty_mulEquiv_of_commutator hpf f e
    exact card_le_27_of_equiv g (card_le_27_of_isPGroup
      CFSG.Sporadic.Schreier.m24_center_eq_bot' hout h3) P hP
  · obtain ⟨x, y, -, -, -, hz, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
    have hs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.He :=
      CFSG.Sporadic.He.isSimpleGroup_He
    have hpf : Group.IsPerfect CFSG.Blueprint.NativeSporadic.He :=
      KS11Lie2Proof.isPerfect_of_isSimpleGroup hz
    have hfin : Finite CFSG.Blueprint.NativeSporadic.He :=
      Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.He.card_He]; norm_num)
    have h3 : (Nat.card CFSG.Blueprint.NativeSporadic.He).factorization 3 ≤ 3 := by
      rw [CFSG.Sporadic.He.card_He, show (4030387200 : ℕ) = 3 ^ 3 * 149273600 by norm_num,
        Sec4.Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
    obtain ⟨g⟩ := nonempty_mulEquiv_of_commutator hpf f e
    exact card_le_27_of_equiv g (card_le_27_of_isPGroup
      (KS11Lie2Proof.center_eq_bot_of_isSimpleGroup hz)
      CFSG.Sporadic.Schreier.AT_He_Schreier.1 h3) P hP

end Spor

end CFSG.RankThree.PartTwo.Sec11

end
