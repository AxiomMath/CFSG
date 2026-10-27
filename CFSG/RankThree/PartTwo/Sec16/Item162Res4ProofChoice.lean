module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res2ProofOther
import CFSG.RankThree.PartTwo.Sec16.Item162Res2ProofAll
import CFSG.RankThree.PartTwo.Sec16.Item162ResProofConf
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec17.Item17Q0Proof
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def Choice162 (A : Subgroup G) (c : G) (S : Subgroup G) : Prop :=
  S ⊓ Subgroup.centralizer ({c} : Set G) ∈
    scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2)

end Defs

@[expose] def Step162A7OtherSevenC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y₁ Y₂ S : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S S → L ≤ Y₁ →
      MeetsY4 A (lB A) L Y₁ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      WStarS4 A → TransOmegaThree A c →
      Nonempty (↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁ ≃* alternatingGroup (Fin 7)) →
      (¬ ∃ g ∈ Subgroup.normalizer (A : Set G), Y₂ = Y₁.map (MulAut.conj g).toMonoidHom) →
      Choice162 A c S →
      ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
        Subgroup.zpowers b ≠ Subgroup.zpowers c → MeetsY4 A (lB A) Lb Y₂ →
        Nonempty (↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7)) →
        Late.sectionCentralizer A Y₂ (CFSG.Open.pCoreOf 2 Y₂) = (Subgroup.zpowers b : Set G) →
          False

@[expose] def Step162ChoiceFaithful : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    CFSG.Open.pCoreOf 2 L = ⊥ → ∀ Y ∈ scriptY0Star A (lB A), L ≤ Y →
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) →
      ∀ Sc ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2),
        Sc ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
          ∃ K ∈ scriptY0Star A (lB A), L ≤ K ∧ Sc ≤ Subgroup.normalizer (K : Set G)

namespace Res162d

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer' (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
    (Subgroup.normal_subgroupOf_centralizer_normalizer _)

omit [Finite G] in
theorem not_normalizer_le_of_trans {A : Subgroup G} {c : G}
    (hc : Subgroup.zpowers c ∈ omegaA A) (hT : TransOmegaThree A c) :
    ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro hWH
  apply omegaA_ne_singleton_of_trans (c := c) hT
  ext F
  rw [Set.mem_singleton_iff]
  constructor
  · intro hF
    obtain ⟨v, hv, rfl⟩ := hT.2 F hF
    exact Late.map_conj_eq_of_mem_normalizer (hWH hv)
  · rintro rfl
    exact hc

theorem choice162_of_le {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    {S Sc : Subgroup G} (hS : S ∈ scriptQPi A (lB A) ⊤ (piOf 2))
    (hSc : Sc ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))
      (piOf 2))
    (hScS : Sc ≤ S) : Choice162 A c S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hScc : Sc ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_le_normalizer_zpowers h.toSec14Std.isE27 hD.mem_A hSc.prop.1.1
      hSc.prop.1.2
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hD.mem_A)
  have hAC : A ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) :
      Set G) :=
    (le_inf hS.1.1.1.2.2 (hAc.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS
  have hmem : S ⊓ Subgroup.centralizer ({c} : Set G) ∈
      scriptQPi A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2) :=
    ⟨⟨mem_scriptQ_of_le hS.1.1 inf_le_left hAC,
      inf_le_right.trans (centralizer_singleton_le_normalizer_zpowers c)⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hS2.to_le inf_le_left)⟩
  have hle : Sc ≤ S ⊓ Subgroup.centralizer ({c} : Set G) := le_inf hScS hScc
  have heq : S ⊓ Subgroup.centralizer ({c} : Set G) = Sc := le_antisymm (hSc.2 hmem hle) hle
  unfold Choice162
  rw [heq]
  exact hSc

theorem exists_le_normalizer_of_centralizer {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h155 : Item155 A (lB A)) (hL4 : L ∈ scriptY4 A (lB A))
    {Sc : Subgroup G}
    (hSc : Sc ∈ scriptQPi A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2))
    (hScL : Sc ≤ Subgroup.normalizer (L : Set G))
    (hne : Sc ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    ∃ K ∈ scriptY0Star A (lB A), L ≤ K ∧ Sc ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set Q := Sc ⊓ Subgroup.centralizer (L : Set G) with hQdef
  set Y' := L ⊔ Q with hY'def
  have hSc2 : IsPGroup 2 Sc := isPGroup_of_mem_scriptQPi Nat.prime_two hSc
  have hQ2 : IsPGroup 2 Q := hSc2.to_le inf_le_left
  have hNC := normalizer_le_normalizer_centralizer' L
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    (le_inf hSc.1.1.1.2.2 (hD.le_normalizer.trans hNC)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hQQ : Q ∈ scriptQ A (lB A) := mem_scriptQ_of_le hSc.1.1 inf_le_left hAQ
  have hQC : Q ≤ Subgroup.centralizer (L : Set G) := inf_le_right
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.le_centralizer_iff.mp hQC).trans (Subgroup.centralizer_le_normalizer _)
  have hQL : Q ≤ Subgroup.normalizer (L : Set G) :=
    hQC.trans (Subgroup.centralizer_le_normalizer _)
  have hScQ : Sc ≤ Subgroup.normalizer (Q : Set G) :=
    (le_inf Subgroup.le_normalizer (hScL.trans hNC)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hY'Q : Y' ≤ Subgroup.normalizer (Q : Set G) := sup_le hLQ Subgroup.le_normalizer
  have hQO : Q ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'Q hQ2
  have hO2 : CFSG.Open.pCoreOf 2 Y' ≠ ⊥ := fun h0 => hne (le_bot_iff.mp (h0 ▸ hQO))
  have hY'Δ : Y' = delta A (lB A) Y' :=
    le_antisymm (sup_le (hL4.2.2.1.le.trans (delta_mono le_sup_left)) (le_delta hQQ le_sup_right))
      (delta_le _)
  have hScc : Sc ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_le_normalizer_zpowers h.toSec14Std.isE27 hD.mem_A hSc.1.1 hSc.1.2
  have hY'c : Y' ≤ Subgroup.centralizer ({c} : Set G) :=
    sup_le hD.le_centralizer (inf_le_left.trans hScc)
  have hY'top : Y' ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hD.ne_one (top_le_iff.mp (htop ▸ hY'c))
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) := le_normalizer_sup hD.le_normalizer hAQ
  have hY'3 : Y' ∈ scriptY3 A (lB A) := ⟨⟨⟨hY'top, hAY'⟩, hO2⟩, hY'Δ⟩
  have hres : oPrimeResidualOf 3 Y' = L :=
    ((oPrimeResidualOf_eq_of_le le_sup_left fun x hx k hk =>
      mem_of_pow_three_of_mem_sup hQL hQ2 hx hk).symm.trans hL4.2.1.symm)
  have hX4 : oPrimeResidualOf 3 Y' ∈ scriptY4 A (lB A) := by
    rw [hres]
    exact hL4
  have hY'eq : Y' = oPrimeResidualOf 3 Y' ⊔ CFSG.Open.pCoreOf 2 Y' := by
    rw [hres]
    exact le_antisymm (sup_le le_sup_left (hQO.trans le_sup_right))
      (sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y'))
  have hΩ : omg155 A (oPrimeResidualOf 3 Y') := by
    rw [hres]
    exact Or.inr ⟨c, L, h.zpowers_mem_omegaA, h.mem_lA, by
      rw [inf_idem, sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)]⟩
  obtain ⟨K, hK⟩ := (h155 Y' hY'3 hX4 hY'eq).1 hΩ
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y' : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y') hO2
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hAY'O : A ⊔ Y' ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y' : Set G) :=
    sup_le (hAY'.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y'))
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y')
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y' : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (hAY'O hx)⟩
  have hΔ := (h155 Y' hY'3 hX4 hY'eq).2 K hK (Or.inl hΩ) M hMm
  have hScY' : Sc ≤ Subgroup.normalizer (Y' : Set G) := le_normalizer_sup hScL hScQ
  have hScM : Sc ≤ M :=
    (hScY'.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y')).trans hle
  refine ⟨K, hK.1, ?_, (le_delta hSc.1.1 hScM).trans hΔ⟩
  rw [← hres]
  exact hK.2.1

theorem exists_choice_member {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h155 : Item155 A (lB A)) (hF : Step162ChoiceFaithful) (hL4 : L ∈ scriptY4 A (lB A))
    (h7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hLY : L ≤ Y)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) {Sc : Subgroup G}
    (hSc : Sc ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))
      (piOf 2)) :
    ∃ K ∈ scriptY0Star A (lB A), L ≤ K ∧ Sc ≤ Subgroup.normalizer (K : Set G) := by
  have hScL : Sc ≤ Subgroup.normalizer (L : Set G) := hSc.prop.1.2.trans
    (normalizer_zpowers_le_normalizer_L h (three_dvd_card_of_mem_lA h h.zpowers_mem_omegaA
      h.mem_lA))
  by_cases hO : CFSG.Open.pCoreOf 2 L = ⊥
  · by_cases hQ : Sc ⊓ Subgroup.centralizer (L : Set G) = ⊥
    · exact hF G A c L h h7 hO Y hY hLY ⟨φ⟩ Sc hSc hQ
    · exact exists_le_normalizer_of_centralizer h h155 hL4 hSc.prop hScL hQ
  · refine ⟨Y, hY, hLY, ?_⟩
    exact (le_delta hSc.prop.1.1 (hScL.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))).trans
      (delta_normalizer_le_of_mem_scriptY4 h h155 hL4 hO hY hLY)

theorem false_of_other_ten (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14)
    (h142 : Concl142S14) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    {Y₁ Y₂ S : Subgroup G} (hmax : MaxCE162 A (lB A) Y₁ Y₂ S S) (hLY₁ : L ≤ Y₁)
    (hm₁ : MeetsY4 A (lB A) L Y₁)
    (h7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hT : TransOmegaThree A c) (φ₁ : ↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁ ≃* alternatingGroup (Fin 10))
    {b : G} {Lb : Subgroup G} (hb : Subgroup.zpowers b ∈ omegaA A) (hLb : Lb ∈ lA A b)
    (hm₂ : MeetsY4 A (lB A) Lb Y₂) (φ₂ : ↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7)) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φL⟩ := h7
  have hD := h.toSec13Data
  have hY₁ := hmax.1.mem₁
  have hY₂ := hmax.1.mem₂
  have hAY₁ : A ≤ Y₁ := Step163Alt.le_of_alternating_ten (Res162.partTwoE_maximal h)
    hD.isElemAbelian hY₁.prop.1.1.2 hY₁.prop.2.2 φ₁
  obtain ⟨y, hy, hby⟩ := Step163Alt.omega_transitive_of_ten hD.isElemAbelian hD.card_eq hAY₁
    φ₁ hT.1 _ h.zpowers_mem_omegaA _ hb
  have hyY : y ∈ Y₁ := (Subgroup.mem_inf.mp hy).1
  have hyW : y ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hy).2
  have hb' : Sec15R G A b Lb := sec15R_of_point h hb hLb
  have hLLb : L.map (MulAut.conj y).toMonoidHom = Lb :=
    map_conj_eq_of_zpowers hb' h.zpowers_mem_omegaA h.mem_lA hyW hby
  have hLbY₁ : Lb ≤ Y₁ := by
    rw [← hLLb]
    have := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hLY₁
    rwa [Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hyY)] at this
  obtain ⟨φLb⟩ := nonempty_a7_of_map_conj hLLb ⟨φL⟩
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hb).1
  have hb3 : b ^ 3 = 1 := hD.isElemAbelian.2 b hbA
  have hb1 : b ≠ 1 := by
    intro h1
    have h3 := (zpowers_mem_omegaA_iff.mp hb).2.1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
    omega
  have hLbp : Group.IsPerfect ↥Lb := Sec6.isPerfect_of_mem_thetaComponentsAt hLb.1
  have hθb := Res162b.theta_le_pCoreOf_of_ten hLbY₁ (hAY₁ hbA) hb3 hb1
    (le_centralizer_of_mem_thetaComponentsAt hLb.1) hLbp φLb φ₁
  have h14 := h.toSec14Std
  have hOS : CFSG.Open.pCoreOf 2 Y₁ ≤ S := by
    have hV := Sec17.Proof17Q0.pCoreOf_mem_scriptQ_of_cover h14 (h1444 G A c L h14)
      (h146 G A c L h14) (hbot G A c L h14) (h142 G A c L h14) hY₁.prop.1
      (Or.inr (hAY₁ hD.mem_A))
    exact Proof162.pCoreOf_le_of_mem_scriptQ h14.isE27 (h146 G A c L h14) hmax.1.s₁ hV
  have hSN₂ : S ≤ Subgroup.normalizer (Y₂ : Set G) := hmax.1.s₂.prop.1.2
  set θ := aschbacherSolvableCore 3 ↥Lb with hθ
  set P := θ.map Lb.subtype with hP
  have hP2 : IsPGroup 2 P := by
    have hPO : P ≤ CFSG.Open.pCoreOf 2 Y₁ := by
      rintro _ ⟨t, ht, rfl⟩
      exact hθb t ht
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₁).to_le hPO
  have hPN : P ≤ Subgroup.normalizer ((Lb ⊓ Y₂ : Subgroup G) : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer t.2, hSN₂ (hOS (hθb t ht))⟩
  have hLle : Lb ≤ P ⊔ (Lb ⊓ Y₂) := by
    intro l hl
    obtain ⟨d, hdD, hdL, hdl⟩ := Res162b.exists_mem_inf_of_seven hb' hY₂ hm₂ φLb φ₂ l hl
    have hP' : d⁻¹ * l ∈ P := ⟨_, hdl, by simp⟩
    have he : l = d * (d⁻¹ * l) := by group
    rw [he]
    exact mul_mem (Subgroup.mem_sup_right hdD) (Subgroup.mem_sup_left hP')
  have hL3 : Lb = oPrimeResidualOf 3 Lb := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact eq_oPrimeResidualOf_of_isSimpleGroup hLbp φLb.isSimpleGroup
      (three_dvd_card_of_mem_lA hb' hb hLb)
  have hLbY₂ : Lb ≤ Y₂ := (Proof162.le_of_le_sup_of_isPGroup_two hPN hP2 hLle hL3).trans
    inf_le_right
  have hm₁b : MeetsY4 A (lB A) Lb Y₁ := Res162.meetsY4_of_alternating_ten hb' hT.1 hY₁ φ₁
    h.zpowers_mem_omegaA h.mem_lA hm₁
  have hconf' : Conf162 A (lB A) b Lb Y₂ Y₁ S := ⟨hmax.symm, hLbY₂, hm₂, hm₁b⟩
  have h14b := hb'.toSec14Std
  exact Res162.false_of_le_normalizer_of_conf162 hb' hconf' (h1444 G A b Lb h14b)
    (h146 G A b Lb h14b) (hbot G A b Lb h14b) (h142 G A b Lb h14b) ⟨φLb⟩ φ₂
    (hLbY₁.trans Subgroup.le_normalizer)

end Res162d

open Proof162 Res162d in
theorem step162A7Other_of_choice
    (h1514 : Item1514R) (h153 : Item153MainR)
    (hobs : Claim153ObsR) (hn : Claim153NormalR) (h1411 : Item1411_1R)
    (hWloc : Claim1411NonsolvWR) (h155 : Item155R) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (h142 : Concl142S14) (hF : Step162ChoiceFaithful)
    (hC : Step162A7OtherSevenC) : Step162A7Other := by
  intro G _ _ A c L h Y₁ Y₂ S hmax hLY₁ hm₁ h7 hW4 hT hY₁t hnW b Lb hb hLb hbc hm₂ hY₂7 hsc
  obtain ⟨φ₂⟩ := hY₂7
  rcases hY₁t with ⟨⟨φ₁⟩⟩ | ⟨⟨φ₁⟩⟩
  swap
  · exact false_of_other_ten h1444 h146 hbot h142 h hmax hLY₁ hm₁ h7 hT φ₁ hb hLb hm₂ φ₂
  obtain ⟨φL⟩ := h7
  have h14 := h.toSec14Std
  have hY₁ := hmax.1.mem₁
  have hY₂ := hmax.1.mem₂
  have hcovL : L = (Y₁ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L := by
    rw [inf_eq_right.mpr hLY₁, sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)]
  have hcov₁ := Res162.eq_sup_of_forall_mem (Res162.exists_mem_inf_of_cover hcovL
    (by rw [Nat.card_congr φ₁.toEquiv, Nat.card_congr φL.toEquiv]))
  have hY₁L : Y₁ ≤ L ⊔ CFSG.Open.pCoreOf 2 Y₁ := by
    rw [inf_eq_right.mpr hLY₁] at hcov₁
    exact hcov₁.le
  have hL4 : L ∈ scriptY4 A (lB A) := mem_scriptY4_of_cover h (h142 G A c L h14) hY₁.prop.1
    hLY₁ hY₁L
  obtain ⟨Sc, -, hSc⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2)))
    (bot_mem_scriptQPi_two (A := A) _)
  obtain ⟨K, hK, hLK, hScK⟩ := exists_choice_member h (h155 G A c L h) hF hL4 ⟨φL⟩ hY₁ hLY₁ φ₁ hSc
  have hScQ : Sc ∈ scriptQPi A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2) :=
    ⟨⟨hSc.prop.1.1, hScK⟩, hSc.prop.2⟩
  obtain ⟨T, hScT, hT'⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))) hScQ
  have h153' := h153 G A c L h
  have hobs' := hobs G A c L h
  have hTG := mem_qStarTop_of_mem_qStarN h153' hobs' hK hT'
  have hSG := mem_qStarTop_of_mem_qStarN h153' hobs' hY₁ hmax.1.s₁
  obtain ⟨w, hw, hSw⟩ := h1411 G A c L h T hTG S hSG
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hw).1
  have hzc : Subgroup.zpowers (w * c * w⁻¹) =
      (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hcΩ : Subgroup.zpowers (w * c * w⁻¹) ∈ omegaA A := by
    rw [hzc]
    exact (map_conj_mem_omegaA_iff hwA).mpr h.zpowers_mem_omegaA
  have hLmem : L.map (MulAut.conj w).toMonoidHom ∈ lA A (w * c * w⁻¹) :=
    (map_conj_mem_lA_iff hwA).mpr h.mem_lA
  have hR' : Sec15R G A (w * c * w⁻¹) (L.map (MulAut.conj w).toMonoidHom) :=
    sec15R_of_point h hcΩ hLmem
  have hK' : K.map (MulAut.conj w).toMonoidHom ∈ scriptY0Star A (lB A) :=
    map_conj_mem_scriptY0Star hwA hK
  have hLK' : L.map (MulAut.conj w).toMonoidHom ≤ K.map (MulAut.conj w).toMonoidHom :=
    Subgroup.map_mono hLK
  have hSK' : S ∈ scriptQPiStar A (lB A)
      (Subgroup.normalizer ((K.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G))
      (piOf 2) := by
    have h1 := Sec17.HeadProof.map_conj_mem_scriptQPiStar hwA hT'
    rw [Subgroup.map_equiv_normalizer_eq, ← hSw] at h1
    exact h1
  have hScw : Sc.map (MulAut.conj w).toMonoidHom ∈ scriptQPiStar A (lB A)
      (Subgroup.normalizer (Subgroup.zpowers (w * c * w⁻¹) : Set G)) (piOf 2) := by
    have h1 := Sec17.HeadProof.map_conj_mem_scriptQPiStar hwA hSc
    rwa [Subgroup.map_equiv_normalizer_eq, ← hzc] at h1
  have hchoice : Choice162 A (w * c * w⁻¹) S :=
    choice162_of_le hR' hSG.prop hScw (by rw [hSw]; exact Subgroup.map_mono hScT)
  have hpartner : ∃ Y' : Subgroup G, (Y' = Y₁ ∨ Y' = Y₂) ∧
      ¬ ∃ x ∈ xA A, K.map (MulAut.conj w).toMonoidHom = Y'.map (MulAut.conj x).toMonoidHom := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x₁, hx₁, h₁⟩ := hcon Y₁ (Or.inl rfl)
    obtain ⟨x₂, hx₂, h₂⟩ := hcon Y₂ (Or.inr rfl)
    obtain ⟨y₁, hy₁, h₁'⟩ := conj_symm hx₁ h₁
    exact hmax.1.not_conj (conj_trans hy₁ hx₂ h₁' h₂)
  obtain ⟨Y', hY'eq, hnc'⟩ := hpartner
  obtain ⟨p, Lp, hp, hLp, hmp, hscp, φY', hY'mem, hS'⟩ : ∃ (p : G) (Lp : Subgroup G),
      Subgroup.zpowers p ∈ omegaA A ∧ Lp ∈ lA A p ∧ MeetsY4 A (lB A) Lp Y' ∧
      Late.sectionCentralizer A Y' (CFSG.Open.pCoreOf 2 Y') = (Subgroup.zpowers p : Set G) ∧
      Nonempty (↥Y' ⧸ CFSG.pCore 2 ↥Y' ≃* alternatingGroup (Fin 7)) ∧
      Y' ∈ scriptY0Star A (lB A) ∧
      S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Y' : Set G)) (piOf 2) := by
    rcases hY'eq with rfl | rfl
    · exact ⟨c, L, h.zpowers_mem_omegaA, h.mem_lA, hm₁,
        Res162.sectionCentralizer_eq_zpowers_of_meetsY4 h hY₁ hm₁ φ₁, ⟨φ₁⟩, hY₁, hmax.1.s₁⟩
    · exact ⟨b, Lb, hb, hLb, hm₂, hsc, ⟨φ₂⟩, hY₂, hmax.1.s₂⟩
  obtain ⟨φY'⟩ := φY'
  have hmax' : MaxCE162 A (lB A) (K.map (MulAut.conj w).toMonoidHom) Y' S S :=
    ⟨⟨hK', hY'mem, hSK', hS', hmax.1.ne_bot, hnc'⟩, hmax.2⟩
  have hm' : MeetsY4 A (lB A) (L.map (MulAut.conj w).toMonoidHom)
      (K.map (MulAut.conj w).toMonoidHom) :=
    ⟨_, map_conj_mem_scriptY4 hwA hL4, le_inf le_rfl hLK'⟩
  have hnW' := not_conj_normalizer hR' (h153 G A _ _ hR') (hobs G A _ _ hR') (hn G A _ _ hR')
    (hWloc G A _ _ hR') hmax'.1
  have hTw : TransOmegaThree A (w * c * w⁻¹) := transOmegaThree_of_conj hwA hT hzc
  have hne : omegaA A ≠ {Subgroup.zpowers (w * c * w⁻¹)} := omegaA_ne_singleton_of_trans hTw
  rcases h1514 G A _ _ hR' _ hK' hm' with ⟨-, -, hΩ, -⟩ | ⟨h7', hW4', -, hKt⟩ |
      ⟨-, -, -, hΩ, -⟩
  · exact hne hΩ
  · by_cases hpc : Subgroup.zpowers p = Subgroup.zpowers (w * c * w⁻¹)
    ·
      have hLpL := eq_of_zpowers_eq hR' hp hLp hpc
      have hconf : Conf162 A (lB A) (w * c * w⁻¹) (L.map (MulAut.conj w).toMonoidHom)
          (K.map (MulAut.conj w).toMonoidHom) Y' S := ⟨hmax', hLK', hm', hLpL ▸ hmp⟩
      have h14' := hR'.toSec14Std
      exact Res162b.false_of_conf162 hR' hconf (not_normalizer_le_of_trans hcΩ hTw)
        (h1514 G A _ _ hR') (h1444 G A _ _ h14') (h146 G A _ _ h14') (hbot G A _ _ h14')
        (h142 G A _ _ h14')
    · rcases hKt with ⟨⟨φK⟩⟩ | ⟨⟨φK⟩⟩
      · exact hC G A _ _ hR' _ Y' S hmax' hLK' hm' h7' hW4' hTw ⟨φK⟩ hnW' hchoice p Lp hp hLp
          hpc hmp ⟨φY'⟩ hscp
      · exact false_of_other_ten h1444 h146 hbot h142 hR' hmax' hLK' hm' h7' hTw φK hp hLp hmp
          φY'
  · exact hne hΩ

theorem step162A7OtherSeven_of_other (h : Step162A7Other) : Step162A7OtherSeven :=
  fun G _ _ A c L hR Y₁ Y₂ S hmax hLY₁ hm₁ h7 hW4 hT hY₁ hnW b Lb hb hLb hbc hm₂ hY₂ hsc =>
    h G A c L hR Y₁ Y₂ S hmax hLY₁ hm₁ h7 hW4 hT (Or.inl hY₁) hnW b Lb hb hLb hbc hm₂ hY₂ hsc

theorem step162A7OtherSeven_of_choice
    (h1514 : Item1514R)
    (h153 : Item153MainR) (hobs : Claim153ObsR) (hn : Claim153NormalR) (h1411 : Item1411_1R)
    (hWloc : Claim1411NonsolvWR) (h155 : Item155R) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (h142 : Concl142S14) (hF : Step162ChoiceFaithful)
    (hC : Step162A7OtherSevenC) : Step162A7OtherSeven :=
  step162A7OtherSeven_of_other (step162A7Other_of_choice h1514 h153 hobs hn h1411 hWloc h155
    h1444 h146 hbot h142 hF hC)

end CFSG.RankThree.PartTwo.Sec16
