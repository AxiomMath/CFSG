module

public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofA5
import CFSG.RankThree.PartTwo.Sec15.Item153TwinProofTools
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.Sporadic.ON
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof152Gen CFSG.RankThree.PartTwo.Sec15.Proof156

variable {G : Type} [Group G] [Finite G]

@[expose] def Step156CQA5D (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A ≠ {Subgroup.zpowers c₀} → ¬ L₀ ≤ Subgroup.normalizer (Y : Set G) →
      Nonempty (↥X₁ ⧸ CFSG.pCore 2 ↥X₁ ≃* alternatingGroup (Fin 5)) →
      Y = X₁ ⊔ CFSG.Open.pCoreOf 2 Y →
        Y ≤ Subgroup.centralizer ({d} : Set G) ∧
          CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) ≠ ⊥

@[expose] noncomputable def Step156CQA5DR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156CQA5D A (lB A)

namespace Proof153Twin2

omit [Finite G] in
theorem eq_bot_of_isPerfect_of_isSolvable' {H : Type*} [Group H] {J : Subgroup H}
    (hJp : Group.IsPerfect J) (hJs : Group.IsSolvable J) : J = ⊥ := by
  obtain ⟨n, hn⟩ := hJs.solvable
  have hd : ∀ k, derivedSeries J k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, hJp.commutator_eq_top]
  rw [hd n] at hn
  rw [eq_bot_iff]
  intro j hj
  have : (⟨j, hj⟩ : J) ∈ (⊤ : Subgroup J) := Subgroup.mem_top _
  rw [hn, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

omit [Finite G] in
theorem normal_subgroupOf_of_le_normalizer {K Y : Subgroup G}
    (hKY : K ≤ Subgroup.normalizer (Y : Set G)) : (Y.subgroupOf K).Normal := by
  refine ⟨fun n hn k => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := (Subgroup.mem_normalizer_iff.mp (hKY k.2) n).mp hn
  simpa using this

theorem false_of_le_normalizer_of_a5 {K Y D : Subgroup G}
    (hY5 : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)))
    (hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K))
    (h9 : 9 ∣ Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K))
    (hKY : K ≤ Subgroup.normalizer (Y : Set G)) (hDp : Group.IsPerfect D) (hDK : D ≤ K)
    (hDY : D ≤ Y) (hD1 : D ≠ ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hθs, hθc, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  have : (aschbacherSolvableCore 3 ↥K).Normal := Subgroup.normal_of_characteristic _
  set θ := aschbacherSolvableCore 3 ↥K with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hYn : (Y.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hKY
  have hNn : ((Y.subgroupOf K).map π).Normal := hYn.map _ (QuotientGroup.mk'_surjective θ)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hNn with hNt | hNc
  ·
    have h1 : Nat.card (↥K ⧸ θ) ∣ Nat.card (Y.subgroupOf K) := by
      have h := Subgroup.card_map_dvd (Y.subgroupOf K) π
      rwa [hNt, Subgroup.card_top] at h
    have h2 : Nat.card (Y.subgroupOf K) ∣ Nat.card Y := by
      rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨e⟩ := hY5
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Y)
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_five] at hcard
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥Y))
    have h9Y : 9 ∣ 60 * 2 ^ k := by
      rw [← hk, ← hcard]
      exact h9.trans (h1.trans h2)
    have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have := hcop.dvd_of_dvd_mul_right h9Y
    norm_num at this
  ·
    have : Group.IsPerfect ↥D := hDp
    have hD'p : Group.IsPerfect (D.subgroupOf K) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hDK).symm.toMonoidHom)
        (MulEquiv.surjective _)
    have hD'Y : D.subgroupOf K ≤ Y.subgroupOf K := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hDY (Subgroup.mem_subgroupOf.mp hx))
    have hmap : Group.IsPerfect ((D.subgroupOf K).map π) := Group.IsPerfect.map π
    have hle : (D.subgroupOf K).map π ≤ Subgroup.center (↥K ⧸ θ) :=
      (Subgroup.map_mono hD'Y).trans hNc
    have hbot : (D.subgroupOf K).map π = ⊥ := by
      have hc := Subgroup.isPerfect_iff.mp hmap
      calc (D.subgroupOf K).map π = ⁅(D.subgroupOf K).map π, (D.subgroupOf K).map π⁆ := hc.symm
        _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (hle.trans (Subgroup.center_le_centralizer _))
    have hDθ : D.subgroupOf K ≤ θ := by
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
      exact hbot
    have : Group.IsSolvable ↥θ := hθs
    have hDs : Group.IsSolvable (D.subgroupOf K) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hDθ)
    have h0 := eq_bot_of_isPerfect_of_isSolvable' hD'p hDs
    rw [Subgroup.subgroupOf_eq_bot] at h0
    exact hD1 (disjoint_self.mp (h0.mono_right hDK))

end Proof153Twin2

open Proof153Twin2

theorem step156CQA5_of
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Item142AllS14) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h152 : Item152 A (lB A)) (hD : Step156CQA5D A (lB A)) :
    Step156CQA5 A (lB A) := by
  intro Y hY hY5 c₀ L₀ d X₁ D hΩ hLN hX5 hYX
  obtain ⟨hYd, hO2⟩ := hD Y hY hY5 c₀ L₀ d X₁ D hΩ hLN hX5 hYX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := D.omega, mem_lA := D.mem_lA }
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA := h₀.isE27
  obtain ⟨hcA, hc3, -⟩ := zpowers_mem_omegaA_iff.mp D.omega
  have hc1 : c₀ ≠ 1 := by
    intro hc1
    rw [hc1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
    exact absurd hc3 (by norm_num)
  obtain ⟨hdL, S3, hdS, hSd⟩ := D.central_d
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L₀) Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 D.hj hdL D.ne_d S3 hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h₀.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h₀.isSimpleGroup h₀.nonabelian D.ne_d)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs D.hj hdL D.ne_d
    ⟨S3, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hcA D.mem_d hc1 D.mem_lA.1 hJq
  have h9K : 9 ∣ Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
    rcases h134 G A c₀ L₀ h₀.toSec13Data D.hj d D.mem_d D.ne_d ⟨_, hS⟩ K hK hJK with
      ⟨-, h6, -⟩ | ⟨-, h6, -⟩ | ⟨hON, -⟩
    · rw [card_of_isTripleCover h6, card_alternatingGroup_six]
      norm_num
    · rw [card_of_isTripleCover h6, card_alternatingGroup_six]
      norm_num
    · rw [card_of_isTripleCover hON, CFSG.Sporadic.ON.card_ON]
      norm_num
  have hKC : K ≤ Subgroup.centralizer ({d} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK
  have hKp : Group.IsPerfect K := Sec6.isPerfect_of_mem_thetaComponentsAt hK
  have hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hK
  set C := Subgroup.centralizer ({d} : Set G) with hC
  have hO2C : CFSG.Open.pCoreOf 2 C ≠ ⊥ := hO2
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 C : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) C) hO2C
  have hCN : C ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 C : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hAC : A ≤ C := fun a ha => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val
      (h₀.toSec13Data.isElemAbelian.1.is_comm.comm ⟨d, D.mem_d⟩ ⟨a, ha⟩)).symm
  obtain ⟨M', hle, hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hM'm : M' ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    ⟨hM', fun x hx => hle (hCN (sup_le hYd hAC hx))⟩
  have hKY : K ≤ Subgroup.normalizer (Y : Set G) :=
    Proof153Twin.le_normalizer_of_isPerfect_of_le h₀ h152 hY hM'm hKp
      ((hKC.trans hCN).trans hle)
  obtain ⟨hAX, -, -, hXq, -, -, -, -, hdC, -⟩ := facts_of_data156 D hA
  have hcov := cover_of_data156 h₀ (h142 G A c₀ L₀ h₀) D
  have hd3 : d ^ 3 = 1 := hA.1.2 d D.mem_d
  have hdXL : d ∈ Subgroup.normalizer ((X₁ ⊓ L₀ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hAX h₀.toSec13Data.le_normalizer D.mem_d
  have hW := map_subgroupOf_eq_top_of_le_sup inf_le_left hcov
  have hW' := map_inf_centralizer_eq_top inf_le_left hdXL hd3 hdC hW
  obtain ⟨D', hD'W, hD'p, hD'top⟩ := exists_isPerfect_cover hXq.1 hW'
  have hD'X : D' ≤ X₁ := hD'W.trans (inf_le_left.trans inf_le_left)
  have hD'L : D' ≤ L₀ := hD'W.trans (inf_le_left.trans inf_le_right)
  have hD'd : D' ≤ C := hD'W.trans inf_le_right
  have hD'K : D' ≤ K :=
    (Sec6.le_inSubgroup_perfectResidual_of_isPerfect hD'p (le_inf hD'L hD'd)).trans hJK
  have hD'1 : D' ≠ ⊥ := by
    intro h0
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hXq
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥X₁ ⧸ aschbacherSolvableCore 3 ↥X₁)
    have hxm : x ∈ (D'.subgroupOf X₁).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X₁)) :=
      hD'top ▸ Subgroup.mem_top x
    rw [h0, Subgroup.bot_subgroupOf, Subgroup.map_bot, Subgroup.mem_bot] at hxm
    exact hx hxm
  exact false_of_le_normalizer_of_a5 hY5 hKq h9K hKY hD'p hD'K (hD'X.trans D.le_x) hD'1

theorem step156CQA5R_of
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Item142AllS14) (h152 : Item152R) (hD : Step156CQA5DR) :
    Step156CQA5R :=
  fun G _ _ A c L hR => step156CQA5_of h134 h48 h142 hR.toSec14Std (h152 G A c L hR)
    (hD G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
