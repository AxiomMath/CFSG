module

public import CFSG.RankThree.PartTwo.Sec15.Item153
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.Sporadic.J2
import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def IsType156 (Y : Subgroup G) : Prop :=
  Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∨
    Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6)) ∨
    Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON

structure Data156 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (Y : Subgroup G) (c₀ : G)
    (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G) : Prop where
  omega : Subgroup.zpowers c₀ ∈ omegaA A
  mem_lA : L₀ ∈ lA A c₀
  hj : Nonempty (↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀ ≃* CFSG.Blueprint.NativeSporadic.J2)
  mem_x : X₁ ∈ scriptY0 A LB
  le_x : X₁ ≤ Y
  type_x : Nonempty (↥X₁ ⧸ CFSG.pCore 2 ↥X₁ ≃* alternatingGroup (Fin 5)) ∨
    Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6))
  mem_d : d ∈ A
  ne_d : d ≠ 1
  central_d : IsThreeCentralIn L₀ d
  cent : Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁) =
    (Subgroup.closure {c₀, d} : Set G)
  choice : Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6)) ∨
    Y = X₁ ⊔ CFSG.Open.pCoreOf 2 Y

@[expose] def Step156ON (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON →
      ∃ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁

@[expose] def Step156D (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6))) →
    ∀ (c₀ : G) (L₀ : Subgroup G), Subgroup.zpowers c₀ ∈ omegaA A → L₀ ∈ lA A c₀ →
      Nonempty (↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀ ≃* CFSG.Blueprint.NativeSporadic.J2) →
      c₀ ∈ Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) →
      ∃ d : G, d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn L₀ d ∧
        Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) = (Subgroup.closure {c₀, d} : Set G)

@[expose] def KS156HJGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    ∀ Y ∈ scriptY0Star A (lB A), IsType156 Y →
    ∀ (d : G) (X₁ : Subgroup G), Data156 A (lB A) Y c L d X₁ →
      omegaA A = {Subgroup.zpowers c} →
      ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), S ≤ Subgroup.normalizer (Y : Set G) →
        S ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∈
          scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2) →
        L ≤ S ⊔ Y

@[expose] def Step156Meet (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, IsType156 Y →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A = {Subgroup.zpowers c₀} → L₀ ≤ Subgroup.normalizer (Y : Set G) →
        3 ∣ Nat.card ↥(L₀ ⊓ Y)

@[expose] def Step156CQ (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, IsType156 Y →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A ≠ {Subgroup.zpowers c₀} →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ∀ F : Subgroup G, F ≤ Subgroup.closure {c₀, d} → Nat.card F = 3 →
        F ≠ Subgroup.zpowers d →
          CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (F : Set G) = ⊥

theorem card_theta_dvd_card_quot {L Y : Subgroup G} (hLY : L ≤ Y) :
    Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥L →* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hLY) with hf
  have hθ := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hker2 : IsPGroup 2 f.ker := by
    intro x
    have hx : (Subgroup.inclusion hLY (x : ↥L)) ∈ CFSG.pCore 2 ↥Y := by
      have h1 : f x = 1 := x.2
      change QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (Subgroup.inclusion hLY (x : ↥L)) = 1 at h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥Y)) ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subgroup.inclusion_injective hLY ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hkerθ : f.ker ≤ aschbacherSolvableCore 3 ↥L := by
    refine hθ.2.2.2.1 f.ker (MonoidHom.normal_ker f) ?_ ?_
    · have := hker2.isNilpotent
      infer_instance
    · intro h3
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker2
      rw [hk] at h3
      have := Nat.prime_three.dvd_of_dvd_pow h3
      omega
  have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = (aschbacherSolvableCore 3 ↥L).index :=
    rfl
  rw [h1]
  refine (Subgroup.index_dvd_of_le hkerθ).trans ?_
  rw [Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card _

theorem not_dvd_card_of_isType156 {Y : Subgroup G}
    (htype : IsType156 Y) : ¬ 604800 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  rcases htype with he | h6 | hON
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_five]
    norm_num
  · rw [card_of_isTripleCover h6, card_alternatingGroup_six]
    norm_num
  · rw [card_of_isTripleCover hON, CFSG.Sporadic.ON.card_ON]
    norm_num

theorem not_mem_zpowers_of_data156 {A : Subgroup G} {c₀ : G}
    {L₀ : Subgroup G} (h₀ : Sec14Std G A c₀ L₀) {LB : Subgroup G → Subgroup G}
    {Y X₁ : Subgroup G} {d : G} (D : Data156 A LB Y c₀ L₀ d X₁) :
    d ∉ Subgroup.zpowers c₀ := by
  obtain ⟨φ⟩ := D.hj
  have hL : L₀ ∈ thetaComponentsAt 3 c₀ := D.mem_lA.1
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hL
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hs : IsSimpleGroup (↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀) := φ.isSimpleGroup
  have hnab : ∃ a b : ↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a, b, fun h => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
  have hZ := center_eq_bot_of_isSimpleGroup hs hnab
  have hcL : c₀ ∉ L₀ := not_mem_of_center_eq_bot h₀.toSec13Data hZ
  intro hdc
  apply hcL
  have hdL : d ∈ L₀ := D.central_d.1
  have hd3 : d ^ 3 = 1 := h₀.toSec13Data.isElemAbelian.2 d D.mem_d
  have hdord : orderOf d = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hd3 D.ne_d
  have hle : Subgroup.zpowers d ≤ Subgroup.zpowers c₀ := Subgroup.zpowers_le.mpr hdc
  have hcard : Nat.card (Subgroup.zpowers c₀) ≤ Nat.card (Subgroup.zpowers d) := by
    have h1 : Nat.card (Subgroup.zpowers c₀) = 3 := h₀.toSec13Data.zpowers_mem_omegaA.2.1
    have h2 : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hdord]
    rw [h1, h2]
  have heq : Subgroup.zpowers d = Subgroup.zpowers c₀ := Subgroup.eq_of_le_of_card_ge hle hcard
  have hc : c₀ ∈ Subgroup.zpowers d := heq ▸ Subgroup.mem_zpowers c₀
  exact (Subgroup.zpowers_le.mpr hdL) hc

theorem false_of_centralizer_eq_bot (hchar : CFSG.Assembly.IsCharTwoType G) {A M : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hM : IsMaximalTwoLocal M) (hAM : A ≤ M) {c d : G}
    (hc : c ∈ A) (hc3 : Nat.card (Subgroup.zpowers c) = 3) (hd : d ∈ A) (hd1 : d ≠ 1)
    (hdc : d ∉ Subgroup.zpowers c)
    (hC : ∀ F : Subgroup G, F ≤ Subgroup.closure {c, d} → Nat.card F = 3 →
      F ≠ Subgroup.zpowers d → CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (F : Set G) = ⊥) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Subgroup.closure ({c, d} : Set G) with hE
  have hEA : E ≤ A := by
    rw [hE, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hc
    · exact hd
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := fun x hx => hA.2 x (hEA hx)
  have hEab : CFSG.Open.IsElemAbelian 3 E :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from congrArg Subtype.val
      (hA.1.is_comm.comm ⟨x, hEA x.2⟩ ⟨y, hEA y.2⟩))⟩⟩, hE3⟩
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE3 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  have hcE : Subgroup.zpowers c ≤ E :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert c _))
  have hdE : d ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
  have hk2 : 2 ≤ k := by
    have hdvd : Nat.card (Subgroup.zpowers c) ∣ Nat.card E := Subgroup.card_dvd_of_le hcE
    rw [hc3, hk] at hdvd
    have hk1 : k ≠ 0 := by
      rintro rfl
      norm_num at hdvd
    by_contra hk2
    have hk1' : k = 1 := by omega
    have hcard : Nat.card E ≤ Nat.card (Subgroup.zpowers c) := by rw [hk, hc3, hk1', pow_one]
    exact hdc ((Subgroup.eq_of_le_of_card_ge hcE hcard).symm ▸ hdE)
  have hE9 : 3 ^ (1 + 1) ≤ Nat.card E := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk2
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) :=
    (hEA.trans hAM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M
  have hcop : Nat.Coprime 3 (Nat.card Q) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three E Q hEab hE9 hEQ hcop
  have hQd : Q ≤ Subgroup.centralizer (Subgroup.zpowers d : Set G) := by
    rw [← hgen]
    refine iSup₂_le fun F hF => ?_
    by_cases hFd : F = Subgroup.zpowers d
    · rw [hFd]
      exact inf_le_right
    · rw [hC F hF.1 (by rw [hF.2, pow_one]) hFd]
      exact bot_le
  have hdM : d ∈ M := hAM hd
  have hMc : IsCharacteristicP 2 ↥M := CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal hchar hM.1
  have hdC : (⟨d, hdM⟩ : ↥M) ∈
      Subgroup.centralizer ((CFSG.pCore 2 ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQ : (y : G) ∈ Q := by
      rw [hQ, CFSG.Open.pCoreOf]
      exact ⟨y, hy, rfl⟩
    have hyd := Subgroup.mem_centralizer_iff.mp (hQd hyQ) d (Subgroup.mem_zpowers d)
    exact Subtype.ext hyd.symm
  have hdO : (⟨d, hdM⟩ : ↥M) ∈ CFSG.pCore 2 ↥M := hMc hdC
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥M)) ⟨_, hdO⟩
  have hdj : d ^ 2 ^ j = 1 := by
    have := congrArg (fun z : CFSG.pCore 2 ↥M => ((z : ↥M) : G)) hj
    simpa using this
  have hd3 : d ^ 3 = 1 := hA.2 d hd
  apply hd1
  have hco : Nat.Coprime (2 ^ j) 3 := Nat.Coprime.pow_left j (by norm_num)
  have h1 := (pow_gcd_eq_one (a := d)).mpr ⟨hdj, hd3⟩
  rwa [hco.gcd_eq_one, pow_one] at h1

theorem false_of_omegaA_ne {A : Subgroup G} {c₀ : G}
    {L₀ : Subgroup G} (h₀ : Sec14Std G A c₀ L₀) (hCQ : Step156CQ A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (htype : IsType156 Y) {d : G} {X₁ : Subgroup G}
    (D : Data156 A (lB A) Y c₀ L₀ d X₁) (hΩ : omegaA A ≠ {Subgroup.zpowers c₀}) : False := by
  obtain ⟨M, hM⟩ := exists_mem_maximalTwoLocalsContaining hY.prop.2
  have hAM : A ≤ M := fun a ha => hM.2 (Subgroup.mem_sup_right ha)
  have hc := h₀.toSec13Data.zpowers_mem_omegaA
  exact false_of_centralizer_eq_bot h₀.toTheoremFourHyp.charTwoType
    h₀.toSec13Data.isElemAbelian hM.1 hAM (Subgroup.zpowers_le.mp hc.1) hc.2.1 D.mem_d D.ne_d
    (not_mem_zpowers_of_data156 h₀ D) (hCQ Y hY htype c₀ L₀ d X₁ D hΩ M hM)

end CFSG.RankThree.PartTwo.Sec15
