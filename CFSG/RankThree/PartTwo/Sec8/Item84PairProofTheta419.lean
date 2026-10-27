module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofJComp
public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofJ3
public import CFSG.RankThree.PartTwo.Sec4.Statements423
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofRest
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofXNormal
public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofTools
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Blueprint

namespace CFSG.RankThree.PartTwo.Sec4

@[expose] def IsType419Theta (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, ChevalleyExceptionalModel X .G2 2 n) ∨ Nonempty (X ≃* projSU 3 3 1) ∨
    (∃ n : ℕ, ReeTitsModel X .twistedF4 2 n) ∨ ReeTitsModel X .Tits 2 1 ∨
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (X ≃* projSp 2 (GaloisField 2 n))) ∨
    Nonempty (X ≃* alternatingGroup (Fin 6)) ∨
    (∃ m : ℕ, Odd m ∧ Nonempty (X ≃* projSU 3 2 m))

section Item419Theta


@[expose] def Item4_19ThetaJ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G →
    ∀ L ∈ thetaComponents 3 G, ∀ (A : Subgroup G) (c : G),
      Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A →
      Nat.card A = 3 ^ 4 →
      Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
        (Subgroup.zpowers c : Set G) →
      orderOf c = 3 →
    ∀ a ∈ A, a ∉ Subgroup.zpowers c →
    ∀ K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({a} : Set G)),
      IsType419Theta ↥(thetaImage K) →
      (∀ A₀ ∈ partTwoF G, Nat.card A₀ ≤ 3 ^ 4) →
        (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField) ∨
        (Nonempty (↥(thetaImage K) ≃* alternatingGroup (Fin 6)) ∧
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 9)) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 3 (GaloisField 2 1)))) ∨
        (Nonempty (↥(thetaImage K) ≃* alternatingGroup (Fin 6)) ∧
          Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸
            Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* NativeSporadic.J3))

end Item419Theta

end CFSG.RankThree.PartTwo.Sec4

namespace CFSG.RankThree.PartTwo.Sec8

namespace Item84Pair

theorem card_le_of_mem_partTwoF_subgroup {G : Type} [Group G] [Finite G]
    (h611 : Sec6.Item6_11_1) (hst : PartTwoStanding G) (H : Subgroup G) :
    ∀ A₀ ∈ partTwoF H, Nat.card A₀ ≤ 3 ^ 4 := by
  intro A₀ hA₀
  obtain ⟨hA₀ab, -, E₀, ⟨hE₀ab, hE₀card, T, hT1, hT2, hE₀T⟩, hE₀A₀⟩ := hA₀
  set E₂ := E₀.map H.subtype with hE₂
  set T₂ := T.map H.subtype with hT₂
  have hT₂1 : T₂ ≠ ⊥ := by
    intro hbot
    apply hT1
    rwa [hT₂, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at hbot
  have hE₂N : E₂ ≤ Subgroup.normalizer (T₂ : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem _ (hE₀T he))
  have hE₂E : E₂ ∈ partTwoE G :=
    ⟨Item812Res4.isElemAbelian_map _ hE₀ab, by
      rw [hE₂, Subgroup.card_map_of_injective H.subtype_injective, hE₀card], T₂, hT₂1,
      hT2.map _, hE₂N⟩
  have hA₀G : CFSG.Assembly.IsElemAbelian 3 (A₀.map H.subtype) :=
    Item812Res4.isElemAbelian_map _ hA₀ab
  obtain ⟨A₁, hA₀A₁, hA₁max⟩ :=
    Finite.exists_le_maximal (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) hA₀G
  have hA₁F : A₁ ∈ partTwoF G :=
    ⟨hA₁max.prop, fun B hB hAB => le_antisymm (hA₁max.2 hB hAB) hAB, E₂,
      hE₂E, (Subgroup.map_mono hE₀A₀).trans hA₀A₁⟩
  have hrk := h611 G hst A₁ hA₁F
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (Item812Res4.isPGroup_of_isElemAbelian hA₁max.prop)
  have hm4 : m ≤ 4 := by
    have : m ≤ CFSG.Open.pRank 3 A₁ :=
      le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three A₁)
        ⟨A₁, le_rfl, hA₁max.prop, hm⟩
    omega
  have hle : Nat.card (A₀.map H.subtype) ≤ Nat.card A₁ := Subgroup.card_le_of_le hA₀A₁
  rw [Subgroup.card_map_of_injective H.subtype_injective, hm] at hle
  calc Nat.card A₀ ≤ 3 ^ m := hle
    _ ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hm4

end Item84Pair

section Final


open Item84Pair

theorem kF89J_of_theta (h419 : Sec4.Item4_19ThetaJ3) (hJ3 : KF89NotJ3) (hcent : KF89JCentA)
    (hcomp : KF89JComp) (h84 : Pair84A) (h611 : Sec6.Item6_11_1) : KF89J := by
  intro G _ _ A c L a b X n h Y hY hIJ h8
  set H := Subgroup.centralizer ({a} : Set G) with hHdef
  obtain ⟨Y₀, hY₀, rfl⟩ := hY
  set N := aschbacherSolvableCore 3 ↥H with hNdef
  set π := QuotientGroup.mk' N with hπ
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  have hS4 : SectionFourHyp H :=
    hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG h.a_ne_one)
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have haA : a ∈ A := h.a_mem
  have ha1 : a ≠ 1 := h.a_ne_one
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb1 : b ≠ 1 := h.isGammaIndex.2.1
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hAH : A ≤ H := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc x hx a haA)
  have haH : a ∈ H := hAH haA
  have hbH : b ∈ H := hAH hbA
  set AH := A.subgroupOf H with hAHdef
  have hAHab : CFSG.Assembly.IsElemAbelian 3 AH := Item812Res4.isElemAbelian_subgroupOf H hAab
  have hXb : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hX : X ≤ Subgroup.centralizer ({b} : Set G) := by
    obtain ⟨X', -, hX'⟩ := hXb
    rw [← hX']
    exact Subgroup.map_subtype_le X'
  obtain ⟨hKcomp, hKtype, hKA6⟩ := hcomp G A c L a b X n h Y₀ hY₀ hIJ hbH
  have hmax : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) AH := by
    refine ⟨hAHab, fun B hB hAB => ?_⟩
    have hBG : CFSG.Assembly.IsElemAbelian 3 (B.map H.subtype) :=
      Item812Res4.isElemAbelian_map _ hB
    have hAB' : A ≤ B.map H.subtype := fun x hx =>
      ⟨⟨x, hAH hx⟩, hAB (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have heq := h.mem_partTwoF.2.1 _ hBG hAB'
    intro x hx
    have hx' : (x : G) ∈ A := by
      rw [← heq]
      exact ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr hx'
  have hcard : Nat.card AH = 3 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, h.card_eq]
    norm_num
  have hθY : (aschbacherSolvableCore 3 ↥Y₀).map Y₀.subtype ≤ N := by
    have hint := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hY₀.2.1
    intro y hy
    have hy' : y ∈ inSubgroup (aschbacherSolvableCore 3) Y₀ := hy
    rw [hint] at hy'
    exact hy'.2
  have hsec : Late.sectionCentralizer AH Y₀ ((aschbacherSolvableCore 3 ↥Y₀).map Y₀.subtype) =
      (Subgroup.zpowers (⟨a, haH⟩ : H) : Set H) := by
    ext x
    constructor
    · rintro ⟨hxA, hxY⟩
      have hxa := hcent G A c L a b X n h Y₀ hY₀ hIJ x (Subgroup.mem_subgroupOf.mp hxA)
        (fun y hy => hθY (hxY y hy))
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxa
      refine ⟨k, Subtype.ext ?_⟩
      simpa using hk
    · rintro ⟨k, rfl⟩
      refine ⟨AH.zpow_mem (Subgroup.mem_subgroupOf.mpr haA) k, fun y _ => ?_⟩
      have hc : (⟨a, haH⟩ : H) ^ k * y = y * (⟨a, haH⟩ : H) ^ k := by
        have h1 : Commute (⟨a, haH⟩ : H) y := Subtype.ext
          (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
        exact (h1.zpow_left k).eq
      have h1 : (⟨a, haH⟩ : H) ^ k * y * ((⟨a, haH⟩ : H) ^ k)⁻¹ * y⁻¹ = 1 := by
        rw [hc]
        group
      change (⟨a, haH⟩ : H) ^ k * y * ((⟨a, haH⟩ : H) ^ k)⁻¹ * y⁻¹ ∈ _
      rw [h1]
      exact Subgroup.one_mem _
  have hord : orderOf (⟨a, haH⟩ : H) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime ha3 ha1
  have hb'A : (⟨b, hbH⟩ : H) ∈ AH := Subgroup.mem_subgroupOf.mpr hbA
  have hb'c : (⟨b, hbH⟩ : H) ∉ Subgroup.zpowers (⟨a, haH⟩ : H) := by
    rintro ⟨k, hk⟩
    have hbk : b ∈ Subgroup.zpowers a := ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hab : a ∈ Subgroup.zpowers b := by
      have hle : Subgroup.zpowers b ≤ Subgroup.zpowers a := (Subgroup.zpowers_le).mpr hbk
      have heq : Subgroup.zpowers b = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ha3 ha1,
            orderOf_eq_prime hb3 hb1])
      rw [heq]
      exact Subgroup.mem_zpowers a
    have hout : Sec4.InducesOuterTheta a X := by
      rcases h84 G A c L a b X n h with h' | h'
      · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
      · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
    obtain ⟨haN, hnot⟩ := hout
    apply hnot
    have hay : ∀ y ∈ X, a * y = y * a := by
      intro y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hab
      have hyb : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp (hX hy)
      exact (Commute.zpow_left (show Commute b y from hyb.symm) j).eq
    rw [KFacts.thetaQuotMulAut_compAction_eq_one haN hay]
    exact ⟨1, map_one _⟩
  set J := sec8J X a with hJdef
  have hJH : J ≤ H := (Item87Proof.residual_le _).trans inf_le_right
  have hK'le : imageModTheta H J ≤
      Y₀.map π ⊓ Subgroup.centralizer ({π ⟨b, hbH⟩} : Set (H ⧸ N)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxJ : (x : G) ∈ J := Subgroup.mem_subgroupOf.mp hx
    have hxXC : (x : G) ∈ X ⊓ Subgroup.centralizer ({a} : Set G) := Item87Proof.residual_le _ hxJ
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : (x : G) ∈ Y₀.map H.subtype := hIJ (Subgroup.mem_sup_right hxJ)
      obtain ⟨y, hy, hyx⟩ := h1
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact ⟨y, hy, rfl⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hX hxXC.1)
  have hK'q : IsQuasisimple (imageModTheta H J) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK'le) hKcomp.1
  have hJq : IsQuasisimple (J ⧸ aschbacherSolvableCore 3 J) :=
    Item87Proof.isQuasisimple_quot_of_imageModTheta hJH hK'q
  have hJmem : J ∈ thetaComponentsIn
      (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Item87Proof.mem_thetaComponentsIn_residual hXb hJq
  have hJY : J ≤ Y₀.map H.subtype := le_sup_right.trans hIJ
  have hJb : J ≤ Subgroup.centralizer ({b} : Set G) :=
    (Item87Proof.residual_le _).trans (inf_le_left.trans hX)
  have hYH : Y₀.map H.subtype ≤ H := Subgroup.map_subtype_le Y₀
  have hJmem' : J ∈ thetaComponentsIn
      (Y₀.map H.subtype ⊓ Subgroup.centralizer ({b} : Set G)) := by
    obtain ⟨-, hJ''⟩ := mem_thetaComponentsIn_iff.mp hJmem
    refine mem_thetaComponentsIn_iff.mpr ⟨le_inf hJY hJb, ?_⟩
    exact PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three (le_inf hJY hJb)
      (le_inf inf_le_right (inf_le_left.trans hYH)) hJ''
  have hM'map : (Y₀ ⊓ Subgroup.centralizer ({(⟨b, hbH⟩ : H)} : Set H)).map H.subtype =
      Y₀.map H.subtype ⊓ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,
      CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton H ⟨b, hbH⟩,
      ← inf_assoc, inf_eq_left.mpr hYH]
  have hK : J.subgroupOf H ∈
      thetaComponentsIn (Y₀ ⊓ Subgroup.centralizer ({(⟨b, hbH⟩ : H)} : Set H)) :=
    Item87Proof.subgroupOf_mem_thetaComponentsIn hM'map hJmem'
  have htype : Sec4.IsType419Theta ↥(Sec4.thetaImage (J.subgroupOf H)) := hKtype
  have hF : ∀ A₀ ∈ partTwoF H, Nat.card A₀ ≤ 3 ^ 4 :=
    card_le_of_mem_partTwoF_subgroup h611 h.toPartTwoStanding H
  set eY : Y₀ ⧸ aschbacherSolvableCore 3 Y₀ ≃*
      ↥(Y₀.map H.subtype) ⧸ aschbacherSolvableCore 3 ↥(Y₀.map H.subtype) :=
    Item812Res2.thetaQuotEquiv (Y₀.equivMapOfInjective _ H.subtype_injective) with heY
  rcases h419 H hS4 Y₀ hY₀ AH ⟨a, haH⟩ hmax hcard hsec hord ⟨b, hbH⟩ hb'A hb'c
      (J.subgroupOf H) hK htype hF with hk | ⟨hA6, hL9⟩ | ⟨hA6, hJ⟩
  · rcases hk with hk | hk
    · exact absurd (Or.inl (Sec13.inducesStdKind_sub H Y₀ hk)) h8.2
    · exact absurd (Or.inr (Sec13.inducesStdKind_sub H Y₀ hk)) h8.2
  · refine ⟨?_, hKA6 hA6⟩
    rcases hL9 with h9 | h6
    · obtain ⟨e9⟩ := h9
      exact Or.inl ⟨eY.symm.trans e9⟩
    · obtain ⟨e6⟩ := h6
      exact Or.inr ⟨eY.symm.trans e6⟩
  · exact absurd (Item812Res5.nonempty_center_quot_of_mulEquiv eY hJ)
      (hJ3 G A c L a b X n h _ ⟨Y₀, hY₀, rfl⟩ hIJ h8 (hKA6 hA6))


theorem kF89J_of_theta_ne (h419 : Sec4.Item4_19ThetaJ3) (hJ3 : KF89NotJ3) (hcent : KF89JCentA)
    (hcomp : KF89JCompNe) (h84 : Pair84A) (h611 : Sec6.Item6_11_1) : KF89J :=
  kF89J_of_theta h419 hJ3 hcent (kF89JComp_of_ne hcomp kF87INontriv_holds h84) h84 h611

end Final

end CFSG.RankThree.PartTwo.Sec8
