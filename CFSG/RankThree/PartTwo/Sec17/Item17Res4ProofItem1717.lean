module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res4ProofA10Q
public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofW
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofFrame
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofSyl
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofL3
public import CFSG.RankThree.PartTwo.Sec17.Item1721ProofRoute
import CFSG.RankThree.PartTwo.Sec17.Item17Q0Proof
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofComm
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofQ0

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] noncomputable def Item1717One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (h : Sec17Y1 G A c L Y₀ Y₁ S p P),
    omegaA A = {Subgroup.zpowers c} →
    letI := kerAO2_normal h.le_normalizer_y0
    S = (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) ∧
      (((IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
            Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))) ∧
          ∃ (a : G) (ha : a ∈ A), a ∈ L ∧ a ≠ 1 ∧
            imgY0 A Y₀ (S ⊓ Y₀) = oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha)) ∨
        (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
          (CFSG.Assembly.IsElemAbelian 2 (imgY0 A Y₀ (S ⊓ Y₀)) ∧
            Nat.card (imgY0 A Y₀ (S ⊓ Y₀)) = 16) ∧
          ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A), Subgroup.closure {a, b} = A ⊓ L ∧
            imgY0 A Y₀ (S ⊓ Y₀) =
              oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊔ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) ∧
            oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊓ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) = ⊥) ∨
        (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
          (∃ T : Sylow 2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)),
            Nonempty (↥(imgY0 A Y₀ (S ⊓ Y₀)) ≃*
              ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))))) ∧
          ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A) (d : G),
            Subgroup.closure {a, b} = A ⊓ L ∧ d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn L d ∧
            imgY0 A Y₀ (S ⊓ Y₀) =
              oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊔ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) ⊔
                imgY0 A Y₀ (S ⊓ Y₀ ⊓ Subgroup.centralizer {d})))

theorem types_of_item1715 (h1715 : Item1715) {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (hJ : ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) := by
  rcases h1715 G A c L Y₀ h with ⟨-, -, -, hL⟩ | ⟨-, hA7, -, -, -⟩
  · rcases hL with ⟨q, hq, -, hiso⟩ | hA7 | hM22 | hJ2
    · exact Or.inl ⟨q, 1, hq, le_rfl, hiso⟩
    · exact Or.inr (Or.inl hA7)
    · exact Or.inr (Or.inr hM22)
    · exact absurd hJ2 hJ
  · exact Or.inr (Or.inl hA7)

theorem claim1720Inner_of_one (h1717 : Item1717One) (h1715 : Item1715) (h142 : Concl142S14)
    (h166 : Item166S17) (hbot : Item145BotS17) (h168 : Item168S17) : Claim1720Inner := by
  intro G _ _ A c L Y₀ Y₁ S p P h
  have hs := h.toSec17Std
  rcases h1715 G A c L Y₀ hs with ⟨hΩ, -⟩ | ⟨-, ⟨φL⟩, ⟨φ⟩, -, hT⟩
  · exact (h1717 G A c L Y₀ Y₁ S p P h hΩ).1.le
  · obtain ⟨g, hP⟩ := Proof17Res4.exists_a10Pic hs φ φL hT.1
    have hSG := Proof1712.mem_qStar_top h (h166 G A c L Y₀ hs) (hbot G A c L Y₀ hs)
      (h168 G A c L Y₀ hs)
    exact Proof17Res4.le_sup_cQuot_of_a10 h hP (h142 G A c L hs.toSec14Std) (hs.qStar_le S hSG)

theorem mem_normalizer_inf_L_of_one {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L Y₀ Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G} (h : Sec17Y1 G A c L Y₀ Y₁ S p P)
    (h1717 : Item1717One) (hΩ : omegaA A = {Subgroup.zpowers c})
    (hO2 : CFSG.Open.pCoreOf 2 Y₀ ≤ S)
    (hJ : ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {t : G} (htL : t ∈ L) (htinv : ∀ x ∈ A ⊓ L, t * x * t⁻¹ = x⁻¹) :
    t ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  have hs := h.toSec17Std
  have := kerAO2_normal h.le_normalizer_y0
  have htY : t ∈ Y₀ := hs.le_y0 htL
  have himg : Proof1721.barY0 A Y₀ htY ∈ Subgroup.normalizer
      ((imgY0 A Y₀ (S ⊓ Y₀) : Subgroup _) : Set _) := by
    obtain ⟨-, hcase⟩ := h1717 G A c L Y₀ Y₁ S p P h hΩ
    rcases hcase with ⟨-, a, ha, haL, -, heq⟩ | ⟨-, -, a, ha, b, hb, hab, heq, -⟩ |
      ⟨hJ2, -⟩
    · rw [heq]
      exact Proof1721.mem_normalizer_oTwoCY0 htY ha (htinv a ⟨ha, haL⟩)
    · have haL : a ∈ A ⊓ L := hab ▸ Subgroup.subset_closure (Set.mem_insert a {b})
      have hbL : b ∈ A ⊓ L := hab ▸ Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
      rw [heq]
      exact mem_normalizer_sup (Proof1721.mem_normalizer_oTwoCY0 htY ha (htinv a haL))
        (Proof1721.mem_normalizer_oTwoCY0 htY hb (htinv b hbL))
    · exact absurd hJ2 hJ
  have hSY := Proof1721.mem_normalizer_inf_of_mk hO2 htY himg
  have hSL : S ⊓ L = (S ⊓ Y₀) ⊓ L := by rw [inf_assoc, inf_eq_right.mpr hs.le_y0]
  rw [hSL]
  exact Late.le_normalizer_inf (Subgroup.zpowers_le.mpr hSY)
    (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer htL)) (Subgroup.mem_zpowers t)

theorem claim1721T_of_one
    (h1717 : Item1717One) (h1715 : Item1715) (h142 : Concl142S14)
    (hO2 : Claim17O2Y0) (hSyl : Claim1721SylL3) (hK : KS1721Invert) (h9 : CardInfNineS17) :
    Claim1721T := by
  intro G _ _ A c L Y₀ Y₁ S p P h hJ
  have hs := h.toSec17Std
  have h9' : Nat.card (A ⊓ L : Subgroup G) = 9 := h9 G A c L Y₀ hs
  have htype := types_of_item1715 h1715 hs hJ
  obtain ⟨t, htL, htE, htinv⟩ := Proof1721.exists_inverting_of_quot hK htype inf_le_right h9'
    (fun x hx => HeadProof.pow_three_of_std hs hx.1) (Proof1721.not_dvd_card_L h hSyl htype)
  refine ⟨t, Subgroup.mem_inf.mpr ⟨htL, Proof1721.mem_normalizer_A_of_mem_L hs h9' htL htE⟩, ?_,
    htinv⟩
  rcases h1715 G A c L Y₀ hs with ⟨hΩ, -⟩ | ⟨-, ⟨φL⟩, ⟨φ⟩, -, hT⟩
  · exact mem_normalizer_inf_L_of_one h h1717 hΩ (hO2 G A c L Y₀ Y₁ S p P h) hJ htL htinv
  · obtain ⟨g, hP⟩ := Proof17Res4.exists_a10Pic hs φ φL hT.1
    exact Proof17Res4.mem_normalizer_inf_L_of_a10 h hP (h142 G A c L hs.toSec14Std)
      (hO2 G A c L Y₀ Y₁ S p P h) h9' htL htinv

theorem claim1721T_of_one_items
    (h1717 : Item1717One) (h1715 : Item1715) (h142 : Concl142S14)
    (hQ : Step171CommQ) (h146 : Item146S14) (h166 : Item166S17) (h168 : Item168S17)
    (hbot : Item145BotS17) (h138 : Item138N) (h9 : CardInfNineS17) : Claim1721T :=
  claim1721T_of_one h1717 h1715 h142 (claim17O2Y0_of hQ h146 h166 h168 hbot)
    (claim1721SylL3_of h1715 h138) ks1721Invert_proof h9

open Proof1721 in
theorem claim1721SComm_of_types
    (hL3 : Claim1721SCommL3) (h1715 : Item1715) (h9 : CardInfNineS17) : Claim1721SComm := by
  intro G _ _ A c L Y₀ Y₁ S p P h hJ hΩ T hT hAT
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs := h.toSec17Std
  have h9' : Nat.card (A ⊓ L : Subgroup G) = 9 := h9 G A c L Y₀ hs
  rcases types_of_item1715 h1715 hs hJ with hL | hA7 | hM22
  · exact hL3 G A c L Y₀ Y₁ S p P h hL hΩ T hT hAT
  all_goals
    have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
      center_eq_bot_of_types hs.mem_lA.1 (by tauto)
    have hcL : c ∉ L := hs.toSec15R.hypS.2.2 c hs.zpowers_mem_omegaA L hs.mem_lA
    have hc : orderOf c = 3 := orderOf_eq_prime hs.c_pow_three (fun h1 => hcL (h1 ▸ one_mem L))
    have h3L : 3 ∣ Nat.card L := three_dvd_card_L h9'
    have hCL := Sec15R.centralizer_le_normalizer_L hs.toSec15R h3L
    have hSyl : IsSylowOf 3 (T ⊓ L) L := hT.inf_of_le_normalizer hs.le_centralizer_c hCL
  · exact commutator_mem_of_inn hZ (innThreeSylow_alt7 hA7) hs.mem_partTwoF
      (eq_zpowers_sup_inf hs h9') hs.le_centralizer_c hc hT.isPGroup hAT hT.le (hT.le.trans hCL)
      hSyl
  · exact commutator_mem_of_inn hZ (innThreeSylow_m22 hM22) hs.mem_partTwoF
      (eq_zpowers_sup_inf hs h9') hs.le_centralizer_c hc hT.isPGroup hAT hT.le (hT.le.trans hCL)
      hSyl

open Proof1721 in
theorem claim1721SW_of_types
    (h175 : Item175R) (h1715 : Item1715) (hSyl : Claim1721SylL3)
    (hcomm : Claim1721SComm) (hA10 : Claim1721SA10) (h9 : CardInfNineS17) : Claim1721SW := by
  intro G _ _ A c L Y₀ Y₁ S p P h hJ
  have hs := h.toSec17Std
  by_cases hΩ : omegaA A = {Subgroup.zpowers c}
  · exact exists_inverts_c_of_omega h hΩ (h175 G A c L hs.toSec15R)
      (hcomm G A c L Y₀ Y₁ S p P h hJ hΩ) (h9 G A c L Y₀ hs)
      (not_dvd_card_L h hSyl (types_of_item1715 h1715 hs hJ))
  · rcases hs.a10_or_omega with hY | hΩ'
    · exact hA10 G A c L Y₀ Y₁ S p P h hJ hY hΩ
    · exact absurd hΩ' hΩ

theorem claim1721S_of_types
    (h175 : Item175R) (h1715 : Item1715) (h138 : Item138N) (hcomm : Claim1721SCommL3)
    (h9 : CardInfNineS17) (hloc : Claim1411LocalR) : Claim1721S :=
  claim1721S_of (claim1721SW_of_types h175 h1715 (claim1721SylL3_of h1715 h138)
    (claim1721SComm_of_types hcomm h1715 h9) (claim1721SA10_proof h1715) h9) hloc h9

theorem claim1720_of_one (h1717 : Item1717One) (h1715 : Item1715) (h142 : Concl142S14)
    (hQ : Step171CommQ) (hOdd : Claim1716Odd) (h146 : Item146S14) (hbot : Item145BotS17)
    (h166 : Item166S17) (h168 : Item168S17) : Claim1720 :=
  claim1720_of_steps (claim1720Inner_of_one h1717 h1715 h142 h166 hbot h168)
    (claim1720A10_proof h1715 h142 (claim17O2Y0_of hQ h146 h166 h168 hbot))
    (claim17Q0_of_step171CommQ hQ) h1715 hOdd h146 hbot h166 h168

theorem item1721_of_one
    (h166 : Item166S17) (hbot : Item145BotS17) (h168 : Item168S17) (h146 : Item146S14)
    (h9 : CardInfNineS17) (h1719 : Item1719) (h1720 : Claim1720) (h1717 : Item1717One)
    (h1715 : Item1715) (h142 : Concl142S14) (hQ : Step171CommQ) (h138 : Item138N)
    (h175 : Item175R) (hcomm : Claim1721SCommL3) (hloc : Claim1411LocalR) : Item1721 :=
  item1721_of h166 hbot h168 h146 h9 h1719 h1720
    (claim1721T_of_one_items h1717 h1715 h142 hQ h146 h166 h168 hbot h138 h9)
    (claim1721S_of_types h175 h1715 h138 hcomm h9 hloc)

@[expose] def Claim1719WNJOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      omegaA A = {Subgroup.zpowers c} →
      ∃ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
        w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
          w ∉ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G)

theorem claim1719WNJ_of_one (hOne : Claim1719WNJOne) (h1715 : Item1715) (h142 : Concl142S14)
    (h9 : CardInfNineS17) : Claim1719WNJ := by
  intro G _ _ A c L Y₀ Y₁ S p P h hJ
  have hs := h.toSec17Std
  rcases h1715 G A c L Y₀ hs with ⟨hΩ, -⟩ | ⟨-, ⟨φL⟩, ⟨φ⟩, -, hT⟩
  · exact hOne G A c L Y₀ Y₁ S p P h hJ hΩ
  · obtain ⟨g, hP⟩ := Proof17Res4.exists_a10Pic hs φ φL hT.1
    exact Proof17Res4.exists_w_of_a10 h hP (h142 G A c L hs.toSec14Std) (h9 G A c L Y₀ hs)

@[expose] noncomputable def Claim1718QuotOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (h : Sec17Y1 G A c L Y₀ Y₁ S p P),
    omegaA A = {Subgroup.zpowers c} →
    letI := kerAO2_normal h.le_normalizer_y0
    ∀ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
      imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom) ≠ imgY0 A Y₀ (S ⊓ Y₀) →
        3 ∣ Nat.card ↥(imgY0 A Y₀ (S ⊓ Y₀) ⊔
          imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom))

theorem claim1718Quot_of_one (hOne : Claim1718QuotOne) (h1715 : Item1715) (h142 : Concl142S14) :
    Claim1718Quot := by
  intro G _ _ A c L Y₀ Y₁ S p P h
  have hs := h.toSec17Std
  rcases h1715 G A c L Y₀ hs with ⟨hΩ, -⟩ | ⟨-, ⟨φL⟩, ⟨φ⟩, -, hT⟩
  · exact hOne G A c L Y₀ Y₁ S p P h hΩ
  · obtain ⟨g, hP⟩ := Proof17Res4.exists_a10Pic hs φ φL hT.1
    have := kerAO2_normal h.le_normalizer_y0
    exact fun w hw hne =>
      Proof17Res4.three_dvd_of_a10 h hP (h142 G A c L hs.toSec14Std) hw hne

end CFSG.RankThree.PartTwo.Sec17
