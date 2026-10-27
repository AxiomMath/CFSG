module

public import CFSG.RankThree.PartTwo.Sec16.Item162ResProofOther
public import CFSG.RankThree.PartTwo.Sec16.Item162Res2ProofTenL
import CFSG.RankThree.PartTwo.Sec16.Item162ResProofConf
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec17.Item17Q0Proof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def Step162A7OtherSeven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y₁ Y₂ S : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S S → L ≤ Y₁ →
      MeetsY4 A (lB A) L Y₁ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      WStarS4 A → TransOmegaThree A c →
      Nonempty (↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁ ≃* alternatingGroup (Fin 7)) →
      (¬ ∃ g ∈ Subgroup.normalizer (A : Set G), Y₂ = Y₁.map (MulAut.conj g).toMonoidHom) →
      ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
        Subgroup.zpowers b ≠ Subgroup.zpowers c → MeetsY4 A (lB A) Lb Y₂ →
        Nonempty (↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7)) →
        Late.sectionCentralizer A Y₂ (CFSG.Open.pCoreOf 2 Y₂) = (Subgroup.zpowers b : Set G) →
          False

theorem step162A7Other_of (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14)
    (h142 : Concl142S14) (hS : Step162A7OtherSeven) : Step162A7Other := by
  classical
  intro G _ _ A c L h Y₁ Y₂ S hmax hLY₁ hm₁ h7 hW4 hT hY₁t hnW b Lb hb hLb hbc hm₂ hY₂7 hsc
  rcases hY₁t with hY₁7 | ⟨⟨φ₁⟩⟩
  · exact hS G A c L h Y₁ Y₂ S hmax hLY₁ hm₁ h7 hW4 hT hY₁7 hnW b Lb hb hLb hbc hm₂ hY₂7 hsc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ₂⟩ := hY₂7
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

end CFSG.RankThree.PartTwo.Sec16
