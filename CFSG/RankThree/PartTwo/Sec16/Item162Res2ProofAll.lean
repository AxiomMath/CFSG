module

public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item162Res2ProofTenL
import CFSG.RankThree.PartTwo.Sec16.Item162ResProofConf
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

namespace Res162b

variable {G : Type} [Group G] [Finite G]

theorem false_of_conf162 {A : Subgroup G} {c : G} {L Y₁ Y₂ S : Subgroup G}
    (h : Sec15R G A c L) (hconf : Conf162 A (lB A) c L Y₁ Y₂ S)
    (hWH : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h1514 : Item1514 A (lB A) c L) (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h142 : Concl142 A (lB A)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hY₁ := hconf.maxCE.1.mem₁
  have hY₂ := hconf.maxCE.1.mem₂
  have hLY₁ : L ≤ Y₁ := hconf.le_y
  have hSN₂ : S ≤ Subgroup.normalizer (Y₂ : Set G) := hconf.maxCE.1.s₂.prop.1.2
  have hcA : c ∈ A := hD.mem_A
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
  have hLp : Group.IsPerfect ↥L := Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  rcases h1514 Y₁ hY₁ hconf.meets₁ with ⟨-, -, hΩ, -, -⟩ | ⟨h7, -, hT, hY₁t⟩ | ⟨-, -, -, hΩ, -⟩
  · exact hWH (normalizer_le_of_omegaA_eq hΩ)
  rotate_left
  · exact hWH (normalizer_le_of_omegaA_eq hΩ)
  obtain ⟨-, hY₂t⟩ := a7_of_not_normalizer_le h1514 hY₂ hconf.meets₂ hWH
  obtain ⟨φL⟩ := h7
  have hΩ3 : (omegaA A).ncard = 3 := hT.1
  have hθ₁ : ∀ t : ↥L, t ∈ aschbacherSolvableCore 3 ↥L → (t : G) ∈ CFSG.Open.pCoreOf 2 Y₁ := by
    rcases hY₁t with ⟨⟨φ₁⟩⟩ | ⟨⟨φ₁⟩⟩
    · exact theta_le_pCoreOf_of_seven hLY₁ φL φ₁
    · have hAY₁ : A ≤ Y₁ := Step163Alt.le_of_alternating_ten (Res162.partTwoE_maximal h)
        hD.isElemAbelian hY₁.prop.1.1.2 hY₁.prop.2.2 φ₁
      exact theta_le_pCoreOf_of_ten hLY₁ (hAY₁ hcA) hc3 hD.ne_one hD.le_centralizer hLp φL φ₁
  have hOS : CFSG.Open.pCoreOf 2 Y₁ ≤ S := by
    rcases hY₁t with ⟨⟨φ₁⟩⟩ | ⟨⟨φ₁⟩⟩
    · have hcovL : L = (Y₁ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L := by
        rw [inf_of_le_right hLY₁]
        exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).symm
      have hcov₁ := Res162.eq_sup_of_forall_mem (Res162.exists_mem_inf_of_cover hcovL
        (by rw [Nat.card_congr φ₁.toEquiv, Nat.card_congr φL.toEquiv]))
      exact pCoreOf_le_of_conf162 h hconf h1444 h146 hbot h142 (Or.inl hcov₁)
    · have hAY₁ : A ≤ Y₁ := Step163Alt.le_of_alternating_ten (Res162.partTwoE_maximal h)
        hD.isElemAbelian hY₁.prop.1.1.2 hY₁.prop.2.2 φ₁
      exact pCoreOf_le_of_conf162 h hconf h1444 h146 hbot h142 (Or.inr (hAY₁ hcA))
  have hθN : ∀ t : ↥L, t ∈ aschbacherSolvableCore 3 ↥L →
      (t : G) ∈ Subgroup.normalizer (Y₂ : Set G) := fun t ht => hSN₂ (hOS (hθ₁ t ht))
  rcases hY₂t with ⟨⟨φ₂⟩⟩ | ⟨⟨φ₂⟩⟩
  ·
    rcases hY₁t with ⟨⟨φ₁⟩⟩ | ⟨⟨φ₁⟩⟩
    · exact false_of_conf162_a7 h hconf h1444 h146 hbot h142 ⟨φL⟩ φ₁ φ₂
    ·
      set θ := aschbacherSolvableCore 3 ↥L with hθ
      set P := θ.map L.subtype with hP
      have hP2 : IsPGroup 2 P := by
        have hPO : P ≤ CFSG.Open.pCoreOf 2 Y₁ := by
          rintro _ ⟨t, ht, rfl⟩
          exact hθ₁ t ht
        exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₁).to_le hPO
      have hPN : P ≤ Subgroup.normalizer ((L ⊓ Y₂ : Subgroup G) : Set G) := by
        rintro _ ⟨t, ht, rfl⟩
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer t.2, hSN₂ (hOS (hθ₁ t ht))⟩
      have hLle : L ≤ P ⊔ (L ⊓ Y₂) := by
        intro l hl
        obtain ⟨d, hdD, hdL, hdl⟩ := exists_mem_inf_of_seven h hY₂ hconf.meets₂ φL φ₂ l hl
        have hP' : d⁻¹ * l ∈ P := ⟨_, hdl, by simp⟩
        have he' : l = d * (d⁻¹ * l) := by group
        rw [he']
        refine mul_mem (Subgroup.mem_sup_right hdD) (Subgroup.mem_sup_left hP')
      have hL3 : L = oPrimeResidualOf 3 L := by
        have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
          alternatingGroup.isSimpleGroup (by simp)
        exact eq_oPrimeResidualOf_of_isSimpleGroup hLp φL.isSimpleGroup
          (three_dvd_card_of_mem_lA h h.zpowers_mem_omegaA h.mem_lA)
      have hLY₂ : L ≤ Y₂ := (Proof162.le_of_le_sup_of_isPGroup_two hPN hP2 hLle hL3).trans
        inf_le_right
      have hconf' : Conf162 A (lB A) c L Y₂ Y₁ S :=
        ⟨hconf.maxCE.symm, hLY₂, hconf.meets₂, hconf.meets₁⟩
      exact Res162.false_of_le_normalizer_of_conf162 h hconf' h1444 h146 hbot h142 ⟨φL⟩ φ₂
        (hLY₁.trans Subgroup.le_normalizer)
  ·
    have hLN₂ := le_normalizer_of_ten h hΩ3 φL hY₂ φ₂ hconf.meets₂ hθN
    rcases hY₁t with ⟨⟨φ₁⟩⟩ | ⟨⟨φ₁⟩⟩
    · exact Res162.false_of_le_normalizer_of_conf162 h hconf h1444 h146 hbot h142 ⟨φL⟩ φ₁ hLN₂
    ·
      have hAY₁ : A ≤ Y₁ := Step163Alt.le_of_alternating_ten (Res162.partTwoE_maximal h)
        hD.isElemAbelian hY₁.prop.1.1.2 hY₁.prop.2.2 φ₁
      obtain ⟨F, hF, hFc⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hΩ3]; norm_num)
        (Subgroup.zpowers c)
      obtain ⟨y, hy, hFy⟩ := Step163Alt.omega_transitive_of_ten hD.isElemAbelian hD.card_eq hAY₁
        φ₁ hΩ3 _ h.zpowers_mem_omegaA F hF
      have hyY : y ∈ Y₁ := (Subgroup.mem_inf.mp hy).1
      have hyW : y ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hy).2
      set c' := y * c * y⁻¹ with hc'
      have hFc' : F = Subgroup.zpowers c' := by
        rw [hFy, MonoidHom.map_zpowers]
        rfl
      have hc'Ω : Subgroup.zpowers c' ∈ omegaA A := hFc' ▸ hF
      have hne : Subgroup.zpowers c' ≠ Subgroup.zpowers c := hFc' ▸ hFc
      set L' := L.map (MulAut.conj y).toMonoidHom with hL'
      have hL'A : L' ∈ lA A c' := (map_conj_mem_lA_iff hyW).mpr h.mem_lA
      have hL'Y₁ : L' ≤ Y₁ := by
        have := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hLY₁
        rwa [Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hyY)] at this
      obtain ⟨φL'⟩ := nonempty_a7_of_map_conj (w := y) rfl ⟨φL⟩
      have h' : Sec15R G A c' L' := sec15R_of_point h hc'Ω hL'A
      have hm' : MeetsY4 A (lB A) L' Y₂ := Res162.meetsY4_of_alternating_ten h' hΩ3 hY₂ φ₂
        h.zpowers_mem_omegaA h.mem_lA hconf.meets₂
      have hc'A : c' ∈ A := (zpowers_mem_omegaA_iff.mp hc'Ω).1
      have hc'3 : c' ^ 3 = 1 := hD.isElemAbelian.2 c' hc'A
      have hc'1 : c' ≠ 1 := by
        intro h1
        have h3 := (zpowers_mem_omegaA_iff.mp hc'Ω).2.1
        rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
        omega
      have hθ' := theta_le_pCoreOf_of_ten hL'Y₁ (hAY₁ hc'A) hc'3 hc'1
        (le_centralizer_of_mem_thetaComponentsAt hL'A.1)
        (Sec6.isPerfect_of_mem_thetaComponentsAt hL'A.1) φL' φ₁
      have hLN₂' := le_normalizer_of_ten h' hΩ3 φL' hY₂ φ₂ hm'
        (fun t ht => hSN₂ (hOS (hθ' t ht)))
      have hgen := le_sup_of_ten h hc'Ω hL'A hne φL φL' hY₁ φ₁ hLY₁ hL'Y₁
      have hY₁N : Y₁ ≤ Subgroup.normalizer (Y₂ : Set G) :=
        hgen.trans (sup_le (sup_le hLN₂ hLN₂') (hOS.trans hSN₂))
      obtain ⟨X, hX, hXLY⟩ := hconf.meets₂
      have heq : Y₁ = Y₂ := Proof162.eq_of_le_normalizer_of_mem_scriptY4 hY₁ hY₂.prop hX
        ((hXLY.trans inf_le_left).trans hLY₁) (hXLY.trans inf_le_right) hY₁N
      exact hconf.maxCE.1.not_conj ⟨1, one_mem _, by rw [Late.map_conj_one, heq]⟩

end Res162b

theorem step162A10R_of_items (h1514 : Item1514R) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (h142 : Concl142S14) : Step162A10R := by
  intro G _ _ A c₀ L₀ _ c L Y₁ Y₂ S h hconf hWH _ _ _
  have h14 := h.toSec14Std
  exact (Res162b.false_of_conf162 h hconf hWH (h1514 G A c L h) (h1444 G A c L h14)
    (h146 G A c L h14) (hbot G A c L h14) (h142 G A c L h14)).elim

end CFSG.RankThree.PartTwo.Sec16
