module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End5ProofStar
public import CFSG.RankThree.PartTwo.Sec21.Hering2125Bar
public import CFSG.RankThree.PartTwo.Sec21.Hering2125Quasi
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Open (IsCharTwoType)
open Hering2125

@[expose] def InducesInnerG2 {G : Type} [Group G] [Finite G] (Y : Subgroup G) (c : G) : Prop :=
  InducesInnerBar Y c ∧ ∃ n : ℕ, 0 < n ∧ Even n ∧
    Blueprint.ChevalleyExceptionalModel (Y ⧸ aschbacherSolvableCore 3 Y) .G2 2 n

@[expose] def InducesInnerD4 {G : Type} [Group G] [Finite G] (Y : Subgroup G) (c : G) : Prop :=
  InducesInnerBar Y c ∧ ∃ n : ℕ, 0 < n ∧ Even n ∧
    Blueprint.ChevalleyExceptionalModel (Y ⧸ aschbacherSolvableCore 3 Y) .trialityD4 2 n

@[expose] def Item2125Cases : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G) (e : G) (Y : Subgroup G),
    Gen2125 G A E U c L d U₀ a X e Y →
      InducesTypeTwoL2 Y c ∨ InducesInnerG2 Y c ∨ InducesInnerD4 Y c ∨
      Nonempty (imageI Y (Sec11.sec11K L e) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))

theorem theta_two_torsion_fixed {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : A ∈ partTwoS G) {e c : G} (he : e ∈ A) (he1 : e ≠ 1) (hcA : c ∈ A) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 e) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hθc : ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) Y, ∀ y ∈ Y, t * y = y * t) :
    ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) Y, t * t = 1 → c * t * c⁻¹ = t := by
  intro t ht ht2
  have hθeq := Sec6.theta_eq_inf_of_mem_thetaComponentsAt hY
  have htmem : t ∈ Y ⊓ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) :=
    hθeq ▸ ht
  have htC : t ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) :=
    htmem.2
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) := hAY hcA
  haveI := Sec4.aschbacherSolvableCore_characteristic ↥Y
  have hcΘ : c ∈ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) Y : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (aschbacherSolvableCore 3 ↥Y) hcN
  have hct : c * t * c⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Y :=
    (Subgroup.mem_normalizer_iff.mp hcΘ t).mp ht
  have hct' : c * t * c⁻¹ ∈ Y := (Subgroup.map_subtype_le _) hct
  have ht' : t ∈ Y := (Subgroup.map_subtype_le _) ht
  have hz : t * c * t⁻¹ * c⁻¹ ∈ ⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({e} : Set G)), A⁆ := by
    have := Subgroup.commutator_mem_commutator htC hcA
    rwa [commutatorElement_def] at this
  have hodd := hA.2.1 e he he1
  set K : Subgroup G := ⁅inSubgroup (aschbacherSolvableCore 3)
    (Subgroup.centralizer ({e} : Set G)), A⁆ with hK
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hct2 : (c * t * c⁻¹) * (c * t * c⁻¹) = 1 := by
    calc (c * t * c⁻¹) * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hcomm : t * (c * t * c⁻¹) = (c * t * c⁻¹) * t := hθc t ht _ hct'
  have hzeq : t * c * t⁻¹ * c⁻¹ = t * (c * t * c⁻¹) := by rw [hinv]; group
  have hzz : (t * c * t⁻¹ * c⁻¹) * (t * c * t⁻¹ * c⁻¹) = 1 := by
    rw [hzeq]
    calc t * (c * t * c⁻¹) * (t * (c * t * c⁻¹))
        = t * ((c * t * c⁻¹) * t) * (c * t * c⁻¹) := by group
      _ = t * (t * (c * t * c⁻¹)) * (c * t * c⁻¹) := by rw [hcomm]
      _ = (t * t) * ((c * t * c⁻¹) * (c * t * c⁻¹)) := by group
      _ = 1 := by rw [ht2, hct2, one_mul]
  have h2 : orderOf (t * c * t⁻¹ * c⁻¹) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hzz)
  have hn : orderOf (t * c * t⁻¹ * c⁻¹) ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨t * c * t⁻¹ * c⁻¹, hz⟩ : K)
    rwa [Subgroup.orderOf_mk] at this
  have h1 : orderOf (t * c * t⁻¹ * c⁻¹) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hodd) h2 hn
  have hz1 : t * c * t⁻¹ * c⁻¹ = 1 := orderOf_eq_one_iff.mp h1
  rw [hzeq] at hz1
  have : c * t * c⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_right hz1
  rw [this, hinv]

@[expose] def Item2125CharTwo : Prop :=
  (∀ (X : Type) [Group X] (n : ℕ), Blueprint.ChevalleyExceptionalModel X .G2 2 n →
      IsCharTwoType X) ∧
    ∀ (X : Type) [Group X] (n : ℕ), Blueprint.ChevalleyExceptionalModel X .trialityD4 2 n →
      IsCharTwoType X

theorem item2125StarLocal_of_cases (h44 : Sec4.Item4_4)
    (h45 : Sec4.Item4_5) (hOrd : KS213Order) (hNine : KS213Nine) (hTwo : KS213TwoRank)
    (hC : Item2125Cases) (hX : Item2125CharTwo) : Item2125StarLocal := by
  intro G _ _ A E U c L d U₀ a X e Y hgen U₁ hU₁ hU₁I heU₁
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg := hgen.cfg.cfg
  have hpair := hcfg.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hEA : E ≤ A := hpair.mem_E.2
  have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [h27, hpair.mem_E.1.2.1])
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hpair.mem_E.1.1
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have he := hgen.mem_e
  have hed : e ∉ Subgroup.zpowers d := fun h => hgen.not_mem_cd (Subgroup.mem_sup_right h)
  have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
  have hc1 : c ≠ 1 := hpairs.2.1
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have he3 : e ^ 3 = 1 := hAe.2 e he
  have hY := hgen.mem_Y
  have hG4 := hpair.standing.toTheoremFourHyp
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe he he1 Y hY
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hU₁Y : U₁ ≤ Y := hU₁I.trans hgen.le_I
  have hU₁L : U₁ ≤ L := hU₁I.trans ((Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left)
  have hcU₁ : c ∈ Subgroup.centralizer (U₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLC (hU₁L hu))
  have hUθ := Item2119End5Proof.inf_theta_eq_bot hpair.mem_S he he1 hEA hE3 hY (hEA.trans hAY) hU₁
  obtain ⟨-, hU₁ab, hU₁card⟩ := mem_fourGroups_iff.mp hU₁.1
  have hcB : c ∈ E ⊓ Subgroup.centralizer (U₁ : Set G) := ⟨hEeq ▸ hcA, hcU₁⟩
  have hBN : E ⊓ Subgroup.centralizer (U₁ : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    inf_le_left.trans (hEA.trans hAY)
  have hcnt : c ∉ Sec4.thetaQuotCentralizer Y := by
    intro hc
    have hce : c ∈ Subgroup.zpowers e := by
      rw [← hgen.cent]
      exact ⟨hcA, hc⟩
    have hcard : ∀ x : G, x ^ 3 = 1 → x ≠ 1 → Nat.card (Subgroup.zpowers x) = 3 := by
      intro x hx3 hx1
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hx3 hx1
    have heq : Subgroup.zpowers c = Subgroup.zpowers e :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hce)
        (by rw [hcard c hc3 hc1, hcard e he3 he1])
    apply hgen.not_mem_cd
    exact Subgroup.mem_sup_left (heq ▸ Subgroup.mem_zpowers e)
  have hAS : A ∈ partTwoS G := hpair.mem_S
  have hUb4 := (bar_four_group hU₁Y hUθ hU₁ab hU₁card).1
  rcases hC G A E U c L d U₀ a X e Y hgen with hT | hG2 | hD4 | hSL
  · have hZ := center_eq_bot_of_typeTwo hT
    have hB : IsBar211 (Y ⧸ aschbacherSolvableCore 3 Y) := by
      obtain ⟨-, n, hn, hev, e', -⟩ := hT
      exact isBar211_of_projSL3 hn hev e'
    have hθc := theta_central_of_items h44 hOrd hNine hTwo hG4 hAS he he1 hY hAY hB hZ
      (exists_act_of_nontrivial hcA hAY hZ hcnt)
    have hθ2 := theta_two_torsion_fixed hAS he he1 hcA hY hAY hθc
    exact not_commutator_le_theta hZ hcB hBN
      (exists_pCore_not_theta hT hc3 hU₁Y hUθ hU₁ab hU₁card hcU₁ hθc hθ2)
  · obtain ⟨hin, n, hn, hev, hmod⟩ := hG2
    have hXc : IsCharTwoType (Y ⧸ aschbacherSolvableCore 3 Y) := hX.1 _ n hmod
    have hZ := center_bar_eq_bot_of_charTwo hXc hUb4
    have hθc := theta_central_of_items h44 hOrd hNine hTwo hG4 hAS he he1 hY hAY
      (isBar211_of_g2 hn hev hmod) hZ (exists_act_of_nontrivial hcA hAY hZ hcnt)
    have hθ2 := theta_two_torsion_fixed hAS he he1 hcA hY hAY hθc
    exact not_commutator_of_inner hXc hZ hin hBN hcB hc3 hcnt hU₁Y hUθ hU₁ab hU₁card hcU₁ hθc hθ2
  · obtain ⟨hin, n, hn, hev, hmod⟩ := hD4
    have hXc : IsCharTwoType (Y ⧸ aschbacherSolvableCore 3 Y) := hX.2 _ n hmod
    have hZ := center_bar_eq_bot_of_charTwo hXc hUb4
    have hθc := theta_central_of_items h44 hOrd hNine hTwo hG4 hAS he he1 hY hAY
      (isBar211_of_d4 hn hev hmod) hZ (exists_act_of_nontrivial hcA hAY hZ hcnt)
    have hθ2 := theta_two_torsion_fixed hAS he he1 hcA hY hAY hθc
    exact not_commutator_of_inner hXc hZ hin hBN hcB hc3 hcnt hU₁Y hUθ hU₁ab hU₁card hcU₁ hθc hθ2
  · exact (false_of_sl2five hU₁Y hUθ hU₁ab hU₁card hU₁I hSL).elim

end CFSG.RankThree.PartTwo.Sec21
