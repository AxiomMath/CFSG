module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJNotLeDefs
public import CFSG.RankThree.PartTwo.Sec15.Item15No135
public import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofON
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

theorem false_of_omegaA_eq_of
    {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G} (h₀ : Sec14Std G A c₀ L₀)
    (h1411 : Item1411_1 A (lB A)) (hgen : KS156HJGen) (hmeet : Step156Meet A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hSG : ∀ S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G)) (piOf 2),
      S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hSY : ∀ S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G)) (piOf 2),
      S ≤ Subgroup.normalizer (Y : Set G))
    (htype : IsType156 Y) {d : G} {X₁ : Subgroup G} (D : Data156 A (lB A) Y c₀ L₀ d X₁)
    (hΩ : omegaA A = {Subgroup.zpowers c₀}) : False := by
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  have hbot : (⊥ : Subgroup G) ∈
      scriptQPi A (lB A) (Subgroup.normalizer (X : Set G)) (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (X : Set G)) (piOf 2))) hbot
  have hSH := inf_mem_scriptQPiStar_of_transOn (isNaturalFamily_lB A)
    (normalizer_le_of_omegaA_eq hΩ) h1411 (hSG S hS)
  have hLN : L₀ ≤ Subgroup.normalizer (Y : Set G) :=
    (hgen G A c₀ L₀ h₀ Y hY htype d X₁ D hΩ S (hSG S hS) (hSY S hS) hSH).trans
      (sup_le (hSY S hS) Subgroup.le_normalizer)
  obtain ⟨φ⟩ := D.hj
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hLY : L₀ ≤ Y := le_of_le_normalizer_of_theta
    (Sec6.isPerfect_of_mem_thetaComponentsAt D.mem_lA.1) φ.isSimpleGroup hLN
    (hmeet Y hY htype c₀ L₀ d X₁ D hΩ hLN)
  have hdvd := card_theta_dvd_card_quot hLY
  rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.J2.card_J2] at hdvd
  exact not_dvd_card_of_isType156 htype hdvd

section Item156


theorem false_of_isType156_of_omegaA_eq {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A)) (h1411 : Item1411_1 A (lB A))
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (hON : Step156ON A (lB A))
    (hD : Step156D A (lB A)) (hgen : KS156HJGen) (hmeet : Step156Meet A (lB A))
    (hΩ : omegaA A = {Subgroup.zpowers c}) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hSG : ∀ S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G)) (piOf 2),
      S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hSY : ∀ S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G)) (piOf 2),
      S ≤ Subgroup.normalizer (Y : Set G))
    (htype : IsType156 Y) : False := by
  obtain ⟨c₀, L₀, d, X₁, D⟩ :
      ∃ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A (lB A) Y c₀ L₀ d X₁ := by
    rcases htype with he | h6 | hON'
    · exact exists_data156_of_small' h h148 h134 h48 h415 hD hY (Or.inl he)
    · exact exists_data156_of_small' h h148 h134 h48 h415 hD hY (Or.inr h6)
    · exact hON Y hY hON'
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := D.omega, mem_lA := D.mem_lA }
  have hc₀ : Subgroup.zpowers c₀ = Subgroup.zpowers c := by
    have h1 := D.omega
    rw [hΩ] at h1
    exact h1
  exact false_of_omegaA_eq_of h₀ h1411 hgen hmeet hY hSG hSY htype D (by rw [hΩ, hc₀])

theorem item156_of_omegaA_eq {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (h1411 : Item1411_1 A (lB A)) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hON : Step156ON A (lB A)) (hD : Step156D A (lB A))
    (hgen : KS156HJGen) (hmeet : Step156Meet A (lB A))
    (hΩ : omegaA A = {Subgroup.zpowers c}) : Item156 A (lB A) := by
  intro Y hY
  have key := false_of_isType156_of_omegaA_eq h h148 h1411 h134 h48 h415 hON hD hgen hmeet hΩ hY
    (fun S hS => ((h153 Y hY).2.1 S hS).1) (hobs Y hY)
  exact ⟨⟨fun e => key (Or.inl ⟨e⟩)⟩, fun h6 => key (Or.inr (Or.inl h6)),
    fun hON' => key (Or.inr (Or.inr hON'))⟩

end Item156

section Item156R


theorem res1J2Item156_of (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h142 : Item142AllS14) (h1411 : Item1411_1R) (h152 : Item152R)
    (h153 : Item153MainR) (hobs : Claim153ObsR) : Res1J2Item156 := by
  intro G _ _ A c L hR _ hΩ
  have hS := hR.toSec14Std
  exact item156_of_omegaA_eq hS (h148 G A c L hR) (h153 G A c L hR) (hobs G A c L hR)
    (h1411 G A c L hR) h134 h48 h415
    (step156ON_of hS h142 (step156ONX_of h134 h48 hS (h148 G A c L hR)
      (step156ONXKR_of_items h148 h152 h134 h48 G A c L hR)))
    (step156D_of hS h142) (ks156HJGen_of h142) (step156Meet_of hS h142) hΩ

end Item156R

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
