module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7E
public import CFSG.Quasithin.Vol2.Ch10SecKIK2b
public import CFSG.Quasithin.Background.G64ProofBasic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

theorem stronglyQuasithin_of_card {Q : Type} [Group Q] [Finite Q] (hQ : Nat.card Q = 2520) :
    CFSG.Open.SQTKTauCeti.StronglyQuasithin Q := by
  intro p hp hp2
  show CFSG.Open.pRank p (⊤ : Subgroup Q) ≤ 2
  by_contra hlt
  have hdvd : p ^ CFSG.Open.pRank p (⊤ : Subgroup Q) ∣ Nat.card (⊤ : Subgroup Q) :=
    CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card p hp ⊤
  rw [Subgroup.card_top, hQ] at hdvd
  have h3 : p ^ 3 ∣ 2520 := (pow_dvd_pow p (by omega)).trans hdvd
  have hle : p ^ 3 ≤ 2520 := Nat.le_of_dvd (by norm_num) h3
  have hp13 : p ≤ 13 := by
    by_contra h
    have : 14 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  have hp2' := hp.two_le
  interval_cases p <;> first | exact hp2 rfl | exact absurd h3 (by norm_num)

variable {G : Type} [Group G] [Finite G]

theorem sqtkGroup_autOn {J W : Subgroup G} (hJN : J ≤ Subgroup.normalizer (W : Set G))
    (hA7 : IsAlt 7 (↥J ⧸ CFSG.pCore 2 ↥J) ∨
      IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7)))
    (hSQ : SQTKGroup ↥J) (hO2 : pCoreOf 2 (autOn J W) = ⊥)
    (hJW : ¬ J ≤ Subgroup.centralizer (W : Set G)) :
    SQTKGroup ↥(autOn J W) ∧
      (Nat.card ↥(autOn J W) = 2520 ∨ Nat.card ↥(autOn J W) = 7560) := by
  have hle := InternalSec.pCore_le_ker_autOnHom hJN hO2
  set ρ : (↥J ⧸ CFSG.pCore 2 ↥J) →* ↥(autOn J W) :=
    QuotientGroup.lift _ (InternalSec.autOnHom hJN) hle with hρ
  have hρs : Function.Surjective ρ := by
    intro y
    obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hJN y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hnt : ¬ Subsingleton ↥(autOn J W) := by
    intro hs
    apply InternalSec.ker_autOnHom_ne_top hJN hJW
    rw [eq_top_iff]
    intro l _
    exact Subsingleton.elim _ _
  have hc := K7.card_quot_A7 hA7 ρ hρs hnt
  have hQ : SQTKGroup (↥J ⧸ CFSG.pCore 2 ↥J) :=
    InternalSec.sqtkGroup_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup) hSQ
  refine ⟨?_, hc⟩
  rcases hc with h1 | h2
  · refine ⟨stronglyQuasithin_of_card h1, ?_⟩
    exact (hQ.2.quotient ρ.ker).of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm
  · have hinj : Function.Injective ρ := by
      refine (hρs.bijective_of_nat_card_le ?_).1
      rw [h2]
      rcases K7.card_A7 hA7 with h | h <;> omega
    refine InternalSec.sqtkGroup_of_surjective ρ hρs ?_ hQ
    rw [(MonoidHom.ker_eq_bot_iff ρ).2 hinj]
    exact IsPGroup.of_bot

theorem b51Hyp_A7 {S Y J W : Subgroup G} [IsMulCommutative ↥W] (hS : IsSylowTwoOf S Y)
    (hJY : J ≤ Y) (hYJ : Y ≤ Subgroup.normalizer (J : Set G))
    (hY2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ J) (hWe : IsElemAbelian 2 W)
    (hred : IsTwoReducedIn Y W)
    (hA7 : IsAlt 7 (↥J ⧸ CFSG.pCore 2 ↥J) ∨
      IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7)))
    (hSQ : SQTKGroup ↥J) (hJW : ¬ J ≤ Subgroup.centralizer (W : Set G))
    (hTW : ¬ thompsonJ S ≤ Subgroup.centralizer (W : Set G)) :
    B51Hyp (ffJ (autOn Y W)) (autOn J W) ∧
      (Nat.card ↥(autOn J W) = 2520 ∨ Nat.card ↥(autOn J W) = 7560) := by
  have hJN : J ≤ Subgroup.normalizer (W : Set G) := hJY.trans hred.2.1
  have hO2 : pCoreOf 2 (autOn Y W) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hO2J : pCoreOf 2 (autOn J W) = ⊥ := pCoreOf_autOn_L_eq_bot1527d hJY hYJ hO2
  have hq : CFSG.IsQuasisimple ↥(autOn J W) :=
    InternalSec.isQuasisimple_autOn hJN (K7.isQuasisimple_A7 hA7) hO2J hJW
  obtain ⟨hSQa, hc⟩ := sqtkGroup_autOn hJN hA7 hSQ hO2J hJW
  obtain ⟨A, -, hA, hLA⟩ := SecC.C10KH.exists_offender_of_thompsonJ hWe hred hS hYJ hY2 hq hTW
  have h2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ J ⊔ Subgroup.centralizer (W : Set G) :=
    fun y hy => by
      obtain ⟨e, he⟩ := hY2 y hy
      exact ⟨e, Subgroup.mem_sup_left he⟩
  exact ⟨(InternalSec.b51Hyp_ffJ_autOn hred.2.1 hJY hYJ h2 hO2 hq hSQa hA hLA).1, hc⟩

theorem sqtkGroup_of_le {X J : Subgroup G} (hS : SQTKGroup ↥X) (hJX : J ≤ X) :
    SQTKGroup ↥J := by
  set e := Subgroup.subgroupOfEquivOfLe hJX
  refine InternalSec.sqtkGroup_of_surjective e.toMonoidHom e.surjective ?_
    (InternalSec.sqtkGroup_subgroup hS (J.subgroupOf X))
  rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
  exact IsPGroup.of_bot

section Setting

variable {X T J : Subgroup G}

omit [Finite G] in
theorem commutator_le_conjClosure {Z Y : Subgroup G} (hJY : J ≤ Y) :
    ⁅Z, J⁆ ≤ conjClosure Z Y := by
  rw [Subgroup.commutator_le]
  intro z hz j hj
  rw [commutatorElement_def]
  have h1 : z ∈ conjClosure Z Y := le_conjClosure Z Y hz
  have h2 : j * z⁻¹ * j⁻¹ ∈ conjClosure Z Y := mem_conjClosure (hJY hj) (Z.inv_mem hz)
  have e : z * j * z⁻¹ * j⁻¹ = z * (j * z⁻¹ * j⁻¹) := by group
  rw [e]
  exact (conjClosure Z Y).mul_mem h1 h2

theorem b51Hyp_setting (hX : CFSG.SectionRank.IsSQTKCat ↥X) (hC : CharTwo X)
    (hT : IsSylowTwoOf T X) (hJ : J ∈ cComp X) (hJn : (J.subgroupOf X).Normal)
    (hA : IsAlt 7 ↥(modO2Image X J) ∨ IsHat ↥(modO2Image X J) ↥(alternatingGroup (Fin 7)))
    (hTJ : ¬ thompsonJ T ≤
      Subgroup.centralizer ((⁅quasithinOmegaOneCenter T, J⁆ : Subgroup G) : Set G)) :
    ∃ hW : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) (J ⊔ T)),
      IsTwoReducedIn (J ⊔ T) (conjClosure (quasithinOmegaOneCenter T) (J ⊔ T)) ∧
      ⁅quasithinOmegaOneCenter T, J⁆ ≤ conjClosure (quasithinOmegaOneCenter T) (J ⊔ T) ∧
      (haveI := hW.1;
        B51Hyp (ffJ (autOn (J ⊔ T) (conjClosure (quasithinOmegaOneCenter T) (J ⊔ T))))
          (autOn J (conjClosure (quasithinOmegaOneCenter T) (J ⊔ T))) ∧
        (Nat.card ↥(autOn J (conjClosure (quasithinOmegaOneCenter T) (J ⊔ T))) = 2520 ∨
          Nat.card ↥(autOn J (conjClosure (quasithinOmegaOneCenter T) (J ⊔ T))) = 7560)) := by
  set Z := quasithinOmegaOneCenter T with hZ
  set Y := J ⊔ T with hY
  set W := conjClosure Z Y with hWdef
  have hJX : J ≤ X := le_of_mem_cComp hJ
  have hXJ : X ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).1 hJn
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hT.1.trans hXJ
  have hYX : Y ≤ X := sup_le hJX hT.1
  have hYJ : Y ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hTN
  have hTY : IsSylowTwoOf T Y := B6.isSylowTwoOf_mono hT le_sup_right hYX
  have hCY : CharTwo Y :=
    S153D.charTwo_of_le hC hYX
      ((CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hT).trans le_sup_right)
  obtain ⟨-, hWe, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hTY hCY (le_refl Z)
  have hY2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ J := InternalSec.two_of_sup hT.2.1 hTN
  have hSQ : SQTKGroup ↥J := sqtkGroup_of_le (G64.sqtkGroup_of_isSQTKCat hX) hJX
  have hA7 : IsAlt 7 (↥J ⧸ CFSG.pCore 2 ↥J) ∨
      IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7)) := by
    obtain ⟨e⟩ := modO2_mulEquiv hJ
    rcases hA with hA | h
    · obtain ⟨f⟩ := hA
      exact Or.inl ⟨e.trans f⟩
    · exact Or.inr (IsHat.of_mulEquiv e.symm h)
  have hZJ : ⁅Z, J⁆ ≤ W := commutator_le_conjClosure le_sup_left
  have hJW : ¬ J ≤ Subgroup.centralizer (W : Set G) := by
    intro hle
    apply hTJ
    have hb : ⁅Z, J⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact (Subgroup.mem_centralizer_iff.mp (hle hj) z (le_conjClosure Z Y hz)).symm
    rw [hb, Subgroup.coe_bot, Subgroup.centralizer_singleton_one]
    exact le_top
  have hTW : ¬ thompsonJ T ≤ Subgroup.centralizer (W : Set G) :=
    fun hle => hTJ (hle.trans (Subgroup.centralizer_le hZJ))
  have := hWe.1
  exact ⟨hWe, hred, hZJ, b51Hyp_A7 hTY le_sup_left hYJ hY2 hWe hred hA7 hSQ hJW hTW⟩

end Setting

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8
