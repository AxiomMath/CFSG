module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res10Proof
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofCore
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec15.F153L3C2HJ
import CFSG.RankThree.PartTwo.Sec14.Item14Res7ProofMemFix
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

theorem step1515HJEndFpfRCore_of_res11Q
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h143 : Ronan148Q.Item143QS14) (hRle : Step1515HJEndFpfRLe)
    (hON : KS1515ONCent) (hA6 : Step1515HJEndFpfA6A6) : Step1515HJEndFpfRCore := by
  intro G _ _ A c L h hfree d hdA hd1 hdZ hodd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hD := h.sec13Data
  have hS := h.sec15R.toSec14Std
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hcA := hD.mem_A
  have hdL : d ∈ L := Proof15Res4.mem_of_isZCentral hdZ
  have hcL : c ∉ L := (j2_point_facts hD h.j2).1
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set R : Subgroup G := ⁅CFSG.Open.pCoreOf 2 N, Subgroup.zpowers c⁆ with hRdef
  set C := Subgroup.centralizer ({d} : Set G) with hCdef
  set M := pPrimeCoreOf 3 C with hMdef
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'def
  set X₀ := inSubgroup perfectResidual (L ⊓ C) with hX₀def
  have hRc : R = ⁅R, Subgroup.zpowers c⁆ := Proof15Res11.commutatorR_eq h
  obtain ⟨hR2, -⟩ := Proof15Res11.commutatorR_isPGroup h
  have hRM : R ⊓ M = ⊥ := Proof15Res11.commutatorR_inf_eq_bot h hodd
  have hRL : R ≤ Subgroup.centralizer (L : Set G) :=
    Proof15Res10.commutator_le_centralizer hD.le_centralizer
  have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hcA hdA)
  have hCM : C ≤ Subgroup.normalizer (M : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hcM : c ∈ Subgroup.normalizer (M : Set G) := hCM hcC
  have hO'C : O' ≤ C :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdA))
  have hO'c : O' ≤ Subgroup.centralizer ({c} : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA))
  have hO'3 : Nat.Coprime 3 (Nat.card O') := coprime_card_pPrimeCoreOf 3 _
  obtain ⟨hdΩ, hcdΩ⟩ := Proof15Res11.omega_facts h134 h48 hD h.j2 h.omega_ne hdA hd1 hdZ
  have hR1 : R ≤ delta A (lB A) C ⊔ M := hRle G A c L h hfree d hdA hd1 hdZ hodd
  obtain ⟨Q, hQ⟩ := maxInvariantPiSubgroups_nonempty (delta A (lB A) C) A (piCompl 3)
  obtain ⟨-, halt⟩ := h143 G A c L hS d hdA hd1 hdΩ Q hQ
  rcases halt with h1 | ⟨b, d', Lb, hbΩ, hLb, hJb, hd'A, hd'1, hd'c, hdbd', X, hΔ, hinv, hcase⟩
  ·
    have hR2' : R ≤ M ⊔ O' := by
      rw [h1] at hR1
      exact hR1.trans (sup_le le_rfl le_sup_left)
    exact Proof15Res11.le_of_le_sup_of_le_centralizer hRc hcM (hO'C.trans hCM) hO'c hR2'
  have hXΔ : X ≤ delta A (lB A) C := hΔ ▸ le_sup_right
  have hXC : X ≤ C := hXΔ.trans (delta_le C)
  have hcN : c ∈ Subgroup.normalizer ((M ⊔ X : Subgroup G) : Set G) :=
    hinv.inf_le ⟨hcC, Subgroup.le_normalizer hcA⟩
  have hO'N : O' ≤ Subgroup.normalizer ((M ⊔ X : Subgroup G) : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (hinv.centralizer_le hdA)
  have hΔle : delta A (lB A) C ≤ (M ⊔ X) ⊔ O' := by
    rw [hΔ]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (le_sup_right.trans le_sup_left)
  have hRMX : R ≤ M ⊔ X := by
    refine Proof15Res11.le_of_le_sup_of_le_centralizer hRc hcN hO'N hO'c ?_
    exact hR1.trans (sup_le hΔle (le_sup_left.trans le_sup_left))
  rcases hcase with ⟨-, -, hne⟩ | ⟨-, ⟨𝒳, h𝒳, hne𝒳, hX𝒳⟩, htypes⟩
  ·
    exfalso
    have hDb : Sec13Data G A b Lb := { hD with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
    have hd'Z : IsZCentral Lb d' := by
      obtain ⟨hd'L, S, hS1, hS2⟩ := hd'c
      obtain ⟨-, -, hθ3, -⟩ :=
        solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
      obtain ⟨hSy, hZ⟩ := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJb hd'L hd'1 S hS1 hS2
      exact ⟨_, hSy, hZ⟩
    have hcd : c ∉ Subgroup.zpowers d := fun h => hcL (Subgroup.zpowers_le.mpr hdL h)
    have hdc : d ∉ Subgroup.zpowers c := Proof152ResW.not_mem_zpowers_symm hA hd1 hcA hcd
    have hΩb : omegaA A ≠ {Subgroup.zpowers b} := by
      intro heq
      have h1 : Subgroup.zpowers c ∈ ({Subgroup.zpowers b} : Set (Subgroup G)) :=
        heq ▸ hD.zpowers_mem_omegaA
      have h2 : Subgroup.zpowers (c * d) ∈ ({Subgroup.zpowers b} : Set (Subgroup G)) :=
        heq ▸ hcdΩ d (Subgroup.mem_zpowers d)
      rw [Set.mem_singleton_iff] at h1 h2
      have hcd' : c * d ∈ Subgroup.zpowers c := by
        rw [h1, ← h2]
        exact Subgroup.mem_zpowers _
      apply hdc
      have e : d = c⁻¹ * (c * d) := by group
      rw [e]
      exact (Subgroup.zpowers c).mul_mem
        ((Subgroup.zpowers c).inv_mem (Subgroup.mem_zpowers c)) hcd'
    obtain ⟨-, hbk⟩ := Proof15Res11.omega_facts h134 h48 hDb hJb hΩb hd'A hd'1 hd'Z
    have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
    have hd3 : Nat.card (Subgroup.zpowers d) = 3 :=
      Sec13.card_zpowers_of_pow_three (hA.1.2 d hdA) hd1
    have hd'3 : Nat.card (Subgroup.zpowers d') = 3 :=
      Sec13.card_zpowers_of_pow_three (hA.1.2 d' hd'A) hd'1
    have hdd' : d ∉ Subgroup.zpowers d' := fun hm =>
      hne (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hm) (by rw [hd3, hd'3]))
    have hBA : Subgroup.closure {b, d'} ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers d' := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hbd' : b ∉ Subgroup.zpowers d' := by
      intro hm
      apply hdd'
      have hle : Subgroup.closure {b, d'} ≤ Subgroup.zpowers d' := by
        rw [Subgroup.closure_le]
        rintro x (rfl | rfl)
        · exact hm
        · exact Subgroup.mem_zpowers _
      exact hle hdbd'
    obtain ⟨k, hk, hkeq⟩ := Proof152ResW.exists_eq_zpowers_mul hA hbA hd'A hd'1 hbd'
      (Subgroup.zpowers_le.mpr (hBA hdbd')) hd3 hne
    exact hdΩ (hkeq ▸ hbk k hk)
  obtain ⟨hX₀p', hX₀tc', hX₀q', hX₀Z', hdX₀', hX₀3', hX₀Δ'⟩ :=
    Proof15Res11.residual_facts h hfree hdA hd1 hdZ
  have hX₀p : Group.IsPerfect ↥X₀ := hX₀p'
  have hX₀tc : Sec4.IsTripleCover ↥X₀ (alternatingGroup (Fin 6)) := hX₀tc'
  have hX₀q : IsQuasisimple ↥X₀ := hX₀q'
  have hX₀Z : Nat.card (Subgroup.center ↥X₀) = 3 := hX₀Z'
  have hdX₀ : d ∈ X₀ := hdX₀'
  have hX₀3 : X₀ = oPrimeResidualOf 3 X₀ := hX₀3'
  have hX₀Δ : X₀ ≤ delta A (lB A) C := hX₀Δ'
  have hX₀L : X₀ ≤ L := Item148HJ.residual_le L d
  have hX₀C : X₀ ≤ C := Item148HJ.residual_le_centralizer_singleton L d
  have hX₀MX : X₀ ≤ M ⊔ X := by
    rw [hX₀3]
    exact Proof15Res7.oPrimeResidualOf_le_of_le_sup_coprime hO'3 hO'N
      (hX₀Δ.trans hΔle)
  have hX₀M : X₀ ⊓ M = ⊥ := Proof15Res11.inf_pPrimeCoreOf_eq_bot hX₀C hX₀q hX₀Z
  have hθXM : inSubgroup (aschbacherSolvableCore 3) X ≤ M := by
    rcases hinv with hnorm | ⟨-, hXθ, -, -⟩
    · exact Proof15Res11.theta_le_pPrimeCoreOf hXC hnorm
    · exact Res7MemFix.theta_le_of_mem hXθ
  have hX₀c : X₀ ≤ Subgroup.centralizer ({c} : Set G) := hX₀L.trans hD.le_centralizer
  rcases htypes with hONt | hA6t | hA6A6t
  ·
    have hRX₀ : R ≤ Subgroup.centralizer (X₀ : Set G) :=
      hRL.trans (Subgroup.centralizer_le hX₀L)
    have hcX₀ : c ∈ Subgroup.centralizer (X₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hX₀c hx)
    have hc3 : c ^ 3 = 1 := by rw [← hD.orderOf_eq]; exact pow_orderOf_eq_one c
    have hcR : c ∈ Subgroup.normalizer (R : Set G) := Proof15Res10.le_normalizer_commutatorR h hcA
    have hR0 := hON G M X X₀ R c
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 C))
      (hXC.trans hCM) hONt hθXM hX₀MX hX₀M hX₀p hX₀tc ⟨d, hdX₀, hd1, hXC⟩ hRMX hRM hR2 hRX₀
      hcM hcN hcX₀ hc3 hcR hRc
    rw [hR0]
    exact bot_le
  ·
    have hXM : X ≤ Subgroup.normalizer (M : Set G) := hXC.trans hCM
    have hX₀Nm : X₀ ≤ Subgroup.normalizer (M : Set G) := hX₀C.trans hCM
    have hcardX : Nat.card X =
        1080 * Nat.card (inSubgroup (aschbacherSolvableCore 3) X) := by
      rw [inSubgroup, Subgroup.card_map_of_injective X.subtype_injective,
        ← Proof15Res11.card_of_isTripleCover_a6 hA6t]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hθle : Nat.card (inSubgroup (aschbacherSolvableCore 3) X) ≤
        Nat.card (M ⊓ X : Subgroup G) :=
      Subgroup.card_le_of_le (le_inf hθXM (Sec17.Proof171Steps.theta_le X))
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hXM
    have h2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hX₀Nm
    have hinf0 : Nat.card (M ⊓ X₀ : Subgroup G) = 1 := by
      rw [inf_comm, hX₀M, Subgroup.card_bot]
    have hcardX₀ : Nat.card X₀ = 1080 := Proof15Res11.card_of_isTripleCover_a6 hX₀tc
    rw [hinf0, mul_one, hcardX₀] at h2
    have hpos : 0 < Nat.card (M ⊓ X : Subgroup G) := Nat.card_pos
    have hle : Nat.card (M ⊔ X : Subgroup G) ≤ Nat.card (M ⊔ X₀ : Subgroup G) := by
      rw [h2]
      have h3 : Nat.card (M ⊔ X : Subgroup G) * Nat.card (M ⊓ X : Subgroup G) ≤
          Nat.card M * 1080 * Nat.card (M ⊓ X : Subgroup G) := by
        rw [h1, hcardX, ← mul_assoc]
        exact Nat.mul_le_mul_left _ hθle
      exact Nat.le_of_mul_le_mul_right h3 hpos
    have heq : M ⊔ X₀ = M ⊔ X :=
      Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hX₀MX) hle
    exact Proof15Res11.le_of_le_sup_of_le_centralizer hRc hcM hX₀Nm hX₀c (heq ▸ hRMX)
  ·
    rcases hinv with hnorm | ⟨-, hXθ, -, -⟩
    · exact hA6 G A c L h hfree d hdA hd1 hdZ hodd X hΔ hnorm ⟨𝒳, h𝒳, hne𝒳, hX𝒳⟩ hA6A6t hX₀MX
        hRMX
    · exact absurd hA6A6t (F153L3C2.not_isCentralProductA6Covers_of_quasi
        (Sec6.isQuasisimple_of_mem_thetaComponentsAt hXθ))

section Step1515

theorem step1515R_of_res11Q (h131 : Item131) (h137 : Item137) (hcl : Claim1515M12)
    (h1511 : Item1511R) (h1512 : Item1512R) (h1513 : Item1513R) (h156 : Item156R)
    (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h135 : Item135) (h135s : Item135Simple) (h153 : Item153MainR)
    (hobs : Claim153ObsR) (h149 : Sec16.Item149S14) (h1411 : Item1411_1R)
    (hloc : Claim1411LocalR) (h1444 : Item1444S14) (h146 : Item146S14) (hc142 : Concl142R)
    (h152 : Item152R) (hgen : KS1517Gen) (h155 : Item155wR) (h143 : Ronan148Q.Item143QS14)
    (hoff : Step1515HJEndFpfRBoundOff) (hON : KS1515ONCent) (hA6 : Step1515HJEndFpfA6A6)
    (hθ : KL325ThetaCent) (hK325 : KL325SubgroupOrder) : Step1515R :=
  step1515R_of_core h131 h137 hcl h1511 h1512 h1513 h156 h148 hbot h142 h134 h48 h135 h135s
    h153 hobs h149 h1411 hloc h1444 h146 hc142 h152 hgen h155
    (step1515HJEndFpfRCore_of_res11Q h134 h48 h143 (step1515HJEndFpfRLe_of_off hc142 hoff) hON
      hA6) hθ hK325

end Step1515

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
