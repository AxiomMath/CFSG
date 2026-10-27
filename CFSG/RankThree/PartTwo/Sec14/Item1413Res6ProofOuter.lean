module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofOdd
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCore
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofUpper
import CFSG.RankThree.PartTwo.Sec10.Item101
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Defs
import CFSG.LocalAnalysis.AGLEmbedding.CoprimeSup
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof1413Res6

variable {G : Type} [Group G] [Finite G]

open Proof1413Res5 in
theorem inf_thetaQuotCentralizer_le_pCore (hspor : SporadicModels131) {A L : Subgroup G}
    {c : G} (P : Pt142 A c L) :
    k142 A (lB A) c ⊓ Sec4.thetaQuotCentralizer L ≤ pPrimeCoreOf 3 (k142 A (lB A) c) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := k142 A (lB A) c with hKdef
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set X := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hX
  set N := K ⊓ Sec4.thetaQuotCentralizer L with hN
  set θ := inSubgroup (aschbacherSolvableCore 3) L with hθ
  have hD := P.std.toSec13Data
  have hNK : N ≤ K := inf_le_left
  have hKN : K ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer
      (P.k_le_normalizer.trans (Sec6.normalizer_le_normalizer_thetaQuotCentralizer L))
  refine le_pPrimeCoreOf hNK hKN ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
  intro h3
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 3 h3
  set M := X ⊔ pPrimeCoreOf 3 H with hM
  have hXH : X ≤ H :=
    (pPrimeCoreOf_le 3 _).trans ((Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr hD.mem_A)).trans
        (centralizer_singleton_le_normalizer_zpowers c))
  have hM3 : ¬ 3 ∣ Nat.card M :=
    (isPiSubgroup_piCompl_iff Nat.prime_three M).mp
      (isPiSubgroup_piCompl_sup
        ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr (not_three_dvd_pCoreOf _))
        ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr (not_three_dvd_pCoreOf _))
        (hXH.trans (le_normalizer_pPrimeCoreOf 3 H)))
  have hMK : M ≤ K := by
    rw [hKdef, P.eq_k]
    exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
  have hKLM : K ≤ L ⊔ M := by
    rw [hKdef, P.eq_k, hM, sup_assoc, sup_comm (pPrimeCoreOf 3 H) X]
  have hLn : (L.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer P.l_le).mpr P.k_le_normalizer
  have hy3 : IsPGroup 3 (Subgroup.zpowers (y : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy, pow_one])
  have hyK : Subgroup.zpowers (y : G) ≤ K := Subgroup.zpowers_le.mpr (hNK y.2)
  have hyL : Subgroup.zpowers (y : G) ≤ L :=
    CFSG.AGLEmbedding.le_of_le_sup_of_coprime_card_of_le hyK P.l_le hMK hLn hy3
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hM3).symm (hyK.trans hKLM)
  have hyL' : (y : G) ∈ L := hyL (Subgroup.mem_zpowers _)
  have hyθ : (y : G) ∈ θ := by
    have hyC : (y : G) ∈ Sec4.thetaQuotCentralizer L := (Subgroup.mem_inf.mp y.2).2
    obtain ⟨hlN, hl1⟩ := Proof142Res.mem_thetaQuotCentralizer_iff'.mp hyC
    rw [Proof142Res.thetaQuotMulAut_of_mem hyL'] at hl1
    have hZ := Item148PtRes2.center_eq_bot_of_sec14 hspor P.std
    have hl2 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) (⟨y, hyL'⟩ : ↥L) = 1 :=
      Sec17.Proof17Res7.conj_injective_of_center hZ (hl1.trans (map_one _).symm)
    exact ⟨⟨y, hyL'⟩, (QuotientGroup.eq_one_iff _).mp hl2, rfl⟩
  have hθ3 := (Sec6.theta_solvable_and_not_dvd L).2
  have h1 : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe, hy]
  have h2 := Subgroup.orderOf_dvd_natCard θ hyθ
  rw [h1] at h2
  exact hθ3 h2

open Proof1413Res5 in
theorem not_two_dvd_centralizer_of_gamma' (hspor : SporadicModels131) (h142 : Item142AllS14)
    (hbot : Item145BotS14) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hfail : Fail1411 A (lB A)) {c' : G} (hc' : Subgroup.zpowers c' ∈ gammaA A (lB A))
    {L' : Subgroup G} (hL' : L' ∈ lA A c') (hAc : A = Subgroup.zpowers c' ⊔ (A ⊓ L')) :
    ¬ 2 ∣ Nat.card ↥(Subgroup.centralizer ({c'} : Set G) ⊓ Sec4.thetaQuotCentralizer L') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h' : Sec14Std G A c' L' := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  have hD := h'.toSec13Data
  have hA27 : IsE27 A := h'.isE27
  have hA3 : IsPGroup 3 A := hA27.isPGroup
  have := ker142_normal (LB := lB A) hD.isElemAbelian.1 hD.mem_A
  have hc'A : c' ∈ A := hD.mem_A
  set H := Subgroup.normalizer (Subgroup.zpowers c' : Set G) with hH
  set K := k142 A (lB A) c' with hKdef
  set O := pPrimeCoreOf 3 K with hOdef
  set θ := inSubgroup (aschbacherSolvableCore 3) L' with hθ
  have h142' : ∀ Q ∈ maxInvariantPiSubgroups H A (piCompl 3),
      Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({c'} : Set G)) ∧ _ :=
    h142 G A c' L' h'
  have hOodd := not_two_dvd_pCore_of_gamma h142 hbot hR hfail hc' hL'
  have P : Pt142 A c' L' := ⟨h', eq_k_of_gamma h142 hbot hR hc' hL'⟩
  set N₁ := Subgroup.centralizer ({c'} : Set G) ⊓ Sec4.thetaQuotCentralizer L' with hN₁
  have hKH : K ≤ H := delta_le _
  have hCK : K ⊓ Sec4.thetaQuotCentralizer L' ≤ O := inf_thetaQuotCentralizer_le_pCore hspor P
  have hθN₁ : θ ≤ N₁ :=
    le_inf ((Sec6.theta_le L').trans (Sec6.le_centralizer_of_mem_thetaComponentsAt hL'.1))
      (Sec6.theta_le_thetaQuotCentralizer L')
  have hCN : Subgroup.centralizer ({c'} : Set G) ≤ Subgroup.normalizer (L' : Set G) :=
    centralizer_le_normalizer_of_three_dvd h' P.three_dvd
  have hN₁θ : N₁ ≤ Subgroup.normalizer (θ : Set G) :=
    (inf_le_left.trans hCN).trans (Sec6.normalizer_le_normalizer_theta L')
  have hAθ : A ≤ Subgroup.normalizer (θ : Set G) :=
    hD.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta L')
  have hcomm : ∀ x ∈ N₁, ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ θ := by
    intro x hx a ha
    rw [hAc] at ha
    have hcom : ∀ z ∈ A ⊓ L', z * c' = c' * z := fun z hz => hD.commute hz.1 hc'A
    obtain ⟨i, d, hd, rfl⟩ := Sec10.exists_zpow_mul_of_mem_sup_zpowers hcom ha
    have hxc : Commute x (c' ^ i) :=
      Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hx.1) i
    have hdx : d * x * d⁻¹ * x⁻¹ ∈ θ := by
      have h1 := commutator_mem_theta_of_mem hx.2 (inv_mem hd.2)
      have h2 : d * x * d⁻¹ * x⁻¹ = d * (x * d⁻¹ * x⁻¹ * d⁻¹⁻¹) * d⁻¹ := by group
      rw [h2]
      exact (Subgroup.mem_normalizer_iff.mp (hAθ hd.1) _).mp h1
    have h3 : c' ^ i * d * x * (c' ^ i * d)⁻¹ * x⁻¹ =
        c' ^ i * (d * x * d⁻¹ * x⁻¹) * (c' ^ i)⁻¹ := by
      calc c' ^ i * d * x * (c' ^ i * d)⁻¹ * x⁻¹ =
          c' ^ i * (d * x * d⁻¹ * x⁻¹) * (x * (c' ^ i)⁻¹ * x⁻¹) := by group
        _ = c' ^ i * (d * x * d⁻¹ * x⁻¹) * (c' ^ i)⁻¹ := by
          rw [show x * (c' ^ i)⁻¹ * x⁻¹ = (c' ^ i)⁻¹ by rw [hxc.inv_right.eq]; group]
    rw [h3]
    exact (Subgroup.mem_normalizer_iff.mp (hAθ (Subgroup.zpow_mem _ hc'A i)) _).mp hdx
  intro h2
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥N₁) 2 h2
  set U := Subgroup.zpowers (t : G) ⊔ θ with hU
  have ht2 : IsPGroup 2 (Subgroup.zpowers (t : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one])
  have htθ : Subgroup.zpowers (t : G) ≤ Subgroup.normalizer (θ : Set G) :=
    Subgroup.zpowers_le.mpr (hN₁θ t.2)
  have hθ3 := (Sec6.theta_solvable_and_not_dvd L').2
  have hU3 : ¬ 3 ∣ Nat.card U :=
    (isPiSubgroup_piCompl_iff Nat.prime_three U).mp
      (isPiSubgroup_piCompl_sup (isPiSubgroup_piCompl_three_of_piOf_two
        ((isPiSubgroup_piOf_iff Nat.prime_two _).mpr ht2))
        ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr hθ3) htθ)
  have hUN₁ : U ≤ N₁ := sup_le (Subgroup.zpowers_le.mpr t.2) hθN₁
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun u hu => ?_
    have hle : U ≤ U.comap (MulAut.conj a).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (fun z hz => ?_)
      · show a * (t : G) * a⁻¹ ∈ U
        have h1 := hcomm t t.2 a ha
        rw [show a * (t : G) * a⁻¹ = (a * t * a⁻¹ * (t : G)⁻¹) * t by group]
        exact mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      · show a * z * a⁻¹ ∈ U
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hAθ ha) z).mp hz)
    exact hle hu
  obtain ⟨S, hS, -, hAS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA3 hU3 hAU (bot_le : (⊥ : Subgroup G) ≤ U) IsPGroup.of_bot
    (fun a _ => Subgroup.mem_normalizer_iff.mpr fun x => by simp)
  have hS1 : S ≠ ⊥ := by
    intro hSb
    have hzt := hS.2.2 _ le_sup_left ht2 (hSb ▸ bot_le)
    rw [hSb] at hzt
    have ht1 : (t : G) = 1 := by
      have := Subgroup.mem_zpowers (t : G)
      rwa [hzt, Subgroup.mem_bot] at this
    have : t = 1 := Subtype.ext ht1
    rw [this, orderOf_one] at ht
    omega
  have hSN₁ : S ≤ N₁ := hS.1.trans hUN₁
  have hSH : S ≤ H :=
    (hSN₁.trans inf_le_left).trans (centralizer_singleton_le_normalizer_zpowers c')
  obtain ⟨Q, hQ, hSQ⟩ := exists_le_mem_maxInvariantPiSubgroups
    ⟨hSH, (isPiSubgroup_piCompl_iff Nat.prime_three S).mpr (not_three_dvd_of_two hS.2.1), hAS⟩
  have hSq : S ∈ scriptQ A (lB A) := mem_scriptQ_of_le (h142' Q hQ).1.1 hSQ hAS
  have hSK : S ≤ K := le_delta hSq hSH
  have hSO : S ≤ O := (le_inf hSK (hSN₁.trans inf_le_right)).trans hCK
  apply hS1
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  have hk0 : k = 0 := by
    by_contra hk0
    exact hOodd ((dvd_pow_self 2 hk0).trans (hk ▸ Subgroup.card_dvd_of_le hSO))
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq S hk

end Proof1413Res6

end CFSG.RankThree.PartTwo.Sec14
