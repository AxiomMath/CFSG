module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXU
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXU3M
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXBT
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXCS
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.GH74.Generic.S3.LeavesFine
public import CFSG.GH74.Generic.S3.Lem37
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.Quasithin.Background.C124AsmClassify
public import CFSG.Quasithin.Background.C124Interface
public import CFSG.Quasithin.Background.C124YZStar
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Fin
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WKl2
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXT
public import CFSG.Quasithin.Vol2.Ch3Sec2Inputs
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.RankThree.PartOne.CTP.SpEven
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts

public section

namespace CFSG.Quasithin.H13.P31X

open CFSG.QuasithinUnique CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

theorem u3_conclude {n : ℕ} {Y : Type} [Group Y] [Finite Y] {X U : Subgroup Y}
    {G : Type} [Group G] [Finite G] (hU : IsSylowTwoOf U X) (e₀ : ↥X ≃* G)
    {UG : Subgroup G} (hUG : IsSylowTwoOf UG ⊤) {g zc : ℕ}
    (hcardU : Nat.card UG = (2 ^ n) ^ 3)
    (hcardN : Nat.card (Subgroup.normalizer (UG : Set G)) * g =
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * zc)
    (hcoat : IsCoatom (Subgroup.normalizer (UG : Set G)))
    (hcyc : ∃ c ∈ Subgroup.normalizer (UG : Set G), ∀ b ∈ Subgroup.normalizer (UG : Set G),
      ∃ k : ℕ, (c ^ k)⁻¹ * b ∈ UG)
    (haut : ∀ α : MulAut G, UG.map α.toMonoidHom = UG →
      ∃ j : ℕ, ∀ b ∈ Subgroup.normalizer (UG : Set G), α b * (b ^ 2 ^ j)⁻¹ ∈ UG) :
    Nat.card ↥(X ⊓ Subgroup.normalizer (U : Set Y)) * g = Nat.card ↥U * (4 ^ n - 1) * zc ∧
      IsCoatom ((X ⊓ Subgroup.normalizer (U : Set Y)).subgroupOf X) ∧
      (∃ c ∈ X ⊓ Subgroup.normalizer (U : Set Y), ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y),
        ∃ k : ℕ, (c ^ k)⁻¹ * b ∈ U) ∧
      ∀ r ∈ Subgroup.normalizer (X : Set Y) ⊓ Subgroup.normalizer (U : Set Y),
        ∃ j : ℕ, ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y), r * b * r⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U := by
  obtain ⟨e, he⟩ := bt_sylow_iso hU e₀ hUG
  refine ⟨?_, bt_coatom hU e he hcoat, bt_cyc hU e he hcyc, ?_⟩
  · have h4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [bt_card_B hU e he, bt_card_U hU e he, hcardU, h4]
    exact hcardN
  · intro r hr
    obtain ⟨α, hαU, hαx⟩ := bt_conj hU e he r hr
    obtain ⟨j, hj⟩ := haut α hαU
    refine ⟨j, fun b hb => ?_⟩
    have hbX : b ∈ X := (Subgroup.mem_inf.mp hb).1
    have hrbX : r * b * r⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hr.1 b).1 hbX
    have hbN : e ⟨b, hbX⟩ ∈ Subgroup.normalizer (UG : Set G) :=
      (bt_mem_B hU e he ⟨b, hbX⟩).1 hb
    have h1 := hj (e ⟨b, hbX⟩) hbN
    rw [← hαx ⟨b, hbX⟩ hrbX, ← map_pow, ← map_inv, ← map_mul] at h1
    have h2 := (bt_mem_U e he _).2 h1
    simpa using h2


theorem u3BorelFacts_holds :
    U3BorelFacts := by
  intro n hn Y _ _ X U hperf hX hU
  obtain ⟨⟨hp, hf1, -⟩, K, _, _, hK, ⟨e₀⟩⟩ := id hX
  have hu : UnitaryFieldData 2 n K := ⟨hp, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := hu.charP
  haveI : Finite K := hu.finite
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) hu
  let eP : hypPSU hu 1 1 ≃* StatedProj (StatedSU 3 (2 ^ n) K) :=
    hypPSUEquivStatedProj hu hR (by norm_num)
  let θ : ↥X ⧸ Subgroup.center ↥X ≃* hypPSU hu 1 1 := e₀.trans eP.symm
  have hker : Nat.card (hypProj hu 1 1).ker = Nat.gcd 3 (2 ^ n + 1) := by
    rw [ker_hypProj, card_hypScalars hu (r := 1) (ε := 1) (by norm_num)]
  have hq : (3, 2 ^ n) ≠ (3, 2) := by
    intro h32
    have h1 : 2 ^ n = 2 := (Prod.mk.inj h32).2
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier
    (F := K) (p := 2) (f := n) hK (by omega) (n := 3) le_rfl (by decide) hq
  have hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (hypPSU hu 1 1)) =
      Nat.card (hypProj hu 1 1).ker := by
    have h1 : Nat.card (CFSG.Open.griessHopfMultiplier (hypPSU hu 1 1)) =
        Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (hypPSU hu 1 1)) :=
      Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
        (hypPSU hu 1 1)).toEquiv
    have h2 : Nat.card (CFSG.Open.griessHopfMultiplier (hypPSU hu 1 1)) =
        Nat.card (Multiplicative (ZMod (Nat.gcd 3 (2 ^ n + 1)))) :=
      Nat.card_congr
        ((CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eP).trans eM).toEquiv
    rw [hker, ← h1, h2, Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (ZMod (Nat.gcd 3 (2 ^ n + 1))) ≃ ZMod (Nat.gcd 3 (2 ^ n + 1))),
      Nat.card_zmod]
  have hperfE : Group.IsPerfect (hypSU hu 1 1) := u3_isPerfect_hypSU hu hn
  have hZc : (hypProj hu 1 1).ker = Subgroup.center (hypSU hu 1 1) := by
    rw [ker_hypProj]
    exact u3_hypScalars_eq_center hu hn
  have hdvdM : Nat.card (Subgroup.center ↥X) ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (hypPSU hu 1 1)) := by
    have := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hperf
      (CFSG.GH74.Generic.centralQuotientMap θ) (CFSG.GH74.Generic.centralQuotientMap_surjective θ)
      (CFSG.GH74.Generic.centralQuotientMap_ker θ).le
    rwa [CFSG.GH74.Generic.centralQuotientMap_ker θ] at this
  have hdvd : Nat.card (Subgroup.center ↥X) ∣ Nat.card (hypProj hu 1 1).ker := hM ▸ hdvdM
  have hprime : Nat.card (hypProj hu 1 1).ker = 1 ∨ (Nat.card (hypProj hu 1 1).ker).Prime := by
    rw [hker]
    rcases (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 (2 ^ n + 1)) with h | h
    · exact Or.inl h
    · right
      rw [h]
      exact Nat.prime_three
  refine ⟨hker ▸ hdvd, ?_⟩
  rcases bt_case_split (hypProj hu 1 1) (hypProj_surjective hu 1 1) hZc.le hperfE hperf θ hM hdvd
    hprime with hZ | ⟨hcZ, ⟨θ'⟩⟩
  ·
    let ψ : ↥X ≃* hypPSU hu 1 1 := (QuotientGroup.quotientBot.symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans θ)
    have hc1 : Nat.card (Subgroup.center ↥X) = 1 := by
      rw [hZ]
      exact Subgroup.card_bot
    have hN := u3_card_N_P hu
    obtain ⟨h2, h3, h4, h5⟩ := u3_conclude (g := Nat.gcd 3 (2 ^ n + 1)) (zc := 1) hU ψ
      (u3_isSylow_P hu) (u3_card_U_P hu) (hN.trans (mul_one _).symm) (u3_coatom_P hu)
      (u3_cyc_N_P hu) (u3_aut_P hu hn)
    rw [hc1]
    exact ⟨h2, h3, h4, h5⟩
  ·
    have hN := u3_card_N_E hu
    obtain ⟨h2, h3, h4, h5⟩ := u3_conclude (g := Nat.gcd 3 (2 ^ n + 1))
      (zc := Nat.card (Subgroup.center ↥X)) hU θ' (u3_isSylow_E hu) (u3_card_U_E hu)
      (by rw [hN, hcZ, hker]) (u3_coatom_E hu) (u3_cyc_N_E hu) (u3_aut_E hu hn)
    exact ⟨h2, h3, h4, h5⟩

end CFSG.Quasithin.H13.P31X
