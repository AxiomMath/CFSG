module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXW
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXL3T
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXL3M
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXL3R
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXL3Flag

public section

namespace CFSG.Quasithin.H13.P31X

open CFSG.QuasithinUnique CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ASVolI

theorem l3BorelFacts_holds : L3BorelFacts := by
  intro n hn Y _ _ X U hperf hX hU
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := id hX
  haveI : CharP K 2 := burnsideA26_charP_two hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; omega
  let θ : ↥X ⧸ Subgroup.center ↥X ≃* projectiveSL 3 K :=
    e₀.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
  have hker : Nat.card (proj 3 K).ker = Nat.gcd 3 (2 ^ n - 1) := by
    rw [ker_proj, l3_card_scalars, hK]
  have hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (projectiveSL 3 K)) =
      Nat.card (proj 3 K).ker := by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_three_le
      (k := K) (n := 3) le_rfl (by rw [hcard]; omega) (fun h => by
        have h4 := h.2
        rw [hcard] at h4
        omega)
    have h1 := Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (projectiveSL 3 K)).toEquiv
    have e2 : CFSG.Open.griessHopfMultiplier (projectiveSL 3 K) ≃*
        Multiplicative (ZMod (Nat.gcd 3 (Fintype.card K - 1))) :=
      (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).symm).trans eM
    rw [← h1, Nat.card_congr e2.toEquiv, Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (ZMod (Nat.gcd 3 (Fintype.card K - 1))) ≃
        ZMod (Nat.gcd 3 (Fintype.card K - 1))), Nat.card_zmod, hker, hcard]
  have hdvdM : Nat.card (Subgroup.center ↥X) ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (projectiveSL 3 K)) := by
    have := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hperf
      (CFSG.GH74.Generic.centralQuotientMap θ) (CFSG.GH74.Generic.centralQuotientMap_surjective θ)
      (CFSG.GH74.Generic.centralQuotientMap_ker θ).le
    rwa [CFSG.GH74.Generic.centralQuotientMap_ker θ] at this
  have hdvd : Nat.card (Subgroup.center ↥X) ∣ Nat.card (proj 3 K).ker := hM ▸ hdvdM
  have hprime : Nat.card (proj 3 K).ker = 1 ∨ (Nat.card (proj 3 K).ker).Prime := by
    rw [hker]
    rcases (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 (2 ^ n - 1)) with h | h
    · exact Or.inl h
    · right
      rw [h]
      exact Nat.prime_three
  have hkerE : (proj 3 K).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [ker_proj, scalars_eq_center]
  rcases bt_case_split (proj 3 K) (proj_surjective 3 K) hkerE (l3_isPerfect_sl3 (K := K)) hperf θ
      hM hdvd hprime with hZ | ⟨hcZ, ⟨θ'⟩⟩
  ·
    have hc1 : Nat.card (Subgroup.center ↥X) = 1 := by
      rw [hZ]
      exact Subgroup.card_bot
    let ψ : ↥X ≃* projectiveSL 3 K :=
      (QuotientGroup.quotientBot.symm).trans ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans θ)
    obtain ⟨e, he⟩ := bt_sylow_iso hU ψ (l3_isSylow_projUnitriangular (K := K))
    have hN : Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) =
        projUpperTriangular 3 K := normalizer_projUnitriangular (n := 3) (K := K) 2
    have hcardU : Nat.card ↥(projUnitriangular 3 K) = (2 ^ n) ^ 3 := by
      rw [card_projUnitriangular, hK] <;> norm_num
    have hcardN : Nat.card ↥(Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K))) *
        Nat.gcd 3 (2 ^ n - 1) = (2 ^ n) ^ 3 * (2 ^ n - 1) ^ 2 * 1 := by
      rw [hN, mul_one]
      have h := l3_card_projUpperTriangular (K := K)
      rw [hK] at h
      exact h
    have hcomm : ∀ a ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)),
        ∀ b ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)),
        a * b * a⁻¹ * b⁻¹ ∈ projUnitriangular 3 K := by
      intro a ha b hb
      rw [hN] at ha hb
      exact l3_comm_projUpperTriangular ha hb
    have hsolv : ∀ A : Subgroup (projectiveSL 3 K), projUnitriangular 3 K ≤ A →
        Group.IsSolvable ↥A → A ≤ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) := by
      intro A hUA hA
      rw [hN]
      exact l3_solv_P' hK4 hUA hA
    have hmodel : Even n → ¬ 3 ∣ n → ∀ α : MulAut (projectiveSL 3 K),
        (projUnitriangular 3 K).map α.toMonoidHom = projUnitriangular 3 K →
        ∀ c ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)),
          c ∉ projUnitriangular 3 K → c ^ 3 ∈ projUnitriangular 3 K →
          α c * c ∈ projUnitriangular 3 K → ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ 2 ^ (n / 2) + 1 →
            ∃ b ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)),
              b ^ p ∈ projUnitriangular 3 K ∧ α b * b⁻¹ ∉ projUnitriangular 3 K := by
      intro hev _ α hα c hc hcU hc3 hcr p hp hp5 hpn
      rw [hN] at hc ⊢
      exact l3_rclaim_P (l3_borel_aut (K := K)) hK hev hp hp5 hpn α hα hc hcU hc3 hcr
    obtain ⟨h2, h3, h4, h5⟩ := l3_transport hU e he (zc := 1) hcardU hcardN hcomm hsolv hmodel
    rw [hc1]
    exact ⟨one_dvd _, h2, h3, h4, h5⟩
  ·
    have hcZ' : Nat.card (Subgroup.center ↥X) = Nat.gcd 3 (2 ^ n - 1) := hcZ.trans hker
    obtain ⟨e, he⟩ := bt_sylow_iso hU θ' (l3_isSylow_unitriangular (K := K))
    have hN : Subgroup.normalizer (unitriangular 3 K : Set (Matrix.SpecialLinearGroup (Fin 3) K)) =
        upperTriangular 3 K := normalizer_unitriangular
    have hcardU : Nat.card ↥(unitriangular 3 K) = (2 ^ n) ^ 3 := by
      rw [card_unitriangular, hK] <;> norm_num
    have hcardN : Nat.card ↥(Subgroup.normalizer
        (unitriangular 3 K : Set (Matrix.SpecialLinearGroup (Fin 3) K))) *
        Nat.gcd 3 (2 ^ n - 1) = (2 ^ n) ^ 3 * (2 ^ n - 1) ^ 2 * Nat.card (Subgroup.center ↥X) := by
      rw [hN, l3_card_upperTriangular, hK, hcZ']
    have hcomm : ∀ a ∈ Subgroup.normalizer
        (unitriangular 3 K : Set (Matrix.SpecialLinearGroup (Fin 3) K)),
        ∀ b ∈ Subgroup.normalizer
          (unitriangular 3 K : Set (Matrix.SpecialLinearGroup (Fin 3) K)),
        a * b * a⁻¹ * b⁻¹ ∈ unitriangular 3 K := by
      intro a ha b hb
      rw [hN] at ha hb
      exact l3_comm_upperTriangular ha hb
    have hsolv : ∀ A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K), unitriangular 3 K ≤ A →
        Group.IsSolvable ↥A →
        A ≤ Subgroup.normalizer (unitriangular 3 K : Set (Matrix.SpecialLinearGroup (Fin 3) K)) := by
      intro A hUA hA
      rw [hN]
      exact l3_solv_S hK4 hUA hA
    have hmodel : Even n → ¬ 3 ∣ n → ∀ α : MulAut (Matrix.SpecialLinearGroup (Fin 3) K),
        (unitriangular 3 K).map α.toMonoidHom = unitriangular 3 K →
        ∀ c ∈ Subgroup.normalizer
          (unitriangular 3 K : Set (Matrix.SpecialLinearGroup (Fin 3) K)),
          c ∉ unitriangular 3 K → c ^ 3 ∈ unitriangular 3 K →
          α c * c ∈ unitriangular 3 K → ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ 2 ^ (n / 2) + 1 →
            ∃ b ∈ Subgroup.normalizer
              (unitriangular 3 K : Set (Matrix.SpecialLinearGroup (Fin 3) K)),
              b ^ p ∈ unitriangular 3 K ∧ α b * b⁻¹ ∉ unitriangular 3 K := by
      intro hev _ α hα c hc hcU hc3 hcr p hp hp5 hpn
      rw [hN] at hc ⊢
      exact l3_rclaim_S (l3_borel_aut (K := K)) hK hev hp hp5 hpn α hα hc hcU hc3 hcr
    obtain ⟨h2, h3, h4, h5⟩ :=
      l3_transport hU e he (zc := Nat.card (Subgroup.center ↥X)) hcardU hcardN hcomm hsolv hmodel
    exact ⟨dvd_of_eq hcZ', h2, h3, h4, h5⟩

end CFSG.Quasithin.H13.P31X
