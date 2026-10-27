module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientTools
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LieBorelTorus
public import CFSG.Quasithin.Vol2.Ch9KGFFSpConj
public import CFSG.Quasithin.Vol2.Ch10SecKHK3D

public section

open CFSG.Open
open CFSG.Blueprint
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (normalizer_unipotent)

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

noncomputable def normalizerQuotientUnipotentEquiv {K : Type} [Field K] :
    normalizerQuotient (unipotent 2 K) ≃* (Fin 2 → Kˣ) := by
  have hnorm := normalizer_unipotent (r := 2) (K := K)
  have hle : Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K)) ≤ borelSubgroup 2 K :=
    hnorm.le
  have hB : borelSubgroup 2 K ≤ Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K)) :=
    hnorm.ge
  let φ : ↥(Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K))) →* (Fin 2 → Kˣ) :=
    (diagHom 2 K).comp (Subgroup.inclusion hle)
  have hφsurj : Function.Surjective φ := by
    intro t
    obtain ⟨b, hb⟩ := diagHom_surjective (r := 2) (K := K) t
    exact ⟨⟨b, hB b.2⟩, hb⟩
  have hφker : φ.ker = (unipotent 2 K).subgroupOf
      (Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K))) := by
    ext x
    show diagHom 2 K ⟨(x : StatedSp 2 K), hle x.2⟩ = 1 ↔ (x : StatedSp 2 K) ∈ unipotent 2 K
    rw [← MonoidHom.mem_ker, ker_diagHom, Subgroup.mem_subgroupOf]
  exact (QuotientGroup.quotientMulEquivOfEq hφker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)

theorem k_Sp4CartanRank_holds : K_Sp4CartanRank := by
  intro Y _ _ n hY hq S hS
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eP⟩⟩ := hY.statedClassicalModel (by decide)
  letI := hKf
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp at hq
    · exact h
  have hq4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    rw [← Nat.card_eq_fintype_card, hKcard])
  let eYSp : Y ≃* StatedSp 2 K :=
    eP.trans (CFSG.Quasithin.Vol2.Ch10.SecC.C10KH.projEquivSp (F := K)).symm
  have hU : IsSylowTwoOf (unipotent 2 K) ⊤ :=
    CFSG.Quasithin.H13.Ch9.KGFF.isSylowTwoOf_unipotent
  obtain ⟨eN⟩ := normalizerQuotient_equiv_of_isSylowTwoOf (S := S)
    (S' := unipotent 2 K) eYSp hS hU
  let e : normalizerQuotient S ≃* (Fin 2 → Kˣ) :=
    eN.trans (normalizerQuotientUnipotentEquiv (K := K))
  have hcardN : Nat.card (normalizerQuotient S) = (Nat.card K - 1) ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_pi, Nat.card_units]
  have hcardY : Nat.card Y =
      Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
    rw [Nat.card_congr eYSp.toEquiv]
    exact card_statedSp_two K
  have hfac : ∀ {q r : ℕ}, 4 ≤ q → r.Prime → r ≠ 2 → r ∣ q - 1 →
      (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))).factorization r =
        ((q - 1) ^ 2).factorization r := by
    intro q r hq4 hr hr2 hdvd
    have hr_not_dvd_q : ¬ r ∣ q := by
      intro h
      have h1 : r ∣ q - (q - 1) := Nat.dvd_sub h hdvd
      rw [show q - (q - 1) = 1 by omega] at h1
      exact hr.not_dvd_one h1
    have hr_not_dvd_q1 : ¬ r ∣ q + 1 := by
      intro h
      have h1 : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub h hdvd
      have h2 : (q + 1) - (q - 1) = 2 := by omega
      rw [h2] at h1
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h1)
    have hr_dvd_q2m1 : r ∣ q ^ 2 - 1 := by
      have hq2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
        have h := Nat.sq_sub_sq q 1
        rw [show (1 : ℕ) ^ 2 = 1 by norm_num] at h
        rw [h, mul_comm]
      rw [hq2]
      exact dvd_trans hdvd (dvd_mul_right (q - 1) (q + 1))
    have hr_not_dvd_q2p1 : ¬ r ∣ q ^ 2 + 1 := by
      intro h
      have h1 : r ∣ (q ^ 2 + 1) - (q ^ 2 - 1) := Nat.dvd_sub h hr_dvd_q2m1
      have h2 : (q ^ 2 + 1) - (q ^ 2 - 1) = 2 := by
        have hk : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
        omega
      rw [h2] at h1
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h1)
    have hq1ne : q ^ 2 - 1 ≠ 0 := by
      have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
      omega
    have hq4ne : q ^ 4 - 1 ≠ 0 := by
      have : 1 < q ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
      omega
    have hq4eq : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
      have h := Nat.sq_sub_sq (q ^ 2) 1
      rw [show (1 : ℕ) ^ 2 = 1 by norm_num] at h
      have hsq : (q ^ 2) ^ 2 = q ^ 4 := by ring
      rw [← hsq, h, mul_comm]
    have hq2eq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have h := Nat.sq_sub_sq q 1
      rw [show (1 : ℕ) ^ 2 = 1 by norm_num] at h
      rw [h, mul_comm]
    have hr_not_dvd_q4 : ¬ r ∣ q ^ 4 := fun h => hr_not_dvd_q (hr.dvd_of_dvd_pow h)
    have h1 : (q ^ 4).factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hr_not_dvd_q4
    have h2 : ((q ^ 2 - 1) * (q ^ 4 - 1)).factorization r =
        (q ^ 2 - 1).factorization r + (q ^ 4 - 1).factorization r := by
      rw [Nat.factorization_mul hq1ne hq4ne, Finsupp.add_apply]
    have h3 : (q ^ 4 - 1).factorization r =
        (q ^ 2 - 1).factorization r + (q ^ 2 + 1).factorization r := by
      rw [hq4eq, Nat.factorization_mul hq1ne (by positivity), Finsupp.add_apply]
    have h4 : (q ^ 2 + 1).factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hr_not_dvd_q2p1
    have h5 : (q ^ 2 - 1).factorization r =
        (q - 1).factorization r + (q + 1).factorization r := by
      rw [hq2eq, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply]
    have h6 : (q + 1).factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hr_not_dvd_q1
    have h7 : (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))).factorization r =
        (q ^ 4).factorization r + ((q ^ 2 - 1) * (q ^ 4 - 1)).factorization r := by
      rw [Nat.factorization_mul (by positivity) (mul_ne_zero hq1ne hq4ne), Finsupp.add_apply]
    rw [h7, h1, h2, h3, h4, h5, h6, Nat.factorization_pow, Finsupp.smul_apply,
      smul_eq_mul]
    ring
  refine ⟨?_, fun r hr hr2 hdvd => ?_⟩
  · refine IsMulCommutative.mk (Std.Commutative.mk ?_)
    intro a b
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  · have hcomm : ∀ a b : normalizerQuotient S, a * b = b * a := by
      intro a b
      apply e.injective
      rw [map_mul, map_mul]
      exact mul_comm _ _
    have hdvd' : r ∣ Nat.card K - 1 := by
      rw [hKcard]
      exact hdvd
    have hcu : Nat.card {x : Kˣ // x ^ r = 1} = r :=
      CFSG.LocalAnalysis.RankFourTheoremC.card_units_pow_eq_one hdvd'
    have hpi : Nat.card {a : Fin 2 → Kˣ // a ^ r = 1} = r ^ 2 := by
      calc Nat.card {a : Fin 2 → Kˣ // a ^ r = 1} =
          Nat.card ({x : Kˣ // x ^ r = 1} × {x : Kˣ // x ^ r = 1}) := by
            refine Nat.card_congr ?_
            exact
              { toFun := fun a =>
                  (⟨a.1 0, by
                      have h := congrFun a.2 0
                      simpa using h⟩,
                   ⟨a.1 1, by
                      have h := congrFun a.2 1
                      simpa using h⟩)
                invFun := fun p =>
                  ⟨fun i => if i = 0 then p.1.1 else p.2.1, by
                    funext i
                    fin_cases i
                    · simpa using p.1.2
                    · simpa using p.2.2⟩
                left_inv := fun a => by
                  apply Subtype.ext
                  funext i
                  fin_cases i <;> simp
                right_inv := fun p => by
                  obtain ⟨p1, p2⟩ := p
                  simp }
        _ = Nat.card {x : Kˣ // x ^ r = 1} * Nat.card {x : Kˣ // x ^ r = 1} :=
            Nat.card_prod _ _
        _ = r ^ 2 := by rw [hcu]; ring
    have hkA : Nat.card {a : normalizerQuotient S // a ^ r = 1} = r ^ 2 := by
      rw [← hpi]
      exact Nat.card_congr
        { toFun := fun a => ⟨e a.1, by rw [← map_pow, a.2, map_one]⟩
          invFun := fun b => ⟨e.symm b.1, by rw [← map_pow, b.2, map_one]⟩
          left_inv := fun a => Subtype.ext (e.symm_apply_apply a.1)
          right_inv := fun b => Subtype.ext (e.apply_symm_apply b.1) }
    obtain ⟨hp, ho⟩ := pRank_and_card_Omega1p_of_comm hcomm hr hkA
    haveI : Fact (Nat.Prime r) := ⟨hr⟩
    have hp' : CFSG.pRank r (⊤ : Subgroup (normalizerQuotient S)) = 2 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.Quasithin.pRank_top_subtype]
      exact hp
    refine ⟨hp', ho, ?_⟩
    rw [hcardY, hcardN]
    exact hfac hq4 hr hr2 hdvd'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
