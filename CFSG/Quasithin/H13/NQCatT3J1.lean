module

public import CFSG.Quasithin.H13.NQCatT3Red
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113J1ZK
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Simplicity.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.EmptyFaithful.R3c2Excl
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146C1
public import CFSG.Quasithin.EmptyFaithful.S146C2
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152He9Y1
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153G27
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.SBc5Common
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.A5S1520a
public import CFSG.Quasithin.H13.A6S1513
public import CFSG.Quasithin.H13.A6S4L1
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.H13.U3L14E
public import CFSG.Quasithin.Vol2.Ch10SecA1011
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecAFactsOrth
public import CFSG.Quasithin.Vol2.Ch10SecBL32O2
public import CFSG.Quasithin.Vol2.Ch10SecBL32Prod
public import CFSG.Quasithin.Vol2.Ch10SecC8Main12
public import CFSG.Quasithin.Vol2.Ch10SecC9Entry
public import CFSG.Quasithin.Vol2.Ch10SecC9L32
public import CFSG.Quasithin.Vol2.Ch10SecC9S5c
public import CFSG.Quasithin.Vol2.Ch10SecEE3ProdC
public import CFSG.Quasithin.Vol2.Ch10SecQ9G10
public import CFSG.Quasithin.Vol2.Ch10SecQ9G11
public import CFSG.Quasithin.Vol2.Ch10SecQ9H9
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Main
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Lift
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeC2
public import CFSG.Quasithin.Vol2.Ch6Sec1G22
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem11
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem12
public import CFSG.Sporadic.Schreier.M23

public section

namespace CFSG.Quasithin.H13.NQCat.T3

open CFSG.Quasithin.H13.NQCat.T513 CFSG.Walter CFSG.Walter.J1Props CFSG.Blueprint

variable {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A}

theorem three_j1 (h : Star513 Q R S B D)
    (hJ : IsSporadic .J1 ↥Q)
    (hD3 : ∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  by_contra hnot
  obtain ⟨e₀⟩ : Nonempty (↥Q ≃* NativeSporadic.Carrier .J1) := hJ
  have hZ : Subgroup.center ↥Q = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun z hz =>
    eq_one_of_forall_commute_of_j1 e₀ fun k => (Subgroup.mem_center_iff.mp hz k).symm
  let e : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨b, hb, hb3⟩ := exists_b_three e h
  obtain ⟨hE3, hE9⟩ := exists_three_group e hZ (fun α _ => exists_eq_conj_of_j1 e₀ α) h hD3
    hnot hb hb3
  have hQc : Nat.card ↥Q = 175560 := by
    rw [Nat.card_congr (e₀.trans walterJ1EquivNative.symm).toEquiv, card_walterJ1]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hE3.exists_card_eq
  have hdvd := Subgroup.card_subgroup_dvd_card
    (iPart Q e D ⊔ Subgroup.zpowers (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩))
  rw [hm, hQc] at hdvd
  rw [hm] at hE9
  have hm2 : 2 ≤ m := by
    by_contra hm2
    interval_cases m <;> norm_num at hE9
  have : 3 ^ 2 ∣ 175560 := (pow_dvd_pow 3 hm2).trans hdvd
  revert this
  decide

end CFSG.Quasithin.H13.NQCat.T3
