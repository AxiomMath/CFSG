module

public import CFSG.Quasithin.Vol2.Ch4Sec4F4411D
public import CFSG.Walter.Bender1970.S2.PSL2Overgroups
public import CFSG.Walter.J1Props.Hyp
public import CFSG.Walter.Models
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.Quasithin.H13.Ch4.E443.F4411


open Subgroup CFSG.GorensteinWalter
open scoped MatrixGroups

theorem perfCentral_psl2_odd {p e : ℕ} [Fact p.Prime] (hp3 : 3 < p) (he : 1 ≤ e) :
    PerfCentral PSL(2, GaloisField p e) := by
  have hp : p.Prime := Fact.out
  have : Finite SL(2, GaloisField p e) := Finite.of_injective
    (fun A : SL(2, GaloisField p e) => (A : Matrix (Fin 2) (Fin 2) (GaloisField p e)))
    Subtype.coe_injective
  have : Finite PSL(2, GaloisField p e) :=
    Finite.of_surjective (QuotientGroup.mk : SL(2, GaloisField p e) → _) Quot.mk_surjective
  intro U Y hU hY hYU
  have hF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hK : ∀ m, m ≠ 0 → IsOddPrimePower (Nat.card (GaloisField p m)) ∧
      3 < Nat.card (GaloisField p m) := fun m hm => by
    rw [GaloisField.card p m hm]
    exact ⟨⟨p, m, hp, hp.odd_of_ne_two (by omega), by omega, rfl⟩,
      lt_of_lt_of_le hp3 (Nat.le_self_pow hm p)⟩
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF
      (normalizer (U : Set PSL(2, GaloisField p e))) with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, -, hz, ⟨eH⟩⟩ | ⟨-, ⟨eH⟩⟩ | ⟨-, ⟨eH⟩⟩ | ⟨-, ⟨eH⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNel, -, hCc, -, -, hNC⟩ | ⟨m, hm, -, ⟨eH⟩⟩ | ⟨m, hm, -, ⟨eH⟩⟩
  · exact commutator_eq_bot_of_solvable hY hYU
      (Group.isSolvable_of_comm fun a b => hEl.toIsMulCommutative.is_comm.comm a b)
  · exact commutator_eq_bot_of_solvable hY hYU
      (Group.isSolvable_of_comm fun a b => IsCyclic.isMulCommutative.is_comm.comm a b)
  · have : NeZero z := ⟨fun hz0 => by
      rw [hz0, mul_zero] at hz
      exact Nat.card_pos.ne' hz⟩
    have := CFSG.Walter.isSolvable_dihedralGroup' z
    exact commutator_eq_bot_of_solvable hY hYU (isSolvable_of_mulEquiv eH)
  · have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact commutator_eq_bot_of_solvable hY hYU (isSolvable_of_mulEquiv eH)
  · have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact commutator_eq_bot_of_solvable hY hYU (isSolvable_of_mulEquiv eH)
  · have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    rw [eq_bot_of_normalizer_simple hU eH (not_isPGroup_two_of_dvd Nat.prime_three (by norm_num)
      (by rw [nat_card_alternatingGroup, Nat.card_fin]; decide)), commutator_bot_left]
  · have : N.Normal := hN
    exact commutator_eq_bot_of_solvable hY hYU
      (CFSG.Walter.isSolvable_of_sup_eq_top hNel.toIsMulCommutative inferInstance hNC)
  · have : IsSimpleGroup PSL(2, GaloisField p m) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by have := (hK m hm).2; omega)
    rw [eq_bot_of_normalizer_simple hU eH
      (not_isPGroup_two_of_psl2_odd (GaloisField p m) (hK m hm).1), commutator_bot_left]
  · rw [eq_bot_of_normalizer_pgl2 hU eH (hK m hm).1 (hK m hm).2, commutator_bot_left]

theorem perfCentral_of_isPSL_odd {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    {p e : ℕ} (hp : p.Prime) (hp3 : 3 < p) (he : 1 ≤ e) (h : IsPSL 2 p e K) :
    PerfCentral (K ⧸ center K) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField K 2 p e h
  have : IsSimpleGroup PSL(2, GaloisField p e) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card p e (by omega)]
      exact le_trans (by omega) (Nat.le_self_pow (by omega) p))
  exact perfCentral_quot_of_mulEquiv hK φ (perfCentral_psl2_odd hp3 he)

theorem perfCentral_of_isJ1 {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (h : IsSporadic .J1 K) : PerfCentral (K ⧸ center K) := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup CFSG.Open.walterJ1 := CFSG.Walter.J1Props.isSimpleGroup_walterJ1
  exact perfCentral_quot_of_mulEquiv hK (e.trans CFSG.Walter.walterJ1EquivNative.symm)
    (perfCentral_of_jankoHyp CFSG.Walter.J1Props.jankoHyp)

end CFSG.Quasithin.H13.Ch4.E443.F4411
