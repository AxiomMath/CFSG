module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvPlan
import CFSG.RankThree.PartTwo.Sec10.Sec10XProofCover
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofModels
import CFSG.RankThree.PartTwo.KFacts.KS14OrdersSpor
public import CFSG.RankThree.PartTwo.Sec13.Item131a

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace M12Inv

theorem center_eq_bot_of_equiv {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : Subgroup.center T = ⊥) : Subgroup.center S = ⊥ := by
  have h1 : (Subgroup.center S).map e.toMonoidHom = ⊥ := (Subgroup.map_center_eq e).trans h
  exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center S) (f := e.toMonoidHom)
    e.injective).mp h1

noncomputable def equivQuotientCenter {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    X ≃* X ⧸ Subgroup.center X :=
  (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm)

theorem false_of_slPi_model {X : Type} [Group X] {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hPi : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    (φ : X ≃* Sec4.slPi π 3 (p ^ f) K) (eM : X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.M12) :
    False := by
  have hp : Fact p.Prime := ⟨hPi.prime⟩
  obtain ⟨ψ⟩ := Sec4.Item462AltProof.nonempty_quotient_center_slPi hPi hq
  have φc : X ⧸ Subgroup.center X ≃*
      Sec4.slPi π 3 (p ^ f) K ⧸ Subgroup.center (Sec4.slPi π 3 (p ^ f) K) :=
    QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  have hiso := Sec4.Item462AltProof.isoLThreePi_projImage_slPi hPi hq
  exact KFacts.KS14.not_isoLThreePi_M12 p f
    (Sec4.Item462AltProof.isoLThreePi_of_mulEquiv (eM.symm.trans (φc.trans ψ)) hiso)

theorem exists_prime_pow_of_isSLThreePi {X : Type} [Group X] (hX : Sec4.IsSLThreePi X) :
    ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsSLThreePiAt X (p ^ e) := by
  obtain ⟨q, K, hF, hfin, hcase⟩ := hX
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  have hnc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  rcases hcase with ⟨hK, hq, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩
  · have hqn : q = ringChar K ^ (n : ℕ) := by rw [← hK, hnc]
    refine ⟨ringChar K, n, inferInstance, n.pos, ?_⟩
    rw [← hqn]
    exact ⟨K, hF, hfin, Or.inl ⟨hK, hq, ⟨e⟩⟩⟩
  · have hqd : q ∣ ringChar K ^ (n : ℕ) := ⟨q, by rw [← hnc, hK, sq]⟩
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hqd
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, pow_zero] at hm
        rw [hm] at hq
        norm_num at hq
      · exact h0
    refine ⟨ringChar K, m, inferInstance, hm1, ?_⟩
    rw [← hm]
    exact ⟨K, hF, hfin, Or.inr ⟨hK, hq, ⟨e⟩⟩⟩

theorem false_of_isSLThreePi {X : Type} [Group X] (hSL : Sec4.IsSLThreePi X)
    (eM : X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.M12) : False := by
  obtain ⟨p, e, hp, he, hAt⟩ := exists_prime_pow_of_isSLThreePi hSL
  exact KFacts.KS14.not_isoLThreePi_M12 p e
    (Sec4.Item462AltProof.isoLThreePi_of_mulEquiv eM.symm
      (Sec4.Item462AltProof.isoLThreePi_quotient_center_of_isSLThreePiAt he hAt))

theorem false_of_isSLThreePiTwo {G : Type} [Group G] [Finite G] {F Y : Subgroup G} {b : G}
    (hD : Sec13Data G F b Y) (h7 : Sec4.IsSLThreePiTwo (lBarA b Y F))
    (eM : (Y ⧸ aschbacherSolvableCore 3 Y) ⧸ Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) ≃*
      CFSG.Blueprint.NativeSporadic.M12) : False := by
  obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData h7
  have hNn := lBar_normal hD
  have hNp := isPerfect_subgroupOf_lBar hD
  have hN1 := subgroupOf_lBar_ne_bot hD
  by_cases hq2 : 2 < p ^ f
  · have hLN : D.L₀ ≤ (Sec12.lBar b Y).subgroupOf (lBarA b Y F) := D.le_of_normal hq2 hNn hNp hN1
    have hNL : (Sec12.lBar b Y).subgroupOf (lBarA b Y F) ≤ D.L₀ := D.le_of_isPerfect hNp
    have hNL' : (Sec12.lBar b Y).subgroupOf (lBarA b Y F) = D.L₀ := le_antisymm hNL hLN
    obtain ⟨η, -⟩ := exists_lBarEquiv hD.mem_thetaComponentsAt
    exact false_of_slPi_model D.piField D.modThree
      (η.trans ((Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.trans
        ((MulEquiv.subgroupCongr hNL').trans D.e))) eM
  · exfalso
    have hp := D.piField.prime
    have hf := D.piField.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have hsolv := SLTwoData.isSolvable_of_two D h2
    have : Group.IsSolvable ((Sec12.lBar b Y).subgroupOf (lBarA b Y F)) :=
      Group.isSolvable_of_isSolvable_injective
        ((Sec12.lBar b Y).subgroupOf (lBarA b Y F)).subtype_injective
    have : Nontrivial ((Sec12.lBar b Y).subgroupOf (lBarA b Y F)) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hN1
    haveI := hNp
    exact Group.IsPerfect.not_isSolvable ((Sec12.lBar b Y).subgroupOf (lBarA b Y F)) inferInstance

end M12Inv

open M12Inv in
theorem invPartA_of (h131a : Item131a) (hspor : SporadicModels131) : InvPartA := by
  intro G _ _ F b Y hD hM
  haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  obtain ⟨e₂⟩ : Nonempty (Y ⧸ solvableRadical Y ≃* CFSG.Blueprint.NativeSporadic.M12) := hM
  have hq : CFSG.IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  obtain ⟨e₁⟩ := Sec10.Sec10XProof.nonempty_quotient_center_mulEquiv (Y := Y) hq
  have eM : (Y ⧸ aschbacherSolvableCore 3 Y) ⧸ Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) ≃*
      CFSG.Blueprint.NativeSporadic.M12 := e₁.trans e₂
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := hspor
  have toM12 : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ →
      (Y ⧸ aschbacherSolvableCore 3 Y) ≃* CFSG.Blueprint.NativeSporadic.M12 := fun hZ =>
    (equivQuotientCenter hZ).trans eM
  have key : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ ∧ b ∉ Y ∧
      Nat.card (F ⊓ Y : Subgroup G) = 9 := by
    rcases h131a G F b Y hD with ⟨hL3, -⟩ | ⟨hPGL, -, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ |
      ⟨⟨φ⟩, -⟩ | h7 | ⟨-, h8⟩
    ·
      exfalso
      obtain ⟨p, e, hp, he, hcase⟩ := hL3
      rcases hcase with ⟨hq', ⟨φ⟩⟩ | ⟨hq', ⟨φ⟩⟩
      · obtain ⟨hS, hZ⟩ := isPerfect_center_projSL p e he hq'
        obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hS hZ φ
        have ε := toM12 (center_eq_bot_of_equiv ψ hZ)
        exact KFacts.KS14.not_isoLThreePi_M12 p e (Or.inl ⟨hq', ⟨(ε.symm.trans ψ)⟩⟩)
      · by_cases hq2 : 2 < p ^ e
        · obtain ⟨hS, hZ⟩ := isPerfect_center_projSU p e he hq' hq2
          obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hS hZ φ
          have ε := toM12 (center_eq_bot_of_equiv ψ hZ)
          exact KFacts.KS14.not_isoLThreePi_M12 p e (Or.inr ⟨hq', ⟨(ε.symm.trans ψ)⟩⟩)
        · have h2 : p ^ e = 2 := by
            have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
            omega
          obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
          exact false_of_isSolvable hD isSolvable_projSU_two φ
    ·
      exfalso
      obtain ⟨hL3, hZ, -⟩ := facts_of_isZ3PGLThreePi hD hPGL
      obtain ⟨p, e, hp, he, hiso⟩ := hL3
      have ε := toM12 hZ
      rcases hiso with ⟨hq', ⟨φ⟩⟩ | ⟨hq', ⟨φ⟩⟩
      · exact KFacts.KS14.not_isoLThreePi_M12 p e (Or.inl ⟨hq', ⟨(ε.symm.trans φ)⟩⟩)
      · exact KFacts.KS14.not_isoLThreePi_M12 p e (Or.inr ⟨hq', ⟨(ε.symm.trans φ)⟩⟩)
    ·
      exfalso
      obtain ⟨hS, hZ⟩ := isPerfect_center_alt7
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hS hZ φ
      have ε := toM12 (center_eq_bot_of_equiv ψ hZ)
      exact (KFacts.KS14.isEmpty_mulEquiv_M12_alternating.2.1).false (ε.symm.trans ψ)
    ·
      exfalso
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hM22p hM22z φ
      have ε := toM12 (center_eq_bot_of_equiv ψ hM22z)
      exact KFacts.KS14.isEmpty_mulEquiv_M12_M22.false (ε.symm.trans ψ)
    ·
      obtain ⟨hbY, h9, -, ⟨ψ⟩⟩ := facts_of_prod hD hM12p hM12z φ
      exact ⟨center_eq_bot_of_equiv ψ hM12z, hbY, h9⟩
    ·
      exfalso
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hJ2p hJ2z φ
      have ε := toM12 (center_eq_bot_of_equiv ψ hJ2z)
      exact KFacts.KS14.isEmpty_mulEquiv_M12_J2.false (ε.symm.trans ψ)
    ·
      exact (false_of_isSLThreePiTwo hD h7 eM).elim
    ·
      rcases h8 with hSL | ⟨-, ⟨ε⟩⟩ | ⟨-, ⟨ε⟩⟩
      · exact (false_of_isSLThreePi hSL eM).elim
      · exact ((KFacts.KS14.isEmpty_mulEquiv_M12_alternating.2.1).false (eM.symm.trans ε)).elim
      · exact (KFacts.KS14.isEmpty_mulEquiv_M12_M22.false (eM.symm.trans ε)).elim
  exact ⟨⟨toM12 key.1⟩, key.2.1, key.2.2⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
