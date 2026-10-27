module

public import CFSG.RankThree.PartTwo.Sec13.KF135FamOddTools
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrowGlue434Out
public import CFSG.RankThree.PartTwo.Sec12.Hering129LRank
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcG2
public import CFSG.RankThree.PartOne.K133.G2Odd

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof

open CFSG Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)
open CFSG.Blueprint.Chevalley

namespace FamOdd

variable {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
  {V : Subgroup (MulAut S)}

theorem exists_isElemAbelian_of_le_pRank' {G : Type*} [Group G] [Finite G] {q : ℕ}
    [hq : Fact q.Prime] {H : Subgroup G} {k : ℕ} (hk : k ≤ CFSG.Open.pRank q H) :
    ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian q E ∧ Nat.card E = q ^ k := by
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hq.out.one_lt H
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) q (hcard ▸ pow_dvd_pow q hk)
  have hF' : CFSG.Open.IsElemAbelian q F :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (hE.comm a.1.2 b.1.2))⟩⟩,
      fun y _ => Subtype.ext (by simpa using hE.2 _ y.2)⟩
  refine ⟨(F.map E.subtype), (Subgroup.map_subtype_le F).trans hEH, hF'.map _, ?_⟩
  rw [Subgroup.card_map_of_injective Subtype.val_injective, hF]

theorem exists_elemAbelian_cube_of_le_inner (h : KF135Hyp S p P x u V) (hP : P ≤ inner S)
    (hab : ∀ Q : Sylow p S, IsMulCommutative (Q : Subgroup S)) :
    ∃ E : Subgroup S, CFSG.Open.IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hinj := conj_injective h
  set E : Subgroup S := P.comap (MulAut.conj : S →* MulAut S)
  have hEc : Nat.card E = Nat.card P := by
    have hc := Subgroup.card_map_of_injective (f := (MulAut.conj : S →* MulAut S)) (K := E) hinj
    rw [Subgroup.map_comap_eq_self hP] at hc
    exact hc.symm
  have hEp : IsPGroup p E := h.pgroup.comap_of_injective _ hinj
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  have hQc := hab Q
  refine ⟨E, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => hinj ?_⟩, hEc ▸ h.card⟩
  · have hc := congrArg (fun z : Q => (z : S)) (hQc.is_comm.comm ⟨a, hEQ a.2⟩ ⟨b, hEQ b.2⟩)
    simpa using hc
  · rw [map_pow, map_one]
    exact h.exponent _ hg

theorem false_of_rankLE2_of_sylow_abelian (h : KF135Hyp S p P x u V) (hP : P ≤ inner S)
    (hab : ∀ Q : Sylow p S, IsMulCommutative (Q : Subgroup S))
    (hr : ∀ E : Subgroup S, CFSG.Open.IsElemAbelian p E → Nat.card E ≤ p ^ 2) : False := by
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_cube_of_le_inner h hP hab
  have h1 := hr E hE
  have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
  omega

section G2


theorem g2_hyp_false {q : TauCeti.PrimePower} (hq3 : 3 < q.p) (he : q.exponent = 1)
    (hiso : Sec4.IsoGTwo S q) (h : KF135Hyp S p P x u V) : False := by
  obtain ⟨hv, ⟨φ⟩⟩ := hiso
  have hout : Nat.card (Outer S) = 1 := by
    rw [Nat.card_congr (equivalence φ).toEquiv]
    exact Sec19.SeitzScopeProof.card_outer_G2_prime hq3 he hv
  have hP := P_le_inner_of_not_dvd h (by rw [hout]; exact h.prime.not_dvd_one)
  by_cases hpr : p = q.p
  ·
    obtain ⟨H, ⟨T, hT, hT2, hHT⟩, hrank⟩ :=
      Sec12.Hering129L.exists_isTwoLocal_pRank_ge_g2 (X := S) (r := q) (by omega)
        (Or.inl ⟨rfl, ⟨hv, ⟨φ⟩⟩⟩)
    rw [he, mul_one] at hrank
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    obtain ⟨E, hEH, hE, hEc⟩ := exists_isElemAbelian_of_le_pRank' hrank
    rw [← hpr] at hE hEc
    exact false_of_h2a_witness h hE hEc hT hT2 (hHT ▸ hEH)
  ·
    have hp5 : 5 ≤ p := by linarith [h.seven_le]
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hab : ∀ Q : Sylow p S, IsMulCommutative (Q : Subgroup S) :=
      LocalAnalysis.RankFourTheoremC.crossSylowAbelianAt_G2 hv p h.prime hp5
        (by simpa [eq_comm] using hpr) S h.simple ⟨φ⟩
    refine false_of_rankLE2_of_sylow_abelian h hP hab ?_
    intro E hE
    set K := GaloisField q.p q.exponent
    have hK : Nat.card K = q.card := by
      rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
    obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv (by omega) K hK
    let ψ : S ≃* adjointGroup .G2 K := (φ.trans b.symm).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot)).trans QuotientGroup.quotientBot)
    have hKc : Nat.card K = q.p := by rw [hK, TauCeti.PrimePower.card_def, he, pow_one]
    have hKodd : Odd (Nat.card K) := by
      rw [hKc]
      exact q.prime_p.odd_of_ne_two (by omega)
    have hpK : ¬ p ∣ Nat.card K := by
      rw [hKc]
      intro hd
      exact hpr ((Nat.prime_dvd_prime_iff_eq h.prime q.prime_p).1 hd)
    have hEψ : CFSG.IsElementaryAbelian p (E.map ψ.toMonoidHom) :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.1 (hE.map _)
    have := CFSG.RankThree.PartOne.K133.card_le_sq_G2_odd K (ℓ := q.p) hKodd h.prime hp5 hpK _ hEψ
    rwa [Subgroup.card_map_of_injective ψ.injective] at this

end G2

end FamOdd

end CFSG.RankThree.PartTwo.Sec13.KF135Proof
