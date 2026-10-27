module

public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOLie
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOPSp
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOPLin
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOPUni

import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256h2
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOOrder
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1Rows

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.Open
open CFSG.RankThree.PartTwo.Sec4.Ronan148L
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremB.MovingAround
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)
open CFSG.Yardstones.Md42047359a2a (lieFamily)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256c (defField)

theorem lemmaO_lie_P (hExc : FF79KLemmaOExc) {L : Type} [Group L] [Finite L]
    (hs : IsSimpleGroup L) (hna : ∃ a b : L, a * b ≠ b * a) (d : ValidLieTypeIndex)
    (he : Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hA3 : HasAbelianSylow3 L) (hB : ThreeRankLeOneInv L) {x : MulAut L} (hx3 : x ^ 3 = 1)
    (hout : ∀ c : L, x ≠ MulAut.conj c) {K : Subgroup L}
    (hKle : K ≤ x.toMonoidHom.eqLocus (MonoidHom.id L))
    (hA : Nonempty (K ≃* alternatingGroup (Fin 5)))
    (hKc : IsComponent (K.subgroupOf (x.toMonoidHom.eqLocus (MonoidHom.id L)))) :
    IsLnq 2 2 6 (⊤ : Subgroup L) ∨ IsLnq 2 5 3 (⊤ : Subgroup L) ∨
      IsLnq 3 2 2 (⊤ : Subgroup L) := by
  obtain ⟨eA⟩ := hA
  by_cases hc : lieIndexChar d.1 = 2 ∨ lieIndexChar d.1 = 5
  swap
  · exfalso
    push Not at hc
    have hfix := autFix_eq_eqLocus x
    rw [← hfix] at hKle hKc
    exact noA5ONAt_of_lie hs hna d hc.1 hc.2 he x hx3 K hKle
      (native_isQuasisimple_of_component hKle hKc) hKc.2 (Or.inl (nonempty_centerQuot_a5 eA))
  have hKO : CFSG.Open.IsComponentOf K (fixSubgroup x) := openComponentOf_of_native hKle hKc
  have hout' : ∀ c : L, MulAut.conj c ≠ x := fun c h => hout c h.symm
  have hquot := nonempty_centerQuot_a5 eA
  haveI := hs
  obtain ⟨d, hv⟩ := d
  replace hc : lieIndexChar d = 2 ∨ lieIndexChar d = 5 := hc
  have hKcard : Nat.card K = 60 := by
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Nat.factorial]
  have h3L : 3 ∣ Nat.card L :=
    (by rw [hKcard]; norm_num : 3 ∣ Nat.card K).trans (Subgroup.card_subgroup_dvd_card K)
  have hLcard : Nat.card L = I1420.lieOrderFormula d := lieOrderBridge_holds ⟨d, hv⟩ L he
  have hExc' : IsExcLieIndex d → False := fun h =>
    hExc L hs hna ⟨d, hv⟩ h he hA3 hB x hx3 hout K hKO hquot
  have hgen : lieFamily d = .exceptional → defField d ≠ 2 → defField d ≠ 4 →
      d.characteristic = 2 → False := fun hF h2 h4 hch =>
    Inputs256h.noA5Comp_exceptional_big Inputs256h.noA5TriD4Outer_holds L hs hna ⟨d, hv⟩
      ⟨hF, hch, h2, h4⟩ he x hx3 K hKO hquot
  obtain ⟨e⟩ := id he
  cases d with
  | A r q =>
    have hq3 : q.p ≠ 3 := by
      intro h
      have : lieIndexChar (.A r q) = q.p := rfl
      omega
    have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
    rcases lemmaO_linear_P r q hv he hq3 hx3 hout hKO ⟨eA⟩ hB with ⟨rfl, h | h⟩ | ⟨rfl, h⟩
    · left
      obtain ⟨h1, h2⟩ := prime_pow_eq_prime_pow q.prime_p Nat.prime_two q.exponent_pos
        (hcard.symm.trans h |>.trans (by norm_num : 64 = 2 ^ 6))
      exact isLnq_top_of_typeA hv e h1 h2
    · right; left
      obtain ⟨h1, h2⟩ := prime_pow_eq_prime_pow q.prime_p (by norm_num : Nat.Prime 5)
        q.exponent_pos (hcard.symm.trans h |>.trans (by norm_num : 125 = 5 ^ 3))
      exact isLnq_top_of_typeA hv e h1 h2
    · right; right
      obtain ⟨h1, h2⟩ := prime_pow_eq_prime_pow q.prime_p Nat.prime_two q.exponent_pos
        (hcard.symm.trans h |>.trans (by norm_num : 4 = 2 ^ 2))
      exact isLnq_top_of_typeA hv e h1 h2
  | twistedA r q =>
    exfalso
    have hq3 : q.p ≠ 3 := by
      intro h
      have : lieIndexChar (.twistedA r q) = q.p := rfl
      omega
    exact lemmaO_unitary_P r q hv he hq3 hx3 hout hKO ⟨eA⟩ hB
  | B r q =>
    exfalso
    have hq3 : q.p ≠ 3 := by
      intro h
      have : lieIndexChar (.B r q) = q.p := rfl
      omega
    have hr : 2 ≤ r ∧ ¬(r = 2 ∧ q.card = 2) :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    by_cases hr2 : r = 2
    · subst hr2
      exact lemmaO_symplectic_gen hna (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)
        hq3 hx3 hout hKO ⟨eA⟩
    · by_cases hp2 : q.p = 2
      · exact lemmaO_symplectic_gen hna
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp2 (by omega) e)
          hq3 hx3 hout hKO ⟨eA⟩
      · exact hExc' (show 3 ≤ r ∧ q.p ≠ 2 from ⟨by omega, hp2⟩)
  | C r q =>
    exfalso
    have hq3 : q.p ≠ 3 := by
      intro h
      have : lieIndexChar (.C r q) = q.p := rfl
      omega
    exact lemmaO_symplectic_gen hna
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e) hq3 hx3 hout hKO ⟨eA⟩
  | D r q =>
    exfalso
    have hr : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
    by_cases hr4 : r = 4
    · subst hr4
      by_cases hbig : q.p = 2 ∧ 8 ≤ q.card
      · obtain ⟨hq2, hq8⟩ := hbig
        rw [hq2] at hm
        have hf8 : 8 ≤ 2 ^ q.exponent := by
          have := TauCeti.PrimePower.card_def q
          rw [hq2] at this
          omega
        exact Inputs256h.noA5_omega Inputs256h.noA5D4Outer_holds hna (Or.inl rfl) hm hf8
          hx3 hKO hquot
      · apply hExc'
        show q.p ≠ 2 ∨ q.card < 8
        by_contra hcon
        exact hbig ⟨by omega, by omega⟩
    · exact Inputs256h.noA5_omega_outer Nat.prime_three (by norm_num) (Or.inl rfl) hm
        (fun _ h => absurd h hr4) x hx3 hout' K hKO hquot
  | twistedD r q =>
    exfalso
    exact Inputs256h.noA5_omega_outer Nat.prime_three (by norm_num) (Or.inr rfl)
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e)
      (fun h => absurd h (by simp)) x hx3 hout' K hKO hquot
  | E6 q =>
    exfalso
    by_cases hbig : q.p = 2 ∧ 8 ≤ q.card
    · exact hgen (by simp [lieFamily]) (by show q.card ≠ 2; omega)
        (by show q.card ≠ 4; omega) (by simpa using hbig.1)
    · exact hExc' (by show q.p ≠ 2 ∨ q.card < 8; omega)
  | E7 q =>
    exfalso
    by_cases hbig : q.p = 2 ∧ 8 ≤ q.card
    · exact hgen (by simp [lieFamily]) (by show q.card ≠ 2; omega)
        (by show q.card ≠ 4; omega) (by simpa using hbig.1)
    · exact hExc' (by show q.p ≠ 2 ∨ q.card < 8; omega)
  | E8 q =>
    exfalso
    by_cases hbig : q.p = 2 ∧ 8 ≤ q.card
    · exact hgen (by simp [lieFamily]) (by show q.card ≠ 2; omega)
        (by show q.card ≠ 4; omega) (by simpa using hbig.1)
    · exact hExc' (by show q.p ≠ 2 ∨ q.card < 8; omega)
  | F4 q =>
    exfalso
    by_cases hbig : q.p = 2 ∧ 8 ≤ q.card
    · exact hgen (by simp [lieFamily]) (by show q.card ≠ 2; omega)
        (by show q.card ≠ 4; omega) (by simpa using hbig.1)
    · exact hExc' (by show q.p ≠ 2 ∨ q.card < 8; omega)
  | G2 q =>
    exfalso
    by_cases hbig : q.p = 2 ∧ 8 ≤ q.card
    · exact hgen (by simp [lieFamily]) (by show q.card ≠ 2; omega)
        (by show q.card ≠ 4; omega) (by simpa using hbig.1)
    · exact hExc' (by show q.p ≠ 2 ∨ q.card < 8; omega)
  | twistedE6 q =>
    exfalso
    by_cases hbig : q.p = 2 ∧ 8 ≤ q.card
    · exact hgen (by simp [lieFamily]) (by show q.card ≠ 2; omega)
        (by show q.card ≠ 4; omega) (by simpa using hbig.1)
    · exact hExc' (by show q.p ≠ 2 ∨ q.card < 8; omega)
  | trialityD4 q =>
    exfalso
    by_cases hbig : q.p = 2 ∧ 8 ≤ q.card
    · exact hgen (by simp [lieFamily]) (by show q.card ≠ 2; omega)
        (by show q.card ≠ 4; omega) (by simpa using hbig.1)
    · exact hExc' (by show q.p ≠ 2 ∨ q.card < 8; omega)
  | reeF4 m => exact (hExc' (by trivial)).elim
  | tits => exact (hExc' (by trivial)).elim
  | suzuki m =>
    exact absurd (hLcard ▸ h3L) (not_three_dvd_lieOrderFormula_suzuki m)
  | reeG2 m =>
    exfalso
    have : lieIndexChar (.reeG2 m) = 3 := rfl
    omega

end CFSG.RankThree.PartTwo.Sec21.FF79
