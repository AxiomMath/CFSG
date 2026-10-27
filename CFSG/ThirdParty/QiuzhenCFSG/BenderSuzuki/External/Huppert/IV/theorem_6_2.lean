module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_1.part_a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.corollary_9_2
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
import Mathlib.Algebra.Field.ULift

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-!
# Huppert IV.6.2

Thompson's local normal-complement theorem in the book form: for an odd prime
`q`, if `S` is a Sylow `q`-subgroup of `Q` and both `C_Q(Z(S))` and
`N_Q(J(S))` have normal `q`-complements, then `Q` has a normal
`q`-complement.

The proof below is the book-order proof body. The public theorem is the short
book statement; local `step_*` names mark the corresponding paragraphs of
Huppert IV.6.2.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

attribute [local instance] commutatorElement

universe u v

/-- Decode the first coordinate of the Huppert IV.6.2(a) score. -/
public theorem score_div_eq_left
    {a b n : ℕ} (hb : b ≤ n) :
    (a * (n + 1) + b) / (n + 1) = a := by
  have hb' : b < n + 1 := Nat.lt_succ_of_le hb
  rw [Nat.mul_comm a (n + 1)]
  rw [Nat.mul_add_div (Nat.succ_pos n) a b]
  rw [Nat.div_eq_of_lt hb']
  simp

/-- If one Huppert score is at most another, then its first coordinate is at
most the other's first coordinate. -/
public theorem score_left_le_of_score_le
    {a b c d n : ℕ} (hb : b ≤ n) (hd : d ≤ n)
    (hscore : a * (n + 1) + b ≤ c * (n + 1) + d) :
    a ≤ c := by
  have hdiv := Nat.div_le_div_right (c := n + 1) hscore
  rw [score_div_eq_left hb, score_div_eq_left hd] at hdiv
  exact hdiv

/-- If the first coordinates agree, a Huppert-score comparison compares the
second coordinates. -/
public theorem score_right_le_of_left_eq_score_le
    {a b c d n : ℕ} (hleft : a = c)
    (hscore : a * (n + 1) + b ≤ c * (n + 1) + d) :
    b ≤ d := by
  subst c
  exact Nat.add_le_add_iff_left.mp hscore

/-- Projection of maximality for Huppert IV.6.2(a): score comparison implies
comparison of the `p`-part of the normalizer order. -/
public theorem huppertIV62_normalizer_factorization_le_of_score_le
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} {U V : Subgroup Q}
    (hscore :
      Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) p *
          (Nat.card Q + 1) + Nat.card V ≤
        Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) p *
          (Nat.card Q + 1) + Nat.card U) :
    Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) p ≤
      Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) p := by
  exact score_left_le_of_score_le
    (Subgroup.card_le_card_group (H := V))
    (Subgroup.card_le_card_group (H := U)) hscore

/-- Projection of maximality for Huppert IV.6.2(a): if the normalizer `p`-parts
are equal, score comparison implies comparison of subgroup orders. -/
public theorem huppertIV62_card_le_of_factorization_eq_score_le
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} {U V : Subgroup Q}
    (hfactor :
      Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) p =
        Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) p)
    (hscore :
      Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) p *
          (Nat.card Q + 1) + Nat.card V ≤
        Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) p *
          (Nat.card Q + 1) + Nat.card U) :
    Nat.card V ≤ Nat.card U := by
  exact score_right_le_of_left_eq_score_le hfactor hscore

/-- Conjugation preserves the cardinality of a subgroup. -/
public theorem card_conj_smul
    {Q : Type u} [Group Q] (U : Subgroup Q) (g : Q) :
    Nat.card (MulAut.conj g • U : Subgroup Q) = Nat.card U := by
  exact Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) U).symm.toEquiv

/-- The normalizer of a conjugate subgroup is the conjugate of the normalizer. -/
public theorem normalizer_conj_smul_eq
    {Q : Type u} [Group Q] (U : Subgroup Q) (g : Q) :
    Subgroup.normalizer ((MulAut.conj g • U : Subgroup Q) : Set Q) =
      MulAut.conj g • Subgroup.normalizer (U : Set Q) := by
  have hmap : ((MulDistribMulAction.toMonoidEnd (MulAut Q) Q) (MulAut.conj g) : Q →* Q) =
      (MulAut.conj g : Q →* Q) := by
    ext x
    calc
      ((MulDistribMulAction.toMonoidEnd (MulAut Q) Q) (MulAut.conj g)) x
          = (MulAut.conj g) • x := rfl
      _ = (MulAut.conj g) x := rfl
  simpa [Subgroup.pointwise_smul_def, hmap] using
    (Subgroup.map_equiv_normalizer_eq (H := U) (f := MulAut.conj g)).symm

/-- A normal `p`-complement in a subgroup normalizer is invariant under
conjugating the underlying subgroup. -/
public theorem hasNormalPComplement_normalizer_conj_smul_iff
    {Q : Type u} [Group Q] {p : ℕ} (U : Subgroup Q) (g : Q) :
    HasNormalPComplement p
        (↥(Subgroup.normalizer ((MulAut.conj g • U : Subgroup Q) : Set Q))) ↔
      HasNormalPComplement p (↥(Subgroup.normalizer (U : Set Q))) := by
  let e :
      Subgroup.normalizer (U : Set Q) ≃*
        Subgroup.normalizer ((MulAut.conj g • U : Subgroup Q) : Set Q) :=
    (Subgroup.equivSMul (MulAut.conj g) (Subgroup.normalizer (U : Set Q))).trans
      (MulEquiv.subgroupCongr
        (normalizer_conj_smul_eq (U := U) (g := g)).symm)
  constructor
  · intro hconj
    exact hasNormalPComplement_of_equiv (G := _) (p := p) e.symm hconj
  · intro hU
    exact hasNormalPComplement_of_equiv (G := _) (p := p) e hU

/-- Bad `p`-subgroup membership is invariant under conjugation. -/
public theorem huppertIV62_noncomplement_pSubgroup_conj_smul_iff
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} (U : Subgroup Q) (g : Q) :
    (MulAut.conj g • U : Subgroup Q) ≠ ⊥ ∧
        IsPGroup p (MulAut.conj g • U : Subgroup Q) ∧
          ¬ HasNormalPComplement p
            (↥(Subgroup.normalizer
              ((MulAut.conj g • U : Subgroup Q) : Set Q))) ↔
      U ≠ ⊥ ∧ IsPGroup p U ∧
        ¬ HasNormalPComplement p (↥(Subgroup.normalizer (U : Set Q))) := by
  constructor
  · intro hbad
    refine ⟨?_, ?_, ?_⟩
    · intro hUbot
      have hconj_bot : (MulAut.conj g • U : Subgroup Q) = ⊥ := by
        simp [hUbot]
      exact hbad.1 hconj_bot
    · exact hbad.2.1.of_equiv
        (Subgroup.equivSMul (MulAut.conj g) U).symm
    · intro hcomp
      exact hbad.2.2
        ((hasNormalPComplement_normalizer_conj_smul_iff
          (U := U) (g := g)).2 hcomp)
  · intro hbad
    refine ⟨?_, ?_, ?_⟩
    · intro hconj_bot
      apply hbad.1
      have hback :=
        congrArg (fun T : Subgroup Q => (MulAut.conj g)⁻¹ • T) hconj_bot
      simpa using hback
    · exact hbad.2.1.of_equiv
        (Subgroup.equivSMul (MulAut.conj g) U)
    · intro hcomp
      exact hbad.2.2
        ((hasNormalPComplement_normalizer_conj_smul_iff
          (U := U) (g := g)).1 hcomp)

/-- The Huppert IV.6.2(a) score is invariant under conjugation. -/
public theorem huppertIV62_score_conj_smul_eq
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} (U : Subgroup Q) (g : Q) :
    Nat.factorization
          (Nat.card
            (Subgroup.normalizer
              ((MulAut.conj g • U : Subgroup Q) : Set Q))) p *
        (Nat.card Q + 1) + Nat.card (MulAut.conj g • U : Subgroup Q) =
      Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) p *
        (Nat.card Q + 1) + Nat.card U := by
  rw [normalizer_conj_smul_eq (U := U) (g := g)]
  rw [card_conj_smul (U := Subgroup.normalizer (U : Set Q)) (g := g)]
  rw [card_conj_smul (U := U) (g := g)]

private theorem hkt_local_sylow_map_eq_ambient_of_normalizer_top
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    {U : Subgroup Q} (S : Sylow q Q)
    (P : Sylow q (Subgroup.normalizer (U : Set Q)))
    (hNtop : Subgroup.normalizer (U : Set Q) = ⊤)
    (hPmap_le_S :
      (P : Subgroup (Subgroup.normalizer (U : Set Q))).map
          (Subgroup.normalizer (U : Set Q)).subtype ≤ (S : Subgroup Q)) :
    (P : Subgroup (Subgroup.normalizer (U : Set Q))).map
        (Subgroup.normalizer (U : Set Q)).subtype = (S : Subgroup Q) := by
  classical
  let N : Subgroup Q := Subgroup.normalizer (U : Set Q)
  let Pmap : Subgroup Q := (P : Subgroup N).map N.subtype
  have hNtop' : N = ⊤ := by simpa [N] using hNtop
  have hcardN : Nat.card N = Nat.card Q := by
    simp [hNtop']
  have hPmap_card : Nat.card Pmap = Nat.card (P : Subgroup N) := by
    simpa [Pmap, N] using
      Subgroup.card_map_of_injective
        (K := (P : Subgroup N)) (f := N.subtype) N.subtype_injective
  have hP_card_S : Nat.card (P : Subgroup N) = Nat.card (S : Subgroup Q) := by
    rw [Sylow.card_eq_multiplicity P, Sylow.card_eq_multiplicity S, hcardN]
  apply Subgroup.eq_of_le_of_card_ge
    (show Pmap ≤ (S : Subgroup Q) from by simpa [Pmap, N] using hPmap_le_S)
  rw [hPmap_card, hP_card_S]

private theorem hkt_zpowers_isPGroup_of_isPElement
    {Q : Type u} [Group Q] {q : ℕ} [Fact q.Prime] {x : Q}
    (hx : IsPElement (p := q) x) :
    IsPGroup q (Subgroup.zpowers x) := by
  rcases hx with ⟨n, hn⟩
  refine IsPGroup.of_card (p := q) (G := Subgroup.zpowers x) (n := n) ?_
  simpa [Nat.card_zpowers] using hn

private theorem hkt_pCore_sup_zpowers_isPGroup_of_isPElement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime] {x : Q}
    (hx : IsPElement (p := q) x) :
    IsPGroup q (pCore q Q ⊔ Subgroup.zpowers x : Subgroup Q) := by
  exact IsPGroup.to_sup_of_normal_left
    (p := q) (H := pCore q Q) (K := Subgroup.zpowers x)
    (pCore_isPGroup (G := Q) (p := q))
    (hkt_zpowers_isPGroup_of_isPElement (Q := Q) (q := q) hx)

private theorem hkt_pCore_lt_sup_zpowers_of_not_mem
    {Q : Type u} [Group Q] {q : ℕ} {x : Q}
    (hx_not : x ∉ pCore q Q) :
    pCore q Q < (pCore q Q ⊔ Subgroup.zpowers x : Subgroup Q) := by
  refine lt_of_le_of_ne le_sup_left ?_
  intro hsup_eq
  exact hx_not (by
    have hx_zpow : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    have hx_sup : x ∈ (pCore q Q ⊔ Subgroup.zpowers x : Subgroup Q) :=
      show x ∈ (pCore q Q ⊔ Subgroup.zpowers x : Subgroup Q) from
        (le_sup_right : Subgroup.zpowers x ≤
          (pCore q Q ⊔ Subgroup.zpowers x : Subgroup Q)) hx_zpow
    rw [← hsup_eq] at hx_sup
    exact hx_sup)

private theorem hkt_card_pCore_lt_sup_zpowers_of_not_mem
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} {x : Q}
    (hx_not : x ∉ pCore q Q) :
    Nat.card (pCore q Q) <
      Nat.card (pCore q Q ⊔ Subgroup.zpowers x : Subgroup Q) :=
  natCard_lt_of_subgroup_lt (G := Q)
    (hkt_pCore_lt_sup_zpowers_of_not_mem (Q := Q) (q := q) hx_not)

private theorem hkt_pCore_le_sylow
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    pCore q Q ≤ (S : Subgroup Q) := by
  have hsup_p : IsPGroup q ((S : Subgroup Q) ⊔ pCore q Q : Subgroup Q) :=
    IsPGroup.to_sup_of_normal_right (p := q) (H := (S : Subgroup Q))
      (K := pCore q Q) S.isPGroup' (pCore_isPGroup (G := Q) (p := q))
  have hsup_eq : (S : Subgroup Q) ⊔ pCore q Q = (S : Subgroup Q) :=
    S.is_maximal' hsup_p le_sup_left
  exact le_sup_right.trans (le_of_eq hsup_eq)

private theorem hkt_card_normalizer_quotient_lt_of_ne_bot
    {Q : Type u} [Group Q] [Finite Q] {U : Subgroup Q} (hU_ne_bot : U ≠ ⊥) :
    let N : Subgroup Q := Subgroup.normalizer (U : Set Q)
    letI : (U.subgroupOf N).Normal := hkt_subgroupOf_normalizer_normal U
    Nat.card (N ⧸ U.subgroupOf N) < Nat.card Q := by
  classical
  intro N
  let : (U.subgroupOf N).Normal := hkt_subgroupOf_normalizer_normal U
  have hU_le_N : U ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := U))
  have hUN_ne_bot : U.subgroupOf N ≠ ⊥ := by
    intro hUNbot
    apply hU_ne_bot
    have hcardU : Nat.card U = 1 := by
      rw [← natCard_subgroupOf_eq U N hU_le_N, hUNbot, Subgroup.card_bot]
    exact (Subgroup.eq_bot_iff_card (H := U)).2 hcardU
  have hquot_lt : Nat.card (N ⧸ U.subgroupOf N) < Nat.card N :=
    natCard_quotient_lt_natCard_of_ne_bot (G := N) (U.subgroupOf N) hUN_ne_bot
  exact lt_of_lt_of_le hquot_lt (Subgroup.card_le_card_group (H := N))

private theorem hkt_dvd_card_normalizer_quotient_of_lt_sylow
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) {U : Subgroup Q} (hUS : U < (S : Subgroup Q)) :
    let N : Subgroup Q := Subgroup.normalizer (U : Set Q)
    letI : (U.subgroupOf N).Normal := hkt_subgroupOf_normalizer_normal U
    q ∣ Nat.card (N ⧸ U.subgroupOf N) := by
  classical
  intro N
  let UN : Subgroup N := U.subgroupOf N
  let : UN.Normal := by
    simpa [UN, N] using hkt_subgroupOf_normalizer_normal U
  have hU_le_N : U ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := U))
  have hUN_card : Nat.card UN = Nat.card U := by
    simpa [UN, N] using
      Nat.card_congr
        ((Subgroup.subgroupOfEquivOfLe (H := U) (K := N) hU_le_N).toEquiv)
  have hfact_lt :
      Nat.factorization (Nat.card U) q <
        Nat.factorization (Nat.card N) q := by
    simpa [N] using
      hkt_factorization_lt_ambient_normalizer_of_lt_sylow (S := S) hUS
  have hcardN :
      Nat.card N = Nat.card (N ⧸ UN) * Nat.card UN := by
    simpa [UN] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := UN))
  have hquot_ne_zero : Nat.card (N ⧸ UN) ≠ 0 := Nat.card_pos.ne'
  have hUN_ne_zero : Nat.card UN ≠ 0 := Nat.card_pos.ne'
  have hfactorN :
      Nat.factorization (Nat.card N) q =
        Nat.factorization (Nat.card (N ⧸ UN)) q +
          Nat.factorization (Nat.card UN) q := by
    rw [hcardN, Nat.factorization_mul hquot_ne_zero hUN_ne_zero]
    rfl
  have hfactorQuot_pos :
      0 < Nat.factorization (Nat.card (N ⧸ UN)) q := by
    by_contra hzero
    have hfactorQuot_zero :
        Nat.factorization (Nat.card (N ⧸ UN)) q = 0 := Nat.eq_zero_of_not_pos hzero
    have hle :
        Nat.factorization (Nat.card N) q ≤ Nat.factorization (Nat.card U) q := by
      rw [hfactorN, hfactorQuot_zero, zero_add, hUN_card]
    exact (not_lt_of_ge hle) hfact_lt
  exact (Nat.Prime.dvd_iff_one_le_factorization
    (Fact.out : Nat.Prime q) hquot_ne_zero).2 hfactorQuot_pos

private theorem huppert_IV_6_2_d_normal_hasNormalPComplement_le_pCore_of_pPrimeCore_eq_bot
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥)
    (H : Subgroup Q) [H.Normal] (hcomp : HasNormalPComplement q H) :
    H ≤ pCore q Q := by
  classical
  let K : Subgroup H := pPrimeCore q H
  have hmap_le : K.map H.subtype ≤ pPrimeCore q Q := by
    simpa [K] using pPrimeCore_map_subtype_le_pPrimeCore_of_normal (G := Q) (p := q) H
  have hK_bot : K = ⊥ := by
    have hmap_bot : K.map H.subtype = ⊥ := by
      exact le_bot_iff.mp (by simpa [hcore_bot] using hmap_le)
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := K) (f := H.subtype) H.subtype_injective).1 hmap_bot
  have hquot_p : IsPGroup q (H ⧸ K) := by
    simpa [K] using
      isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
        (p := q) (H := H) hcomp
  have hH_p : IsPGroup q H := by
    let e : H ⧸ K ≃* H ⧸ (⊥ : Subgroup H) :=
      QuotientGroup.quotientMulEquivOfEq hK_bot
    have hbot : IsPGroup q (H ⧸ (⊥ : Subgroup H)) := hquot_p.of_equiv e
    exact hbot.of_equiv (QuotientGroup.quotientBot (G := H))
  exact le_sSup ⟨(inferInstance : H.Normal), hH_p⟩
private theorem hkt_iv62_h_centralizer_of_pCore_normal
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (_hcore_bot : pPrimeCore q Q = ⊥) (_hnot_Qp : ¬ IsPGroup q Q) :
    (Subgroup.centralizer ((pCore q Q : Subgroup Q) : Set Q)).Normal := by
  classical
  simpa using
    (inferInstance : (Subgroup.centralizer ((pCore q Q : Subgroup Q) : Set Q)).Normal)

private theorem hkt_iv62_h_centralizer_le_fitting_of_reduced
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (_hnot_Qp : ¬ IsPGroup q Q)
    (hsolv : Group.IsSolvable Q) :
    Subgroup.centralizer ((pCore q Q : Subgroup Q) : Set Q) ≤ fittingSubgroup Q := by
  classical
  have hfit_eq : fittingSubgroup Q = pCore q Q := Fitting_eq_pcore Q q hcore_bot
  have hcent_fit :
      Subgroup.centralizer ((fittingSubgroup Q : Subgroup Q) : Set Q) ≤
        fittingSubgroup Q :=
    centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := Q) hsolv
  simpa [hfit_eq] using hcent_fit

private theorem hkt_iv62_h_centralizer_of_pCore_nilpotent
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (hnot_Qp : ¬ IsPGroup q Q)
    (hsolv : Group.IsSolvable Q) :
    Group.IsNilpotent (Subgroup.centralizer ((pCore q Q : Subgroup Q) : Set Q)) := by
  classical
  let C : Subgroup Q := Subgroup.centralizer ((pCore q Q : Subgroup Q) : Set Q)
  have hC_le_fit : C ≤ fittingSubgroup Q := by
    simpa [C] using hkt_iv62_h_centralizer_le_fitting_of_reduced
      (Q := Q) (q := q) hcore_bot hnot_Qp hsolv
  have hC_nil : Group.IsNilpotent C := by
    exact Group.nilpotent_of_mulEquiv
      (G := C.subgroupOf (fittingSubgroup Q)) (G' := C)
      (Subgroup.subgroupOfEquivOfLe
        (G := Q) (H := C) (K := fittingSubgroup Q) hC_le_fit)
  simpa [C] using hC_nil

private theorem hkt_iv62_h_nilpotent_normal_pPrimeCore_maps_le_ambient_pPrimeCore
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (_hcore_bot : pPrimeCore q Q = ⊥) (_hnot_Qp : ¬ IsPGroup q Q)
    (N : Subgroup Q) [N.Normal]
    (_hNnil : Group.IsNilpotent N) :
    (pPrimeCore q N).map N.subtype ≤ pPrimeCore q Q := by
  classical
  exact pPrimeCore_map_subtype_le_pPrimeCore_of_normal (G := Q) (p := q) N

private theorem hkt_iv62_h_nilpotent_normal_pPrimeCore_bot_of_map_le
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥)
    (N : Subgroup Q) [N.Normal]
    (hmap : (pPrimeCore q N).map N.subtype ≤ pPrimeCore q Q) :
    pPrimeCore q N = ⊥ := by
  classical
  have hmap_bot : (pPrimeCore q N).map N.subtype = ⊥ := by
    exact le_bot_iff.mp (by simpa [hcore_bot] using hmap)
  exact (Subgroup.map_eq_bot_iff_of_injective
    (H := pPrimeCore q N) (f := N.subtype) N.subtype_injective).1 hmap_bot

private theorem hkt_iv62_h_nilpotent_normal_pPrimeCore_bot
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (hnot_Qp : ¬ IsPGroup q Q)
    (N : Subgroup Q) [hNnormal : N.Normal]
    (hNnil : Group.IsNilpotent N) :
    pPrimeCore q N = ⊥ := by
  classical
  exact hkt_iv62_h_nilpotent_normal_pPrimeCore_bot_of_map_le
    (Q := Q) (q := q) hcore_bot N
    (hkt_iv62_h_nilpotent_normal_pPrimeCore_maps_le_ambient_pPrimeCore
      (Q := Q) (q := q) hcore_bot hnot_Qp N hNnil)

private theorem hkt_iv62_h_isPGroup_of_nilpotent_non_q_pcores_bot
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (N : Subgroup Q) [N.Normal]
    (hNnil : Group.IsNilpotent N)
    (hNqprime_bot : pPrimeCore q N = ⊥) :
    IsPGroup q N := by
  classical
  have hnon_q_pcores_bot : ∀ r : ℕ, r.Prime → r ≠ q → pCore r N = ⊥ := by
    intro r hr hneq
    let : Fact r.Prime := ⟨hr⟩
    have hcore_le : pCore r N ≤ pPrimeCore q N := by
      have hcop : Nat.Coprime q (Nat.card (pCore r N)) := by
        obtain ⟨n, hcard⟩ := (pCore_isPGroup (G := N) (p := r)).exists_card_eq
        rw [hcard]
        exact ((Nat.coprime_primes (Fact.out : Nat.Prime q) hr).2 hneq.symm).pow_right n
      exact le_sSup
        (show pCore r N ∈ {K : Subgroup N | K.Normal ∧ Nat.Coprime q (Nat.card K)} from
          ⟨inferInstance, hcop⟩)
    exact le_bot_iff.mp (by simpa [hNqprime_bot] using hcore_le)
  have hnilTop : Group.IsNilpotent (↥(⊤ : Subgroup N)) := by
    exact Group.nilpotent_of_mulEquiv
      (G := N) (G' := ↥(⊤ : Subgroup N))
      (Subgroup.topEquiv.symm : N ≃* ↥(⊤ : Subgroup N))
  have hTop_le_iSup :
      (⊤ : Subgroup N) ≤
        ⨆ r : (Nat.card N).primeFactors.attach, pCore r.1 N :=
    normal_nilpotent_le_sup_pCore
      (G := N) (N := (⊤ : Subgroup N)) (hN := inferInstance) hnilTop
  have hTop_le_pCore : (⊤ : Subgroup N) ≤ pCore q N := by
    refine hTop_le_iSup.trans ?_
    refine iSup_le ?_
    intro r
    by_cases hrq : r.1 = q
    · simp [hrq]
    · have hrprime : Nat.Prime r.1 := Nat.prime_of_mem_primeFactors r.1.2
      have hbot : pCore r.1 N = ⊥ :=
        hnon_q_pcores_bot r.1 hrprime hrq
      simp [hbot]
  have htop_p : IsPGroup q (⊤ : Subgroup N) :=
    IsPGroup.to_le (H := (⊤ : Subgroup N)) (K := pCore q N)
      (pCore_isPGroup (G := N) (p := q)) hTop_le_pCore
  simpa using htop_p.of_equiv
    (Subgroup.topEquiv : (⊤ : Subgroup N) ≃* N)

private theorem hkt_iv62_h_nilpotent_normal_isPGroup_of_pPrimeCore_bot
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (N : Subgroup Q) [hNnormal : N.Normal]
    (hNnil : Group.IsNilpotent N) (hNqprime_bot : pPrimeCore q N = ⊥) :
    IsPGroup q N := by
  classical
  exact hkt_iv62_h_isPGroup_of_nilpotent_non_q_pcores_bot
    (Q := Q) (q := q) N hNnil hNqprime_bot

private theorem hkt_iv62_h_normal_pSubgroup_le_pCore
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (N : Subgroup Q) [hNnormal : N.Normal] (hNp : IsPGroup q N) :
    N ≤ pCore q Q := by
  classical
  exact le_sSup ⟨hNnormal, hNp⟩

private theorem hkt_iv62_h_nilpotent_normal_le_pCore_of_pPrimeCore_bot
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (N : Subgroup Q) [hNnormal : N.Normal]
    (hNnil : Group.IsNilpotent N) (hNqprime_bot : pPrimeCore q N = ⊥) :
    N ≤ pCore q Q := by
  classical
  exact hkt_iv62_h_normal_pSubgroup_le_pCore
    (Q := Q) (q := q) N
    (hkt_iv62_h_nilpotent_normal_isPGroup_of_pPrimeCore_bot
      (Q := Q) (q := q) N hNnil hNqprime_bot)

private theorem hkt_iv62_h_nilpotent_normal_le_pCore
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (hnot_Qp : ¬ IsPGroup q Q)
    (N : Subgroup Q) [hNnormal : N.Normal]
    (hNnil : Group.IsNilpotent N) :
    N ≤ pCore q Q := by
  classical
  have hNqprime_bot : pPrimeCore q N = ⊥ :=
    hkt_iv62_h_nilpotent_normal_pPrimeCore_bot
      (Q := Q) (q := q) hcore_bot hnot_Qp N hNnil
  exact hkt_iv62_h_nilpotent_normal_le_pCore_of_pPrimeCore_bot
    (Q := Q) (q := q) N hNnil hNqprime_bot

private theorem hkt_iv62_h_fitting_pCore_corrected_structure
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (hnot_Qp : ¬ IsPGroup q Q)
    (hsolv : Group.IsSolvable Q) :
    ∃ C : Subgroup Q,
      C = Subgroup.centralizer ((pCore q Q : Subgroup Q) : Set Q) ∧
        C.Normal ∧ Group.IsNilpotent C ∧ C ≤ pCore q Q := by
  classical
  let C : Subgroup Q := Subgroup.centralizer ((pCore q Q : Subgroup Q) : Set Q)
  have hC_normal : C.Normal := by
    simpa [C] using hkt_iv62_h_centralizer_of_pCore_normal
      (Q := Q) (q := q) hcore_bot hnot_Qp
  have : C.Normal := hC_normal
  have hC_nil : Group.IsNilpotent C := by
    simpa [C] using hkt_iv62_h_centralizer_of_pCore_nilpotent
      (Q := Q) (q := q) hcore_bot hnot_Qp hsolv
  have hC_le : C ≤ pCore q Q :=
    hkt_iv62_h_nilpotent_normal_le_pCore
      (Q := Q) (q := q) hcore_bot hnot_Qp C hC_nil
  exact ⟨C, rfl, hC_normal, hC_nil, hC_le⟩

private theorem hkt_iv62_h_fitting_pCore_self_centralizing
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (hnot_Qp : ¬ IsPGroup q Q)
    (hsolv : Group.IsSolvable Q) :
    Subgroup.centralizer ((pCore q Q : Subgroup Q) : Set Q) ≤ pCore q Q := by
  obtain ⟨C, hC_eq, _hC_normal, _hC_nil, hC_le⟩ :=
    hkt_iv62_h_fitting_pCore_corrected_structure
      (Q := Q) (q := q) hcore_bot hnot_Qp hsolv
  simpa [hC_eq] using hC_le
private theorem hkt_pCore_sup_zpowers_le_sylow_of_mem
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) {y : Q} (hyS : y ∈ (S : Subgroup Q)) :
    pCore q Q ⊔ Subgroup.zpowers y ≤ (S : Subgroup Q) := by
  refine sup_le (hkt_pCore_le_sylow (Q := Q) (q := q) S) ?_
  exact Subgroup.zpowers_le.2 hyS


private theorem hkt_normalized_pSubgroup_le_sylow
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) {A : Subgroup Q}
    (hAp : IsPGroup q A)
    (hS_le_norm_A : (S : Subgroup Q) ≤ Subgroup.normalizer (A : Set Q)) :
    A ≤ (S : Subgroup Q) := by
  have hsup_p : IsPGroup q ((S : Subgroup Q) ⊔ A : Subgroup Q) :=
    IsPGroup.to_sup_of_normal_right'
      (G := Q) (H := (S : Subgroup Q)) (K := A)
      S.isPGroup' hAp hS_le_norm_A
  have hsup_eq : (S : Subgroup Q) ⊔ A = (S : Subgroup Q) :=
    S.is_maximal' hsup_p le_sup_left
  exact le_sup_right.trans (le_of_eq hsup_eq)

private theorem hkt_pCore_sup_zpowers_le_normalizer_of_comm_mod_core
    {Q : Type u} [Group Q] {q : ℕ} {z : Q} {S : Subgroup Q}
    (hcomm : ∀ s : Q, s ∈ S → ⁅z, s⁆ ∈ pCore q Q) :
    S ≤ Subgroup.normalizer ((pCore q Q ⊔ Subgroup.zpowers z : Subgroup Q) : Set Q) := by
  classical
  let W : Subgroup Q := pCore q Q ⊔ Subgroup.zpowers z
  have hconj_z : ∀ s : Q, s ∈ S → s * z * s⁻¹ ∈ W := by
    intro s hs
    have hcomm_inv : ⁅z, s⁆⁻¹ ∈ pCore q Q :=
      (pCore q Q).inv_mem (hcomm s hs)
    refine (Subgroup.mem_sup_of_normal_left
      (s := pCore q Q) (t := Subgroup.zpowers z) (x := s * z * s⁻¹)).2 ?_
    refine ⟨⁅z, s⁆⁻¹, hcomm_inv, z, Subgroup.mem_zpowers z, ?_⟩
    simp [commutatorElement_def, mul_assoc]
  have hforward :
      ∀ s : Q, s ∈ S → ∀ x : Q, x ∈ W → s * x * s⁻¹ ∈ W := by
    intro s hs x hx
    rcases (Subgroup.mem_sup_of_normal_left
        (s := pCore q Q) (t := Subgroup.zpowers z) (x := x)).1 (by simpa [W] using hx) with
      ⟨c, hc, k, hk, rfl⟩
    have hc_conj : s * c * s⁻¹ ∈ pCore q Q :=
      (pCore_normal (G := Q) (p := q)).conj_mem c hc s
    have hk_conj : s * k * s⁻¹ ∈ W := by
      rcases Subgroup.mem_zpowers_iff.mp hk with ⟨n, rfl⟩
      simpa [conj_zpow, W] using (W.zpow_mem (hconj_z s hs) n)
    have hmul : (s * c * s⁻¹) * (s * k * s⁻¹) ∈ W :=
      W.mul_mem ((show pCore q Q ≤ W from by simp [W]) hc_conj) hk_conj
    simpa [mul_assoc] using hmul
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hforward s hs x (by simpa [W] using hx)
  · intro hx
    have hx' : s⁻¹ * (s * x * s⁻¹) * (s⁻¹)⁻¹ ∈ W :=
      hforward s⁻¹ (S.inv_mem hs) (s * x * s⁻¹) (by simpa [W] using hx)
    simpa [mul_assoc, W] using hx'

private theorem hkt_pCore_sup_zpowers_comm_mod_core_of_generator
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    {z n w : Q}
    (hzn : ⁅z, n⁆ ∈ pCore q Q)
    (hw : w ∈ (pCore q Q ⊔ Subgroup.zpowers z : Subgroup Q)) :
    ⁅w, n⁆ ∈ pCore q Q := by
  classical
  let N : Subgroup Q := pCore q Q
  let : N.Normal := by
    simpa [N] using (pCore_normal (G := Q) (p := q))
  let π : Q →* Q ⧸ N := QuotientGroup.mk' N
  let C : Subgroup Q :=
    (Subgroup.centralizer ({π n} : Set (Q ⧸ N))).comap π
  have hN_le_C : N ≤ C := by
    intro a ha
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = π n := by simpa using hy
    subst y
    simp [π, (QuotientGroup.eq_one_iff (N := N) (x := a)).2 ha]
  have hzC : z ∈ C := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = π n := by simpa using hy
    subst y
    have hcomm_q : ⁅π z, π n⁆ = 1 := by
      have hmk : π ⁅z, n⁆ = 1 :=
        (QuotientGroup.eq_one_iff (N := N) (x := ⁅z, n⁆)).2 (by
          simpa [N] using hzn)
      simpa [π] using
        (show π ⁅z, n⁆ = ⁅π z, π n⁆ from
          map_commutatorElement (f := π) (g₁ := z) (g₂ := n)).symm.trans hmk
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm_q).symm
  have hW_le_C : (pCore q Q ⊔ Subgroup.zpowers z : Subgroup Q) ≤ C := by
    refine sup_le ?_ ?_
    · intro a ha
      exact hN_le_C (by simpa [N] using ha)
    · exact Subgroup.zpowers_le.2 hzC
  have hwC : w ∈ C := hW_le_C hw
  have hwcent : π w ∈ Subgroup.centralizer ({π n} : Set (Q ⧸ N)) := by
    simpa [C] using hwC
  have hmul : π w * π n = π n * π w :=
    ((Subgroup.mem_centralizer_iff.mp hwcent) (π n) (by simp)).symm
  have hcomm_q : ⁅π w, π n⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr hmul
  have hmk : π ⁅w, n⁆ = 1 := by
    simpa [π] using
      (show π ⁅w, n⁆ = ⁅π w, π n⁆ from
        map_commutatorElement (f := π) (g₁ := w) (g₂ := n)).trans hcomm_q
  have hwN : ⁅w, n⁆ ∈ N :=
    (QuotientGroup.eq_one_iff (N := N) (x := ⁅w, n⁆)).1 hmk
  simpa [N] using hwN

/-- A `q`-element can be conjugated into any fixed Sylow `q`-subgroup. -/
private theorem hkt_exists_conj_mem_sylow_of_isPElement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) {x : Q} (hx : IsPElement (p := q) x) :
    ∃ g : Q, g * x * g⁻¹ ∈ (S : Subgroup Q) := by
  classical
  have hZp : IsPGroup q (Subgroup.zpowers x) :=
    hkt_zpowers_isPGroup_of_isPElement (Q := Q) (q := q) hx
  obtain ⟨T, hZ_le_T⟩ := IsPGroup.exists_le_sylow (G := Q) (p := q) hZp
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q T S
  have hconjT_eq_S :
      (MulAut.conj g • (T : Subgroup Q) : Subgroup Q) = (S : Subgroup Q) := by
    calc
      (MulAut.conj g • (T : Subgroup Q) : Subgroup Q) =
          ((g • T : Sylow q Q) : Subgroup Q) := by
            rw [← Sylow.coe_subgroup_smul (g := g) (P := T)]
      _ = (S : Subgroup Q) := by simp [hg]
  have hxT : x ∈ (T : Subgroup Q) :=
    hZ_le_T (Subgroup.mem_zpowers x)
  have hxConjT :
      (MulAut.conj g) x ∈ (MulAut.conj g • (T : Subgroup Q) : Subgroup Q) :=
    Set.mem_smul_set.mpr ⟨x, hxT, rfl⟩
  exact ⟨g, by simpa [MulAut.conj_apply, hconjT_eq_S] using hxConjT⟩

/-- If a conjugate of an element lies in the `q`-core, then the element itself
lies in the `q`-core. -/
private theorem hkt_mem_pCore_of_conj_mem
    {Q : Type u} [Group Q] {q : ℕ} {g x : Q}
    (hx : g * x * g⁻¹ ∈ pCore q Q) :
    x ∈ pCore q Q := by
  have hx_back :
      g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ ∈ pCore q Q :=
    (pCore_normal (G := Q) (p := q)).conj_mem (g * x * g⁻¹) hx g⁻¹
  simpa [mul_assoc] using hx_back

/-- To absorb all ambient `q`-elements into `O_q(Q)`, it is enough to absorb
the `q`-elements that already lie in a fixed Sylow subgroup. -/
private theorem hkt_isPElement_mem_pCore_of_sylow_absorption
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hS :
      ∀ y : Q, y ∈ (S : Subgroup Q) → IsPElement (p := q) y → y ∈ pCore q Q)
    {x : Q} (hx : IsPElement (p := q) x) :
    x ∈ pCore q Q := by
  classical
  obtain ⟨g, hgS⟩ := hkt_exists_conj_mem_sylow_of_isPElement (Q := Q) (q := q) S hx
  have hgx_p : IsPElement (p := q) (g * x * g⁻¹) := by
    simpa [MulAut.conj_apply] using
      (isPElement_aut_iff (G := Q) (p := q) (MulAut.conj g) x).2 hx
  exact hkt_mem_pCore_of_conj_mem (Q := Q) (q := q) (g := g) (x := x)
    (hS (g * x * g⁻¹) hgS hgx_p)


/- Huppert IV.6.2(f), internalized from the source paragraph so later have steps in this file do not depend on the old split part_f module. -/
/-- Maximality of the selected bad subgroup forces every strictly larger normal
layer inside the local Sylow subgroup to have an ambient normalizer with a normal
`q`-complement.  This is the common counting step used for both the center and
Thompson layers in `N_Q(U)/U`. -/
private theorem hkt_iv62_f_layer_ambient_normalizer_hasNormalPComplement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    {U : Subgroup Q}
    (hUmax :
      ∀ W : Subgroup Q,
        W ≠ ⊥ →
        IsPGroup q W →
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
          Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q * (Nat.card Q + 1) + Nat.card W ≤ Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q * (Nat.card Q + 1) + Nat.card U)
    (N : Subgroup Q) (hN : N = Subgroup.normalizer (U : Set Q))
    (P : Sylow q N) (K : Subgroup (P : Subgroup N)) [K.Normal]
    (hcardUK : Nat.card U < Nat.card K) :
    HasNormalPComplement q
      (Subgroup.normalizer
        (((K.map (P : Subgroup N).subtype).map N.subtype : Subgroup Q) : Set Q)) := by
  classical
  subst N
  let N : Subgroup Q := Subgroup.normalizer (U : Set Q)
  let K_N : Subgroup N := K.map (P : Subgroup N).subtype
  let V : Subgroup Q := K_N.map N.subtype
  change HasNormalPComplement q (↥(Subgroup.normalizer (V : Set Q)))
  have hK_normal : K.Normal := inferInstance
  have hcardK_N : Nat.card K_N = Nat.card K := by
    simpa [K_N, N] using
      Subgroup.card_map_of_injective (K := K) (f := (P : Subgroup N).subtype)
        (P : Subgroup N).subtype_injective
  have hcardV : Nat.card V = Nat.card K := by
    have hcardV_N : Nat.card V = Nat.card K_N := by
      simpa [V, K_N, N] using
        Subgroup.card_map_of_injective (K := K_N) (f := N.subtype) N.subtype_injective
    exact hcardV_N.trans hcardK_N
  have hV_ne_bot : V ≠ ⊥ := by
    intro hVbot
    have hcardV_one : Nat.card V = 1 := by
      rw [hVbot, Subgroup.card_bot]
    have hcardK_one : Nat.card K = 1 := by
      rw [← hcardV, hcardV_one]
    have hU_ge_one : 1 ≤ Nat.card U := Nat.succ_le_of_lt Nat.card_pos
    have hU_lt_one : Nat.card U < 1 := by
      simpa [hcardK_one] using hcardUK
    exact (not_lt_of_ge hU_ge_one) hU_lt_one
  have hKp : IsPGroup q K := P.isPGroup'.to_subgroup K
  have hK_Np : IsPGroup q K_N := by
    simpa [K_N, N] using hKp.map (P : Subgroup N).subtype
  have hVp : IsPGroup q V := by
    simpa [V, K_N, N] using hK_Np.map N.subtype
  let Pmap : Subgroup Q := (P : Subgroup N).map N.subtype
  have hPmap_card : Nat.card Pmap = Nat.card (P : Subgroup N) := by
    simpa [Pmap, N] using
      Subgroup.card_map_of_injective (K := (P : Subgroup N)) (f := N.subtype)
        N.subtype_injective
  have hPmap_le_normalizer_V : Pmap ≤ Subgroup.normalizer (V : Set Q) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨pN, hpP, rfl⟩
    let pP : (P : Subgroup N) := ⟨pN, hpP⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hzV
      rcases Subgroup.mem_map.mp hzV with ⟨kN, hkN, hkN_eq⟩
      rcases Subgroup.mem_map.mp hkN with ⟨k, hkK, hk_eq⟩
      have hk_eqN : (k : N) = kN := by simpa using hk_eq
      refine Subgroup.mem_map.mpr ⟨((pP * k * pP⁻¹ : (P : Subgroup N)) : N), ?_, ?_⟩
      · exact Subgroup.mem_map.mpr
          ⟨(pP * k * pP⁻¹ : (P : Subgroup N)),
            hK_normal.conj_mem k hkK pP, rfl⟩
      · calc
          N.subtype (((pP * k * pP⁻¹ : (P : Subgroup N)) : N)) =
              N.subtype pN * N.subtype kN * (N.subtype pN)⁻¹ := by
                simp [pP, hk_eqN, mul_assoc]
          _ = N.subtype pN * z * (N.subtype pN)⁻¹ := by rw [hkN_eq]
    · intro hzV
      rcases Subgroup.mem_map.mp hzV with ⟨kN, hkN, hkN_eq⟩
      rcases Subgroup.mem_map.mp hkN with ⟨k, hkK, hk_eq⟩
      have hk_eqN : (k : N) = kN := by simpa using hk_eq
      refine Subgroup.mem_map.mpr ⟨((pP⁻¹ * k * pP : (P : Subgroup N)) : N), ?_, ?_⟩
      · exact Subgroup.mem_map.mpr
          ⟨(pP⁻¹ * k * pP : (P : Subgroup N)),
            by simpa using hK_normal.conj_mem k hkK pP⁻¹, rfl⟩
      · calc
          N.subtype (((pP⁻¹ * k * pP : (P : Subgroup N)) : N)) =
              (N.subtype pN)⁻¹ * N.subtype kN * N.subtype pN := by
                simp [pP, hk_eqN, mul_assoc]
          _ = (N.subtype pN)⁻¹ * (N.subtype pN * z * (N.subtype pN)⁻¹) * N.subtype pN := by
                rw [hkN_eq]
          _ = z := by simp [mul_assoc]
  have hPmap_dvd_normalizer : Nat.card Pmap ∣ Nat.card (Subgroup.normalizer (V : Set Q)) :=
    Subgroup.card_dvd_of_le hPmap_le_normalizer_V
  have hfactorP :
      Nat.factorization (Nat.card (P : Subgroup N)) q =
        Nat.factorization (Nat.card N) q := by
    exact section8_factorization_card_sylow (G := N) (p := q) P
  have hfactor :
      Nat.factorization (Nat.card N) q ≤
        Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q := by
    rw [← hfactorP, ← hPmap_card]
    exact Nat.factorization_le_factorization_of_dvd_right
      hPmap_dvd_normalizer Nat.card_pos.ne' Nat.card_pos.ne'
  have hcardUV : Nat.card U < Nat.card V := by
    simpa [hcardV] using hcardUK
  by_contra hcompV
  have hscore : Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q * (Nat.card Q + 1) + Nat.card V ≤ Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q * (Nat.card Q + 1) + Nat.card U :=
    hUmax V hV_ne_bot hVp hcompV
  have hfactor_le :
      Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q ≤
        Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q :=
    huppertIV62_normalizer_factorization_le_of_score_le
      (U := U) (V := V) hscore
  have hfactor_eq :
      Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q =
        Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q :=
    le_antisymm hfactor_le (by subst N; exact hfactor)
  have hcard_le : Nat.card V ≤ Nat.card U :=
    huppertIV62_card_le_of_factorization_eq_score_le
      (U := U) (V := V) hfactor_eq hscore
  exact (not_lt_of_ge hcard_le) hcardUV
set_option maxHeartbeats 800000 in
private theorem hkt_generatorRank_le_of_surjective
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    generatorRank H ≤ generatorRank G := by
  classical
  unfold generatorRank
  by_cases hgen :
      {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤}.Nonempty
  · have hsInf_mem :
        sInf {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤} ∈
          {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤} :=
      Nat.sInf_mem hgen
    rcases hsInf_mem with ⟨s, hs⟩
    refine Nat.sInf_le ?_
    refine ⟨fun i => f (s i), ?_⟩
    apply (Subgroup.eq_top_iff' (H := Subgroup.closure (Set.range fun i => f (s i)))).2
    intro y
    rcases hf y with ⟨x, rfl⟩
    have hx : x ∈ Subgroup.closure (Set.range s) := by simp [hs]
    change f x ∈ Subgroup.closure (Set.range fun i => f (s i))
    refine Subgroup.closure_induction (k := Set.range s)
      (p := fun z _ => f z ∈ Subgroup.closure (Set.range fun i => f (s i)))
      (x := x) ?_ ?_ ?_ ?_ hx
    · rintro z ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨i, rfl⟩
    · simp
    · intro a b _ _ ha hb
      simpa [map_mul] using (Subgroup.closure (Set.range fun i => f (s i))).mul_mem ha hb
    · intro a _ ha
      simpa [MonoidHom.map_inv] using (Subgroup.closure (Set.range fun i => f (s i))).inv_mem ha
  · have hfalse : False := by
      refine hgen ?_
      refine ⟨Nat.card G, ?_⟩
      let : Fintype G := Fintype.ofFinite G
      let e : Fin (Nat.card G) → G := fun i =>
        ((finCongr (Nat.card_eq_fintype_card (α := G))).trans (Fintype.equivFin G).symm) i
      refine ⟨e, ?_⟩
      apply (Subgroup.eq_top_iff' (H := Subgroup.closure (Set.range e))).2
      intro x
      refine Subgroup.subset_closure ?_
      let e' : Fin (Nat.card G) ≃ G :=
        (finCongr (Nat.card_eq_fintype_card (α := G))).trans (Fintype.equivFin G).symm
      exact ⟨e'.symm x, by simp [e, e']⟩
    exact False.elim hfalse


/-- Huppert IV.6.2's rank version of the abelian subgroups defining `J(S)`:
abelian subgroups of `S` with maximal generator rank `m(S)`. -/
@[expose]
public def huppertRankThompsonAbelianSubgroups
    {G : Type*} [Group G] (S : Subgroup G) : Set (Subgroup G) :=
  {A : Subgroup G |
    A ≤ S ∧
      IsMulCommutative A ∧
        ∀ B : Subgroup G, B ≤ S → IsMulCommutative B →
          generatorRank B ≤ generatorRank A}

/-- Huppert IV.6.2's rank Thompson subgroup `J(S)`, generated by the abelian
subgroups of maximal generator rank. -/
@[expose]
public def huppertRankThompsonSubgroup
    {G : Type*} [Group G] (S : Subgroup G) : Subgroup G :=
  sSup (huppertRankThompsonAbelianSubgroups (G := G) S)

private theorem hkt_generatorRank_eq_of_mulEquiv
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) :
    generatorRank G = generatorRank H := by
  exact le_antisymm
    (hkt_generatorRank_le_of_surjective (G := H) (H := G) e.symm.toMonoidHom e.symm.surjective)
    (hkt_generatorRank_le_of_surjective (G := G) (H := H) e.toMonoidHom e.surjective)

private theorem hkt_huppertRankThompsonAbelianSubgroups_nonempty
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) :
    ∃ A : Subgroup G, A ∈ huppertRankThompsonAbelianSubgroups (G := G) S := by
  classical
  let candidates : Set (Subgroup G) := {A : Subgroup G | A ≤ S ∧ IsMulCommutative A}
  have hcandidates_nonempty : candidates.Nonempty := by
    refine ⟨⊥, ?_⟩
    exact ⟨bot_le, inferInstance⟩
  have hcandidates_finite : candidates.Finite := Set.toFinite candidates
  obtain ⟨A, hA, hAmax⟩ :=
    hcandidates_finite.exists_maximalFor
      (f := fun A : Subgroup G => generatorRank A) candidates hcandidates_nonempty
  rcases hA with ⟨hA_le_S, hA_comm⟩
  refine ⟨A, hA_le_S, hA_comm, ?_⟩
  intro B hB_le_S hB_comm
  by_cases hle : generatorRank A ≤ generatorRank B
  · exact hAmax ⟨hB_le_S, hB_comm⟩ hle
  · exact Nat.le_of_not_ge hle

public theorem huppertRankThompsonSubgroup_le
    {G : Type*} [Group G] (S : Subgroup G) :
    huppertRankThompsonSubgroup (G := G) S ≤ S := by
  refine sSup_le ?_
  intro A hA
  exact hA.1

private theorem hkt_huppertRankThompsonSubgroup_top_map_subtype
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) :
    (huppertRankThompsonSubgroup (G := S) (⊤ : Subgroup S)).map S.subtype =
      huppertRankThompsonSubgroup (G := G) S := by
  classical
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le ?_
    intro A hA
    exact (Subgroup.map_le_iff_le_comap).mp <| le_sSup <| by
      refine ⟨?_, ?_, ?_⟩
      · simpa using (Subgroup.map_subtype_le (H := S) (K := A))
      · let : IsMulCommutative A := hA.2.1
        exact Subgroup.map_isMulCommutative (H := A) S.subtype
      · intro B hB_le_S hB_comm
        let B' : Subgroup S := B.subgroupOf S
        have hAmax := hA.2.2 B' (by simp) (by
          let : IsMulCommutative B := hB_comm
          infer_instance)
        calc
          generatorRank B = generatorRank B' :=
            hkt_generatorRank_eq_of_mulEquiv
              (Subgroup.subgroupOfEquivOfLe (H := B) (K := S) hB_le_S).symm
          _ ≤ generatorRank A := hAmax
          _ = generatorRank (A.map S.subtype) := by
            exact hkt_generatorRank_eq_of_mulEquiv
              (Subgroup.equivMapOfInjective A S.subtype S.subtype_injective)
  · refine sSup_le ?_
    intro A hA
    have hAin :
        A.subgroupOf S ∈
          huppertRankThompsonAbelianSubgroups (G := S) (⊤ : Subgroup S) := by
      refine ⟨by simp, ?_, ?_⟩
      · let : IsMulCommutative A := hA.2.1
        infer_instance
      · intro B _ hB_comm
        have hAmax := hA.2.2 (B.map S.subtype) (by
          simpa using (Subgroup.map_subtype_le (H := S) (K := B))) (by
            let : IsMulCommutative B := hB_comm
            exact Subgroup.map_isMulCommutative (H := B) S.subtype)
        calc
          generatorRank B = generatorRank (B.map S.subtype) :=
            hkt_generatorRank_eq_of_mulEquiv
              (Subgroup.equivMapOfInjective B S.subtype S.subtype_injective)
          _ ≤ generatorRank A := hAmax
          _ = generatorRank (A.subgroupOf S) := by
            exact (hkt_generatorRank_eq_of_mulEquiv
              (Subgroup.subgroupOfEquivOfLe (H := A) (K := S) hA.1)).symm
    calc
      A = (A.subgroupOf S).map S.subtype := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hA.1]
      _ ≤ (huppertRankThompsonSubgroup (G := S) (⊤ : Subgroup S)).map S.subtype := by
        exact Subgroup.map_mono (le_sSup hAin)

private theorem hkt_huppertRankThompsonSubgroup_top_map_mulEquiv
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H] (e : G ≃* H) :
    (huppertRankThompsonSubgroup (G := G) (⊤ : Subgroup G)).map e.toMonoidHom =
      huppertRankThompsonSubgroup (G := H) (⊤ : Subgroup H) := by
  classical
  have himage :
      (MulEquiv.mapSubgroup e) ''
          huppertRankThompsonAbelianSubgroups (G := G) (⊤ : Subgroup G) =
        huppertRankThompsonAbelianSubgroups (G := H) (⊤ : Subgroup H) := by
    ext A
    constructor
    · rintro ⟨B, hB, rfl⟩
      refine ⟨by simp, ?_, ?_⟩
      · let : IsMulCommutative B := hB.2.1
        exact Subgroup.map_isMulCommutative (H := B) e.toMonoidHom
      · intro C _ hC_comm
        have hBmax := hB.2.2 (C.map e.symm.toMonoidHom) (by simp) (by
          let : IsMulCommutative C := hC_comm
          exact Subgroup.map_isMulCommutative (H := C) e.symm.toMonoidHom)
        calc
          generatorRank C = generatorRank (C.map e.symm.toMonoidHom) :=
            hkt_generatorRank_eq_of_mulEquiv
              (Subgroup.equivMapOfInjective C e.symm.toMonoidHom e.symm.injective)
          _ ≤ generatorRank B := hBmax
          _ = generatorRank (B.map e.toMonoidHom) := by
            exact hkt_generatorRank_eq_of_mulEquiv
              (Subgroup.equivMapOfInjective B e.toMonoidHom e.injective)
    · intro hA
      refine ⟨A.map e.symm.toMonoidHom, ?_, ?_⟩
      · refine ⟨by simp, ?_, ?_⟩
        · let : IsMulCommutative A := hA.2.1
          exact Subgroup.map_isMulCommutative (H := A) e.symm.toMonoidHom
        · intro C _ hC_comm
          have hAmax := hA.2.2 (C.map e.toMonoidHom) (by simp) (by
            let : IsMulCommutative C := hC_comm
            exact Subgroup.map_isMulCommutative (H := C) e.toMonoidHom)
          calc
            generatorRank C = generatorRank (C.map e.toMonoidHom) :=
              hkt_generatorRank_eq_of_mulEquiv
                (Subgroup.equivMapOfInjective C e.toMonoidHom e.injective)
            _ ≤ generatorRank A := hAmax
            _ = generatorRank (A.map e.symm.toMonoidHom) := by
              exact hkt_generatorRank_eq_of_mulEquiv
                (Subgroup.equivMapOfInjective A e.symm.toMonoidHom e.symm.injective)
      · ext x
        simp
  calc
    (huppertRankThompsonSubgroup (G := G) (⊤ : Subgroup G)).map e.toMonoidHom
        = (MulEquiv.mapSubgroup e)
            (sSup (huppertRankThompsonAbelianSubgroups (G := G) (⊤ : Subgroup G))) := rfl
    _ = sSup ((MulEquiv.mapSubgroup e) ''
          huppertRankThompsonAbelianSubgroups (G := G) (⊤ : Subgroup G)) := by
        simp
    _ = huppertRankThompsonSubgroup (G := H) (⊤ : Subgroup H) := by
        simpa [huppertRankThompsonSubgroup] using congrArg sSup himage

private theorem hkt_huppertRankThompsonSubgroup_top_characteristic
    {G : Type*} [Group G] [Finite G] :
    (huppertRankThompsonSubgroup (G := G) (⊤ : Subgroup G)).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  simpa using hkt_huppertRankThompsonSubgroup_top_map_mulEquiv (G := G) (H := G) φ

private theorem hkt_huppertRankThompsonSubgroup_le_of_mem
    {G : Type*} [Group G] [Finite G] {P R A : Subgroup G}
    (hR_le_P : R ≤ P)
    (hA : A ∈ huppertRankThompsonAbelianSubgroups (G := G) P)
    (hA_le_R : A ≤ R) :
    huppertRankThompsonSubgroup (G := G) R ≤
      huppertRankThompsonSubgroup (G := G) P := by
  refine sSup_le ?_
  intro B hB
  have hB_in_P : B ∈ huppertRankThompsonAbelianSubgroups (G := G) P := by
    refine ⟨hB.1.trans hR_le_P, hB.2.1, ?_⟩
    intro C hC_le_P hC_comm
    have hC_le_A := hA.2.2 C hC_le_P hC_comm
    have hA_le_B := hB.2.2 A hA_le_R hA.2.1
    exact hC_le_A.trans hA_le_B
  exact le_sSup hB_in_P

private theorem hkt_huppertRankThompsonAbelianSubgroups_mem_of_le
    {G : Type*} [Group G] {P R A : Subgroup G}
    (hR_le_P : R ≤ P)
    (hA : A ∈ huppertRankThompsonAbelianSubgroups (G := G) P)
    (hA_le_R : A ≤ R) :
    A ∈ huppertRankThompsonAbelianSubgroups (G := G) R := by
  refine ⟨hA_le_R, hA.2.1, ?_⟩
  intro B hB_le_R hB_comm
  exact hA.2.2 B (hB_le_R.trans hR_le_P) hB_comm

private theorem hkt_huppertRankThompsonSubgroup_eq_of_le
    {G : Type*} [Group G] [Finite G] {P R : Subgroup G}
    (hR_le_P : R ≤ P)
    (hJP_le_R : huppertRankThompsonSubgroup (G := G) P ≤ R) :
    huppertRankThompsonSubgroup (G := G) R =
      huppertRankThompsonSubgroup (G := G) P := by
  apply le_antisymm
  · obtain ⟨A, hA⟩ := hkt_huppertRankThompsonAbelianSubgroups_nonempty (G := G) P
    exact hkt_huppertRankThompsonSubgroup_le_of_mem (G := G) hR_le_P hA
      ((le_sSup hA).trans hJP_le_R)
  · refine sSup_le ?_
    intro A hA
    exact le_sSup <|
      hkt_huppertRankThompsonAbelianSubgroups_mem_of_le (G := G) hR_le_P hA
        ((le_sSup hA).trans hJP_le_R)

private theorem hkt_huppertRankThompsonSubgroup_normalizer_eq_top_of_le_pCore
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hJ_le_core :
      huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) ≤ pCore q Q) :
    Subgroup.normalizer
        (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q) = ⊤ := by
  classical
  have hcore_le_S : pCore q Q ≤ (S : Subgroup Q) :=
    hkt_pCore_le_sylow (Q := Q) (q := q) S
  have hJcore_eq_JS :
      huppertRankThompsonSubgroup (G := Q) (pCore q Q) =
        huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) :=
    hkt_huppertRankThompsonSubgroup_eq_of_le (G := Q) hcore_le_S hJ_le_core
  let JcoreSub : Subgroup (pCore q Q) :=
    huppertRankThompsonSubgroup (G := pCore q Q) (⊤ : Subgroup (pCore q Q))
  have hJcoreSub_char : JcoreSub.Characteristic := by
    simpa [JcoreSub] using
      (hkt_huppertRankThompsonSubgroup_top_characteristic (G := pCore q Q))
  have hJcore_map :
      JcoreSub.map (pCore q Q).subtype =
        huppertRankThompsonSubgroup (G := Q) (pCore q Q) := by
    simpa [JcoreSub] using
      hkt_huppertRankThompsonSubgroup_top_map_subtype (G := Q) (pCore q Q)
  have hJcore_normal :
      (huppertRankThompsonSubgroup (G := Q) (pCore q Q)).Normal := by
    have : JcoreSub.Characteristic := hJcoreSub_char
    have hmap_normal : (JcoreSub.map (pCore q Q).subtype).Normal := by
      exact ConjAct.normal_of_characteristic_of_normal
    simpa [hJcore_map] using hmap_normal
  have hJS_normal :
      (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q)).Normal := by
    simpa [hJcore_eq_JS] using hJcore_normal
  exact Subgroup.normalizer_eq_top_iff.mpr hJS_normal

/-- The rank Thompson subgroup maps to the rank Thompson subgroup of the image
Sylow after quotienting by the canonical `p'`-core. -/
private theorem hkt_huppertRankThompsonSubgroup_sylow_map_quotient_pPrimeCore
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (S : Sylow p Q) :
    let M : Subgroup Q := pPrimeCore p Q
    let π : Q →* Q ⧸ M := QuotientGroup.mk' M
    let Sbar : Sylow p (Q ⧸ M) :=
      S.mapSurjective (f := π) (QuotientGroup.mk'_surjective M)
    (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q)).map π =
      huppertRankThompsonSubgroup (G := Q ⧸ M) (Sbar : Subgroup (Q ⧸ M)) := by
  classical
  intro M π Sbar
  have hqinj : Function.Injective (π.comp (S : Subgroup Q).subtype) := by
    simpa [π, M] using
      quotient_pPrimeCore_subgroupMap_injective
        (G := Q) (p := p) (H := (S : Subgroup Q)) S.isPGroup'
  let f : S →* ((S : Subgroup Q).map π) :=
    (π.comp (S : Subgroup Q).subtype).codRestrict ((S : Subgroup Q).map π) (by
      intro x
      exact Subgroup.mem_map_of_mem π x.2)
  let e : S ≃* ((S : Subgroup Q).map π) := by
    refine MulEquiv.ofBijective f ⟨?_, ?_⟩
    · intro a b hab
      exact hqinj <| by exact congrArg Subtype.val hab
    · intro x
      rcases Subgroup.mem_map.mp x.2 with ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      apply Subtype.ext
      exact hxy
  have hcomp :
      ((Subgroup.subtype ((S : Subgroup Q).map π)).comp e.toMonoidHom) =
        π.comp (S : Subgroup Q).subtype := by
    rfl
  calc
    (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q)).map π =
        ((huppertRankThompsonSubgroup (G := S) (⊤ : Subgroup S)).map
          (S : Subgroup Q).subtype).map π := by
          rw [hkt_huppertRankThompsonSubgroup_top_map_subtype]
    _ = (huppertRankThompsonSubgroup (G := S) (⊤ : Subgroup S)).map
          (π.comp (S : Subgroup Q).subtype) := by
          rw [Subgroup.map_map]
    _ = ((huppertRankThompsonSubgroup (G := S) (⊤ : Subgroup S)).map e.toMonoidHom).map
          (Subgroup.subtype ((S : Subgroup Q).map π)) := by
          rw [Subgroup.map_map, hcomp]
    _ = (huppertRankThompsonSubgroup (G := ((S : Subgroup Q).map π))
          (⊤ : Subgroup ((S : Subgroup Q).map π))).map
          (Subgroup.subtype ((S : Subgroup Q).map π)) := by
          rw [hkt_huppertRankThompsonSubgroup_top_map_mulEquiv]
    _ = huppertRankThompsonSubgroup (G := Q ⧸ M) (Sbar : Subgroup (Q ⧸ M)) := by
          simpa [Sbar, Sylow.coe_mapSurjective] using
            hkt_huppertRankThompsonSubgroup_top_map_subtype
              (G := Q ⧸ M) ((S : Subgroup Q).map π)

/-- The local normal-complement hypothesis for Huppert's rank `J(S)` descends
to the canonical `p'`-core quotient. -/
private theorem hkt_normalizer_huppertRankThompsonSubgroup_hasNormalPComplement_quotient_pPrimeCore
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (S : Sylow p Q)
    (hcomp : HasNormalPComplement p
      (↥(Subgroup.normalizer
        (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q)))) :
    let M : Subgroup Q := pPrimeCore p Q
    let π : Q →* Q ⧸ M := QuotientGroup.mk' M
    let Sbar : Sylow p (Q ⧸ M) :=
      S.mapSurjective (f := π) (QuotientGroup.mk'_surjective M)
    HasNormalPComplement p
      (↥(Subgroup.normalizer
        (huppertRankThompsonSubgroup (G := Q ⧸ M) (Sbar : Subgroup (Q ⧸ M)) :
          Set (Q ⧸ M)))) := by
  classical
  intro M π Sbar
  have : Fact (IsPGroup p (↥(huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q)))) :=
    ⟨IsPGroup.to_le S.isPGroup' (huppertRankThompsonSubgroup_le (G := Q) (S : Subgroup Q))⟩
  have hJ_map :
      (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q)).map π =
        huppertRankThompsonSubgroup (G := Q ⧸ M) (Sbar : Subgroup (Q ⧸ M)) := by
    simpa [M, π, Sbar] using
      hkt_huppertRankThompsonSubgroup_sylow_map_quotient_pPrimeCore (Q := Q) (p := p) S
  have hnorm_eq :
      Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q ⧸ M) (Sbar : Subgroup (Q ⧸ M)) :
            Set (Q ⧸ M)) =
        (Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q)).map π := by
    simpa [π, M, hJ_map] using
      (normalizer_map_quotient_eq_map_normalizer
        (G := Q) (p := p)
        (T := huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q)) (M := M)
        (inferInstance : M.Normal)
        (by simpa [M] using (pPrimeCore_coprime_card (G := Q) (p := p))))
  rw [hnorm_eq]
  exact hkt_hasNormalPComplement_map_quotient_pPrimeCore
    (Q := Q) (p := p)
    (H := Subgroup.normalizer
      (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q)) hcomp

set_option maxHeartbeats 800000 in
/-- Sentence 2 of Huppert IV.6.2(f): by parts (b),(c), applied recursively to
`N_Q(U)/U`, the quotient `N_Q(U)/U` has a normal `q`-complement. -/
private theorem hkt_iv62_f_normalizer_quotient_hasNormalPComplement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hsmall_rec : ∀ {R : Type u} [Group R] [Finite R] (T : Sylow q R), Nat.card R < Nat.card Q → q ∣ Nat.card R → HasNormalPComplement q (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R)) → HasNormalPComplement q (Subgroup.normalizer (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R)) → HasNormalPComplement q R)
    {U : Subgroup Q}
    (hU_ne_bot : U ≠ ⊥) (_hU_p : IsPGroup q U)
    (_hU_no_complement : ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))))
    (hUmax :
      ∀ W : Subgroup Q,
        W ≠ ⊥ →
        IsPGroup q W →
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
          Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q * (Nat.card Q + 1) + Nat.card W ≤ Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q * (Nat.card Q + 1) + Nat.card U)
    (P : Sylow q (Subgroup.normalizer (U : Set Q)))
    (hUS : U < (S : Subgroup Q))
    (hUN_le_P :
      U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≤
        (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hcardUP :
      Nat.card U < Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q)))) :
    let N : Subgroup Q := Subgroup.normalizer (U : Set Q)
    let UN : Subgroup N := U.subgroupOf N
    letI : UN.Normal := hkt_subgroupOf_normalizer_normal U
    HasNormalPComplement q (N ⧸ UN) := by
  classical
  let N : Subgroup Q := Subgroup.normalizer (U : Set Q)
  let UN : Subgroup N := U.subgroupOf N
  let : UN.Normal := by
    simpa [UN, N] using hkt_subgroupOf_normalizer_normal U
  let qN : N →* N ⧸ UN := QuotientGroup.mk' UN
  let Pbar : Sylow q (N ⧸ UN) :=
    P.mapSurjective (f := qN) (QuotientGroup.mk'_surjective UN)
  have hPbar_eq : (Pbar : Subgroup (N ⧸ UN)) = (P : Subgroup N).map qN := by
    simp [Pbar, Sylow.coe_mapSurjective]
  have hcard_lt : Nat.card (N ⧸ UN) < Nat.card Q := by
    simpa [N, UN] using hkt_card_normalizer_quotient_lt_of_ne_bot (Q := Q) hU_ne_bot
  have hq_dvd_quot : q ∣ Nat.card (N ⧸ UN) := by
    simpa [N, UN] using
      hkt_dvd_card_normalizer_quotient_of_lt_sylow (Q := Q) (q := q) (S := S) hUS
  have hcenter_comp : HasNormalPComplement q
      (Subgroup.centralizer
        (centerIn (G := N ⧸ UN) (Pbar : Subgroup (N ⧸ UN)) : Set (N ⧸ UN))) := by
    let UP : Subgroup (P : Subgroup N) := UN.subgroupOf (P : Subgroup N)
    let Zbar : Subgroup ((P : Subgroup N) ⧸ UP) := Subgroup.center ((P : Subgroup N) ⧸ UP)
    let K : Subgroup (P : Subgroup N) := Zbar.comap (QuotientGroup.mk' UP)
    let K_N : Subgroup N := K.map (P : Subgroup N).subtype
    have hUN_le_P' : UN ≤ (P : Subgroup N) := by
      simpa [UN, N] using hUN_le_P
    have hUN_normal : UN.Normal := by
      simpa [UN, N] using hkt_subgroupOf_normalizer_normal U
    let : UN.Normal := hUN_normal
    have hUP_normal : UP.Normal := by
      simpa [UP] using (inferInstance : (UN.subgroupOf (P : Subgroup N)).Normal)
    let : UP.Normal := hUP_normal
    have hUN_le_KN : UN ≤ K_N := by
      intro u hu
      refine Subgroup.mem_map.mpr ?_
      let uP : (P : Subgroup N) := ⟨u, hUN_le_P' hu⟩
      refine ⟨uP, ?_, rfl⟩
      have huUP : uP ∈ UP := by
        simpa [uP, UP, Subgroup.mem_subgroupOf] using hu
      dsimp [K]
      change QuotientGroup.mk' UP uP ∈ Zbar
      have hqu : QuotientGroup.mk' UP uP = 1 :=
        (QuotientGroup.eq_one_iff (N := UP) (x := uP)).2 huUP
      simp [hqu]
    have hcomp_ambient : HasNormalPComplement q
        (Subgroup.normalizer ((K_N.map N.subtype : Subgroup Q) : Set Q)) := by
      have hU_le_N : U <= N := by
        simpa [N] using (Subgroup.le_normalizer (H := U))
      have hUN_card : Nat.card UN = Nat.card U := by
        simpa [UN, N] using
          Nat.card_congr
            ((Subgroup.subgroupOfEquivOfLe (H := U) (K := N) hU_le_N).toEquiv)
      have hUP_card : Nat.card UP = Nat.card U := by
        have hUP_UN : Nat.card UP = Nat.card UN := by
          simpa [UP] using
            Nat.card_congr
              ((Subgroup.subgroupOfEquivOfLe (H := UN) (K := (P : Subgroup N))
                hUN_le_P').toEquiv)
        exact hUP_UN.trans hUN_card
      have hUP_lt : Nat.card UP < Nat.card (P : Subgroup N) := by
        simpa [hUP_card, N] using hcardUP
      have hK_card : Nat.card U < Nat.card K := by
        have hcenter : Nat.card UP < Nat.card K := by
          dsimp [Zbar, K]
          exact hkt_center_quotient_comap_card_gt
            (G := (P : Subgroup N)) (p := q) (H := UP) P.isPGroup' hUP_lt
        exact hUP_card ▸ hcenter
      simpa [K_N] using
        hkt_iv62_f_layer_ambient_normalizer_hasNormalPComplement
          (Q := Q) (q := q) (U := U) hUmax N rfl P K hK_card
    have hcomp_intrinsic : HasNormalPComplement q (Subgroup.normalizer (K_N : Set N)) :=
      hkt_hasNormalPComplement_normalizer_subgroupOf_of_ambient_image
        (G := Q) (p := q) (N := N) (K := K_N) hcomp_ambient
    have hcenter_eq :
        K_N.map qN = centerIn (G := N ⧸ UN) ((P : Subgroup N).map qN) := by
      have := hkt_centerIn_map_quotient_subgroup_eq
          (G := N) (N := UN) (P := (P : Subgroup N)) hUN_le_P'
      simpa [K_N, K, Zbar, UP] using this
    have hcomp_quot : HasNormalPComplement q
        (Subgroup.centralizer (K_N.map qN : Set (N ⧸ UN))) := by
      change HasNormalPComplement q
        (Subgroup.centralizer (K_N.map (QuotientGroup.mk' UN) : Set (N ⧸ UN)))
      exact hkt_hasNormalPComplement_centralizer_map_quotient_of_normalizer
        (G := N) (p := q) (N := UN) (T := K_N) hUN_le_KN hcomp_intrinsic
    rw [hcenter_eq] at hcomp_quot
    rw [hPbar_eq]; exact hcomp_quot
  have hJ_comp : HasNormalPComplement q
      (Subgroup.normalizer
        (thompsonSubgroup (G := N ⧸ UN) (Pbar : Subgroup (N ⧸ UN)) :
          Set (N ⧸ UN))) := by
    let UP : Subgroup (P : Subgroup N) := UN.subgroupOf (P : Subgroup N)
    let Jbar : Subgroup ((P : Subgroup N) ⧸ UP) :=
      thompsonSubgroup (G := ((P : Subgroup N) ⧸ UP)) ⊤
    let K : Subgroup (P : Subgroup N) := Jbar.comap (QuotientGroup.mk' UP)
    let K_N : Subgroup N := K.map (P : Subgroup N).subtype
    have hUN_le_P' : UN ≤ (P : Subgroup N) := by
      simpa [UN, N] using hUN_le_P
    have hUN_normal : UN.Normal := by
      simpa [UN, N] using hkt_subgroupOf_normalizer_normal U
    let : UN.Normal := hUN_normal
    have hUP_normal : UP.Normal := by
      simpa [UP] using (inferInstance : (UN.subgroupOf (P : Subgroup N)).Normal)
    let : UP.Normal := hUP_normal
    have hUN_le_KN : UN ≤ K_N := by
      intro u hu
      refine Subgroup.mem_map.mpr ?_
      let uP : (P : Subgroup N) := ⟨u, hUN_le_P' hu⟩
      refine ⟨uP, ?_, rfl⟩
      have huUP : uP ∈ UP := by
        simpa [uP, UP, Subgroup.mem_subgroupOf] using hu
      dsimp [K]
      change QuotientGroup.mk' UP uP ∈ Jbar
      have hqu : QuotientGroup.mk' UP uP = 1 :=
        (QuotientGroup.eq_one_iff (N := UP) (x := uP)).2 huUP
      simp [hqu]
    have hcomp_ambient : HasNormalPComplement q
        (Subgroup.normalizer ((K_N.map N.subtype : Subgroup Q) : Set Q)) := by
      have hU_le_N : U <= N := by
        simpa [N] using (Subgroup.le_normalizer (H := U))
      have hUN_card : Nat.card UN = Nat.card U := by
        simpa [UN, N] using
          Nat.card_congr
            ((Subgroup.subgroupOfEquivOfLe (H := U) (K := N) hU_le_N).toEquiv)
      have hUP_card : Nat.card UP = Nat.card U := by
        have hUP_UN : Nat.card UP = Nat.card UN := by
          simpa [UP] using
            Nat.card_congr
              ((Subgroup.subgroupOfEquivOfLe (H := UN) (K := (P : Subgroup N))
                hUN_le_P').toEquiv)
        exact hUP_UN.trans hUN_card
      have hUP_lt : Nat.card UP < Nat.card (P : Subgroup N) := by
        simpa [hUP_card, N] using hcardUP
      have hK_card : Nat.card U < Nat.card K := by
        have hJ : Nat.card UP < Nat.card K := by
          dsimp [Jbar, K]
          exact hkt_thompson_quotient_comap_card_gt
            (G := (P : Subgroup N)) (H := UP) hUP_lt
        exact hUP_card ▸ hJ
      have hJbar_normal : Jbar.Normal := by
        have : Jbar.Characteristic := by
          dsimp [Jbar]
          exact section8_thompsonSubgroup_top_characteristic
            (G := ((P : Subgroup N) ⧸ UP))
        infer_instance
      have : K.Normal := by
        dsimp [K]
        exact hJbar_normal.comap (QuotientGroup.mk' UP)
      simpa [K_N] using
        hkt_iv62_f_layer_ambient_normalizer_hasNormalPComplement
          (Q := Q) (q := q) (U := U) hUmax N rfl P K hK_card
    have hcomp_intrinsic : HasNormalPComplement q (Subgroup.normalizer (K_N : Set N)) :=
      hkt_hasNormalPComplement_normalizer_subgroupOf_of_ambient_image
        (G := Q) (p := q) (N := N) (K := K_N) hcomp_ambient
    have hJ_eq :
        K_N.map qN = thompsonSubgroup (G := N ⧸ UN) ((P : Subgroup N).map qN) := by
      simpa [qN, UP, Jbar, K, K_N] using
        hkt_thompsonSubgroup_map_quotient_subgroup_eq
          (G := N) (N := UN) (P := (P : Subgroup N)) hUN_le_P'
    have hcomp_quot : HasNormalPComplement q
        (Subgroup.normalizer (K_N.map qN : Set (N ⧸ UN))) := by
      change HasNormalPComplement q
        (Subgroup.normalizer (K_N.map (QuotientGroup.mk' UN) : Set (N ⧸ UN)))
      exact hkt_hasNormalPComplement_normalizer_map_quotient_of_normalizer
        (G := N) (p := q) (N := UN) (T := K_N) hUN_le_KN hcomp_intrinsic
    rw [hJ_eq] at hcomp_quot
    rw [hPbar_eq]; exact hcomp_quot
  have hJrank_comp : HasNormalPComplement q
      (Subgroup.normalizer
        (huppertRankThompsonSubgroup (G := N ⧸ UN) (Pbar : Subgroup (N ⧸ UN)) :
          Set (N ⧸ UN))) := by
    let UP : Subgroup (P : Subgroup N) := UN.subgroupOf (P : Subgroup N)
    let Jbar : Subgroup ((P : Subgroup N) ⧸ UP) :=
      huppertRankThompsonSubgroup (G := ((P : Subgroup N) ⧸ UP)) ⊤
    let K : Subgroup (P : Subgroup N) := Jbar.comap (QuotientGroup.mk' UP)
    let K_N : Subgroup N := K.map (P : Subgroup N).subtype
    have hUN_le_P' : UN ≤ (P : Subgroup N) := by
      simpa [UN, N] using hUN_le_P
    have hUN_normal : UN.Normal := by
      simpa [UN, N] using hkt_subgroupOf_normalizer_normal U
    let : UN.Normal := hUN_normal
    have hUP_normal : UP.Normal := by
      simpa [UP] using (inferInstance : (UN.subgroupOf (P : Subgroup N)).Normal)
    let : UP.Normal := hUP_normal
    have hUN_le_KN : UN ≤ K_N := by
      intro u hu
      refine Subgroup.mem_map.mpr ?_
      let uP : (P : Subgroup N) := ⟨u, hUN_le_P' hu⟩
      refine ⟨uP, ?_, rfl⟩
      have huUP : uP ∈ UP := by
        simpa [uP, UP, Subgroup.mem_subgroupOf] using hu
      dsimp [K]
      change QuotientGroup.mk' UP uP ∈ Jbar
      have hqu : QuotientGroup.mk' UP uP = 1 :=
        (QuotientGroup.eq_one_iff (N := UP) (x := uP)).2 huUP
      simp [hqu]
    have hcomp_ambient : HasNormalPComplement q
        (Subgroup.normalizer ((K_N.map N.subtype : Subgroup Q) : Set Q)) := by
      have hU_le_N : U <= N := by
        simpa [N] using (Subgroup.le_normalizer (H := U))
      have hUN_card : Nat.card UN = Nat.card U := by
        simpa [UN, N] using
          Nat.card_congr
            ((Subgroup.subgroupOfEquivOfLe (H := U) (K := N) hU_le_N).toEquiv)
      have hUP_card : Nat.card UP = Nat.card U := by
        have hUP_UN : Nat.card UP = Nat.card UN := by
          simpa [UP] using
            Nat.card_congr
              ((Subgroup.subgroupOfEquivOfLe (H := UN) (K := (P : Subgroup N))
                hUN_le_P').toEquiv)
        exact hUP_UN.trans hUN_card
      have hUP_lt : Nat.card UP < Nat.card (P : Subgroup N) := by
        simpa [hUP_card, N] using hcardUP
      have hK_card : Nat.card U < Nat.card K := by
        let R := (P : Subgroup N) ⧸ UP
        let : Group R := by
          dsimp [R]
          infer_instance
        let : Finite R := by
          dsimp [R]
          infer_instance
        let Zbar : Subgroup R := Subgroup.center R
        let KZ : Subgroup (P : Subgroup N) :=
          Zbar.comap (QuotientGroup.mk' UP)
        have hZJ : Zbar ≤ Jbar := by
          have : Fact (IsPGroup q R) :=
            ⟨IsPGroup.to_quotient (H := UP) P.isPGroup'⟩
          obtain ⟨A, hA⟩ :=
            hkt_huppertRankThompsonAbelianSubgroups_nonempty
              (G := R) (⊤ : Subgroup R)
          let AZ : Subgroup R := A ⊔ Zbar
          have hZ_comm : IsMulCommutative Zbar := by
            dsimp [Zbar]
            infer_instance
          have hZ_le_cent_A : Zbar ≤ Subgroup.centralizer (A : Set R) := by
            intro z hz
            rw [Subgroup.mem_centralizer_iff]
            intro a ha
            symm
            exact (Subgroup.mem_center_iff.mp hz a).symm
          have hA_le_cent_Z : A ≤ Subgroup.centralizer (Zbar : Set R) := by
            intro a ha
            rw [Subgroup.mem_centralizer_iff]
            intro z hz
            symm
            exact Subgroup.mem_center_iff.mp hz a
          have hAZ_comm : IsMulCommutative AZ := by
            have hA_self : A ≤ Subgroup.centralizer (A : Set R) :=
              (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1
            have hZ_self : Zbar ≤ Subgroup.centralizer (Zbar : Set R) :=
              (Subgroup.le_centralizer_iff_isMulCommutative (K := Zbar)).2 hZ_comm
            have hsupA : AZ ≤ Subgroup.centralizer (A : Set R) :=
              sup_le hA_self hZ_le_cent_A
            have hsupZ : AZ ≤ Subgroup.centralizer (Zbar : Set R) :=
              sup_le hA_le_cent_Z hZ_self
            exact (Subgroup.le_centralizer_iff_isMulCommutative (K := AZ)).1
              (Subgroup.le_centralizer_sup_of_le_centralizers hsupA hsupZ)
          have hA_rank_le_AZ : generatorRank A ≤ generatorRank AZ := by
            have hAp : IsPGroup q A :=
              (Fact.out : IsPGroup q R).to_subgroup A
            have hAZp : IsPGroup q AZ :=
              (Fact.out : IsPGroup q R).to_subgroup AZ
            let : Fact (IsPGroup q A) := ⟨hAp⟩
            let : IsMulCommutative A := hA.2.1
            let A' : Subgroup AZ := A.subgroupOf AZ
            let e : A' ≃* A :=
              Subgroup.subgroupOfEquivOfLe (H := A) (K := AZ) le_sup_left
            exact
              (generatorRank_le_groupRank_of_commutative_pgroup (p := q) A).trans
                ((groupRank_le_of_equiv e).trans
                  ((groupRank_le_of_subgroup A').trans
                    (groupRank_le_generatorRank_of_commutative_pgroup
                      (p := q) hAZp hAZ_comm)))
          have hAZ_mem : AZ ∈
              huppertRankThompsonAbelianSubgroups (G := R) (⊤ : Subgroup R) := by
            refine ⟨by simp, hAZ_comm, ?_⟩
            intro C _ hCcomm
            exact (hA.2.2 C (by simp) hCcomm).trans hA_rank_le_AZ
          have hAZ_le : AZ ≤ Jbar := by
            dsimp [Jbar, huppertRankThompsonSubgroup]
            exact le_sSup hAZ_mem
          exact le_sup_right.trans hAZ_le
        have hKZ_le_K : KZ ≤ K := by
          exact Subgroup.comap_mono hZJ
        have hKZ_card : Nat.card U < Nat.card KZ := by
          have hcenter : Nat.card UP < Nat.card KZ := by
            dsimp [Zbar, KZ]
            exact hkt_center_quotient_comap_card_gt
              (G := (P : Subgroup N)) (p := q) (H := UP) P.isPGroup' hUP_lt
          exact hUP_card ▸ hcenter
        exact hKZ_card.trans_le (Subgroup.card_le_of_le hKZ_le_K)
      have hJbar_normal : Jbar.Normal := by
        have : Jbar.Characteristic := by
          dsimp [Jbar]
          exact hkt_huppertRankThompsonSubgroup_top_characteristic
            (G := ((P : Subgroup N) ⧸ UP))
        infer_instance
      have : K.Normal := by
        dsimp [K]
        exact hJbar_normal.comap (QuotientGroup.mk' UP)
      simpa [K_N] using
        hkt_iv62_f_layer_ambient_normalizer_hasNormalPComplement
          (Q := Q) (q := q) (U := U) hUmax N rfl P K hK_card
    have hcomp_intrinsic : HasNormalPComplement q (Subgroup.normalizer (K_N : Set N)) :=
      hkt_hasNormalPComplement_normalizer_subgroupOf_of_ambient_image
        (G := Q) (p := q) (N := N) (K := K_N) hcomp_ambient
    have hJ_eq :
        K_N.map qN =
          huppertRankThompsonSubgroup (G := N ⧸ UN) ((P : Subgroup N).map qN) := by
      let e : (P : Subgroup N) ⧸ UP ≃* (P : Subgroup N).map qN :=
        quotientSubgroupRangeEquiv (P : Subgroup N) UN
      calc
        K_N.map qN = K.map (qN.comp (P : Subgroup N).subtype) := by
          simp [K_N, Subgroup.map_map]
        _ = (Jbar.map e.toMonoidHom).map ((P : Subgroup N).map qN).subtype := by
          ext x
          constructor
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨k, hkK, rfl⟩
            refine Subgroup.mem_map.mpr ⟨e (QuotientGroup.mk' UP k), ?_, ?_⟩
            · exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' UP k,
                (by simpa [K] using hkK), rfl⟩
            · simpa [e, qN] using
                quotientSubgroupRangeEquiv_apply_mk (P : Subgroup N) UN k
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨z, hz, hzval⟩
            rcases Subgroup.mem_map.mp hz with ⟨zq, hzJ, rfl⟩
            obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective UP zq
            refine Subgroup.mem_map.mpr ⟨k, hzJ, ?_⟩
            calc
              qN ((k : (P : Subgroup N)) : N) =
                  (e (QuotientGroup.mk' UP k) : N ⧸ UN) := by
                simpa [e, qN] using
                  (quotientSubgroupRangeEquiv_apply_mk (P : Subgroup N) UN k).symm
              _ = x := hzval
        _ = (huppertRankThompsonSubgroup
              (G := (P : Subgroup N).map qN) ⊤).map
              ((P : Subgroup N).map qN).subtype := by
          have hJ_map : Jbar.map e.toMonoidHom =
              huppertRankThompsonSubgroup (G := (P : Subgroup N).map qN) ⊤ := by
            simpa [Jbar] using
              hkt_huppertRankThompsonSubgroup_top_map_mulEquiv e
          rw [hJ_map]
        _ = huppertRankThompsonSubgroup (G := N ⧸ UN) ((P : Subgroup N).map qN) := by
          simpa using hkt_huppertRankThompsonSubgroup_top_map_subtype
            (G := N ⧸ UN) ((P : Subgroup N).map qN)
    have hcomp_quot : HasNormalPComplement q
        (Subgroup.normalizer (K_N.map qN : Set (N ⧸ UN))) := by
      change HasNormalPComplement q
        (Subgroup.normalizer (K_N.map (QuotientGroup.mk' UN) : Set (N ⧸ UN)))
      exact hkt_hasNormalPComplement_normalizer_map_quotient_of_normalizer
        (G := N) (p := q) (N := UN) (T := K_N) hUN_le_KN hcomp_intrinsic
    rw [hJ_eq] at hcomp_quot
    rw [hPbar_eq]; exact hcomp_quot
  exact hsmall_rec Pbar hcard_lt hq_dvd_quot hcenter_comp hJrank_comp

/-- Sentence 2 of Huppert IV.6.2(f), rewritten using `N_Q(U)=Q` and
`U=O_q(Q)`: the quotient `Q/O_q(Q)` has a normal `q`-complement. -/
private theorem hkt_iv62_f_pCore_quotient_hasNormalPComplement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hsmall_rec : ∀ {R : Type u} [Group R] [Finite R] (T : Sylow q R), Nat.card R < Nat.card Q → q ∣ Nat.card R → HasNormalPComplement q (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R)) → HasNormalPComplement q (Subgroup.normalizer (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R)) → HasNormalPComplement q R)
    {U : Subgroup Q}
    (hU_ne_bot : U ≠ ⊥) (_hU_p : IsPGroup q U)
    (_hU_no_complement : ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))))
    (hUmax :
      ∀ W : Subgroup Q,
        W ≠ ⊥ →
        IsPGroup q W →
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
          Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q * (Nat.card Q + 1) + Nat.card W ≤ Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q * (Nat.card Q + 1) + Nat.card U)
    (P : Sylow q (Subgroup.normalizer (U : Set Q)))
    (hUS : U < (S : Subgroup Q))
    (hUN_le_P :
      U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≤
        (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hcardUP :
      Nat.card U < Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hNtop : Subgroup.normalizer (U : Set Q) = ⊤)
    (hU_eq_core : U = pCore q Q) :
    HasNormalPComplement q (Q ⧸ pCore q Q) := by
  classical
  let N : Subgroup Q := Subgroup.normalizer (U : Set Q)
  let UN : Subgroup N := U.subgroupOf N
  let : UN.Normal := by
    simpa [UN, N] using hkt_subgroupOf_normalizer_normal U
  have hcomp_N : HasNormalPComplement q (N ⧸ UN) := by
    simpa [N, UN] using
      hkt_iv62_f_normalizer_quotient_hasNormalPComplement
        (Q := Q) (q := q) S hsmall_rec hU_ne_bot _hU_p _hU_no_complement hUmax P hUS hUN_le_P hcardUP
  let TopQ : Subgroup Q := ⊤
  let : ((pCore q Q).subgroupOf TopQ).Normal := by
    simpa [TopQ] using
      (Subgroup.Normal.subgroupOf (inferInstance : (pCore q Q).Normal) TopQ)
  let eNTop : N ⧸ UN ≃* TopQ ⧸ (pCore q Q).subgroupOf TopQ :=
    QuotientGroup.equivQuotientSubgroupOfOfEq (G := Q)
      (A' := U) (A := N) (B' := pCore q Q) (B := TopQ)
      hU_eq_core (by simpa [N, TopQ] using hNtop)
  have hcomp_top : HasNormalPComplement q (TopQ ⧸ (pCore q Q).subgroupOf TopQ) :=
    hasNormalPComplement_of_equiv (G := N ⧸ UN) (p := q) eNTop hcomp_N
  let qCore : Q →* Q ⧸ pCore q Q := QuotientGroup.mk' (pCore q Q)
  have htop_map : TopQ.map qCore = ⊤ := by
    simpa [TopQ, qCore] using
      (Subgroup.map_top_of_surjective qCore (QuotientGroup.mk'_surjective (pCore q Q)))
  let eRange : TopQ ⧸ (pCore q Q).subgroupOf TopQ ≃* TopQ.map qCore :=
    quotientSubgroupRangeEquiv TopQ (pCore q Q)
  let eQ : TopQ ⧸ (pCore q Q).subgroupOf TopQ ≃* Q ⧸ pCore q Q :=
    eRange.trans ((MulEquiv.subgroupCongr htop_map).trans Subgroup.topEquiv)
  exact hasNormalPComplement_of_equiv
    (G := TopQ ⧸ (pCore q Q).subgroupOf TopQ) (p := q) eQ hcomp_top

/-- The strict containment `U < S`, rewritten through `U = O_q(Q)`, says that
`q` still divides the quotient by `O_q(Q)`. -/
private theorem hkt_iv62_f_pCore_quotient_card_dvd
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    {U : Subgroup Q} (hUS : U < (S : Subgroup Q))
    (hNtop : Subgroup.normalizer (U : Set Q) = ⊤)
    (hU_eq_core : U = pCore q Q) :
    q ∣ Nat.card (Q ⧸ pCore q Q) := by
  classical
  let N : Subgroup Q := Subgroup.normalizer (U : Set Q)
  let UN : Subgroup N := U.subgroupOf N
  let : UN.Normal := by
    simpa [UN, N] using hkt_subgroupOf_normalizer_normal U
  have hq_dvd_N : q ∣ Nat.card (N ⧸ UN) := by
    simpa [N, UN] using
      hkt_dvd_card_normalizer_quotient_of_lt_sylow (Q := Q) (q := q) (S := S) hUS
  let TopQ : Subgroup Q := ⊤
  let : ((pCore q Q).subgroupOf TopQ).Normal := by
    simpa [TopQ] using
      (Subgroup.Normal.subgroupOf (inferInstance : (pCore q Q).Normal) TopQ)
  let eNTop : N ⧸ UN ≃* TopQ ⧸ (pCore q Q).subgroupOf TopQ :=
    QuotientGroup.equivQuotientSubgroupOfOfEq (G := Q)
      (A' := U) (A := N) (B' := pCore q Q) (B := TopQ)
      hU_eq_core (by simpa [N, TopQ] using hNtop)
  let qCore : Q →* Q ⧸ pCore q Q := QuotientGroup.mk' (pCore q Q)
  have htop_map : TopQ.map qCore = ⊤ := by
    simpa [TopQ, qCore] using
      (Subgroup.map_top_of_surjective qCore (QuotientGroup.mk'_surjective (pCore q Q)))
  let eRange : TopQ ⧸ (pCore q Q).subgroupOf TopQ ≃* TopQ.map qCore :=
    quotientSubgroupRangeEquiv TopQ (pCore q Q)
  let eQ : TopQ ⧸ (pCore q Q).subgroupOf TopQ ≃* Q ⧸ pCore q Q :=
    eRange.trans ((MulEquiv.subgroupCongr htop_map).trans Subgroup.topEquiv)
  have hcard_eq : Nat.card (N ⧸ UN) = Nat.card (Q ⧸ pCore q Q) := by
    exact Nat.card_congr (eNTop.trans eQ).toEquiv
  simpa [hcard_eq] using hq_dvd_N

/-- The canonical quotient by `O_q(Q)` has trivial `q`-core. -/
private theorem hkt_iv62_f_pCore_quotient_pCore_eq_bot
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime] :
    pCore q (Q ⧸ pCore q Q) = ⊥ := by
  let π : Q →* Q ⧸ pCore q Q := QuotientGroup.mk' (pCore q Q)
  have hmap :
      (pCore q Q).map π = pCore q (Q ⧸ pCore q Q) := by
    exact pCore_map_mk'_eq_of_normal_isPGroup (G := Q) (p := q) (pCore q Q)
      (pCore_isPGroup (G := Q) (p := q))
  calc
    pCore q (Q ⧸ pCore q Q) = (pCore q Q).map π := hmap.symm
    _ = ⊥ := by
      change (pCore q Q).map (QuotientGroup.mk' (pCore q Q)) = ⊥
      exact QuotientGroup.map_mk'_self (N := pCore q Q)

/-- Sentence 1 of Huppert IV.6.2(f): every proper subgroup containing the fixed
Sylow `q`-subgroup is `q`-nilpotent.  The source proof says that the IV.6.2
hypotheses plainly hold inside such a subgroup, so the minimal-counterexample
recursion applies there. -/
private theorem hkt_iv62_f_proper_over_sylow_hasNormalPComplement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    (hproper_rec : ∀ (H : Subgroup Q) (T : Sylow q H), H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H → HasNormalPComplement q (Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H)) → HasNormalPComplement q (Subgroup.normalizer (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H)) → HasNormalPComplement q H)
    {H : Subgroup Q} (hS_le_H : (S : Subgroup Q) ≤ H) (hHtop : H < ⊤) :
    HasNormalPComplement q H := by
  classical
  let SH : Sylow q H := S.subtype hS_le_H
  have hSH_map_eq : (SH : Subgroup H).map H.subtype = (S : Subgroup Q) := by
    calc
      (SH : Subgroup H).map H.subtype = ((S : Subgroup Q).subgroupOf H).map H.subtype := by
        simp [SH]
      _ = (S : Subgroup Q) := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hS_le_H]
  have hH_ne_bot : H ≠ ⊥ := by
    intro hHbot
    have hSbot : (S : Subgroup Q) = ⊥ := le_bot_iff.mp (by simpa [hHbot] using hS_le_H)
    exact (Sylow.ne_bot_of_dvd_card (G := Q) (p := q) S hq_dvd) hSbot
  have hq_dvd_H : q ∣ Nat.card H := by
    have hq_dvd_S : q ∣ Nat.card (S : Subgroup Q) :=
      S.dvd_card_of_dvd_card hq_dvd
    exact hq_dvd_S.trans (Subgroup.card_dvd_of_le hS_le_H)
  have hcenter_le :
      centerIn (G := Q) (S : Subgroup Q) ≤
        (centerIn (G := H) (SH : Subgroup H)).map H.subtype := by
    intro z hz
    refine Subgroup.mem_map.mpr ?_
    have hzH : z ∈ H := hS_le_H hz.1
    refine ⟨⟨z, hzH⟩, ?_, rfl⟩
    constructor
    · change (⟨z, hzH⟩ : H) ∈ (SH : Subgroup H)
      have hzMap : z ∈ (SH : Subgroup H).map H.subtype := by
        rw [hSH_map_eq]
        exact hz.1
      rcases Subgroup.mem_map.mp hzMap with ⟨y, hy, hyz⟩
      have hy_eq : y = ⟨z, hzH⟩ := Subtype.ext hyz
      simpa [hy_eq] using hy
    · change (⟨z, hzH⟩ : H) ∈ Subgroup.centralizer ((SH : Subgroup H) : Set H)
      rw [Subgroup.mem_centralizer_iff]
      intro y hySH
      apply Subtype.ext
      have hyS : ((y : H) : Q) ∈ (S : Subgroup Q) := by
        have hyMap : ((y : H) : Q) ∈ (SH : Subgroup H).map H.subtype :=
          Subgroup.mem_map.mpr ⟨y, hySH, rfl⟩
        simpa [hSH_map_eq] using hyMap
      exact Subgroup.mem_centralizer_iff.mp hz.2 ((y : H) : Q) hyS
  have hcenter_local :
      HasNormalPComplement q
        (Subgroup.centralizer (centerIn (G := H) (SH : Subgroup H) : Set H)) :=
    hkt_hasNormalPComplement_centralizer_subgroupOf_of_ambient_le
      (G := Q) (p := q) (N := H)
      (K := centerIn (G := H) (SH : Subgroup H))
      (T := centerIn (G := Q) (S : Subgroup Q)) hcenter_le hcentralizer_dvd
  have hJrank_local :
      HasNormalPComplement q
        (Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := H) (SH : Subgroup H) : Set H)) := by
    let JH : Subgroup H :=
      huppertRankThompsonSubgroup (G := H) (SH : Subgroup H)
    let JS : Subgroup SH :=
      huppertRankThompsonSubgroup (G := SH) (⊤ : Subgroup SH)
    let f : SH →* S :=
      (H.subtype.comp (SH : Subgroup H).subtype).codRestrict (S : Subgroup Q) (by
        intro x
        have hx : ((x : SH) : H) ∈ (SH : Subgroup H) := x.property
        have hxmap : (((x : SH) : H) : Q) ∈
            (SH : Subgroup H).map H.subtype :=
          Subgroup.mem_map.mpr ⟨(x : SH), hx, rfl⟩
        simpa [hSH_map_eq] using hxmap)
    have hf_inj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : S => (z : Q)) hxy
    have hf_surj : Function.Surjective f := by
      intro x
      have hxmap : (x : Q) ∈ (SH : Subgroup H).map H.subtype := by
        simp [hSH_map_eq, x.property]
      rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      apply Subtype.ext
      exact hyx
    let e : SH ≃* S := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
    have he_comp :
        (S : Subgroup Q).subtype.comp e.toMonoidHom =
          H.subtype.comp (SH : Subgroup H).subtype := by
      ext x
      rfl
    have hJ_map_eq : JH.map H.subtype =
        huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) := by
      calc
        JH.map H.subtype =
            JS.map (H.subtype.comp (SH : Subgroup H).subtype) := by
              rw [← Subgroup.map_map]
              simpa [JH, JS] using congrArg (fun K : Subgroup H => K.map H.subtype)
                (hkt_huppertRankThompsonSubgroup_top_map_subtype
                  (G := H) (SH : Subgroup H)).symm
        _ = JS.map ((S : Subgroup Q).subtype.comp e.toMonoidHom) := by
              exact congrArg (fun g => JS.map g) he_comp.symm
        _ = (JS.map e.toMonoidHom).map (S : Subgroup Q).subtype := by
              rw [Subgroup.map_map]
        _ = (huppertRankThompsonSubgroup (G := S) (⊤ : Subgroup S)).map
              (S : Subgroup Q).subtype := by
              rw [hkt_huppertRankThompsonSubgroup_top_map_mulEquiv]
        _ = huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) :=
              hkt_huppertRankThompsonSubgroup_top_map_subtype (G := Q) (S : Subgroup Q)
    have hJ_ambient : HasNormalPComplement q
        (Subgroup.normalizer ((JH.map H.subtype : Subgroup Q) : Set Q)) := by
      rw [hJ_map_eq]
      exact hnormalizer_rank_dvd
    exact hkt_hasNormalPComplement_normalizer_subgroupOf_of_ambient_image
      (G := Q) (p := q) (N := H) (K := JH) hJ_ambient
  exact hproper_rec H SH hH_ne_bot hHtop.ne hq_dvd_H hcenter_local hJrank_local
/-- Multiplicative commutativity transfers across a multiplicative equivalence. -/
private theorem hkt_isMulCommutative_of_mulEquiv
    {G G' : Type u} [Group G] [Group G'] (e : G ≃* G')
    [IsMulCommutative G] :
    IsMulCommutative G' := by
  refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
  obtain ⟨x0, rfl⟩ := e.surjective x
  obtain ⟨y0, rfl⟩ := e.surjective y
  simpa using congrArg e ((inferInstance : IsMulCommutative G).is_comm.comm x0 y0)

/-- Elementary abelian structure transfers across a multiplicative equivalence. -/
private theorem hkt_isElementaryAbelian_of_mulEquiv
    {G G' : Type u} [Group G] [Group G'] {r : ℕ}
    (e : G ≃* G') [IsElementaryAbelian r G] :
    IsElementaryAbelian r G' := by
  refine
    { toIsMulCommutative := hkt_isMulCommutative_of_mulEquiv e
      exponent_dvd_p := ?_ }
  simpa [Monoid.exponent_eq_of_mulEquiv e] using
    (IsElementaryAbelian.exponent_dvd_p r G)


/-- A finite nontrivial characteristically simple `r`-group is elementary abelian. -/
private theorem hkt_characteristicallySimple_isElementaryAbelian_of_isPGroup
    {G : Type u} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    (hG_ne_bot : (⊤ : Subgroup G) ≠ ⊥)
    (hchar_simple : ∀ N : Subgroup G, N.Characteristic → N = ⊥ ∨ N = ⊤)
    (hGp : IsPGroup r G) :
    IsElementaryAbelian r G := by
  classical
  let : Fact (IsPGroup r G) := ⟨hGp⟩
  let Φ : Subgroup G := frattini G
  have hΦ_char : Φ.Characteristic := by
    simpa [Φ] using (frattini_characteristic (G := G))
  rcases hchar_simple Φ hΦ_char with hΦ_bot | hΦ_top
  · exact (frattini_eq_bot_iff_isElementaryAbelian (R := G) (p := r)).1
      (by simpa [Φ] using hΦ_bot)
  · exfalso
    have hbot_top : (⊥ : Subgroup G) = ⊤ := by
      exact frattini_nongenerating (G := G) (K := ⊥) (by simp [Φ, hΦ_top])
    exact hG_ne_bot hbot_top.symm

/-- Solvability transports across a multiplicative equivalence. -/
private theorem hkt_isSolvable_of_mulEquiv
    {G H : Type u} [Group G] [Group H] (e : G ≃* H) [Group.IsSolvable G] :
    Group.IsSolvable H := by
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
/-- Coprime-action endpoint used in the Frattini paragraph: if a `q`-subgroup
and an `r`-element (`r ≠ q`) generate a subgroup with a normal `q`-complement,
then the `r`-element centralizes the `q`-subgroup. -/
private theorem hkt_generated_coprime_action_trivial_from_complement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (hcompH : HasNormalPComplement q (↥(((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q))))) :
    ∀ a : Q, a ∈ A → a * x = x * a := by
  classical
  let H : Subgroup Q := (A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)
  have hA_le_generated : A ≤ H := le_sup_left
  have hx_mem_generated : x ∈ H := by
    exact (le_sup_right : (Subgroup.zpowers x : Subgroup Q) ≤ H)
      (Subgroup.mem_zpowers x)
  rcases hcompH with ⟨K, hKnormal, hKcop, hquotp⟩
  let : K.Normal := hKnormal
  let AH : Subgroup H := A.subgroupOf H
  have hH_le_normalizer : H ≤ Subgroup.normalizer (A : Set Q) := by
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 x_norm)
  have hAHnormal : AH.Normal := by
    simpa [AH, H] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := A) (K := H) hA_le_generated).2 hH_le_normalizer
  have hAHp : IsPGroup q AH := by
    simpa [AH, H] using
      A_p.of_equiv
        ((Subgroup.subgroupOfEquivOfLe (H := A) (K := H) hA_le_generated).symm)
  let xH : H := ⟨x, hx_mem_generated⟩
  have hxH_r : IsPElement (p := r) xH := by
    rcases x_p with ⟨n, hn⟩
    exact ⟨n, by simpa [xH, Subgroup.orderOf_coe] using hn⟩
  have hxH_mem_K : xH ∈ K := by
    rcases hxH_r with ⟨n, hn⟩
    rcases (IsPGroup.iff_orderOf (p := q) (G := H ⧸ K)).1 hquotp
        (QuotientGroup.mk' K xH) with ⟨m, hm⟩
    have hbar_dvd_x : orderOf (QuotientGroup.mk' K xH) ∣ orderOf xH :=
      orderOf_map_dvd (QuotientGroup.mk' K) xH
    have hbar_dvd_r : orderOf (QuotientGroup.mk' K xH) ∣ r ^ n := by
      simpa [hn] using hbar_dvd_x
    have hbar_dvd_q : orderOf (QuotientGroup.mk' K xH) ∣ q ^ m := by
      rw [hm]
    have hcop_qr : Nat.Coprime (q ^ m) (r ^ n) := by
      exact (((Nat.coprime_primes (Fact.out : q.Prime) hr).2
        (fun hqr => hr_ne_q hqr.symm)).pow_right n).pow_left m
    have hbar_order_one : orderOf (QuotientGroup.mk' K xH) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop_qr hbar_dvd_q hbar_dvd_r
    exact (QuotientGroup.eq_one_iff (N := K) (x := xH)).1
      (orderOf_eq_one_iff.mp hbar_order_one)
  have hinf_bot : AH ⊓ K = ⊥ := by
    rcases hAHp.exists_card_eq with ⟨n, hn⟩
    have hcop : Nat.Coprime (Nat.card AH) (Nat.card K) := by
      rw [hn]
      exact hKcop.pow_left n
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hcomm_bot : ⁅AH, K⁆ = ⊥ := by
    have hleft : ⁅AH, K⁆ ≤ AH := by
      let : AH.Normal := hAHnormal
      exact Subgroup.commutator_le_left (H₁ := AH) (H₂ := K)
    have hright : ⁅AH, K⁆ ≤ K :=
      Subgroup.commutator_le_right (H₁ := AH) (H₂ := K)
    apply eq_bot_iff.mpr
    intro y hy
    have hyinf : y ∈ AH ⊓ K := ⟨hleft hy, hright hy⟩
    simpa [hinf_bot] using hyinf
  have hK_le_centAH : K ≤ Subgroup.centralizer (AH : Set H) := by
    have hcomm_K_AH : ⁅K, AH⁆ = ⊥ := by
      simpa [Subgroup.commutator_comm] using hcomm_bot
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K) (H₂ := AH)).1
      hcomm_K_AH
  intro a ha
  let aH : H := ⟨a, hA_le_generated ha⟩
  have haH : aH ∈ AH := by
    simpa [AH, aH, H, Subgroup.mem_subgroupOf] using ha
  have hcommH : aH * xH = xH * aH :=
    (Subgroup.mem_centralizer_iff.mp (hK_le_centAH hxH_mem_K)) aH haH
  exact congrArg Subtype.val hcommH

/-- If `G = N N_G(T)`, then the image of `T` in `G ⧸ N` is normal. -/
private theorem hkt_map_quotient_normal_of_sup_normalizer_eq_top
    {G : Type u} [Group G] {N T : Subgroup G} [N.Normal]
    (h : N ⊔ Subgroup.normalizer (T : Set G) = ⊤) :
    (T.map (QuotientGroup.mk' N)).Normal := by
  classical
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let M : Subgroup G := Subgroup.normalizer (T : Set G)
  have hMmap_le_normalizer : M.map π ≤ Subgroup.normalizer (T.map π : Set (G ⧸ N)) := by
    simpa [M, π] using (Subgroup.le_normalizer_map (H := T) (f := π))
  have hLmap_top : (N ⊔ M).map π = (⊤ : Subgroup (G ⧸ N)) := by
    calc
      (N ⊔ M).map π = (⊤ : Subgroup G).map π := by
        rw [show N ⊔ M = (⊤ : Subgroup G) by simpa [M] using h]
      _ = ⊤ := Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N)
  have hNmap_bot : N.map π = (⊥ : Subgroup (G ⧸ N)) := by
    exact (Subgroup.map_eq_bot_iff (H := N) (f := π)).2 (by
      intro x hx
      simpa [π, QuotientGroup.ker_mk'] using hx)
  have hMmap_top : M.map π = (⊤ : Subgroup (G ⧸ N)) := by
    have hsup_top : N.map π ⊔ M.map π = (⊤ : Subgroup (G ⧸ N)) := by
      simpa [Subgroup.map_sup] using hLmap_top
    simpa [hNmap_bot] using hsup_top
  have htop_le_normalizer : (⊤ : Subgroup (G ⧸ N)) ≤
      Subgroup.normalizer (T.map π : Set (G ⧸ N)) := by
    simpa [hMmap_top] using hMmap_le_normalizer
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop_le_normalizer)

/-- A subgroup contained in a complement to `N` maps injectively to `G ⧸ N`, hence keeps its order. -/
private theorem hkt_natCard_map_quotient_eq_of_image_complement
    {G : Type u} [Group G] [Finite G] {N K : Subgroup G} [N.Normal]
    {R : Subgroup K} (hcomp : (N.subgroupOf K).IsComplement' R)
    (P : Subgroup R) :
    Nat.card ((P.map (K.subtype.comp R.subtype)).map (QuotientGroup.mk' N)) =
      Nat.card (P.map (K.subtype.comp R.subtype)) := by
  classical
  let ιR : R →* G := K.subtype.comp R.subtype
  let Pamb : Subgroup G := P.map ιR
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have hNsub_Pamb_bot : N.subgroupOf Pamb = (⊥ : Subgroup Pamb) := by
    apply le_antisymm ?_ bot_le
    intro x hx
    have hxN : (x : G) ∈ N :=
      Subgroup.mem_subgroupOf.mp hx
    rcases Subgroup.mem_map.mp x.property with ⟨y, hyP, hyx⟩
    have hyNK : ((y : R) : K) ∈ N.subgroupOf K := by
      change (((y : R) : K) : G) ∈ N
      have hyx' : (((y : R) : K) : G) = (x : G) := by
        simpa [ιR] using hyx
      rw [hyx']
      exact hxN
    have hyR : ((y : R) : K) ∈ R := (y : R).property
    have hyK_one : ((y : R) : K) = 1 :=
      Subgroup.disjoint_def.mp hcomp.disjoint hyNK hyR
    have hy_amb_one : ιR y = (1 : G) := by
      simpa [ιR] using congrArg Subtype.val hyK_one
    have hx_val_one : (x : G) = 1 := by
      rw [← hyx]
      exact hy_amb_one
    have hx_one : x = 1 := Subtype.ext hx_val_one
    simpa using hx_one
  have hcard_quot : Nat.card (Pamb ⧸ N.subgroupOf Pamb) = Nat.card Pamb := by
    let e : Pamb ⧸ N.subgroupOf Pamb ≃* Pamb :=
      (QuotientGroup.quotientMulEquivOfEq hNsub_Pamb_bot).trans
        (QuotientGroup.quotientBot (G := Pamb))
    exact Nat.card_congr e.toEquiv
  calc
    Nat.card (Pamb.map π) = Nat.card (Pamb ⧸ N.subgroupOf Pamb) := by
      simpa [π] using (natCard_map_mk'_eq Pamb N)
    _ = Nat.card Pamb := hcard_quot
/-- A Sylow subgroup of a complement remains Sylow in the ambient product when
    the other complement factor is a `q`-group and the primes are distinct. -/
private theorem hkt_sylow_map_subtype_of_complement_coprime
    {K : Type u} [Group K] [Finite K]
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime]
    {H R : Subgroup K} (hcomp : H.IsComplement' R)
    (hHp : IsPGroup q H) (hr_ne_q : r ≠ q)
    (Pr : Sylow r R) :
    ∃ Pk : Sylow r K, (Pk : Subgroup K) = (Pr : Subgroup R).map R.subtype := by
  classical
  let Pmap : Subgroup K := (Pr : Subgroup R).map R.subtype
  have hPmap_p : IsPGroup r Pmap := by
    simpa [Pmap] using Pr.isPGroup'.map R.subtype
  have hcard_Pmap : Nat.card Pmap = Nat.card (Pr : Subgroup R) := by
    simpa [Pmap] using
      (Subgroup.card_map_of_injective (K := (Pr : Subgroup R))
        (f := R.subtype) R.subtype_injective)
  have hindex_Pmap : Pmap.index = Nat.card H * (Pr : Subgroup R).index := by
    have hmuleq :
        Pmap.index * Nat.card (Pr : Subgroup R) =
          (Nat.card H * (Pr : Subgroup R).index) * Nat.card (Pr : Subgroup R) := by
      calc
        Pmap.index * Nat.card (Pr : Subgroup R)
            = Pmap.index * Nat.card Pmap := by rw [hcard_Pmap]
        _ = Nat.card K := Subgroup.index_mul_card (H := Pmap)
        _ = Nat.card H * Nat.card R := hcomp.card_mul_card.symm
        _ = Nat.card H * ((Pr : Subgroup R).index * Nat.card (Pr : Subgroup R)) := by
          rw [Subgroup.index_mul_card (H := (Pr : Subgroup R))]
        _ = (Nat.card H * (Pr : Subgroup R).index) * Nat.card (Pr : Subgroup R) := by
          rw [Nat.mul_assoc]
    exact Nat.mul_right_cancel (Nat.card_pos : 0 < Nat.card (Pr : Subgroup R)) hmuleq
  have hcop_r_H : Nat.Coprime r (Nat.card H) := by
    rcases hHp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact ((Nat.coprime_primes (Fact.out : Nat.Prime r) (Fact.out : Nat.Prime q)).2
      hr_ne_q).pow_right n
  have hnot_dvd_index : ¬ r ∣ Pmap.index := by
    intro hdiv
    rw [hindex_Pmap] at hdiv
    exact (Fact.out : Nat.Prime r).not_dvd_mul
      ((Fact.out : Nat.Prime r).coprime_iff_not_dvd.mp hcop_r_H)
      Pr.not_dvd_index hdiv
  exact ⟨hPmap_p.toSylow hnot_dvd_index, rfl⟩

/-- A complement that centralizes the normal factor is itself normal. -/
private theorem hkt_normal_of_complement_centralizes
    {K : Type u} [Group K]
    {H R : Subgroup K} [H.Normal]
    (hcomp : H.IsComplement' R)
    (hcent : R ≤ Subgroup.centralizer (H : Set K)) :
    R.Normal := by
  classical
  have hH_le_normR : H ≤ Subgroup.normalizer (R : Set K) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      have hr_cent : r ∈ Subgroup.centralizer (H : Set K) := hcent hr
      have hcomm : h * r = r * h :=
        (Subgroup.mem_centralizer_iff.mp hr_cent) h hh
      have hconj : h * r * h⁻¹ = r := by
        calc
          h * r * h⁻¹ = (r * h) * h⁻¹ := by rw [hcomm]
          _ = r := by simp [mul_assoc]
      simpa [hconj] using hr
    · intro hconj_mem
      let s : K := h * r * h⁻¹
      have hs_cent : s ∈ Subgroup.centralizer (H : Set K) := hcent hconj_mem
      have hs_comm_h : h * s = s * h :=
        (Subgroup.mem_centralizer_iff.mp hs_cent) h hh
      have hback : h⁻¹ * s * h = s := by
        calc
          h⁻¹ * s * h = h⁻¹ * (s * h) := by rw [mul_assoc]
          _ = h⁻¹ * (h * s) := by rw [← hs_comm_h]
          _ = s := by simp
      have hr_eq : r = s := by
        calc
          r = h⁻¹ * (h * r * h⁻¹) * h := by simp [mul_assoc]
          _ = h⁻¹ * s * h := by rfl
          _ = s := hback
      rw [hr_eq]
      exact hconj_mem
  have htop_le_norm : (⊤ : Subgroup K) ≤ Subgroup.normalizer (R : Set K) := by
    rw [← hcomp.sup_eq_top]
    exact sup_le hH_le_normR Subgroup.le_normalizer
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop_le_norm)

/-- A normal `q'` complement gives a normal `q`-complement. -/
private theorem hkt_hasNormalPComplement_of_normal_complement
    {K : Type u} [Group K] [Finite K]
    {q : ℕ} [Fact q.Prime]
    {H R : Subgroup K} [R.Normal]
    (hcomp : H.IsComplement' R)
    (hRcop : Nat.Coprime q (Nat.card R))
    (hHp : IsPGroup q H) :
    HasNormalPComplement q K := by
  classical
  refine ⟨R, inferInstance, hRcop, ?_⟩
  exact hHp.of_equiv hcomp.QuotientMulEquiv.symm
/-- If all proper overgroups of a fixed Sylow `q`-subgroup have a normal
`q`-complement, then the same holds for any proper subgroup whose index is not
divisible by `q`, after conjugating a Sylow subgroup into the fixed one. -/
private theorem hkt_hasNormalPComplement_of_proper_index_not_dvd
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hproper_over_sylow :
      ∀ H : Subgroup Q, (S : Subgroup Q) ≤ H → H < ⊤ → HasNormalPComplement q H)
    {L : Subgroup Q} (hLproper : L < ⊤) (hLindex : ¬ q ∣ L.index) :
    HasNormalPComplement q L := by
  classical
  let T : Sylow q L := default
  let TQsub : Subgroup Q := (T : Subgroup L).map L.subtype
  have hTQp : IsPGroup q TQsub := by
    simpa [TQsub] using
      IsPGroup.map (p := q) (H := (T : Subgroup L)) T.isPGroup' L.subtype
  have hTQ_not_index : ¬ q ∣ TQsub.index := by
    intro hidx
    have hidx_eq : TQsub.index = (T : Subgroup L).index * L.index := by
      simpa [TQsub] using Subgroup.index_map_subtype (H := L) (T : Subgroup L)
    have hprod : q ∣ (T : Subgroup L).index * L.index := by
      simpa [hidx_eq] using hidx
    exact (Fact.out : Nat.Prime q).not_dvd_mul T.not_dvd_index hLindex hprod
  let TQ : Sylow q Q := hTQp.toSylow hTQ_not_index
  have hTQ_coe : (TQ : Subgroup Q) = TQsub := by
    exact IsPGroup.toSylow_coe hTQp hTQ_not_index
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q TQ S
  let Lg : Subgroup Q := L.conjBy g
  have hconjT_eq_S :
      (MulAut.conj g • (TQ : Subgroup Q) : Subgroup Q) = (S : Subgroup Q) := by
    calc
      (MulAut.conj g • (TQ : Subgroup Q) : Subgroup Q) =
          ((g • TQ : Sylow q Q) : Subgroup Q) := by
            rw [← Sylow.coe_subgroup_smul]
      _ = (S : Subgroup Q) := by simp [hg]
  have hTQsub_le_L : TQsub ≤ L := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hS_le_Lg : (S : Subgroup Q) ≤ Lg := by
    calc
      (S : Subgroup Q) = MulAut.conj g • (TQ : Subgroup Q) := hconjT_eq_S.symm
      _ = MulAut.conj g • TQsub := by rw [hTQ_coe]
      _ = TQsub.map (MulAut.conj g).toMonoidHom := rfl
      _ ≤ L.map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hTQsub_le_L
      _ = L.conjBy g := rfl
      _ = Lg := rfl
  have hLgproper : Lg < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    have hLtop : L = ⊤ := by
      calc
        L = (L.conjBy g).conjBy g⁻¹ := (Subgroup.conjBy_inv L g).symm
        _ = ⊤ := by
          rw [show L.conjBy g = ⊤ by simpa [Lg] using htop]
          simp [Subgroup.conjBy]
    exact (ne_of_lt hLproper) hLtop
  have hcompLg : HasNormalPComplement q Lg := hproper_over_sylow Lg hS_le_Lg hLgproper
  let e : L ≃* Lg := (MulAut.conj g).subgroupMap L
  exact hasNormalPComplement_of_equiv (G := Lg) (G' := L) (p := q) e.symm hcompLg

/-- A normal subgroup of order prime to `q` with `q`-group quotient is a Hall
subgroup for the set of primes different from `q`. -/
private theorem hkt_isHallSubgroup_non_q_of_coprime_quotient_pgroup
    {G : Type u} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {K : Subgroup G} [K.Normal]
    (hKcop : Nat.Coprime q (Nat.card K))
    (hquot_q : IsPGroup q (G ⧸ K)) :
    IsHallSubgroup ({p : Nat.Primes | p.val ≠ q}) K := by
  classical
  refine isHallSubgroup_of (G := G) (π := ({p : Nat.Primes | p.val ≠ q})) (H := K) ?_ ?_
  · intro p hp_dvd hp_eq_q
    have hq_dvd : q ∣ Nat.card K := by
      simpa [hp_eq_q] using hp_dvd
    exact ((Fact.out : Nat.Prime q).coprime_iff_not_dvd.mp hKcop) hq_dvd
  · intro p hp_ne_q hp_dvd_index
    have hp_dvd_quot : p.val ∣ Nat.card (G ⧸ K) := by
      simpa [Subgroup.index_eq_card] using hp_dvd_index
    rcases hquot_q.exists_card_eq with ⟨n, hn⟩
    have hp_dvd_pow : p.val ∣ q ^ n := by
      simpa [hn] using hp_dvd_quot
    have hcop : Nat.Coprime p.val (q ^ n) := by
      exact ((Nat.coprime_primes p.property (Fact.out : Nat.Prime q)).2 hp_ne_q).pow_right n
    exact (p.property.coprime_iff_not_dvd.mp hcop) hp_dvd_pow
/-- If a normal Hall subgroup together with `U` generates the whole group, then
no prime outside the Hall set divides the index of `U`. -/
private theorem hkt_prime_not_dvd_index_of_sup_hall
    {G : Type u} [Group G] [Finite G] {π : Set Nat.Primes}
    {K U : Subgroup G} [K.Normal] {p : Nat.Primes}
    (hKHall : IsHallSubgroup π K) (hpπ : p ∉ π)
    (hKU : K ⊔ U = ⊤) :
    ¬ p.val ∣ U.index := by
  intro hpU
  have hrel_eq :
      U.relIndex (U ⊔ K) = (U ⊓ K).relIndex K := by
    have hK_rel :
        K.relIndex (U ⊔ K) = (U ⊓ K).relIndex U := by
      calc
        K.relIndex (U ⊔ K) = K.relIndex U := by
          simp
        _ = (U ⊓ K).relIndex U := by
          symm
          simpa [inf_comm] using (Subgroup.inf_relIndex_left (H := U) (K := K))
    have hmul :
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
          (U ⊓ K).relIndex K * (U ⊓ K).relIndex U := by
      calc
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
            (U ⊓ K).relIndex (U ⊔ K) := by
          exact
            Subgroup.relIndex_mul_relIndex (H := U ⊓ K) (K := U) (L := U ⊔ K)
              inf_le_left le_sup_left
        _ = (U ⊓ K).relIndex K * K.relIndex (U ⊔ K) := by
          symm
          exact
            Subgroup.relIndex_mul_relIndex (H := U ⊓ K) (K := K) (L := U ⊔ K)
              inf_le_right le_sup_right
        _ = (U ⊓ K).relIndex K * (U ⊓ K).relIndex U := by
          rw [hK_rel]
    have hrel_pos : 0 < (U ⊓ K).relIndex U := by
      have hrel_ne_zero : (U ⊓ K).relIndex U ≠ 0 := by
        dsimp [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite (H := (U ⊓ K).subgroupOf U)
      exact Nat.pos_of_ne_zero hrel_ne_zero
    have hmul' :
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
          (U ⊓ K).relIndex U * (U ⊓ K).relIndex K := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    exact Nat.eq_of_mul_eq_mul_left hrel_pos hmul'
  have hidx_eq : U.relIndex (U ⊔ K) = U.index := by
    rw [show U ⊔ K = ⊤ by simpa [sup_comm] using hKU]
    exact Subgroup.relIndex_top_right (H := U)
  have hrel_dvd_cardK : U.relIndex (U ⊔ K) ∣ Nat.card K := by
    rw [hrel_eq]
    exact Subgroup.relIndex_dvd_card (H := U ⊓ K) (K := K)
  have hidx_dvd_cardK : U.index ∣ Nat.card K := by
    simpa [hidx_eq] using hrel_dvd_cardK
  exact hpπ (hKHall.p_in_pi_of_p_dvd_card p (hpU.trans hidx_dvd_cardK))
/-- In a characteristically simple finite group, the subgroup generated by all
`r`-elements is the whole group as soon as `r` divides the group order. -/
private theorem hkt_pElementsSubgroup_top_of_characteristically_simple
    {G : Type u} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    (hchar_simple : ∀ N : Subgroup G, N.Characteristic → N = ⊥ ∨ N = ⊤)
    (hr_dvd : r ∣ Nat.card G) :
    pElementsSubgroup r G = ⊤ := by
  classical
  rcases hchar_simple (pElementsSubgroup r G)
      (pElementsSubgroup_characteristic r G) with hp_bot | hp_top
  · exfalso
    let Pr : Sylow r G := default
    have hPr_ne_bot : (Pr : Subgroup G) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card (G := G) (p := r) Pr hr_dvd
    apply hPr_ne_bot
    apply le_antisymm ?_ bot_le
    intro x hxPr
    have hx_r : IsPElement (p := r) x := by
      rcases (IsPGroup.iff_orderOf (p := r) (G := (Pr : Subgroup G))).1
          Pr.isPGroup' ⟨x, hxPr⟩ with ⟨n, hn⟩
      exact ⟨n, by simpa [Subgroup.orderOf_coe] using hn⟩
    have hx_elem : x ∈ pElementsSubgroup r G := by
      change x ∈ Subgroup.closure {x : G | IsPElement (p := r) x}
      exact Subgroup.subset_closure hx_r
    simpa [hp_bot] using hx_elem
  · exact hp_top
/-- If every element of `R` maps into the ambient centralizer of `H`, then `R`
centralizes the copy of `H` inside the overgroup `K0`. -/
private theorem hkt_le_centralizer_subgroupOf_of_top_le_comap_centralizer
    {Q : Type u} [Group Q] {H K0 : Subgroup Q}
    {R : Subgroup K0}
    (hcent : (⊤ : Subgroup R) ≤
      (Subgroup.centralizer (H : Set Q)).comap (K0.subtype.comp R.subtype)) :
    R ≤ Subgroup.centralizer (H.subgroupOf K0 : Set K0) := by
  classical
  let ιR : R →* Q := K0.subtype.comp R.subtype
  intro x hxR
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  let xR : R := ⟨x, hxR⟩
  have hxC : ιR xR ∈ Subgroup.centralizer (H : Set Q) := hcent (by simp)
  have haH : ((a : K0) : Q) ∈ H := by
    simpa [Subgroup.mem_subgroupOf] using ha
  have hcomm : ((a : K0) : Q) * ιR xR = ιR xR * ((a : K0) : Q) :=
    (Subgroup.mem_centralizer_iff.mp hxC) ((a : K0) : Q) haH
  apply Subtype.ext
  change ((a : K0) : Q) * ((x : K0) : Q) = ((x : K0) : Q) * ((a : K0) : Q)
  exact hcomm
/-- The right factor of a complement is trivial if it is contained in the left
factor. -/
private theorem hkt_right_complement_eq_bot_of_le_left
    {K : Type u} [Group K] {H R : Subgroup K}
    (hcomp : H.IsComplement' R) (hR_le_H : R ≤ H) :
    R = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hxR
  exact Subgroup.disjoint_def.mp hcomp.disjoint (hR_le_H hxR) hxR

private theorem hkt_right_complement_eq_bot_of_ambient_le_left
    {Q : Type u} [Group Q] {H K : Subgroup Q} {HK : Subgroup K}
    (hHK_eq : HK = H.subgroupOf K) {R : Subgroup K}
    (hcomp : HK.IsComplement' R) (hK_le_H : K ≤ H) :
    R = ⊥ := by
  subst HK
  refine hkt_right_complement_eq_bot_of_le_left hcomp ?_
  rw [(Subgroup.subgroupOf_eq_top (H := H) (K := K)).2 hK_le_H]
  exact le_top

private theorem hkt_false_of_centralizing_complement_part_d
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥)
    {H K : Subgroup Q} [K.Normal] (hH_eq_core : H = pCore q Q)
    {HK : Subgroup K} [HK.Normal] (hHK_eq : HK = H.subgroupOf K)
    {R : Subgroup K}
    (hcomp : HK.IsComplement' R)
    (hRcop : Nat.Coprime q (Nat.card R))
    (hHKp : IsPGroup q HK)
    (hcent : R ≤ Subgroup.centralizer (HK : Set K))
    (hR_ne_bot : R ≠ ⊥) :
    False := by
  have : R.Normal :=
    hkt_normal_of_complement_centralizes
      (K := K) (H := HK) (R := R) hcomp hcent
  have hcompK : HasNormalPComplement q K :=
    hkt_hasNormalPComplement_of_normal_complement
      (K := K) (H := HK) (R := R) hcomp hRcop hHKp
  have hK_le_core : K ≤ pCore q Q :=
    huppert_IV_6_2_d_normal_hasNormalPComplement_le_pCore_of_pPrimeCore_eq_bot
      (Q := Q) (q := q) hcore_bot K hcompK
  have hK_le_H : K ≤ H := by
    simpa [hH_eq_core] using hK_le_core
  exact hR_ne_bot
    (hkt_right_complement_eq_bot_of_ambient_le_left
      (H := H) (K := K) (HK := HK) (R := R) hHK_eq hcomp hK_le_H)

private theorem hkt_sylow_top_of_top_or_proper_false
    {Q R : Type u} [Group Q] [Group R] {r : ℕ} [Fact r.Prime]
    (Pr : Sylow r R) {L : Subgroup Q}
    (hPr_top_of_Ltop : L = ⊤ → (Pr : Subgroup R) = ⊤)
    (hFalse_of_Lproper : L < ⊤ → False) :
    (Pr : Subgroup R) = ⊤ := by
  by_cases hLtop : L = ⊤
  · exact hPr_top_of_Ltop hLtop
  · exact False.elim (hFalse_of_Lproper (lt_of_le_of_ne le_top hLtop))

private theorem hkt_isPGroup_of_sylow_top
    {R : Type u} [Group R] {r : ℕ} [Fact r.Prime]
    (Pr : Sylow r R) (hPr_top : (Pr : Subgroup R) = ⊤) :
    IsPGroup r R := by
  have htop_p : IsPGroup r (⊤ : Subgroup R) := hPr_top ▸ Pr.isPGroup'
  exact htop_p.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup R) ≃* R)
private theorem hkt_sylow_eq_top_of_H_sup_normalizer_image_top
    {Q : Type u} [Group Q] [Finite Q]
    {H K : Subgroup Q} [H.Normal]
    {Kbar : Subgroup (Q ⧸ H)} [Kbar.Normal]
    (hK_le_comap : K ≤ Kbar.comap (QuotientGroup.mk' H))
    (hKbar_minimal : IsMinimalNormal Kbar)
    {R : Subgroup K}
    (hcompR : (H.subgroupOf K).IsComplement' R)
    (hR_card_eq_Kbar : Nat.card R = Nat.card Kbar)
    {r : ℕ} [Fact r.Prime] (Pr : Sylow r R)
    (hr_dvd_R : r ∣ Nat.card R)
    {Pamb : Subgroup Q}
    (hPamb_def : Pamb = (Pr : Subgroup R).map (K.subtype.comp R.subtype))
    (hH_sup_norm_top : H ⊔ Subgroup.normalizer (Pamb : Set Q) = ⊤) :
    (Pr : Subgroup R) = ⊤ := by
  classical
  subst Pamb
  let ιR : R →* Q := K.subtype.comp R.subtype
  let Pamb : Subgroup Q := (Pr : Subgroup R).map ιR
  let π : Q →* Q ⧸ H := QuotientGroup.mk' H
  have hH_sup_norm_top' : H ⊔ Subgroup.normalizer (Pamb : Set Q) = ⊤ := by
    simpa [Pamb, ιR] using hH_sup_norm_top
  let Pbar : Subgroup (Q ⧸ H) := Pamb.map π
  have hPamb_le_K : Pamb ≤ K := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    change (((y : R) : K) : Q) ∈ K
    exact ((y : R) : K).property
  have hPbar_le_Kbar : Pbar ≤ Kbar := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact hK_le_comap (hPamb_le_K hy)
  have hPbar_ne_bot : Pbar ≠ ⊥ := by
    intro hPbar_bot
    have hPamb_le_H : Pamb ≤ H := by
      have hleker : Pamb ≤ π.ker :=
        (Subgroup.map_eq_bot_iff (H := Pamb) (f := π)).1 hPbar_bot
      intro x hx
      have hxker : x ∈ π.ker := hleker hx
      simpa [π, QuotientGroup.ker_mk'] using hxker
    have hPr_bot : (Pr : Subgroup R) = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro y hyPr
      have hyPamb : ιR y ∈ Pamb := by
        exact Subgroup.mem_map.mpr ⟨y, hyPr, rfl⟩
      have hyHK : ((y : R) : K) ∈ H.subgroupOf K := by
        change (((y : R) : K) : Q) ∈ H
        exact hPamb_le_H hyPamb
      have hyR : ((y : R) : K) ∈ R := (y : R).property
      have hyK_one : ((y : R) : K) = 1 :=
        Subgroup.disjoint_def.mp hcompR.disjoint hyHK hyR
      have hy_one : y = 1 := Subtype.ext hyK_one
      simpa using hy_one
    exact (Sylow.ne_bot_of_dvd_card (G := R) (p := r) Pr hr_dvd_R) hPr_bot
  have hPbar_normal : Pbar.Normal := by
    simpa [Pbar, Pamb, π] using
      (hkt_map_quotient_normal_of_sup_normalizer_eq_top
        (N := H) (T := Pamb) hH_sup_norm_top')
  have hPbar_eq_Kbar : Pbar = Kbar := by
    have : Pbar.Normal := hPbar_normal
    have : IsMinimalNormal Kbar := hKbar_minimal
    rcases IsMinimalNormal.minimal Pbar hPbar_le_Kbar with hbot | htop
    · exact False.elim (hPbar_ne_bot hbot)
    · exact htop
  have hcard_Pr_Pamb : Nat.card (Pr : Subgroup R) = Nat.card Pamb := by
    simpa [Pamb, ιR] using
      (Subgroup.card_map_of_injective (K := (Pr : Subgroup R))
        (f := ιR) (by
          intro x y hxy
          exact Subtype.ext (Subtype.ext hxy))).symm
  have hcard_Pbar_Pamb : Nat.card Pbar = Nat.card Pamb := by
    change Nat.card (((Pr : Subgroup R).map (K.subtype.comp R.subtype)).map
        (QuotientGroup.mk' H)) =
      Nat.card ((Pr : Subgroup R).map (K.subtype.comp R.subtype))
    exact hkt_natCard_map_quotient_eq_of_image_complement
      (N := H) (K := K) (R := R) hcompR (Pr : Subgroup R)
  have hcard_Pr_R : Nat.card (Pr : Subgroup R) = Nat.card R := by
    calc
      Nat.card (Pr : Subgroup R) = Nat.card Pamb := hcard_Pr_Pamb
      _ = Nat.card Pbar := hcard_Pbar_Pamb.symm
      _ = Nat.card Kbar := by rw [hPbar_eq_Kbar]
      _ = Nat.card R := hR_card_eq_Kbar.symm
  exact (Subgroup.card_eq_iff_eq_top (H := (Pr : Subgroup R))).1 hcard_Pr_R

/-- If `P` normalizes `N` and `N ∩ P = 1`, then the subgroup generated by
`N` and `P` has the expected product order. -/
private theorem hkt_sup_natCard_eq_mul_of_inf_eq_bot_of_le_normalizer
    {G : Type u} [Group G] {N P : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (N : Set G))
    (hinf : N ⊓ P = ⊥) :
    Nat.card (N ⊔ P : Subgroup G) = Nat.card N * Nat.card P := by
  classical
  let R : Subgroup G := P ⊔ N
  let Ns : Subgroup R := N.subgroupOf R
  let Ps : Subgroup R := P.subgroupOf R
  have : Ns.Normal := by
    simpa [R, Ns] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := P) (N := N) hPN)
  have hcomp : Ns.IsComplement' Ps := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxN hxP
      apply Subtype.ext
      have hxinf : ((x : R) : G) ∈ N ⊓ P := ⟨hxN, hxP⟩
      have hxbot : ((x : R) : G) ∈ (⊥ : Subgroup G) := by
        simpa [hinf] using hxinf
      simpa using hxbot
    · rw [Set.eq_univ_iff_forall]
      intro x
      have htop : Ns ⊔ Ps = ⊤ := by
        calc
          Ns ⊔ Ps = (N ⊔ P).subgroupOf R := by
            symm
            simpa [R, Ns, Ps] using
              (Subgroup.subgroupOf_sup (A := N) (A' := P) (B := R)
                le_sup_right le_sup_left)
          _ = ⊤ := by
            exact Subgroup.subgroupOf_eq_top.mpr (by simp [R, sup_comm])
      have hx_top : x ∈ Ns ⊔ Ps := by simp [htop]
      rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := Ns) (t := Ps)).1
          hx_top with
        ⟨n, hnN, p, hpP, hmul⟩
      exact ⟨n, hnN, p, hpP, hmul⟩
  have hmul := hcomp.card_mul_card
  have hNcard : Nat.card Ns = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := N) (K := R)
      le_sup_right).toEquiv
  have hPcard : Nat.card Ps = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := P) (K := R)
      le_sup_left).toEquiv
  have hR : Nat.card R = Nat.card N * Nat.card P := by
    simpa [R, Ns, Ps, hNcard, hPcard, mul_comm] using hmul.symm
  simpa [R, sup_comm] using hR

/-- In a product of a `p`-subgroup with a normal `p'`-subgroup, replacing the
normal factor by a proper normal subfactor gives a proper subgroup. -/
private theorem hkt_sup_lt_top_of_sup_eq_top_of_coprime_normal
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {S K M : Subgroup G} [K.Normal] [M.Normal]
    (hS_p : IsPGroup p S)
    (hK_coprime : Nat.Coprime p (Nat.card K))
    (hM_le_K : M ≤ K) (hM_ne_K : M ≠ K)
    (hS_sup_K : S ⊔ K = ⊤) :
    S ⊔ M < ⊤ := by
  classical
  refine lt_of_le_of_ne le_top ?_
  intro hSM_top
  have hM_coprime : Nat.Coprime p (Nat.card M) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hM_le_K) hK_coprime
  rcases hS_p.exists_card_eq with ⟨n, hS_card⟩
  have hK_inf_S : K ⊓ S = ⊥ := by
    have hcop : Nat.Coprime (Nat.card K) (Nat.card S) := by
      rw [hS_card]
      exact hK_coprime.symm.pow_right n
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hM_inf_S : M ⊓ S = ⊥ := by
    have hcop : Nat.Coprime (Nat.card M) (Nat.card S) := by
      rw [hS_card]
      exact hM_coprime.symm.pow_right n
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hS_le_norm_K : S ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_of_normal
  have hS_le_norm_M : S ≤ Subgroup.normalizer (M : Set G) :=
    Subgroup.le_normalizer_of_normal
  have hcard_KS : Nat.card (K ⊔ S : Subgroup G) = Nat.card K * Nat.card S :=
    hkt_sup_natCard_eq_mul_of_inf_eq_bot_of_le_normalizer
      (N := K) (P := S) hS_le_norm_K hK_inf_S
  have hcard_MS : Nat.card (M ⊔ S : Subgroup G) = Nat.card M * Nat.card S :=
    hkt_sup_natCard_eq_mul_of_inf_eq_bot_of_le_normalizer
      (N := M) (P := S) hS_le_norm_M hM_inf_S
  have htop_K : Nat.card (⊤ : Subgroup G) = Nat.card K * Nat.card S := by
    simpa [hS_sup_K, sup_comm] using hcard_KS
  have htop_M : Nat.card (⊤ : Subgroup G) = Nat.card M * Nat.card S := by
    simpa [hSM_top, sup_comm] using hcard_MS
  have hcard_MK : Nat.card M = Nat.card K := by
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (htop_M.symm.trans htop_K)
  have hM_eq_K : M = K :=
    Subgroup.eq_of_le_of_card_ge hM_le_K (by rw [hcard_MK])
  exact hM_ne_K hM_eq_K
/-- Huppert IV.6.2(f), in the solvability form needed by the later clauses.
The source paragraph proves a stronger elementary-abelian complement structure;
this core keeps only the final solvability consequence, while the remaining
source leaf below is stated in that structural form. -/
private theorem hkt_iv62_f_reduced_nonburnside_isSolvable_core
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (_hnot_Qp : ¬ IsPGroup q Q)
    (_hq2 : q ≠ 2) (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (_hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    (hproper_rec : ∀ (H : Subgroup Q) (T : Sylow q H), H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H → HasNormalPComplement q (Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H)) → HasNormalPComplement q (Subgroup.normalizer (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H)) → HasNormalPComplement q H)
    (hsmall_rec : ∀ {R : Type u} [Group R] [Finite R] (T : Sylow q R), Nat.card R < Nat.card Q → q ∣ Nat.card R → HasNormalPComplement q (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R)) → HasNormalPComplement q (Subgroup.normalizer (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R)) → HasNormalPComplement q R)
    {U : Subgroup Q}
    (hU_ne_bot : U ≠ ⊥) (_hU_p : IsPGroup q U)
    (_hU_no_complement : ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))))
    (hUmax :
      ∀ W : Subgroup Q,
        W ≠ ⊥ →
        IsPGroup q W →
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
          Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q * (Nat.card Q + 1) + Nat.card W ≤ Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q * (Nat.card Q + 1) + Nat.card U)
    (P : Sylow q (Subgroup.normalizer (U : Set Q)))
    (hUS : U < (S : Subgroup Q))
    (hUN_le_P :
      U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≤
        (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hcardUP :
      Nat.card U < Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hNtop : Subgroup.normalizer (U : Set Q) = ⊤)
    (hU_eq_core : U = pCore q Q) :
    ∃ Kbar : Subgroup (Q ⧸ pCore q Q), ∃ hKbar_normal : Kbar.Normal,
      @IsMinimalNormal (Q ⧸ pCore q Q) _ Kbar hKbar_normal ∧
        Kbar ≠ ⊥ ∧
          Kbar ≠ ⊤ ∧
            Nat.Coprime q (Nat.card Kbar) ∧
              IsPGroup q ((Q ⧸ pCore q Q) ⧸ Kbar) ∧
                q ∣ Nat.card (Q ⧸ pCore q Q) ∧
                  pCore q (Q ⧸ pCore q Q) = ⊥ ∧
                    Group.IsSolvable Q := by
  classical
  -- Sentence 1: if `S ≤ H < Q`, then the hypotheses hold in `H`; hence
  -- `H` is `q`-nilpotent by the minimal-counterexample recursion.
  have hproper_over_sylow :
      ∀ H : Subgroup Q, (S : Subgroup Q) ≤ H → H < ⊤ →
        HasNormalPComplement q H := by
    intro H hS_le_H hHtop
    exact hkt_iv62_f_proper_over_sylow_hasNormalPComplement
      (Q := Q) (q := q) S hq_dvd hcentralizer_dvd hnormalizer_rank_dvd hproper_rec
      hS_le_H hHtop
  -- Sentence 2: by (b),(c), the quotient `Q/O_q(Q)` has a normal
  -- `q`-complement.
  have hquot_comp : HasNormalPComplement q (Q ⧸ pCore q Q) :=
    hkt_iv62_f_pCore_quotient_hasNormalPComplement
      (Q := Q) (q := q) S hsmall_rec hU_ne_bot _hU_p _hU_no_complement hUmax P hUS hUN_le_P hcardUP
      hNtop hU_eq_core
  -- The strict containment `U < S`, together with `U = O_q(Q)`, says the
  -- quotient still has `q` in its order; this is the entry point for the
  -- book's Zassenhaus/minimal-normal paragraph.
  have hquot_dvd : q ∣ Nat.card (Q ⧸ pCore q Q) :=
    hkt_iv62_f_pCore_quotient_card_dvd
      (Q := Q) (q := q) S hUS hNtop hU_eq_core
  rcases hquot_comp with ⟨Kbar, hKbar_normal, hKbar_coprime, hquot_q⟩
  let : Kbar.Normal := hKbar_normal
  have hquot_pcore_bot : pCore q (Q ⧸ pCore q Q) = ⊥ :=
    hkt_iv62_f_pCore_quotient_pCore_eq_bot (Q := Q) (q := q)
  have hKbar_ne_top : Kbar ≠ ⊤ := by
    intro hKbar_top
    have hcard_top : Nat.card Kbar = Nat.card (Q ⧸ pCore q Q) := by
      simp [hKbar_top]
    have hcop_quot : Nat.Coprime q (Nat.card (Q ⧸ pCore q Q)) := by
      simpa [hcard_top] using hKbar_coprime
    exact ((Fact.out : Nat.Prime q).coprime_iff_not_dvd.mp hcop_quot) hquot_dvd
  have hKbar_ne_bot : Kbar ≠ ⊥ := by
    intro hKbar_bot
    subst Kbar
    let Gbar : Type u := Q ⧸ pCore q Q
    let : Group Gbar := inferInstance
    let : Finite Gbar := inferInstance
    have hquot_p : IsPGroup q (Gbar ⧸ (⊥ : Subgroup Gbar)) := by
      simpa [Gbar] using hquot_q
    have hGbar_p : IsPGroup q Gbar :=
      hquot_p.of_equiv (QuotientGroup.quotientBot (G := Gbar))
    have hpcore_top : pCore q Gbar = ⊤ := by
      have htop_p : IsPGroup q (⊤ : Subgroup Gbar) :=
        hGbar_p.to_subgroup (⊤ : Subgroup Gbar)
      have htop_le : (⊤ : Subgroup Gbar) ≤ pCore q Gbar :=
        le_sSup ⟨(inferInstance : (⊤ : Subgroup Gbar).Normal), htop_p⟩
      exact top_le_iff.mp htop_le
    have hpcore_bot : pCore q Gbar = ⊥ := by
      simpa [Gbar] using hquot_pcore_bot
    have htop_bot : (⊤ : Subgroup Gbar) = ⊥ := by
      rw [← hpcore_top, hpcore_bot]
    have hsub : Subsingleton Gbar := by
      refine ⟨fun x y => ?_⟩
      have hx_bot : x ∈ (⊥ : Subgroup Gbar) := by
        simp [← htop_bot]
      have hy_bot : y ∈ (⊥ : Subgroup Gbar) := by
        simp [← htop_bot]
      rw [Subgroup.mem_bot] at hx_bot hy_bot
      simp [hx_bot, hy_bot]
    have : Subsingleton Gbar := hsub
    have hcard_one : Nat.card Gbar = 1 := by simp
    exact (Fact.out : Nat.Prime q).not_dvd_one (by simpa [Gbar, hcard_one] using hquot_dvd)
  have hquot_data :
      @IsMinimalNormal (Q ⧸ pCore q Q) _ Kbar hKbar_normal ∧
        Group.IsSolvable (Q ⧸ pCore q Q) := by
    -- Sentence 2 continued: write `K/O_q(Q)` for the normal `q`-complement
    -- of `Q/O_q(Q)`.  The quotient by this subgroup is a `q`-group, so the
    -- only remaining source work is the Zassenhaus/minimal-normal/Frattini
    -- paragraph proving that `K/O_q(Q)` itself is solvable.
    have hKbar_data :
        @IsMinimalNormal (Q ⧸ pCore q Q) _ Kbar hKbar_normal ∧ Group.IsSolvable Kbar := by
      -- Book paragraph:
      -- * let `H = O_q(Q)` and pull `Kbar` back to `K ≤ Q`;
      -- * by Schur-Zassenhaus, `H` has a complement `R` in `K`;
      -- * choose a minimal normal layer `HT/H` with `1 < T ≤ R`;
      -- * if `T < R`, then the corresponding proper subgroup containing
      --   the fixed Sylow subgroup is `q`-nilpotent by `hproper_over_sylow`, forcing
      --   `T ◁ Q` and contradicting clause (d);
      -- * hence `T = R`; the Frattini argument gives `H N_Q(R_q) = Q`, so
      --   the layer is elementary abelian.  Therefore `K/O_q(Q) ≃ R` is
      --   solvable.
      let H : Subgroup Q := pCore q Q
      have : H.Normal := by
        simpa [H] using (inferInstance : (pCore q Q).Normal)
      let π : Q →* Q ⧸ H := QuotientGroup.mk' H
      let K : Subgroup Q := Kbar.comap π
      have hH_le_K : H ≤ K := by
        intro x hx
        have hx1 : π x = 1 := (QuotientGroup.eq_one_iff (N := H) (x := x)).2 hx
        simp [K, π, hx1]
      let HK : Subgroup K := H.subgroupOf K
      have : HK.Normal := by
        simpa [HK, H, K] using
          (Subgroup.Normal.subgroupOf (inferInstance : (pCore q Q).Normal) K)
      have hHK_coprime_index : Nat.Coprime (Nat.card HK) HK.index := by
        -- `HK` is a `q`-group and `K/H ≃ Kbar` has order prime to `q`.
        -- This is the precise Schur-Zassenhaus coprimeness used in the book.
        have hHK_p : IsPGroup q HK := by
          have hH_p : IsPGroup q H := by
            simpa [H] using pCore_isPGroup (G := Q) (p := q)
          exact hH_p.of_equiv (Subgroup.subgroupOfEquivOfLe (H := H) (K := K) hH_le_K).symm
        rcases hHK_p.exists_card_eq with ⟨n, hnHK⟩
        have hindex_eq_card : HK.index = Nat.card Kbar := by
          have hcard_quot : Nat.card (K ⧸ HK) = Nat.card Kbar := by
            simpa [HK, H, K, π] using
              (card_quotient_subgroupOf_comap_eq
                (f := π) (hf := QuotientGroup.mk'_surjective H) (H := Kbar))
          simpa [Subgroup.index_eq_card] using hcard_quot
        rw [hnHK, hindex_eq_card]
        exact Nat.Coprime.pow_left n hKbar_coprime
      obtain ⟨R, hHK_R_compl⟩ :=
        Subgroup.exists_right_complement'_of_coprime (N := HK) hHK_coprime_index
      -- Since R complements H in K, it is isomorphic to K/H, hence to
      -- the normal complement `Kbar` in `Q/O_q(Q)`.
      let φ : K →* Kbar :=
        { toFun := fun k => ⟨π (k : Q), by
              change π (k : Q) ∈ Kbar
              exact k.property⟩
          map_one' := by
            apply Subtype.ext
            simp [π]
          map_mul' := by
            intro a b
            apply Subtype.ext
            simp [π] }
      have hφ_surj : Function.Surjective φ := by
        intro y
        rcases QuotientGroup.mk'_surjective H (y : Q ⧸ H) with ⟨x, hx⟩
        have hxK : x ∈ K := by
          change π x ∈ Kbar
          simp [π, hx, y.property]
        refine ⟨⟨x, hxK⟩, ?_⟩
        apply Subtype.ext
        simpa [φ, π] using hx
      have hφ_ker : φ.ker = HK := by
        ext x
        change φ x = 1 ↔ x ∈ HK
        constructor
        · intro hx
          have hxH : (x : Q) ∈ H := by
            have hxmk : π (x : Q) = 1 := by
              exact Subtype.ext_iff.mp hx
            exact (QuotientGroup.eq_one_iff (N := H) (x := (x : Q))).1 hxmk
          exact hxH
        · intro hx
          apply Subtype.ext
          have hxH : (x : Q) ∈ H := Subgroup.mem_subgroupOf.mp hx
          exact (QuotientGroup.eq_one_iff (N := H) (x := (x : Q))).2 hxH
      let eKbar : K ⧸ HK ≃* Kbar :=
        (QuotientGroup.quotientMulEquivOfEq hφ_ker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective φ hφ_surj)
      let eR : K ⧸ HK ≃* R := hHK_R_compl.symm.QuotientMulEquiv
      have hKbar_ne_top : Kbar ≠ ⊤ := by
        intro hKbar_top
        have hcard_top : Nat.card Kbar = Nat.card (Q ⧸ H) := by
          simp [hKbar_top, H]
        have hcop_quot : Nat.Coprime q (Nat.card (Q ⧸ H)) := by
          simpa [hcard_top] using hKbar_coprime
        exact ((Fact.out : Nat.Prime q).coprime_iff_not_dvd.mp hcop_quot)
          (by simpa [H] using hquot_dvd)
      have hKbar_ne_bot : Kbar ≠ ⊥ := by
        intro hKbar_bot
        subst Kbar
        let Gbar : Type u := Q ⧸ H
        let : Group Gbar := inferInstance
        let : Finite Gbar := inferInstance
        have hquot_p : IsPGroup q (Gbar ⧸ (⊥ : Subgroup Gbar)) := by
          simpa [Gbar, H] using hquot_q
        have hGbar_p : IsPGroup q Gbar :=
          hquot_p.of_equiv (QuotientGroup.quotientBot (G := Gbar))
        have hpcore_top : pCore q Gbar = ⊤ := by
          have htop_p : IsPGroup q (⊤ : Subgroup Gbar) :=
            hGbar_p.to_subgroup (⊤ : Subgroup Gbar)
          have htop_le : (⊤ : Subgroup Gbar) ≤ pCore q Gbar :=
            le_sSup ⟨(inferInstance : (⊤ : Subgroup Gbar).Normal), htop_p⟩
          exact top_le_iff.mp htop_le
        have hpcore_bot : pCore q Gbar = ⊥ := by
          simpa [Gbar, H] using hkt_iv62_f_pCore_quotient_pCore_eq_bot (Q := Q) (q := q)
        have htop_bot : (⊤ : Subgroup Gbar) = ⊥ := by
          rw [← hpcore_top, hpcore_bot]
        have hsub : Subsingleton Gbar := by
          refine ⟨fun x y => ?_⟩
          have hx_bot : x ∈ (⊥ : Subgroup Gbar) := by
            simp [← htop_bot]
          have hy_bot : y ∈ (⊥ : Subgroup Gbar) := by
            simp [← htop_bot]
          rw [Subgroup.mem_bot] at hx_bot hy_bot
          simp [hx_bot, hy_bot]
        have : Subsingleton Gbar := hsub
        have hcard_one : Nat.card Gbar = 1 := by simp
        exact (Fact.out : Nat.Prime q).not_dvd_one (by simpa [Gbar, H, hcard_one] using hquot_dvd)

      have hR_card_eq_Kbar : Nat.card R = Nat.card Kbar := by
        calc
          Nat.card R = Nat.card (K ⧸ HK) := Nat.card_congr eR.symm.toEquiv
          _ = Nat.card Kbar := Nat.card_congr eKbar.toEquiv
      have hR_coprime_q : Nat.Coprime q (Nat.card R) := by
        simpa [hR_card_eq_Kbar] using hKbar_coprime

      have hR_ne_bot : R ≠ ⊥ := by
        intro hR_bot
        have hKbar_card_gt : 1 < Nat.card Kbar :=
          (Subgroup.one_lt_card_iff_ne_bot (H := Kbar)).2 hKbar_ne_bot
        have hR_card_one : Nat.card R = 1 := by
          rw [hR_bot, Subgroup.card_bot]
        have hKbar_card_one : Nat.card Kbar = 1 := by
          rw [← hR_card_eq_Kbar, hR_card_one]
        omega

      have hR_data :
          @IsMinimalNormal (Q ⧸ H) _ Kbar hKbar_normal ∧
            ∃ r : ℕ, Nat.Prime r ∧ IsElementaryAbelian r R := by
        -- This is exactly the remaining source paragraph after Zassenhaus:
        -- the minimal normal layer first makes `R` characteristically simple;
        -- the Frattini argument then forces a Sylow subgroup of `R` to be all
        -- of `R`, hence the layer is an elementary abelian `r`-group.
        have hKbar_minimal_layer_eq :
              ∀ Mbar : Subgroup (Q ⧸ H), [Mbar.Normal] → [IsMinimalNormal Mbar] →
                Mbar ≤ Kbar → Mbar ≠ ⊥ → Mbar = Kbar := by
            intro Mbar hMbar_norm hMbar_min hMbar_le_Kbar hMbar_ne_bot
            let : Mbar.Normal := hMbar_norm
            let : IsMinimalNormal Mbar := hMbar_min
            -- Source core: choose the corresponding `T ≤ R`; if `T < R`, the
            -- proper over-Sylow subgroup is `q`-nilpotent and part (d) gives a
            -- nontrivial normal `q'`-subgroup contradiction. Hence `T = R`.
            let Msub : Subgroup Kbar := Mbar.subgroupOf Kbar
            let eKR : Kbar ≃* R := eKbar.symm.trans eR
            let T : Subgroup R := Msub.map eKR.toMonoidHom
            have hT_top : T = ⊤ := by
              by_contra hT_ne_top
              have hMbar_ne_Kbar : Mbar ≠ Kbar := by
                intro hMbar_eq
                have hMsub_top : Msub = ⊤ := by
                  exact Subgroup.subgroupOf_eq_top.mpr (by simp [hMbar_eq])
                have hT_top' : T = ⊤ := by
                  change Msub.map eKR.toMonoidHom = ⊤
                  rw [hMsub_top]
                  exact Subgroup.map_top_of_surjective eKR.toMonoidHom eKR.surjective
                exact hT_ne_top hT_top'
              let Sbar : Subgroup (Q ⧸ H) := (S : Subgroup Q).map π
              have hSbar_p : IsPGroup q Sbar := by
                simpa [Sbar] using S.isPGroup'.map π
              have hSbar_sup_Kbar : Sbar ⊔ Kbar = ⊤ := by
                let ρ : Q →* ((Q ⧸ H) ⧸ Kbar) := (QuotientGroup.mk' Kbar).comp π
                have hρ_surj : Function.Surjective ρ := by
                  intro z
                  rcases QuotientGroup.mk'_surjective Kbar z with ⟨y, hy⟩
                  rcases QuotientGroup.mk'_surjective H y with ⟨x, hx⟩
                  refine ⟨x, ?_⟩
                  calc
                    ρ x = (QuotientGroup.mk' Kbar) y := by
                      simpa [ρ, π] using congrArg (QuotientGroup.mk' Kbar) hx
                    _ = z := hy
                let Pquot : Sylow q ((Q ⧸ H) ⧸ Kbar) := S.mapSurjective (f := ρ) hρ_surj
                have hPquot_top : (Pquot : Subgroup ((Q ⧸ H) ⧸ Kbar)) = ⊤ := by
                  symm
                  exact Pquot.is_maximal'
                    (hquot_q.to_subgroup (⊤ : Subgroup ((Q ⧸ H) ⧸ Kbar))) le_top
                have hSρ_top : (S : Subgroup Q).map ρ = ⊤ := by
                  simpa [Pquot] using hPquot_top
                let qbar : (Q ⧸ H) →* ((Q ⧸ H) ⧸ Kbar) := QuotientGroup.mk' Kbar
                have hSbar_map_top : Sbar.map qbar = ⊤ := by
                  simpa [Sbar, qbar, ρ, Subgroup.map_map] using hSρ_top
                have hqbar_range : qbar.range = ⊤ := by
                  exact MonoidHom.range_eq_top_of_surjective qbar
                    (QuotientGroup.mk'_surjective Kbar)
                have hmap_range : Sbar.map qbar = qbar.range := by
                  rw [hSbar_map_top, hqbar_range]
                have hcodisj_ker : Codisjoint Sbar qbar.ker :=
                  (Subgroup.map_eq_range_iff (f := qbar) (H := Sbar)).1 hmap_range
                have hcodisj : Codisjoint Sbar Kbar := by
                  simpa [qbar, QuotientGroup.ker_mk'] using hcodisj_ker
                simpa [codisjoint_iff, sup_comm] using hcodisj
              have hLbar_lt_top : Sbar ⊔ Mbar < ⊤ :=
                hkt_sup_lt_top_of_sup_eq_top_of_coprime_normal
                  (S := Sbar) (K := Kbar) (M := Mbar)
                  hSbar_p hKbar_coprime hMbar_le_Kbar hMbar_ne_Kbar hSbar_sup_Kbar
              let Lbar : Subgroup (Q ⧸ H) := Sbar ⊔ Mbar
              let L : Subgroup Q := Lbar.comap π
              have hS_le_L : (S : Subgroup Q) ≤ L := by
                intro x hx
                change π x ∈ Lbar
                exact (le_sup_left : Sbar ≤ Lbar) (Subgroup.mem_map_of_mem π hx)
              have hL_lt_top : L < ⊤ := by
                have hcomap_lt : Lbar.comap π < (⊤ : Subgroup (Q ⧸ H)).comap π :=
                  (Subgroup.comap_lt_comap_of_surjective (f := π)
                    (QuotientGroup.mk'_surjective H)).2 (by simpa [Lbar] using hLbar_lt_top)
                simpa [L] using hcomap_lt
              have hcompL : HasNormalPComplement q L :=
                hproper_over_sylow L hS_le_L hL_lt_top
              let M : Subgroup Q := Mbar.comap π
              have hM_le_L : M ≤ L := by
                intro x hx
                change π x ∈ Lbar
                exact (le_sup_right : Mbar ≤ Lbar) hx
              have hcompM : HasNormalPComplement q M :=
                hasNormalPComplement_of_le q hM_le_L hcompL
              have : M.Normal := hMbar_norm.comap π
              have hM_le_H : M ≤ H := by
                simpa [M, H] using
                  huppert_IV_6_2_d_normal_hasNormalPComplement_le_pCore_of_pPrimeCore_eq_bot
                    (Q := Q) (q := q) hcore_bot M hcompM
              have hM_map : M.map π = Mbar := by
                simpa [M] using
                  (Subgroup.map_comap_eq_self_of_surjective
                    (f := π) (h := QuotientGroup.mk'_surjective H) (H := Mbar))
              have hM_le_ker : M ≤ π.ker := by
                simpa [π, H, QuotientGroup.ker_mk'] using hM_le_H
              have hM_map_bot : M.map π = ⊥ := by
                exact (Subgroup.map_eq_bot_iff (H := M) (f := π)).2 hM_le_ker
              have hMbar_bot : Mbar = ⊥ := by
                rw [← hM_map, hM_map_bot]
              exact hMbar_ne_bot hMbar_bot
            have hMsub_top : Msub = ⊤ := by
              have htop_map : (⊤ : Subgroup Kbar).map eKR.toMonoidHom = (⊤ : Subgroup R) := by
                exact Subgroup.map_top_of_surjective eKR.toMonoidHom eKR.surjective
              have hmap_top : Msub.map eKR.toMonoidHom = (⊤ : Subgroup Kbar).map eKR.toMonoidHom := by
                change T = (⊤ : Subgroup Kbar).map eKR.toMonoidHom
                rw [hT_top, htop_map]
              exact (Subgroup.map_injective (f := eKR.toMonoidHom) eKR.injective) hmap_top
            exact le_antisymm hMbar_le_Kbar ((Subgroup.subgroupOf_eq_top).1 hMsub_top)
        have hKbar_minimal :
            @IsMinimalNormal (Q ⧸ H) _ Kbar hKbar_normal := by
          refine ⟨?_⟩
          intro N hN_normal hN_le_Kbar
          by_cases hN_bot : N = ⊥
          · exact Or.inl hN_bot
          · right
            let : N.Normal := hN_normal
            obtain ⟨Mbar, hMbar_norm, hMbar_le_N, hMbar_ne_bot, hMbar_min⟩ :=
              exists_minimal_normal_le (G := Q ⧸ H) N hN_normal hN_bot
            have : Mbar.Normal := hMbar_norm
            have : IsMinimalNormal Mbar := by
              refine ⟨?_⟩
              intro L hL_normal hL_le_Mbar
              by_cases hL_bot : L = ⊥
              · exact Or.inl hL_bot
              · right
                exact hMbar_min L hL_normal hL_le_Mbar hL_bot
            have hMbar_eq_Kbar : Mbar = Kbar :=
              hKbar_minimal_layer_eq Mbar (hMbar_le_N.trans hN_le_Kbar) hMbar_ne_bot
            exact le_antisymm hN_le_Kbar (by simpa [hMbar_eq_Kbar] using hMbar_le_N)
        have hR_char_simple :
            ∀ N : Subgroup R, N.Characteristic → N = ⊥ ∨ N = ⊤ := by
          intro N hNchar
          let eRK : R ≃* Kbar := eR.symm.trans eKbar
          let Nbar : Subgroup Kbar := N.map eRK.toMonoidHom
          have hNbar_char : Nbar.Characteristic := by
            have : N.Characteristic := hNchar
            simpa [Nbar, eRK] using
              (section8_characteristic_map_equiv (G := R) (G' := Kbar) N eRK)
          let Namb : Subgroup (Q ⧸ H) := Nbar.map Kbar.subtype
          have hNamb_normal : Namb.Normal := by
            have : Nbar.Characteristic := hNbar_char
            dsimp [Namb]
            infer_instance
          have hNamb_le_Kbar : Namb ≤ Kbar := by
            intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
            exact y.property
          have : @IsMinimalNormal (Q ⧸ H) _ Kbar hKbar_normal := hKbar_minimal
          rcases IsMinimalNormal.minimal Namb hNamb_le_Kbar with hNamb_bot | hNamb_top
          · left
            have hNbar_bot : Nbar = ⊥ := by
              have hmap_bot : Nbar.map Kbar.subtype = (⊥ : Subgroup Kbar).map Kbar.subtype := by
                simpa [Namb] using hNamb_bot
              exact (Subgroup.map_injective (f := Kbar.subtype) Kbar.subtype_injective) hmap_bot
            have hN_map_bot : N.map eRK.toMonoidHom = (⊥ : Subgroup Kbar) := by
              simpa [Nbar] using hNbar_bot
            have hbot_map : (⊥ : Subgroup R).map eRK.toMonoidHom = (⊥ : Subgroup Kbar) := by
              simp
            exact (Subgroup.map_injective (f := eRK.toMonoidHom) eRK.injective)
              (by simpa [hbot_map] using hN_map_bot)
          · right
            have htop_map : (⊤ : Subgroup Kbar).map Kbar.subtype = Kbar := by
              simpa [MonoidHom.range_eq_map] using
                (Kbar.range_subtype : Kbar.subtype.range = Kbar)
            have hNbar_top : Nbar = ⊤ := by
              have hmap_top : Nbar.map Kbar.subtype = (⊤ : Subgroup Kbar).map Kbar.subtype := by
                simpa [Namb, htop_map] using hNamb_top
              exact (Subgroup.map_injective (f := Kbar.subtype) Kbar.subtype_injective) hmap_top
            have htop_map_e : (⊤ : Subgroup R).map eRK.toMonoidHom = (⊤ : Subgroup Kbar) := by
              exact Subgroup.map_top_of_surjective eRK.toMonoidHom eRK.surjective
            have hN_map_top : N.map eRK.toMonoidHom = (⊤ : Subgroup R).map eRK.toMonoidHom := by
              change Nbar = (⊤ : Subgroup R).map eRK.toMonoidHom
              rw [hNbar_top, htop_map_e]
            exact (Subgroup.map_injective (f := eRK.toMonoidHom) eRK.injective) hN_map_top
        have hR_pgroup : ∃ r : ℕ, Nat.Prime r ∧ IsPGroup r R := by
          have hR_card_ne_one : Nat.card R ≠ 1 := by
            intro hcard
            have hR_bot' : R = ⊥ := (Subgroup.card_eq_one (H := R)).1 hcard
            exact hR_ne_bot hR_bot'
          obtain ⟨r, hr, hr_dvd_R⟩ := Nat.exists_prime_and_dvd hR_card_ne_one
          have : Fact r.Prime := ⟨hr⟩
          let Pr : Sylow r R := default
          have hPr_top : (Pr : Subgroup R) = ⊤ := by
            let ιR : R →* Q := K.subtype.comp R.subtype
            let Pamb : Subgroup Q := (Pr : Subgroup R).map ιR
            let Namb : Subgroup Q := Subgroup.normalizer (Pamb : Set Q)
            let L : Subgroup Q := H ⊔ Namb
            have hPr_top_of_Ltop : L = ⊤ → (Pr : Subgroup R) = ⊤ := by
              intro hLtop
              have hcompR : (H.subgroupOf K).IsComplement' R := by
                simpa only [HK] using hHK_R_compl
              have hK_le_comap : K ≤ Kbar.comap (QuotientGroup.mk' H) := by
                intro x hx
                simpa [K, π] using hx
              exact hkt_sylow_eq_top_of_H_sup_normalizer_image_top
                (H := H) (K := K) (Kbar := Kbar) (R := R)
                hK_le_comap hKbar_minimal hcompR hR_card_eq_Kbar Pr hr_dvd_R rfl
                (by simpa [L, Namb, Pamb, ιR] using hLtop)
            have hFalse_of_Lproper : L < ⊤ → False := by
              intro hLproper
              have hcompR : HK.IsComplement' R := by
                simpa [HK] using hHK_R_compl
              have hH_p : IsPGroup q H := by
                simpa [H] using pCore_isPGroup (G := Q) (p := q)
              have hHK_p : IsPGroup q HK := by
                exact hH_p.of_equiv
                  (Subgroup.subgroupOfEquivOfLe (H := H) (K := K) hH_le_K).symm
              have hr_ne_q : r ≠ q := by
                intro hrq
                have hq_dvd_R : q ∣ Nat.card R := by
                  simpa [hrq] using hr_dvd_R
                exact ((Fact.out : Nat.Prime q).coprime_iff_not_dvd.mp hR_coprime_q) hq_dvd_R
              have hK_normal : K.Normal := by
                simpa [K, π] using hKbar_normal.comap π
              let : K.Normal := hK_normal
              obtain ⟨Pk, hPk_eq⟩ :=
                hkt_sylow_map_subtype_of_complement_coprime
                  (q := q) (r := r) hcompR hHK_p hr_ne_q Pr
              have hPamb_eq : Pamb = (Pk : Subgroup K).map K.subtype := by
                rw [hPk_eq]
                simp [Pamb, ιR, Subgroup.map_map]
              have hK_sup_Namb_top : K ⊔ Namb = ⊤ := by
                have hfr := Sylow.normalizer_sup_eq_top (p := r) (N := K) Pk
                simpa [Namb, hPamb_eq, sup_comm] using hfr
              let Lbar : Subgroup (Q ⧸ H) := L.map π
              have hKbar_hall : IsHallSubgroup ({p : Nat.Primes | p.val ≠ q}) Kbar := by
                exact hkt_isHallSubgroup_non_q_of_coprime_quotient_pgroup
                  (G := Q ⧸ H) (q := q) (K := Kbar) hKbar_coprime hquot_q
              have hKbar_sup_Lbar_top : Kbar ⊔ Lbar = ⊤ := by
                let Nbar : Subgroup (Q ⧸ H) := Namb.map π
                have hK_map : K.map π = Kbar := by
                  simpa [K] using
                    (Subgroup.map_comap_eq_self_of_surjective
                      (f := π) (h := QuotientGroup.mk'_surjective H) (H := Kbar))
                have hKbar_sup_Nbar_top : Kbar ⊔ Nbar = ⊤ := by
                  calc
                    Kbar ⊔ Nbar = K.map π ⊔ Namb.map π := by rw [hK_map]
                    _ = (K ⊔ Namb).map π := by
                      rw [← Subgroup.map_sup]
                    _ = ⊤ := by
                      rw [hK_sup_Namb_top]
                      exact Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective H)
                have hNbar_le_Lbar : Nbar ≤ Lbar := by
                  exact Subgroup.map_mono (f := π) (show Namb ≤ L from le_sup_right)
                exact top_le_iff.mp (by
                  rw [← hKbar_sup_Nbar_top]
                  exact sup_le_sup_left hNbar_le_Lbar Kbar)
              have hLindex : ¬ q ∣ L.index := by
                let qprime : Nat.Primes := ⟨q, Fact.out⟩
                have hqprime_not_mem : qprime ∉ ({p : Nat.Primes | p.val ≠ q}) := by
                  intro hmem
                  exact hmem rfl
                have hLbar_index : ¬ q ∣ Lbar.index := by
                  simpa [qprime] using
                    (hkt_prime_not_dvd_index_of_sup_hall
                      (G := Q ⧸ H) (π := ({p : Nat.Primes | p.val ≠ q}))
                      (K := Kbar) (U := Lbar) (p := qprime)
                      hKbar_hall hqprime_not_mem hKbar_sup_Lbar_top)
                have hker_le_L : π.ker ≤ L := by
                  intro x hx
                  have hxH : x ∈ H := by
                    simpa [π, QuotientGroup.ker_mk'] using hx
                  exact (le_sup_left : H ≤ L) hxH
                have hindex_eq : Lbar.index = L.index := by
                  simpa [Lbar] using
                    (Subgroup.index_map_eq L (QuotientGroup.mk'_surjective H) hker_le_L)
                intro hqL
                exact hLbar_index (by simpa [hindex_eq] using hqL)
              have hcompL : HasNormalPComplement q L :=
                hkt_hasNormalPComplement_of_proper_index_not_dvd
                  (Q := Q) (q := q) S hproper_over_sylow hLproper hLindex
              have hPamb_p : IsPGroup r Pamb := by
                simpa [Pamb, ιR] using
                  IsPGroup.map (p := r) (H := (Pr : Subgroup R)) Pr.isPGroup' ιR
              have hPamb_cent_H : Pamb ≤ Subgroup.centralizer (H : Set Q) := by
                intro x hxP
                rw [Subgroup.mem_centralizer_iff]
                intro a ha
                have hx_r : IsPElement (p := r) x := by
                  let xP : Pamb := ⟨x, hxP⟩
                  rcases (IsPGroup.iff_orderOf (p := r) (G := Pamb)).1 hPamb_p xP with ⟨n, hn⟩
                  exact ⟨n, by simpa [xP, Subgroup.orderOf_coe] using hn⟩
                have hx_norm_H : x ∈ Subgroup.normalizer (H : Set Q) := by
                  have htop : Subgroup.normalizer (H : Set Q) = (⊤ : Subgroup Q) :=
                    Subgroup.normalizer_eq_top_iff.mpr (inferInstance : H.Normal)
                  simp [htop]
                have hx_Namb : x ∈ Namb := by
                  exact (Subgroup.le_normalizer (H := Pamb)) hxP
                have hx_L : x ∈ L := (le_sup_right : Namb ≤ L) hx_Namb
                have hgen_le_L : H ⊔ (Subgroup.zpowers x : Subgroup Q) ≤ L := by
                  exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hx_L)
                have hcomp_gen :
                    HasNormalPComplement q (↥(H ⊔ (Subgroup.zpowers x : Subgroup Q))) :=
                  hasNormalPComplement_of_le q hgen_le_L hcompL
                exact hkt_generated_coprime_action_trivial_from_complement
                  (Q := Q) (q := q) H r x hH_p hr hr_ne_q hx_r hx_norm_H hcomp_gen a ha
              let CR : Subgroup R := (Subgroup.centralizer (H : Set Q)).comap ιR
              have hR_pElements_le_CR : pElementsSubgroup r R ≤ CR := by
                unfold pElementsSubgroup
                rw [Subgroup.closure_le]
                intro y hy
                obtain ⟨g, hgPr⟩ :=
                  hkt_exists_conj_mem_sylow_of_isPElement (Q := R) (q := r) Pr hy
                have hconj_cent : ιR (g * y * g⁻¹) ∈ Subgroup.centralizer (H : Set Q) := by
                  exact hPamb_cent_H (Subgroup.mem_map.mpr ⟨g * y * g⁻¹, hgPr, rfl⟩)
                have : (Subgroup.centralizer (H : Set Q)).Normal :=
                  Subgroup.normal_centralizer (H := H)
                have hback :
                    (ιR g)⁻¹ * ιR (g * y * g⁻¹) * ((ιR g)⁻¹)⁻¹ ∈
                      Subgroup.centralizer (H : Set Q) :=
                  (inferInstance : (Subgroup.centralizer (H : Set Q)).Normal).conj_mem
                    (ιR (g * y * g⁻¹)) hconj_cent (ιR g)⁻¹
                change ιR y ∈ Subgroup.centralizer (H : Set Q)
                convert hback using 1
                simp only [map_mul, map_inv]
                simp [mul_assoc]
              have hpElems_top : pElementsSubgroup r R = ⊤ :=
                hkt_pElementsSubgroup_top_of_characteristically_simple
                  (G := R) (r := r) hR_char_simple hr_dvd_R
              have htop_le_CR : (⊤ : Subgroup R) ≤ CR := by
                intro x _hx
                have hxElem : x ∈ pElementsSubgroup r R := by
                  rw [hpElems_top]
                  exact trivial
                exact hR_pElements_le_CR hxElem
              have hR_cent_Hsub : R ≤ Subgroup.centralizer (H.subgroupOf K : Set K) :=
                hkt_le_centralizer_subgroupOf_of_top_le_comap_centralizer
                  (H := H) (K0 := K) (R := R) htop_le_CR
              have hR_cent_HK : R ≤ Subgroup.centralizer (HK : Set K) := by
                simpa [HK] using hR_cent_Hsub
              exact hkt_false_of_centralizing_complement_part_d
                (Q := Q) (q := q) (H := H) (K := K) (HK := HK) (R := R)
                hcore_bot rfl rfl hHK_R_compl hR_coprime_q hHK_p hR_cent_HK hR_ne_bot
            exact hkt_sylow_top_of_top_or_proper_false
              (Q := Q) Pr hPr_top_of_Ltop hFalse_of_Lproper
          exact ⟨r, hr, hkt_isPGroup_of_sylow_top Pr hPr_top⟩
        obtain ⟨r, hr, hRp⟩ := hR_pgroup
        have : Fact r.Prime := ⟨hr⟩
        have hR_top_ne_bot : (⊤ : Subgroup R) ≠ ⊥ := by
          have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).2 hR_ne_bot
          exact top_ne_bot
        exact ⟨hKbar_minimal, ⟨r, hr,
          hkt_characteristicallySimple_isElementaryAbelian_of_isPGroup
            (G := R) (r := r) hR_top_ne_bot hR_char_simple hRp⟩⟩
      have hKbar_minimal : @IsMinimalNormal (Q ⧸ H) _ Kbar hKbar_normal := hR_data.1
      have hR_elementary : ∃ r : ℕ, Nat.Prime r ∧ IsElementaryAbelian r R := hR_data.2
      have hR_solv : Group.IsSolvable R := by
        obtain ⟨r, hr, hR_elem⟩ := hR_elementary
        have : Fact r.Prime := ⟨hr⟩
        have : IsElementaryAbelian r R := hR_elem
        have hR_p : IsPGroup r R := IsElementaryAbelian.isPGroup r R
        have : Group.IsNilpotent R := hR_p.isNilpotent
        exact IsNilpotent.to_isSolvable
      have : Group.IsSolvable R := hR_solv
      have hquot_solv' : Group.IsSolvable (K ⧸ HK) := by
        exact hkt_isSolvable_of_mulEquiv eR.symm
      have : Group.IsSolvable (K ⧸ HK) := hquot_solv'
      have hKbar_solv : Group.IsSolvable Kbar := hkt_isSolvable_of_mulEquiv eKbar
      exact ⟨by simpa [H] using hKbar_minimal, hKbar_solv⟩
    have hKbar_minimal : @IsMinimalNormal (Q ⧸ pCore q Q) _ Kbar hKbar_normal := hKbar_data.1
    have : Group.IsSolvable Kbar := hKbar_data.2
    have : Group.IsSolvable ((Q ⧸ pCore q Q) ⧸ Kbar) := by
      have hquot_nil : Group.IsNilpotent ((Q ⧸ pCore q Q) ⧸ Kbar) :=
        hquot_q.isNilpotent
      have : Group.IsNilpotent ((Q ⧸ pCore q Q) ⧸ Kbar) := hquot_nil
      exact IsNilpotent.to_isSolvable
    have hquot_solv : Group.IsSolvable (Q ⧸ pCore q Q) :=
      Group.isSolvable_of_ker_le_range Kbar.subtype
        (QuotientGroup.mk' Kbar) (by
          rw [QuotientGroup.ker_mk']
          simpa [MonoidHom.range_eq_map] using
            (Kbar.range_subtype :
              Kbar.subtype.range = Kbar).symm.le)
    exact ⟨hKbar_minimal, hquot_solv⟩
  have hKbar_minimal : @IsMinimalNormal (Q ⧸ pCore q Q) _ Kbar hKbar_normal := hquot_data.1
  have hquot_solv : Group.IsSolvable (Q ⧸ pCore q Q) := hquot_data.2
  have : Group.IsSolvable (pCore q Q) := by
    have hp : IsPGroup q (pCore q Q) := pCore_isPGroup (G := Q) (p := q)
    have : Group.IsNilpotent (pCore q Q) :=
      IsPGroup.isNilpotent (p := q) (G := pCore q Q) hp
    exact IsNilpotent.to_isSolvable
  have : Group.IsSolvable (Q ⧸ pCore q Q) := hquot_solv
  have hQ_solv : Group.IsSolvable Q :=
    Group.isSolvable_of_ker_le_range (pCore q Q).subtype
      (QuotientGroup.mk' (pCore q Q)) (by
        rw [QuotientGroup.ker_mk']
        simpa [MonoidHom.range_eq_map] using
          ((pCore q Q).range_subtype :
            (pCore q Q).subtype.range = pCore q Q).symm.le)
  exact ⟨Kbar, hKbar_normal, hKbar_minimal, hKbar_ne_bot, hKbar_ne_top,
    hKbar_coprime, hquot_q, hquot_dvd, hquot_pcore_bot, hQ_solv⟩

/-- Corrected public boundary for Huppert IV.6.2(f) in the reduced hard branch.
It exposes the quotient normal `q`-complement produced in the source paragraph,
together with the nontrivial reduced quotient facts used by the later clauses;
the older solvability theorem below is just the projection of this package. -/
public theorem hkt_iv62_f_reduced_nonburnside_corrected_structure
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (hnot_Qp : ¬ IsPGroup q Q)
    (hq2 : q ≠ 2) (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    (hproper_rec : ∀ (H : Subgroup Q) (T : Sylow q H), H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H → HasNormalPComplement q (Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H)) → HasNormalPComplement q (Subgroup.normalizer (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H)) → HasNormalPComplement q H)
    (hsmall_rec : ∀ {R : Type u} [Group R] [Finite R] (T : Sylow q R), Nat.card R < Nat.card Q → q ∣ Nat.card R → HasNormalPComplement q (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R)) → HasNormalPComplement q (Subgroup.normalizer (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R)) → HasNormalPComplement q R)
    {U : Subgroup Q}
    (hU_ne_bot : U ≠ ⊥) (hU_p : IsPGroup q U)
    (hU_no_complement : ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))))
    (hUmax :
      ∀ W : Subgroup Q,
        W ≠ ⊥ →
        IsPGroup q W →
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
          Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q * (Nat.card Q + 1) + Nat.card W ≤ Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q * (Nat.card Q + 1) + Nat.card U)
    (P : Sylow q (Subgroup.normalizer (U : Set Q)))
    (hUS : U < (S : Subgroup Q))
    (hUN_le_P :
      U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≤
        (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hcardUP :
      Nat.card U < Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hNtop : Subgroup.normalizer (U : Set Q) = ⊤)
    (hU_eq_core : U = pCore q Q) :
    ∃ Kbar : Subgroup (Q ⧸ pCore q Q), ∃ hKbar_normal : Kbar.Normal,
      @IsMinimalNormal (Q ⧸ pCore q Q) _ Kbar hKbar_normal ∧
        Kbar ≠ ⊥ ∧
          Kbar ≠ ⊤ ∧
            Nat.Coprime q (Nat.card Kbar) ∧
              IsPGroup q ((Q ⧸ pCore q Q) ⧸ Kbar) ∧
                q ∣ Nat.card (Q ⧸ pCore q Q) ∧
                  pCore q (Q ⧸ pCore q Q) = ⊥ ∧
                    Group.IsSolvable Q := by
  exact hkt_iv62_f_reduced_nonburnside_isSolvable_core
    (Q := Q) (q := q) (U := U)
    hcore_bot hnot_Qp hq2 S hq_dvd hnot_burnside hcentralizer_dvd
    hnormalizer_rank_dvd hproper_rec hsmall_rec hU_ne_bot hU_p hU_no_complement
    hUmax P hUS hUN_le_P hcardUP hNtop hU_eq_core


private theorem hkt_omega₁_card_eq_pow_generatorRank_of_commutative_pgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [IsMulCommutative G] [Fact (IsPGroup p G)] :
    Nat.card (omega₁ (G := G) (p := p)) = p ^ generatorRank G := by
  let Qquot : Type _ := G ⧸ frattini G
  have hΩquot :
      Nat.card (omega₁ (G := G) (p := p)) = Nat.card Qquot := by
    simpa [Qquot] using
      section9_c92_omega1_card_eq_card_quotient_frattini_of_commutative
        (p := p) G
  have hQelem : IsElementaryAbelian p Qquot := by
    simpa [Qquot] using isElementaryAbelian_quotient_frattini (R := G) (p := p)
  let : IsElementaryAbelian p Qquot := hQelem
  have hQcard : Nat.card Qquot = p ^ generatorRank Qquot :=
    elementaryAbelian_card_eq_pow_generatorRank (p := p) Qquot
  have hQ_le_G : generatorRank Qquot ≤ generatorRank G := by
    simpa [Qquot] using
      hkt_generatorRank_le_of_surjective
        (G := G) (H := G ⧸ frattini G)
        (QuotientGroup.mk' (frattini G))
        (QuotientGroup.mk'_surjective (frattini G))
  have hG_le_Q : generatorRank G ≤ generatorRank Qquot := by
    simpa [Qquot] using generatorRank_le_generatorRank_quotient_frattini (p := p) G
  have hgen_eq : generatorRank Qquot = generatorRank G := le_antisymm hQ_le_G hG_le_Q
  calc
    Nat.card (omega₁ (G := G) (p := p)) = Nat.card Qquot := hΩquot
    _ = p ^ generatorRank Qquot := hQcard
    _ = p ^ generatorRank G := by rw [hgen_eq]


private theorem hkt_isElementaryAbelian_quotient_of_isElementaryAbelian
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal]
    (hGelem : IsElementaryAbelian p G) :
    IsElementaryAbelian p (G ⧸ N) := by
  let : IsElementaryAbelian p G := hGelem
  let : IsMulCommutative G := hGelem.toIsMulCommutative
  let : CommGroup G := IsMulCommutative.instCommGroup
  refine
    { toIsMulCommutative := ?_
      exponent_dvd_p := ?_ }
  · have hcomm_bot : _root_.commutator G = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top]
      exact CommGroup.center_eq_top
    have hcomm_le : _root_.commutator G ≤ N := by
      rw [hcomm_bot]
      exact bot_le
    exact ⟨(Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := N)).2 hcomm_le |>.is_comm⟩
  · exact (Group.exponent_quotient_dvd (H := N)).trans
      (IsElementaryAbelian.exponent_dvd_p p G)

private theorem hkt_iv62_o_elementary_card_bound_to_rank_bound
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    {B : Subgroup Q} (hB_elem : IsElementaryAbelian q B)
    (hcard : Nat.card B ≤ q ^ 2) :
    generatorRank B ≤ 2 := by
  classical
  let : IsElementaryAbelian q B := hB_elem
  by_contra hle
  have hlt_rank : 2 < generatorRank B := Nat.lt_of_not_ge hle
  have hq_one : 1 < q := (Fact.out : Nat.Prime q).one_lt
  have hpow_lt : q ^ 2 < q ^ generatorRank B :=
    Nat.pow_lt_pow_right hq_one hlt_rank
  have hBcard_pow : Nat.card B = q ^ generatorRank B :=
    elementaryAbelian_card_eq_pow_generatorRank (p := q) B
  have hcard_lt : q ^ 2 < Nat.card B := by
    simpa [hBcard_pow] using hpow_lt
  exact (not_lt_of_ge hcard) hcard_lt

private theorem hkt_iv62_o_card_bound_of_relIndex_and_inf_bot
    {B : Type u} [Group B] [Finite B] {q : ℕ}
    (C1 C2 : Subgroup B)
    (hC1 : C1.index ≤ q) (hC2 : C2.index ≤ q)
    (hinf : C1 ⊓ C2 = (⊥ : Subgroup B)) :
    Nat.card B ≤ q ^ 2 := by
  classical
  have hcard_eq : Nat.card B = C1.index * Nat.card C1 := by
    rw [C1.index_mul_card.symm]
  have hcard_C1_le_index_C2 : Nat.card C1 ≤ C2.index := by
    have hcard_rel : Nat.card C1 = C2.relIndex C1 := by
      calc
        Nat.card C1 = (⊥ : Subgroup B).relIndex C1 := by
          rw [Subgroup.relIndex_bot_left]
        _ = (C1 ⊓ C2).relIndex C1 := by rw [hinf]
        _ = C2.relIndex C1 := by rw [Subgroup.inf_relIndex_left]
    have hrel_ne_zero : C2.relIndex (⊤ : Subgroup B) ≠ 0 := by
      rw [Subgroup.relIndex_top_right]
      exact Subgroup.index_ne_zero_of_finite (H := C2)
    have hrel_le : C2.relIndex C1 ≤ C2.relIndex (⊤ : Subgroup B) :=
      Subgroup.relIndex_le_of_le_right (H := C2) (K := C1) (L := ⊤) le_top
        hrel_ne_zero
    simpa [hcard_rel, Subgroup.relIndex_top_right] using hrel_le
  calc
    Nat.card B = C1.index * Nat.card C1 := hcard_eq
    _ ≤ q * q := Nat.mul_le_mul hC1 (hcard_C1_le_index_C2.trans hC2)
    _ = q ^ 2 := by rw [pow_two]

private theorem hkt_iv62_o_commutator_layer_rank_at_most_two_of_relIndex
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    {B : Subgroup Q} (hB_elem : IsElementaryAbelian q B)
    (C1 C2 : Subgroup B)
    (hC1 : C1.index ≤ q) (hC2 : C2.index ≤ q)
    (hinf : C1 ⊓ C2 = (⊥ : Subgroup B)) :
    generatorRank B ≤ 2 := by
  classical
  exact hkt_iv62_o_elementary_card_bound_to_rank_bound
    (Q := Q) (q := q) hB_elem
    (hkt_iv62_o_card_bound_of_relIndex_and_inf_bot
      (B := B) (q := q) C1 C2 hC1 hC2 hinf)

private theorem hkt_iv62_p_pCore_le_commutator_layer_centralizer
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    {B : Subgroup Q}
    (hB_le_center_pCore : B ≤ centerIn (G := Q) (pCore q Q : Subgroup Q)) :
    pCore q Q ≤ Subgroup.centralizer (B : Set Q) := by
  classical
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hb_center : b ∈ centerIn (G := Q) (pCore q Q : Subgroup Q) :=
    hB_le_center_pCore hb
  exact (Subgroup.mem_centralizer_iff.mp hb_center.2 x hx).symm

private theorem hkt_commutator_eq_bot_of_coprime_double_commutator_eq_bot
    {Q : Type u} [Group Q] [Finite Q]
    (W R : Subgroup Q)
    (hRnormW : R ≤ Subgroup.normalizer (W : Set Q))
    (hcoprime : Nat.Coprime (Nat.card R) (Nat.card W))
    (hdouble : ⁅⁅W, R⁆, R⁆ = (⊥ : Subgroup Q)) :
    ⁅W, R⁆ = (⊥ : Subgroup Q) := by
  classical
  have : Subgroup.Normalizes R W := ⟨hRnormW⟩
  have hcommAction2_eq_commAction :
      commutatorAction₂ (A := R) (G := W) =
        commutatorAction (A := R) (G := W) :=
    commutatorAction₂_eq_commutatorAction_of_coprime
      (G := W) (A := R) hcoprime
  have hcommAction_map :
      (commutatorAction (A := R) (G := W)).map W.subtype = ⁅W, R⁆ := by
    simpa using commutatorAction_subgroup_conj_map_eq_commutator W R hRnormW
  have hcommAction2_map_le :
      (commutatorAction₂ (A := R) (G := W)).map W.subtype ≤ ⁅⁅W, R⁆, R⁆ := by
    let C : Subgroup W := commutatorAction (A := R) (G := W)
    let S : Set W :=
      {x : W | ∃ a : R, ∃ h : W, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc
      (commutatorAction₂ (A := R) (G := W)).map W.subtype =
          (Subgroup.closure S).map W.subtype := by
        rfl
      _ = Subgroup.closure (W.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := W.subtype) S)
      _ ≤ ⁅⁅W, R⁆, R⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅W, R⁆, R⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : Q) ∈ ⁅W, R⁆ := by
          rw [← hcommAction_map]
          exact Subgroup.mem_map_of_mem W.subtype hhC
        have hcomm : ⁅(h : Q)⁻¹, (a : Q)⁆ ∈ ⁅⁅W, R⁆, R⁆ :=
          Subgroup.commutator_mem_commutator
            ((⁅W, R⁆ : Subgroup Q).inv_mem hhcomm) a.2
        simpa [commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormW, mul_assoc]
          using hcomm
  have hle : ⁅W, R⁆ ≤ (⊥ : Subgroup Q) := by
    intro x hx
    have hx_commAction : x ∈ (commutatorAction (A := R) (G := W)).map W.subtype := by
      rwa [hcommAction_map]
    have hx_commAction2 : x ∈ (commutatorAction₂ (A := R) (G := W)).map W.subtype := by
      rwa [hcommAction2_eq_commAction]
    have hx_double := hcommAction2_map_le hx_commAction2
    rwa [hdouble] at hx_double
  exact le_antisymm hle (show (⊥ : Subgroup Q) ≤ ⁅W, R⁆ from bot_le)
private theorem hkt_actsTrivially_of_isPGroup_on_cyclic_prime_order
    {A G : Type*} [Group A] [Group G] [Finite G] [MulDistribMulAction A G]
    {p : ℕ} (hp : Nat.Prime p) (hA : IsPGroup p A) (hG_cyclic : IsCyclic G)
    (hG_card : Nat.card G = p) :
    ActsTrivially (A := A) (G := G) := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic G := hG_cyclic
  let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
  have hA_top : IsPGroup p (⊤ : Subgroup A) := by
    simpa using hA.to_subgroup (⊤ : Subgroup A)
  have hφrange_p : IsPGroup p φ.range := by
    rw [MonoidHom.range_eq_map]
    exact IsPGroup.map (p := p) (H := (⊤ : Subgroup A)) hA_top φ
  have hmulAut_card : Nat.card (MulAut G) = p - 1 := by
    rw [IsCyclic.card_mulAut, hG_card, Nat.totient_prime hp]
  have hp_not_dvd_mulAut : ¬ p ∣ Nat.card (MulAut G) := by
    intro hp_dvd
    have hdiv_one : p ∣ 1 := by
      have hdiv_sub : p ∣ p - (p - 1) :=
        Nat.dvd_sub (dvd_refl p) (hmulAut_card ▸ hp_dvd)
      have hsub : p - (p - 1) = 1 := by
        have hp_eq : p = (p - 1) + 1 := by
          simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hp.pos).symm
        rw [hp_eq]
        exact Nat.add_sub_cancel_left (p - 1) 1
      rw [hsub] at hdiv_sub
      exact hdiv_sub
    exact hp.not_dvd_one hdiv_one
  have hp_not_dvd_range : ¬ p ∣ Nat.card φ.range := by
    intro hp_dvd
    exact hp_not_dvd_mulAut (hp_dvd.trans (Subgroup.card_subgroup_dvd_card φ.range))
  have hφrange_card_one : Nat.card φ.range = 1 :=
    (hφrange_p.card_eq_or_dvd).resolve_right hp_not_dvd_range
  have hφrange_bot : φ.range = ⊥ := (Subgroup.card_eq_one (H := φ.range)).1 hφrange_card_one
  intro a g
  have ha_range : φ a ∈ φ.range := ⟨a, rfl⟩
  have ha_bot : φ a ∈ (⊥ : Subgroup (MulAut G)) := by simpa [hφrange_bot] using ha_range
  have ha_one : φ a = 1 := by simpa using ha_bot
  simpa [φ, MulDistribMulAction.toMulAut_apply] using congrArg (fun f : MulAut G => f g) ha_one


/-- The final elementary permutation fact in Huppert IV.6.2(r): for odd `q`,
a `q`-group cannot act nontrivially on the two eigenspaces. -/
private theorem hkt_fin_two_perm_hom_eq_one_of_isPGroup_odd
    {A : Type*} [Group A] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hA : IsPGroup q A)
    (σ : A →* Equiv.Perm (Fin 2)) :
    σ = 1 := by
  classical
  have hA_top : IsPGroup q (⊤ : Subgroup A) := by
    simpa using hA.to_subgroup (⊤ : Subgroup A)
  have hσrange_p : IsPGroup q σ.range := by
    rw [MonoidHom.range_eq_map]
    exact IsPGroup.map (p := q) (H := (⊤ : Subgroup A)) hA_top σ
  have hperm_card : Nat.card (Equiv.Perm (Fin 2)) = 2 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hq_not_dvd_perm : ¬ q ∣ Nat.card (Equiv.Perm (Fin 2)) := by
    intro hdiv
    have hq_dvd_two : q ∣ 2 := by
      rw [← hperm_card]
      exact hdiv
    have hq_eq_two : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime q) Nat.prime_two).1
        hq_dvd_two
    exact hq2 hq_eq_two
  have hq_not_dvd_range : ¬ q ∣ Nat.card σ.range := by
    intro hdiv
    exact hq_not_dvd_perm (hdiv.trans (Subgroup.card_subgroup_dvd_card σ.range))
  have hσrange_card_one : Nat.card σ.range = 1 :=
    (hσrange_p.card_eq_or_dvd).resolve_right hq_not_dvd_range
  have hσrange_bot : σ.range = ⊥ :=
    (Subgroup.card_eq_one (H := σ.range)).1 hσrange_card_one
  ext a x
  have ha_range : σ a ∈ σ.range := ⟨a, rfl⟩
  have ha_bot : σ a ∈ (⊥ : Subgroup (Equiv.Perm (Fin 2))) := by
    simpa [hσrange_bot] using ha_range
  have ha_one : σ a = 1 := by simpa using ha_bot
  simp [ha_one]

private theorem hkt_iv62_q_preterminal_layer_card_eq_two_dimensional
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (A B : Subgroup Q)
    (A_le_sylow : A ≤ (S : Subgroup Q))
    (_A_commutative : IsMulCommutative A)
    (_A_not_le_pCore : ¬ A ≤ pCore q Q)
    (_A_rank_maximal :
      ∀ C : Subgroup Q,
        C ≤ (S : Subgroup Q) → IsMulCommutative C →
          ¬ C ≤ pCore q Q →
            generatorRank C ≤ generatorRank A)
    (A_normalizes_B : A ≤ Subgroup.normalizer (B : Set Q))
    (A_not_centralizes_B : ¬ A ≤ Subgroup.centralizer (B : Set Q))
    (_B_normal : B.Normal)
    (_B_le_pCore : B ≤ pCore q Q)
    (B_elementary : IsElementaryAbelian q B)
    (B_rank_at_most_two : generatorRank B ≤ 2)
    (_B_centralizer_eq_pCore : Subgroup.centralizer (B : Set Q) = pCore q Q) :
    Nat.card B = q ^ 2 := by
  classical
  have _hq2 : q ≠ 2 := hq2
  let : IsElementaryAbelian q B := B_elementary
  have hBcard_pow : Nat.card B = q ^ generatorRank B :=
    elementaryAbelian_card_eq_pow_generatorRank (p := q) B
  have hA_p : IsPGroup q A := IsPGroup.to_le S.isPGroup' A_le_sylow
  have hnot_rank_le_one : ¬ generatorRank B ≤ 1 := by
    intro hrank_le_one
    have hrank_zero_or_one : generatorRank B = 0 ∨ generatorRank B = 1 := by
      cases h : generatorRank B with
      | zero =>
          exact Or.inl rfl
      | succ n =>
          have hn_zero : n = 0 := by
            have hs : Nat.succ n ≤ 1 := by simpa [h] using hrank_le_one
            exact Nat.eq_zero_of_le_zero (Nat.succ_le_succ_iff.mp hs)
          exact Or.inr (by simp [hn_zero])
    rcases hrank_zero_or_one with hrank_zero | hrank_one
    · have hBcard_one : Nat.card B = 1 := by
        simpa [hrank_zero] using hBcard_pow
      have hBbot : B = ⊥ := (Subgroup.card_eq_one (H := B)).1 hBcard_one
      have hA_centralizes : A ≤ Subgroup.centralizer (B : Set Q) := by
        intro a _ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have hb_one : b = 1 := by simpa [hBbot] using hb
        simp [hb_one]
      exact A_not_centralizes_B hA_centralizes
    · have hBcard_q : Nat.card B = q := by
        simpa [hrank_one] using hBcard_pow
      have hB_cyclic : IsCyclic B := isCyclic_of_prime_card hBcard_q
      have : Subgroup.Normalizes A B := ⟨A_normalizes_B⟩
      have htriv : ActsTrivially (A := A) (G := B) :=
        hkt_actsTrivially_of_isPGroup_on_cyclic_prime_order
          (A := A) (G := B) (p := q) (Fact.out : Nat.Prime q)
          hA_p hB_cyclic hBcard_q
      have hcomm : ⁅A, B⁆ = ⊥ :=
        commutator_eq_bot_of_actsTrivially_subgroup_conj
          (K := B) (R := A) A_normalizes_B htriv
      have hA_centralizes : A ≤ Subgroup.centralizer (B : Set Q) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm
      exact A_not_centralizes_B hA_centralizes
  have htwo_le_rank : 2 ≤ generatorRank B := by
    cases h : generatorRank B with
    | zero =>
        exact False.elim (hnot_rank_le_one (by simp [h]))
    | succ n =>
        cases hn : n with
        | zero =>
            exact False.elim (hnot_rank_le_one (by simp [h, hn]))
        | succ m =>
            simp
  have hrank_eq_two : generatorRank B = 2 :=
    le_antisymm B_rank_at_most_two htwo_le_rank
  simpa [hrank_eq_two] using hBcard_pow


/-!
Internalized Huppert IV.6.2(r) linear/eigenline infrastructure.
These declarations are copied into this file so the book-order proof does not depend on the old split part_r modules.
-/


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\Field.lean`. -/

private theorem hkt_iv62_r_coprime_order_nonscalar_element_exists
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (_hcore_bot : pPrimeCore q Q = ⊥) (_hnot_Qp : ¬ IsPGroup q Q)
    (_hq2 : q ≠ 2) (S : Sylow q Q)
    (_hq_dvd : q ∣ Nat.card Q)
    (_hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (_hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (_hnormalizer_rank_dvd : HasNormalPComplement q
      (↥(Subgroup.normalizer
        (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    (_hproper_rec : ∀ (H : Subgroup Q) (T : Sylow q H), H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H → HasNormalPComplement q (Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q H)
    (_hsmall_rec : ∀ {R : Type u} [Group R] [Finite R] (T : Sylow q R), Nat.card R < Nat.card Q → q ∣ Nat.card R → HasNormalPComplement q (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q R)
    {U : Subgroup Q}
    (_hU_ne_bot : U ≠ ⊥) (_hU_p : IsPGroup q U)
    (_hU_no_complement : ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))))
    (_hUmax :
      ∀ W : Subgroup Q,
        W ≠ ⊥ →
        IsPGroup q W →
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
          Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q * (Nat.card Q + 1) + Nat.card W ≤ Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q * (Nat.card Q + 1) + Nat.card U)
    (P : Sylow q (Subgroup.normalizer (U : Set Q)))
    (_hUS : U < (S : Subgroup Q))
    (_hUN_le_P :
      U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≤
        (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (_hcardUP :
      Nat.card U < Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (_hNtop : Subgroup.normalizer (U : Set Q) = ⊤)
    (_hU_eq_core : U = pCore q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : Subgroup Q) (_hC_cyclic : IsCyclic C)
    (hC_coprime : Nat.Coprime q (Nat.card C))
    (hA_conj_commutes_C :
      ∀ a : L.1, ∀ c : C,
        Commute
          (M.2.1 ((a : Q) * (c : Q) * (a : Q)⁻¹))
          (M.2.1 (c : Q)))
    (hC_generator :
      ∃ c : Q,
        C = Subgroup.zpowers c ∧
          ∀ μ : ZMod q,
            (M.2.1 c).toLinearMap ≠
              μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) :
    ∃ c : Q,
      Nat.Coprime q (orderOf c) ∧
        (∀ a : L.1, ∀ d : Subgroup.zpowers c,
          Commute
            (M.2.1 ((a : Q) * (d : Q) * (a : Q)⁻¹))
            (M.2.1 (d : Q))) ∧
          ∀ μ : ZMod q,
            (M.2.1 c).toLinearMap ≠ μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) := by
  classical
  obtain ⟨c, hC_eq_zpowers, hc_not_scalar⟩ := hC_generator
  refine ⟨c, ?_, ?_, hc_not_scalar⟩
  · convert hC_coprime using 1
    simp [hC_eq_zpowers, Nat.card_zpowers]
  · intro a d
    have hmem : (d : Q) ∈ C :=
      hC_eq_zpowers.symm ▸ d.property
    let dC : C := ⟨(d : Q), hmem⟩
    apply hA_conj_commutes_C a dC

private theorem hkt_iv62_r_quadratic_extension_choice_exists
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) }) :
    Nonempty (Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF }))) := by
  classical
  have _ := hq2
  have _ := C
  exact ⟨ULift.{u} (GaloisField q 2), inferInstance, ⟨⟨inferInstance, by
    rw [Nat.card_congr (Equiv.ulift : ULift.{u} (GaloisField q 2) ≃ GaloisField q 2)]
    simpa using (GaloisField.card (p := q) (n := 2) (by decide : (2 : ℕ) ≠ 0))⟩,
    ⟨ULift.ringEquiv.symm.toRingHom.comp (algebraMap (ZMod q) (GaloisField q 2)),
      by exact RingHom.injective _⟩⟩⟩

private theorem hkt_iv62_r_quadratic_splitting_field_exists
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) }) :
    Nonempty (Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF }))) := by
  classical
  obtain ⟨K0⟩ := hkt_iv62_r_quadratic_extension_choice_exists
    (Q := Q) (q := q) hq2 S L M C
  exact ⟨K0⟩

private theorem hkt_linearEquiv_pow_apply_eigenvector
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (f : V ≃ₗ[F] V) {v : V} {μ : F}
    (h : f v = μ • v) :
    ∀ n : ℕ, (f ^ n) v = (μ ^ n) • v := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (f ^ (n + 1)) v = f ((f ^ n) v) := by
          rw [pow_succ']
          rfl
        _ = f ((μ ^ n) • v) := by rw [ih]
        _ = (μ ^ n) • f v := by simp
        _ = (μ ^ n) • (μ • v) := by rw [h]
        _ = (μ ^ (n + 1)) • v := by
          rw [pow_succ']
          simp [smul_smul, mul_comm]


private theorem hkt_iv62_r_cyclic_generator_rhoF_ne_one
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))))
    (rhoF_lifts_nonscalar :
      letI : Field K.1 := K.2.1
      ∃ c : C.1,
      (∀ μ : ZMod q,
        (M.2.1 (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) ∧
      (∀ μ : K.1,
        (rhoF (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End K.1 (Fin 2 → K.1))))
    (rhoF_compatible :
      ∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => K.2.2.2.1 (v i)) =
          fun i => K.2.2.2.1 ((M.2.1 g v) i))
    (generator : C.1)
    (generator_spans : ∀ c : C.1, ∃ n : ℕ, (generator.1 : Q) ^ n = (c.1 : Q)) :
    rhoF (generator.1 : Q) ≠ 1 := by
  classical
  have _ := rhoF_compatible
  let : Field K.1 := K.2.1
  obtain ⟨c, _hc_rho, hc_rhoF⟩ := rhoF_lifts_nonscalar
  obtain ⟨n, hn⟩ :=
    (generator_spans c)
  intro hgen
  apply hc_rhoF (1 : K.1)
  have hc_eq : (c.1 : Q) = (generator.1 : Q) ^ n := by
    exact hn.symm
  have hceq : rhoF (c.1 : Q) = 1 := by
    calc
      rhoF (c.1 : Q) = rhoF ((generator.1 : Q) ^ n) := by rw [hc_eq]
      _ = rhoF (generator.1 : Q) ^ n := by rw [map_pow]
      _ = 1 := by simp [hgen]
  have htemp : (rhoF (c.1 : Q)).toLinearMap = 1 := by
    calc
      (rhoF (c.1 : Q)).toLinearMap
          = (rhoF (c.1 : Q) : (Fin 2 → K.fst) →ₗ[K.fst] Fin 2 → K.fst) := rfl
      _ = ((1 : (Fin 2 → K.fst) ≃ₗ[K.fst] Fin 2 → K.fst) : (Fin 2 → K.fst) →ₗ[K.fst] Fin 2 → K.fst) :=
        congrArg (fun (φ : (Fin 2 → K.fst) ≃ₗ[K.fst] Fin 2 → K.fst) => (φ : (Fin 2 → K.fst) →ₗ[K.fst] Fin 2 → K.fst)) hceq
      _ = 1 := rfl
  simpa [one_smul] using htemp

private theorem hkt_iv62_r_cyclic_generator_rhoF_order_dvd_card
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))))
    (rhoF_lifts_nonscalar :
      letI : Field K.1 := K.2.1
      ∃ c : C.1,
      (∀ μ : ZMod q,
        (M.2.1 (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) ∧
      (∀ μ : K.1,
        (rhoF (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End K.1 (Fin 2 → K.1))))
    (rhoF_compatible :
      ∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => K.2.2.2.1 (v i)) =
          fun i => K.2.2.2.1 ((M.2.1 g v) i))
    (generator : C.1)
    (generator_spans : ∀ c : C.1, ∃ n : ℕ, (generator.1 : Q) ^ n = (c.1 : Q)) :
    orderOf (rhoF (generator.1 : Q)) ∣ Nat.card C.1 := by
  classical
  have _ := rhoF_lifts_nonscalar
  have _ := rhoF_compatible
  have _ := generator_spans
  have horder_subtype : orderOf (generator.1 : Q) = orderOf generator :=
    orderOf_submonoid generator
  have hgen_dvd_card : orderOf generator ∣ Nat.card C.1 := by
    simpa using
      (Subgroup.orderOf_dvd_natCard (⊤ : Subgroup C.1)
        (show generator ∈ (⊤ : Subgroup C.1) by simp))
  have hmap_dvd : orderOf (rhoF (generator.1 : Q)) ∣ orderOf (generator.1 : Q) :=
    orderOf_map_dvd rhoF (generator.1 : Q)
  exact hmap_dvd.trans (by simpa [horder_subtype] using hgen_dvd_card)

private theorem hkt_iv62_r_cyclic_generator_rhoF_order_coprime
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))))
    (rhoF_lifts_nonscalar :
      letI : Field K.1 := K.2.1
      ∃ c : C.1,
      (∀ μ : ZMod q,
        (M.2.1 (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) ∧
      (∀ μ : K.1,
        (rhoF (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End K.1 (Fin 2 → K.1))))
    (rhoF_compatible :
      ∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => K.2.2.2.1 (v i)) =
          fun i => K.2.2.2.1 ((M.2.1 g v) i))
    (generator : C.1)
    (generator_spans : ∀ c : C.1, ∃ n : ℕ, (generator.1 : Q) ^ n = (c.1 : Q)) :
    Nat.Coprime q (orderOf (rhoF (generator.1 : Q))) := by
  classical
  exact C.2.2.1.of_dvd_right
    (hkt_iv62_r_cyclic_generator_rhoF_order_dvd_card
      (Q := Q) (q := q) S L M C K rhoF rhoF_lifts_nonscalar rhoF_compatible generator generator_spans)

private theorem hkt_iv62_r_cyclic_generator_rhoF_order_ge_two
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))))
    (rhoF_lifts_nonscalar :
      letI : Field K.1 := K.2.1
      ∃ c : C.1,
      (∀ μ : ZMod q,
        (M.2.1 (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) ∧
      (∀ μ : K.1,
        (rhoF (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End K.1 (Fin 2 → K.1))))
    (rhoF_compatible :
      ∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => K.2.2.2.1 (v i)) =
          fun i => K.2.2.2.1 ((M.2.1 g v) i))
    (generator : C.1)
    (generator_spans : ∀ c : C.1, ∃ n : ℕ, (generator.1 : Q) ^ n = (c.1 : Q)) :
    2 ≤ orderOf (rhoF (generator.1 : Q)) := by
  classical
  have hne : rhoF (generator.1 : Q) ≠ 1 :=
    hkt_iv62_r_cyclic_generator_rhoF_ne_one
      (Q := Q) (q := q) S L M C K rhoF rhoF_lifts_nonscalar rhoF_compatible generator generator_spans
  have hdvd_card : orderOf (rhoF (generator.1 : Q)) ∣ Nat.card C.1 :=
    hkt_iv62_r_cyclic_generator_rhoF_order_dvd_card
      (Q := Q) (q := q) S L M C K rhoF rhoF_lifts_nonscalar rhoF_compatible generator generator_spans
  have hcard_pos : 0 < Nat.card C.1 := Nat.card_pos
  have hne_zero : orderOf (rhoF (generator.1 : Q)) ≠ 0 := by
    intro hzero
    obtain ⟨k, hk⟩ := hdvd_card
    rw [hzero, zero_mul] at hk
    exact (Nat.ne_of_gt hcard_pos) hk
  have hne_one : orderOf (rhoF (generator.1 : Q)) ≠ 1 := by
    intro horder
    exact hne (orderOf_eq_one_iff.mp horder)
  omega

private theorem hkt_GL2_zmod_scalarExtension_pow_apply
    {q n : ℕ} [Fact q.Prime] {F : Type u} [Field F]
    (τ : ZMod q →+* F)
    (f : (Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q))
    (fF : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F))
    (hfF :
      ∀ v : Fin 2 → ZMod q,
        fF (fun i => τ (v i)) = fun i => τ ((f v) i)) :
    ∀ v : Fin 2 → ZMod q,
      (fF ^ n) (fun i => τ (v i)) = fun i => τ (((f ^ n) v) i) := by
  induction n with
  | zero =>
      intro v
      simp
  | succ n ih =>
      intro v
      rw [pow_succ, pow_succ]
      simp only [LinearEquiv.mul_apply]
      rw [hfF, ih]

private theorem hkt_GL2_zmod_scalarExtension_pow_eq_one_iff
    {q n : ℕ} [Fact q.Prime] {F : Type u} [Field F]
    (τ : ZMod q →+* F) (τ_injective : Function.Injective τ)
    (f : (Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q))
    (fF : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F))
    (hfF :
      ∀ v : Fin 2 → ZMod q,
        fF (fun i => τ (v i)) = fun i => τ ((f v) i)) :
    fF ^ n = 1 ↔ f ^ n = 1 := by
  constructor
  · intro hF
    ext v i
    have hcoord := congrFun
      (hkt_GL2_zmod_scalarExtension_pow_apply
        (q := q) (n := n) τ f fF hfF v) i
    rw [hF] at hcoord
    exact τ_injective hcoord |>.symm
  · intro hf
    let b : Module.Basis (Fin 2) F (Fin 2 → F) := Pi.basisFun F (Fin 2)
    have hlin :
        (fF ^ n).toLinearMap =
          (1 : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)).toLinearMap := by
      apply b.ext
      intro i
      let eZ : Fin 2 → ZMod q := fun j => if j = i then 1 else 0
      let eF : Fin 2 → F := fun j => if j = i then 1 else 0
      have h_embed : (fun j : Fin 2 => τ (eZ j)) = eF := by
        ext j
        by_cases h : j = i <;> simp [eZ, eF, h]
      have h_basis : b i = eF := by
        ext j
        by_cases h : j = i <;> simp [b, eF, Pi.basisFun_apply, Pi.single, h]
      have hvec := hkt_GL2_zmod_scalarExtension_pow_apply
        (q := q) (n := n) τ f fF hfF eZ
      rw [hf] at hvec
      rw [h_embed] at hvec
      rw [h_basis]
      simpa [eF, eZ] using hvec
    apply LinearEquiv.ext
    intro x
    exact LinearMap.congr_fun hlin x

private theorem hkt_linearEquiv_toLinearMap_pow
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : V ≃ₗ[K] V) (n : ℕ) :
    (f ^ n).toLinearMap = f.toLinearMap ^ n := by
  induction n with
  | zero =>
      ext x
      rfl
  | succ n ih =>
      rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

private theorem
    hkt_zmod_irreducible_monic_degree_le_two_dvd_X_pow_sub_one_dvd_X_pow_q_sq_sub_one
    {q m : ℕ} [Fact q.Prime] {R : Polynomial (ZMod q)}
    (hR_monic : R.Monic) (hR_irred : Irreducible R)
    (hR_deg : R.natDegree ≤ 2)
    (hR_dvd_m : R ∣ Polynomial.X ^ m - 1)
    (hcop : Nat.Coprime q m) :
    R ∣ Polynomial.X ^ (q ^ 2 - 1) - 1 := by
  classical
  let : Fact (Irreducible R) := ⟨hR_irred⟩
  have : Module.Finite (ZMod q) (AdjoinRoot R) := hR_monic.finite_adjoinRoot
  have : Finite (AdjoinRoot R) := Module.finite_of_finite (ZMod q)
  let : Fintype (AdjoinRoot R) := Fintype.ofFinite (AdjoinRoot R)
  let α : AdjoinRoot R := AdjoinRoot.root R
  have hcard : Nat.card (AdjoinRoot R) = q ^ R.natDegree := by
    rw [Nat.card_eq_fintype_card]
    rw [Module.card_fintype (AdjoinRoot.powerBasis' hR_monic).basis]
    rw [ZMod.card]
    rw [Fintype.card_fin, AdjoinRoot.powerBasis'_dim]
  have hroot_R : Polynomial.aeval α R = 0 := by
    simp [α, Polynomial.aeval_def]
  have hroot_m : Polynomial.aeval α
      (Polynomial.X ^ m - 1 : Polynomial (ZMod q)) = 0 := by
    exact Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
      (f := algebraMap (ZMod q) (AdjoinRoot R)) (x := α) hR_dvd_m hroot_R
  have hpow_m_sub : α ^ m - 1 = 0 := by
    simpa only [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_one] using hroot_m
  have hpow_m : α ^ m = 1 := sub_eq_zero.mp hpow_m_sub
  have hm_ne_zero : m ≠ 0 := by
    intro hm
    have hnot : ¬ q ∣ m := (Fact.out : q.Prime).coprime_iff_not_dvd.mp hcop
    exact hnot (by rw [hm]; exact dvd_zero q)
  have hα_ne_zero : α ≠ 0 := by
    intro hα
    have : (0 : AdjoinRoot R) ^ m = (1 : AdjoinRoot R) := by
      simpa [hα] using hpow_m
    simp [hm_ne_zero] at this
  have hcardF : Fintype.card (AdjoinRoot R) = q ^ R.natDegree := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hpow_card : α ^ (Fintype.card (AdjoinRoot R) - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one α hα_ne_zero
  have hcard_dvd_target : Fintype.card (AdjoinRoot R) - 1 ∣ q ^ 2 - 1 := by
    have hdeg_pos : 0 < R.natDegree := hR_irred.natDegree_pos
    have hdeg_cases : R.natDegree = 1 ∨ R.natDegree = 2 := by omega
    rcases hdeg_cases with hdeg | hdeg
    · rw [hcardF, hdeg, pow_one]
      exact Nat.sub_one_dvd_pow_sub_one (x := q) (n := 2)
    · rw [hcardF, hdeg]
  have horder_dvd_card : orderOf α ∣ Fintype.card (AdjoinRoot R) - 1 :=
    orderOf_dvd_of_pow_eq_one hpow_card
  have hpow_target : α ^ (q ^ 2 - 1) = 1 := by
    exact (orderOf_dvd_iff_pow_eq_one).mp (horder_dvd_card.trans hcard_dvd_target)
  have htarget_eval : Polynomial.aeval α
      (Polynomial.X ^ (q ^ 2 - 1) - 1 : Polynomial (ZMod q)) = 0 := by
    simpa only [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_one]
      using sub_eq_zero.mpr hpow_target
  have hmin : minpoly (ZMod q) α = R := by
    rw [AdjoinRoot.minpoly_root hR_irred.ne_zero]
    simp [hR_monic.leadingCoeff]
  have hmin_dvd : minpoly (ZMod q) α ∣
      (Polynomial.X ^ (q ^ 2 - 1) - 1 : Polynomial (ZMod q)) := by
    exact (minpoly.dvd_iff (A := ZMod q) (x := α)).mpr htarget_eval
  simpa [hmin] using hmin_dvd

private theorem
    hkt_zmod_squarefree_degree_le_two_dvd_X_pow_sub_one_dvd_X_pow_q_sq_sub_one_source
    {q m : ℕ} [Fact q.Prime] (P : Polynomial (ZMod q))
    (hP_monic : P.Monic)
    (hP_sq : Squarefree P)
    (hP_deg : P.natDegree ≤ 2)
    (hP_dvd_m : P ∣ Polynomial.X ^ m - 1)
    (hcop : Nat.Coprime q m) :
    P ∣ Polynomial.X ^ (q ^ 2 - 1) - 1 := by
  classical
  let T : Polynomial (ZMod q) := Polynomial.X ^ (q ^ 2 - 1) - 1
  have hP0 : P ≠ 0 := hP_monic.ne_zero
  have hn : 0 < q ^ 2 - 1 := by
    have hq_ge_two : 2 ≤ q := (Fact.out : q.Prime).two_le
    have hq_sq_ge : 4 ≤ q ^ 2 := by
      simpa using Nat.pow_le_pow_left hq_ge_two 2
    omega
  have hT0 : T ≠ 0 := by
    dsimp [T]
    simpa using (Polynomial.X_pow_sub_C_ne_zero (R := ZMod q) hn (1 : ZMod q))
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP0 hT0]
  rw [Multiset.le_iff_count]
  intro R
  by_cases hRmem : R ∈ UniqueFactorizationMonoid.normalizedFactors P
  · have hnodup : (UniqueFactorizationMonoid.normalizedFactors P).Nodup :=
      (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP0).mp hP_sq
    have hR_count_left : Multiset.count R (UniqueFactorizationMonoid.normalizedFactors P) ≤ 1 := by
      exact (Multiset.nodup_iff_count_le_one.mp hnodup) R
    have hR_data := (Polynomial.mem_normalizedFactors_iff hP0).mp hRmem
    rcases hR_data with ⟨hR_irred, hR_monic, hR_dvd_P⟩
    have hR_deg : R.natDegree ≤ 2 := by
      have hdeg_le_P : R.natDegree ≤ P.natDegree :=
        Polynomial.natDegree_le_of_dvd hR_dvd_P hP0
      exact hdeg_le_P.trans hP_deg
    have hR_dvd_m : R ∣ Polynomial.X ^ m - 1 := hR_dvd_P.trans hP_dvd_m
    have hR_dvd_T : R ∣ T := by
      dsimp [T]
      exact hkt_zmod_irreducible_monic_degree_le_two_dvd_X_pow_sub_one_dvd_X_pow_q_sq_sub_one
        hR_monic hR_irred hR_deg hR_dvd_m hcop
    have hRmem_T : R ∈ UniqueFactorizationMonoid.normalizedFactors T :=
      (Polynomial.mem_normalizedFactors_iff hT0).mpr ⟨hR_irred, hR_monic, hR_dvd_T⟩
    have hR_count_T_pos : 0 < Multiset.count R (UniqueFactorizationMonoid.normalizedFactors T) :=
      Multiset.count_pos.mpr hRmem_T
    omega
  · simp [Multiset.count_eq_zero_of_notMem hRmem]

private theorem hkt_GL2_zmod_coprime_minpoly_dvd_X_pow_q_sq_sub_one_source
    {q : ℕ} [Fact q.Prime]
    (f : (Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q))
    (hcop : Nat.Coprime q (orderOf f)) :
    minpoly (ZMod q) f.toLinearMap ∣
      Polynomial.X ^ (q ^ 2 - 1) - 1 := by
  classical
  let m := orderOf f
  have hP_dvd_m :
      minpoly (ZMod q) f.toLinearMap ∣
        Polynomial.X ^ m - 1 := by
    have hpow_toLin : (f ^ m).toLinearMap =
        (1 : (Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)).toLinearMap := by
      dsimp [m]
      rw [pow_orderOf_eq_one]
      rfl
    have hpow_lin : f.toLinearMap ^ m = 1 := by
      rw [← hkt_linearEquiv_toLinearMap_pow]
      exact hpow_toLin
    have hzero : Polynomial.aeval f.toLinearMap
        (Polynomial.X ^ m - 1 : Polynomial (ZMod q)) = 0 := by
      simpa only [Polynomial.aeval_sub, Polynomial.aeval_X_pow,
        Polynomial.aeval_one] using sub_eq_zero.mpr hpow_lin
    exact (minpoly.dvd_iff (A := ZMod q) (x := f.toLinearMap)).mpr hzero
  have hm_nonzero : (m : ZMod q) ≠ 0 := by
    intro hm
    have hnot : ¬ q ∣ m := (Fact.out : q.Prime).coprime_iff_not_dvd.mp hcop
    exact hnot ((ZMod.natCast_eq_zero_iff m q).mp hm)
  have hP_sq : Squarefree (minpoly (ZMod q) f.toLinearMap) := by
    have hsep_X :
        (Polynomial.X ^ m - 1 : Polynomial (ZMod q)).Separable := by
      rw [Polynomial.X_pow_sub_one_separable_iff]
      exact hm_nonzero
    exact (Polynomial.Separable.of_dvd hsep_X hP_dvd_m).squarefree
  have hP_deg : (minpoly (ZMod q) f.toLinearMap).natDegree ≤ 2 := by
    have hle :
        (minpoly (ZMod q) f.toLinearMap).natDegree ≤
          f.toLinearMap.charpoly.natDegree :=
      Polynomial.natDegree_le_of_dvd
        (LinearMap.minpoly_dvd_charpoly f.toLinearMap)
        (LinearMap.charpoly_monic f.toLinearMap).ne_zero
    have hchar :
        f.toLinearMap.charpoly.natDegree =
          Module.finrank (ZMod q) (Fin 2 → ZMod q) := by
      exact LinearMap.charpoly_natDegree f.toLinearMap
    have hfin : Module.finrank (ZMod q) (Fin 2 → ZMod q) = 2 := by
      simp
    omega
  exact
    hkt_zmod_squarefree_degree_le_two_dvd_X_pow_sub_one_dvd_X_pow_q_sq_sub_one_source
      (q := q) (m := m) (minpoly (ZMod q) f.toLinearMap)
      (minpoly.monic (LinearMap.isIntegral f.toLinearMap)) hP_sq hP_deg hP_dvd_m hcop

private theorem hkt_GL2_zmod_coprime_order_dvd_q_sq_sub_one_source
    {q : ℕ} [Fact q.Prime]
    (f : (Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q))
    (hcop : Nat.Coprime q (orderOf f)) :
    orderOf f ∣ q ^ 2 - 1 := by
  classical
  have hmin :
      minpoly (ZMod q) f.toLinearMap ∣
        Polynomial.X ^ (q ^ 2 - 1) - 1 :=
    hkt_GL2_zmod_coprime_minpoly_dvd_X_pow_q_sq_sub_one_source
      (q := q) f hcop
  have hzero : Polynomial.aeval f.toLinearMap
      (Polynomial.X ^ (q ^ 2 - 1) - 1 : Polynomial (ZMod q)) = 0 := by
    exact (minpoly.dvd_iff (A := ZMod q) (x := f.toLinearMap)).mp hmin
  have hpow_sub : f.toLinearMap ^ (q ^ 2 - 1) - 1 = 0 := by
    simpa only [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_one] using hzero
  have hpow_lin : f.toLinearMap ^ (q ^ 2 - 1) = 1 := sub_eq_zero.mp hpow_sub
  have hpow_toLin : (f ^ (q ^ 2 - 1)).toLinearMap = 1 := by
    rw [hkt_linearEquiv_toLinearMap_pow]
    exact hpow_lin
  have hpow : f ^ (q ^ 2 - 1) = 1 := by
    apply LinearEquiv.ext
    intro x
    exact LinearMap.congr_fun hpow_toLin x
  exact orderOf_dvd_of_pow_eq_one hpow

private theorem hkt_GL2_zmod_scalarExtension_coprime_order_dvd_q_sq_sub_one_source
    {q : ℕ} [Fact q.Prime] {F : Type u} [Field F] [Finite F]
    (τ : ZMod q →+* F) (τ_injective : Function.Injective τ)
    (_hcardF : Nat.card F = q ^ 2)
    (f : (Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q))
    (fF : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F))
    (hfF :
      ∀ v : Fin 2 → ZMod q,
        fF (fun i => τ (v i)) = fun i => τ ((f v) i))
    (hcop : Nat.Coprime q (orderOf fF)) :
    orderOf fF ∣ q ^ 2 - 1 := by
  classical
  have horder : orderOf fF = orderOf f := by
    exact (orderOf_eq_orderOf_iff (x := fF) (y := f)).2
      (fun n =>
        hkt_GL2_zmod_scalarExtension_pow_eq_one_iff
          (q := q) (n := n) τ τ_injective f fF hfF)
  have hcop_f : Nat.Coprime q (orderOf f) := by
    simpa [horder] using hcop
  simpa [horder] using
    hkt_GL2_zmod_coprime_order_dvd_q_sq_sub_one_source
      (q := q) f hcop_f

private theorem hkt_exists_isPrimitiveRoot_of_dvd_card_sub_one
    {F : Type u} [Field F] [Finite F] {h : ℕ}
    (hh : 2 ≤ h) (hdvd : h ∣ Nat.card F - 1) :
    ∃ ε : F, IsPrimitiveRoot ε h := by
  classical
  have _ := hh
  let : IsCyclic Fˣ := inferInstance
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  let u : Fˣ := ζ ^ (Nat.card Fˣ / h)
  refine ⟨(u : F), ?_⟩
  rw [IsPrimitiveRoot.iff_orderOf, orderOf_units]
  have hcard_units : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units (α := F)
  have hdvd_units : h ∣ Nat.card Fˣ := by
    simpa [hcard_units] using hdvd
  have hζ_ne_zero : orderOf ζ ≠ 0 := by
    rw [hζ]
    exact Nat.ne_of_gt (Nat.card_pos (α := Fˣ))
  have hdvd_order : h ∣ orderOf ζ := by
    rwa [hζ]
  simpa [u, hζ] using
    (orderOf_pow_orderOf_div (x := ζ) hζ_ne_zero hdvd_order)

private theorem hkt_iv62_r_cyclic_generator_rhoF_primitiveRoot_of_order_dvd_q_sq_sub_one
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))))
    (rhoF_lifts_nonscalar :
      letI : Field K.1 := K.2.1
      ∃ c : C.1,
      (∀ μ : ZMod q,
        (M.2.1 (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) ∧
      (∀ μ : K.1,
        (rhoF (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End K.1 (Fin 2 → K.1))))
    (rhoF_compatible :
      ∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => K.2.2.2.1 (v i)) =
          fun i => K.2.2.2.1 ((M.2.1 g v) i))
    (generator : C.1)
    (generator_spans : ∀ c : C.1, ∃ n : ℕ, (generator.1 : Q) ^ n = (c.1 : Q))
    (hdvd : orderOf (rhoF (generator.1 : Q)) ∣ q ^ 2 - 1) :
    letI : Field K.1 := K.2.1
    ∃ ε : K.1, IsPrimitiveRoot ε (orderOf (rhoF (generator.1 : Q))) := by
  classical
  let : Field K.1 := K.2.1
  let : Finite K.1 := K.2.2.1.1
  have horder_ge_two : 2 ≤ orderOf (rhoF (generator.1 : Q)) :=
    hkt_iv62_r_cyclic_generator_rhoF_order_ge_two
      (Q := Q) (q := q) S L M C K rhoF rhoF_lifts_nonscalar rhoF_compatible generator generator_spans
  have hdvd_card : orderOf (rhoF (generator.1 : Q)) ∣ Nat.card K.1 - 1 := by
    simpa [K.2.2.1.2] using hdvd
  exact hkt_exists_isPrimitiveRoot_of_dvd_card_sub_one
    (F := K.1) horder_ge_two hdvd_card

private theorem hkt_iv62_r_cyclic_generator_rhoF_internal_eigenspace_decomposition
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))))
    (rhoF_lifts_nonscalar :
      letI : Field K.1 := K.2.1
      ∃ c : C.1,
      (∀ μ : ZMod q,
        (M.2.1 (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) ∧
      (∀ μ : K.1,
        (rhoF (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End K.1 (Fin 2 → K.1))))
    (rhoF_compatible :
      ∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => K.2.2.2.1 (v i)) =
          fun i => K.2.2.2.1 ((M.2.1 g v) i))
    (generator : C.1)
    (generator_spans : ∀ c : C.1, ∃ n : ℕ, (generator.1 : Q) ^ n = (c.1 : Q))
    (ε : K.1)
    (hε :
      letI : Field K.1 := K.2.1
      IsPrimitiveRoot ε (orderOf (rhoF (generator.1 : Q)))) :
    letI : Field K.1 := K.2.1
    DirectSum.IsInternal <| fun i : Fin (orderOf (rhoF (generator.1 : Q))) =>
      Module.End.eigenspace (rhoF (generator.1 : Q)).toLinearMap (ε ^ (i.1 : ℤ)) := by
  classical
  let : Field K.1 := K.2.1
  let g := rhoF (generator.1 : Q)
  have hg : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have hh : orderOf g ≥ 2 :=
    hkt_iv62_r_cyclic_generator_rhoF_order_ge_two
      (Q := Q) (q := q) S L M C K rhoF rhoF_lifts_nonscalar rhoF_compatible generator generator_spans
  simpa [g] using
    (proposition_2_4_a (g := g) (h := orderOf g) hg hh hε)

private theorem hkt_iv62_r_cyclic_generator_rhoF_order_dvd_q_sq_sub_one_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))))
    (rhoF_lifts_nonscalar :
      letI : Field K.1 := K.2.1
      ∃ c : C.1,
      (∀ μ : ZMod q,
        (M.2.1 (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) ∧
      (∀ μ : K.1,
        (rhoF (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End K.1 (Fin 2 → K.1))))
    (rhoF_compatible :
      ∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => K.2.2.2.1 (v i)) =
          fun i => K.2.2.2.1 ((M.2.1 g v) i))
    (generator : C.1)
    (generator_spans : ∀ c : C.1, ∃ n : ℕ, (generator.1 : Q) ^ n = (c.1 : Q)) :
    orderOf (rhoF (generator.1 : Q)) ∣ q ^ 2 - 1 := by
  classical
  let : Field K.1 := K.2.1
  let : Finite K.1 := K.2.2.1.1
  exact hkt_GL2_zmod_scalarExtension_coprime_order_dvd_q_sq_sub_one_source
    (q := q) (F := K.1) K.2.2.2.1 K.2.2.2.2 K.2.2.1.2
    (M.2.1 (generator.1 : Q)) (rhoF (generator.1 : Q))
    (rhoF_compatible (generator.1 : Q))
    (hkt_iv62_r_cyclic_generator_rhoF_order_coprime
      (Q := Q) (q := q) S L M C K rhoF rhoF_lifts_nonscalar rhoF_compatible generator generator_spans)

private theorem hkt_iv62_r_cyclic_generator_rhoF_primitiveRoot_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))))
    (rhoF_lifts_nonscalar :
      letI : Field K.1 := K.2.1
      ∃ c : C.1,
      (∀ μ : ZMod q,
        (M.2.1 (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) ∧
      (∀ μ : K.1,
        (rhoF (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End K.1 (Fin 2 → K.1))))
    (rhoF_compatible :
      ∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => K.2.2.2.1 (v i)) =
          fun i => K.2.2.2.1 ((M.2.1 g v) i))
    (generator : C.1)
    (generator_spans : ∀ c : C.1, ∃ n : ℕ, (generator.1 : Q) ^ n = (c.1 : Q)) :
    letI : Field K.1 := K.2.1
    ∃ ε : K.1, IsPrimitiveRoot ε (orderOf (rhoF (generator.1 : Q))) := by
  classical
  let : Field K.1 := K.2.1
  exact hkt_iv62_r_cyclic_generator_rhoF_primitiveRoot_of_order_dvd_q_sq_sub_one
    (Q := Q) (q := q) S L M C K rhoF rhoF_lifts_nonscalar rhoF_compatible generator generator_spans
    (hkt_iv62_r_cyclic_generator_rhoF_order_dvd_q_sq_sub_one_source
      (Q := Q) (q := q) S L M C K rhoF rhoF_lifts_nonscalar rhoF_compatible generator generator_spans)

private theorem hkt_iv62_r_generator_eigenlines_from_internal_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))))
    (rhoF_lifts_nonscalar :
      letI : Field K.1 := K.2.1
      ∃ c : C.1,
      (∀ μ : ZMod q,
        (M.2.1 (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) ∧
      (∀ μ : K.1,
        (rhoF (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End K.1 (Fin 2 → K.1))))
    (rhoF_compatible :
      ∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => K.2.2.2.1 (v i)) =
          fun i => K.2.2.2.1 ((M.2.1 g v) i))
    (generator : C.1)
    (generator_spans : ∀ c : C.1, ∃ n : ℕ, (generator.1 : Q) ^ n = (c.1 : Q))
    (ε : K.1)
    (hε :
      letI : Field K.1 := K.2.1
      IsPrimitiveRoot ε (orderOf (rhoF (generator.1 : Q))))
    (_hdecomp :
      letI : Field K.1 := K.2.1
      DirectSum.IsInternal <| fun i : Fin (orderOf (rhoF (generator.1 : Q))) =>
        Module.End.eigenspace (rhoF (generator.1 : Q)).toLinearMap (ε ^ (i.1 : ℤ))) :
    ∃ eigenvalue_gen : Fin 2 → K.1,
    ∃ eigenvector : Fin 2 → (Fin 2 → K.1),
      (letI : Field K.1 := K.2.1
       ∀ i : Fin 2, eigenvector i ≠ 0) ∧
      eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
      (letI : Field K.1 := K.2.1
       LinearIndependent K.1 eigenvector) ∧
      (letI : Field K.1 := K.2.1
       ∀ i : Fin 2,
        rhoF (generator.1 : Q) (eigenvector i) =
          eigenvalue_gen i • eigenvector i) := by
  classical
  have _ := rhoF_lifts_nonscalar
  have _ := rhoF_compatible
  have _ := generator_spans
  have _ := hε
  let : Field K.1 := K.2.1
  let g := rhoF (generator.1 : Q)
  let A : Fin (orderOf g) → Submodule K.1 (Fin 2 → K.1) :=
    fun i => Module.End.eigenspace g.toLinearMap (ε ^ (i.1 : ℤ))
  let B : Module.Basis (Σ i, Fin (Module.finrank K.1 (A i))) K.1 (Fin 2 → K.1) :=
    _hdecomp.collectedBasis (fun i => Module.finBasis K.1 (A i))
  have hfinV : Module.finrank K.1 (Fin 2 → K.1) = 2 := by
    simp
  have hcard : Fintype.card (Σ i, Fin (Module.finrank K.1 (A i))) = 2 := by
    exact (Module.finrank_eq_card_basis B).symm.trans hfinV
  let e : (Σ i, Fin (Module.finrank K.1 (A i))) ≃ Fin 2 :=
    Fintype.equivFinOfCardEq hcard
  let B2 : Module.Basis (Fin 2) K.1 (Fin 2 → K.1) := B.reindex e
  refine ⟨fun i => ε ^ (((e.symm i).1.1 : ℤ)), B2, ?_, ?_, B2.linearIndependent, ?_⟩
  · intro i
    exact LinearIndependent.ne_zero i B2.linearIndependent
  · intro hsame
    have hidx : (0 : Fin 2) = 1 :=
      LinearIndependent.injective B2.linearIndependent hsame
    exact (by decide : (0 : Fin 2) ≠ 1) hidx
  · intro i
    have hmem : B2 i ∈ A ((e.symm i).1) := by
      change (B.reindex e) i ∈ A ((e.symm i).1)
      rw [Module.Basis.reindex_apply]
      exact _hdecomp.collectedBasis_mem (fun i => Module.finBasis K.1 (A i)) (e.symm i)
    simpa [g, A] using (Module.End.mem_eigenspace_iff.mp hmem)

private theorem hkt_iv62_r_cyclic_generator_eigenline_relation
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))))
    (rhoF_lifts_nonscalar :
      letI : Field K.1 := K.2.1
      ∃ c : C.1,
      (∀ μ : ZMod q,
        (M.2.1 (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) ∧
      (∀ μ : K.1,
        (rhoF (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End K.1 (Fin 2 → K.1))))
    (rhoF_compatible :
      ∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => K.2.2.2.1 (v i)) =
          fun i => K.2.2.2.1 ((M.2.1 g v) i))
    (generator : C.1)
    (generator_spans : ∀ c : C.1, ∃ n : ℕ, (generator.1 : Q) ^ n = (c.1 : Q))
    (eigenvalue_gen : Fin 2 → K.1)
    (eigenvector : Fin 2 → (Fin 2 → K.1))
    (heigenvectors_nonzero :
      letI : Field K.1 := K.2.1
      ∀ i : Fin 2, eigenvector i ≠ 0)
    (hgenerator_eigenline_relation :
      letI : Field K.1 := K.2.1
      ∀ i : Fin 2,
        rhoF (generator.1 : Q) (eigenvector i) =
          eigenvalue_gen i • eigenvector i) :
    (letI : Field K.1 := K.2.1;
      (∀ i : Fin 2, eigenvector i ≠ 0) ∧
        ∀ i : Fin 2, ∀ c : C.1,
          rhoF (c.1 : Q) (eigenvector i) =
            (eigenvalue_gen i ^
              Classical.choose (generator_spans c)) • eigenvector i) := by
  classical
  have _ := rhoF_lifts_nonscalar
  have _ := rhoF_compatible
  let : Field K.1 := K.2.1
  constructor
  · exact heigenvectors_nonzero
  · intro i c
    let n : ℕ :=
      Classical.choose (generator_spans c)
    have hn : (generator.1 : Q) ^ n = (c.1 : Q) :=
      Classical.choose_spec (generator_spans c)
    have hc_eq : (c.1 : Q) = (generator.1 : Q) ^ n := by
      exact hn.symm
    have hpow :=
      hkt_linearEquiv_pow_apply_eigenvector
        (rhoF (generator.1 : Q))
        (hgenerator_eigenline_relation i) n
    calc
      rhoF (c.1 : Q) (eigenvector i) =
          rhoF ((generator.1 : Q) ^ n) (eigenvector i) := by
        rw [hc_eq]
      _ = (rhoF (generator.1 : Q) ^ n) (eigenvector i) := by
        rw [map_pow]
      _ = eigenvalue_gen i ^ n • eigenvector i := hpow
      _ = (eigenvalue_gen i ^
            Classical.choose (generator_spans c)) • eigenvector i := by
        rfl

private theorem hkt_iv62_r_coprime_action_generator_eigenlines_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))))
    (rhoF_lifts_nonscalar :
      letI : Field K.1 := K.2.1
      ∃ c : C.1,
      (∀ μ : ZMod q,
        (M.2.1 (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) ∧
      (∀ μ : K.1,
        (rhoF (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End K.1 (Fin 2 → K.1))))
    (rhoF_compatible :
      ∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => K.2.2.2.1 (v i)) =
          fun i => K.2.2.2.1 ((M.2.1 g v) i))
    (generator : C.1)
    (generator_spans : ∀ c : C.1, ∃ n : ℕ, (generator.1 : Q) ^ n = (c.1 : Q)) :
    ∃ eigenvalue_gen : Fin 2 → K.1,
    ∃ eigenvector : Fin 2 → (Fin 2 → K.1),
      (letI : Field K.1 := K.2.1
       ∀ i : Fin 2, eigenvector i ≠ 0) ∧
      eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
      (letI : Field K.1 := K.2.1
       LinearIndependent K.1 eigenvector) ∧
      (letI : Field K.1 := K.2.1
       ∀ i : Fin 2,
        rhoF (generator.1 : Q) (eigenvector i) =
          eigenvalue_gen i • eigenvector i) := by
  classical
  have _ := hq2
  let : Field K.1 := K.2.1
  obtain ⟨ε, hε⟩ :=
    hkt_iv62_r_cyclic_generator_rhoF_primitiveRoot_source
      (Q := Q) (q := q) S L M C K rhoF rhoF_lifts_nonscalar rhoF_compatible generator generator_spans
  have hdecomp :=
    hkt_iv62_r_cyclic_generator_rhoF_internal_eigenspace_decomposition
      (Q := Q) (q := q) S L M C K rhoF rhoF_lifts_nonscalar rhoF_compatible generator generator_spans ε hε
  exact hkt_iv62_r_generator_eigenlines_from_internal_source
    (Q := Q) (q := q) S L M C K rhoF rhoF_lifts_nonscalar rhoF_compatible generator generator_spans ε hε hdecomp


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\Lift.lean`. -/

private theorem hkt_GL2_zmod_scalarExtension_action_nonscalar
    {Q : Type u} [Group Q] {q : ℕ} [Fact q.Prime] {F : Type v} [Field F]
    (τ : ZMod q →+* F)
    (rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)))
    (τ_injective : Function.Injective τ) :
    ∃ rhoF : Q →* ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F)),
      (∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => τ (v i)) = fun i => τ ((rho g v) i)) ∧
        (∀ g : Q,
          (∀ μ : ZMod q,
            (rho g).toLinearMap ≠
              μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) →
          ∀ μ : F,
            (rhoF g).toLinearMap ≠ μ • (1 : Module.End F (Fin 2 → F))) := by
  classical
  let rhoF : Q →* ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) := by
    refine
      { toFun := fun g =>
          let A : Matrix (Fin 2) (Fin 2) F :=
            (LinearMap.toMatrix' (rho g).toLinearMap).map τ
          let Ainv : Matrix (Fin 2) (Fin 2) F :=
            (LinearMap.toMatrix' (rho g⁻¹).toLinearMap).map τ
          Matrix.toLin'OfInv (M := Ainv) (M' := A) ?_ ?_
        map_one' := ?_
        map_mul' := ?_ }
    · have hlin : (rho g⁻¹).toLinearMap * (rho g).toLinearMap = 1 := by
        have hlinEquiv : rho g⁻¹ * rho g = 1 := by
          simp
        ext v i
        have hv := congrArg
          (fun e : (Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q) => e v) hlinEquiv
        simp [Module.End.mul_eq_comp] at hv ⊢
      rw [← Matrix.map_mul, ← LinearMap.toMatrix'_mul, hlin, LinearMap.toMatrix'_one,
        Matrix.map_one]
      all_goals
        first
        | exact map_zero τ
        | exact map_one τ
    · have hlin : (rho g).toLinearMap * (rho g⁻¹).toLinearMap = 1 := by
        have hlinEquiv : rho g * rho g⁻¹ = 1 := by
          simp
        ext v i
        have hv := congrArg
          (fun e : (Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q) => e v) hlinEquiv
        simp [Module.End.mul_eq_comp] at hv ⊢
      rw [← Matrix.map_mul, ← LinearMap.toMatrix'_mul, hlin, LinearMap.toMatrix'_one,
        Matrix.map_one]
      all_goals
        first
        | exact map_zero τ
        | exact map_one τ
    · apply LinearEquiv.toLinearMap_injective
      ext v i
      simp [Matrix.toLin'OfInv]
    · intro g h
      ext v i
      simp [Matrix.toLin'OfInv, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        LinearMap.toMatrix'_mul, Matrix.map_mul]
  have rhoF_apply :
      ∀ (g : Q) (v : Fin 2 → ZMod q),
        rhoF g (fun i => τ (v i)) = fun i => τ ((rho g v) i) := by
    intro g v
    ext i
    simp [rhoF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    simp_rw [← map_mul]
    rw [← map_add]
    apply congrArg τ
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      congrArg (fun w : Fin 2 → ZMod q => w i)
        (LinearMap.toMatrix'_mulVec (rho g).toLinearMap v)
  have rhoF_nonscalar :
      ∀ g : Q,
        (∀ μ : ZMod q,
          (rho g).toLinearMap ≠
            μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) →
        ∀ μ : F,
          (rhoF g).toLinearMap ≠ μ • (1 : Module.End F (Fin 2 → F)) := by
    intro g h μ hg
    apply h (LinearMap.toMatrix' (rho g).toLinearMap 0 0)
    let A := LinearMap.toMatrix' (rho g).toLinearMap
    apply LinearMap.toMatrix'.injective
    ext i j
    by_cases hij : i = j
    · subst j
      have h00 : τ (A 0 0) = μ := by
        have hentry := congrArg
          (fun (T : Module.End F (Fin 2 → F)) => LinearMap.toMatrix' T 0 0) hg
        simpa [rhoF, Matrix.toLin'OfInv, A] using hentry
      have hii : τ (A i i) = μ := by
        have hentry := congrArg
          (fun (T : Module.End F (Fin 2 → F)) => LinearMap.toMatrix' T i i) hg
        simpa [rhoF, Matrix.toLin'OfInv, A] using hentry
      apply τ_injective
      simpa [A] using hii.trans h00.symm
    · have hij0 : A i j = 0 := by
        apply τ_injective
        have hentry := congrArg
          (fun (T : Module.End F (Fin 2 → F)) => LinearMap.toMatrix' T i j) hg
        simpa [rhoF, Matrix.toLin'OfInv, A, hij] using hentry
      simp [A, hij, hij0]
  exact ⟨rhoF, rhoF_apply, rhoF_nonscalar⟩

private theorem hkt_subgroup_cyclic_generator_spans_in_ambient
    {Q : Type u} [Group Q] [Finite Q] (C : Subgroup Q) [IsCyclic C] :
    ∃ generator : C, ∀ c : C, ∃ n : ℕ, (generator.1 : Q) ^ n = (c.1 : Q) := by
  classical
  obtain ⟨generator, generator_spans_powers⟩ :=
    IsCyclic.exists_monoid_generator (α := C)
  refine ⟨generator, ?_⟩
  intro c
  obtain ⟨n, hn⟩ :=
    (Submonoid.mem_powers_iff c generator).mp (generator_spans_powers c)
  exact ⟨n, congrArg (fun y : C => (y : Q)) hn⟩
private theorem hkt_iv62_r_package_eigenspaces_from_generator
    {Q : Type u} [Group Q] {F : Type v} [Field F]
    {C : Subgroup Q}
    (rhoF : Q →* ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F)))
    (compatible : Prop) (hcompatible : compatible)
    (generator : C)
    (generator_spans : ∀ c : C, ∃ n : ℕ, (generator.1 : Q) ^ n = (c.1 : Q))
    (eigenvalue_gen : Fin 2 → F)
    (eigenvector : Fin 2 → (Fin 2 → F))
    (heigenvectors_distinct : eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2))
    (heigenvectors_linearIndependent : LinearIndependent F eigenvector)
    (heigenvectors_all_raw :
      (∀ i : Fin 2, eigenvector i ≠ 0) ∧
        ∀ i : Fin 2, ∀ c : C,
          rhoF (c.1 : Q) (eigenvector i) =
            (eigenvalue_gen i ^
              Classical.choose (generator_spans c)) • eigenvector i) :
    Nonempty (Σ eigenvalue : Fin 2 → C → F,
      { eigenvector : Fin 2 → (Fin 2 → F) //
        compatible ∧
          eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
            LinearIndependent F eigenvector ∧
              (∀ i : Fin 2, eigenvector i ≠ 0) ∧
                ∀ i : Fin 2, ∀ c : C,
                  rhoF (c.1 : Q) (eigenvector i) =
                    eigenvalue i c • eigenvector i }) := by
  classical
  let eigenvalue : Fin 2 → C → F :=
    fun i c => eigenvalue_gen i ^ Classical.choose (generator_spans c)
  refine Nonempty.intro (Sigma.mk eigenvalue ?_)
  refine ⟨eigenvector, hcompatible, heigenvectors_distinct,
    heigenvectors_linearIndependent, ?_⟩
  simpa [eigenvalue] using heigenvectors_all_raw

set_option maxHeartbeats 800000 in
private theorem hkt_iv62_r_eigenspaces_from_lifted_action
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))))
    (hrhoF_lifts_nonscalar :
      letI : Field K.1 := K.2.1
      ∃ c : C.1,
        (∀ μ : ZMod q,
          (M.2.1 (c.1 : Q)).toLinearMap ≠
            μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) ∧
          (∀ μ : K.1,
            (rhoF (c.1 : Q)).toLinearMap ≠
              μ • (1 : Module.End K.1 (Fin 2 → K.1))))
    (hrhoF_compatible :
      ∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => K.2.2.2.1 (v i)) =
          fun i => K.2.2.2.1 ((M.2.1 g v) i)) :
    Nonempty (Σ eigenvalue : Fin 2 → C.1 → K.1,
      { eigenvector : Fin 2 → (Fin 2 → K.1) //
        (∀ g : Q, ∀ v : Fin 2 → ZMod q,
          rhoF g (fun i => K.2.2.2.1 (v i)) =
            fun i => K.2.2.2.1 ((M.2.1 g v) i)) ∧
          eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
            (letI : Field K.1 := K.2.1;
              LinearIndependent K.1 eigenvector) ∧
              (letI : Field K.1 := K.2.1;
                (∀ i : Fin 2, eigenvector i ≠ 0) ∧
                  ∀ i : Fin 2, ∀ c : C.1,
                    rhoF (c.1 : Q) (eigenvector i) =
                      eigenvalue i c • eigenvector i) }) := by
  classical
  let : Field K.1 := K.2.1
  let : IsCyclic C.1 := C.2.1
  obtain ⟨generator, generator_spans⟩ :=
    hkt_subgroup_cyclic_generator_spans_in_ambient (Q := Q) C.1
  obtain ⟨eigenvalue_gen, eigenvector, heigenvectors_nonzero,
      heigenvectors_distinct, heigenvectors_linearIndependent,
      hgenerator_eigenline_relation⟩ :=
    hkt_iv62_r_coprime_action_generator_eigenlines_source
      (Q := Q) (q := q) hq2 S L M C K rhoF
      hrhoF_lifts_nonscalar hrhoF_compatible generator generator_spans
  have heigenvectors_all_raw :
      (let : Field K.1 := K.2.1;
        (∀ i : Fin 2, eigenvector i ≠ 0) ∧
          ∀ i : Fin 2, ∀ c : C.1,
            rhoF (c.1 : Q) (eigenvector i) =
              (eigenvalue_gen i ^
                Classical.choose (generator_spans c)) • eigenvector i) := by
    exact hkt_iv62_r_cyclic_generator_eigenline_relation
      (Q := Q) (q := q) S L M C K rhoF hrhoF_lifts_nonscalar
      hrhoF_compatible generator generator_spans eigenvalue_gen eigenvector
      heigenvectors_nonzero hgenerator_eigenline_relation
  exact hkt_iv62_r_package_eigenspaces_from_generator
    (Q := Q) (F := K.1) (C := C.1) rhoF
    (∀ g : Q, ∀ v : Fin 2 → ZMod q,
      rhoF g (fun i => K.2.2.2.1 (v i)) =
        fun i => K.2.2.2.1 ((M.2.1 g v) i))
    hrhoF_compatible generator generator_spans eigenvalue_gen eigenvector
    heigenvectors_distinct heigenvectors_linearIndependent heigenvectors_all_raw

set_option maxHeartbeats 800000 in
private theorem hkt_iv62_r_eigenspaces_exist_over_quadratic_split
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF }))) :
    Nonempty (Σ rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))),
      Σ eigenvalue : Fin 2 → C.1 → K.1,
        { eigenvector : Fin 2 → (Fin 2 → K.1) //
          (∀ g : Q, ∀ v : Fin 2 → ZMod q,
            rhoF g (fun i => K.2.2.2.1 (v i)) =
              fun i => K.2.2.2.1 ((M.2.1 g v) i)) ∧
            eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
              (letI : Field K.1 := K.2.1;
                LinearIndependent K.1 eigenvector) ∧
                (let : Field K.1 := K.2.1; (∀ i : Fin 2, eigenvector i ≠ 0) ∧ ∀ i : Fin 2, ∀ c : C.1, rhoF (c.1 : Q) (eigenvector i) = eigenvalue i c • eigenvector i) }) := by
  classical
  let : Field K.1 := K.2.1
  let tau : ZMod q →+* K.1 := K.2.2.2.1
  let rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) := M.2.1
  obtain ⟨rhoF, hrhoF_compatible_raw, hrhoF_nonscalar_raw⟩ :=
    hkt_GL2_zmod_scalarExtension_action_nonscalar
      (Q := Q) (q := q) (F := K.1) tau rho K.2.2.2.2
  have hrhoF_compatible :
      ∀ g : Q, ∀ v : Fin 2 → ZMod q,
        rhoF g (fun i => K.2.2.2.1 (v i)) =
          fun i => K.2.2.2.1 ((M.2.1 g v) i) := by
    intro g v
    simpa [tau, rho] using hrhoF_compatible_raw g v
  have hrhoF_lifts_nonscalar :
      ∃ c : C.1,
        (∀ μ : ZMod q,
          (M.2.1 (c.1 : Q)).toLinearMap ≠
            μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) ∧
          (∀ μ : K.1,
            (rhoF (c.1 : Q)).toLinearMap ≠
              μ • (1 : Module.End K.1 (Fin 2 → K.1))) := by
    obtain ⟨c, hc⟩ := C.2.2.2.2
    exact ⟨c, hc, by
      intro μ
      exact hrhoF_nonscalar_raw (c.1 : Q) (by simpa [rho] using hc) μ⟩
  obtain ⟨eigenspaces⟩ := hkt_iv62_r_eigenspaces_from_lifted_action
    (Q := Q) (q := q) hq2 S L M C K rhoF
    hrhoF_lifts_nonscalar hrhoF_compatible
  exact Nonempty.intro (Sigma.mk rhoF eigenspaces)
private theorem hkt_finiteField_scalar_q_power_eq_one
    {q k : ℕ} [Fact q.Prime]
    {F : Type*} [Field F] [Finite F]
    (hcard : Nat.card F = q ^ 2) {μ : F} (hμ : μ ≠ 0)
    (hpow : μ ^ (q ^ k) = 1) : μ = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  let u : Fˣ := Units.mk0 μ hμ
  have huq : u ^ (q ^ k) = 1 := by
    ext
    simpa [u] using hpow
  have hcardF : Fintype.card F = q ^ 2 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hμcard : μ ^ (q ^ 2 - 1) = 1 := by
    simpa [hcardF] using FiniteField.pow_card_sub_one_eq_one μ hμ
  have hucard : u ^ (q ^ 2 - 1) = 1 := by
    ext
    simpa [u] using hμcard
  have hq2pos : 0 < q ^ 2 := pow_pos (Fact.out : q.Prime).pos 2
  have hq2cop : Nat.Coprime (q ^ 2) (q ^ 2 - 1) := by
    have hle : 1 ≤ q ^ 2 := Nat.succ_le_of_lt hq2pos
    exact (Nat.coprime_self_sub_right (m := 1) (n := q ^ 2) hle).mpr
      (Nat.coprime_one_right (q ^ 2))
  have hqcop : Nat.Coprime q (q ^ 2 - 1) :=
    Nat.Coprime.of_dvd_left (dvd_pow_self q (by norm_num : (2 : ℕ) ≠ 0)) hq2cop
  have hcop : Nat.Coprime (q ^ k) (q ^ 2 - 1) := hqcop.pow_left k
  have hu : u = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨huq, hucard⟩
  exact Units.ext_iff.mp hu

private theorem hkt_iv62_r_sylow_scalar_eigenvalue_eq_one
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (_hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (B0 : Σ rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))),
      Σ eigenvalue : Fin 2 → C.1 → K.1,
        { eigenvector : Fin 2 → (Fin 2 → K.1) //
          (∀ g : Q, ∀ v : Fin 2 → ZMod q,
            rhoF g (fun i => K.2.2.2.1 (v i)) =
              fun i => K.2.2.2.1 ((M.2.1 g v) i)) ∧
            eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
              (letI : Field K.1 := K.2.1;
                LinearIndependent K.1 eigenvector) ∧
                (letI : Field K.1 := K.2.1; (∀ i : Fin 2, eigenvector i ≠ 0) ∧ ∀ i : Fin 2, ∀ c : C.1, rhoF (c.1 : Q) (eigenvector i) = eigenvalue i c • eigenvector i) })
    (a : L.1) (i : Fin 2) :
    letI : Field K.1 := K.2.1
    ∀ {μ : K.1}, μ ≠ 0 →
      B0.1 (a : Q) (B0.2.2.1 i) = μ • B0.2.2.1 i →
      μ = 1 := by
  classical
  let : Field K.1 := K.2.1
  let : Finite K.1 := K.2.2.1.1
  let rhoF := B0.1
  let eigenvector := B0.2.2.1
  have heigenvector_nonzero : ∀ i : Fin 2, eigenvector i ≠ 0 := B0.2.2.2.2.2.2.1
  intro μ hμ hline
  have hvne : eigenvector i ≠ 0 := heigenvector_nonzero i
  have haS : (a : Q) ∈ (S : Subgroup Q) := L.2.2.1 a.property
  obtain ⟨k, hk⟩ :=
    (IsPGroup.iff_orderOf (p := q) (G := (S : Subgroup Q))).1 S.isPGroup'
      (⟨(a : Q), haS⟩ : (S : Subgroup Q))
  have horder : orderOf (a : Q) = q ^ k := by
    simpa [Subgroup.orderOf_coe] using hk
  have hpow_rho_order : (rhoF (a : Q)) ^ orderOf (a : Q) = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hpow_rho : (rhoF (a : Q)) ^ (q ^ k) = 1 := by
    rw [← horder]
    exact hpow_rho_order
  have happly :=
    hkt_linearEquiv_pow_apply_eigenvector
      (rhoF (a : Q)) hline (q ^ k)
  have hfixed : ((rhoF (a : Q)) ^ (q ^ k)) (eigenvector i) =
      eigenvector i := by
    rw [hpow_rho]
    simp
  have hscalar_smul : (μ ^ (q ^ k)) • eigenvector i =
      (1 : K.1) • eigenvector i := by
    simpa [rhoF, eigenvector] using happly.symm.trans hfixed
  have hscalar : μ ^ (q ^ k) = 1 :=
    (smul_left_injective K.1 hvne) hscalar_smul
  exact hkt_finiteField_scalar_q_power_eq_one (q := q) (k := k)
    (F := K.1) K.2.2.1.2 hμ hscalar


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\EigenlineCore.lean`. -/

private theorem hkt_iv62_r_diag_coord_eq_zero
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (b : Module.Basis (Fin 2) F V) (d : Fin 2 -> F)
    (T : V ≃ₗ[F] V)
    (hT : ∀ i, T (b i) = d i • b i)
    (v : V) (μ : F) (heig : T v = μ • v) :
    ∀ i, (d i - μ) * (b.repr v i) = 0 := by
  classical
  intro i
  have hcoord : b.repr (T v) i = b.repr (μ • v) i := by
    simpa using congrArg (fun w : V => b.repr w i) heig
  have hTv : b.repr (T v) i = d i * b.repr v i := by
    calc
      b.repr (T v) i = b.repr (T (∑ j : Fin 2, (b.repr v j) • b j)) i := by
        rw [b.sum_repr]
      _ = b.repr (∑ j : Fin 2, T ((b.repr v j) • b j)) i := by
        rw [map_sum]
      _ = b.repr (∑ j : Fin 2, (b.repr v j) • T (b j)) i := by
        simp [map_smul]
      _ = b.repr (∑ j : Fin 2, (b.repr v j) • (d j • b j)) i := by
        simp [hT]
      _ = d i * b.repr v i := by
        fin_cases i <;> simp [mul_comm]
  have hμv : b.repr (μ • v) i = μ * b.repr v i := by simp
  rw [hTv, hμv] at hcoord
  calc
    (d i - μ) * b.repr v i = d i * b.repr v i - μ * b.repr v i := by ring
    _ = 0 := sub_eq_zero.mpr hcoord

private theorem hkt_iv62_r_eigenvector_of_diagonal_fin_two
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (b : Module.Basis (Fin 2) F V) (d : Fin 2 -> F)
    (T : V ≃ₗ[F] V)
    (hT : ∀ i, T (b i) = d i • b i)
    (hd : d 0 ≠ d 1)
    (v : V) (μ : F) (hv : v ≠ 0) (heig : T v = μ • v) :
    ∃ i : Fin 2, ∃ c : F, c ≠ 0 ∧ v = c • b i := by
  classical
  let x : Fin 2 -> F := b.repr v
  have hcoord := hkt_iv62_r_diag_coord_eq_zero b d T hT v μ heig
  by_cases hx0 : x 0 = 0
  · have hx1_ne : x 1 ≠ 0 := by
      intro hx1
      apply hv
      apply b.repr.injective
      ext i
      fin_cases i <;> simp [x, hx0, hx1]
    refine ⟨1, x 1, hx1_ne, ?_⟩
    calc
      v = ∑ j : Fin 2, x j • b j := by simp [x, b.sum_repr v]
      _ = x 1 • b 1 := by simp [hx0]
  · have hd0μ : d 0 = μ := by
      have h : (d 0 - μ) * x 0 = 0 := by simpa [x] using hcoord 0
      have hz := (mul_eq_zero.mp h).resolve_right hx0
      exact sub_eq_zero.mp hz
    have hx1 : x 1 = 0 := by
      have h : (d 1 - μ) * x 1 = 0 := by simpa [x] using hcoord 1
      have hfac : d 1 - μ ≠ 0 := by
        rw [← hd0μ]
        exact sub_ne_zero.mpr hd.symm
      exact (mul_eq_zero.mp h).resolve_left hfac
    refine ⟨0, x 0, hx0, ?_⟩
    calc
      v = ∑ j : Fin 2, x j • b j := by simp [x, b.sum_repr v]
      _ = x 0 • b 0 := by simp [hx1]

private theorem hkt_iv62_r_line_of_distinct_diagonal_action
    {F : Type u} [Field F]
    (eigenvalue : Fin 2 → F)
    (eigenvector : Fin 2 → (Fin 2 → F))
    (hlin : LinearIndependent F eigenvector)
    (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F))
    (heigen : ∀ i : Fin 2, T (eigenvector i) = eigenvalue i • eigenvector i)
    (hd : eigenvalue 0 ≠ eigenvalue 1)
    {v : Fin 2 -> F} {μ : F} :
    v ≠ 0 -> T v = μ • v ->
      ∃ i : Fin 2, ∃ ν : F, ν ≠ 0 ∧ v = ν • eigenvector i := by
  classical
  intro hv heig
  let b : Module.Basis (Fin 2) F (Fin 2 -> F) :=
    basisOfPiSpaceOfLinearIndependent hlin
  have hdiag : ∀ i, T (b i) = eigenvalue i • b i := by
    intro i
    simpa [b, coe_basisOfPiSpaceOfLinearIndependent] using heigen i
  rcases hkt_iv62_r_eigenvector_of_diagonal_fin_two
      (b := b) (d := eigenvalue) (T := T) hdiag hd v μ hv heig with
    ⟨i, ν, hν, hvline⟩
  refine ⟨i, ν, hν, ?_⟩
  simpa [b, coe_basisOfPiSpaceOfLinearIndependent] using hvline


private theorem hkt_iv62_r_rhoF_nonscalar_of_compatible
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (B0 : Σ rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))),
      Σ eigenvalue : Fin 2 → C.1 → K.1,
        { eigenvector : Fin 2 → (Fin 2 → K.1) //
          (∀ g : Q, ∀ v : Fin 2 → ZMod q,
            rhoF g (fun i => K.2.2.2.1 (v i)) =
              fun i => K.2.2.2.1 ((M.2.1 g v) i)) ∧
            eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
              (letI : Field K.1 := K.2.1;
                LinearIndependent K.1 eigenvector) ∧
                (letI : Field K.1 := K.2.1; (∀ i : Fin 2, eigenvector i ≠ 0) ∧ ∀ i : Fin 2, ∀ c : C.1, rhoF (c.1 : Q) (eigenvector i) = eigenvalue i c • eigenvector i) })
    (c : C.1)
    (hc : ∀ ν : ZMod q,
      (M.2.1 (c.1 : Q)).toLinearMap ≠ ν • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) :
    letI : Field K.1 := K.2.1
    ∀ μ : K.1,
      (B0.1 (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End K.1 (Fin 2 → K.1)) := by
  classical
  let : Field K.1 := K.2.1
  intro μ hscalar
  apply hc (LinearMap.toMatrix' (M.2.1 (c.1 : Q)).toLinearMap 0 0)
  let A := LinearMap.toMatrix' (M.2.1 (c.1 : Q)).toLinearMap
  apply LinearMap.toMatrix'.injective
  ext i j
  by_cases hij : i = j
  · subst j
    have h00 : K.2.2.2.1 (A 0 0) = μ := by
      have happ := congrArg
        (fun (T : Module.End K.1 (Fin 2 → K.1)) =>
          T (fun k => K.2.2.2.1 ((Pi.single 0 (1 : ZMod q) : Fin 2 → ZMod q) k)) 0) hscalar
      have hcompat := congrFun (B0.2.2.2.1 (c.1 : Q) (Pi.single 0 1)) 0
      simpa [A] using hcompat.symm.trans happ
    have hii : K.2.2.2.1 (A i i) = μ := by
      have happ := congrArg
        (fun (T : Module.End K.1 (Fin 2 → K.1)) =>
          T (fun k => K.2.2.2.1 ((Pi.single i (1 : ZMod q) : Fin 2 → ZMod q) k)) i) hscalar
      have hcompat := congrFun (B0.2.2.2.1 (c.1 : Q) (Pi.single i 1)) i
      simpa [A] using hcompat.symm.trans happ
    apply K.2.2.2.1.injective
    simpa [A] using hii.trans h00.symm
  · have hij0 : A i j = 0 := by
      apply K.2.2.2.1.injective
      have happ := congrArg
        (fun (T : Module.End K.1 (Fin 2 → K.1)) =>
          T (fun k => K.2.2.2.1 ((Pi.single j (1 : ZMod q) : Fin 2 → ZMod q) k)) i) hscalar
      have hcompat := congrFun (B0.2.2.2.1 (c.1 : Q) (Pi.single j 1)) i
      simpa [A, hij] using hcompat.symm.trans happ
    simp [A, hij, hij0]

private theorem hkt_iv62_r_distinct_eigenvalues_of_rhoF_nonscalar
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (B0 : Σ rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))),
      Σ eigenvalue : Fin 2 → C.1 → K.1,
        { eigenvector : Fin 2 → (Fin 2 → K.1) //
          (∀ g : Q, ∀ v : Fin 2 → ZMod q,
            rhoF g (fun i => K.2.2.2.1 (v i)) =
              fun i => K.2.2.2.1 ((M.2.1 g v) i)) ∧
            eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
              (letI : Field K.1 := K.2.1;
                LinearIndependent K.1 eigenvector) ∧
                (letI : Field K.1 := K.2.1; (∀ i : Fin 2, eigenvector i ≠ 0) ∧ ∀ i : Fin 2, ∀ c : C.1, rhoF (c.1 : Q) (eigenvector i) = eigenvalue i c • eigenvector i) })
    (c : C.1)
    (hnonscalar :
      letI : Field K.1 := K.2.1
      ∀ μ : K.1,
        (B0.1 (c.1 : Q)).toLinearMap ≠ μ • (1 : Module.End K.1 (Fin 2 → K.1))) :
    letI : Field K.1 := K.2.1
    B0.2.1 0 c ≠ B0.2.1 1 c := by
  classical
  let : Field K.1 := K.2.1
  intro heq
  apply hnonscalar (B0.2.1 0 c)
  let b : Module.Basis (Fin 2) K.1 (Fin 2 → K.1) :=
    basisOfPiSpaceOfLinearIndependent B0.2.2.2.2.2.1
  apply b.ext
  intro i
  fin_cases i
  · simpa [b, coe_basisOfPiSpaceOfLinearIndependent] using
      (B0.2.2.2.2.2.2.2 (0 : Fin 2) c)
  · simpa [b, coe_basisOfPiSpaceOfLinearIndependent, heq.symm] using
      (B0.2.2.2.2.2.2.2 (1 : Fin 2) c)

private theorem hkt_iv62_r_A_eigenline_permutation_pointwise_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (B0 : Σ rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))),
      Σ eigenvalue : Fin 2 → C.1 → K.1,
        { eigenvector : Fin 2 → (Fin 2 → K.1) //
          (∀ g : Q, ∀ v : Fin 2 → ZMod q,
            rhoF g (fun i => K.2.2.2.1 (v i)) =
              fun i => K.2.2.2.1 ((M.2.1 g v) i)) ∧
            eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
              (letI : Field K.1 := K.2.1;
                LinearIndependent K.1 eigenvector) ∧
                (letI : Field K.1 := K.2.1; (∀ i : Fin 2, eigenvector i ≠ 0) ∧ ∀ i : Fin 2, ∀ c : C.1, rhoF (c.1 : Q) (eigenvector i) = eigenvalue i c • eigenvector i) }) :
    ∃ linePermFun : L.1 → Fin 2 → Fin 2,
      letI : Field K.1 := K.2.1
      ∀ a : L.1, ∀ i : Fin 2,
        ∃ μ : K.1, μ ≠ 0 ∧
          B0.1 (a : Q) (B0.2.2.1 i) =
            μ • B0.2.2.1 (linePermFun a i) := by
  classical
  have _ := hq2
  let : Field K.1 := K.2.1
  let rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) := M.2.1
  let rhoF : Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1)) := B0.1
  let eigenvalue : Fin 2 → C.1 → K.1 := B0.2.1
  let eigenvector : Fin 2 → (Fin 2 → K.1) := B0.2.2.1
  have heigen : ∀ i : Fin 2, ∀ c : C.1,
      rhoF (c.1 : Q) (eigenvector i) = eigenvalue i c • eigenvector i := by
    intro i c
    exact B0.2.2.2.2.2.2.2 i c
  have heigenvector_ne : ∀ i : Fin 2, eigenvector i ≠ 0 :=
    B0.2.2.2.2.2.2.1
  have hnonscalar : ∃ c0 : C.1, ∀ μ : K.1,
      (rhoF (c0.1 : Q)).toLinearMap ≠
        μ • (1 : Module.End K.1 (Fin 2 → K.1)) := by
    obtain ⟨c0, hc0⟩ := C.2.2.2.2
    exact ⟨c0,
      hkt_iv62_r_rhoF_nonscalar_of_compatible
        (Q := Q) (q := q) S L M C K B0 c0 hc0⟩
  obtain ⟨c0, hc0_nonscalar⟩ := hnonscalar
  have hc0_sep : eigenvalue 0 c0 ≠ eigenvalue 1 c0 :=
    hkt_iv62_r_distinct_eigenvalues_of_rhoF_nonscalar
      (Q := Q) (q := q) S L M C K B0 c0 hc0_nonscalar
  have hcommF_of_hcomm (x y : Q)
      (hxy : Commute (rho x) (rho y)) :
      Commute (rhoF x) (rhoF y) := by
    change rhoF x * rhoF y = rhoF y * rhoF x
    apply LinearEquiv.toLinearMap_injective
    let b : Module.Basis (Fin 2) K.1 (Fin 2 → K.1) := Pi.basisFun K.1 (Fin 2)
    apply b.ext
    intro i
    let eZ : Fin 2 → ZMod q := fun j => if j = i then 1 else 0
    let eF : Fin 2 → K.1 := fun j => if j = i then 1 else 0
    have h_embed : (fun j : Fin 2 => K.2.2.2.1 (eZ j)) = eF := by
      ext j
      by_cases h : j = i <;> simp [eZ, eF, h]
    have h_basis : b i = eF := by
      ext j
      by_cases h : j = i <;> simp [b, eF, Pi.basisFun_apply, Pi.single, h]
    have hxy' : rho (x * y) = rho (y * x) := by
      simpa only [map_mul] using hxy.eq
    change (rhoF x * rhoF y) (b i) = (rhoF y * rhoF x) (b i)
    rw [← map_mul, ← map_mul, h_basis, ← h_embed]
    calc
      rhoF (x * y) (fun j => K.2.2.2.1 (eZ j)) =
          fun j => K.2.2.2.1 ((rho (x * y) eZ) j) := by
            exact B0.2.2.2.1 (x * y) eZ
      _ = fun j => K.2.2.2.1 ((rho (y * x) eZ) j) := by rw [hxy']
      _ = rhoF (y * x) (fun j => K.2.2.2.1 (eZ j)) := by
            exact (B0.2.2.2.1 (y * x) eZ).symm
  have hlineWitnesses :
      ∀ a : L.1, ∀ i : Fin 2, ∃ j : Fin 2, ∃ μ : K.1,
        μ ≠ 0 ∧ rhoF (a : Q) (eigenvector i) = μ • eigenvector j := by
    intro a i
    let d : Q := (a : Q)⁻¹ * (c0.1 : Q) * (a : Q)
    have hcommZ : Commute (rho d) (rho (c0.1 : Q)) := by
      simpa [d, mul_assoc] using C.2.2.2.1 (a⁻¹) c0
    have hcommF : Commute (rhoF d) (rhoF (c0.1 : Q)) :=
      hcommF_of_hcomm d (c0.1 : Q) hcommZ
    have hdv_ne : rhoF d (eigenvector i) ≠ 0 := by
      intro hzero
      exact heigenvector_ne i ((rhoF d).injective (by simpa using hzero))
    have hdv_eigen :
        rhoF (c0.1 : Q) (rhoF d (eigenvector i)) =
          eigenvalue i c0 • rhoF d (eigenvector i) := by
      calc
        rhoF (c0.1 : Q) (rhoF d (eigenvector i)) =
            rhoF d (rhoF (c0.1 : Q) (eigenvector i)) := by
              change (rhoF (c0.1 : Q) * rhoF d) (eigenvector i) =
                (rhoF d * rhoF (c0.1 : Q)) (eigenvector i)
              rw [hcommF.eq]
        _ = rhoF d (eigenvalue i c0 • eigenvector i) := by rw [heigen]
        _ = eigenvalue i c0 • rhoF d (eigenvector i) := by simp
    obtain ⟨j, ν, hν, hdv_line⟩ :=
      hkt_iv62_r_line_of_distinct_diagonal_action
        (F := K.1) (eigenvalue := fun k : Fin 2 => eigenvalue k c0)
        (eigenvector := eigenvector) B0.2.2.2.2.2.1 (rhoF (c0.1 : Q))
        (by intro k; exact heigen k c0) hc0_sep hdv_ne hdv_eigen
    have heval : eigenvalue j c0 = eigenvalue i c0 := by
      have hcalc := hdv_eigen
      rw [hdv_line] at hcalc
      simp only [map_smul, heigen, smul_smul] at hcalc
      have hcoef : ν * eigenvalue j c0 = eigenvalue i c0 * ν :=
        (smul_left_injective K.1 (heigenvector_ne j)) hcalc
      apply mul_left_cancel₀ hν
      simpa [mul_comm] using hcoef
    have hji : j = i := by
      fin_cases i <;> fin_cases j
      · rfl
      · exact False.elim (hc0_sep heval.symm)
      · exact False.elim (hc0_sep heval)
      · rfl
    have hdv_line_i : rhoF d (eigenvector i) = ν • eigenvector i := by
      simpa [hji] using hdv_line
    have hav_ne : rhoF (a : Q) (eigenvector i) ≠ 0 := by
      intro hzero
      exact heigenvector_ne i ((rhoF (a : Q)).injective (by simpa using hzero))
    have hca_eq : (c0.1 : Q) * (a : Q) = (a : Q) * d := by
      simp [d, mul_assoc]
    have hca_map :
        rhoF (c0.1 : Q) * rhoF (a : Q) = rhoF (a : Q) * rhoF d := by
      have h := congrArg rhoF hca_eq
      simpa only [map_mul] using h
    have hav_conj :
        rhoF (c0.1 : Q) (rhoF (a : Q) (eigenvector i)) =
          rhoF (a : Q) (rhoF d (eigenvector i)) := by
      exact congrArg
        (fun f : (Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1) => f (eigenvector i))
        hca_map
    have hav_eigen :
        rhoF (c0.1 : Q) (rhoF (a : Q) (eigenvector i)) =
          ν • rhoF (a : Q) (eigenvector i) := by
      calc
        rhoF (c0.1 : Q) (rhoF (a : Q) (eigenvector i)) =
            rhoF (a : Q) (rhoF d (eigenvector i)) := hav_conj
        _ = rhoF (a : Q) (ν • eigenvector i) :=
          congrArg (rhoF (a : Q)) hdv_line_i
        _ = ν • rhoF (a : Q) (eigenvector i) :=
          map_smul (rhoF (a : Q)) ν (eigenvector i)
    exact hkt_iv62_r_line_of_distinct_diagonal_action
      (F := K.1) (eigenvalue := fun k : Fin 2 => eigenvalue k c0)
      (eigenvector := eigenvector) B0.2.2.2.2.2.1 (rhoF (c0.1 : Q))
      (by intro k; exact heigen k c0) hc0_sep hav_ne hav_eigen
  choose lineFields hline using hlineWitnesses
  exact ⟨lineFields, hline⟩

/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\EigenlineAction.lean`. -/

private theorem hkt_iv62_r_eigenline_scalar_multiple_index_eq
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (B0 : Σ rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))),
      Σ eigenvalue : Fin 2 → C.1 → K.1,
        { eigenvector : Fin 2 → (Fin 2 → K.1) //
          (∀ g : Q, ∀ v : Fin 2 → ZMod q,
            rhoF g (fun i => K.2.2.2.1 (v i)) =
              fun i => K.2.2.2.1 ((M.2.1 g v) i)) ∧
            eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
              (letI : Field K.1 := K.2.1;
                LinearIndependent K.1 eigenvector) ∧
                (letI : Field K.1 := K.2.1; (∀ i : Fin 2, eigenvector i ≠ 0) ∧ ∀ i : Fin 2, ∀ c : C.1, rhoF (c.1 : Q) (eigenvector i) = eigenvalue i c • eigenvector i) }) :
    letI : Field K.1 := K.2.1
    ∀ {i j : Fin 2} {μ ν : K.1}, μ ≠ 0 →
      μ • B0.2.2.1 i = ν • B0.2.2.1 j → i = j := by
  classical
  let : Field K.1 := K.2.1
  intro i j μ ν hμ h
  exact B0.2.2.2.2.2.1.eq_of_smul_apply_eq_smul_apply μ ν i j hμ h

private theorem hkt_iv62_r_A_eigenline_permutation_action_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (B0 : Σ rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))),
      Σ eigenvalue : Fin 2 → C.1 → K.1,
        { eigenvector : Fin 2 → (Fin 2 → K.1) //
          (∀ g : Q, ∀ v : Fin 2 → ZMod q,
            rhoF g (fun i => K.2.2.2.1 (v i)) =
              fun i => K.2.2.2.1 ((M.2.1 g v) i)) ∧
            eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
              (letI : Field K.1 := K.2.1;
                LinearIndependent K.1 eigenvector) ∧
                (letI : Field K.1 := K.2.1; (∀ i : Fin 2, eigenvector i ≠ 0) ∧ ∀ i : Fin 2, ∀ c : C.1, rhoF (c.1 : Q) (eigenvector i) = eigenvalue i c • eigenvector i) }) :
    ∃ linePermFun : L.1 → Fin 2 → Fin 2,
      (∀ i : Fin 2, linePermFun 1 i = i) ∧
        (∀ a b : L.1, ∀ i : Fin 2,
          linePermFun (a * b) i = linePermFun a (linePermFun b i)) ∧
          letI : Field K.1 := K.2.1
          ∀ a : L.1, ∀ i : Fin 2,
            ∃ μ : K.1, μ ≠ 0 ∧
              B0.1 (a : Q) (B0.2.2.1 i) =
                μ • B0.2.2.1 (linePermFun a i) := by
  classical
  let : Field K.1 := K.2.1
  let rhoF : Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1)) := B0.1
  let eigenvector : Fin 2 → (Fin 2 → K.1) := B0.2.2.1
  change ∃ linePermFun : L.1 → Fin 2 → Fin 2,
      (∀ i : Fin 2, linePermFun 1 i = i) ∧
        (∀ a b : L.1, ∀ i : Fin 2,
          linePermFun (a * b) i = linePermFun a (linePermFun b i)) ∧
          ∀ a : L.1, ∀ i : Fin 2,
            ∃ μ : K.1, μ ≠ 0 ∧
              rhoF (a : Q) (eigenvector i) =
                μ • eigenvector (linePermFun a i)
  obtain ⟨linePermFun, hlinePerm_preserves_raw⟩ := hkt_iv62_r_A_eigenline_permutation_pointwise_source
    (Q := Q) (q := q) hq2 S L M C K B0
  have hlinePerm_preserves : ∀ a : L.1, ∀ i : Fin 2,
      ∃ μ : K.1, μ ≠ 0 ∧
        rhoF (a : Q) (eigenvector i) = μ • eigenvector (linePermFun a i) := by
    intro a i
    exact hlinePerm_preserves_raw a i
  refine ⟨linePermFun, ?_, ?_, hlinePerm_preserves⟩
  · intro i
    obtain ⟨μ, hμ, hline⟩ := hlinePerm_preserves (1 : L.1) i
    have hEq : μ • eigenvector (linePermFun 1 i) =
        (1 : K.1) • eigenvector i := by
      simpa using hline.symm
    exact hkt_iv62_r_eigenline_scalar_multiple_index_eq
      (Q := Q) (q := q) S L M C K B0 hμ
      (show μ • B0.2.2.1 (linePermFun 1 i) =
        (1 : K.1) • B0.2.2.1 i from hEq)
  · intro a b i
    obtain ⟨lam, hlam, hline_ab⟩ := hlinePerm_preserves (a * b) i
    obtain ⟨ν, hν, hline_b⟩ := hlinePerm_preserves b i
    obtain ⟨μ, hμ, hline_a⟩ := hlinePerm_preserves a (linePermFun b i)
    have hcomp : rhoF ((a * b : L.1) : Q) (eigenvector i) =
        (ν * μ) • eigenvector (linePermFun a (linePermFun b i)) := by
      calc
        rhoF ((a * b : L.1) : Q) (eigenvector i)
            = (rhoF (a : Q) * rhoF (b : Q)) (eigenvector i) := by
              rw [← MonoidHom.map_mul]
              rfl
        _ = rhoF (a : Q) (rhoF (b : Q) (eigenvector i)) := by
              rfl
        _ = rhoF (a : Q) (ν • eigenvector (linePermFun b i)) := by
              rw [hline_b]
        _ = ν • rhoF (a : Q) (eigenvector (linePermFun b i)) := by
              simp
        _ = ν • (μ • eigenvector (linePermFun a (linePermFun b i))) := by
              rw [hline_a]
        _ = (ν * μ) • eigenvector (linePermFun a (linePermFun b i)) := by
              rw [mul_smul]
    have hEq : lam • eigenvector (linePermFun (a * b) i) =
        (ν * μ) • eigenvector (linePermFun a (linePermFun b i)) := by
      exact hline_ab.symm.trans hcomp
    exact hkt_iv62_r_eigenline_scalar_multiple_index_eq
      (Q := Q) (q := q) S L M C K B0 hlam
      (show lam • B0.2.2.1 (linePermFun (a * b) i) =
        (ν * μ) • B0.2.2.1 (linePermFun a (linePermFun b i)) from hEq)


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\EigenlineTrivial.lean`. -/

private theorem hkt_iv62_r_trivial_eigenline_perm_forces_basis_fixed_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (B0 : Σ rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))),
      Σ eigenvalue : Fin 2 → C.1 → K.1,
        { eigenvector : Fin 2 → (Fin 2 → K.1) //
          (∀ g : Q, ∀ v : Fin 2 → ZMod q,
            rhoF g (fun i => K.2.2.2.1 (v i)) =
              fun i => K.2.2.2.1 ((M.2.1 g v) i)) ∧
            eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
              (letI : Field K.1 := K.2.1;
                LinearIndependent K.1 eigenvector) ∧
                (letI : Field K.1 := K.2.1; (∀ i : Fin 2, eigenvector i ≠ 0) ∧ ∀ i : Fin 2, ∀ c : C.1, rhoF (c.1 : Q) (eigenvector i) = eigenvalue i c • eigenvector i) })
    (linePerm : L.1 →* Equiv.Perm (Fin 2))
    (hlinePerm_preserves_eigenlines :
      letI : Field K.1 := K.2.1
      ∀ a : L.1, ∀ i : Fin 2,
        ∃ μ : K.1, μ ≠ 0 ∧
          B0.1 (a : Q) (B0.2.2.1 i) =
            μ • B0.2.2.1 (linePerm a i)) :
    linePerm = 1 → ∀ a : L.1, ∀ i : Fin 2,
        B0.1 (a : Q) (B0.2.2.1 i) = B0.2.2.1 i := by
  classical
  let : Field K.1 := K.2.1
  let rhoF : Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1)) := B0.1
  let eigenvector : Fin 2 → (Fin 2 → K.1) := B0.2.2.1
  have hpreserves : ∀ a : L.1, ∀ i : Fin 2,
      ∃ μ : K.1, μ ≠ 0 ∧
        rhoF (a : Q) (eigenvector i) = μ • eigenvector (linePerm a i) := by
    intro a i
    exact hlinePerm_preserves_eigenlines a i
  change linePerm = 1 → ∀ a : L.1, ∀ i : Fin 2,
    rhoF (a : Q) (eigenvector i) = eigenvector i
  intro hperm a i
  obtain ⟨μ, hμ, hline⟩ := hpreserves a i
  have hidx : linePerm a i = i := by
    have h := congrArg (fun f : L.1 →* Equiv.Perm (Fin 2) => f a i) hperm
    simpa using h
  have hline_same : rhoF (a : Q) (eigenvector i) = μ • eigenvector i := by
    simpa [hidx] using hline
  have hμ1 := hkt_iv62_r_sylow_scalar_eigenvalue_eq_one
    (Q := Q) (q := q) hq2 S L M C K B0 a i hμ
    (show B0.1 (a : Q) (B0.2.2.1 i) = μ • B0.2.2.1 i from hline_same)
  simpa [hμ1] using hline_same

private theorem hkt_iv62_r_trivial_eigenline_perm_forces_rhoF_trivial_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (B0 : Σ rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))),
      Σ eigenvalue : Fin 2 → C.1 → K.1,
        { eigenvector : Fin 2 → (Fin 2 → K.1) //
          (∀ g : Q, ∀ v : Fin 2 → ZMod q,
            rhoF g (fun i => K.2.2.2.1 (v i)) =
              fun i => K.2.2.2.1 ((M.2.1 g v) i)) ∧
            eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
              (letI : Field K.1 := K.2.1;
                LinearIndependent K.1 eigenvector) ∧
                (letI : Field K.1 := K.2.1; (∀ i : Fin 2, eigenvector i ≠ 0) ∧ ∀ i : Fin 2, ∀ c : C.1, rhoF (c.1 : Q) (eigenvector i) = eigenvalue i c • eigenvector i) })
    (linePerm : L.1 →* Equiv.Perm (Fin 2))
    (hlinePerm_preserves_eigenlines :
      letI : Field K.1 := K.2.1
      ∀ a : L.1, ∀ i : Fin 2,
        ∃ μ : K.1, μ ≠ 0 ∧
          B0.1 (a : Q) (B0.2.2.1 i) =
            μ • B0.2.2.1 (linePerm a i)) :
    linePerm = 1 → ∀ a : L.1, B0.1 (a : Q) = 1 := by
  classical
  let : Field K.1 := K.2.1
  intro hperm a
  let b : Module.Basis (Fin 2) K.1 (Fin 2 → K.1) :=
    basisOfPiSpaceOfLinearIndependent B0.2.2.2.2.2.1
  apply b.ext'
  intro i
  have hfix := hkt_iv62_r_trivial_eigenline_perm_forces_basis_fixed_source
    (Q := Q) (q := q) hq2 S L M C K B0 linePerm hlinePerm_preserves_eigenlines hperm a i
  simpa [b, coe_basisOfPiSpaceOfLinearIndependent] using hfix

private theorem hkt_iv62_r_trivial_eigenline_perm_forces_rho_trivial_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (B0 : Σ rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))),
      Σ eigenvalue : Fin 2 → C.1 → K.1,
        { eigenvector : Fin 2 → (Fin 2 → K.1) //
          (∀ g : Q, ∀ v : Fin 2 → ZMod q,
            rhoF g (fun i => K.2.2.2.1 (v i)) =
              fun i => K.2.2.2.1 ((M.2.1 g v) i)) ∧
            eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
              (letI : Field K.1 := K.2.1;
                LinearIndependent K.1 eigenvector) ∧
                (letI : Field K.1 := K.2.1; (∀ i : Fin 2, eigenvector i ≠ 0) ∧ ∀ i : Fin 2, ∀ c : C.1, rhoF (c.1 : Q) (eigenvector i) = eigenvalue i c • eigenvector i) })
    (linePerm : L.1 →* Equiv.Perm (Fin 2))
    (hlinePerm_preserves_eigenlines :
      letI : Field K.1 := K.2.1
      ∀ a : L.1, ∀ i : Fin 2,
        ∃ μ : K.1, μ ≠ 0 ∧
          B0.1 (a : Q) (B0.2.2.1 i) =
            μ • B0.2.2.1 (linePerm a i)) :
    linePerm = 1 → ∀ a : L.1, M.2.1 (a : Q) = 1 := by
  classical
  let : Field K.1 := K.2.1
  intro hperm a
  have hrhoF := hkt_iv62_r_trivial_eigenline_perm_forces_rhoF_trivial_source
    (Q := Q) (q := q) hq2 S L M C K B0 linePerm hlinePerm_preserves_eigenlines hperm a
  apply LinearEquiv.ext
  intro v
  ext i
  apply K.2.2.2.2
  have hcompat := B0.2.2.2.1 (a : Q) v
  have hF := congrArg (fun e : (Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1) =>
      e (fun j => K.2.2.2.1 (v j))) hrhoF
  have hcoord : (fun j => K.2.2.2.1 ((M.2.1 (a : Q) v) j)) =
      fun j => K.2.2.2.1 (v j) := by
    rw [← hcompat]
    simpa using hF
  exact congrFun hcoord i

private theorem hkt_iv62_r_trivial_eigenline_perm_forces_centralization_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (B0 : Σ rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))),
      Σ eigenvalue : Fin 2 → C.1 → K.1,
        { eigenvector : Fin 2 → (Fin 2 → K.1) //
          (∀ g : Q, ∀ v : Fin 2 → ZMod q,
            rhoF g (fun i => K.2.2.2.1 (v i)) =
              fun i => K.2.2.2.1 ((M.2.1 g v) i)) ∧
            eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
              (letI : Field K.1 := K.2.1;
                LinearIndependent K.1 eigenvector) ∧
                (letI : Field K.1 := K.2.1; (∀ i : Fin 2, eigenvector i ≠ 0) ∧ ∀ i : Fin 2, ∀ c : C.1, rhoF (c.1 : Q) (eigenvector i) = eigenvalue i c • eigenvector i) })
    (linePerm : L.1 →* Equiv.Perm (Fin 2))
    (hlinePerm_preserves_eigenlines :
      letI : Field K.1 := K.2.1
      ∀ a : L.1, ∀ i : Fin 2,
        ∃ μ : K.1, μ ≠ 0 ∧
          B0.1 (a : Q) (B0.2.2.1 i) =
            μ • B0.2.2.1 (linePerm a i)) :
    linePerm = 1 → L.1 ≤ Subgroup.centralizer (L.2.1 : Set Q) := by
  classical
  let : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
  intro hperm a ha b hb
  let aA : L.1 := ⟨a, ha⟩
  let bB : L.2.1 := ⟨b, hb⟩
  have hrho := hkt_iv62_r_trivial_eigenline_perm_forces_rho_trivial_source
    (Q := Q) (q := q) hq2 S L M C K B0 linePerm hlinePerm_preserves_eigenlines hperm aA
  have hcompat := M.2.2.2 a bB
  have hcoord : M.1 (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) a) bB)) =
      M.1 (Additive.ofMul bB) := by
    rw [hcompat, hrho]
    simp
  have hfix_add : Additive.ofMul ((MulAut.conjNormal (H := L.2.1) a) bB) =
      Additive.ofMul bB := M.1.injective hcoord
  have hfix : ((MulAut.conjNormal (H := L.2.1) a) bB : L.2.1) = bB :=
    Additive.ofMul.injective hfix_add
  have hval : a * b * a⁻¹ = b := by
    simpa [bB, MulAut.conjNormal_apply, MulAut.conj_apply] using congrArg Subtype.val hfix
  have hcomm : a * b = b * a := mul_inv_eq_iff_eq_mul.mp hval
  exact hcomm.symm


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\EigenlineSeed.lean`. -/

private theorem hkt_iv62_r_A_eigenline_permutation_seed
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (K : Σ F : Type u,
      Σ field_F : Field F,
        ({ _finite_F : Finite F // Nat.card F = q ^ 2 } ×
          (letI : Field F := field_F;
            { zmodToF : ZMod q →+* F // Function.Injective zmodToF })))
    (B0 : Σ rhoF : (let : Field K.1 := K.2.1;
      Q →* ((Fin 2 → K.1) ≃ₗ[K.1] (Fin 2 → K.1))),
      Σ eigenvalue : Fin 2 → C.1 → K.1,
        { eigenvector : Fin 2 → (Fin 2 → K.1) //
          (∀ g : Q, ∀ v : Fin 2 → ZMod q,
            rhoF g (fun i => K.2.2.2.1 (v i)) =
              fun i => K.2.2.2.1 ((M.2.1 g v) i)) ∧
            eigenvector (0 : Fin 2) ≠ eigenvector (1 : Fin 2) ∧
              (letI : Field K.1 := K.2.1;
                LinearIndependent K.1 eigenvector) ∧
                (letI : Field K.1 := K.2.1; (∀ i : Fin 2, eigenvector i ≠ 0) ∧ ∀ i : Fin 2, ∀ c : C.1, rhoF (c.1 : Q) (eigenvector i) = eigenvalue i c • eigenvector i) }) :
    Nonempty { linePerm : L.1 →* Equiv.Perm (Fin 2) // linePerm = 1 → L.1 ≤ Subgroup.centralizer (L.2.1 : Set Q) } := by
  classical
  let : Field K.1 := K.2.1
  obtain ⟨linePermFun, hlinePerm_one, hlinePerm_mul, hlinePerm_preserves⟩ :=
    hkt_iv62_r_A_eigenline_permutation_action_source
      (Q := Q) (q := q) hq2 S L M C K B0
  let linePerm : L.1 →* Equiv.Perm (Fin 2) := by
    refine {
      toFun := fun a => {
        toFun := linePermFun a
        invFun := linePermFun a⁻¹
        left_inv := ?_
        right_inv := ?_ }
      map_one' := ?_
      map_mul' := ?_ }
    · intro i
      have h := hlinePerm_mul a⁻¹ a i
      simpa [hlinePerm_one] using h.symm
    · intro i
      have h := hlinePerm_mul a a⁻¹ i
      simpa [hlinePerm_one] using h.symm
    · ext i
      exact congrArg Fin.val (hlinePerm_one i)
    · intro a b
      ext i
      exact congrArg Fin.val (hlinePerm_mul a b i)
  have hlinePerm_preserves_eigenlines :
      ∀ a : L.1, ∀ i : Fin 2,
        ∃ μ : K.1, μ ≠ 0 ∧
          B0.1 (a : Q) (B0.2.2.1 i) =
            μ • B0.2.2.1 (linePerm a i) := by
    intro a i
    simpa [linePerm] using hlinePerm_preserves a i
  exact ⟨linePerm,
    hkt_iv62_r_trivial_eigenline_perm_forces_centralization_source
      (Q := Q) (q := q) hq2 S L M C K B0 linePerm hlinePerm_preserves_eigenlines⟩


private theorem hkt_iv62_r_trivial_line_action_forces_scalar_centralization
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (linePerm : L.1 →* Equiv.Perm (Fin 2))
    (trivial_linePerm_forces_A_centralizes_B :
      linePerm = 1 → L.1 ≤ Subgroup.centralizer (L.2.1 : Set Q)) :
    linePerm = 1 → False := by
  classical
  have _ := hq2
  have _ := C
  intro htriv
  exact L.2.2.2.2.2.2.1 (trivial_linePerm_forces_A_centralizes_B htriv)


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\EigenlineFinal.lean`. -/

private theorem hkt_iv62_r_line_permutation_nontrivial_of_diagonalization
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) })
    (linePerm : L.1 →* Equiv.Perm (Fin 2))
    (trivial_linePerm_forces_A_centralizes_B :
      linePerm = 1 → L.1 ≤ Subgroup.centralizer (L.2.1 : Set Q)) :
    linePerm ≠ 1 := by
  classical
  exact hkt_iv62_r_trivial_line_action_forces_scalar_centralization
    (Q := Q) (q := q) hq2 S L M C linePerm trivial_linePerm_forces_A_centralizes_B


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\Terminal.lean`. -/

/-- Huppert IV.6.2(r), coordinate source theorem debt: an elementary abelian
`q`-group of order `q^2` is additively isomorphic to `(ZMod q)^2`. -/
private theorem hkt_iv62_terminal_coordinates_exists
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q }) :
    Nonempty (Additive (L.2.1) ≃+ (Fin 2 → ZMod q)) := by
  classical
  let : IsElementaryAbelian q L.2.1 := L.2.2.2.2.2.2.2.2.2.1
  let : CommGroup L.2.1 :=
    { mul_comm := fun a b =>
        L.2.2.2.2.2.2.2.2.2.1.toIsMulCommutative.is_comm.comm a b }
  have : Module.Finite (ZMod q) (Additive (L.2.1)) := Module.Finite.of_finite
  have : Module.Finite (ZMod q) (Fin 2 → ZMod q) := Module.Finite.of_finite
  have hnat : Nat.card (Additive (L.2.1)) =
      q ^ Module.finrank (ZMod q) (Additive (L.2.1)) := by
    simpa using Module.natCard_eq_pow_finrank (K := ZMod q) (V := Additive (L.2.1))
  have hcard : Nat.card (Additive (L.2.1)) = q ^ 2 := by
    simpa [Additive] using L.2.2.2.2.2.2.2.2.2.2.1
  have hpow : q ^ Module.finrank (ZMod q) (Additive (L.2.1)) = q ^ 2 := by
    rw [← hnat, hcard]
  have hfin : Module.finrank (ZMod q) (Additive (L.2.1)) = 2 :=
    Nat.pow_right_injective (Nat.Prime.two_le (Fact.out : Nat.Prime q)) hpow
  have htarget : Module.finrank (ZMod q) (Fin 2 → ZMod q) = 2 := by
    simp
  exact ⟨(LinearEquiv.ofFinrankEq (Additive (L.2.1)) (Fin 2 → ZMod q) (by
    rw [hfin, htarget])).toAddEquiv⟩

set_option backward.isDefEq.respectTransparency false in
/-- Huppert IV.6.2(r), conjugation-action source theorem debt: after choosing
coordinates on `B`, conjugation gives a linear action of `Q` with kernel
`C_Q(B)=O_q(Q)`. -/
private theorem hkt_iv62_terminal_conjugation_linear_action_exists
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q)) :
    ∃ rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)),
      rho.ker = pCore q Q ∧
        (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
          ∀ g : Q, ∀ b : L.2.1,
            coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
              rho g (coord (Additive.ofMul b))) := by
  classical
  let : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
  let : IsElementaryAbelian q L.2.1 := L.2.2.2.2.2.2.2.2.2.1
  let : CommGroup L.2.1 :=
    { mul_comm := fun a b =>
        L.2.2.2.2.2.2.2.2.2.1.toIsMulCommutative.is_comm.comm a b }
  let : MulDistribMulAction Q L.2.1 :=
    MulDistribMulAction.compHom L.2.1 (MulAut.conjNormal (H := L.2.1))
  let coordLin : Additive (L.2.1) ≃ₗ[ZMod q] (Fin 2 → ZMod q) :=
    coord.toLinearEquiv (fun c x => by
      simpa using (ZMod.map_smul coord.toAddMonoidHom c x))
  let rep : Representation (ZMod q) Q (Additive (L.2.1)) :=
    Theory.Representation.ofElementaryAbelianAction (A := Q) (G := L.2.1) (p := q)
  have rep_apply (g : Q) (b : L.2.1) :
      rep g (Additive.ofMul b) =
        Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b) := by
    simp [rep, MulAction.compHom_smul_def]
  let repAut : Q →* (Additive (L.2.1) ≃ₗ[ZMod q] Additive (L.2.1)) :=
    { toFun := fun g =>
        LinearEquiv.ofLinearMap (rep g) (rep g⁻¹)
          (by
            change rep g * rep g⁻¹ = LinearMap.id
            rw [← map_mul rep, mul_inv_cancel, map_one]
            rfl)
          (by
            change rep g⁻¹ * rep g = LinearMap.id
            rw [← map_mul rep, inv_mul_cancel, map_one]
            rfl)
      map_one' := by
        ext x
        simp [rep]
      map_mul' := by
        intro g h
        ext x
        simp [rep] }
  let rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) :=
    { toFun := fun g => coordLin.symm.trans ((repAut g).trans coordLin)
      map_one' := by
        ext v i
        simp [repAut, coordLin]
      map_mul' := by
        intro g h
        ext v i
        simp [repAut, coordLin] }
  refine ⟨rho, ?_, ?_⟩
  · ext g
    constructor
    · intro hg
      rw [← L.2.2.2.2.2.2.2.2.2.2.2]
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      let bB : L.2.1 := ⟨b, hb⟩
      have hfix_coord :
          rho g (coord (Additive.ofMul bB)) = coord (Additive.ofMul bB) := by
        simpa [MonoidHom.mem_ker] using
          congrArg
            (fun e : (Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q) =>
              e (coord (Additive.ofMul bB))) hg
      have hrep_fix : rep g (Additive.ofMul bB) = Additive.ofMul bB := by
        apply coordLin.injective
        simpa [rho, repAut, coordLin] using hfix_coord
      have hfix_add :
          Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) bB) =
            Additive.ofMul bB := by
        rw [← rep_apply g bB]
        exact hrep_fix
      have hfix : ((MulAut.conjNormal (H := L.2.1) g) bB : L.2.1) = bB :=
        Additive.ofMul.injective hfix_add
      have hval : g * b * g⁻¹ = b := by
        simpa [bB] using congrArg Subtype.val hfix
      have hgb : g * b = b * g := mul_inv_eq_iff_eq_mul.mp hval
      exact hgb.symm
    · intro hg
      rw [← L.2.2.2.2.2.2.2.2.2.2.2] at hg
      rw [MonoidHom.mem_ker]
      ext v i
      let x : Additive (L.2.1) := coordLin.symm v
      let xB : L.2.1 := Additive.toMul x
      have hx : Additive.ofMul xB = x := by
        simp [xB]
      have hcomm : (xB : Q) * g = g * (xB : Q) :=
        (Subgroup.mem_centralizer_iff.mp hg) (xB : Q) xB.2
      have hfix_val : g * (xB : Q) * g⁻¹ = (xB : Q) := by
        rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
      have hfix : (MulAut.conjNormal (H := L.2.1) g) xB = xB := by
        ext
        simpa using hfix_val
      have hfix_add :
          Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) xB) =
            Additive.ofMul xB := by
        rw [hfix]
      have hrep_fix : rep g x = x := by
        rw [← hx]
        rw [rep_apply, hfix_add]
      have hrho_fix : rho g v = v := by
        simpa [rho, repAut, coordLin, x] using congrArg coordLin hrep_fix
      simpa using congrFun hrho_fix i
  · intro g b
    have hrep_apply := rep_apply g b
    simpa [rho, repAut, coordLin] using congrArg coord hrep_apply.symm

/-- Huppert IV.6.2(r), linearization source theorem debt: the terminal layer
`B` of order `q^2` gives a faithful two-dimensional linear conjugation action
of `Q/O_q(Q)`. -/
private theorem hkt_iv62_terminal_linear_model_exists
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q }) :
    Nonempty (Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) }) := by
  classical
  obtain ⟨coord⟩ := hkt_iv62_terminal_coordinates_exists (Q := Q) (q := q) S L
  obtain ⟨rho, hker, hcompat⟩ :=
    hkt_iv62_terminal_conjugation_linear_action_exists
      (Q := Q) (q := q) S L coord
  exact ⟨coord, rho, hker, hcompat⟩

/-- Huppert IV.6.2(r), final no-swap contradiction once the source has supplied
its eigenspace permutation. The hard source work is not hidden here: it is the
construction of the coprime-order diagonalization and the induced action of `A`
on the two uniquely determined eigenspaces. -/
private theorem hkt_iv62_gl2_terminal_model_contradiction
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (M : Σ coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q),
      { rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q)) //
        rho.ker = pCore q Q ∧
          (letI : (L.2.1).Normal := L.2.2.2.2.2.2.2.1
            ∀ g : Q, ∀ b : L.2.1,
              coord (Additive.ofMul ((MulAut.conjNormal (H := L.2.1) g) b)) =
                rho g (coord (Additive.ofMul b))) })
    (linePerm : L.1 →* Equiv.Perm (Fin 2))
    (linePerm_nontrivial : linePerm ≠ 1) : False := by
  classical
  have _ := M
  have hA_p : IsPGroup q L.1 := IsPGroup.to_le S.isPGroup' L.2.2.1
  have htrivial : linePerm = 1 :=
    hkt_fin_two_perm_hom_eq_one_of_isPGroup_odd (q := q) hq2 hA_p linePerm
  exact linePerm_nontrivial htrivial

set_option maxHeartbeats 800000
/-- Huppert IV.6.2(r), final GL(2,q) contradiction.  The terminal layer makes
`G/O_q(G)` act faithfully on a two-dimensional elementary abelian `q`-group;
for `q ≠ 2`, the source eigenspace data gives a forbidden nontrivial action of
a `q`-group on a two-element set. -/
private theorem hkt_iv62_terminal_linear_contradiction
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (hnot_Qp : ¬ IsPGroup q Q)
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd : HasNormalPComplement q
      (↥(Subgroup.normalizer
        (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    (hproper_rec : ∀ (H : Subgroup Q) (T : Sylow q H), H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H → HasNormalPComplement q (Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q H)
    (hsmall_rec : ∀ {R : Type u} [Group R] [Finite R] (T : Sylow q R), Nat.card R < Nat.card Q → q ∣ Nat.card R → HasNormalPComplement q (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q R)
    {U : Subgroup Q}
    (hU_ne_bot : U ≠ ⊥) (hU_p : IsPGroup q U)
    (hU_no_complement : ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))))
    (hUmax :
      ∀ W : Subgroup Q,
        W ≠ ⊥ →
        IsPGroup q W →
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
          Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q * (Nat.card Q + 1) + Nat.card W ≤ Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q * (Nat.card Q + 1) + Nat.card U)
    (P : Sylow q (Subgroup.normalizer (U : Set Q)))
    (hUS : U < (S : Subgroup Q))
    (hUN_le_P :
      U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≤
        (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hcardUP :
      Nat.card U < Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hNtop : Subgroup.normalizer (U : Set Q) = ⊤)
    (hU_eq_core : U = pCore q Q)
    (L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q })
    (C0 : Subgroup Q) (hC0_cyclic : IsCyclic C0)
    (hC0_coprime : Nat.Coprime q (Nat.card C0))
    (hC0_model :
      ∀ (hBnorm : (L.2.1).Normal)
        (coord : Additive (L.2.1) ≃+ (Fin 2 → ZMod q))
        (rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q))),
        rho.ker = pCore q Q →
          (letI : (L.2.1).Normal := hBnorm
            ∀ g : Q, ∀ b : (L.2.1),
              coord (Additive.ofMul ((MulAut.conjNormal (H := (L.2.1)) g) b)) =
                rho g (coord (Additive.ofMul b))) →
          (∀ a : L.1, ∀ d : C0,
            Commute
              (rho ((a : Q) * (d : Q) * (a : Q)⁻¹))
              (rho (d : Q))) ∧
            ∃ c : Q,
              C0 = Subgroup.zpowers c ∧
                ∀ μ : ZMod q,
                  (rho c).toLinearMap ≠
                    μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) : False := by
  classical
  obtain ⟨M⟩ := hkt_iv62_terminal_linear_model_exists (Q := Q) (q := q) S L
  obtain ⟨hA_conj_commutes_C0, hC0_generator⟩ :=
    hC0_model L.2.2.2.2.2.2.2.1 M.1 M.2.1 M.2.2.1 M.2.2.2
  obtain ⟨c, hc_order, hA_conj_commutes_zpowers, hc_not_scalar⟩ :=
    hkt_iv62_r_coprime_order_nonscalar_element_exists
      (Q := Q) (q := q) (U := U)
      hcore_bot hnot_Qp hq2 S hq_dvd hnot_burnside hcentralizer_dvd
      hnormalizer_rank_dvd hproper_rec hsmall_rec hU_ne_bot hU_p hU_no_complement hUmax P hUS hUN_le_P hcardUP
      hNtop hU_eq_core L M C0 hC0_cyclic hC0_coprime
      hA_conj_commutes_C0 hC0_generator
  let C : { C : Subgroup Q //
      IsCyclic C ∧
        Nat.Coprime q (Nat.card C) ∧
          (∀ a : L.1, ∀ c : C,
            Commute
              (M.2.1 ((a : Q) * (c.1 : Q) * (a : Q)⁻¹))
              (M.2.1 (c.1 : Q))) ∧
            ∃ c : C, ∀ μ : ZMod q,
              (M.2.1 (c.1 : Q)).toLinearMap ≠
                μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) } :=
    ⟨Subgroup.zpowers c, by infer_instance,
      by simpa [Nat.card_zpowers] using hc_order,
      hA_conj_commutes_zpowers, ⟨⟨c, Subgroup.mem_zpowers c⟩, hc_not_scalar⟩⟩
  obtain ⟨K⟩ := hkt_iv62_r_quadratic_splitting_field_exists
    (Q := Q) (q := q) hq2 S L M C
  obtain ⟨B0⟩ := hkt_iv62_r_eigenspaces_exist_over_quadratic_split
    (Q := Q) (q := q) hq2 S L M C K
  obtain ⟨linePerm, htrivial_linePerm_forces_A_centralizes_B⟩ :=
    hkt_iv62_r_A_eigenline_permutation_seed
      (Q := Q) (q := q) hq2 S L M C K B0
  have linePerm_nontrivial : linePerm ≠ 1 :=
    hkt_iv62_r_line_permutation_nontrivial_of_diagonalization
      (Q := Q) (q := q) hq2 S L M C linePerm htrivial_linePerm_forces_A_centralizes_B
  exact hkt_iv62_gl2_terminal_model_contradiction
    (Q := Q) (q := q) hq2 S L M linePerm linePerm_nontrivial

section ExtractedIV62TerminalObligations

variable {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
variable (hcore_bot : pPrimeCore q Q = ⊥) (hnot_Qp : ¬ IsPGroup q Q)
variable (hq2 : q ≠ 2) (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
variable (hnot_burnside :
  ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
variable (hcentralizer_dvd :
  HasNormalPComplement q
    (↥(Subgroup.centralizer
      (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
variable (hnormalizer_rank_dvd :
  HasNormalPComplement q
    (↥(Subgroup.normalizer
      (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
variable (hproper_rec :
  ∀ (H : Subgroup Q) (T : Sylow q H),
    H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
    HasNormalPComplement q
      (Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H)) →
    HasNormalPComplement q
      (Subgroup.normalizer
        (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H)) →
    HasNormalPComplement q H)
variable (hsmall_rec :
  ∀ {R : Type u} [Group R] [Finite R] (T : Sylow q R),
    Nat.card R < Nat.card Q → q ∣ Nat.card R →
    HasNormalPComplement q
      (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R)) →
    HasNormalPComplement q
      (Subgroup.normalizer
        (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R)) →
    HasNormalPComplement q R)
variable (A : Subgroup Q)
variable (hA_le_S : A ≤ (S : Subgroup Q))
variable (hA_comm : IsMulCommutative A)
variable (hA_not_core : ¬ A ≤ pCore q Q)
variable (hA_rank_maximal :
  ∀ C : Subgroup Q,
    C ≤ (S : Subgroup Q) → IsMulCommutative C → ¬ C ≤ pCore q Q →
      generatorRank C ≤ generatorRank A)
variable (hA_card_minimal :
  ∀ C : Subgroup Q,
    C ≤ (S : Subgroup Q) → IsMulCommutative C → ¬ C ≤ pCore q Q →
      generatorRank C = generatorRank A → Nat.card A ≤ Nat.card C)
variable (hA_global_rank :
  ∀ C : Subgroup Q,
    C ≤ (S : Subgroup Q) → IsMulCommutative C →
      generatorRank C ≤ generatorRank A)
variable (Kbar : Subgroup (Q ⧸ pCore q Q))
variable (hKbar_normal : Kbar.Normal)
variable (hKbar_minimal : IsMinimalNormal Kbar)
variable (hKbar_ne_bot : Kbar ≠ ⊥) (hKbar_ne_top : Kbar ≠ ⊤)
variable (hKbar_coprime : Nat.Coprime q (Nat.card Kbar))
variable (hquot_q : IsPGroup q ((Q ⧸ pCore q Q) ⧸ Kbar))
variable (hquot_dvd : q ∣ Nat.card (Q ⧸ pCore q Q))
variable (hquot_pcore_bot : pCore q (Q ⧸ pCore q Q) = ⊥)
variable (hsolvable : Group.IsSolvable Q)


/-- Extracted source-(i) obligation. Huppert's J(P0) is the subgroup generated
by abelian subgroups of maximal generator rank, so the source proves that
rank-J normalizer is a q-group. The additional max-order Thompson normalizer
required by the strengthened recursive interface only needs a normal
q-complement; it is deliberately not asserted to be a q-group. -/
private theorem hkt_iv62_i_J_normalizers_local_extracted
    (hA_le_S : A ≤ (S : Subgroup Q))
    (hA_comm : IsMulCommutative A)
    (hA_global_rank :
      ∀ C : Subgroup Q,
        C ≤ (S : Subgroup Q) → IsMulCommutative C →
          generatorRank C ≤ generatorRank A)
    (hKbar_normal : Kbar.Normal)
    (hKbar_minimal : IsMinimalNormal Kbar)
    (_hKbar_ne_bot : Kbar ≠ ⊥)
    (hKbar_coprime : Nat.Coprime q (Nat.card Kbar))
    (hsolvable : Group.IsSolvable Q)
    (X : Subgroup Q) (TX : Sylow q X)
    (hX_eq : X =
      ((⁅Kbar, A.map (QuotientGroup.mk' (pCore q Q))⁆ ⊔
        A.map (QuotientGroup.mk' (pCore q Q))).comap
          (QuotientGroup.mk' (pCore q Q))))
    (hA_le_TX : A.subgroupOf X ≤ (TX : Subgroup X))
    (hTX_map_le_S : (TX : Subgroup X).map X.subtype ≤ (S : Subgroup Q))
    (hTX_map_eq : (TX : Subgroup X).map X.subtype = pCore q Q ⊔ A)
    :
    Subgroup.normalizer
        (huppertRankThompsonSubgroup (G := X) (TX : Subgroup X) : Set X) ≤
      (TX : Subgroup X) := by
  classical
  let π : Q →* Q ⧸ pCore q Q := QuotientGroup.mk' (pCore q Q)
  let Abar : Subgroup (Q ⧸ pCore q Q) := A.map π
  let K2bar : Subgroup (Q ⧸ pCore q Q) := ⁅Kbar, Abar⁆
  let Xbar : Subgroup (Q ⧸ pCore q Q) := K2bar ⊔ Abar
  let K2X : Subgroup Xbar := K2bar.subgroupOf Xbar
  let AX : Subgroup Xbar := Abar.subgroupOf Xbar
  let piX : X →* Xbar :=
    (π.comp X.subtype).codRestrict Xbar (fun x => by
      have hx : (x : Q) ∈
          ((⁅Kbar, A.map (QuotientGroup.mk' (pCore q Q))⁆ ⊔
            A.map (QuotientGroup.mk' (pCore q Q))).comap
              (QuotientGroup.mk' (pCore q Q))) :=
        (le_of_eq hX_eq) x.property
      simpa [Xbar, K2bar, Abar, π] using hx)
  have hA_le_X : A ≤ X := by
    intro a ha
    rw [hX_eq]
    change π a ∈ Xbar
    exact (le_sup_right : Abar ≤ K2bar ⊔ Abar)
      (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
  have hTXbar_eq : (TX : Subgroup X).map piX = AX := by
    apply (Subgroup.map_subtype_inj (H := Xbar)).mp
    calc
      ((TX : Subgroup X).map piX).map Xbar.subtype =
          ((TX : Subgroup X).map X.subtype).map π := by
            rw [Subgroup.map_map, Subgroup.map_map]
            rfl
      _ = (pCore q Q ⊔ A).map π := by rw [hTX_map_eq]
      _ = Abar := by simp [Abar, π, Subgroup.map_sup]
      _ = AX.map Xbar.subtype := by
        symm
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2]
        exact le_sup_right
  have hAbar_eq : (A.subgroupOf X).map piX = AX := by
    apply (Subgroup.map_subtype_inj (H := Xbar)).mp
    calc
      ((A.subgroupOf X).map piX).map Xbar.subtype =
          ((A.subgroupOf X).map X.subtype).map π := by
            rw [Subgroup.map_map, Subgroup.map_map]
            rfl
      _ = A.map π := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hA_le_X]
      _ = Abar := rfl
      _ = AX.map Xbar.subtype := by
        symm
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2]
        exact le_sup_right
  have hA_rank_mem :
      A.subgroupOf X ∈
        huppertRankThompsonAbelianSubgroups (G := X) (TX : Subgroup X) := by
    refine ⟨hA_le_TX, ?_, ?_⟩
    · let : IsMulCommutative A := hA_comm
      infer_instance
    · intro C hC_le_TX hC_comm
      have hCmap_le_S : C.map X.subtype ≤ (S : Subgroup Q) :=
        (Subgroup.map_mono hC_le_TX).trans hTX_map_le_S
      have hCmap_comm : IsMulCommutative (C.map X.subtype) := by
        let : IsMulCommutative C := hC_comm
        exact Subgroup.map_isMulCommutative (H := C) X.subtype
      have hglobal := hA_global_rank (C.map X.subtype) hCmap_le_S hCmap_comm
      calc
        generatorRank C = generatorRank (C.map X.subtype) :=
          hkt_generatorRank_eq_of_mulEquiv
            (Subgroup.equivMapOfInjective C X.subtype X.subtype_injective)
        _ ≤ generatorRank A := hglobal
        _ = generatorRank (A.subgroupOf X) :=
          hkt_generatorRank_eq_of_mulEquiv
            (Subgroup.subgroupOfEquivOfLe (H := A) (K := X) hA_le_X).symm
  let J : Subgroup X :=
    huppertRankThompsonSubgroup (G := X) (TX : Subgroup X)
  let Jbar : Subgroup Xbar := J.map piX
  have hA_le_J : A.subgroupOf X ≤ J := by
    exact le_sSup hA_rank_mem
  have hAX_le_Jbar : AX ≤ Jbar := by
    rw [← hAbar_eq]
    exact Subgroup.map_mono hA_le_J
  have hJ_le_TX : J ≤ (TX : Subgroup X) := by
    exact huppertRankThompsonSubgroup_le (G := X) (TX : Subgroup X)
  have hJbar_le_AX : Jbar ≤ AX := by
    rw [← hTXbar_eq]
    exact Subgroup.map_mono hJ_le_TX
  have hJ_p : IsPGroup q J := IsPGroup.to_le TX.isPGroup' hJ_le_TX
  have hJbar_p : IsPGroup q Jbar := hJ_p.map piX
  let JT : Subgroup TX :=
    huppertRankThompsonSubgroup (G := TX) (⊤ : Subgroup TX)
  have : JT.Characteristic :=
    hkt_huppertRankThompsonSubgroup_top_characteristic (G := TX)
  have hJT_map : JT.map (TX : Subgroup X).subtype = J := by
    simpa [JT, J] using
      hkt_huppertRankThompsonSubgroup_top_map_subtype
        (G := X) (TX : Subgroup X)
  have hTX_le_normalizer_J :
      (TX : Subgroup X) ≤ Subgroup.normalizer (J : Set X) := by
    have hle :=
      (Subgroup.le_normalizer (H := (TX : Subgroup X))).trans
        (hkt_normalizer_le_normalizer_map_subtype_of_characteristic
          (Q := X) (H := (TX : Subgroup X)) (K := JT))
    rw [hJT_map] at hle
    exact hle
  have hAX_le_normalizer_Jbar :
      AX ≤ Subgroup.normalizer (Jbar : Set Xbar) := by
    calc
      AX = (TX : Subgroup X).map piX := hTXbar_eq.symm
      _ ≤ (Subgroup.normalizer (J : Set X)).map piX :=
        Subgroup.map_mono hTX_le_normalizer_J
      _ ≤ Subgroup.normalizer (Jbar : Set Xbar) := by
        exact Subgroup.le_normalizer_map piX
  let : Kbar.Normal := hKbar_normal
  have hAbar_normalizes_Kbar :
      Abar ≤ Subgroup.normalizer (Kbar : Set (Q ⧸ pCore q Q)) :=
    Subgroup.le_normalizer_of_normal
  have hK2bar_le_Kbar : K2bar ≤ Kbar := by
    simpa [K2bar] using
      (Subgroup.commutator_le_left (H₁ := Kbar) (H₂ := Abar))
  have hAbar_p : IsPGroup q Abar := by
    simpa [Abar, π] using
      (IsPGroup.to_le (H := A) (K := (S : Subgroup Q))
        S.isPGroup' hA_le_S).map π
  have hAbar_Kbar_coprime :
      Nat.Coprime (Nat.card Abar) (Nat.card Kbar) := by
    rcases hAbar_p.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hKbar_coprime.pow_left n
  let : Group.IsSolvable Q := hsolvable
  let : Group.IsSolvable (Q ⧸ pCore q Q) := by infer_instance
  obtain ⟨r, hr, hKbar_elementary⟩ := by
    let : Group.IsSolvable Kbar := inferInstance
    exact minimalNormal_solvable_exists_isElementaryAbelian
      (G := Q ⧸ pCore q Q) (M := Kbar)
  let : Fact r.Prime := ⟨hr⟩
  let : IsElementaryAbelian r Kbar := hKbar_elementary
  have hK2bar_inf_cent_Abar :
      K2bar ⊓ Subgroup.centralizer (Abar : Set (Q ⧸ pCore q Q)) = ⊥ := by
    have : Subgroup.Normalizes Abar Kbar := ⟨hAbar_normalizes_Kbar⟩
    let Cfix : Subgroup Kbar := fixedPointSubgroup (↥Abar) (↥Kbar)
    let Ccomm : Subgroup Kbar :=
      commutatorAction (A := ↥Abar) (G := ↥Kbar)
    have hfixed_eq :
        Cfix = (subgroupCentralizerIn Kbar Abar).subgroupOf Kbar := by
      simpa [Cfix] using
        fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
          Kbar Abar hAbar_normalizes_Kbar
    have hcomm_map : Ccomm.map Kbar.subtype = K2bar := by
      simpa [Ccomm, K2bar] using
        commutatorAction_subgroup_conj_map_eq_commutator
          Kbar Abar hAbar_normalizes_Kbar
    have hKbar_solvable : Group.IsSolvable Kbar := by
      let : IsMulCommutative Kbar :=
        hKbar_elementary.toIsMulCommutative
      infer_instance
    have hKbar_comm : IsMulCommutative Kbar :=
      hKbar_elementary.toIsMulCommutative
    have hcompl : IsCompl Cfix Ccomm := by
      simpa [Cfix, Ccomm] using
        (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
          (G := Kbar) (A := Abar)
          hKbar_solvable hAbar_Kbar_coprime hKbar_comm)
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rcases hx with ⟨hxK2, hxCentA⟩
    have hxKbar : x ∈ Kbar := hK2bar_le_Kbar hxK2
    let xK : Kbar := ⟨x, hxKbar⟩
    have hxFix : xK ∈ Cfix := by
      rw [hfixed_eq]
      change (x : Q ⧸ pCore q Q) ∈ subgroupCentralizerIn Kbar Abar
      exact ⟨hxKbar, hxCentA⟩
    have hxComm : xK ∈ Ccomm := by
      have hxMap : x ∈ Ccomm.map Kbar.subtype := by
        simpa [hcomm_map] using hxK2
      rcases Subgroup.mem_map.mp hxMap with ⟨y, hyC, hyx⟩
      have hy_eq : y = xK := Subtype.ext hyx
      simpa [hy_eq] using hyC
    have hxbot : xK ∈ (⊥ : Subgroup Kbar) := by
      have hinf_bot : Cfix ⊓ Ccomm = ⊥ := hcompl.disjoint.eq_bot
      have hxinf : xK ∈ Cfix ⊓ Ccomm := ⟨hxFix, hxComm⟩
      simpa [hinf_bot] using hxinf
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)
  have hK2bar_coprime : Nat.Coprime q (Nat.card K2bar) :=
    Nat.Coprime.of_dvd_right
      (Subgroup.card_dvd_of_le hK2bar_le_Kbar) hKbar_coprime
  have hK2X_card : Nat.card K2X = Nat.card K2bar :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (H := K2bar) (K := Xbar) le_sup_left).toEquiv
  have hK2X_coprime : Nat.Coprime q (Nat.card K2X) := by
    rw [hK2X_card]
    exact hK2bar_coprime
  have hK2X_Jbar_inf : K2X ⊓ Jbar = ⊥ := by
    have hcop : Nat.Coprime (Nat.card K2X) (Nat.card Jbar) := by
      rcases hJbar_p.exists_card_eq with ⟨n, hn⟩
      rw [hn]
      exact hK2X_coprime.symm.pow_right n
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hK2bar_le_sup : K2bar ≤ Kbar ⊔ Abar := by
    simpa [K2bar] using commutator_le_sup Kbar Abar
  have hsup_le_normalizer_K2bar :
      Kbar ⊔ Abar ≤
        Subgroup.normalizer (K2bar : Set (Q ⧸ pCore q Q)) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hK2bar_le_sup).mp
      (by simpa [K2bar] using commutator_normal_in_sup Kbar Abar)
  have hXbar_le_normalizer_K2bar :
      Xbar ≤ Subgroup.normalizer (K2bar : Set (Q ⧸ pCore q Q)) := by
    exact sup_le (Subgroup.le_normalizer (H := K2bar))
      (le_sup_right.trans hsup_le_normalizer_K2bar)
  have hK2X_normal : K2X.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show K2bar ≤ Xbar from le_sup_left)).2 hXbar_le_normalizer_K2bar
  let : K2X.Normal := hK2X_normal
  have hK2X_sup_AX : K2X ⊔ AX = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact (Subgroup.subgroupOf_eq_top).2 (by simp)
  have hker_le_TX : piX.ker ≤ (TX : Subgroup X) := by
    intro z hz
    have hzval := congrArg Subtype.val (show piX z = 1 from hz)
    have hzcore : (z : Q) ∈ pCore q Q := by
      apply (QuotientGroup.eq_one_iff
        (N := pCore q Q) (x := (z : Q))).1
      simpa [piX, π] using hzval
    have hzmap : (z : Q) ∈ (TX : Subgroup X).map X.subtype := by
      rw [hTX_map_eq]
      exact (le_sup_left : pCore q Q ≤ pCore q Q ⊔ A) hzcore
    rcases Subgroup.mem_map.mp hzmap with ⟨t, ht, htz⟩
    have htz' : t = z := Subtype.ext htz
    simpa [htz'] using ht
  have hrank :
      Subgroup.normalizer (J : Set X) ≤ (TX : Subgroup X) := by
    intro n hn
    have hynorm : piX n ∈ Subgroup.normalizer (Jbar : Set Xbar) := by
      exact (Subgroup.le_normalizer_map (H := J) piX)
        (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
    have hytop : piX n ∈ K2X ⊔ AX := by
      rw [hK2X_sup_AX]
      exact Subgroup.mem_top _
    rcases (Subgroup.mem_sup_of_normal_left
      (s := K2X) (t := AX) (x := piX n)).1 hytop with
      ⟨k, hk, a, ha, hka⟩
    have hanorm : a ∈ Subgroup.normalizer (Jbar : Set Xbar) :=
      hAX_le_normalizer_Jbar ha
    have hknorm : k ∈ Subgroup.normalizer (Jbar : Set Xbar) := by
      have hprod :=
        (Subgroup.normalizer (Jbar : Set Xbar)).mul_mem hynorm
          ((Subgroup.normalizer (Jbar : Set Xbar)).inv_mem hanorm)
      rw [← hka] at hprod
      simpa [mul_assoc] using hprod
    have hkcent : k ∈ Subgroup.centralizer (AX : Set Xbar) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a' ha'
      have haJ : a' ∈ Jbar := hAX_le_Jbar ha'
      have hcommK : ⁅k, a'⁆ ∈ K2X :=
        (Subgroup.commutator_le_left (H₁ := K2X) (H₂ := AX))
          (Subgroup.commutator_mem_commutator hk ha')
      have hcommJ : ⁅k, a'⁆ ∈ Jbar := by
        rw [commutatorElement_def]
        exact Jbar.mul_mem
          ((Subgroup.mem_normalizer_iff.mp hknorm a').1 haJ)
          (Jbar.inv_mem haJ)
      have hcommbot : ⁅k, a'⁆ ∈ (⊥ : Subgroup Xbar) := by
        rw [← hK2X_Jbar_inf]
        exact ⟨hcommK, hcommJ⟩
      exact (commutatorElement_eq_one_iff_mul_comm.mp
        (Subgroup.mem_bot.mp hcommbot)).symm
    have hkcent_ambient :
        (k : Q ⧸ pCore q Q) ∈
          Subgroup.centralizer (Abar : Set (Q ⧸ pCore q Q)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a' ha'
      let aX : Xbar := ⟨a', (le_sup_right : Abar ≤ K2bar ⊔ Abar) ha'⟩
      have haX : aX ∈ AX := by
        exact ha'
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hkcent aX haX)
    have hkbot_ambient :
        (k : Q ⧸ pCore q Q) ∈
          (⊥ : Subgroup (Q ⧸ pCore q Q)) := by
      rw [← hK2bar_inf_cent_Abar]
      exact ⟨hk, hkcent_ambient⟩
    have hkone : k = 1 := by
      apply Subtype.ext
      exact Subgroup.mem_bot.mp hkbot_ambient
    have hynAX : piX n ∈ AX := by
      rw [← hka, hkone, one_mul]
      exact ha
    rw [← hTXbar_eq] at hynAX
    rcases Subgroup.mem_map.mp hynAX with ⟨t, ht, htn⟩
    have hdker : n * t⁻¹ ∈ piX.ker := by
      rw [MonoidHom.mem_ker]
      simp [htn]
    have hdTX : n * t⁻¹ ∈ (TX : Subgroup X) := hker_le_TX hdker
    have hprod : (n * t⁻¹) * t ∈ (TX : Subgroup X) :=
      (TX : Subgroup X).mul_mem hdTX ht
    simpa [mul_assoc] using hprod
  exact by simpa [J] using hrank
/-- Extracted source-(i)/(o) obligation: choose the conjugate whose common
centralizer with `A` is trivial, retaining the conjugate index bound. -/
private theorem hkt_iv62_o_conjugate_centralizers_extracted
    (hA_le_S : A ≤ (S : Subgroup Q))
    (hKbar_normal : Kbar.Normal)
    (hKbar_minimal : IsMinimalNormal Kbar)
    (hKbar_ne_bot : Kbar ≠ ⊥)
    (hKbar_coprime : Nat.Coprime q (Nat.card Kbar))
    (hsolvable : Group.IsSolvable Q)
    (B : Subgroup Q)
    (hB_normal : B.Normal)
    (hB_le_center_core : B ≤ centerIn (G := Q) (pCore q Q : Subgroup Q))
    (hA_index :
      (((Subgroup.centralizer (A : Set Q)).comap B.subtype)).index ≤ q)
    (hcomm_sup_Abar_top :
      ⁅Kbar, A.map (QuotientGroup.mk' (pCore q Q))⁆ ⊔
          A.map (QuotientGroup.mk' (pCore q Q)) = ⊤)
    (RqprimeLayer : Subgroup Q)
    (hB_fixed_trivial :
      ∀ b : B,
        (b : Q) ∈ Subgroup.centralizer (RqprimeLayer : Set Q) →
          (b : Q) = 1) :
    ∃ x : Q,
      let Ax : Subgroup Q := A.map (MulAut.conj x).toMonoidHom
      (((Subgroup.centralizer (Ax : Set Q)).comap B.subtype)).index ≤ q ∧
        ∀ b : B,
          b ∈ (Subgroup.centralizer (A : Set Q)).comap B.subtype →
          b ∈ (Subgroup.centralizer (Ax : Set Q)).comap B.subtype →
          (b : Q) = 1 := by
  classical
  let π : Q →* Q ⧸ pCore q Q := QuotientGroup.mk' (pCore q Q)
  let Abar : Subgroup (Q ⧸ pCore q Q) := A.map π
  let K2bar : Subgroup (Q ⧸ pCore q Q) := ⁅Kbar, Abar⁆
  let P : Subgroup Q := pCore q Q ⊔ A
  let : Kbar.Normal := hKbar_normal
  have hAbar_p : IsPGroup q Abar := by
    simpa [Abar, π] using
      (IsPGroup.to_le (H := A) (K := (S : Subgroup Q))
        S.isPGroup' hA_le_S).map π
  have hK2bar_le_Kbar : K2bar ≤ Kbar := by
    simpa [K2bar] using
      (Subgroup.commutator_le_left (H₁ := Kbar) (H₂ := Abar))
  have hcomm_sup_top : K2bar ⊔ Abar = ⊤ := by
    simpa [K2bar, Abar, π] using hcomm_sup_Abar_top
  have hKbar_sup_Abar_top : Kbar ⊔ Abar = ⊤ := by
    apply top_unique
    rw [← hcomm_sup_top]
    exact sup_le (hK2bar_le_Kbar.trans le_sup_left) le_sup_right
  have hK2bar_normal : K2bar.Normal := by
    have hK2_le_sup : K2bar ≤ Kbar ⊔ Abar := by
      simpa [K2bar] using commutator_le_sup Kbar Abar
    have hsup_le_normalizer :
        Kbar ⊔ Abar ≤
          Subgroup.normalizer (K2bar : Set (Q ⧸ pCore q Q)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK2_le_sup).mp
        (by simpa [K2bar] using commutator_normal_in_sup Kbar Abar)
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    simpa [hKbar_sup_Abar_top] using hsup_le_normalizer
  have hK2bar_ne_bot : K2bar ≠ ⊥ := by
    intro hK2_bot
    have hAbar_top : Abar = ⊤ := by
      simpa [hK2_bot] using hcomm_sup_top
    have hquotient_p : IsPGroup q (Q ⧸ pCore q Q) := by
      rw [hAbar_top] at hAbar_p
      exact hAbar_p.of_equiv Subgroup.topEquiv
    have hKbar_p : IsPGroup q Kbar :=
      hquotient_p.to_subgroup Kbar
    exact hKbar_ne_bot
      (section8_eq_bot_of_isPGroup_of_coprime hKbar_p hKbar_coprime)
  have hK2bar_eq_Kbar : K2bar = Kbar := by
    let : K2bar.Normal := hK2bar_normal
    rcases hKbar_minimal.minimal K2bar hK2bar_le_Kbar with hbot | htop
    · exact False.elim (hK2bar_ne_bot hbot)
    · exact htop
  have hKbar_Abar_coprime :
      Nat.Coprime (Nat.card Kbar) (Nat.card Abar) := by
    rcases hAbar_p.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hKbar_coprime.symm.pow_right n
  have hKbar_inf_Abar : Kbar ⊓ Abar = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hKbar_Abar_coprime).eq_bot
  have hP_map : P.map π = Abar := by
    simp [P, Abar, π, Subgroup.map_sup]
  have hP_comap : Abar.comap π = P := by
    dsimp [Abar, P, π]
    exact QuotientGroup.comap_map_mk' (pCore q Q) A
  let : Group.IsSolvable Q := hsolvable
  let : Group.IsSolvable (Q ⧸ pCore q Q) := by infer_instance
  obtain ⟨r, hr, hKbar_elementary⟩ := by
    let : Group.IsSolvable Kbar := inferInstance
    exact minimalNormal_solvable_exists_isElementaryAbelian
      (G := Q ⧸ pCore q Q) (M := Kbar)
  let : Fact r.Prime := ⟨hr⟩
  have hKbar_comm : IsMulCommutative Kbar :=
    hKbar_elementary.toIsMulCommutative
  have hAbar_maximal :
      ∀ Hbar : Subgroup (Q ⧸ pCore q Q),
        Abar ≤ Hbar → Hbar ≠ Abar → Hbar = ⊤ := by
    intro Hbar hAbar_le_Hbar hHbar_ne_Abar
    let Nbar : Subgroup (Q ⧸ pCore q Q) := Kbar ⊓ Hbar
    have hNbar_ne_bot : Nbar ≠ ⊥ := by
      intro hNbar_bot
      have hHbar_le_Abar : Hbar ≤ Abar := by
        intro h hh
        have htop_mem : h ∈ Kbar ⊔ Abar := by
          rw [hKbar_sup_Abar_top]
          exact Subgroup.mem_top h
        rcases (Subgroup.mem_sup_of_normal_left
            (s := Kbar) (t := Abar) (x := h)).1 htop_mem with
          ⟨k, hk, a, ha, hka⟩
        have haH : a ∈ Hbar := hAbar_le_Hbar ha
        have hkH : k ∈ Hbar := by
          have hprod : h * a⁻¹ ∈ Hbar :=
            Hbar.mul_mem hh (Hbar.inv_mem haH)
          rw [← hka] at hprod
          simpa [mul_assoc] using hprod
        have hk_bot : k ∈ (⊥ : Subgroup (Q ⧸ pCore q Q)) := by
          rw [← hNbar_bot]
          exact ⟨hk, hkH⟩
        have hk_one : k = 1 := Subgroup.mem_bot.mp hk_bot
        rw [← hka, hk_one, one_mul]
        exact ha
      exact hHbar_ne_Abar
        (le_antisymm hHbar_le_Abar hAbar_le_Hbar)
    have hHbar_le_normalizer_Nbar :
        Hbar ≤ Subgroup.normalizer (Nbar : Set (Q ⧸ pCore q Q)) := by
      have hsub_eq :
          Nbar.subgroupOf Hbar = Kbar.subgroupOf Hbar := by
        ext x
        simp [Nbar, Subgroup.mem_subgroupOf]
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer
        (show Nbar ≤ Hbar from inf_le_right)).mp
      rw [hsub_eq]
      exact hKbar_normal.subgroupOf Hbar
    have hKbar_le_normalizer_Nbar :
        Kbar ≤ Subgroup.normalizer (Nbar : Set (Q ⧸ pCore q Q)) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        have hnK : n ∈ Kbar := hn.1
        have hcomm : k * n = n * k :=
          setLike_mul_comm
            (s := Kbar) hk hnK
        have heq : k * n * k⁻¹ = n := by
          calc
            k * n * k⁻¹ = n * k * k⁻¹ := by rw [hcomm]
            _ = n := by simp [mul_assoc]
        simpa [heq] using hn
      · intro hconj
        have hnK : n ∈ Kbar := by
          have htmp :
              k⁻¹ * (k * n * k⁻¹) * k ∈ Kbar :=
            Kbar.mul_mem
              (Kbar.mul_mem (Kbar.inv_mem hk) hconj.1) hk
          simpa [mul_assoc] using htmp
        have hcomm : k * n = n * k :=
          setLike_mul_comm
            (s := Kbar) hk hnK
        have heq : k * n * k⁻¹ = n := by
          calc
            k * n * k⁻¹ = n * k * k⁻¹ := by rw [hcomm]
            _ = n := by simp [mul_assoc]
        simpa [heq] using hconj
    have hNbar_normal : Nbar.Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      apply top_unique
      rw [← hKbar_sup_Abar_top]
      exact sup_le hKbar_le_normalizer_Nbar
        (hAbar_le_Hbar.trans hHbar_le_normalizer_Nbar)
    let : Nbar.Normal := hNbar_normal
    have hNbar_eq_Kbar : Nbar = Kbar := by
      rcases hKbar_minimal.minimal Nbar inf_le_left with hbot | htop
      · exact False.elim (hNbar_ne_bot hbot)
      · exact htop
    apply top_unique
    rw [← hKbar_sup_Abar_top]
    exact sup_le
      (by
        rw [← hNbar_eq_Kbar]
        exact inf_le_right)
      hAbar_le_Hbar
  have hP_ne_top : P ≠ ⊤ := by
    intro hP_top
    have hP_map_top : (⊤ : Subgroup Q).map π = Abar := by
      simpa [hP_top] using hP_map
    have hAbar_top : Abar = ⊤ :=
      hP_map_top.symm.trans
        (Subgroup.map_top_of_surjective π
          (QuotientGroup.mk'_surjective (pCore q Q)))
    have hKbar_bot : Kbar = ⊥ := by
      simpa [hAbar_top] using hKbar_inf_Abar
    exact hKbar_ne_bot hKbar_bot
  have hP_not_normal : ¬ P.Normal := by
    intro hP_normal
    let : P.Normal := hP_normal
    have hAbar_normal : Abar.Normal := by
      simpa [hP_map] using
        hP_normal.map π (QuotientGroup.mk'_surjective (pCore q Q))
    let : Abar.Normal := hAbar_normal
    have hK2bar_le_Abar : K2bar ≤ Abar := by
      simpa [K2bar] using
        (Subgroup.commutator_le_right (H₁ := Kbar) (H₂ := Abar))
    have hK2bar_le_inf : K2bar ≤ Kbar ⊓ Abar :=
      fun _ hx => ⟨hK2bar_le_Kbar hx, hK2bar_le_Abar hx⟩
    have hK2bar_bot : K2bar = ⊥ :=
      le_bot_iff.mp (hK2bar_le_inf.trans (le_of_eq hKbar_inf_Abar))
    exact hK2bar_ne_bot hK2bar_bot
  have hnormalizer_P_ne_top :
      Subgroup.normalizer (P : Set Q) ≠ ⊤ := by
    intro htop
    exact hP_not_normal (Subgroup.normalizer_eq_top_iff.mp htop)
  obtain ⟨x, hx_not_normalizer⟩ :
      ∃ x : Q, x ∉ Subgroup.normalizer (P : Set Q) := by
    by_contra h
    apply hnormalizer_P_ne_top
    apply top_unique
    intro y _hy
    exact not_not.mp ((not_exists.mp h) y)
  let Ax : Subgroup Q := A.map (MulAut.conj x).toMonoidHom
  have hAx_not_le_P : ¬ Ax ≤ P := by
    intro hAx_le_P
    apply hx_not_normalizer
    have hcore_map_eq :
        (pCore q Q).map (MulAut.conj x).toMonoidHom = pCore q Q := by
      have htemp := Subgroup.Normal.conj_smul_eq_self x (pCore q Q)
      have htemp' : MulAut.conj x • (pCore q Q : Subgroup Q) =
          (pCore q Q).map (MulAut.conj x).toMonoidHom := by
        calc
          MulAut.conj x • (pCore q Q : Subgroup Q)
              = Subgroup.map ((MulDistribMulAction.toMonoidEnd (MulAut Q) Q) (MulAut.conj x)) (pCore q Q : Subgroup Q) := by
            simp [Subgroup.pointwise_smul_def]
          _ = Subgroup.map (MulAut.conj x : Q →* Q) (pCore q Q : Subgroup Q) := by
            apply congrArg (fun f : Q →* Q => Subgroup.map f (pCore q Q : Subgroup Q))
            ext y; simp
          _ = (pCore q Q).map (MulAut.conj x).toMonoidHom := rfl
      rw [htemp'] at htemp
      exact htemp
    have hP_map_conj_le :
        P.map (MulAut.conj x).toMonoidHom ≤ P := by
      change (pCore q Q ⊔ A).map (MulAut.conj x).toMonoidHom ≤ P
      rw [Subgroup.map_sup]
      exact sup_le
        (hcore_map_eq.le.trans le_sup_left)
        (by simpa [Ax] using hAx_le_P)
    have hcard_map :
        Nat.card (P.map (MulAut.conj x).toMonoidHom) = Nat.card P :=
      Subgroup.card_map_of_injective (MulAut.conj x).injective
    have hP_map_conj_eq :
        P.map (MulAut.conj x).toMonoidHom = P :=
      Subgroup.eq_of_le_of_card_ge hP_map_conj_le (by rw [hcard_map])
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hmem :
          (MulAut.conj x) y ∈
            P.map (MulAut.conj x).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hy
      rw [hP_map_conj_eq] at hmem
      exact hmem
    · intro hconj
      have hmem :
          (MulAut.conj x) y ∈
            P.map (MulAut.conj x).toMonoidHom := by
        rw [hP_map_conj_eq]
        exact hconj
      rcases Subgroup.mem_map.mp hmem with ⟨z, hz, hzy⟩
      have hzy' : z = y := (MulAut.conj x).injective hzy
      simpa [hzy'] using hz
  let H : Subgroup Q := P ⊔ Ax
  have hAbar_le_Hmap : Abar ≤ H.map π := by
    rw [← hP_map]
    exact Subgroup.map_mono (le_sup_left : P ≤ P ⊔ Ax)
  have hHmap_ne_Abar : H.map π ≠ Abar := by
    intro hHmap_eq
    apply hAx_not_le_P
    intro a ha
    have hmap_mem : π a ∈ H.map π :=
      Subgroup.mem_map_of_mem π
        ((le_sup_right : Ax ≤ P ⊔ Ax) ha)
    rw [hHmap_eq] at hmap_mem
    have hcomap_mem : a ∈ Abar.comap π := hmap_mem
    simpa [hP_comap] using hcomap_mem
  have hHmap_top : H.map π = ⊤ :=
    hAbar_maximal (H.map π) hAbar_le_Hmap hHmap_ne_Abar
  have hker_le_H : π.ker ≤ H := by
    simpa [π, QuotientGroup.ker_mk'] using
      (le_sup_left.trans le_sup_left :
        pCore q Q ≤ P ⊔ Ax)
  have hH_top : H = ⊤ := by
    have hcomap_map : (H.map π).comap π = H :=
      Subgroup.comap_map_eq_self hker_le_H
    rw [hHmap_top] at hcomap_map
    simpa using hcomap_map.symm
  let : B.Normal := hB_normal
  let CA : Subgroup B :=
    (Subgroup.centralizer (A : Set Q)).comap B.subtype
  let CAx : Subgroup B :=
    (Subgroup.centralizer (Ax : Set Q)).comap B.subtype
  let eB : MulAut B := MulAut.conjNormal (H := B) x
  have hCA_map : CA.map eB.toMonoidHom = CAx := by
    ext b
    constructor
    · intro hb
      rcases Subgroup.mem_map.mp hb with ⟨b0, hb0, hb0b⟩
      have hb_eq : eB b0 = b := hb0b
      change (b : Q) ∈ Subgroup.centralizer (Ax : Set Q)
      rw [← hb_eq, Subgroup.mem_centralizer_iff]
      intro ax hax
      rcases Subgroup.mem_map.mp hax with ⟨a, ha, rfl⟩
      have hb0_cent :
          (b0 : Q) ∈ Subgroup.centralizer (A : Set Q) :=
        Subgroup.mem_subgroupOf.mp hb0
      have hcomm :
          a * (b0 : Q) = (b0 : Q) * a :=
        Subgroup.mem_centralizer_iff.mp hb0_cent a ha
      have hmap := congrArg (MulAut.conj x) hcomm
      simpa [eB, map_mul, MulAut.conjNormal_apply] using hmap
    · intro hb
      refine Subgroup.mem_map.mpr ⟨eB.symm b, ?_, by simp⟩
      change ((eB.symm b : B) : Q) ∈
        Subgroup.centralizer (A : Set Q)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hax : (MulAut.conj x) a ∈ Ax :=
        Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom ha
      have hb_cent :
          (b : Q) ∈ Subgroup.centralizer (Ax : Set Q) :=
        Subgroup.mem_subgroupOf.mp hb
      have hcomm :
          (MulAut.conj x) a * (b : Q) =
            (b : Q) * (MulAut.conj x) a :=
        Subgroup.mem_centralizer_iff.mp hb_cent
          ((MulAut.conj x) a) hax
      have hmap := congrArg (MulAut.conj x⁻¹) hcomm
      simpa [eB, map_mul, MulAut.conjNormal_symm_apply, mul_assoc] using hmap
  have hAx_index : CAx.index ≤ q := by
    have hindex_eq : CAx.index = CA.index := by
      rw [← hCA_map]
      exact Subgroup.index_map_equiv CA eB
    rw [hindex_eq]
    simpa [CA] using hA_index
  refine ⟨x, ?_, ?_⟩
  · simpa [Ax, CAx] using hAx_index
  · intro b hbA hbAx
    have hb_center_core :
        (b : Q) ∈ centerIn (G := Q) (pCore q Q : Subgroup Q) :=
      hB_le_center_core b.property
    have hcore_le_cent_b :
        pCore q Q ≤ Subgroup.centralizer ({(b : Q)} : Set Q) := by
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      exact (Subgroup.mem_centralizer_iff.mp hb_center_core.2 c hc).symm
    have hA_le_cent_b :
        A ≤ Subgroup.centralizer ({(b : Q)} : Set Q) := by
      have hbA' : (b : Q) ∈ Subgroup.centralizer (A : Set Q) := hbA
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      exact (Subgroup.mem_centralizer_iff.mp hbA' a ha).symm
    have hAx_le_cent_b :
        Ax ≤ Subgroup.centralizer ({(b : Q)} : Set Q) := by
      have hbAx' : (b : Q) ∈ Subgroup.centralizer (Ax : Set Q) := by
        have hbAx_cent : (b : Q) ∈ Subgroup.centralizer
            (((MulAut.conj x : Q → Q) '' (A : Set Q)) : Set Q) :=
          Subgroup.mem_subgroupOf.mp hbAx
        simpa [Ax] using hbAx_cent
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      exact (Subgroup.mem_centralizer_iff.mp hbAx' a ha).symm
    have hP_le_cent_b :
        P ≤ Subgroup.centralizer ({(b : Q)} : Set Q) := by
      dsimp [P]
      exact sup_le hcore_le_cent_b hA_le_cent_b
    have hH_le_cent_b :
        H ≤ Subgroup.centralizer ({(b : Q)} : Set Q) := by
      dsimp [H]
      exact sup_le hP_le_cent_b hAx_le_cent_b
    apply hB_fixed_trivial b
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrH : r ∈ H := by
      rw [hH_top]
      exact Subgroup.mem_top r
    have hr_cent_b :
        r ∈ Subgroup.centralizer ({(b : Q)} : Set Q) :=
      hH_le_cent_b hrH
    exact
      (Subgroup.mem_centralizer_iff.mp hr_cent_b
        (b : Q) (by simp)).symm

/-- Extracted source-(r) obligation.  The selected cyclic actor carries the
nonscalar-model property at selection time; the three structural properties
alone do not imply it. -/
private theorem hkt_iv62_r_cyclic_nonscalar_actor_extracted
    (hA_le_S : A ≤ (S : Subgroup Q))
    (hKbar_normal : Kbar.Normal)
    (hKbar_minimal : IsMinimalNormal Kbar)
    (hKbar_ne_bot : Kbar ≠ ⊥)
    (hKbar_coprime : Nat.Coprime q (Nat.card Kbar))
    (hsolvable : Group.IsSolvable Q)
    (Klayer RqprimeLayer B : Subgroup Q)
    (hKlayer_eq : Klayer = Kbar.comap (QuotientGroup.mk' (pCore q Q)))
    (hKlayer_normal : Klayer.Normal)
    (hRqprime_le_Klayer : RqprimeLayer ≤ Klayer)
    (hKlayer_eq_core_sup_Rqprime :
      Klayer = pCore q Q ⊔ RqprimeLayer)
    (hRqprime_coprime : Nat.Coprime q (Nat.card RqprimeLayer))
    (hcomm_sup_Abar_top :
      ⁅Kbar, A.map (QuotientGroup.mk' (pCore q Q))⁆ ⊔
          A.map (QuotientGroup.mk' (pCore q Q)) = ⊤)
    (hB_le_center_core : B ≤ centerIn (G := Q) (pCore q Q : Subgroup Q))
    (hB_centralizer : Subgroup.centralizer (B : Set Q) = pCore q Q)
    (hKlayer_not_centralizes_B : ¬ Klayer ≤ Subgroup.centralizer (B : Set Q)) :
    ∃ C0 : Subgroup Q,
      IsCyclic C0 ∧
        Nat.Coprime q (Nat.card C0) ∧
          ∀ (hBnorm : B.Normal)
            (coord : Additive B ≃+ (Fin 2 → ZMod q))
            (rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q))),
            rho.ker = pCore q Q →
            (letI : B.Normal := hBnorm
              ∀ g : Q, ∀ b : B,
                coord (Additive.ofMul ((MulAut.conjNormal (H := B) g) b)) =
                  rho g (coord (Additive.ofMul b))) →
            (∀ a : A, ∀ d : C0,
              Commute
                (rho ((a : Q) * (d : Q) * (a : Q)⁻¹))
                (rho (d : Q))) ∧
              ∃ c : Q,
                C0 = Subgroup.zpowers c ∧
                  ∀ μ : ZMod q,
                    (rho c).toLinearMap ≠
                      μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q)) := by
  classical
  let π : Q →* Q ⧸ pCore q Q := QuotientGroup.mk' (pCore q Q)
  let Abar : Subgroup (Q ⧸ pCore q Q) := A.map π
  let K2bar : Subgroup (Q ⧸ pCore q Q) := ⁅Kbar, Abar⁆
  let : Kbar.Normal := hKbar_normal
  have hAbar_p : IsPGroup q Abar := by
    simpa [Abar, π] using
      (IsPGroup.to_le (H := A) (K := (S : Subgroup Q))
        S.isPGroup' hA_le_S).map π
  have hAbar_normalizes_Kbar :
      Abar ≤ Subgroup.normalizer (Kbar : Set (Q ⧸ pCore q Q)) :=
    Subgroup.le_normalizer_of_normal
  have hK2bar_le_Kbar : K2bar ≤ Kbar := by
    simpa [K2bar] using
      (Subgroup.commutator_le_left (H₁ := Kbar) (H₂ := Abar))
  have hcomm_sup_top : K2bar ⊔ Abar = ⊤ := by
    simpa [K2bar, Abar, π] using hcomm_sup_Abar_top
  have hKbar_sup_Abar_top : Kbar ⊔ Abar = ⊤ := by
    apply top_unique
    rw [← hcomm_sup_top]
    exact sup_le (hK2bar_le_Kbar.trans le_sup_left) le_sup_right
  have hK2bar_normal : K2bar.Normal := by
    have hK2_le_sup : K2bar ≤ Kbar ⊔ Abar := by
      simpa [K2bar] using commutator_le_sup Kbar Abar
    have hsup_le_normalizer :
        Kbar ⊔ Abar ≤
          Subgroup.normalizer (K2bar : Set (Q ⧸ pCore q Q)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK2_le_sup).mp
        (by simpa [K2bar] using commutator_normal_in_sup Kbar Abar)
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    simpa [hKbar_sup_Abar_top] using hsup_le_normalizer
  have hK2bar_ne_bot : K2bar ≠ ⊥ := by
    intro hK2_bot
    have hAbar_top : Abar = ⊤ := by
      simpa [hK2_bot] using hcomm_sup_top
    have hquotient_p : IsPGroup q (Q ⧸ pCore q Q) := by
      rw [hAbar_top] at hAbar_p
      exact hAbar_p.of_equiv Subgroup.topEquiv
    have hKbar_p : IsPGroup q Kbar := hquotient_p.to_subgroup Kbar
    exact hKbar_ne_bot
      (section8_eq_bot_of_isPGroup_of_coprime hKbar_p hKbar_coprime)
  have hK2bar_eq_Kbar : K2bar = Kbar := by
    let : K2bar.Normal := hK2bar_normal
    rcases hKbar_minimal.minimal K2bar hK2bar_le_Kbar with hbot | htop
    · exact False.elim (hK2bar_ne_bot hbot)
    · exact htop
  have hAbar_Kbar_coprime :
      Nat.Coprime (Nat.card Abar) (Nat.card Kbar) := by
    rcases hAbar_p.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hKbar_coprime.pow_left n
  let : Group.IsSolvable Q := hsolvable
  let : Group.IsSolvable (Q ⧸ pCore q Q) := by infer_instance
  obtain ⟨r, hr, hKbar_elementary⟩ := by
    let : Group.IsSolvable Kbar := inferInstance
    exact minimalNormal_solvable_exists_isElementaryAbelian
      (G := Q ⧸ pCore q Q) (M := Kbar)
  let : Fact r.Prime := ⟨hr⟩
  let : IsElementaryAbelian r Kbar := hKbar_elementary
  have hKbar_comm : IsMulCommutative Kbar :=
    hKbar_elementary.toIsMulCommutative
  have hK2bar_inf_cent_Abar :
      K2bar ⊓ Subgroup.centralizer (Abar : Set (Q ⧸ pCore q Q)) = ⊥ := by
    have : Subgroup.Normalizes Abar Kbar := ⟨hAbar_normalizes_Kbar⟩
    let Cfix : Subgroup Kbar := fixedPointSubgroup (↥Abar) (↥Kbar)
    let Ccomm : Subgroup Kbar :=
      commutatorAction (A := ↥Abar) (G := ↥Kbar)
    have hfixed_eq :
        Cfix = (subgroupCentralizerIn Kbar Abar).subgroupOf Kbar := by
      simpa [Cfix] using
        fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
          Kbar Abar hAbar_normalizes_Kbar
    have hcomm_map : Ccomm.map Kbar.subtype = K2bar := by
      simpa [Ccomm, K2bar] using
        commutatorAction_subgroup_conj_map_eq_commutator
          Kbar Abar hAbar_normalizes_Kbar
    have hKbar_solvable : Group.IsSolvable Kbar := by
      let : IsMulCommutative Kbar := hKbar_comm
      infer_instance
    have hcompl : IsCompl Cfix Ccomm := by
      simpa [Cfix, Ccomm] using
        (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
          (G := Kbar) (A := Abar)
          hKbar_solvable hAbar_Kbar_coprime hKbar_comm)
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rcases hx with ⟨hxK2, hxCentA⟩
    have hxKbar : x ∈ Kbar := hK2bar_le_Kbar hxK2
    let xK : Kbar := ⟨x, hxKbar⟩
    have hxFix : xK ∈ Cfix := by
      rw [hfixed_eq]
      change (x : Q ⧸ pCore q Q) ∈ subgroupCentralizerIn Kbar Abar
      exact ⟨hxKbar, hxCentA⟩
    have hxComm : xK ∈ Ccomm := by
      have hxMap : x ∈ Ccomm.map Kbar.subtype := by
        simpa [hcomm_map] using hxK2
      rcases Subgroup.mem_map.mp hxMap with ⟨y, hyC, hyx⟩
      have hy_eq : y = xK := Subtype.ext hyx
      simpa [hy_eq] using hyC
    have hxbot : xK ∈ (⊥ : Subgroup Kbar) := by
      have hinf_bot : Cfix ⊓ Ccomm = ⊥ := hcompl.disjoint.eq_bot
      have hxinf : xK ∈ Cfix ⊓ Ccomm := ⟨hxFix, hxComm⟩
      simpa [hinf_bot] using hxinf
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)
  have hcore_le_centralizer_B :
      pCore q Q ≤ Subgroup.centralizer (B : Set Q) :=
    hkt_iv62_p_pCore_le_commutator_layer_centralizer hB_le_center_core
  have hRqprime_not_centralizes_B :
      ¬ RqprimeLayer ≤ Subgroup.centralizer (B : Set Q) := by
    intro hRqprime_centralizes
    apply hKlayer_not_centralizes_B
    rw [hKlayer_eq_core_sup_Rqprime]
    exact sup_le hcore_le_centralizer_B hRqprime_centralizes
  obtain ⟨c, hcR, hc_not_centralizer⟩ :
      ∃ c : Q,
        c ∈ RqprimeLayer ∧ c ∉ Subgroup.centralizer (B : Set Q) :=
    Set.not_subset.mp hRqprime_not_centralizes_B
  let C0 : Subgroup Q := Subgroup.zpowers c
  have hc_order_coprime : Nat.Coprime q (orderOf c) :=
    Nat.Coprime.of_dvd_right
      (RqprimeLayer.orderOf_dvd_natCard hcR) hRqprime_coprime
  refine ⟨C0, by infer_instance, ?_, ?_⟩
  · simpa [C0, Nat.card_zpowers] using hc_order_coprime
  · intro hBnorm coord rho hker _hmodel
    refine ⟨?_, ⟨c, rfl, ?_⟩⟩
    · intro a d
      have hdR : (d : Q) ∈ RqprimeLayer :=
        (Subgroup.zpowers_le.2 hcR) d.property
      have hdK : (d : Q) ∈ Klayer := hRqprime_le_Klayer hdR
      have hconjK :
          (a : Q) * (d : Q) * (a : Q)⁻¹ ∈ Klayer :=
        hKlayer_normal.conj_mem (d : Q) hdK (a : Q)
      have hdbar : π (d : Q) ∈ Kbar := by
        rw [hKlayer_eq] at hdK
        exact hdK
      have hconjbar : π ((a : Q) * (d : Q) * (a : Q)⁻¹) ∈ Kbar := by
        rw [hKlayer_eq] at hconjK
        exact hconjK
      have hbar_comm :
          π ((a : Q) * (d : Q) * (a : Q)⁻¹) * π (d : Q) =
            π (d : Q) * π ((a : Q) * (d : Q) * (a : Q)⁻¹) :=
        setLike_mul_comm
          (s := Kbar) hconjbar hdbar
      have hquot_commutator :
          π ⁅(a : Q) * (d : Q) * (a : Q)⁻¹, (d : Q)⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hbar_comm
      have hcomm_core :
          ⁅(a : Q) * (d : Q) * (a : Q)⁻¹, (d : Q)⁆ ∈ pCore q Q := by
        apply (QuotientGroup.eq_one_iff
          (N := pCore q Q)
          (x := ⁅(a : Q) * (d : Q) * (a : Q)⁻¹, (d : Q)⁆)).1
        calc
          π (⁅(a : Q) * (d : Q) * (a : Q)⁻¹, (d : Q)⁆)
              = ⁅π ((a : Q) * (d : Q) * (a : Q)⁻¹), π (d : Q)⁆ := by simp
          _ = 1 := hquot_commutator
      have hmemker :
          ⁅(a : Q) * (d : Q) * (a : Q)⁻¹, (d : Q)⁆ ∈ rho.ker := by
        rw [hker]
        exact hcomm_core
      have hrho_commutator :
          ⁅rho ((a : Q) * (d : Q) * (a : Q)⁻¹), rho (d : Q)⁆ = 1 := by
        have hmap_one :
            rho ⁅(a : Q) * (d : Q) * (a : Q)⁻¹, (d : Q)⁆ = 1 := by
          simpa [MonoidHom.mem_ker] using hmemker
        simpa only [map_commutatorElement] using hmap_one
      change
        rho ((a : Q) * (d : Q) * (a : Q)⁻¹) * rho (d : Q) =
          rho (d : Q) * rho ((a : Q) * (d : Q) * (a : Q)⁻¹)
      exact commutatorElement_eq_one_iff_mul_comm.mp hrho_commutator
    · intro μ hscalar
      have hscalar_apply :
          ∀ v : Fin 2 → ZMod q, rho c v = μ • v := by
        intro v
        have hv := congrArg
          (fun f : Module.End (ZMod q) (Fin 2 → ZMod q) => f v) hscalar
        simpa using hv
      have hcbarK2 : π c ∈ K2bar := by
        rw [hK2bar_eq_Kbar]
        have hcK : c ∈ Klayer := hRqprime_le_Klayer hcR
        rw [hKlayer_eq] at hcK
        exact hcK
      have hcbarCent :
          π c ∈ Subgroup.centralizer (Abar : Set (Q ⧸ pCore q Q)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro abar habar
        rcases Subgroup.mem_map.mp habar with ⟨a, haA, rfl⟩
        have hrho_comm : Commute (rho c) (rho a) := by
          change rho c * rho a = rho a * rho c
          apply LinearEquiv.toLinearMap_injective
          apply LinearMap.ext
          intro v
          change rho c (rho a v) = rho a (rho c v)
          rw [hscalar_apply, hscalar_apply]
          exact (map_smul (rho a) μ v).symm
        have hmap_one : rho ⁅c, a⁆ = 1 := by
          rw [map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr hrho_comm.eq
        have hcomm_core : ⁅c, a⁆ ∈ pCore q Q := by
          have hmemker : ⁅c, a⁆ ∈ rho.ker := by
            simpa [MonoidHom.mem_ker] using hmap_one
          rw [hker] at hmemker
          exact hmemker
        have hquot_one : π ⁅c, a⁆ = 1 := by
          apply (QuotientGroup.eq_one_iff
            (N := pCore q Q) (x := ⁅c, a⁆)).2
          exact hcomm_core
        have hquot_commutator : ⁅π c, π a⁆ = 1 := by
          simpa only [map_commutatorElement] using hquot_one
        exact (commutatorElement_eq_one_iff_mul_comm.mp hquot_commutator).symm
      have hcbarBot : π c ∈ (⊥ : Subgroup (Q ⧸ pCore q Q)) := by
        rw [← hK2bar_inf_cent_Abar]
        exact ⟨hcbarK2, hcbarCent⟩
      have hcCore : c ∈ pCore q Q := by
        apply (QuotientGroup.eq_one_iff (N := pCore q Q) (x := c)).1
        exact Subgroup.mem_bot.mp hcbarBot
      exact hc_not_centralizer (by
        rw [hB_centralizer]
        exact hcCore)
end ExtractedIV62TerminalObligations

private theorem hkt_isPElement_mem_pCore_terminal_from_Wz
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (hnot_Qp : ¬ IsPGroup q Q)
    (hq2 : q ≠ 2) (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    (hproper_rec :
      ∀ (H : Subgroup Q) (T : Sylow q H),
        H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q
          (Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q H)
    (hsmall_rec :
      ∀ {R : Type u} [Group R] [Finite R] (T : Sylow q R),
        Nat.card R < Nat.card Q → q ∣ Nat.card R →
        HasNormalPComplement q
          (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q R)
    {U : Subgroup Q}
    (hU_ne_bot : U ≠ ⊥) (hU_p : IsPGroup q U)
    (hU_no_complement : ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))))
    (hUmax :
      ∀ W : Subgroup Q,
        W ≠ ⊥ →
        IsPGroup q W →
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
          Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q *
              (Nat.card Q + 1) + Nat.card W ≤
            Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q *
              (Nat.card Q + 1) + Nat.card U)
    (P : Sylow q (Subgroup.normalizer (U : Set Q)))
    (hUS : U < (S : Subgroup Q))
    (hUN_le_P :
      U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≤
        (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hcardUP :
      Nat.card U < Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hNtop : Subgroup.normalizer (U : Set Q) = ⊤)
    (hU_eq_core : U = pCore q Q)
    {z : Q} {Wz : Subgroup Q}
    (hWz_eq : Wz = pCore q Q ⊔ Subgroup.zpowers z)
    (hz_not_core : z ∉ pCore q Q)
    (hz_mem_S : z ∈ (S : Subgroup Q))
    (hWz_p : IsPGroup q Wz)
    (_hWz_le_S : Wz ≤ (S : Subgroup Q))
    (hS_le_normalizer_Wz : (S : Subgroup Q) ≤ Subgroup.normalizer (Wz : Set Q))
    (hnormalizer_Wz_comp : HasNormalPComplement q (↥(Subgroup.normalizer (Wz : Set Q))))
    (hz_comm_mod_core_S :
      ∀ s : Q, s ∈ (S : Subgroup Q) → ⁅z, s⁆ ∈ pCore q Q) :
    False := by
  let NWz : Subgroup Q := Subgroup.normalizer (Wz : Set Q)
  have hS_le_NWz : (S : Subgroup Q) ≤ NWz := by
    simpa [NWz] using hS_le_normalizer_Wz
  let SWz : Sylow q NWz := S.subtype hS_le_NWz
  let WzNWz : Subgroup NWz := Wz.subgroupOf NWz
  have hWz_le_NWz : Wz ≤ NWz := by
    simpa [NWz] using (Subgroup.le_normalizer (H := Wz))
  have hWzNWz_p : IsPGroup q WzNWz := by
    simpa [WzNWz] using
      hWz_p.of_equiv
        ((Subgroup.subgroupOfEquivOfLe (H := Wz) (K := NWz) hWz_le_NWz).symm)
  have hNWz_quotient_centralizer_p :
      IsPGroup q
        (NWz ⧸
          ((Subgroup.centralizer (Wz : Set Q)).subgroupOf NWz)) := by
    simpa [NWz] using
      hkt_normalizer_quotient_centralizer_isPGroup_of_hasNormalPComplement
        (Q := Q) (q := q) (U := Wz) hWz_p hnormalizer_Wz_comp
  have hNWz_map_top :
      (SWz : Subgroup NWz).map
          (QuotientGroup.mk'
            ((Subgroup.centralizer (Wz : Set Q)).subgroupOf NWz)) = ⊤ := by
    exact sylow_map_quotient_eq_top_of_quotient_isPGroup
      (G := NWz) (p := q) SWz
      ((Subgroup.centralizer (Wz : Set Q)).subgroupOf NWz)
      hNWz_quotient_centralizer_p
  have hNWz_decomp :
      ∀ n : NWz,
        ∃ s : NWz,
          s ∈ (SWz : Subgroup NWz) ∧
            n * s⁻¹ ∈ ((Subgroup.centralizer (Wz : Set Q)).subgroupOf NWz) := by
    intro n
    exact hkt_exists_sylow_div_mem_of_quotient_isPGroup
      (G := NWz) (p := q) SWz
      ((Subgroup.centralizer (Wz : Set Q)).subgroupOf NWz)
      hNWz_quotient_centralizer_p n
  have hz_comm_mod_core_NWz :
      ∀ n : NWz, ⁅z, (n : Q)⁆ ∈ pCore q Q := by
    intro n
    rcases hNWz_decomp n with ⟨s, hsSWz, hcs⟩
    let c : NWz := n * s⁻¹
    have hcC : (c : Q) ∈ Subgroup.centralizer (Wz : Set Q) := by
      simpa [c, Subgroup.mem_subgroupOf] using hcs
    have hsS : (s : Q) ∈ (S : Subgroup Q) := by
      simpa [SWz, Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hsSWz
    have hcomm_s : ⁅z, (s : Q)⁆ ∈ pCore q Q :=
      hz_comm_mod_core_S (s : Q) hsS
    have hzWz : z ∈ Wz := by
      rw [hWz_eq]
      exact (le_sup_right : Subgroup.zpowers z ≤ pCore q Q ⊔ Subgroup.zpowers z)
        (Subgroup.mem_zpowers z)
    have hcz : z * (c : Q) = (c : Q) * z :=
      (Subgroup.mem_centralizer_iff.mp hcC) z hzWz
    have hn_eq : (n : Q) = (c : Q) * (s : Q) := by
      simp [c, mul_assoc]
    have hcomm_eq : ⁅z, (n : Q)⁆ = (c : Q) * ⁅z, (s : Q)⁆ * (c : Q)⁻¹ := by
      rw [hn_eq, commutatorElement_def]
      calc
        z * ((c : Q) * (s : Q)) * z⁻¹ * (((c : Q) * (s : Q))⁻¹)
            = (c : Q) * z * (s : Q) * z⁻¹ * ((s : Q)⁻¹ * (c : Q)⁻¹) := by
              rw [← mul_assoc z (c : Q) (s : Q), hcz]
              group
        _ = (c : Q) * (z * (s : Q) * z⁻¹ * (s : Q)⁻¹) * (c : Q)⁻¹ := by
              group
    rw [hcomm_eq]
    exact (pCore_normal (G := Q) (p := q)).conj_mem ⁅z, (s : Q)⁆ hcomm_s (c : Q)
  have hWz_comm_mod_core_NWz :
      ∀ w : Q, w ∈ Wz → ∀ n : NWz, ⁅w, (n : Q)⁆ ∈ pCore q Q := by
    intro w hw n
    exact hkt_pCore_sup_zpowers_comm_mod_core_of_generator
      (Q := Q) (q := q) (z := z) (n := (n : Q)) (w := w)
      (hz_comm_mod_core_NWz n) (by simpa [hWz_eq] using hw)
  have hcore_le_Wz : pCore q Q ≤ Wz := by
    rw [hWz_eq]
    exact le_sup_left
  have hcore_le_NWz : pCore q Q ≤ NWz := hcore_le_Wz.trans hWz_le_NWz
  let CoreNWz : Subgroup NWz := (pCore q Q).subgroupOf NWz
  have hCoreNWz_normal : CoreNWz.Normal := by
    have hnorm_top : Subgroup.normalizer ((pCore q Q : Subgroup Q) : Set Q) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr (pCore_normal (G := Q) (p := q))
    have hNWz_le_norm_core : NWz ≤ Subgroup.normalizer ((pCore q Q : Subgroup Q) : Set Q) := by
      intro n hn
      simp [hnorm_top]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hcore_le_NWz).2 hNWz_le_norm_core
  let : CoreNWz.Normal := hCoreNWz_normal
  let Wzbar : Subgroup (NWz ⧸ CoreNWz) :=
    WzNWz.map (QuotientGroup.mk' CoreNWz)
  have hWzbar_le_center : Wzbar ≤ Subgroup.center (NWz ⧸ CoreNWz) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨w, hwWz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro nbar
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective CoreNWz nbar
    have hwQ : (w : Q) ∈ Wz := by
      simpa [WzNWz, Subgroup.mem_subgroupOf] using hwWz
    have hcomm_coreQ : ⁅(w : Q), (n : Q)⁆ ∈ pCore q Q :=
      hWz_comm_mod_core_NWz (w : Q) hwQ n
    have hcomm_CoreNWz : ⁅w, n⁆ ∈ CoreNWz := by
      apply Subgroup.mem_subgroupOf.mpr
      have h_eq : (↑⁅w, n⁆ : Q) = ⁅(w : Q), (n : Q)⁆ :=
        map_commutatorElement (NWz.subtype) w n
      rw [h_eq]
      exact hcomm_coreQ
    have hcomm_quot :
        ⁅QuotientGroup.mk' CoreNWz w, QuotientGroup.mk' CoreNWz n⁆ = 1 := by
      rw [← map_commutatorElement (QuotientGroup.mk' CoreNWz) w n]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact hcomm_CoreNWz
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm_quot).symm
  have hWzbar_p : IsPGroup q Wzbar := by
    simpa [Wzbar] using hWzNWz_p.map (QuotientGroup.mk' CoreNWz)
  have hz_mem_Wz : z ∈ Wz := by
    rw [hWz_eq]
    exact (le_sup_right : Subgroup.zpowers z ≤ pCore q Q ⊔ Subgroup.zpowers z)
      (Subgroup.mem_zpowers z)
  have hz_mem_NWz : z ∈ NWz := hWz_le_NWz hz_mem_Wz
  let zNWz : NWz := ⟨z, hz_mem_NWz⟩
  have hzNWz_mem_WzNWz : zNWz ∈ WzNWz := by
    simpa [zNWz, WzNWz, Subgroup.mem_subgroupOf] using hz_mem_Wz
  have hzbar_mem_Wzbar : QuotientGroup.mk' CoreNWz zNWz ∈ Wzbar :=
    Subgroup.mem_map.mpr ⟨zNWz, hzNWz_mem_WzNWz, rfl⟩
  have hzbar_ne_one : QuotientGroup.mk' CoreNWz zNWz ≠ 1 := by
    intro hzbar_one
    have hzCoreNWz : zNWz ∈ CoreNWz :=
      (QuotientGroup.eq_one_iff (N := CoreNWz) (x := zNWz)).1 hzbar_one
    exact hz_not_core (by
      simpa [zNWz, CoreNWz, Subgroup.mem_subgroupOf] using hzCoreNWz)
  have hWzbar_ne_bot : Wzbar ≠ ⊥ := by
    intro hbot
    have hzbar_bot : QuotientGroup.mk' CoreNWz zNWz ∈ (⊥ : Subgroup (NWz ⧸ CoreNWz)) := by
      simpa [hbot] using hzbar_mem_Wzbar
    exact hzbar_ne_one (by simpa using hzbar_bot)
  have hWzbar_normal : Wzbar.Normal := by
    refine ⟨?_⟩
    intro x hx g
    have hx_center : x ∈ Subgroup.center (NWz ⧸ CoreNWz) := hWzbar_le_center hx
    have hcomm := (Subgroup.mem_center_iff.mp hx_center) g
    have hconj_eq : g * x * g⁻¹ = x := by
      rw [hcomm]
      simp [mul_assoc]
    simpa [hconj_eq] using hx
  have hWzbar_le_pCore_quot : Wzbar ≤ pCore q (NWz ⧸ CoreNWz) := by
    exact le_sSup ⟨hWzbar_normal, hWzbar_p⟩
  have hpCore_quot_ne_bot : pCore q (NWz ⧸ CoreNWz) ≠ ⊥ := by
    intro hbot
    have hWzbar_le_bot : Wzbar ≤ ⊥ := by
      intro x hx
      have hx_core : x ∈ pCore q (NWz ⧸ CoreNWz) := hWzbar_le_pCore_quot hx
      simpa [hbot] using hx_core
    exact hWzbar_ne_bot (eq_bot_iff.mpr hWzbar_le_bot)
  let RNWz : Subgroup NWz :=
    (pCore q (NWz ⧸ CoreNWz)).comap (QuotientGroup.mk' CoreNWz)
  have hCoreNWz_le_RNWz : CoreNWz ≤ RNWz := by
    intro a ha
    change QuotientGroup.mk' CoreNWz a ∈ pCore q (NWz ⧸ CoreNWz)
    have ha_one : QuotientGroup.mk' CoreNWz a = 1 :=
      (QuotientGroup.eq_one_iff (N := CoreNWz) (x := a)).2 ha
    simp [ha_one]
  have hCoreNWz_lt_RNWz : CoreNWz < RNWz := by
    refine lt_of_le_of_ne hCoreNWz_le_RNWz ?_
    intro hEq
    let Rbar : Subgroup (NWz ⧸ CoreNWz) := pCore q (NWz ⧸ CoreNWz)
    have hRbar_le_bot : Rbar ≤ ⊥ := by
      intro x hx
      obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective CoreNWz x
      have hnRNWz : n ∈ RNWz := by
        simpa [RNWz, Rbar] using hx
      have hnCore : n ∈ CoreNWz := by
        simpa [hEq] using hnRNWz
      have hmk_one : QuotientGroup.mk' CoreNWz n = 1 :=
        (QuotientGroup.eq_one_iff (N := CoreNWz) (x := n)).2 hnCore
      simp [hmk_one]
    exact hpCore_quot_ne_bot (eq_bot_iff.mpr hRbar_le_bot)
  let RQ : Subgroup Q := RNWz.map NWz.subtype
  have hCoreNWz_card : Nat.card CoreNWz = Nat.card (pCore q Q) := by
    simpa [CoreNWz, NWz] using
      Nat.card_congr
        ((Subgroup.subgroupOfEquivOfLe (H := pCore q Q) (K := NWz) hcore_le_NWz).toEquiv)
  have hRNWz_card_eq_RQ : Nat.card RNWz = Nat.card RQ := by
    simpa [RQ] using
      (Subgroup.card_map_of_injective (K := RNWz) (f := NWz.subtype)
        Subtype.val_injective).symm
  have hcore_card_lt_RQ : Nat.card (pCore q Q) < Nat.card RQ := by
    calc
      Nat.card (pCore q Q) = Nat.card CoreNWz := hCoreNWz_card.symm
      _ < Nat.card RNWz := natCard_lt_of_subgroup_lt (G := NWz) hCoreNWz_lt_RNWz
      _ = Nat.card RQ := hRNWz_card_eq_RQ
  have hcore_le_RQ : pCore q Q ≤ RQ := by
    intro a ha
    let aNWz : NWz := ⟨a, hcore_le_NWz ha⟩
    have haCore : aNWz ∈ CoreNWz := by
      simpa [aNWz, CoreNWz, Subgroup.mem_subgroupOf] using ha
    have haRNWz : aNWz ∈ RNWz := hCoreNWz_le_RNWz haCore
    exact Subgroup.mem_map.mpr ⟨aNWz, haRNWz, rfl⟩
  have hCoreNWz_p : IsPGroup q CoreNWz := by
    simpa [CoreNWz, NWz] using
      (pCore_isPGroup (G := Q) (p := q)).of_equiv
        ((Subgroup.subgroupOfEquivOfLe (H := pCore q Q) (K := NWz) hcore_le_NWz).symm)
  have hRNWz_p : IsPGroup q RNWz := by
    have hker_p : IsPGroup q (QuotientGroup.mk' CoreNWz).ker := by
      have hker_eq : (QuotientGroup.mk' CoreNWz).ker = CoreNWz :=
        QuotientGroup.ker_mk' CoreNWz
      exact hCoreNWz_p.of_equiv (MulEquiv.subgroupCongr hker_eq.symm)
    simpa [RNWz] using
      (pCore_isPGroup (G := NWz ⧸ CoreNWz) (p := q)).comap_of_ker_isPGroup
        (QuotientGroup.mk' CoreNWz) hker_p
  have hRQ_p : IsPGroup q RQ := by
    simpa [RQ] using hRNWz_p.map NWz.subtype
  have hRQ_le_NWz : RQ ≤ NWz := by
    intro a ha
    rcases Subgroup.mem_map.mp ha with ⟨r, _hr, rfl⟩
    exact r.2
  have hRNWz_normal : RNWz.Normal := by
    simpa [RNWz] using
      (pCore_normal (G := NWz ⧸ CoreNWz) (p := q)).comap
        (QuotientGroup.mk' CoreNWz)
  have hNWz_le_normalizer_RQ : NWz ≤ Subgroup.normalizer (RQ : Set Q) := by
    intro n hn
    let nNWz : NWz := ⟨n, hn⟩
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro haRQ
      rcases Subgroup.mem_map.mp haRQ with ⟨r, hrR, hr_eq⟩
      refine Subgroup.mem_map.mpr
        ⟨(nNWz * r * nNWz⁻¹ : NWz), hRNWz_normal.conj_mem r hrR nNWz, ?_⟩
      calc
        (((nNWz * r * nNWz⁻¹ : NWz) : NWz) : Q) =
            n * (r : Q) * n⁻¹ := by simp [nNWz, mul_assoc]
        _ = n * a * n⁻¹ := by simpa [hr_eq]
    · intro hconjRQ
      rcases Subgroup.mem_map.mp hconjRQ with ⟨r, hrR, hr_eq⟩
      refine Subgroup.mem_map.mpr
        ⟨(nNWz⁻¹ * r * nNWz : NWz),
          by simpa using hRNWz_normal.conj_mem r hrR nNWz⁻¹, ?_⟩
      calc
        (((nNWz⁻¹ * r * nNWz : NWz) : NWz) : Q) =
            n⁻¹ * (r : Q) * n := by simp [nNWz, mul_assoc]
        _ = n⁻¹ * (n * a * n⁻¹) * n := by simpa [hr_eq]
        _ = a := by simp [mul_assoc]
  have hS_le_normalizer_RQ : (S : Subgroup Q) ≤ Subgroup.normalizer (RQ : Set Q) :=
    hS_le_normalizer_Wz.trans (by simpa [NWz] using hNWz_le_normalizer_RQ)
  have hRQ_le_S : RQ ≤ (S : Subgroup Q) :=
    hkt_normalized_pSubgroup_le_sylow (Q := Q) (q := q) S hRQ_p hS_le_normalizer_RQ
  have hWz_le_RQ : Wz ≤ RQ := by
    intro a haWz
    have haNWz : a ∈ NWz := hWz_le_NWz haWz
    let aNWz : NWz := ⟨a, haNWz⟩
    have haWzNWz : aNWz ∈ WzNWz := by
      simpa [aNWz, WzNWz, Subgroup.mem_subgroupOf] using haWz
    have hbar : QuotientGroup.mk' CoreNWz aNWz ∈ Wzbar :=
      Subgroup.mem_map.mpr ⟨aNWz, haWzNWz, rfl⟩
    have hpcore_bar : QuotientGroup.mk' CoreNWz aNWz ∈ pCore q (NWz ⧸ CoreNWz) :=
      hWzbar_le_pCore_quot hbar
    have haRNWz : aNWz ∈ RNWz := by
      simpa [RNWz] using hpcore_bar
    exact Subgroup.mem_map.mpr ⟨aNWz, haRNWz, rfl⟩
  let RQS : Subgroup (S : Subgroup Q) := RQ.subgroupOf (S : Subgroup Q)
  have hRQS_normal : RQS.Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hRQ_le_S).2 hS_le_normalizer_RQ
  have hWzS_le_RQS : Wz.subgroupOf (S : Subgroup Q) ≤ RQS := by
    intro a ha
    have haWz : (a : Q) ∈ Wz := by
      simpa [Subgroup.mem_subgroupOf] using ha
    simpa [RQS, Subgroup.mem_subgroupOf] using hWz_le_RQ haWz
  have hz_mem_RQ : z ∈ RQ := hWz_le_RQ hz_mem_Wz
  have hzS_mem_RQS : (⟨z, hz_mem_S⟩ : (S : Subgroup Q)) ∈ RQS := by
    simpa [RQS, Subgroup.mem_subgroupOf] using hz_mem_RQ
  have hcoreS_lt_RQS :
      Nat.card ((pCore q Q).subgroupOf (S : Subgroup Q)) < Nat.card RQS := by
    have hcoreS_card : Nat.card ((pCore q Q).subgroupOf (S : Subgroup Q)) =
        Nat.card (pCore q Q) := by
      exact Nat.card_congr
        ((Subgroup.subgroupOfEquivOfLe (H := pCore q Q) (K := (S : Subgroup Q))
          (hkt_pCore_le_sylow (Q := Q) (q := q) S)).toEquiv)
    have hRQS_card : Nat.card RQS = Nat.card RQ := by
      change Nat.card (RQ.subgroupOf (S : Subgroup Q)) = Nat.card RQ
      exact Nat.card_congr
        ((Subgroup.subgroupOfEquivOfLe (H := RQ) (K := (S : Subgroup Q))
          hRQ_le_S).toEquiv)
    calc
      Nat.card ((pCore q Q).subgroupOf (S : Subgroup Q)) = Nat.card (pCore q Q) := hcoreS_card
      _ < Nat.card RQ := hcore_card_lt_RQ
      _ = Nat.card RQS := hRQS_card.symm
  have hRQ_ne_bot : RQ ≠ ⊥ := by
    intro hbot
    have hcard_RQ_one : Nat.card RQ = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    have hcore_pos : 1 ≤ Nat.card (pCore q Q) := Nat.succ_le_of_lt Nat.card_pos
    have hcore_lt_one : Nat.card (pCore q Q) < 1 := by
      calc
        Nat.card (pCore q Q) < Nat.card RQ := hcore_card_lt_RQ
        _ = 1 := hcard_RQ_one
    exact (not_lt_of_ge hcore_pos) hcore_lt_one
  have hfactor_RQ :
      Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q ≤
        Nat.factorization (Nat.card (Subgroup.normalizer (RQ : Set Q))) q := by
    have hfactorS_Q :
        Nat.factorization (Nat.card (S : Subgroup Q)) q =
          Nat.factorization (Nat.card Q) q :=
      section8_factorization_card_sylow (G := Q) (p := q) S
    have hS_dvd_RQ_norm : Nat.card (S : Subgroup Q) ∣
        Nat.card (Subgroup.normalizer (RQ : Set Q)) :=
      Subgroup.card_dvd_of_le hS_le_normalizer_RQ
    have hfactorS_le_RQ_norm :
        Nat.factorization (Nat.card (S : Subgroup Q)) q ≤
          Nat.factorization (Nat.card (Subgroup.normalizer (RQ : Set Q))) q :=
      Nat.factorization_le_factorization_of_dvd_right
        hS_dvd_RQ_norm Nat.card_pos.ne' Nat.card_pos.ne'
    have hnormU_card : Nat.card (Subgroup.normalizer (U : Set Q)) = Nat.card Q := by
      rw [hNtop]
      simp
    calc
      Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q =
          Nat.factorization (Nat.card Q) q := by rw [hnormU_card]
      _ = Nat.factorization (Nat.card (S : Subgroup Q)) q := hfactorS_Q.symm
      _ ≤ Nat.factorization (Nat.card (Subgroup.normalizer (RQ : Set Q))) q :=
        hfactorS_le_RQ_norm
  have hnormalizer_RQ_comp : HasNormalPComplement q (↥(Subgroup.normalizer (RQ : Set Q))) := by
    by_contra hcompRQ
    have hscore :=
      hUmax RQ hRQ_ne_bot hRQ_p hcompRQ
    have hfactor_le :
        Nat.factorization (Nat.card (Subgroup.normalizer (RQ : Set Q))) q ≤
          Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q :=
      huppertIV62_normalizer_factorization_le_of_score_le
        (U := U) (V := RQ) hscore
    have hfactor_eq :
        Nat.factorization (Nat.card (Subgroup.normalizer (RQ : Set Q))) q =
          Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q :=
      le_antisymm hfactor_le hfactor_RQ
    have hcard_le : Nat.card RQ ≤ Nat.card U :=
      huppertIV62_card_le_of_factorization_eq_score_le
        (U := U) (V := RQ) hfactor_eq hscore
    exact (not_lt_of_ge hcard_le) (by simpa [hU_eq_core] using hcore_card_lt_RQ)
  have hnormalizer_RQ_ne_top : Subgroup.normalizer (RQ : Set Q) ≠ ⊤ := by
    intro htop
    have hRQ_normal : RQ.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hRQ_le_core : RQ ≤ pCore q Q := le_sSup ⟨hRQ_normal, hRQ_p⟩
    exact (not_lt_of_ge (Subgroup.card_le_of_le hRQ_le_core)) hcore_card_lt_RQ
  -- (g) Choose an abelian subgroup `A ≤ S` of maximal rank outside `O_q(Q)`,
  -- and among those choose one of minimal order.  This is the source's
  -- maximal-rank/minimal-order choice, built directly from the non-core
  -- element `z ∈ S` above.
  have step_g : Nonempty { A : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            (∀ C : Subgroup Q,
              C ≤ (S : Subgroup Q) → IsMulCommutative C →
                ¬ C ≤ pCore q Q →
                  generatorRank C ≤ generatorRank A) ∧
              (∀ C : Subgroup Q,
                C ≤ (S : Subgroup Q) → IsMulCommutative C →
                  ¬ C ≤ pCore q Q →
                    generatorRank C = generatorRank A →
                      Nat.card A ≤ Nat.card C) ∧
                ∀ C : Subgroup Q,
                  C ≤ (S : Subgroup Q) → IsMulCommutative C →
                    generatorRank C ≤ generatorRank A } := by
    classical
    have hglobal_noncore_rank_max :
        ∃ A : Subgroup Q,
          A ≤ (S : Subgroup Q) ∧
            IsMulCommutative A ∧
              ¬ A ≤ pCore q Q ∧
                ∀ C : Subgroup Q,
                  C ≤ (S : Subgroup Q) → IsMulCommutative C →
                    generatorRank C ≤ generatorRank A := by
      -- Huppert IV.6.2(g): `J(S) ⊄ O_q(Q)` gives an abelian
      -- subgroup `A ≤ S` with `d(A) = m(S)` and `A ⊄ O_q(Q)`.
      let Jrank : Subgroup Q :=
        huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q)
      have hnormalizer_rank_Jrank :
          HasNormalPComplement q (↥(Subgroup.normalizer (Jrank : Set Q))) := by
        simpa [Jrank] using hnormalizer_rank_dvd
      have hJrank_not_core : ¬ Jrank ≤ pCore q Q := by
        intro hJrank_le_core
        have hJrank_normalizer_top :
            Subgroup.normalizer (Jrank : Set Q) = ⊤ := by
          simpa [Jrank] using
            hkt_huppertRankThompsonSubgroup_normalizer_eq_top_of_le_pCore
              (Q := Q) (q := q) S hJrank_le_core
        have hQ_comp : HasNormalPComplement q Q :=
          hkt_hasNormalPComplement_of_subgroup_eq_top
            (Subgroup.normalizer (Jrank : Set Q)) hJrank_normalizer_top
            hnormalizer_rank_Jrank
        have hU_comp : HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))) := by
          let e : Subgroup.normalizer (U : Set Q) ≃* Q :=
            (MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv
          exact hasNormalPComplement_of_equiv (G := Q) (p := q) e.symm hQ_comp
        exact hU_no_complement hU_comp
      have hmax_rank_outside_core :
          ∃ A : Subgroup Q,
            A ∈ huppertRankThompsonAbelianSubgroups (G := Q) (S : Subgroup Q) ∧
              ¬ A ≤ pCore q Q := by
        by_contra hnone
        apply hJrank_not_core
        dsimp [Jrank, huppertRankThompsonSubgroup]
        refine sSup_le ?_
        intro A hA
        by_contra hA_not_core
        exact hnone ⟨A, hA, hA_not_core⟩
      rcases hmax_rank_outside_core with ⟨A, hA_rank, hA_not_core⟩
      exact ⟨A, hA_rank.1, hA_rank.2.1, hA_not_core, hA_rank.2.2⟩
    obtain ⟨Amax, hAmax_le_S, hAmax_comm, hAmax_not_core, hAmax_global_rank⟩ :=
      hglobal_noncore_rank_max
    let rankMaxCandidates : Set (Subgroup Q) :=
      {A | A ≤ (S : Subgroup Q) ∧ IsMulCommutative A ∧ ¬ A ≤ pCore q Q ∧
        generatorRank A = generatorRank Amax}
    have hrankMax_finite : rankMaxCandidates.Finite := Set.toFinite _
    have hrankMax_nonempty : rankMaxCandidates.Nonempty := by
      exact ⟨Amax, hAmax_le_S, hAmax_comm, hAmax_not_core, rfl⟩
    obtain ⟨Amin, hAmin_min⟩ :=
      hrankMax_finite.exists_minimalFor
        (f := fun A : Subgroup Q => Nat.card A) _ hrankMax_nonempty
    have hAmin_le_S : Amin ≤ (S : Subgroup Q) := hAmin_min.prop.1
    have hAmin_comm : IsMulCommutative Amin := hAmin_min.prop.2.1
    have hAmin_not_core : ¬ Amin ≤ pCore q Q := hAmin_min.prop.2.2.1
    have hAmin_rank_eq : generatorRank Amin = generatorRank Amax := hAmin_min.prop.2.2.2
    have hAmin_global_rank :
        ∀ C : Subgroup Q,
          C ≤ (S : Subgroup Q) → IsMulCommutative C →
            generatorRank C ≤ generatorRank Amin := by
      intro C hC_le hC_comm
      exact (hAmax_global_rank C hC_le hC_comm).trans_eq hAmin_rank_eq.symm
    have hAmin_rank :
        ∀ C : Subgroup Q,
          C ≤ (S : Subgroup Q) → IsMulCommutative C →
            ¬ C ≤ pCore q Q →
              generatorRank C ≤ generatorRank Amin := by
      intro C hC_le hC_comm _hC_not_core
      exact hAmin_global_rank C hC_le hC_comm
    have hAmin_card_min :
        ∀ C : Subgroup Q,
          C ≤ (S : Subgroup Q) → IsMulCommutative C →
            ¬ C ≤ pCore q Q →
              generatorRank C = generatorRank Amin →
                Nat.card Amin ≤ Nat.card C := by
      intro C hC_le hC_comm hC_not_core hC_rank
      have hC_rankMax : C ∈ rankMaxCandidates := by
        exact ⟨hC_le, hC_comm, hC_not_core, by
          rw [hC_rank, hAmin_rank_eq]⟩
      exact hAmin_min.le hC_rankMax
    exact ⟨⟨Amin, hAmin_le_S, hAmin_comm,
      hAmin_not_core, hAmin_rank, hAmin_card_min, hAmin_global_rank⟩⟩
  obtain ⟨A0_full⟩ := step_g
  rcases A0_full with
    ⟨A, hA_le_S, hA_commutative, hA_not_le_pCore,
      hA_rank_maximal, hA_card_minimal, hA_global_rank⟩
  let A0 : { A : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            ∀ C : Subgroup Q,
              C ≤ (S : Subgroup Q) → IsMulCommutative C →
                ¬ C ≤ pCore q Q →
                  generatorRank C ≤ generatorRank A } :=
    ⟨A, hA_le_S, hA_commutative, hA_not_le_pCore, hA_rank_maximal⟩
  -- (f) The reduced non-Burnside hard branch supplies the quotient normal
  -- `q`-complement used later in the book, and in particular solvability.
  obtain ⟨step_f_Kbar, step_f_Kbar_normal, step_f_Kbar_minimal,
      step_f_Kbar_ne_bot, step_f_Kbar_ne_top, step_f_Kbar_coprime,
      step_f_quot_q, step_f_quot_dvd, step_f_quot_pcore_bot,
      step_f_solvable⟩ :=
    hkt_iv62_f_reduced_nonburnside_corrected_structure
      (Q := Q) (q := q) (U := U)
      hcore_bot hnot_Qp hq2 S hq_dvd hnot_burnside hcentralizer_dvd
      hnormalizer_rank_dvd hproper_rec hsmall_rec hU_ne_bot hU_p hU_no_complement
      hUmax P hUS hUN_le_P hcardUP hNtop hU_eq_core
  let : step_f_Kbar.Normal := step_f_Kbar_normal
  let piCore : Q →* Q ⧸ pCore q Q := QuotientGroup.mk' (pCore q Q)
  let Klayer : Subgroup Q := step_f_Kbar.comap piCore
  have step_f_pCore_le_Klayer : pCore q Q ≤ Klayer := by
    intro x hx
    change piCore x ∈ step_f_Kbar
    have hx_one : piCore x = 1 :=
      (QuotientGroup.eq_one_iff (N := pCore q Q) (x := x)).2 hx
    simp [hx_one]
  have step_f_Klayer_normal : Klayer.Normal := by
    simpa [Klayer, piCore] using step_f_Kbar_normal.comap piCore
  let : Klayer.Normal := step_f_Klayer_normal
  let CoreKlayer : Subgroup Klayer := (pCore q Q).subgroupOf Klayer
  have step_f_CoreKlayer_normal : CoreKlayer.Normal := by
    simpa [CoreKlayer] using
      Subgroup.Normal.subgroupOf (pCore_normal (G := Q) (p := q)) Klayer
  let : CoreKlayer.Normal := step_f_CoreKlayer_normal
  let phiKlayer : Klayer →* step_f_Kbar :=
    { toFun := fun k => ⟨piCore (k : Q), k.property⟩
      map_one' := by
        apply Subtype.ext
        simp [piCore]
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp [piCore] }
  have step_f_phiKlayer_surj : Function.Surjective phiKlayer := by
    intro y
    rcases QuotientGroup.mk'_surjective (pCore q Q) (y : Q ⧸ pCore q Q) with ⟨x, hx⟩
    have hxK : x ∈ Klayer := by
      change piCore x ∈ step_f_Kbar
      have : piCore x = y := hx
      rw [this]
      exact y.property
    refine ⟨⟨x, hxK⟩, ?_⟩
    apply Subtype.ext
    dsimp [phiKlayer, piCore]
    exact hx
  have step_f_phiKlayer_ker : phiKlayer.ker = CoreKlayer := by
    ext x
    change phiKlayer x = 1 ↔ x ∈ CoreKlayer
    constructor
    · intro hx
      change (x : Q) ∈ pCore q Q
      have hxmk : piCore (x : Q) = 1 := Subtype.ext_iff.mp hx
      exact (QuotientGroup.eq_one_iff (N := pCore q Q) (x := (x : Q))).1 hxmk
    · intro hx
      apply Subtype.ext
      have hxCore : (x : Q) ∈ pCore q Q := by
        simpa [CoreKlayer, Subgroup.mem_subgroupOf] using hx
      exact (QuotientGroup.eq_one_iff (N := pCore q Q) (x := (x : Q))).2 hxCore
  let eKlayerKbar : Klayer ⧸ CoreKlayer ≃* step_f_Kbar :=
    (QuotientGroup.quotientMulEquivOfEq step_f_phiKlayer_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective phiKlayer step_f_phiKlayer_surj)
  have step_f_CoreKlayer_p : IsPGroup q CoreKlayer := by
    exact (pCore_isPGroup (G := Q) (p := q)).of_equiv
      ((Subgroup.subgroupOfEquivOfLe (H := pCore q Q) (K := Klayer)
        step_f_pCore_le_Klayer).symm)
  have step_f_CoreKlayer_index_eq_Kbar_card :
      CoreKlayer.index = Nat.card step_f_Kbar := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr eKlayerKbar.toEquiv
  have step_f_CoreKlayer_coprime_index :
      Nat.Coprime (Nat.card CoreKlayer) CoreKlayer.index := by
    rcases step_f_CoreKlayer_p.exists_card_eq with ⟨n, hn⟩
    rw [hn, step_f_CoreKlayer_index_eq_Kbar_card]
    exact Nat.Coprime.pow_left n step_f_Kbar_coprime
  obtain ⟨Rlayer, step_f_CoreKlayer_Rlayer_compl⟩ :=
    Subgroup.exists_right_complement'_of_coprime (N := CoreKlayer)
      step_f_CoreKlayer_coprime_index
  let eKlayerRlayer : Klayer ⧸ CoreKlayer ≃* Rlayer :=
    step_f_CoreKlayer_Rlayer_compl.symm.QuotientMulEquiv
  let RqprimeLayer : Subgroup Q := Rlayer.map Klayer.subtype
  have step_f_RqprimeLayer_le_Klayer : RqprimeLayer ≤ Klayer := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨r, _hr, rfl⟩
    exact (r : Klayer).property
  have step_f_Rlayer_card_eq_Kbar_card : Nat.card Rlayer = Nat.card step_f_Kbar := by
    calc
      Nat.card Rlayer = Nat.card (Klayer ⧸ CoreKlayer) := Nat.card_congr eKlayerRlayer.symm.toEquiv
      _ = Nat.card step_f_Kbar := Nat.card_congr eKlayerKbar.toEquiv
  have step_f_Rlayer_card_eq_RqprimeLayer_card :
      Nat.card Rlayer = Nat.card RqprimeLayer := by
    simpa [RqprimeLayer] using
      (Subgroup.card_map_of_injective (K := Rlayer) (f := Klayer.subtype)
        Subtype.val_injective).symm
  have step_f_RqprimeLayer_coprime_q : Nat.Coprime q (Nat.card RqprimeLayer) := by
    rw [← step_f_Rlayer_card_eq_RqprimeLayer_card, step_f_Rlayer_card_eq_Kbar_card]
    exact step_f_Kbar_coprime
  -- (h) In this reduced solvable branch, `O_q(Q)` is self-centralizing.
  have step_h_self_centralizing :
      Subgroup.centralizer ((pCore q Q : Subgroup Q) : Set Q) ≤ pCore q Q :=
    hkt_iv62_h_fitting_pCore_self_centralizing
      (Q := Q) (q := q) hcore_bot hnot_Qp step_f_solvable
  -- (k) Put `Z0 = Z(S)`.  Since the selected abelian subgroup is not contained
  -- in `O_q(Q)`, the Sylow subgroup is nontrivial and hence has nontrivial
  -- center; self-centralizing then forces the normal closure of `Z0` into
  -- `Z(O_q(Q))`.
  let Z0 : Subgroup Q := centerIn (G := Q) (S : Subgroup Q)
  have step_k_Z0_ne_bot : Z0 ≠ ⊥ := by
    have hS_ne_bot : (S : Subgroup Q) ≠ ⊥ := by
      intro hSbot
      exact A0.2.2.2.1 (by
        intro a ha
        have haS : a ∈ (S : Subgroup Q) := A0.2.1 ha
        have ha_bot : a ∈ (⊥ : Subgroup Q) := by
          simpa [hSbot] using haS
        have ha_one : a = 1 := Subgroup.mem_bot.mp ha_bot
        rw [ha_one]
        exact (pCore q Q).one_mem)
    simpa [Z0] using section8_centerIn_ne_bot_of_isPGroup S.isPGroup' hS_ne_bot
  have step_k_Z0_nontrivial_element : ∃ z0 : Z0, (z0 : Q) ≠ 1 := by
    by_contra hnone
    apply step_k_Z0_ne_bot
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx_ne_one
    exact hnone ⟨⟨x, hx⟩, hx_ne_one⟩
  have step_k_Z0_le_centralizer_pCore :
      Z0 ≤ Subgroup.centralizer ((pCore q Q : Subgroup Q) : Set Q) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxS : x ∈ (S : Subgroup Q) :=
      hkt_pCore_le_sylow (Q := Q) (q := q) S hx
    exact Subgroup.mem_centralizer_iff.mp hz.2 x hxS
  have step_k_normalClosure_Z0_le_center_pCore :
      Subgroup.normalClosure ((Z0 : Subgroup Q) : Set Q) ≤
        centerIn (G := Q) (pCore q Q : Subgroup Q) := by
    have : (Subgroup.centralizer ((pCore q Q : Subgroup Q) : Set Q)).Normal := by
      infer_instance
    have hclosure_le_cent :
        Subgroup.normalClosure ((Z0 : Subgroup Q) : Set Q) ≤
          Subgroup.centralizer ((pCore q Q : Subgroup Q) : Set Q) :=
      Subgroup.normalClosure_le_normal step_k_Z0_le_centralizer_pCore
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ((pCore q Q : Subgroup Q) : Set Q) :=
      hclosure_le_cent hx
    exact ⟨step_h_self_centralizing hxC, hxC⟩
  -- (l) Let `W` be the normal closure of `Z(S)`; then `W` is a nontrivial
  -- normal abelian subgroup of `Z(O_q(Q))`.
  let W : Subgroup Q := Subgroup.normalClosure ((Z0 : Subgroup Q) : Set Q)
  have step_l_W_eq : W = Subgroup.normalClosure ((Z0 : Subgroup Q) : Set Q) := rfl
  have step_l_center_sylow_le_W : centerIn (G := Q) (S : Subgroup Q) ≤ W := by
    intro x hx
    dsimp [W, Z0]
    exact Subgroup.subset_normalClosure hx
  have step_l_W_normal : W.Normal := by
    dsimp [W]
    infer_instance
  have step_l_W_ne_bot : W ≠ ⊥ := by
    rcases step_k_Z0_nontrivial_element with ⟨z0, hz0_ne_one⟩
    intro hW_bot
    have hzW : (z0 : Q) ∈ W := by
      dsimp [W]
      exact Subgroup.subset_normalClosure z0.property
    have hz_bot : (z0 : Q) ∈ (⊥ : Subgroup Q) := by
      simpa [hW_bot] using hzW
    exact hz0_ne_one (Subgroup.mem_bot.mp hz_bot)
  have step_l_W_le_center_pCore : W ≤ centerIn (G := Q) (pCore q Q : Subgroup Q) := by
    simpa [W] using step_k_normalClosure_Z0_le_center_pCore
  have step_l_W_comm : ∀ x y : W, x * y = y * x := by
    intro x y
    have hx_center : (x : Q) ∈ centerIn (G := Q) (pCore q Q : Subgroup Q) :=
      step_l_W_le_center_pCore x.property
    have hyCore : (y : Q) ∈ pCore q Q :=
      (step_l_W_le_center_pCore y.property).1
    have hyx : (y : Q) * (x : Q) = (x : Q) * (y : Q) :=
      Subgroup.mem_centralizer_iff.mp hx_center.2 (y : Q) hyCore
    exact Subtype.ext hyx.symm
  -- (m) Since `C_Q(W)` has a normal q-complement but `Q` itself is not a
  -- q-group, `Q/C_Q(W)` has a prime divisor `r ≠ q`; a corresponding cyclic
  -- `r`-subgroup acts nontrivially on `W`.
  let Cw : Subgroup Q := Subgroup.centralizer (W : Set Q)
  let : W.Normal := step_l_W_normal
  have : Cw.Normal := by
    dsimp [Cw]
    exact Subgroup.normal_centralizer (H := W)
  have step_m_Cw_le_CZS :
      Cw ≤ Subgroup.centralizer (centerIn (G := Q) (S : Subgroup Q) : Set Q) := by
    dsimp [Cw]
    exact Subgroup.centralizer_le
      (show ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q) ⊆
          (W : Set Q) from step_l_center_sylow_le_W)
  have step_m_Cw_comp : HasNormalPComplement q Cw :=
    hasNormalPComplement_of_le q step_m_Cw_le_CZS hcentralizer_dvd
  have step_m_quot_not_qgroup : ¬ IsPGroup q (Q ⧸ Cw) := by
    intro hquot
    have hQcomp : HasNormalPComplement q Q :=
      hkt_hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient
        (G := Q) (p := q) Cw hquot step_m_Cw_comp
    exact hnot_Qp
      (hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
        (Q := Q) (p := q) hcore_bot hQcomp)
  obtain ⟨r_actor, hr_actor_prime, hr_actor_ne_q, hr_actor_dvd⟩ :=
    hkt_exists_qprime_divisor_card_of_not_isPGroup q (Q ⧸ Cw) step_m_quot_not_qgroup
  have : Fact r_actor.Prime := ⟨hr_actor_prime⟩
  obtain ⟨x_actor, hx_actor_r, hx_actor_not_Cw⟩ :=
    hkt_exists_pElement_notMem_of_prime_dvd_quotient (G := Q) (N := Cw) hr_actor_dvd
  let actor : Subgroup Q := Subgroup.zpowers x_actor
  have step_m_actor_normalizes_W : actor ≤ Subgroup.normalizer (W : Set Q) := by
    have hnorm_top : Subgroup.normalizer (W : Set Q) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr step_l_W_normal
    intro y hy
    simp [hnorm_top]
  have step_m_actor_card_coprime_q : Nat.Coprime (Nat.card actor) q := by
    rcases hx_actor_r with ⟨n, hn⟩
    have hcop_rq : Nat.Coprime r_actor q :=
      (Nat.coprime_primes hr_actor_prime (Fact.out : Nat.Prime q)).2 hr_actor_ne_q
    have hcop : Nat.Coprime (r_actor ^ n) q := hcop_rq.pow_left n
    simpa [actor, Nat.card_zpowers, hn] using hcop
  have step_m_actor_not_centralizes_W : ¬ actor ≤ Subgroup.centralizer (W : Set Q) := by
    intro hle
    exact hx_actor_not_Cw (by
      have hx_mem : x_actor ∈ Subgroup.zpowers x_actor := Subgroup.mem_zpowers x_actor
      have hx_cent : x_actor ∈ Subgroup.centralizer (W : Set Q) := hle hx_mem
      simpa [Cw] using hx_cent)
  -- (n) Form the actual commutator carrier `[W,Q]` and its `Omega_1` layer.
  -- It is a nontrivial normal elementary abelian q-subgroup lying in
  -- `Z(O_q(Q))`, and the selected abelian subgroup normalizes it.
  let commCarrier : Subgroup Q := ⁅W, Klayer⁆
  have step_n_commCarrier_normal : commCarrier.Normal := by
    dsimp [commCarrier]
    infer_instance
  have step_n_commCarrier_le_W : commCarrier ≤ W := by
    dsimp [commCarrier]
    exact Subgroup.commutator_le_left (H₁ := W) (H₂ := Klayer)
  have step_n_commCarrier_le_center_pCore :
      commCarrier ≤ centerIn (G := Q) (pCore q Q : Subgroup Q) :=
    step_n_commCarrier_le_W.trans step_l_W_le_center_pCore
  have step_n_commCarrier_le_pCore : commCarrier ≤ pCore q Q :=
    fun _x hx => (step_n_commCarrier_le_center_pCore hx).1
  have step_n_commCarrier_comm : ∀ x y : commCarrier, x * y = y * x := by
    intro x y
    apply Subtype.ext
    have hx_center : (x : Q) ∈ centerIn (G := Q) (pCore q Q : Subgroup Q) :=
      step_n_commCarrier_le_center_pCore x.property
    have hy_core : (y : Q) ∈ pCore q Q := step_n_commCarrier_le_pCore y.property
    exact (Subgroup.mem_centralizer_iff.mp hx_center.2 (y : Q) hy_core).symm
  have step_n_commCarrier_ne_bot : commCarrier ≠ ⊥ := by
    intro hcomm_bot
    have hK_W_bot : ⁅Klayer, W⁆ = (⊥ : Subgroup Q) := by
      rw [Subgroup.commutator_comm Klayer W]
      simpa [commCarrier] using hcomm_bot
    have hK_le_Cw : Klayer ≤ Cw := by
      simpa [Cw] using
        (Subgroup.commutator_eq_bot_iff_le_centralizer
          (H₁ := Klayer) (H₂ := W)).1 hK_W_bot
    have hCore_le_Cw : pCore q Q ≤ Cw := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw_center : (w : Q) ∈ centerIn (G := Q) (pCore q Q : Subgroup Q) :=
        step_l_W_le_center_pCore hw
      exact (Subgroup.mem_centralizer_iff.mp hw_center.2 x hx).symm
    let Cwbar : Subgroup (Q ⧸ pCore q Q) := Cw.map piCore
    have hCwbar_normal : Cwbar.Normal := by
      dsimp [Cwbar]
      exact Subgroup.Normal.map (inferInstance : Cw.Normal) piCore
        (QuotientGroup.mk'_surjective (pCore q Q))
    let : Cwbar.Normal := hCwbar_normal
    have hKbar_le_Cwbar : step_f_Kbar ≤ Cwbar := by
      intro y hy
      rcases QuotientGroup.mk'_surjective (pCore q Q) y with ⟨x, rfl⟩
      have hxK : x ∈ Klayer := by
        change piCore x ∈ step_f_Kbar
        exact hy
      exact Subgroup.mem_map.mpr ⟨x, hK_le_Cw hxK, rfl⟩
    have hCwbar_quot_p : IsPGroup q ((Q ⧸ pCore q Q) ⧸ Cwbar) := by
      let e : ((Q ⧸ pCore q Q) ⧸ step_f_Kbar) ⧸ Cwbar.map (QuotientGroup.mk' step_f_Kbar) ≃*
          (Q ⧸ pCore q Q) ⧸ Cwbar :=
        QuotientGroup.quotientQuotientEquivQuotient
          (N := step_f_Kbar) (M := Cwbar) hKbar_le_Cwbar
      exact (step_f_quot_q.to_quotient (Cwbar.map (QuotientGroup.mk' step_f_Kbar))).of_equiv e
    have hquot_Cw_p : IsPGroup q (Q ⧸ Cw) := by
      let e : (Q ⧸ pCore q Q) ⧸ Cwbar ≃* Q ⧸ Cw :=
        QuotientGroup.quotientQuotientEquivQuotient
          (N := pCore q Q) (M := Cw) hCore_le_Cw
      exact hCwbar_quot_p.of_equiv e
    exact step_m_quot_not_qgroup hquot_Cw_p
  let : commCarrier.Normal := step_n_commCarrier_normal
  let Ωcomm : Subgroup commCarrier := omega₁ (G := commCarrier) (p := q)
  have : Ωcomm.Characteristic := by
    simpa [Ωcomm] using omega₁_characteristic (G := commCarrier) (p := q)
  have : ((Ωcomm.map commCarrier.subtype : Subgroup Q)).Normal := by
    infer_instance
  let B : Subgroup Q := Ωcomm.map commCarrier.subtype
  have step_n_B_eq_omega : B = (omega₁ (G := commCarrier) (p := q)).map commCarrier.subtype := by
    rfl
  have step_n_B_normal : B.Normal := by
    dsimp [B]
    infer_instance
  have step_n_B_le_center_pCore : B ≤ centerIn (G := Q) (pCore q Q : Subgroup Q) := by
    intro x hx
    rcases hx with ⟨d, _hd, rfl⟩
    exact step_n_commCarrier_le_center_pCore d.property
  have step_n_B_le_pCore : B ≤ pCore q Q := fun _x hx => (step_n_B_le_center_pCore hx).1
  have step_n_B_comm : ∀ x y : B, x * y = y * x := by
    intro x y
    rcases x.property with ⟨dx, _hdx, hdxeq⟩
    rcases y.property with ⟨dy, _hdy, hdyeq⟩
    apply Subtype.ext
    dsimp at hdxeq hdyeq
    calc
      ((x * y : B) : Q) = (dx : Q) * (dy : Q) := by simp [← hdxeq, ← hdyeq]
      _ = (dy : Q) * (dx : Q) := congrArg Subtype.val (step_n_commCarrier_comm dx dy)
      _ = ((y * x : B) : Q) := by simp [← hdxeq, ← hdyeq]
  have step_n_B_pow_eq_one : ∀ x : B, x ^ q = 1 := by
    have hD_comm_inst : IsMulCommutative commCarrier := ⟨⟨step_n_commCarrier_comm⟩⟩
    let : IsMulCommutative commCarrier := hD_comm_inst
    have : IsElementaryAbelian q Ωcomm := by
      simpa [Ωcomm] using IsElementaryAbelian.omega₁_of_isMulCommutative
        (G := commCarrier) (p := q)
    intro x
    rcases x.property with ⟨d, hd, hdeq⟩
    apply Subtype.ext
    have hdD_pow : (d : commCarrier) ^ q = 1 := by
      exact elemPow_eq_one_of_isElementaryAbelian (G := commCarrier) (A := Ωcomm) (d : commCarrier) hd
    have hdQ_pow : ((d : commCarrier) : Q) ^ q = 1 := by
      simpa using congrArg commCarrier.subtype hdD_pow
    dsimp at hdeq
    simpa [← hdeq] using hdQ_pow
  have step_n_commCarrier_isPGroup : IsPGroup q commCarrier :=
    IsPGroup.to_le (pCore_isPGroup (G := Q) (p := q)) step_n_commCarrier_le_pCore
  have step_n_q_dvd_commCarrier : q ∣ Nat.card commCarrier := by
    rcases IsPGroup.card_eq_or_dvd (p := q) (G := commCarrier) step_n_commCarrier_isPGroup with hcard | hdvd
    · have hcard_gt : 1 < Nat.card commCarrier :=
        (Subgroup.one_lt_card_iff_ne_bot (H := commCarrier)).2 step_n_commCarrier_ne_bot
      omega
    · exact hdvd
  have step_n_B_ne_bot : B ≠ ⊥ := by
    simpa [B, Ωcomm] using omega₁_map_subtype_ne_bot (M := commCarrier) (p := q) step_n_q_dvd_commCarrier
  have step_n_A_normalizes_B : A0.1 ≤ Subgroup.normalizer (B : Set Q) := by
    have htop : Subgroup.normalizer (B : Set Q) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr step_n_B_normal
    intro a _ha
    simp [htop]
  have step_n_B_mul_comm : IsMulCommutative B := by
    refine ⟨⟨?_⟩⟩
    exact step_n_B_comm
  have step_n_B_elementary : IsElementaryAbelian q B := by
    refine
      { toIsMulCommutative := step_n_B_mul_comm
        exponent_dvd_p := ?_ }
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.2 step_n_B_pow_eq_one
  have step_n_core_le_centralizer_W :
      pCore q Q ≤ Subgroup.centralizer (W : Set Q) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw_center :
        (w : Q) ∈ centerIn (G := Q) (pCore q Q : Subgroup Q) :=
      step_l_W_le_center_pCore hw
    exact (Subgroup.mem_centralizer_iff.mp hw_center.2 x hx).symm
  have step_n_comm_W_core_bot : ⁅W, pCore q Q⁆ = (⊥ : Subgroup Q) := by
    have hcoreW : ⁅pCore q Q, W⁆ = (⊥ : Subgroup Q) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := pCore q Q) (H₂ := W)).2 step_n_core_le_centralizer_W
    simpa [Subgroup.commutator_comm] using hcoreW
  have step_n_Klayer_eq_core_sup_Rqprime :
      Klayer = pCore q Q ⊔ RqprimeLayer := by
    have hmap_top :
        (⊤ : Subgroup Klayer).map Klayer.subtype = Klayer := by
      simpa [MonoidHom.range_eq_map] using
        (Klayer.range_subtype : Klayer.subtype.range = Klayer)
    have hmap_sup :
        (CoreKlayer ⊔ Rlayer).map Klayer.subtype =
          (pCore q Q ⊔ RqprimeLayer : Subgroup Q) := by
      rw [Subgroup.map_sup]
      congr 1
      simpa [CoreKlayer] using
        (Subgroup.map_subgroupOf_eq_of_le (H := pCore q Q) (K := Klayer)
          step_f_pCore_le_Klayer)
    have htop : (CoreKlayer ⊔ Rlayer).map Klayer.subtype = Klayer := by
      rw [step_f_CoreKlayer_Rlayer_compl.sup_eq_top]
      exact hmap_top
    exact htop.symm.trans hmap_sup
  have step_n_commCarrier_le_comm_W_Rqprime :
      commCarrier ≤ ⁅W, RqprimeLayer⁆ := by
    have : (pCore q Q).Normal := pCore_normal (G := Q) (p := q)
    dsimp [commCarrier]
    rw [step_n_Klayer_eq_core_sup_Rqprime]
    rw [Subgroup.commutator_le]
    intro w hw k hk
    rcases (Subgroup.mem_sup_of_normal_left
        (s := pCore q Q) (t := RqprimeLayer) (x := k)).1 hk with
      ⟨c, hc, r, hr, hcr⟩
    have hwr : ⁅w, r⁆ ∈ ⁅W, RqprimeLayer⁆ :=
      Subgroup.commutator_mem_commutator hw hr
    have hcomm_wc : w * c = c * w :=
      Subgroup.mem_centralizer_iff.mp (step_n_core_le_centralizer_W hc) w hw
    have hwrW : ⁅w, r⁆ ∈ W :=
      (Subgroup.commutator_le_left (H₁ := W) (H₂ := RqprimeLayer)) hwr
    have hcomm_wrc : ⁅w, r⁆ * c = c * ⁅w, r⁆ :=
      Subgroup.mem_centralizer_iff.mp
        (step_n_core_le_centralizer_W hc) ⁅w, r⁆ hwrW
    have hconj_wr : c * ⁅w, r⁆ * c⁻¹ = ⁅w, r⁆ := by
      calc
        c * ⁅w, r⁆ * c⁻¹ = ⁅w, r⁆ * c * c⁻¹ := by
          rw [← hcomm_wrc]
        _ = ⁅w, r⁆ := by simp [mul_assoc]
    have hk_eq : k = c * r := hcr.symm
    rw [hk_eq]
    convert hwr using 1
    calc
      ⁅w, c * r⁆ = c * ⁅w, r⁆ * c⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]
        rw [← mul_assoc w c r, hcomm_wc]
        simp [mul_assoc]
      _ = ⁅w, r⁆ := hconj_wr
  have step_n_comm_W_Rqprime_le_commCarrier :
      ⁅W, RqprimeLayer⁆ ≤ commCarrier := by
    dsimp [commCarrier]
    exact Subgroup.commutator_mono
      (show W ≤ W by rfl) step_f_RqprimeLayer_le_Klayer
  have step_n_commCarrier_eq_comm_W_Rqprime :
      commCarrier = ⁅W, RqprimeLayer⁆ :=
    le_antisymm step_n_commCarrier_le_comm_W_Rqprime
      step_n_comm_W_Rqprime_le_commCarrier
  have step_n_B_fixed_trivial :
      ∀ b : B,
        (b : Q) ∈ Subgroup.centralizer (RqprimeLayer : Set Q) →
          (b : Q) = 1 := by
    have step_n_W_comm : ∀ x y : W, x * y = y * x := by
      intro x y
      apply Subtype.ext
      have hx_center :
          (x : Q) ∈ centerIn (G := Q) (pCore q Q : Subgroup Q) :=
        step_l_W_le_center_pCore x.property
      have hy_core : (y : Q) ∈ pCore q Q :=
        (step_l_W_le_center_pCore y.property).1
      exact (Subgroup.mem_centralizer_iff.mp
        hx_center.2 (y : Q) hy_core).symm
    have hW_comm : IsMulCommutative W := ⟨⟨step_n_W_comm⟩⟩
    have hW_solvable : Group.IsSolvable W := by
      let : IsMulCommutative W := hW_comm
      infer_instance
    have hW_p : IsPGroup q W :=
      IsPGroup.to_le (pCore_isPGroup (G := Q) (p := q))
        (fun x hx => (step_l_W_le_center_pCore hx).1)
    have hcoprime :
        Nat.Coprime (Nat.card RqprimeLayer) (Nat.card W) := by
      rcases hW_p.exists_card_eq with ⟨n, hn⟩
      rw [hn]
      exact (Nat.Coprime.symm step_f_RqprimeLayer_coprime_q).pow_right n
    have : Subgroup.Normalizes RqprimeLayer W :=
      ⟨Subgroup.le_normalizer_of_normal⟩
    let Cfix : Subgroup W := fixedPointSubgroup (↥RqprimeLayer) (↥W)
    let Ccomm : Subgroup W :=
      commutatorAction (A := ↥RqprimeLayer) (G := ↥W)
    have hfixed_eq :
        Cfix = (subgroupCentralizerIn W RqprimeLayer).subgroupOf W := by
      simpa [Cfix] using
        fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
          W RqprimeLayer Subgroup.le_normalizer_of_normal
    have hcomm_map : Ccomm.map W.subtype = ⁅W, RqprimeLayer⁆ := by
      simpa [Ccomm] using
        commutatorAction_subgroup_conj_map_eq_commutator
          W RqprimeLayer Subgroup.le_normalizer_of_normal
    have hcompl : IsCompl Cfix Ccomm := by
      simpa [Cfix, Ccomm] using
        (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
          (G := W) (A := RqprimeLayer) hW_solvable hcoprime hW_comm)
    have hB_le_commCarrier : B ≤ commCarrier := by
      rintro _ ⟨d, _hd, rfl⟩
      exact d.property
    intro b hb_cent
    have hbW : (b : Q) ∈ W :=
      step_n_commCarrier_le_W (hB_le_commCarrier b.property)
    let bW : W := ⟨(b : Q), hbW⟩
    have hbFix : bW ∈ Cfix := by
      rw [hfixed_eq]
      change (b : Q) ∈ subgroupCentralizerIn W RqprimeLayer
      exact ⟨hbW, hb_cent⟩
    have hbComm : bW ∈ Ccomm := by
      have hbMap : (b : Q) ∈ Ccomm.map W.subtype := by
        rw [hcomm_map, ← step_n_commCarrier_eq_comm_W_Rqprime]
        exact hB_le_commCarrier b.property
      rcases Subgroup.mem_map.mp hbMap with ⟨y, hy, hyb⟩
      have hy_eq : y = bW := Subtype.ext hyb
      simpa [hy_eq] using hy
    have hbBot : bW ∈ (⊥ : Subgroup W) := by
      have hinf : Cfix ⊓ Ccomm = ⊥ := hcompl.disjoint.eq_bot
      have hbInf : bW ∈ Cfix ⊓ Ccomm := ⟨hbFix, hbComm⟩
      simpa [hinf] using hbInf
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hbBot)
  -- (o), reduced to the book's two conjugate-centralizer index bounds.
  have step_o_rank_at_most_two_of_relIndex
      (C1 C2 : Subgroup B)
      (hC1_index : C1.index ≤ q) (hC2_index : C2.index ≤ q)
      (hC12_inf_bot : C1 ⊓ C2 = (⊥ : Subgroup B)) :
      generatorRank B ≤ 2 := by
    exact hkt_iv62_o_commutator_layer_rank_at_most_two_of_relIndex
      (Q := Q) (q := q) (B := B) step_n_B_elementary
      C1 C2 hC1_index hC2_index hC12_inf_bot
  -- (p), easy half: since `B ≤ Z(O_q(Q))`, the `q`-core centralizes `B`.
  have step_p_Klayer_le_of_normal_not_q :
      ∀ C0 : Subgroup Q,
        C0.Normal → pCore q Q ≤ C0 → ¬ IsPGroup q C0 → Klayer ≤ C0 := by
    intro C0 hC0_normal hcore_le_C0 hC0_not_q
    classical
    let Cbar : Subgroup (Q ⧸ pCore q Q) := C0.map piCore
    have hCbar_normal : Cbar.Normal := by
      dsimp [Cbar]
      exact Subgroup.Normal.map hC0_normal piCore
        (QuotientGroup.mk'_surjective (pCore q Q))
    have hKbar_le_Cbar : step_f_Kbar ≤ Cbar := by
      by_contra hnot_le
      have hKbar_inf_Cbar_bot : step_f_Kbar ⊓ Cbar = (⊥ : Subgroup (Q ⧸ pCore q Q)) := by
        have : Cbar.Normal := hCbar_normal
        have hle : step_f_Kbar ⊓ Cbar ≤ step_f_Kbar := inf_le_left
        have : (step_f_Kbar ⊓ Cbar).Normal := inferInstance
        rcases step_f_Kbar_minimal.minimal (step_f_Kbar ⊓ Cbar) hle with hbot | htop
        · exact hbot
        · exact False.elim (hnot_le (by
            intro x hx
            have hxinf : x ∈ step_f_Kbar ⊓ Cbar := by
              simpa [htop] using hx
            exact hxinf.2))
      have hCbar_subgroupOf_bot : step_f_Kbar.subgroupOf Cbar = (⊥ : Subgroup Cbar) := by
        refine le_antisymm ?_ bot_le
        intro x hx
        have hxinf : (x : Q ⧸ pCore q Q) ∈ step_f_Kbar ⊓ Cbar := ⟨hx, x.property⟩
        have hxbot : (x : Q ⧸ pCore q Q) ∈ (⊥ : Subgroup (Q ⧸ pCore q Q)) := by
          simpa [hKbar_inf_Cbar_bot] using hxinf
        exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxbot))
      have hCbar_map_q_p : IsPGroup q (Cbar.map (QuotientGroup.mk' step_f_Kbar)) := by
        exact step_f_quot_q.to_subgroup (Cbar.map (QuotientGroup.mk' step_f_Kbar))
      have hCbar_quot_p : IsPGroup q (Cbar ⧸ step_f_Kbar.subgroupOf Cbar) := by
        exact hCbar_map_q_p.of_equiv (quotientSubgroupRangeEquiv Cbar step_f_Kbar).symm
      have hCbar_p : IsPGroup q Cbar := by
        let e : Cbar ⧸ step_f_Kbar.subgroupOf Cbar ≃* Cbar :=
          (QuotientGroup.quotientMulEquivOfEq hCbar_subgroupOf_bot).trans
            (QuotientGroup.quotientBot (G := Cbar))
        exact hCbar_quot_p.of_equiv e
      have hC0_quot_p : IsPGroup q (C0 ⧸ (pCore q Q).subgroupOf C0) := by
        let e : C0 ⧸ (pCore q Q).subgroupOf C0 ≃* Cbar :=
          quotientSubgroupRangeEquiv C0 (pCore q Q)
        exact hCbar_p.of_equiv e.symm
      have hcore_sub_p : IsPGroup q ((pCore q Q).subgroupOf C0) := by
        exact (pCore_isPGroup (G := Q) (p := q)).of_equiv
          ((Subgroup.subgroupOfEquivOfLe (H := pCore q Q) (K := C0) hcore_le_C0).symm)
      have : ((pCore q Q).subgroupOf C0).Normal := by
        exact Subgroup.Normal.subgroupOf (pCore_normal (G := Q) (p := q)) C0
      have hC0_p : IsPGroup q C0 :=
        hkt_isPGroup_of_normal_quotient ((pCore q Q).subgroupOf C0) hcore_sub_p hC0_quot_p
      exact hC0_not_q hC0_p
    intro x hx
    have hxmap : piCore x ∈ Cbar := hKbar_le_Cbar hx
    rcases hxmap with ⟨c, hcC0, hc_eq⟩
    have hxc_core : x * c⁻¹ ∈ pCore q Q := by
      have hquot : piCore (x * c⁻¹) = 1 := by
        calc
          piCore (x * c⁻¹) = piCore x * (piCore c)⁻¹ := by simp [piCore]
          _ = piCore x * (piCore x)⁻¹ := by rw [hc_eq]
          _ = 1 := by simp
      exact (QuotientGroup.eq_one_iff (N := pCore q Q) (x := x * c⁻¹)).1 hquot
    have hx_eq : x = (x * c⁻¹) * c := by simp
    rw [hx_eq]
    exact C0.mul_mem (hcore_le_C0 hxc_core) hcC0
  have step_p_pCore_le_centralizer_B :
      pCore q Q ≤ Subgroup.centralizer (B : Set Q) :=
    hkt_iv62_p_pCore_le_commutator_layer_centralizer
      (Q := Q) (q := q) (B := B) step_n_B_le_center_pCore
  have step_p_A_not_centralizes_B_of_centralizer_eq
      (step_p_centralizer_eq : Subgroup.centralizer (B : Set Q) = pCore q Q) :
      ¬ A0.1 ≤ Subgroup.centralizer (B : Set Q) := by
    intro hA_le_cent
    exact A0.2.2.2.1 (by
      intro a ha
      have ha_cent : a ∈ Subgroup.centralizer (B : Set Q) := hA_le_cent ha
      simpa [step_p_centralizer_eq] using ha_cent)
  have step_p_centralizer_eq_of_commutator
      (R : Subgroup Q)
      (hR_le_of_normal_not_q :
        ∀ C0 : Subgroup Q,
          C0.Normal → pCore q Q ≤ C0 → ¬ IsPGroup q C0 → R ≤ C0)
      (hB_commutator_R : ⁅B, R⁆ = B) :
      Subgroup.centralizer (B : Set Q) = pCore q Q := by
    classical
    let C0 : Subgroup Q := Subgroup.centralizer (B : Set Q)
    have hC0_normal : C0.Normal := by
      have : B.Normal := step_n_B_normal
      dsimp [C0]
      exact Subgroup.normal_centralizer (H := B)
    have hcentralizer_le_pCore : C0 ≤ pCore q Q := by
      intro x hxC0
      by_contra hx_not_pCore
      have hC0_not_q : ¬ IsPGroup q C0 := by
        intro hC0_q
        have hC0_le_pCore : C0 ≤ pCore q Q :=
          le_sSup ⟨hC0_normal, hC0_q⟩
        exact hx_not_pCore (hC0_le_pCore hxC0)
      have hR_le_C0 : R ≤ C0 :=
        hR_le_of_normal_not_q C0 hC0_normal step_p_pCore_le_centralizer_B hC0_not_q
      have hcomm_RB_bot : ⁅R, B⁆ = (⊥ : Subgroup Q) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := R) (H₂ := B)).2 hR_le_C0
      have hcomm_BR_bot : ⁅B, R⁆ = (⊥ : Subgroup Q) := by
        simpa [Subgroup.commutator_comm] using hcomm_RB_bot
      exact step_n_B_ne_bot (by
        rw [← hB_commutator_R, hcomm_BR_bot])
    exact le_antisymm hcentralizer_le_pCore step_p_pCore_le_centralizer_B
  have step_p_centralizer_eq_of_Klayer_not_centralized
      (hKlayer_not_le_centralizer : ¬ Klayer ≤ Subgroup.centralizer (B : Set Q)) :
      Subgroup.centralizer (B : Set Q) = pCore q Q := by
    classical
    let C0 : Subgroup Q := Subgroup.centralizer (B : Set Q)
    have hC0_normal : C0.Normal := by
      have : B.Normal := step_n_B_normal
      dsimp [C0]
      exact Subgroup.normal_centralizer (H := B)
    have hcentralizer_le_pCore : C0 ≤ pCore q Q := by
      intro x hxC0
      by_contra hx_not_pCore
      have hC0_not_q : ¬ IsPGroup q C0 := by
        intro hC0_q
        have hC0_le_pCore : C0 ≤ pCore q Q :=
          le_sSup ⟨hC0_normal, hC0_q⟩
        exact hx_not_pCore (hC0_le_pCore hxC0)
      have hK_le_C0 : Klayer ≤ C0 :=
        step_p_Klayer_le_of_normal_not_q C0 hC0_normal
          step_p_pCore_le_centralizer_B hC0_not_q
      exact hKlayer_not_le_centralizer hK_le_C0
    exact le_antisymm hcentralizer_le_pCore step_p_pCore_le_centralizer_B
  -- (q) is now a small consequence once the book's (o) rank bound and (p)
  -- centralizer equality have been established for this concrete `B`.
  have step_q_card_eq_of_rank_and_centralizer
      (step_o_rank_at_most_two : generatorRank B ≤ 2)
      (step_p_centralizer_eq : Subgroup.centralizer (B : Set Q) = pCore q Q) :
      Nat.card B = q ^ 2 := by
    exact hkt_iv62_q_preterminal_layer_card_eq_two_dimensional
      (Q := Q) (q := q) hq2 S A0.1 B A0.2.1 A0.2.2.1
      A0.2.2.2.1 A0.2.2.2.2 step_n_A_normalizes_B
      (step_p_A_not_centralizes_B_of_centralizer_eq step_p_centralizer_eq)
      step_n_B_normal step_n_B_le_pCore step_n_B_elementary
      step_o_rank_at_most_two step_p_centralizer_eq
  have step_r_terminal_contradiction_from_data
      (step_o_rank_at_most_two : generatorRank B ≤ 2)
      (step_p_centralizer_eq : Subgroup.centralizer (B : Set Q) = pCore q Q)
      (C0 : Subgroup Q) (hC0_cyclic : IsCyclic C0)
      (hC0_coprime : Nat.Coprime q (Nat.card C0))
      (hC0_model :
        ∀ (hBnorm : B.Normal)
          (coord : Additive B ≃+ (Fin 2 → ZMod q))
          (rho : Q →* ((Fin 2 → ZMod q) ≃ₗ[ZMod q] (Fin 2 → ZMod q))),
          rho.ker = pCore q Q →
          (let : B.Normal := hBnorm
            ∀ g : Q, ∀ b : B,
              coord (Additive.ofMul ((MulAut.conjNormal (H := B) g) b)) =
                rho g (coord (Additive.ofMul b))) →
          (∀ a : A0.1, ∀ d : C0,
            Commute
              (rho ((a : Q) * (d : Q) * (a : Q)⁻¹))
              (rho (d : Q))) ∧
            ∃ c : Q,
              C0 = Subgroup.zpowers c ∧
                ∀ μ : ZMod q,
                  (rho c).toLinearMap ≠
                    μ • (1 : Module.End (ZMod q) (Fin 2 → ZMod q))) :
      False := by
    classical
    have step_q_card : Nat.card B = q ^ 2 :=
      step_q_card_eq_of_rank_and_centralizer
        step_o_rank_at_most_two step_p_centralizer_eq
    let L : Σ A : Subgroup Q, { B : Subgroup Q //
      A ≤ (S : Subgroup Q) ∧
        IsMulCommutative A ∧
          ¬ A ≤ pCore q Q ∧
            A ≤ Subgroup.normalizer (B : Set Q) ∧
              ¬ A ≤ Subgroup.centralizer (B : Set Q) ∧
                B.Normal ∧
                  B ≤ pCore q Q ∧
                    IsElementaryAbelian q B ∧
                      Nat.card B = q ^ 2 ∧
                        Subgroup.centralizer (B : Set Q) = pCore q Q } :=
      ⟨A0.1, ⟨B,
        A0.2.1,
        A0.2.2.1,
        A0.2.2.2.1,
        step_n_A_normalizes_B,
        step_p_A_not_centralizes_B_of_centralizer_eq step_p_centralizer_eq,
        step_n_B_normal,
        step_n_B_le_pCore,
        step_n_B_elementary,
        step_q_card,
        step_p_centralizer_eq⟩⟩
    exact hkt_iv62_terminal_linear_contradiction
      (Q := Q) (q := q) (U := U)
      hcore_bot hnot_Qp hq2 S hq_dvd hnot_burnside hcentralizer_dvd
      hnormalizer_rank_dvd hproper_rec hsmall_rec hU_ne_bot hU_p hU_no_complement
      hUmax P hUS hUN_le_P hcardUP hNtop hU_eq_core
      L C0 hC0_cyclic hC0_coprime
      (by
        simpa [L] using hC0_model)
  -- (o) The source now needs the two conjugate centralizers in B whose
  -- indices are at most q and whose intersection is trivial.
  have step_o_data :
      ⁅step_f_Kbar, A0.1.map piCore⁆ ⊔ A0.1.map piCore = ⊤ ∧
        ∃ C1 C2 : Subgroup B,
          C1.index ≤ q ∧ C2.index ≤ q ∧ C1 ⊓ C2 = (⊥ : Subgroup B) := by
    classical
    let centInB (H : Subgroup Q) : Subgroup B :=
      (Subgroup.centralizer (H : Set Q)).comap B.subtype
    let interInB (H : Subgroup Q) : Subgroup B := H.comap B.subtype
    have step_o_inter_le_cent
        (H : Subgroup Q) (hH_comm : IsMulCommutative H) :
        interInB H ≤ centInB H := by
      intro b hb
      change (b : Q) ∈ Subgroup.centralizer (H : Set Q)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hbH : (b : Q) ∈ H :=
        Subgroup.mem_subgroupOf.mp hb
      exact (setLike_mul_comm (s := H) hbH ha).symm
    have step_o_index_of_inter
        (H : Subgroup Q) (hH_comm : IsMulCommutative H)
        (hinter : (interInB H).index ≤ q) :
        (centInB H).index ≤ q := by
      exact (Subgroup.index_antitone (step_o_inter_le_cent H hH_comm)).trans hinter

    have step_i_j_data :
        ⁅step_f_Kbar, A0.1.map piCore⁆ ⊔ A0.1.map piCore = ⊤ ∧
          (interInB A0.1).index ≤ q := by
      -- Huppert IV.6.2(i),(j): retain the quotient generation fact while
      -- proving that `A` loses at most one generator modulo `O_q(Q)`.
      have step_i_j_core :
          ⁅step_f_Kbar, A0.1.map piCore⁆ ⊔ A0.1.map piCore = ⊤ ∧
            generatorRank A0.1 ≤
              generatorRank (A0.1 ⊓ pCore q Q : Subgroup Q) + 1 := by
        let Y : Subgroup A0.1 := (A0.1 ⊓ pCore q Q).subgroupOf A0.1
        let : IsMulCommutative A0.1 := A0.2.2.1
        let : Y.Normal := Subgroup.normal_of_isMulCommutative Y
        have hsource_i_j :
            ⁅step_f_Kbar, A0.1.map piCore⁆ ⊔ A0.1.map piCore = ⊤ ∧
              IsCyclic (A0.1 ⧸ Y) := by
          classical
          let : Group.IsSolvable Q := step_f_solvable
          let : Group.IsSolvable (Q ⧸ pCore q Q) := by infer_instance
          let Abar : Subgroup (Q ⧸ pCore q Q) := A0.1.map piCore
          let K2bar : Subgroup (Q ⧸ pCore q Q) := ⁅step_f_Kbar, Abar⁆
          let Xbar : Subgroup (Q ⧸ pCore q Q) := K2bar ⊔ Abar
          let X : Subgroup Q := Xbar.comap piCore
          have hAbar_p : IsPGroup q Abar := by
            simpa [Abar, piCore] using
              (IsPGroup.to_le (H := A0.1) (K := (S : Subgroup Q))
                S.isPGroup' A0.2.1).map piCore
          have hAbar_comm : IsMulCommutative Abar := by
            let : IsMulCommutative A0.1 := A0.2.2.1
            simpa [Abar] using
              Subgroup.map_isMulCommutative (H := A0.1) piCore
          have hAbar_ne_bot : Abar ≠ ⊥ := by
            intro hAbar_bot
            apply A0.2.2.2.1
            intro a haA
            have hmap_bot : piCore a ∈ (⊥ : Subgroup (Q ⧸ pCore q Q)) := by
              rw [← hAbar_bot]
              exact Subgroup.mem_map.mpr ⟨a, haA, rfl⟩
            exact (QuotientGroup.eq_one_iff
              (N := pCore q Q) (x := a)).1 (Subgroup.mem_bot.mp hmap_bot)
          have hK2bar_le_Kbar : K2bar ≤ step_f_Kbar := by
            simpa [K2bar] using
              (Subgroup.commutator_le_left
                (H₁ := step_f_Kbar) (H₂ := Abar))
          have hAbar_normalizes_K2bar :
              Abar ≤ Subgroup.normalizer (K2bar : Set (Q ⧸ pCore q Q)) := by
            have hK2_le_sup : K2bar ≤ step_f_Kbar ⊔ Abar := by
              simpa [K2bar] using commutator_le_sup step_f_Kbar Abar
            have hsup_le :
                step_f_Kbar ⊔ Abar ≤ Subgroup.normalizer (K2bar : Set (Q ⧸ pCore q Q)) := by
              exact (Subgroup.normal_subgroupOf_iff_le_normalizer hK2_le_sup).mp
                (by simpa [K2bar] using commutator_normal_in_sup step_f_Kbar Abar)
            exact le_sup_right.trans hsup_le
          obtain ⟨r, hr, hKbar_elementary⟩ := by
            let : Group.IsSolvable step_f_Kbar := inferInstance
            exact minimalNormal_solvable_exists_isElementaryAbelian
              (G := Q ⧸ pCore q Q) (M := step_f_Kbar)
          let : Fact r.Prime := ⟨hr⟩
          let : IsElementaryAbelian r step_f_Kbar := hKbar_elementary
          let : CommGroup step_f_Kbar :=
            { mul_comm := fun a b =>
                hKbar_elementary.toIsMulCommutative.is_comm.comm a b }
          have hcent_le_Kbar :
              Subgroup.centralizer (step_f_Kbar : Set (Q ⧸ pCore q Q)) ≤ step_f_Kbar := by
            let F : Subgroup (Q ⧸ pCore q Q) := fittingSubgroup (Q ⧸ pCore q Q)
            have hF_eq_Kbar : F = step_f_Kbar := by
              have hKbar_le_F : step_f_Kbar ≤ F := by
                exact le_sSup
                  ⟨step_f_Kbar_normal,
                    (inferInstance : Group.IsNilpotent step_f_Kbar)⟩
              have hpcore_F_bot : pCore q F = ⊥ := by
                let Xq : Subgroup (Q ⧸ pCore q Q) := (pCore q F).map F.subtype
                have hXq_normal : Xq.Normal := by
                  have : F.Normal := by infer_instance
                  have : (pCore q F).Characteristic :=
                    pCore_characteristic (G := F) (p := q)
                  simpa [Xq] using
                    (inferInstance : ((pCore q F).map F.subtype).Normal)
                have hXq_p : IsPGroup q Xq := by
                  simpa [Xq] using
                    IsPGroup.map (p := q) (H := pCore q F)
                      (pCore_isPGroup (G := F) (p := q)) F.subtype
                have hXq_le_core : Xq ≤ pCore q (Q ⧸ pCore q Q) :=
                  le_sSup ⟨hXq_normal, hXq_p⟩
                have hXq_bot : Xq = ⊥ :=
                  le_bot_iff.mp
                    (hXq_le_core.trans (le_of_eq step_f_quot_pcore_bot))
                exact
                  (Subgroup.map_eq_bot_iff_of_injective
                    (H := pCore q F) (f := F.subtype)
                    F.subtype_injective).1 (by simpa [Xq] using hXq_bot)
              have hq_not_dvd_F : ¬ q ∣ Nat.card F := by
                intro hqF
                classical
                let Sq : Sylow q F := Classical.choice inferInstance
                have hSq_normal : (Sq : Subgroup F).Normal :=
                  Group.IsNilpotent.sylow_normal (p := q) inferInstance Sq
                have hSq_le_core : (Sq : Subgroup F) ≤ pCore q F :=
                  le_sSup ⟨hSq_normal, Sq.isPGroup'⟩
                have hqSq : q ∣ Nat.card (Sq : Subgroup F) :=
                  Sylow.dvd_card_of_dvd_card Sq hqF
                have hSq_bot : (Sq : Subgroup F) = ⊥ :=
                  le_bot_iff.mp (hSq_le_core.trans (le_of_eq hpcore_F_bot))
                have hcardSq : Nat.card (Sq : Subgroup F) = 1 := by
                  simp [hSq_bot]
                rw [hcardSq] at hqSq
                exact (Fact.out : Nat.Prime q).not_dvd_one hqSq
              have hq_coprime_F : Nat.Coprime q (Nat.card F) :=
                (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime q)).2
                  hq_not_dvd_F
              let qK : (Q ⧸ pCore q Q) →* (Q ⧸ pCore q Q) ⧸ step_f_Kbar :=
                QuotientGroup.mk' step_f_Kbar
              let Fbar : Subgroup ((Q ⧸ pCore q Q) ⧸ step_f_Kbar) := F.map qK
              have hFbar_p : IsPGroup q Fbar := by
                exact step_f_quot_q.to_subgroup Fbar
              have hFbar_coprime : Nat.Coprime q (Nat.card Fbar) := by
                exact Nat.Coprime.of_dvd_right
                  (Subgroup.card_map_dvd (H := F) qK) hq_coprime_F
              have hFbar_bot : Fbar = ⊥ :=
                section8_eq_bot_of_isPGroup_of_coprime hFbar_p hFbar_coprime
              have hF_le_Kbar : F ≤ step_f_Kbar := by
                have hF_le_ker : F ≤ qK.ker :=
                  (Subgroup.map_eq_bot_iff (H := F) (f := qK)).1
                    (by simpa [Fbar] using hFbar_bot)
                simpa [qK, QuotientGroup.ker_mk'] using hF_le_ker
              exact le_antisymm hF_le_Kbar hKbar_le_F
            have hcent_le_F :
                Subgroup.centralizer (F : Set (Q ⧸ pCore q Q)) ≤ F :=
              centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
                (G := (Q ⧸ pCore q Q)) (by infer_instance)
            simpa [hF_eq_Kbar] using hcent_le_F
          have hK2bar_ne_bot : K2bar ≠ ⊥ := by
            intro hK2bot
            have hAbar_le_cent :
                Abar ≤ Subgroup.centralizer (step_f_Kbar : Set (Q ⧸ pCore q Q)) := by
              apply (Subgroup.commutator_eq_bot_iff_le_centralizer
                (H₁ := Abar) (H₂ := step_f_Kbar)).mp
              rw [Subgroup.commutator_comm]
              simpa [K2bar] using hK2bot
            have hAbar_le_Kbar : Abar ≤ step_f_Kbar :=
              hAbar_le_cent.trans hcent_le_Kbar
            have hcard_dvd : Nat.card Abar ∣ Nat.card step_f_Kbar := by
              have hsub_dvd :
                  Nat.card (Abar.subgroupOf step_f_Kbar) ∣ Nat.card step_f_Kbar :=
                Subgroup.card_subgroup_dvd_card (Abar.subgroupOf step_f_Kbar)
              have hcard_eq :
                  Nat.card (Abar.subgroupOf step_f_Kbar) = Nat.card Abar :=
                Nat.card_congr
                  (Subgroup.subgroupOfEquivOfLe
                    (H := Abar) (K := step_f_Kbar) hAbar_le_Kbar).toEquiv
              rwa [hcard_eq] at hsub_dvd
            have hAbar_coprime : Nat.Coprime q (Nat.card Abar) :=
              Nat.Coprime.of_dvd_right hcard_dvd step_f_Kbar_coprime
            exact hAbar_ne_bot
              (section8_eq_bot_of_isPGroup_of_coprime hAbar_p hAbar_coprime)
          have hXbar_top : Xbar = ⊤ := by
            by_contra hXbar_ne_top
            have hXbar_lt_top : Xbar < ⊤ :=
              lt_of_le_of_ne le_top hXbar_ne_top
            have hX_ne_top : X ≠ ⊤ := by
              have hcomap_lt :
                  Xbar.comap piCore <
                    (⊤ : Subgroup (Q ⧸ pCore q Q)).comap piCore :=
                (Subgroup.comap_lt_comap_of_surjective
                  (f := piCore) (QuotientGroup.mk'_surjective (pCore q Q))).2
                  hXbar_lt_top
              simpa [X] using hcomap_lt.ne
            have hcore_le_X : pCore q Q ≤ X := by
              intro x hx
              change piCore x ∈ Xbar
              have hx1 : piCore x = 1 :=
                (QuotientGroup.eq_one_iff
                  (N := pCore q Q) (x := x)).2 hx
              rw [hx1]
              exact Xbar.one_mem
            have hX_ne_bot : X ≠ ⊥ := by
              intro hXbot
              exact hU_ne_bot (by simpa [hU_eq_core, hXbot] using hcore_le_X)
            have hq_dvd_X : q ∣ Nat.card X := by
              have hcore_ne_bot : pCore q Q ≠ ⊥ := by
                simpa [hU_eq_core] using hU_ne_bot
              have hq_core : q ∣ Nat.card (pCore q Q) := by
                rcases IsPGroup.card_eq_or_dvd (p := q) (G := pCore q Q)
                    (pCore_isPGroup (G := Q) (p := q)) with hcard | hdvd
                · exact False.elim
                    (hcore_ne_bot
                      ((Subgroup.card_eq_one (H := pCore q Q)).1 hcard))
                · exact hdvd
              exact hq_core.trans (Subgroup.card_dvd_of_le hcore_le_X)
            let P0Q : Subgroup Q := pCore q Q ⊔ A0.1
            have hP0Q_le_X : P0Q ≤ X := by
              apply sup_le
              · exact hcore_le_X
              · intro a ha
                change piCore a ∈ Xbar
                exact (le_sup_right : Abar ≤ K2bar ⊔ Abar)
                  (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
            let P0X : Subgroup X := P0Q.subgroupOf X
            have hP0Q_p : IsPGroup q P0Q := by
              exact IsPGroup.to_sup_of_normal_left
                (pCore_isPGroup (G := Q) (p := q))
                (IsPGroup.to_le (H := A0.1) (K := (S : Subgroup Q))
                  S.isPGroup' A0.2.1)
            have hP0X_p : IsPGroup q P0X := by
              exact hP0Q_p.of_equiv
                (Subgroup.subgroupOfEquivOfLe
                  (H := P0Q) (K := X) hP0Q_le_X).symm
            have hP0X_sylow_index : ¬ q ∣ P0X.index := by
              have hK2bar_coprime : Nat.Coprime q (Nat.card K2bar) :=
                Nat.Coprime.of_dvd_right
                  (Subgroup.card_dvd_of_le hK2bar_le_Kbar)
                  step_f_Kbar_coprime
              have hK2_Abar_inf : K2bar ⊓ Abar = ⊥ := by
                have hAbar_K2_coprime :
                    Nat.Coprime (Nat.card K2bar) (Nat.card Abar) := by
                  rcases hAbar_p.exists_card_eq with ⟨n, hn⟩
                  rw [hn]
                  exact hK2bar_coprime.symm.pow_right n
                exact (Subgroup.disjoint_of_coprime_natCard hAbar_K2_coprime).eq_bot
              let K2X : Subgroup Xbar := K2bar.subgroupOf Xbar
              let AX : Subgroup Xbar := Abar.subgroupOf Xbar
              have hXbar_le_norm_K2 :
                  Xbar ≤ Subgroup.normalizer
                    (K2bar : Set (Q ⧸ pCore q Q)) :=
                sup_le (Subgroup.le_normalizer (H := K2bar))
                  hAbar_normalizes_K2bar
              have hK2X_normal : K2X.Normal :=
                (Subgroup.normal_subgroupOf_iff_le_normalizer
                  (show K2bar ≤ Xbar from le_sup_left)).2 hXbar_le_norm_K2
              let : K2X.Normal := hK2X_normal
              have hK2X_sup_AX : K2X ⊔ AX = ⊤ := by
                rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
                exact (Subgroup.subgroupOf_eq_top).2 (by
                  simp)
              have hcompX : K2X.IsComplement' AX := by
                refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
                · rw [Subgroup.disjoint_def]
                  intro x hxK hxA
                  apply Subtype.ext
                  have hxinf :
                      (x : (Q ⧸ pCore q Q)) ∈ K2bar ⊓ Abar := ⟨hxK, hxA⟩
                  have hxbot :
                      (x : (Q ⧸ pCore q Q)) ∈
                        (⊥ : Subgroup (Q ⧸ pCore q Q)) := by
                    simpa [hK2_Abar_inf] using hxinf
                  exact Subgroup.mem_bot.mp hxbot
                · rw [Set.eq_univ_iff_forall]
                  intro x
                  rcases (Subgroup.mem_sup_of_normal_left
                    (s := K2X) (t := AX)).1
                      (show x ∈ K2X ⊔ AX by
                        rw [hK2X_sup_AX]
                        exact Subgroup.mem_top x) with
                    ⟨k, hk, a, ha, hka⟩
                  exact ⟨k, hk, a, ha, hka⟩
              have hAX_p : IsPGroup q AX := by
                exact hAbar_p.of_equiv
                  (Subgroup.subgroupOfEquivOfLe
                    (H := Abar) (K := Xbar) le_sup_right).symm
              have hK2X_card : Nat.card K2X = Nat.card K2bar :=
                Nat.card_congr
                  (Subgroup.subgroupOfEquivOfLe
                    (H := K2bar) (K := Xbar) le_sup_left).toEquiv
              have hAX_not_dvd_index : ¬ q ∣ AX.index := by
                rw [hcompX.index_eq_card, hK2X_card]
                exact (Nat.Prime.coprime_iff_not_dvd
                  (Fact.out : Nat.Prime q)).1 hK2bar_coprime
              let AXSyl : Sylow q Xbar :=
                hAX_p.toSylow hAX_not_dvd_index
              let piX : X →* Xbar :=
                (piCore.comp X.subtype).codRestrict Xbar (fun x => x.property)
              have hpiX_surj : Function.Surjective piX := by
                intro y
                obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
                  (pCore q Q) (y : (Q ⧸ pCore q Q))
                have hxX : x ∈ X := by
                  change piCore x ∈ Xbar
                  rw [hx]
                  exact y.property
                refine ⟨⟨x, hxX⟩, ?_⟩
                apply Subtype.ext
                change piCore x = (y : Q ⧸ pCore q Q)
                exact hx
              have hker_eq : piX.ker = (pCore q Q).subgroupOf X := by
                ext x
                simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
                constructor
                · intro hx
                  have hval := congrArg Subtype.val hx
                  change piCore (x : Q) = 1 at hval
                  exact (QuotientGroup.eq_one_iff
                    (N := pCore q Q) (x := (x : Q))).1 hval
                · intro hx
                  apply Subtype.ext
                  change piCore (x : Q) = 1
                  exact (QuotientGroup.eq_one_iff
                    (N := pCore q Q) (x := (x : Q))).2 hx
              have hker_p : IsPGroup q piX.ker := by
                rw [hker_eq]
                exact (pCore_isPGroup (G := Q) (p := q)).of_equiv
                  (Subgroup.subgroupOfEquivOfLe
                    (H := pCore q Q) (K := X) hcore_le_X).symm
              have hAX_le_range : (AXSyl : Subgroup Xbar) ≤ piX.range := by
                rw [MonoidHom.range_eq_top.mpr hpiX_surj]
                exact le_top
              let TX0 : Sylow q X :=
                AXSyl.comapOfKerIsPGroup piX hker_p hAX_le_range
              have hcomap_eq : Abar.comap piCore = P0Q := by
                change
                  (A0.1.map (QuotientGroup.mk' (pCore q Q))).comap
                      (QuotientGroup.mk' (pCore q Q)) =
                    pCore q Q ⊔ A0.1
                exact QuotientGroup.comap_map_mk' (pCore q Q) A0.1
              have hTX0_eq : (TX0 : Subgroup X) = P0X := by
                ext x
                change piX x ∈ AX ↔ (x : Q) ∈ P0Q
                have hmem :
                    piX x ∈ AX ↔ piCore (x : Q) ∈ Abar := by
                  rfl
                rw [hmem, ← hcomap_eq]
                rfl
              have hnot : ¬ q ∣ (TX0 : Subgroup X).index := TX0.not_dvd_index
              simpa [hTX0_eq] using hnot
            let TX : Sylow q X := hP0X_p.toSylow hP0X_sylow_index
            -- Source (i): for P₀ = O_q(Q)A inside X, A lies in both Thompson
            -- subgroups; the normalizer q'-layers centralize A and are trivial.
            have hcenter_X : HasNormalPComplement q
                (Subgroup.centralizer
                  (centerIn (G := X) (TX : Subgroup X) : Set X)) := by
              have hZ0_le_pCore : Z0 ≤ pCore q Q :=
                step_k_Z0_le_centralizer_pCore.trans step_h_self_centralizing
              have hP0Q_le_S : P0Q ≤ (S : Subgroup Q) := by
                exact sup_le
                  (hkt_pCore_le_sylow (Q := Q) (q := q) S) A0.2.1
              have hZ0_le_center_map :
                  Z0 ≤ (centerIn (G := X) (TX : Subgroup X)).map X.subtype := by
                intro z hzZ0
                have hzP0Q : z ∈ P0Q := by
                  exact (le_sup_left : pCore q Q ≤ P0Q)
                    (hZ0_le_pCore hzZ0)
                have hzX : z ∈ X := hP0Q_le_X hzP0Q
                let zX : X := ⟨z, hzX⟩
                have hzTX : zX ∈ (TX : Subgroup X) := by
                  have hzP0X : zX ∈ P0X := by
                    simpa [P0X, Subgroup.mem_subgroupOf] using hzP0Q
                  simpa [TX, IsPGroup.toSylow_coe] using hzP0X
                have hzcentTX :
                    zX ∈ Subgroup.centralizer ((TX : Subgroup X) : Set X) := by
                  rw [Subgroup.mem_centralizer_iff]
                  intro x hxTX
                  apply Subtype.ext
                  have hxP0Q : (x : Q) ∈ P0Q := by
                    have hxP0X : (x : X) ∈ P0X := by
                      simpa [TX, P0X, IsPGroup.toSylow_coe] using hxTX
                    simpa [P0X, Subgroup.mem_subgroupOf] using hxP0X
                  exact Subgroup.mem_centralizer_iff.mp hzZ0.2
                    (x : Q) (hP0Q_le_S hxP0Q)
                exact Subgroup.mem_map.mpr
                  ⟨zX, ⟨hzTX, hzcentTX⟩, rfl⟩
              exact
                hkt_hasNormalPComplement_centralizer_subgroupOf_of_ambient_le
                  (G := Q) (p := q) (N := X)
                  (K := centerIn (G := X) (TX : Subgroup X))
                  (T := Z0) hZ0_le_center_map hcentralizer_dvd
            -- Huppert IV.6.2(i): A belongs to the rank-defined J(P0).
            -- Its normalizer has trivial q'-part. The extra max-order
            -- Thompson normalizer is kept only at the normal-complement level.
            have hA_le_P0Q : A0.1 ≤ P0Q := le_sup_right
            have hA_subgroupOf_le_TX : A0.1.subgroupOf X ≤ (TX : Subgroup X) := by
              intro a ha
              have haP0Q : (a : Q) ∈ P0Q := hA_le_P0Q ha
              have haP0X : a ∈ P0X := by
                simpa [P0X, Subgroup.mem_subgroupOf] using haP0Q
              simpa [TX, IsPGroup.toSylow_coe] using haP0X
            have hP0Q_le_S : P0Q ≤ (S : Subgroup Q) :=
              sup_le (hkt_pCore_le_sylow (Q := Q) (q := q) S) A0.2.1
            have hTX_map_le_S :
                (TX : Subgroup X).map X.subtype ≤ (S : Subgroup Q) := by
              intro x hx
              rcases Subgroup.mem_map.mp hx with ⟨y, hyTX, rfl⟩
              have hyP0Q : (y : Q) ∈ P0Q := by
                have hyP0X : (y : X) ∈ P0X := by
                  simpa [TX, P0X, IsPGroup.toSylow_coe] using hyTX
                simpa [P0X, Subgroup.mem_subgroupOf] using hyP0X
              exact hP0Q_le_S hyP0Q
            have hJ_local :=
              hkt_iv62_i_J_normalizers_local_extracted
                (Q := Q) (q := q) (S := S)
                (A := A0.1) (hA_le_S := A0.2.1)
                (hA_comm := A0.2.2.1) (hA_global_rank := hA_global_rank)
                (Kbar := step_f_Kbar)
                (hKbar_normal := step_f_Kbar_normal)
                (hKbar_minimal := step_f_Kbar_minimal)
                (_hKbar_ne_bot := step_f_Kbar_ne_bot)
                (hKbar_coprime := step_f_Kbar_coprime)
                (hsolvable := step_f_solvable)
                (X := X) (TX := TX) (hX_eq := by rfl)
                (hA_le_TX := hA_subgroupOf_le_TX)
                (hTX_map_le_S := hTX_map_le_S)
                (hTX_map_eq := by
                  simpa [TX, P0X, P0Q] using
                    (show (P0Q.subgroupOf X).map X.subtype = P0Q by
                      rw [Subgroup.subgroupOf_map_subtype,
                        inf_eq_left.2 hP0Q_le_X]))
            have hJrank_X : HasNormalPComplement q
                (Subgroup.normalizer
                  (huppertRankThompsonSubgroup (G := X) (TX : Subgroup X) : Set X)) :=
              hkt_hasNormalPComplement_of_isPGroup
                (Q := Subgroup.normalizer
                  (huppertRankThompsonSubgroup (G := X) (TX : Subgroup X) : Set X))
                (p := q) (IsPGroup.to_le TX.isPGroup' hJ_local)
            have hX_comp : HasNormalPComplement q X :=
              hproper_rec X TX hX_ne_bot hX_ne_top hq_dvd_X
                hcenter_X hJrank_X            -- Once X has a normal q-complement, its normal q'-part centralizes
            -- O_q(Q); source (h) kills it, and K₂ maps to the identity.
            have hK2bar_bot : K2bar = ⊥ := by
              rcases hX_comp with ⟨N, hN_normal, hN_coprime, hX_quot_p⟩
              let : N.Normal := hN_normal
              let CoreX : Subgroup X := (pCore q Q).subgroupOf X
              have hCoreX_normal : CoreX.Normal := by
                simpa [CoreX] using
                  Subgroup.Normal.subgroupOf
                    (pCore_normal (G := Q) (p := q)) X
              let : CoreX.Normal := hCoreX_normal
              have hCoreX_p : IsPGroup q CoreX := by
                have hsub_p : IsPGroup q ((pCore q Q).subgroupOf X) :=
                  (pCore_isPGroup (G := Q) (p := q)).of_equiv
                    (Subgroup.subgroupOfEquivOfLe
                      (H := pCore q Q) (K := X) hcore_le_X).symm
                simpa [CoreX] using hsub_p
              have hN_CoreX_coprime :
                  Nat.Coprime (Nat.card N) (Nat.card CoreX) := by
                rcases hCoreX_p.exists_card_eq with ⟨n, hn⟩
                rw [hn]
                exact hN_coprime.symm.pow_right n
              have hN_inf_CoreX : N ⊓ CoreX = ⊥ :=
                (Subgroup.disjoint_of_coprime_natCard hN_CoreX_coprime).eq_bot
              have hN_le_cent_CoreX :
                  N ≤ Subgroup.centralizer (CoreX : Set X) := by
                apply (Subgroup.commutator_eq_bot_iff_le_centralizer
                  (H₁ := N) (H₂ := CoreX)).mp
                apply le_bot_iff.mp
                exact (Subgroup.commutator_le_inf
                  (H₁ := N) (H₂ := CoreX)).trans
                    (le_of_eq hN_inf_CoreX)
              have hN_le_CoreX : N ≤ CoreX := by
                intro n hnN
                have hn_cent : n ∈ Subgroup.centralizer (CoreX : Set X) :=
                  hN_le_cent_CoreX hnN
                have hn_ambient_cent :
                    ((n : X) : Q) ∈
                      Subgroup.centralizer (pCore q Q : Set Q) := by
                  rw [Subgroup.mem_centralizer_iff]
                  intro x hxcore
                  let xX : X := ⟨x, hcore_le_X hxcore⟩
                  have hxCoreX : xX ∈ CoreX := by
                    simpa [CoreX, xX]
                  have hcommX : xX * n = n * xX :=
                    (Subgroup.mem_centralizer_iff.mp hn_cent) xX hxCoreX
                  exact congrArg (fun y : X => (y : Q)) hcommX
                have hn_core : ((n : X) : Q) ∈ pCore q Q :=
                  step_h_self_centralizing hn_ambient_cent
                simpa [CoreX, Subgroup.mem_subgroupOf] using hn_core
              have hN_p : IsPGroup q N :=
                IsPGroup.to_le (H := N) (K := CoreX) hCoreX_p hN_le_CoreX
              have hN_bot : N = ⊥ :=
                section8_eq_bot_of_isPGroup_of_coprime hN_p hN_coprime
              have hX_p : IsPGroup q X := by
                let e : X ⧸ N ≃* X :=
                  (QuotientGroup.quotientMulEquivOfEq hN_bot).trans
                    (QuotientGroup.quotientBot (G := X))
                exact hX_quot_p.of_equiv e
              have hXbar_p : IsPGroup q Xbar := by
                have hmap_p : IsPGroup q (X.map piCore) :=
                  IsPGroup.map (p := q) (H := X) hX_p piCore
                have hmap_eq : X.map piCore = Xbar := by
                  simpa [X] using
                    (Subgroup.map_comap_eq_self_of_surjective
                      (f := piCore)
                      (QuotientGroup.mk'_surjective (pCore q Q)) Xbar)
                rw [hmap_eq] at hmap_p
                exact hmap_p
              have hK2bar_p : IsPGroup q K2bar :=
                IsPGroup.to_le (H := K2bar) (K := Xbar) hXbar_p le_sup_left
              have hK2bar_coprime : Nat.Coprime q (Nat.card K2bar) :=
                Nat.Coprime.of_dvd_right
                  (Subgroup.card_dvd_of_le hK2bar_le_Kbar)
                  step_f_Kbar_coprime
              exact section8_eq_bot_of_isPGroup_of_coprime
                hK2bar_p hK2bar_coprime
            exact hK2bar_ne_bot hK2bar_bot
          let ρ : Representation (ZMod r) Abar (Additive step_f_Kbar) :=
            Theory.Representation.ofElementaryAbelianAction
              (A := Abar) (G := step_f_Kbar) (p := r)
          have hρ_faithful : Function.Injective ρ := by
            have hAbar_Kbar_coprime :
                Nat.Coprime (Nat.card Abar) (Nat.card step_f_Kbar) := by
              rcases hAbar_p.exists_card_eq with ⟨n, hn⟩
              rw [hn]
              exact step_f_Kbar_coprime.pow_left n
            have hAbar_inf_Kbar : Abar ⊓ step_f_Kbar = ⊥ :=
              (Subgroup.disjoint_of_coprime_natCard hAbar_Kbar_coprime).eq_bot
            apply (MonoidHom.ker_eq_bot_iff ρ).1
            rw [Theory.Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup]
            apply le_antisymm
            · intro a haFix
              have ha_cent : (a : (Q ⧸ pCore q Q)) ∈
                  Subgroup.centralizer (step_f_Kbar : Set (Q ⧸ pCore q Q)) := by
                rw [Subgroup.mem_centralizer_iff]
                intro k hkKbar
                let kK : step_f_Kbar := ⟨k, hkKbar⟩
                have hfix : a • kK = kK :=
                  (mem_fixingSubgroup_iff
                    (M := Abar) (s := (Set.univ : Set step_f_Kbar))).1
                    haFix kK (Set.mem_univ _)
                have hconj : (a : (Q ⧸ pCore q Q)) * k * (a : (Q ⧸ pCore q Q))⁻¹ = k := by
                  simpa [MulAut.conjNormal_apply] using congrArg Subtype.val hfix
                symm
                calc
                  (a : (Q ⧸ pCore q Q)) * k =
                      ((a : (Q ⧸ pCore q Q)) * k *
                        (a : (Q ⧸ pCore q Q))⁻¹) *
                          (a : (Q ⧸ pCore q Q)) := by
                    simp [mul_assoc]
                  _ = k * (a : (Q ⧸ pCore q Q)) :=
                    congrArg
                      (fun z : (Q ⧸ pCore q Q) =>
                        z * (a : (Q ⧸ pCore q Q))) hconj
              have haKbar : (a : (Q ⧸ pCore q Q)) ∈ step_f_Kbar :=
                hcent_le_Kbar ha_cent
              have haInf : (a : (Q ⧸ pCore q Q)) ∈ Abar ⊓ step_f_Kbar :=
                ⟨a.property, haKbar⟩
              have ha_one : (a : (Q ⧸ pCore q Q)) = 1 := by
                have ha_bot :
                    (a : (Q ⧸ pCore q Q)) ∈
                      (⊥ : Subgroup (Q ⧸ pCore q Q)) := by
                  rw [← hAbar_inf_Kbar]
                  exact haInf
                exact Subgroup.mem_bot.mp ha_bot
              apply Subgroup.mem_bot.mpr
              apply Subtype.ext
              exact ha_one
            · exact bot_le
          have hρ_irreducible : Representation.IsIrreducible ρ := by
            let : Nontrivial step_f_Kbar :=
              (Subgroup.nontrivial_iff_ne_bot step_f_Kbar).2 step_f_Kbar_ne_bot
            have hminv : ∀ N : Subgroup step_f_Kbar,
                N.Normal → IsInvariant Abar step_f_Kbar N → N ≠ ⊥ → N = ⊤ := by
              intro N _hNnormal hNinv hNne
              let Namb : Subgroup (Q ⧸ pCore q Q) := N.map step_f_Kbar.subtype
              have hNamb_le_Kbar : Namb ≤ step_f_Kbar := by
                exact Subgroup.map_subtype_le N
              have hK2_le_norm_Namb :
                  K2bar ≤ Subgroup.normalizer (Namb : Set (Q ⧸ pCore q Q)) := by
                intro k hkK2
                rw [Subgroup.mem_normalizer_iff]
                intro n
                constructor
                · intro hn
                  have hkKbar : k ∈ step_f_Kbar := hK2bar_le_Kbar hkK2
                  have hnKbar : n ∈ step_f_Kbar := hNamb_le_Kbar hn
                  have hcomm : k * n = n * k :=
                    setLike_mul_comm
                      (s := step_f_Kbar) hkKbar hnKbar
                  simpa [hcomm, mul_assoc] using hn
                · intro hconj
                  have hkKbar : k ∈ step_f_Kbar := hK2bar_le_Kbar hkK2
                  have hnKbar : n ∈ step_f_Kbar := by
                    have hconjK : k * n * k⁻¹ ∈ step_f_Kbar :=
                      hNamb_le_Kbar hconj
                    have hk_inv : k⁻¹ ∈ step_f_Kbar :=
                      step_f_Kbar.inv_mem hkKbar
                    have htmp : k⁻¹ * (k * n * k⁻¹) * k ∈ step_f_Kbar :=
                      step_f_Kbar.mul_mem
                        (step_f_Kbar.mul_mem hk_inv hconjK) hkKbar
                    simpa [mul_assoc] using htmp
                  have hcomm : k * n = n * k :=
                    setLike_mul_comm
                      (s := step_f_Kbar) hkKbar hnKbar
                  simpa [hcomm, mul_assoc] using hconj
              have hAbar_le_norm_Namb :
                  Abar ≤ Subgroup.normalizer (Namb : Set (Q ⧸ pCore q Q)) := by
                have hforward :
                    ∀ (a : Abar) {n : Q ⧸ pCore q Q},
                      n ∈ Namb →
                        (a : Q ⧸ pCore q Q) * n *
                            (a : Q ⧸ pCore q Q)⁻¹ ∈ Namb := by
                  intro a n hn
                  rcases Subgroup.mem_map.mp hn with ⟨n0, hn0, rfl⟩
                  refine Subgroup.mem_map.mpr ⟨a • n0, ?_, ?_⟩
                  · exact (hNinv.invariant a n0).1 hn0
                  · simp
                      [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
                intro a haA
                rw [Subgroup.mem_normalizer_iff]
                intro n
                constructor
                · exact hforward ⟨a, haA⟩
                · intro hconj
                  have hback :=
                    hforward (⟨a, haA⟩ : Abar)⁻¹ hconj
                  simpa [mul_assoc] using hback
              have hNamb_normal : Namb.Normal := by
                apply Subgroup.normalizer_eq_top_iff.mp
                apply top_unique
                rw [← hXbar_top]
                exact sup_le hK2_le_norm_Namb hAbar_le_norm_Namb
              let : Namb.Normal := hNamb_normal
              rcases step_f_Kbar_minimal.minimal Namb hNamb_le_Kbar with hbot | htop
              · exfalso
                apply hNne
                exact
                  (Subgroup.map_eq_bot_iff_of_injective
                    (H := N) (f := step_f_Kbar.subtype)
                    step_f_Kbar.subtype_injective).1 hbot
              · apply top_unique
                intro k _hk
                have hkNamb : (k : (Q ⧸ pCore q Q)) ∈ Namb := by
                  rw [htop]
                  exact k.property
                rcases Subgroup.mem_map.mp hkNamb with ⟨n, hnN, hnk⟩
                have hn_eq : n = k := Subtype.ext hnk
                simpa [← hn_eq] using hnN
            let ρ0 := Theory.Representation.ofElementaryAbelianAction
              (A := Abar) (G := step_f_Kbar) (p := r)
            refine
              { toNontrivial := inferInstance
                eq_bot_or_eq_top := ?_ }
            intro Srep
            let N : Subgroup step_f_Kbar :=
              Srep.toSubmodule.toAddSubgroup.toSubgroup'
            have hN_inv : IsInvariant Abar step_f_Kbar N := by
              have hmap_mem (a : Abar) {x : step_f_Kbar}
                  (hx : x ∈ N) : a • x ∈ N := by
                change Additive.ofMul (a • x) ∈ Srep.toSubmodule
                have hx' : Additive.ofMul x ∈ Srep.toSubmodule := by
                  simpa [N, Submodule.mem_toAddSubgroup, AddSubgroup.mem_toSubgroup'] using hx
                have hx'' := Srep.apply_mem_toSubmodule a hx'
                simpa [ρ, ρ0,
                  Theory.Representation.ofElementaryAbelianAction_apply_ofMul] using hx''
              refine { invariant := ?_ }
              intro a x
              constructor
              · exact hmap_mem a
              · intro hx
                have hx' : (a : Abar)⁻¹ • ((a : Abar) • x) ∈ N :=
                  hmap_mem (a : Abar)⁻¹ hx
                simpa only [inv_smul_smul] using hx'
            by_cases hN_bot : N = ⊥
            · left
              apply Subrepresentation.toSubmodule_injective
              ext x
              have hxN : Additive.toMul x ∈ N ↔ x ∈ Srep.toSubmodule := by
                simp [N]
              rw [← hxN, hN_bot]
              constructor
              · intro hx
                have hx' := Subgroup.mem_bot.mp hx
                have hx0 : x = 0 := by
                  apply Additive.toMul.injective
                  simpa using hx'
                exact (Submodule.mem_bot (R := ZMod r) (M := Additive step_f_Kbar)).mpr hx0
              · intro hx
                have hx0 : x = 0 :=
                  (Submodule.mem_bot (R := ZMod r) (M := Additive step_f_Kbar)).mp hx
                rw [Subgroup.mem_bot, hx0]
                rfl
            · right
              have hN_top : N = ⊤ := hminv N inferInstance hN_inv hN_bot
              apply Subrepresentation.toSubmodule_injective
              ext x
              have hxN : Additive.toMul x ∈ N ↔ x ∈ Srep.toSubmodule := by
                simp [N]
              rw [← hxN, hN_top]
              constructor
              · intro _
                trivial
              · intro _
                trivial
          let : Representation.IsIrreducible ρ := hρ_irreducible
          have hcenter_cyclic : IsCyclic (Subgroup.center Abar) :=
            center_cyclic_of_representation_faithful_irreducible ρ hρ_faithful
          have hAbar_center : Subgroup.center Abar = ⊤ := by
            let : CommGroup Abar :=
              { mul_comm := hAbar_comm.is_comm.comm }
            exact CommGroup.center_eq_top
          have hAbar_cyclic : IsCyclic Abar := by
            have htop_cyclic : IsCyclic (⊤ : Subgroup Abar) := by
              rw [← hAbar_center]
              exact hcenter_cyclic
            let : IsCyclic (⊤ : Subgroup Abar) := htop_cyclic
            let eTop : (⊤ : Subgroup Abar) ≃* Abar := Subgroup.topEquiv
            exact (MulEquiv.isCyclic eTop).1 htop_cyclic
          let Ycore : Subgroup A0.1 := (pCore q Q).subgroupOf A0.1
          have hY_eq : Y = Ycore := by
            ext a
            simp [Y, Ycore, Subgroup.mem_subgroupOf]
          let e : A0.1 ⧸ Ycore ≃* Abar :=
            quotientSubgroupRangeEquiv A0.1 (pCore q Q)
          have hquot_core_cyclic : IsCyclic (A0.1 ⧸ Ycore) := by
            let : IsCyclic Abar := hAbar_cyclic
            exact isCyclic_of_injective e.toMonoidHom e.injective
          let eY : A0.1 ⧸ Y ≃* A0.1 ⧸ Ycore :=
            QuotientGroup.quotientMulEquivOfEq hY_eq
          let : IsCyclic (A0.1 ⧸ Ycore) := hquot_core_cyclic
          have hquot_cyclic : IsCyclic (A0.1 ⧸ Y) :=
            isCyclic_of_injective eY.toMonoidHom eY.injective
          have hcomm_sup_Abar_top :
              ⁅step_f_Kbar, A0.1.map piCore⁆ ⊔ A0.1.map piCore = ⊤ := by
            simpa [K2bar, Abar] using hXbar_top
          exact ⟨hcomm_sup_Abar_top, hquot_cyclic⟩
        have hquot_cyclic : IsCyclic (A0.1 ⧸ Y) := hsource_i_j.2
        have hrank_endpoint : generatorRank A0.1 ≤ generatorRank Y + 1 := by
          classical
          obtain ⟨Sgen, hSgen_card, hSgen_closure⟩ := Group.rank_spec Y
          obtain ⟨xbar, hxbar⟩ :=
            (isCyclic_iff_exists_zpowers_eq_top (α := A0.1 ⧸ Y)).1 hquot_cyclic
          obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Y xbar
          let e : Y ↪ A0.1 := ⟨Y.subtype, Y.subtype_injective⟩
          let Tgen : Finset A0.1 := insert x (Sgen.map e)
          let Ugen : Subgroup A0.1 := Subgroup.closure (Tgen : Set A0.1)
          have hmapSgen_le :
              (Subgroup.closure (Sgen : Set Y)).map Y.subtype ≤ Ugen := by
            rw [MonoidHom.map_closure, Subgroup.closure_le]
            intro z hz
            rcases hz with ⟨y, hySgen, rfl⟩
            apply Subgroup.subset_closure
            change (y : A0.1) ∈ Tgen
            simp only [Tgen, Finset.mem_insert, Finset.mem_map]
            exact Or.inr ⟨y, hySgen, rfl⟩
          have hY_le_Ugen : Y ≤ Ugen := by
            intro y hy
            let y' : Y := ⟨y, hy⟩
            have hy' : y' ∈ Subgroup.closure (Sgen : Set Y) := by
              rw [hSgen_closure]
              simp
            exact hmapSgen_le (Subgroup.mem_map_of_mem Y.subtype hy')
          let qY : A0.1 →* A0.1 ⧸ Y := QuotientGroup.mk' Y
          have hxUgen : x ∈ Ugen := by
            apply Subgroup.subset_closure
            simp [Tgen]
          have hqxUgen : qY x ∈ Ugen.map qY :=
            Subgroup.mem_map_of_mem qY hxUgen
          have hzpow_le : Subgroup.zpowers (qY x) ≤ Ugen.map qY :=
            (Subgroup.zpowers_le).2 hqxUgen
          have hmap_top : Ugen.map qY = ⊤ := by
            apply top_unique
            rw [← hxbar]
            exact hzpow_le
          have hcomap : Subgroup.comap qY (Ugen.map qY) = Y ⊔ Ugen := by
            exact QuotientGroup.comap_map_mk' (N := Y) Ugen
          have hUgen_top : Ugen = ⊤ := by
            have hs : Y ⊔ Ugen = Ugen := sup_eq_right.2 hY_le_Ugen
            have ht : (⊤ : Subgroup A0.1) = Y ⊔ Ugen := by
              calc
                (⊤ : Subgroup A0.1) = Subgroup.comap qY ⊤ := by
                  ext g
                  simp [qY]
                _ = Subgroup.comap qY (Ugen.map qY) := by rw [hmap_top]
                _ = Y ⊔ Ugen := hcomap
            exact (ht.trans hs).symm
          rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
          apply (Group.rank_le (by simpa [Ugen] using hUgen_top)).trans
          calc
            Tgen.card ≤ (Sgen.map e).card + 1 := Finset.card_insert_le ..
            _ = Sgen.card + 1 := by simp
            _ = Group.rank Y + 1 := by rw [hSgen_card]
        have hY_rank :
            generatorRank Y =
              generatorRank (A0.1 ⊓ pCore q Q : Subgroup Q) := by
          rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
          simpa [Y] using Group.rank_congr
            (Subgroup.subgroupOfEquivOfLe
              (H := A0.1 ⊓ pCore q Q) (K := A0.1) inf_le_left)
        exact ⟨hsource_i_j.1, by simpa [hY_rank] using hrank_endpoint⟩
      have hcomm_sup_Abar_top :
          ⁅step_f_Kbar, A0.1.map piCore⁆ ⊔ A0.1.map piCore = ⊤ :=
        step_i_j_core.1
      have step_j_Acore_rank_drop :
          generatorRank A0.1 ≤
            generatorRank (A0.1 ⊓ pCore q Q : Subgroup Q) + 1 :=
        step_i_j_core.2
      -- Huppert IV.6.2(n): `<A ∩ O_q(Q), B>` is abelian and lies in the Sylow subgroup.
      have step_n_sup_core_B_rank_le_A :
          generatorRank ((A0.1 ⊓ pCore q Q) ⊔ B : Subgroup Q) ≤ generatorRank A0.1 := by
        let Acore : Subgroup Q := A0.1 ⊓ pCore q Q
        have step_n_B_le_S : B ≤ (S : Subgroup Q) :=
          step_n_B_le_pCore.trans (hkt_pCore_le_sylow (Q := Q) (q := q) S)
        have step_n_core_B_le_S : (Acore ⊔ B : Subgroup Q) ≤ (S : Subgroup Q) := by
          exact sup_le (inf_le_left.trans A0.2.1) step_n_B_le_S
        have step_n_Acore_comm : IsMulCommutative Acore := by
          refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
          apply Subtype.ext
          exact setLike_mul_comm (s := A0.1)
            x.property.1 y.property.1
        have step_n_B_le_cent_Acore : B ≤ Subgroup.centralizer (Acore : Set Q) := by
          intro b hb
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          have hb_center : (b : Q) ∈ centerIn (G := Q) (pCore q Q : Subgroup Q) :=
            step_n_B_le_center_pCore hb
          have ha_core : a ∈ pCore q Q := by
            simpa [Acore] using ha.2
          exact Subgroup.mem_centralizer_iff.mp hb_center.2 a ha_core
        have step_n_Acore_le_cent_B : Acore ≤ Subgroup.centralizer (B : Set Q) := by
          intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          have hb_cent : (b : Q) ∈ Subgroup.centralizer (Acore : Set Q) :=
            step_n_B_le_cent_Acore hb
          exact (Subgroup.mem_centralizer_iff.mp hb_cent a ha).symm
        have step_n_core_B_comm : IsMulCommutative (Acore ⊔ B : Subgroup Q) := by
          have hAcore_self : Acore ≤ Subgroup.centralizer (Acore : Set Q) :=
            (Subgroup.le_centralizer_iff_isMulCommutative (K := Acore)).2 step_n_Acore_comm
          have hB_self : B ≤ Subgroup.centralizer (B : Set Q) :=
            (Subgroup.le_centralizer_iff_isMulCommutative (K := B)).2 step_n_B_mul_comm
          have hsup_cent_Acore : (Acore ⊔ B : Subgroup Q) ≤
              Subgroup.centralizer (Acore : Set Q) :=
            sup_le hAcore_self step_n_B_le_cent_Acore
          have hsup_cent_B : (Acore ⊔ B : Subgroup Q) ≤
              Subgroup.centralizer (B : Set Q) :=
            sup_le step_n_Acore_le_cent_B hB_self
          have hsup_cent_sup : (Acore ⊔ B : Subgroup Q) ≤
              Subgroup.centralizer ((Acore ⊔ B : Subgroup Q) : Set Q) :=
            Subgroup.le_centralizer_sup_of_le_centralizers hsup_cent_Acore hsup_cent_B
          exact (Subgroup.le_centralizer_iff_isMulCommutative (K := (Acore ⊔ B : Subgroup Q))).1
            hsup_cent_sup
        simpa [Acore] using
          hA_global_rank ((Acore ⊔ B : Subgroup Q)) step_n_core_B_le_S step_n_core_B_comm
      -- Huppert IV.6.2(n): the previous two rank comparisons give `d(B / (B ∩ A)) ≤ 1`.
      have step_n_B_mod_inter_rank_le_one :
          Nat.card B ≤ q * Nat.card (interInB A0.1) := by
        let AcapB : Subgroup B := interInB A0.1
        have step_n_inter_normal : AcapB.Normal := by
          let : IsMulCommutative B := step_n_B_mul_comm
          infer_instance
        let : AcapB.Normal := step_n_inter_normal
        have step_n_quot_elem : IsElementaryAbelian q (B ⧸ AcapB) :=
          hkt_isElementaryAbelian_quotient_of_isElementaryAbelian
            (p := q) AcapB step_n_B_elementary
        have step_n_quot_rank_le_one : generatorRank (B ⧸ AcapB) ≤ 1 := by
          have step_n_rank_subadd :
              generatorRank (A0.1 ⊓ pCore q Q : Subgroup Q) +
                  generatorRank (B ⧸ AcapB) ≤
                generatorRank A0.1 := by
            let Acore : Subgroup Q := A0.1 ⊓ pCore q Q
            have hAcore_comm : IsMulCommutative Acore := by
              refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
              apply Subtype.ext
              exact setLike_mul_comm (s := A0.1)
                x.property.1 y.property.1
            have : Fact (IsPGroup q Acore) :=
              ⟨IsPGroup.to_le (pCore_isPGroup (G := Q) (p := q)) inf_le_right⟩
            let Ωsub : Subgroup Acore := omega₁ (G := Acore) (p := q)
            let ΩA : Subgroup Q := Ωsub.map Acore.subtype
            have hΩA_le_Acore : ΩA ≤ Acore := by
              rintro _ ⟨a, ha, rfl⟩
              exact a.2
            have hΩsub_elem : IsElementaryAbelian q Ωsub := by
              let : IsMulCommutative Acore := hAcore_comm
              simpa [Ωsub] using
                IsElementaryAbelian.omega₁_of_isMulCommutative (G := Acore) (p := q)
            have hΩA_elem : IsElementaryAbelian q ΩA := by
              let : IsElementaryAbelian q Ωsub := hΩsub_elem
              let eΩ : Ωsub ≃* ΩA :=
                Subgroup.equivMapOfInjective (f := Acore.subtype) Ωsub
                  Acore.subtype_injective
              exact hkt_isElementaryAbelian_of_mulEquiv eΩ
            have hΩA_subgroupOf_B : ΩA.subgroupOf B = AcapB := by
              ext b
              constructor
              · intro hb
                change (b : Q) ∈ A0.1
                exact (hΩA_le_Acore hb).1
              · intro hb
                change (b : Q) ∈ A0.1 at hb
                let a : Acore := ⟨(b : Q), hb, step_n_B_le_pCore b.2⟩
                have hbpowB : b ^ q = 1 := step_n_B_pow_eq_one b
                have hbpowQ : (b : Q) ^ q = 1 := by
                  simpa using congrArg B.subtype hbpowB
                have hapow : a ^ q = 1 := by
                  apply Subtype.ext
                  simpa [a] using hbpowQ
                have haΩ : a ∈ Ωsub := by
                  change a ∈ Subgroup.closure {z : Acore | z ^ (q ^ 1) = 1}
                  exact Subgroup.subset_closure (by simpa [pow_one] using hapow)
                exact Subgroup.mem_map_of_mem Acore.subtype haΩ
            have hB_le_cent_ΩA : B ≤ Subgroup.centralizer (ΩA : Set Q) := by
              intro b hb
              rw [Subgroup.mem_centralizer_iff]
              intro a ha
              have hbC := step_n_B_le_center_pCore hb
              exact Subgroup.mem_centralizer_iff.mp hbC.2 a (hΩA_le_Acore ha).2
            let E : Subgroup Q := B ⊔ ΩA
            have hE_elem : IsElementaryAbelian q E := by
              let : IsElementaryAbelian q ΩA := hΩA_elem
              let : IsElementaryAbelian q B := step_n_B_elementary
              change IsElementaryAbelian q ↥(B ⊔ ΩA : Subgroup Q)
              rw [sup_comm]
              exact isElementaryAbelian_sup_of_le_centralizer'
                (p := q) (E := ΩA) (C := B) hB_le_cent_ΩA
            have hB_le_norm_ΩA : B ≤ Subgroup.normalizer (ΩA : Set Q) :=
              hB_le_cent_ΩA.trans (centralizer_le_normalizer ΩA)
            have hquot_card :
                Nat.card (E ⧸ ΩA.subgroupOf E) = Nat.card (B ⧸ AcapB) := by
              let e₂ := QuotientGroup.quotientInfEquivProdNormalizerQuotient
                B ΩA hB_le_norm_ΩA
              have he₂card :
                  Nat.card (B ⧸ ΩA.subgroupOf B) =
                    Nat.card ((B ⊔ ΩA : Subgroup Q) ⧸
                      ΩA.subgroupOf (B ⊔ ΩA : Subgroup Q)) :=
                Nat.card_congr e₂.toEquiv
              change Nat.card ((B ⊔ ΩA : Subgroup Q) ⧸
                  ΩA.subgroupOf (B ⊔ ΩA : Subgroup Q)) =
                    Nat.card (B ⧸ AcapB)
              exact he₂card.symm.trans
                (Nat.card_congr
                  (QuotientGroup.quotientMulEquivOfEq hΩA_subgroupOf_B).toEquiv)
            have hΩA_card : Nat.card ΩA = Nat.card Ωsub := by
              simpa [ΩA] using
                Subgroup.card_map_of_injective (K := Ωsub) (f := Acore.subtype)
                  Acore.subtype_injective
            have hE_card :
                Nat.card E = Nat.card (B ⧸ AcapB) * Nat.card Ωsub := by
              have hc := (ΩA.subgroupOf E).index_mul_card
              change Nat.card (E ⧸ ΩA.subgroupOf E) *
                  Nat.card (ΩA.subgroupOf E) = Nat.card E at hc
              rw [hquot_card, natCard_subgroupOf_eq ΩA E le_sup_right, hΩA_card] at hc
              exact hc.symm
            have hΩsub_pow : Nat.card Ωsub = q ^ generatorRank Acore := by
              let : IsMulCommutative Acore := hAcore_comm
              simpa [Ωsub] using
                hkt_omega₁_card_eq_pow_generatorRank_of_commutative_pgroup
                  (G := Acore) (p := q)
            have hquot_pow : Nat.card (B ⧸ AcapB) =
                q ^ generatorRank (B ⧸ AcapB) := by
              let : IsElementaryAbelian q (B ⧸ AcapB) := step_n_quot_elem
              exact elementaryAbelian_card_eq_pow_generatorRank (p := q) (B ⧸ AcapB)
            have hE_pow : Nat.card E = q ^ generatorRank E := by
              let : IsElementaryAbelian q E := hE_elem
              exact elementaryAbelian_card_eq_pow_generatorRank (p := q) E
            have hE_rank : generatorRank E =
                generatorRank Acore + generatorRank (B ⧸ AcapB) := by
              have hpows : q ^ generatorRank E =
                  q ^ (generatorRank Acore + generatorRank (B ⧸ AcapB)) := by
                calc
                  q ^ generatorRank E = Nat.card E := hE_pow.symm
                  _ = Nat.card (B ⧸ AcapB) * Nat.card Ωsub := hE_card
                  _ = q ^ generatorRank (B ⧸ AcapB) *
                      q ^ generatorRank Acore := by rw [hquot_pow, hΩsub_pow]
                  _ = q ^ (generatorRank Acore +
                      generatorRank (B ⧸ AcapB)) := by
                        rw [pow_add, Nat.mul_comm]
              exact (Nat.pow_right_injective (Fact.out : Nat.Prime q).one_lt) hpows
            have hE_le_S : E ≤ (S : Subgroup Q) := by
              dsimp [E]
              exact sup_le
                (step_n_B_le_pCore.trans
                  (hkt_pCore_le_sylow (Q := Q) (q := q) S))
                (hΩA_le_Acore.trans (inf_le_left.trans A0.2.1))
            have hE_comm : IsMulCommutative E := hE_elem.toIsMulCommutative
            have hE_le_rank_A : generatorRank E ≤ generatorRank A0.1 :=
              hA_global_rank E hE_le_S hE_comm
            rw [hE_rank] at hE_le_rank_A
            simpa [Acore] using hE_le_rank_A
          omega
        have step_n_quot_card_le_q : Nat.card (B ⧸ AcapB) ≤ q := by
          let : IsElementaryAbelian q (B ⧸ AcapB) := step_n_quot_elem
          have hcard_pow : Nat.card (B ⧸ AcapB) =
              q ^ generatorRank (B ⧸ AcapB) :=
            elementaryAbelian_card_eq_pow_generatorRank (p := q) (B ⧸ AcapB)
          have hpow_le : q ^ generatorRank (B ⧸ AcapB) ≤ q ^ 1 :=
            Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime q))
              step_n_quot_rank_le_one
          calc
            Nat.card (B ⧸ AcapB) = q ^ generatorRank (B ⧸ AcapB) := hcard_pow
            _ ≤ q ^ 1 := hpow_le
            _ = q := by rw [pow_one]
        have step_n_card_factor :
            Nat.card B = Nat.card (B ⧸ AcapB) * Nat.card AcapB := by
          exact Subgroup.card_eq_card_quotient_mul_card_subgroup (s := AcapB)
        change Nat.card B ≤ q * Nat.card AcapB
        calc
          Nat.card B = Nat.card (B ⧸ AcapB) * Nat.card AcapB := step_n_card_factor
          _ ≤ q * Nat.card AcapB := Nat.mul_le_mul_right _ step_n_quot_card_le_q
      -- Translate the elementary-abelian quotient/cardinality bound into the subgroup index.
      have step_o_inter_index_from_card : (interInB A0.1).index ≤ q := by
        have hmul : (interInB A0.1).index * Nat.card (interInB A0.1) ≤
            q * Nat.card (interInB A0.1) := by
          calc
            (interInB A0.1).index * Nat.card (interInB A0.1) = Nat.card B := by
              exact (interInB A0.1).index_mul_card
            _ ≤ q * Nat.card (interInB A0.1) := step_n_B_mod_inter_rank_le_one
        exact Nat.le_of_mul_le_mul_right hmul Nat.card_pos
      exact ⟨hcomm_sup_Abar_top, step_o_inter_index_from_card⟩
    have hcomm_sup_Abar_top :
        ⁅step_f_Kbar, A0.1.map piCore⁆ ⊔ A0.1.map piCore = ⊤ :=
      step_i_j_data.1
    have step_o_A_inter_index : (interInB A0.1).index ≤ q :=
      step_i_j_data.2
    have step_o_A_index : (centInB A0.1).index ≤ q :=
      step_o_index_of_inter A0.1 A0.2.2.1 step_o_A_inter_index
    have step_o_conjugate_data :
        ∃ x : Q,
          let Ax : Subgroup Q := A0.1.map (MulAut.conj x).toMonoidHom
          (centInB Ax).index ≤ q ∧
            centInB A0.1 ⊓ centInB Ax = (⊥ : Subgroup B) := by
      -- Huppert IV.6.2(i): choose a conjugate `A^x` so that `Q = ⟨S, A, A^x⟩`.
      have step_i_conjugate_generates :
          ∃ x : Q,
            let Ax : Subgroup Q := A0.1.map (MulAut.conj x).toMonoidHom
            (centInB Ax).index ≤ q ∧
              (∀ b : B, b ∈ centInB A0.1 → b ∈ centInB Ax → (b : Q) = 1) := by
        simpa [centInB] using
          hkt_iv62_o_conjugate_centralizers_extracted
            (Q := Q) (q := q) (S := S)
            (A := A0.1) (hA_le_S := A0.2.1)
            (Kbar := step_f_Kbar)
            (hKbar_normal := step_f_Kbar_normal)
            (hKbar_minimal := step_f_Kbar_minimal)
            (hKbar_ne_bot := step_f_Kbar_ne_bot)
            (hKbar_coprime := step_f_Kbar_coprime)
            (hsolvable := step_f_solvable)
            (B := B) (hB_normal := step_n_B_normal)
            (hB_le_center_core := step_n_B_le_center_pCore)
            (hA_index := step_o_A_index)
            (hcomm_sup_Abar_top := hcomm_sup_Abar_top)
            (RqprimeLayer := RqprimeLayer)
            (hB_fixed_trivial := step_n_B_fixed_trivial)
      -- Huppert IV.6.2(o): `B ∩ Z(BQ) = 1` converts simultaneous centralization into triviality.
      have step_o_inf_bot_from_conjugate :
          ∃ x : Q,
            let Ax : Subgroup Q := A0.1.map (MulAut.conj x).toMonoidHom
            (centInB Ax).index ≤ q ∧
              centInB A0.1 ⊓ centInB Ax = (⊥ : Subgroup B) := by
        rcases step_i_conjugate_generates with ⟨x, hx_index, hx_trivial⟩
        refine ⟨x, hx_index, ?_⟩
        refine le_antisymm ?_ bot_le
        intro b hb
        rw [Subgroup.mem_bot]
        apply Subtype.ext
        exact hx_trivial b hb.1 hb.2
      exact step_o_inf_bot_from_conjugate
    rcases step_o_conjugate_data with ⟨x, hx_index, hx_inf_bot⟩
    let Ax : Subgroup Q := A0.1.map (MulAut.conj x).toMonoidHom
    exact ⟨hcomm_sup_Abar_top,
      centInB A0.1, centInB Ax, step_o_A_index, hx_index, hx_inf_bot⟩
  rcases step_o_data with
    ⟨step_i_comm_sup_Abar_top, C1, C2, hC1_index, hC2_index, hC12_inf_bot⟩
  have step_o_rank_at_most_two : generatorRank B ≤ 2 :=
    step_o_rank_at_most_two_of_relIndex C1 C2 hC1_index hC2_index hC12_inf_bot
  -- (p) The same commutator-layer construction must show the q-prime layer
  -- does not centralize B; then the minimal normal q-prime layer from (f)
  -- forces C_Q(B)=O_q(Q).
  have step_p_Klayer_not_centralizes_B :
      ¬ Klayer ≤ Subgroup.centralizer (B : Set Q) := by
    classical
    intro hKlayer_centralizes_B
    have step_p_core_le_centralizer_W :
        pCore q Q ≤ Subgroup.centralizer (W : Set Q) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw_center : (w : Q) ∈ centerIn (G := Q) (pCore q Q : Subgroup Q) :=
        step_l_W_le_center_pCore hw
      exact (Subgroup.mem_centralizer_iff.mp hw_center.2 x hx).symm
    have step_p_comm_W_core_bot : ⁅W, pCore q Q⁆ = (⊥ : Subgroup Q) := by
      have hcoreW : ⁅pCore q Q, W⁆ = (⊥ : Subgroup Q) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer
          (H₁ := pCore q Q) (H₂ := W)).2 step_p_core_le_centralizer_W
      simpa [Subgroup.commutator_comm] using hcoreW
    have step_p_Klayer_eq_core_sup_Rqprime :
        Klayer = pCore q Q ⊔ RqprimeLayer := by
      have hmap_top :
          (⊤ : Subgroup Klayer).map Klayer.subtype = Klayer := by
        simpa [MonoidHom.range_eq_map] using
          (Klayer.range_subtype : Klayer.subtype.range = Klayer)
      have hmap_sup :
          (CoreKlayer ⊔ Rlayer).map Klayer.subtype =
            (pCore q Q ⊔ RqprimeLayer : Subgroup Q) := by
        rw [Subgroup.map_sup]
        congr 1
        · simpa [CoreKlayer] using
            (Subgroup.map_subgroupOf_eq_of_le (H := pCore q Q) (K := Klayer)
              step_f_pCore_le_Klayer)
      have htop : (CoreKlayer ⊔ Rlayer).map Klayer.subtype = Klayer := by
        rw [step_f_CoreKlayer_Rlayer_compl.sup_eq_top]
        exact hmap_top
      exact htop.symm.trans hmap_sup
    have step_p_commCarrier_le_comm_W_Rqprime :
        commCarrier ≤ ⁅W, RqprimeLayer⁆ := by
      have : (pCore q Q).Normal := pCore_normal (G := Q) (p := q)
      dsimp [commCarrier]
      rw [step_p_Klayer_eq_core_sup_Rqprime]
      rw [Subgroup.commutator_le]
      intro w hw k hk
      rcases (Subgroup.mem_sup_of_normal_left
          (s := pCore q Q) (t := RqprimeLayer) (x := k)).1 hk with
        ⟨c, hc, r, hr, hcr⟩
      have hwr : ⁅w, r⁆ ∈ ⁅W, RqprimeLayer⁆ :=
        Subgroup.commutator_mem_commutator hw hr
      have hcomm_wc : w * c = c * w :=
        Subgroup.mem_centralizer_iff.mp (step_p_core_le_centralizer_W hc) w hw
      have hwrW : ⁅w, r⁆ ∈ W :=
        (Subgroup.commutator_le_left (H₁ := W) (H₂ := RqprimeLayer)) hwr
      have hcomm_wrc : ⁅w, r⁆ * c = c * ⁅w, r⁆ :=
        Subgroup.mem_centralizer_iff.mp (step_p_core_le_centralizer_W hc) ⁅w, r⁆ hwrW
      have hconj_wr : c * ⁅w, r⁆ * c⁻¹ = ⁅w, r⁆ := by
        calc
          c * ⁅w, r⁆ * c⁻¹ = ⁅w, r⁆ * c * c⁻¹ := by
            rw [← hcomm_wrc]
          _ = ⁅w, r⁆ := by simp [mul_assoc]
      have hk_eq : k = c * r := hcr.symm
      rw [hk_eq]
      convert hwr using 1
      calc
        ⁅w, c * r⁆ = c * ⁅w, r⁆ * c⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]
          rw [← mul_assoc w c r, hcomm_wc]
          simp [mul_assoc]
        _ = ⁅w, r⁆ := hconj_wr
    have step_p_comm_W_Rqprime_le_commCarrier :
        ⁅W, RqprimeLayer⁆ ≤ commCarrier := by
      dsimp [commCarrier]
      exact Subgroup.commutator_mono (show W ≤ W by rfl) step_f_RqprimeLayer_le_Klayer
    have step_p_commCarrier_eq_comm_W_Rqprime :
        commCarrier = ⁅W, RqprimeLayer⁆ :=
      le_antisymm step_p_commCarrier_le_comm_W_Rqprime
        step_p_comm_W_Rqprime_le_commCarrier
    have step_p_Rqprime_centralizes_B :
        RqprimeLayer ≤ Subgroup.centralizer (B : Set Q) :=
      step_f_RqprimeLayer_le_Klayer.trans hKlayer_centralizes_B
    have step_p_coprime_Rqprime_commCarrier :
        Nat.Coprime (Nat.card RqprimeLayer) (Nat.card commCarrier) := by
      rcases step_n_commCarrier_isPGroup.exists_card_eq with ⟨n, hn⟩
      rw [hn]
      exact (Nat.Coprime.symm step_f_RqprimeLayer_coprime_q).pow_right n
    have : Fact (IsPGroup q commCarrier) := ⟨step_n_commCarrier_isPGroup⟩
    have : Subgroup.Normalizes RqprimeLayer commCarrier :=
      ⟨Subgroup.le_normalizer_of_normal⟩
    have step_p_Rqprime_trivial_on_omega :
        ActsTriviallyOnSubgroup (A := RqprimeLayer) (G := commCarrier) Ωcomm := by
      intro r d hd
      apply Subtype.ext
      have hdB : ((d : commCarrier) : Q) ∈ B := by
        dsimp [B, Ωcomm] at *
        exact Subgroup.mem_map_of_mem commCarrier.subtype hd
      have hr_cent : (r : Q) ∈ Subgroup.centralizer (B : Set Q) :=
        step_p_Rqprime_centralizes_B r.property
      have hcomm_dr : ((d : commCarrier) : Q) * (r : Q) = (r : Q) * ((d : commCarrier) : Q) :=
        Subgroup.mem_centralizer_iff.mp hr_cent ((d : commCarrier) : Q) hdB
      have hfixQ : (r : Q) * ((d : commCarrier) : Q) * (r : Q)⁻¹ = (d : Q) := by
        calc
          (r : Q) * ((d : commCarrier) : Q) * (r : Q)⁻¹ =
              ((d : commCarrier) : Q) * (r : Q) * (r : Q)⁻¹ := by
                rw [← hcomm_dr]
          _ = (d : Q) := by simp [mul_assoc]
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hfixQ
    have step_p_Rqprime_trivial_on_commCarrier :
        ActsTrivially (A := RqprimeLayer) (G := commCarrier) :=
      theorem_1_11 (G := commCarrier) (A := RqprimeLayer) (p := q) hq2
        step_p_coprime_Rqprime_commCarrier step_p_Rqprime_trivial_on_omega
    have step_p_commCarrier_Rqprime_bot :
        ⁅commCarrier, RqprimeLayer⁆ = (⊥ : Subgroup Q) := by
      have hcomm_action_bot :
          commutatorAction (A := RqprimeLayer) (G := commCarrier) =
            (⊥ : Subgroup commCarrier) := by
        rw [commutatorAction_eq_closure]
        refine le_antisymm ?_ bot_le
        refine (Subgroup.closure_le (K := (⊥ : Subgroup commCarrier))).2 ?_
        rintro x ⟨r, d, rfl⟩
        have hfix := step_p_Rqprime_trivial_on_commCarrier r d
        simp [hfix]
      have hmap :
          (commutatorAction (A := RqprimeLayer) (G := commCarrier)).map
              commCarrier.subtype = ⁅commCarrier, RqprimeLayer⁆ := by
        simpa using
          commutatorAction_subgroup_conj_map_eq_commutator
            commCarrier RqprimeLayer (Subgroup.le_normalizer_of_normal)
      rw [← hmap, hcomm_action_bot]
      simp
    have step_p_comm_W_Rqprime_Rqprime_bot :
        ⁅⁅W, RqprimeLayer⁆, RqprimeLayer⁆ = (⊥ : Subgroup Q) := by
      simpa [← step_p_commCarrier_eq_comm_W_Rqprime] using
        step_p_commCarrier_Rqprime_bot
    have step_p_W_action_coprime :
        Nat.Coprime (Nat.card RqprimeLayer) (Nat.card W) := by
      have hW_p : IsPGroup q W :=
        IsPGroup.to_le (pCore_isPGroup (G := Q) (p := q))
          (fun x hx => (step_l_W_le_center_pCore hx).1)
      rcases hW_p.exists_card_eq with ⟨n, hn⟩
      rw [hn]
      exact (Nat.Coprime.symm step_f_RqprimeLayer_coprime_q).pow_right n
    have step_p_comm_W_Rqprime_bot :
        ⁅W, RqprimeLayer⁆ = (⊥ : Subgroup Q) :=
      hkt_commutator_eq_bot_of_coprime_double_commutator_eq_bot
        (Q := Q) W RqprimeLayer Subgroup.le_normalizer_of_normal
        step_p_W_action_coprime step_p_comm_W_Rqprime_Rqprime_bot
    exact step_n_commCarrier_ne_bot (by
      rw [step_p_commCarrier_eq_comm_W_Rqprime, step_p_comm_W_Rqprime_bot])
  have step_p_centralizer_eq : Subgroup.centralizer (B : Set Q) = pCore q Q :=
    step_p_centralizer_eq_of_Klayer_not_centralized step_p_Klayer_not_centralizes_B
  -- (r) Choose a cyclic q-prime actor whose conjugate images commute in the
  -- two-dimensional model and whose generator acts nonscalarly.
  have step_r_cyclic_qprime_actor :=
    hkt_iv62_r_cyclic_nonscalar_actor_extracted
      (Q := Q) (q := q) (S := S)
      (A := A0.1) (hA_le_S := A0.2.1)
      (Kbar := step_f_Kbar)
      (hKbar_normal := step_f_Kbar_normal)
      (hKbar_minimal := step_f_Kbar_minimal)
      (hKbar_ne_bot := step_f_Kbar_ne_bot)
      (hKbar_coprime := step_f_Kbar_coprime)
      (hsolvable := step_f_solvable)
      (Klayer := Klayer) (RqprimeLayer := RqprimeLayer) (B := B)
      (hKlayer_eq := by rfl) (hKlayer_normal := step_f_Klayer_normal)
      (hRqprime_le_Klayer := step_f_RqprimeLayer_le_Klayer)
      (hKlayer_eq_core_sup_Rqprime := step_n_Klayer_eq_core_sup_Rqprime)
      (hRqprime_coprime := step_f_RqprimeLayer_coprime_q)
      (hcomm_sup_Abar_top := step_i_comm_sup_Abar_top)
      (hB_le_center_core := step_n_B_le_center_pCore)
      (hB_centralizer := step_p_centralizer_eq)
      (hKlayer_not_centralizes_B := step_p_Klayer_not_centralizes_B)
  rcases step_r_cyclic_qprime_actor with
    ⟨C0, hC0_cyclic, hC0_coprime, hC0_model⟩
  exact step_r_terminal_contradiction_from_data
    step_o_rank_at_most_two step_p_centralizer_eq
    C0 hC0_cyclic hC0_coprime hC0_model

private theorem hkt_isPElement_mem_pCore_terminal_from_selected_overgroup
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (hnot_Qp : ¬ IsPGroup q Q)
    (hq2 : q ≠ 2) (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    (hproper_rec :
      ∀ (H : Subgroup Q) (T : Sylow q H),
        H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q
          (Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q H)
    (hsmall_rec :
      ∀ {R : Type u} [Group R] [Finite R] (T : Sylow q R),
        Nat.card R < Nat.card Q → q ∣ Nat.card R →
        HasNormalPComplement q
          (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q R)
    {U : Subgroup Q}
    (hU_ne_bot : U ≠ ⊥) (hU_p : IsPGroup q U)
    (hU_no_complement : ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))))
    (hUmax :
      ∀ W : Subgroup Q,
        W ≠ ⊥ →
        IsPGroup q W →
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
          Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q *
              (Nat.card Q + 1) + Nat.card W ≤
            Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q *
              (Nat.card Q + 1) + Nat.card U)
    (P : Sylow q (Subgroup.normalizer (U : Set Q)))
    (hUS : U < (S : Subgroup Q))
    (hUN_le_P :
      U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≤
        (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hcardUP :
      Nat.card U < Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hNtop : Subgroup.normalizer (U : Set Q) = ⊤)
    (hU_eq_core : U = pCore q Q)
    {V : Subgroup Q}
    (hV_normalizer_comp : HasNormalPComplement q (↥(Subgroup.normalizer (V : Set Q))))
    (hcore_le_V : pCore q Q ≤ V)
    (hcore_lt_V : Nat.card (pCore q Q) < Nat.card V)
    (hV_le_S : V ≤ (S : Subgroup Q))
    (hVp : IsPGroup q V)
    (hS_le_normalizer_V : (S : Subgroup Q) ≤ Subgroup.normalizer (V : Set Q))
    (hnormalizer_V_ne_top : Subgroup.normalizer (V : Set Q) ≠ ⊤) :
    False := by
  let VS : Subgroup (S : Subgroup Q) := V.subgroupOf (S : Subgroup Q)
  have hVS_normal : VS.Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hV_le_S).2 hS_le_normalizer_V
  let CoreV : Subgroup V := (pCore q Q).subgroupOf V
  have hCoreV_normal : CoreV.Normal := by
    have hV_le_norm_core : V ≤ Subgroup.normalizer ((pCore q Q : Subgroup Q) : Set Q) := by
      intro v _hv
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        exact (pCore_normal (G := Q) (p := q)).conj_mem z hz v
      · intro hz
        have hz' : v⁻¹ * (v * z * v⁻¹) * (v⁻¹)⁻¹ ∈ pCore q Q :=
          (pCore_normal (G := Q) (p := q)).conj_mem (v * z * v⁻¹) hz v⁻¹
        simpa [mul_assoc] using hz'
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hcore_le_V).2 hV_le_norm_core
  have hCoreV_ne_top : CoreV ≠ ⊤ := by
    intro htop
    have hV_le_core : V ≤ pCore q Q := by
      intro v hvV
      let vV : V := ⟨v, hvV⟩
      have hvCoreV : vV ∈ CoreV := by
        rw [htop]
        trivial
      simpa [CoreV, Subgroup.mem_subgroupOf] using hvCoreV
    exact (not_lt_of_ge (Subgroup.card_le_of_le hV_le_core)) hcore_lt_V
  have hS_ne_top : (S : Subgroup Q) ≠ ⊤ := by
    intro hStop
    have htop_q : IsPGroup q (⊤ : Subgroup Q) :=
      S.isPGroup'.of_equiv (MulEquiv.subgroupCongr hStop)
    exact hnot_Qp
      (htop_q.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q))
  have hV_ne_top : V ≠ ⊤ := by
    intro hVtop
    exact hS_ne_top (eq_top_iff.mpr (by intro z _hz; exact hV_le_S (by simp [hVtop])))
  let HV : Subgroup Q := Subgroup.normalizer (V : Set Q)
  have hHV_ne_top : HV ≠ ⊤ := by
    simpa [HV] using hnormalizer_V_ne_top
  have hHV_ne_bot : HV ≠ ⊥ := by
    intro hHVbot
    have hS_le_bot : (S : Subgroup Q) ≤ ⊥ := by
      simpa [HV, hHVbot] using hS_le_normalizer_V
    exact (Sylow.ne_bot_of_dvd_card (G := Q) (p := q) S hq_dvd) (le_bot_iff.mp hS_le_bot)
  have hq_dvd_HV : q ∣ Nat.card HV := by
    exact dvd_trans
      (S.dvd_card_of_dvd_card hq_dvd)
      (Subgroup.card_dvd_of_le (by simpa [HV] using hS_le_normalizer_V))
  have hHV_comp : HasNormalPComplement q HV := by
    simpa [HV] using hV_normalizer_comp
  have hVquot_p : IsPGroup q (V ⧸ CoreV) := hVp.to_quotient CoreV
  have : Fact (IsPGroup q (V ⧸ CoreV)) := ⟨hVquot_p⟩
  have hVquot_nontrivial : Nontrivial (V ⧸ CoreV) :=
    (QuotientGroup.nontrivial_iff (N := CoreV)).2 hCoreV_ne_top
  have : Nontrivial (V ⧸ CoreV) := hVquot_nontrivial
  have hVquot_center_nontrivial : Nontrivial (Subgroup.center (V ⧸ CoreV)) :=
    IsPGroup.center_nontrivial (p := q) (G := V ⧸ CoreV) hVquot_p
  have : Nontrivial (Subgroup.center (V ⧸ CoreV)) := hVquot_center_nontrivial
  let : Subgroup.Normalizes (S : Subgroup Q) V := ⟨hS_le_normalizer_V⟩
  have hCoreV_inv : IsInvariant (S : Subgroup Q) V CoreV := by
    refine ⟨?_⟩
    intro s x
    constructor
    · intro hx
      have hx_core : (x : Q) ∈ pCore q Q := by
        change (x : Q) ∈ pCore q Q at hx
        exact hx
      have hconj_core :
          ((s : Q) * (x : Q) * (s : Q)⁻¹) ∈ pCore q Q :=
        (pCore_normal (G := Q) (p := q)).conj_mem (x : Q) hx_core (s : Q)
      change (((s • x : V) : Q)) ∈ pCore q Q
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      exact hconj_core
    · intro hx
      have hx_core : (((s • x : V) : Q)) ∈ pCore q Q := by
        change (((s • x : V) : Q)) ∈ pCore q Q at hx
        exact hx
      let y : Q := (s : Q) * (x : Q) * (s : Q)⁻¹
      have hsmul_coe : (((s • x : V) : Q)) = y := by
        exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
          (A := (S : Subgroup Q)) (K := V) (a := s) (k := x)
      have hy_core : y ∈ pCore q Q := by
        rw [← hsmul_coe]
        exact hx_core
      have hback : ((s : Q)⁻¹ * y * ((s : Q)⁻¹)⁻¹) ∈ pCore q Q :=
        (pCore_normal (G := Q) (p := q)).conj_mem y hy_core ((s : Q)⁻¹)
      have hback_eq : ((s : Q)⁻¹ * y * ((s : Q)⁻¹)⁻¹) = (x : Q) := by
        dsimp [y]
        group
      change (x : Q) ∈ pCore q Q
      rwa [hback_eq] at hback
  let : IsInvariant (S : Subgroup Q) V CoreV := hCoreV_inv
  let : MulAction.QuotientAction (S : Subgroup Q) CoreV :=
    quotientAction_of_isInvariant (A := (S : Subgroup Q)) CoreV hCoreV_inv
  let : MulDistribMulAction (S : Subgroup Q) (V ⧸ CoreV) :=
    quotientMulDistribMulAction (A := (S : Subgroup Q)) (G := V) CoreV hCoreV_inv
  have hCenter_inv : IsInvariant (S : Subgroup Q) (V ⧸ CoreV)
      (Subgroup.center (V ⧸ CoreV)) := by
    simpa using
      isInvariant_of_characteristic
        (A := (S : Subgroup Q)) (G := V ⧸ CoreV) (Subgroup.center (V ⧸ CoreV))
  let : IsInvariant (S : Subgroup Q) (V ⧸ CoreV) (Subgroup.center (V ⧸ CoreV)) :=
    hCenter_inv
  let : MulDistribMulAction (S : Subgroup Q) (Subgroup.center (V ⧸ CoreV)) :=
    instMulDistribMulAction_subtype (G := V ⧸ CoreV) (A := (S : Subgroup Q))
  have hCenter_p : IsPGroup q (Subgroup.center (V ⧸ CoreV)) :=
    hVquot_p.to_subgroup (Subgroup.center (V ⧸ CoreV))
  have hcenter_dvd : q ∣ Nat.card (Subgroup.center (V ⧸ CoreV)) := by
    have hcenter_card_ne_one : Nat.card (Subgroup.center (V ⧸ CoreV)) ≠ 1 :=
      (Finite.one_lt_card_iff_nontrivial.mpr hVquot_center_nontrivial).ne'
    rcases hCenter_p.card_eq_or_dvd with hcard | hdiv
    · exact False.elim (hcenter_card_ne_one hcard)
    · exact hdiv
  have hone_fixed :
      (1 : Subgroup.center (V ⧸ CoreV)) ∈
        MulAction.fixedPoints (S : Subgroup Q) (Subgroup.center (V ⧸ CoreV)) := by
    simp [MulAction.mem_fixedPoints]
  obtain ⟨zbar, hzbar_fixed, hone_ne_zbar⟩ :=
    S.isPGroup'.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := Subgroup.center (V ⧸ CoreV)) hcenter_dvd hone_fixed
  have hzbar_ne_one : zbar ≠ 1 := by
    exact hone_ne_zbar.symm
  have hzbar_fixed_all :
      ∀ s : (S : Subgroup Q), s • zbar = zbar :=
    MulAction.mem_fixedPoints.mp hzbar_fixed
  obtain ⟨zV, hzV_bar⟩ := QuotientGroup.mk'_surjective CoreV (zbar : V ⧸ CoreV)
  let z : Q := zV
  have hz_mem_V : z ∈ V := zV.2
  have hz_not_core : z ∉ pCore q Q := by
    intro hz_core
    have hzV_core : zV ∈ CoreV := by
      simpa [z, CoreV, Subgroup.mem_subgroupOf] using hz_core
    have hzbar_eq_one : zbar = 1 := by
      apply Subtype.ext
      have hz_mk_one : QuotientGroup.mk' CoreV zV = 1 :=
        (QuotientGroup.eq_one_iff (N := CoreV) (x := zV)).2 hzV_core
      simpa [hzV_bar] using hz_mk_one
    exact hzbar_ne_one hzbar_eq_one
  have hz_comm_mod_core :
      ∀ v : Q, v ∈ V → ⁅z, v⁆ ∈ pCore q Q := by
    intro v hvV
    let vV : V := ⟨v, hvV⟩
    have hzbar_center : (zbar : V ⧸ CoreV) ∈ Subgroup.center (V ⧸ CoreV) := zbar.2
    have hcomm_q : ⁅QuotientGroup.mk' CoreV zV, QuotientGroup.mk' CoreV vV⁆ = 1 := by
      have hmul := (Subgroup.mem_center_iff.mp hzbar_center) (QuotientGroup.mk' CoreV vV)
      exact commutatorElement_eq_one_iff_mul_comm.mpr (by simpa [hzV_bar] using hmul.symm)
    have hmk_comm : QuotientGroup.mk' CoreV ⁅zV, vV⁆ = 1 := by
      simpa [map_commutatorElement] using
        (show QuotientGroup.mk' CoreV ⁅zV, vV⁆ =
            ⁅QuotientGroup.mk' CoreV zV, QuotientGroup.mk' CoreV vV⁆ from
          map_commutatorElement (f := QuotientGroup.mk' CoreV) (g₁ := zV) (g₂ := vV)).trans hcomm_q
    have hcomm_CoreV : ⁅zV, vV⁆ ∈ CoreV :=
      (QuotientGroup.eq_one_iff (N := CoreV) (x := ⁅zV, vV⁆)).1 hmk_comm
    change ((⁅zV, vV⁆ : V) : Q) ∈ pCore q Q
    exact (show ((⁅zV, vV⁆ : V) : Q) ∈ pCore q Q from by
      simpa [CoreV, Subgroup.mem_subgroupOf] using hcomm_CoreV)
  have hz_comm_mod_core_S :
      ∀ s : Q, s ∈ (S : Subgroup Q) → ⁅z, s⁆ ∈ pCore q Q := by
    intro s hsS
    let sS : (S : Subgroup Q) := ⟨s, hsS⟩
    have hfix_center := hzbar_fixed_all sS
    have hfix_coe' :
        sS • (zbar : V ⧸ CoreV) = (zbar : V ⧸ CoreV) := by
      have hcoe :
          ((sS • zbar : Subgroup.center (V ⧸ CoreV)) : V ⧸ CoreV) =
            sS • (zbar : V ⧸ CoreV) := rfl
      rw [← hcoe, hfix_center]
    have hqfix : ((sS • zV : V) : V ⧸ CoreV) = (zV : V ⧸ CoreV) := by
      calc
        ((sS • zV : V) : V ⧸ CoreV) = sS • (zV : V ⧸ CoreV) := rfl
        _ = sS • (zbar : V ⧸ CoreV) := by
            change sS • (QuotientGroup.mk' CoreV zV) = sS • (zbar : V ⧸ CoreV)
            rw [hzV_bar]
        _ = (zbar : V ⧸ CoreV) := hfix_coe'
        _ = (zV : V ⧸ CoreV) := hzV_bar.symm
    have hdiff_CoreV : (sS • zV) / zV ∈ CoreV :=
      (QuotientGroup.eq_iff_div_mem (N := CoreV)).1 hqfix
    have hdiff_core :
        (s * z * s⁻¹ * z⁻¹) ∈ pCore q Q := by
      simpa [sS, z, CoreV, Subgroup.mem_subgroupOf, div_eq_mul_inv,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc] using
        hdiff_CoreV
    have hcomm_inv : (s * z * s⁻¹ * z⁻¹)⁻¹ ∈ pCore q Q :=
      (pCore q Q).inv_mem hdiff_core
    simpa [commutatorElement_def, mul_assoc] using hcomm_inv
  have hz_isPElement : IsPElement (p := q) z := by
    rcases (IsPGroup.iff_orderOf (p := q) (G := V)).1 hVp zV with ⟨n, hn⟩
    exact ⟨n, by simpa [z, Subgroup.orderOf_coe] using hn⟩
  let Wz : Subgroup Q := pCore q Q ⊔ Subgroup.zpowers z
  have hWz_p : IsPGroup q Wz := by
    simpa [Wz] using
      hkt_pCore_sup_zpowers_isPGroup_of_isPElement (Q := Q) (q := q) hz_isPElement
  have hcore_lt_Wz : Nat.card (pCore q Q) < Nat.card Wz := by
    simpa [Wz] using hkt_card_pCore_lt_sup_zpowers_of_not_mem (Q := Q) (q := q) hz_not_core
  have hz_mem_S : z ∈ (S : Subgroup Q) := hV_le_S hz_mem_V
  have hWz_le_S : Wz ≤ (S : Subgroup Q) := by
    simpa [Wz] using hkt_pCore_sup_zpowers_le_sylow_of_mem (Q := Q) (q := q) S hz_mem_S
  have hS_le_normalizer_Wz : (S : Subgroup Q) ≤ Subgroup.normalizer (Wz : Set Q) := by
    simpa [Wz] using
      hkt_pCore_sup_zpowers_le_normalizer_of_comm_mod_core
        (Q := Q) (q := q) (z := z) (S := (S : Subgroup Q)) hz_comm_mod_core_S
  have hnormalizer_Wz_ne_top : Subgroup.normalizer (Wz : Set Q) ≠ ⊤ := by
    intro htop
    have hWz_normal : Wz.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hWz_le_core : Wz ≤ pCore q Q := le_sSup ⟨hWz_normal, hWz_p⟩
    exact (not_lt_of_ge (Subgroup.card_le_of_le hWz_le_core)) hcore_lt_Wz
  have hWz_ne_bot : Wz ≠ ⊥ := by
    intro hbot
    have hcardWz : Nat.card Wz = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    have hcore_pos : 1 ≤ Nat.card (pCore q Q) := Nat.succ_le_of_lt Nat.card_pos
    have hcore_lt_one : Nat.card (pCore q Q) < 1 := by
      calc
        Nat.card (pCore q Q) < Nat.card Wz := hcore_lt_Wz
        _ = 1 := hcardWz
    exact (not_lt_of_ge hcore_pos) hcore_lt_one
  have hfactor_Wz :
      Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q ≤
        Nat.factorization (Nat.card (Subgroup.normalizer (Wz : Set Q))) q := by
    have hfactorS_Q :
        Nat.factorization (Nat.card (S : Subgroup Q)) q =
          Nat.factorization (Nat.card Q) q :=
      section8_factorization_card_sylow (G := Q) (p := q) S
    have hS_dvd_Wz_norm : Nat.card (S : Subgroup Q) ∣ Nat.card (Subgroup.normalizer (Wz : Set Q)) :=
      Subgroup.card_dvd_of_le hS_le_normalizer_Wz
    have hfactorS_le_Wz_norm :
        Nat.factorization (Nat.card (S : Subgroup Q)) q ≤
          Nat.factorization (Nat.card (Subgroup.normalizer (Wz : Set Q))) q :=
      Nat.factorization_le_factorization_of_dvd_right
        hS_dvd_Wz_norm Nat.card_pos.ne' Nat.card_pos.ne'
    have hnormU_card : Nat.card (Subgroup.normalizer (U : Set Q)) = Nat.card Q := by
      rw [hNtop]
      simp
    calc
      Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q =
          Nat.factorization (Nat.card Q) q := by rw [hnormU_card]
      _ = Nat.factorization (Nat.card (S : Subgroup Q)) q := hfactorS_Q.symm
      _ ≤ Nat.factorization (Nat.card (Subgroup.normalizer (Wz : Set Q))) q :=
        hfactorS_le_Wz_norm
  have hnormalizer_Wz_comp : HasNormalPComplement q (↥(Subgroup.normalizer (Wz : Set Q))) := by
    by_contra hcompWz
    have hscore :=
      hUmax Wz hWz_ne_bot hWz_p hcompWz
    have hfactor_le :
        Nat.factorization (Nat.card (Subgroup.normalizer (Wz : Set Q))) q ≤
          Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q :=
      huppertIV62_normalizer_factorization_le_of_score_le
        (U := U) (V := Wz) hscore
    have hfactor_eq :
        Nat.factorization (Nat.card (Subgroup.normalizer (Wz : Set Q))) q =
          Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q :=
      le_antisymm hfactor_le hfactor_Wz
    have hcard_le : Nat.card Wz ≤ Nat.card U :=
      huppertIV62_card_le_of_factorization_eq_score_le
        (U := U) (V := Wz) hfactor_eq hscore
    exact (not_lt_of_ge hcard_le) (by simpa [Wz, hU_eq_core] using hcore_lt_Wz)
  exact hkt_isPElement_mem_pCore_terminal_from_Wz
    (Q := Q) (q := q) hcore_bot hnot_Qp hq2 S hq_dvd hnot_burnside
    hcentralizer_dvd hnormalizer_rank_dvd hproper_rec hsmall_rec hU_ne_bot hU_p hU_no_complement hUmax P hUS
    hUN_le_P hcardUP hNtop hU_eq_core
    (z := z) (Wz := Wz) (by rfl) hz_not_core hz_mem_S hWz_p hWz_le_S
    hS_le_normalizer_Wz hnormalizer_Wz_comp hz_comm_mod_core_S
private theorem hkt_isPElement_mem_pCore_of_selected_pSubgroup_eq_pCore_reduced_nonburnside
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (hnot_Qp : ¬ IsPGroup q Q)
    (hq2 : q ≠ 2) (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    {U : Subgroup Q}
    (hU_ne_bot : U ≠ ⊥) (hU_p : IsPGroup q U)
    (hU_no_complement : ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))))
    (hUmax :
      ∀ W : Subgroup Q,
        W ≠ ⊥ →
        IsPGroup q W →
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
          Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q *
              (Nat.card Q + 1) + Nat.card W ≤
            Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q *
              (Nat.card Q + 1) + Nat.card U)
    (P : Sylow q (Subgroup.normalizer (U : Set Q)))
    (hUS : U < (S : Subgroup Q))
    (hUN_le_P :
      U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≤
        (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hcardUP :
      Nat.card U < Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hPmap_le_S :
      (P : Subgroup (Subgroup.normalizer (U : Set Q))).map
          (Subgroup.normalizer (U : Set Q)).subtype ≤ (S : Subgroup Q))
    (hproper_rec :
      ∀ (H : Subgroup Q) (T : Sylow q H),
        H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q
          (Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q H)
    (hsmall_rec :
      ∀ {R : Type u} [Group R] [Finite R] (T : Sylow q R),
        Nat.card R < Nat.card Q → q ∣ Nat.card R →
        HasNormalPComplement q
          (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q R)
    (_hcenter_local :
      HasNormalPComplement q
        (Subgroup.centralizer
          (centerIn (G := Subgroup.normalizer (U : Set Q))
            (P : Subgroup (Subgroup.normalizer (U : Set Q))) :
              Set (Subgroup.normalizer (U : Set Q)))))
    (_hJrank_local :
      HasNormalPComplement q
        (Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Subgroup.normalizer (U : Set Q))
            (P : Subgroup (Subgroup.normalizer (U : Set Q))) :
              Set (Subgroup.normalizer (U : Set Q)))))
    (hNtop : Subgroup.normalizer (U : Set Q) = ⊤)
    (hU_eq_core : U = pCore q Q)
    {x : Q} (hx : IsPElement (p := q) x) :
    x ∈ pCore q Q := by
  classical
  refine hkt_isPElement_mem_pCore_of_sylow_absorption (Q := Q) (q := q) S ?_ hx
  intro y hyS hy
  by_contra hy_not_core
  have hUy_p :
      IsPGroup q (pCore q Q ⊔ Subgroup.zpowers y : Subgroup Q) :=
    hkt_pCore_sup_zpowers_isPGroup_of_isPElement (Q := Q) (q := q) hy
  have hUy_card :
      Nat.card (pCore q Q) <
        Nat.card (pCore q Q ⊔ Subgroup.zpowers y : Subgroup Q) :=
    hkt_card_pCore_lt_sup_zpowers_of_not_mem (Q := Q) (q := q) hy_not_core
  have hUy_ne_core :
      pCore q Q ≠ (pCore q Q ⊔ Subgroup.zpowers y : Subgroup Q) := by
    intro hEq
    have hcard_eq :
        Nat.card (pCore q Q) =
          Nat.card (pCore q Q ⊔ Subgroup.zpowers y : Subgroup Q) :=
      congrArg (fun H : Subgroup Q => Nat.card H) hEq
    exact (lt_irrefl _) (hUy_card.trans_le (le_of_eq hcard_eq.symm))
  have hpCore_le_S : pCore q Q ≤ (S : Subgroup Q) :=
    hkt_pCore_le_sylow (Q := Q) (q := q) S
  have hUy_le_S : pCore q Q ⊔ Subgroup.zpowers y ≤ (S : Subgroup Q) :=
    hkt_pCore_sup_zpowers_le_sylow_of_mem (Q := Q) (q := q) S hyS
  have hU_le_Pmap :
      U ≤ (P : Subgroup (Subgroup.normalizer (U : Set Q))).map
          (Subgroup.normalizer (U : Set Q)).subtype := by
    intro u huU
    have huN : u ∈ Subgroup.normalizer (U : Set Q) :=
      (Subgroup.le_normalizer (H := U)) huU
    exact Subgroup.mem_map.mpr
      ⟨⟨u, huN⟩, hUN_le_P (by simpa [Subgroup.mem_subgroupOf] using huU), rfl⟩
  have hpcore_le_Pmap :
      pCore q Q ≤ (P : Subgroup (Subgroup.normalizer (U : Set Q))).map
          (Subgroup.normalizer (U : Set Q)).subtype := by
    simpa [← hU_eq_core] using hU_le_Pmap
  have hPmap_eq_S :
      (P : Subgroup (Subgroup.normalizer (U : Set Q))).map
          (Subgroup.normalizer (U : Set Q)).subtype = (S : Subgroup Q) :=
    hkt_local_sylow_map_eq_ambient_of_normalizer_top
      (Q := Q) (q := q) (U := U) S P hNtop hPmap_le_S
  have hUy_le_Pmap :
      pCore q Q ⊔ Subgroup.zpowers y ≤
        (P : Subgroup (Subgroup.normalizer (U : Set Q))).map
          (Subgroup.normalizer (U : Set Q)).subtype := by
    simpa [hPmap_eq_S] using hUy_le_S
  let N : Subgroup Q := Subgroup.normalizer (U : Set Q)
  let UN : Subgroup N := U.subgroupOf N
  let UP : Subgroup (P : Subgroup N) := UN.subgroupOf (P : Subgroup N)
  have hU_le_N : U ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := U))
  have hUN_le_P' : UN ≤ (P : Subgroup N) := by
    simpa [UN, N] using hUN_le_P
  have hUN_card : Nat.card UN = Nat.card U := by
    simpa [UN, N] using
      Nat.card_congr
        ((Subgroup.subgroupOfEquivOfLe (H := U) (K := N) hU_le_N).toEquiv)
  have hUP_card : Nat.card UP = Nat.card U := by
    have hUP_UN : Nat.card UP = Nat.card UN := by
      simpa [UP] using
        Nat.card_congr
          ((Subgroup.subgroupOfEquivOfLe (H := UN) (K := (P : Subgroup N))
            hUN_le_P').toEquiv)
    exact hUP_UN.trans hUN_card
  have hyPmap :
      y ∈ (P : Subgroup N).map N.subtype := by
    simpa [N, hPmap_eq_S] using hyS
  rcases Subgroup.mem_map.mp hyPmap with ⟨yN, hyP, hyN_eq⟩
  let yP : (P : Subgroup N) := ⟨yN, hyP⟩
  let K : Subgroup (P : Subgroup N) :=
    UP ⊔ Subgroup.normalClosure ({yP} : Set (P : Subgroup N))
  have hUN_normal : UN.Normal := by
    simpa [UN, N] using hkt_subgroupOf_normalizer_normal U
  let : UN.Normal := hUN_normal
  have hUP_normal : UP.Normal := by
    simpa [UP] using (inferInstance : (UN.subgroupOf (P : Subgroup N)).Normal)
  let : UP.Normal := hUP_normal
  have hK_normal : K.Normal := by
    dsimp [K]
    infer_instance
  let : K.Normal := hK_normal
  have hyP_mem_K : yP ∈ K := by
    exact (le_sup_right :
        Subgroup.normalClosure ({yP} : Set (P : Subgroup N)) ≤ K)
      (Subgroup.subset_normalClosure (by simp))
  have hyP_not_UP : yP ∉ UP := by
    intro hyUP
    have hyU : (yP : N) ∈ UN := by
      simpa [UP, Subgroup.mem_subgroupOf] using hyUP
    have hyUQ : (yP : Q) ∈ U := by
      simpa [UN, N, Subgroup.mem_subgroupOf] using hyU
    have hy_coe : (yP : Q) = y := by
      simpa [yP, N] using hyN_eq
    exact hy_not_core (by simpa [hU_eq_core, hy_coe] using hyUQ)
  have hUP_lt_K : UP < K := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro hUP_eq_K
    exact hyP_not_UP (by simpa [← hUP_eq_K] using hyP_mem_K)
  have hK_card_gt : Nat.card U < Nat.card K := by
    have hUP_card_lt : Nat.card UP < Nat.card K :=
      natCard_lt_of_subgroup_lt (G := (P : Subgroup N)) hUP_lt_K
    simpa [hUP_card] using hUP_card_lt
  let K_N : Subgroup N := K.map (P : Subgroup N).subtype
  let V : Subgroup Q := K_N.map N.subtype
  have hV_normalizer_comp :
      HasNormalPComplement q (↥(Subgroup.normalizer (V : Set Q))) := by
    have hcardK_N : Nat.card K_N = Nat.card K := by
      simpa [K_N, N] using
        Subgroup.card_map_of_injective (K := K) (f := (P : Subgroup N).subtype)
          (P : Subgroup N).subtype_injective
    have hcardV : Nat.card V = Nat.card K := by
      have hcardV_N : Nat.card V = Nat.card K_N := by
        simpa [V, K_N, N] using
          Subgroup.card_map_of_injective (K := K_N) (f := N.subtype) N.subtype_injective
      exact hcardV_N.trans hcardK_N
    have hV_ne_bot : V ≠ ⊥ := by
      intro hVbot
      have hcardV_one : Nat.card V = 1 := by
        rw [hVbot, Subgroup.card_bot]
      have hcardK_one : Nat.card K = 1 := by
        rw [← hcardV, hcardV_one]
      have hU_ge_one : 1 ≤ Nat.card U := Nat.succ_le_of_lt Nat.card_pos
      have hU_lt_one : Nat.card U < 1 := by
        simpa [hcardK_one] using hK_card_gt
      exact (not_lt_of_ge hU_ge_one) hU_lt_one
    have hKp : IsPGroup q K := P.isPGroup'.to_subgroup K
    have hK_Np : IsPGroup q K_N := by
      simpa [K_N, N] using hKp.map (P : Subgroup N).subtype
    have hVp : IsPGroup q V := by
      simpa [V, K_N, N] using hK_Np.map N.subtype
    let Pmap : Subgroup Q := (P : Subgroup N).map N.subtype
    have hPmap_card : Nat.card Pmap = Nat.card (P : Subgroup N) := by
      simpa [Pmap, N] using
        Subgroup.card_map_of_injective (K := (P : Subgroup N)) (f := N.subtype)
          N.subtype_injective
    have hPmap_le_normalizer_V : Pmap ≤ Subgroup.normalizer (V : Set Q) := by
      have hnormK_top : Subgroup.normalizer (K : Set (P : Subgroup N)) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr hK_normal
      have hinner_map_le :
          (Subgroup.normalizer (K : Set (P : Subgroup N))).map
              (P : Subgroup N).subtype ≤
            Subgroup.normalizer ((K.map (P : Subgroup N).subtype : Subgroup N) : Set N) :=
        hkt_normalizer_map_subtype_le_normalizer_map (G := N) (N := (P : Subgroup N)) K
      have hinner_map_top :
          (Subgroup.normalizer (K : Set (P : Subgroup N))).map
              (P : Subgroup N).subtype = (P : Subgroup N) := by
        rw [hnormK_top]
        simpa [MonoidHom.range_eq_map] using
          ((P : Subgroup N).range_subtype : (P : Subgroup N).subtype.range = (P : Subgroup N))
      have hP_le_normalizer_KN :
          (P : Subgroup N) ≤ Subgroup.normalizer (K_N : Set N) := by
        simpa [K_N, hinner_map_top] using hinner_map_le
      have hPmap_le_normKN_map :
          Pmap ≤ (Subgroup.normalizer (K_N : Set N)).map N.subtype := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
        exact Subgroup.mem_map.mpr ⟨p, hP_le_normalizer_KN hp, rfl⟩
      have hnormKN_map_le :
          (Subgroup.normalizer (K_N : Set N)).map N.subtype ≤
            Subgroup.normalizer ((K_N.map N.subtype : Subgroup Q) : Set Q) :=
        hkt_normalizer_map_subtype_le_normalizer_map (G := Q) N K_N
      exact hPmap_le_normKN_map.trans (by simpa [V] using hnormKN_map_le)
    have hPmap_dvd_normalizer : Nat.card Pmap ∣ Nat.card (Subgroup.normalizer (V : Set Q)) :=
      Subgroup.card_dvd_of_le hPmap_le_normalizer_V
    have hfactorP :
        Nat.factorization (Nat.card (P : Subgroup N)) q =
          Nat.factorization (Nat.card N) q := by
      exact section8_factorization_card_sylow (G := N) (p := q) P
    have hfactor :
        Nat.factorization (Nat.card N) q ≤
          Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q := by
      rw [← hfactorP, ← hPmap_card]
      exact Nat.factorization_le_factorization_of_dvd_right
        hPmap_dvd_normalizer Nat.card_pos.ne' Nat.card_pos.ne'
    have hcardUV : Nat.card U < Nat.card V := by
      simpa [hcardV] using hK_card_gt
    by_contra hcompV
    have hscore :=
      hUmax V hV_ne_bot hVp hcompV
    have hfactor_le :
        Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q ≤
          Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q :=
      huppertIV62_normalizer_factorization_le_of_score_le
        (U := U) (V := V) hscore
    have hfactor_eq :
        Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q =
          Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q :=
      le_antisymm hfactor_le (by
        change
          Nat.factorization (Nat.card N) q ≤
            Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q
        exact hfactor)
    have hcard_le : Nat.card V ≤ Nat.card U :=
      huppertIV62_card_le_of_factorization_eq_score_le
        (U := U) (V := V) hfactor_eq hscore
    exact (not_lt_of_ge hcard_le) hcardUV
  have hU_le_V : U ≤ V := by
    intro u huU
    let uN : N := ⟨u, hU_le_N huU⟩
    let uP : (P : Subgroup N) := ⟨uN, hUN_le_P' (Subgroup.mem_subgroupOf.mpr huU)⟩
    have huUP : uP ∈ UP := by
      simpa [uP, uN, UP, UN, Subgroup.mem_subgroupOf] using huU
    have huK : uP ∈ K := (le_sup_left : UP ≤ K) huUP
    have huKN : (uP : N) ∈ K_N := Subgroup.mem_map.mpr ⟨uP, huK, rfl⟩
    exact Subgroup.mem_map.mpr ⟨(uP : N), huKN, rfl⟩
  have hyV : y ∈ V := by
    have hyKN : (yP : N) ∈ K_N := Subgroup.mem_map.mpr ⟨yP, hyP_mem_K, rfl⟩
    exact Subgroup.mem_map.mpr ⟨(yP : N), hyKN, by simpa [yP, N] using hyN_eq⟩
  have hUy_le_V : pCore q Q ⊔ Subgroup.zpowers y ≤ V := by
    refine sup_le ?_ ?_
    · simpa [← hU_eq_core] using hU_le_V
    · exact Subgroup.zpowers_le.2 hyV
  have hVp : IsPGroup q V := by
    have hKp : IsPGroup q K := P.isPGroup'.to_subgroup K
    have hK_Np : IsPGroup q K_N := by
      simpa [K_N, N] using hKp.map (P : Subgroup N).subtype
    simpa [V, K_N, N] using hK_Np.map N.subtype
  have hcore_lt_V : Nat.card (pCore q Q) < Nat.card V := by
    exact hUy_card.trans_le (Subgroup.card_le_of_le hUy_le_V)
  have hV_le_S : V ≤ (S : Subgroup Q) := by
    intro z hzV
    rcases Subgroup.mem_map.mp hzV with ⟨kN, hkN, rfl⟩
    rcases Subgroup.mem_map.mp hkN with ⟨k, hkK, rfl⟩
    exact hPmap_eq_S ▸ Subgroup.mem_map.mpr ⟨(k : N), k.2, rfl⟩
  have hPmap_le_normalizer_V :
      (P : Subgroup N).map N.subtype ≤ Subgroup.normalizer (V : Set Q) := by
    let Pmap : Subgroup Q := (P : Subgroup N).map N.subtype
    have hnormK_top : Subgroup.normalizer (K : Set (P : Subgroup N)) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hK_normal
    have hinner_map_le :
        (Subgroup.normalizer (K : Set (P : Subgroup N))).map
            (P : Subgroup N).subtype ≤
          Subgroup.normalizer ((K.map (P : Subgroup N).subtype : Subgroup N) : Set N) :=
      hkt_normalizer_map_subtype_le_normalizer_map (G := N) (N := (P : Subgroup N)) K
    have hinner_map_top :
        (Subgroup.normalizer (K : Set (P : Subgroup N))).map
            (P : Subgroup N).subtype = (P : Subgroup N) := by
      rw [hnormK_top]
      simpa [MonoidHom.range_eq_map] using
        ((P : Subgroup N).range_subtype : (P : Subgroup N).subtype.range = (P : Subgroup N))
    have hP_le_normalizer_KN :
        (P : Subgroup N) ≤ Subgroup.normalizer (K_N : Set N) := by
      simpa [K_N, hinner_map_top] using hinner_map_le
    have hPmap_le_normKN_map :
        Pmap ≤ (Subgroup.normalizer (K_N : Set N)).map N.subtype := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
      exact Subgroup.mem_map.mpr ⟨p, hP_le_normalizer_KN hp, rfl⟩
    have hnormKN_map_le :
        (Subgroup.normalizer (K_N : Set N)).map N.subtype ≤
          Subgroup.normalizer ((K_N.map N.subtype : Subgroup Q) : Set Q) :=
      hkt_normalizer_map_subtype_le_normalizer_map (G := Q) N K_N
    change Pmap ≤ Subgroup.normalizer (V : Set Q)
    exact hPmap_le_normKN_map.trans (by simpa [V] using hnormKN_map_le)
  have hS_le_normalizer_V : (S : Subgroup Q) ≤ Subgroup.normalizer (V : Set Q) := by
    simpa [N, hPmap_eq_S] using hPmap_le_normalizer_V
  have hnormalizer_V_ne_top : Subgroup.normalizer (V : Set Q) ≠ ⊤ := by
    intro htop
    have hVnormal : V.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hV_le_core : V ≤ pCore q Q := by
      exact le_sSup ⟨hVnormal, hVp⟩
    exact (not_lt_of_ge (Subgroup.card_le_of_le hV_le_core)) hcore_lt_V
  have hcore_le_V : pCore q Q ≤ V := by
    simpa [← hU_eq_core] using hU_le_V
  exact hkt_isPElement_mem_pCore_terminal_from_selected_overgroup
    (Q := Q) (q := q) hcore_bot hnot_Qp hq2 S hq_dvd hnot_burnside
    hcentralizer_dvd hnormalizer_rank_dvd hproper_rec hsmall_rec
    hU_ne_bot hU_p hU_no_complement hUmax P hUS hUN_le_P hcardUP
    hNtop hU_eq_core (V := V) hV_normalizer_comp hcore_le_V hcore_lt_V
    hV_le_S hVp hS_le_normalizer_V hnormalizer_V_ne_top

/-- Huppert IV.6.2(f)--(r), isolated p-length core after the maximal bad
subgroup has been identified with `O_q(Q)`.  The source proof constructs
`Q = O_q(Q) ⋊ R`, proves the elementary-abelian minimal normal layer in
`Q/O_q(Q)`, and finishes with the two-dimensional linear contradiction. -/
private theorem hkt_hasPLengthOne_of_selected_pSubgroup_eq_pCore_reduced_nonburnside
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (hnot_Qp : ¬ IsPGroup q Q)
    (hq2 : q ≠ 2) (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    {U : Subgroup Q}
    (hU_ne_bot : U ≠ ⊥) (hU_p : IsPGroup q U)
    (hU_no_complement : ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))))
    (hUmax :
      ∀ W : Subgroup Q,
        W ≠ ⊥ →
        IsPGroup q W →
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
          Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q *
              (Nat.card Q + 1) + Nat.card W ≤
            Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q *
              (Nat.card Q + 1) + Nat.card U)
    (P : Sylow q (Subgroup.normalizer (U : Set Q)))
    (hUS : U < (S : Subgroup Q))
    (hUN_le_P :
      U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≤
        (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hcardUP :
      Nat.card U < Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hPmap_le_S :
      (P : Subgroup (Subgroup.normalizer (U : Set Q))).map
          (Subgroup.normalizer (U : Set Q)).subtype ≤ (S : Subgroup Q))
    (hproper_rec :
      ∀ (H : Subgroup Q) (T : Sylow q H),
        H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q
          (Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q H)
    (hsmall_rec :
      ∀ {R : Type u} [Group R] [Finite R] (T : Sylow q R),
        Nat.card R < Nat.card Q → q ∣ Nat.card R →
        HasNormalPComplement q
          (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q R)
    (hcenter_local :
      HasNormalPComplement q
        (Subgroup.centralizer
          (centerIn (G := Subgroup.normalizer (U : Set Q))
            (P : Subgroup (Subgroup.normalizer (U : Set Q))) :
              Set (Subgroup.normalizer (U : Set Q)))))
    (hJrank_local :
      HasNormalPComplement q
        (Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Subgroup.normalizer (U : Set Q))
            (P : Subgroup (Subgroup.normalizer (U : Set Q))) :
              Set (Subgroup.normalizer (U : Set Q)))))
    (hNtop : Subgroup.normalizer (U : Set Q) = ⊤)
    (hU_eq_core : U = pCore q Q) :
    HasPLengthOne q Q := by
  have hle : pElementsSubgroup q Q ≤ Op_p'p q Q := by
    have hle_core : pElementsSubgroup q Q ≤ pCore q Q := by
      unfold pElementsSubgroup
      exact (Subgroup.closure_le (K := pCore q Q)).2 (by
        intro x hx
        exact
          hkt_isPElement_mem_pCore_of_selected_pSubgroup_eq_pCore_reduced_nonburnside
            (Q := Q) (q := q) hcore_bot hnot_Qp hq2 S hq_dvd hnot_burnside
            hcentralizer_dvd hnormalizer_rank_dvd hU_ne_bot hU_p hU_no_complement hUmax P hUS hUN_le_P hcardUP
            hPmap_le_S hproper_rec hsmall_rec hcenter_local hJrank_local hNtop hU_eq_core hx)
    have hOp_eq : Op_p'p q Q = pCore q Q :=
      Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := Q) (p := q) hcore_bot
    simpa [hOp_eq] using hle_core
  exact hkt_hasPLengthOne_of_pElementsSubgroup_le_Op_p'p (Q := Q) (q := q) hle
/-- Huppert IV.6.2(e)--(r), after the maximal bad subgroup has been shown to
be the largest normal `q`-subgroup.  This is the remaining Thompson-specific
part of the reduced proof: from `U = O_q(Q)`, `O_{q'}(Q)=1`, the non-Burnside
hypothesis, and the two local hypotheses, the assumed non-`q`-group branch is
impossible. -/
private theorem hkt_false_of_selected_pSubgroup_eq_pCore_reduced_nonburnside
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥) (hnot_Qp : ¬ IsPGroup q Q)
    (hq2 : q ≠ 2) (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    {U : Subgroup Q}
    (hU_ne_bot : U ≠ ⊥) (hU_p : IsPGroup q U)
    (hU_no_complement : ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))))
    (hUmax :
      ∀ W : Subgroup Q,
        W ≠ ⊥ →
        IsPGroup q W →
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
          Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q *
              (Nat.card Q + 1) + Nat.card W ≤
            Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q *
              (Nat.card Q + 1) + Nat.card U)
    (P : Sylow q (Subgroup.normalizer (U : Set Q)))
    (hUS : U < (S : Subgroup Q))
    (hUN_le_P :
      U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≤
        (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hcardUP :
      Nat.card U < Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))))
    (hPmap_le_S :
      (P : Subgroup (Subgroup.normalizer (U : Set Q))).map
          (Subgroup.normalizer (U : Set Q)).subtype ≤ (S : Subgroup Q))
    (hproper_rec :
      ∀ (H : Subgroup Q) (T : Sylow q H),
        H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q
          (Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q H)
    (hsmall_rec :
      ∀ {R : Type u} [Group R] [Finite R] (T : Sylow q R),
        Nat.card R < Nat.card Q → q ∣ Nat.card R →
        HasNormalPComplement q
          (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q R)
    (hcenter_local :
      HasNormalPComplement q
        (Subgroup.centralizer
          (centerIn (G := Subgroup.normalizer (U : Set Q))
            (P : Subgroup (Subgroup.normalizer (U : Set Q))) :
              Set (Subgroup.normalizer (U : Set Q)))))
    (hJrank_local :
      HasNormalPComplement q
        (Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Subgroup.normalizer (U : Set Q))
            (P : Subgroup (Subgroup.normalizer (U : Set Q))) :
              Set (Subgroup.normalizer (U : Set Q)))))
    (hNtop : Subgroup.normalizer (U : Set Q) = ⊤)
    (hU_eq_core : U = pCore q Q) : False := by
  classical
  have hnot_compQ : ¬ HasNormalPComplement q Q := by
    intro hcompQ
    exact hnot_Qp
      (hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
        (Q := Q) (p := q) hcore_bot hcompQ)
  have hUnormal : U.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  have hpcore_ne_bot : pCore q Q ≠ ⊥ := by
    intro hpcore_bot
    exact hU_ne_bot (by simp [hU_eq_core, hpcore_bot])
  have hpcore_lt_S : pCore q Q < (S : Subgroup Q) := by
    simpa [hU_eq_core] using hUS
  have hpcore_le_S : pCore q Q ≤ (S : Subgroup Q) := hpcore_lt_S.le
  have hS_not_normal : ¬ (S : Subgroup Q).Normal := by
    intro hSnormal
    have hS_le_pcore : (S : Subgroup Q) ≤ pCore q Q :=
      le_sSup ⟨hSnormal, S.isPGroup'⟩
    exact (not_lt_of_ge hS_le_pcore) hpcore_lt_S
  have hN_S_ne_top : Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≠ ⊤ := by
    intro htop
    exact hS_not_normal (Subgroup.normalizer_eq_top_iff.mp htop)
  -- This is the source continuation after Huppert IV.6.2(e): construct the
  -- solvable structure `Q = O_q(Q) ⋊ R`, prove the elementary-abelian minimal
  -- normal complement layer, then use the Thompson subgroup/centralizer
  -- hypotheses to force p-length one.  Once that core is available, the
  -- contradiction is purely formal: every `q`-subgroup lies in `O_q(Q)`.
  have hplenQ : HasPLengthOne q Q :=
    hkt_hasPLengthOne_of_selected_pSubgroup_eq_pCore_reduced_nonburnside
      (Q := Q) (q := q) hcore_bot hnot_Qp hq2 S hq_dvd
      hnot_burnside hcentralizer_dvd hnormalizer_rank_dvd hU_ne_bot hU_p hU_no_complement hUmax P hUS hUN_le_P
      hcardUP hPmap_le_S hproper_rec hsmall_rec hcenter_local hJrank_local hNtop hU_eq_core
  have hS_le_pcore : (S : Subgroup Q) ≤ pCore q Q :=
    pSubgroup_le_pCore_of_hasPLengthOne_of_pPrimeCore_eq_bot
      (Q := Q) (p := q) (A := (S : Subgroup Q)) S.isPGroup' hplenQ hcore_bot
  exact (not_lt_of_ge hS_le_pcore) hpcore_lt_S

private theorem hkt_thompson_iv62_pPrimeCore_eq_bot_isPGroup_of_local_p_nilpotence_proper_nonburnside_step
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥)
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    (_hcentralizer_ne_top :
      Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤)
    (_hnormalizer_ne_top :
      Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤)
    (hsmaller_rec :
      ∀ {R : Type u} [Group R] [Finite R] (T : Sylow q R),
        Nat.card R < Nat.card Q → q ∣ Nat.card R →
        HasNormalPComplement q
          (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R)) →
        HasNormalPComplement q R) :
    IsPGroup q Q := by
  classical
  by_contra hnot_Qp
  have hproper_rec :
      ∀ (H : Subgroup Q) (T : Sylow q H),
        H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q
          (Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H)) →
        HasNormalPComplement q H := by
    intro H T hH_ne_bot hH_ne_top hqH hcenterH hJrankH
    by_cases hburnsideH :
        (T : Subgroup H) ≤ centerIn (G := H) (Subgroup.normalizer (T : Subgroup H))
    · exact hkt_hasNormalPComplement_of_sylow_le_center_normalizer T hburnsideH
    by_cases hcenterH_top :
        Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H) = ⊤
    · exact hkt_hasNormalPComplement_of_subgroup_eq_top
        (Subgroup.centralizer (centerIn (G := H) (T : Subgroup H) : Set H))
        hcenterH_top hcenterH
    by_cases hJrankH_top :
        Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H) = ⊤
    · exact hkt_hasNormalPComplement_of_subgroup_eq_top
        (Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := H) (T : Subgroup H) : Set H))
        hJrankH_top hJrankH
    let M : Subgroup H := pPrimeCore q H
    let π : H →* H ⧸ M := QuotientGroup.mk' M
    let Hbar : Type u := H ⧸ M
    let Tbar : Sylow q Hbar :=
      T.mapSurjective (f := π) (QuotientGroup.mk'_surjective M)
    have hcore_bar : pPrimeCore q Hbar = ⊥ := by
      simpa [Hbar, M] using pPrimeCore_quotient_pPrimeCore_eq_bot (G := H) (p := q)
    have hq_dvd_bar : q ∣ Nat.card Hbar := by
      simpa [Hbar, M] using
        hkt_dvd_card_quotient_pPrimeCore_of_dvd_card (Q := H) (p := q) hqH
    have hnot_burnside_bar :
        ¬ (Tbar : Subgroup Hbar) ≤
          centerIn (G := Hbar) (Subgroup.normalizer (Tbar : Subgroup Hbar)) := by
      simpa [Hbar, M, π, Tbar] using
        hkt_quotient_pPrimeCore_nonburnside_of_nonburnside
          (Q := H) (q := q) T hburnsideH
    have hcentralizer_bar :
        HasNormalPComplement q
          (↥(Subgroup.centralizer
            (centerIn (G := Hbar) (Tbar : Subgroup Hbar) : Set Hbar))) := by
      simpa [Hbar, M, π, Tbar] using
        hkt_centralizer_center_sylow_hasNormalPComplement_quotient_pPrimeCore
          (Q := H) (p := q) T hcenterH
    have hnormalizer_rank_bar :
        HasNormalPComplement q
          (↥(Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := Hbar) (Tbar : Subgroup Hbar) : Set Hbar))) := by
      simpa [Hbar, M, π, Tbar] using
        hkt_normalizer_huppertRankThompsonSubgroup_hasNormalPComplement_quotient_pPrimeCore
          (Q := H) (p := q) T hJrankH
    by_cases hcenter_bar_top :
        Subgroup.centralizer
            (centerIn (G := Hbar) (Tbar : Subgroup Hbar) : Set Hbar) = ⊤
    · have hcomp_bar : HasNormalPComplement q Hbar :=
        hkt_hasNormalPComplement_of_subgroup_eq_top
          (Subgroup.centralizer
            (centerIn (G := Hbar) (Tbar : Subgroup Hbar) : Set Hbar))
          hcenter_bar_top hcentralizer_bar
      have hHbar_p : IsPGroup q Hbar :=
        hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
          (Q := Hbar) (p := q) hcore_bar hcomp_bar
      exact hkt_hasNormalPComplement_of_quotient_pPrimeCore_isPGroup
        (Q := H) (p := q) (by simpa [Hbar, M] using hHbar_p)
    by_cases hnormalizer_rank_bar_top :
        Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := Hbar) (Tbar : Subgroup Hbar) : Set Hbar) = ⊤
    · have hcomp_bar : HasNormalPComplement q Hbar :=
        hkt_hasNormalPComplement_of_subgroup_eq_top
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := Hbar) (Tbar : Subgroup Hbar) : Set Hbar))
          hnormalizer_rank_bar_top hnormalizer_rank_bar
      have hHbar_p : IsPGroup q Hbar :=
        hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
          (Q := Hbar) (p := q) hcore_bar hcomp_bar
      exact hkt_hasNormalPComplement_of_quotient_pPrimeCore_isPGroup
        (Q := H) (p := q) (by simpa [Hbar, M] using hHbar_p)
    have hH_lt_Q : Nat.card H < Nat.card Q := by
      have hH_lt_top : H < (⊤ : Subgroup Q) := lt_top_iff_ne_top.mpr hH_ne_top
      simpa using natCard_lt_of_subgroup_lt (G := Q) hH_lt_top
    have hbar_le_H : Nat.card Hbar ≤ Nat.card H := by
      have hdiv : Nat.card Hbar ∣ Nat.card H := by
        simpa [Hbar, M] using Subgroup.card_quotient_dvd_card (s := M)
      exact Nat.le_of_dvd Nat.card_pos hdiv
    have hbar_lt_Q : Nat.card Hbar < Nat.card Q := lt_of_le_of_lt hbar_le_H hH_lt_Q
    have hcomp_bar : HasNormalPComplement q Hbar :=
      hsmaller_rec (R := Hbar) Tbar hbar_lt_Q hq_dvd_bar
        hcentralizer_bar hnormalizer_rank_bar
    have hHbar_p : IsPGroup q Hbar :=
      hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
        (Q := Hbar) (p := q) hcore_bar hcomp_bar
    exact hkt_hasNormalPComplement_of_quotient_pPrimeCore_isPGroup
      (Q := H) (p := q) (by simpa [Hbar, M] using hHbar_p)
  by_cases hbad : ∃ U : Subgroup Q, U ≠ ⊥ ∧ IsPGroup q U ∧
      ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q)))
  · obtain ⟨U, P, hU_ne_bot, hU_p, hU_no_complement, hUS, hUmax,
      hUN_le_P, hcardUP, hPmap_le_S⟩ := by
      classical
      show ∃ U : Subgroup Q,
        ∃ P : Sylow q (Subgroup.normalizer (U : Set Q)),
          U ≠ ⊥ ∧
            IsPGroup q U ∧
              ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))) ∧
                U < (S : Subgroup Q) ∧
                  (∀ W : Subgroup Q,
                    W ≠ ⊥ →
                    IsPGroup q W →
                      ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
                        Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q *
                            (Nat.card Q + 1) + Nat.card W ≤
                          Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q *
                            (Nat.card Q + 1) + Nat.card U) ∧
            U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≤
              (P : Subgroup (Subgroup.normalizer (U : Set Q))) ∧
            Nat.card U < Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))) ∧
            (P : Subgroup (Subgroup.normalizer (U : Set Q))).map
                (Subgroup.normalizer (U : Set Q)).subtype ≤ (S : Subgroup Q)
      obtain ⟨U0, hU0_ne_bot, hU0p, hU0_no_complement, hU0S, hU0max⟩ := by
        show ∃ U : Subgroup Q,
          U ≠ ⊥ ∧
            IsPGroup q U ∧
              ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))) ∧
                U < (S : Subgroup Q) ∧
                  ∀ V : Subgroup Q,
                    V ≠ ⊥ →
                      IsPGroup q V →
                        ¬ HasNormalPComplement q (↥(Subgroup.normalizer (V : Set Q))) →
                          Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q *
                              (Nat.card Q + 1) + Nat.card V ≤
                            Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q *
                              (Nat.card Q + 1) + Nat.card U
        let noncomplementPSubgroups : Set (Subgroup Q) :=
          {U | U ≠ ⊥ ∧ IsPGroup q U ∧
            ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q)))}
        let score : Subgroup Q → ℕ := fun U =>
          Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q *
              (Nat.card Q + 1) + Nat.card U
        have hbad' : noncomplementPSubgroups.Nonempty := by
          rcases hbad with ⟨U, hU⟩
          refine ⟨U, ?_⟩
          simpa [noncomplementPSubgroups] using hU
        have hfinite : noncomplementPSubgroups.Finite := Set.toFinite _
        obtain ⟨Upre, hUpremax'⟩ := hfinite.exists_maximalFor (f := score) _ hbad'
        have hUpre_mem_noncomplementPSubgroups : Upre ∈ noncomplementPSubgroups :=
          hUpremax'.prop
        have hUprebad : Upre ≠ ⊥ ∧ IsPGroup q Upre ∧
            ¬ HasNormalPComplement q (↥(Subgroup.normalizer (Upre : Set Q))) := by
          simpa [noncomplementPSubgroups] using hUpre_mem_noncomplementPSubgroups
        have hUpremax :
            ∀ V : Subgroup Q,
              V ≠ ⊥ →
                IsPGroup q V →
                  ¬ HasNormalPComplement q (↥(Subgroup.normalizer (V : Set Q))) →
                    Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q *
                        (Nat.card Q + 1) + Nat.card V ≤
                      Nat.factorization (Nat.card (Subgroup.normalizer (Upre : Set Q))) q *
                        (Nat.card Q + 1) + Nat.card Upre := by
          intro V hV_ne_bot hVp hV_no_complement
          have hV_mem_noncomplementPSubgroups : V ∈ noncomplementPSubgroups := by
            exact ⟨hV_ne_bot, hVp, hV_no_complement⟩
          simpa [score] using hUpremax'.le hV_mem_noncomplementPSubgroups
        obtain ⟨T, hUpreT⟩ := IsPGroup.exists_le_sylow (G := Q) (p := q) hUprebad.2.1
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q T S
        let Uselected : Subgroup Q := (MulAut.conj g) • Upre
        have hS_not_bad : ¬ ((S : Subgroup Q) ≠ ⊥ ∧ IsPGroup q (S : Subgroup Q) ∧
            ¬ HasNormalPComplement q
              (↥(Subgroup.normalizer ((S : Subgroup Q) : Set Q)))) := by
          intro hSbad
          have hNS_le_rank_normalizer :
              Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≤
                Subgroup.normalizer
                  (huppertRankThompsonSubgroup
                    (G := Q) (S : Subgroup Q) : Set Q) := by
            let JS : Subgroup S :=
              huppertRankThompsonSubgroup (G := S) (⊤ : Subgroup S)
            have : JS.Characteristic :=
              hkt_huppertRankThompsonSubgroup_top_characteristic (G := S)
            have hJS_map :
                JS.map (S : Subgroup Q).subtype =
                  huppertRankThompsonSubgroup
                    (G := Q) (S : Subgroup Q) := by
              simpa [JS] using
                hkt_huppertRankThompsonSubgroup_top_map_subtype
                  (G := Q) (S : Subgroup Q)
            have hle :=
              hkt_normalizer_le_normalizer_map_subtype_of_characteristic
                (Q := Q) (H := (S : Subgroup Q)) (K := JS)
            rw [hJS_map] at hle
            exact hle
          have hNS_comp :
              HasNormalPComplement q
                (↥(Subgroup.normalizer ((S : Subgroup Q) : Set Q))) :=
            hasNormalPComplement_of_le q
              hNS_le_rank_normalizer hnormalizer_rank_dvd
          exact hSbad.2.2 hNS_comp
        have hU_le_S : Uselected ≤ (S : Subgroup Q) := by
          dsimp [Uselected]
          calc
            (MulAut.conj g) • Upre ≤ (MulAut.conj g) • (T : Subgroup Q) := by
              intro x hx
              rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
              exact Set.mem_smul_set.mpr ⟨y, hUpreT hy, rfl⟩
            _ = ((g • T : Sylow q Q) : Subgroup Q) := by
              rw [← Sylow.coe_subgroup_smul (g := g) (P := T)]
            _ = (S : Subgroup Q) := by
              simp [hg]
        have hU_bad : Uselected ≠ ⊥ ∧ IsPGroup q Uselected ∧
            ¬ HasNormalPComplement q (↥(Subgroup.normalizer (Uselected : Set Q))) := by
          dsimp [Uselected]
          exact (huppertIV62_noncomplement_pSubgroup_conj_smul_iff (U := Upre) (g := g)).2 hUprebad
        have hU_ne_S : Uselected ≠ (S : Subgroup Q) := by
          intro hUS_eq
          have hSbad : (S : Subgroup Q) ≠ ⊥ ∧ IsPGroup q (S : Subgroup Q) ∧
              ¬ HasNormalPComplement q
                (↥(Subgroup.normalizer ((S : Subgroup Q) : Set Q))) := by
            refine ⟨?_, ?_, ?_⟩
            · intro hSbot
              exact hU_bad.1 (hUS_eq.trans hSbot)
            · rw [← hUS_eq]
              exact hU_bad.2.1
            · intro hScomp
              have hUcomp : HasNormalPComplement q
                  (↥(Subgroup.normalizer (Uselected : Set Q))) := by
                rw [hUS_eq]
                exact hScomp
              exact hU_bad.2.2 hUcomp
          exact hS_not_bad hSbad
        refine ⟨Uselected, hU_bad.1, hU_bad.2.1, hU_bad.2.2,
          lt_of_le_of_ne hU_le_S hU_ne_S, ?_⟩
        intro V hV_ne_bot hVp hV_no_complement
        dsimp [Uselected]
        change
          Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q *
              (Nat.card Q + 1) + Nat.card V ≤
            Nat.factorization
                (Nat.card (Subgroup.normalizer (((MulAut.conj g) • Upre : Subgroup Q) : Set Q))) q *
              (Nat.card Q + 1) + Nat.card ((MulAut.conj g) • Upre : Subgroup Q)
        rw [huppertIV62_score_conj_smul_eq (p := q) (U := Upre) (g := g)]
        exact hUpremax V hV_ne_bot hVp hV_no_complement
      have hU0_conditions : U0 ≠ ⊥ ∧ IsPGroup q U0 ∧
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U0 : Set Q))) :=
        ⟨hU0_ne_bot, hU0p, hU0_no_complement⟩
      obtain ⟨P0, hUN0_le_P0, hcard0⟩ := by
        show ∃ P : Sylow q (Subgroup.normalizer (U0 : Set Q)),
          U0.subgroupOf (Subgroup.normalizer (U0 : Set Q)) ≤
            (P : Subgroup (Subgroup.normalizer (U0 : Set Q))) ∧
          Nat.card U0 < Nat.card (P : Subgroup (Subgroup.normalizer (U0 : Set Q)))
        let N : Subgroup Q := Subgroup.normalizer (U0 : Set Q)
        have hU0_le_N : U0 ≤ N := by
          simpa [N] using (Subgroup.le_normalizer (H := U0))
        let UN : Subgroup N := U0.subgroupOf N
        have hUNp : IsPGroup q UN := by
          simpa [UN, N] using
            hU0p.of_equiv
              ((Subgroup.subgroupOfEquivOfLe (H := U0) (K := N) hU0_le_N).symm)
        obtain ⟨P, hUN_le_P⟩ := IsPGroup.exists_le_sylow (G := N) (p := q) hUNp
        refine ⟨P, by simpa [UN, N] using hUN_le_P, ?_⟩
        have hfact_lt :
            Nat.factorization (Nat.card U0) q < Nat.factorization (Nat.card N) q := by
          simpa [N] using hkt_factorization_lt_ambient_normalizer_of_lt_sylow (S := S) hU0S
        have hcardU0 : Nat.card U0 = q ^ Nat.factorization (Nat.card U0) q :=
          section8_card_eq_prime_pow_factorization_of_isPGroup (G := Q) (p := q) hU0p
        have hcardP :
            Nat.card (P : Subgroup N) = q ^ Nat.factorization (Nat.card N) q := by
          rw [section8_card_eq_prime_pow_factorization_of_isPGroup
            (G := N) (p := q) (H := (P : Subgroup N)) P.isPGroup']
          rw [section8_factorization_card_sylow (G := N) (p := q) P]
        calc
          Nat.card U0 = q ^ Nat.factorization (Nat.card U0) q := hcardU0
          _ < q ^ Nat.factorization (Nat.card N) q :=
            (Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime q))).2 hfact_lt
          _ = Nat.card (P : Subgroup N) := hcardP.symm
      let N0 : Subgroup Q := Subgroup.normalizer (U0 : Set Q)
      let P0map : Subgroup Q := (P0 : Subgroup N0).map N0.subtype
      have hP0map_p : IsPGroup q P0map := by
        simpa [P0map, N0] using P0.isPGroup'.map N0.subtype
      obtain ⟨R, hP0map_le_R⟩ := IsPGroup.exists_le_sylow (G := Q) (p := q) hP0map_p
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q R S
      let U : Subgroup Q := MulAut.conj g • U0
      let e : N0 ≃* (Subgroup.normalizer (U : Set Q)) := by
        dsimp [U, N0]
        exact
          (Subgroup.equivSMul (MulAut.conj g) (Subgroup.normalizer (U0 : Set Q))).trans
            (MulEquiv.subgroupCongr
              (normalizer_conj_smul_eq (U := U0) (g := g)).symm)
      let P : Sylow q (Subgroup.normalizer (U : Set Q)) := P0.mapSurjective (f := e.toMonoidHom) e.surjective
      have hconjR_eq_S : (MulAut.conj g • (R : Subgroup Q) : Subgroup Q) = (S : Subgroup Q) := by
        calc
          (MulAut.conj g • (R : Subgroup Q) : Subgroup Q) =
              ((g • R : Sylow q Q) : Subgroup Q) := by
                rw [← Sylow.coe_subgroup_smul (g := g) (P := R)]
          _ = (S : Subgroup Q) := by simp [hg]
      have hconjP0map_le_S : (MulAut.conj g • P0map : Subgroup Q) ≤ (S : Subgroup Q) := by
        intro x hx
        rcases Set.mem_smul_set.mp hx with ⟨y, hyP0, rfl⟩
        have hyR : y ∈ (R : Subgroup Q) := hP0map_le_R hyP0
        have hyConjR : (MulAut.conj g) y ∈ (MulAut.conj g • (R : Subgroup Q) : Subgroup Q) :=
          Set.mem_smul_set.mpr ⟨y, hyR, rfl⟩
        simpa [hconjR_eq_S] using hyConjR
      have hPmap_le_S :
          (P : Subgroup (Subgroup.normalizer (U : Set Q))).map (Subgroup.normalizer (U : Set Q)).subtype ≤ (S : Subgroup Q) := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨n, hnP, rfl⟩
        have hn_map : n ∈ (P0 : Subgroup N0).map e.toMonoidHom := by
          simpa [P, Sylow.coe_mapSurjective] using hnP
        rcases Subgroup.mem_map.mp hn_map with ⟨p0, hp0, hp0eq⟩
        have hp0P0map : (p0 : Q) ∈ P0map := by
          exact Subgroup.mem_map.mpr ⟨p0, hp0, rfl⟩
        have hx_conj : ((n : (Subgroup.normalizer (U : Set Q))) : Q) ∈ (MulAut.conj g • P0map : Subgroup Q) := by
          refine Set.mem_smul_set.mpr ⟨(p0 : Q), hp0P0map, ?_⟩
          calc
            (MulAut.conj g) (p0 : Q) = ((e p0 : (Subgroup.normalizer (U : Set Q))) : Q) := rfl
            _ = ((n : (Subgroup.normalizer (U : Set Q))) : Q) := congrArg (fun y : (Subgroup.normalizer (U : Set Q)) => (y : Q)) hp0eq
        exact hconjP0map_le_S hx_conj
      have hU_conditions : U ≠ ⊥ ∧ IsPGroup q U ∧
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))) := by
        dsimp [U]
        exact (huppertIV62_noncomplement_pSubgroup_conj_smul_iff (U := U0) (g := g)).2 hU0_conditions
      have hU_ne_bot : U ≠ ⊥ := hU_conditions.1
      have hU_p : IsPGroup q U := hU_conditions.2.1
      have hU_no_complement : ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))) :=
        hU_conditions.2.2
      have hUmax :
          ∀ W : Subgroup Q,
            W ≠ ⊥ →
            IsPGroup q W →
              ¬ HasNormalPComplement q (↥(Subgroup.normalizer (W : Set Q))) →
                Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q *
                    (Nat.card Q + 1) + Nat.card W ≤
                  Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q *
                    (Nat.card Q + 1) + Nat.card U := by
        intro W hW_ne_bot hWp hW_no_complement
        dsimp [U]
        change
          Nat.factorization (Nat.card (Subgroup.normalizer (W : Set Q))) q *
              (Nat.card Q + 1) + Nat.card W ≤
            Nat.factorization (Nat.card (Subgroup.normalizer (((MulAut.conj g) • U0 : Subgroup Q) : Set Q))) q *
              (Nat.card Q + 1) + Nat.card ((MulAut.conj g) • U0 : Subgroup Q)
        rw [huppertIV62_score_conj_smul_eq (p := q) (U := U0) (g := g)]
        exact hU0max W hW_ne_bot hWp hW_no_complement
      have hUN_le_P : U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≤ (P : Subgroup (Subgroup.normalizer (U : Set Q))) := by
        intro x hx
        have hxU : ((x : (Subgroup.normalizer (U : Set Q))) : Q) ∈ U := by
          simpa [Subgroup.mem_subgroupOf] using hx
        rcases Set.mem_smul_set.mp hxU with ⟨u0, hu0U, hux⟩
        have hu0N0 : u0 ∈ N0 := by
          simpa [N0] using (Subgroup.le_normalizer (H := U0) hu0U)
        let u0N : N0 := ⟨u0, hu0N0⟩
        have hu0P : u0N ∈ (P0 : Subgroup N0) := by
          have hu0UN : u0N ∈ U0.subgroupOf N0 := by
            simpa [u0N, N0, Subgroup.mem_subgroupOf] using hu0U
          simpa [N0] using hUN0_le_P0 hu0UN
        have hmapmem : e u0N ∈ (P : Subgroup (Subgroup.normalizer (U : Set Q))) := by
          have : e u0N ∈ (P0 : Subgroup N0).map e.toMonoidHom :=
            Subgroup.mem_map.mpr ⟨u0N, hu0P, rfl⟩
          simpa [P, Sylow.coe_mapSurjective] using this
        have heq : e u0N = x := by
          apply Subtype.ext
          calc
            ((e u0N : (Subgroup.normalizer (U : Set Q))) : Q) = (MulAut.conj g) u0 := rfl
            _ = ((x : (Subgroup.normalizer (U : Set Q))) : Q) := by simpa using hux
        simpa [heq] using hmapmem
      have hcardU : Nat.card U = Nat.card U0 := by
        simpa [U] using card_conj_smul (U := U0) (g := g)
      have hcardP : Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))) = Nat.card (P0 : Subgroup N0) := by
        have hmapcard : Nat.card ((P0 : Subgroup N0).map e.toMonoidHom) =
            Nat.card (P0 : Subgroup N0) :=
          Subgroup.card_map_of_injective (K := (P0 : Subgroup N0)) (f := e.toMonoidHom) e.injective
        simpa [P, Sylow.coe_mapSurjective] using hmapcard
      have hcard : Nat.card U < Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))) := by
        simpa [hcardU, hcardP] using hcard0
      have hU_le_Pmap : U ≤ (P : Subgroup (Subgroup.normalizer (U : Set Q))).map (Subgroup.normalizer (U : Set Q)).subtype := by
        intro x hxU
        have hxN : x ∈ (Subgroup.normalizer (U : Set Q)) := by
          simpa using (Subgroup.le_normalizer (H := U) hxU)
        exact Subgroup.mem_map.mpr
          ⟨⟨x, hxN⟩, hUN_le_P (by simpa [Subgroup.mem_subgroupOf] using hxU), rfl⟩
      have hU_le_S : U ≤ (S : Subgroup Q) := hU_le_Pmap.trans hPmap_le_S
      have hU_ne_S : U ≠ (S : Subgroup Q) := by
        intro hUS_eq
        let Pmap : Subgroup Q := (P : Subgroup (Subgroup.normalizer (U : Set Q))).map (Subgroup.normalizer (U : Set Q)).subtype
        have hPmap_card : Nat.card Pmap = Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))) := by
          simpa [Pmap] using
            Subgroup.card_map_of_injective (K := (P : Subgroup (Subgroup.normalizer (U : Set Q)))) (f := (Subgroup.normalizer (U : Set Q)).subtype) (Subgroup.normalizer (U : Set Q)).subtype_injective
        have hPmap_le_U : Pmap ≤ U := by
          simpa [Pmap, hUS_eq] using hPmap_le_S
        have hPmap_eq_U : Pmap = U := le_antisymm hPmap_le_U (by simpa [Pmap] using hU_le_Pmap)
        have hcard_eq : Nat.card U = Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))) := by
          rw [← hPmap_card, hPmap_eq_U]
        exact (not_lt_of_ge (le_of_eq hcard_eq.symm)) hcard
      refine ⟨U, P, hU_ne_bot, hU_p, hU_no_complement, lt_of_le_of_ne hU_le_S hU_ne_S, hUmax, ?_, ?_, ?_⟩
      · exact hUN_le_P
      · exact hcard
      · exact hPmap_le_S
    have hcenter_map_le :
        centerIn (G := Q) (S : Subgroup Q) ≤
          (centerIn (G := Subgroup.normalizer (U : Set Q))
            (P : Subgroup (Subgroup.normalizer (U : Set Q)))).map
              (Subgroup.normalizer (U : Set Q)).subtype := by
      let K : Subgroup (Subgroup.normalizer (U : Set Q)) := (S : Subgroup Q).comap (Subgroup.normalizer (U : Set Q)).subtype
      have hKp : IsPGroup q K := by
        simpa [K] using S.isPGroup'.comap_of_injective (Subgroup.normalizer (U : Set Q)).subtype (Subgroup.normalizer (U : Set Q)).subtype_injective
      have hP_le_K : (P : Subgroup (Subgroup.normalizer (U : Set Q))) ≤ K := by
        intro x hxP
        exact hPmap_le_S (Subgroup.mem_map.mpr ⟨x, hxP, rfl⟩)
      have hK_eq_P : K = (P : Subgroup (Subgroup.normalizer (U : Set Q))) := P.is_maximal' hKp hP_le_K
      intro z hz
      have hzS : z ∈ (S : Subgroup Q) := hz.1
      have hzCentS : z ∈ Subgroup.centralizer ((S : Subgroup Q) : Set Q) := hz.2
      have hzN : z ∈ (Subgroup.normalizer (U : Set Q)) := by
        rw [Subgroup.mem_normalizer_iff]
        intro u
        constructor
        · intro hu
          have hzu : z * u = u * z :=
            (Subgroup.mem_centralizer_iff.mp hzCentS u (hUS.le hu)).symm
          have hcalc : z * u * z⁻¹ = u := by
            calc
              z * u * z⁻¹ = (z * u) * z⁻¹ := by rw [mul_assoc]
              _ = (u * z) * z⁻¹ := by rw [hzu]
              _ = u := by simp
          simpa [hcalc] using hu
        · intro hu
          let w : Q := z * u * z⁻¹
          have hwS : w ∈ (S : Subgroup Q) := hUS.le hu
          have hzw : z * w = w * z :=
            (Subgroup.mem_centralizer_iff.mp hzCentS w hwS).symm
          have hu_eq : u = w := by
            calc
              u = z⁻¹ * w * z := by simp [w, mul_assoc]
              _ = w := by
                calc
                  z⁻¹ * w * z = z⁻¹ * (w * z) := by rw [mul_assoc]
                  _ = z⁻¹ * (z * w) := by rw [← hzw]
                  _ = w := by simp
          rw [hu_eq]
          exact hu
      let zN : (Subgroup.normalizer (U : Set Q)) := ⟨z, hzN⟩
      have hzK : zN ∈ K := by
        simpa [K, zN, Subgroup.mem_subgroupOf] using hzS
      have hzP : zN ∈ (P : Subgroup (Subgroup.normalizer (U : Set Q))) := by
        simpa [hK_eq_P] using hzK
      refine Subgroup.mem_map.mpr ⟨zN, ?_, rfl⟩
      refine ⟨hzP, ?_⟩
      change zN ∈ Subgroup.centralizer ((P : Subgroup (Subgroup.normalizer (U : Set Q))) : Set (Subgroup.normalizer (U : Set Q)))
      rw [Subgroup.mem_centralizer_iff]
      intro y hyP
      apply Subtype.ext
      have hyS : ((y : (Subgroup.normalizer (U : Set Q))) : Q) ∈ (S : Subgroup Q) :=
        hPmap_le_S (Subgroup.mem_map.mpr ⟨y, hyP, rfl⟩)
      exact Subgroup.mem_centralizer_iff.mp hzCentS ((y : (Subgroup.normalizer (U : Set Q))) : Q) hyS
    have hcenter_local :
        HasNormalPComplement q
          (Subgroup.centralizer
            (centerIn (G := Subgroup.normalizer (U : Set Q))
              (P : Subgroup (Subgroup.normalizer (U : Set Q))) :
                Set (Subgroup.normalizer (U : Set Q)))) :=
      hkt_hasNormalPComplement_centralizer_subgroupOf_of_ambient_le
        (G := Q) (p := q) (N := Subgroup.normalizer (U : Set Q))
        (K := centerIn (G := Subgroup.normalizer (U : Set Q))
          (P : Subgroup (Subgroup.normalizer (U : Set Q))))
        (T := centerIn (G := Q) (S : Subgroup Q))
        hcenter_map_le
        hcentralizer_dvd
    have hJrank_local :
        HasNormalPComplement q
          (Subgroup.normalizer
            (huppertRankThompsonSubgroup (G := Subgroup.normalizer (U : Set Q))
              (P : Subgroup (Subgroup.normalizer (U : Set Q))) :
                Set (Subgroup.normalizer (U : Set Q)))) := by
      set_option maxHeartbeats 800000 in
      classical
      let JN : Subgroup (Subgroup.normalizer (U : Set Q)) := huppertRankThompsonSubgroup (G := (Subgroup.normalizer (U : Set Q))) (P : Subgroup (Subgroup.normalizer (U : Set Q)))
      let Pmap : Subgroup Q := (P : Subgroup (Subgroup.normalizer (U : Set Q))).map (Subgroup.normalizer (U : Set Q)).subtype
      let V : Subgroup Q := JN.map (Subgroup.normalizer (U : Set Q)).subtype
      have hV_eq_JPmap : V = huppertRankThompsonSubgroup (G := Q) Pmap := by
        set_option maxHeartbeats 800000 in
        exact (by
          let JP : Subgroup (P : Subgroup (Subgroup.normalizer (U : Set Q))) :=
            huppertRankThompsonSubgroup (G := (P : Subgroup (Subgroup.normalizer (U : Set Q)))) ⊤
          let e : (P : Subgroup (Subgroup.normalizer (U : Set Q))) ≃* Pmap :=
            Subgroup.equivMapOfInjective (P : Subgroup (Subgroup.normalizer (U : Set Q))) (Subgroup.normalizer (U : Set Q)).subtype (Subgroup.normalizer (U : Set Q)).subtype_injective
          calc
            V = JP.map ((Subgroup.normalizer (U : Set Q)).subtype.comp (P : Subgroup (Subgroup.normalizer (U : Set Q))).subtype) := by
              rw [← Subgroup.map_map]
              simpa [V, JN, JP] using congrArg (fun K : Subgroup (Subgroup.normalizer (U : Set Q)) => K.map (Subgroup.normalizer (U : Set Q)).subtype)
                (hkt_huppertRankThompsonSubgroup_top_map_subtype
                  (G := (Subgroup.normalizer (U : Set Q))) (P : Subgroup (Subgroup.normalizer (U : Set Q)))).symm
            _ = JP.map (Pmap.subtype.comp e.toMonoidHom) := by
              have he :
                  Pmap.subtype.comp e.toMonoidHom =
                    (Subgroup.normalizer (U : Set Q)).subtype.comp
                      (P : Subgroup (Subgroup.normalizer (U : Set Q))).subtype := by
                ext j
                rfl
              exact congrArg (fun g => JP.map g) he.symm
            _ = (JP.map e.toMonoidHom).map Pmap.subtype := by
              rw [Subgroup.map_map]
            _ = (huppertRankThompsonSubgroup (G := Pmap) ⊤).map Pmap.subtype := by
              rw [hkt_huppertRankThompsonSubgroup_top_map_mulEquiv]
            _ = huppertRankThompsonSubgroup (G := Q) Pmap := by
              simpa using
                hkt_huppertRankThompsonSubgroup_top_map_subtype (G := Q) Pmap
        )
      by_contra hJ_no_comp
      have hV_no_comp : ¬ HasNormalPComplement q (↥(Subgroup.normalizer (V : Set Q))) := by
        intro hcompV
        have hmap_le : (Subgroup.normalizer (JN : Set (Subgroup.normalizer (U : Set Q)))).map (Subgroup.normalizer (U : Set Q)).subtype ≤
            Subgroup.normalizer (V : Set Q) := by
          simpa [V, JN] using
            hkt_normalizer_map_subtype_le_normalizer_map (G := Q) (Subgroup.normalizer (U : Set Q)) JN
        have hcomp_map : HasNormalPComplement q
            (↥((Subgroup.normalizer (JN : Set (Subgroup.normalizer (U : Set Q)))).map (Subgroup.normalizer (U : Set Q)).subtype)) :=
          hasNormalPComplement_of_le q hmap_le hcompV
        have hcomp_intr : HasNormalPComplement q (Subgroup.normalizer (JN : Set (Subgroup.normalizer (U : Set Q)))) :=
          hasNormalPComplement_of_map_subtype q (Subgroup.normalizer (U : Set Q)) (Subgroup.normalizer (JN : Set (Subgroup.normalizer (U : Set Q)))) hcomp_map
        exact hJ_no_comp (by simpa [JN] using hcomp_intr)
      have hU_le_N : U ≤ (Subgroup.normalizer (U : Set Q)) :=
        Subgroup.le_normalizer
      have hUN_ne_bot : U.subgroupOf (Subgroup.normalizer (U : Set Q)) ≠ ⊥ := by
        intro hUNbot
        apply hU_ne_bot
        have hcardU : Nat.card U = 1 := by
          rw [← natCard_subgroupOf_eq U (Subgroup.normalizer (U : Set Q)) hU_le_N, hUNbot, Subgroup.card_bot]
        exact (Subgroup.eq_bot_iff_card (H := U)).2 hcardU
      have hP_ne_bot : (P : Subgroup (Subgroup.normalizer (U : Set Q))) ≠ ⊥ := by
        intro hPbot
        exact hUN_ne_bot (le_bot_iff.mp (by simpa [hPbot] using hUN_le_P))
      have hcenter_ne_bot : centerIn (G := (Subgroup.normalizer (U : Set Q))) (P : Subgroup (Subgroup.normalizer (U : Set Q))) ≠ ⊥ := by
        exact section8_centerIn_ne_bot_of_isPGroup P.isPGroup' hP_ne_bot
      have hcenter_le_JN : centerIn (G := (Subgroup.normalizer (U : Set Q))) (P : Subgroup (Subgroup.normalizer (U : Set Q))) ≤ JN := by
        obtain ⟨A, hA⟩ :=
          hkt_huppertRankThompsonAbelianSubgroups_nonempty
            (G := (Subgroup.normalizer (U : Set Q))) (P : Subgroup (Subgroup.normalizer (U : Set Q)))
        let Z : Subgroup (Subgroup.normalizer (U : Set Q)) := centerIn (G := (Subgroup.normalizer (U : Set Q))) (P : Subgroup (Subgroup.normalizer (U : Set Q)))
        let AZ : Subgroup (Subgroup.normalizer (U : Set Q)) := A ⊔ Z
        have hZ_comm : IsMulCommutative Z := by
          refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
          apply Subtype.ext
          exact
            (Subgroup.mem_centralizer_iff.mp x.property.2
              (y : Subgroup.normalizer (U : Set Q)) y.property.1).symm
        have hZ_le_cent_A : Z ≤ Subgroup.centralizer (A : Set (Subgroup.normalizer (U : Set Q))) := by
          intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          exact Subgroup.mem_centralizer_iff.mp hz.2 a (hA.1 ha)
        have hA_le_cent_Z : A ≤ Subgroup.centralizer (Z : Set (Subgroup.normalizer (U : Set Q))) := by
          intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          exact (Subgroup.mem_centralizer_iff.mp hz.2 a (hA.1 ha)).symm
        have hAZ_comm : IsMulCommutative AZ := by
          have hA_self : A ≤ Subgroup.centralizer (A : Set (Subgroup.normalizer (U : Set Q))) :=
            (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1
          have hZ_self : Z ≤ Subgroup.centralizer (Z : Set (Subgroup.normalizer (U : Set Q))) :=
            (Subgroup.le_centralizer_iff_isMulCommutative (K := Z)).2 hZ_comm
          exact (Subgroup.le_centralizer_iff_isMulCommutative (K := AZ)).1
            (Subgroup.le_centralizer_sup_of_le_centralizers
              (sup_le hA_self hZ_le_cent_A) (sup_le hA_le_cent_Z hZ_self))
        have hAZ_le_P : AZ ≤ (P : Subgroup (Subgroup.normalizer (U : Set Q))) :=
          sup_le hA.1 (by
            intro z hz
            exact hz.1)
        have hA_rank_le_AZ : generatorRank A ≤ generatorRank AZ := by
          have hAp : IsPGroup q A :=
            IsPGroup.to_le (H := A)
              (K := (P : Subgroup (Subgroup.normalizer (U : Set Q))))
              P.isPGroup' hA.1
          have hAZp : IsPGroup q AZ :=
            IsPGroup.to_le (H := AZ)
              (K := (P : Subgroup (Subgroup.normalizer (U : Set Q))))
              P.isPGroup' hAZ_le_P
          let : Fact (IsPGroup q A) := ⟨hAp⟩
          let : IsMulCommutative A := hA.2.1
          let A' : Subgroup AZ := A.subgroupOf AZ
          let eA : A' ≃* A :=
            Subgroup.subgroupOfEquivOfLe (H := A) (K := AZ) le_sup_left
          exact
            (generatorRank_le_groupRank_of_commutative_pgroup (p := q) A).trans
              ((groupRank_le_of_equiv eA).trans
                ((groupRank_le_of_subgroup A').trans
                  (groupRank_le_generatorRank_of_commutative_pgroup
                    (p := q) hAZp hAZ_comm)))
        have hAZ_mem : AZ ∈
            huppertRankThompsonAbelianSubgroups (G := (Subgroup.normalizer (U : Set Q))) (P : Subgroup (Subgroup.normalizer (U : Set Q))) := by
          refine ⟨hAZ_le_P, hAZ_comm, ?_⟩
          intro C hC_le hCcomm
          exact (hA.2.2 C hC_le hCcomm).trans hA_rank_le_AZ
        have hAZ_le : AZ ≤ JN := by
          dsimp [JN, huppertRankThompsonSubgroup]
          exact le_sSup hAZ_mem
        exact le_sup_right.trans hAZ_le
      have hJN_ne_bot : JN ≠ ⊥ := by
        intro hJNbot
        apply hcenter_ne_bot
        exact le_bot_iff.mp (by simpa [hJNbot] using hcenter_le_JN)
      have hV_ne_bot : V ≠ ⊥ := by
        intro hVbot
        apply hJN_ne_bot
        exact (Subgroup.map_eq_bot_iff_of_injective (H := JN) (f := (Subgroup.normalizer (U : Set Q)).subtype)
          (Subgroup.normalizer (U : Set Q)).subtype_injective).1 (by simpa [V] using hVbot)
      have hJN_le_P : JN ≤ (P : Subgroup (Subgroup.normalizer (U : Set Q))) := by
        simpa [JN] using
          huppertRankThompsonSubgroup_le (G := (Subgroup.normalizer (U : Set Q))) (P : Subgroup (Subgroup.normalizer (U : Set Q)))
      have hJNp : IsPGroup q JN :=
        IsPGroup.to_le (H := JN) (K := (P : Subgroup (Subgroup.normalizer (U : Set Q)))) P.isPGroup' hJN_le_P
      have hVp : IsPGroup q V := by
        simpa [V, JN] using hJNp.map (Subgroup.normalizer (U : Set Q)).subtype
      have hscore := hUmax V hV_ne_bot hVp hV_no_comp
      have hfactor_V_le_U :
          Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q ≤
            Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q :=
        huppertIV62_normalizer_factorization_le_of_score_le
          (Q := Q) (p := q) (U := U) (V := V) hscore
      have hPmap_card : Nat.card Pmap = Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q))) := by
        simpa [Pmap] using
          Subgroup.card_map_of_injective (K := (P : Subgroup (Subgroup.normalizer (U : Set Q)))) (f := (Subgroup.normalizer (U : Set Q)).subtype)
            (Subgroup.normalizer (U : Set Q)).subtype_injective
      have hfactorP :
          Nat.factorization (Nat.card (P : Subgroup (Subgroup.normalizer (U : Set Q)))) q =
            Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q :=
        section8_factorization_card_sylow (G := (Subgroup.normalizer (U : Set Q))) (p := q) P
      have hfactorPmap :
          Nat.factorization (Nat.card Pmap) q = Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q := by
        rw [hPmap_card, hfactorP]
      have hPmap_not_lt_S : ¬ Pmap < (S : Subgroup Q) := by
        intro hPmap_lt_S
        have hfact_lt :
            Nat.factorization (Nat.card Pmap) q <
              Nat.factorization (Nat.card (Subgroup.normalizer (Pmap : Set Q))) q :=
          hkt_factorization_lt_ambient_normalizer_of_lt_sylow (S := S) hPmap_lt_S
        have hnormPmap_le_normV :
            Subgroup.normalizer (Pmap : Set Q) ≤ Subgroup.normalizer (V : Set Q) := by
          have :
              (huppertRankThompsonSubgroup (G := Pmap) (⊤ : Subgroup Pmap)).Characteristic :=
            hkt_huppertRankThompsonSubgroup_top_characteristic (G := Pmap)
          rw [hV_eq_JPmap]
          have hmap :
              (huppertRankThompsonSubgroup (G := Pmap)
                  (⊤ : Subgroup Pmap)).map Pmap.subtype =
                huppertRankThompsonSubgroup (G := Q) Pmap :=
            hkt_huppertRankThompsonSubgroup_top_map_subtype (G := Q) Pmap
          rw [← hmap]
          exact
            hkt_normalizer_le_normalizer_map_subtype_of_characteristic
              (H := Pmap)
              (K := huppertRankThompsonSubgroup (G := Pmap) (⊤ : Subgroup Pmap))
        have hfact_normPmap_le_normV :
            Nat.factorization (Nat.card (Subgroup.normalizer (Pmap : Set Q))) q ≤
              Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q :=
          Nat.factorization_le_factorization_of_dvd_right
            (Subgroup.card_dvd_of_le hnormPmap_le_normV) Nat.card_pos.ne' Nat.card_pos.ne'
        have hlt_self : Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q <
            Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q := by
          calc
            Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q = Nat.factorization (Nat.card Pmap) q :=
              hfactorPmap.symm
            _ < Nat.factorization (Nat.card (Subgroup.normalizer (Pmap : Set Q))) q :=
              hfact_lt
            _ ≤ Nat.factorization (Nat.card (Subgroup.normalizer (V : Set Q))) q :=
              hfact_normPmap_le_normV
            _ ≤ Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q :=
              hfactor_V_le_U
            _ = Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q := by rfl
        exact (lt_irrefl _) hlt_self
      have hPmap_eq_S : Pmap = (S : Subgroup Q) := by
        by_contra hne
        exact hPmap_not_lt_S
          (lt_of_le_of_ne (by simpa [Pmap] using hPmap_le_S) hne)
      have hV_eq_JS :
          V = huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) := by
        calc
          V = huppertRankThompsonSubgroup (G := Q) Pmap := hV_eq_JPmap
          _ = huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) := by
            rw [hPmap_eq_S]
      have hcompV : HasNormalPComplement q (↥(Subgroup.normalizer (V : Set Q))) := by
        rw [hV_eq_JS]
        exact hnormalizer_rank_dvd
      exact hV_no_comp hcompV
    have hNtop : Subgroup.normalizer (U : Set Q) = ⊤ := by
      classical
      by_contra hN_ne_top
      have hN_ne_bot : Subgroup.normalizer (U : Set Q) ≠ ⊥ := by
        intro hNbot
        have hU_le_bot : U ≤ (⊥ : Subgroup Q) := by
          intro x hxU
          have hxN : x ∈ Subgroup.normalizer (U : Set Q) :=
            (Subgroup.le_normalizer (H := U)) hxU
          simpa [hNbot] using hxN
        exact hU_ne_bot (le_bot_iff.mp hU_le_bot)
      have hq_dvd_N : q ∣ Nat.card (Subgroup.normalizer (U : Set Q)) := by
        have hU_nontrivial : Nontrivial U :=
          (Subgroup.nontrivial_iff_ne_bot (H := U)).2 hU_ne_bot
        rcases hU_p.nontrivial_iff_card.mp hU_nontrivial with ⟨n, hn_pos, hcardU⟩
        have hqU : q ∣ Nat.card U := by
          rw [hcardU]
          exact dvd_pow_self q hn_pos.ne'
        exact hqU.trans (Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := U)))
      have hcomp_normU : HasNormalPComplement q (Subgroup.normalizer (U : Set Q)) :=
        hproper_rec (Subgroup.normalizer (U : Set Q)) P hN_ne_bot hN_ne_top
          hq_dvd_N hcenter_local hJrank_local
      exact hU_no_complement hcomp_normU
    have hU_eq_core : U = pCore q Q := by
      classical
      have hUnormal : U.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
      have hU_le_pCore : U ≤ pCore q Q := le_sSup ⟨hUnormal, hU_p⟩
      by_contra hUne
      have hU_lt_pCore : U < pCore q Q := lt_of_le_of_ne hU_le_pCore hUne
      have hpCore_ne_bot : pCore q Q ≠ ⊥ := by
        intro hbot
        exact hU_ne_bot (le_bot_iff.mp (by simpa [hbot] using hU_le_pCore))
      have hpCore_no_comp :
          ¬ HasNormalPComplement q (↥(Subgroup.normalizer ((pCore q Q : Subgroup Q) : Set Q))) := by
        intro hcomp_norm
        have hnorm_top : Subgroup.normalizer ((pCore q Q : Subgroup Q) : Set Q) = ⊤ :=
          Subgroup.normalizer_eq_top (pCore q Q)
        have hcomp_Q : HasNormalPComplement q Q :=
          hkt_hasNormalPComplement_of_subgroup_eq_top
            (Subgroup.normalizer ((pCore q Q : Subgroup Q) : Set Q)) hnorm_top hcomp_norm
        exact hnot_Qp
          (hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
            (Q := Q) (p := q) hcore_bot hcomp_Q)
      have hfactor :
          Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q ≤
            Nat.factorization
              (Nat.card (Subgroup.normalizer ((pCore q Q : Subgroup Q) : Set Q))) q := by
        have hpcore_norm_top :
            Subgroup.normalizer ((pCore q Q : Subgroup Q) : Set Q) = ⊤ :=
          Subgroup.normalizer_eq_top (pCore q Q)
        rw [hNtop, hpcore_norm_top]
      have hcard : Nat.card U < Nat.card (pCore q Q : Subgroup Q) :=
        natCard_lt_of_subgroup_lt (G := Q) hU_lt_pCore
      have hscore :=
        hUmax (pCore q Q : Subgroup Q) hpCore_ne_bot (pCore_isPGroup (p := q) (G := Q)) hpCore_no_comp
      have hfactor_le :
          Nat.factorization
              (Nat.card (Subgroup.normalizer ((pCore q Q : Subgroup Q) : Set Q))) q ≤
            Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q :=
        huppertIV62_normalizer_factorization_le_of_score_le
          (U := U) (V := (pCore q Q : Subgroup Q)) hscore
      have hfactor_eq :
          Nat.factorization
              (Nat.card (Subgroup.normalizer ((pCore q Q : Subgroup Q) : Set Q))) q =
            Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q :=
        le_antisymm hfactor_le hfactor
      have hcard_le : Nat.card (pCore q Q : Subgroup Q) ≤ Nat.card U :=
        huppertIV62_card_le_of_factorization_eq_score_le
          (U := U) (V := (pCore q Q : Subgroup Q)) hfactor_eq hscore
      exact (not_lt_of_ge hcard_le) hcard
    exact hkt_false_of_selected_pSubgroup_eq_pCore_reduced_nonburnside
      (Q := Q) (q := q) hcore_bot hnot_Qp hq2 S hq_dvd
      hnot_burnside hcentralizer_dvd hnormalizer_rank_dvd hU_ne_bot hU_p hU_no_complement hUmax P hUS hUN_le_P
      hcardUP hPmap_le_S hproper_rec hsmaller_rec hcenter_local hJrank_local hNtop hU_eq_core
  · have hcompQ : HasNormalPComplement q Q :=
      huppertIV58_hasNormalPComplement_of_no_noncomplement_pSubgroups (Q := Q) (q := q) hbad
    exact hnot_Qp
      (hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
        (Q := Q) (p := q) hcore_bot hcompQ)

private theorem hkt_thompson_iv62_pPrimeCore_eq_bot_isPGroup_of_local_p_nilpotence_proper_nonburnside
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcore_bot : pPrimeCore q Q = ⊥)
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    (_hcentralizer_ne_top :
      Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤)
    (_hnormalizer_ne_top :
      Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤) :
    IsPGroup q Q := by
  classical
  refine hkt_thompson_iv62_pPrimeCore_eq_bot_isPGroup_of_local_p_nilpotence_proper_nonburnside_step
    (Q := Q) (q := q) hcore_bot hq2 S hq_dvd hnot_burnside
    hcentralizer_dvd hnormalizer_rank_dvd _hcentralizer_ne_top _hnormalizer_ne_top ?_
  intro R hRGroup hRFinite T hR_lt_Q hqR hcenterR hJR
  let : Group R := hRGroup
  let : Finite R := hRFinite
  by_cases hburnsideR :
      (T : Subgroup R) ≤ centerIn (G := R) (Subgroup.normalizer (T : Subgroup R))
  · exact hkt_hasNormalPComplement_of_sylow_le_center_normalizer T hburnsideR
  by_cases hcenterR_top :
      Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R) = ⊤
  · exact hkt_hasNormalPComplement_of_subgroup_eq_top
      (Subgroup.centralizer (centerIn (G := R) (T : Subgroup R) : Set R))
      hcenterR_top hcenterR
  by_cases hJR_top :
      Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R) = ⊤
  · exact hkt_hasNormalPComplement_of_subgroup_eq_top
      (Subgroup.normalizer
        (huppertRankThompsonSubgroup (G := R) (T : Subgroup R) : Set R))
      hJR_top hJR
  let M : Subgroup R := pPrimeCore q R
  let π : R →* R ⧸ M := QuotientGroup.mk' M
  let Rbar : Type u := R ⧸ M
  let Tbar : Sylow q Rbar :=
    T.mapSurjective (f := π) (QuotientGroup.mk'_surjective M)
  have hcore_bar : pPrimeCore q Rbar = ⊥ := by
    simpa [Rbar, M] using pPrimeCore_quotient_pPrimeCore_eq_bot (G := R) (p := q)
  have hq_dvd_bar : q ∣ Nat.card Rbar := by
    simpa [Rbar, M] using
      hkt_dvd_card_quotient_pPrimeCore_of_dvd_card (Q := R) (p := q) hqR
  have hnot_burnside_bar :
      ¬ (Tbar : Subgroup Rbar) ≤
        centerIn (G := Rbar) (Subgroup.normalizer (Tbar : Subgroup Rbar)) := by
    simpa [Rbar, M, π, Tbar] using
      hkt_quotient_pPrimeCore_nonburnside_of_nonburnside
        (Q := R) (q := q) T hburnsideR
  have hcentralizer_bar :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Rbar) (Tbar : Subgroup Rbar) : Set Rbar))) := by
    simpa [Rbar, M, π, Tbar] using
      hkt_centralizer_center_sylow_hasNormalPComplement_quotient_pPrimeCore
        (Q := R) (p := q) T hcenterR
  have hnormalizer_rank_bar :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Rbar) (Tbar : Subgroup Rbar) : Set Rbar))) := by
    simpa [Rbar, M, π, Tbar] using
      hkt_normalizer_huppertRankThompsonSubgroup_hasNormalPComplement_quotient_pPrimeCore
        (Q := R) (p := q) T hJR
  by_cases hcenter_bar_top :
      Subgroup.centralizer
          (centerIn (G := Rbar) (Tbar : Subgroup Rbar) : Set Rbar) = ⊤
  · have hcomp_bar : HasNormalPComplement q Rbar :=
      hkt_hasNormalPComplement_of_subgroup_eq_top
        (Subgroup.centralizer
          (centerIn (G := Rbar) (Tbar : Subgroup Rbar) : Set Rbar))
        hcenter_bar_top hcentralizer_bar
    have hRbar_p : IsPGroup q Rbar :=
      hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
        (Q := Rbar) (p := q) hcore_bar hcomp_bar
    exact hkt_hasNormalPComplement_of_quotient_pPrimeCore_isPGroup
      (Q := R) (p := q) (by simpa [Rbar, M] using hRbar_p)
  by_cases hnormalizer_bar_top :
      Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Rbar) (Tbar : Subgroup Rbar) : Set Rbar) = ⊤
  · have hcomp_bar : HasNormalPComplement q Rbar :=
      hkt_hasNormalPComplement_of_subgroup_eq_top
        (Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Rbar) (Tbar : Subgroup Rbar) : Set Rbar))
        hnormalizer_bar_top hnormalizer_rank_bar
    have hRbar_p : IsPGroup q Rbar :=
      hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
        (Q := Rbar) (p := q) hcore_bar hcomp_bar
    exact hkt_hasNormalPComplement_of_quotient_pPrimeCore_isPGroup
      (Q := R) (p := q) (by simpa [Rbar, M] using hRbar_p)
  have hbar_le_R : Nat.card Rbar ≤ Nat.card R := by
    have hdiv : Nat.card Rbar ∣ Nat.card R := by
      simpa [Rbar, M] using Subgroup.card_quotient_dvd_card (s := M)
    exact Nat.le_of_dvd Nat.card_pos hdiv
  have hbar_lt_Q : Nat.card Rbar < Nat.card Q := lt_of_le_of_lt hbar_le_R hR_lt_Q
  have hRbar_p : IsPGroup q Rbar :=
    hkt_thompson_iv62_pPrimeCore_eq_bot_isPGroup_of_local_p_nilpotence_proper_nonburnside
      (Q := Rbar) (q := q) hcore_bar hq2 Tbar hq_dvd_bar
      hnot_burnside_bar hcentralizer_bar hnormalizer_rank_bar
      hcenter_bar_top hnormalizer_bar_top
  exact hkt_hasNormalPComplement_of_quotient_pPrimeCore_isPGroup
    (Q := R) (p := q) (by simpa [Rbar, M] using hRbar_p)

termination_by Nat.card Q
decreasing_by
  all_goals assumption
/--
Proper non-Burnside core of Thompson IV.6.2, reduced to the canonical
`q'`-core quotient. The local hypotheses must force `Q / O_{q'}(Q)` to be a
`q`-group; once this is known, the normal complement is just `O_{q'}(Q)`.
-/
private theorem hkt_thompson_iv62_quotient_pPrimeCore_isPGroup_of_local_p_nilpotence_proper_nonburnside
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    (_hcentralizer_ne_top :
      Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤)
    (_hnormalizer_ne_top :
      Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤) :
    IsPGroup q (Q ⧸ pPrimeCore q Q) := by
  classical
  let M : Subgroup Q := pPrimeCore q Q
  let π : Q →* Q ⧸ M := QuotientGroup.mk' M
  let Qbar : Type u := Q ⧸ M
  let Sbar : Sylow q Qbar :=
    S.mapSurjective (f := π) (QuotientGroup.mk'_surjective M)
  have hcore_bar : pPrimeCore q Qbar = ⊥ := by
    simpa [Qbar, M] using pPrimeCore_quotient_pPrimeCore_eq_bot (G := Q) (p := q)
  have hq_dvd_bar : q ∣ Nat.card Qbar := by
    simpa [Qbar, M] using
      hkt_dvd_card_quotient_pPrimeCore_of_dvd_card (Q := Q) (p := q) hq_dvd
  have hnot_burnside_bar :
      ¬ (Sbar : Subgroup Qbar) ≤
        centerIn (G := Qbar) (Subgroup.normalizer (Sbar : Subgroup Qbar)) := by
    simpa [Qbar, M, π, Sbar] using
      hkt_quotient_pPrimeCore_nonburnside_of_nonburnside
        (Q := Q) (q := q) S hnot_burnside
  have hcentralizer_bar :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Qbar) (Sbar : Subgroup Qbar) : Set Qbar))) := by
    simpa [Qbar, M, π, Sbar] using
      hkt_centralizer_center_sylow_hasNormalPComplement_quotient_pPrimeCore
        (Q := Q) (p := q) S hcentralizer_dvd
  have hnormalizer_rank_bar :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Qbar) (Sbar : Subgroup Qbar) : Set Qbar))) := by
    simpa [Qbar, M, π, Sbar] using
      hkt_normalizer_huppertRankThompsonSubgroup_hasNormalPComplement_quotient_pPrimeCore
        (Q := Q) (p := q) S hnormalizer_rank_dvd
  by_cases hcentralizer_bar_top :
      Subgroup.centralizer
          (centerIn (G := Qbar) (Sbar : Subgroup Qbar) : Set Qbar) = ⊤
  · have hcomp_bar : HasNormalPComplement q Qbar :=
      hkt_hasNormalPComplement_of_subgroup_eq_top
        (Subgroup.centralizer
          (centerIn (G := Qbar) (Sbar : Subgroup Qbar) : Set Qbar))
        hcentralizer_bar_top hcentralizer_bar
    exact hkt_isPGroup_of_quotient_pPrimeCore_isPGroup_of_pPrimeCore_eq_bot
      (Q := Qbar) (p := q) hcore_bar
      (isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
        (p := q) (H := Qbar) hcomp_bar)
  by_cases hnormalizer_bar_top :
      Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Qbar) (Sbar : Subgroup Qbar) : Set Qbar) = ⊤
  · have hcomp_bar : HasNormalPComplement q Qbar :=
      hkt_hasNormalPComplement_of_subgroup_eq_top
        (Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Qbar) (Sbar : Subgroup Qbar) : Set Qbar))
        hnormalizer_bar_top hnormalizer_rank_bar
    exact hkt_isPGroup_of_quotient_pPrimeCore_isPGroup_of_pPrimeCore_eq_bot
      (Q := Qbar) (p := q) hcore_bar
      (isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
        (p := q) (H := Qbar) hcomp_bar)
  exact
    hkt_thompson_iv62_pPrimeCore_eq_bot_isPGroup_of_local_p_nilpotence_proper_nonburnside
      (Q := Qbar) (q := q) hcore_bar hq2 Sbar hq_dvd_bar
      hnot_burnside_bar hcentralizer_bar hnormalizer_rank_bar
      hcentralizer_bar_top hnormalizer_bar_top

/--
The proper non-Burnside core of Thompson IV.6.2: both local subgroups are
proper, and the proof must use the local normal `q`-complements to build a
normal `q`-complement in `Q`.
-/
private theorem hkt_thompson_iv62_normal_p_complement_of_local_p_nilpotence_proper_nonburnside
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    (hcentralizer_ne_top :
      Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤)
    (hnormalizer_ne_top :
      Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤) :
    HasNormalPComplement q Q := by
  exact hkt_hasNormalPComplement_of_quotient_pPrimeCore_isPGroup
    (hkt_thompson_iv62_quotient_pPrimeCore_isPGroup_of_local_p_nilpotence_proper_nonburnside
      hq2 S hq_dvd hnot_burnside hcentralizer_dvd hnormalizer_rank_dvd
      hcentralizer_ne_top hnormalizer_ne_top)

/--
The genuinely hard Thompson IV.6.2 branch after the Burnside normal-complement
case has been removed.  In this branch the Sylow subgroup is not already
central in its normalizer, so the proof must use the two local `q`-nilpotence
hypotheses for `C_Q(Z(S))` and `N_Q(J(S))`.
-/
private theorem hkt_thompson_iv62_normal_p_complement_of_local_p_nilpotence_nonburnside
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q)))) :
    HasNormalPComplement q Q := by
  by_cases hcentralizer_top :
      Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q) = ⊤
  · exact hkt_hasNormalPComplement_of_subgroup_eq_top
      (Subgroup.centralizer
        (centerIn (G := Q) (S : Subgroup Q) : Set Q))
      hcentralizer_top hcentralizer_dvd
  by_cases hnormalizer_top :
      Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q) = ⊤
  · exact hkt_hasNormalPComplement_of_subgroup_eq_top
      (Subgroup.normalizer
        (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))
      hnormalizer_top hnormalizer_rank_dvd
  exact
    hkt_thompson_iv62_normal_p_complement_of_local_p_nilpotence_proper_nonburnside
      hq2 S hq_dvd hnot_burnside hcentralizer_dvd hnormalizer_rank_dvd
      hcentralizer_top hnormalizer_top

/--
Thompson IV.6.2 in the exact local form used by Huppert V.8.13: for odd `q`,
local `q`-nilpotence of `C_Q(Z(S))` and `N_Q(J(S))` forces `Q` itself to have a
normal `q`-complement.
-/
private theorem hkt_thompson_iv62_normal_p_complement_of_local_p_nilpotence_of_dvd_card
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (hq_dvd : q ∣ Nat.card Q)
    (hcentralizer_dvd :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank_dvd :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q)))) :
    HasNormalPComplement q Q := by
  by_cases hS :
      (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q))
  · exact hkt_hasNormalPComplement_of_sylow_le_center_normalizer S hS
  · exact
      hkt_thompson_iv62_normal_p_complement_of_local_p_nilpotence_nonburnside
        hq2 S hq_dvd hS hcentralizer_dvd hnormalizer_rank_dvd

/-- Thompson IV.6.2 in the exact local form used by Huppert V.8.13: for odd `q`,
local `q`-nilpotence of `C_Q(Z(S))` and `N_Q(J(S))` forces `Q` itself to have a
normal `q`-complement. -/
private theorem hkt_thompson_iv62_normal_p_complement_of_local_p_nilpotence
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (hcentralizer :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q)))) :
    HasNormalPComplement q Q := by
  by_cases hq_dvd : q ∣ Nat.card Q
  · exact hkt_thompson_iv62_normal_p_complement_of_local_p_nilpotence_of_dvd_card
      hq2 S hq_dvd hcentralizer hnormalizer_rank
  · exact hkt_hasNormalPComplement_of_not_dvd_card (Q := Q) (p := q) hq_dvd

/-- Huppert IV.6.2 (Thompson).  If `q > 2`, `S` is a Sylow `q`-subgroup of
`Q`, and both `C_Q(Z(S))` and `N_Q(J(S))` have normal `q`-complements, then
`Q` has a normal `q`-complement. -/
public theorem huppert_IV_6_2_thompson_normal_p_complement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (hcentralizer :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))))
    (_hnormalizer :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (thompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))))
    (hnormalizer_rank :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q)))) :
    HasNormalPComplement q Q := by
  have step_main : HasNormalPComplement q Q :=
    hkt_thompson_iv62_normal_p_complement_of_local_p_nilpotence
      hq2 S hcentralizer hnormalizer_rank
  exact step_main

end External
end CFSG.BenderSuzuki
