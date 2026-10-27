module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_13
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.LinearAlgebra.Projectivization.Action

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section3

-- universe w

open PFchapter1section1 PFAppendixIII MatrixGroups
open scoped LinearAlgebra.Projectivization

/-!
# Peterfalvi, Part II, Chapter I, Section 3, Lemma 1
-/

public theorem twoPrimeResidual_normal
    {G : Type*} [Group G] [Finite G] :
    (twoPrimeResidual G).Normal := by
  apply Subgroup.Normal.of_conjugate_fixed
  intro g
  rw [twoPrimeResidual, Subgroup.pointwise_smul_def]
  change Subgroup.map (MulAut.conj g).toMonoidHom
      (⨆ S : Sylow 2 G, (S : Subgroup G)) = ⨆ S : Sylow 2 G, (S : Subgroup G)
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le ?_
    intro P
    change ((g • P : Sylow 2 G) : Subgroup G) ≤ _
    exact le_iSup (fun Q : Sylow 2 G => (Q : Subgroup G)) (g • P)
  · refine iSup_le ?_
    intro P
    have hle := le_iSup
      (fun Q : Sylow 2 G =>
        (Q : Subgroup G).map (MulAut.conj g).toMonoidHom) (g⁻¹ • P)
    have hmap :
        ((g⁻¹ • P : Sylow 2 G) : Subgroup G).map
            (MulAut.conj g).toMonoidHom = P := by
      rw [Sylow.coe_subgroup_smul]
      change
        ((P : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom).map
            (MulAut.conj g).toMonoidHom = P
      rw [Subgroup.map_map]
      have hcomp :
          (MulAut.conj g).toMonoidHom.comp
              (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
        ext x
        change (MulAut.conj g) ((MulAut.conj g⁻¹) x) = x
        simp only [MulAut.conj_apply]
        group
      rw [hcomp, P.map_id]
    rw [hmap] at hle
    exact hle

public theorem odd_card_quotient_twoPrimeResidual
    {G : Type*} [Group G] [Finite G] :
    letI : (twoPrimeResidual G).Normal := twoPrimeResidual_normal
    Odd (Nat.card (G ⧸ twoPrimeResidual G)) := by
  let L := twoPrimeResidual G
  letI : L.Normal := twoPrimeResidual_normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := Sylow.nonempty.some
  let pi : G →* G ⧸ L := QuotientGroup.mk' L
  let Pbar : Sylow 2 (G ⧸ L) :=
    P.mapSurjective (f := pi) (QuotientGroup.mk'_surjective L)
  have hP_le_L : (P : Subgroup G) ≤ L :=
    le_iSup (fun Q : Sylow 2 G => (Q : Subgroup G)) P
  have hPbar_bot : (Pbar : Subgroup (G ⧸ L)) = ⊥ := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_eq_bot_iff]
    simpa [pi, QuotientGroup.ker_mk'] using hP_le_L
  rw [← Nat.not_even_iff_odd]
  intro heven
  exact Pbar.ne_bot_of_dvd_card heven.two_dvd hPbar_bot


/--
Peterfalvi obligation from (A1): in the rank-one setup, `Q` acts regularly on
`Ω - {H}`, hence `|Q| = |Ω| - 1`.
-/
private theorem hypothesisA1_H_card_eq_Q_mul_D_card
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    Nat.card H = Nat.card Q * Nat.card D := by
  let QH : Subgroup H := Q.subgroupOf H
  let DH : Subgroup H := D.subgroupOf H
  haveI : QH.Normal := by
    simpa [QH] using hA1.Q_normal_in_H
  have hdisjH : Disjoint QH DH := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxD
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hA1.Q_disjoint_D hxQ hxD
  have hsupH : QH ⊔ DH = ⊤ := by
    have hsup_eq : QH ⊔ DH = (Q ⊔ D).subgroupOf H := by
      symm
      simpa [QH, DH] using
        (Subgroup.subgroupOf_sup (A := Q) (A' := D) (B := H)
          hA1.Q_le_H hA1.D_le_H)
    rw [hsup_eq, hA1.Q_sup_D]
    ext x
    simp
  have hcomp : QH.IsComplement' DH := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjH ?_
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ QH ⊔ DH := by simp [hsupH]
    rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := QH) (t := DH)).1 hx with
      ⟨q, hqQ, d, hdD, hmul⟩
    exact ⟨q, hqQ, d, hdD, hmul⟩
  have hQcard : Nat.card QH = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := Q) (K := H)
      hA1.Q_le_H).toEquiv
  have hDcard : Nat.card DH = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := D) (K := H)
      hA1.D_le_H).toEquiv
  have hmul := hcomp.card_mul
  rw [hQcard, hDcard] at hmul
  exact hmul.symm

private theorem hypothesisA1_H_card_eq_complement_mul_D_card
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    Nat.card H = (Nat.card Ω - 1) * Nat.card D := by
  classical
  obtain ⟨alpha, hH⟩ := hA1.point_stabilizer
  subst H
  let beta : Ω := t⁻¹ • alpha
  have hbeta_ne : beta ≠ alpha := by
    intro h
    apply hA1.t_not_mem_H
    change t • alpha = alpha
    have htinv : t⁻¹ = t :=
      hA1.involution_t.inv_eq_self
    simpa [beta, htinv] using h
  let betaComp : SubMulAction.ofStabilizer G alpha :=
    ⟨beta, (SubMulAction.mem_ofStabilizer_iff (G := G) alpha).2 hbeta_ne⟩
  have hD :
      D = MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta := by
    simpa [beta, rightConjugate_stabilizer] using hA1.D_eq
  have hDsub_eq :
      D.subgroupOf (MulAction.stabilizer G alpha) =
        MulAction.stabilizer (MulAction.stabilizer G alpha) betaComp := by
    ext x
    constructor
    · intro hx
      apply Subtype.ext
      change (x : G) • beta = beta
      have hxD : (x : G) ∈ MulAction.stabilizer G beta := by
        have hxD' : (x : G) ∈ D := Subgroup.mem_subgroupOf.mp hx
        exact (hD ▸ hxD').2
      exact hxD
    · intro hx
      have hxBeta : (x : G) • beta = beta := by
        have hx' := congrArg Subtype.val hx
        change (x : G) • beta = beta at hx'
        exact hx'
      have hxInf :
          (x : G) ∈ MulAction.stabilizer G alpha ⊓
            MulAction.stabilizer G beta := by
        exact ⟨x.property, hxBeta⟩
      apply Subgroup.mem_subgroupOf.mpr
      exact hD.symm ▸ hxInf
  haveI : MulAction.IsMultiplyPretransitive G Ω 2 := hA1.two_transitive
  haveI : MulAction.IsPretransitive G Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hstab_multi :
      MulAction.IsMultiplyPretransitive
        (MulAction.stabilizer G alpha) (SubMulAction.ofStabilizer G alpha) 1 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := G) (a := alpha)).mp hA1.two_transitive
  haveI :
      MulAction.IsPretransitive
        (MulAction.stabilizer G alpha) (SubMulAction.ofStabilizer G alpha) :=
    (MulAction.is_one_pretransitive_iff
      (G := MulAction.stabilizer G alpha)
      (α := SubMulAction.ofStabilizer G alpha)).mp hstab_multi
  have hindex :
      (MulAction.stabilizer
          (MulAction.stabilizer G alpha) betaComp).index =
        Nat.card Ω - 1 := by
    calc
      (MulAction.stabilizer
          (MulAction.stabilizer G alpha) betaComp).index =
          Nat.card (SubMulAction.ofStabilizer G alpha) := by
        exact MulAction.index_stabilizer_of_transitive
          (MulAction.stabilizer G alpha) betaComp
      _ = Nat.card Ω - 1 := by
        exact SubMulAction.nat_card_ofStabilizer_eq G alpha
  have hDcard :
      Nat.card (MulAction.stabilizer
        (MulAction.stabilizer G alpha) betaComp) = Nat.card D := by
    rw [← hDsub_eq]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := D)
        (K := MulAction.stabilizer G alpha) hA1.D_le_H).toEquiv
  have hmul :=
    (MulAction.stabilizer
      (MulAction.stabilizer G alpha) betaComp).card_mul_index
  rw [hindex, hDcard] at hmul
  simpa [Nat.mul_comm] using hmul.symm

public theorem hypothesisA1_q_card_eq_complement_card
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    Nat.card Q = Nat.card Ω - 1 := by
  have hQD := hypothesisA1_H_card_eq_Q_mul_D_card H D Q t hA1
  have hHD := hypothesisA1_H_card_eq_complement_mul_D_card H D Q t hA1
  have hcancel : Nat.card Q * Nat.card D = (Nat.card Ω - 1) * Nat.card D := by
    rw [← hQD, hHD]
  have hD_ne : Nat.card D ≠ 0 := by
    exact (Nat.card_ne_zero).2 ⟨inferInstance, inferInstance⟩
  exact mul_right_cancel₀ hD_ne hcancel

private theorem section3_q_card_eq_complement_card
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    Nat.card Q = Nat.card Ω - 1 := by
  exact hypothesisA1_q_card_eq_complement_card H D Q t hsec.section2.hA.A1

private theorem sylow_le_of_odd_quotient
    {G : Type*} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    (hodd : Odd (Nat.card (G ⧸ L))) (P : Sylow 2 G) :
    (P : Subgroup G) ≤ L := by
  let π : G →* G ⧸ L := QuotientGroup.mk' L
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmapP :
      IsPGroup 2 ((P : Subgroup G).map π) :=
    P.isPGroup'.map π
  rcases IsPGroup.iff_card.mp hmapP with ⟨n, hn⟩
  have hcard_dvd :
      Nat.card ((P : Subgroup G).map π) ∣ Nat.card (G ⧸ L) :=
    Subgroup.card_subgroup_dvd_card ((P : Subgroup G).map π)
  cases n with
  | zero =>
      have hmap_bot : (P : Subgroup G).map π = ⊥ := by
        exact Subgroup.eq_bot_of_card_eq
          (H := (P : Subgroup G).map π) (by simpa using hn)
      have hle_ker : (P : Subgroup G) ≤ π.ker :=
        (Subgroup.map_eq_bot_iff (H := (P : Subgroup G)) (f := π)).mp hmap_bot
      simpa [π, QuotientGroup.ker_mk'] using hle_ker
  | succ n =>
      have htwo_dvd_map :
          2 ∣ Nat.card ((P : Subgroup G).map π) := by
        rw [hn]
        exact dvd_pow_self 2 (Nat.succ_ne_zero n)
      exact False.elim (hodd.not_two_dvd_nat (htwo_dvd_map.trans hcard_dvd))

public theorem twoPrimeResidual_le_of_odd_quotient
    {G : Type*} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    (hodd : Odd (Nat.card (G ⧸ L))) :
    twoPrimeResidual G ≤ L := by
  rw [twoPrimeResidual]
  exact iSup_le fun P => sylow_le_of_odd_quotient hodd P

private theorem section3_q_le_model_subgroup_of_odd_quotient
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hQ_two : ∃ n : ℕ, Nat.card Q = 2 ^ n)
    {L : Subgroup G} [L.Normal] (hodd : Odd (Nat.card (G ⧸ L))) :
    Q ≤ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases PFchapter1section1.proposition_1_c H D Q t hsec.section2.hA.A1 with
    ⟨P, hP_le_Q⟩
  rcases hQ_two with ⟨n, hQ_card⟩
  have hQ_pgroup : IsPGroup 2 Q :=
    IsPGroup.of_card hQ_card
  have hQ_eq_P : Q = (P : Subgroup G) :=
    P.is_maximal' hQ_pgroup hP_le_Q
  rw [hQ_eq_P]
  exact sylow_le_of_odd_quotient hodd P


public theorem simple_subgroup_le_twoPrimeResidual_of_pgroup
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hQp : IsPGroup 2 Q) (hQ_ne : Q ≠ ⊥)
    {L : Subgroup G} (hQ_le_L : Q ≤ L) (hLsimple : IsSimpleGroup L) :
    L ≤ twoPrimeResidual G := by
  let QL : Subgroup L := Q.subgroupOf L
  letI : IsSimpleGroup L := hLsimple
  have hQL_ne : QL ≠ ⊥ := by
    intro hbot
    apply hQ_ne
    apply le_antisymm
    · intro x hx
      have hxQL : (⟨x, hQ_le_L hx⟩ : L) ∈ QL := hx
      rw [hbot] at hxQL
      simpa using hxQL
    · exact bot_le
  have hnormal_top :
      Subgroup.normalClosure (QL : Set L) = ⊤ := by
    rcases (Subgroup.normalClosure_normal :
        (Subgroup.normalClosure (QL : Set L)).Normal).eq_bot_or_eq_top with
      hbot | htop
    · exfalso
      apply hQL_ne
      apply le_antisymm
      · intro x hx
        have hxclosure := Subgroup.le_normalClosure hx
        rw [hbot] at hxclosure
        simpa using hxclosure
      · exact bot_le
    · exact htop
  have hclosure_le :
      Subgroup.normalClosure (QL : Set L) ≤
        (twoPrimeResidual G).comap L.subtype := by
    intro x hx
    change (x : G) ∈ twoPrimeResidual G
    change x ∈ Subgroup.closure (Group.conjugatesOfSet (QL : Set L)) at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        rcases Group.mem_conjugatesOfSet_iff.mp hx with
          ⟨a, ha, hconj⟩
        obtain ⟨l, rfl⟩ := isConj_iff.mp hconj
        let Qc : Subgroup G :=
          Q.map (MulAut.conj (l : G)).toMonoidHom
        have hQc_p : IsPGroup 2 Qc :=
          hQp.map (MulAut.conj (l : G)).toMonoidHom
        obtain ⟨P, hQc_le_P⟩ := hQc_p.exists_le_sylow
        rw [twoPrimeResidual]
        apply (le_iSup (fun S : Sylow 2 G => (S : Subgroup G)) P)
        apply hQc_le_P
        change (l : G) * (a : G) * (l : G)⁻¹ ∈ Qc
        refine ⟨(a : G), ?_, rfl⟩
        exact ha
    | one => exact (twoPrimeResidual G).one_mem
    | mul x y hx hy ihx ihy =>
        exact (twoPrimeResidual G).mul_mem ihx ihy
    | inv x hx ihx =>
        exact (twoPrimeResidual G).inv_mem ihx
  intro x hx
  let xL : L := ⟨x, hx⟩
  have hxclosure : xL ∈ Subgroup.normalClosure (QL : Set L) := by
    rw [hnormal_top]
    exact Subgroup.mem_top xL
  have hxcomap := hclosure_le hxclosure
  exact hxcomap

/--
Peterfalvi obligation from the external named models used in Theorem A: the simple
rank-one model subgroup is generated by its Sylow `2`-subgroups.  Since `Q`
is a Sylow `2`-subgroup contained in `L`, this identifies the model subgroup
with the subgroup generated by the ambient Sylow `2`-subgroups.
-/
-- The simplicity input for this model is Huppert II.6.13.
public theorem psl2Realization_subgroup_le_twoPrimeResidual
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (Q : Subgroup G) (hQ_two : ∃ n : ℕ, Nat.card Q = 2 ^ n)
    (hQ_ne : Q ≠ ⊥)
    {L : Subgroup G} (_hL : L.Normal) {q : ℕ}
    (_hodd : Odd (Nat.card (G ⧸ L))) (hq : ∃ n : ℕ, q = 2 ^ n) (hq_gt : 2 < q)
    (m : ℕ) (hm_ne : m ≠ 0) (hq_model : q = 2 ^ m)
    (e : L ≃* PSL2BinaryMatrixGroup m)
    (hQ_le_L : Q ≤ L) :
    L ≤ twoPrimeResidual G := by
  have hQp : IsPGroup 2 Q := by
    rcases hQ_two with ⟨n, hn⟩
    exact IsPGroup.of_card hn
  have hfield_card : Nat.card (BinaryGaloisField m) = 2 ^ m := by
    simpa [BinaryGaloisField] using GaloisField.card 2 m hm_ne
  have hsimple_model : IsSimpleGroup (PSL2BinaryMatrixGroup m) := by
    apply External.huppert_II_6_13 2 (by omega)
    · right
      rw [hfield_card, ← hq_model]
      omega
    · right
      rw [hfield_card]
      intro h
      have heven : Even (2 ^ m) :=
        Nat.even_pow.mpr ⟨by norm_num, hm_ne⟩
      rw [h] at heven
      exact (by decide : ¬ Even 3) heven
  have hsimple_L : IsSimpleGroup L :=
    e.isSimpleGroup_congr.mpr hsimple_model
  exact simple_subgroup_le_twoPrimeResidual_of_pgroup
    Q hQp hQ_ne hQ_le_L hsimple_L

-- The simplicity input for this model is Huppert-Blackburn XI.3.6.
public theorem suzukiRealization_subgroup_le_twoPrimeResidual
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (Q : Subgroup G) (hQ_two : ∃ n : ℕ, Nat.card Q = 2 ^ n)
    (hQ_ne : Q ≠ ⊥)
    {L : Subgroup G} (_hL : L.Normal) {q : ℕ}
    (_hodd : Odd (Nat.card (G ⧸ L))) (_hq : ∃ n : ℕ, q = 2 ^ n) (_hq_gt : 2 < q)
    (m : ℕ) (hm_ne : m ≠ 0) (_hq_model : q = 2 ^ (2 * m + 1))
    (e : L ≃* SuzukiMatrixGroup m)
    (hQ_le_L : Q ≤ L) :
    L ≤ twoPrimeResidual G := by
  have hQp : IsPGroup 2 Q := by
    rcases hQ_two with ⟨n, hn⟩
    exact IsPGroup.of_card hn
  have hsimple_model : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (External.huppert_blackburn_XI_3_6 m (Nat.pos_of_ne_zero hm_ne)).1
  have hsimple_L : IsSimpleGroup L :=
    e.isSimpleGroup_congr.mpr hsimple_model
  exact simple_subgroup_le_twoPrimeResidual_of_pgroup
    Q hQp hQ_ne hQ_le_L hsimple_L

-- The simplicity input for this model is Huppert II.10.13.
public theorem psuRealization_subgroup_le_twoPrimeResidual
    {G Ω E : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [Field E] [Finite E]
    (Q : Subgroup G) (hQ_two : ∃ n : ℕ, Nat.card Q = 2 ^ n)
    (hQ_ne : Q ≠ ⊥)
    {L : Subgroup G} (_hL : L.Normal) {q : ℕ}
    (_hodd : Odd (Nat.card (G ⧸ L))) (_hq : ∃ n : ℕ, q = 2 ^ n) (hq_gt : 2 < q)
    (J : HermitianForm 3 E)
    (hEcard : Nat.card E = q ^ 2)
    (hfixedCard : Nat.card {z : E // J.conj z = z} = q)
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hQ_le_L : Q ≤ L) :
    L ≤ twoPrimeResidual G := by
  have hQp : IsPGroup 2 Q := by
    rcases hQ_two with ⟨n, hn⟩
    exact IsPGroup.of_card hn
  have hsimple_model :
      IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    External.huppert_II_10_13 J q hq_gt hEcard hfixedCard
  have hsimple_L : IsSimpleGroup L :=
    e.isSimpleGroup_congr.mpr hsimple_model
  exact simple_subgroup_le_twoPrimeResidual_of_pgroup
    Q hQp hQ_ne hQ_le_L hsimple_L


/-- A model subgroup supplied by Theorem A for an arbitrary `HypothesisA`
context is the subgroup generated by the Sylow `2`-subgroups. This is the
context-free core of Lemma 1 used when the induction hypothesis is applied to
a normal subgroup in Proposition 2. -/
public theorem hypothesisA_model_subgroup_eq_twoPrimeResidual
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA : HypothesisA G Ω H D Q t)
    (L : Subgroup G) (hL : L.Normal) (q : ℕ)
    (hodd : Odd (Nat.card (G ⧸ L)))
    (hq : ∃ n : ℕ, q = 2 ^ n) (hq_gt : 2 < q)
    (hmodel :
      psl2ActionModel G Ω L q ∨
        suzukiActionModel G Ω L q ∨
          unitaryActionModel G Ω L q) :
    IsPGroup 2 Q ∧ twoPrimeResidual G = L := by
  have hΩ_power : ∃ n : ℕ, Nat.card Ω - 1 = 2 ^ n := by
    rcases hmodel with
        ⟨k, hk, _hqk, _eL, _rho, eΩ, _hnatural, _hequiv⟩ |
        ⟨k, hk, _hqk, _eL, _rho, eΩ, _hnatural, _hequiv⟩ |
        ⟨E, hEfield, hEfinite, J, hJstandard, hEcard, hfixedCard,
          _eL, _rho, eΩ, _hnatural, _hequiv⟩
    · have hfield : Nat.card (BinaryGaloisField k) = 2 ^ k := by
        simpa [BinaryGaloisField] using (GaloisField.card 2 k hk)
      have hpoints :
          Nat.card (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)) =
            2 ^ k + 1 := by
        calc
          _ = Nat.card (BinaryGaloisField k) + 1 :=
            Projectivization.card_of_finrank_two
              (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k) (by simp)
          _ = 2 ^ k + 1 := by rw [hfield]
      exact ⟨k, by rw [Nat.card_congr eΩ, hpoints]; omega⟩
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      let pi : BinaryGaloisField (2 * k + 1) ≃+*
          BinaryGaloisField (2 * k + 1) :=
        iterateFrobeniusEquiv (BinaryGaloisField (2 * k + 1)) 2 (k + 1)
      have hpi : ∀ x : BinaryGaloisField (2 * k + 1),
          pi x = x ^ (2 ^ (k + 1)) := by
        intro x
        exact iterateFrobeniusEquiv_def
          (BinaryGaloisField (2 * k + 1)) 2 (k + 1) x
      rcases External.huppert_blackburn_XI_3_3 k hkpos pi hpi with
        ⟨_, _, _, _, _, hpoints, _, _⟩
      have hpoints' :
          let K := BinaryGaloisField (2 * k + 1)
          let pinf : ℙ K (Fin 4 → K) :=
            Projectivization.mk K ![1, 0, 0, 0] (by simp)
          let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
            Projectivization.mk K
              ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
                y, x, 1] (by simp)
          let O : Set (ℙ K (Fin 4 → K)) :=
            {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
          Nat.card {z // z ∈ O} = (2 ^ (2 * k + 1)) ^ 2 + 1 := by
        simpa only [hpi] using hpoints
      refine ⟨(2 * k + 1) * 2, ?_⟩
      rw [Nat.card_congr eΩ, hpoints']
      simp [pow_mul]
    · letI : Field E := hEfield
      letI : Finite E := hEfinite
      have hpoints :=
        (External.huppert_II_10_12 J q hEcard hfixedCard hJstandard).1
      rcases hq with ⟨n, hn⟩
      refine ⟨n * 3, ?_⟩
      rw [Nat.card_congr eΩ, hpoints, hn]
      simp [pow_mul]
  have hQ_card : Nat.card Q = Nat.card Ω - 1 :=
    hypothesisA1_q_card_eq_complement_card H D Q t hA.A1
  have hQ_two : ∃ n : ℕ, Nat.card Q = 2 ^ n := by
    rcases hΩ_power with ⟨n, hn⟩
    exact ⟨n, hQ_card.trans hn⟩
  have hQ_ne : Q ≠ ⊥ := by
    intro hQ
    have hodd_one : Odd (Nat.card Q) := by simp [hQ]
    exact hodd_one.not_two_dvd_nat hA.A1.Q_even.two_dvd
  letI : L.Normal := hL
  have hres_le_L : twoPrimeResidual G ≤ L :=
    twoPrimeResidual_le_of_odd_quotient hodd
  have hQ_le_L : Q ≤ L := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases PFchapter1section1.proposition_1_c H D Q t hA.A1 with
      ⟨P, hP_le_Q⟩
    rcases hQ_two with ⟨n, hQ_card'⟩
    have hQ_pgroup : IsPGroup 2 Q := IsPGroup.of_card hQ_card'
    have hQ_eq_P : Q = (P : Subgroup G) :=
      P.is_maximal' hQ_pgroup hP_le_Q
    rw [hQ_eq_P]
    exact sylow_le_of_odd_quotient hodd P
  have hL_le_res : L ≤ twoPrimeResidual G := by
    rcases hmodel with
        ⟨m, hm_ne, hq_model, e, _rho, _eΩ, _hnatural, _hequiv⟩ |
        ⟨m, hm_ne, hq_model, e, _rho, _eΩ, _hnatural, _hequiv⟩ |
        ⟨E, hEfield, hEfinite, J, _hJstandard, hEcard, hfixedCard,
          e, _rho, _eΩ, _hnatural, _hequiv⟩
    · exact psl2Realization_subgroup_le_twoPrimeResidual
        (G := G) (Ω := Ω) Q hQ_two hQ_ne hL hodd hq hq_gt
          m hm_ne hq_model e hQ_le_L
    · exact suzukiRealization_subgroup_le_twoPrimeResidual
        (G := G) (Ω := Ω) Q hQ_two hQ_ne hL hodd hq hq_gt
          m hm_ne hq_model e hQ_le_L
    · letI : Field E := hEfield
      letI : Finite E := hEfinite
      exact psuRealization_subgroup_le_twoPrimeResidual
        (G := G) (Ω := Ω) Q hQ_two hQ_ne hL hodd hq hq_gt
          J hEcard hfixedCard e hQ_le_L
  rcases hQ_two with ⟨n, hn⟩
  exact ⟨IsPGroup.of_card hn, le_antisymm hres_le_L hL_le_res⟩

public theorem lemma_1
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (L : Subgroup G) (hL : L.Normal) (q : ℕ)
    (hodd : Odd (Nat.card (G ⧸ L)))
    (hq : ∃ n : ℕ, q = 2 ^ n) (hq_gt : 2 < q)
    (hmodel :
      ((∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ k)
          (eL : L ≃* PSL2BinaryMatrixGroup k)
          (rho : PSL2BinaryMatrixGroup k →*
            Equiv.Perm (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)))
          (eΩ : Ω ≃ ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)),
        (∀ A : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField k),
          ∀ z : ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k),
            rho (QuotientGroup.mk'
              (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
                (BinaryGaloisField k))) A) z =
              Matrix.SpecialLinearGroup.toLin' A • z) ∧
        ∀ l : L, ∀ ω : Ω,
          eΩ ((l : G) • ω) = rho (eL l) (eΩ ω)) ∨
      (∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ (2 * k + 1)),
        let K := BinaryGaloisField (2 * k + 1)
        let pinf : ℙ K (Fin 4 → K) :=
          Projectivization.mk K ![1, 0, 0, 0] (by simp)
        let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
          Projectivization.mk K
            ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
              y, x, 1] (by simp)
        let O : Set (ℙ K (Fin 4 → K)) :=
          {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
        ∃ (eL : L ≃* SuzukiMatrixGroup k)
            (rho : SuzukiMatrixGroup k →* Equiv.Perm {z // z ∈ O})
            (eΩ : Ω ≃ {z // z ∈ O}),
          (∀ g : SuzukiMatrixGroup k, ∀ z : {z // z ∈ O},
            ((rho g z : {z // z ∈ O}) : ℙ K (Fin 4 → K)) =
              (Matrix.GeneralLinearGroup.toLin
                (g : GL (Fin 4) K)).toLinearEquiv •
                  (z : ℙ K (Fin 4 → K))) ∧
          ∀ l : L, ∀ ω : Ω,
            eΩ ((l : G) • ω) = rho (eL l) (eΩ ω)) ∨
      (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
        J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
        Nat.card E = q ^ 2 ∧
        Nat.card {z : E // J.conj z = z} = q ∧
        let P := ℙ E (Fin 3 → E)
        let A : Set P :=
          {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
            x = Projectivization.mk E v hv ∧
              dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
        let X := {x : P // x ∈ A}
        ∃ (eL : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
            (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm X)
            (eΩ : Ω ≃ X),
          (∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : X,
            ∀ M : J.specialSubgroup,
              Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) E) =
                  (g : Matrix.ProjGenLinGroup (Fin 3) E) →
                ((rho g z : X) : P) =
                  (Matrix.GeneralLinearGroup.toLin
                    (M : GL (Fin 3) E)).toLinearEquiv • (z : P)) ∧
          ∀ l : L, ∀ ω : Ω,
            eΩ ((l : G) • ω) = rho (eL l) (eΩ ω)))) :
    IsPGroup 2 Q ∧ twoPrimeResidual G = L := by
  have hΩ_power : ∃ n : ℕ, Nat.card Ω - 1 = 2 ^ n := by
    rcases hmodel with
        ⟨k, hk, _hqk, _eL, _rho, eΩ, _hnatural, _hequiv⟩ |
        ⟨k, hk, _hqk, _eL, _rho, eΩ, _hnatural, _hequiv⟩ |
        ⟨E, hEfield, hEfinite, J, hJstandard, hEcard, hfixedCard,
          _eL, _rho, eΩ, _hnatural, _hequiv⟩
    · have hfield : Nat.card (BinaryGaloisField k) = 2 ^ k := by
        simpa [BinaryGaloisField] using (GaloisField.card 2 k hk)
      have hpoints :
          Nat.card (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)) =
            2 ^ k + 1 := by
        calc
          _ = Nat.card (BinaryGaloisField k) + 1 :=
            Projectivization.card_of_finrank_two
              (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k) (by simp)
          _ = 2 ^ k + 1 := by rw [hfield]
      refine ⟨k, ?_⟩
      rw [Nat.card_congr eΩ, hpoints]
      omega
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      let pi : BinaryGaloisField (2 * k + 1) ≃+*
          BinaryGaloisField (2 * k + 1) :=
        iterateFrobeniusEquiv (BinaryGaloisField (2 * k + 1)) 2 (k + 1)
      have hpi : ∀ x : BinaryGaloisField (2 * k + 1),
          pi x = x ^ (2 ^ (k + 1)) := by
        intro x
        exact iterateFrobeniusEquiv_def
          (BinaryGaloisField (2 * k + 1)) 2 (k + 1) x
      rcases External.huppert_blackburn_XI_3_3 k hkpos pi hpi with
        ⟨_, _, _, _, _, hpoints, _, _⟩
      have hpoints' :
          let K := BinaryGaloisField (2 * k + 1)
          let pinf : ℙ K (Fin 4 → K) :=
            Projectivization.mk K ![1, 0, 0, 0] (by simp)
          let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
            Projectivization.mk K
              ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
                y, x, 1] (by simp)
          let O : Set (ℙ K (Fin 4 → K)) :=
            {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
          Nat.card {z // z ∈ O} = (2 ^ (2 * k + 1)) ^ 2 + 1 := by
        simpa only [hpi] using hpoints
      refine ⟨(2 * k + 1) * 2, ?_⟩
      rw [Nat.card_congr eΩ, hpoints']
      simp [pow_mul]
    · letI : Field E := hEfield
      letI : Finite E := hEfinite
      have hpoints :=
        (External.huppert_II_10_12 J q hEcard hfixedCard hJstandard).1
      rcases hq with ⟨n, hn⟩
      refine ⟨n * 3, ?_⟩
      rw [Nat.card_congr eΩ, hpoints, hn]
      simp [pow_mul]
  have hQ_card : Nat.card Q = Nat.card Ω - 1 :=
    section3_q_card_eq_complement_card H D Q K V W Q0 S Q1 t s hsec
  have hQ_two : ∃ n : ℕ, Nat.card Q = 2 ^ n := by
    rcases hΩ_power with ⟨n, hn⟩
    exact ⟨n, by rw [hQ_card, hn]⟩
  have hQ_ne : Q ≠ ⊥ := by
    intro hQ
    have hsQ0 : s ∈ Q0 :=
      (hsec.section2.Q0_def s).mpr
        (Or.inr ⟨hsec.s_mem_H, hsec.s_involution⟩)
    have hsQ : s ∈ Q := hsec.section2.Q0_le_Q hsQ0
    rw [hQ] at hsQ
    exact hsec.s_involution.ne_one (by simpa using hsQ)
  letI : L.Normal := hL
  have hres_le_L : twoPrimeResidual G ≤ L := by
    exact twoPrimeResidual_le_of_odd_quotient (L := L) hodd
  have hQ_le_L : Q ≤ L :=
    section3_q_le_model_subgroup_of_odd_quotient
      H D Q K V W Q0 S Q1 t s hsec hQ_two hodd
  have hL_le_res : L ≤ twoPrimeResidual G := by
    rcases hmodel with
        ⟨m, hm_ne, hq_model, e, _rho, _eΩ, _hnatural, _hequiv⟩ |
        ⟨m, hm_ne, hq_model, e, _rho, _eΩ, _hnatural, _hequiv⟩ |
        ⟨E, hEfield, hEfinite, J, _hJstandard, hEcard, hfixedCard,
          e, _rho, _eΩ, _hnatural, _hequiv⟩
    · exact psl2Realization_subgroup_le_twoPrimeResidual
        (G := G) (Ω := Ω) Q hQ_two hQ_ne hL hodd hq hq_gt
          m hm_ne hq_model e hQ_le_L
    · exact suzukiRealization_subgroup_le_twoPrimeResidual
        (G := G) (Ω := Ω) Q hQ_two hQ_ne hL hodd hq hq_gt
          m hm_ne hq_model e hQ_le_L
    · letI : Field E := hEfield
      letI : Finite E := hEfinite
      exact psuRealization_subgroup_le_twoPrimeResidual
        (G := G) (Ω := Ω) Q hQ_two hQ_ne hL hodd hq hq_gt
          J hEcard hfixedCard e hQ_le_L
  rcases hQ_two with ⟨n, hn⟩
  exact ⟨IsPGroup.of_card hn, le_antisymm hres_le_L hL_le_res⟩
end PFchapter1section3
end CFSG.BenderSuzuki
