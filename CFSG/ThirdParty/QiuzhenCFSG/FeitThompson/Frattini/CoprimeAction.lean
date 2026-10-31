module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Solvable
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative

public theorem CFSG.actsTrivially_quotient_commutatorAction
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G] :
    let H : Subgroup G := commutatorAction (A := A) (G := G)
    letI : H.Normal := commutatorAction_normal (G := G) (A := A)
    letI : MulDistribMulAction A (G ⧸ H) :=
      quotientMulDistribMulAction (A := A) (G := G) H
        (commutatorAction_isInvariant (G := G) (A := A))
    ActsTrivially (A := A) (G := G ⧸ H) := by
  let H : Subgroup G := commutatorAction (A := A) (G := G)
  let hHinv : IsInvariant A G H := commutatorAction_isInvariant (G := G) (A := A)
  letI : H.Normal := commutatorAction_normal (G := G) (A := A)
  letI : MulDistribMulAction A (G ⧸ H) :=
    quotientMulDistribMulAction (A := A) (G := G) H hHinv
  change ∀ a : A, ∀ q : G ⧸ H, a • q = q
  intro a q
  refine QuotientGroup.induction_on q ?_
  intro g
  change (QuotientGroup.mk' H) (a • g) = (QuotientGroup.mk' H) g
  have hgen : g⁻¹ * (a • g) ∈ H := by
    change g⁻¹ * (a • g) ∈ commutatorAction (A := A) (G := G)
    rw [commutatorAction_eq_closure (G := G) (A := A)]
    exact Subgroup.subset_closure ⟨a, g, rfl⟩
  have hconj : (a • g) * g⁻¹ ∈ H := by
    have : g * (g⁻¹ * (a • g)) * g⁻¹ ∈ H := (inferInstance : H.Normal).conj_mem _ hgen g
    simpa [mul_assoc] using this
  exact (QuotientGroup.eq_iff_div_mem).2 (by simpa [div_eq_mul_inv] using hconj)

public theorem CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_fixedPointQuotientImage
    {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G]
    (hfixed_quotient_image :
      ∀ (H : Subgroup G) [H.Normal] (hHinv : IsInvariant A G H),
        letI : MulDistribMulAction A (G ⧸ H) :=
          quotientMulDistribMulAction (A := A) (G := G) H hHinv
        fixedPointSubgroup A (G ⧸ H) = (fixedPointSubgroup A G).map (QuotientGroup.mk' H)) :
    fixedPointSubgroup A G ⊔ commutatorAction (A := A) (G := G) = ⊤ := by
  let H : Subgroup G := commutatorAction (A := A) (G := G)
  have hHnorm : H.Normal := commutatorAction_normal (G := G) (A := A)
  have hHinv : IsInvariant A G H := commutatorAction_isInvariant (G := G) (A := A)
  letI : H.Normal := hHnorm
  letI : MulDistribMulAction A (G ⧸ H) :=
    quotientMulDistribMulAction (A := A) (G := G) H hHinv
  have htriv_quot : ActsTrivially (A := A) (G := G ⧸ H) :=
    actsTrivially_quotient_commutatorAction (G := G) (A := A)
  have hfixed_quot : fixedPointSubgroup A (G ⧸ H) = ⊤ := by
    ext q
    constructor
    · intro _hq
      simp
    · intro _hq
      have hqfix : ∀ a : A, a • q = q := by
        intro a
        exact htriv_quot a q
      simpa [fixedPointSubgroup] using hqfix
  have hquot_fixed_eq_map :
      fixedPointSubgroup A (G ⧸ H) = (fixedPointSubgroup A G).map (QuotientGroup.mk' H) :=
    hfixed_quotient_image H hHinv
  have hmap_top : (fixedPointSubgroup A G).map (QuotientGroup.mk' H) = ⊤ := by
    simpa [hfixed_quot] using hquot_fixed_eq_map.symm
  have hsup :
      fixedPointSubgroup A G ⊔ H = ⊤ := by
    calc
      fixedPointSubgroup A G ⊔ H
          = Subgroup.comap (QuotientGroup.mk' H)
              ((fixedPointSubgroup A G).map (QuotientGroup.mk' H)) := by
                simp [sup_comm]
      _ = Subgroup.comap (QuotientGroup.mk' H) (⊤ : Subgroup (G ⧸ H)) := by simp [hmap_top]
      _ = ⊤ := by simp
  simpa [H, sup_comm] using hsup

public theorem CFSG.commutatorAction₂_eq_commutatorAction_of_coprime
    {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G]
    (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    commutatorAction₂ (A := A) (G := G) = commutatorAction (A := A) (G := G) := by
  let H : Subgroup G := commutatorAction (A := A) (G := G)
  letI : IsInvariant A G H := commutatorAction_isInvariant (G := G) (A := A)
  let Csub : Subgroup H := commutatorAction (A := A) (G := H)
  letI : Csub.Normal := commutatorAction_normal (G := H) (A := A)
  letI : MulAction.QuotientAction A Csub :=
    quotientAction_of_isInvariant (A := A) (G := H) Csub
      (commutatorAction_isInvariant (G := H) (A := A))
  letI : MulDistribMulAction A (H ⧸ Csub) :=
    quotientMulDistribMulAction (A := A) (G := H) Csub
      (commutatorAction_isInvariant (G := H) (A := A))
  let qH : H →* H ⧸ Csub := QuotientGroup.mk' Csub
  have htriv_quot : ActsTrivially (A := A) (G := H ⧸ Csub) :=
    actsTrivially_quotient_commutatorAction (G := H) (A := A)
  have hq_smul (a : A) (h : H) : qH (a • h) = qH h := by
    have hfix : a • (qH h) = qH h := htriv_quot a (qH h)
    exact (MulAction.Quotient.smul_mk (H := Csub) a h).symm.trans hfix
  have hcard_quot_dvd : Nat.card (H ⧸ Csub) ∣ Nat.card G := by
    exact (Subgroup.card_quotient_dvd_card (s := Csub)).trans (Subgroup.card_subgroup_dvd_card H)
  have hcop_quot : Nat.Coprime (Nat.card A) (Nat.card (H ⧸ Csub)) :=
    Nat.Coprime.of_dvd_right hcard_quot_dvd hcoprime
  have hgen_mem_H (a : A) (g : G) : g⁻¹ * (a • g) ∈ H := by
    change g⁻¹ * (a • g) ∈ commutatorAction (A := A) (G := G)
    rw [commutatorAction_eq_closure (G := G) (A := A)]
    exact Subgroup.subset_closure ⟨a, g, rfl⟩
  have hgen_mem_Csub (a : A) (g : G) : ⟨g⁻¹ * (a • g), hgen_mem_H a g⟩ ∈ Csub := by
    let cg : A →* H ⧸ Csub := by
      refine
        { toFun := fun b => qH ⟨g⁻¹ * (b • g), hgen_mem_H b g⟩
          map_one' := by
            have h1 : (⟨g⁻¹ * ((1 : A) • g), hgen_mem_H 1 g⟩ : H) = 1 := by
              ext
              simp
            rw [h1]
            simp
          map_mul' := ?_ }
      intro b c
      let hg_b : H := ⟨g⁻¹ * (b • g), hgen_mem_H b g⟩
      let hg_c : H := ⟨g⁻¹ * (c • g), hgen_mem_H c g⟩
      have hsm :
          (b * c) • g = b • g * ((b • hg_c : H) : G) := by
        calc
          (b * c) • g = b • (c • g) := by simp [smul_smul]
          _ = b • (g * (g⁻¹ * (c • g))) := by simp
          _ = b • g * b • (g⁻¹ * (c • g)) := by simp [smul_mul']
          _ = b • g * ((b • hg_c : H) : G) := by rfl
      have hmulH :
          (⟨g⁻¹ * ((b * c) • g), hgen_mem_H (b * c) g⟩ : H) = hg_b * (b • hg_c) := by
        ext
        change g⁻¹ * ((b * c) • g) = (g⁻¹ * (b • g)) * ((b • hg_c : H) : G)
        simp [hsm, mul_assoc]
      calc
        qH ⟨g⁻¹ * ((b * c) • g), hgen_mem_H (b * c) g⟩
            = qH (hg_b * (b • hg_c)) := by simp [hmulH]
        _ = qH hg_b * qH (b • hg_c) := by simp [qH]
        _ = qH hg_b * qH hg_c := by
              simp [hq_smul]
        _ = qH ⟨g⁻¹ * (b • g), hgen_mem_H b g⟩ *
              qH ⟨g⁻¹ * (c • g), hgen_mem_H c g⟩ := by rfl
    have hdivA : orderOf (cg a) ∣ Nat.card A := by
      exact (orderOf_map_dvd (ψ := cg) a).trans (orderOf_dvd_natCard a)
    have hdivQ : orderOf (cg a) ∣ Nat.card (H ⧸ Csub) := orderOf_dvd_natCard (cg a)
    have horder : orderOf (cg a) = 1 := Nat.eq_one_of_dvd_coprimes hcop_quot hdivA hdivQ
    have hcg_one : cg a = 1 := (orderOf_eq_one_iff).1 horder
    have : qH ⟨g⁻¹ * (a • g), hgen_mem_H a g⟩ = 1 := by simpa [cg] using hcg_one
    exact (QuotientGroup.eq_one_iff (N := Csub) (x := (⟨g⁻¹ * (a • g), hgen_mem_H a g⟩ : H))).1
      (by simpa [qH] using this)
  have hcomm_le : commutatorAction (A := A) (G := G) ≤ commutatorAction₂ (A := A) (G := G) := by
    have hmap :
        Csub.map H.subtype = commutatorAction₂ (A := A) (G := G) :=
      commutatorAction_map_subtype_eq_commutatorAction₂ (G := G) (A := A)
    rw [commutatorAction_eq_closure (G := G) (A := A)]
    refine (Subgroup.closure_le (K := commutatorAction₂ (A := A) (G := G))).2 ?_
    intro x hx
    rcases hx with ⟨a, g, rfl⟩
    rw [← hmap]
    exact Subgroup.mem_map_of_mem H.subtype (hgen_mem_Csub a g)
  exact le_antisymm commutatorAction₂_le_commutatorAction hcomm_le

public theorem CFSG.isCompl_fixedPointSubgroup_commutatorAction_of_sup_eq_top_of_coprime_of_isMulCommutative
    {G A : Type*} [Group G] [Group A] [Finite A]
    [MulDistribMulAction A G]
    (hsup : fixedPointSubgroup A G ⊔ commutatorAction (A := A) (G := G) = ⊤)
    (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (hcomm : IsMulCommutative G) :
    IsCompl (fixedPointSubgroup A G) (commutatorAction (A := A) (G := G)) := by
  letI : IsMulCommutative G := hcomm
  letI : Fintype A := Fintype.ofFinite A
  let N : G →* G := by
    refine
      { toFun := fun g => ∏ a : A, a • g
        map_one' := by simp
        map_mul' := ?_ }
    intro x y
    simp only [smul_mul']
    exact Finset.prod_mul_distrib
  have hnorm_gen (a : A) (g : G) : N (g⁻¹ * (a • g)) = 1 := by
    have hprod_shift : (∏ b : A, (b * a) • g) = ∏ b : A, b • g := by
      have hbij : Function.Bijective (fun b : A => b * a) := by
        refine ⟨?_, ?_⟩
        · intro b₁ b₂ h
          exact mul_right_cancel h
        · intro b
          refine ⟨b * a⁻¹, ?_⟩
          simp [mul_assoc]
      simpa using
        (Fintype.prod_bijective
          (e := fun b : A => b * a)
          (he := hbij)
          (f := fun b : A => (b * a) • g)
          (g := fun b : A => b • g)
          (by intro b; rfl))
    calc
      N (g⁻¹ * (a • g))
          = ∏ b : A, (b • g)⁻¹ * ((b * a) • g) := by
              simp [N, smul_mul', smul_smul]
      _ = (∏ b : A, (b • g)⁻¹) * (∏ b : A, ((b * a) • g)) := by
            rw [Finset.prod_mul_distrib]
      _ = (∏ b : A, (b • g)⁻¹) * (∏ b : A, b • g) := by simp [hprod_shift]
      _ = ((∏ b : A, b • g)⁻¹) * (∏ b : A, b • g) := by simp
      _ = 1 := by simp
  have hcomm_le_ker : commutatorAction (A := A) (G := G) ≤ N.ker := by
    rw [commutatorAction_eq_closure (G := G) (A := A)]
    refine (Subgroup.closure_le (K := N.ker)).2 ?_
    intro x hx
    rcases hx with ⟨a, g, rfl⟩
    simpa [MonoidHom.mem_ker] using hnorm_gen a g
  have hinf_bot :
      fixedPointSubgroup A G ⊓ commutatorAction (A := A) (G := G) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    rcases hx with ⟨hxFix, hxComm⟩
    have hxFix' : ∀ a : A, a • x = x := by
      simpa [fixedPointSubgroup] using hxFix
    have hxNpow : N x = x ^ Nat.card A := by
      calc
        N x = ∏ a : A, x := by simp [N, hxFix']
        _ = x ^ Fintype.card A := by simp
        _ = x ^ Nat.card A := by simp [Nat.card_eq_fintype_card]
    have hxN1 : N x = 1 := by
      have hxKer : x ∈ N.ker := hcomm_le_ker hxComm
      simpa [MonoidHom.mem_ker] using hxKer
    have hxpow1 : x ^ Nat.card A = 1 := by simpa [hxNpow] using hxN1
    have hdivA : orderOf x ∣ Nat.card A := (orderOf_dvd_iff_pow_eq_one).2 hxpow1
    have hdivG : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
    have horder1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcoprime hdivA hdivG
    exact (orderOf_eq_one_iff).1 horder1
  exact
    ⟨(disjoint_iff).2 hinf_bot,
      (codisjoint_iff).2 (by simpa [sup_comm] using hsup)⟩

public theorem CFSG.actsTrivially_of_trivial_quotient_frattini_of_sup_eq_top
    {R A : Type*} [Group R] [Finite R] [Group A]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] [MulDistribMulAction A R]
    (hsup : fixedPointSubgroup A R ⊔ commutatorAction (A := A) (G := R) = ⊤)
    (hquot :
      letI : MulDistribMulAction A (R ⧸ frattini R) :=
        quotientMulDistribMulAction (A := A) (G := R) (frattini R)
          (isInvariant_of_characteristic (A := A) (G := R) (frattini R))
      ActsTrivially (A := A) (G := R ⧸ frattini R)) :
    ActsTrivially (A := A) (G := R) := by
  letI : MulDistribMulAction A (R ⧸ frattini R) :=
    quotientMulDistribMulAction (A := A) (G := R) (frattini R)
      (isInvariant_of_characteristic (A := A) (G := R) (frattini R))
  have hquot' : ActsTrivially (A := A) (G := R ⧸ frattini R) := by
    simpa using hquot
  have hcomm_le_frattini :
      commutatorAction (A := A) (G := R) ≤ frattini R := by
    rw [commutatorAction_eq_closure (G := R) (A := A)]
    refine (Subgroup.closure_le (K := frattini R)).2 ?_
    intro x hx
    rcases hx with ⟨a, g, rfl⟩
    have hq_eq : (a • (g : R) : R ⧸ frattini R) = (g : R ⧸ frattini R) :=
      hquot' a (g : R ⧸ frattini R)
    have hdiv_mem : (a • (g : R)) / g ∈ frattini R := (QuotientGroup.eq_iff_div_mem).1 hq_eq
    have hmul_mem : (a • g : R) * g⁻¹ ∈ frattini R := by
      simpa [div_eq_mul_inv] using hdiv_mem
    have hconj_mem' : g⁻¹ * ((a • g : R) * g⁻¹) * (g⁻¹)⁻¹ ∈ frattini R := by
      exact (inferInstance : (frattini R).Normal).conj_mem _ hmul_mem g⁻¹
    have hconj_mem : g⁻¹ * ((a • g : R) * g⁻¹) * g ∈ frattini R := by
      simpa using hconj_mem'
    simpa [mul_assoc] using hconj_mem
  have hsup_frattini : fixedPointSubgroup A R ⊔ frattini R = ⊤ := by
    have htop_le : (⊤ : Subgroup R) ≤ fixedPointSubgroup A R ⊔ frattini R := by
      calc
        (⊤ : Subgroup R) = fixedPointSubgroup A R ⊔ commutatorAction (A := A) (G := R) := by
          simp [hsup]
        _ ≤ fixedPointSubgroup A R ⊔ frattini R := by
          exact sup_le_sup_left hcomm_le_frattini (fixedPointSubgroup A R)
    exact top_le_iff.mp htop_le
  have hfixed_top : fixedPointSubgroup A R = ⊤ :=
    lemma_1_7_a (R := R) (p := p) (H := fixedPointSubgroup A R) hsup_frattini
  intro a g
  have hg_mem : g ∈ fixedPointSubgroup A R := by
    simp [hfixed_top]
  have hg_fixed : ∀ b : A, b • g = g := by
    simpa [fixedPointSubgroup] using hg_mem
  exact hg_fixed a
