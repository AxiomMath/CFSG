module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped IsMulCommutative commutatorElement

namespace CFSG.Section9

universe v
universe w
universe u

private theorem isElementaryAbelian_of_mulEquiv_sec9
    {p : ℕ} {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) [IsElementaryAbelian p H] :
    IsElementaryAbelian p G := by
  refine
    { toIsMulCommutative := ?_
      exponent_dvd_p := ?_ }
  · refine ⟨⟨?_⟩⟩
    intro a b
    apply e.injective
    simpa using mul_comm (e a) (e b)
  · rw [Monoid.exponent_eq_of_mulEquiv e]
    exact IsElementaryAbelian.exponent_dvd_p p H

private theorem isElementaryAbelian_quotient_of_normal_sec9
    {p : ℕ} {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsElementaryAbelian p G] :
    IsElementaryAbelian p (G ⧸ N) := by
  refine
    { toIsMulCommutative := ?_
      exponent_dvd_p := ?_ }
  · refine ⟨⟨?_⟩⟩
    intro a b
    rcases QuotientGroup.mk'_surjective N a with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective N b with ⟨y, rfl⟩
    simp [mul_comm]
  · exact (Group.exponent_quotient_dvd (H := N)).trans
      (IsElementaryAbelian.exponent_dvd_p p G)

private noncomputable def quotient_comap_equiv_quotient_quotient_sec9
    {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal]
    (Q : Subgroup (G ⧸ N)) [Q.Normal] :
    (G ⧸ Q.comap (QuotientGroup.mk' N)) ≃* ((G ⧸ N) ⧸ Q) := by
  let C : Subgroup G := Q.comap (QuotientGroup.mk' N)
  have hN_le_C : N ≤ C := QuotientGroup.le_comap_mk' N Q
  have hmap : C.map (QuotientGroup.mk' N) = Q := by
    simpa [C] using
      Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) Q
  exact
    (QuotientGroup.quotientQuotientEquivQuotient N C hN_le_C).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hmap)

private theorem nontrivial_of_not_actsTrivially_sec9
    {A X : Type u} [SMul A X]
    (h : ¬ ActsTrivially (A := A) (G := X)) :
    Nontrivial X := by
  by_contra hnt
  haveI : Subsingleton X := not_nontrivial_iff_subsingleton.mp hnt
  exact h (fun a x => Subsingleton.elim (a • x) x)

private theorem nontrivial_of_mulEquiv_sec9
    {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) [Nontrivial H] :
    Nontrivial G := by
  refine ⟨?_⟩
  rcases exists_pair_ne H with ⟨a, b, hab⟩
  exact ⟨e.symm a, e.symm b, by
    intro h
    apply hab
    simpa using congrArg e h⟩

private theorem subgroupOf_map_subtype_eq_sec9
    {G : Type u} [Group G] (M : Subgroup G) (C : Subgroup M) :
    ((C.map M.subtype).subgroupOf M) = C := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hyC, hyx⟩
    have hyxM : y = x := M.subtype_injective hyx
    simpa [hyxM] using hyC
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem subgroupOf_subgroupOf_map_subtype_eq_sec9
    {G : Type u} [Group G] {M MF : Subgroup G} (hMFleM : MF ≤ M)
    (C : Subgroup M) (hC_le_MF : C ≤ MF.subgroupOf M) :
    (C.subgroupOf (MF.subgroupOf M)).map
        (Subgroup.subgroupOfEquivOfLe (H := MF) (K := M) hMFleM).toMonoidHom =
      ((C.map M.subtype).subgroupOf MF) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hyC, rfl⟩
    have hyC_M : ((y : MF.subgroupOf M) : M) ∈ C := by
      simpa [Subgroup.mem_subgroupOf] using hyC
    change (((Subgroup.subgroupOfEquivOfLe (H := MF) (K := M) hMFleM).toMonoidHom y : MF) : G) ∈
      C.map M.subtype
    exact ⟨((y : MF.subgroupOf M) : M), hyC_M, rfl⟩
  · intro hx
    rcases hx with ⟨y, hyC, hyx⟩
    refine ⟨⟨y, hC_le_MF hyC⟩, hyC, ?_⟩
    apply Subtype.ext
    exact hyx

private theorem theorem_9_4_typeII_core_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      section16TypeII M MF →
        ∃ H0 : Subgroup G, ∃ p : Nat.Primes, hoReductionData M MF U W2 H0 p := by
  classical
  intro h92 hII
  have h92full := h92
  have hMF := h92.mf
  have htypeP := h92.typeP
  rcases hMF.1 with ⟨hMFleM, hMFnormalM, hMFnil, _hMFhall⟩
  rcases htypeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhall, _hMFder, _hcomp, _hnil, _hW1norm, _hW1cyc, _hW1card,
      hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne, _hW2cyc,
      _hcentralizer, _hhat, _hprimeCentralizer⟩
  have hMF_ne_bot : MF ≠ ⊥ := by
    intro hbot
    exact hMFnotcyc (by subst hbot; infer_instance)
  have hMFsub_ne_bot : MF.subgroupOf M ≠ ⊥ := by
    intro hbot
    apply hMF_ne_bot
    ext x
    constructor
    · intro hx
      have hxsub : (⟨x, hMFleM hx⟩ : M) ∈ MF.subgroupOf M := by
        simpa [Subgroup.mem_subgroupOf] using hx
      have hxbot : (⟨x, hMFleM hx⟩ : M) ∈ (⊥ : Subgroup M) := by
        simpa [hbot] using hxsub
      simpa using hxbot
    · intro hx
      rw [hx]
      exact MF.one_mem
  have hbot_lt_MFsub : (⊥ : Subgroup M) < MF.subgroupOf M :=
    lt_of_le_of_ne bot_le (Ne.symm hMFsub_ne_bot)
  rcases exists_maximal_normal_lt_containing_B (G := M)
      (A := MF.subgroupOf M) (B := ⊥)
      (inferInstance : (⊥ : Subgroup M).Normal) hbot_lt_MFsub with
    ⟨C, hCnormalM, _hbotC, hCltMF, hCmax⟩
  have hC_le_MFsub : C ≤ MF.subgroupOf M := le_of_lt hCltMF
  let H0 : Subgroup G := C.map M.subtype
  have hH0_le_MF : H0 ≤ MF := by
    intro x hx
    rcases hx with ⟨y, hyC, rfl⟩
    simpa [Subgroup.mem_subgroupOf] using hC_le_MFsub hyC
  have hH0_normal_M : (H0.subgroupOf M).Normal := by
    have hH0sub_eq : H0.subgroupOf M = C := by
      simpa [H0] using subgroupOf_map_subtype_eq_sec9 (G := G) M C
    simpa [hH0sub_eq] using hCnormalM
  have hH0_normal_MF : (H0.subgroupOf MF).Normal := by
    let eMF : MF.subgroupOf M ≃* MF :=
      Subgroup.subgroupOfEquivOfLe (H := MF) (K := M) hMFleM
    have hCsub_normal : (C.subgroupOf (MF.subgroupOf M)).Normal :=
      Subgroup.Normal.subgroupOf (G := M) (hH := hCnormalM) (MF.subgroupOf M)
    have hmap_eq :
        (C.subgroupOf (MF.subgroupOf M)).map eMF.toMonoidHom =
          H0.subgroupOf MF := by
      simpa [H0, eMF] using
        subgroupOf_subgroupOf_map_subtype_eq_sec9 (G := G) hMFleM C hC_le_MFsub
    have hmap_normal :
        ((C.subgroupOf (MF.subgroupOf M)).map eMF.toMonoidHom).Normal :=
      hCsub_normal.map eMF.toMonoidHom eMF.surjective
    exact hmap_eq ▸ hmap_normal
  have hH0_lt_MF : H0 < MF := by
    have hmap_lt : C.map M.subtype < (MF.subgroupOf M).map M.subtype := by
      exact (Subgroup.map_subtype_lt_map_subtype (G' := M)
        (H := C) (K := MF.subgroupOf M)).2 hCltMF
    simpa [H0, Subgroup.map_subgroupOf_eq_of_le hMFleM] using hmap_lt
  have hchiefM : IsChiefFactor C (MF.subgroupOf M) := by
    refine
      { normal_K := hCnormalM
        normal_H := hMFnormalM
        lt := hCltMF
        is_maximal := ?_ }
    intro N hNnormal hCN hNleMF
    by_cases hNC : N = C
    · exact Or.inl hNC
    · have hCNlt : C < N := lt_of_le_of_ne hCN (Ne.symm hNC)
      exact Or.inr (hCmax N hNnormal bot_le hCNlt hNleMF)
  let cf : ChiefFactor M := { V := C, U := MF.subgroupOf M, isChief := hchiefM }
  let π : M →* M ⧸ C := QuotientGroup.mk' C
  let Uq : Subgroup (M ⧸ C) := (MF.subgroupOf M).map π
  haveI : Uq.Normal := by
    simpa [Uq, π, cf] using
      hchiefM.normal_H.map π (QuotientGroup.mk'_surjective C)
  haveI : IsMinimalNormal Uq := by
    simpa [Uq, π, cf] using chiefFactor_quotient_isMinimalNormal (G := M) cf
  have hsolvMFsub : Group.IsSolvable (MF.subgroupOf M) := by
    have hsolvMF : Group.IsSolvable MF := by
      letI : Group.IsNilpotent MF := hMFnil
      exact IsNilpotent.to_isSolvable
    let eMF : MF.subgroupOf M ≃* MF :=
      Subgroup.subgroupOfEquivOfLe (H := MF) (K := M) hMFleM
    letI : Group.IsSolvable MF := hsolvMF
    exact Group.isSolvable_of_surjective
      (f := eMF.symm.toMonoidHom) eMF.symm.surjective
  haveI : Group.IsSolvable Uq := by
    letI : Group.IsSolvable (MF.subgroupOf M) := hsolvMFsub
    simpa [Uq, π] using
      Group.isSolvable_of_surjective
        (f := π.subgroupMap (MF.subgroupOf M))
        (MonoidHom.subgroupMap_surjective π (MF.subgroupOf M))
  rcases minimalNormal_solvable_exists_isElementaryAbelian (G := M ⧸ C) Uq with
    ⟨p, hpprime, hUqElem⟩
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hquotMFsubElem : IsElementaryAbelian p
      (MF.subgroupOf M ⧸ C.subgroupOf (MF.subgroupOf M)) := by
    haveI : IsElementaryAbelian p Uq := hUqElem
    exact isElementaryAbelian_of_mulEquiv_sec9
      (quotientSubgroupRangeEquiv (MF.subgroupOf M) C)
  have hquotMFElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := by
    let eMF : MF.subgroupOf M ≃* MF :=
      Subgroup.subgroupOfEquivOfLe (H := MF) (K := M) hMFleM
    have hmap_eq :
        (C.subgroupOf (MF.subgroupOf M)).map eMF.toMonoidHom =
          H0.subgroupOf MF := by
      simpa [H0, eMF] using
        subgroupOf_subgroupOf_map_subtype_eq_sec9 (G := G) hMFleM C hC_le_MFsub
    let eQ : (MF.subgroupOf M ⧸ C.subgroupOf (MF.subgroupOf M)) ≃*
        (MF ⧸ H0.subgroupOf MF) :=
      QuotientGroup.congr (C.subgroupOf (MF.subgroupOf M))
        (H0.subgroupOf MF) eMF hmap_eq
    haveI : IsElementaryAbelian p
        (MF.subgroupOf M ⧸ C.subgroupOf (MF.subgroupOf M)) := hquotMFsubElem
    exact isElementaryAbelian_of_mulEquiv_sec9 eQ.symm
  refine ⟨H0, ⟨p, hpprime⟩, ?_⟩
  refine ⟨hH0_le_MF, hMFleM, hH0_normal_M, hH0_normal_MF, hH0_lt_MF, ?_, ?_⟩
  · exact ⟨hH0_normal_MF, by simpa using hquotMFElem⟩
  · intro hIIIIV
    exact False.elim
      ((not_typeIII_or_typeIV_of_hypothesis_9_2_typeII_sec9
        M MF U W1 W2 q h92full hII) hIIIIV)

private theorem theorem_9_4_typeIIIIV_pf93_facts_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (section16TypeIII M MF ∨ section16TypeIV M MF) →
        Nat.Prime (Nat.card W2) ∧
          subgroupCentralizerIn MF (U ⊔ W1) = ⊥ ∧
            ∃ p : ℕ,
              Nat.card W2 = p ∧
                Nat.card MF = p ^ q * Nat.card (subgroupCentralizerIn MF U) := by
  intro h92 hIIIIV
  rcases (theorem_9_3 M MF U W1 W2 q h92).2 hIIIIV with
    ⟨p, hpprime, hW2card, hcent, hcardMF⟩
  refine ⟨?_, hcent, p, hW2card, hcardMF⟩
  simpa [hW2card] using hpprime


private theorem not_actsTrivially_frattini_quotient_of_not_actsTrivially_sec9
    {R A : Type u} [Group R] [Finite R] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] [MulDistribMulAction A R]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hnot : ¬ ActsTrivially (A := A) (G := R)) :
    letI : MulDistribMulAction A (R ⧸ frattini R) :=
      quotientMulDistribMulAction (A := A) (G := R) (frattini R)
        (isInvariant_of_characteristic (A := A) (G := R) (frattini R))
    ¬ ActsTrivially (A := A) (G := R ⧸ frattini R) := by
  intro hquot
  exact hnot (theorem_1_8 (R := R) (A := A) (p := p) hcop hquot)

private theorem pCore_isInvariant_of_normalizes_sec9
    {G : Type u} [Group G] [Finite G]
    {A MF : Subgroup G} {p : ℕ} [Fact p.Prime]
    [Subgroup.Normalizes A MF] :
    IsInvariant A MF (pCore p MF) := by
  haveI : (pCore p MF).Characteristic := pCore_characteristic (G := MF) (p := p)
  exact isInvariant_of_characteristic (A := A) (G := MF) (pCore p MF)

private theorem theorem_9_4_typeIIIIV_prime_coprime_UW1_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      Nat.Coprime (Nat.card W2) (Nat.card (U ⊔ W1 : Subgroup G)) := by
  intro h92
  have hcop_MF_UW1 :
      Nat.Coprime (Nat.card MF) (Nat.card (U ⊔ W1 : Subgroup G)) :=
    nat_card_MF_coprime_U_sup_W1_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92
  have hW2_le_MF : W2 ≤ MF := by
    rcases h92.typeP with ⟨_hMFtype, hcommon⟩
    rcases hcommon with
      ⟨_hhall, _hMFder, _hcomp, _hnil, _hW1norm, _hW1cyc, _hW1card,
        _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, hW2le,
        _hW2ne, _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer⟩
    exact hW2le
  have hW2_dvd_MF : Nat.card W2 ∣ Nat.card MF := by
    have hsub :
        Nat.card (W2.subgroupOf MF) ∣ Nat.card MF :=
      Subgroup.card_subgroup_dvd_card (W2.subgroupOf MF)
    simpa [natCard_subgroupOf_eq W2 MF hW2_le_MF] using hsub
  exact Nat.Coprime.of_dvd_left hW2_dvd_MF hcop_MF_UW1

private theorem theorem_9_4_typeIIIIV_pCore_coprime_U_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      Nat.Coprime (Nat.card U) (Nat.card (pCore (Nat.card W2) MF)) := by
  intro h92
  have hcop_MF_UW1 :
      Nat.Coprime (Nat.card MF) (Nat.card (U ⊔ W1 : Subgroup G)) :=
    nat_card_MF_coprime_U_sup_W1_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92
  have hpCore_dvd_MF :
      Nat.card (pCore (Nat.card W2) MF) ∣ Nat.card MF :=
    Subgroup.card_subgroup_dvd_card (pCore (Nat.card W2) MF)
  have hU_dvd_UW1 :
      Nat.card U ∣ Nat.card (U ⊔ W1 : Subgroup G) := by
    have hsub :
        Nat.card (U.subgroupOf (U ⊔ W1 : Subgroup G)) ∣
          Nat.card (U ⊔ W1 : Subgroup G) :=
      Subgroup.card_subgroup_dvd_card (U.subgroupOf (U ⊔ W1 : Subgroup G))
    simpa [natCard_subgroupOf_eq U (U ⊔ W1 : Subgroup G) le_sup_left] using hsub
  exact Nat.Coprime.of_dvd_left hU_dvd_UW1 <|
    Nat.Coprime.of_dvd_right hpCore_dvd_MF hcop_MF_UW1.symm

private theorem theorem_9_4_typeIIIIV_pCore_frattini_nontrivial_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ)
    [Fact (Nat.card W2).Prime]
    [Subgroup.Normalizes U MF] :
    hypothesis_9_2_statement M MF U W1 W2 q →
      letI : IsInvariant U MF (pCore (Nat.card W2) MF) :=
        pCore_isInvariant_of_normalizes_sec9 (A := U) (MF := MF)
          (p := Nat.card W2)
      ¬ ActsTrivially (A := U) (G := pCore (Nat.card W2) MF) →
        letI : IsInvariant U MF (pCore (Nat.card W2) MF) :=
          pCore_isInvariant_of_normalizes_sec9 (A := U) (MF := MF)
            (p := Nat.card W2)
        letI : MulDistribMulAction U
            ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
          quotientMulDistribMulAction (A := U) (G := pCore (Nat.card W2) MF)
            (frattini (pCore (Nat.card W2) MF))
            (isInvariant_of_characteristic (A := U) (G := pCore (Nat.card W2) MF)
              (frattini (pCore (Nat.card W2) MF)))
        ¬ ActsTrivially (A := U)
            (G := (pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) := by
  intro h92 hnot
  let p := Nat.card W2
  have hpcore_p : IsPGroup p (pCore p MF) := pCore_isPGroup (G := MF) (p := p)
  letI : Fact (IsPGroup p (pCore p MF)) := ⟨hpcore_p⟩
  letI : IsInvariant U MF (pCore p MF) :=
    pCore_isInvariant_of_normalizes_sec9 (A := U) (MF := MF) (p := p)
  have hcop :
      Nat.Coprime (Nat.card U) (Nat.card (pCore p MF)) := by
    simpa [p] using
      theorem_9_4_typeIIIIV_pCore_coprime_U_sec9 M MF U W1 W2 q h92
  exact not_actsTrivially_frattini_quotient_of_not_actsTrivially_sec9
    (R := pCore p MF) (A := U) (p := p) hcop hnot

private theorem exists_simple_submodule_nontrivial_of_not_actsTrivially_subgroup_sec9
    {A V : Type u} [Group A] [Finite A] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p V] [MulDistribMulAction A V]
    (H : Subgroup A)
    (hcop : Nat.Coprime p (Nat.card A))
    (hH : ¬ ActsTrivially (A := H) (G := V)) :
    let ρ : Representation (ZMod p) A (Additive V) :=
      Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := p)
    letI instAdd : AddCommGroup ρ.asModule := Representation.instAddCommGroupAsModule ρ
    letI instMod : Module (MonoidAlgebra (ZMod p) A) ρ.asModule :=
      Representation.instModuleMonoidAlgebraAsModule ρ
    ∃ m : @Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule _
        instAdd.toAddCommMonoid instMod,
      IsSimpleModule (MonoidAlgebra (ZMod p) A) m ∧
        ¬ H ≤ (Subrepresentation.ofSubmodule' m).toRepresentation.ker := by
  classical
  let ρ : Representation (ZMod p) A (Additive V) :=
    Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := p)
  let instAdd : AddCommGroup ρ.asModule := Representation.instAddCommGroupAsModule ρ
  letI : AddCommGroup ρ.asModule := instAdd
  let instMod : Module (MonoidAlgebra (ZMod p) A) ρ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  letI : Module (MonoidAlgebra (ZMod p) A) ρ.asModule := instMod
  have hHker : ¬ H ≤ ρ.ker := by
    intro hHle
    apply hH
    intro h v
    have hh : (h : A) ∈ ρ.ker := hHle h.property
    rw [Theory.Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup] at hh
    exact (mem_fixingSubgroup_iff (M := A) (s := (Set.univ : Set V))).1 hh v
      (Set.mem_univ v)
  have hchar : ringChar (ZMod p) = 0 ∨
      (Nat.Prime (ringChar (ZMod p)) ∧
        Nat.Coprime (ringChar (ZMod p)) (Nat.card A)) := by
    right
    constructor
    · simpa [ZMod.ringChar_zmod_n] using (Fact.out : Nat.Prime p)
    · simpa [ZMod.ringChar_zmod_n] using hcop
  have hcr : ρ.IsCompletelyReducible :=
    Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
      (ρ := ρ) hchar
  have hsemi :
      @IsSemisimpleModule (MonoidAlgebra (ZMod p) A) _
        ρ.asModule instAdd instMod := by
    unfold Representation.IsCompletelyReducible at hcr
    exact hcr
  exact @exists_simple_submodule_nontrivial_of_not_le_ker
    A _ (ZMod p) _ (Additive V) _ _ ρ hsemi H hHker

private theorem invariant_subgroup_of_submodule_nontrivial_sec9
    {A V : Type u} [Group A] [Group V]
    {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p V] [MulDistribMulAction A V]
    (H : Subgroup A)
    (ρ : Representation (ZMod p) A (Additive V))
    (hρ : ρ = Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := p)) :
    letI instAdd : AddCommGroup ρ.asModule := Representation.instAddCommGroupAsModule ρ
    letI instMod : Module (MonoidAlgebra (ZMod p) A) ρ.asModule :=
      Representation.instModuleMonoidAlgebraAsModule ρ
    ∀ m : @Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule _
        instAdd.toAddCommMonoid instMod,
      ¬ H ≤ (Subrepresentation.ofSubmodule' m).toRepresentation.ker →
        ∃ Q : Subgroup V,
          IsInvariant A V Q ∧
            Q = (Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))).symm
              (Subrepresentation.ofSubmodule' m).toSubmodule ∧
            ¬ ∀ h : H, ∀ q : Q, (h : A) • (q : V) = (q : V) := by
  classical
  let instAdd : AddCommGroup ρ.asModule := Representation.instAddCommGroupAsModule ρ
  letI : AddCommGroup ρ.asModule := instAdd
  let instMod : Module (MonoidAlgebra (ZMod p) A) ρ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  letI : Module (MonoidAlgebra (ZMod p) A) ρ.asModule := instMod
  intro m hm_nontriv
  let S : Subrepresentation ρ := Subrepresentation.ofSubmodule' m
  let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  let Q : Subgroup V := η.symm S.toSubmodule
  have hQinv : IsInvariant A V Q := by
    refine ⟨?_⟩
    intro a v
    constructor
    · intro hv
      have hvS : Additive.ofMul v ∈ S.toSubmodule := by
        simpa [Q, S, η] using hv
      have hmem := S.apply_mem_toSubmodule a hvS
      simpa [Q, S, η, hρ] using hmem
    · intro hv
      have hvS : Additive.ofMul (a • v) ∈ S.toSubmodule := by
        simpa [Q, S, η] using hv
      have hmem := S.apply_mem_toSubmodule a⁻¹ hvS
      simpa [Q, S, η, hρ, inv_smul_smul] using hmem
  refine ⟨Q, hQinv, rfl, ?_⟩
  intro htriv
  apply hm_nontriv
  intro a ha
  rw [MonoidHom.mem_ker]
  ext q
  have hqQ : Additive.toMul (q : Additive V) ∈ Q := by
    simp [Q, S, η]
  let qQ : Q := ⟨Additive.toMul (q : Additive V), hqQ⟩
  have hfix := htriv ⟨a, ha⟩ qQ
  change (a : A) • Additive.toMul (q : Additive V) =
    Additive.toMul (q : Additive V) at hfix
  simpa [qQ, S, hρ, Subrepresentation.toRepresentation] using hfix

private theorem theorem_9_4_typeIIIIV_frattini_quotient_complement_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ)
    [Fact (Nat.card W2).Prime]
    [Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF] :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (Q : Subgroup
        ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF))) →
        letI : IsInvariant (U ⊔ W1 : Subgroup G) MF (pCore (Nat.card W2) MF) :=
          pCore_isInvariant_of_normalizes_sec9
            (A := (U ⊔ W1 : Subgroup G)) (MF := MF) (p := Nat.card W2)
        letI : MulDistribMulAction (U ⊔ W1 : Subgroup G)
            ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
          quotientMulDistribMulAction
            (A := (U ⊔ W1 : Subgroup G)) (G := pCore (Nat.card W2) MF)
            (frattini (pCore (Nat.card W2) MF))
            (isInvariant_of_characteristic
              (A := (U ⊔ W1 : Subgroup G)) (G := pCore (Nat.card W2) MF)
              (frattini (pCore (Nat.card W2) MF)))
        IsInvariant (U ⊔ W1 : Subgroup G)
          ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) Q →
        letI : IsInvariant (U ⊔ W1 : Subgroup G) MF (pCore (Nat.card W2) MF) :=
          pCore_isInvariant_of_normalizes_sec9
            (A := (U ⊔ W1 : Subgroup G)) (MF := MF) (p := Nat.card W2)
        letI : MulDistribMulAction (U ⊔ W1 : Subgroup G)
            ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
          quotientMulDistribMulAction
            (A := (U ⊔ W1 : Subgroup G)) (G := pCore (Nat.card W2) MF)
            (frattini (pCore (Nat.card W2) MF))
            (isInvariant_of_characteristic
              (A := (U ⊔ W1 : Subgroup G)) (G := pCore (Nat.card W2) MF)
              (frattini (pCore (Nat.card W2) MF)))
        ∃ Qcompl : Subgroup
          ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)),
          IsCompl Q Qcompl ∧
            IsInvariant (U ⊔ W1 : Subgroup G)
              ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF))
              Qcompl := by
  classical
  intro h92 Q hQ_inv
  let UW1 : Subgroup G := U ⊔ W1
  let P : Subgroup MF := pCore (Nat.card W2) MF
  letI : IsInvariant UW1 MF P := by
    simpa [UW1, P] using
      pCore_isInvariant_of_normalizes_sec9
        (A := (U ⊔ W1 : Subgroup G)) (MF := MF) (p := Nat.card W2)
  letI : MulDistribMulAction UW1 (P ⧸ frattini P) :=
    quotientMulDistribMulAction (A := UW1) (G := P) (frattini P)
      (isInvariant_of_characteristic (A := UW1) (G := P) (frattini P))
  haveI : IsInvariant UW1 (P ⧸ frattini P) Q := by
    simpa [UW1, P] using hQ_inv
  have hcop :
      Nat.Coprime (Nat.card W2) (Nat.card UW1) := by
    simpa [UW1] using
      theorem_9_4_typeIIIIV_prime_coprime_UW1_sec9 M MF U W1 W2 q h92
  have hElem : IsElementaryAbelian (Nat.card W2) (P ⧸ frattini P) := by
    simpa [P] using
      elementaryAbelian_pCore_quotient_frattini (G := MF) (p := Nat.card W2)
  letI : IsElementaryAbelian (Nat.card W2) (P ⧸ frattini P) := hElem
  exact exists_isCompl_isInvariant_of_elementaryAbelian_coprime
    (G := P ⧸ frattini P) (A := UW1) (p := Nat.card W2) hcop Q

private theorem theorem_9_4_typeIIIIV_frattini_simple_factor_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ)
    [Fact (Nat.card W2).Prime]
    [Subgroup.Normalizes U MF]
    [Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF] :
    hypothesis_9_2_statement M MF U W1 W2 q →
      letI : IsInvariant U MF (pCore (Nat.card W2) MF) :=
        pCore_isInvariant_of_normalizes_sec9
          (A := U) (MF := MF) (p := Nat.card W2)
      letI : MulDistribMulAction U
          ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
        quotientMulDistribMulAction (A := U) (G := pCore (Nat.card W2) MF)
          (frattini (pCore (Nat.card W2) MF))
          (isInvariant_of_characteristic (A := U) (G := pCore (Nat.card W2) MF)
            (frattini (pCore (Nat.card W2) MF)))
      ¬ ActsTrivially (A := U)
          (G := (pCore (Nat.card W2) MF) ⧸
            frattini (pCore (Nat.card W2) MF)) →
        letI : IsInvariant (U ⊔ W1 : Subgroup G) MF
            (pCore (Nat.card W2) MF) :=
          pCore_isInvariant_of_normalizes_sec9
            (A := (U ⊔ W1 : Subgroup G)) (MF := MF) (p := Nat.card W2)
        letI : MulDistribMulAction (U ⊔ W1 : Subgroup G)
            ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
          quotientMulDistribMulAction
            (A := (U ⊔ W1 : Subgroup G)) (G := pCore (Nat.card W2) MF)
            (frattini (pCore (Nat.card W2) MF))
            (isInvariant_of_characteristic
              (A := (U ⊔ W1 : Subgroup G)) (G := pCore (Nat.card W2) MF)
              (frattini (pCore (Nat.card W2) MF)))
        (hElem : IsElementaryAbelian (Nat.card W2)
          ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF))) →
          letI : IsElementaryAbelian (Nat.card W2)
              ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
            hElem
          let ρ : Representation (ZMod (Nat.card W2)) (U ⊔ W1 : Subgroup G)
              (Additive
                ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF))) :=
            Theory.Representation.ofElementaryAbelianAction
              (A := (U ⊔ W1 : Subgroup G))
              (G := (pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF))
              (p := Nat.card W2)
          letI instAdd : AddCommGroup ρ.asModule :=
            Representation.instAddCommGroupAsModule ρ
          letI instMod : Module (MonoidAlgebra (ZMod (Nat.card W2))
              (U ⊔ W1 : Subgroup G)) ρ.asModule :=
            Representation.instModuleMonoidAlgebraAsModule ρ
          ∃ m : @Submodule (MonoidAlgebra (ZMod (Nat.card W2))
              (U ⊔ W1 : Subgroup G)) ρ.asModule _ instAdd.toAddCommMonoid instMod,
            IsSimpleModule (MonoidAlgebra (ZMod (Nat.card W2))
              (U ⊔ W1 : Subgroup G)) m ∧
              ¬ U.subgroupOf (U ⊔ W1 : Subgroup G) ≤
                (Subrepresentation.ofSubmodule' m).toRepresentation.ker := by
  classical
  intro h92 hU hElem
  let UW1 : Subgroup G := U ⊔ W1
  let P : Subgroup MF := pCore (Nat.card W2) MF
  let V : Type u := P ⧸ frattini P
  letI : IsInvariant U MF P :=
    pCore_isInvariant_of_normalizes_sec9
      (A := U) (MF := MF) (p := Nat.card W2)
  let hFr_inv_U : IsInvariant U P (frattini P) :=
    isInvariant_of_characteristic (A := U) (G := P) (frattini P)
  letI : MulAction.QuotientAction U (frattini P) :=
    quotientAction_of_isInvariant (A := U) (G := P) (frattini P) hFr_inv_U
  letI : MulDistribMulAction U V :=
    quotientMulDistribMulAction (A := U) (G := P) (frattini P) hFr_inv_U
  letI : IsInvariant UW1 MF P :=
    pCore_isInvariant_of_normalizes_sec9
      (A := UW1) (MF := MF) (p := Nat.card W2)
  letI : MulDistribMulAction UW1 V :=
    quotientMulDistribMulAction (A := UW1) (G := P) (frattini P)
      (isInvariant_of_characteristic (A := UW1) (G := P) (frattini P))
  letI : IsElementaryAbelian (Nat.card W2) V := by
    simpa [V, P] using hElem
  have hUsub : ¬ ActsTrivially (A := U.subgroupOf UW1) (G := V) := by
    intro htriv
    apply hU
    intro u x
    let uUW1 : UW1 := ⟨(u : G), (show U ≤ UW1 from le_sup_left) u.property⟩
    have huUW1 : uUW1 ∈ U.subgroupOf UW1 := by
      simp [uUW1, Subgroup.mem_subgroupOf, u.property]
    have hfix := htriv ⟨uUW1, huUW1⟩ x
    change u • x = x at hfix
    exact hfix
  have hcop :
      Nat.Coprime (Nat.card W2) (Nat.card UW1) := by
    simpa [UW1] using
      theorem_9_4_typeIIIIV_prime_coprime_UW1_sec9 M MF U W1 W2 q h92
  simpa [UW1, V, P] using
    exists_simple_submodule_nontrivial_of_not_actsTrivially_subgroup_sec9
      (A := UW1) (V := V) (p := Nat.card W2)
      (H := U.subgroupOf UW1) hcop hUsub

private theorem theorem_9_4_typeIIIIV_UW1_frattini_nontrivial_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U W1 W2 : Subgroup G)
    [Fact (Nat.card W2).Prime]
    [Subgroup.Normalizes U MF]
    [Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF] :
    letI : IsInvariant U MF (pCore (Nat.card W2) MF) :=
      pCore_isInvariant_of_normalizes_sec9
        (A := U) (MF := MF) (p := Nat.card W2)
    letI : MulDistribMulAction U
        ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
      quotientMulDistribMulAction (A := U) (G := pCore (Nat.card W2) MF)
        (frattini (pCore (Nat.card W2) MF))
        (isInvariant_of_characteristic (A := U) (G := pCore (Nat.card W2) MF)
          (frattini (pCore (Nat.card W2) MF)))
    ¬ ActsTrivially (A := U)
        (G := (pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) →
      letI : IsInvariant (U ⊔ W1 : Subgroup G) MF (pCore (Nat.card W2) MF) :=
        pCore_isInvariant_of_normalizes_sec9
          (A := (U ⊔ W1 : Subgroup G)) (MF := MF) (p := Nat.card W2)
      letI : MulDistribMulAction (U ⊔ W1 : Subgroup G)
          ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
        quotientMulDistribMulAction
          (A := (U ⊔ W1 : Subgroup G)) (G := pCore (Nat.card W2) MF)
          (frattini (pCore (Nat.card W2) MF))
          (isInvariant_of_characteristic
            (A := (U ⊔ W1 : Subgroup G)) (G := pCore (Nat.card W2) MF)
            (frattini (pCore (Nat.card W2) MF)))
      ¬ ActsTrivially (A := (U ⊔ W1 : Subgroup G))
          (G := (pCore (Nat.card W2) MF) ⧸
            frattini (pCore (Nat.card W2) MF)) := by
  classical
  intro hU hUW1
  apply hU
  intro u x
  let P : Subgroup MF := pCore (Nat.card W2) MF
  letI : IsInvariant U MF P := by
    simpa [P] using
      pCore_isInvariant_of_normalizes_sec9
        (A := U) (MF := MF) (p := Nat.card W2)
  letI : IsInvariant (U ⊔ W1 : Subgroup G) MF P := by
    simpa [P] using
      pCore_isInvariant_of_normalizes_sec9
        (A := (U ⊔ W1 : Subgroup G)) (MF := MF) (p := Nat.card W2)
  let uUW1 : (U ⊔ W1 : Subgroup G) :=
    ⟨(u : G), (show U ≤ U ⊔ W1 from le_sup_left) u.property⟩
  refine QuotientGroup.induction_on x ?_
  intro y
  have hfix := hUW1 uUW1 (QuotientGroup.mk' (frattini P) y)
  have hsmul : (u • y : P) = uUW1 • y := by
    apply Subtype.ext
    apply MF.subtype_injective
    change
      (u : G) * (((y : P) : MF) : G) * (u : G)⁻¹ =
        (uUW1 : G) * (((y : P) : MF) : G) * (uUW1 : G)⁻¹
    rfl
  change QuotientGroup.mk' (frattini P) (u • y) =
    QuotientGroup.mk' (frattini P) y
  change QuotientGroup.mk' (frattini P) (uUW1 • y) =
    QuotientGroup.mk' (frattini P) y at hfix
  rw [hsmul]
  exact hfix

private theorem not_actsTrivially_quotient_of_isCompl_nontrivial_subgroup_sec9
    {A V : Type u} [Group A] [Group V] [MulDistribMulAction A V]
    {H : Subgroup A} {Q C : Subgroup V}
    [C.Normal]
    (hQ_inv : IsInvariant A V Q)
    (hC_inv : IsInvariant A V C)
    (hQC : IsCompl Q C)
    (hQ_nontriv : ¬ ∀ h : H, ∀ q : Q, (h : A) • (q : V) = (q : V)) :
    letI hC_inv_H : IsInvariant H V C :=
      { invariant := fun h v => hC_inv.invariant (h : A) v }
    letI : MulDistribMulAction H (V ⧸ C) :=
      quotientMulDistribMulAction (A := H) (G := V) C hC_inv_H
    ¬ ActsTrivially (A := H) (G := V ⧸ C) := by
  classical
  let hC_inv_H : IsInvariant H V C :=
    { invariant := fun h v => hC_inv.invariant (h : A) v }
  letI : IsInvariant H V C := hC_inv_H
  letI : MulAction.QuotientAction H C :=
    quotientAction_of_isInvariant (A := H) (G := V) C hC_inv_H
  letI : MulDistribMulAction H (V ⧸ C) :=
    quotientMulDistribMulAction (A := H) (G := V) C hC_inv_H
  intro htriv
  apply hQ_nontriv
  intro h q
  have hqQ : (q : V) ∈ Q := q.property
  have hsmulQ : (h : H) • (q : V) ∈ Q := by
    change (h : A) • (q : V) ∈ Q
    exact (hQ_inv.invariant (h : A) (q : V)).1 hqQ
  have hfixquot := htriv h (QuotientGroup.mk' C (q : V))
  have hsmul_mk :
      (h : H) • QuotientGroup.mk' C (q : V) =
        QuotientGroup.mk' C ((h : H) • (q : V)) := by
    simp
  have hmk_eq :
      QuotientGroup.mk' C ((h : H) • (q : V)) =
        QuotientGroup.mk' C (q : V) := by
    simpa [hsmul_mk] using hfixquot
  have hdivC : ((h : H) • (q : V)) / (q : V) ∈ C :=
    (QuotientGroup.eq_iff_div_mem).1 hmk_eq
  have hdivQ : ((h : H) • (q : V)) / (q : V) ∈ Q :=
    Q.div_mem hsmulQ hqQ
  have hdivInf : ((h : H) • (q : V)) / (q : V) ∈ Q ⊓ C := by
    exact ⟨hdivQ, hdivC⟩
  have hdivBot : ((h : H) • (q : V)) / (q : V) ∈ (⊥ : Subgroup V) := by
    simpa [hQC.inf_eq_bot] using hdivInf
  have hdivOne : ((h : H) • (q : V)) / (q : V) = 1 := by
    simpa using hdivBot
  have heqH : (h : H) • (q : V) = (q : V) := div_eq_one.mp hdivOne
  change (h : A) • (q : V) = (q : V) at heqH
  exact heqH


private noncomputable def theorem_9_4_typeIIIIV_liftedH0_sec9
    {G : Type u} [Group G] [Finite G]
    (MF : Subgroup G) (p : ℕ)
    (Qcompl : Subgroup ((pCore p MF) ⧸ frattini (pCore p MF))) :
    Subgroup G :=
  let P : Subgroup MF := pCore p MF
  let C : Subgroup P := Qcompl.comap (QuotientGroup.mk' (frattini P))
  let K : Subgroup MF := pPrimeCore p MF
  ((C.map P.subtype) ⊔ K).map MF.subtype

private theorem theorem_9_4_typeIIIIV_liftedH0_le_MF_sec9
    {G : Type u} [Group G] [Finite G]
    (MF : Subgroup G) (p : ℕ)
    (Qcompl : Subgroup ((pCore p MF) ⧸ frattini (pCore p MF))) :
    theorem_9_4_typeIIIIV_liftedH0_sec9 MF p Qcompl ≤ MF := by
  intro x hx
  rcases hx with ⟨y, _hy, rfl⟩
  exact y.property

private theorem theorem_9_4_typeIIIIV_liftedH0_subgroupOf_MF_eq_sec9
    {G : Type u} [Group G] [Finite G]
    (MF : Subgroup G) (p : ℕ)
    (Qcompl : Subgroup ((pCore p MF) ⧸ frattini (pCore p MF))) :
    (theorem_9_4_typeIIIIV_liftedH0_sec9 MF p Qcompl).subgroupOf MF =
      ((Qcompl.comap (QuotientGroup.mk' (frattini (pCore p MF)))).map
          (pCore p MF).subtype ⊔ pPrimeCore p MF) := by
  let P : Subgroup MF := pCore p MF
  let C : Subgroup P := Qcompl.comap (QuotientGroup.mk' (frattini P))
  let K : Subgroup MF := pPrimeCore p MF
  have hsub :
      (((C.map P.subtype) ⊔ K).map MF.subtype).subgroupOf MF =
        (C.map P.subtype) ⊔ K :=
    subgroupOf_map_subtype_eq_sec9 (G := G) MF ((C.map P.subtype) ⊔ K)
  simpa [theorem_9_4_typeIIIIV_liftedH0_sec9, P, C, K] using hsub

private theorem theorem_9_4_typeIIIIV_frattini_le_lifted_preimage_sec9
    {G : Type u} [Group G] [Finite G]
    (MF : Subgroup G) (p : ℕ)
    (Qcompl : Subgroup ((pCore p MF) ⧸ frattini (pCore p MF))) :
    frattini (pCore p MF) ≤
      Qcompl.comap (QuotientGroup.mk' (frattini (pCore p MF))) := by
  simpa using
    (QuotientGroup.le_comap_mk' (frattini (pCore p MF)) Qcompl)

private theorem theorem_9_4_typeIIIIV_lifted_preimage_map_eq_sec9
    {G : Type u} [Group G] [Finite G]
    (MF : Subgroup G) (p : ℕ)
    (Qcompl : Subgroup ((pCore p MF) ⧸ frattini (pCore p MF))) :
    (Qcompl.comap (QuotientGroup.mk' (frattini (pCore p MF)))).map
        (QuotientGroup.mk' (frattini (pCore p MF))) = Qcompl := by
  exact Subgroup.map_comap_eq_self_of_surjective
    (f := QuotientGroup.mk' (frattini (pCore p MF)))
    (QuotientGroup.mk'_surjective (frattini (pCore p MF))) Qcompl

private theorem theorem_9_4_typeIIIIV_liftedH0_subgroupOf_MF_normal_sec9
    {G : Type u} [Group G] [Finite G]
    (MF : Subgroup G) (p : ℕ) [Fact p.Prime]
    (hMFnil : Group.IsNilpotent MF)
    (Qcompl : Subgroup ((pCore p MF) ⧸ frattini (pCore p MF)))
    [Qcompl.Normal] :
    ((theorem_9_4_typeIIIIV_liftedH0_sec9 MF p Qcompl).subgroupOf MF).Normal := by
  classical
  let P : Subgroup MF := pCore p MF
  let C : Subgroup P := Qcompl.comap (QuotientGroup.mk' (frattini P))
  let Cmap : Subgroup MF := C.map P.subtype
  let K : Subgroup MF := pPrimeCore p MF
  have hC_normal : C.Normal := by
    dsimp [C]
    infer_instance
  have hCmap_le_P : Cmap ≤ P := by
    intro x hx
    rcases hx with ⟨y, _hyC, rfl⟩
    exact y.property
  have hCmap_subgroupOf_P_eq : Cmap.subgroupOf P = C := by
    simpa [Cmap] using subgroupOf_map_subtype_eq_sec9 (G := MF) P C
  have hCmap_subgroupOf_P_normal : (Cmap.subgroupOf P).Normal := by
    simpa [hCmap_subgroupOf_P_eq] using hC_normal
  have hP_le_norm_Cmap : P ≤ Subgroup.normalizer (Cmap : Set MF) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCmap_le_P).1
      hCmap_subgroupOf_P_normal
  have hK_le_centP : K ≤ Subgroup.centralizer (P : Set MF) := by
    have hP_p : IsPGroup p P := by
      simpa [P] using pCore_isPGroup (G := MF) (p := p)
    simpa [P, K] using
      pPrimeCore_le_centralizer_of_normal_pgroup
        (G := MF) (p := p) (R := P) hP_p
  have hcentP_le_centCmap :
      Subgroup.centralizer (P : Set MF) ≤
        Subgroup.centralizer (Cmap : Set MF) :=
    Subgroup.centralizer_le
      (show (Cmap : Set MF) ⊆ (P : Set MF) from hCmap_le_P)
  have hK_le_norm_Cmap : K ≤ Subgroup.normalizer (Cmap : Set MF) :=
    (hK_le_centP.trans hcentP_le_centCmap).trans
      (centralizer_le_normalizer Cmap)
  have htop_le_PK : (⊤ : Subgroup MF) ≤ P ⊔ K := by
    haveI : Group.IsNilpotent MF := hMFnil
    have hnilTop : Group.IsNilpotent (↥(⊤ : Subgroup MF)) := by
      exact Group.nilpotent_of_mulEquiv
        (G := MF) (G' := ↥(⊤ : Subgroup MF))
        (Subgroup.topEquiv.symm : MF ≃* ↥(⊤ : Subgroup MF))
    have hTop_le_iSup :
        (⊤ : Subgroup MF) ≤
          ⨆ q : (Nat.card MF).primeFactors.attach, pCore q.1 MF :=
      normal_nilpotent_le_sup_pCore
        (G := MF) (N := (⊤ : Subgroup MF)) (hN := inferInstance) hnilTop
    refine hTop_le_iSup.trans ?_
    refine iSup_le ?_
    intro q
    by_cases hqp : q.1 = p
    · subst hqp
      exact le_sup_left
    · have hqprime : Nat.Prime q.1 := Nat.prime_of_mem_primeFactors q.1.2
      letI : Fact (Nat.Prime q.1) := ⟨hqprime⟩
      obtain ⟨n, hn⟩ := (pCore_isPGroup (G := MF) (p := q.1)).exists_card_eq
      have hcop : Nat.Coprime p (Nat.card (pCore q.1 MF)) := by
        rw [hn]
        have hpq : p ≠ q.1 := by
          intro hpq'
          exact hqp hpq'.symm
        exact ((Nat.coprime_primes (Fact.out : Nat.Prime p) hqprime).2 hpq).pow_right n
      exact
        (le_sSup (show pCore q.1 MF ∈
          {K : Subgroup MF | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
            ⟨inferInstance, hcop⟩)).trans le_sup_right
  have htop_le_norm_Cmap :
      (⊤ : Subgroup MF) ≤ Subgroup.normalizer (Cmap : Set MF) :=
    htop_le_PK.trans (sup_le hP_le_norm_Cmap hK_le_norm_Cmap)
  have hCmap_normal : Cmap.Normal := by
    refine ⟨?_⟩
    intro n hn g
    have hg_norm : g ∈ Subgroup.normalizer (Cmap : Set MF) :=
      htop_le_norm_Cmap (by simp)
    exact ((Subgroup.mem_normalizer_iff.mp hg_norm n).1 hn)
  have hH0MF_normal : (Cmap ⊔ K).Normal := by
    haveI : Cmap.Normal := hCmap_normal
    haveI : K.Normal := by
      simpa [K] using (pPrimeCore_normal (G := MF) (p := p))
    exact Subgroup.sup_normal Cmap K
  rw [theorem_9_4_typeIIIIV_liftedH0_subgroupOf_MF_eq_sec9]
  simpa [P, C, Cmap, K] using hH0MF_normal

private theorem isInvariant_comap_quotient_mk'_sec9
    {A R : Type u} [Group A] [Group R] [MulDistribMulAction A R]
    (N : Subgroup R) [N.Normal]
    (hN_inv : IsInvariant A R N)
    (Q : Subgroup (R ⧸ N))
    (hQ_inv :
      letI : MulDistribMulAction A (R ⧸ N) :=
        quotientMulDistribMulAction (A := A) (G := R) N hN_inv;
      IsInvariant A (R ⧸ N) Q) :
    IsInvariant A R (Q.comap (QuotientGroup.mk' N)) := by
  classical
  letI : MulDistribMulAction A (R ⧸ N) :=
    quotientMulDistribMulAction (A := A) (G := R) N hN_inv
  have hQ_inv' : IsInvariant A (R ⧸ N) Q := hQ_inv
  refine ⟨?_⟩
  intro a x
  constructor
  · intro hx
    change QuotientGroup.mk' N x ∈ Q at hx
    change QuotientGroup.mk' N (a • x) ∈ Q
    have hsmul_mk :
        a • QuotientGroup.mk' N x = QuotientGroup.mk' N (a • x) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := N) a x)
    have hmem :=
      (IsInvariant.invariant (A := A) (G := R ⧸ N) (H := Q)
        a (QuotientGroup.mk' N x)).1 hx
    simpa [hsmul_mk] using hmem
  · intro hx
    change QuotientGroup.mk' N (a • x) ∈ Q at hx
    change QuotientGroup.mk' N x ∈ Q
    have hsmul_mk :
        a • QuotientGroup.mk' N x = QuotientGroup.mk' N (a • x) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := N) a x)
    have hx' : a • QuotientGroup.mk' N x ∈ Q := by
      simpa [hsmul_mk] using hx
    exact
      (IsInvariant.invariant (A := A) (G := R ⧸ N) (H := Q)
        a (QuotientGroup.mk' N x)).2 hx'

private theorem theorem_9_4_typeIIIIV_liftedH0_subgroupOf_MF_isInvariant_sec9
    {G : Type u} [Group G] [Finite G]
    (A MF : Subgroup G) (p : ℕ) [Fact p.Prime]
    [Subgroup.Normalizes A MF]
    (Qcompl : Subgroup ((pCore p MF) ⧸ frattini (pCore p MF))) :
    (let P : Subgroup MF := pCore p MF;
      letI : IsInvariant A MF P :=
        pCore_isInvariant_of_normalizes_sec9 (A := A) (MF := MF) (p := p);
      letI : MulDistribMulAction A (P ⧸ frattini P) :=
        quotientMulDistribMulAction (A := A) (G := P) (frattini P)
          (isInvariant_of_characteristic (A := A) (G := P) (frattini P));
      IsInvariant A (P ⧸ frattini P) Qcompl) →
      IsInvariant A MF
        ((theorem_9_4_typeIIIIV_liftedH0_sec9 MF p Qcompl).subgroupOf MF) := by
  classical
  intro hQcompl_inv
  let P : Subgroup MF := pCore p MF
  let C : Subgroup P := Qcompl.comap (QuotientGroup.mk' (frattini P))
  let Cmap : Subgroup MF := C.map P.subtype
  let K : Subgroup MF := pPrimeCore p MF
  letI : IsInvariant A MF P :=
    pCore_isInvariant_of_normalizes_sec9 (A := A) (MF := MF) (p := p)
  let hFr_inv : IsInvariant A P (frattini P) :=
    isInvariant_of_characteristic (A := A) (G := P) (frattini P)
  letI : MulDistribMulAction A (P ⧸ frattini P) :=
    quotientMulDistribMulAction (A := A) (G := P) (frattini P) hFr_inv
  have hQcompl_inv' : IsInvariant A (P ⧸ frattini P) Qcompl := by
    simpa [P] using hQcompl_inv
  have hC_inv : IsInvariant A P C := by
    simpa [C] using
      isInvariant_comap_quotient_mk'_sec9
        (A := A) (R := P) (N := frattini P) hFr_inv Qcompl hQcompl_inv'
  have hCmap_inv : IsInvariant A MF Cmap := by
    haveI : IsInvariant A P C := hC_inv
    simpa [Cmap] using isInvariant_map_subtype (A := A) (G := MF) P C
  have hK_inv : IsInvariant A MF K := by
    simpa [K] using
      isInvariant_of_characteristic (A := A) (G := MF) (pPrimeCore p MF)
  have hsup_inv : IsInvariant A MF (Cmap ⊔ K) := by
    haveI : IsInvariant A MF Cmap := hCmap_inv
    haveI : IsInvariant A MF K := hK_inv
    exact isInvariant_sup Cmap K
  rw [theorem_9_4_typeIIIIV_liftedH0_subgroupOf_MF_eq_sec9]
  simpa [P, C, Cmap, K] using hsup_inv

private theorem theorem_9_4_typeIIIIV_liftedH0_subgroupOf_M_normal_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ)
    [Fact (Nat.card W2).Prime]
    [Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF] :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (Qcompl : Subgroup
        ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF))) →
      (let UW1 : Subgroup G := U ⊔ W1;
        let P : Subgroup MF := pCore (Nat.card W2) MF;
        letI : IsInvariant UW1 MF P :=
          pCore_isInvariant_of_normalizes_sec9
            (A := UW1) (MF := MF) (p := Nat.card W2);
        letI : MulDistribMulAction UW1 (P ⧸ frattini P) :=
          quotientMulDistribMulAction (A := UW1) (G := P) (frattini P)
            (isInvariant_of_characteristic (A := UW1) (G := P) (frattini P));
        IsInvariant UW1 (P ⧸ frattini P) Qcompl) →
      [Qcompl.Normal] →
        ((theorem_9_4_typeIIIIV_liftedH0_sec9 MF (Nat.card W2) Qcompl).subgroupOf M).Normal := by
  classical
  intro h92 Qcompl hQcompl_inv _hQcompl_normal
  let p : ℕ := Nat.card W2
  let UW1 : Subgroup G := U ⊔ W1
  let H0 : Subgroup G := theorem_9_4_typeIIIIV_liftedH0_sec9 MF p Qcompl
  let H0MF : Subgroup MF := H0.subgroupOf MF
  have h92full : hypothesis_9_2_statement M MF U W1 W2 q := h92
  have hMF := h92.mf
  rcases hMF.1 with ⟨hMF_le_M, _hMF_normal_M, hMFnil, _hMFhall⟩
  have hPsource := h92.typePDefinitionData
  rcases hPsource with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hUleD,
      _hUnil, _hW1normU, hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hH0_le_MF : H0 ≤ MF := by
    simpa [H0, p] using
      theorem_9_4_typeIIIIV_liftedH0_le_MF_sec9 MF (Nat.card W2) Qcompl
  have hH0_le_M : H0 ≤ M := hH0_le_MF.trans hMF_le_M
  have hH0_normal_MF : H0MF.Normal := by
    simpa [H0MF, H0, p] using
      theorem_9_4_typeIIIIV_liftedH0_subgroupOf_MF_normal_sec9
        MF (Nat.card W2) hMFnil Qcompl
  have hH0_inv_UW1 : IsInvariant UW1 MF H0MF := by
    have hQcompl_inv' :
        let P : Subgroup MF := pCore p MF;
        letI : IsInvariant UW1 MF P :=
          pCore_isInvariant_of_normalizes_sec9 (A := UW1) (MF := MF) (p := p);
        letI : MulDistribMulAction UW1 (P ⧸ frattini P) :=
          quotientMulDistribMulAction (A := UW1) (G := P) (frattini P)
            (isInvariant_of_characteristic (A := UW1) (G := P) (frattini P));
        IsInvariant UW1 (P ⧸ frattini P) Qcompl := by
      simpa [UW1, p] using hQcompl_inv
    simpa [H0MF, H0, p, UW1] using
      theorem_9_4_typeIIIIV_liftedH0_subgroupOf_MF_isInvariant_sec9
        (A := UW1) (MF := MF) (p := p) Qcompl hQcompl_inv'
  have hMF_norm_H0 : MF ≤ Subgroup.normalizer (H0 : Set G) := by
    refine subgroup_le_normalizer_of_conj_mem H0 MF ?_
    intro a x hxH0
    let aMF : MF := a
    have hxMF : x ∈ MF := hH0_le_MF hxH0
    let xMF : MF := ⟨x, hxMF⟩
    have hxH0MF : xMF ∈ H0MF := by
      simpa [H0MF, xMF, Subgroup.mem_subgroupOf] using hxH0
    have hconjH0MF : aMF * xMF * aMF⁻¹ ∈ H0MF :=
      hH0_normal_MF.conj_mem xMF hxH0MF aMF
    simpa [H0MF, aMF, xMF, Subgroup.mem_subgroupOf] using hconjH0MF
  have hUW1_norm_H0 : UW1 ≤ Subgroup.normalizer (H0 : Set G) := by
    refine subgroup_le_normalizer_of_conj_mem H0 UW1 ?_
    intro a x hxH0
    let aUW1 : UW1 := a
    have hxMF : x ∈ MF := hH0_le_MF hxH0
    let xMF : MF := ⟨x, hxMF⟩
    have hxH0MF : xMF ∈ H0MF := by
      simpa [H0MF, xMF, Subgroup.mem_subgroupOf] using hxH0
    have hconjH0MF : aUW1 • xMF ∈ H0MF :=
      (IsInvariant.invariant (A := UW1) (G := MF) (H := H0MF)
        aUW1 xMF).1 hxH0MF
    simpa [H0MF, H0, aUW1, xMF, Subgroup.mem_subgroupOf,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hconjH0MF
  have hM_eq : M = (MF ⊔ U) ⊔ W1 := by
    calc
      M = ambientDerivedSubgroup M ⊔ W1 := hcompMW1.2.2.1
      _ = (MF ⊔ U) ⊔ W1 := by rw [hcompDU.2.2.1]
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).2
  rw [hM_eq]
  exact sup_le
    (sup_le hMF_norm_H0 (le_sup_left.trans hUW1_norm_H0))
    (le_sup_right.trans hUW1_norm_H0)

private theorem card_eq_one_of_isPGroup_of_coprime_sec9
    {A : Type u} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime]
    (hA : IsPGroup p A) (hcop : Nat.Coprime p (Nat.card A)) :
    Nat.card A = 1 := by
  rcases hA.exists_card_eq with ⟨n, hn⟩
  cases n with
  | zero =>
      simpa [Nat.card_eq_fintype_card] using hn
  | succ n =>
      have hpdvd : p ∣ Nat.card A := by
        rw [hn]
        exact ⟨p ^ n, by rw [pow_succ, mul_comm]⟩
      have hnot : ¬ p ∣ Nat.card A :=
        (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mp hcop
      exact False.elim (hnot hpdvd)

private theorem pCore_inf_pPrimeCore_eq_bot_sec9
    {Q : Type u} [Group Q] [Finite Q]
    (p : ℕ) [Fact p.Prime] :
    pCore p Q ⊓ pPrimeCore p Q = ⊥ := by
  let I : Subgroup Q := pCore p Q ⊓ pPrimeCore p Q
  have hI_sub_p : IsPGroup p (I.subgroupOf (pCore p Q)) :=
    (pCore_isPGroup (G := Q) (p := p)).to_subgroup (I.subgroupOf (pCore p Q))
  have hI_p : IsPGroup p I :=
    hI_sub_p.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := I) (K := pCore p Q) inf_le_left)
  have hI_cop : Nat.Coprime p (Nat.card I) :=
    Nat.Coprime.of_dvd_right
      (Subgroup.card_dvd_of_le (show I ≤ pPrimeCore p Q from inf_le_right))
      (pPrimeCore_coprime_card (G := Q) (p := p))
  have hcard : Nat.card I = 1 :=
    card_eq_one_of_isPGroup_of_coprime_sec9 hI_p hI_cop
  have hI_bot : I = ⊥ := (Subgroup.card_eq_one (H := I)).1 hcard
  simpa [I] using hI_bot

private theorem nilpotent_top_le_pCore_sup_pPrimeCore_sec9
    {Q : Type u} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (hQnil : Group.IsNilpotent Q) :
    (⊤ : Subgroup Q) ≤ pCore p Q ⊔ pPrimeCore p Q := by
  classical
  haveI : Group.IsNilpotent Q := hQnil
  have hnilTop : Group.IsNilpotent (↥(⊤ : Subgroup Q)) := by
    exact Group.nilpotent_of_mulEquiv
      (G := Q) (G' := ↥(⊤ : Subgroup Q))
      (Subgroup.topEquiv.symm : Q ≃* ↥(⊤ : Subgroup Q))
  have hTop_le_iSup :
      (⊤ : Subgroup Q) ≤ ⨆ q : (Nat.card Q).primeFactors.attach, pCore q.1 Q :=
    normal_nilpotent_le_sup_pCore
      (G := Q) (N := (⊤ : Subgroup Q)) (hN := inferInstance) hnilTop
  refine hTop_le_iSup.trans ?_
  refine iSup_le ?_
  intro q
  by_cases hqp : q.1 = p
  · subst hqp
    exact le_sup_left
  · have hqprime : Nat.Prime q.1 := Nat.prime_of_mem_primeFactors q.1.2
    letI : Fact (Nat.Prime q.1) := ⟨hqprime⟩
    obtain ⟨n, hn⟩ := (pCore_isPGroup (G := Q) (p := q.1)).exists_card_eq
    have hcop : Nat.Coprime p (Nat.card (pCore q.1 Q)) := by
      rw [hn]
      have hpq : p ≠ q.1 := by
        intro hpq'
        exact hqp hpq'.symm
      exact ((Nat.coprime_primes (Fact.out : Nat.Prime p) hqprime).2 hpq).pow_right n
    exact
      (le_sSup (show pCore q.1 Q ∈
        {K : Subgroup Q | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
          ⟨inferInstance, hcop⟩)).trans le_sup_right

private noncomputable def quotient_equiv_of_sup_eq_top_inf_eq_bot_sec9
    {G : Type u} [Group G]
    (P K H : Subgroup G) [K.Normal] [H.Normal]
    (C : Subgroup P) [C.Normal]
    (hH_eq : H = C.map P.subtype ⊔ K)
    (hPK_top : P ⊔ K = (⊤ : Subgroup G))
    (hP_inf_K : P ⊓ K = ⊥) :
    (P ⧸ C) ≃* (G ⧸ H) := by
  classical
  have hCmap_le_H : C.map P.subtype ≤ H := by
    rw [hH_eq]
    exact le_sup_left
  have hK_le_H : K ≤ H := by
    rw [hH_eq]
    exact le_sup_right
  let φ : P →* G ⧸ H := (QuotientGroup.mk' H).comp P.subtype
  have hker : φ.ker = C := by
    ext x
    constructor
    · intro hx
      have hxφ : φ x = 1 := MonoidHom.mem_ker.mp hx
      have hxH : ((x : P) : G) ∈ H := by
        exact (QuotientGroup.eq_one_iff (N := H) (x := ((x : P) : G))).1
          (by simpa [φ] using hxφ)
      have hxH' : ((x : P) : G) ∈ C.map P.subtype ⊔ K := by
        simpa [hH_eq] using hxH
      rcases (Subgroup.mem_sup_of_normal_right.1 hxH') with ⟨c, hcCmap, k, hkK, hck⟩
      rcases hcCmap with ⟨cP, hcC, hcP_eq⟩
      have hcP : c ∈ P := by
        rw [← hcP_eq]
        exact cP.property
      have hkP : k ∈ P := by
        have hk_eq : k = c⁻¹ * ((x : P) : G) := by
          calc
            k = 1 * k := by simp
            _ = c⁻¹ * c * k := by simp
            _ = c⁻¹ * (c * k) := by group
            _ = c⁻¹ * ((x : P) : G) := by rw [hck]
        rw [hk_eq]
        exact P.mul_mem (P.inv_mem hcP) x.property
      have hk_bot : k ∈ (⊥ : Subgroup G) := by
        simpa [hP_inf_K] using (show k ∈ P ⊓ K from ⟨hkP, hkK⟩)
      have hk_one : k = 1 := by simpa using hk_bot
      have hx_eq_cP : x = cP := by
        apply Subtype.ext
        calc
          ((x : P) : G) = c * k := hck.symm
          _ = c := by simp [hk_one]
          _ = cP := hcP_eq.symm
      simpa [hx_eq_cP] using hcC
    · intro hx
      have hxCmap : ((x : P) : G) ∈ C.map P.subtype := ⟨x, hx, rfl⟩
      have hxH : ((x : P) : G) ∈ H := hCmap_le_H hxCmap
      have hxφ : φ x = 1 :=
        (QuotientGroup.eq_one_iff (N := H) (x := ((x : P) : G))).2 hxH
      exact MonoidHom.mem_ker.mpr (by simpa [φ] using hxφ)
  have hrange : φ.range = ⊤ := by
    apply top_unique
    intro y _hy
    rcases QuotientGroup.mk'_surjective H y with ⟨g, rfl⟩
    have hg_PK : g ∈ P ⊔ K := by
      rw [hPK_top]
      exact Subgroup.mem_top g
    rcases (Subgroup.mem_sup_of_normal_right.1 hg_PK) with ⟨p0, hp0, k0, hk0, hpk0⟩
    refine ⟨⟨p0, hp0⟩, ?_⟩
    apply (QuotientGroup.eq_iff_div_mem).2
    have hk0H : k0 ∈ H := hK_le_H hk0
    have hconjH : p0 * k0⁻¹ * p0⁻¹ ∈ H :=
      (show H.Normal from inferInstance).conj_mem (k0⁻¹) (H.inv_mem hk0H) p0
    have hdiv_eq : (p0 : G) / g = p0 * k0⁻¹ * p0⁻¹ := by
      rw [← hpk0, div_eq_mul_inv, mul_inv_rev]
      simp [mul_assoc]
    simpa [φ, hdiv_eq] using hconjH
  exact
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans
        ((MulEquiv.subgroupCongr hrange).trans
          (Subgroup.topEquiv : (⊤ : Subgroup (G ⧸ H)) ≃* (G ⧸ H))))

private theorem subgroupOf_sup_eq_left_of_inf_eq_bot_sec9
    {G : Type u} [Group G]
    (P K : Subgroup G) [K.Normal]
    (C : Subgroup P)
    (hP_inf_K : P ⊓ K = ⊥) :
    ((C.map P.subtype ⊔ K).subgroupOf P) = C := by
  ext x
  constructor
  · intro hx
    have hx' : ((x : P) : G) ∈ C.map P.subtype ⊔ K := by
      simpa [Subgroup.mem_subgroupOf] using hx
    rcases (Subgroup.mem_sup_of_normal_right.1 hx') with ⟨c, hcCmap, k, hkK, hck⟩
    rcases hcCmap with ⟨cP, hcC, hcP_eq⟩
    have hcP : c ∈ P := by
      rw [← hcP_eq]
      exact cP.property
    have hkP : k ∈ P := by
      have hk_eq : k = c⁻¹ * ((x : P) : G) := by
        calc
          k = 1 * k := by simp
          _ = c⁻¹ * c * k := by simp
          _ = c⁻¹ * (c * k) := by group
          _ = c⁻¹ * ((x : P) : G) := by rw [hck]
      rw [hk_eq]
      exact P.mul_mem (P.inv_mem hcP) x.property
    have hk_bot : k ∈ (⊥ : Subgroup G) := by
      simpa [hP_inf_K] using (show k ∈ P ⊓ K from ⟨hkP, hkK⟩)
    have hk_one : k = 1 := by simpa using hk_bot
    have hx_eq_cP : x = cP := by
      apply Subtype.ext
      calc
        ((x : P) : G) = c * k := hck.symm
        _ = c := by simp [hk_one]
        _ = cP := hcP_eq.symm
    simpa [hx_eq_cP] using hcC
  · intro hx
    change ((x : P) : G) ∈ C.map P.subtype ⊔ K
    exact Subgroup.mem_sup_left ⟨x, hx, rfl⟩

private noncomputable def theorem_9_4_typeIIIIV_liftedH0_pCore_quotient_equiv_sec9
    {G : Type u} [Group G] [Finite G]
    (MF : Subgroup G) (p : ℕ) [Fact p.Prime]
    (hMFnil : Group.IsNilpotent MF)
    (Qcompl : Subgroup ((pCore p MF) ⧸ frattini (pCore p MF)))
    [Qcompl.Normal]
    (H : Subgroup MF) [H.Normal]
    (hH_eq :
      H =
        ((Qcompl.comap (QuotientGroup.mk' (frattini (pCore p MF)))).map
            (pCore p MF).subtype ⊔ pPrimeCore p MF)) :
    let P : Subgroup MF := pCore p MF
    let C : Subgroup P := Qcompl.comap (QuotientGroup.mk' (frattini P))
    (P ⧸ C) ≃* (MF ⧸ H) := by
  classical
  let P : Subgroup MF := pCore p MF
  let C : Subgroup P := Qcompl.comap (QuotientGroup.mk' (frattini P))
  let Cmap : Subgroup MF := C.map P.subtype
  let K : Subgroup MF := pPrimeCore p MF
  haveI : K.Normal := by
    simpa [K] using (pPrimeCore_normal (G := MF) (p := p))
  have hH_eq' : H = Cmap ⊔ K := by
    simpa [P, C, Cmap, K] using hH_eq
  have htop_le_PK : (⊤ : Subgroup MF) ≤ P ⊔ K := by
    simpa [P, K] using
      nilpotent_top_le_pCore_sup_pPrimeCore_sec9 (Q := MF) (p := p) hMFnil
  have hPK_top : P ⊔ K = (⊤ : Subgroup MF) := top_unique htop_le_PK
  have hP_inf_K : P ⊓ K = ⊥ := by
    simpa [P, K] using pCore_inf_pPrimeCore_eq_bot_sec9 (Q := MF) p
  exact
    quotient_equiv_of_sup_eq_top_inf_eq_bot_sec9
      (P := P) (K := K) (H := H) (C := C) hH_eq' hPK_top hP_inf_K

private theorem theorem_9_4_typeIIIIV_liftedH0_pCore_subgroupOf_eq_sec9
    {G : Type u} [Group G] [Finite G]
    (MF : Subgroup G) (p : ℕ) [Fact p.Prime]
    (Qcompl : Subgroup ((pCore p MF) ⧸ frattini (pCore p MF)))
    (H : Subgroup MF)
    (hH_eq :
      H =
        ((Qcompl.comap (QuotientGroup.mk' (frattini (pCore p MF)))).map
            (pCore p MF).subtype ⊔ pPrimeCore p MF)) :
    let P : Subgroup MF := pCore p MF
    let C : Subgroup P := Qcompl.comap (QuotientGroup.mk' (frattini P))
    H.subgroupOf P = C := by
  classical
  let P : Subgroup MF := pCore p MF
  let C : Subgroup P := Qcompl.comap (QuotientGroup.mk' (frattini P))
  let Cmap : Subgroup MF := C.map P.subtype
  let K : Subgroup MF := pPrimeCore p MF
  haveI : K.Normal := by
    simpa [K] using (pPrimeCore_normal (G := MF) (p := p))
  have hH_eq' : H = Cmap ⊔ K := by
    simpa [P, C, Cmap, K] using hH_eq
  have hP_inf_K : P ⊓ K = ⊥ := by
    simpa [P, K] using pCore_inf_pPrimeCore_eq_bot_sec9 (Q := MF) p
  rw [hH_eq']
  exact subgroupOf_sup_eq_left_of_inf_eq_bot_sec9 P K C hP_inf_K

private theorem inf_simple_factor_eq_bot_or_eq_self_sec9
    {A V : Type u} [Group A] [Group V]
    {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p V] [MulDistribMulAction A V]
    (Q L : Subgroup V)
    (hQ_inv : IsInvariant A V Q)
    (hL_inv : IsInvariant A V L) :
    let ρ : Representation (ZMod p) A (Additive V) :=
      Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := p)
    letI instAdd : AddCommGroup ρ.asModule :=
      Representation.instAddCommGroupAsModule ρ
    letI instMod : Module (MonoidAlgebra (ZMod p) A) ρ.asModule :=
      Representation.instModuleMonoidAlgebraAsModule ρ
    (m : @Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule _
      instAdd.toAddCommMonoid instMod) →
      IsSimpleModule (MonoidAlgebra (ZMod p) A) m →
      Q = (Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))).symm
        (Subrepresentation.ofSubmodule' m).toSubmodule →
      L ⊓ Q = ⊥ ∨ L ⊓ Q = Q := by
  classical
  intro ρ m hm_simple hQ_eq
  let instAddRho : AddCommGroup ρ.asModule := Representation.instAddCommGroupAsModule ρ
  letI : AddCommGroup ρ.asModule := instAddRho
  let instModRho : Module (MonoidAlgebra (ZMod p) A) ρ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  letI : Module (MonoidAlgebra (ZMod p) A) ρ.asModule := instModRho
  let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  let RQ : Subgroup V := L ⊓ Q
  have hRQ_inv : IsInvariant A V RQ := by
    constructor
    intro a v
    constructor
    · intro hv
      exact ⟨(hL_inv.invariant a v).1 hv.1, (hQ_inv.invariant a v).1 hv.2⟩
    · intro hv
      exact ⟨(hL_inv.invariant a v).2 hv.1, (hQ_inv.invariant a v).2 hv.2⟩
  let σ : Subrepresentation ρ :=
    { toSubmodule := η RQ
      apply_mem_toSubmodule := by
        intro a v hv
        have hvRQ : Additive.toMul v ∈ RQ := by
          simpa [η] using hv
        have hmem : a • Additive.toMul v ∈ RQ :=
          (hRQ_inv.invariant a (Additive.toMul v)).1 hvRQ
        simpa [η, ρ] using hmem }
  let rM : Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule := σ.asSubmodule
  let S : Subrepresentation ρ := Subrepresentation.ofSubmodule' m
  have hηQ_eq : η Q = S.toSubmodule := by
    rw [hQ_eq]
    simp [η, S]
  have hrM_le_m : rM ≤ m := by
    intro v hv
    have hvRQ : Additive.toMul v ∈ RQ := by
      change Additive.toMul v ∈ RQ at hv
      exact hv
    have hvQ : Additive.toMul v ∈ Q := hvRQ.2
    have hvηQ : v ∈ η Q := by
      change Additive.toMul v ∈ Q
      exact hvQ
    rw [hηQ_eq] at hvηQ
    change v ∈ m at hvηQ
    exact hvηQ
  have hAtom : IsAtom m :=
    (@isSimpleModule_iff_isAtom (MonoidAlgebra (ZMod p) A) _
      ρ.asModule instAddRho instModRho m).1 hm_simple
  rcases (hAtom.le_iff.mp hrM_le_m) with hrM_bot | hrM_eq_m
  · left
    change RQ = ⊥
    apply le_antisymm
    · intro x hx
      have hxv : Additive.ofMul x ∈ rM := by
        change x ∈ RQ
        exact hx
      have hxbot : Additive.ofMul x ∈ (⊥ : Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule) := by
        simpa [hrM_bot] using hxv
      have hxzero : Additive.ofMul x = 0 := by
        change Additive.ofMul x = 0 at hxbot
        exact hxbot
      have hxone : x = 1 := by
        have := congrArg Additive.toMul hxzero
        simpa using this
      simp [hxone]
    · exact bot_le
  · right
    change RQ = Q
    apply le_antisymm inf_le_right
    intro x hxQ
    have hxηQ : Additive.ofMul x ∈ η Q := by
      change x ∈ Q
      exact hxQ
    have hxm : Additive.ofMul x ∈ m := by
      rw [hηQ_eq] at hxηQ
      change Additive.ofMul x ∈ m at hxηQ
      exact hxηQ
    have hxrM : Additive.ofMul x ∈ rM := by
      simpa [hrM_eq_m] using hxm
    change x ∈ RQ at hxrM
    exact hxrM

private theorem subgroup_eq_complement_of_le_of_inf_eq_bot_sec9
    {V : Type u} [Group V] [IsMulCommutative V]
    (Q Qcompl L : Subgroup V)
    (hcompl : IsCompl Q Qcompl)
    (hQcompl_le_L : Qcompl ≤ L)
    (hL_inf_Q : L ⊓ Q = ⊥) :
    L = Qcompl := by
  classical
  haveI : Qcompl.Normal := Subgroup.normal_of_isMulCommutative Qcompl
  apply le_antisymm
  · intro x hxL
    have hx_top : x ∈ Q ⊔ Qcompl := by
      rw [hcompl.sup_eq_top]
      exact Subgroup.mem_top x
    rcases Subgroup.mem_sup_of_normal_right.1 hx_top with ⟨q, hqQ, c, hcQcompl, hqc⟩
    have hqL : q ∈ L := by
      have hcL : c ∈ L := hQcompl_le_L hcQcompl
      have hq_eq : q = x * c⁻¹ := by
        calc
          q = (q * c) * c⁻¹ := by simp
          _ = x * c⁻¹ := by rw [hqc]
      rw [hq_eq]
      exact L.mul_mem hxL (L.inv_mem hcL)
    have hq_bot : q ∈ (⊥ : Subgroup V) := by
      simpa [hL_inf_Q] using (show q ∈ L ⊓ Q from ⟨hqL, hqQ⟩)
    have hq_one : q = 1 := by simpa using hq_bot
    have hx_eq_c : x = c := by simpa [hq_one] using hqc.symm
    simpa [hx_eq_c] using hcQcompl
  · exact hQcompl_le_L

private theorem subgroup_eq_top_of_complement_le_sec9
    {V : Type u} [Group V]
    (Q Qcompl L : Subgroup V)
    (hcompl : IsCompl Q Qcompl)
    (hQ_le_L : Q ≤ L)
    (hQcompl_le_L : Qcompl ≤ L) :
    L = ⊤ := by
  apply top_unique
  rw [← hcompl.sup_eq_top]
  exact sup_le hQ_le_L hQcompl_le_L

set_option maxHeartbeats 800000 in
private theorem theorem_9_4_typeIIIIV_liftedH0_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ)
    [Fact (Nat.card W2).Prime]
    [Subgroup.Normalizes U MF]
    [Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF] :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hElem : IsElementaryAbelian (Nat.card W2)
        ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF))) →
      let UW1 : Subgroup G := U ⊔ W1
      let P : Subgroup MF := pCore (Nat.card W2) MF
      let V : Type u := P ⧸ frattini P
      letI : IsInvariant U MF P :=
        pCore_isInvariant_of_normalizes_sec9
          (A := U) (MF := MF) (p := Nat.card W2)
      letI : MulDistribMulAction U V :=
        quotientMulDistribMulAction (A := U) (G := P) (frattini P)
          (isInvariant_of_characteristic (A := U) (G := P) (frattini P))
      letI : IsInvariant UW1 MF P :=
        pCore_isInvariant_of_normalizes_sec9
          (A := UW1) (MF := MF) (p := Nat.card W2)
      letI : MulDistribMulAction UW1 V :=
        quotientMulDistribMulAction (A := UW1) (G := P) (frattini P)
          (isInvariant_of_characteristic (A := UW1) (G := P) (frattini P))
      letI : IsElementaryAbelian (Nat.card W2) V := by
        simpa [V, P] using hElem
      (Q Qcompl : Subgroup V) →
        IsInvariant UW1 V Q →
        IsInvariant UW1 V Qcompl →
        IsCompl Q Qcompl →
        let ρ : Representation (ZMod (Nat.card W2)) UW1 (Additive V) :=
          Theory.Representation.ofElementaryAbelianAction
            (A := UW1) (G := V) (p := Nat.card W2)
        letI instAdd : AddCommGroup ρ.asModule :=
          Representation.instAddCommGroupAsModule ρ
        letI instMod : Module (MonoidAlgebra (ZMod (Nat.card W2)) UW1) ρ.asModule :=
          Representation.instModuleMonoidAlgebraAsModule ρ
        (m : @Submodule (MonoidAlgebra (ZMod (Nat.card W2)) UW1)
          ρ.asModule _ instAdd.toAddCommMonoid instMod) →
          IsSimpleModule (MonoidAlgebra (ZMod (Nat.card W2)) UW1) m →
          Q = (Subgroup.toAddSubgroup.trans
              (AddSubgroup.toZModSubmodule (n := Nat.card W2))).symm
            (Subrepresentation.ofSubmodule' m).toSubmodule →
          letI : CommGroup V := IsMulCommutative.instCommGroup;
          letI : Qcompl.Normal := Subgroup.normal_of_isMulCommutative Qcompl;
          (hQcompl_inv_U : IsInvariant U V Qcompl) →
          (letI : IsInvariant U V Qcompl := hQcompl_inv_U;
            letI : MulDistribMulAction U (V ⧸ Qcompl) :=
              quotientMulDistribMulAction (A := U) (G := V) Qcompl hQcompl_inv_U;
            ¬ ActsTrivially (A := U) (G := V ⧸ Qcompl)) →
          let H0 := theorem_9_4_typeIIIIV_liftedH0_sec9 MF (Nat.card W2) Qcompl
          H0 ≤ MF ∧
            (H0.subgroupOf M).Normal ∧
            (H0.subgroupOf MF).Normal ∧
            H0 < MF ∧
            (∃ hnormal : (H0.subgroupOf MF).Normal,
              letI : (H0.subgroupOf MF).Normal := hnormal
              IsElementaryAbelian (Nat.card W2) (MF ⧸ H0.subgroupOf MF)) ∧
            IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) ∧
              ¬ quotientCentralizedBy MF H0 U := by
  classical
  intro h92 hElem
  dsimp only
  intro Q Qcompl _hQ_inv _hQcompl_inv _hQcompl m _hm_simple _hQ_eq
    _hQcompl_inv_U _hQcompl_nontriv_U
  haveI : IsElementaryAbelian (Nat.card W2)
      ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) := hElem
  haveI : Qcompl.Normal := by
    refine ⟨?_⟩
    intro n hn g
    simpa [mul_assoc, mul_left_comm, mul_comm] using hn
  have hH0_le_MF :
      theorem_9_4_typeIIIIV_liftedH0_sec9 MF (Nat.card W2) Qcompl ≤ MF :=
    theorem_9_4_typeIIIIV_liftedH0_le_MF_sec9 MF (Nat.card W2) Qcompl
  have hMFnil : Group.IsNilpotent MF := by
    have hMF := h92.mf
    rcases hMF.1 with ⟨_hMF_le_M, _hMF_normal_M, hMFnil, _hMFhall⟩
    exact hMFnil
  have hH0_normal_M :
      ((theorem_9_4_typeIIIIV_liftedH0_sec9 MF (Nat.card W2) Qcompl).subgroupOf M).Normal := by
    simpa using
      theorem_9_4_typeIIIIV_liftedH0_subgroupOf_M_normal_sec9
        M MF U W1 W2 q h92 Qcompl (by simpa using _hQcompl_inv)
  have hH0_normal_MF :
      ((theorem_9_4_typeIIIIV_liftedH0_sec9 MF (Nat.card W2) Qcompl).subgroupOf MF).Normal := by
    simpa using
      theorem_9_4_typeIIIIV_liftedH0_subgroupOf_MF_normal_sec9
        MF (Nat.card W2) hMFnil Qcompl
  have hH0_subgroupOf_MF_eq :
      (theorem_9_4_typeIIIIV_liftedH0_sec9 MF (Nat.card W2) Qcompl).subgroupOf MF =
        ((Qcompl.comap
            (QuotientGroup.mk' (frattini (pCore (Nat.card W2) MF)))).map
              (pCore (Nat.card W2) MF).subtype ⊔
            pPrimeCore (Nat.card W2) MF) :=
    theorem_9_4_typeIIIIV_liftedH0_subgroupOf_MF_eq_sec9 MF (Nat.card W2) Qcompl
  have hQcompl_preimage_map :
      (Qcompl.comap
          (QuotientGroup.mk' (frattini (pCore (Nat.card W2) MF)))).map
            (QuotientGroup.mk' (frattini (pCore (Nat.card W2) MF))) = Qcompl :=
    theorem_9_4_typeIIIIV_lifted_preimage_map_eq_sec9 MF (Nat.card W2) Qcompl
  have hfrattini_le_preimage :
      frattini (pCore (Nat.card W2) MF) ≤
        Qcompl.comap
          (QuotientGroup.mk' (frattini (pCore (Nat.card W2) MF))) :=
    theorem_9_4_typeIIIIV_frattini_le_lifted_preimage_sec9 MF (Nat.card W2) Qcompl
  let p : ℕ := Nat.card W2
  let P : Subgroup MF := pCore p MF
  let V : Type u := P ⧸ frattini P
  let C : Subgroup P := Qcompl.comap (QuotientGroup.mk' (frattini P))
  let H0 : Subgroup G := theorem_9_4_typeIIIIV_liftedH0_sec9 MF p Qcompl
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := by
    simpa [H0MF, H0, p] using hH0_normal_MF
  have hH0MF_eq :
      H0MF = C.map P.subtype ⊔ pPrimeCore p MF := by
    simpa [H0MF, H0, C, P, p] using hH0_subgroupOf_MF_eq
  have ePC_MF : (P ⧸ C) ≃* (MF ⧸ H0MF) := by
    simpa [P, C] using
      theorem_9_4_typeIIIIV_liftedH0_pCore_quotient_equiv_sec9
        (MF := MF) (p := p) hMFnil Qcompl (H := H0MF) hH0MF_eq
  have ePV : (P ⧸ C) ≃* (V ⧸ Qcompl) := by
    simpa [V, C] using
      quotient_comap_equiv_quotient_quotient_sec9
        (G := P) (N := frattini P) Qcompl
  have eMFV : (MF ⧸ H0MF) ≃* (V ⧸ Qcompl) := ePC_MF.symm.trans ePV
  haveI : IsElementaryAbelian p V := by
    simpa [V, P, p] using hElem
  have hVquot_elem : IsElementaryAbelian p (V ⧸ Qcompl) :=
    isElementaryAbelian_quotient_of_normal_sec9 Qcompl
  have hH0MF_elem : IsElementaryAbelian p (MF ⧸ H0MF) := by
    haveI : IsElementaryAbelian p (V ⧸ Qcompl) := hVquot_elem
    exact isElementaryAbelian_of_mulEquiv_sec9 eMFV
  letI : IsInvariant U MF P :=
    pCore_isInvariant_of_normalizes_sec9 (A := U) (MF := MF) (p := p)
  let hFr_inv_U : IsInvariant U P (frattini P) :=
    isInvariant_of_characteristic (A := U) (G := P) (frattini P)
  letI : MulAction.QuotientAction U (frattini P) :=
    quotientAction_of_isInvariant (A := U) (G := P) (frattini P) hFr_inv_U
  letI : MulDistribMulAction U V :=
    quotientMulDistribMulAction (A := U) (G := P) (frattini P) hFr_inv_U
  have hQcompl_inv_U' : IsInvariant U V Qcompl := by
    simpa [V, P, p] using _hQcompl_inv_U
  letI : IsInvariant U V Qcompl := hQcompl_inv_U'
  letI : MulAction.QuotientAction U Qcompl :=
    quotientAction_of_isInvariant (A := U) (G := V) Qcompl hQcompl_inv_U'
  letI : MulDistribMulAction U (V ⧸ Qcompl) :=
    quotientMulDistribMulAction (A := U) (G := V) Qcompl hQcompl_inv_U'
  have hVQ_nontriv : Nontrivial (V ⧸ Qcompl) :=
    nontrivial_of_not_actsTrivially_sec9 (by
      simpa [V, P, p] using _hQcompl_nontriv_U)
  have hMFQ_nontriv : Nontrivial (MF ⧸ H0MF) := by
    haveI : Nontrivial (V ⧸ Qcompl) := hVQ_nontriv
    exact nontrivial_of_mulEquiv_sec9 eMFV
  have hH0MF_ne_top : H0MF ≠ ⊤ := by
    haveI : Nontrivial (MF ⧸ H0MF) := hMFQ_nontriv
    exact QuotientGroup.nontrivial_iff.mp inferInstance
  have hH0_lt_MF' : H0 < MF := by
    have hH0_le_MF' : H0 ≤ MF := by
      simpa [H0, p] using hH0_le_MF
    refine lt_of_le_of_ne hH0_le_MF' ?_
    intro hH0_eq_MF
    apply hH0MF_ne_top
    ext x
    constructor
    · intro _hx
      exact Subgroup.mem_top x
    · intro _hx
      change (x : G) ∈ H0
      rw [hH0_eq_MF]
      exact x.property
  have hH0MF_subgroupOf_P_eq : H0MF.subgroupOf P = C := by
    simpa [H0MF, H0, P, C, p] using
      theorem_9_4_typeIIIIV_liftedH0_pCore_subgroupOf_eq_sec9
        (MF := MF) (p := p) Qcompl (H := H0MF) hH0MF_eq
  have hnot_cent : ¬ quotientCentralizedBy MF H0 U := by
    intro hcent
    apply (by simpa [V, P, p] using _hQcompl_nontriv_U)
    intro u x
    rcases QuotientGroup.mk'_surjective Qcompl x with ⟨v, rfl⟩
    rcases QuotientGroup.mk'_surjective (frattini P) v with ⟨p0, rfl⟩
    have hsmul_mk_Q :
        u • QuotientGroup.mk' Qcompl (QuotientGroup.mk' (frattini P) p0) =
          QuotientGroup.mk' Qcompl
            (u • QuotientGroup.mk' (frattini P) p0) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := Qcompl) u
          (QuotientGroup.mk' (frattini P) p0))
    rw [hsmul_mk_Q]
    apply (QuotientGroup.eq_iff_div_mem).2
    have hsmul_mk_P :
        u • QuotientGroup.mk' (frattini P) p0 =
          QuotientGroup.mk' (frattini P) (u • p0) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := frattini P) u p0)
    have hdiv_eq :
        (u • QuotientGroup.mk' (frattini P) p0) /
            QuotientGroup.mk' (frattini P) p0 =
          QuotientGroup.mk' (frattini P) ((u • p0) / p0) := by
      simp [div_eq_mul_inv]
    rw [hdiv_eq]
    have hcommH0 : ⁅(u : G), (((p0 : P) : MF) : G)⁆ ∈ H0 :=
      hcent (u : G) u.property (((p0 : P) : MF) : G) (((p0 : P) : MF).property)
    have hval :
        ((((u • p0 : P) / p0 : P) : MF) : G) =
          ⁅(u : G), (((p0 : P) : MF) : G)⁆ := by
      have hsmulP_G :
          (((u • p0 : P) : MF) : G) =
            (u : G) * (((p0 : P) : MF) : G) * (u : G)⁻¹ := by
        change ((u • ((p0 : P) : MF) : MF) : G) =
          (u : G) * (((p0 : P) : MF) : G) * (u : G)⁻¹
        simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      simp [hsmulP_G, commutatorElement_def, div_eq_mul_inv, mul_assoc]
    have hmemH0MF : (((u • p0 : P) / p0 : P) : MF) ∈ H0MF := by
      change ((((u • p0 : P) / p0 : P) : MF) : G) ∈ H0
      rw [hval]
      exact hcommH0
    have hmemC : ((u • p0 : P) / p0 : P) ∈ C := by
      have hsub : ((u • p0 : P) / p0 : P) ∈ H0MF.subgroupOf P := by
        simpa [Subgroup.mem_subgroupOf] using hmemH0MF
      simpa [hH0MF_subgroupOf_P_eq] using hsub
    exact hmemC
  refine ⟨hH0_le_MF, hH0_normal_M, hH0_normal_MF, ?_, ?_, ?_, ?_⟩
  · simpa [H0, p] using hH0_lt_MF'
  · exact ⟨hH0_normal_MF, by simpa [H0MF, H0, p] using hH0MF_elem⟩
  · have hMF_le_M : MF ≤ M := by
      exact h92.mf.1.1
    have hMF_normal_M : (MF.subgroupOf M).Normal := by
      exact h92.mf.1.2.1
    have hUW1_le_M : (U ⊔ W1 : Subgroup G) ≤ M := by
      have hPsource := h92.typePDefinitionData
      rcases hPsource with
        ⟨_hMFsource, _hW1cyc, _hW1ne, ⟨hW1_le_M, _hW1hall⟩,
          _hcompMW1, hUleD, _hUnil, _hW1normU, _hcompDU, _hMFnotcyc,
          _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
          _hcentW1, _hnormX⟩
      have hU_le_M : U ≤ M :=
        hUleD.trans (section12_ambientDerivedSubgroup_le (G := G) (E := M))
      exact sup_le hU_le_M hW1_le_M
    refine
      { normal_K := by simpa [H0, p] using hH0_normal_M
        normal_H := hMF_normal_M
        lt := ?_
        is_maximal := ?_ }
    · refine lt_iff_le_not_ge.2 ⟨?_, ?_⟩
      · intro x hx
        change (x : G) ∈ MF
        exact hH0_lt_MF'.1 (by
          simpa [H0, p, Subgroup.mem_subgroupOf] using hx)
      · intro hle
        have hMF_le_H0 : MF ≤ H0 := by
          intro x hxMF
          let xM : M := ⟨x, hMF_le_M hxMF⟩
          have hxMFsub : xM ∈ MF.subgroupOf M := by
            simpa [xM, Subgroup.mem_subgroupOf] using hxMF
          have hxH0sub : xM ∈ H0.subgroupOf M := hle hxMFsub
          simpa [xM, Subgroup.mem_subgroupOf] using hxH0sub
        exact (not_le_of_gt hH0_lt_MF') hMF_le_H0
    · intro N hN_normal hH0M_le_N hN_le_MFM
      let K : Subgroup MF := pPrimeCore p MF
      haveI : K.Normal := by
        simpa [K] using (pPrimeCore_normal (G := MF) (p := p))
      have hPK_top : P ⊔ K = (⊤ : Subgroup MF) := by
        exact top_unique (by
          simpa [P, K] using
            nilpotent_top_le_pCore_sup_pPrimeCore_sec9 (Q := MF) (p := p) hMFnil)
      let NMF : Subgroup MF := N.comap (Subgroup.inclusion hMF_le_M)
      let NP : Subgroup P := NMF.subgroupOf P
      let L : Subgroup V := NP.map (QuotientGroup.mk' (frattini P))
      have hH0MF_le_NMF : H0MF ≤ NMF := by
        intro x hx
        change (⟨((x : MF) : G), hMF_le_M x.property⟩ : M) ∈ N
        have hxH0M : (⟨((x : MF) : G), hMF_le_M x.property⟩ : M) ∈
            H0.subgroupOf M := by
          simpa [H0MF, Subgroup.mem_subgroupOf] using hx
        exact hH0M_le_N hxH0M
      have hK_le_NMF : K ≤ NMF := by
        refine (show K ≤ H0MF from ?_).trans hH0MF_le_NMF
        rw [hH0MF_eq]
        exact le_sup_right
      have hC_le_NP : C ≤ NP := by
        intro x hxC
        change ((x : P) : MF) ∈ NMF
        apply hH0MF_le_NMF
        have hxH0P : x ∈ H0MF.subgroupOf P := by
          simpa [hH0MF_subgroupOf_P_eq] using hxC
        simpa [Subgroup.mem_subgroupOf] using hxH0P
      have hfrattini_le_C : frattini P ≤ C := by
        intro x hx
        change QuotientGroup.mk' (frattini P) x ∈ Qcompl
        have hx_one : QuotientGroup.mk' (frattini P) x = 1 :=
          (QuotientGroup.eq_one_iff (N := frattini P) (x := x)).2 hx
        simp [hx_one]
      have hfrattini_le_NP : frattini P ≤ NP := hfrattini_le_C.trans hC_le_NP
      have hC_map_eq_Qcompl :
          C.map (QuotientGroup.mk' (frattini P)) = Qcompl := by
        simpa [C] using
          (Subgroup.map_comap_eq_self_of_surjective
            (f := QuotientGroup.mk' (frattini P))
            (QuotientGroup.mk'_surjective (frattini P)) Qcompl)
      have hQcompl_le_L : Qcompl ≤ L := by
        intro x hx
        have hxCmap : x ∈ C.map (QuotientGroup.mk' (frattini P)) := by
          simpa [hC_map_eq_Qcompl] using hx
        rcases Subgroup.mem_map.mp hxCmap with ⟨c, hcC, hc_eq⟩
        exact Subgroup.mem_map.mpr ⟨c, hC_le_NP hcC, hc_eq⟩
      let UW1 : Subgroup G := U ⊔ W1
      letI : IsInvariant UW1 MF P :=
        pCore_isInvariant_of_normalizes_sec9 (A := UW1) (MF := MF) (p := p)
      let hFr_inv_UW1 : IsInvariant UW1 P (frattini P) :=
        isInvariant_of_characteristic (A := UW1) (G := P) (frattini P)
      letI : MulAction.QuotientAction UW1 (frattini P) :=
        quotientAction_of_isInvariant (A := UW1) (G := P) (frattini P) hFr_inv_UW1
      letI : MulDistribMulAction UW1 V :=
        quotientMulDistribMulAction (A := UW1) (G := P) (frattini P) hFr_inv_UW1
      have hNP_forward : ∀ (a : UW1) (x : P), x ∈ NP → a • x ∈ NP := by
        intro a x hx
        change ((a • x : P) : MF) ∈ NMF
        have hxN : (⟨(((x : P) : MF) : G), hMF_le_M ((x : P) : MF).property⟩ :
            M) ∈ N := by
          simpa [NP, NMF, Subgroup.mem_subgroupOf, Subgroup.mem_comap,
            Subgroup.inclusion] using hx
        have haUW1 : (a : G) ∈ U ⊔ W1 := by
          change (a : G) ∈ UW1
          exact a.property
        let aM : M := ⟨(a : G), hUW1_le_M haUW1⟩
        let xM : M := ⟨(((x : P) : MF) : G), hMF_le_M ((x : P) : MF).property⟩
        have hconjN : aM * xM * aM⁻¹ ∈ N :=
          hN_normal.conj_mem xM (by simpa [xM] using hxN) aM
        have hsmulG :
            (((a • x : P) : MF) : G) =
              (a : G) * (((x : P) : MF) : G) * (a : G)⁻¹ := by
          change ((a • ((x : P) : MF) : MF) : G) =
            (a : G) * (((x : P) : MF) : G) * (a : G)⁻¹
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        change
          (⟨(((a • x : P) : MF) : G),
            hMF_le_M ((a • x : P) : MF).property⟩ : M) ∈ N
        have heq :
            (⟨(((a • x : P) : MF) : G),
              hMF_le_M ((a • x : P) : MF).property⟩ : M) =
              aM * xM * aM⁻¹ := by
          apply Subtype.ext
          exact hsmulG
        rw [heq]
        exact hconjN
      have hL_forward : ∀ (a : UW1) {x : V}, x ∈ L → a • x ∈ L := by
        intro a x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hyNP, rfl⟩
        refine Subgroup.mem_map.mpr ⟨a • y, hNP_forward a y hyNP, ?_⟩
        exact (MulAction.Quotient.smul_mk (H := frattini P) a y).symm
      have hL_inv : IsInvariant UW1 V L := by
        constructor
        intro a x
        constructor
        · exact hL_forward a
        · intro hx
          have hx' : (a⁻¹ : UW1) • (a • x) ∈ L := hL_forward a⁻¹ hx
          simpa using hx'
      have hQ_inv' : IsInvariant UW1 V Q := by
        simpa [UW1, V, P, p] using _hQ_inv
      have hQ_eq' :
          Q = (Subgroup.toAddSubgroup.trans
              (AddSubgroup.toZModSubmodule (n := p))).symm
            (Subrepresentation.ofSubmodule' m).toSubmodule := by
        simpa [UW1, V, P, p] using _hQ_eq
      haveI : CommGroup V := IsMulCommutative.instCommGroup
      have hL_cases : L ⊓ Q = ⊥ ∨ L ⊓ Q = Q := by
        simpa [UW1, V, P, p] using
          inf_simple_factor_eq_bot_or_eq_self_sec9
            (A := UW1) (V := V) (p := p) Q L hQ_inv' hL_inv
            m _hm_simple hQ_eq'
      rcases hL_cases with hLinf_bot | hLinf_eq
      · have hL_eq_Qcompl : L = Qcompl :=
          subgroup_eq_complement_of_le_of_inf_eq_bot_sec9
            Q Qcompl L _hQcompl hQcompl_le_L hLinf_bot
        left
        apply le_antisymm
        · intro x hxN
          have hxMF : (x : G) ∈ MF := by
            simpa [Subgroup.mem_subgroupOf] using hN_le_MFM hxN
          let xMF : MF := ⟨(x : G), hxMF⟩
          have hxNMF : xMF ∈ NMF := by
            simpa [NMF, Subgroup.mem_comap, Subgroup.inclusion, xMF] using hxN
          have hxPK : xMF ∈ P ⊔ K := by
            rw [hPK_top]
            exact Subgroup.mem_top xMF
          rcases Subgroup.mem_sup_of_normal_right.1 hxPK with ⟨p0, hp0P, k0, hk0K, hpk⟩
          let p0P : P := ⟨p0, hp0P⟩
          have hk0NMF : k0 ∈ NMF := hK_le_NMF hk0K
          have hp0NP : p0P ∈ NP := by
            change p0 ∈ NMF
            have hp0_eq : p0 = xMF * k0⁻¹ := by
              calc
                p0 = (p0 * k0) * k0⁻¹ := by simp
                _ = xMF * k0⁻¹ := by rw [hpk]
            rw [hp0_eq]
            exact NMF.mul_mem hxNMF (NMF.inv_mem hk0NMF)
          have hp0L : QuotientGroup.mk' (frattini P) p0P ∈ L :=
            Subgroup.mem_map.mpr ⟨p0P, hp0NP, rfl⟩
          have hp0Qcompl : QuotientGroup.mk' (frattini P) p0P ∈ Qcompl := by
            simpa [hL_eq_Qcompl] using hp0L
          have hp0C : p0P ∈ C := by
            simpa [C, Subgroup.mem_comap] using hp0Qcompl
          have hp0Cmap : p0 ∈ C.map P.subtype :=
            ⟨p0P, hp0C, rfl⟩
          have hxH0MF : xMF ∈ H0MF := by
            rw [hH0MF_eq]
            exact Subgroup.mem_sup_of_normal_right.2 ⟨p0, hp0Cmap, k0, hk0K, hpk⟩
          simpa [xMF, H0MF, Subgroup.mem_subgroupOf] using hxH0MF
        · exact hH0M_le_N
      · have hQ_le_L : Q ≤ L := by
          intro x hxQ
          have hxInf : x ∈ L ⊓ Q := by
            rw [hLinf_eq]
            exact hxQ
          exact hxInf.1
        have hL_eq_top : L = ⊤ :=
          subgroup_eq_top_of_complement_le_sec9 Q Qcompl L _hQcompl hQ_le_L hQcompl_le_L
        right
        apply le_antisymm hN_le_MFM
        intro x hxMFsub
        have hxMF : (x : G) ∈ MF := by
          simpa [Subgroup.mem_subgroupOf] using hxMFsub
        let xMF : MF := ⟨(x : G), hxMF⟩
        have hxPK : xMF ∈ P ⊔ K := by
          rw [hPK_top]
          exact Subgroup.mem_top xMF
        rcases Subgroup.mem_sup_of_normal_right.1 hxPK with ⟨p0, hp0P, k0, hk0K, hpk⟩
        let p0P : P := ⟨p0, hp0P⟩
        have hp0L : QuotientGroup.mk' (frattini P) p0P ∈ L := by
          rw [hL_eq_top]
          exact Subgroup.mem_top _
        rcases Subgroup.mem_map.mp hp0L with ⟨yP, hyNP, hy_eq⟩
        have hy_div_fr : yP / p0P ∈ frattini P :=
          (QuotientGroup.eq_iff_div_mem (N := frattini P)).mp hy_eq
        have hy_div_NP : yP / p0P ∈ NP := hfrattini_le_NP hy_div_fr
        have hp0NP : p0P ∈ NP := by
          have hp0_eq : p0P = (yP / p0P)⁻¹ * yP := by
            simp [div_eq_mul_inv, mul_assoc]
          rw [hp0_eq]
          exact NP.mul_mem (NP.inv_mem hy_div_NP) hyNP
        have hp0NMF : p0 ∈ NMF := by
          simpa [NP, p0P, Subgroup.mem_subgroupOf] using hp0NP
        have hk0NMF : k0 ∈ NMF := hK_le_NMF hk0K
        have hxNMF : xMF ∈ NMF := by
          rw [← hpk]
          exact NMF.mul_mem hp0NMF hk0NMF
        simpa [NMF, Subgroup.mem_comap, Subgroup.inclusion, xMF] using hxNMF
  · simpa [H0, p] using hnot_cent

set_option maxHeartbeats 800000 in
private theorem theorem_9_4_typeIIIIV_maschke_frattini_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ)
    [Fact (Nat.card W2).Prime]
    [Subgroup.Normalizes U MF]
    [Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF] :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (section16TypeIII M MF ∨ section16TypeIV M MF) →
        IsInvariant (U ⊔ W1 : Subgroup G) MF (pCore (Nat.card W2) MF) →
          letI : IsInvariant U MF (pCore (Nat.card W2) MF) :=
            pCore_isInvariant_of_normalizes_sec9
              (A := U) (MF := MF) (p := Nat.card W2)
          letI : MulDistribMulAction U
              ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
            quotientMulDistribMulAction (A := U) (G := pCore (Nat.card W2) MF)
              (frattini (pCore (Nat.card W2) MF))
              (isInvariant_of_characteristic (A := U) (G := pCore (Nat.card W2) MF)
                (frattini (pCore (Nat.card W2) MF)))
          ¬ ActsTrivially (A := U)
              (G := (pCore (Nat.card W2) MF) ⧸
                frattini (pCore (Nat.card W2) MF)) →
            letI : IsInvariant (U ⊔ W1 : Subgroup G) MF
                (pCore (Nat.card W2) MF) :=
              pCore_isInvariant_of_normalizes_sec9
                (A := (U ⊔ W1 : Subgroup G)) (MF := MF) (p := Nat.card W2)
            letI : MulDistribMulAction (U ⊔ W1 : Subgroup G)
                ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
              quotientMulDistribMulAction
                (A := (U ⊔ W1 : Subgroup G)) (G := pCore (Nat.card W2) MF)
                (frattini (pCore (Nat.card W2) MF))
                (isInvariant_of_characteristic
                  (A := (U ⊔ W1 : Subgroup G)) (G := pCore (Nat.card W2) MF)
                  (frattini (pCore (Nat.card W2) MF)))
            ¬ ActsTrivially (A := (U ⊔ W1 : Subgroup G))
                (G := (pCore (Nat.card W2) MF) ⧸
                  frattini (pCore (Nat.card W2) MF)) →
            IsElementaryAbelian (Nat.card W2)
              ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) →
              ∃ H0 : Subgroup G,
                H0 ≤ MF ∧
                  (H0.subgroupOf M).Normal ∧
                  (H0.subgroupOf MF).Normal ∧
                  H0 < MF ∧
                  (∃ hnormal : (H0.subgroupOf MF).Normal,
                    letI : (H0.subgroupOf MF).Normal := hnormal
                    IsElementaryAbelian (Nat.card W2) (MF ⧸ H0.subgroupOf MF)) ∧
                IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) ∧
                  ¬ quotientCentralizedBy MF H0 U := by
  classical
  intro h92 _hIIIIV _hPinv hU _hUW1 hElem
  let UW1 : Subgroup G := U ⊔ W1
  let P : Subgroup MF := pCore (Nat.card W2) MF
  let V : Type u := P ⧸ frattini P
  letI : IsInvariant U MF P :=
    pCore_isInvariant_of_normalizes_sec9
      (A := U) (MF := MF) (p := Nat.card W2)
  letI : MulDistribMulAction U V :=
    quotientMulDistribMulAction (A := U) (G := P) (frattini P)
      (isInvariant_of_characteristic (A := U) (G := P) (frattini P))
  letI : IsInvariant UW1 MF P :=
    pCore_isInvariant_of_normalizes_sec9
      (A := UW1) (MF := MF) (p := Nat.card W2)
  letI : MulDistribMulAction UW1 V :=
    quotientMulDistribMulAction (A := UW1) (G := P) (frattini P)
      (isInvariant_of_characteristic (A := UW1) (G := P) (frattini P))
  letI : IsElementaryAbelian (Nat.card W2) V := by
    simpa [V, P] using hElem
  obtain ⟨m, hm_simple, hm_nontriv⟩ := by
    simpa [UW1, V, P] using
      theorem_9_4_typeIIIIV_frattini_simple_factor_sec9
        M MF U W1 W2 q h92 hU hElem
  let ρ : Representation (ZMod (Nat.card W2)) UW1 (Additive V) :=
    Theory.Representation.ofElementaryAbelianAction
      (A := UW1) (G := V) (p := Nat.card W2)
  obtain ⟨Q, hQ_inv, hQ_eq, hQ_nontriv⟩ :=
    invariant_subgroup_of_submodule_nontrivial_sec9
      (A := UW1) (V := V) (p := Nat.card W2)
      (H := U.subgroupOf UW1) ρ rfl m hm_nontriv
  obtain ⟨Qcompl, hQcompl, hQcompl_inv⟩ := by
    simpa [UW1, V, P] using
      theorem_9_4_typeIIIIV_frattini_quotient_complement_sec9
        M MF U W1 W2 q h92 Q hQ_inv
  letI : CommGroup V := IsMulCommutative.instCommGroup
  haveI : Qcompl.Normal := Subgroup.normal_of_isMulCommutative Qcompl
  have hQcompl_inv_Usub : IsInvariant (U.subgroupOf UW1) V Qcompl :=
    { invariant := fun h v => hQcompl_inv.invariant (h : UW1) v }
  have hQcompl_nontriv :
      letI : IsInvariant (U.subgroupOf UW1) V Qcompl := hQcompl_inv_Usub
      letI : MulDistribMulAction (U.subgroupOf UW1) (V ⧸ Qcompl) :=
        quotientMulDistribMulAction (A := U.subgroupOf UW1) (G := V)
          Qcompl hQcompl_inv_Usub
      ¬ ActsTrivially (A := U.subgroupOf UW1) (G := V ⧸ Qcompl) := by
    simpa using
      not_actsTrivially_quotient_of_isCompl_nontrivial_subgroup_sec9
        (A := UW1) (V := V) (H := U.subgroupOf UW1)
        (Q := Q) (C := Qcompl) hQ_inv hQcompl_inv hQcompl hQ_nontriv
  have hQcompl_inv_U : IsInvariant U V Qcompl :=
    { invariant := fun u v =>
        hQcompl_inv.invariant
          (⟨(u : G), (show U ≤ UW1 from le_sup_left) u.property⟩ : UW1) v }
  have hQcompl_nontriv_U :
      letI : IsInvariant U V Qcompl := hQcompl_inv_U
      letI : MulDistribMulAction U (V ⧸ Qcompl) :=
        quotientMulDistribMulAction (A := U) (G := V) Qcompl hQcompl_inv_U
      ¬ ActsTrivially (A := U) (G := V ⧸ Qcompl) := by
    letI : IsInvariant U V Qcompl := hQcompl_inv_U
    letI : MulDistribMulAction U (V ⧸ Qcompl) :=
      quotientMulDistribMulAction (A := U) (G := V) Qcompl hQcompl_inv_U
    letI : IsInvariant (U.subgroupOf UW1) V Qcompl := hQcompl_inv_Usub
    letI : MulDistribMulAction (U.subgroupOf UW1) (V ⧸ Qcompl) :=
      quotientMulDistribMulAction (A := U.subgroupOf UW1) (G := V)
        Qcompl hQcompl_inv_Usub
    intro htriv
    apply hQcompl_nontriv
    intro h x
    let u : U := ⟨((h : U.subgroupOf UW1) : UW1), h.property⟩
    have hfix := htriv u x
    change h • x = x at hfix
    exact hfix
  -- Source step still open: lift the complementary kernel `Qcompl` through
  -- the inverse-image/product construction with `O_{p'}(MF)` to build `H0`,
  -- then identify `MF/H0` with the selected noncentral factor quotient above.
  let H0 := theorem_9_4_typeIIIIV_liftedH0_sec9 MF (Nat.card W2) Qcompl
  refine ⟨H0, ?_⟩
  simpa [H0, UW1, V, P] using
    theorem_9_4_typeIIIIV_liftedH0_source_sec9
      (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) (q := q)
      h92 hElem Q Qcompl hQ_inv hQcompl_inv hQcompl m hm_simple
      (by simpa [UW1, V, P] using hQ_eq) hQcompl_inv_U
      (by simpa [UW1, V, P] using hQcompl_nontriv_U)


private theorem index_dvd_card_of_sup_eq_top_normal_sec9
    {Q : Type u} [Group Q] [Finite Q]
    {K U : Subgroup Q} [K.Normal]
    (hKU : K ⊔ U = ⊤) :
    U.index ∣ Nat.card K := by
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
  simpa [hidx_eq] using hrel_dvd_cardK

private theorem theorem_9_4_typeIIIIV_not_actsTrivially_pCore_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ)
    [Fact (Nat.card W2).Prime]
    [Subgroup.Normalizes U MF] :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (section16TypeIII M MF ∨ section16TypeIV M MF) →
        letI : IsInvariant U MF (pCore (Nat.card W2) MF) :=
          pCore_isInvariant_of_normalizes_sec9
            (A := U) (MF := MF) (p := Nat.card W2)
        ¬ ActsTrivially (A := U) (G := pCore (Nat.card W2) MF) := by
  classical
  intro h92 hIIIIV
  let p := Nat.card W2
  let P : Subgroup MF := pCore p MF
  letI : IsInvariant U MF P := by
    simpa [P, p] using
      pCore_isInvariant_of_normalizes_sec9 (A := U) (MF := MF) (p := p)
  intro htrivP
  let K : Subgroup MF := pPrimeCore p MF
  let C : Subgroup MF := fixedPointSubgroup U MF
  have hMFnil : Group.IsNilpotent MF := by
    exact h92.mf.1.2.2.1
  have hP_le_C : P ≤ C := by
    intro x hx
    change ∀ a : U, a • x = x
    intro a
    have hfix : a • (⟨x, hx⟩ : P) = (⟨x, hx⟩ : P) := htrivP a ⟨x, hx⟩
    exact congrArg Subtype.val hfix
  have htop_le_PK : (⊤ : Subgroup MF) ≤ P ⊔ K := by
    simpa [P, K, p] using
      nilpotent_top_le_pCore_sup_pPrimeCore_sec9 (Q := MF) (p := p) hMFnil
  have htop_le_CK : (⊤ : Subgroup MF) ≤ C ⊔ K :=
    htop_le_PK.trans (sup_le_sup_right hP_le_C K)
  have hCK_top : K ⊔ C = (⊤ : Subgroup MF) := by
    rw [sup_comm]
    exact top_unique htop_le_CK
  have hidx_dvd_K : C.index ∣ Nat.card K := by
    simpa [C, K] using
      index_dvd_card_of_sup_eq_top_normal_sec9 (Q := MF) (K := K) (U := C) hCK_top
  have hcop_K : Nat.Coprime p (Nat.card K) := by
    simpa [K, p] using pPrimeCore_coprime_card (G := MF) (p := p)
  have hcop_idx : Nat.Coprime p C.index :=
    Nat.Coprime.of_dvd_right hidx_dvd_K hcop_K
  have hcent_le_MF : subgroupCentralizerIn MF U ≤ MF := by
    intro x hx
    have hx' : x ∈ MF ∧ x ∈ Subgroup.centralizer (U : Set G) := by
      simpa [subgroupCentralizerIn] using hx
    exact hx'.1
  have hfixed_eq :
      fixedPointSubgroup U MF = (subgroupCentralizerIn MF U).subgroupOf MF := by
    exact fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn MF U
      (Subgroup.Normalizes.le_normalizer (A := U) (K := MF))
  have hcard_C :
      Nat.card C = Nat.card (subgroupCentralizerIn MF U) := by
    simp [C, hfixed_eq,
      natCard_subgroupOf_eq (subgroupCentralizerIn MF U) MF hcent_le_MF]
  rcases theorem_9_4_typeIIIIV_pf93_facts_sec9 M MF U W1 W2 q h92 hIIIIV with
    ⟨hW2prime, _hUW1centralizer, p0, hp0, hcardMF⟩
  have hcardMF' :
      Nat.card MF = p ^ q * Nat.card (subgroupCentralizerIn MF U) := by
    simpa [p, hp0] using hcardMF
  have hidx_eq_pow : C.index = p ^ q := by
    have hmul :
        C.index * Nat.card C = p ^ q * Nat.card C := by
      calc
        C.index * Nat.card C = Nat.card MF := Subgroup.index_mul_card (H := C)
        _ = p ^ q * Nat.card (subgroupCentralizerIn MF U) := hcardMF'
        _ = p ^ q * Nat.card C := by rw [hcard_C]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  have hqprime : Nat.Prime q := q_prime_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hqpos : 0 < q := hqprime.pos
  have hp_dvd_idx : p ∣ C.index := by
    rw [hidx_eq_pow]
    exact dvd_pow_self p hqpos.ne'
  have hp_not_dvd_idx : ¬ p ∣ C.index :=
    (hW2prime.coprime_iff_not_dvd).mp (by simpa [p] using hcop_idx)
  exact hp_not_dvd_idx hp_dvd_idx

private theorem theorem_9_4_typeIIIIV_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (section16TypeIII M MF ∨ section16TypeIV M MF) →
        ∃ H0 : Subgroup G, ∃ p : Nat.Primes, hoReductionData M MF U W2 H0 p := by
  intro h92 hIIIIV
  rcases theorem_9_4_typeIIIIV_pf93_facts_sec9 M MF U W1 W2 q h92 hIIIIV with
    ⟨hW2prime, _hUW1centralizer, _hMFcard⟩
  let _p : Nat.Primes := ⟨Nat.card W2, hW2prime⟩
  haveI : Fact (Nat.card W2).Prime := ⟨hW2prime⟩
  have hUW1_norm_MF : U ⊔ W1 ≤ Subgroup.normalizer (MF : Set G) :=
    (theorem_9_3_action_normalizes_and_solvable_sec9 M MF U W1 W2 q h92).1
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_left.trans hUW1_norm_MF
  haveI : Subgroup.Normalizes U MF := ⟨hU_norm_MF⟩
  haveI : Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF := ⟨hUW1_norm_MF⟩
  have hUW1_pCore_inv :
      IsInvariant (U ⊔ W1 : Subgroup G) MF (pCore (Nat.card W2) MF) := by
    exact pCore_isInvariant_of_normalizes_sec9
      (A := (U ⊔ W1 : Subgroup G)) (MF := MF) (p := Nat.card W2)
  have hU_pCore_inv :
      IsInvariant U MF (pCore (Nat.card W2) MF) :=
    pCore_isInvariant_of_normalizes_sec9 (A := U) (MF := MF) (p := Nat.card W2)
  have hU_not_trivial_pCore :
      letI : IsInvariant U MF (pCore (Nat.card W2) MF) := hU_pCore_inv
      ¬ ActsTrivially (A := U) (G := pCore (Nat.card W2) MF) :=
    theorem_9_4_typeIIIIV_not_actsTrivially_pCore_sec9
      M MF U W1 W2 q h92 hIIIIV
  have _hU_not_trivial_frattini :
      letI : IsInvariant U MF (pCore (Nat.card W2) MF) := hU_pCore_inv
      letI : MulDistribMulAction U
          ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
        quotientMulDistribMulAction (A := U) (G := pCore (Nat.card W2) MF)
          (frattini (pCore (Nat.card W2) MF))
          (isInvariant_of_characteristic (A := U) (G := pCore (Nat.card W2) MF)
            (frattini (pCore (Nat.card W2) MF)))
      ¬ ActsTrivially (A := U)
          (G := (pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
    theorem_9_4_typeIIIIV_pCore_frattini_nontrivial_sec9
      M MF U W1 W2 q h92 hU_not_trivial_pCore
  have _hP_frattini_elem :
      IsElementaryAbelian (Nat.card W2)
        ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
    elementaryAbelian_pCore_quotient_frattini (G := MF) (p := Nat.card W2)
  have _hUW1_not_trivial_frattini :
      letI : IsInvariant (U ⊔ W1 : Subgroup G) MF
          (pCore (Nat.card W2) MF) := hUW1_pCore_inv
      letI : MulDistribMulAction (U ⊔ W1 : Subgroup G)
          ((pCore (Nat.card W2) MF) ⧸ frattini (pCore (Nat.card W2) MF)) :=
        quotientMulDistribMulAction
          (A := (U ⊔ W1 : Subgroup G)) (G := pCore (Nat.card W2) MF)
          (frattini (pCore (Nat.card W2) MF))
          (isInvariant_of_characteristic
            (A := (U ⊔ W1 : Subgroup G)) (G := pCore (Nat.card W2) MF)
            (frattini (pCore (Nat.card W2) MF)))
      ¬ ActsTrivially (A := (U ⊔ W1 : Subgroup G))
          (G := (pCore (Nat.card W2) MF) ⧸
            frattini (pCore (Nat.card W2) MF)) :=
    theorem_9_4_typeIIIIV_UW1_frattini_nontrivial_sec9
      MF U W1 W2 _hU_not_trivial_frattini
  rcases theorem_9_4_typeIIIIV_maschke_frattini_source_sec9
      M MF U W1 W2 q h92 hIIIIV hUW1_pCore_inv
      _hU_not_trivial_frattini _hUW1_not_trivial_frattini _hP_frattini_elem with
    ⟨H0, hH0_le_MF, hH0_normal_M, hH0_normal_MF, hH0_lt_MF,
      hquot_elem, hchief, hnot_cent⟩
  have hMF_le_M : MF ≤ M := by
    exact h92.mf.1.1
  refine ⟨H0, ⟨Nat.card W2, hW2prime⟩, ?_⟩
  refine
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, hH0_normal_MF, hH0_lt_MF,
      ?_, ?_⟩
  · simpa using hquot_elem
  · intro _hIIIIV'
    exact ⟨rfl, hchief, hnot_cent⟩

public theorem theorem_9_4_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      ∃ H0 : Subgroup G, ∃ p : Nat.Primes, hoReductionData M MF U W2 H0 p := by
  intro h92
  by_cases hII : section16TypeII M MF
  · exact theorem_9_4_typeII_core_sec9 M MF U W1 W2 q h92 hII
  · have hIIIIV : section16TypeIII M MF ∨ section16TypeIV M MF := by
      rcases h92.typeCases with hII' | hIII | hIV
      · exact False.elim (hII hII')
      · exact Or.inl hIII
      · exact Or.inr hIV
    exact theorem_9_4_typeIIIIV_source_core_sec9 M MF U W1 W2 q h92 hIIIIV

public theorem theorem_9_4
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      ∃ H0 : Subgroup G, ∃ p : Nat.Primes, hoReductionData M MF U W2 H0 p := by
  exact theorem_9_4_source_core_sec9 M MF U W1 W2 q

end CFSG.Section9
