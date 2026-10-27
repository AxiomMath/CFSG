module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.lemma_6_5_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.MinCE
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SolvableDimension
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.IsSubnormal
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Order.Preorder.Finite
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.lemma_7_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.theorem_7_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.theorem_7_3

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-!
# Statements from BG Section 7

This file records the statement scaffold for the results in `docs/section7.tex`.
-/

section

variable {G : Type*} [Group G] [Finite G]

lemma CFSG.IsSubnormalIn.le
    {G : Type*} [Group G] {A P : Subgroup G} (hAP : IsSubnormalIn A P) : A ≤ P := by
  rcases hAP with ⟨n, chain, h0, hlast, hstep, _⟩
  subst h0 hlast
  have hmono : ∀ i : Fin (n + 1), chain 0 ≤ chain i := by
    intro i
    induction i using Fin.induction with
    | zero =>
        exact le_rfl
    | succ i ih =>
        exact ih.trans (hstep i)
  simpa using hmono (Fin.last n)

private theorem CFSG.theorem_7_4_part_a
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {A P : Subgroup G} (hA : Hypothesis7_1 A) (hAsubnormal : IsSubnormalIn A P) :
    subgroupCentralizerIn (section7K A) P =
      piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) := by
  let π : Set Nat.Primes := subgroupPrimeSet A
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let CA : Subgroup G := Subgroup.centralizer (A : Set G)
  have hA_le_P : A ≤ P := hAsubnormal.le
  have hC_le_CA : C ≤ CA := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp hx a (hA_le_P ha)
  have hK_pi : IsPiSubgroup (G := G) πᶜ (section7K A) := by
    simpa [π, section7K, CA] using piCoreIn_isPiSubgroup (G := G) πᶜ CA
  apply le_antisymm
  · intro x hx
    have hK_le_CA : section7K A ≤ CA := by
      simpa [CA] using section7K_le_centralizer (G := G) A
    have hCA_normK : CA ≤ Subgroup.normalizer (section7K A : Set G) := by
      have hKsub_eq : (section7K A).subgroupOf CA = piCore πᶜ ↥CA := by
        simpa [π, section7K, CA] using piCore_map_subtype_subgroupOf (G := G) πᶜ CA
      have hKsub_norm : ((section7K A).subgroupOf CA).Normal := by
        rw [hKsub_eq]
        infer_instance
      exact Subgroup.le_normalizer_of_normal_subgroupOf hK_le_CA
    have hC_normK : C ≤ Subgroup.normalizer (section7K A : Set G) :=
      hC_le_CA.trans hCA_normK
    let S : Subgroup G := subgroupCentralizerIn (section7K A) P
    have hS_pi : IsPiSubgroup (G := G) πᶜ S := by
      exact IsPiSubgroup.of_le inf_le_left hK_pi
    have hSsub_eq : S.subgroupOf C = (section7K A).subgroupOf C := by
      ext y
      simp [S, subgroupCentralizerIn, C]
    have hSsub_norm : (S.subgroupOf C).Normal := by
      rw [hSsub_eq]
      exact Subgroup.normal_subgroupOf_of_le_normalizer hC_normK
    have hSsub_pi : IsPiSubgroup (G := C) πᶜ (S.subgroupOf C) := by
      exact hS_pi.subgroupOf (by intro y hy; exact hy.2)
    have hSsub_le_core : S.subgroupOf C ≤ piCore πᶜ ↥C :=
      le_sSup ⟨hSsub_norm, hSsub_pi⟩
    have hxC : x ∈ C := hx.2
    have hxSsub : (⟨x, hxC⟩ : C) ∈ S.subgroupOf C := by
      change x ∈ S
      exact hx
    have hxcore_sub : (⟨x, hxC⟩ : C) ∈ piCore πᶜ ↥C := hSsub_le_core hxSsub
    have hcore_eq : (piCoreIn πᶜ C).subgroupOf C = piCore πᶜ ↥C := by
      simpa using piCore_map_subtype_subgroupOf (G := G) πᶜ C
    have hxcore_sub' : (⟨x, hxC⟩ : C) ∈ (piCoreIn πᶜ C).subgroupOf C := by
      simpa [hcore_eq] using hxcore_sub
    simpa [Subgroup.mem_subgroupOf] using hxcore_sub'
  · intro x hx
    have hxC : x ∈ C := piCoreIn_le (G := G) πᶜ C hx
    have hC_pi : IsPiSubgroup (G := G) πᶜ (piCoreIn πᶜ C) :=
      piCoreIn_isPiSubgroup (G := G) πᶜ C
    have hpiCoreC_le_CA : piCoreIn πᶜ C ≤ CA :=
      (piCoreIn_le (G := G) πᶜ C).trans hC_le_CA
    have hxK : x ∈ section7K A :=
      le_section7K_of_le_centralizer_isPiSubgroup hA hpiCoreC_le_CA hC_pi hx
    exact ⟨hxK, hxC⟩

lemma CFSG.subgroupPrimeSet_eq_of_le_isPiSubgroup
    {G : Type*} [Group G] [Finite G] {A B : Subgroup G} (hAB : A ≤ B)
    (hBπ : IsPiSubgroup (G := G) (subgroupPrimeSet A) B) :
    subgroupPrimeSet B = subgroupPrimeSet A := by
  ext p
  constructor
  · intro hpB
    exact hBπ p hpB
  · intro hpA
    have hcard_dvd : Nat.card A ∣ Nat.card B := by
      have hsub_dvd : Nat.card (A.subgroupOf B) ∣ Nat.card B :=
        Subgroup.card_subgroup_dvd_card (A.subgroupOf B)
      have hcard_eq : Nat.card (A.subgroupOf B) = Nat.card A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
      rwa [hcard_eq] at hsub_dvd
    exact dvd_trans hpA hcard_dvd

private theorem CFSG.hypothesis7_1_of_le_isPiSubgroup
    {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hA : Hypothesis7_1 A) (hAB : A ≤ B) (hBproper : B ≠ ⊤)
    (hBπ : IsPiSubgroup (G := G) (subgroupPrimeSet A) B) :
    Hypothesis7_1 B := by
  have hπeq : subgroupPrimeSet B = subgroupPrimeSet A :=
    subgroupPrimeSet_eq_of_le_isPiSubgroup hAB hBπ
  constructor
  · exact ne_bot_of_le_ne_bot hA.1 hAB
  · constructor
    · exact hBproper
    · intro X hBX hXproper
      have hAX : A ≤ X := hAB.trans hBX
      apply le_antisymm
      · calc
          section7Generated X B (subgroupPrimeSet B)ᶜ
              ≤ section7Generated X A (subgroupPrimeSet A)ᶜ := by
                apply sSup_le
                intro Q hQ
                have hQ' : Q ∈ section7HFamily X A (subgroupPrimeSet A)ᶜ := by
                  rcases hQ with ⟨hQX, hQπ, hBnormQ⟩
                  refine ⟨hQX, ?_, hAB.trans hBnormQ⟩
                  simpa [hπeq] using hQπ
                exact le_sSup hQ'
          _ = piCoreIn (subgroupPrimeSet A)ᶜ X := hA.2.2 X hAX hXproper
          _ = piCoreIn (subgroupPrimeSet B)ᶜ X := by simp [hπeq]
      · have hXfam :
            piCoreIn (subgroupPrimeSet B)ᶜ X ∈
              section7HFamily X B (subgroupPrimeSet B)ᶜ := by
          refine ⟨piCoreIn_le (G := G) (subgroupPrimeSet B)ᶜ X,
            piCoreIn_isPiSubgroup (G := G) (subgroupPrimeSet B)ᶜ X, ?_⟩
          have hX_norm :
              X ≤ Subgroup.normalizer (piCoreIn (subgroupPrimeSet B)ᶜ X : Set G) := by
            have hsub_eq :
                (piCoreIn (subgroupPrimeSet B)ᶜ X).subgroupOf X =
                  piCore (subgroupPrimeSet B)ᶜ ↥X := by
              simpa using
                piCore_map_subtype_subgroupOf (G := G) (subgroupPrimeSet B)ᶜ X
            have hsub_norm : ((piCoreIn (subgroupPrimeSet B)ᶜ X).subgroupOf X).Normal := by
              rw [hsub_eq]
              infer_instance
            exact Subgroup.le_normalizer_of_normal_subgroupOf
              (piCoreIn_le (G := G) (subgroupPrimeSet B)ᶜ X)
          exact hBX.trans hX_norm
        have :
            piCoreIn (subgroupPrimeSet B)ᶜ X ≤
              section7Generated X B (subgroupPrimeSet B)ᶜ := by
          exact le_sSup hXfam
        simpa [hπeq] using this


private lemma CFSG.isSubnormalIn_of_normal_subgroupOf
    {G : Type*} [Group G] {A P : Subgroup G} (hAP : A ≤ P)
    [hAPnorm : (A.subgroupOf P).Normal] :
    IsSubnormalIn A P := by
  refine ⟨1, ![A, P], by simp, by simp, ?_, ?_⟩
  · intro i
    fin_cases i
    simpa using hAP
  · intro i
    fin_cases i
    change (A.subgroupOf P).Normal
    exact (inferInstance : (A.subgroupOf P).Normal)

private theorem CFSG.le_normalizer_section7K_of_le_normalizer
    {G : Type*} [Group G] [Finite G] {A P : Subgroup G}
    (hPA : P ≤ Subgroup.normalizer (A : Set G)) :
    P ≤ Subgroup.normalizer (section7K A : Set G) := by
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  have hK_le_C : section7K A ≤ C := by
    simpa [C] using section7K_le_centralizer (G := G) A
  have hP_le_normC : P ≤ Subgroup.normalizer (C : Set G) := by
    refine subgroup_le_normalizer_of_conj_mem C P ?_
    intro p c hc
    change (p : G) * c * (p : G)⁻¹ ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hpaA : (p : G)⁻¹ * a * (p : G) ∈ A := by
      have hp_inv_normA : (p : G)⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
        hPA (P.inv_mem p.property)
      simpa using (Subgroup.mem_normalizer_iff.mp hp_inv_normA a).1 ha
    have hc_comm : (c : G) * ((p : G)⁻¹ * a * (p : G)) = ((p : G)⁻¹ * a * (p : G)) * c :=
      (Subgroup.mem_centralizer_iff.mp hc _ hpaA).symm
    have hcomm := congrArg (fun t : G => (p : G) * t * (p : G)⁻¹) hc_comm
    simpa [mul_assoc] using hcomm.symm
  have hKsub_eq : (section7K A).subgroupOf C = piCore (subgroupPrimeSet A)ᶜ ↥C := by
    simpa [C, section7K] using
      piCore_map_subtype_subgroupOf (G := G) (subgroupPrimeSet A)ᶜ C
  have hKsub_char : ((section7K A).subgroupOf C).Characteristic := by
    rw [hKsub_eq]
    exact piCore_characteristic (G := ↥C) (subgroupPrimeSet A)ᶜ
  refine subgroup_le_normalizer_of_conj_mem (section7K A) P ?_
  intro p x hx
  let pC : Subgroup.normalizer (C : Set G) := ⟨p, hP_le_normC p.property⟩
  let xC : C := ⟨x, hK_le_C hx⟩
  have hxC : xC ∈ (section7K A).subgroupOf C := by
    change x ∈ section7K A
    exact hx
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom C pC).toMonoidHom ((section7K A).subgroupOf C) =
        (section7K A).subgroupOf C :=
    hKsub_char.fixed (Subgroup.normalizerMonoidHom C pC)
  have hxComap :
      xC ∈
        Subgroup.comap (Subgroup.normalizerMonoidHom C pC).toMonoidHom
          ((section7K A).subgroupOf C) := by
    rw [hfix]
    exact hxC
  have hxImage : (Subgroup.normalizerMonoidHom C pC) xC ∈ (section7K A).subgroupOf C := hxComap
  change (p : G) * x * (p : G)⁻¹ ∈ section7K A at hxImage
  simpa [pC, xC, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe] using hxImage

private theorem CFSG.isHallSubgroup_subgroupOf_sup_section7K
    {G : Type*} [Group G] [Finite G] {A P : Subgroup G}
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hPπ : IsPiSubgroup (G := G) (subgroupPrimeSet A) P) :
    let KP : Subgroup G := section7K A ⊔ P
    IsHallSubgroup (subgroupPrimeSet A) (P.subgroupOf KP) := by
  let KP : Subgroup G := section7K A ⊔ P
  let Ksub : Subgroup KP := (section7K A).subgroupOf KP
  let Psub : Subgroup KP := P.subgroupOf KP
  have hK_pi' : IsPiSubgroup (G := G) (subgroupPrimeSet A)ᶜ (section7K A) := by
    simpa [section7K] using
      piCoreIn_isPiSubgroup (G := G) (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (A : Set G))
  have hPnormK : P ≤ Subgroup.normalizer (section7K A : Set G) :=
    le_normalizer_section7K_of_le_normalizer hPnormA
  have hKP_le_normK : KP ≤ Subgroup.normalizer (section7K A : Set G) := by
    exact sup_le Subgroup.le_normalizer hPnormK
  have hKsub_norm : Ksub.Normal := by
    simpa [KP, Ksub] using
      (Subgroup.normal_subgroupOf_of_le_normalizer
        (H := KP) (N := section7K A) hKP_le_normK)
  let : Ksub.Normal := hKsub_norm
  have hcopKP : Nat.Coprime (Nat.card P) (Nat.card (section7K A)) := by
    refine Nat.coprime_of_dvd ?_
    intro p hpPrime hpP hpK
    let p' : Nat.Primes := ⟨p, hpPrime⟩
    have hp_in : p' ∈ subgroupPrimeSet A := hPπ p' hpP
    have hp_notin : p' ∉ subgroupPrimeSet A := by
      simpa using hK_pi' p' hpK
    exact hp_notin hp_in
  have hcop_sub :
      Nat.Coprime (Nat.card Psub) (Nat.card Ksub) := by
    have hcardPsub : Nat.card Psub = Nat.card P := by
      simpa [Psub] using
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := P) (K := KP) le_sup_right).toEquiv
    have hcardKsub : Nat.card Ksub = Nat.card (section7K A) := by
      simpa [Ksub] using
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := section7K A) (K := KP) le_sup_left).toEquiv
    rwa [hcardPsub, hcardKsub]
  have hdisj : Disjoint Ksub Psub := by
    have hbot : Ksub ⊓ Psub = ⊥ := by
      rw [inf_comm]
      exact (Subgroup.disjoint_of_coprime_natCard hcop_sub).eq_bot
    rw [Subgroup.disjoint_def]
    intro x hxK hxP
    have hxbot : x ∈ (⊥ : Subgroup KP) := by
      simpa [hbot] using (show x ∈ Ksub ⊓ Psub from ⟨hxK, hxP⟩)
    simpa using hxbot
  have hsup_top : Ksub ⊔ Psub = ⊤ := by
    calc
      Ksub ⊔ Psub = ((section7K A) ⊔ P).subgroupOf KP := by
        symm
        exact
          Subgroup.subgroupOf_sup
            (A := section7K A) (A' := P) (B := KP) le_sup_left le_sup_right
      _ = ⊤ := by simp [KP]
  have hcomp : Ksub.IsComplement' Psub := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
    rw [Set.eq_univ_iff_forall]
    intro x
    have hxsup : x ∈ Ksub ⊔ Psub := by simp [hsup_top]
    exact (Subgroup.mem_sup_of_normal_left (x := x) (s := Ksub) (t := Psub)).1 hxsup
  have hPsub_pi : IsPiSubgroup (G := KP) (subgroupPrimeSet A) Psub :=
    hPπ.subgroupOf le_sup_right
  have hKsub_pi' : IsPiSubgroup (G := KP) (subgroupPrimeSet A)ᶜ Ksub :=
    hK_pi'.subgroupOf le_sup_left
  refine isHallSubgroup_of (G := KP) (π := subgroupPrimeSet A) (H := Psub) ?_ ?_
  · intro p hp
    exact hPsub_pi p hp
  · intro p hp_in hp_idx
    have hp_card : p.val ∣ Nat.card Ksub := by
      rw [hcomp.index_eq_card] at hp_idx
      exact hp_idx
    exact (hKsub_pi' p hp_card) hp_in

private theorem CFSG.mem_subgroupCentralizerIn_of_mem_section7K_of_mem_normalizer
    {G : Type*} [Group G] [Finite G] {A P : Subgroup G}
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hPπ : IsPiSubgroup (G := G) (subgroupPrimeSet A) P)
    {x : G} (hxK : x ∈ section7K A) (hxNorm : x ∈ Subgroup.normalizer (P : Set G)) :
    x ∈ subgroupCentralizerIn (section7K A) P := by
  have hK_pi' : IsPiSubgroup (G := G) (subgroupPrimeSet A)ᶜ (section7K A) := by
    simpa [section7K] using
      piCoreIn_isPiSubgroup (G := G) (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (A : Set G))
  have hPnormK : P ≤ Subgroup.normalizer (section7K A : Set G) :=
    le_normalizer_section7K_of_le_normalizer hPnormA
  have hcopPK : Nat.Coprime (Nat.card P) (Nat.card (section7K A)) := by
    refine Nat.coprime_of_dvd ?_
    intro p hpPrime hpP hpK
    let p' : Nat.Primes := ⟨p, hpPrime⟩
    have hp_in : p' ∈ subgroupPrimeSet A := hPπ p' hpP
    have hp_notin : p' ∉ subgroupPrimeSet A := by
      simpa using hK_pi' p' hpK
    exact hp_notin hp_in
  have hPK_bot : P ⊓ section7K A = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcopPK).eq_bot
  refine ⟨hxK, ?_⟩
  change x ∈ Subgroup.centralizer (P : Set G)
  rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
  intro p hp
  have hcommP : p * x * p⁻¹ * x⁻¹ ∈ P := by
    have hxpinv : x * p⁻¹ * x⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hxNorm (p⁻¹)).1 (P.inv_mem hp)
    simpa [mul_assoc] using P.mul_mem hp hxpinv
  have hcommK : p * x * p⁻¹ * x⁻¹ ∈ section7K A := by
    have hpxpinv : p * x * p⁻¹ ∈ section7K A :=
      (Subgroup.mem_normalizer_iff.mp (hPnormK hp) x).1 hxK
    exact (section7K A).mul_mem hpxpinv ((section7K A).inv_mem hxK)
  have hcommInf : p * x * p⁻¹ * x⁻¹ ∈ P ⊓ section7K A := ⟨hcommP, hcommK⟩
  have hcommBot : p * x * p⁻¹ * x⁻¹ ∈ (⊥ : Subgroup G) := by
    simpa [hPK_bot] using hcommInf
  simpa [commutatorElement_def] using hcommBot

private theorem CFSG.ne_top_of_isPiSubgroup_singleton_ne_bot
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {Q : Subgroup G} {q : Nat.Primes}
    (hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q) (hQ_ne_bot : Q ≠ ⊥) :
    Q ≠ ⊤ := by
  intro hQ_top
  subst hQ_top
  let : Fact q.val.Prime := ⟨q.2⟩
  let : Nontrivial ↥(⊤ : Subgroup G) :=
    (Subgroup.nontrivial_iff_ne_bot (H := (⊤ : Subgroup G))).2 (by simpa using hQ_ne_bot)
  let : Nontrivial G := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).injective.nontrivial
  have htop_q : IsPGroup q.val (⊤ : Subgroup G) :=
    isPGroup_of_isPiSubgroup_singleton hQπ
  have hGq : IsPGroup q.val G := htop_q.of_equiv Subgroup.topEquiv
  have hcenter_nontrivial : Nontrivial (Subgroup.center G) :=
    IsPGroup.center_nontrivial (p := q.val) (G := G) hGq
  have hcenter_ne_bot : Subgroup.center G ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (H := Subgroup.center G)).1 hcenter_nontrivial
  exact hcenter_ne_bot (center_eq_bot_of_min_ce (G := G))

private theorem CFSG.normal_or_exists_intermediate_of_chain
    {G : Type*} [Group G] {A B : Subgroup G} :
    ∀ n, ∀ chain : Fin (n + 1) → Subgroup G,
      chain 0 = A →
      chain (Fin.last n) = B →
      (∀ i : Fin n, chain i.castSucc ≤ chain i.succ) →
      (∀ i : Fin n, ((chain i.castSucc).subgroupOf (chain i.succ)).Normal) →
      ((A.subgroupOf B).Normal) ∨
        ∃ C : Subgroup G, A < C ∧ C < B ∧ IsSubnormalIn A C ∧ (C.subgroupOf B).Normal
  | 0, chain, h0, hlast, _hstep, _hnorm => by
      have hAB : A = B := h0.symm.trans hlast
      subst hAB
      exact Or.inl <| by
        have htop : A.subgroupOf A = (⊤ : Subgroup A) := by
          ext x
          simp
        rw [htop]
        infer_instance
  | n + 1, chain, h0, hlast, hstep, hnorm => by
      let C : Subgroup G := chain (Fin.castSucc (Fin.last n))
      let chain0 : Fin (n + 1) → Subgroup G := fun i => chain i.castSucc
      have hchain00 : chain0 0 = A := by
        simpa [chain0] using h0
      have hchain0_last : chain0 (Fin.last n) = C := by
        simp [chain0, C]
      have hchain0_step : ∀ i : Fin n, chain0 i.castSucc ≤ chain0 i.succ := by
        intro i
        simpa [chain0] using hstep i.castSucc
      have hchain0_norm :
          ∀ i : Fin n, ((chain0 i.castSucc).subgroupOf (chain0 i.succ)).Normal := by
        intro i
        change ((chain i.castSucc.castSucc).subgroupOf (chain i.castSucc.succ)).Normal
        exact hnorm i.castSucc
      have hAC : IsSubnormalIn A C := by
        exact
          ⟨n, chain0, hchain00, hchain0_last, hchain0_step, hchain0_norm⟩
      by_cases hCB : C = B
      · rw [← hCB]
        exact
          normal_or_exists_intermediate_of_chain (A := A) (B := C)
            n chain0 hchain00 hchain0_last hchain0_step hchain0_norm
      · have hC_lt_B : C < B := by
          have hC_le_B : C ≤ B := by
            simpa [C, hlast] using hstep (Fin.last n)
          exact lt_of_le_of_ne hC_le_B hCB
        by_cases hACeq : A = C
        · subst hACeq
          exact Or.inl <| by
            rw [← hlast]
            change ((chain (Fin.last n).castSucc).subgroupOf (chain (Fin.last n).succ)).Normal
            exact hnorm (Fin.last n)
        · refine Or.inr ⟨C, ?_, hC_lt_B, hAC, ?_⟩
          · exact lt_of_le_of_ne hAC.le hACeq
          · rw [← hlast]
            change ((chain (Fin.last n).castSucc).subgroupOf (chain (Fin.last n).succ)).Normal
            exact hnorm (Fin.last n)

private theorem CFSG.IsSubnormalIn.normal_or_exists_intermediate
    {G : Type*} [Group G] {A P : Subgroup G} (hAP : IsSubnormalIn A P) :
    ((A.subgroupOf P).Normal) ∨
      ∃ B : Subgroup G, A < B ∧ B < P ∧ IsSubnormalIn A B ∧ (B.subgroupOf P).Normal := by
  rcases hAP with ⟨n, chain, h0, hlast, hstep, hnorm⟩
  exact
    normal_or_exists_intermediate_of_chain (A := A) (B := P)
      n chain h0 hlast hstep hnorm

public theorem CFSG.le_normalizer_piCoreIn_of_le_normalizer
    {G : Type*} [Group G] [Finite G] {π : Set Nat.Primes} {H P : Subgroup G}
    (hPH : P ≤ Subgroup.normalizer (H : Set G)) :
    P ≤ Subgroup.normalizer (piCoreIn π H : Set G) := by
  have hpi_le_H : piCoreIn π H ≤ H := piCoreIn_le (G := G) π H
  have hsub_eq : (piCoreIn π H).subgroupOf H = piCore π ↥H := by
    simpa using piCore_map_subtype_subgroupOf (G := G) π H
  have hsub_char : ((piCoreIn π H).subgroupOf H).Characteristic := by
    rw [hsub_eq]
    exact piCore_characteristic (G := ↥H) π
  refine subgroup_le_normalizer_of_conj_mem (piCoreIn π H) P ?_
  intro p x hx
  let pH : Subgroup.normalizer (H : Set G) := ⟨p, hPH p.property⟩
  let xH : H := ⟨x, hpi_le_H hx⟩
  have hxH : xH ∈ (piCoreIn π H).subgroupOf H := by
    change x ∈ piCoreIn π H
    exact hx
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H pH).toMonoidHom ((piCoreIn π H).subgroupOf H) =
        (piCoreIn π H).subgroupOf H :=
    hsub_char.fixed (Subgroup.normalizerMonoidHom H pH)
  have hxComap :
      xH ∈
        Subgroup.comap (Subgroup.normalizerMonoidHom H pH).toMonoidHom
          ((piCoreIn π H).subgroupOf H) := by
    rw [hfix]
    exact hxH
  have hxImage :
      (Subgroup.normalizerMonoidHom H pH) xH ∈ (piCoreIn π H).subgroupOf H := hxComap
  change (p : G) * x * (p : G)⁻¹ ∈ piCoreIn π H at hxImage
  simpa [pH, xH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe] using hxImage

private theorem CFSG.normalizer_ne_top_of_ne_bot_ne_top
    {G : Type*} [Group G] [Finite G] [IsMinCE G] {Q : Subgroup G}
    (hQ_ne_bot : Q ≠ ⊥) (hQ_ne_top : Q ≠ ⊤) :
    Subgroup.normalizer (Q : Set G) ≠ ⊤ := by
  intro hNtop
  have hQnormal : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  let : IsSimpleGroup G := IsMinCE.simple
  rcases hQnormal.eq_bot_or_eq_top with hQbot | hQtop
  · exact hQ_ne_bot hQbot
  · exact hQ_ne_top hQtop


private theorem CFSG.quotient_card_prime_of_normal_no_intermediate
    {G : Type*} [Group G] [Finite G] {A P : Subgroup G}
    (hAP : A < P) [hAPnorm : (A.subgroupOf P).Normal]
    (hsolvP : Group.IsSolvable P)
    (hno : ∀ B : Subgroup G, A < B → B < P → (B.subgroupOf P).Normal → False) :
    Nat.Prime (Nat.card (P ⧸ (A.subgroupOf P))) := by
  let A0 : Subgroup P := A.subgroupOf P
  have hA0_ne_top : A0 ≠ ⊤ := by
    intro hA0top
    have hPleA : P ≤ A := (Subgroup.subgroupOf_eq_top).mp hA0top
    exact hAP.ne (le_antisymm hAP.le hPleA)
  let : A0.Normal := by
    simpa [A0] using hAPnorm
  have hquot_nontrivial : Nontrivial (P ⧸ A0) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsubs
    exact hA0_ne_top (QuotientGroup.subgroup_eq_top_of_subsingleton A0 hsubs)
  let : Nontrivial (P ⧸ A0) := hquot_nontrivial
  have : Group.IsSolvable (P ⧸ A0) := Group.isSolvable_of_surjective
    (f := QuotientGroup.mk' A0) (QuotientGroup.mk'_surjective A0)
  obtain ⟨N, hNnorm, hNindex_prime⟩ := exist_index_p_of_solvable (P ⧸ A0)
  by_cases hNbot : N = ⊥
  · have hprime_bot : Nat.Prime (Nat.card ((P ⧸ A0) ⧸ (⊥ : Subgroup (P ⧸ A0)))) := by
        simpa [Subgroup.index_eq_card, hNbot] using hNindex_prime
    have hcard_bot :
        Nat.card ((P ⧸ A0) ⧸ (⊥ : Subgroup (P ⧸ A0))) = Nat.card (P ⧸ A0) :=
      Nat.card_congr QuotientGroup.quotientBot.toEquiv
    have hprime : Nat.Prime (Nat.card (P ⧸ A0)) := by
      simpa [hcard_bot] using hprime_bot
    simpa [A0] using hprime
  · have hN_ne_top : N ≠ ⊤ := by
      intro hNtop
      exact hNindex_prime.ne_one (by simp [hNtop])
    let e : Subgroup (P ⧸ A0) ≃o {H : Subgroup P // A0 ≤ H} :=
      QuotientGroup.comapMk'OrderIso A0
    let Bsub : Subgroup P := (e N).1
    have hA0_le_Bsub : A0 ≤ Bsub := (e N).2
    have hBsub_norm : Bsub.Normal := by
      exact hNnorm.comap (QuotientGroup.mk' A0)
    have hBsub_ne_top : Bsub ≠ ⊤ := by
      intro hBsub_top
      apply hN_ne_top
      exact e.injective <| by
        apply Subtype.ext
        change Bsub = Subgroup.comap (QuotientGroup.mk' A0) ⊤
        simp [Bsub, hBsub_top]
    have hBsub_ne_A0 : Bsub ≠ A0 := by
      intro hBsub_eq
      apply hNbot
      exact e.injective <| by
        apply Subtype.ext
        change Bsub = Subgroup.comap (QuotientGroup.mk' A0) ⊥
        simp [Bsub, hBsub_eq]
    let B : Subgroup G := Bsub.map P.subtype
    have hB_le_P : B ≤ P := by
      exact Subgroup.map_subtype_le (H := P) (K := Bsub)
    have hBsub_eq : B.subgroupOf P = Bsub := by
      change (Bsub.map P.subtype).subgroupOf P = Bsub
      exact Subgroup.comap_map_eq_self_of_injective (H := Bsub) (f := P.subtype) P.subtype_injective
    have hA_le_B : A ≤ B := by
      intro a ha
      exact Subgroup.mem_map.mpr ⟨⟨a, hAP.le ha⟩, hA0_le_Bsub (by simpa), rfl⟩
    have hA_ne_B : A ≠ B := by
      intro hAB
      apply hBsub_ne_A0
      simpa [A0, B, hAB] using hBsub_eq.symm
    have hB_ne_P : B ≠ P := by
      intro hBP
      apply hBsub_ne_top
      simpa [B, hBP] using hBsub_eq.symm
    have hAB : A < B := lt_of_le_of_ne hA_le_B hA_ne_B
    have hBP : B < P := lt_of_le_of_ne hB_le_P hB_ne_P
    have hBnorm : (B.subgroupOf P).Normal := by
      simpa [hBsub_eq] using hBsub_norm
    exact False.elim (hno B hAB hBP hBnorm)

private theorem CFSG.exists_mem_section7HStarFamily_normalized_by_of_normal_no_intermediate
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {A P : Subgroup G} (_hA : Hypothesis7_1 A) (hAP : A ≤ P)
    {q : Nat.Primes} (_hq : q ∉ subgroupPrimeSet A)
    (hPproper : P ≠ ⊤) [hAPnorm : (A.subgroupOf P).Normal]
    (hPπ : IsPiSubgroup (subgroupPrimeSet A) P)
    (htrans : ConjugationActionTransitiveOn (section7K A)
      (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)))
    (hno : ∀ B : Subgroup G, A < B → B < P → (B.subgroupOf P).Normal → False) :
    ∃ Q ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes),
      P ≤ Subgroup.normalizer (Q : Set G) := by
  classical
  let Ωsub :=
    {Q : Subgroup G // Q ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)}
  have hbot_fam :
      (⊥ : Subgroup G) ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
    refine ⟨le_top, ?_, ?_⟩
    intro p hp
    exact False.elim (p.2.not_dvd_one (by simpa using hp))
    · intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp
  obtain ⟨Q₀, hQ₀, _⟩ := exists_mem_section7HStarFamily_of_mem_family hbot_fam
  by_cases hAPeq : A = P
  · refine ⟨Q₀, hQ₀, ?_⟩
    simpa [hAPeq] using (section7HStarFamily.mem_family hQ₀).2.2
  · have hA_lt_P : A < P := lt_of_le_of_ne hAP hAPeq
    have : Group.IsSolvable P := solvable_of_proper_subgroup hPproper
    have hquot_prime :
        Nat.Prime (Nat.card (P ⧸ (A.subgroupOf P))) :=
      quotient_card_prime_of_normal_no_intermediate hA_lt_P (hsolvP := inferInstance) hno
    let r : Nat.Primes := ⟨Nat.card (P ⧸ (A.subgroupOf P)), hquot_prime⟩
    let : Fact r.val.Prime := ⟨r.2⟩
    let : MulAction (section7K A) Ωsub := {
      smul := fun k Q => ⟨Q.1.conjBy (k : G), by
        exact mem_section7HStarFamily_top_conjBy_of_mem_centralizer
          (section7K_le_centralizer A k.property) Q.2⟩
      one_smul := by
        intro Q
        apply Subtype.ext
        exact Subgroup.conjBy_one Q.1
      mul_smul := by
        intro k₁ k₂ Q
        apply Subtype.ext
        exact (Subgroup.conjBy_conjBy Q.1 (k₂ : G) (k₁ : G)).symm }
    let Q₀sub : Ωsub := ⟨Q₀, hQ₀⟩
    have hOrbit_univ : MulAction.orbit (section7K A) Q₀sub = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro Q
      rcases htrans Q₀ hQ₀ Q.1 Q.2 with ⟨k, hk⟩
      exact MulAction.mem_orbit_iff.mpr ⟨k, by
        apply Subtype.ext
        exact hk.symm⟩
    have hcardΩ_dvd : Nat.card Ωsub ∣ Nat.card (section7K A) := by
      let : Fintype (section7K A) := Fintype.ofFinite (section7K A)
      let : Fintype Ωsub := Fintype.ofFinite Ωsub
      let : Fintype ↥(MulAction.orbit (section7K A) Q₀sub) :=
        Fintype.ofFinite ↥(MulAction.orbit (section7K A) Q₀sub)
      let : Fintype ↥(MulAction.stabilizer (section7K A) Q₀sub) :=
        Fintype.ofFinite ↥(MulAction.stabilizer (section7K A) Q₀sub)
      refine ⟨Fintype.card (MulAction.stabilizer (section7K A) Q₀sub), ?_⟩
      simpa [Nat.card_eq_fintype_card, hOrbit_univ] using
        (MulAction.card_orbit_mul_card_stabilizer_eq_card_group
          (section7K A) Q₀sub).symm
    have hr_dvd_P : r.val ∣ Nat.card P := by
      simpa [r] using Subgroup.card_quotient_dvd_card (s := A.subgroupOf P)
    have hr_in_pi : r ∈ subgroupPrimeSet A := hPπ r hr_dvd_P
    have hK_pi' : IsPiSubgroup (G := G) (subgroupPrimeSet A)ᶜ (section7K A) := by
      simpa [section7K] using
        piCoreIn_isPiSubgroup (G := G) (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (A : Set G))
    have hr_not_dvd_K : ¬ r.val ∣ Nat.card (section7K A) := by
      intro hrK
      have hr_notin : r ∉ subgroupPrimeSet A := by
        simpa using hK_pi' r hrK
      exact hr_notin hr_in_pi
    have hr_not_dvd_Ω : ¬ r.val ∣ Nat.card Ωsub := by
      intro hrΩ
      exact hr_not_dvd_K (dvd_trans hrΩ hcardΩ_dvd)
    have hPnormA : P ≤ Subgroup.normalizer (A : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf hAP
    let : MulAction P Ωsub := {
      smul := fun p Q => ⟨Q.1.conjBy ((p : P) : G), by
        exact mem_section7HStarFamily_top_conjBy_of_mem_normalizer (hPnormA p.property) Q.2⟩
      one_smul := by
        intro Q
        apply Subtype.ext
        exact Subgroup.conjBy_one Q.1
      mul_smul := by
        intro p₁ p₂ Q
        apply Subtype.ext
        exact (Subgroup.conjBy_conjBy Q.1 ((p₂ : P) : G) ((p₁ : P) : G)).symm }
    have hAker : A.subgroupOf P ≤ (MulAction.toPermHom P Ωsub).ker := by
      intro a ha
      have haA : (a : G) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using ha
      apply Equiv.ext
      intro Q
      apply Subtype.ext
      rcases section7HStarFamily.mem_family Q.2 with ⟨_, _, hAnormQ⟩
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hAnormQ haA) y).1 hy
      · intro hx
        have ha_inv : (a : G)⁻¹ ∈ Subgroup.normalizer (Q.1 : Set G) :=
          (Subgroup.normalizer (Q.1 : Set G)).inv_mem (hAnormQ haA)
        exact Subgroup.mem_map.mpr ⟨(a : G)⁻¹ * x * (a : G),
          by simpa using (Subgroup.mem_normalizer_iff.mp ha_inv x).1 hx, by
            simp [mul_assoc]⟩
    let τbar : P ⧸ (A.subgroupOf P) →* Equiv.Perm Ωsub :=
      QuotientGroup.lift (A.subgroupOf P) (MulAction.toPermHom P Ωsub) <| by
        intro a ha
        exact hAker ha
    let : MulAction (P ⧸ (A.subgroupOf P)) Ωsub := MulAction.compHom Ωsub τbar
    have hquot_pgroup : IsPGroup r.val (P ⧸ (A.subgroupOf P)) := by
      exact IsPGroup.of_card (p := r.val) (G := P ⧸ (A.subgroupOf P)) (n := 1) (by simp [r])
    rcases hquot_pgroup.nonempty_fixed_point_of_prime_not_dvd_card Ωsub hr_not_dvd_Ω with
      ⟨Qfix, hQfix⟩
    refine ⟨Qfix.1, Qfix.2, ?_⟩
    intro p hp
    let pg : P := ⟨p, hp⟩
    have hpfix :
        (QuotientGroup.mk pg : P ⧸ (A.subgroupOf P)) • Qfix = Qfix :=
      (MulAction.mem_fixedPoints.mp hQfix) (QuotientGroup.mk pg)
    have hpeq : Qfix.1.conjBy (p : G) = Qfix.1 := by
      exact congrArg Subtype.val (by
        simpa [pg, τbar, MulAction.compHom_smul_def] using hpfix)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxconj :
          p * x * p⁻¹ ∈ Qfix.1.conjBy (p : G) :=
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      simpa [hpeq] using hxconj
    · intro hx
      have hxconj :
          p * x * p⁻¹ ∈ Qfix.1.conjBy (p : G) := by
        simpa [hpeq] using hx
      rcases Subgroup.mem_map.mp hxconj with ⟨y, hy, hyEq⟩
      have hyx : y = x := by
        apply (MulAut.conj p).injective
        simpa [MulAut.conj_apply] using hyEq
      simpa [hyx] using hy

private theorem CFSG.mem_section7HStarFamily_A_of_mem_section7HStarFamily_P_of_normal_no_intermediate
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {A P Q : Subgroup G} (hA : Hypothesis7_1 A) (hAP : A ≤ P)
    {q : Nat.Primes} (hq : q ∉ subgroupPrimeSet A)
    (hPproper : P ≠ ⊤) [hAPnorm : (A.subgroupOf P).Normal]
    (hPπ : IsPiSubgroup (subgroupPrimeSet A) P)
    (htrans : ConjugationActionTransitiveOn (section7K A)
      (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)))
    (hno : ∀ B : Subgroup G, A < B → B < P → (B.subgroupOf P).Normal → False)
    (hQ : Q ∈ section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes)) :
    Q ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
  classical
  let : Fact q.val.Prime := ⟨q.2⟩
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  let H : Subgroup G := piCoreIn (subgroupPrimeSet A)ᶜ N
  have hQfamP : Q ∈ section7HFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) :=
    section7HStarFamily.mem_family hQ
  have hPnormQ : P ≤ N := by
    simpa [N] using hQfamP.2.2
  have hQfamA : Q ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
    exact ⟨le_top, hQfamP.2.1, hAP.trans hPnormQ⟩
  by_cases hQbot : Q = ⊥
  · obtain ⟨Q₀, hQ₀, hPnormQ₀⟩ :=
      exists_mem_section7HStarFamily_normalized_by_of_normal_no_intermediate
        hA hAP hq hPproper hPπ htrans hno
    have hQ₀famP : Q₀ ∈ section7HFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) := by
      exact ⟨le_top, (section7HStarFamily.mem_family hQ₀).2.1, hPnormQ₀⟩
    have hQ₀_eq_Q : Q₀ = Q := by
      exact hQ.2 Q₀ (by simp [hQbot]) hQ₀famP
    simpa [hQ₀_eq_Q, hQbot] using hQ₀
  · obtain ⟨Q₁, hQ₁, hQ_le_Q₁⟩ := exists_mem_section7HStarFamily_of_mem_family hQfamA
    have hQ_ne_top : Q ≠ ⊤ :=
      ne_top_of_isPiSubgroup_singleton_ne_bot hQfamP.2.1 hQbot
    have hNproper : N ≠ ⊤ :=
      normalizer_ne_top_of_ne_bot_ne_top hQbot hQ_ne_top
    have hA_le_N : A ≤ N := hAP.trans hPnormQ
    have hNQ₁_le_H : N ⊓ Q₁ ≤ H := by
      simpa [H, N] using
        inf_le_piCoreIn_of_hypothesis hA hq hQ₁ hA_le_N hNproper
    have hQ_le_NQ₁ : Q ≤ N ⊓ Q₁ := by
      intro x hx
      exact ⟨Subgroup.le_normalizer hx, hQ_le_Q₁ hx⟩
    have hQ_le_H : Q ≤ H := hQ_le_NQ₁.trans hNQ₁_le_H
    have hH_pi' : IsPiSubgroup (G := G) (subgroupPrimeSet A)ᶜ H := by
      simpa [H] using
        piCoreIn_isPiSubgroup (G := G) (subgroupPrimeSet A)ᶜ N
    have hcopPH : Nat.Coprime (Nat.card P) (Nat.card H) := by
      refine Nat.coprime_of_dvd ?_
      intro p hpPrime hpP hpH
      let p' : Nat.Primes := ⟨p, hpPrime⟩
      have hp_in : p' ∈ subgroupPrimeSet A := hPπ p' hpP
      have hp_notin : p' ∉ subgroupPrimeSet A := by
        simpa using hH_pi' p' hpH
      exact hp_notin hp_in
    have hPnormH : P ≤ Subgroup.normalizer (H : Set G) := by
      have hP_le_normN : P ≤ Subgroup.normalizer (N : Set G) :=
        hPnormQ.trans Subgroup.le_normalizer
      simpa [H, N] using
        le_normalizer_piCoreIn_of_le_normalizer
          (π := (subgroupPrimeSet A)ᶜ) (H := N) (P := P) hP_le_normN
    have hHproper : H ≠ ⊤ := by
      intro hHtop
      apply hNproper
      exact top_unique (by simpa [H, hHtop] using (piCoreIn_le (G := G) (subgroupPrimeSet A)ᶜ N))
    have : Group.IsSolvable H := solvable_of_proper_subgroup hHproper
    have : Subgroup.Normalizes P H := ⟨hPnormH⟩
    have hQsub_pi : IsPiSubgroup (G := H) ({q} : Set Nat.Primes) (Q.subgroupOf H) :=
      hQfamP.2.1.subgroupOf hQ_le_H
    have hQsub_inv : IsInvariant (↥P) (↥H) (Q.subgroupOf H) := by
      simpa [N] using
        (isInvariant_subgroupOf_of_le_normalizer
          (A := P) (H := H) (K := Q) hPnormH hPnormQ hQ_le_H)
    obtain ⟨Q₂sub, hQ₂Hall, hQ₂inv, hQsub_le_Q₂sub⟩ :=
      proposition_1_5_b (G := ↥H) (A := ↥P) (hsolv := inferInstance) hcopPH
        ({q} : Set Nat.Primes) (Q.subgroupOf H) hQsub_pi hQsub_inv
    let Q₂ : Subgroup G := Q₂sub.map H.subtype
    have hQ₂_le_H : Q₂ ≤ H := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.property
    have hQ₂_pi : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q₂ := by
      simpa [Q₂] using (hQ₂Hall.isPiSubgroup).map H.subtype
    let : IsInvariant (↥P) (↥H) Q₂sub := hQ₂inv
    have hPnormQ₂ : P ≤ Subgroup.normalizer (Q₂ : Set G) := by
      refine subgroup_le_normalizer_of_conj_mem Q₂ P ?_
      intro p x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hyInv : p • y ∈ Q₂sub :=
        (IsInvariant.invariant (A := ↥P) (G := ↥H) (H := Q₂sub) p y).1 hy
      exact Subgroup.mem_map.mpr ⟨p • y, hyInv, by
        simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]⟩
    have hQ_le_Q₂ : Q ≤ Q₂ := by
      intro x hx
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hQ_le_H hx⟩, hQsub_le_Q₂sub (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
    have hQ₂famP : Q₂ ∈ section7HFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) := by
      exact ⟨le_top, hQ₂_pi, hPnormQ₂⟩
    have hQ₂_eq_Q : Q₂ = Q := hQ.2 Q₂ hQ_le_Q₂ hQ₂famP
    have hQ₂_subgroupOf_H : Q₂.subgroupOf H = Q₂sub := by
      change (Q₂sub.map H.subtype).subgroupOf H = Q₂sub
      exact Subgroup.comap_map_eq_self_of_injective
        (H := Q₂sub) (f := H.subtype) H.subtype_injective
    have hQHallH : IsHallSubgroup ({q} : Set Nat.Primes) (Q.subgroupOf H) := by
      have hQsub_eq : Q.subgroupOf H = Q₂sub := by
        calc
          Q.subgroupOf H = Q₂.subgroupOf H := by simp [hQ₂_eq_Q]
          _ = Q₂sub := hQ₂_subgroupOf_H
      simpa [hQsub_eq] using hQ₂Hall
    let NQ₁ : Subgroup G := N ⊓ Q₁
    have hNQ₁_le_H' : NQ₁ ≤ H := by
      simpa [NQ₁] using hNQ₁_le_H
    have hNQ₁_pi : IsPiSubgroup (G := H) ({q} : Set Nat.Primes) (NQ₁.subgroupOf H) := by
      have hNQ₁_piG : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) NQ₁ := by
        refine IsPiSubgroup.of_le ?_ (section7HStarFamily.mem_family hQ₁).2.1
        simp [NQ₁]
      exact hNQ₁_piG.subgroupOf hNQ₁_le_H'
    have hNQ₁_pgroup : IsPGroup q.val (NQ₁.subgroupOf H) :=
      isPGroup_of_isPiSubgroup_singleton hNQ₁_pi
    have hQsub_pgroup : IsPGroup q.val (Q.subgroupOf H) :=
      isPGroup_of_isPiSubgroup_singleton hQHallH.isPiSubgroup
    have hQsub_not_dvd_index : ¬ q.val ∣ (Q.subgroupOf H).index := by
      intro hidx
      exact (hQHallH.p_in_pi_of_p_dvd_index q hidx) (by simp)
    let SQ : Sylow q.val H := IsPGroup.toSylow (p := q.val) hQsub_pgroup hQsub_not_dvd_index
    obtain ⟨S, hNQ₁_le_S⟩ := IsPGroup.exists_le_sylow (p := q.val) hNQ₁_pgroup
    have hcard_NQ₁_sub_le :
        Nat.card (NQ₁.subgroupOf H) ≤ Nat.card (S : Subgroup H) :=
      Subgroup.card_le_of_le hNQ₁_le_S
    have hcard_S_eq_Qsub :
        Nat.card (S : Subgroup H) = Nat.card (Q.subgroupOf H) := by
      calc
        Nat.card (S : Subgroup H) = q.val ^ Nat.factorization (Nat.card H) q.val := by
          simpa using Sylow.card_eq_multiplicity S
        _ = Nat.card (SQ : Subgroup H) := by
          symm
          simpa using Sylow.card_eq_multiplicity SQ
        _ = Nat.card (Q.subgroupOf H) := by
          simp [SQ, IsPGroup.toSylow_coe]
    have hcard_NQ₁_le_Q : Nat.card NQ₁ ≤ Nat.card Q := by
      have hcard_NQ₁_eq :
          Nat.card (NQ₁.subgroupOf H) = Nat.card NQ₁ := by
        simpa [NQ₁] using
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (H := NQ₁) (K := H) hNQ₁_le_H').toEquiv
      have hcard_Q_eq :
          Nat.card (Q.subgroupOf H) = Nat.card Q := by
        simpa using
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (H := Q) (K := H) hQ_le_H).toEquiv
      rw [← hcard_NQ₁_eq, ← hcard_Q_eq]
      exact hcard_NQ₁_sub_le.trans_eq hcard_S_eq_Qsub
    have hNQ₁_eq_Q : Q = NQ₁ := by
      exact Subgroup.eq_of_le_of_card_ge hQ_le_NQ₁ hcard_NQ₁_le_Q
    have hQ_eq_Q₁ : Q = Q₁ := by
      by_contra hQeqQ₁
      have hQ₁_pi : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q₁ :=
        (section7HStarFamily.mem_family hQ₁).2.1
      have hnc : NormalizerCondition ↥Q₁ :=
        normalizerCondition_of_isPiSubgroup_singleton hQ₁_pi
      have hQsub_ne_top : Q.subgroupOf Q₁ ≠ ⊤ := by
        intro htop
        have hQ₁_le_Q : Q₁ ≤ Q := Subgroup.subgroupOf_eq_top.mp htop
        exact hQeqQ₁ (le_antisymm hQ_le_Q₁ hQ₁_le_Q)
      have hQsub_lt_top : Q.subgroupOf Q₁ < ⊤ :=
        lt_top_iff_ne_top.mpr hQsub_ne_top
      have hlt_norm :
          Q.subgroupOf Q₁ <
            Subgroup.normalizer ((Q.subgroupOf Q₁ : Subgroup Q₁) : Set Q₁) :=
        hnc _ hQsub_lt_top
      have hnorm_eq :
          Subgroup.normalizer ((Q.subgroupOf Q₁ : Subgroup Q₁) : Set Q₁) =
            Q.subgroupOf Q₁ := by
        calc
          Subgroup.normalizer ((Q.subgroupOf Q₁ : Subgroup Q₁) : Set Q₁)
              = NQ₁.subgroupOf Q₁ := by
                  symm
                  calc
                    NQ₁.subgroupOf Q₁ = N.subgroupOf Q₁ := by simp [NQ₁]
                    _ = Subgroup.normalizer ((Q.subgroupOf Q₁ : Subgroup Q₁) : Set Q₁) := by
                        change (Subgroup.normalizer (Q : Set G)).subgroupOf Q₁ =
                          Subgroup.normalizer ((Q.subgroupOf Q₁ : Subgroup Q₁) : Set Q₁)
                        exact Subgroup.subgroupOf_normalizer_eq (H := Q) (N := Q₁) hQ_le_Q₁
          _ = Q.subgroupOf Q₁ := by simp [NQ₁, hNQ₁_eq_Q]
      exact hlt_norm.ne hnorm_eq.symm
    simpa [hQ_eq_Q₁] using hQ₁

private theorem CFSG.mem_normalizer_of_conjBy_eq_self
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hconj : H.conjBy g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hy' : g * y * g⁻¹ ∈ H.conjBy g :=
      Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    simpa [hconj] using hy'
  · intro hy
    have hy' : g * y * g⁻¹ ∈ H.conjBy g := by
      simpa [hconj] using hy
    rcases Subgroup.mem_map.mp hy' with ⟨z, hz, hzEq⟩
    have hzy : z = y := by
      exact (MulAut.conj g).injective <| by
        simpa [MulAut.conj_apply, mul_assoc] using hzEq
    simpa [hzy] using hz

private theorem CFSG.theorem_7_4_normal_case
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {A P : Subgroup G} (hA : Hypothesis7_1 A) (hAP : A ≤ P)
    {q : Nat.Primes} (hq : q ∉ subgroupPrimeSet A)
    (hPproper : P ≠ ⊤) [hAPnorm : (A.subgroupOf P).Normal]
    (hPπ : IsPiSubgroup (subgroupPrimeSet A) P)
    (htrans : ConjugationActionTransitiveOn (section7K A)
      (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)))
    (hno : ∀ B : Subgroup G, A < B → B < P → (B.subgroupOf P).Normal → False) :
    subgroupCentralizerIn (section7K A) P =
        piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) ∧
      ConjugationActionTransitiveOn
        (piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)))
        (section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes)) ∧
      section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) ⊆
        section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) ∧
      ∀ Q ∈ section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes),
        P ⊓ ambientDerivedSubgroup (Subgroup.normalizer (P : Set G)) ≤
          ambientDerivedSubgroup (Subgroup.normalizer (Q : Set G)) ∧
        ((Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) =
          piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) *
            ((Subgroup.normalizer (P : Set G)) ⊓ Subgroup.normalizer (Q : Set G)) := by
  classical
  have hparta :
      subgroupCentralizerIn (section7K A) P =
        piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) :=
    theorem_7_4_part_a hA (isSubnormalIn_of_normal_subgroupOf hAP)
  have hsubset :
      section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) ⊆
        section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
    intro Q hQ
    exact
      mem_section7HStarFamily_A_of_mem_section7HStarFamily_P_of_normal_no_intermediate
        hA hAP hq hPproper hPπ htrans hno hQ
  have htransP :
      ConjugationActionTransitiveOn
        (subgroupCentralizerIn (section7K A) P)
        (section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes)) := by
    intro Q₁ hQ₁ Q₂ hQ₂
    have hQ₁famP : Q₁ ∈ section7HFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) :=
      section7HStarFamily.mem_family hQ₁
    have hQ₂famP : Q₂ ∈ section7HFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) :=
      section7HStarFamily.mem_family hQ₂
    have hQ₁A : Q₁ ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := hsubset hQ₁
    have hQ₂A : Q₂ ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := hsubset hQ₂
    by_cases hQ₂bot : Q₂ = ⊥
    · have hQ₁bot : Q₁ = ⊥ := by
        have hQ₂_le_Q₁ : Q₂ ≤ Q₁ := by
          simp [hQ₂bot]
        have hQ₁_eq_Q₂ := hQ₂.2 Q₁ hQ₂_le_Q₁ hQ₁famP
        rw [hQ₂bot] at hQ₁_eq_Q₂
        exact hQ₁_eq_Q₂
      refine ⟨1, ?_⟩
      simpa [hQ₁bot, hQ₂bot] using (Subgroup.conjBy_one (⊥ : Subgroup G)).symm
    · have hQ₂_ne_top : Q₂ ≠ ⊤ :=
        ne_top_of_isPiSubgroup_singleton_ne_bot hQ₂famP.2.1 hQ₂bot
      have hNQ₂proper : Subgroup.normalizer (Q₂ : Set G) ≠ ⊤ :=
        normalizer_ne_top_of_ne_bot_ne_top hQ₂bot hQ₂_ne_top
      have hPnormA : P ≤ Subgroup.normalizer (A : Set G) :=
        Subgroup.le_normalizer_of_normal_subgroupOf hAP
      obtain ⟨k, hk⟩ := htrans Q₁ hQ₁A Q₂ hQ₂A
      let KP : Subgroup G := section7K A ⊔ P
      let N : Subgroup G := KP ⊓ Subgroup.normalizer (Q₂ : Set G)
      have hN_le_normQ₂ : N ≤ Subgroup.normalizer (Q₂ : Set G) := inf_le_right
      have hNproper : N ≠ ⊤ := by
        intro hNtop
        apply hNQ₂proper
        apply top_unique
        intro x hx
        have hxN : x ∈ N := by simp [hNtop]
        exact hN_le_normQ₂ hxN
      have : Group.IsSolvable N := solvable_of_proper_subgroup hNproper
      let Nsub : Subgroup KP := N.subgroupOf KP
      let eN : Nsub ≃* N := Subgroup.subgroupOfEquivOfLe (H := N) (K := KP) inf_le_left
      have hsolvNsub : Group.IsSolvable Nsub :=
        Group.isSolvable_of_surjective (f := eN.symm.toMonoidHom) eN.symm.surjective
      have hPHallKP : IsHallSubgroup (subgroupPrimeSet A) (P.subgroupOf KP) := by
        simpa [KP] using
          isHallSubgroup_subgroupOf_sup_section7K
            (A := A) (P := P) hPnormA hPπ
      have hPsubKP_le_Nsub : P.subgroupOf KP ≤ Nsub := by
        intro x hx
        change ((x : KP) : G) ∈ N
        exact ⟨x.2, hQ₂famP.2.2 (by simpa [Subgroup.mem_subgroupOf] using hx)⟩
      let kKP : KP := ⟨k, Subgroup.mem_sup_left k.property⟩
      let PkKP : Subgroup KP := (P.subgroupOf KP).map (MulAut.conj kKP).toMonoidHom
      have hPkKP_hall : IsHallSubgroup (subgroupPrimeSet A) PkKP := by
        simpa [PkKP] using hPHallKP.map_conj kKP
      have hPkKP_map_eq : PkKP.map KP.subtype = P.conjBy (k : G) := by
        simpa [PkKP, Subgroup.conjBy] using
          map_subgroupOf_map_conj_eq (K0 := KP) (K := P) le_sup_right kKP
      have hPnormQ₁ : P ≤ Subgroup.normalizer (Q₁ : Set G) := hQ₁famP.2.2
      have hPk_le_normQ₂ : P.conjBy (k : G) ≤ Subgroup.normalizer (Q₂ : Set G) := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨p, hpP, rfl⟩
        rw [hk, Subgroup.mem_normalizer_iff]
        intro z
        constructor
        · intro hz
          rcases Subgroup.mem_map.mp hz with ⟨y, hyQ₁, rfl⟩
          have hpy : p * y * p⁻¹ ∈ Q₁ :=
            (Subgroup.mem_normalizer_iff.mp (hPnormQ₁ hpP) y).1 hyQ₁
          exact Subgroup.mem_map.mpr ⟨p * y * p⁻¹, hpy, by simp [mul_assoc]⟩
        · intro hz
          have hpInvNormQ₁ : p⁻¹ ∈ Subgroup.normalizer (Q₁ : Set G) :=
            (Subgroup.normalizer (Q₁ : Set G)).inv_mem (hPnormQ₁ hpP)
          rcases Subgroup.mem_map.mp hz with ⟨y, hyQ₁, hyEq⟩
          have hyEq' : y = p * ((k : G)⁻¹ * z * (k : G)) * p⁻¹ := by
            apply (MulAut.conj (k : G)).injective
            simpa [MulAut.conj_apply, mul_assoc] using hyEq
          have hpy : p⁻¹ * y * p ∈ Q₁ := by
            simpa [inv_inv] using
              (Subgroup.mem_normalizer_iff.mp hpInvNormQ₁ y).1 hyQ₁
          have hyEq'' : p⁻¹ * y * p = (k : G)⁻¹ * z * (k : G) := by
            calc
              p⁻¹ * y * p = p⁻¹ * (p * ((k : G)⁻¹ * z * (k : G)) * p⁻¹) * p := by
                  rw [hyEq']
              _ = (k : G)⁻¹ * z * (k : G) := by simp [mul_assoc]
          exact Subgroup.mem_map.mpr ⟨p⁻¹ * y * p, hpy, by
            calc
              (k : G) * (p⁻¹ * y * p) * (k : G)⁻¹ = (k : G) * ((k : G)⁻¹ * z * (k : G)) * (k : G)⁻¹ := by
                  rw [hyEq'']
              _ = z := by simp [mul_assoc]⟩
      have hPkKP_le_Nsub : PkKP ≤ Nsub := by
        intro x hx
        change ((x : KP) : G) ∈ N
        have hxPkKP : ((x : KP) : G) ∈ PkKP.map KP.subtype :=
          Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        have hxPk : ((x : KP) : G) ∈ P.conjBy (k : G) := by
          simpa [hPkKP_map_eq] using hxPkKP
        exact ⟨x.2, hPk_le_normQ₂ hxPk⟩
      let P0 : Subgroup Nsub := (P.subgroupOf KP).subgroupOf Nsub
      let Pk0 : Subgroup Nsub := PkKP.subgroupOf Nsub
      have hP0_hall : IsHallSubgroup (subgroupPrimeSet A) P0 := by
        simpa [P0] using hPHallKP.subgroupOf hPsubKP_le_Nsub
      have hPk0_hall : IsHallSubgroup (subgroupPrimeSet A) Pk0 := by
        simpa [Pk0] using hPkKP_hall.subgroupOf hPkKP_le_Nsub
      let : MulDistribMulAction Unit Nsub := {
        smul := fun _ x => x
        one_smul := fun _ => rfl
        mul_smul := fun _ _ _ => rfl
        smul_mul := fun _ _ _ => rfl
        smul_one := fun _ => rfl }
      have hcopUnitNsub : Nat.Coprime (Nat.card Unit) (Nat.card Nsub) := by simp
      have hP0inv : IsInvariant Unit Nsub P0 := by
        refine ⟨?_⟩
        intro _ y
        simp
      have hPk0inv : IsInvariant Unit Nsub Pk0 := by
        refine ⟨?_⟩
        intro _ y
        simp
      obtain ⟨x, _hxfix, hxconj⟩ :=
        proposition_1_5_c (G := ↥Nsub) (A := Unit) hsolvNsub hcopUnitNsub
          (subgroupPrimeSet A) P0 Pk0 hP0_hall hPk0_hall hP0inv hPk0inv
      let φ : Nsub →* G := KP.subtype.comp Nsub.subtype
      have hφP0 : P0.map φ = P := by
        calc
          P0.map φ = (P0.map Nsub.subtype).map KP.subtype := by
            simp [φ, Subgroup.map_map]
          _ = (P.subgroupOf KP).map KP.subtype := by
            rw [Subgroup.map_subgroupOf_eq_of_le hPsubKP_le_Nsub]
          _ = P := by
            simpa using Subgroup.map_subgroupOf_eq_of_le (H := P) (K := KP) le_sup_right
      have hφPk0 : Pk0.map φ = P.conjBy (k : G) := by
        calc
          Pk0.map φ = (Pk0.map Nsub.subtype).map KP.subtype := by
            simp [φ, Subgroup.map_map]
          _ = PkKP.map KP.subtype := by
            rw [Subgroup.map_subgroupOf_eq_of_le hPkKP_le_Nsub]
          _ = P.conjBy (k : G) := hPkKP_map_eq
      have hφP0conj :
          (P0.map (MulAut.conj x).toMonoidHom).map φ =
            P.conjBy ((((x : Nsub) : KP) : G)) := by
        calc
          (P0.map (MulAut.conj x).toMonoidHom).map φ =
              ((P0.map (MulAut.conj x).toMonoidHom).map Nsub.subtype).map KP.subtype := by
                simp [φ, Subgroup.map_map, MonoidHom.comp_assoc]
          _ = ((P.subgroupOf KP).map (MulAut.conj ((x : Nsub) : KP)).toMonoidHom).map KP.subtype := by
                exact congrArg (fun S : Subgroup KP => S.map KP.subtype) <|
                  map_subgroupOf_map_conj_eq
                    (K0 := Nsub) (K := P.subgroupOf KP) hPsubKP_le_Nsub x
          _ = P.conjBy ((((x : Nsub) : KP) : G)) := by
                simpa [Subgroup.conjBy] using
                  map_subgroupOf_map_conj_eq
                    (K0 := KP) (K := P) le_sup_right ((x : Nsub) : KP)
      have hφconj := congrArg (fun S : Subgroup Nsub => S.map φ) hxconj
      have hPk_eq_Px : P.conjBy (k : G) = P.conjBy ((((x : Nsub) : KP) : G)) := by
        change Subgroup.map φ Pk0 = Subgroup.map φ (Subgroup.map (MulAut.conj x).toMonoidHom P0) at hφconj
        rw [hφPk0, hφP0conj] at hφconj
        exact hφconj
      have hPnormK : P ≤ Subgroup.normalizer (section7K A : Set G) :=
        le_normalizer_section7K_of_le_normalizer hPnormA
      have hKP_le_normK : KP ≤ Subgroup.normalizer (section7K A : Set G) := by
        exact sup_le Subgroup.le_normalizer hPnormK
      have hKsub_norm : ((section7K A).subgroupOf KP).Normal := by
        simpa [KP] using
          (Subgroup.normal_subgroupOf_of_le_normalizer
            (H := KP) (N := section7K A) hKP_le_normK)
      let : ((section7K A).subgroupOf KP).Normal := hKsub_norm
      have hKsub_sup_top : (section7K A).subgroupOf KP ⊔ P.subgroupOf KP = ⊤ := by
        calc
          (section7K A).subgroupOf KP ⊔ P.subgroupOf KP =
              ((section7K A) ⊔ P).subgroupOf KP := by
                symm
                exact
                  Subgroup.subgroupOf_sup
                    (A := section7K A) (A' := P) (B := KP) le_sup_left le_sup_right
          _ = ⊤ := by simp [KP]
      have hxKP_sup : ((x : Nsub) : KP) ∈ (section7K A).subgroupOf KP ⊔ P.subgroupOf KP := by
          simp [hKsub_sup_top]
      rcases
          (Subgroup.mem_sup_of_normal_left
            (s := (section7K A).subgroupOf KP) (t := P.subgroupOf KP) (x := ((x : Nsub) : KP))).1
            hxKP_sup with
        ⟨gKP, hgKP, pKP, hpKP, hgp_eq⟩
      have hgK : ((gKP : KP) : G) ∈ section7K A := by
        simpa [Subgroup.mem_subgroupOf] using hgKP
      have hpP : ((pKP : KP) : G) ∈ P := by
        simpa [Subgroup.mem_subgroupOf] using hpKP
      let xG : G := (((x : Nsub) : KP) : G)
      let gG : G := ((gKP : KP) : G)
      let pG : G := ((pKP : KP) : G)
      have hx_eq : gG * pG = xG := by
        exact congrArg Subtype.val hgp_eq
      have hxNormQ₂ : xG ∈ Subgroup.normalizer (Q₂ : Set G) := by
        exact (show xG ∈ N from (x : Nsub).property).2
      have hpNormQ₂ : pG ∈ Subgroup.normalizer (Q₂ : Set G) := hQ₂famP.2.2 hpP
      have hg_eq : gG = xG * pG⁻¹ := by
        calc
          gG = gG * pG * pG⁻¹ := by simp [gG, pG, mul_assoc]
          _ = xG * pG⁻¹ := by simp [hx_eq]
      have hgNormQ₂ : gG ∈ Subgroup.normalizer (Q₂ : Set G) := by
        have hpInvNormQ₂ : pG⁻¹ ∈ Subgroup.normalizer (Q₂ : Set G) :=
          (Subgroup.normalizer (Q₂ : Set G)).inv_mem hpNormQ₂
        have hxmul : xG * pG⁻¹ ∈ Subgroup.normalizer (Q₂ : Set G) :=
          (Subgroup.normalizer (Q₂ : Set G)).mul_mem hxNormQ₂ hpInvNormQ₂
        simpa [hg_eq] using hxmul
      have hpNormP : pG ∈ Subgroup.normalizer (P : Set G) := P.le_normalizer hpP
      have hPx_eq_Pg : P.conjBy xG = P.conjBy gG := by
        simpa [xG, gG, pG, hx_eq, Subgroup.conjBy] using
          (map_conj_mul_right_eq_of_mem_normalizer
            (H := P) (g := gG) (x := ⟨pG, hpNormP⟩))
      have hPk_eq_Pg : P.conjBy (k : G) = P.conjBy gG := by
        rw [hPk_eq_Px, hPx_eq_Pg]
      have hQgInvNormQ₂ : gG⁻¹ ∈ Subgroup.normalizer (Q₂ : Set G) :=
        (Subgroup.normalizer (Q₂ : Set G)).inv_mem hgNormQ₂
      have hQ₂_conj_ginv : Q₂.conjBy gG⁻¹ = Q₂ := by
        have htmp : Q₂.conjBy gG⁻¹ = Q₂.conjBy (1 : G) := by
          simpa [Subgroup.conjBy] using
            (map_conj_mul_right_eq_of_mem_normalizer
              (H := Q₂) (g := (1 : G)) (x := ⟨gG⁻¹, hQgInvNormQ₂⟩))
        rw [Subgroup.conjBy_one] at htmp
        exact htmp
      have hPc_eq : P.conjBy (gG⁻¹ * (k : G)) = P := by
        calc
          P.conjBy (gG⁻¹ * (k : G)) = (P.conjBy (k : G)).conjBy gG⁻¹ := by
              rw [Subgroup.conjBy_conjBy]
          _ = (P.conjBy gG).conjBy gG⁻¹ := by rw [hPk_eq_Pg]
          _ = P.conjBy (1 : G) := by
              rw [Subgroup.conjBy_conjBy]
              simp
          _ = P := by rw [Subgroup.conjBy_one]
      have hcNormP : gG⁻¹ * (k : G) ∈ Subgroup.normalizer (P : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hy' : (gG⁻¹ * (k : G)) * y * (gG⁻¹ * (k : G))⁻¹ ∈ P.conjBy (gG⁻¹ * (k : G)) :=
            Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
          simpa [hPc_eq] using hy'
        · intro hy
          have hy' : (gG⁻¹ * (k : G)) * y * (gG⁻¹ * (k : G))⁻¹ ∈ P.conjBy (gG⁻¹ * (k : G)) := by
            simpa [hPc_eq] using hy
          rcases Subgroup.mem_map.mp hy' with ⟨z, hz, hzEq⟩
          have hzy : z = y := by
            exact (MulAut.conj (gG⁻¹ * (k : G))).injective <| by
              simpa [MulAut.conj_apply, mul_assoc] using hzEq
          simpa [hzy] using hz
      have hcK : gG⁻¹ * (k : G) ∈ section7K A := by
        exact (section7K A).mul_mem ((section7K A).inv_mem hgK) k.property
      have hcCent : gG⁻¹ * (k : G) ∈ subgroupCentralizerIn (section7K A) P :=
        mem_subgroupCentralizerIn_of_mem_section7K_of_mem_normalizer
          (A := A) (P := P) hPnormA hPπ hcK hcNormP
      refine ⟨⟨gG⁻¹ * (k : G), hcCent⟩, ?_⟩
      calc
        Q₂ = Q₂.conjBy gG⁻¹ := hQ₂_conj_ginv.symm
        _ = (Q₁.conjBy (k : G)).conjBy gG⁻¹ := by rw [hk]
        _ = Q₁.conjBy (gG⁻¹ * (k : G)) := by rw [Subgroup.conjBy_conjBy]
  constructor
  · exact hparta
  constructor
  · rw [← hparta]
    exact htransP
  constructor
  · exact hsubset
  · intro Q hQ
    let Np : Subgroup G := Subgroup.normalizer (P : Set G)
    let Nq : Subgroup G := Subgroup.normalizer (Q : Set G)
    let CK : Subgroup G := subgroupCentralizerIn (section7K A) P
    let L : Subgroup G := Np ⊓ Nq
    have hQfamP : Q ∈ section7HFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) :=
      section7HStarFamily.mem_family hQ
    have hP_le_Nq : P ≤ Nq := by
      simpa [Nq] using hQfamP.2.2
    have hCK_le_Np : CK ≤ Np := by
      intro x hx
      exact (centralizer_le_normalizer (R := P)) hx.2
    have hfactorCK : ((Np : Subgroup G) : Set G) = (CK : Set G) * (L : Set G) := by
      ext x
      constructor
      · intro hxNp
        let Qx : Subgroup G := Q.conjBy x
        have hQx :
            Q.conjBy x ∈ section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) :=
          mem_section7HStarFamily_top_conjBy_of_mem_normalizer (A := P) hxNp hQ
        let c : subgroupCentralizerIn (section7K A) P :=
          Classical.choose (htransP Q hQ Qx (by simpa [Qx] using hQx))
        have hc : (c : G) ∈ subgroupCentralizerIn (section7K A) P := c.property
        have hQc : Q.conjBy x = Q.conjBy (c : G) :=
          Classical.choose_spec (htransP Q hQ Qx (by simpa [Qx] using hQx))
        let l : G := (c : G)⁻¹ * x
        have hlNq_eq : Q.conjBy l = Q := by
          calc
            Q.conjBy l = (Q.conjBy x).conjBy (c : G)⁻¹ := by
                simpa [l] using (Subgroup.conjBy_conjBy Q x ((c : G)⁻¹)).symm
            _ = (Q.conjBy (c : G)).conjBy (c : G)⁻¹ := by rw [hQc]
            _ = Q.conjBy (1 : G) := by
                rw [Subgroup.conjBy_conjBy]
                simp
            _ = Q := by rw [Subgroup.conjBy_one]
        have hlNq : l ∈ Nq :=
          mem_normalizer_of_conjBy_eq_self hlNq_eq
        have hlNp : l ∈ Np := by
          have hcNp : (c : G) ∈ Np := hCK_le_Np hc
          have hcInvNp : (c : G)⁻¹ ∈ Np := Np.inv_mem hcNp
          exact Np.mul_mem hcInvNp hxNp
        exact Set.mem_mul.mpr ⟨c, hc, l, ⟨hlNp, hlNq⟩, by
          simp [l]⟩
      · rintro ⟨c, hc, l, hl, rfl⟩
        exact Np.mul_mem (hCK_le_Np hc) hl.1
    have hfactor_pi :
        ((Np : Subgroup G) : Set G) =
          (piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) : Set G) *
            (L : Set G) := by
      simpa [CK, hparta] using hfactorCK
    by_cases hPbot : P = ⊥
    · refine ⟨?_, ?_⟩
      · simp [hPbot]
      · change ((Np : Subgroup G) : Set G) =
          (piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) : Set G) *
            (L : Set G)
        exact hfactor_pi
    · have hNp_proper : Np ≠ ⊤ :=
        normalizer_ne_top_of_ne_bot_ne_top hPbot hPproper
      have : Group.IsSolvable Np := solvable_of_proper_subgroup hNp_proper
      have hNp_le_normPiCore :
          Np ≤
            Subgroup.normalizer
              (piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) : Set G) := by
        refine
          le_normalizer_piCoreIn_of_le_normalizer
            (π := (subgroupPrimeSet A)ᶜ) (H := Subgroup.centralizer (P : Set G)) (P := Np) ?_
        intro n hn
        rw [Subgroup.mem_normalizer_iff]
        intro c
        constructor
        · intro hc
          rw [Subgroup.mem_centralizer_iff] at hc ⊢
          intro p hp
          have hninv : n⁻¹ ∈ Np := Np.inv_mem hn
          have hnp : n⁻¹ * p * n ∈ P := by
            simpa using (Subgroup.mem_normalizer_iff.mp hninv p).1 hp
          have hcnp : (c : G) * (n⁻¹ * p * n) = (n⁻¹ * p * n) * c := (hc _ hnp).symm
          have htmp := congrArg (fun t : G => n * t * n⁻¹) hcnp
          simpa [mul_assoc] using htmp.symm
        · intro hc
          have hninv : n⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
            (Subgroup.normalizer (P : Set G)).inv_mem hn
          rw [Subgroup.mem_centralizer_iff] at hc ⊢
          intro p hp
          have hninvp : n * p * n⁻¹ ∈ P :=
            (Subgroup.mem_normalizer_iff.mp hn p).1 hp
          have hcninvp : (n * c * n⁻¹ : G) * (n * p * n⁻¹) = (n * p * n⁻¹) * (n * c * n⁻¹) :=
            (hc _ hninvp).symm
          have htmp := congrArg (fun t : G => n⁻¹ * t * n) hcninvp
          simpa [mul_assoc] using htmp.symm
      have hCKsub_norm : (CK.subgroupOf Np).Normal := by
        simpa [CK, hparta] using
          Subgroup.normal_subgroupOf_of_le_normalizer
            (H := Np) (N := piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)))
            hNp_le_normPiCore
      let : (CK.subgroupOf Np).Normal := hCKsub_norm
      have hL_le_Np : L ≤ Np := inf_le_left
      have hL_le_Nq : L ≤ Nq := inf_le_right
      have hKU_top : CK.subgroupOf Np ⊔ L.subgroupOf Np = ⊤ := by
        apply top_unique
        intro x hx
        have hxNp : ((x : Np) : G) ∈ Np := x.property
        have hxfactor : ((x : Np) : G) ∈ (CK : Set G) * (L : Set G) := by
          rw [← hfactorCK]
          exact hxNp
        rcases Set.mem_mul.mp hxfactor with ⟨c, hc, l, hl, hcl_eq⟩
        have hcsub : (⟨c, hCK_le_Np hc⟩ : Np) ∈ CK.subgroupOf Np := by
          simpa [Subgroup.mem_subgroupOf] using hc
        have hlsub : (⟨l, hl.1⟩ : Np) ∈ L.subgroupOf Np := by
          simpa [Subgroup.mem_subgroupOf] using hl
        have hmul : (⟨c, hCK_le_Np hc⟩ : Np) * ⟨l, hl.1⟩ = x := by
          apply Subtype.ext
          simpa using hcl_eq
        rw [← hmul]
        exact Subgroup.mul_mem_sup hcsub hlsub
      have hPsub_le_Lsub : P.subgroupOf Np ≤ L.subgroupOf Np := by
        intro x hx
        change ((x : Np) : G) ∈ L
        exact ⟨x.2, hP_le_Nq (by simpa [Subgroup.mem_subgroupOf] using hx)⟩
      have hCK_pi' : IsPiSubgroup (G := G) (subgroupPrimeSet A)ᶜ CK := by
        simpa [CK, hparta] using
          piCoreIn_isPiSubgroup
            (G := G) (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G))
      have hcopPC : Nat.Coprime (Nat.card (P.subgroupOf Np)) (Nat.card (CK.subgroupOf Np)) := by
        have hcop : Nat.Coprime (Nat.card P) (Nat.card CK) := by
          refine Nat.coprime_of_dvd ?_
          intro p hpPrime hpPcard hpCKcard
          let p' : Nat.Primes := ⟨p, hpPrime⟩
          have hp_in : p' ∈ subgroupPrimeSet A := hPπ p' hpPcard
          have hp_notin : p' ∉ subgroupPrimeSet A := by
            simpa using hCK_pi' p' hpCKcard
          exact hp_notin hp_in
        simpa [natCard_subgroupOf_eq P Np Subgroup.le_normalizer,
          natCard_subgroupOf_eq CK Np hCK_le_Np] using hcop
      have h65a :
          P.subgroupOf Np ⊓ derivedSubgroup Np =
            P.subgroupOf Np ⊓ ⁅L.subgroupOf Np, L.subgroupOf Np⁆ := by
        exact
          lemma_6_5_a
            (G := Np) (K := CK.subgroupOf Np) (U := L.subgroupOf Np) (H := P.subgroupOf Np)
            hKU_top hPsub_le_Lsub hcopPC
      have h65a_map :
          ((P.subgroupOf Np ⊓ derivedSubgroup Np).map Np.subtype) =
            ((P.subgroupOf Np ⊓ ⁅L.subgroupOf Np, L.subgroupOf Np⁆).map Np.subtype) :=
        congrArg (fun S : Subgroup Np => S.map Np.subtype) h65a
      have hleft_eq :
          ((P.subgroupOf Np ⊓ derivedSubgroup Np).map Np.subtype) =
            P ⊓ ambientDerivedSubgroup Np := by
        rw [Subgroup.map_inf_eq _ _ Np.subtype Np.subtype_injective,
          Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer]
        rfl
      have hcomm_map_eq_Np :
          (⁅L.subgroupOf Np, L.subgroupOf Np⁆).map Np.subtype = ⁅L, L⁆ := by
        simpa using commutator_subgroupOf_map_eq Np L L hL_le_Np hL_le_Np
      have hcomm_le_ambientNq :
          (⁅L.subgroupOf Np, L.subgroupOf Np⁆).map Np.subtype ≤ ambientDerivedSubgroup Nq := by
        rw [hcomm_map_eq_Np]
        have hcomm_map_eq_Nq :
            (⁅L.subgroupOf Nq, L.subgroupOf Nq⁆).map Nq.subtype = ⁅L, L⁆ := by
          simpa using commutator_subgroupOf_map_eq Nq L L hL_le_Nq hL_le_Nq
        rw [← hcomm_map_eq_Nq]
        have hcomm_le_derNq : ⁅L.subgroupOf Nq, L.subgroupOf Nq⁆ ≤ derivedSubgroup Nq := by
          change ⁅L.subgroupOf Nq, L.subgroupOf Nq⁆ ≤ ⁅(⊤ : Subgroup Nq), ⊤⁆
          exact Subgroup.commutator_mono le_top le_top
        exact Subgroup.map_mono hcomm_le_derNq
      have hright_le :
          ((P.subgroupOf Np ⊓ ⁅L.subgroupOf Np, L.subgroupOf Np⁆).map Np.subtype) ≤
            ambientDerivedSubgroup Nq := by
        rw [Subgroup.map_inf_eq _ _ Np.subtype Np.subtype_injective,
          Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer]
        exact inf_le_right.trans hcomm_le_ambientNq
      have hder : P ⊓ ambientDerivedSubgroup Np ≤ ambientDerivedSubgroup Nq := by
        rw [← hleft_eq, h65a_map]
        exact hright_le
      exact ⟨by simpa [Np, Nq] using hder, by simpa [Np, Nq, L] using hfactor_pi⟩

public theorem CFSG.theorem_7_4_core
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {A P : Subgroup G} (hA : Hypothesis7_1 A)
    {q : Nat.Primes} (hq : q ∉ subgroupPrimeSet A)
    (hPproper : P ≠ ⊤) (hAsubnormal : IsSubnormalIn A P)
    (hPπ : IsPiSubgroup (subgroupPrimeSet A) P)
    (htrans : ConjugationActionTransitiveOn (section7K A)
      (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes))) :
    subgroupCentralizerIn (section7K A) P =
        piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) ∧
      ConjugationActionTransitiveOn
        (piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)))
        (section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes)) ∧
      section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) ⊆
        section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) ∧
      ∀ Q ∈ section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes),
        P ⊓ ambientDerivedSubgroup (Subgroup.normalizer (P : Set G)) ≤
          ambientDerivedSubgroup (Subgroup.normalizer (Q : Set G)) ∧
        ((Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) =
          piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) *
            ((Subgroup.normalizer (P : Set G)) ⊓ Subgroup.normalizer (Q : Set G)) := by
  classical
  have hcard_lt_of_lt :
      ∀ {H K : Subgroup G}, H < K → Nat.card H < Nat.card K := by
    intro H K hHK
    exact natCard_lt_of_subgroup_lt hHK
  let T : ℕ → Prop := fun n =>
    ∀ {A P : Subgroup G}, Hypothesis7_1 A →
      q ∉ subgroupPrimeSet A →
      P ≠ ⊤ →
      IsSubnormalIn A P →
      IsPiSubgroup (subgroupPrimeSet A) P →
      ConjugationActionTransitiveOn
        (section7K A) (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)) →
      Nat.card P - Nat.card A = n →
      subgroupCentralizerIn (section7K A) P =
          piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) ∧
        ConjugationActionTransitiveOn
          (piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)))
          (section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes)) ∧
        section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) ⊆
          section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) ∧
        ∀ Q ∈ section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes),
          P ⊓ ambientDerivedSubgroup (Subgroup.normalizer (P : Set G)) ≤
            ambientDerivedSubgroup (Subgroup.normalizer (Q : Set G)) ∧
          ((Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) =
            piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) *
              ((Subgroup.normalizer (P : Set G)) ⊓ Subgroup.normalizer (Q : Set G))
  have hT : ∀ n, T n := by
    intro n
    refine Nat.strong_induction_on (p := T) n ?_
    intro n ih A P hA hq hPproper hAsubnormal hPπ htrans hmeasure
    by_cases hno : ∀ B : Subgroup G, A < B → B < P → (B.subgroupOf P).Normal → False
    · have hAPnorm : (A.subgroupOf P).Normal := by
        rcases hAsubnormal.normal_or_exists_intermediate with hnorm | ⟨B, hAB, hBP, _hAsubB, hBnorm⟩
        · exact hnorm
        · exact False.elim (hno B hAB hBP hBnorm)
      let : (A.subgroupOf P).Normal := hAPnorm
      exact theorem_7_4_normal_case hA hAsubnormal.le hq hPproper hPπ htrans hno
    · have hexB : ∃ B : Subgroup G, A < B ∧ B < P ∧ (B.subgroupOf P).Normal := by
        by_contra h
        apply hno
        intro B hAB hBP hBnorm
        exact h ⟨B, hAB, hBP, hBnorm⟩
      have hstep :
          ∀ {B : Subgroup G}, A < B → B < P → IsSubnormalIn A B → (B.subgroupOf P).Normal →
            subgroupCentralizerIn (section7K A) P =
                piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) ∧
              ConjugationActionTransitiveOn
                (piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)))
                (section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes)) ∧
              section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) ⊆
                section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) ∧
              ∀ Q ∈ section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes),
                P ⊓ ambientDerivedSubgroup (Subgroup.normalizer (P : Set G)) ≤
                  ambientDerivedSubgroup (Subgroup.normalizer (Q : Set G)) ∧
                ((Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) =
                  piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) *
                    ((Subgroup.normalizer (P : Set G)) ⊓ Subgroup.normalizer (Q : Set G)) := by
        intro B hAB hBP hAsubB hBnorm
        have hBproper : B ≠ ⊤ := ne_top_of_le_ne_top hPproper hBP.1
        have hBπ : IsPiSubgroup (G := G) (subgroupPrimeSet A) B :=
          IsPiSubgroup.of_le hBP.1 hPπ
        have hπeq : subgroupPrimeSet B = subgroupPrimeSet A :=
          subgroupPrimeSet_eq_of_le_isPiSubgroup hAB.1 hBπ
        have hqB : q ∉ subgroupPrimeSet B := by
          simpa [hπeq] using hq
        have hcardA_lt_B : Nat.card A < Nat.card B := hcard_lt_of_lt hAB
        have hcardB_lt_P : Nat.card B < Nat.card P := hcard_lt_of_lt hBP
        have hmeasureAB : Nat.card B - Nat.card A < n := by
          rw [← hmeasure]
          omega
        have hmeasureBP : Nat.card P - Nat.card B < n := by
          rw [← hmeasure]
          omega
        have hABres :=
          ih (Nat.card B - Nat.card A) hmeasureAB hA hq hBproper hAsubB hBπ htrans rfl
        have hB : Hypothesis7_1 B :=
          hypothesis7_1_of_le_isPiSubgroup hA hAB.1 hBproper hBπ
        let : (B.subgroupOf P).Normal := hBnorm
        have hBsubP : IsSubnormalIn B P := isSubnormalIn_of_normal_subgroupOf hBP.1
        have hPπB : IsPiSubgroup (G := G) (subgroupPrimeSet B) P := by
          simpa [hπeq] using hPπ
        have htransB :
            ConjugationActionTransitiveOn
              (section7K B) (section7HStarFamily (⊤ : Subgroup G) B ({q} : Set Nat.Primes)) := by
          simpa [section7K, hπeq] using hABres.2.1
        have hBPres :=
          ih (Nat.card P - Nat.card B) hmeasureBP hB hqB hPproper hBsubP hPπB htransB rfl
        have hKB_eq : section7K B = subgroupCentralizerIn (section7K A) B := by
          simpa [section7K, hπeq] using hABres.1.symm
        have hcentP_eq :
            subgroupCentralizerIn (section7K B) P =
              subgroupCentralizerIn (section7K A) P := by
          ext x
          constructor
          · intro hx
            rcases hx with ⟨hxKB, hxCP⟩
            have hxCB : x ∈ Subgroup.centralizer (B : Set G) := by
              rw [Subgroup.mem_centralizer_iff]
              intro b hb
              exact (Subgroup.mem_centralizer_iff.mp hxCP) b (hBP.1 hb)
            have hxKAB : x ∈ subgroupCentralizerIn (section7K A) B := by
              simpa [hKB_eq, subgroupCentralizerIn] using hxKB
            exact ⟨hxKAB.1, hxCP⟩
          · intro hx
            rcases hx with ⟨hxKA, hxCP⟩
            have hxCB : x ∈ Subgroup.centralizer (B : Set G) := by
              rw [Subgroup.mem_centralizer_iff]
              intro b hb
              exact (Subgroup.mem_centralizer_iff.mp hxCP) b (hBP.1 hb)
            have hxKAB : x ∈ subgroupCentralizerIn (section7K A) B := ⟨hxKA, hxCB⟩
            have hxKB : x ∈ section7K B := by
              simpa [hKB_eq, subgroupCentralizerIn] using hxKAB
            exact ⟨hxKB, hxCP⟩
        have hsubsetPA :
            section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) ⊆
              section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
          (hBPres.2.2.1).trans (hABres.2.2.1)
        exact ⟨by
            calc
              subgroupCentralizerIn (section7K A) P = subgroupCentralizerIn (section7K B) P :=
                hcentP_eq.symm
              _ =
                  piCoreIn (subgroupPrimeSet B)ᶜ (Subgroup.centralizer (P : Set G)) := hBPres.1
              _ =
                  piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) := by
                    simp [hπeq],
          by simpa [section7K, hπeq] using hBPres.2.1,
          hsubsetPA,
          by simpa [hπeq] using hBPres.2.2.2⟩
      rcases hAsubnormal.normal_or_exists_intermediate with hAPnorm | ⟨B, hAB, hBP, hAsubB, hBnorm⟩
      · obtain ⟨B, hAB, hBP, hBnorm⟩ := hexB
        let : (A.subgroupOf P).Normal := hAPnorm
        have hP_le_normA : P ≤ Subgroup.normalizer (A : Set G) :=
          Subgroup.le_normalizer_of_normal_subgroupOf hAsubnormal.le
        have hAnormB : (A.subgroupOf B).Normal := by
          exact Subgroup.normal_subgroupOf_of_le_normalizer
            (H := B) (N := A) (hBP.1.trans hP_le_normA)
        let : (A.subgroupOf B).Normal := hAnormB
        have hAsubB : IsSubnormalIn A B := isSubnormalIn_of_normal_subgroupOf hAB.1
        exact hstep hAB hBP hAsubB hBnorm
      · exact hstep hAB hBP hAsubB hBnorm
  exact hT (Nat.card P - Nat.card A) hA hq hPproper hAsubnormal hPπ htrans rfl


end

/-! # Theorem 7.4 from BG Section 7 -/

open scoped Pointwise

section

variable {G : Type*} [Group G] [Finite G]

public theorem CFSG.theorem_7_4
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {A P : Subgroup G} (hA : Hypothesis7_1 A)
    {q : Nat.Primes} (hq : q ∉ subgroupPrimeSet A)
    (hPproper : P ≠ ⊤) (hAsubnormal : IsSubnormalIn A P)
    (hPπ : IsPiSubgroup (subgroupPrimeSet A) P)
    (htrans : ConjugationActionTransitiveOn (section7K A)
      (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes))) :
    subgroupCentralizerIn (section7K A) P =
        piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) ∧
      ConjugationActionTransitiveOn
        (piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)))
        (section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes)) ∧
      section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes) ⊆
        section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) ∧
      ∀ Q ∈ section7HStarFamily (⊤ : Subgroup G) P ({q} : Set Nat.Primes),
        P ⊓ ambientDerivedSubgroup (Subgroup.normalizer (P : Set G)) ≤
          ambientDerivedSubgroup (Subgroup.normalizer (Q : Set G)) ∧
        ((Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) =
          piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (P : Set G)) *
            ((Subgroup.normalizer (P : Set G)) ⊓ Subgroup.normalizer (Q : Set G)) := by
  simpa using
    (theorem_7_4_core (G := G) (A := A) (P := P) hA hq hPproper hAsubnormal hPπ htrans)

end
