module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma103
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection8.theorem_8_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Lemma 10.4

This file formalizes the local normalizer calculation `(10E)` and isolates
Peterfalvi `[II1; 4.5]` as its exact implication-shaped source boundary.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The literal conclusion package of Peterfalvi `[II1; 4.5]`. -/
public structure II1Lemma45Conclusion
    {X : Type u} [Group X] [Finite X]
    (W E : Subgroup X) (hEW : E ≤ W) : Prop where
  hall : IsHallSubgroup (subgroupPrimeSet E) (E.subgroupOf W)
  normal_complement : ∃ K : Subgroup X, IsNormalComplementIn W E K

/-- Genuine earlier-book callback for Peterfalvi `[II1; 4.5]`.

For `π = π(E)`, the hypothesis is the source formula `(4C)` for every
nontrivial primary subgroup of the solvable subgroup `E`. -/
@[expose] public def II1Lemma45NormalComplement
    {X : Type u} [Group X] [Finite X] : Prop :=
  ∀ (W E : Subgroup X) (hEW : E ≤ W),
    Group.IsSolvable E →
    (∀ q : Nat.Primes, q ∈ subgroupPrimeSet E →
      ∀ U : Subgroup X, U ≤ E → U ≠ ⊥ → IsPGroup q.val U →
        (normalizerIn W U : Set X) =
          (piCoreIn (subgroupPrimeSet E)ᶜ
              (W ⊓ Subgroup.centralizer (U : Set X)) : Set X) *
            (normalizerIn E U : Set X)) →
      II1Lemma45Conclusion W E hEW

/-- Formula `(4C)` implies the `p'`-core normalizer factorization consumed by
the proved `[II1; 4.4]`. -/
private theorem lemma45_factor_for_lemma44
    {X : Type u} [Group X] [Finite X]
    {W E U : Subgroup X} (hEW : E ≤ W)
    (p : Nat.Primes) (hpE : p ∈ subgroupPrimeSet E)
    (_hUE : U ≤ E) (_hUne : U ≠ ⊥) (_hUp : IsPGroup p.val U)
    (h4C :
      (normalizerIn W U : Set X) =
        (piCoreIn (subgroupPrimeSet E)ᶜ
            (W ⊓ Subgroup.centralizer (U : Set X)) : Set X) *
          (normalizerIn E U : Set X)) :
    (normalizerIn W U : Set X) =
      (((pPrimeCore p.val (normalizerIn W U)).map
        (normalizerIn W U).subtype : Subgroup X) : Set X) *
        (normalizerIn E U : Set X) := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  let N : Subgroup X := normalizerIn W U
  let C : Subgroup X := W ⊓ Subgroup.centralizer (U : Set X)
  let A : Subgroup X := piCoreIn (subgroupPrimeSet E)ᶜ C
  let Op : Subgroup X := (pPrimeCore p.val N).map N.subtype
  have hCN : C ≤ N := by
    intro x hx
    exact ⟨hx.1, centralizer_le_normalizer U hx.2⟩
  have hAN : A ≤ N := (piCoreIn_le (subgroupPrimeSet E)ᶜ C).trans hCN
  have hNnormC : N ≤ Subgroup.normalizer (C : Set X) := by
    apply Subgroup.le_normalizer_inf
    · exact inf_le_left.trans W.le_normalizer
    · exact le_normalizer_centralizer_of_le_normalizer inf_le_right
  have hNnormA : N ≤ Subgroup.normalizer (A : Set X) := by
    exact section8_le_normalizer_piCoreIn_of_le_normalizer hNnormC
  have hAnormN : (A.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAN]
    exact hNnormA
  have hApi : IsPiSubgroup (G := X)
      (({p} : Set Nat.Primes)ᶜ) A := by
    intro q hqA
    have hqNotE : q ∉ subgroupPrimeSet E :=
      piCoreIn_isPiSubgroup (subgroupPrimeSet E)ᶜ C q hqA
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hqp
    subst q
    exact hqNotE hpE
  have hAcore : A ≤ piCoreIn (({p} : Set Nat.Primes)ᶜ) N :=
    section8_le_piCoreIn_of_normal_isPiSubgroup hAN hAnormN hApi
  have hAOp : A ≤ Op := by
    have hcoreEq :=
      section8_piCoreIn_singleton_compl_eq_pPrimeCore_map
        (G := X) (p := p.val) N
    have hpEq : (⟨p.val, Fact.out⟩ : Nat.Primes) = p := Subtype.ext rfl
    rw [hpEq] at hcoreEq
    rw [hcoreEq] at hAcore
    exact hAcore
  apply Set.Subset.antisymm
  · rw [h4C]
    exact Set.mul_subset_mul hAOp Set.Subset.rfl
  · rintro x ⟨a, ha, b, hb, rfl⟩
    exact N.mul_mem (Subgroup.map_subtype_le _ ha) ⟨hEW hb.1, hb.2⟩

/-- The proved `[II1; 4.4]` supplies the Sylow subgroup and fusion control
needed in the inductive proof of `[II1; 4.5]`. -/
public theorem ii1Lemma45_alternativeA
    {X : Type u} [Group X] [Finite X]
    (W E : Subgroup X) (hEW : E ≤ W)
    (p : Nat.Primes) (hpE : p ∈ subgroupPrimeSet E)
    (h4C : ∀ q : Nat.Primes, q ∈ subgroupPrimeSet E →
      ∀ U : Subgroup X, U ≤ E → U ≠ ⊥ → IsPGroup q.val U →
        (normalizerIn W U : Set X) =
          (piCoreIn (subgroupPrimeSet E)ᶜ
              (W ⊓ Subgroup.centralizer (U : Set X)) : Set X) *
            (normalizerIn E U : Set X)) :
    Lemma94AlternativeA W E hEW p.val := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  apply ii1Lemma44Ambient (W := W) (E := E) hEW
  intro P U hUP hshape
  have hPne : (P : Subgroup E) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card P hpE
  have hUE : U ≤ E := hUP.trans (Subgroup.map_subtype_le _)
  have hUne : U ≠ ⊥ := by
    rcases hshape with hUncyc | hUPeq
    · intro hbot
      apply hUncyc
      rw [hbot]
      infer_instance
    · intro hbot
      apply hPne
      apply Subgroup.map_injective E.subtype_injective
      rw [Subgroup.map_bot, ← hUPeq, hbot]
  have hUp : IsPGroup p.val U :=
    (P.isPGroup'.map E.subtype).to_le hUP
  exact lemma45_factor_for_lemma44 hEW p hpE hUE hUne hUp
    (h4C p hpE U hUE hUne hUp)

/-- The Hall-subgroup half of `[II1; 4.5]`, obtained from the proved fusion
criterion `[II1; 4.4]`. -/
public theorem ii1Lemma45_hall
    {X : Type u} [Group X] [Finite X]
    (W E : Subgroup X) (hEW : E ≤ W)
    (h4C : ∀ q : Nat.Primes, q ∈ subgroupPrimeSet E →
      ∀ U : Subgroup X, U ≤ E → U ≠ ⊥ → IsPGroup q.val U →
        (normalizerIn W U : Set X) =
          (piCoreIn (subgroupPrimeSet E)ᶜ
              (W ⊓ Subgroup.centralizer (U : Set X)) : Set X) *
            (normalizerIn E U : Set X)) :
    IsHallSubgroup (subgroupPrimeSet E) (E.subgroupOf W) := by
  apply isHallSubgroup_of
  · intro q hqcard
    change q.val ∣ Nat.card E
    simpa [natCard_subgroupOf_eq E W hEW] using hqcard
  · intro p hpE hpindex
    letI : Fact p.val.Prime := ⟨p.property⟩
    obtain ⟨Q, hQE, _hfusion⟩ :=
      ii1Lemma45_alternativeA W E hEW p hpE h4C
    have hQle : (Q : Subgroup W) ≤ E.subgroupOf W := hQE
    have hindexDvd : (E.subgroupOf W).index ∣ (Q : Subgroup W).index :=
      Subgroup.index_dvd_of_le hQle
    exact Q.not_dvd_index (hpindex.trans hindexDvd)

/-- The old complementary-prime core lies in the `p`-residual used for the
inductive step of `[II1; 4.5]`. -/
private theorem lemma45_piCore_le_hallPResidual
    {X : Type u} [Group X] [Finite X]
    {W E U : Subgroup X} (p : Nat.Primes)
    (hpE : p ∈ subgroupPrimeSet E) :
    piCoreIn (subgroupPrimeSet E)ᶜ
        (W ⊓ Subgroup.centralizer (U : Set X)) ≤
      (External.hallPResidual p.val W).map W.subtype := by
  classical
  let A : Subgroup X := piCoreIn (subgroupPrimeSet E)ᶜ
    (W ⊓ Subgroup.centralizer (U : Set X))
  have hAW : A ≤ W :=
    (piCoreIn_le (G := X) (subgroupPrimeSet E)ᶜ
      (W ⊓ Subgroup.centralizer (U : Set X))).trans inf_le_left
  have hcopEA : Nat.Coprime (Nat.card E) (Nat.card A) := by
    simpa [A] using coprime_card_of_piCoreIn_compl (G := X) E
      (W ⊓ Subgroup.centralizer (U : Set X))
  have hpdivE : p.val ∣ Nat.card E := by
    simpa [subgroupPrimeSet] using hpE
  have hpcopA : Nat.Coprime p.val (Nat.card A) :=
    Nat.Coprime.of_dvd_left hpdivE hcopEA
  intro x hxA
  let xW : W := ⟨x, hAW hxA⟩
  refine Subgroup.mem_map.mpr ⟨xW, ?_, rfl⟩
  apply Subgroup.subset_closure
  change Nat.Coprime p.val (orderOf xW)
  have hord : orderOf xW ∣ Nat.card A := by
    have h := orderOf_dvd_natCard (⟨x, hxA⟩ : A)
    simpa [xW, Subgroup.orderOf_coe] using h
  exact Nat.Coprime.of_dvd_right hord hpcopA

/-- A recursive normal complement over the `p`-residual lifts to the original
group.  Its local Hall property makes it characteristic in the residual. -/
private theorem lemma45_normalComplement_lift
    {X : Type u} [Group X] [Finite X]
    {W E W₀ E₀ K : Subgroup X}
    (hW₀W : W₀ ≤ W) (hW₀normal : (W₀.subgroupOf W).Normal)
    (hE₀ : E₀ = W₀ ⊓ E) (hEW₀ : E ⊔ W₀ = W)
    (hHall₀ : IsHallSubgroup (subgroupPrimeSet E₀) (E₀.subgroupOf W₀))
    (hcomp₀ : IsNormalComplementIn W₀ E₀ K) :
    IsNormalComplementIn W E K := by
  classical
  let Kloc : Subgroup W₀ := K.subgroupOf W₀
  let E₀loc : Subgroup W₀ := E₀.subgroupOf W₀
  have hKleW₀ : K ≤ W₀ := hcomp₀.le_M
  have hE₀leW₀ : E₀ ≤ W₀ := by
    rw [← hcomp₀.sup_eq]
    exact le_sup_right
  have hE₀leE : E₀ ≤ E := by
    rw [hE₀]
    exact inf_le_right
  have hKnormal : Kloc.Normal := by
    simpa [Kloc] using hcomp₀.normal_in_M
  letI : Kloc.Normal := hKnormal
  have hcompLoc : Kloc.IsComplement' E₀loc := by
    have hdisj : Disjoint Kloc E₀loc := by
      rw [Subgroup.disjoint_def]
      intro x hxK hxE₀
      apply Subtype.ext
      exact (Subgroup.disjoint_def.mp hcomp₀.disjoint_D) hxK hxE₀
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
    rw [Set.eq_univ_iff_forall]
    intro x
    have hsupTop : Kloc ⊔ E₀loc = ⊤ := by
      calc
        Kloc ⊔ E₀loc = (K ⊔ E₀).subgroupOf W₀ :=
          (Subgroup.subgroupOf_sup hKleW₀ hE₀leW₀).symm
        _ = W₀.subgroupOf W₀ := by rw [hcomp₀.sup_eq]
        _ = ⊤ := Subgroup.subgroupOf_self W₀
    have hxSup : x ∈ Kloc ⊔ E₀loc := by simp [hsupTop]
    rcases (Subgroup.mem_sup_of_normal_left
      (s := Kloc) (t := E₀loc)).1 hxSup with ⟨k, hk, e, he, hke⟩
    exact Set.mem_mul.mpr ⟨k, hk, e, he, hke⟩
  have hKHall : IsHallSubgroup (subgroupPrimeSet E₀)ᶜ Kloc :=
    Section14.section14_complement_isHall_compl_of_isHall
      hHall₀ hcompLoc.symm
  have hKchar : Kloc.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro e
    exact hKHall.eq_of_normal (hKHall.map_mulAut e)
  have hKleW : K ≤ W := hKleW₀.trans hW₀W
  have hKnormalW : (K.subgroupOf W).Normal := by
    exact normal_subgroupOf_map_of_characteristic_of_normal
      W₀ K W hW₀W hW₀normal Kloc hKchar
        (Subgroup.map_subgroupOf_eq_of_le hKleW₀).symm hKleW
  have hEW : E ≤ W := by
    rw [← hEW₀]
    exact le_sup_left
  refine
    { le_M := hKleW
      normal_in_M := hKnormalW
      sup_eq := ?_
      disjoint_D := ?_ }
  · apply le_antisymm
    · exact sup_le hKleW hEW
    · rw [← hEW₀]
      apply sup_le le_sup_right
      rw [← hcomp₀.sup_eq]
      exact sup_le le_sup_left (hE₀leE.trans le_sup_right)
  · rw [Subgroup.disjoint_def]
    intro x hxK hxE
    have hxE₀ : x ∈ E₀ := by
      rw [hE₀]
      exact ⟨hKleW₀ hxK, hxE⟩
    exact (Subgroup.disjoint_def.mp hcomp₀.disjoint_D) hxK hxE₀

/-- Peterfalvi `[II1; 4.5]`: the normalizer factorization `(4C)` makes `E`
a Hall subgroup of `W` and gives it a normal complement. -/
public theorem ii1Lemma45NormalComplement
    {X : Type u} [Group X] [Finite X] :
    II1Lemma45NormalComplement (X := X) := by
  classical
  intro W E hEW hEsolv h4C
  induction hcard : Nat.card E using Nat.strong_induction_on generalizing W E with
  | h n ih =>
      have hHall := ii1Lemma45_hall W E hEW h4C
      by_cases hEbot : E = ⊥
      · refine ⟨hHall, W, ?_⟩
        refine
          { le_M := le_rfl
            normal_in_M := ?_
            sup_eq := by simp [hEbot]
            disjoint_D := by simp [hEbot] }
        rw [Subgroup.subgroupOf_self]
        infer_instance
      · let EW : Subgroup W := E.subgroupOf W
        have hEWne : EW ≠ ⊥ := by
          intro hbot
          apply hEbot
          calc
            E = EW.map W.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hEW).symm
            _ = ⊥ := by rw [hbot, Subgroup.map_bot]
        have hEWsolv : Group.IsSolvable EW := by
          let eEW : EW ≃* E := Subgroup.subgroupOfEquivOfLe hEW
          letI : Group.IsSolvable E := hEsolv
          exact Group.isSolvable_of_isSolvable_injective
            (f := eEW.toMonoidHom) eEW.injective
        letI : Group.IsSolvable EW := hEWsolv
        letI : Nontrivial EW :=
          (Subgroup.nontrivial_iff_ne_bot EW).2 hEWne
        have hcommLt : derivedSubgroup EW < ⊤ :=
          Group.IsSolvable.commutator_lt_top_of_nontrivial (G := EW)
        have hAbOneLt : 1 < Nat.card (EW ⧸ derivedSubgroup EW) := by
          have hindex : 1 < (derivedSubgroup EW).index :=
            Subgroup.one_lt_index_of_ne_top hcommLt.ne
          simpa [Subgroup.index_eq_card] using hindex
        obtain ⟨p, hp, hpAb⟩ := Nat.exists_prime_and_dvd hAbOneLt.ne'
        let p' : Nat.Primes := ⟨p, hp⟩
        have hpEW : p ∣ Nat.card EW :=
          hpAb.trans (Subgroup.card_quotient_dvd_card
            (s := derivedSubgroup EW))
        have hpE : p' ∈ subgroupPrimeSet E := by
          change p ∣ Nat.card E
          simpa [EW, natCard_subgroupOf_eq E W hEW] using hpEW
        obtain ⟨P, hPE, hfusion⟩ :=
          ii1Lemma45_alternativeA W E hEW p' hpE h4C
        letI : Fact p.Prime := ⟨hp⟩
        have hres :=
          hallPResidual_factorization_of_dvd_abelianization_of_controlsFusionIn
            EW P hPE hfusion hpAb
        let R : Subgroup W := External.hallPResidual p'.val W
        let W₀ : Subgroup X := R.map W.subtype
        let E₀ : Subgroup X := W₀ ⊓ E
        have hW₀W : W₀ ≤ W := Subgroup.map_subtype_le R
        have hW₀normal : (W₀.subgroupOf W).Normal := by
          have hsub : W₀.subgroupOf W = R := by
            apply Subgroup.map_injective W.subtype_injective
            rw [Subgroup.map_subgroupOf_eq_of_le hW₀W]
          rw [hsub]
          exact External.hallPResidual_normal p'.val W
        have hEW₀ : E ⊔ W₀ = W := by
          have hmap := congrArg
            (fun H : Subgroup W => H.map W.subtype) hres.2
          change (EW ⊔ R).map W.subtype =
            (⊤ : Subgroup W).map W.subtype at hmap
          have htopmap : (⊤ : Subgroup W).map W.subtype = W := by
            simpa [MonoidHom.range_eq_map] using
              (Subgroup.range_subtype (H := W))
          rw [htopmap] at hmap
          simpa [EW, R, W₀, Subgroup.map_sup,
            Subgroup.map_subgroupOf_eq_of_le hEW] using hmap
        have hW₀ne : W₀ ≠ W := by
          intro hEq
          apply hres.1.ne
          apply Subgroup.map_injective W.subtype_injective
          have htopmap : (⊤ : Subgroup W).map W.subtype = W := by
            simpa [MonoidHom.range_eq_map] using
              (Subgroup.range_subtype (H := W))
          calc
            R.map W.subtype = W₀ := rfl
            _ = W := hEq
            _ = (⊤ : Subgroup W).map W.subtype := htopmap.symm
        have hW₀lt : W₀ < W := lt_of_le_of_ne hW₀W hW₀ne
        have hE₀E : E₀ ≤ E := inf_le_right
        have hE₀ne : E₀ ≠ E := by
          intro hEq
          have hEW₀le : E ≤ W₀ := by
            rw [← hEq]
            exact inf_le_left
          have hWW₀ : W ≤ W₀ := by
            rw [← hEW₀]
            exact sup_le hEW₀le le_rfl
          exact hW₀lt.2 hWW₀
        have hE₀lt : E₀ < E := lt_of_le_of_ne hE₀E hE₀ne
        have hE₀card : Nat.card E₀ < n := by
          rw [← hcard]
          exact natCard_lt_of_subgroup_lt hE₀lt
        have hE₀solv : Group.IsSolvable E₀ := by
          letI : Group.IsSolvable E := hEsolv
          exact Group.isSolvable_of_isSolvable_injective
            (f := Subgroup.inclusion hE₀E)
            (Subgroup.inclusion_injective hE₀E)
        have h4C₀ : ∀ q : Nat.Primes, q ∈ subgroupPrimeSet E₀ →
            ∀ U : Subgroup X, U ≤ E₀ → U ≠ ⊥ → IsPGroup q.val U →
              (normalizerIn W₀ U : Set X) =
                (piCoreIn (subgroupPrimeSet E₀)ᶜ
                    (W₀ ⊓ Subgroup.centralizer (U : Set X)) : Set X) *
                  (normalizerIn E₀ U : Set X) := by
          intro q hq U hUE₀ hUne hUq
          let C : Subgroup X :=
            W ⊓ Subgroup.centralizer (U : Set X)
          let C₀ : Subgroup X :=
            W₀ ⊓ Subgroup.centralizer (U : Set X)
          let A : Subgroup X :=
            piCoreIn (subgroupPrimeSet E)ᶜ C
          let A₀ : Subgroup X :=
            piCoreIn (subgroupPrimeSet E₀)ᶜ C₀
          have hqE : q ∈ subgroupPrimeSet E :=
            section8_subgroupPrimeSet_mono hE₀E hq
          have hUE : U ≤ E := hUE₀.trans hE₀E
          have hfactor := h4C q hqE U hUE hUne hUq
          have hAW₀ : A ≤ W₀ := by
            simpa [A, C, W₀, R] using
              lemma45_piCore_le_hallPResidual (W := W) (E := E)
                (U := U) p' hpE
          have hAC₀ : A ≤ C₀ := by
            intro a ha
            exact ⟨hAW₀ ha,
              (piCoreIn_le (G := X) (subgroupPrimeSet E)ᶜ C ha).2⟩
          have hC₀C : C₀ ≤ C := by
            intro x hx
            exact ⟨hW₀W hx.1, hx.2⟩
          have hC₀normA : C₀ ≤ Subgroup.normalizer (A : Set X) := by
            exact section8_le_normalizer_piCoreIn_of_le_normalizer
              (hC₀C.trans C.le_normalizer)
          have hAnormalC₀ : (A.subgroupOf C₀).Normal :=
            (Subgroup.normal_subgroupOf_iff_le_normalizer hAC₀).2 hC₀normA
          have hApi₀ : IsPiSubgroup (G := X)
              (subgroupPrimeSet E₀)ᶜ A := by
            intro r hrA
            have hrNotE : r ∉ subgroupPrimeSet E := by
              simpa [A, C] using
                (piCoreIn_isPiSubgroup (G := X)
                  (subgroupPrimeSet E)ᶜ C r hrA)
            show r ∉ subgroupPrimeSet E₀
            intro hrE₀
            exact hrNotE (section8_subgroupPrimeSet_mono hE₀E hrE₀)
          have hAA₀ : A ≤ A₀ := by
            exact section8_le_piCoreIn_of_normal_isPiSubgroup
              hAC₀ hAnormalC₀ hApi₀
          apply Set.Subset.antisymm
          · intro x hx
            have hxW : x ∈ normalizerIn W U :=
              ⟨hW₀W hx.1, hx.2⟩
            change x ∈ (normalizerIn W U : Set X) at hxW
            rw [hfactor] at hxW
            rcases hxW with ⟨a, ha, e, he, rfl⟩
            have haW₀ : a ∈ W₀ := hAW₀ ha
            have heW₀ : e ∈ W₀ := by
              have haeW₀ : a * e ∈ W₀ := hx.1
              have := W₀.mul_mem (W₀.inv_mem haW₀) haeW₀
              simpa [mul_assoc] using this
            exact ⟨a, hAA₀ ha, e,
              ⟨⟨heW₀, he.1⟩, he.2⟩, rfl⟩
          · rintro x ⟨a, ha, e, he, rfl⟩
            apply (normalizerIn W₀ U).mul_mem
            · exact ⟨
                (piCoreIn_le (G := X) (subgroupPrimeSet E₀)ᶜ C₀ ha).1,
                centralizer_le_normalizer U
                  ((piCoreIn_le (G := X)
                    (subgroupPrimeSet E₀)ᶜ C₀ ha).2)⟩
            · exact ⟨he.1.1, he.2⟩
        have hrec := ih (Nat.card E₀) hE₀card
          (W := W₀) (E := E₀) inf_le_left hE₀solv h4C₀ rfl
        refine ⟨hHall, hrec.normal_complement.choose, ?_⟩
        exact lemma45_normalComplement_lift hW₀W hW₀normal rfl hEW₀
          hrec.hall hrec.normal_complement.choose_spec

/-- Conjugation preserves a join if it preserves each factor. -/
public theorem conjugate_mem_sup_of_mem_normalizers
    {G : Type*} [Group G] {A B : Subgroup G} {x y : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G))
    (hy : y ∈ A ⊔ B) :
    x * y * x⁻¹ ∈ A ⊔ B := by
  rw [Subgroup.sup_eq_closure] at hy ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
  · intro z hz
    rcases hz with hzA | hzB
    · exact Subgroup.subset_closure
        (Or.inl ((Subgroup.mem_normalizer_iff.mp hA z).1 hzA))
    · exact Subgroup.subset_closure
        (Or.inr ((Subgroup.mem_normalizer_iff.mp hB z).1 hzB))
  · simp
  · intro a b _ha _hb hca hcb
    simpa [mul_assoc] using
      (Subgroup.closure ((A : Set G) ∪ (B : Set G))).mul_mem hca hcb
  · intro a _ha hca
    simpa [mul_assoc] using
      (Subgroup.closure ((A : Set G) ∪ (B : Set G))).inv_mem hca

/-- An element normalizing two subgroups normalizes their join. -/
public theorem mem_normalizer_sup_of_mem_normalizers
    {G : Type*} [Group G] {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact conjugate_mem_sup_of_mem_normalizers hA hB
  · intro hy
    have hAinv : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem hA
    have hBinv : x⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
      (Subgroup.normalizer (B : Set G)).inv_mem hB
    have h := conjugate_mem_sup_of_mem_normalizers
      (A := A) (B := B) (x := x⁻¹) (y := x * y * x⁻¹)
      hAinv hBinv hy
    simpa [mul_assoc] using h

/-- If normalizing a join is already known to preserve both factors, the
normalizer of one factor inside the normalizer of the other is the normalizer
of the join. -/
public theorem normalizerIn_normalizerIn_eq_normalizerIn_sup
    {G : Type*} [Group G] {M A B : Subgroup G}
    (hSupA : Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) ≤
      Subgroup.normalizer (A : Set G))
    (hSupB : Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) ≤
      Subgroup.normalizer (B : Set G)) :
    normalizerIn (normalizerIn M B) A = normalizerIn M (A ⊔ B) := by
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1.1,
      mem_normalizer_sup_of_mem_normalizers hx.2 hx.1.2⟩
  · intro x hx
    exact ⟨⟨hx.1, hSupB hx.2⟩, hSupA hx.2⟩

private theorem lemma104_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type u} [Group G] (A B : Subgroup G)
    (hnorm : B ≤ Subgroup.normalizer (A : Set G))
    (hdisj : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G),
      Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have hinj : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisj
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective toSup := by
    intro x
    have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnorm]
      exact x.property
    rcases hx with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinj, hsurj⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

private theorem lemma104_sylow_left_of_commuting_prime_sup
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hqp : q ≠ p)
    {P U : Subgroup G}
    (hPp : IsPGroup p P) (hUq : IsPGroup q U)
    (hPnormU : P ≤ Subgroup.normalizer (U : Set G)) :
    theorem4bIsSylowSubgroupOf q U (U ⊔ P) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let Y : Subgroup G := U ⊔ P
  have hUY : U ≤ Y := le_sup_left
  let UY : Subgroup Y := U.subgroupOf Y
  have hUYq : IsPGroup q UY :=
    hUq.of_equiv (Subgroup.subgroupOfEquivOfLe hUY).symm
  have hcop : Nat.Coprime (Nat.card U) (Nat.card P) :=
    IsPGroup.coprime_card_of_ne q p hqp U P hUq hPp
  have hdisj : Disjoint U P := by
    rw [disjoint_iff]
    exact Subgroup.inf_eq_bot_of_coprime hcop
  have hcardY : Nat.card Y = Nat.card U * Nat.card P := by
    exact lemma104_natCard_sup_eq_mul_of_disjoint_of_le_normalizer U P
      hPnormU hdisj
  have hcardUY : Nat.card UY = Nat.card U := by
    exact natCard_subgroupOf_eq U Y hUY
  have hindex : UY.index = Nat.card P := by
    apply Nat.mul_left_cancel (Nat.card_pos : 0 < Nat.card U)
    calc
      Nat.card U * UY.index = Nat.card UY * UY.index := by
        rw [hcardUY]
      _ = Nat.card Y := UY.card_mul_index
      _ = Nat.card U * Nat.card P := hcardY
  have hnot : ¬ q ∣ UY.index := by
    rw [hindex]
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn]
    exact hq.coprime_iff_not_dvd.mp
      (Nat.Coprime.pow_right n ((Nat.coprime_primes hq hp).2 hqp))
  let Q : Sylow q Y := hUYq.toSylow hnot
  refine ⟨Q, ?_⟩
  exact (Subgroup.map_subgroupOf_eq_of_le hUY).symm

private theorem lemma104_theorem4bIsSylowSubgroupOf_le
    {X : Type u} [Group X] {p : ℕ} {P E : Subgroup X}
    (h : theorem4bIsSylowSubgroupOf p P E) : P ≤ E := by
  rcases h with ⟨Q, hQ⟩
  rw [hQ]
  exact Subgroup.map_subtype_le (Q : Subgroup E)

/- The checked `(10E)` normalizer identity.  The characteristic-Sylow
argument is essential: normalizing a join does not preserve arbitrary
factors without the primary hypotheses. -/
public theorem lemma104_normalizer_sup_eq
    {X : Type u} [Group X] [Finite X]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hqp : q ≠ p)
    {M D P U : Subgroup X}
    (hUD : U ≤ D)
    (hUP : U ≤ Subgroup.centralizer (P : Set X))
    (hUq : IsPGroup q U)
    (hPsylD : theorem4bIsSylowSubgroupOf p P D) :
    normalizerIn (normalizerIn M P) U = normalizerIn M (U ⊔ P) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let Y : Subgroup X := U ⊔ P
  have hPD : P ≤ D := lemma104_theorem4bIsSylowSubgroupOf_le hPsylD
  have hPY : P ≤ Y := le_sup_right
  have hYD : Y ≤ D := sup_le hUD hPD
  have hPsylY : theorem4bIsSylowSubgroupOf p P Y :=
    theorem4bIsSylowSubgroupOf_of_between hp hPsylD hPY hYD
  obtain ⟨PY, hPYmap⟩ := hPsylY
  have hPp : IsPGroup p P := by
    have h := PY.isPGroup'.map Y.subtype
    rwa [← hPYmap] at h
  have hUnormP : U ≤ Subgroup.normalizer (P : Set X) :=
    hUP.trans (centralizer_le_normalizer P)
  have hPcentralU : P ≤ Subgroup.centralizer (U : Set X) :=
    le_centralizer_of_le_centralizer hUP
  have hPnormU : P ≤ Subgroup.normalizer (U : Set X) :=
    hPcentralU.trans (centralizer_le_normalizer U)
  have hPnormalY : (P.subgroupOf Y).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hPY).2
    exact sup_le hUnormP Subgroup.le_normalizer
  have hPYeq : (PY : Subgroup Y) = P.subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    calc
      (PY : Subgroup Y).map Y.subtype = P := hPYmap.symm
      _ = (P.subgroupOf Y).map Y.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hPY).symm
  have hPYnormal : (PY : Subgroup Y).Normal := by
    rw [hPYeq]
    exact hPnormalY
  letI : (PY : Subgroup Y).Characteristic :=
    Sylow.characteristic_of_normal PY hPYnormal
  have hUsylY : theorem4bIsSylowSubgroupOf q U Y := by
    simpa [Y] using lemma104_sylow_left_of_commuting_prime_sup
      hp hq hqp hPp hUq hPnormU
  obtain ⟨UY, hUYmap⟩ := hUsylY
  have hUYle : U ≤ Y := le_sup_left
  have hUnormalY : (U.subgroupOf Y).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hUYle).2
    exact sup_le Subgroup.le_normalizer hPnormU
  have hUYeq : (UY : Subgroup Y) = U.subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    calc
      (UY : Subgroup Y).map Y.subtype = U := hUYmap.symm
      _ = (U.subgroupOf Y).map Y.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hUYle).symm
  have hUYnormal : (UY : Subgroup Y).Normal := by
    rw [hUYeq]
    exact hUnormalY
  letI : (UY : Subgroup Y).Characteristic :=
    Sylow.characteristic_of_normal UY hUYnormal
  apply le_antisymm
  · intro x hx
    have hxM : x ∈ M := hx.1.1
    have hxP : x ∈ Subgroup.normalizer (P : Set X) := hx.1.2
    have hxU : x ∈ Subgroup.normalizer (U : Set X) := hx.2
    exact ⟨hxM, by
      simpa [Y] using mem_normalizer_sup_of_mem_normalizers hxU hxP⟩
  · intro x hx
    have hxNormY : x ∈ Subgroup.normalizer (Y : Set X) := by
      simpa [Y] using hx.2
    have hxNormPmap :=
      section8_normalizer_map_subtype_le_of_characteristic
        (H := Y) (K := (PY : Subgroup Y)) hxNormY
    have hxNormUmap :=
      section8_normalizer_map_subtype_le_of_characteristic
        (H := Y) (K := (UY : Subgroup Y)) hxNormY
    rw [← hPYmap] at hxNormPmap
    rw [← hUYmap] at hxNormUmap
    exact ⟨⟨hx.1, hxNormPmap⟩, hxNormUmap⟩

private theorem lemma104_natCard_eq_mul_of_eq_set_mul_of_disjoint
    {G : Type u} [Group G] [Finite G]
    {N A B : Subgroup G}
    (hN : (N : Set G) = (A : Set G) * (B : Set G))
    (hdisj : Disjoint A B) :
    Nat.card N = Nat.card A * Nat.card B := by
  let f : A × B → N := fun z =>
    ⟨(z.1 : G) * (z.2 : G), by
      change (z.1 : G) * (z.2 : G) ∈ (N : Set G)
      rw [hN]
      exact ⟨z.1, z.1.property, z.2, z.2.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subgroup.mul_injective_of_disjoint hdisj
      exact congrArg Subtype.val hxy
    · intro n
      have hn : (n : G) ∈ (A : Set G) * (B : Set G) := by
        rw [← hN]
        exact n.property
      rcases hn with ⟨a, ha, b, hb, hab⟩
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card N = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective f hf).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

private theorem lemma104_normal_sylow_eq_pCore
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : Nat.Prime p) (P : Sylow p G)
    (hPnormal : (P : Subgroup G).Normal) :
    pCore p G = (P : Subgroup G) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Unique (Sylow p G) := Sylow.unique_of_normal P hPnormal
  apply le_antisymm
  · obtain ⟨Q, hcoreQ⟩ :=
      (pCore_isPGroup (p := p) (G := G)).exists_le_sylow
    simpa [Subsingleton.elim Q P] using hcoreQ
  · exact le_sSup ⟨hPnormal, P.isPGroup'⟩

/-- The normal `2`-factor supplied by Proposition 8.4 is the `2`-core of
the relevant centralizer.  This is the first structural equality in source
`(10E)`. -/
public theorem proposition84_factor_eq_pCore_mul
    {X : Type u} [Group X] [Finite X]
    {M D Y S : Subgroup X}
    (hDodd : Odd (Nat.card D))
    (hS : Proposition84NormalizerFactor M D Y S) :
    let C := M ⊓ Subgroup.centralizer (Y : Set X)
    (normalizerIn M Y : Set X) =
      ((pCore 2 C).map C.subtype : Set X) *
        (normalizerIn D Y : Set X) := by
  classical
  let N : Subgroup X := normalizerIn M Y
  let R : Subgroup X := normalizerIn D Y
  let C : Subgroup X := M ⊓ Subgroup.centralizer (Y : Set X)
  have hRodd : Odd (Nat.card R) := by
    apply hDodd.of_dvd_nat
    exact Subgroup.card_dvd_of_le inf_le_left
  have hScopR : Nat.Coprime (Nat.card S) (Nat.card R) := by
    obtain ⟨n, hn⟩ := hS.isPGroup_two.exists_card_eq
    rw [hn]
    exact hRodd.coprime_two_left.pow_left n
  have hSdisjR : Disjoint S R := by
    rw [disjoint_iff]
    exact Subgroup.inf_eq_bot_of_coprime hScopR
  have hNcard : Nat.card N = Nat.card S * Nat.card R := by
    exact lemma104_natCard_eq_mul_of_eq_set_mul_of_disjoint
      (by simpa [N, R, normalizerIn] using hS.normalizerIn_eq_mul) hSdisjR
  have hSN : S ≤ N := by
    simpa [N, normalizerIn] using hS.le_normalizerIn
  let SN : Subgroup N := S.subgroupOf N
  have hSNcard : Nat.card SN = Nat.card S :=
    natCard_subgroupOf_eq S N hSN
  have hSNindex : SN.index = Nat.card R := by
    apply Nat.mul_left_cancel (Nat.card_pos : 0 < Nat.card S)
    calc
      Nat.card S * SN.index = Nat.card SN * SN.index := by rw [hSNcard]
      _ = Nat.card N := SN.card_mul_index
      _ = Nat.card S * Nat.card R := hNcard
  have hSNtwo : IsPGroup 2 SN :=
    hS.isPGroup_two.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm
  have htwo_not_index : ¬2 ∣ SN.index := by
    rw [hSNindex]
    exact hRodd.not_two_dvd_nat
  let PN : Sylow 2 N := hSNtwo.toSylow htwo_not_index
  have hPNmap : S = (PN : Subgroup N).map N.subtype := by
    rw [IsPGroup.toSylow_coe]
    exact (Subgroup.map_subgroupOf_eq_of_le hSN).symm
  have hSC : S ≤ C := by
    exact fun _ hs => ⟨hS.le_M hs, hS.le_centralizer hs⟩
  have hCN : C ≤ N := by
    intro x hx
    exact ⟨hx.1, centralizer_le_normalizer Y hx.2⟩
  have hSsylC : theorem4bIsSylowSubgroupOf 2 S C := by
    have hSsylN : theorem4bIsSylowSubgroupOf 2 S N := ⟨PN, hPNmap⟩
    exact theorem4bIsSylowSubgroupOf_of_between (by decide) hSsylN hSC hCN
  obtain ⟨PC, hPCmap⟩ := hSsylC
  have hNnormS : N ≤ Subgroup.normalizer (S : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).mp
      hS.normal_in_normalizerIn
  have hSCnormal : (S.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSC).mpr
      (hCN.trans hNnormS)
  have hPCeq : (PC : Subgroup C) = S.subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    calc
      (PC : Subgroup C).map C.subtype = S := hPCmap.symm
      _ = (S.subgroupOf C).map C.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hSC).symm
  have hPCnormal : (PC : Subgroup C).Normal := by
    rw [hPCeq]
    exact hSCnormal
  have hcoreC : pCore 2 C = (PC : Subgroup C) :=
    lemma104_normal_sylow_eq_pCore (by decide) PC hPCnormal
  have hS_eq_core : S = (pCore 2 C).map C.subtype := by
    rw [hcoreC]
    exact hPCmap
  simpa [C, R, normalizerIn, hS_eq_core] using hS.normalizerIn_eq_mul

/- The Corollary 8.5 witness needed by Proposition 8.4 for the smaller
subgroups occurring in `(10E)`. -/
public theorem lemma104_hasNontrivialPeterfalviNormalizer
    {X : Type u} [Group X] [Finite X]
    {M W D E V : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E V t)
    {U : Subgroup X}
    (hUA : U ≤ d.choice.initial.A1)
    (hUne : U ≠ ⊥)
    (hPnormU : d.choice.P ≤ Subgroup.normalizer (U : Set X)) :
    HasNontrivialPeterfalviNormalizer D t U := by
  classical
  have hJne : d.choice.initial.J ≠ ⊥ := by
    intro hJbot
    have hcardOne : Nat.card d.choice.initial.J = 1 :=
      Subgroup.card_eq_one.mpr hJbot
    rw [d.centralizer_A1_card] at hcardOne
    have hpTwo : 2 ≤ d.choice.p := d.choice.p_prime.two_le
    have hpow : 4 ≤ 2 ^ d.choice.p := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d.choice.p := Nat.pow_le_pow_right (by omega) hpTwo
    omega
  letI : Nontrivial d.choice.initial.J :=
    (Subgroup.nontrivial_iff_ne_bot d.choice.initial.J).2 hJne
  obtain ⟨j, hjne⟩ := exists_ne (1 : d.choice.initial.J)
  have hjA : (j : X) ∈
      {x : X | x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (d.choice.initial.A1 : Set X)} := by
    rw [← d.centralizer_A1]
    exact j.property
  have hjU : (j : X) ∈
      {x : X | x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (U : Set X)} := by
    rw [d.centralizer_uniform U hUA hUne hPnormU]
    exact hjA
  refine ⟨j, hjU.1, centralizer_le_normalizer U hjU.2, ?_⟩
  intro hjOne
  apply hjne
  apply Subtype.ext
  exact hjOne

/-- Proposition 8.4 applied to `U ⊔ P` gives the first factorization in
source `(10E)`. -/
public theorem lemma104_first_factor
    {X : Type u} [Group X] [Finite X]
    {M E : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101Conclusion M E
      (M ⊓ rightConjugate M t)
      (E ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    {q : ℕ} (hq : Nat.Prime q)
    {U : Subgroup X}
    (hUA : U ≤ d.choice.initial.A1)
    (hUCP : U ≤ Subgroup.centralizer (d.choice.P : Set X))
    (hUne : U ≠ ⊥)
    (hUq : IsPGroup q U) :
    let D := M ⊓ rightConjugate M t
    let P := d.choice.P
    let Y := U ⊔ P
    let C := M ⊓ Subgroup.centralizer (Y : Set X)
    (normalizerIn M Y : Set X) =
      ((pCore 2 C).map C.subtype : Set X) *
        (normalizerIn D Y : Set X) := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  let P : Subgroup X := d.choice.P
  let Y : Subgroup X := U ⊔ P
  have hA1V : d.choice.initial.A1 ≤ V := by
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hUV : U ≤ V := hUA.trans hA1V
  have hPV : P ≤ V := d.choice.P_le_V
  have hYV : Y ≤ D ⊓ Subgroup.centralizer ({t} : Set X) := by
    have hYV' : Y ≤ V := sup_le hUV hPV
    simpa [D, V, peterfalviV] using hYV'
  have hPnormU : P ≤ Subgroup.normalizer (U : Set X) := by
    exact (le_centralizer_of_le_centralizer hUCP).trans
      (centralizer_le_normalizer U)
  have hUnormal : (U.subgroupOf Y).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
    exact sup_le Subgroup.le_normalizer hPnormU
  have hI : HasNontrivialPeterfalviNormalizer D t U :=
    lemma104_hasNontrivialPeterfalviNormalizer d hUA hUne hPnormU
  obtain ⟨S, hS⟩ := Proposition84Statement.exists_factor_of_normal
    d83 h84 hYV hUne le_sup_left hUnormal hI
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hfactor := proposition84_factor_eq_pCore_mul hDodd hS
  simpa [D, P, Y] using hfactor

/- The actual Lemma 10.4 subgroup `C = C_A(P)` lies in
`N = N_M(P)` and is solvable because it lies in the odd-order subgroup
`D`. -/
public theorem lemma104_C_le_N_and_solvable
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (hDM : D ≤ M) (hDodd : Odd (Nat.card D)) :
    let C := d.choice.initial.A1 ⊓
      Subgroup.centralizer (d.choice.P : Set X)
    let N := normalizerIn M d.choice.P
    C ≤ N ∧ Group.IsSolvable C := by
  let C := d.choice.initial.A1 ⊓
    Subgroup.centralizer (d.choice.P : Set X)
  let N := normalizerIn M d.choice.P
  have hA1V : d.choice.initial.A1 ≤ peterfalviV D t := by
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hCD : C ≤ D :=
    inf_le_left.trans (hA1V.trans inf_le_left)
  have hCN : C ≤ N := by
    intro x hx
    exact ⟨hDM (hCD hx), centralizer_le_normalizer d.choice.P hx.2⟩
  refine ⟨hCN, odd_order_theorem C ?_⟩
  exact hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hCD)

/- Exact first-sentence assembly for Lemma 10.4 once `(10E)` has been
converted to the literal `[II1; 4.5]` premise. -/
public theorem lemma104_apply_II1Lemma45
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (hDM : D ≤ M) (hDodd : Odd (Nat.card D))
    (h45 : II1Lemma45NormalComplement (X := X))
    (hfactor :
      let C := d.choice.initial.A1 ⊓
        Subgroup.centralizer (d.choice.P : Set X)
      let N := normalizerIn M d.choice.P
      ∀ q : Nat.Primes, q ∈ subgroupPrimeSet C →
        ∀ U : Subgroup X, U ≤ C → U ≠ ⊥ →
          IsPGroup q.val U →
          (normalizerIn N U : Set X) =
            (piCoreIn (subgroupPrimeSet C)ᶜ
                (N ⊓ Subgroup.centralizer (U : Set X)) : Set X) *
              (normalizerIn C U : Set X)) :
    let C := d.choice.initial.A1 ⊓
      Subgroup.centralizer (d.choice.P : Set X)
    let N := normalizerIn M d.choice.P
    IsHallSubgroup (subgroupPrimeSet C) (C.subgroupOf N) ∧
      ∃ K : Subgroup X, IsNormalComplementIn N C K := by
  let C := d.choice.initial.A1 ⊓
    Subgroup.centralizer (d.choice.P : Set X)
  let N := normalizerIn M d.choice.P
  have hCS := lemma104_C_le_N_and_solvable d hDM hDodd
  change C ≤ N ∧ Group.IsSolvable C at hCS
  change ∀ q : Nat.Primes, q ∈ subgroupPrimeSet C →
      ∀ U : Subgroup X, U ≤ C → U ≠ ⊥ →
        IsPGroup q.val U →
        (normalizerIn N U : Set X) =
          (piCoreIn (subgroupPrimeSet C)ᶜ
              (N ⊓ Subgroup.centralizer (U : Set X)) : Set X) *
            (normalizerIn C U : Set X) at hfactor
  have h := h45 N C hCS.1 hCS.2 hfactor
  exact ⟨h.hall, h.normal_complement⟩

/- A prime in `π(C_A(P))` cannot be the selected prime `p`, because
`A₁` is the embedded `p'`-core of `V`. -/
public theorem Lemma101Conclusion.prime_ne_selected_of_mem_C
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    {q : Nat.Primes}
    (hq : q ∈ subgroupPrimeSet
      (d.choice.initial.A1 ⊓ Subgroup.centralizer (d.choice.P : Set X))) :
    q.val ≠ d.choice.p := by
  have hqdivC : q.val ∣ Nat.card
      (d.choice.initial.A1 ⊓ Subgroup.centralizer (d.choice.P : Set X) :
        Subgroup X) := by
    simpa [subgroupPrimeSet] using hq
  have hCA : d.choice.initial.A1 ⊓
      Subgroup.centralizer (d.choice.P : Set X) ≤ d.choice.initial.A1 :=
    inf_le_left
  have hqdivA : q.val ∣ Nat.card d.choice.initial.A1 :=
    hqdivC.trans (Subgroup.card_dvd_of_le hCA)
  letI : Fact d.choice.p.Prime := ⟨d.choice.p_prime⟩
  have hcardA : Nat.card d.choice.initial.A1 =
      Nat.card (pPrimeCore d.choice.p (peterfalviV D t)) := by
    rw [d.A1_eq_pPrimeCore,
      Subgroup.card_map_of_injective (peterfalviV D t).subtype_injective]
  have hpCopA : Nat.Coprime d.choice.p (Nat.card d.choice.initial.A1) := by
    rw [hcardA]
    exact pPrimeCore_coprime_card
  intro hqp
  have hpnot : ¬ d.choice.p ∣ Nat.card d.choice.initial.A1 :=
    d.choice.p_prime.coprime_iff_not_dvd.mp hpCopA
  exact hpnot (by simpa [hqp] using hqdivA)

/- In a commuting product `C P`, the normalizer of `U ≤ C` splits as
`P N_C(U)`.  This is the algebraic second half of `(10E)`. -/
public theorem normalizer_sup_eq_P_mul_C
    {X : Type u} [Group X] [Finite X]
    {N C P U : Subgroup X}
    (hCN : C ≤ N) (hPN : P ≤ N)
    (hU_C : U ≤ C)
    (hC_P : C ≤ Subgroup.centralizer (P : Set X))
    (hP_U : P ≤ Subgroup.centralizer (U : Set X))
    (hNset : (N : Set X) = (C : Set X) * (P : Set X)) :
    (normalizerIn N U : Set X) =
      (P : Set X) * (normalizerIn C U : Set X) := by
  ext x
  constructor
  · intro hx
    have hxProd : x ∈ (C : Set X) * (P : Set X) := by
      rw [← hNset]
      exact hx.1
    rcases Set.mem_mul.mp hxProd with ⟨c, hc, p, hp, hcp⟩
    have hcEq : c = x * p⁻¹ := by
      rw [← hcp]
      simp [mul_assoc]
    have hcNorm : c ∈ Subgroup.normalizer (U : Set X) := by
      apply Subgroup.mem_normalizer_fintype
      intro y hy
      have hpy : y * p = p * y :=
        (Subgroup.mem_centralizer_iff.mp (hP_U hp)) y hy
      have hpInv : p⁻¹ * y * p = y := by
        calc
          p⁻¹ * y * p = p⁻¹ * (y * p) := by rw [mul_assoc]
          _ = p⁻¹ * (p * y) := by rw [hpy]
          _ = y := by simp
      have hxy : x * y * x⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp hx.2 y).mp hy
      rw [hcEq]
      have hconj :
          (x * p⁻¹) * y * (x * p⁻¹)⁻¹ = x * y * x⁻¹ := by
        calc
          (x * p⁻¹) * y * (x * p⁻¹)⁻¹ =
              x * (p⁻¹ * y * p) * x⁻¹ := by group
          _ = x * y * x⁻¹ := by rw [hpInv]
      rw [hconj]
      exact hxy
    have hcp' : p * c = x := by
      calc
        p * c = c * p :=
          Subgroup.mem_centralizer_iff.mp (hC_P hc) p hp
        _ = x := hcp
    exact Set.mem_mul.mpr ⟨p, hp, c, ⟨hc, hcNorm⟩, hcp'⟩
  · rintro ⟨p, hp, c, hc, rfl⟩
    have hpNorm : p ∈ Subgroup.normalizer (U : Set X) :=
      centralizer_le_normalizer U (hP_U hp)
    have hcNorm : c ∈ Subgroup.normalizer (U : Set X) := hc.2
    have hpN : p ∈ N := hPN hp
    have hcN : c ∈ N := hCN hc.1
    exact ⟨N.mul_mem hpN hcN,
      (Subgroup.normalizer (U : Set X)).mul_mem hpNorm hcNorm⟩

/-- Lemma 10.1(c) gives the `P N_{C_A(P)}(U)` factor in source `(10E)`. -/
public theorem lemma104_normalizerIn_D_sup_eq
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    {q : ℕ} (hq : Nat.Prime q) (hqp : q ≠ d.choice.p)
    {U : Subgroup X}
    (hUC : U ≤ d.choice.initial.A1 ⊓
      Subgroup.centralizer (d.choice.P : Set X))
    (hUq : IsPGroup q U) :
    (normalizerIn D (U ⊔ d.choice.P) : Set X) =
      (d.choice.P : Set X) *
        (normalizerIn (d.choice.initial.A1 ⊓
          Subgroup.centralizer (d.choice.P : Set X)) U : Set X) := by
  let C : Subgroup X := d.choice.initial.A1 ⊓
    Subgroup.centralizer (d.choice.P : Set X)
  let P : Subgroup X := d.choice.P
  let ND : Subgroup X := normalizerIn D P
  have hA1V : d.choice.initial.A1 ≤ peterfalviV D t := by
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hCD : C ≤ D :=
    inf_le_left.trans (hA1V.trans inf_le_left)
  have hCP : C ≤ Subgroup.centralizer (P : Set X) := inf_le_right
  have hPU : P ≤ Subgroup.centralizer (U : Set X) :=
    le_centralizer_of_le_centralizer (hUC.trans hCP)
  have hCN : C ≤ ND := by
    intro x hx
    exact ⟨hCD hx, centralizer_le_normalizer P (hCP hx)⟩
  have hPN : P ≤ ND := by
    have hPD : P ≤ D := by
      rcases d.P_sylow_D with ⟨PD, hPD⟩
      change d.choice.P ≤ D
      rw [hPD]
      exact Subgroup.map_subtype_le (PD : Subgroup D)
    intro x hx
    exact ⟨hPD hx, Subgroup.le_normalizer hx⟩
  have hNset : (ND : Set X) = (C : Set X) * (P : Set X) := by
    simpa [C, P, ND] using d.normalizer_factorization.2.1
  have hsplit : (normalizerIn ND U : Set X) =
      (P : Set X) * (normalizerIn C U : Set X) :=
    normalizer_sup_eq_P_mul_C hCN hPN hUC hCP hPU hNset
  have hsup := lemma104_normalizer_sup_eq d.choice.p_prime hq hqp
    (M := D) (D := D) (P := P) (U := U)
    (hUC.trans hCD) (hUC.trans hCP) hUq d.P_sylow_D
  change (normalizerIn D (U ⊔ P) : Set X) =
    (P : Set X) * (normalizerIn C U : Set X)
  rw [← hsup]
  exact hsplit

/-- A `q`-group is a `π'`-group when `q ∉ π`. -/
public theorem isPiSubgroup_compl_of_isPGroup_of_not_mem
    {G : Type*} [Group G] [Finite G]
    {π : Set Nat.Primes} {Q : Subgroup G} {q : Nat.Primes}
    (hqπ : q ∉ π) (hQq : IsPGroup q.val Q) :
    IsPiSubgroup (G := G) πᶜ Q := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  intro r hr
  rw [Set.mem_compl_iff]
  obtain ⟨n, hcard⟩ := hQq.exists_card_eq
  have hrqDvd : r.val ∣ q.val :=
    r.property.dvd_of_dvd_pow (by simpa [hcard] using hr)
  have hrq : r = q :=
    Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.property q.property).mp hrqDvd)
  simpa [hrq] using hqπ

/-- Source notation `C_A(P)`. -/
@[expose] public def lemma104C
    {X : Type u} [Group X] [Finite X]
    {M W D E V : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E V t) : Subgroup X :=
  d.choice.initial.A1 ⊓ Subgroup.centralizer (d.choice.P : Set X)

/-- Source notation `N = N_M(P)`. -/
@[expose] public def lemma104N
    {X : Type u} [Group X] [Finite X]
    {M W D E V : Subgroup X} {t : X}
  (d : Lemma101Conclusion M W D E V t) : Subgroup X :=
  normalizerIn M d.choice.P

/- Source `(10E)`, converted to the literal factorization required by
`[II1; 4.5]`.  The second conclusion is the centralizer bound used in the
final Frattini argument of Lemma 10.4. -/
public theorem lemma104_10E
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (hDodd : Odd (Nat.card ↥(M ⊓ rightConjugate M t)))
    (q : Nat.Primes) (hqC : q ∈ subgroupPrimeSet (lemma104C d))
    (U : Subgroup X) (hUC : U ≤ lemma104C d) (hUne : U ≠ ⊥)
    (hUq : IsPGroup q.val U) :
    (normalizerIn (lemma104N d) U : Set X) =
        (piCoreIn (subgroupPrimeSet (lemma104C d))ᶜ
            (lemma104N d ⊓ Subgroup.centralizer (U : Set X)) : Set X) *
          (normalizerIn (lemma104C d) U : Set X) ∧
      normalizerIn (lemma104N d) U ≤
        M ⊓ Subgroup.centralizer (d.choice.P : Set X) := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  let P : Subgroup X := d.choice.P
  let C : Subgroup X := lemma104C d
  let N : Subgroup X := lemma104N d
  let Y : Subgroup X := U ⊔ P
  let H : Subgroup X := N ⊓ Subgroup.centralizer (U : Set X)
  let K : Subgroup X := piCoreIn (subgroupPrimeSet C)ᶜ H
  change (normalizerIn N U : Set X) =
      (K : Set X) * (normalizerIn C U : Set X) ∧
    normalizerIn N U ≤ M ⊓ Subgroup.centralizer (P : Set X)
  have hA1V : d.choice.initial.A1 ≤ V := by
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hUA : U ≤ d.choice.initial.A1 := hUC.trans inf_le_left
  have hUV : U ≤ V := hUA.trans hA1V
  have hUD : U ≤ D := hUV.trans inf_le_left
  have hPD : P ≤ D := by
    obtain ⟨PD, hPDmap⟩ := d.P_sylow_D
    have hPD0 : d.choice.P ≤ M ⊓ rightConjugate M t := by
      rw [hPDmap]
      exact Subgroup.map_subtype_le
        (PD : Subgroup (M ⊓ rightConjugate M t : Subgroup X))
    simpa [D, P] using hPD0
  have hCD : C ≤ D :=
    inf_le_left.trans (hA1V.trans inf_le_left)
  have hUP : U ≤ Subgroup.centralizer (P : Set X) := by
    simpa [C, lemma104C, P] using hUC.trans inf_le_right
  have hPU : P ≤ Subgroup.centralizer (U : Set X) :=
    le_centralizer_of_le_centralizer hUP
  have hPnormU : P ≤ Subgroup.normalizer (U : Set X) :=
    hPU.trans (centralizer_le_normalizer U)
  have hPp : IsPGroup d.choice.p P := by
    obtain ⟨PD, hPDmap⟩ := d.P_sylow_D
    have hPp0 : IsPGroup d.choice.p d.choice.P := by
      rw [hPDmap]
      exact PD.isPGroup'.map (M ⊓ rightConjugate M t).subtype
    simpa [P] using hPp0
  have hqnep : q.val ≠ d.choice.p := by
    simpa [C] using d.prime_ne_selected_of_mem_C hqC
  have hNormM : normalizerIn N U = normalizerIn M Y := by
    simpa [D, P, C, N, Y, lemma104N] using
      lemma104_normalizer_sup_eq d.choice.p_prime q.property hqnep
        hUD hUP hUq d.P_sylow_D
  have hNormD : normalizerIn (normalizerIn D P) U = normalizerIn D Y := by
    simpa [D, P, Y] using
      lemma104_normalizer_sup_eq d.choice.p_prime q.property hqnep
        (M := D) hUD hUP hUq d.P_sylow_D
  have hYV : Y ≤ D ⊓ Subgroup.centralizer ({t} : Set X) := by
    have hYV' : Y ≤ V :=
      sup_le hUV (by simpa [P, V, D] using d.choice.P_le_V)
    simpa [D, V, Y, peterfalviV] using hYV'
  have hUnormalY : (U.subgroupOf Y).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
    exact sup_le Subgroup.le_normalizer hPnormU
  have hI : HasNontrivialPeterfalviNormalizer D t U := by
    simpa [D] using
      lemma104_hasNontrivialPeterfalviNormalizer d hUA hUne hPnormU
  obtain ⟨S, hS⟩ := Proposition84Statement.exists_factor_of_normal
    d83 h84 hYV hUne le_sup_left hUnormalY hI
  have hCNDP : C ≤ normalizerIn D P := by
    intro x hx
    exact ⟨hCD hx, centralizer_le_normalizer P
      (by simpa [C, P, lemma104C] using hx.2)⟩
  have hPNDP : P ≤ normalizerIn D P :=
    fun x hx => ⟨hPD hx, Subgroup.le_normalizer hx⟩
  have hC_P : C ≤ Subgroup.centralizer (P : Set X) := by
    simpa [C, P, lemma104C] using
      (inf_le_right : lemma104C d ≤
        Subgroup.centralizer (d.choice.P : Set X))
  have hNDset : (normalizerIn D P : Set X) =
      (C : Set X) * (P : Set X) := by
    simpa [D, P, C, lemma104C] using d.normalizer_factorization.2.1
  have hSecondLocal :
      (normalizerIn (normalizerIn D P) U : Set X) =
        (P : Set X) * (normalizerIn C U : Set X) :=
    normalizer_sup_eq_P_mul_C hCNDP hPNDP (by simpa [C] using hUC)
      hC_P hPU hNDset
  have hSecond :
      (normalizerIn D Y : Set X) =
        (P : Set X) * (normalizerIn C U : Set X) := by
    rw [← hNormD]
    exact hSecondLocal
  have hCodd : Odd (Nat.card C) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hCD)
  let two : Nat.Primes := ⟨2, Nat.prime_two⟩
  have htwoNotC : two ∉ subgroupPrimeSet C := by
    intro htwo
    exact hCodd.not_two_dvd_nat
      (by change 2 ∣ Nat.card C at htwo; exact htwo)
  let p' : Nat.Primes := ⟨d.choice.p, d.choice.p_prime⟩
  have hpNotC : p' ∉ subgroupPrimeSet C := by
    intro hpC
    exact (d.prime_ne_selected_of_mem_C
      (by simpa [C, lemma104C] using hpC)) rfl
  have hSpi : IsPiSubgroup (G := X) (subgroupPrimeSet C)ᶜ S :=
    isPiSubgroup_compl_of_isPGroup_of_not_mem htwoNotC
      (by simpa [two] using hS.isPGroup_two)
  have hPpi : IsPiSubgroup (G := X) (subgroupPrimeSet C)ᶜ P :=
    isPiSubgroup_compl_of_isPGroup_of_not_mem hpNotC
      (by simpa [p'] using hPp)
  have hSCP : S ≤ Subgroup.centralizer (P : Set X) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact Subgroup.mem_centralizer_iff.mp (hS.le_centralizer hs) p
      ((le_sup_right : P ≤ Y) hp)
  have hSCU : S ≤ Subgroup.centralizer (U : Set X) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_iff.mp (hS.le_centralizer hs) u
      ((le_sup_left : U ≤ Y) hu)
  have hSN : S ≤ N := by
    intro s hs
    exact ⟨hS.le_M hs, centralizer_le_normalizer P (hSCP hs)⟩
  have hSH : S ≤ H := fun s hs => ⟨hSN hs, hSCU hs⟩
  have hPN : P ≤ N := by
    intro p hp
    exact ⟨(hPD hp).1, Subgroup.le_normalizer hp⟩
  have hPH : P ≤ H := fun p hp => ⟨hPN hp, hPU hp⟩
  have hHNY : H ≤ normalizerIn M Y := by
    intro x hx
    refine ⟨hx.1.1, ?_⟩
    exact mem_normalizer_sup_of_mem_normalizers
      (centralizer_le_normalizer U hx.2) hx.1.2
  have hNMYnormS : normalizerIn M Y ≤ Subgroup.normalizer (S : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS.le_normalizerIn).mp
      hS.normal_in_normalizerIn
  have hSnormalH : (S.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSH).mpr
      (hHNY.trans hNMYnormS)
  have hPnormalH : (P.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr
      (fun _ hx => hx.1.2)
  have hSK : S ≤ K :=
    section8_le_piCoreIn_of_normal_isPiSubgroup hSH hSnormalH hSpi
  have hPK : P ≤ K :=
    section8_le_piCoreIn_of_normal_isPiSubgroup hPH hPnormalH hPpi
  have hfactor : (normalizerIn N U : Set X) =
      (K : Set X) * (normalizerIn C U : Set X) := by
    ext x
    constructor
    · intro hx
      have hxMY : x ∈ normalizerIn M Y := by
        rw [← hNormM]
        exact hx
      have hxFactor : x ∈
          (S : Set X) * (normalizerIn D Y : Set X) := by
        have hSfactor : (normalizerIn M Y : Set X) =
            (S : Set X) * (normalizerIn D Y : Set X) := by
          simpa [D, normalizerIn] using hS.normalizerIn_eq_mul
        rw [← hSfactor]
        exact hxMY
      rcases hxFactor with ⟨s, hs, z, hz, hsz⟩
      have hzFactor : z ∈
          (P : Set X) * (normalizerIn C U : Set X) := by
        rw [← hSecond]
        exact hz
      rcases hzFactor with ⟨p, hp, c, hc, hpc⟩
      refine ⟨s * p, K.mul_mem (hSK hs) (hPK hp), c, hc, ?_⟩
      calc
        (s * p) * c = s * (p * c) := mul_assoc _ _ _
        _ = s * z := congrArg (s * ·) hpc
        _ = x := hsz
    · rintro ⟨k, hk, c, hc, rfl⟩
      have hkH : k ∈ H :=
        piCoreIn_le (G := X) (subgroupPrimeSet C)ᶜ H hk
      have hkNorm : k ∈ normalizerIn N U :=
        ⟨hkH.1, centralizer_le_normalizer U hkH.2⟩
      have hcNorm : c ∈ normalizerIn N U :=
        ⟨⟨(hCD hc.1).1, centralizer_le_normalizer P (hC_P hc.1)⟩,
          hc.2⟩
      exact (normalizerIn N U).mul_mem hkNorm hcNorm
  refine ⟨hfactor, ?_⟩
  letI : Fact d.choice.p.Prime := ⟨d.choice.p_prime⟩
  letI : IsMulCommutative P :=
    (isCyclic_of_prime_card
      (by simpa [P] using d.P_card)).isMulCommutative
  intro x hx
  have hxM : x ∈ M := hx.1.1
  have hxMY : x ∈ normalizerIn M Y := by
    rw [← hNormM]
    exact hx
  have hxFactor : x ∈ (S : Set X) * (normalizerIn D Y : Set X) := by
    have hSfactor : (normalizerIn M Y : Set X) =
        (S : Set X) * (normalizerIn D Y : Set X) := by
      simpa [D, normalizerIn] using hS.normalizerIn_eq_mul
    rw [← hSfactor]
    exact hxMY
  rcases hxFactor with ⟨s, hs, z, hz, hsz⟩
  have hzFactor : z ∈
      (P : Set X) * (normalizerIn C U : Set X) := by
    rw [← hSecond]
    exact hz
  rcases hzFactor with ⟨p, hp, c, hc, hpc⟩
  refine ⟨hxM, ?_⟩
  have hsCent : s ∈ Subgroup.centralizer (P : Set X) := hSCP hs
  have hpCent : p ∈ Subgroup.centralizer (P : Set X) :=
    Subgroup.le_centralizer P hp
  have hcCent : c ∈ Subgroup.centralizer (P : Set X) := hC_P hc.1
  have hprodCent : s * (p * c) ∈ Subgroup.centralizer (P : Set X) :=
    (Subgroup.centralizer (P : Set X)).mul_mem hsCent
      ((Subgroup.centralizer (P : Set X)).mul_mem hpCent hcCent)
  have hspc : s * (p * c) = x := by
    calc
      s * (p * c) = s * z := congrArg (s * ·) hpc
      _ = x := hsz
  rw [hspc] at hprodCent
  exact hprodCent

/- The final Sylow--Frattini contradiction in Lemma 10.4, separated from
the `(10E)` construction and the `[II1; 4.5]` Hall callback. -/
public theorem Lemma101Conclusion.not_sylow_M_of_C_ne_bot_of_hall
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (hHall : IsHallSubgroup (subgroupPrimeSet (lemma104C d))
      ((lemma104C d).subgroupOf (lemma104N d)))
    (h10E : ∀ q : Nat.Primes, q ∈ subgroupPrimeSet (lemma104C d) →
      ∀ U : Subgroup X, U ≤ lemma104C d → U ≠ ⊥ →
        IsPGroup q.val U →
        normalizerIn (lemma104N d) U ≤
          M ⊓ Subgroup.centralizer (d.choice.P : Set X))
    (hCne : lemma104C d ≠ ⊥) :
    ¬ theorem4bIsSylowSubgroupOf d.choice.p d.choice.P M := by
  classical
  let C : Subgroup X := lemma104C d
  let N : Subgroup X := lemma104N d
  let B : Subgroup X :=
    M ⊓ Subgroup.centralizer (d.choice.P : Set X)
  have hA1V : d.choice.initial.A1 ≤
      peterfalviV (M ⊓ rightConjugate M t) t := by
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hA1M : d.choice.initial.A1 ≤ M :=
    hA1V.trans (inf_le_left.trans inf_le_left)
  have hCB : C ≤ B := by
    intro x hx
    exact ⟨hA1M hx.1, hx.2⟩
  have hBN : B ≤ N := by
    intro x hx
    exact ⟨hx.1, centralizer_le_normalizer d.choice.P hx.2⟩
  have hCN : C ≤ N := hCB.trans hBN
  have hBnormal : (B.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBN]
    apply Subgroup.le_normalizer_inf
    · exact inf_le_left.trans M.le_normalizer
    · exact le_normalizer_centralizer_of_le_normalizer inf_le_right
  have hCcard : Nat.card C ≠ 1 := by
    intro hcard
    apply hCne
    exact (Subgroup.eq_bot_iff_card C).2 hcard
  obtain ⟨q, hqprime, hqC⟩ := Nat.exists_prime_and_dvd hCcard
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hqmem : q' ∈ subgroupPrimeSet C := by
    change q ∣ Nat.card C
    exact hqC
  letI : Fact q.Prime := ⟨hqprime⟩
  let CN : Subgroup N := C.subgroupOf N
  let PC : Sylow q CN :=
    Classical.choice (Sylow.nonempty (p := q) (G := CN))
  obtain ⟨PN, hPN⟩ :=
    isHallSubgroup_sylow_map_to_overgroup_sylow_for_final
      (H := N) (K := CN) (p := q') hHall (by simpa [C] using hqmem) PC
  let UN : Subgroup N := (PC : Subgroup CN).map CN.subtype
  let U : Subgroup X := UN.map N.subtype
  have hUsylN : theorem4bIsSylowSubgroupOf q U N := by
    refine ⟨PN, ?_⟩
    change UN.map N.subtype = (PN : Subgroup N).map N.subtype
    rw [hPN]
  have hUC : U ≤ C := by
    intro x hx
    rcases hx with ⟨n, hnUN, rfl⟩
    rcases hnUN with ⟨c, _hcPC, hc⟩
    subst n
    exact c.property
  have hqCN : q ∣ Nat.card CN := by
    simpa [CN, natCard_subgroupOf_eq C N hCN] using hqC
  have hPCne : (PC : Subgroup CN) ≠ ⊥ := by
    intro hPCbot
    apply PC.not_dvd_index
    have hcardOne : Nat.card (PC : Subgroup CN) = 1 := by
      simp [hPCbot]
    have hmul := Subgroup.card_mul_index (PC : Subgroup CN)
    rw [hcardOne, one_mul] at hmul
    rwa [hmul]
  have hUNne : UN ≠ ⊥ := by
    intro hUNbot
    apply hPCne
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := (PC : Subgroup CN)) (f := CN.subtype)
      CN.subtype_injective).1 hUNbot
  have hUne : U ≠ ⊥ := by
    intro hUbot
    apply hUNne
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := UN) (f := N.subtype) N.subtype_injective).1 hUbot
  have hUp : IsPGroup q U :=
    (PC.isPGroup'.map CN.subtype).map N.subtype
  have hUB : U ≤ B := hUC.trans hCB
  have hUsylB : theorem4bIsSylowSubgroupOf q U B :=
    theorem4bIsSylowSubgroupOf_of_between hqprime hUsylN hUB hBN
  rcases hUsylB with ⟨PB, hPB⟩
  have hfrattini : B ⊔ normalizerIn N U = N :=
    normal_sup_normalizerIn_eq_of_sylow hBN hBnormal PB hPB.symm
  have hnormLe : normalizerIn N U ≤ B := by
    exact h10E q' (by simpa [C] using hqmem) U hUC hUne
      (by simpa [q'] using hUp)
  have hNB : N ≤ B := by
    rw [← hfrattini]
    exact sup_le le_rfl hnormLe
  have hNB_eq : N = B := le_antisymm hNB hBN
  intro hPsylM
  have hstrict : B < N := by
    simpa [B, N, lemma104N, normalizerIn] using
      d.normalizer_growth_if_sylow_M hPsylM
  exact hstrict.ne hNB_eq.symm

/-- The conclusions of source Lemma 10.4. -/
public structure Lemma104Conclusion
    {X : Type u} [Group X] [Finite X]
    (M W D E V : Subgroup X) (t : X)
    (d : Lemma101Conclusion M W D E V t) : Prop where
  C_le_N : lemma104C d ≤ lemma104N d
  C_hall_N :
    IsHallSubgroup (subgroupPrimeSet (lemma104C d))
      ((lemma104C d).subgroupOf (lemma104N d))
  normal_complement :
    ∃ K : Subgroup X, IsNormalComplementIn (lemma104N d) (lemma104C d) K
  P_not_sylow_M_of_C_ne_bot :
    lemma104C d ≠ ⊥ →
      ¬ theorem4bIsSylowSubgroupOf d.choice.p d.choice.P M

/- Source Lemma 10.4.  The only source boundary introduced here is the
literal implication `[II1; 4.5]`; `(10E)` and the Frattini contradiction are
proved internally above. -/
public theorem lemma_10_4
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (_ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h45 : II1Lemma45NormalComplement (X := X)) :
    Lemma104Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t d := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hDM : D ≤ M := inf_le_left
  have hHallFactor : ∀ q : Nat.Primes,
      q ∈ subgroupPrimeSet (lemma104C d) →
      ∀ U : Subgroup X, U ≤ lemma104C d → U ≠ ⊥ →
        IsPGroup q.val U →
        (normalizerIn (lemma104N d) U : Set X) =
          (piCoreIn (subgroupPrimeSet (lemma104C d))ᶜ
              (lemma104N d ⊓ Subgroup.centralizer (U : Set X)) : Set X) *
            (normalizerIn (lemma104C d) U : Set X) := by
    intro q hq U hUC hUne hUq
    exact (lemma104_10E d83 h84 d hDodd q hq U hUC hUne hUq).1
  obtain ⟨hHall, hComplement⟩ := lemma104_apply_II1Lemma45
    d hDM hDodd h45 hHallFactor
  have hBound : ∀ q : Nat.Primes,
      q ∈ subgroupPrimeSet (lemma104C d) →
      ∀ U : Subgroup X, U ≤ lemma104C d → U ≠ ⊥ →
        IsPGroup q.val U →
        normalizerIn (lemma104N d) U ≤
          M ⊓ Subgroup.centralizer (d.choice.P : Set X) := by
    intro q hq U hUC hUne hUq
    exact (lemma104_10E d83 h84 d hDodd q hq U hUC hUne hUq).2
  have hCne : lemma104C d ≠ ⊥ →
      ¬ theorem4bIsSylowSubgroupOf d.choice.p d.choice.P M := by
    intro hCne
    exact d.not_sylow_M_of_C_ne_bot_of_hall hHall hBound hCne
  have hCN : lemma104C d ≤ lemma104N d :=
    (lemma104_C_le_N_and_solvable d hDM hDodd).1
  exact {
    C_le_N := hCN
    C_hall_N := hHall
    normal_complement := hComplement
    P_not_sylow_M_of_C_ne_bot := hCne }

end CFSG.BenderSuzuki
