module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCount
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCountLevi
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootOmega
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmFour
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmMinus
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.StandardType

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup relIndex_omegaGroup)

theorem card_orthDerived_of_type {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W)
    (hR : (polarBilin R).Nondegenerate) {m : ℕ} (hdim : finrank K W = 2 * (m + 1))
    (hΩ : omegaGroup R hR ≤ orthDerived R) {ε : ℤ}
    (hε : (ε = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType R) ∨
      (ε = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType R)) :
    (Nat.card ↥(orthDerived R) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) - ε) *
        ∏ i ∈ Finset.Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1) := by
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have heq : orthDerived R = omegaGroup R hR :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hR) hΩ
  have hle : orthDerived R ≤ TauCeti.QuadraticMap.orthogonalGroup R :=
    Subgroup.commutator_le_self _
  have hidx := relIndex_omegaGroup R hR
  rw [← heq, Subgroup.relIndex] at hidx
  have h1 := Subgroup.card_mul_index ((orthDerived R).subgroupOf
    (TauCeti.QuadraticMap.orthogonalGroup R))
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  have h2 := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := K) hR hdim hε
  have h3 : ((Nat.card ↥(orthDerived R) * 2 : ℕ) : ℤ) = 2 *
      ((Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) - ε) *
        ∏ i ∈ Finset.Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1)) := by
    rw [h1, h2]
    ring
  push_cast at h3
  linarith

private theorem odd_card_pow_sub_one {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) : Odd (Nat.card K ^ n - 1) := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hcard]
  exact CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one f.pos hn

private theorem odd_card_pow_add_one {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) : Odd (Nat.card K ^ n + 1) := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hcard]
  exact CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one f.pos hn

theorem card_orthDerived_eq_ordD {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W)
    (hR : (polarBilin R).Nondegenerate) {m : ℕ} (hdim : finrank K W = 2 * (m + 1))
    (hΩ : omegaGroup R hR ≤ orthDerived R) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType R) :
    Nat.card ↥(orthDerived R) = CFSG.Open.ordD (m + 1) (Nat.card K) := by
  apply Nat.cast_injective (R := ℤ)
  rw [card_orthDerived_of_type R hR hdim hΩ (Or.inl ⟨rfl, hplus⟩), CFSG.Open.ordD,
    CFSG.Timmesfeld.ClassicalOrders.gcd_four_eq_one (odd_card_pow_sub_one (n := m + 1) (by omega)),
    Nat.div_one, Nat.add_sub_cancel]
  have hq1 : (1 : ℕ) ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (Nat.one_le_pow _ _ hq1),
    CFSG.Timmesfeld.ClassicalOrders.cast_prod_pow_sub_one hq1]
  push_cast
  simp only [← pow_mul]
  rw [Nat.mul_comm m (m + 1)]

theorem card_orthDerived_eq_ordTwistedD {K W : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W)
    (hR : (polarBilin R).Nondegenerate) {m : ℕ} (hdim : finrank K W = 2 * (m + 1))
    (hΩ : omegaGroup R hR ≤ orthDerived R) (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType R) :
    Nat.card ↥(orthDerived R) = CFSG.Open.ordTwistedD (m + 1) (Nat.card K) := by
  apply Nat.cast_injective (R := ℤ)
  rw [card_orthDerived_of_type R hR hdim hΩ (Or.inr ⟨rfl, hminus⟩), CFSG.Open.ordTwistedD,
    CFSG.Timmesfeld.ClassicalOrders.gcd_four_eq_one (odd_card_pow_add_one (n := m + 1) (by omega)),
    Nat.div_one, Nat.add_sub_cancel]
  have hq1 : (1 : ℕ) ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
    CFSG.Timmesfeld.ClassicalOrders.cast_prod_pow_sub_one hq1]
  push_cast
  simp only [← pow_mul]
  rw [Nat.mul_comm m (m + 1), sub_neg_eq_add]

theorem not_isPlusType_of_forall_ne_zero {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    {R : QuadraticForm K W} {d : ℕ} (hdim : finrank K W = 2 * d)
    (h : ∀ U : Submodule K W, finrank K U = d → ∃ u ∈ U, R u ≠ 0) :
    ¬ CFSG.GroupTheory.WeirSylow.IsPlusType R := by
  rintro ⟨U, hU, hU0⟩
  obtain ⟨u, hu, hne⟩ := h U (by omega)
  exact hne (hU0 u hu)

end CFSG.StandardType

namespace CFSG.StandardType

theorem card_quotient_center_eq_card_of_center_eq_bot {W : Type} [Group W]
    (h : Subgroup.center W = ⊥) :
    Nat.card (W ⧸ Subgroup.center W) = Nat.card W := by
  rw [h]
  exact Nat.card_congr QuotientGroup.quotientBot.toEquiv

theorem isChevTwoLayeredBy_of_isQuasisimple_of_isChevTwoLayered {W : Type} [Group W]
    (hW : CFSG.Open.IsQuasisimple W) (h : CFSG.LieType.ChevTwo.IsChevTwoLayered W) :
    CFSG.LieType.ChevTwo.IsChevTwoLayeredBy W [Nat.card (W ⧸ Subgroup.center W)] := by
  refine CFSG.LieType.ChevTwo.isChevTwoLayeredBy_of_isQuasisimple hW ?_
  have htop : CFSG.Open.IsComponentOf (⊤ : Subgroup W) ⊤ :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl ⊤,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv (G := W)) hW⟩
  exact CFSG.LieType.ChevTwo.isChevSimple_of_mulEquiv
    (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv
      (Subgroup.topEquiv (G := W))).symm (h.2 ⊤ htop)

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.ChevTwo
open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)

namespace RCSTOm

theorem omFix_isChevTwoLayeredBy_of_quasisimple {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ) (hOE : orthDerived Q ≤ elementaryGroup Q)
    (hΩ : omegaGroup (Q.restrict (wSub P₁ P₂)) (nondegenerate_restrict_wSub hQ h₁₂) ≤
      orthDerived (Q.restrict (wSub P₁ P₂)))
    (hQq : CFSG.IsQuasisimple ↥(orthDerived (Q.restrict (wSub P₁ P₂))))
    (hZ : Subgroup.center ↥(orthDerived (Q.restrict (wSub P₁ P₂))) = ⊥) :
    IsChevTwoLayeredBy ↥(omFix Q P₁ P₂)
      [Nat.card ↥(orthDerived (Q.restrict (wSub P₁ P₂)))] := by
  haveI : Fintype K := Fintype.ofFinite K
  have hL := isChevTwoLayered_orthDerived_of_isQuasisimple _
    (nondegenerate_restrict_wSub hQ h₁₂) hQq
  have hOpen : CFSG.Open.IsQuasisimple ↥(orthDerived (Q.restrict (wSub P₁ P₂))) :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp hQq
  have hBy := isChevTwoLayeredBy_of_isQuasisimple_of_isChevTwoLayered hOpen hL
  rw [card_quotient_center_eq_card_of_center_eq_bot hZ] at hBy
  exact IsChevTwoLayeredBy.of_mulEquiv
    (omFixEquiv h₁₂ hQ hEΩ hOE (nondegenerate_restrict_wSub hQ h₁₂) hΩ) hBy

theorem omFix_isChevTwoLayeredBy_of_totallySingular_plus {K V : Type} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ) (hOE : orthDerived Q ≤ elementaryGroup Q)
    (hT : ∃ T : Submodule K (wSub P₁ P₂), finrank K T = 3 ∧
      ∀ x ∈ T, (Q.restrict (wSub P₁ P₂)) x = 0)
    {m : ℕ} (hdim : finrank K (wSub P₁ P₂) = 2 * (m + 1))
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict (wSub P₁ P₂))) :
    IsChevTwoLayeredBy ↥(omFix Q P₁ P₂) [CFSG.Open.ordD (m + 1) (Nat.card K)] := by
  haveI : Fintype K := Fintype.ofFinite K
  have hR := nondegenerate_restrict_wSub hQ h₁₂
  haveI : Nontrivial ↥(wSub P₁ P₂) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hΩ := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT
  have hcard := card_orthDerived_eq_ordD _ hR hdim hΩ hplus
  simpa [hcard] using omFix_isChevTwoLayeredBy_of_quasisimple h₁₂ hQ hEΩ hOE hΩ
    (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT)
    (CFSG.RankThree.PartOne.center_orthDerived_eq_bot hR hT)

theorem omFix_isChevTwoLayeredBy_of_totallySingular_minus {K V : Type} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ) (hOE : orthDerived Q ≤ elementaryGroup Q)
    (hT : ∃ T : Submodule K (wSub P₁ P₂), finrank K T = 3 ∧
      ∀ x ∈ T, (Q.restrict (wSub P₁ P₂)) x = 0)
    {m : ℕ} (hdim : finrank K (wSub P₁ P₂) = 2 * (m + 1))
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict (wSub P₁ P₂))) :
    IsChevTwoLayeredBy ↥(omFix Q P₁ P₂) [CFSG.Open.ordTwistedD (m + 1) (Nat.card K)] := by
  haveI : Fintype K := Fintype.ofFinite K
  have hR := nondegenerate_restrict_wSub hQ h₁₂
  haveI : Nontrivial ↥(wSub P₁ P₂) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hΩ := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT
  have hcard := card_orthDerived_eq_ordTwistedD _ hR hdim hΩ hminus
  simpa [hcard] using omFix_isChevTwoLayeredBy_of_quasisimple h₁₂ hQ hEΩ hOE hΩ
    (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT)
    (CFSG.RankThree.PartOne.center_orthDerived_eq_bot hR hT)

theorem omFix_isChevTwoLayeredBy_of_four {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ) (hOE : orthDerived Q ≤ elementaryGroup Q)
    (hdim : finrank K (wSub P₁ P₂) = 4)
    (hts : ∀ U : Submodule K (wSub P₁ P₂), finrank K U = 2 → ∃ u ∈ U,
      (Q.restrict (wSub P₁ P₂)) u ≠ 0) :
    IsChevTwoLayeredBy ↥(omFix Q P₁ P₂) [CFSG.Open.ordTwistedD 2 (Nat.card K)] := by
  haveI : Fintype K := Fintype.ofFinite K
  have hR := nondegenerate_restrict_wSub hQ h₁₂
  haveI : Nontrivial ↥(wSub P₁ P₂) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hΩ := omegaGroup_le_orthDerived_of_four hR hdim hts
  obtain ⟨hQq, hZ, -⟩ := isQuasisimple_orthDerived_of_four hR hdim hts
  have hcard := card_orthDerived_eq_ordTwistedD _ hR (m := 1) (by omega) hΩ
    (not_isPlusType_of_forall_ne_zero (by omega) hts)
  simpa [hcard] using omFix_isChevTwoLayeredBy_of_quasisimple h₁₂ hQ hEΩ hOE hΩ hQq hZ

theorem omFix_isChevTwoLayeredBy_of_six {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ) (hOE : orthDerived Q ≤ elementaryGroup Q)
    (hdim : finrank K (wSub P₁ P₂) = 6)
    (hts : ∀ U : Submodule K (wSub P₁ P₂), finrank K U = 3 → ∃ u ∈ U,
      (Q.restrict (wSub P₁ P₂)) u ≠ 0) :
    IsChevTwoLayeredBy ↥(omFix Q P₁ P₂) [CFSG.Open.ordTwistedD 3 (Nat.card K)] := by
  haveI : Fintype K := Fintype.ofFinite K
  have hR := nondegenerate_restrict_wSub hQ h₁₂
  haveI : Nontrivial ↥(wSub P₁ P₂) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hΩ := omegaGroup_le_orthDerived_of_six hR hdim hts
  obtain ⟨hQq, hZ⟩ := isQuasisimple_orthDerived_of_six hR hdim hts
  have hcard := card_orthDerived_eq_ordTwistedD _ hR (m := 2) (by omega) hΩ
    (not_isPlusType_of_forall_ne_zero (by omega) hts)
  simpa [hcard] using omFix_isChevTwoLayeredBy_of_quasisimple h₁₂ hQ hEΩ hOE hΩ hQq hZ

end RCSTOm

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.ChevTwo
open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

namespace RCSTOm

theorem isPlusType_restrict_wSub_of_hypFrame {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {N : ℕ} (F : HypFrame Q N)
    (hdimV : finrank K V = 2 * N) {i j : Fin N} (hij : i ≠ j) (s t : Bool) {c : K}
    (hc : c ≠ 0) :
    CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.restrict (wSub (framePair F j t) (smulPair (framePair F i s) hc))) := by
  classical
  set sf : Finset (Fin N) := (Finset.univ.erase i).erase j with hsf
  have hk_i : ∀ k ∈ sf, i ≠ (k : Fin N) := fun k hk =>
    (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)).symm
  have hk_j : ∀ k ∈ sf, j ≠ (k : Fin N) := fun k hk =>
    (Finset.ne_of_mem_erase hk).symm
  set v : ↥sf → ↥(wSub (framePair F j t) (smulPair (framePair F i s) hc)) :=
    fun k => ⟨F.vec (k : Fin N) true, vec_mem_wSub F (hk_i _ k.2) (hk_j _ k.2) hc true⟩
  have hli : LinearIndependent K v :=
    LinearIndependent.of_comp (Submodule.subtype _)
      (F.linearIndependent_vec (fun _ => true) |>.comp Subtype.val Subtype.val_injective)
  have hcard : Fintype.card ↥sf = N - 2 := by
    rw [Fintype.card_coe, hsf, Finset.card_erase_of_mem (by simp [hij.symm]),
      Finset.card_erase_of_mem (by simp), Finset.card_univ, Fintype.card_fin]
    omega
  have hdimT : finrank K ↥(Submodule.span K (Set.range v)) = N - 2 := by
    rw [finrank_span_eq_card hli, hcard]
  have hdimW : finrank K (wSub (framePair F j t) (smulPair (framePair F i s) hc)) = 2 * N - 4 := by
    have := finrank_wSub_add_four (Q := Q) (orth₁₂ F hij s t hc)
    omega
  refine ⟨Submodule.span K (Set.range v), ?_, ?_⟩
  · rw [hdimT, hdimW]
    omega
  · intro x hx
    have hx' : (x : V) ∈ Submodule.span K (Set.range (fun k : ↥sf => F.vec (k : Fin N) true)) := by
      have hmap : Submodule.map (Submodule.subtype
          (wSub (framePair F j t) (smulPair (framePair F i s) hc)))
          (Submodule.span K (Set.range v)) =
          Submodule.span K (Set.range (fun k : ↥sf => F.vec (k : Fin N) true)) := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      rw [← hmap]
      exact Submodule.mem_map_of_mem hx
    exact CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span
      (S := Set.range (fun k : ↥sf => F.vec (k : Fin N) true))
      (fun u hu => by obtain ⟨k, rfl⟩ := hu; exact F.map_vec _ _)
      (fun u hu w hw => by
        obtain ⟨k, rfl⟩ := hu
        obtain ⟨l, rfl⟩ := hw
        by_cases hkl : k = l
        · subst hkl
          rw [QuadraticMap.polar_self, F.map_vec, smul_zero]
        · exact F.polar_vec_of_ne (fun h => hkl (Subtype.ext h)) true true) hx'

theorem ggInvolCentTypedBy_frame {K V : Type} [Field K] [Fintype K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {P₁ P₂ : HypPair Q}
    (hQ : (polarBilin Q).Nondegenerate) (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hOE : orthDerived Q ≤ elementaryGroup Q) (h₁₂ : P₁.Orth P₂) {oW : List ℕ}
    (hW : IsChevTwoLayeredBy ↥(omFix Q P₁ P₂) oW)
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U} (hx : σ x = eichler Q P₁.e P₂.e)
    {G : Type} [Group G] [Finite G] (ψ : U →* G) (hψ : Function.Injective ψ) (u : U) :
    GGInvolCentTypedBy ψ.range (ψ (u * x * u⁻¹))
      (CFSG.Open.ordA 1 (Fintype.card K) :: oW) := by
  haveI : Finite K := Finite.of_fintype K
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hE : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  set φ := ψ.comp (MulAut.conj u).toMonoidHom with hφdef
  have hφ : Function.Injective φ := RCSTSp.comp_conj_injective hψ u
  have hφr : φ.range = ψ.range := RCSTSp.range_comp_conj ψ u
  have hr : ψ (u * x * u⁻¹) = φ x := by
    simp only [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hr, ← hφr]
  have hRE : rootRadical Q P₁ P₂ ≤ σ.range := hσE ▸ rootRadical_le_elementaryGroup h₁₂
  have hL₁E : leviFix (elementaryGroup Q) P₁ P₂ ≤ σ.range :=
    hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hL₂E : omFix Q P₁ P₂ ≤ σ.range :=
    hσE ▸ fun g hg => (mem_omFix.mp hg).1
  set QG := Φ σ φ (rootRadical Q P₁ P₂) with hQGdef
  set AG := Φ σ φ (leviFix (elementaryGroup Q) P₁ P₂) with hAGdef
  set BG := Φ σ φ (omFix Q P₁ P₂) with hBGdef
  have hsup : QG ⊔ (AG ⊔ BG) =
      Φ σ φ (rootRadical Q P₁ P₂ ⊔ leviFix (elementaryGroup Q) P₁ P₂ ⊔ omFix Q P₁ P₂) := by
    rw [Φ_sup hσ φ (sup_le hRE hL₁E) hL₂E, Φ_sup hσ φ hRE hL₁E, sup_assoc]
  have hcen : QG ⊔ (AG ⊔ BG) = centralizer ({φ x} : Set G) ⊓ φ.range := by
    rw [inf_comm, ggRCQL_range_inf_centralizer hφ x, centralizer_eq_comap hσ hσE x, hx,
      centralizer_inf_elementaryGroup_eq h₁₂, hsup]
    rfl
  have hQ2 : IsPGroup 2 QG := Φ_isPGroup φ hσ isPGroup_rootRadical
  have hLQ : AG ⊔ BG ≤ normalizer (QG : Set G) := by
    have h := Φ_le_normalizer (σ := σ) φ (sup_le (leviFix_le_normalizer_rootRadical h₁₂)
      (omFix_le_normalizer_rootRadical h₁₂))
    rwa [Φ_sup hσ φ hL₁E hL₂E] at h
  have h12 : AG ≤ centralizer (BG : Set G) :=
    Φ_le_centralizer hσ φ (leviFix_le_centralizer_omFix h₁₂)
  have hAG : IsChevTwoLayeredBy ↥AG [CFSG.Open.ordA 1 (Fintype.card K)] :=
    IsChevTwoLayeredBy.of_mulEquiv ((Φ_equiv hσ φ hφ hL₁E).trans (leviFixEquiv P₁ P₂ h₁₂ hE))
      (isChevTwoLayeredBy_specialLinear (Fin 2) K)
  have hBG : IsChevTwoLayeredBy ↥BG oW :=
    IsChevTwoLayeredBy.of_mulEquiv (Φ_equiv hσ φ hφ hL₂E) hW
  have hL : IsChevTwoLayeredBy ↥(AG ⊔ BG) (CFSG.Open.ordA 1 (Fintype.card K) :: oW) := by
    have h := IsChevTwoLayeredBy.of_commute_sup (AG.subgroupOf (AG ⊔ BG))
      (BG.subgroupOf (AG ⊔ BG))
      (fun a ha b hb => by
        refine (commute_iff_eq a b).mpr (Subtype.ext ?_)
        exact (mem_centralizer_iff.mp (h12 ha) (b : G) hb).symm)
      (by rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self])
      (hAG.of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_left))
      (hBG.of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_right))
    simpa using h
  exact ggInvolCentTypedBy_of_sup_eq hQ2 hLQ hcen hL

end RCSTOm

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.ChevTwo
open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

namespace RCSTOm

theorem omFix_isChevTwoLayeredBy_of_splitFour {K V : Type} [Field K] [Fintype K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {P₁ P₂ P₃ P₄ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₃₄ : P₃.Orth P₄) (h₁₃ : P₁.Orth P₃)
    (h₁₄ : P₁.Orth P₄) (h₂₃ : P₂.Orth P₃) (h₂₄ : P₂.Orth P₄)
    (hQ : (polarBilin Q).Nondegenerate) (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hOE : orthDerived Q ≤ elementaryGroup Q)
    (hdim : finrank K (wSub P₁ P₂) = 4)
    (hS : ∃ S : Submodule K (wSub P₁ P₂), finrank K S = 2 ∧
      ∀ x ∈ S, (Q.restrict (wSub P₁ P₂)) x = 0) :
    IsChevTwoLayeredBy ↥(omFix Q P₁ P₂)
      [CFSG.Open.ordA 1 (Fintype.card K), CFSG.Open.ordA 1 (Fintype.card K)] := by
  haveI : Finite K := Finite.of_fintype K
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Fintype ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (wSub P₁ P₂))) :=
    Fintype.ofFinite _
  have hE : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  have hR := nondegenerate_restrict_wSub hQ h₁₂
  rcases card_eq_two_or_four_le K with hK | hK
  ·
    obtain ⟨S, hSdim, hSsing⟩ := hS
    have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict (wSub P₁ P₂)) :=
      ⟨S, by rw [hSdim, hdim], hSsing⟩
    have hcardO : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.restrict (wSub P₁ P₂))) = 2 ^ 3 * 3 ^ 2 := by
      have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (Q := Q.restrict
        (wSub P₁ P₂)) hR (m := 1) (by rw [hdim]) (Or.inl ⟨rfl, hplus⟩)
      rw [hK, Finset.Icc_self, Finset.prod_singleton] at h
      have h' : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (wSub P₁ P₂))) :
          ℤ) = ((2 ^ 3 * 3 ^ 2 : ℕ) : ℤ) := by
        rw [h]
        norm_num
      exact Nat.cast_injective h'
    have hOsolv : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.restrict (wSub P₁ P₂))) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        (p := 2) (q := 3) (a := 3) (b := 2) (by norm_num) (by norm_num) (by norm_num)
        (by rw [← Nat.card_eq_fintype_card]; exact hcardO)
    have hOm : Group.IsSolvable ↥(omFix Q P₁ P₂) := by
      let ρ : ↥(omFix Q P₁ P₂) →* ↥(TauCeti.QuadraticMap.orthogonalGroup
          (Q.restrict (wSub P₁ P₂))) :=
        { toFun := fun g => ⟨resW Q P₁ P₂ g, resW_mem_orthogonalGroup g⟩
          map_one' := Subtype.ext (map_one (resW Q P₁ P₂))
          map_mul' := fun a b => Subtype.ext (map_mul (resW Q P₁ P₂) a b) }
      have hρ : Function.Injective ρ := fun a b hab =>
        resW_injective h₁₂ (congrArg Subtype.val hab)
      haveI := hOsolv
      exact Group.isSolvable_of_isSolvable_injective hρ
    exact isChevTwoLayeredBy_of_isSolvable hOm _
  ·
    have hΩ := omegaGroup_le_orthDerived_of_splitFour hR hdim hS hK
    have hcardR := card_orthDerived_le_four hR hdim hS hK
    have hLa : leviFix (elementaryGroup Q) P₃ P₄ ≤ omFix Q P₁ P₂ :=
      leviFix_le_omFix h₁₃ h₁₄ h₂₃ h₂₄
    have hLb : leviFix (elementaryGroup Q) P₃ (flipPair P₄) ≤ omFix Q P₁ P₂ :=
      leviFix_le_omFix h₁₃ (orth_flip h₁₄) h₂₃ (orth_flip h₂₄)
    have hab : leviFix (elementaryGroup Q) P₃ P₄ ≤
        centralizer (leviFix (elementaryGroup Q) P₃ (flipPair P₄) : Set (V ≃ₗ[K] V)) :=
      leviFix_le_centralizer_flip h₃₄ hE hE
    have hdisj : leviFix (elementaryGroup Q) P₃ P₄ ⊓
        leviFix (elementaryGroup Q) P₃ (flipPair P₄) = ⊥ := leviFix_inf_flip_eq_bot h₃₄
    have hcard' : Nat.card (omFix Q P₁ P₂) ≤
        Nat.card (leviFix (elementaryGroup Q) P₃ P₄) *
          Nat.card (leviFix (elementaryGroup Q) P₃ (flipPair P₄)) := by
      rw [Nat.card_congr (omFixEquiv h₁₂ hQ hEΩ hOE hR hΩ).toEquiv,
        Nat.card_congr (leviFixEquiv P₃ P₄ h₃₄ hE).toEquiv,
        Nat.card_congr (leviFixEquiv P₃ (flipPair P₄) (orth_flip h₃₄) hE).toEquiv, ← _root_.sq]
      exact hcardR
    have hgen : omFix Q P₁ P₂ = leviFix (elementaryGroup Q) P₃ P₄ ⊔
        leviFix (elementaryGroup Q) P₃ (flipPair P₄) := by
      refine le_antisymm (fun g hg => ?_) (sup_le hLa hLb)
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_card_le hLa hLb hab hdisj hcard' g hg
      exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
    rw [hgen]
    refine IsChevTwoLayeredBy.of_commute_sup
      (K₁ := (leviFix (elementaryGroup Q) P₃ P₄).subgroupOf
        (leviFix (elementaryGroup Q) P₃ P₄ ⊔ leviFix (elementaryGroup Q) P₃ (flipPair P₄)))
      (K₂ := (leviFix (elementaryGroup Q) P₃ (flipPair P₄)).subgroupOf
        (leviFix (elementaryGroup Q) P₃ P₄ ⊔ leviFix (elementaryGroup Q) P₃ (flipPair P₄)))
      (o₁ := [CFSG.Open.ordA 1 (Fintype.card K)])
      (o₂ := [CFSG.Open.ordA 1 (Fintype.card K)]) ?_ ?_ ?_ ?_
    · intro a ha b hb
      refine (commute_iff_eq a b).mpr (Subtype.ext ?_)
      exact (mem_centralizer_iff.mp (hab ha) (b : V ≃ₗ[K] V) hb).symm
    · rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    · refine IsChevTwoLayeredBy.of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_left) ?_
      exact IsChevTwoLayeredBy.of_mulEquiv (leviFixEquiv P₃ P₄ h₃₄ hE)
        (isChevTwoLayeredBy_specialLinear (Fin 2) K)
    · refine IsChevTwoLayeredBy.of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_right) ?_
      exact IsChevTwoLayeredBy.of_mulEquiv (leviFixEquiv P₃ (flipPair P₄) (orth_flip h₃₄) hE)
        (isChevTwoLayeredBy_specialLinear (Fin 2) K)

theorem omFix_isChevTwoLayeredBy_minus_small {n : ℕ} {K : Type} [Field K] [Fintype K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) {a : K} (ha : a ≠ 0) :
    IsChevTwoLayeredBy ↥(omFix (quadMinus n K b c)
      (framePair (minusFrame n b c).toHypFrame j t)
      (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha))
      [CFSG.Open.ordTwistedD (n - 2) (Nat.card K)] := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have h₁₂ := orth₁₂ (minusFrame n b c).toHypFrame hij s t ha
  have hdimW : finrank K (wSub (framePair (minusFrame n b c).toHypFrame j t)
      (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)) = 2 * n - 4 := by
    have := finrank_wSub_add_four (Q := quadMinus n K b c) h₁₂
    rw [finrank_quadMinus (by omega)] at this
    omega
  have hEΩ := elementaryGroup_quadMinus_le_omegaGroup hirr hn4
  have hOE : orthDerived (quadMinus n K b c) ≤ elementaryGroup (quadMinus n K b c) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadMinus hn4 hirr]
  have hts : ∀ U : Submodule K (wSub (framePair (minusFrame n b c).toHypFrame j t)
      (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)), finrank K U = n - 2 →
      ∃ u ∈ U, (quadMinus n K b c).restrict
        (wSub (framePair (minusFrame n b c).toHypFrame j t)
          (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)) u ≠ 0 := fun U hU =>
    exists_restrict_ne_zero_minus (by omega) hirr h₁₂ U hU
  rcases (show n = 4 ∨ n = 5 by omega) with rfl | rfl
  · have hdim : finrank K (wSub (framePair (minusFrame 4 b c).toHypFrame j t)
        (smulPair (framePair (minusFrame 4 b c).toHypFrame i s) ha)) = 4 := by rw [hdimW]
    exact omFix_isChevTwoLayeredBy_of_four h₁₂ hQ hEΩ hOE hdim hts
  · have hdim : finrank K (wSub (framePair (minusFrame 5 b c).toHypFrame j t)
        (smulPair (framePair (minusFrame 5 b c).toHypFrame i s) ha)) = 6 := by rw [hdimW]
    exact omFix_isChevTwoLayeredBy_of_six h₁₂ hQ hEΩ hOE hdim hts

end RCSTOm

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.ChevTwo
open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

namespace RCSTOm

theorem omFix_isChevTwoLayeredBy_frame_four {K V : Type} [Field K] [Fintype K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (F : HypFrame Q 4) (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ) (hOE : orthDerived Q ≤ elementaryGroup Q)
    (hF0 : ∀ x : V, (∀ k u, polar Q (F.vec k u) x = 0) → x = 0) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (s t : Bool) {c : K} (hc : c ≠ 0) :
    IsChevTwoLayeredBy ↥(omFix Q (framePair F j t) (smulPair (framePair F i s) hc))
      [CFSG.Open.ordA 1 (Fintype.card K), CFSG.Open.ordA 1 (Fintype.card K)] := by
  have h₁₂ := orth₁₂ F hij s t hc
  have h₁₃ := orth₁₃ F hjk t true
  have h₁₄ := orth₁₃ F hjl t true
  have h₂₃ := orth₂₃ F hik s true hc
  have h₂₄ := orth₂₃ F hil s true hc
  have h₃₄ := framePair_orth F hkl true true
  have hspan : ∀ w, InW (framePair F j t) (smulPair (framePair F i s) hc) w →
      w = polar Q w (framePair F k true).f • (framePair F k true).e +
        polar Q w (framePair F k true).e • (framePair F k true).f +
        (polar Q w (framePair F l true).f • (framePair F l true).e +
          polar Q w (framePair F l true).e • (framePair F l true).f) := fun w hw =>
    eq_comb_of_inW_four F hF0 hij hik hil hjk hjl hkl hc hw
  have hWeq : wSub (framePair F j t) (smulPair (framePair F i s) hc) =
      spanU₄ (framePair F k true) (framePair F l true) := by
    apply le_antisymm
    · intro w hw
      rw [hspan w (mem_wSub.mp hw)]
      exact add_mem (add_mem (Submodule.smul_mem _ _ mem_spanU₄_e₁)
        (Submodule.smul_mem _ _ mem_spanU₄_f₁))
        (add_mem (Submodule.smul_mem _ _ mem_spanU₄_e₂) (Submodule.smul_mem _ _ mem_spanU₄_f₂))
    · rw [spanU₄, Submodule.span_le]
      rintro _ (rfl | rfl | rfl | rfl)
      · exact vec_mem_wSub F hik hjk hc true
      · exact vec_mem_wSub F hil hjl hc true
      · exact vec_mem_wSub F hik hjk hc false
      · exact vec_mem_wSub F hil hjl hc false
  have hdim : finrank K (wSub (framePair F j t) (smulPair (framePair F i s) hc)) = 4 := by
    rw [hWeq, finrank_spanU₄ h₃₄]
  exact omFix_isChevTwoLayeredBy_of_splitFour h₁₂ h₃₄ h₁₃ h₁₄ h₂₃ h₂₄ hQ hEΩ hOE hdim
    (exists_totallySingular_two (R := Q.restrict (wSub (framePair F j t)
      (smulPair (framePair F i s) hc)))
      (orth_restrictPair h₃₄ (vec_mem_wSub F hik hjk hc true) (vec_mem_wSub F hik hjk hc false)
        (vec_mem_wSub F hil hjl hc true) (vec_mem_wSub F hil hjl hc false)))

end RCSTOm

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.ChevTwo
open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

section Tags

theorem ggRootInvolCountTag_POmegaPlus : GGRootInvolCountTag .POmegaPlus := by
  intro X _ _ n f ψ hadm _ hker _ r hr
  obtain ⟨-, hf1, hn4⟩ := hadm
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hn : 3 ≤ n := by omega
  revert ψ
  rw [ggU_POmegaPlus_eq hn]
  intro ψ hker hC hr
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn).le
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  obtain ⟨i, j, hij, s, t, -, hX⟩ := exists_plusRootGroup_eq (K := GaloisField 2 f) hn hγ
  have hx' : x ∈ ((plusFrame n (GaloisField 2 f) hn).longRoot hij s t).range := by
    rw [← hX]
    exact hx
  obtain ⟨c₀, rfl⟩ := hx'
  have hc : Multiplicative.toAdd c₀ ≠ 0 := by
    intro h0
    have hc₀ : c₀ = 1 := by rw [← ofAdd_toAdd c₀, h0, ofAdd_zero]
    rw [hc₀, map_one, mul_one, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hσx : spinAction (quadPlus n (GaloisField 2 f))
      ((plusFrame n (GaloisField 2 f) hn).longRoot hij s t c₀) =
      eichler (quadPlus n (GaloisField 2 f)) ((plusFrame n (GaloisField 2 f) hn).vec j t)
        (Multiplicative.toAdd c₀ • (plusFrame n (GaloisField 2 f) hn).vec i s) := by
    rw [← RootCentOmega.spinAction_longRoot_eq_eichler, ofAdd_toAdd]
  have hOE : orthDerived (quadPlus n (GaloisField 2 f)) ≤
      elementaryGroup (quadPlus n (GaloisField 2 f)) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadPlus hn]
  have hcardN : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by omega)
  have hcardF : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardN
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
  · obtain ⟨k, l, hik, hil, hjk, hjl, hkl⟩ := RCSTOm.exists_two_ne le_rfl i j
    have hW := RCSTOm.omFix_isChevTwoLayeredBy_frame_four (plusFrame 4 (GaloisField 2 f) hn)
      (nondegenerate_polarBilin_quadPlus 4 (GaloisField 2 f))
      (RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn) hOE
      (fun x hx => RootCentOmega.eq_zero_of_polar_plusVec hx) hij hik hil hjk hjl hkl s t hc
    refine ⟨[CFSG.Open.ordA 1 (2 ^ f), CFSG.Open.ordA 1 (2 ^ f), CFSG.Open.ordA 1 (2 ^ f)],
      by simp [ggRootFactorOrders], ?_⟩
    have h := RCSTOm.ggInvolCentTypedBy_frame
      (P₁ := framePair (plusFrame 4 (GaloisField 2 f) hn) j t)
      (P₂ := smulPair (framePair (plusFrame 4 (GaloisField 2 f) hn) i s) hc)
      (nondegenerate_polarBilin_quadPlus 4 (GaloisField 2 f))
      (RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn) hOE
      (RCSTOm.orth₁₂ (plusFrame 4 (GaloisField 2 f) hn) hij s t hc) hW
      (RootCentOmega.spinAction_quadPlus_injective)
      (CFSG.LieType.Universal.Spin.range_spinAction_quadPlus hn) hσx ψ hinj u
    simpa [hcardF] using h
  · obtain ⟨k, l, m, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm⟩ :=
      RCSTOm.exists_three_ne hn5 i j
    have hdimW : finrank (GaloisField 2 f)
        (RCSTOm.wSub (framePair (plusFrame n (GaloisField 2 f) hn) j t)
          (smulPair (framePair (plusFrame n (GaloisField 2 f) hn) i s) hc)) = 2 * n - 4 := by
      have h := RCSTOm.finrank_wSub_add_four (Q := quadPlus n (GaloisField 2 f))
        (RCSTOm.orth₁₂ (plusFrame n (GaloisField 2 f) hn) hij s t hc)
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h
      omega
    have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
        ((quadPlus n (GaloisField 2 f)).restrict
          (RCSTOm.wSub (framePair (plusFrame n (GaloisField 2 f) hn) j t)
            (smulPair (framePair (plusFrame n (GaloisField 2 f) hn) i s) hc))) :=
      RCSTOm.isPlusType_restrict_wSub_of_hypFrame (plusFrame n (GaloisField 2 f) hn)
        (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; ring)
        hij s t hc
    have hdim' : finrank (GaloisField 2 f)
        (RCSTOm.wSub (framePair (plusFrame n (GaloisField 2 f) hn) j t)
          (smulPair (framePair (plusFrame n (GaloisField 2 f) hn) i s) hc)) =
        2 * ((n - 3) + 1) := by
      rw [hdimW]
      omega
    have hW := RCSTOm.omFix_isChevTwoLayeredBy_of_totallySingular_plus
      (RCSTOm.orth₁₂ (plusFrame n (GaloisField 2 f) hn) hij s t hc)
      (nondegenerate_polarBilin_quadPlus n (GaloisField 2 f))
      (RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn) hOE
      (RCSTOm.exists_totallySingular_wSub (plusFrame n (GaloisField 2 f) hn) hik hil him hjk
        hjl hjm hkl hkm hlm s t hc) hdim' hplus
    rw [show (n - 3) + 1 = n - 2 by omega] at hW
    refine ⟨[CFSG.Open.ordA 1 (2 ^ f), CFSG.Open.ordD (n - 2) (2 ^ f)],
      by simp [ggRootFactorOrders, show n ≠ 4 by omega], ?_⟩
    have h := RCSTOm.ggInvolCentTypedBy_frame
      (P₁ := framePair (plusFrame n (GaloisField 2 f) hn) j t)
      (P₂ := smulPair (framePair (plusFrame n (GaloisField 2 f) hn) i s) hc)
      (nondegenerate_polarBilin_quadPlus n (GaloisField 2 f))
      (RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn) hOE
      (RCSTOm.orth₁₂ (plusFrame n (GaloisField 2 f) hn) hij s t hc) hW
      (RootCentOmega.spinAction_quadPlus_injective)
      (CFSG.LieType.Universal.Spin.range_spinAction_quadPlus hn) hσx ψ hinj u
    simpa [hcardF, hcardN] using h

theorem ggRootInvolCountTag_POmegaMinus : GGRootInvolCountTag .POmegaMinus := by
  intro X _ _ n f ψ hadm _ hker _ r hr
  obtain ⟨-, hf1, hn⟩ := hadm
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hirr := CFSG.LieType.Universal.minusCoeffs_irr 2 f
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (PsiDiag.SpinM.center_eq_bot (K := GaloisField 2 f) hirr hn).le
  obtain ⟨hr2, γ, ⟨-, hγl⟩, u, hru⟩ := hr
  obtain ⟨i, j, hij, s, t, hst⟩ :=
    RootCentOmega.exists_long_of_ggLongRoot_minus hirr hn (hγl (Or.inr (Or.inl rfl)))
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hr2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  obtain ⟨a, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hst).mp hx
  have ha : a ≠ 0 := by
    rintro rfl
    exact hx1 (map_one _)
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f) hirr
  have hEΩ := elementaryGroup_quadMinus_le_omegaGroup hirr hn
  have hOE : orthDerived (quadMinus n (GaloisField 2 f) (CFSG.LieType.Universal.minusCoeffs 2 f).1
      (CFSG.LieType.Universal.minusCoeffs 2 f).2) ≤
      elementaryGroup (quadMinus n (GaloisField 2 f)
        (CFSG.LieType.Universal.minusCoeffs 2 f).1
        (CFSG.LieType.Universal.minusCoeffs 2 f).2) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadMinus hn hirr]
  have hcardN : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hcardF : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardN
  rcases (show n ≤ 5 ∨ 6 ≤ n by omega) with hn5 | hn6
  · have hW := RCSTOm.omFix_isChevTwoLayeredBy_minus_small
      (K := GaloisField 2 f) hirr hn hn5 hij s t ha
    refine ⟨[CFSG.Open.ordA 1 (2 ^ f), CFSG.Open.ordTwistedD (n - 2) (2 ^ f)],
      by simp [ggRootFactorOrders], ?_⟩
    have h := RCSTOm.ggInvolCentTypedBy_frame
      (P₁ := framePair (minusFrame n (CFSG.LieType.Universal.minusCoeffs 2 f).1
        (CFSG.LieType.Universal.minusCoeffs 2 f).2).toHypFrame j t)
      (P₂ := smulPair (framePair (minusFrame n (CFSG.LieType.Universal.minusCoeffs 2 f).1
        (CFSG.LieType.Universal.minusCoeffs 2 f).2).toHypFrame i s) ha)
      hQ hEΩ hOE (RCSTOm.orth₁₂ _ hij s t ha) hW
      (RootCentOmega.spinAction_quadMinus_injective hirr)
      (CFSG.LieType.Universal.Spin.range_spinAction_quadMinus hn hirr)
      (RootCentOmega.spinAction_longRoot_eq_eichler
        (minusFrame n (CFSG.LieType.Universal.minusCoeffs 2 f).1
          (CFSG.LieType.Universal.minusCoeffs 2 f).2).toHypFrame hij s t a) ψ hinj u
    simp only [hcardF, hcardN] at h
    exact h
  · set F := (minusFrame n (CFSG.LieType.Universal.minusCoeffs 2 f).1
      (CFSG.LieType.Universal.minusCoeffs 2 f).2).toHypFrame with hF
    have h₁₂ : (framePair F j t).Orth (smulPair (framePair F i s) ha) :=
      RCSTOm.orth₁₂ F hij s t ha
    obtain ⟨k, l, m, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm⟩ :=
      RCSTOm.exists_three_ne (by omega : 5 ≤ n - 1) i j
    have hdimW : finrank (GaloisField 2 f) (RCSTOm.wSub (framePair F j t)
        (smulPair (framePair F i s) ha)) = 2 * n - 4 := by
      have h := RCSTOm.finrank_wSub_add_four (Q := quadMinus n (GaloisField 2 f)
        (CFSG.LieType.Universal.minusCoeffs 2 f).1
        (CFSG.LieType.Universal.minusCoeffs 2 f).2) h₁₂
      rw [RCSTOm.finrank_quadMinus (by omega)] at h
      omega
    have hneg : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
        ((quadMinus n (GaloisField 2 f) (CFSG.LieType.Universal.minusCoeffs 2 f).1
            (CFSG.LieType.Universal.minusCoeffs 2 f).2).restrict
          (RCSTOm.wSub (framePair F j t) (smulPair (framePair F i s) ha))) :=
      not_isPlusType_of_forall_ne_zero (d := n - 2) (by rw [hdimW]; omega)
        (fun U hU => RCSTOm.exists_restrict_ne_zero_minus (by omega) hirr h₁₂ U hU)
    have hdim' : finrank (GaloisField 2 f) (RCSTOm.wSub (framePair F j t)
        (smulPair (framePair F i s) ha)) = 2 * ((n - 3) + 1) := by
      rw [hdimW]
      omega
    have hW := RCSTOm.omFix_isChevTwoLayeredBy_of_totallySingular_minus h₁₂
      (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f) hirr) hEΩ hOE
      (RCSTOm.exists_totallySingular_wSub F hik hil him hjk hjl hjm hkl hkm hlm s t ha)
      hdim' hneg
    rw [show (n - 3) + 1 = n - 2 by omega] at hW
    refine ⟨[CFSG.Open.ordA 1 (2 ^ f), CFSG.Open.ordTwistedD (n - 2) (2 ^ f)],
      by simp [ggRootFactorOrders], ?_⟩
    have h := RCSTOm.ggInvolCentTypedBy_frame
      (P₁ := framePair F j t) (P₂ := smulPair (framePair F i s) ha)
      (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f) hirr) hEΩ hOE h₁₂ hW
      (RootCentOmega.spinAction_quadMinus_injective hirr)
      (CFSG.LieType.Universal.Spin.range_spinAction_quadMinus hn hirr)
      (RootCentOmega.spinAction_longRoot_eq_eichler F hij s t a) ψ hinj u
    simp only [hcardF, hcardN] at h
    exact h

end Tags

end CFSG.StandardType
