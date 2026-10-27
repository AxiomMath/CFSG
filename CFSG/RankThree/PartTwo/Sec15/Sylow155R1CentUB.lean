module

import CFSG.RankThree.PartTwo.Sec11.TwoStarProofLFTools
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.RankThree.PartTwo.Sec3.AlternatingSLTwoLocalRank
import CFSG.RankThree.PartTwo.Sec11.Item116EiiCoprime

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.RankThree.PartTwo.Sec11
open CFSG.RankThree.PartOne.FixedRank36 (fixedSub frattiniRep)
open scoped IsMulCommutative

private theorem res1Cent_exists_fin_rep {K : Type*} [Field K] {X V : Type*} [Group X]
    [AddCommGroup V] [Module K V] [Module.Finite K V] (ρ : X →* (V →ₗ[K] V)) :
    ∃ (n : ℕ) (ρ' : X →* ((Fin n → K) →ₗ[K] (Fin n → K))),
      (∀ x, Module.finrank K (LinearMap.ker (ρ' x - 1)) =
        Module.finrank K (LinearMap.ker (ρ x - 1))) ∧ ∀ x, ρ' x = 1 ↔ ρ x = 1 := by
  let e : V ≃ₗ[K] (Fin (Module.finrank K V) → K) := (Module.finBasis K V).equivFun
  refine ⟨Module.finrank K V,
    { toFun := fun x => e.conjRingEquiv (ρ x)
      map_one' := by simp only [map_one]
      map_mul' := fun x y => by simp only [map_mul] }, fun x => ?_, fun x => ?_⟩
  · have key : ∀ f : V →ₗ[K] V, Module.finrank K (LinearMap.ker (e.conjRingEquiv f)) =
        Module.finrank K (LinearMap.ker f) := by
      intro f
      have hk : LinearMap.ker (e.conjRingEquiv f) = (LinearMap.ker f).map (e : V →ₗ[K] _) := by
        ext w
        constructor
        · intro hw
          refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
          have h0 : e (f (e.symm w)) = 0 := LinearMap.mem_ker.mp hw
          simpa using h0
        · rintro ⟨v, hv, rfl⟩
          change e (f (e.symm (e v))) = 0
          rw [e.symm_apply_apply, LinearMap.mem_ker.mp hv, map_zero]
      rw [hk]
      exact LinearEquiv.finrank_map_eq e _
    have h := key (ρ x - 1)
    rw [map_sub, map_one] at h
    exact h
  · exact map_eq_one_iff _ e.conjRingEquiv.injective

theorem res1Cent_exists_ub_rep {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3) {S X : Subgroup G}
    (hS : IsPGroup p S) (hXS : X ≤ Subgroup.normalizer (S : Set G)) :
    ∃ (n : ℕ) (ρ : ↥X →* ((Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p))),
      (∀ t : ↥X, t ≠ 1 → (∃ k : ℕ, t ^ 2 ^ k = 1) →
        Module.finrank (ZMod p) (LinearMap.ker (ρ t - 1)) ≤ 2) ∧
      ∀ Pi : Subgroup G, Pi ≤ X → Group.IsPerfect Pi →
        (∃ x ∈ Pi, ∃ s ∈ S, x * s * x⁻¹ ≠ s) → ∃ x : ↥X, (x : G) ∈ Pi ∧ ρ x ≠ 1 := by
  have hp : p.Prime := Fact.out
  rcases subsingleton_or_nontrivial ↥S with hsub | hnt
  ·
    refine ⟨0, 1, ?_, ?_⟩
    · intro t _ _
      exact (Submodule.finrank_le _).trans (by simp)
    · rintro Pi _ _ ⟨x, _, s, hs, hxs⟩
      have hs1 : s = 1 := congrArg Subtype.val (Subsingleton.elim (⟨s, hs⟩ : ↥S) 1)
      exact absurd (by rw [hs1]; group) hxs
  ·
    obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
      CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 hS
    have hDp : IsPGroup p D := hS.to_subgroup D
    obtain ⟨-, -, -, hel, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
    have hexp : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by simpa using hDexp x x.2)
    have hclass : commutator D ≤ Subgroup.center D := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := hDcomm (Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_top (b : ↥S)))
      have h2 := Subgroup.mem_centralizer_iff.mp h1.2 g g.2
      apply Subtype.ext
      simpa [commutatorElement_def] using h2
    set ρS : ↥X →* MulAut ↥S := S.normalizerMonoidHom.comp (Subgroup.inclusion hXS)
    set ρD : ↥X →* MulAut ↥D := (Sec3.restrictCharacteristic D).comp ρS with hρD
    have : Module.Finite (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
    obtain ⟨n, ρ', hker, hone⟩ := res1Cent_exists_fin_rep (frattiniRep p ρD)
    refine ⟨n, ρ', ?_, ?_⟩
    ·
      rintro t ht1 ⟨k, htk⟩
      refine le_trans (le_of_eq (hker t)) ?_
      by_contra hlt
      push Not at hlt
      have hrank := TwoStarProof.three_le_pRank_fixed hp2 hDp hexp hclass ρD htk hlt
      have ht1' : (t : G) ≠ 1 := fun h => ht1 (Subtype.ext h)
      have htk' : (t : G) ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val htk
        rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
      have hM : CFSG.Open.IsTwoLocal
          (Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G)) := by
        refine ⟨_, ?_, TwoStarProof.isPGroup_zpowers_of_pow htk', rfl⟩
        intro h1
        apply ht1'
        have : (t : G) ∈ Subgroup.zpowers (t : G) := Subgroup.mem_zpowers _
        rwa [h1, Subgroup.mem_bot] at this
      let ι : ↥D →* G := S.subtype.comp D.subtype
      have hιinj : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
      have hFt : (fixedSub (ρD t)).map ι ≤ Subgroup.centralizer ({(t : G)} : Set G) := by
        rintro _ ⟨y, hy, rfl⟩
        have hy' : ρD t y = y := hy
        have h1 : (t : G) * ι y * (t : G)⁻¹ = ι y := congrArg (fun u : D => ((u : S) : G)) hy'
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc ι y * t = (t : G) * ι y * (t : G)⁻¹ * t := by rw [h1]
          _ = t * ι y := by group
      have hCN : Subgroup.centralizer ({(t : G)} : Set G) ≤
          Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G) := by
        rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
        exact Subgroup.centralizer_le_normalizer ((Subgroup.zpowers (t : G) : Subgroup G) : Set G)
      have h3 : 3 ≤ CFSG.Open.pRank p
          (Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G)) :=
        calc 3 ≤ CFSG.pRank p ↥(fixedSub (ρD t)) := hrank
          _ = CFSG.Open.pRank p (fixedSub (ρD t)) := CFSG.SectionRank.pRank_coe_eq_openPRank p _
          _ ≤ CFSG.Open.pRank p ((fixedSub (ρD t)).map ι) :=
            CFSG.SectionRank.pRank_le_map hp.one_lt ι hιinj _
          _ ≤ _ := CFSG.SectionRank.pRank_mono hp.one_lt (hFt.trans hCN)
      have h4 : CFSG.Open.pRank p (Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G)) ≤
          CFSG.Assembly.RankThreeEven.localRank p G := by
        refine le_csSup ⟨Nat.card G, ?_⟩ ⟨_, hM, rfl⟩
        rintro _ ⟨Z, -, rfl⟩
        exact CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt Z
      omega
    ·
      rintro Pi hPiX hPi ⟨x, hx, s, hs, hxs⟩
      by_contra hcon
      push Not at hcon
      let inc : ↥Pi →* ↥X := Subgroup.inclusion hPiX
      have hD1 : ∀ y : ↥Pi, ρD (inc y) = 1 := by
        refine TwoStarProof.eq_one_of_perfect_of_mem_pGroup (ρD.comp inc)
          (CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup p hDp)
          fun y => ?_
        rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
        intro w
        have h1 := congrArg (fun f => f (Additive.ofMul (QuotientGroup.mk' (frattini D) w)))
          ((hone (inc y)).1 (hcon (inc y) y.2))
        simp only [Module.End.one_apply] at h1
        rw [show Additive.ofMul (QuotientGroup.mk' (frattini D) w) =
          Additive.ofMul ((w : D) : D ⧸ frattini D) from rfl,
          CFSG.RankThree.PartOne.FixedRank36.frattiniRep_apply] at h1
        exact congrArg Additive.toMul h1
      have hS1 : ∀ y : ↥Pi, ρS (inc y) = 1 := by
        refine TwoStarProof.eq_one_of_perfect_of_mem_pGroup (ρS.comp inc) hDfix fun y => ?_
        rw [mem_fixingSubgroup_iff]
        intro d hd
        have h1 := congrArg (fun φ : MulAut ↥D => ((φ ⟨d, hd⟩ : ↥D) : ↥S)) (hD1 y)
        simpa [hρD, Sec3.restrictCharacteristic_apply_coe] using h1
      exact hxs (congrArg (fun φ : MulAut ↥S => ((φ ⟨s, hs⟩ : ↥S) : G)) (hS1 ⟨x, hx⟩))

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
