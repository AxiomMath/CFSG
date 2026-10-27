module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.CoverCentON
public import CFSG.RankThree.PartTwo.KFacts.K426RestON

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Quot

variable {S : Type} [Group S] [Finite S]

theorem good427_of_normal_quot_sq {C : Subgroup S} (E : Subgroup C) [E.Normal] [IsSimpleGroup E]
    (hna : ∃ a b : E, a * b ≠ b * a) (h60 : Nat.card E ≠ 60) {p : ℕ} [Fact p.Prime]
    (hq : Nat.card (C ⧸ E) = p ^ 2) : Good427 C := by
  let eE : E ≃* E.map C.subtype := E.equivMapOfInjective C.subtype C.subtype_injective
  haveI : IsSimpleGroup (E.map C.subtype) := eE.symm.isSimpleGroup
  refine good427_of_derived_le_simple (Subgroup.map_subtype_le E) ?_ ?_ ?_
  · obtain ⟨a, b, hab⟩ := hna
    refine ⟨eE a, eE b, fun h => hab (eE.injective ?_)⟩
    rw [map_mul, map_mul, h]
  · rwa [← Nat.card_congr eE.toEquiv]
  · rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    have hc := IsPGroup.commutative_of_card_eq_prime_sq hq
      (QuotientGroup.mk (⟨g₁, h₁⟩ : C) : C ⧸ E) (QuotientGroup.mk (⟨g₂, h₂⟩ : C))
    have hmem : (⟨g₁, h₁⟩ : C) * ⟨g₂, h₂⟩ * (⟨g₁, h₁⟩ : C)⁻¹ * (⟨g₂, h₂⟩ : C)⁻¹ ∈ E := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hc]
      group
    exact ⟨_, hmem, rfl⟩

theorem good427_of_alt6_normal {C : Subgroup S} (E : Subgroup C) [E.Normal]
    (eE : E ≃* alternatingGroup (Fin 6)) (hq : Nat.card (C ⧸ E) = 9) : Good427 C := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  haveI : IsSimpleGroup E := eE.isSimpleGroup
  have hna : ∃ a b : E, a * b ≠ b * a := by
    have ha : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 0 2) ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    have hb : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    refine ⟨eE.symm ⟨_, ha⟩, eE.symm ⟨_, hb⟩, fun h => ?_⟩
    have h' := congrArg (fun z => ((eE z : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) h
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h'
    revert h'
    decide
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact good427_of_normal_quot_sq (p := 3) E hna
    (by rw [Nat.card_congr eE.toEquiv, hA6]; norm_num) (by rw [hq]; norm_num)

end Quot

section Inner

variable {S : Type} [Group S]

theorem noONS427_of_inner (hZ : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ s : S, orderOf s = 3 →
      ¬ (19 * 31 * 343) ∣ Nat.card (Subgroup.centralizer ({s} : Set S))) :
    NoONS427 S := by
  intro σ h3 h1
  obtain ⟨s, rfl⟩ := cubeInner_of_not_three_dvd_card_outer hout σ h3
  have hs3 : s ^ 3 = 1 := by
    have h' : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, h3]
    have hz : s ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut S => φ g) h'
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [this]
        _ = s ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at hz
    exact hz
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact h1 (map_one _)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [RonanK429H.autFix_conj]
  exact h s (orderOf_eq_prime hs3 hs1)

end Inner

section ON


theorem good427_on (x : Blueprint.NativeSporadic.Carrier .ONan) (hx : orderOf x = 3) :
    Good427 (Subgroup.centralizer ({x} : Set (Blueprint.NativeSporadic.Carrier .ONan))) := by
  haveI : Finite (Blueprint.NativeSporadic.Carrier .ONan) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card Blueprint.NativeSporadic.ON ≠ 0
      rw [CFSG.Sporadic.ON.card_ON]; norm_num)
  obtain ⟨φ, hφ, hker, hconj, hcard⟩ := Census.Karpilovsky.ComponentPrimary.on_cover_data
  obtain ⟨E, hEn, ⟨eE⟩, hq⟩ :=
    Census.Karpilovsky.ComponentPrimary.alt6_normal_of_cover φ hφ hker hcard
  haveI := hEn
  have hg := good427_of_alt6_normal E eE hq
  obtain ⟨g, rfl⟩ := hconj x hx
  exact Good427.of_isConj (isConj_iff.mpr ⟨g, rfl⟩) hg


theorem noCfgS427_on :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .ONan) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  have hZ := RonanK429H.center_eq_bot_of_simple_nonab hna
  have hout := RonanK429H.not_three_dvd_outer_of_mulEquiv e inputs47Core_outON
  refine ⟨noCfgS427_of_inner hZ hout fun s hs =>
    Good427.of_mulEquiv_centralizer e (good427_on (e s) (by rwa [MulEquiv.orderOf_eq])),
    noONS427_of_inner hZ hout fun s hs => ?_⟩
  have hs' : orderOf (e s) = 3 := by rwa [MulEquiv.orderOf_eq]
  have hc := KFacts.K426Rest.onThreeCentralizer (e s) hs'
  have hcard := RonanK429H.card_centralizer_mulEquiv e s
  rw [hcard.symm.trans hc]
  norm_num

end ON

section Row



theorem rowOf427_on
    : RowOf427 (Spor .ONan) :=
  rowOf427_spor CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv noCfgS427_on

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
