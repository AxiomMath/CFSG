module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmNonsing
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmIso
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2OmegaPts

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega MulAction

@[expose] def OmX (s t u : F6) : Prop :=
  u ≠ 0 ∧ qMinus u = 0 ∧ polarMinus u s = 0 ∧ polarMinus u t = 0

instance (s t u : F6) : Decidable (OmX s t u) := by
  unfold OmX
  infer_instance

@[expose] def OmPairHyp (p : F6 × F6) : Prop :=
  qMinus p.1 = 1 ∧ qMinus p.2 = 0 ∧ qMinus (p.1 + p.2) = 0 ∧ p.2 ≠ 0

instance (p : F6 × F6) : Decidable (OmPairHyp p) := by
  unfold OmPairHyp
  infer_instance

private theorem omPair_card :
    (Finset.univ.filter fun p : F6 × F6 => OmPairHyp p).card = 432 := by
  decide +kernel

@[expose] def omS0 : F6 := ![0, 1, 0, 0, 1, 0]

@[expose] def omT0 : F6 := ![1, 0, 0, 0, 0, 0]

private theorem omPair0 : OmPairHyp (omS0, omT0) := by
  decide

private theorem omX0_card : (Finset.univ.filter fun u : F6 => OmX omS0 omT0 u).card = 5 := by
  decide +kernel

private theorem omSpan0 : ∀ v : F6,
    ∃ u₁ ∈ Finset.univ.filter (fun u : F6 => u = 0 ∨ OmX omS0 omT0 u),
      ∃ u₂ ∈ Finset.univ.filter (fun u : F6 => u = 0 ∨ OmX omS0 omT0 u),
      v = polarMinus v omT0 • omS0 + polarMinus v omS0 • omT0 + u₁ + u₂ := by
  decide +kernel

theorem nonempty_mulEquiv_alt5_of_faithful {H : Type*} [Group H] [Finite H] {X : Type*}
    [Finite X] (φ : H →* Equiv.Perm X) (hφ : Function.Injective φ) (hX : Nat.card X = 5)
    (hH : Nat.card H = 60) : Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  classical
  haveI := Fintype.ofFinite X
  have hX' : Fintype.card X = 5 := by rw [← Nat.card_eq_fintype_card]; exact hX
  have hrange : Nat.card φ.range = 60 := by
    rw [← hH]
    exact Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm
  have hidx : φ.range.index = 2 := by
    have h1 := φ.range.card_mul_index
    rw [hrange, Nat.card_perm, hX, show (5 : ℕ).factorial = 120 from rfl] at h1
    omega
  have hrange_eq : φ.range = alternatingGroup X :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  exact ⟨(MonoidHom.ofInjective hφ).trans
    ((MulEquiv.subgroupCongr hrange_eq).trans
      (Equiv.altCongrHom (Fintype.equivFinOfCardEq hX')))⟩

theorem mem_stabilizer_pair {s t : F6} {g : OmG} :
    g ∈ stabilizer OmG (s, t) ↔
      (g : F6 ≃ₗ[ZMod 2] F6) s = s ∧ (g : F6 ≃ₗ[ZMod 2] F6) t = t := by
  rw [mem_stabilizer_iff, Prod.smul_def, Prod.ext_iff]
  rfl

theorem stabilizer_pair_eq (s t : F6) :
    stabilizer OmG s ⊓ stabilizer OmG t = stabilizer OmG (s, t) := by
  ext g
  rw [mem_stabilizer_pair, Subgroup.mem_inf, mem_stabilizer_iff, mem_stabilizer_iff]
  rfl

private theorem omPair_polar' : ∀ s t : F6, OmPairHyp (s, t) → polarMinus t (s + t) = 1 := by
  decide +kernel

theorem orbit_pair {s t : F6} (h : OmPairHyp (s, t)) :
    orbit OmG (s, t) = {p : F6 × F6 | OmPairHyp p} := by
  obtain ⟨hs, ht, hst, h0⟩ := h
  change qMinus s = 1 at hs
  change qMinus t = 0 at ht
  change qMinus (s + t) = 0 at hst
  change t ≠ 0 at h0
  ext ⟨s', t'⟩
  constructor
  · rintro ⟨g, hg⟩
    simp only [Prod.smul_def, Prod.mk.injEq] at hg
    obtain ⟨hgs, hgt⟩ := hg
    have hgs' : (g : F6 ≃ₗ[ZMod 2] F6) s = s' := hgs
    have hgt' : (g : F6 ≃ₗ[ZMod 2] F6) t = t' := hgt
    refine ⟨?_, ?_, ?_, ?_⟩
    · show qMinus s' = 1
      rw [← hgs', qMinus_apply_of_mem g.2, hs]
    · show qMinus t' = 0
      rw [← hgt', qMinus_apply_of_mem g.2, ht]
    · show qMinus (s' + t') = 0
      rw [← hgs', ← hgt', ← map_add, qMinus_apply_of_mem g.2, hst]
    · show t' ≠ 0
      rw [← hgt']
      intro h'
      exact h0 ((g : F6 ≃ₗ[ZMod 2] F6).map_eq_zero_iff.mp h')
  · intro hp
    have hp' := hp
    obtain ⟨hs', ht', hst', h0'⟩ := hp
    change qMinus s' = 1 at hs'
    change qMinus t' = 0 at ht'
    change qMinus (s' + t') = 0 at hst'
    change t' ≠ 0 at h0'
    obtain ⟨g₁, hg₁, hg₁t⟩ := exists_mem_timmesfeldOmega_apply_eq h0 h0' (by rw [ht, ht'])
    have hqs₁ : qMinus ((g₁ : F6 ≃ₗ[ZMod 2] F6) s) = 1 := by
      rw [qMinus_apply_of_mem hg₁, hs]
    have hqs₁t : qMinus ((g₁ : F6 ≃ₗ[ZMod 2] F6) s + t') = 0 := by
      rw [← hg₁t, ← map_add, qMinus_apply_of_mem hg₁, hst]
    have hB₁ : polarMinus t' ((g₁ : F6 ≃ₗ[ZMod 2] F6) s + t') = 1 :=
      omPair_polar' _ _ ⟨hqs₁, ht', hqs₁t, h0'⟩
    have hB' : polarMinus t' (s' + t') = 1 := omPair_polar' _ _ hp'
    obtain ⟨g₂, hg₂, hg₂t, hg₂x⟩ := exists_mem_fix_apply_eq_of_polar_ne_zero (e := t')
      (x := (g₁ : F6 ≃ₗ[ZMod 2] F6) s + t') (y := s' + t') ht' hqs₁t hst'
      (by rw [hB₁]; decide) (by rw [hB']; decide)
    refine ⟨⟨(g₂ : F6 ≃ₗ[ZMod 2] F6) * (g₁ : F6 ≃ₗ[ZMod 2] F6), mul_mem hg₂ hg₁⟩, ?_⟩
    simp only [Prod.smul_def, Prod.mk.injEq]
    constructor
    · show (g₂ : F6 ≃ₗ[ZMod 2] F6) ((g₁ : F6 ≃ₗ[ZMod 2] F6) s) = s'
      rw [map_add, hg₂t] at hg₂x
      exact add_right_cancel hg₂x
    · show (g₂ : F6 ≃ₗ[ZMod 2] F6) ((g₁ : F6 ≃ₗ[ZMod 2] F6) t) = t'
      rw [hg₁t, hg₂t]

private theorem card_pairStab0 : Nat.card (stabilizer OmG (omS0, omT0)) = 60 := by
  have h1 := index_stabilizer OmG (omS0, omT0)
  have hn : {p : F6 × F6 | OmPairHyp p}.ncard = 432 := by
    have e : {p : F6 × F6 | OmPairHyp p} =
        ↑(Finset.univ.filter fun p : F6 × F6 => OmPairHyp p) := by
      ext p
      simp
    rw [e, Set.ncard_coe_finset]
    exact omPair_card
  rw [orbit_pair omPair0, hn] at h1
  have h2 := Subgroup.card_mul_index (stabilizer OmG (omS0, omT0))
  rw [h1, card_timmesfeldOmega] at h2
  generalize Nat.card ↥(stabilizer OmG (omS0, omT0)) = n at h2 ⊢
  omega

@[expose] def omX0Sub : SubMulAction ↥(stabilizer OmG (omS0, omT0)) F6 where
  carrier := {u | OmX omS0 omT0 u}
  smul_mem' g u hu := by
    obtain ⟨hgs, hgt⟩ := mem_stabilizer_pair.1 g.2
    obtain ⟨h0, hq, hps, hpt⟩ := hu
    have hg := (g : OmG).2
    show OmX omS0 omT0 (((g : OmG) : F6 ≃ₗ[ZMod 2] F6) u)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact h0 (((g : OmG) : F6 ≃ₗ[ZMod 2] F6).map_eq_zero_iff.mp h)
    · rw [qMinus_apply_of_mem hg, hq]
    · have := polarMinus_apply_of_mem hg u omS0
      rw [hgs] at this
      rw [this]
      exact hps
    · have := polarMinus_apply_of_mem hg u omT0
      rw [hgt] at this
      rw [this]
      exact hpt

private theorem omFaith0 (g : OmG) (hs : (g : F6 ≃ₗ[ZMod 2] F6) omS0 = omS0)
    (ht : (g : F6 ≃ₗ[ZMod 2] F6) omT0 = omT0)
    (hX : ∀ u, OmX omS0 omT0 u → (g : F6 ≃ₗ[ZMod 2] F6) u = u) : g = 1 := by
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u₁, hu₁, u₂, hu₂, hv⟩ := omSpan0 v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu₁ hu₂
  have h1 : (g : F6 ≃ₗ[ZMod 2] F6) u₁ = u₁ := by
    rcases hu₁ with rfl | h
    · simp
    · exact hX _ h
  have h2 : (g : F6 ≃ₗ[ZMod 2] F6) u₂ = u₂ := by
    rcases hu₂ with rfl | h
    · simp
    · exact hX _ h
  show (g : F6 ≃ₗ[ZMod 2] F6) v = v
  rw [hv, map_add, map_add, map_add, map_smul, map_smul, hs, ht, h1, h2]

private theorem Om_pair0 :
    Nonempty (↥(stabilizer OmG (omS0, omT0)) ≃* alternatingGroup (Fin 5)) := by
  haveI : Finite OmG := Nat.finite_of_card_ne_zero (by rw [card_timmesfeldOmega]; norm_num)
  have hX : Nat.card ↥omX0Sub = 5 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl) :
        ↥omX0Sub ≃ {u : F6 // OmX omS0 omT0 u}), Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact omX0_card
  refine nonempty_mulEquiv_alt5_of_faithful
    (MulAction.toPermHom ↥(stabilizer OmG (omS0, omT0)) ↥omX0Sub) ?_ hX card_pairStab0
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  obtain ⟨hgs, hgt⟩ := mem_stabilizer_pair.1 g.2
  refine Subtype.ext (omFaith0 g.1 hgs hgt fun u hu => ?_)
  have h := Equiv.Perm.ext_iff.1 hg ⟨u, hu⟩
  exact congrArg Subtype.val h

theorem Om_pair {s t : F6} (hs : qMinus s = 1) (ht : qMinus t = 0) (hst : qMinus (s + t) = 0)
    (h0 : t ≠ 0) :
    Nonempty ((MulAction.stabilizer OmG s ⊓ MulAction.stabilizer OmG t : Subgroup OmG) ≃*
      alternatingGroup (Fin 5)) := by
  have hmem : (s, t) ∈ orbit OmG (omS0, omT0) := by
    rw [orbit_pair omPair0]
    exact ⟨hs, ht, hst, h0⟩
  obtain ⟨g, hg⟩ := hmem
  obtain ⟨e⟩ := Om_pair0
  rw [stabilizer_pair_eq, ← hg, stabilizer_smul_eq_stabilizer_map_conj]
  exact ⟨(Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans e⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
