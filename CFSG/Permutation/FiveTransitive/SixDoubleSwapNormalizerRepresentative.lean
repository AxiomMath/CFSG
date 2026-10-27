module

public import CFSG.Permutation.FiveTransitive.LocalEvenCycleWitness
public import CFSG.Permutation.FiveTransitive.TwoRootDoubleSwap
public import CFSG.Permutation.FiveTransitive.TupleSylowConjugacy
public import CFSG.Permutation.FiveTransitive.ConjugateFixedNormalizer
public import CFSG.Permutation.FiveTransitive.NormalizerInvolutionFixedTwo
public import CFSG.Permutation.FiveTransitive.SixPointDoubleSwapShape

public section

namespace CFSG

namespace FiveTransitive.SixDoubleSwapNormalizerRepresentative

open MulAction Equiv FixedSetNormalizerPerm CyclePatternRoots FixedSetCycleRoots

theorem exists_conjugate
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X)
    (S : Sylow 2 (fixingSubgroup G s))
    (hcard : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6)
    (heven : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      ∀ (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)),
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPerm G X Q a ha).sign = 1)
    (e₀ : Fin 4 ↪ X) (he₀ : Set.range e₀ = s)
    (a : G) (ha : orderOf a = 4)
    (htwo : 4 ≤ Nat.card (TwoRoot (toPermHom G X a))) :
    let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
    ∃ (b : G) (_hbN : b ∈ Subgroup.normalizer (Q : Set G))
      (E : Pattern (toPermHom G X b) CyclePatternFinite.doubleTwo),
      E.val = e₀ ∧ orderOf b = 4 ∧ Set.range E.val ⊆ fixedPoints Q X ∧
      (∀ x ∈ fixedPoints Q X, b ^ 2 • x = x) ∧
      (fixedBy X b ∩ fixedPoints Q X).ncard = 2 := by
  classical
  let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
  obtain ⟨E⟩ := TwoRootDoubleSwap.exists_double_two_pattern (toPermHom G X a) htwo
  obtain ⟨T,hT,hfix⟩ := LocalEvenCycleWitness.exists_normalizer a 2 ha
    E.val CyclePatternFinite.doubleTwo E.property
  let t := Set.range E.val
  obtain ⟨c,hce,hc⟩ := TupleSylowConjugacy.exists_transporter G X 4 h4 e₀ E.val
    (fixingSubgroup G s) (fixingSubgroup G t) (by rw [he₀]) rfl S T
  let R := (T : Subgroup (fixingSubgroup G t)).map (fixingSubgroup G t).subtype
  let b := c⁻¹ * a * c
  have hbN : b ∈ Subgroup.normalizer (Q : Set G) :=
    ConjugateFixedNormalizer.normalizer_conj_back G Q R c hc a hT
  have hb : orderOf b = 4 := by
    have h := orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective a
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv, ha] using h
  let e : Fin 4 ↪ X := ⟨fun i => c⁻¹ • E.val i,
    fun i j h => E.val.injective (smul_left_cancel c⁻¹ h)⟩
  have hee : e = e₀ := by
    ext i
    have h := DFunLike.congr_fun hce i
    change c • e₀ i = E.val i at h
    change c⁻¹ • E.val i = e₀ i
    rw [← h, inv_smul_smul]
  have he : ∀ i, b • e i = e (CyclePatternFinite.doubleTwo i) := by
    intro i
    change (c⁻¹ * a * c) • (c⁻¹ • E.val i) = c⁻¹ • E.val (CyclePatternFinite.doubleTwo i)
    simp only [mul_smul, smul_inv_smul]
    exact congrArg (fun x : X => c⁻¹ • x) (E.property i)
  have hef : ∀ i, e i ∈ fixedPoints Q X := by
    intro i
    apply (ConjugateFixedNormalizer.fixed_mem_iff G X Q R c hc (e i)).mpr
    change c • (c⁻¹ • E.val i) ∈ fixedPoints R X
    simpa only [smul_inv_smul] using hfix i
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  let f := fixedPerm G X Q b hbN
  let ef := liftTuple Q e hef
  have hpat : ∀ i, f (ef i) = ef (CyclePatternFinite.doubleTwo i) := by
    intro i
    apply Subtype.ext
    exact he i
  have hsq (i : Fin 4) : CyclePatternFinite.doubleTwo (CyclePatternFinite.doubleTwo i) = i := by
    revert i
    decide
  have hne (i : Fin 4) : CyclePatternFinite.doubleTwo i ≠ i := by
    revert i
    decide
  let er : Fin 4 ↪ TwoRoot f := ⟨fun i => ⟨ef i, by
      constructor
      · rw [hpat,hpat,hsq]
      · intro h
        rw [hpat] at h
        exact hne i (ef.injective h)⟩,
    fun i j h => ef.injective (congrArg Subtype.val h)⟩
  have hcount : 4 ≤ Nat.card (TwoRoot f) := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective er er.injective
  have hf4 : f ^ 4 = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rw [fixedPerm_pow_apply_val, show b ^ 4 = 1 from hb ▸ pow_orderOf_eq_one b, one_smul]
    rfl
  obtain ⟨hf2,hfFix⟩ := SixPointDoubleSwapShape.square_one_and_fixed_two
    (by simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hcard)
    f (heven b hbN) hf4 hcount
  refine ⟨b,hbN,⟨e,he⟩,hee,hb,?_,?_,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact hef i
  · intro x hx
    have h := congrArg (fun p : Perm (fixedPoints Q X) => (p ⟨x,hx⟩).val) hf2
    simpa only [f, fixedPerm_pow_apply_val, Perm.one_apply] using h
  · rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr (NormalizerInvolutionFixedTwo.fixedIntersectionEquiv G X Q b hbN)).symm.trans hfFix

end FiveTransitive.SixDoubleSwapNormalizerRepresentative

end CFSG
