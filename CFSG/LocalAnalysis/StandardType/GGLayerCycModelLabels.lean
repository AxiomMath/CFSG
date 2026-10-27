module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelSp
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelSU
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaSec
public import CFSG.LocalAnalysis.StandardType.GGTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem ggLayerCenterCyclicInput_of_orthogonal
    (hOp : GGLayerOmegaPlusModelInput) (hOm : GGLayerOmegaMinusModelInput)
    (hexc : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGLayerClassicalLabel lab →
        LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I)) :
    GGLayerCenterCyclicInput :=
  ggLayerCenterCyclicInput_of_classical ggLayerUnitaryModelInput_holds
    ggLayerSymplecticModelInput_holds hOp hOm hexc

@[expose] def GGLayerOmegaPlusInnerModelInput : Prop :=
  ∀ (m n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → 1 ≤ n → 4 ≤ m →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ h : LargeEvenOmega (LargeEvenQPlus K m), GGModelLayerCyclic p (MulAut.conj h)

@[expose] def GGLayerOmegaMinusInnerModelInput : Prop :=
  ∀ (m n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → 1 ≤ n → 3 ≤ m →
    ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ h : LargeEvenOmega (LargeEvenQMinus m b c), GGModelLayerCyclic p (MulAut.conj h)

theorem ggLayerOmegaPlusModelInput_of
    (hM : GGLayerOmegaPlusInnerModelInput) : GGLayerOmegaPlusModelInput := by
  intro m n K _ _ hK hn hm p hp hp2
  have := LayerCC.charP_two_of_natCard hK
  exact ⟨LayerCyc.commutator_largeEvenOmegaPlus (by omega),
    ggPSections_largeEvenOmegaPlus (by omega) hp hp2, hM m n K hK hn hm p hp hp2⟩

theorem ggLayerOmegaMinusModelInput_of
    (hM : GGLayerOmegaMinusInnerModelInput) : GGLayerOmegaMinusModelInput := by
  intro m n K _ _ hK hn hm b c hbc p hp hp2
  have := LayerCC.charP_two_of_natCard hK
  exact ⟨LayerCyc.commutator_largeEvenOmegaMinus hm hbc,
    ggPSections_largeEvenOmegaMinus hm hbc hp hp2, hM m n K hK hn hm b c hbc p hp hp2⟩

theorem ggLayerCenterCyclic_of_isSolvable_fix {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : ∀ φ ∈ I, φ ≠ 1 → φ ^ p = 1 → Group.IsSolvable (ggFix φ)) :
    GGLayerCenterCyclic p R I := by
  intro L' _ _ ψ hψ hker hperf _ a ha1 hap hind hcomp
  exfalso
  obtain ⟨φ, hφI, hφ⟩ := hind
  have hφp : φ ^ p = 1 := LayerCC.eq_one_of_comp_eq hψ fun l => by
    rw [← LayerCC.map_pow_apply (fun x => (hφ x).symm) p l, hap, MulAut.one_apply]
  have hφ1 : φ ≠ 1 := by
    intro h1
    apply ha1
    exact LayerCC.eq_one_of_map_eq hker hperf fun l => by rw [← hφ, h1, MulAut.one_apply]
  have hsol := h φ hφI hφ1 hφp
  have hmem : ∀ x : ggFix a, ψ x ∈ ggFix φ := fun x => by
    rw [mem_ggFix, hφ, mem_ggFix.mp x.2]
  let f : ggFix a →* ggFix φ := (ψ.comp (ggFix a).subtype).codRestrict _ hmem
  have hkcomm : ∀ x y : f.ker, x * y = y * x := by
    intro x y
    have hx : ψ ((x : ggFix a) : L') = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
    apply Subtype.ext
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hx)) _).symm
  have : Group.IsSolvable f.ker := Group.isSolvable_of_comm hkcomm
  have hfix : Group.IsSolvable (ggFix a) :=
    Group.isSolvable_of_ker_le_range f.ker.subtype f (Subgroup.range_subtype f.ker).ge
  have hEq : CFSG.IsQuasisimple (LargeEvenLayer (ggFix a)) :=
    (TableBSymp.isQuasisimple_iff _).mp hcomp.2.2
  have : Group.IsSolvable (LargeEvenLayer (ggFix a)) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (LayerCC.largeEvenLayer_le (ggFix a)))
  obtain ⟨x, hx1⟩ := LayerCC.exists_ne_one_of_isQuasisimple hEq
  have : Nontrivial (LargeEvenLayer (ggFix a)) := ⟨⟨x, 1, hx1⟩⟩
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (LargeEvenLayer (ggFix a))).ne
    (Group.isPerfect_def.mp hEq.1)

@[expose] def GGLayerDerivedLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der

theorem eq_three_of_largeEvenSplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hn : lab.n = 1) (h : LargeEvenSplit p lab) : p = 3 := by
  have h1 : ¬ p ∣ 2 ^ lab.n - 1 := by
    rw [hn, show (2 : ℕ) ^ 1 - 1 = 1 by norm_num, Nat.dvd_one]
    exact hp.one_lt.ne'
  have h3 : p ∣ 2 ^ lab.n + 1 → p = 3 := fun hd => by
    rw [hn, show (2 : ℕ) ^ 1 + 1 = 3 by norm_num] at hd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd
  unfold LargeEvenSplit at h
  rcases h with ⟨-, hd⟩ | ⟨-, -, hd⟩ | ⟨-, hd⟩ | ⟨-, hp3⟩
  · exact absurd hd h1
  · exact h3 hd
  · exact absurd hd h1
  · exact hp3

@[expose] def GGLayerDerivedFixSolvableInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGLayerDerivedLabel lab →
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun _R _ I _ =>
      ∀ φ ∈ I, φ ≠ 1 → φ ^ 3 = 1 → Group.IsSolvable (ggFix φ))

theorem largeEvenLabelAll_layerCenterCyclic_derived (hder : GGLayerDerivedFixSolvableInput)
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hsplit : LargeEvenSplit p lab) (h : GGLayerDerivedLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I) := by
  have hn : lab.n = 1 := by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨-, hl⟩ := hlab
    rcases h with h | h | h <;>
    · dsimp only at h
      subst h
      obtain ⟨-, hl2⟩ := hl
      exact hl2
  obtain rfl := eq_three_of_largeEvenSplit hp hn hsplit
  exact LargeEvenLabelAll.mono (fun R _ I F hP hs hab =>
    ggLayerCenterCyclic_of_isSolvable_fix (hP hs hab)) (hder lab hlab h)

@[expose] def GGLayerExceptionalLabel (lab : LargeEvenLabel) : Prop :=
  ¬ GGLayerClassicalLabel lab ∧ ¬ GGLayerDerivedLabel lab

@[expose] def GGLayerCenterCyclicExcInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    LargeEvenSplit p lab → GGLayerExceptionalLabel lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I)

theorem ggLayerCenterCyclicInput_of_inputs
    (hOp : GGLayerOmegaPlusInnerModelInput) (hOm : GGLayerOmegaMinusInnerModelInput)
    (hder : GGLayerDerivedFixSolvableInput) (hexc : GGLayerCenterCyclicExcInput) :
    GGLayerCenterCyclicInput :=
  ggLayerCenterCyclicInput_of_orthogonal (ggLayerOmegaPlusModelInput_of hOp)
    (ggLayerOmegaMinusModelInput_of hOm) fun p lab hp hp2 hlab hsplit hcl => by
      by_cases hd : GGLayerDerivedLabel lab
      · exact largeEvenLabelAll_layerCenterCyclic_derived hder hp hlab hsplit hd
      · exact hexc p lab hp hp2 hlab hsplit ⟨hcl, hd⟩

end CFSG.StandardType

end
