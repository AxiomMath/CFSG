module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldDefs
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem commutator_mem_inn_of_outCyclic {R : Type} [Group R] (h : GGOutCyclic R)
    (α β : MulAut R) : α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : R →* MulAut R).range :=
  (h.ggOutdiagCyclic Set.univ).commutator_mem (subset_ggInndiag (Set.mem_univ α))
    (subset_ggInndiag (Set.mem_univ β))

theorem ggRawFieldCentral_of_outCyclic {R : Type} [Group R] {I F : Set (MulAut R)}
    (h : GGOutCyclic R) (hinn : ∀ r : R, MulAut.conj r ∈ I) : GGRawFieldCentral R I F :=
  ggRawFieldCentral_of_commutator_mem fun α β => by
    obtain ⟨r, hr⟩ := commutator_mem_inn_of_outCyclic h α β
    rw [← hr]
    exact hinn r

section Chev

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K]

theorem conj_mem_chevIDImage (H : Subgroup (LargeEvenChevGL A K)) (x : LargeEvenCenterQuot H) :
    MulAut.conj x ∈ LargeEvenChevIDImage A K H :=
  Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)

theorem largeEvenEntrywise_of_forall_eq {f : K → K} (hf : f 0 = 0) (hfx : ∀ x, f x = x)
    (g : Module.End K (LargeEvenChevModule A K)) : LargeEvenEntrywise A K f hf g = g := by
  have hmap : ∀ v : LargeEvenChevModule A K, Finsupp.mapRange f hf v = v := fun v =>
    Finsupp.ext fun i => by rw [Finsupp.mapRange_apply, hfx]
  apply Finsupp.lhom_ext
  intro b c
  rw [LargeEvenEntrywise, Finsupp.linearCombination_single, hmap, ← map_smul,
    Finsupp.smul_single, smul_eq_mul, mul_one]

theorem ringEquiv_apply_eq_of_card_two (hK : Nat.card K = 2) (σ : K ≃+* K) (x : K) : σ x = x := by
  rcases eq_or_ne x 0 with h0 | h0
  · rw [h0, map_zero]
  · have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
    have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK
    have e : Units.mk0 x h0 = 1 := Subsingleton.elim _ _
    have hx1 : x = 1 := by simpa using congrArg Units.val e
    rw [hx1, map_one]

theorem chevFieldImage_eq_one_of_card_two (hK : Nat.card K = 2) (H : Subgroup (LargeEvenChevGL A K))
    {φ : MulAut (LargeEvenCenterQuot H)} (hφ : φ ∈ LargeEvenChevFieldImage A K H) : φ = 1 := by
  obtain ⟨σ, hσ⟩ := hφ
  ext y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  have := hσ h h (largeEvenEntrywise_of_forall_eq _ (ringEquiv_apply_eq_of_card_two hK σ) _).symm
  simpa using this

theorem chevID_closure_eq_inn_of_card_two (hK : Nat.card K = 2)
    (H : Subgroup (LargeEvenChevGL A K)) :
    Subgroup.closure (LargeEvenInnSet (LargeEvenCenterQuot H) ∪ LargeEvenChevDiagImage A K H) =
      (MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK
  refine le_antisymm (fun φ hφ => chevIDImage_subset_inn_of_subsingleton H hφ) ?_
  rintro _ ⟨x, rfl⟩
  exact conj_mem_chevIDImage H x

theorem ggRawAll_of_card_two (hK : Nat.card K = 2) (H : Subgroup (LargeEvenChevGL A K)) {p : ℕ}
    (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenCenterQuot H) (LargeEvenChevIDImage A K H)
        (LargeEvenChevFieldImage A K H) ∧
      GGRawFieldCentral (LargeEvenCenterQuot H) (LargeEvenChevIDImage A K H)
        (LargeEvenChevFieldImage A K H) ∧
      GGRawFieldConj p (LargeEvenCenterQuot H) (LargeEvenChevIDImage A K H)
        (LargeEvenChevFieldImage A K H) := by
  have hF : ∀ f ∈ LargeEvenChevFieldImage A K H, f = 1 :=
    fun f hf => chevFieldImage_eq_one_of_card_two hK H hf
  have hJ : ((MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range :
      Set (MulAut (LargeEvenCenterQuot H))) = LargeEvenChevIDImage A K H := by
    rw [LargeEvenChevIDImage, chevID_closure_eq_inn_of_card_two hK H]
  exact ⟨ggRawInnField_of_forall_eq_one hp _ hJ (fun x => ⟨x, rfl⟩) hF,
    ggRawFieldCentral_of_forall_eq_one _ hJ hF, ggRawFieldConj_of_forall_eq_one hF⟩

end Chev

theorem recipeChevalley_and {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {q : ℕ} {derived : Bool}
    {Q P : LargeEvenRawCont}
    (hA : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q →
      P (LargeEvenCenterQuot (LargeEvenChevH A K derived)) (LargeEvenChevIDImage A K _)
        (LargeEvenChevFieldImage A K _))
    (h : LargeEvenRecipeChevalley A q derived Q) :
    LargeEvenRecipeChevalley A q derived fun R _ I F => Q R I F ∧ P R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, hA K hK⟩

@[expose] def GGRecipeSmallExcLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2der ∨ lab.tag = .twF4der

theorem largeEvenLabelAll_smallExc {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hS : GGRecipeSmallExcLabel lab) {P : LargeEvenRawCont}
    (hP : ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K] [Finite K],
      Nat.card K = 2 → ∀ H : Subgroup (LargeEvenChevGL A K),
        P (LargeEvenCenterQuot H) (LargeEvenChevIDImage A K H) (LargeEvenChevFieldImage A K H)) :
    LargeEvenLabelAll lab P := by
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · exact recipeChevalley_and (fun K _ _ hK => hP _ K hK _) hQ
  · obtain ⟨-, -, hn1⟩ := hlab
    dsimp only at hn1
    subst hn1
    exact recipeTwF4_and (fun K _ _ hK => hP _ K (by simpa using hK) _) hQ

theorem ggRawInnFieldOn_smallExc : GGRawInnFieldOn GGRecipeSmallExcLabel :=
  fun _ hp _ _ hlab hS => largeEvenLabelAll_smallExc hlab hS fun A _ _ _ hK H =>
    (ggRawAll_of_card_two (A := A) hK H hp.one_lt.ne').1

theorem ggRawFieldCentralOn_smallExc : GGRawFieldCentralOn GGRecipeSmallExcLabel :=
  fun _ hlab hS => largeEvenLabelAll_smallExc hlab hS fun A _ _ _ hK H =>
    (ggRawAll_of_card_two (A := A) (p := 2) hK H (by norm_num)).2.1

theorem ggRawFieldConjOn_smallExc : GGRawFieldConjOn fun _ => GGRecipeSmallExcLabel :=
  fun _ hp _ _ hlab hS => largeEvenLabelAll_smallExc hlab hS fun A _ _ _ hK H =>
    (ggRawAll_of_card_two (A := A) hK H hp.one_lt.ne').2.2

@[expose] def GGRecipeOutCyclicLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .triD4 ∨ lab.tag = .twF4


theorem ggRawFieldCentralOn_outCyclic : GGRawFieldCentralOn GGRecipeOutCyclicLabel := by
  intro lab hlab hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · exact recipeTwisted_and (fun K _ _ hK =>
      ggRawFieldCentral_of_outCyclic (ggOutCyclic_triD4 hn K hK) (conj_mem_chevIDImage _)) hQ
  · obtain ⟨-, -, h3⟩ := hl
    exact recipeTwF4_and (fun K _ _ hK =>
      ggRawFieldCentral_of_outCyclic (ggOutCyclic_twF4 (by omega) K hK)
        (conj_mem_chevIDImage _)) hQ

end CFSG.StandardType

end
