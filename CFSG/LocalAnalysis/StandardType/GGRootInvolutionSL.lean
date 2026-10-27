module

public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore

public section

namespace CFSG.StandardType

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Universal.SpecialLinear
open scoped Pointwise

namespace GGRootSL

variable {m : ℕ} {F : Type} [Field F]

@[expose] def UpperT (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) : Prop :=
  ∀ a b, b < a → M a b = 0

@[expose] def LowerT (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) : Prop :=
  ∀ a b, a < b → M a b = 0

theorem upperT_mul {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hM : UpperT M)
    (hN : UpperT N) : UpperT (M * N) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge l a with h | h
  · rw [hM a l h, zero_mul]
  · rw [hN l b (lt_of_lt_of_le hab h), mul_zero]

theorem upperT_mul_apply_self {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hM : UpperT M)
    (hN : UpperT N) (a : Fin (m + 1)) : (M * N) a a = M a a * N a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hM a l h, zero_mul]
    · rw [hN l a h, mul_zero]
  · simp

theorem lowerT_mul {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hM : LowerT M)
    (hN : LowerT N) : LowerT (M * N) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge a l with h | h
  · rw [hM a l h, zero_mul]
  · rw [hN l b (lt_of_le_of_lt h hab), mul_zero]

theorem lowerT_mul_apply_self {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hM : LowerT M)
    (hN : LowerT N) (a : Fin (m + 1)) : (M * N) a a = M a a * N a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hN l a h, mul_zero]
    · rw [hM a l h, zero_mul]
  · simp

theorem upperT_of_isDiag {M : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hM : M.IsDiag) :
    UpperT M :=
  fun _ _ hab => hM hab.ne'

theorem transvection_apply {i j : Fin (m + 1)} (hij : i ≠ j) (c : F) (a b : Fin (m + 1)) :
    (SpecialLinearGroup.transvection hij c : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b + if i = a ∧ j = b then c else 0 := by
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply]

theorem upperUni_of_mem_posUnipotent {x : SpecialLinearGroup (Fin (m + 1)) F}
    (hx : x ∈ posUnipotent (rootDatum m F)) :
    UpperT (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
      ∀ a, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a = 1 := by
  rw [posUnipotent, iSup_subtype'] at hx
  refine Subgroup.iSup_induction _ hx
    (C := fun x : SpecialLinearGroup (Fin (m + 1)) F =>
      UpperT (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
        ∀ a, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a = 1)
    (fun γ y hy => ?_) ?_ fun y z hy hz => ?_
  · obtain ⟨hγr, hγpos⟩ := γ.2
    have hy' : y ∈ rootSubgroup m F (idx_spec m hγr).1 := by
      rw [← rootGroup_eq_idx m F hγr]
      exact hy
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ y).1 hy'
    have hlt : ((idx m γ.1).1 : ℕ) < (idx m γ.1).2 := by
      have h2 : (0 : ℤ) < ht (ι := Fin m) γ.1 := hγpos
      rw [ht_eq_idx m hγr] at h2
      omega
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [transvection_apply, Matrix.one_apply_ne hab.ne', zero_add, ite_eq_right_iff]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (not_lt.2 (le_of_lt (Fin.lt_def.2 hlt)))
    · rw [transvection_apply, Matrix.one_apply_eq, add_eq_left, ite_eq_right_iff]
      rintro ⟨rfl, h⟩
      exact absurd h (idx_spec m hγr).1.symm
  · exact ⟨fun a b hab => by simp [Matrix.one_apply_ne hab.ne'], fun a => by simp⟩
  · exact ⟨upperT_mul hy.1 hz.1, fun a =>
      (upperT_mul_apply_self hy.1 hz.1 a).trans (by rw [hy.2, hz.2, one_mul])⟩

theorem lowerUni_of_mem_negUnipotent {x : SpecialLinearGroup (Fin (m + 1)) F}
    (hx : x ∈ negUnipotent (rootDatum m F)) :
    LowerT (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
      ∀ a, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a = 1 := by
  rw [negUnipotent, iSup_subtype'] at hx
  refine Subgroup.iSup_induction _ hx
    (C := fun x : SpecialLinearGroup (Fin (m + 1)) F =>
      LowerT (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
        ∀ a, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a = 1)
    (fun γ y hy => ?_) ?_ fun y z hy hz => ?_
  · obtain ⟨hγr, hγneg⟩ := γ.2
    have hy' : y ∈ rootSubgroup m F (idx_spec m hγr).1 := by
      rw [← rootGroup_eq_idx m F hγr]
      exact hy
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ y).1 hy'
    have hlt : ((idx m γ.1).2 : ℕ) < (idx m γ.1).1 := by
      have h2 : ht (ι := Fin m) γ.1 < 0 := hγneg
      rw [ht_eq_idx m hγr] at h2
      omega
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [transvection_apply, Matrix.one_apply_ne hab.ne, zero_add, ite_eq_right_iff]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (not_lt.2 (le_of_lt (Fin.lt_def.2 hlt)))
    · rw [transvection_apply, Matrix.one_apply_eq, add_eq_left, ite_eq_right_iff]
      rintro ⟨rfl, h⟩
      exact absurd h (idx_spec m hγr).1.symm
  · exact ⟨fun a b hab => by simp [Matrix.one_apply_ne hab.ne], fun a => by simp⟩
  · exact ⟨lowerT_mul hy.1 hz.1, fun a =>
      (lowerT_mul_apply_self hy.1 hz.1 a).trans (by rw [hy.2, hz.2, one_mul])⟩

theorem iSup_torus_le_diagonalTorus :
    ⨆ k, torus m F k ≤ SpecialLinearGroup.diagonalTorus F (m + 1) :=
  iSup_le fun k => by
    rw [torus, Subgroup.closure_le]
    rintro h ⟨t, ht⟩
    exact SpecialLinearGroup.mem_diagonalTorus_iff.mpr (by rw [ht]; exact isDiag_diagonal _)

theorem bruhatExtras : BruhatExtras (rootDatum m F) (torus m F) := by
  have hct : CFSG.LieType.CurtisTits.IsCTGroupDatum
      (coxeterMatrix (rootDatum m F).isFiniteType).toCoxeterSystem
      (weylAction (rootDatum m F).isFiniteType) (rootDatum m F).roots (rootDatum m F).rootGroup
      (weylRep m F) (torus m F) := isCTGroupDatum m F
  refine ⟨eq_bot_iff.2 fun x hx => ?_⟩
  obtain ⟨hxB, hxN⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_bot]
  obtain ⟨t, ht, u, hu, rfl⟩ := (Set.ext_iff.1 (coe_borel hct) x).1 hxB
  have hdiag : (t : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag :=
    SpecialLinearGroup.mem_diagonalTorus_iff.mp (iSup_torus_le_diagonalTorus ht)
  have hup : UpperT ((t : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) :=
    upperT_mul (upperT_of_isDiag hdiag) (upperUni_of_mem_posUnipotent hu).1
  obtain ⟨hn1, hn2⟩ := lowerUni_of_mem_negUnipotent hxN
  have key : (t : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
    ext a b
    rcases lt_trichotomy a b with h | rfl | h
    · exact (hn1 a b h).trans (Matrix.one_apply_ne h.ne).symm
    · exact (hn2 a).trans (Matrix.one_apply_eq a).symm
    · exact (hup a b h).trans (Matrix.one_apply_ne h.ne').symm
  exact Subtype.ext key

theorem eq_one_of_mul_self_eq_one {K : Type*} [Field K] [CharP K 2] {x : K} (h : x * x = 1) :
    x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (x + 1) * (x + 1) = 0 := by linear_combination h + (x + 1) * h2
  have h4 : x + 1 = 0 := mul_self_eq_zero.mp h3
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h4
  exact h4

theorem isPGroup_rootGroup [CharP F 2] {γ : Fin (rootDatum m F).rank → ℤ}
    (hγ : γ ∈ (rootDatum m F).roots) : IsPGroup 2 ((rootDatum m F).rootGroup γ) := by
  change IsPGroup 2 (rootGroup m F γ)
  rw [rootGroup_eq_idx m F hγ]
  exact isPGroup_two_range_of_charTwo _

theorem rootGroup_mul_comm {γ : Fin (rootDatum m F).rank → ℤ}
    (hγ : γ ∈ (rootDatum m F).roots) :
    ∀ x ∈ (rootDatum m F).rootGroup γ, ∀ y ∈ (rootDatum m F).rootGroup γ, x * y = y * x := by
  change ∀ x ∈ rootGroup m F γ, ∀ y ∈ rootGroup m F γ, x * y = y * x
  rw [rootGroup_eq_idx m F hγ]
  exact range_mul_comm _

theorem coprime_two_card_torus [Finite F] [CharP F 2] :
    Nat.Coprime 2 (Nat.card (⨆ i, torus m F i : Subgroup (SpecialLinearGroup (Fin (m + 1)) F))) := by
  refine coprime_two_card_of_sq_eq_one _ fun g hg hg2 => ?_
  have hdiag : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag :=
    SpecialLinearGroup.mem_diagonalTorus_iff.mp (iSup_torus_le_diagonalTorus hg)
  have hsq : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
    have := congrArg (fun h : SpecialLinearGroup (Fin (m + 1)) F =>
      (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) hg2
    simpa [pow_two] using this
  refine Subtype.ext (Matrix.ext fun a b => ?_)
  rcases eq_or_ne a b with rfl | hab
  · have h1 := congrFun (congrFun hsq a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a (fun l _ hl => by
      rw [hdiag hl.symm, zero_mul]) (by simp), Matrix.one_apply_eq] at h1
    exact (eq_one_of_mul_self_eq_one h1).trans (Matrix.one_apply_eq a).symm
  · exact (hdiag hab).trans (Matrix.one_apply_ne hab).symm

theorem ggSimpleConj (i j : Fin (rootDatum m F).rank) : GGSimpleConj (rootDatum m F) i j := by
  have hr : (rootDatum m F).rank = m := rfl
  have hadj : ∀ k : ℕ, ∀ hk : k + 1 < (rootDatum m F).rank,
      GGSimpleConj (rootDatum m F) ⟨k, by omega⟩ ⟨k + 1, hk⟩ :=
    fun k hk => ggSimpleConj_of_cartan_eq
      (by simp [rootDatum, CartanMatrix.A, Fin.ext_iff])
      (by simp [rootDatum, CartanMatrix.A, Fin.ext_iff])
  have h0 : ∀ k : ℕ, ∀ hk : k < (rootDatum m F).rank,
      GGSimpleConj (rootDatum m F) ⟨0, by omega⟩ ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => exact fun _ => GGSimpleConj.refl _
    | succ k ih => exact fun hk => (ih (by omega)).trans (hadj k hk)
  exact (h0 i.val i.isLt).symm.trans (h0 j.val j.isLt)

theorem ggRootSylowCentral_specialLinear [Finite F] [CharP F 2] (t : StatedLieTag) :
    GGRootSylowCentral (rootDatum m F) t :=
  ggRootSylowCentral_of_longRoot_reduced (isCTGroupDatum m F) (steinbergExtras m F) bruhatExtras
    rfl (fun _ hγ => isPGroup_rootGroup hγ) coprime_two_card_torus
    (fun _ hγ₀ _ => rootGroup_mul_comm hγ₀)
    fun _ hγ => hγ.longRoot_of_simpleConj rfl ggSimpleConj

end GGRootSL

end CFSG.StandardType
