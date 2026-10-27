module

public import CFSG.RankThree.PartOne.KLCE.A1Type
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.SigmaUnion

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical (conjSL)

open scoped MatrixGroups Pointwise

section A1II

variable {τ : Tag} {K L : Type} [Field K] [Field L] [Algebra K L]

@[expose] def a1HomConj (τ : Tag) (K L : Type) [Field K] [Field L] [Algebra K L]
    (θ : Fin τ.rank → ℤ) (P : GL (Fin 2) L) : SL(2, K) →* ModGL τ L :=
  (rootSL2 τ L θ).comp ((conjSL P).comp (Matrix.SpecialLinearGroup.map (algebraMap K L)))

theorem a1HomConj_apply (θ : Fin τ.rank → ℤ) (P : GL (Fin 2) L) (B : SL(2, K)) :
    a1HomConj τ K L θ P B =
      rootSL2 τ L θ (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K L) B)) := rfl

omit [Algebra K L] in
theorem map_conjSL_ringHom' {L L' : Type} [Field L] [Field L'] (f : L →+* L')
    (P : GL (Fin 2) L) (B : SL(2, L)) :
    Matrix.SpecialLinearGroup.map f (conjSL P B) =
      conjSL (Matrix.GeneralLinearGroup.map f P) (Matrix.SpecialLinearGroup.map f B) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, CFSG.RankThree.Classical.coe_conjSL,
    CFSG.RankThree.Classical.coe_conjSL, Matrix.SpecialLinearGroup.map_apply_coe, ← map_inv,
    map_mul, map_mul]
  rfl

omit [Algebra K L] in
theorem conjSL_injective (P : GL (Fin 2) L) : Function.Injective (conjSL P) := by
  intro A B h
  have := congrArg (conjSL P⁻¹) h
  rwa [← CFSG.RankThree.Classical.conjSL_mul, ← CFSG.RankThree.Classical.conjSL_mul, inv_mul_cancel,
    CFSG.RankThree.Classical.conjSL_one, CFSG.RankThree.Classical.conjSL_one] at this

theorem a1HomConj_injective (θ : Fin τ.rank → ℤ) (P : GL (Fin 2) L) :
    Function.Injective (a1HomConj τ K L θ P) :=
  (rootSL2_injective_of_field θ).comp ((conjSL_injective P).comp (map_specialLinear_injective _))

theorem a1_fixed_range_of_action [Finite K] {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    {N : ModGL τ L} (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (P₀ : GL (Fin 2) L)
    (hX : ∀ B : SL(2, L), N * Units.map (entrywiseHom Fr) (rootSL2 τ L θ B) * N⁻¹ =
      rootSL2 τ L θ (conjSL (P₀ * Matrix.GeneralLinearGroup.map Fr P₀⁻¹)
        (Matrix.SpecialLinearGroup.map Fr B))) :
    rootSpan τ L {θ, -θ} ⊓ twistedFixedPoints N (Units.map (entrywiseHom Fr)) =
      (a1HomConj τ K L θ P₀).range := by
  rw [rootSpan_pm_eq_range hθ]
  ext g
  constructor
  · rintro ⟨⟨B, rfl⟩, hg⟩
    have h := (a1_hS1_of_action Fr hFr P₀ hX B).1 hg
    obtain ⟨C, ⟨c, rfl⟩, rfl⟩ := h
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    exact (a1_hS1_of_action Fr hFr P₀ hX _).2 ⟨_, ⟨c, rfl⟩, rfl⟩

theorem a1_sigma_family_of_action [Finite K] [IsAlgClosed L] (hK4 : 4 ≤ Nat.card K)
    {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) {N : ModGL τ L} (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (P₀ : GL (Fin 2) L)
    (hX : ∀ B : SL(2, L), N * Units.map (entrywiseHom Fr) (rootSL2 τ L θ B) * N⁻¹ =
      rootSL2 τ L θ (conjSL (P₀ * Matrix.GeneralLinearGroup.map Fr P₀⁻¹)
        (Matrix.SpecialLinearGroup.map Fr B))) :
    ∃ P : Unit → Subgroup (ModGL τ L), IsSigmaFamily N Fr {θ, -θ} P ∧
      P () = (a1HomConj τ K L θ P₀).range := by
  classical
  set S : Subgroup (SL(2, L)) := (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map
    (conjSL P₀) with hSdef
  have hSfix : ∀ B : SL(2, L), N * Units.map (entrywiseHom Fr) (rootSL2 τ L θ B) * N⁻¹ =
      rootSL2 τ L θ B ↔ B ∈ S := a1_hS1_of_action (K := K) Fr hFr P₀ hX
  obtain ⟨hfin, hq⟩ := sl2_conj_range_quasisimple (K := K) (L := L) hK4 P₀
  have hz := sl2_conj_range_centralizer (K := K) (L := L) P₀
  have hinj : Function.Injective (rootSL2 τ L θ) := rootSL2_injective_of_field θ
  have hrange : rootSpan τ L {θ, -θ} = (rootSL2 τ L θ).range := rootSpan_pm_eq_range hθ
  have hroots : ∀ α ∈ ({θ, -θ} : Set (Fin τ.rank → ℤ)), IsRoot τ α := by
    intro α hα
    rcases hα with rfl | rfl
    exacts [hθ, IsRoot.neg hθ]
  have hPeq : rootSpan τ L {θ, -θ} ⊓ twistedFixedPoints N (Units.map (entrywiseHom Fr)) =
      S.map (rootSL2 τ L θ) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgQ, hgR⟩ := Subgroup.mem_inf.1 hg
      rw [hrange] at hgQ
      obtain ⟨A, rfl⟩ := hgQ
      exact ⟨A, (hSfix A).1 hgR, rfl⟩
    · rintro _ ⟨A, hA, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, (hSfix A).2 hA⟩
      rw [hrange]
      exact ⟨A, rfl⟩
  have hfinP : Finite (S.map (rootSL2 τ L θ)) := by
    have : Finite S := hfin
    exact Finite.of_equiv S (Subgroup.equivMapOfInjective S (rootSL2 τ L θ) hinj)
  have hqP : CFSG.IsQuasisimple (S.map (rootSL2 τ L θ)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective S (rootSL2 τ L θ) hinj) hq
  have hfac : SigmaFactor N Fr {θ, -θ} (fun _ : Unit => rootSpan τ L {θ, -θ} ⊓
      twistedFixedPoints N (Units.map (entrywiseHom Fr)))
      (Subgroup.normalizer (rootSpan τ L {θ, -θ} : Set (ModGL τ L))) := by
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => inf_le_left, fun _ => inf_le_right,
      fun _ => inf_le_left.trans (rootSpan_le_adjointGroup L _), fun _ y hy hyR u hu => ?_,
      fun y hy hc => ?_⟩
    · rw [hPeq]
      exact hfinP
    · rw [hPeq]
      exact hqP
    · exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hy u).1 hu.1,
        mul_mem (mul_mem hyR hu.2) (inv_mem hyR)⟩
    · have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L)
        (rootSpan τ L {θ, -θ}) (KE.torusGroup_le_normalizer_rootSpan hroots)
      have hy' : y ∈ ((torusGroup τ L ⊔ rootSpan τ L {θ, -θ} : Subgroup (ModGL τ L)) :
        Set (ModGL τ L)) := hy
      rw [e] at hy'
      have hy2 : y ∈ (torusGroup τ L : Set (ModGL τ L)) *
          (rootRankOneGroup τ L θ : Set (ModGL τ L)) := by
        obtain ⟨t, ht, q, hq', rfl⟩ := hy'
        rw [SetLike.mem_coe, hrange] at hq'
        exact ⟨t, ht, q, hq', rfl⟩
      have hcS : ∀ A ∈ S, y * rootSL2 τ L θ A = rootSL2 τ L θ A * y := fun A hA =>
        hc () (rootSL2 τ L θ A) (by rw [hPeq]; exact ⟨A, hA, rfl⟩)
      have hall := commute_rootSL2_of_commute_fixed hθ hz hy2 hcS
      refine ⟨mem_torusGroup_of_centralizes_rootSL2 hθ hy2 hall, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [SetLike.mem_coe, hrange] at hg
      obtain ⟨A, rfl⟩ := hg
      exact (hall A).symm
  refine ⟨fun _ => rootSpan τ L {θ, -θ} ⊓ twistedFixedPoints N (Units.map (entrywiseHom Fr)),
    hfac.toSigma ?_, ?_⟩
  · exact sup_le (KE.torusGroup_le_normalizer_rootSpan hroots) Subgroup.le_normalizer
  · exact a1_fixed_range_of_action hθ Fr hFr P₀ hX

theorem a1_F0_compat_II {θ : Fin τ.rank → ℤ} {n₀ : ModGL τ L} {J₀ : SL(2, L)}
    (hn₀ : ∀ B : SL(2, L), n₀ * rootSL2 τ L θ B * n₀⁻¹ = rootSL2 τ L θ (J₀ * B * J₀⁻¹))
    {Φ₀ : L →+* L} {σ : K ≃+* K}
    (hσ : ∀ c : K, Φ₀ (algebraMap K L c) = algebraMap K L (σ c)) {P₀ : GL (Fin 2) L}
    (hP₀ : P₀ * Matrix.GeneralLinearGroup.map Φ₀ P₀⁻¹ =
      Matrix.SpecialLinearGroup.toGL J₀) (B : SL(2, K)) :
    n₀ * Units.map (entrywiseHom Φ₀) (a1HomConj τ K L θ P₀ B) * n₀⁻¹ =
      a1HomConj τ K L θ P₀ (Matrix.SpecialLinearGroup.map σ.toRingHom B) := by
  have hmap : Matrix.SpecialLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.map (algebraMap K L) B) =
      Matrix.SpecialLinearGroup.map (algebraMap K L)
        (Matrix.SpecialLinearGroup.map σ.toRingHom B) := by
    ext i j
    simp [hσ]
  have hP : Matrix.SpecialLinearGroup.toGL J₀ * Matrix.GeneralLinearGroup.map Φ₀ P₀ = P₀ := by
    rw [← hP₀, map_inv]
    group
  rw [a1HomConj_apply, a1HomConj_apply, entrywise_rootSL2_of_field, hn₀, map_conjSL_ringHom', hmap]
  congr 1
  have h := CFSG.RankThree.Classical.conjSL_mul
    (Matrix.SpecialLinearGroup.toGL J₀) (Matrix.GeneralLinearGroup.map Φ₀ P₀)
    (Matrix.SpecialLinearGroup.map (algebraMap K L)
      (Matrix.SpecialLinearGroup.map σ.toRingHom B))
  rw [hP, CFSG.RankThree.Chevalley.conjSL_toGL] at h
  exact h.symm

theorem a1_hX_of_J {θ : Fin τ.rank → ℤ} {N : ModGL τ L} {J₀ : SL(2, L)}
    (hN : ∀ B : SL(2, L), N * rootSL2 τ L θ B * N⁻¹ = rootSL2 τ L θ (J₀ * B * J₀⁻¹))
    (Fr : L →+* L) {P₀ : GL (Fin 2) L}
    (hP : P₀ * Matrix.GeneralLinearGroup.map Fr P₀⁻¹ = Matrix.SpecialLinearGroup.toGL J₀)
    (B : SL(2, L)) :
    N * Units.map (entrywiseHom Fr) (rootSL2 τ L θ B) * N⁻¹ =
      rootSL2 τ L θ (conjSL (P₀ * Matrix.GeneralLinearGroup.map Fr P₀⁻¹)
        (Matrix.SpecialLinearGroup.map Fr B)) := by
  rw [entrywise_rootSL2_of_field Fr θ B, hN, hP, CFSG.RankThree.Chevalley.conjSL_toGL]

theorem pow_conj_rootSL2 {θ : Fin τ.rank → ℤ} {n : ModGL τ L} {J₀ : SL(2, L)}
    (hn : ∀ B : SL(2, L), n * rootSL2 τ L θ B * n⁻¹ = rootSL2 τ L θ (J₀ * B * J₀⁻¹)) (k : ℕ)
    (B : SL(2, L)) :
    n ^ k * rootSL2 τ L θ B * (n ^ k)⁻¹ = rootSL2 τ L θ (J₀ ^ k * B * (J₀ ^ k)⁻¹) := by
  induction k generalizing B with
  | zero => simp
  | succ k ih =>
    have h1 : n ^ (k + 1) * rootSL2 τ L θ B * (n ^ (k + 1))⁻¹ =
        n * (n ^ k * rootSL2 τ L θ B * (n ^ k)⁻¹) * n⁻¹ := by
      rw [pow_succ']
      group
    rw [h1, ih, hn, pow_succ']
    congr 1
    group

omit [Algebra K L] in
theorem P_frobenius_pow {f₀ : ℕ} [ExpChar L 2] {P₀ J : GL (Fin 2) L}
    (hJ : Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 f₀) J = J)
    (hP : P₀ * Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 f₀) P₀⁻¹ = J) (k : ℕ) :
    P₀ * Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 (f₀ * k)) P₀⁻¹ = J ^ k := by
  induction k with
  | zero =>
    rw [Nat.mul_zero, iterateFrobenius_zero, pow_zero]
    have : Matrix.GeneralLinearGroup.map (RingHom.id L) P₀⁻¹ = P₀⁻¹ := by
      ext i j
      rfl
    rw [this, mul_inv_cancel]
  | succ k ih =>
    have hX : Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 (f₀ * k)) P₀⁻¹ =
        P₀⁻¹ * J ^ k := by
      rw [← ih]
      group
    have hcomp : Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 (f₀ * (k + 1))) P₀⁻¹ =
        Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 f₀)
          (Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 (f₀ * k)) P₀⁻¹) := by
      rw [show f₀ * (k + 1) = f₀ + f₀ * k by ring, iterateFrobenius_add]
      rfl
    rw [hcomp, hX, map_mul, map_pow, hJ, ← mul_assoc, hP, pow_succ']

end A1II

end CFSG.RankThree.PartOne.KLCE
