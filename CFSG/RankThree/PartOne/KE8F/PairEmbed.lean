module

public import CFSG.RankThree.PartOne.KE8F.PairA1
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootPerfectness
public import CFSG.RankThree.PartOne.KE.E8FourA1Family

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Chevalley CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.QuadraticSL2 (map_conjSL)
open CFSG.RankThree.PartOne.KGD (twHom twHom_apply isQuasisimple_map_twHom centralizer_map_twHom
  iterateFrobenius_bijective map_map_sl2 glMap_diagUnitOne glMap_swapGL exists_twist_antidiag
  exists_rootSL2_neg_eq)
open CFSG.RankThree.PartOne.KE
open scoped MatrixGroups Matrix Pointwise

set_option linter.unusedSectionVars false


section Block

variable {L : Type} [Field L]

theorem pair_block_data {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] [IsAlgClosed L]
    {n : ModGL .E8 L} (hn : n ∈ monomialSubgroup .E8 L) {r r' : Fin Tag.E8.rank → ℤ}
    (hr : IsRoot .E8 r) (hr' : IsRoot .E8 r')
    (hw : weylQuotientHom .E8 L ⟨n, hn⟩ • r = r')
    (hw' : weylQuotientHom .E8 L ⟨n, hn⟩ • r' = -r)
    {k₂ : Type} [Field k₂] [Finite k₂] [Algebra k₂ L] (hk₂ : Nat.card k₂ = ℓ ^ (2 * f)) :
    ∃ M₁ M₂ P : GL (Fin 2) L,
      (∀ A : SL2 L, n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (rootSL2 .E8 L r A) *
        n⁻¹ = rootSL2 .E8 L r' (twHom (iterateFrobenius L ℓ f) M₁ A)) ∧
      (∀ B : SL2 L, n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (rootSL2 .E8 L r' B) *
        n⁻¹ = rootSL2 .E8 L r (twHom (iterateFrobenius L ℓ f) M₂ B)) ∧
      ∀ A : SL(2, k₂), twHom (iterateFrobenius L ℓ f) M₂ (twHom (iterateFrobenius L ℓ f) M₁
        (conjSL P (SpecialLinearGroup.map (algebraMap k₂ L) A))) =
          conjSL P (SpecialLinearGroup.map (algebraMap k₂ L) A) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  set Fr₂ : L →+* L := Fr.comp Fr with hFr₂def
  have hFr₂ : ∀ c, Fr₂ c = c ^ (ℓ ^ (2 * f)) := fun c => by
    rw [hFr₂def, RingHom.comp_apply, hFr, hFr, ← pow_mul, ← pow_add, two_mul]
  set n₂ : ModGL .E8 L := n * Units.map (entrywiseHom Fr) n with hn₂
  have hFeFe : ∀ x : ModGL .E8 L, Units.map (entrywiseHom Fr) (Units.map (entrywiseHom Fr) x) =
      Units.map (entrywiseHom Fr₂) x := fun x => by
    refine Units.ext ?_
    simp only [Units.coe_map]
    exact entrywise_entrywise Fr Fr _
  have hT2 : ∀ x : ModGL .E8 L, n₂ * Units.map (entrywiseHom Fr₂) x * n₂⁻¹ =
      n * Units.map (entrywiseHom Fr) (n * Units.map (entrywiseHom Fr) x * n⁻¹) * n⁻¹ :=
    fun x => by
    rw [← hFeFe, hn₂, map_mul, map_mul, map_inv]
    group
  have hFr₂k : ∀ c, Fr₂ c = c ^ Nat.card k₂ := fun c => by
    rw [hk₂]
    exact hFr₂ c
  have hmw := mapsRootLines_weylQuotientHom (τ := .E8) (R := L) ⟨n, hn⟩
  obtain ⟨s₁, hs₁⟩ := exists_conj_rootSL2_eq hn hmw hr hw
  obtain ⟨s₂, hs₂⟩ := exists_conj_rootSL2_eq hn hmw hr' hw'
  obtain ⟨a, ha⟩ := exists_rootSL2_neg_eq (L := L) hr
  set M₁ : GL (Fin 2) L := diagUnitOne s₁ with hM₁
  set M₂ : GL (Fin 2) L := swapGL * diagUnitOne a * diagUnitOne s₂ with hM₂
  have e1 : ∀ A : SL2 L, n * rootSL2 .E8 L r (Matrix.SpecialLinearGroup.map Fr A) * n⁻¹ =
      rootSL2 .E8 L r' (twHom Fr M₁ A) := fun A => by
    rw [hs₁, twHom_apply]
  have e2 : ∀ B : SL2 L, n * rootSL2 .E8 L r' (Matrix.SpecialLinearGroup.map Fr B) * n⁻¹ =
      rootSL2 .E8 L r (twHom Fr M₂ B) := fun B => by
    rw [hs₂, ha, twHom_apply, hM₂, conjSL_mul (swapGL * diagUnitOne a) (diagUnitOne s₂)]
  have hsq : ∀ A : SL2 L, n₂ * Units.map (entrywiseHom Fr₂) (rootSL2 .E8 L r A) * n₂⁻¹ =
      rootSL2 .E8 L r (twHom Fr M₂ (twHom Fr M₁ A)) := fun A => by
    rw [hT2, entrywise_rootSL2_of_field, e1, entrywise_rootSL2_of_field, e2]
  set g : GL (Fin 2) L := M₂ * Matrix.GeneralLinearGroup.map Fr M₁ with hgdef
  set y : Lˣ := a * (s₂ * Units.map Fr.toMonoidHom s₁) with hydef
  have hg : g = swapGL * diagUnitOne y := by
    rw [hgdef, hM₂, hM₁, glMap_diagUnitOne, mul_assoc, mul_assoc, diagUnitOne_mul,
      diagUnitOne_mul]
  obtain ⟨Pm, hPm⟩ := exists_twist_antidiag (K := k₂) Fr₂ hFr₂k 1 y g (by
    rw [hg, coe_swapGL_mul_diagUnitOne]
    simp)
  have hinj : Function.Injective (rootSL2 .E8 L r) := rootSL2_injective_of_field r
  refine ⟨M₁, M₂, Pm, fun A => ?_, fun B => ?_, fun A => ?_⟩
  · rw [entrywise_rootSL2_of_field, e1]
  · rw [entrywise_rootSL2_of_field, e2]
  ·
    set B : SL2 L := conjSL Pm (SpecialLinearGroup.map (algebraMap k₂ L) A) with hB
    have hBS : B ∈ (SpecialLinearGroup.map (algebraMap k₂ L)).range.map (conjSL Pm) :=
      ⟨_, ⟨A, rfl⟩, rfl⟩
    have h1 : conjSL (Pm * Matrix.GeneralLinearGroup.map Fr₂ Pm⁻¹)
        (Matrix.SpecialLinearGroup.map Fr₂ B) = B :=
      (sl2_twistedFixed_iff Fr₂ (frobenius_fixed_iff Fr₂ hFr₂k) Pm B).2 hBS
    rw [twHom_comp_two, ← hgdef, ← hPm]
    exact h1

theorem pair_A1_embedding {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] [IsAlgClosed L] (hℓ2 : ℓ ≠ 2)
    {n : ModGL .E8 L} (hn : n ∈ monomialSubgroup .E8 L) {r₁ r₂ : Fin Tag.E8.rank → ℤ}
    (h₁ : IsRoot .E8 r₁) (h₂ : IsRoot .E8 r₂)
    (hw₁ : weylQuotientHom .E8 L ⟨n, hn⟩ • r₁ = r₂)
    (hw₂ : weylQuotientHom .E8 L ⟨n, hn⟩ • r₂ = -r₁)
    (o12 : r₁ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₂) = 0)
    {k₂ : Type} [Field k₂] [Finite k₂] [Algebra k₂ L] (hk₂ : Nat.card k₂ = ℓ ^ (2 * f))
    (hr₁ : iform r₁ r₁ = 2) (hr₂ : iform r₂ r₂ = 2)
    {σ : Fin Tag.E8.rank → ℤ} (hσ : IsRoot .E8 σ) (hσ₁ : ¬ 2 ∣ iform r₁ σ)
    (hσ₂ : 2 ∣ iform r₂ σ) :
    ∃ e : SL(2, k₂) →* ModGL .E8 L, Function.Injective e ∧
      (∀ A, ∃ X Y : SL2 L, e A = rootSL2 .E8 L r₁ X * rootSL2 .E8 L r₂ Y) ∧
      (∀ A, e A ∈ adjointGroup .E8 L) ∧
      (∀ A, n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (e A) * n⁻¹ = e A) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  obtain ⟨M₁, M₂, Pm, e1, e2, hfix⟩ := pair_block_data (k₂ := k₂) hn h₁ h₂ hw₁ hw₂ hk₂
  have hinj₁ : Function.Injective (rootSL2 .E8 L r₁) := rootSL2_injective_of_field r₁
  have hinj₂ : Function.Injective (rootSL2 .E8 L r₂) := rootSL2_injective_of_field r₂
  have hmapinj : Function.Injective
      (SpecialLinearGroup.map (n := Fin 2) (algebraMap k₂ L)) := by
    intro A B h
    ext i j
    have h1 := congrArg (fun X : SL(2, L) => (X : Matrix (Fin 2) (Fin 2) L) i j) h
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h1
    exact (algebraMap k₂ L).injective h1
  set Bh : SL(2, k₂) →* SL2 L :=
    (conjSL Pm).comp (SpecialLinearGroup.map (algebraMap k₂ L)) with hBh
  have hBinj : Function.Injective Bh := by
    intro A B h
    have h1 : conjSL Pm⁻¹ (Bh A) = conjSL Pm⁻¹ (Bh B) := by rw [h]
    simp only [hBh, MonoidHom.comp_apply, ← conjSL_mul, inv_mul_cancel, conjSL_one] at h1
    exact hmapinj h1
  set Ch : SL(2, k₂) →* SL2 L := (twHom Fr M₁).comp Bh with hCh
  have hcomm : ∀ X Y : SL2 L, rootSL2 .E8 L r₁ X * rootSL2 .E8 L r₂ Y =
      rootSL2 .E8 L r₂ Y * rootSL2 .E8 L r₁ X := fun X Y =>
    (e8_rootSL2_commute_of_orth (L := L) h₁ h₂ o12 X Y).eq
  let e : SL(2, k₂) →* ModGL .E8 L :=
    { toFun := fun A => rootSL2 .E8 L r₁ (Bh A) * rootSL2 .E8 L r₂ (Ch A)
      map_one' := by simp
      map_mul' := fun A A' => by
        simp only [map_mul]
        calc rootSL2 .E8 L r₁ (Bh A) * rootSL2 .E8 L r₁ (Bh A') *
              (rootSL2 .E8 L r₂ (Ch A) * rootSL2 .E8 L r₂ (Ch A'))
            = rootSL2 .E8 L r₁ (Bh A) * (rootSL2 .E8 L r₁ (Bh A') * rootSL2 .E8 L r₂ (Ch A)) *
                rootSL2 .E8 L r₂ (Ch A') := by group
          _ = rootSL2 .E8 L r₁ (Bh A) * (rootSL2 .E8 L r₂ (Ch A) * rootSL2 .E8 L r₁ (Bh A')) *
                rootSL2 .E8 L r₂ (Ch A') := by rw [hcomm]
          _ = _ := by group }
  have he : ∀ A, e A = rootSL2 .E8 L r₁ (Bh A) * rootSL2 .E8 L r₂ (Ch A) := fun A => rfl
  have hfixed : ∀ A, n * Units.map (entrywiseHom Fr) (e A) * n⁻¹ = e A := by
    intro A
    rw [he, map_mul, show n * (Units.map (entrywiseHom Fr) (rootSL2 .E8 L r₁ (Bh A)) *
        Units.map (entrywiseHom Fr) (rootSL2 .E8 L r₂ (Ch A))) * n⁻¹ =
      (n * Units.map (entrywiseHom Fr) (rootSL2 .E8 L r₁ (Bh A)) * n⁻¹) *
        (n * Units.map (entrywiseHom Fr) (rootSL2 .E8 L r₂ (Ch A)) * n⁻¹) by group,
      e1, e2]
    rw [show twHom Fr M₁ (Bh A) = Ch A from rfl]
    have h3 : twHom Fr M₂ (Ch A) = Bh A := hfix A
    rw [h3]
    exact (hcomm _ _).symm
  have hmemQ : ∀ r : Fin Tag.E8.rank → ℤ, IsRoot .E8 r → ∀ X : SL2 L,
      rootSL2 .E8 L r X ∈ adjointGroup .E8 L := fun r hr X =>
    rootSpan_le_adjointGroup L _ (show rootSL2 .E8 L r X ∈
      rootSpan .E8 L ({r, -r} : Set (Fin Tag.E8.rank → ℤ)) from
      rootRankOneGroup_le_rootSpan hr (by simp) (by simp) ⟨X, rfl⟩)
  have hL2 : ringChar L ≠ 2 := by
    rw [ringChar.eq L ℓ]
    exact hℓ2
  have hHSL : (-1 : SL2 L) = HSL (-1 : Lˣ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [HSL]
  have hneg : e (-1) ≠ 1 := by
    intro h1
    have hmap : SpecialLinearGroup.map (algebraMap k₂ L) (-1 : SL(2, k₂)) = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.map_apply_coe]
    have hBneg : Bh (-1) = -1 := by
      rw [hBh, MonoidHom.comp_apply, hmap]
      ext i j
      simp [coe_conjSL]
    have hCneg : Ch (-1) = -1 := by
      rw [hCh, MonoidHom.comp_apply, hBneg, twHom_apply]
      have : SpecialLinearGroup.map Fr (-1 : SL2 L) = -1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.map_apply_coe]
      rw [this]
      ext i j
      simp [coe_conjSL]
    have hm : e (-1) = rootTorusSL2 .E8 L r₁ (-1) * rootTorusSL2 .E8 L r₂ (-1) := by
      rw [he, hBneg, hCneg, hHSL]
      rfl
    rw [hm] at h1
    set D₁ := rootTorusSL2 .E8 L r₁ (-1) with hD₁
    set D₂ := rootTorusSL2 .E8 L r₂ (-1) with hD₂
    set X := pinnedX .E8 L σ (1 : L) with hX
    have c2 := rootTorusSL2_conj_pinnedX_of_isRoot (K := L) h₂ hσ (-1 : Lˣ) (1 : L)
    have e₂ : 2 * iform r₂ σ / iform r₂ r₂ = iform r₂ σ := by
      rw [hr₂]
      exact Int.mul_ediv_cancel_left _ (by norm_num)
    have e₁ : 2 * iform r₁ σ / iform r₁ r₁ = iform r₁ σ := by
      rw [hr₁]
      exact Int.mul_ediv_cancel_left _ (by norm_num)
    rw [e₂, Even.neg_one_zpow (even_iff_two_dvd.2 hσ₂)] at c2
    have c1 := rootTorusSL2_conj_pinnedX_of_isRoot (K := L) h₁ hσ (-1 : Lˣ) (1 : L)
    rw [e₁, Odd.neg_one_zpow (Int.not_even_iff_odd.1 (fun h => hσ₁ (even_iff_two_dvd.1 h)))] at c1
    have key : D₁ * (D₂ * X * D₂⁻¹) * D₁⁻¹ = X := by
      calc D₁ * (D₂ * X * D₂⁻¹) * D₁⁻¹ = (D₁ * D₂) * X * (D₁ * D₂)⁻¹ := by group
        _ = X := by rw [h1]; simp
    rw [hX, c2] at key
    have c1' := rootTorusSL2_conj_pinnedX_of_isRoot (K := L) h₁ hσ (-1 : Lˣ)
      (((1 : Lˣ) : L) * (1 : L))
    rw [e₁, Odd.neg_one_zpow (Int.not_even_iff_odd.1 (fun h => hσ₁ (even_iff_two_dvd.1 h)))] at c1'
    rw [c1'] at key
    have hinj := pinnedX_injective .E8 L σ key
    simp at hinj
    exact Ring.neg_one_ne_one_of_char_ne_two hL2 hinj
  refine ⟨e, ?_, fun A => ⟨_, _, he A⟩, fun A => ?_, hfixed⟩
  ·
    rw [injective_iff_map_eq_one]
    intro A hA
    have h1 : rootSL2 .E8 L r₁ (Bh A) * rootSL2 .E8 L r₂ (Ch A) = 1 := hA
    have hcent : ∀ Y : SL2 L, Bh A * Y = Y * Bh A := by
      intro Y
      apply hinj₁
      rw [map_mul, map_mul]
      have h2 : rootSL2 .E8 L r₁ (Bh A) = rootSL2 .E8 L r₂ ((Ch A)⁻¹) := by
        rw [map_inv]
        exact eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact (hcomm Y ((Ch A)⁻¹)).symm
    have hAc : A ∈ Subgroup.center SL(2, k₂) := by
      rw [Subgroup.mem_center_iff]
      intro A'
      apply hBinj
      rw [map_mul, map_mul]
      exact (hcent (Bh A')).symm
    obtain ⟨r, hr, hsc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hAc
    rw [Fintype.card_fin] at hr
    have hfac : (r - 1) * (r + 1) = 0 := by linear_combination hr
    rcases mul_eq_zero.1 hfac with h | h
    · have hr1 : r = 1 := by linear_combination h
      subst hr1
      apply Subtype.ext
      rw [← hsc]
      simp
    · exfalso
      have hr1 : r = -1 := by linear_combination h
      subst hr1
      have hA' : A = -1 := by
        apply Subtype.ext
        rw [← hsc]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [hA'] at hA
      exact hneg hA
  · rw [he]
    exact mul_mem (hmemQ r₁ h₁ _) (hmemQ r₂ h₂ _)

end Block

end CFSG.RankThree.PartOne.KE8F
