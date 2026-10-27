module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdMod
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdNbr

public section

namespace CFSG.StandardType.UnitAct

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly TableB

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

theorem permSU_mul (hK : UnitaryFieldData 2 n K) (σ τ : Equiv.Perm (Fin d)) :
    permSU hK (σ * τ) = permSU hK σ * permSU hK τ :=
  Subtype.ext (map_mul (CFSG.RankThree.Classical.permGL (K := K)) σ τ)

theorem permSU_one (hK : UnitaryFieldData 2 n K) : permSU hK (1 : Equiv.Perm (Fin d)) = 1 :=
  Subtype.ext (map_one (CFSG.RankThree.Classical.permGL (K := K)))

theorem permSU_inv (hK : UnitaryFieldData 2 n K) (σ : Equiv.Perm (Fin d)) :
    (permSU hK σ)⁻¹ = permSU hK σ⁻¹ :=
  Subtype.ext (map_inv (CFSG.RankThree.Classical.permGL (K := K)) σ).symm

theorem coe_permSU_conj (hK : UnitaryFieldData 2 n K) {D : ↥(unitarySU 2 n K d)}
    {t : Fin d → K} (hD : ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal t)
    (σ : Equiv.Perm (Fin d)) :
    (((permSU hK σ * D * (permSU hK σ)⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = diagonal (fun k => t (σ⁻¹ k)) := by
  have e : (((permSU hK σ * D * (permSU hK σ)⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K)) =
      CFSG.RankThree.Classical.permGL σ * (D : GL (Fin d) K) *
        (CFSG.RankThree.Classical.permGL σ)⁻¹ := rfl
  rw [e, Units.val_mul, Units.val_mul, hD, coe_permGL_matrix, coe_permGL_inv_matrix,
    permMatrix_conj_diag σ t]

theorem perm_image_mem_closure (hK : UnitaryFieldData 2 n K) (φ : ↥(unitarySU 2 n K d) →* L')
    (σ : Equiv.Perm (Fin d)) :
    φ (permSU hK σ) ∈ Subgroup.closure
      {m | m ∈ {x : L' | ∃ τ : Equiv.Perm (Fin d), x = φ (permSU hK τ)} ∧ m * m = 1} := by
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · rw [permSU_one, map_one]
    exact Subgroup.one_mem _
  · intro f x y _ ih
    rw [permSU_mul, map_mul]
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨⟨_, rfl⟩, ?_⟩) ih
    rw [← map_mul, ← permSU_mul, Equiv.swap_mul_self, permSU_one, map_one]

theorem eq_one_of_perm_fixed (hM : UnitTB.Model φ) (hd : 3 ≤ d) {A : Subgroup (MulAut L')}
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) :
    ∀ a ∈ A, (∀ x ∈ {x : L' | ∃ σ : Equiv.Perm (Fin d), x = φ (permSU hM.field σ)},
      MulAut.conj x * a * (MulAut.conj x)⁻¹ = a) → a = 1 := by
  intro a ha hfix
  obtain ⟨t, hat⟩ := hdiag a ha
  exact eq_one_of_conj_perm hM hd hat fun σ => hfix _ ⟨σ, rfl⟩

theorem conj_mul_inv_mem_heart (hM : UnitTB.Model φ) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hd : 3 ≤ d) {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) (σ : Equiv.Perm (Fin d))
    {a : MulAut L'} (ha : a ∈ A) :
    MulAut.conj (φ (permSU hM.field σ)) * a * (MulAut.conj (φ (permSU hM.field σ)))⁻¹ * a⁻¹ ∈
      Subgroup.closure (heartSetU φ p) := by
  obtain ⟨t, hat⟩ := hdiag a ha
  have het := actsDiagU_mul (hat.conj_perm hM.field σ) (actsDiagU_inv hat)
  have hprod : ∏ k, t (σ⁻¹ k) * (t k)⁻¹ = 1 := by
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Equiv.prod_comp σ⁻¹ t]
    exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k _ => hat.ne_zero k)
  have hpow : ∀ k, (t (σ⁻¹ k) * (t k)⁻¹) ^ p = 1 := fun k =>
    hat.ratio_pow hM.field hd hM.ker (hAp a ha) (σ⁻¹ k) k
  obtain ⟨De, hDe⟩ := exists_diagSU hM.field hpq hpow hprod
  have heq : MulAut.conj (φ (permSU hM.field σ)) * a * (MulAut.conj (φ (permSU hM.field σ)))⁻¹ *
      a⁻¹ = MulAut.conj (φ De) := actsDiagU_unique hM.surj het (actsDiagU_conj hDe)
  rw [heq]
  exact Subgroup.subset_closure ⟨De, _, hDe, hpow, rfl⟩

theorem exists_perm_of_normalizes [Finite K] (hM : UnitTB.Model φ)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    (hd : 4 ≤ d) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) {g : ↥(unitarySU 2 n K d)}
    (hg : MulAut.conj (φ g) ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ∃ π : Equiv.Perm (Fin d), ∀ u : Fin d → K,
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal u =
        diagonal (u ∘ π) * ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  classical
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hpv : ∀ k l m : Fin d, TypeA.ggPairVec k l ζ m ^ p = 1 := fun k l m =>
    TypeA.pow_ggPairVec hζ.pow_eq_one m
  have hDex : ∀ k l : Fin d, k ≠ l → ∃ D : ↥(unitarySU 2 n K d),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (TypeA.ggPairVec k l ζ) :=
    fun k l _ => exists_diagSU hM.field hpq (fun m => hpv k l m) (TypeA.prod_ggPairVec ζ hζ0)
  have hconj : ∀ s : ↥(unitarySU 2 n K d),
      MulAut.conj (φ (g * s * g⁻¹)) =
        MulAut.conj (φ g) * MulAut.conj (φ s) * (MulAut.conj (φ g))⁻¹ := by
    intro s
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  have hmono : ∀ i j : Fin d, i ≠ j → ∃ D' : Fin d → K,
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal (TypeA.rootT ζ i j) =
        diagonal D' * ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    obtain ⟨Dij, hDij⟩ := exists_diagSU hM.field hpq (u := TypeA.rootT ζ i j)
      (fun k => TypeA.rootT_pow hζ.pow_eq_one i j k) (TypeA.prod_rootT hζ0 hij)
    set X := g * Dij * g⁻¹ with hX
    have hXA : MulAut.conj (φ X) ∈ A := by
      have h1 : MulAut.conj (φ Dij) ∈ A :=
        conj_mem_of_selfCent hsc hdiag hDij (TypeA.rootT_pow hζ.pow_eq_one i j)
      rw [hX, hconj]
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp h1
    have hXd : ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag :=
      isDiag_of_conj_comm hM hK hd hζinv hDex fun k l _ D hD =>
        IsElemAbelian.comm hA hXA (conj_mem_of_selfCent hsc hdiag hD (hpv k l))
    refine ⟨fun k => ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k k, ?_⟩
    have e1 : X * g = g * Dij := by rw [hX]; group
    have e2 := congrArg (fun y : ↥(unitarySU 2 n K d) =>
      ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) e1
    simp only [Subgroup.coe_mul, Units.val_mul] at e2
    have hXm : ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal fun k => ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k k :=
      ((isDiag_iff_diagonal_diag _).mp hXd).symm
    rw [← hDij, ← e2]
    exact congrArg (· * ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) hXm
  exact TypeA.exists_perm_mul_diagonal hζinv (g : GL (Fin d) K) hmono

theorem exists_weyl_fix [Finite K] (hM : UnitTB.Model φ) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) {w : L'}
    (hw : MulAut.conj w ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ∃ w' ∈ {x : L' | ∃ σ : Equiv.Perm (Fin d), x = φ (permSU hM.field σ)},
      ∀ a ∈ A, a (w * w'⁻¹) = w * w'⁻¹ := by
  classical
  obtain ⟨g, rfl⟩ := hM.surj w
  obtain ⟨π, hπ⟩ := exists_perm_of_normalizes hM hK hp hp2 hpq hd hA hsc hdiag hw
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hpv : ∀ k l m : Fin d, TypeA.ggPairVec k l ζ m ^ p = 1 := fun k l m =>
    TypeA.pow_ggPairVec hζ.pow_eq_one m
  have hDex : ∀ k l : Fin d, k ≠ l → ∃ D : ↥(unitarySU 2 n K d),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (TypeA.ggPairVec k l ζ) :=
    fun k l _ => exists_diagSU hM.field hpq (fun m => hpv k l m) (TypeA.prod_ggPairVec ζ hζ0)
  have hPπ : φ (permSU hM.field π⁻¹) = φ ((permSU hM.field π)⁻¹) := by rw [permSU_inv]
  refine ⟨φ (permSU hM.field π⁻¹), ⟨π⁻¹, rfl⟩, fun a ha => ?_⟩
  obtain ⟨t, hat⟩ := hdiag a ha
  have hsd : ((((g * permSU hM.field π : ↥(unitarySU 2 n K d)) : GL (Fin d) K)) :
      Matrix (Fin d) (Fin d) K).IsDiag := by
    refine isDiag_of_conj_comm hM hK hd hζinv hDex fun k l _ D hD => ?_
    obtain ⟨E, hEdef⟩ : ∃ E : ↥(unitarySU 2 n K d),
        E = permSU hM.field π * D * (permSU hM.field π)⁻¹ := ⟨_, rfl⟩
    have hE : ((E : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal (fun k' => TypeA.ggPairVec k l ζ (π⁻¹ k')) := by
      rw [hEdef]
      exact coe_permSU_conj hM.field hD π
    have hgE : g * E = D * g := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [hE, hD]
      have h1 := hπ (fun k' => TypeA.ggPairVec k l ζ (π⁻¹ k'))
      rw [h1]
      congr 2
      funext m
      simp
    have hsD : g * permSU hM.field π * D = D * (g * permSU hM.field π) :=
      calc g * permSU hM.field π * D = g * E * permSU hM.field π := by rw [hEdef]; group
        _ = D * g * permSU hM.field π := by rw [hgE]
        _ = D * (g * permSU hM.field π) := by group
    have := congrArg (fun y => MulAut.conj (φ y)) hsD
    simpa [map_mul] using this
  have e : φ g * (φ (permSU hM.field π⁻¹))⁻¹ = φ (g * permSU hM.field π) := by
    rw [hPπ, map_inv, inv_inv, map_mul]
  rw [e]
  exact hat.fix_of_diagonal _ ((isDiag_iff_diagonal_diag _).mp hsd).symm

end CFSG.StandardType.UnitAct

end
