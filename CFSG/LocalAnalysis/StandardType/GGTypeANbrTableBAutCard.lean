module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPermAut
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeAMono

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification TypeA

namespace TypeANbrDvd

variable {d p : ℕ} {K : Type} [Field K] [CharP K 2]

theorem exists_diagonal_of_actsDiag_conj [Finite K] {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'}
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    {g : SpecialLinearGroup (Fin d) K} {w : Fin d → K}
    (h : ActsDiag φ' (MulAut.conj (φ' g)) w) :
    ∃ c : K, (g : Matrix (Fin d) (Fin d) K) = diagonal (fun k => c * w k) := by
  obtain ⟨E, hE, hgE⟩ := h
  have hconj : conjAut d K (SpecialLinearGroup.toGL g * E⁻¹) = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := proj_surjective d K x
    rw [conjAut_proj, MulAut.one_apply, proj_eq_proj_iff]
    apply hφker
    have hmain : φ' (CatalogueBHigherLinearAction.slConjugation d K
        (SpecialLinearGroup.toGL g * E⁻¹) y) = φ' y := by
      have h1 : CatalogueBHigherLinearAction.slConjugation d K
          (SpecialLinearGroup.toGL g * E⁻¹) y =
          g * CatalogueBHigherLinearAction.slConjugation d K E⁻¹ y * g⁻¹ := by
        rw [map_mul, MulAut.mul_apply, slConjugation_toGL_eq]
      rw [h1]
      calc φ' (g * CatalogueBHigherLinearAction.slConjugation d K E⁻¹ y * g⁻¹)
          = φ' g * φ' (CatalogueBHigherLinearAction.slConjugation d K E⁻¹ y) *
              (φ' g)⁻¹ := by simp only [map_mul, map_inv]
        _ = MulAut.conj (φ' g)
              (φ' (CatalogueBHigherLinearAction.slConjugation d K E⁻¹ y)) :=
            (MulAut.conj_apply (φ' g)
              (φ' (CatalogueBHigherLinearAction.slConjugation d K E⁻¹ y))).symm
        _ = φ' (CatalogueBHigherLinearAction.slConjugation d K E
              (CatalogueBHigherLinearAction.slConjugation d K E⁻¹ y)) :=
            hgE (CatalogueBHigherLinearAction.slConjugation d K E⁻¹ y)
        _ = φ' y := by
            congr 1
            rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [map_mul, map_inv, hmain, inv_mul_cancel]
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one hconj
  refine ⟨c, ?_⟩
  rw [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] at hc
  have h1 : (g : Matrix (Fin d) (Fin d) K) =
      ((↑g : Matrix (Fin d) (Fin d) K) * (↑(E⁻¹) : Matrix (Fin d) (Fin d) K)) *
        (↑E : Matrix (Fin d) (Fin d) K) := by
    rw [Matrix.mul_assoc,
      show (↑(E⁻¹) : Matrix (Fin d) (Fin d) K) * (↑E : Matrix (Fin d) (Fin d) K) = 1 by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one],
      Matrix.mul_one]
  rw [h1, hc, scalar_apply, hE, diagonal_mul_diagonal]

theorem ActsDiag.conj_of_mul_diagonal {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} {a : MulAut L'} {t t' : Fin d → K}
    (ha : ActsDiag φ' a t) {s : SpecialLinearGroup (Fin d) K}
    (hs : (s : Matrix (Fin d) (Fin d) K) * diagonal t =
      diagonal t' * (s : Matrix (Fin d) (Fin d) K)) :
    ActsDiag φ' (MulAut.conj (φ' s) * a * (MulAut.conj (φ' s))⁻¹) t' := by
  obtain ⟨D, hD, haD⟩ := ha
  refine ⟨SpecialLinearGroup.toGL s * D * SpecialLinearGroup.toGL s⁻¹, ?_, fun y => ?_⟩
  · rw [Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
      SpecialLinearGroup.coe_GL_coe_matrix, hD]
    calc (↑s : Matrix (Fin d) (Fin d) K) * diagonal t * (↑(s⁻¹) : Matrix (Fin d) (Fin d) K)
        = (diagonal t' * (↑s : Matrix (Fin d) (Fin d) K)) *
            (↑(s⁻¹) : Matrix (Fin d) (Fin d) K) := by rw [hs]
      _ = diagonal t' * ((↑s : Matrix (Fin d) (Fin d) K) *
            (↑(s⁻¹) : Matrix (Fin d) (Fin d) K)) := by rw [Matrix.mul_assoc]
      _ = diagonal t' := by
            rw [show (↑s : Matrix (Fin d) (Fin d) K) * (↑(s⁻¹) : Matrix (Fin d) (Fin d) K) = 1 by
                  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
                    Matrix.SpecialLinearGroup.coe_one],
              Matrix.mul_one]
  · have e : CatalogueBHigherLinearAction.slConjugation d K
        (SpecialLinearGroup.toGL s * D * SpecialLinearGroup.toGL s⁻¹) y =
        s * CatalogueBHigherLinearAction.slConjugation d K D (s⁻¹ * y * s) * s⁻¹ := by
      rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, slConjugation_toGL_eq,
        slConjugation_toGL_eq, inv_inv]
    rw [e, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, ← map_inv, ← map_mul,
      ← map_mul, haD, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]

theorem exists_perm_of_conj_mem_normalizer_with_coordinates [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) {L' : Type} [Group L'] [Finite L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) {s : SpecialLinearGroup (Fin d) K}
    (hs : MulAut.conj (φ' s) ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ∃ σ : Equiv.Perm (Fin d),
      (∀ u : Fin d → K, (s : Matrix (Fin d) (Fin d) K) * diagonal u =
        diagonal (u ∘ (σ⁻¹ : Equiv.Perm (Fin d))) * (s : Matrix (Fin d) (Fin d) K)) ∧
      NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
      ∀ a ∈ A,
      MulAut.conj (φ' s) * a * (MulAut.conj (φ' s))⁻¹ =
        NbrInnerWeylA.permConj φ' σ * a * (NbrInnerWeylA.permConj φ' σ)⁻¹ := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (K := K) hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζinv : ζ ≠ ζ⁻¹ := ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hmono : ∀ i j : Fin d, i ≠ j → ∃ D : Fin d → K,
      (↑s : Matrix (Fin d) (Fin d) K) * diagonal (rootT ζ i j) =
        diagonal D * (↑s : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    set Dij : SpecialLinearGroup (Fin d) K :=
      ⟨diagonal (rootT ζ i j), by rw [det_diagonal, prod_rootT hζ0 hij]⟩ with hDij
    have hDijm : (Dij : Matrix (Fin d) (Fin d) K) = diagonal (rootT ζ i j) := rfl
    have haij : MulAut.conj (φ' Dij) ∈ A :=
      conj_mem_of_selfCent hsc hdiag hDijm (rootT_pow hζ.pow_eq_one i j)
    have hbij : MulAut.conj (φ' s) * MulAut.conj (φ' Dij) * (MulAut.conj (φ' s))⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hs (MulAut.conj (φ' Dij))).mp haij
    obtain ⟨w, hwb⟩ := hdiag (MulAut.conj (φ' s) * MulAut.conj (φ' Dij) *
      (MulAut.conj (φ' s))⁻¹) hbij
    have hb_eq : MulAut.conj (φ' s) * MulAut.conj (φ' Dij) * (MulAut.conj (φ' s))⁻¹ =
        MulAut.conj (φ' (s * Dij * s⁻¹)) := by
      simp only [map_mul, map_inv]
    rw [hb_eq] at hwb
    obtain ⟨c, hc⟩ := exists_diagonal_of_actsDiag_conj hφker hwb
    refine ⟨fun k => c * w k, ?_⟩
    have hscaled : (↑(s * Dij * s⁻¹) : Matrix (Fin d) (Fin d) K) *
        (↑s : Matrix (Fin d) (Fin d) K) =
        (↑s : Matrix (Fin d) (Fin d) K) * (Dij : Matrix (Fin d) (Fin d) K) := by
      calc (↑(s * Dij * s⁻¹) : Matrix (Fin d) (Fin d) K) * (↑s : Matrix (Fin d) (Fin d) K)
          = ((↑s : Matrix (Fin d) (Fin d) K) * (Dij : Matrix (Fin d) (Fin d) K)) *
              (↑(s⁻¹) : Matrix (Fin d) (Fin d) K) * (↑s : Matrix (Fin d) (Fin d) K) := by
            rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
        _ = ((↑s : Matrix (Fin d) (Fin d) K) * (Dij : Matrix (Fin d) (Fin d) K)) *
              ((↑(s⁻¹) : Matrix (Fin d) (Fin d) K) * (↑s : Matrix (Fin d) (Fin d) K)) := by
            rw [Matrix.mul_assoc]
        _ = ((↑s : Matrix (Fin d) (Fin d) K) * (Dij : Matrix (Fin d) (Fin d) K)) * 1 := by
            rw [show (↑(s⁻¹) : Matrix (Fin d) (Fin d) K) *
                  (↑s : Matrix (Fin d) (Fin d) K) = 1 by
                rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
                  Matrix.SpecialLinearGroup.coe_one]]
        _ = (↑s : Matrix (Fin d) (Fin d) K) * (Dij : Matrix (Fin d) (Fin d) K) := by
            rw [Matrix.mul_one]
    have h1 := congrArg (fun M : Matrix (Fin d) (Fin d) K =>
      M * (↑s : Matrix (Fin d) (Fin d) K)) hc
    rw [hscaled, hDijm] at h1
    exact h1
  obtain ⟨π, hπ⟩ := exists_perm_mul_diagonal hζinv (SpecialLinearGroup.toGL s)
    (fun i j hij => by
      obtain ⟨D, hD⟩ := hmono i j hij
      exact ⟨D, by simpa only [SpecialLinearGroup.coe_GL_coe_matrix] using hD⟩)
  have hcoord : ∀ u : Fin d → K,
      (s : Matrix (Fin d) (Fin d) K) * diagonal u =
        diagonal (u ∘ ((π⁻¹)⁻¹ : Equiv.Perm (Fin d))) * (s : Matrix (Fin d) (Fin d) K) := by
    intro u
    simpa only [inv_inv, SpecialLinearGroup.coe_GL_coe_matrix] using hπ u
  refine ⟨π⁻¹, hcoord,
    permConj_mem_normalizer_of_selfCent hφ's hφker hA.2 hsc hdiag (π⁻¹),
    fun a ha => ?_⟩
  obtain ⟨t, hat⟩ := hdiag a ha
  have hs' : (↑s : Matrix (Fin d) (Fin d) K) * diagonal t =
      diagonal (t ∘ π) * (↑s : Matrix (Fin d) (Fin d) K) := by
    simpa only [SpecialLinearGroup.coe_GL_coe_matrix] using hπ t
  have hL : ActsDiag φ' (MulAut.conj (φ' s) * a * (MulAut.conj (φ' s))⁻¹) (t ∘ π) :=
    ActsDiag.conj_of_mul_diagonal hat hs'
  have hR : ActsDiag φ' (MulAut.conj (φ' (permSL π)) * a *
      (MulAut.conj (φ' (permSL π)))⁻¹) (t ∘ π) := hat.conj_perm π
  have hpc : NbrInnerWeylA.permConj φ' (π⁻¹) = MulAut.conj (φ' (permSL π)) := by
    show MulAut.conj (φ' (permSL (π⁻¹)⁻¹)) = MulAut.conj (φ' (permSL π))
    rw [inv_inv]
  rw [hpc]
  exact hL.unique hφ's hR

theorem exists_perm_of_conj_mem_normalizer [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) {L' : Type} [Group L'] [Finite L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) {s : SpecialLinearGroup (Fin d) K}
    (hs : MulAut.conj (φ' s) ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ∃ σ : Equiv.Perm (Fin d), ∀ a ∈ A,
      MulAut.conj (φ' s) * a * (MulAut.conj (φ' s))⁻¹ =
        NbrInnerWeylA.permConj φ' σ * a * (NbrInnerWeylA.permConj φ' σ)⁻¹ := by
  obtain ⟨σ, -, -, hσ⟩ := exists_perm_of_conj_mem_normalizer_with_coordinates
    hp hp2 hpK hφ's hφker hA hsc hdiag hs
  exact ⟨σ, hσ⟩

theorem ggAutomizer_eq_range_permAut [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) {L' : Type} [Group L'] [Finite L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t)
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A = (permAut φ' A hN).range := by
  classical
  refine le_antisymm ?_ ?_
  · intro φ hφ
    obtain ⟨g, ⟨l, rfl⟩, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    obtain ⟨s, rfl⟩ := hφ's l
    obtain ⟨σ, hσ⟩ := exists_perm_of_conj_mem_normalizer hp hp2 hpK hφ's hφker hA hsc hdiag hgN
    refine MonoidHom.mem_range.mpr ⟨σ, ?_⟩
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [permAut_apply, ggConjAut_apply, hφg b]
    exact (hσ b b.2).symm
  · rintro _ ⟨σ, rfl⟩
    exact permAut_mem_ggAutomizer hN σ

theorem card_ggAutomizer_eq_factorial_of_model [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) {L' : Type} [Group L'] [Finite L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = d.factorial := by
  classical
  have hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun σ => permConj_mem_normalizer_of_selfCent hφ's hφker hA.2 hsc hdiag σ
  rw [ggAutomizer_eq_range_permAut hp hp2 hpK hφ's hφker hA hsc hdiag hN]
  have hinj : Function.Injective (permAut φ' A hN) :=
    permAut_injective hp hp2 hpK hd hφ's hφker hA hsc hdiag hN
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_perm, Nat.card_fin]

theorem ggAutomizer_card_six_of_nine_le_card
    {K : Type} [Field K] [Finite K] [CharP K 2] {L' : Type} [Group L'] [Finite L']
    {φ' : SpecialLinearGroup (Fin 3) K →* L'}
    (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars 3 K)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hsc : GGTorusSelfCent 3 A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin 3 → K, ActsDiag φ' a t)
    (h3K : 3 ∣ Nat.card K - 1) (h9 : 9 ≤ Nat.card ↥A) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 6 := by
  classical
  let hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun σ => permConj_mem_normalizer_of_selfCent hφ's hφker hA.2 hsc hdiag σ
  have hinj : Function.Injective (permAut φ' A hN) :=
    permAut_injective_of_nine_le_card hN hφ's hφker
      (fun a => hdiag a a.2) h9
  rw [ggAutomizer_eq_range_permAut (p := 3) (by norm_num : Nat.Prime 3)
    (by norm_num : (3 : ℕ) ≠ 2) h3K hφ's hφker hA hsc hdiag hN]
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_perm, Nat.card_fin]
  norm_num

end TypeANbrDvd

end CFSG.StandardType
