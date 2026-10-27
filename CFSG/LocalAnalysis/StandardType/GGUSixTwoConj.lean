module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoSetup
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActCore

public section

namespace CFSG.StandardType.USixTwo

open Matrix CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical CFSG.StandardType.TableBUE
  CFSG.StandardType.SmallU CFSG.StandardType.LineU CFSG.StandardType.UnitTB
  CFSG.StandardType.UnitAct
open scoped commutatorElement

section Matrices

variable {K : Type} [Field K] {d : ℕ}

theorem permGL_conj_apply (σ : Equiv.Perm (Fin d)) (M : GL (Fin d) K) (i j : Fin d) :
    ((permGL σ * M * (permGL σ)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j =
      (M : Matrix (Fin d) (Fin d) K) (σ⁻¹ i) (σ⁻¹ j) := by
  have hinv : (permGL σ : GL (Fin d) K)⁻¹ = permGL σ⁻¹ := (map_inv (permGL (K := K)) σ).symm
  rw [hinv, Units.val_mul, Units.val_mul, Matrix.mul_apply]
  simp only [Matrix.mul_apply, permGL_apply, inv_inv, ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_eq, Finset.sum_comm]
  rw [Finset.sum_eq_single (σ.symm j)]
  · simp
  · intro x _ hx
    rw [if_neg]
    intro h
    exact hx (by rw [← h]; simp)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem isBlockOn_permGL_conj (σ : Equiv.Perm (Fin d)) {S : Finset (Fin d)} {M : GL (Fin d) K}
    (hM : IsBlockOn S (M : Matrix (Fin d) (Fin d) K)) :
    IsBlockOn (S.map σ.toEmbedding)
      ((permGL σ * M * (permGL σ)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  intro i j hij
  rw [permGL_conj_apply]
  have h' : σ⁻¹ i ∉ S ∨ σ⁻¹ j ∉ S := by
    rcases hij with h | h
    · refine Or.inl fun hmem => h ?_
      rw [Finset.mem_map]
      exact ⟨σ⁻¹ i, hmem, by simp⟩
    · refine Or.inr fun hmem => h ?_
      rw [Finset.mem_map]
      exact ⟨σ⁻¹ j, hmem, by simp⟩
  rw [hM _ _ h']
  simp [Matrix.one_apply]

end Matrices

section Block

variable {K : Type} [Field K] {n d : ℕ}

theorem blockSU_conj_mem (hh : UnitaryFieldData 2 n K) (σ : Equiv.Perm (Fin d))
    {S : Finset (Fin d)} {b : ↥(unitarySU 2 n K d)} (hb : b ∈ blockSU S) :
    permSU hh σ * b * (permSU hh σ)⁻¹ ∈ blockSU (S.map σ.toEmbedding) :=
  isBlockOn_permGL_conj σ hb

theorem blockSU_conj_inv_mem (hh : UnitaryFieldData 2 n K) (σ : Equiv.Perm (Fin d))
    {S : Finset (Fin d)} {b : ↥(unitarySU 2 n K d)} (hb : b ∈ blockSU (S.map σ.toEmbedding)) :
    (permSU hh σ)⁻¹ * b * permSU hh σ ∈ blockSU S := by
  have h := blockSU_conj_mem hh σ⁻¹ hb
  rw [← permSU_inv, inv_inv] at h
  have e : (S.map σ.toEmbedding).map (σ⁻¹).toEmbedding = S := by
    rw [Finset.map_map]
    ext x
    simp
  rwa [e] at h

end Block

section LayerConj

variable {L' : Type} [Group L'] [Finite L'] {K : Type} [Field K] [Finite K]

theorem layer_conj_of_perm {φ : ↥(unitarySU 2 1 K 6) →* Qt L'} (hM : Model φ)
    {a₀ a₁ : MulAut L'}
    (hcomp₀ : IsComponentOf (LargeEvenLayer (ggFix (qAutHom L' a₀)))
      (ggFix (qAutHom L' a₀)))
    (hcomp₁ : IsComponentOf (LargeEvenLayer (ggFix (qAutHom L' a₁)))
      (ggFix (qAutHom L' a₁)))
    {S₀ S₁ : Finset (Fin 6)}
    (hS₀ : LargeEvenLayer (ggFix (qAutHom L' a₀)) = (blockSU S₀).map φ)
    (hS₁ : LargeEvenLayer (ggFix (qAutHom L' a₁)) = (blockSU S₁).map φ)
    (τ : Equiv.Perm (Fin 6)) (hτ : S₁.map τ.toEmbedding = S₀) :
    ∃ l : L', LargeEvenLayer (ggFix a₀) =
      (LargeEvenLayer (ggFix a₁)).map (MulAut.conj l).toMonoidHom := by
  obtain ⟨l, hl⟩ := qmk_surjective (φ (permSU hM.field τ))
  refine ⟨l, ?_⟩
  rw [(layer_eq_commutator_comap qmk_surjective qmk_ker_le_center (qAutHom_compat a₀)
      hcomp₀).1,
    (layer_eq_commutator_comap qmk_surjective qmk_ker_le_center (qAutHom_compat a₁) hcomp₁).1,
    Subgroup.map_commutator]
  have hP : ((LargeEvenLayer (ggFix (qAutHom L' a₀))).comap (qmk L')) =
      ((LargeEvenLayer (ggFix (qAutHom L' a₁))).comap (qmk L')).map
        (MulAut.conj l).toMonoidHom := by
    rw [hS₀, hS₁]
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb, hbx⟩ := hx
      have hb₁ : (permSU hM.field τ)⁻¹ * b * permSU hM.field τ ∈ blockSU S₁ :=
        blockSU_conj_inv_mem hM.field τ (hτ ▸ hb)
      refine ⟨l⁻¹ * x * l, ⟨_, hb₁, ?_⟩, by show l * (l⁻¹ * x * l) * l⁻¹ = x; group⟩
      simp only [map_mul, map_inv]
      rw [hl, ← hbx]
    · rintro ⟨y, ⟨b₁, hb₁, hby⟩, rfl⟩
      refine ⟨permSU hM.field τ * b₁ * (permSU hM.field τ)⁻¹, ?_, ?_⟩
      · rw [← hτ]
        exact blockSU_conj_mem hM.field τ hb₁
      · show _ = qmk L' (l * y * l⁻¹)
        simp only [map_mul, map_inv]
        rw [hl, ← hby]
  rw [hP]

theorem largeEvenSmall_conj_iff {X Y : Subgroup L'} (l : L')
    (h : X = Y.map (MulAut.conj l).toMonoidHom) : LargeEvenSmall X ↔ LargeEvenSmall Y :=
  (largeEvenSmall_congr ((Subgroup.equivMapOfInjective Y (MulAut.conj l).toMonoidHom
    (MulAut.conj l).injective).trans (MulEquiv.subgroupCongr h.symm))).symm

end LayerConj


end CFSG.StandardType.USixTwo

end
