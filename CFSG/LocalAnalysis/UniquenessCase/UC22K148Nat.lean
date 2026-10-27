module

public import CFSG.Quasithin.Background.SmithB42Sp4Ident
public import CFSG.Quasithin.Background.SmithB42Sp4Nat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
open CFSG.Quasithin.H (StdMod natAut natImage natNorm)
open CFSG.Open (StatedSp)
open scoped Matrix

namespace NatAux

variable {K : Type} [Field K] {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

@[expose] def stdCoord (φ : M ≃+ (Fin 4 → K)) : M ≃+ (Fin 2 ⊕ Fin 2 → K) :=
  φ.trans (LinearEquiv.funCongrLeft K K antiIdx).toAddEquiv

theorem stdCoord_apply (φ : M ≃+ (Fin 4 → K)) (w : M) (j : Fin 2 ⊕ Fin 2) :
    stdCoord φ w j = φ w (antiIdx j) := rfl

@[expose] def stdTheta (φ : M ≃+ (Fin 4 → K)) : StdMod (Fin 2 ⊕ Fin 2) K ≃* Multiplicative M :=
  (AddEquiv.toMultiplicative (stdCoord φ)).symm

theorem binPsi_natAut_apply (φ : M ≃+ (Fin 4 → K)) (s : StatedSp 2 K) (w : M) :
    binPsi (stdTheta φ) (natAut (StatedSp 2 K) s) w =
      (stdCoord φ).symm (spMat s *ᵥ stdCoord φ w) := rfl

theorem binPsi_natAut_antiSpEquiv [CharP K 2] {φ : M ≃+ (Fin 4 → K)} {h : antiSp K}
    {f : M ≃ₗ[ZMod 2] M} (hf : ∀ w, φ (f w) = (glMat (h : GL (Fin 4) K)).mulVec (φ w)) :
    binPsi (stdTheta φ) (natAut (StatedSp 2 K) (antiSpEquiv K h)) = f := by
  refine LinearEquiv.ext fun w => ?_
  rw [binPsi_natAut_apply]
  apply (stdCoord φ).injective
  rw [AddEquiv.apply_symm_apply, spMat_antiSpEquiv]
  funext j
  have h3 : stdCoord φ w ∘ antiIdx.symm = φ w := by
    funext a
    simp [stdCoord_apply]
  rw [Matrix.submatrix_mulVec_equiv, h3, stdCoord_apply, hf]
  rfl

theorem map_natImage_eq [CharP K 2] [Finite K] {π : antiSp K →* (M ≃ₗ[ZMod 2] M)}
    {φ : M ≃+ (Fin 4 → K)} {i : ℕ}
    (hφ : ∀ g w, φ (π g w) = (glMat (((minorAut K ^ i) g : antiSp K) : GL (Fin 4) K)).mulVec (φ w)) :
    (natImage (StatedSp 2 K)).map (binPsi (stdTheta φ)).toMonoidHom = π.range := by
  ext x
  constructor
  · rintro ⟨z, ⟨s, rfl⟩, rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : antiSp K, (minorAut K ^ i) g = (antiSpEquiv K).symm s :=
      ⟨(minorAut K ^ i)⁻¹ ((antiSpEquiv K).symm s), by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]⟩
    refine ⟨g, ?_⟩
    have h1 := binPsi_natAut_antiSpEquiv (hf := hφ g)
    rw [hg, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  · rintro ⟨g, rfl⟩
    exact ⟨natAut (StatedSp 2 K) (antiSpEquiv K ((minorAut K ^ i) g)), ⟨_, rfl⟩,
      binPsi_natAut_antiSpEquiv (hφ g)⟩

theorem mem_natImage_iff [CharP K 2] [Finite K] {π : antiSp K →* (M ≃ₗ[ZMod 2] M)}
    {φ : M ≃+ (Fin 4 → K)} {i : ℕ}
    (hφ : ∀ g w, φ (π g w) = (glMat (((minorAut K ^ i) g : antiSp K) : GL (Fin 4) K)).mulVec (φ w))
    (z : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)) :
    z ∈ natImage (StatedSp 2 K) ↔ binPsi (stdTheta φ) z ∈ π.range := by
  rw [← map_natImage_eq hφ]
  exact (Subgroup.mem_map_iff_mem (f := (binPsi (stdTheta φ)).toMonoidHom)
    (binPsi (stdTheta φ)).injective).symm

theorem mem_natNorm_of_normalizes [CharP K 2] [Finite K] {π : antiSp K →* (M ≃ₗ[ZMod 2] M)}
    {φ : M ≃+ (Fin 4 → K)} {i : ℕ}
    (hφ : ∀ g w, φ (π g w) = (glMat (((minorAut K ^ i) g : antiSp K) : GL (Fin 4) K)).mulVec (φ w))
    {A : Subgroup (M ≃ₗ[ZMod 2] M)} (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    {a' : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)} (ha' : binPsi (stdTheta φ) a' ∈ A) :
    a' ∈ natNorm (StatedSp 2 K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  rw [mem_natImage_iff hφ, mem_natImage_iff hφ, map_mul, map_mul, map_inv]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := hnorm _ ha' x
    exact ⟨y, by rw [← hx]; exact hy.symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hnorm _ (inv_mem ha') y
    refine ⟨x, ?_⟩
    rw [← hx, hy]
    group

end NatAux

open NatAux in
theorem natural_offender_facts {K : Type} [Field K] [Fintype K] [CharP K 2]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (π : antiSp K →* (M ≃ₗ[ZMod 2] M)) (hπ : Function.Injective π) (hnt : Nontrivial M)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    (hAe : CFSG.IsElementaryAbelian 2 A) (hA1 : A ≠ ⊥)
    (hoff : Nat.card M ≤ Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m}) :
    (∃ (i : ℕ) (φ : M ≃+ (Fin 4 → K)), ∀ g w,
        φ (π g w) = (glMat (((minorAut K ^ i) g : antiSp K) : GL (Fin 4) K)).mulVec (φ w)) ∧
      Nat.card M = 2 ^ (4 * n) ∧ A ≤ π.range ∧
      Nat.card A ^ 2 * Nat.card {m : M // ∀ a ∈ A, a m = m} ^ 3 ≤ Nat.card M ^ 3 := by
  classical
  obtain ⟨i, φ, hφ⟩ := CFSG.Quasithin.B42Sp4.exists_natural_of_offender hn hK π hπ hnt hirr A hnorm
    hAe hA1 hoff
  refine ⟨⟨i, φ, hφ⟩, ?_⟩
  have hM : Nat.card M = 2 ^ (4 * n) := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_fun, hK, Nat.card_eq_fintype_card (α := Fin 4),
      Fintype.card_fin, ← pow_mul, mul_comm]
  refine ⟨hM, ?_⟩
  set θ := stdTheta φ with hθ
  set A' : Subgroup (MulAut (StdMod (Fin 2 ⊕ Fin 2) K)) := A.comap (binPsi θ).toMonoidHom with hA'
  have hA'map : A'.map (binPsi θ).toMonoidHom = A :=
    Subgroup.map_comap_eq_self_of_surjective (binPsi θ).surjective A
  have hE : CFSG.Quasithin.IsElemAbelian2 A' :=
    (isElemAbelian2_iff_map θ A').mpr (by rw [hA'map]; exact hAe)
  have hEN : A' ≤ natNorm (StatedSp 2 K) := fun a' ha' => mem_natNorm_of_normalizes hφ hnorm ha'
  have hcardA : Nat.card A' = Nat.card A := by
    have h1 : Nat.card (A'.map (binPsi θ).toMonoidHom) = Nat.card A' :=
      Subgroup.card_map_of_injective (binPsi θ).injective
    rw [hA'map] at h1
    exact h1.symm
  have hcardF : Nat.card (CFSG.Quasithin.fixV A') = Nat.card {m : M // ∀ a ∈ A, a m = m} := by
    have h1 := natCard_fixGL_map θ A'
    rw [hA'map] at h1
    exact h1.symm
  have hcardV : Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) = Nat.card M := natCard_eq θ
  have hnat : A' ≤ natImage (StatedSp 2 K) := by
    by_contra hnot
    have hlt := CFSG.Quasithin.FFC.Sp4Off.card_mul_card_fixV_lt hn hK hEN hE hnot
    rw [hcardA, hcardF, hcardV] at hlt
    omega
  refine ⟨?_, ?_⟩
  · rw [← map_natImage_eq hφ, ← hA'map]
    exact Subgroup.map_mono hnat
  · have h1 := CFSG.Quasithin.B42Sp4.natImage_card_sq_mul_card_fixV_cube_le hnat hE
    rwa [hcardA, hcardF, hcardV] at h1

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
