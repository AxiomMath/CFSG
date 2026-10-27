module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeConj
import CFSG.LocalAnalysis.StandardType.GGTorCNormalizer
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpTwoAux4
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpTwoAux5

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.StandardType.CommonJSpTwo
open CFSG.StandardType.SpJoin
open CFSG.StandardType.SpCoord

private lemma exists_conj_map_range_of_spPlaneConj {K : Type} [Field K] [Finite K] {r : ℕ}
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : SpPlaneConj K 3 ζ) :
    ∀ T : Subgroup (StatedSp r K), IsElemAbelian 3 T → Nat.card T = 3 ^ r →
      ∃ α : MulAut (StatedSp r K), T = (spPlaneTorus r ζ).range.map α.toMonoidHom := by
  intro T hT hcard
  obtain ⟨c, hc⟩ := hζ r T hT (by omega)
  refine ⟨MulAut.conj c⁻¹, ?_⟩
  have hcomp : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      MonoidHom.id (StatedSp r K) := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [← hc, Subgroup.map_map, hcomp, Subgroup.map_id]

private lemma signedPerm_of_normalizes_spPlane {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (g : StatedSp r K)
    (hg : ∀ s ∈ (spPlaneTorus r ζ).range, g * s * g⁻¹ ∈ (spPlaneTorus r ζ).range) :
    ∃ u : (Fin r → Multiplicative (ZMod 3)) → (Fin r → Multiplicative (ZMod 3)),
      SpCoord.IsSignedPerm u ∧ ∀ f, g * spPlaneTorus r ζ f * g⁻¹ = spPlaneTorus r ζ (u f) := by
  classical
  have hg' : ∀ f : Fin r → Multiplicative (ZMod 3),
      ∃ f', g * spPlaneTorus r ζ f * g⁻¹ = spPlaneTorus r ζ f' := by
    intro f
    obtain ⟨f', hf'⟩ := hg _ (MonoidHom.mem_range.mpr ⟨f, rfl⟩)
    exact ⟨f', hf'.symm⟩
  choose u hu using hg'
  obtain ⟨π, ε, hε, hπ⟩ := TorC.exists_signedPerm_of_normalizes (p := 3)
    Nat.prime_three (by norm_num) hζ g (fun f => ⟨u f, hu f⟩)
  exact ⟨u, ⟨π, ε, hε, fun f i => hπ f (u f) (hu f) i⟩, hu⟩

theorem ggSecFiveBNativeRow_spTwo {K : Type} [Field K] [Finite K] {r : ℕ} (hK : Nat.card K = 2)
    (hr : 3 ≤ r) :
    GGSecFiveBNativeRow (LargeEvenProj (LargeEvenSpGroup K r)) 3 r
      (fun lab => lab = ⟨.twA, r - 1, 1⟩)
      (fun lab => lab = ⟨.C, r - 1, 1⟩ ∨ (r = 3 ∧ lab = ⟨.B2der, 0, 1⟩)) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by simpa using hK)
  haveI : NeZero r := ⟨by omega⟩
  obtain ⟨ζ, hζinj, hζW, hζconj⟩ := ggCommonJSpTwo_exists_torus (K := K)
  have hAt : GGSecFiveBNativeAt (StatedSp r K) 3 r
      (fun lab => lab = ⟨.twA, r - 1, 1⟩)
      (fun lab => lab = ⟨.C, r - 1, 1⟩ ∨ (r = 3 ∧ lab = ⟨.B2der, 0, 1⟩))
      (spPlaneTorus r ζ).range := by
    refine GGSecFiveBNativeAt.of_torus (spPlaneTorus r ζ)
      (TorC.spPlaneTorus_injective hζinj r) (signedPerm_of_normalizes_spPlane hζinj) ?_
    intro f J hJ hcard
    rcases ggCommonJSpTwo_hcomp hK hr hζinj hζW hJ hcard with
      ⟨hdense, -, hΛ, hlab, hZ⟩ | ⟨hsparse, ⟨-, hΛ, hlab⟩ | ⟨h3, hΛ, hlab⟩⟩
    · exact Or.inl ⟨hdense, ⟨⟨.twA, r - 1, 1⟩, rfl, hΛ, hlab, hZ⟩⟩
    · exact Or.inr ⟨hsparse, ⟨⟨.C, r - 1, 1⟩, Or.inl rfl, hΛ, hlab⟩⟩
    · exact Or.inr ⟨hsparse, ⟨⟨.B2der, 0, 1⟩, Or.inr ⟨h3, rfl⟩, hΛ, hlab⟩⟩
  have hRow : GGSecFiveBNativeRow (StatedSp r K) 3 r
      (fun lab => lab = ⟨.twA, r - 1, 1⟩)
      (fun lab => lab = ⟨.C, r - 1, 1⟩ ∨ (r = 3 ∧ lab = ⟨.B2der, 0, 1⟩)) := by
    refine GGSecFiveBNativeRow.of_std (T₀ := (spPlaneTorus r ζ).range) hAt ?_
    exact exists_conj_map_range_of_spPlaneConj hζconj
  exact GGSecFiveBNativeRow.of_mulEquiv
    (α := (TableBSymp.spProjEquivSp (K := K) (m := r)).symm) hRow

theorem ggSecFiveBNativeSparseRow_spTwo {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGSecFiveBNativeSparseRow (LargeEvenProj (LargeEvenSpGroup K 4)) 3 4 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by simpa using hK)
  obtain ⟨ζ, hζinj, hζW, hζconj⟩ := ggCommonJSpTwo_exists_torus (K := K)
  have hAt : GGSecFiveBNativeSparseAt (StatedSp 4 K) 3 4 (spPlaneTorus 4 ζ).range := by
    refine GGSecFiveBNativeSparseAt.of_torus (spPlaneTorus 4 ζ)
      (TorC.spPlaneTorus_injective hζinj 4) (signedPerm_of_normalizes_spPlane hζinj) ?_
    intro f hf hsparse
    exact ggCommonJSpTwo_sparse hK hζinj hζW hf hsparse
  have hRow : GGSecFiveBNativeSparseRow (StatedSp 4 K) 3 4 := by
    refine GGSecFiveBNativeSparseRow.of_std (T₀ := (spPlaneTorus 4 ζ).range) hAt ?_
    exact exists_conj_map_range_of_spPlaneConj hζconj
  exact GGSecFiveBNativeSparseRow.of_mulEquiv
    (α := (TableBSymp.spProjEquivSp (K := K) (m := 4)).symm) hRow

end CFSG.StandardType

end
