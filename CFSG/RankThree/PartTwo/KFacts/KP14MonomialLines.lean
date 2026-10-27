module

public import CFSG.RankThree.PartTwo.KFacts.KP14Monomial
public import CFSG.RankThree.SubgroupLists.CliffordPrime

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP14

open Matrix CFSG.RankThree.SubgroupLists

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_conj_monomial (L : Fin 3 → Submodule (ZMod 3) (Fin 3 → ZMod 3))
    (hL : DirectSum.IsInternal L) (h1 : ∀ i, Module.finrank (ZMod 3) (L i) = 1) :
    ∃ P : GL (Fin 3) (ZMod 3), ∀ g : GL (Fin 3) (ZMod 3),
      (∀ i, ∃ j, translate g (L i) = L j) → P⁻¹ * g * P ∈ monomial := by
  classical
  have hne : ∀ i, ∃ v ∈ L i, v ≠ 0 := fun i =>
    Submodule.exists_mem_ne_zero_of_ne_bot (fun h => by
      have := h1 i
      rw [h, finrank_bot] at this
      exact absurd this (by decide))
  choose b hbL hb0 using hne
  have hspan : ∀ i, L i = (ZMod 3) ∙ b i := fun i =>
    (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr (hbL i))
      (by rw [finrank_span_singleton (hb0 i), h1 i])).symm
  have hind : LinearIndependent (ZMod 3) b :=
    hL.submodule_iSupIndep.linearIndependent L hbL hb0
  set P₀ : Matrix (Fin 3) (Fin 3) (ZMod 3) := Matrix.of fun i j => b j i
  have hP₀ : IsUnit P₀ := Matrix.linearIndependent_cols_iff_isUnit.mp hind
  refine ⟨hP₀.unit, fun g hg => ?_⟩
  choose π hπ using hg
  have hgb : ∀ i, ∃ c : ZMod 3, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ b i = c • b (π i) := by
    intro i
    have hmem : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ b i ∈ L (π i) := by
      rw [← hπ i]
      exact mulVec_mem_translate (hbL i)
    rw [hspan (π i), Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  choose s hs using hgb
  have hgv : ∀ v : Fin 3 → ZMod 3, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = 0 → v = 0 := by
    intro v hv
    have := congrArg (fun w => ((g⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w)
      hv
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  have hs0 : ∀ i, s i ≠ 0 := by
    intro i h
    apply hb0 i
    apply hgv
    rw [hs i, h, zero_smul]
  have hπinj : Function.Injective π := by
    intro i k hik
    by_contra hne
    have hbi : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ b i ∈ L (π k) := by
      rw [← hik, ← hπ i]
      exact mulVec_mem_translate (hbL i)
    rw [← hπ k, mem_translate] at hbi
    obtain ⟨w, hw, hwe⟩ := hbi
    have hwb : w = b i := by
      have : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ (w - b i) = 0 := by
        rw [Matrix.mulVec_sub, hwe, sub_self]
      exact sub_eq_zero.mp (hgv _ this)
    have hdisj : Disjoint (L i) (L k) := hL.submodule_iSupIndep.pairwiseDisjoint hne
    have : b i ∈ L i ⊓ L k := ⟨hbL i, hwb ▸ hw⟩
    rw [hdisj.eq_bot, Submodule.mem_bot] at this
    exact hb0 i this
  have hπbij : Function.Bijective π := Finite.injective_iff_bijective.mp hπinj
  have hcomm : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) * P₀ = P₀ * signedMat π s := by
    ext i j
    have h := congrFun (hs j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    simp only [Matrix.mul_apply, P₀, Matrix.of_apply, signedMat]
    rw [h, Finset.sum_eq_single (π j)]
    · rw [ite_eq_left rfl, mul_comm]
    · intro k _ hk
      rw [ite_eq_right hk, mul_zero]
    · simp
  refine ⟨π, hπbij, s, hs0, ?_⟩
  show ((hP₀.unit⁻¹ * g * hP₀.unit : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = _
  have hU : ((hP₀.unit : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = P₀ :=
    IsUnit.unit_spec hP₀
  have hinv : ((hP₀.unit⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) * P₀ = 1 := by
    rw [show ((hP₀.unit⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) * P₀ =
      ((hP₀.unit⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *
        ((hP₀.unit : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) by rw [hU]]
    exact Units.inv_mul _
  rw [Units.val_mul, Units.val_mul, mul_assoc, hU, hcomm, ← mul_assoc, hinv, Matrix.one_mul]

end CFSG.RankThree.PartTwo.KFacts.KP14
