module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusFinite
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNatType

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.Quasithin.SmithCurtis
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omq_omMinus_iso_natural {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : 4 ≤ Nat.card K) {k : Type} [Field k]
    [CharP k 2] (ι : K →+* k) {V : Type} [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ) (hμ : μ = 0) {a : ℕ}
    (hχ : ∀ h ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      χ h = ι (mat n h (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) ^ 2 ^ a) :
    ∃ β : V ≃ₗ[k] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → k),
      ∀ (g : spinGroup (quadMinus n K b c)) (v : V),
        β (σ g v) = SmallO8mCurtis.naturalRep n b c (ι.comp (iterateFrobenius K 2 a)) g (β v) := by
  subst hμ
  have hnat := omq_isCurtisType_omMinus_natural hn hirr hK (ι.comp (iterateFrobenius K 2 a))
  exact (SmallO8mCurtis.curtisDatum n hn hirr).iso_of_isCurtisType hσ
    (SmallO8mCurtis.naturalRep_isSimple hn hirr (ι.comp (iterateFrobenius K 2 a))) ht
    ⟨hnat.1, hnat.2.1, fun h hh => by
      have h1 := hnat.2.2.1 h hh
      simp only [RingHom.comp_apply, iterateFrobenius_def, map_pow] at h1
      rw [h1, hχ h hh], hnat.2.2.2⟩

end CFSG.LocalAnalysis.WeakClosure81
