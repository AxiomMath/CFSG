module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusNatType
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusNatSimple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis

theorem omq_omPlus_iso_natural {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) {k : Type} [Field k] [CharP k 2] (ι : F →+* k) {V : Type}
    [AddCommGroup V] [Module k V] {σ : Representation k (spinGroup (quadPlus n F)) V}
    (hσ : IsSimpleRep σ) {y : V} {χ : spinGroup (quadPlus n F) → k} {μ : Fin n → k}
    (ht : (omPlusCurtisDatum n F hn).IsCurtisType σ y χ μ) (hμ : μ = 0) {a : ℕ}
    (hχ : ∀ h ∈ (omPlusCurtisDatum n F hn).H,
      χ h = ι ((spinMatrix (quadPlus n F) h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) ^ 2 ^ a) :
    ∃ β : V ≃ₗ[k] (Fin n ⊕ Fin n → k), ∀ (g : spinGroup (quadPlus n F)) (v : V),
      β (σ g v) = omPlusNatRep n (ι.comp (iterateFrobenius F 2 a)) g (β v) := by
  have hnat := omq_isCurtisType_omPlus_natural hn hF (ι.comp (iterateFrobenius F 2 a))
  have ht0 : (omPlusCurtisDatum n F hn).IsCurtisType σ y χ 0 := by
    simpa only [hμ] using ht
  have hnatχ : (omPlusCurtisDatum n F hn).IsCurtisType
      (omPlusNatRep n (ι.comp (iterateFrobenius F 2 a)))
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) χ 0 := by
    refine ⟨hnat.1, hnat.2.1, ?_, hnat.2.2.2⟩
    intro h hh
    have hχh : (fun g => (ι.comp (iterateFrobenius F 2 a))
        ((spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩))) h = χ h := by
      show (ι.comp (iterateFrobenius F 2 a))
        ((spinMatrix (quadPlus n F) h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) = χ h
      rw [RingHom.comp_apply, iterateFrobenius_def, map_pow]
      exact (hχ h hh).symm
    rw [hnat.2.2.1 h hh, hχh]
  obtain ⟨β, hβ⟩ := (omPlusCurtisDatum n F hn).iso_of_isCurtisType hσ
    (omq_isSimpleRep_omPlusNatRep_embedding hn (ι.comp (iterateFrobenius F 2 a))) ht0 hnatχ
  exact ⟨β, hβ⟩

end CFSG.LocalAnalysis.WeakClosure81
