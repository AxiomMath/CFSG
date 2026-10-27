module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3POmegaPlusFixed
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3POmegaPlusSDTwo
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3POmegaPlusSDHigh
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3POmegaPlusDPOne
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3POmegaPlusDPHigh

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckM3_POmegaPlus
    (k f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆) :
    (IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) ε = ε ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε < 2 ∧ ε.rank = 4 ∧
      ∀ x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f,
        ε.mulVec x = x → ε.mulVec y = y → Spin.quadPlus (k + 3) (GaloisField 2 f) x = 0 →
        Spin.quadPlus (k + 3) (GaloisField 2 f) y = 0 →
        QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 →
        ¬ LinearIndependent (GaloisField 2 f) ![x, y]) ∨
    RCKSpinSiegelModel (Spin.quadPlus (k + 3) (GaloisField 2 f)) J' ∨
    RCKSpinFlagModel (Spin.quadPlus (k + 3) (GaloisField 2 f)) J' 4 := by
  obtain ⟨e, he, heε, hsplit⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaPlus k f S hSU hS hε
  rcases hsplit with rfl | ⟨hne, hpair, hεe⟩
  · have hadj : formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e = e :=
      hε.2.2.2.1
    by_cases hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2
    · by_cases hm : e.rank = 4 ∧ ∀ x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f,
          e.mulVec x = x → e.mulVec y = y → Spin.quadPlus (k + 3) (GaloisField 2 f) x = 0 →
          Spin.quadPlus (k + 3) (GaloisField 2 f) y = 0 →
          QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 →
          ¬ LinearIndependent (GaloisField 2 f) ![x, y]
      · exact Or.inl ⟨he, hadj, hdeg, hm⟩
      · exact Or.inr (Or.inl (rckM3_POmegaPlus_fixed k f hf S hSU hS hodd he hadj hdeg hm hJe))
    · by_cases hdeg4 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4
      · exact Or.inr (Or.inl (rckM3_POmegaPlus_selfDualTwo k f hf S hSU hS hodd he hadj
          (by omega) hdeg4 hJe))
      · exact Or.inr (Or.inr (rckM3_POmegaPlus_selfDualHigh k f hf S hSU hS hodd hε he
          (by omega) hJe))
  · by_cases hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2
    · subst hεe
      exact Or.inr (Or.inl (rckM3_POmegaPlus_dualPairOne k f hf S hSU hS hodd he hpair hdeg hJe))
    · exact Or.inr (Or.inr (rckM3_POmegaPlus_dualPairHigh k f hf S hSU hS hodd hε he heε hne
        (by omega) hJe))

end CFSG.StandardType.RCKRP
