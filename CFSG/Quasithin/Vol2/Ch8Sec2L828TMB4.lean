module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Quasithin.Vol2.Ch8Sec2L828SMB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped commutatorElement

@[expose] def MB4_828 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)),
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian2 X →
    (MathieuCode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rkIdx (fixV X) = 7) →
    (∀ g : MulAut V, g ∈ Subgroup.normalizer (H : Set (MulAut V)) → g ∈ H) ∧
    (∃ z ∈ perfectCore (H ⊓ stabSub (fixV X)), z ^ 3 = 1 ∧
        (∀ g ∈ perfectCore (H ⊓ stabSub (fixV X)),
          ⁅z, g⁆ ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X)))) ∧
        ∃ b ∈ s828BPrime H X, z b * b⁻¹ ∉ fixV X) ∧
    (∀ S : Subgroup (MulAut V), S ≤ H ⊓ stabSub (fixV X) → IsPGroup 2 ↥S →
      ¬ 2 ∣ (S.subgroupOf (H ⊓ stabSub (fixV X))).index →
        ∃ t ∈ S, t ^ 2 = 1 ∧ (∃ g ∈ H, g * t * g⁻¹ ∈ X) ∧
          ∀ z ∈ perfectCore (H ⊓ stabSub (fixV X)),
            (∀ g ∈ perfectCore (H ⊓ stabSub (fixV X)),
              ⁅z, g⁆ ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X)))) →
            t * z * t⁻¹ * z ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X))))

end CFSG.Quasithin.H13
