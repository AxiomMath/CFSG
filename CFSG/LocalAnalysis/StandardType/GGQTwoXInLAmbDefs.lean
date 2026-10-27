module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGQTwoXInLAmbOn (c : LargeEvenLieTag → Prop) {G : Type} [Group G]
    (Bs X : Subgroup G) : Prop :=
  LargeEvenMarking X (fun lab _ _ I _ θ => c lab.tag ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
    ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)

end CFSG.StandardType

end
