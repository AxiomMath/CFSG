module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.Structure2AuxLemmas

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem thm612
    (h : Counterexample p A θ) : IsMulCommutative (sOne p A θ) :=
  Sec6S32.isMulCommutative_sOne h

theorem lemma613
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    kOf (thetaOf θ B) ⊓ ssol p A θ ≤ Subgroup.normalizer (sOne p A θ : Set G) :=
  Sec6S32.le_normalizer_sOne h hB

theorem lemma614
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    kOf (thetaOf θ B) ⊓ ssol p A θ ≤ thetaOf θ B ⊓ sTwo p A θ ∧
      thetaOf θ B ⊓ sTwo p A θ ≤ khat (thetaOf θ B) :=
  ⟨Sec6S32.le_inf_sTwo h hB, Sec6S32.inf_sTwo_le_khat h hB⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near
