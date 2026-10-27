module

public import CFSG.GroupTheory.CoprimeActionSupport.EquivariantTwoKernelLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenOuter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114r4f_exists_lift_bar2 {L : Subgroup G} {b : G}
    (hb : b ∈ normalizer (L : Set G)) {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hbr : orderOf b = r) [Fact q.Prime] (hq2 : q ≠ 2)
    {A : Type} [Group A] (hA : IsPGroup q A) (ι : A →* Bar2 L)
    (hι : Function.Injective ι) (κ : A →* A)
    (hκ : ∀ a, autBar2 (L := L) (N := ⊤) ⟨b, ⟨trivial, hb⟩⟩ (ι a) = ι (κ a)) :
    ∃ ψ : A →* G, Function.Injective ψ ∧ (∀ a, ψ a ∈ L) ∧
      ∀ a, b * ψ a * b⁻¹ = ψ (κ a) := by
  classical
  let xN : ↥(⊤ ⊓ normalizer (L : Set G)) := ⟨b, ⟨trivial, hb⟩⟩
  let β : MulAut (Bar2 L) := autBar2 (L := L) (N := ⊤) xN
  have harg : (Subgroup.inclusion (show (⊤ ⊓ normalizer (L : Set G)) ≤ normalizer (L : Set G)
      from inf_le_right) xN) = (⟨b, hb⟩ : ↥(normalizer (L : Set G))) := Subtype.ext rfl
  have hβ : ∀ x : ↥L, β (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) (L.normalizerMonoidHom ⟨b, hb⟩ x) := by
    intro x
    rw [← harg]
    simpa [β, xN, QuotientGroup.mk'_apply] using
      (autBar2_apply_mk_coe (L := L) (N := ⊤) xN x)
  have hκ' : ∀ a, β (ι a) = ι (κ a) := by
    intro a
    simpa [β, xN] using hκ a
  exact CFSG.GroupTheory.CoprimeActionSupport.EquivariantTwoKernelLift.exists_equivariant_lift_of_two_kernel
    (L := L) hb (N := CFSG.pCore 2 ↥L) (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    hr hr2 hbr hq2 hA ι hι κ β hβ hκ'

end CFSG.LocalAnalysis.UniquenessCase.UC22
