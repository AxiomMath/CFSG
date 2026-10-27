module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.L71.Free
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.L71.Gen

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem lemma_7_1_a
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A)
    (hT : TypeA p A θ ∨ ∃ E K : Subgroup G, TypeBCore p A θ E K ∧ ¬ E ≤ B) {a : G} (haB : a ∈ B)
    (ha1 : a ≠ 1) :
    zOf (S ⊓ Subgroup.centralizer {a}) ⊓ Subgroup.centralizer (B : Set G) =
      zOf (S ⊓ Subgroup.centralizer (B : Set G)) :=
  lemma_7_1_a_gen h hr hS hB (exists_isRegFam_inf_eq_zpowers h hB hT) haB ha1

theorem lemma_7_1_b
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A)
    (hT : TypeA p A θ ∨ ∃ E K : Subgroup G, TypeBCore p A θ E K ∧ ¬ E ≤ B) :
    zOf (S ⊓ Subgroup.centralizer (B : Set G)) = zOf S ⊓ Subgroup.centralizer (B : Set G) := by
  refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · have hzS : z ∈ S ⊓ Subgroup.centralizer (B : Set G) := zOf_le _ hz
    have hSle : S ≤ Subgroup.centralizer {z} := by
      refine (eq_iSup_inf_centralizer_of_isSr h hr hS hB).le.trans ?_
      refine iSup_le fun a => iSup_le fun haB => iSup_le fun ha1 w hw => ?_
      have hz' : z ∈ zOf (S ⊓ Subgroup.centralizer {a}) ⊓ Subgroup.centralizer (B : Set G) := by
        rw [lemma_7_1_a h hr hS hB hT haB ha1]
        exact hz
      exact Subgroup.mem_centralizer_singleton_iff.mpr ((mem_zOf_iff.mp hz'.1).2 w hw)
    exact ⟨mem_zOf_iff.mpr ⟨hzS.1, fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mp (hSle hw)⟩, hzS.2⟩
  · exact mem_zOf_iff.mpr ⟨⟨zOf_le S hz.1, hz.2⟩, fun w hw => (mem_zOf_iff.mp hz.1).2 w hw.1⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
