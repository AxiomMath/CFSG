module

public import CFSG.Quasithin.Recognition.Stroth.Str86Q1Eq

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_q1_shape
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S) :
    Q1 L1 L2 S = u3X1 L1 L2 S ∧
      Nat.card (Q1 L1 L2 S) = (2 ^ k) ^ 7 ∧
      ⁅Q1 L1 L2 S, Q1 L1 L2 S⁆ = Z1 L1 L2 S ∧
      Subgroup.center ↥(Q1 L1 L2 S) = (Z1 L1 L2 S).subgroupOf (Q1 L1 L2 S) ∧
      Str86X1Natural hF k hX1' := by
  classical
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hQ1 : Q1 L1 L2 S = u3X1 L1 L2 S :=
    str86Q1Eq_holds G L1 L2 S hF hSB h1 hB2 h2 hZI hZQ
  obtain ⟨hcardX, -, hcenterK1⟩ :=
    str86_X1_structure_of_parts hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hX1Q1
        (str86X1Module_holds hF hSB hk hFc hU3 hB2 h2 hZI hZQ hX1')
  have hNat : Str86X1Natural hF k hX1' :=
    str86_X1Natural_holds hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hX1Q1
  have hK1X : u3K1 L1 L2 S ≤ u3X1 L1 L2 S := by
    rw [← hQ1]
    exact u3K1_le_q1 L1 L2 S
  have hK1comm : IsMulCommutative ↥(u3K1 L1 L2 S) := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact Subgroup.mem_centralizer_iff.mp b.2.2 (a : G) (hK1X a.2)
  have hZ1K1top : (Z1 L1 L2 S).subgroupOf (u3K1 L1 L2 S) = ⊤ := by
    rw [← hcenterK1]
    exact Subgroup.center_eq_top_iff.mpr hK1comm
  have hK1leZ1 : u3K1 L1 L2 S ≤ Z1 L1 L2 S := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥(u3K1 L1 L2 S)) ∈
        (Z1 L1 L2 S).subgroupOf (u3K1 L1 L2 S) := by
      rw [hZ1K1top]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hx'
  have hcenter_le : Subgroup.center ↥(Q1 L1 L2 S) ≤
      (Z1 L1 L2 S).subgroupOf (Q1 L1 L2 S) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hK1leZ1 ⟨x.2, by
      show (x : G) ∈ Subgroup.centralizer (u3X1 L1 L2 S : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haQ : a ∈ Q1 L1 L2 S := by
        rw [hQ1]
        exact ha
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨a, haQ⟩)⟩
  have hcenter_ge : (Z1 L1 L2 S).subgroupOf (Q1 L1 L2 S) ≤
      Subgroup.center ↥(Q1 L1 L2 S) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxZ : (x : G) ∈ Z1 L1 L2 S := Subgroup.mem_subgroupOf.mp hx
    have hQ1C : Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
      le_sup_right.trans hZI
    exact (Subgroup.mem_centralizer_iff.mp (hQ1C y.2) (x : G) hxZ).symm
  refine ⟨hQ1, ?_, ?_, le_antisymm hcenter_le hcenter_ge, hNat⟩
  · rw [hQ1]
    exact hcardX
  · rw [hQ1]
    exact hX1'

end CFSG.Quasithin.Stroth

end
