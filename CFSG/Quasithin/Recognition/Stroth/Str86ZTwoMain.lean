module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoProp2
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoCor2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G]

theorem str86_l2_eq_and_z2_of_bridge
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hbridge : Str86YCommBridge L1 L2 S) :
    IsL2Quot (2 * k) (oTwoQuot ↥L2) ∧
      Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4 ∧
      Nat.card (Z1 L1 L2 S) = 2 ^ k ∧
      Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3 ∧
      ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S ∧
      ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S := by
  obtain ⟨n, hL2⟩ := h2
  have hn : 2 ≤ n := CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  obtain ⟨h1, h2', h3, h4⟩ := str86_prop377 hF hSB hk hFc hU3 hB2 ⟨n, hL2⟩ hZI hZQ
  obtain ⟨hX1', hX1Q1⟩ := str86X1Comm_of_bridge hF hSB hk hFc hU3 hn hL2 hZI hZQ hbridge
  exact ⟨h1, h2', h3, h4, hX1', hX1Q1⟩

end CFSG.Quasithin.Stroth

end
