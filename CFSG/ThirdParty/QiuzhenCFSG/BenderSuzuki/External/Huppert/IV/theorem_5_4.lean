module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4.part_a

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert IV.5.4

Book-order entry for Huppert IV.5.4.  The clauses are split by the book proof: part_a proves the normal-Sylow branch, while part_b--part_d remain outside the active dependency path until their real proofs are formalized.
-/

namespace CFSG.BenderSuzuki
namespace External

universe u

/-- Huppert IV.5.4(a): in the minimal non-`q`-nilpotent setup, the Sylow
`q`-subgroup is normal. -/
public theorem huppert_IV_5_4_a
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (hnot : ¬ HasNormalPComplement q Q)
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q) :
    (S : Subgroup Q).Normal :=
  huppert_IV_5_4_a_invariant_sylow_of_minimal_non_pnilpotent
    (Q := Q) (q := q) hproper hnot S hq_dvd

end External
end CFSG.BenderSuzuki
