module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
public import Mathlib.GroupTheory.Transfer

namespace CFSG
end CFSG
open CFSG

/-!
# Suzuki V.2.10, Corollary 1

A cyclic Sylow subgroup for the least prime divisor of the group order has a
normal complement.
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Suzuki
namespace V

universe u

/--
Suzuki, Group Theory II, Chapter 5, Theorem 2.10, Corollary 1.
If p is the least prime divisor of the order of G and a Sylow p-subgroup is
cyclic, then G has a normal p-complement.
-/
public theorem suzuki_ch5_theorem_2_10_corollary_1
    {G : Type u} [Group G] [Finite G] {p : Nat} [Fact p.Prime]
    (P : Sylow p G) (hp : (Nat.card G).minFac = p) (hP : IsCyclic P) :
    HasNormalPComplement p G := by
  classical
  let N : Subgroup G :=
    (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hp)).ker
  have hcomp : N.IsComplement' (P : Subgroup G) := by
    simpa [N] using hP.isComplement' hp
  letI : N.Normal := by
    dsimp [N]
    infer_instance
  refine ⟨N, inferInstance, ?_, ?_⟩
  · change Nat.Coprime p (Nat.card ↥(N : Set G))
    rw [hcomp.card_left]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr P.not_dvd_index
  · exact P.isPGroup'.of_equiv hcomp.symm.QuotientMulEquiv.symm

end V
end Suzuki
end External
end CFSG.BenderSuzuki
