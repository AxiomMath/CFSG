module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Self-centralizing Klein four subgroups in odd `PSL₂`
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix

universe u

/-- Every Klein four subgroup of `PSL₂(K)` is self-centralizing. -/
public theorem psl2_kleinFour_centralizer_eq_self
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (V : Subgroup (PSL2 K)) (hV : IsKleinFour V) :
    Subgroup.centralizer (V : Set (PSL2 K)) = V := by
  classical
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := by
    intro x y hxy
    exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective hxy
  let VP : Subgroup (PGL2 K) := V.map toPGL
  have hVP : IsKleinFour VP := isKleinFour_map_of_injective V hV toPGL htoPGL
  have hCP : Subgroup.centralizer (VP : Set (PGL2 K)) = VP :=
    pgl2_kleinFour_centralizer_eq_self K hK VP hVP
  apply le_antisymm
  · intro x hx
    have htx : toPGL x ∈
        Subgroup.centralizer (VP : Set (PGL2 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨v, hv, rfl⟩
      have hcomm : x * v = v * x :=
        (Subgroup.mem_centralizer_iff.mp hx) v hv |>.symm
      simpa using (congrArg toPGL hcomm).symm
    rw [hCP] at htx
    rcases Subgroup.mem_map.mp htx with ⟨v, hv, hxy⟩
    have hvx : x = v := by
      apply htoPGL
      simpa using hxy.symm
    simpa [hvx] using hv
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hVcomm : Commute (⟨x, hx⟩ : V) ⟨y, hy⟩ := by
      let : IsKleinFour V := hV
      exact (IsKleinFour.isMulCommutative (G := V)).is_comm.comm
        ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val hVcomm.eq.symm

end CFSG.GorensteinWalter
