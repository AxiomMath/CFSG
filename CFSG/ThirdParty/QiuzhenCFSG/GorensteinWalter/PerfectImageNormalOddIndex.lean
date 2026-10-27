module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
public import Mathlib.GroupTheory.IsPerfect
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

/-!
# Perfect images across solvable kernels
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The image of a nontrivial perfect subgroup across a solvable normal
kernel remains nontrivial and perfect, and lies in every normal odd-index
subgroup of the quotient. -/
public theorem perfect_image_le_normal_odd_index_of_solvable_kernel
    {H : Type u} [Group H] [Finite H]
    (E : Subgroup H) (hEperfect : Group.IsPerfect E) (hEne : E ≠ ⊥)
    (O : Subgroup H) [O.Normal] (hOsolvable : Group.IsSolvable O)
    (L : Subgroup (H ⧸ O)) (hLnormal : L.Normal) (hLindex : Odd L.index) :
    let q : H →* H ⧸ O := QuotientGroup.mk' O
    let Ebar : Subgroup (H ⧸ O) := E.map q
    Ebar ≠ ⊥ ∧ Group.IsPerfect Ebar ∧ Ebar ≤ L := by
  classical
  dsimp
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let Ebar : Subgroup (H ⧸ O) := E.map q
  have hEbarperfect : Group.IsPerfect Ebar := by
    dsimp [Ebar]
    let : Group.IsPerfect E := hEperfect
    exact Group.IsPerfect.map q
  have hEbarne : Ebar ≠ ⊥ := by
    intro hbot
    have hEleO : E ≤ O := by
      have hker : E ≤ q.ker := (Subgroup.map_eq_bot_iff E).mp hbot
      simpa [q, QuotientGroup.ker_mk'] using hker
    let : Group.IsSolvable O := hOsolvable
    have : Group.IsSolvable (E.subgroupOf O) := inferInstance
    have hEsolvable : Group.IsSolvable E :=
      isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEleO)
    let : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).2 hEne
    let : Group.IsPerfect E := hEperfect
    exact Group.IsPerfect.not_isSolvable E hEsolvable
  let : L.Normal := hLnormal
  let pi : (H ⧸ O) →* (H ⧸ O) ⧸ L := QuotientGroup.mk' L
  let I : Subgroup ((H ⧸ O) ⧸ L) := Ebar.map pi
  have hIperfect : Group.IsPerfect I := by
    dsimp [I]
    let : Group.IsPerfect Ebar := hEbarperfect
    exact Group.IsPerfect.map pi
  have hQodd : Odd (Nat.card ((H ⧸ O) ⧸ L)) := by
    simpa only [Subgroup.index_eq_card] using hLindex
  have hQsolvable : Group.IsSolvable ((H ⧸ O) ⧸ L) :=
    odd_order_theorem ((H ⧸ O) ⧸ L) hQodd
  have hIbot : I = ⊥ := by
    by_contra hIne
    let : Group.IsSolvable ((H ⧸ O) ⧸ L) := hQsolvable
    have hIsolvable : Group.IsSolvable I := inferInstance
    let : Nontrivial I := (Subgroup.nontrivial_iff_ne_bot I).2 hIne
    let : Group.IsPerfect I := hIperfect
    exact Group.IsPerfect.not_isSolvable I hIsolvable
  have hEbarL : Ebar ≤ L := by
    have hker : Ebar ≤ pi.ker := (Subgroup.map_eq_bot_iff Ebar).mp hIbot
    simpa [pi, QuotientGroup.ker_mk'] using hker
  exact ⟨hEbarne, hEbarperfect, hEbarL⟩

end CFSG.GorensteinWalter
