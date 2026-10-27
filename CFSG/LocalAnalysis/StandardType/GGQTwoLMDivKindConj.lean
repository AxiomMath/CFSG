module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivKindDiag
public import CFSG.ClassicalGroups.Unitary.Perfect
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.Quasithin.Vol2.Ch11SecO6E
import CFSG.Quasithin.Background.A3Structure312Defs
import CFSG.Quasithin.Vol2.Ch11SecAFacts
import CFSG.Quasithin.Vol2.Ch11SecDFacts
import CFSG.Quasithin.Vol2.Ch11StatementsF
import CFSG.Quasithin.Vol2.Ch11StatementsH
import CFSG.Quasithin.Vol2.Ch1Faithful

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ} {L0 : Type} [Group L0]

theorem qTwoLMDivKind_mem_center_of_map (hF : Nat.card F0 = 4) (hm : 4 ≤ m)
    {π : Su F0 2 1 m →* L0} (hπ : π.ker ≤ Subgroup.center (Su F0 2 1 m)) {s : Su F0 2 1 m}
    (hs : π s ∈ Subgroup.center L0) : s ∈ Subgroup.center (Su F0 2 1 m) := by
  have hK : Nat.card F0 = (2 ^ 1) ^ 2 := by rw [hF]; norm_num
  have hperf : Group.IsPerfect (Su F0 2 1 m) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) hK)
      (by omega) (fun h3 => absurd h3 (by omega))
  refine @CFSG.Quasithin.Vol2.Ch11.O6.mem_center_of_comm_mem_center (Su F0 2 1 m) _ hperf s ?_
  intro u
  apply hπ
  rw [MonoidHom.mem_ker]
  have hsu : π u * π s = π s * π u := Subgroup.mem_center_iff.mp hs (π u)
  simp only [map_mul, map_inv]
  calc π s * π u * (π s)⁻¹ * (π u)⁻¹
      = π u * π s * (π s)⁻¹ * (π u)⁻¹ := by rw [← hsu]
    _ = 1 := by group

end CFSG.StandardType.QTwo

end
