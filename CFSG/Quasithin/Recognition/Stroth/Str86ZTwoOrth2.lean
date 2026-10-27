module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
public import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86_u3H_eq_oTwoUpper_sup_q2 {L1 L2 S : Subgroup G}
    {n : ℕ} (hF : F112HypW L1 L2 S) (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) :
    u3H L1 L2 S = oTwoUpper (u3H L1 L2 S) ⊔ Q2 L1 L2 S := by
  classical
  let H := u3H L1 L2 S
  let π : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (pCore 2 ↥H)
  have hperf : Group.IsPerfect (oTwoQuot ↥H) := by
    have hP : Group.IsPerfect (oTwoQuot ↥L2) := isPerfect_of_isL2Quot hn hL2
    exact Group.IsPerfect.ofSurjective
      (f := (str86_oTwoQuot_u3H_equiv hF).symm.toMonoidHom)
      (str86_oTwoQuot_u3H_equiv hF).symm.surjective
  have hmap : (oTwoUpper (⊤ : Subgroup ↥H)).map π = ⊤ := by
    rw [← oTwoUpper_map π (⊤ : Subgroup ↥H),
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective (pCore 2 ↥H))]
    exact le_antisymm le_top (perfect_le_oTwoUpper le_top
      (inferInstance : Group.IsPerfect ↥(⊤ : Subgroup (oTwoQuot ↥H))))
  have hsup : (⊤ : Subgroup ↥H) = oTwoUpper (⊤ : Subgroup ↥H) ⊔ pCore 2 ↥H := by
    have hcomap := Subgroup.comap_map_eq π (oTwoUpper (⊤ : Subgroup ↥H))
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
    exact hcomap
  have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [Subgroup.map_top, Subgroup.range_subtype H]
  have hO : (oTwoUpper (⊤ : Subgroup ↥H)).map H.subtype = oTwoUpper H := by
    rw [← oTwoUpper_map H.subtype (⊤ : Subgroup ↥H), htop]
  have hQ : (pCore 2 ↥H).map H.subtype = Q2 L1 L2 S := by
    change pCoreOf 2 H = Q2 L1 L2 S
    simpa [H] using str86_pCoreOf_u3H hF
  calc H = (⊤ : Subgroup ↥H).map H.subtype := htop.symm
    _ = (oTwoUpper (⊤ : Subgroup ↥H) ⊔ pCore 2 ↥H).map H.subtype := by
          conv_lhs => rw [hsup]
    _ = oTwoUpper H ⊔ Q2 L1 L2 S := by rw [Subgroup.map_sup, hO, hQ]

end CFSG.Quasithin.Stroth
