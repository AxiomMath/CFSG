module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4TitsA
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H23P4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem RowTits.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : RowTits X) :
    RowTits Y where
  center := center_eq_bot_transport e.symm h.center
  out := H23Out.Out5Pow.of_mulEquiv e h.out
  cen := CenOvergroup.of_mulEquiv e.symm h.cen

theorem RowOK.quot_of_surjective {L S : Type*} [Group L] [Group S] (α : L →* S)
    (hα : Function.Surjective α) (N : Subgroup L) [N.Normal] (hker : α.ker = N) (h : RowOK S) :
    RowOK (L ⧸ N) :=
  RowOK.of_mulEquiv ((QuotientGroup.quotientKerEquivOfSurjective α hα).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)) h

theorem pCore_eq_bot_of_quasisimple {G : Type} [Group G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) (hZ : Subgroup.center ↥L = ⊥) [Finite G] :
    CFSG.pCore 2 ↥L = ⊥ := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq CFSG.pCore_normal with h | h
  · exfalso
    have hP : IsPGroup 2 ↥L := by
      have := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
      rw [h] at this
      exact this.of_surjective (Subgroup.topEquiv : (⊤ : Subgroup ↥L) ≃* ↥L).toMonoidHom
        (Subgroup.topEquiv).surjective
    have hn : Group.IsNilpotent ↥L := hP.isNilpotent
    have hsol : Group.IsSolvable ↥L := inferInstance
    have hnt : Nontrivial ↥L := by
      obtain ⟨-, hs, -⟩ := hq
      have := hs.toNontrivial
      exact Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥L).ne hq.1.commutator_eq_top
  · rwa [hZ, le_bot_iff] at h

theorem RowOK.quot_pCore {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) (h : RowOK ↥L) : RowOK (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hb := pCore_eq_bot_of_quasisimple hq h.center
  exact RowOK.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hb).trans
    QuotientGroup.quotientBot).symm h

theorem RowTits.quot_pCore {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) (h : RowTits ↥L) : RowTits (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hb := pCore_eq_bot_of_quasisimple hq h.center
  exact RowTits.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hb).trans
    QuotientGroup.quotientBot).symm h

end CFSG.Quasithin.H23P4
