module

public import CFSG.Sporadic.MI301Five.RowI
public import CFSG.Sporadic.MI301Five.WreathLayer
public import CFSG.Sporadic.MI301.Frame

public section

namespace CFSG.Sporadic.MI301Five

open CFSG.Blueprint CFSG.Open CFSG.Monster.Existence CFSG.Monster.GMS
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8
  CFSG.LocalAnalysis.GLTheoremA.H301 CFSG.EvenSporadicStandard.HNRecog Subgroup

variable {G : Type} [Group G] [Finite G] {α d z : G}

private theorem glaPLayer_eq_of_commutator_le {p : ℕ} (hp : p.Prime) {X Y : Subgroup G}
    (hXY : X ≤ Y) (hn : (X.subgroupOf Y).Normal) (hc : ⁅Y, Y⁆ ≤ X) :
    GLAPLayer p X = GLAPLayer p Y := by
  apply le_antisymm
  · unfold GLAPLayer
    refine sSup_le fun L hL => le_sSup ?_
    exact glaPComponent_of_isSubnormal' hp (.step hXY hn (.refl Y)) hL
  · unfold GLAPLayer
    refine sSup_le fun L hL => le_sSup ?_
    have hL' : GLAPComponent p Y L := hL
    have hLX : L ≤ X := by
      rw [← CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hL']
      exact (commutator_mono hL'.1 hL'.1).trans hc
    exact CFSG.LocalAnalysis.GLTheoremB.glaPComponent_of_le hp hL' hLX hXY


theorem FiveFrame.hK (F : FiveFrame α d z) (hL : GMSLeechCentralizer z)
    (hX : IsExtraspecialPlusByA5WrTwo ↥(cent2 α d ⊓ cent z)) :
    RowK .m5 5 (rowKOf 5 d (leechQ z)) := by
  show Nonempty (PQuot 5 (rowKOf 5 d (leechQ z)) ≃*
    (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))
  unfold rowKOf
  rw [F.rowIOf_eq, CFSG.Sporadic.MI301.normalizer_leechQ hL]
  exact nonempty_pQuot_glaPLayer_of_shape hX

theorem FiveFrame.hK6 (F : FiveFrame α d z) (hL : GMSLeechCentralizer z)
    (hc : centerOf (rowR0Of d (leechQ z)) = zpowers z) :
    rowKOf 5 d (leechQ z) = GLAPLayer 5 (centralizer ({d} : Set G) ⊓
      centralizer (centerOf (rowR0Of d (leechQ z)) : Set G)) := by
  rw [hc, zpowers_eq_closure, centralizer_closure]
  unfold rowKOf
  rw [F.rowIOf_eq, CFSG.Sporadic.MI301.normalizer_leechQ hL]
  have hdz : d ∈ cent z :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 F.mem_z.2).symm
  have hXY : cent2 α d ⊓ cent z ≤ cent d ⊓ cent z := inf_le_inf_right _ inf_le_right
  refine glaPLayer_eq_of_commutator_le Nat.prime_five hXY ?_ (F.commutator_inf_le hdz)
  rw [normal_subgroupOf_iff hXY]
  intro x y hx hy
  exact ⟨F.conj_mem y hy.1 x hx.1,
    (cent z).mul_mem ((cent z).mul_mem hy.2 hx.2) ((cent z).inv_mem hy.2)⟩

end CFSG.Sporadic.MI301Five
