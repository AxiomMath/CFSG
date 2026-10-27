module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Ctx
public import CFSG.Quasithin.H13.GoldschmidtC137Tail

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

variable {G : Type}

theorem center_eq_bot_of_equiv_alt6 {Q : Type} [Group Q] (e : Q ≃* alternatingGroup (Fin 6)) :
    Subgroup.center Q = ⊥ := by
  have h1 := alternatingGroup.center_eq_bot (α := Fin 6) (by simp)
  ext x
  rw [Subgroup.mem_bot]
  constructor
  · intro hx
    have : e x ∈ Subgroup.center ↥(alternatingGroup (Fin 6)) :=
      Subgroup.mem_center_iff.2 fun g => by
        obtain ⟨y, rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
    rw [h1, Subgroup.mem_bot] at this
    exact (map_eq_one_iff e e.injective).1 this
  · rintro rfl
    exact Subgroup.one_mem _

theorem isAlt6_central_quotient {Q : Type} [Group Q] (e : Q ≃* alternatingGroup (Fin 6)) :
    Nonempty ((Q ⧸ Subgroup.center Q) ≃* alternatingGroup (Fin 6)) := by
  have hc := center_eq_bot_of_equiv_alt6 e
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot.trans e)⟩

namespace S6Ctx

variable [Group G] [Finite G] {X T V L P M : Subgroup G} (h : S6Ctx X T V L P M)
include h

theorem isRankTwoLie2Derived :
    IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  obtain ⟨e⟩ := h.hA6
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (isAlt6_central_quotient e)))))

theorem hB : (L ⊓ centralizer (V : Set G)).subgroupOf X ≤ oTwoPhi (L.subgroupOf X) := by
  rw [h.CLV, ← pCoreOf_subgroupOf_eq h.hLX]
  exact pCoreOf_le_oTwoPhi _

theorem toBaum : BaumCtx X T V L P :=
  ⟨h.hT, h.hprod, h.hL, h.hL2, Or.inl h.hLq, h.isRankTwoLie2Derived, h.hTP, h.hPX, h.hred, h.hVL,
    h.hB⟩

end S6Ctx

end CFSG.Quasithin.H13.U3.GC137
