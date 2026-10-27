module

public import CFSG.RankThree.PartTwo.Sec14.Item1446
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec12.Item128Bar
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

variable {G : Type} [Group G] [Finite G]

theorem concl142_of_item142 (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) {A L : Subgroup G}
    {c : G} {LB : Subgroup G → Subgroup G} (h : Sec14Std G A c L)
    (h142 : ∀ (e : G) (Le : Subgroup G) (hS : Sec14Std G A e Le),
      Item142 A LB e Le hS.toSec13Data.isElemAbelian.1 hS.toSec13Data.mem_A) :
    Concl142 A LB := by
  intro e he Q hQ
  have hD := h.toSec13Data
  have heA : e ∈ A := (zpowers_mem_omegaA_iff.mp he).1
  have hAe : A ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx heA)
  obtain ⟨Le, hLe⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
    hD.card_eq he
  have hS : Sec14Std G A e Le :=
    { h with zpowers_mem_omegaA := he, mem_lA := Sec12.mem_lA_of_mem_lA422 hAe hLe }
  exact (h142 e Le hS Q hQ).1

omit [Finite G] in
theorem concl142_forall_of_item142 (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h142 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
      (h : Sec14Std G A c L),
      Item142 A (lB A) c L h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec14Std G A c L → Concl142 A (lB A) :=
  fun G _ _ A _ _ h => concl142_of_item142 h422 h45 h fun e Le hS => h142 G A e Le hS

end CFSG.RankThree.PartTwo.Sec14
