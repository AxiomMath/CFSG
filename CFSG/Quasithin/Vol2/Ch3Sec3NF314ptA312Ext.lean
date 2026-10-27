module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312Tools

public section

namespace CFSG.Quasithin.H13.NF314ptA312

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.InspA312
open scoped Pointwise

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem surj_of_cover {Q : Type} [Group Q] {B L : Subgroup Q} (hBL : B ≤ L) (N : Subgroup ↥L)
    [N.Normal] (hcov : ∀ x : ↥L, ∃ b : ↥B, ∃ o ∈ N, x = Subgroup.inclusion hBL b * o) :
    Function.Surjective ((QuotientGroup.mk' N).comp (Subgroup.inclusion hBL) : ↥B →* ↥L ⧸ N) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨b, o, ho, hx⟩ := hcov x
    refine ⟨b, ?_⟩
    rw [hx]
    show (QuotientGroup.mk (Subgroup.inclusion hBL b) : ↥L ⧸ N) =
      QuotientGroup.mk (Subgroup.inclusion hBL b * o)
    rw [QuotientGroup.eq]
    simpa using ho

theorem cover_of_sup {Q : Type} [Group Q] {B L : Subgroup Q} (hBL : B ≤ L) (OL : Subgroup Q)
    (hBN : B ≤ Subgroup.normalizer (OL : Set Q)) (hLO : L ≤ B ⊔ OL) (N : Subgroup ↥L)
    (hN : ∀ o ∈ OL, o ∈ L → ∃ h ∈ N, (h : Q) = o) :
    ∀ x : ↥L, ∃ b : ↥B, ∃ o ∈ N, x = Subgroup.inclusion hBL b * o := by
  intro x
  have hx : (x : Q) ∈ ((B : Set Q) * (OL : Set Q)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right B OL hBN]
    exact hLO x.2
  obtain ⟨b, hb, o, ho, hbo⟩ := Set.mem_mul.mp hx
  have hoL : o ∈ L := by
    have : o = (b : Q)⁻¹ * (x : Q) := by
      rw [← hbo, inv_mul_cancel_left]
    rw [this]
    exact L.mul_mem (L.inv_mem (hBL hb)) x.2
  obtain ⟨h, hh, hhe⟩ := hN o ho hoL
  refine ⟨⟨b, hb⟩, h, hh, ?_⟩
  apply Subtype.ext
  show (x : Q) = (b : Q) * (h : Q)
  rw [hhe]
  exact hbo.symm

theorem two_le_of_isPSL_two_two {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) : 2 ≤ n := by
  have h1 : 1 ≤ n := h.1.2.1
  by_contra hc
  have h2 : n = 1 := by omega
  subst h2
  exact h.1.2.2.2.1 (by norm_num)

end CFSG.Quasithin.H13.NF314ptA312
