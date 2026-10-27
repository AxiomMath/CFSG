module

public import CFSG.RankThree.GF2n.Tim79a34BigBar
public import CFSG.RankThree.GF2n.Tim79a34BigNatural
public import CFSG.RankThree.GF2n.Tim79a34TwWSplit

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem card_wbar_mul_card_inf {M V H : Subgroup G} (hWM : wOf V H ≤ M) :
    Nat.card ↥(WbarM M V H) * Nat.card ↥(wOf V H ⊓ inSubgroup (pCore 2) M) =
      Nat.card ↥(wOf V H) := by
  let f : ↥(wOf V H) →* Mbar M :=
    (QuotientGroup.mk' ((inSubgroup (pCore 2) M).subgroupOf M)).comp (Subgroup.inclusion hWM)
  have hrange : f.range = WbarM M V H := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact mem_WbarM_iff.mpr ⟨Subgroup.inclusion hWM w, w.2, rfl⟩
    · intro hx
      obtain ⟨w, hw, rfl⟩ := mem_WbarM_iff.mp hx
      exact ⟨⟨w, hw⟩, rfl⟩
  have hker : Nat.card f.ker = Nat.card ↥(wOf V H ⊓ inSubgroup (pCore 2) M) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨(w.1 : G), w.1.2, ?_⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
        left_inv := fun w => rfl
        right_inv := fun x => rfl }
    · have := MonoidHom.mem_ker.mp w.2
      have h2 : (Subgroup.inclusion hWM w.1 : ↥M) ∈ (inSubgroup (pCore 2) M).subgroupOf M :=
        (QuotientGroup.eq_one_iff _).mp this
      exact Subgroup.mem_subgroupOf.mp h2
    · refine MonoidHom.mem_ker.mpr ?_
      show (QuotientGroup.mk (Subgroup.inclusion hWM ⟨x.1, x.2.1⟩) : Mbar M) = 1
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr x.2.2)
  have h := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange] at h
  rw [mul_comm]
  exact h

theorem bigWbarCardStatement_of_qw (hQW : BigQWStatement) : BigWbarCardStatement := by
  intro G _ _ M V Q P H hH
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hQMeq : Q = inSubgroup (pCore 2) M := hc.hQ
  have hWM := wOf_le_M_of_minCex hc
  have h1 := card_wbar_mul_card_inf (V := V) (H := H) hWM
  have hcardQ : Nat.card ↥(wOf V H ⊓ inSubgroup (pCore 2) M) = Nat.card ↥(P ⊓ wOf V H) := by
    rw [← hQMeq, inf_comm, hQW G M V Q P H hH]
  rw [hcardQ] at h1
  have h2 := twistedWSplit_holds G M V Q P H hH.setup hH.concl
  have hpos : 0 < Nat.card ↥(P ⊓ wOf V H) := Nat.card_pos
  have h3 : Nat.card ↥(WbarM M V H) * Nat.card ↥(P ⊓ wOf V H) =
      Nat.card ↥(V ⊓ wOf V H) * Nat.card ↥(P ⊓ wOf V H) := by
    rw [h1, h2, mul_comm]
  rw [Nat.eq_of_mul_eq_mul_right hpos h3]
  exact hH.module

end CFSG.RankThree.GF2n.Tim79a
