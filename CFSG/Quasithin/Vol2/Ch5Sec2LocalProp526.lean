module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5111

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_2_6_borel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
      sec52S M H ⊔ borelOf L₂ (sec52S M H) = sec52S M H ⊔ (B ⊓ L₂)

section General

variable {G : Type} [Group G] [Finite G]

theorem not_isSolvable_of_perfect {X : Subgroup G} (hX : ⁅X, X⁆ = X) (hne : X ≠ ⊥) :
    ¬ Group.IsSolvable ↥X := fun hs => by
  have h := (isSolvable_iff_perfectCore_eq_bot X).mp hs
  rw [perfectCore_eq_self_of_perfect hX] at h
  exact hne h

end General

namespace Hyp5_2_4

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ : Subgroup G} {n : ℕ}

theorem parabolics_eq (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact)
    (hbor2 : sec52S M H ⊔ borelOf L₂ (sec52S M H) = sec52S M H ⊔ (B ⊓ L₂)) :
    sec52G1 M L H B L₂ = L ⊔ bigB L L₂ (sec52S M H) ∧
      sec52G2 M H D L₂ = L₂ ⊔ bigB L L₂ (sec52S M H) ∧
      bigB L L₂ (sec52S M H) = D ⊔ sec52S M H ⊔ (B ⊓ L₂) := by
  have h := hyp.toHyp5_0_1
  have hN := hyp.notation59
  set S := sec52S M H with hSdef
  have hSL : S ⊓ L = T ⊓ L := h.inf_L_eq h331 hR hyp.hStar
  have hTLS : T ⊓ L ≤ S := hSL ▸ inf_le_left
  have hborL : borelOf L S = borelL T L := by
    unfold borelOf
    rw [hSL]
  have hDTL : D ⊔ (T ⊓ L) = borelL T L := h.borelL_eq_sup hN.2.1
  have hbL : borelOf L S ≤ L := inf_le_left
  have hbL₂ : borelOf L₂ S ≤ L₂ := inf_le_left
  have hB2 : B ⊓ L₂ ≤ S ⊔ borelOf L₂ S := by
    rw [hbor2]
    exact le_sup_right
  have hb2 : borelOf L₂ S ≤ S ⊔ (B ⊓ L₂) := by
    rw [← hbor2]
    exact le_sup_right
  refine ⟨?_, ?_, ?_⟩
  · show L ⊔ S ⊔ (B ⊓ L₂) = L ⊔ (borelOf L S ⊔ borelOf L₂ S ⊔ S)
    have hLY : L ≤ L ⊔ (borelOf L S ⊔ borelOf L₂ S ⊔ S) := le_sup_left
    have hSY : S ≤ L ⊔ (borelOf L S ⊔ borelOf L₂ S ⊔ S) := le_sup_right.trans le_sup_right
    have hb2Y : borelOf L₂ S ≤ L ⊔ (borelOf L S ⊔ borelOf L₂ S ⊔ S) :=
      (le_sup_right.trans le_sup_left).trans le_sup_right
    have hLX : L ≤ L ⊔ S ⊔ (B ⊓ L₂) := le_sup_left.trans le_sup_left
    have hSX : S ≤ L ⊔ S ⊔ (B ⊓ L₂) := le_sup_right.trans le_sup_left
    have hBX : B ⊓ L₂ ≤ L ⊔ S ⊔ (B ⊓ L₂) := le_sup_right
    apply le_antisymm
    · exact sup_le (sup_le hLY hSY) (hB2.trans (sup_le hSY hb2Y))
    · exact sup_le hLX (sup_le (sup_le (hbL.trans hLX) (hb2.trans (sup_le hSX hBX))) hSX)
  · show D ⊔ S ⊔ L₂ = L₂ ⊔ (borelOf L S ⊔ borelOf L₂ S ⊔ S)
    rw [hborL, ← hDTL]
    have hL₂Y : L₂ ≤ L₂ ⊔ (D ⊔ (T ⊓ L) ⊔ borelOf L₂ S ⊔ S) := le_sup_left
    have hSY : S ≤ L₂ ⊔ (D ⊔ (T ⊓ L) ⊔ borelOf L₂ S ⊔ S) := le_sup_right.trans le_sup_right
    have hDY : D ≤ L₂ ⊔ (D ⊔ (T ⊓ L) ⊔ borelOf L₂ S ⊔ S) :=
      (le_sup_left.trans (le_sup_left.trans le_sup_left)).trans le_sup_right
    have hDX : D ≤ D ⊔ S ⊔ L₂ := le_sup_left.trans le_sup_left
    have hSX : S ≤ D ⊔ S ⊔ L₂ := le_sup_right.trans le_sup_left
    have hL₂X : L₂ ≤ D ⊔ S ⊔ L₂ := le_sup_right
    apply le_antisymm
    · exact sup_le (sup_le hDY hSY) hL₂Y
    · exact sup_le hL₂X (sup_le (sup_le (sup_le hDX (hTLS.trans hSX)) (hbL₂.trans hL₂X)) hSX)
  · show borelOf L S ⊔ borelOf L₂ S ⊔ S = D ⊔ S ⊔ (B ⊓ L₂)
    rw [hborL, ← hDTL]
    have hDX : D ≤ D ⊔ S ⊔ (B ⊓ L₂) := le_sup_left.trans le_sup_left
    have hSX : S ≤ D ⊔ S ⊔ (B ⊓ L₂) := le_sup_right.trans le_sup_left
    have hBX : B ⊓ L₂ ≤ D ⊔ S ⊔ (B ⊓ L₂) := le_sup_right
    have hDY : D ≤ D ⊔ (T ⊓ L) ⊔ borelOf L₂ S ⊔ S :=
      le_sup_left.trans (le_sup_left.trans le_sup_left)
    have hSY : S ≤ D ⊔ (T ⊓ L) ⊔ borelOf L₂ S ⊔ S := le_sup_right
    have hb2Y : borelOf L₂ S ≤ D ⊔ (T ⊓ L) ⊔ borelOf L₂ S ⊔ S := le_sup_right.trans le_sup_left
    apply le_antisymm
    · exact sup_le (sup_le (sup_le hDX (hTLS.trans hSX)) (hb2.trans (sup_le hSX hBX))) hSX
    · exact sup_le (sup_le hDY hSY) (hB2.trans (sup_le hSY hb2Y))

end Hyp5_2_4

end CFSG.Quasithin.H13
