module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoNormalizerCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoOrder
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The alternating-group recognition in the proper order-two branch

In the proper `|K| = 2` branch, `N=N_G(H)` has order twelve and index five.
Its trivial normal core makes the action on `G ⧸ N` faithful.  After
reindexing the five cosets, the image has order sixty in `S₅`, hence index
two and therefore equals `A₅`.
-/

namespace CFSG.GorensteinWalter

universe u

/-- The proper `|K| = 2` branch is isomorphic to `A₅`. -/
public theorem
    BrauerSuzukiWallHypotheses.mulEquiv_alternatingGroup_five_of_card_K_eq_two_of_normalizer_ne_top
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2)
    (hNne : Subgroup.normalizer (h.H : Set G) ≠ ⊤) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
  have hGcard : Nat.card G = 60 :=
    h.card_eq_sixty_of_card_K_eq_two_of_normalizer_ne_top hk hNne
  have hNiso : Nonempty (N ≃* alternatingGroup (Fin 4)) :=
    h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
  have hNcard : Nat.card N = 12 := by
    calc
      Nat.card N = Nat.card (alternatingGroup (Fin 4)) :=
        Nat.card_congr hNiso.some.toEquiv
      _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)
  have hNindex : N.index = 5 := by
    have hmul := N.index_mul_card
    rw [hNcard, hGcard] at hmul
    omega
  have hCosetCard : Nat.card (G ⧸ N) = 5 := by
    rw [← N.index_eq_card, hNindex]
  let act : G →* Equiv.Perm (G ⧸ N) := MulAction.toPermHom G (G ⧸ N)
  have hcore : N.normalCore = ⊥ := by
    simpa [N] using
      h.normalCore_normalizer_eq_bot_of_card_K_eq_two hk hNne
  have hactInj : Function.Injective act := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [← N.normalCore_eq_ker]
    exact hcore
  let : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  have hCosetFcard : Fintype.card (G ⧸ N) = 5 := by
    simpa [Nat.card_eq_fintype_card] using hCosetCard
  let eCoset : (G ⧸ N) ≃ Fin 5 := Fintype.equivFinOfCardEq hCosetFcard
  let actFin : G →* Equiv.Perm (Fin 5) :=
    (Equiv.permCongrHom eCoset).toMonoidHom.comp act
  have hactFinInj : Function.Injective actFin := by
    intro x y hxy
    apply hactInj
    apply (Equiv.permCongrHom eCoset).injective
    simpa [actFin] using hxy
  let A : Subgroup (Equiv.Perm (Fin 5)) := actFin.range
  let eRange : G ≃* A :=
    MulEquiv.ofBijective actFin.rangeRestrict
      ⟨fun x y hxy ↦ hactFinInj (congrArg Subtype.val hxy),
        MonoidHom.rangeRestrict_surjective actFin⟩
  have hAcard : Nat.card A = 60 := by
    rw [← Nat.card_congr eRange.toEquiv, hGcard]
  have hperm5card : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    norm_num [Fintype.card_perm, Nat.factorial]
  have hAindex : A.index = 2 := by
    have hmul := A.index_mul_card
    rw [hAcard, hperm5card] at hmul
    omega
  have hAalt : A = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hAindex
  exact ⟨eRange.trans (MulEquiv.subgroupCongr hAalt)⟩

end CFSG.GorensteinWalter
