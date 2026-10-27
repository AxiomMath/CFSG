module

public import CFSG.Quasithin.H13.VolIC113c2
public import CFSG.Quasithin.H13.VolIC113c3

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem asC113c_holds :
    ∀ (G : Type) [Group G] [Finite G] (L T : Subgroup G), IsSylowTwoOf T (L ⊔ T) →
      T ≤ Subgroup.normalizer (L : Set G) → IsShort2 L →
        ∀ m : ℕ, (m = 3 ∨ m = 5) → IsAltType L m →
          pCoreOf 2 (L ⊔ T) = blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
          blockU L ⊓ (T ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
          (∃ _ : IsMulCommutative ↥(blockU L),
            AlternatingNatural (V := ↥(blockU L)) (autOn L (blockU L)) ⊤ ⊥ m) ∧
          (m = 3 → Nonempty (↥L ≃* alternatingGroup (Fin 4))) ∧
          (m = 5 → ∃ _ : ((blockU L).subgroupOf L).Normal,
            Nonempty (↥L ⧸ (blockU L).subgroupOf L ≃* alternatingGroup (Fin 5)) ∨
              (Nonempty (↥L ⧸ (blockU L).subgroupOf L ≃*
                  Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
                Nat.card (Subgroup.center ↥L) = 2)) ∧
          pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
  intro G _ _ L T hT hTN hL m hm hA
  rcases hm with rfl | rfl
  ·
    have hZ := blockZ_eq_bot_of_alt3 hL hA
    refine ⟨pCoreOf_eq_sup_of_alt3 hL hT hTN hA, ?_, alternatingNatural_of_isAltType
      (by decide) hL hA hZ, fun _ => nonempty_mulEquiv_alt4 hL hA, fun h => absurd h (by decide),
      fun q hq => ?_⟩
    · rw [eq_bot_iff, ← hZ]
      exact fun x hx => ⟨hx.1, hx.2.2⟩
    · have hQU := blockQ_eq_blockU_of_alt3 hL hA
      refine Subgroup.mem_centralizer_iff.mpr fun n hn => ?_
      have hnU : n ∈ blockU L := by rw [← hQU]; exact hn
      exact (pCoreOf_comm_blockU hL hT hTN hq hnU).symm
  ·
    obtain ⟨hO, hUC⟩ := stmtC113c G L T hT hTN hL hA
    refine ⟨hO, hUC, alternatingNatural_of_isAltType (by decide) hL hA
      (AppC.blockZ_eq_bot_of_alt5 hL hA), fun h => absurd h (by decide),
      fun _ => quotient_dichotomy_of_alt5 hL hT hTN hA, fun q hq => ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun n hn => ?_
    exact (blockQ_comm_pCoreOf hL hT hTN hA hq hn).symm

end CFSG.Quasithin.H13.VolI
