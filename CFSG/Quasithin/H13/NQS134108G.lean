module

public import CFSG.Quasithin.H13.NQS134108F
public import CFSG.Quasithin.H13.NQS134108D

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem eight (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h1222 : Stmt12_2_2) (h1347 : U3.Stmt13_4_7L2) (h1345 : Stmt13_4_5)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hnhat : ¬ A6.IsHatA6 L) {H₂ : Subgroup G} (hstar : IsHStar T (normalizer (L : Set G)) H₂)
    (hH₂H : H₂ ≤ H) :
    InH T (h0Of S H₂) ∧
      ((U3.Concl1347i T H₂ (U3.l2Of S ⊔ T) ∧
          wt S ⟨z, (inf_le_left : fsuV1 T V ≤ V) D.zV1⟩ = 4 ∧
          V ⊓ centralizer (L : Set G) ≤ ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ ∧
          (IsCore5 K ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ →
            ∀ v ∈ V ⊓ centralizer (L : Set G), v ≠ 1 →
              HasWtIn K ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ v 4)) ∨
        (U3.Concl1347ii T H₂ (U3.l2Of S ⊔ T) ∧
          h0Of S H₂ = normalizer (thompsonJ T : Set G) ∧ InM T (h0Of S H₂) ∧
          ∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X → X ≤ h0Of S H₂ → X = H₂)) := by
  obtain ⟨hVKW, -, -, -, -, -⟩ := D.main_of_a6 hC137 h1332 h1228 hC58 h317 h56 he
  obtain ⟨-, -, -, -, -, hInH0, hH0M, -, -, hcases⟩ :=
    D.eight_setup hC137 h1332 h1228 hC58 h317 h56 h1222 h1347 he hnhat hstar hH₂H
  have h0 : h0Of S H₂ = H₂ ⊔ (U3.l2Of S ⊔ T) := sup_comm _ _
  rw [h0, hVKW]
  refine ⟨hInH0, ?_⟩
  rcases hcases with hi | ⟨hii, hmax⟩
  · obtain ⟨hpsi, hZVW, -⟩ :=
      D.eight_i hC137 h1332 h1228 hC58 h317 h56 h1222 h1347 he hnhat hstar hH₂H hi
    refine Or.inl ⟨hi, ?_, hZVW,
      D.hasWtIn_zV hC137 h1332 h1228 hC58 h317 h56 h1222 h1347 he hnhat hstar hH₂H hi⟩
    show (Finset.univ.filter fun i : Fin 6 =>
      Multiplicative.toAdd (S.frame.ψ ⟨z, D.zV1.1⟩ : G6.PermMod 6) i = 1).card = 4
    rw [hpsi]
    exact wt6_e0123
  ·
    have hTM : T ≤ normalizer (L : Set G) := S.T_le_NL
    have hL2TM : U3.l2Of S ⊔ T ≤ normalizer (L : Set G) :=
      sup_le ((U3.s134_L2_le_L S).trans le_normalizer) hTM
    obtain ⟨-, h2T, -, -⟩ := U3.s134_parabolics S
    have hZcard := U3.s134_card_Z h1332 hC58 h317 h56 S D.exists_inH
    have hL2H₂ : ¬ U3.l2Of S ⊔ T ≤ H₂ := by
      intro h
      apply D.zL
      have hzc : z ∈ U3.cZ T (U3.l2Of S ⊔ T) :=
        mem_inf.2 ⟨D.zV1.2, U3.mem_centralizer_of_le_centralizer (h.trans (hH₂H.trans D.Hz))⟩
      rw [U3.s134_cZ_L2T S hZcard] at hzc
      exact (mem_inf.1 hzc).2
    exact Or.inr ⟨hii, eight_ii S h1345 hstar hL2TM h2T hL2H₂ hInH0 hH0M hii hmax⟩

end Data13410

end CFSG.Quasithin.H13.NQS134
