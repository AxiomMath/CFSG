module

public import CFSG.Quasithin.Background.GoldschmidtE23Glue
public import CFSG.Quasithin.Background.GoldschmidtE23Mod
public import CFSG.Quasithin.Background.GoldschmidtE23E22
public import CFSG.Quasithin.Background.GoldschmidtE23J

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B2F

namespace GE23

section One

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M V : Subgroup Γ} (hV : IsElemAbelian 2 V)

theorem e23_one (hP4 : AsB15Part4) (hComp : B69.AsB69Component)
    (h22 : E2.E22StatementNoN) (h : MinParabolic H T M) (hsq : SQTKGroup ↥H)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ))
    (hns : ¬ Group.IsSolvable ↥H) :
    twoResidual H ≤ thompsonJ H ∧
    ((B69.blkFamily (autI hV H)).card = 1 ∨ (B69.blkFamily (autI hV H)).card = 2) ∧
    autI hV (thompsonJ H) = ⨆ L ∈ B69.blkFamily (autI hV H), L ∧
    (∀ L ∈ B69.blkFamily (autI hV H), ∀ L' ∈ B69.blkFamily (autI hV H), L ≠ L' →
      ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
    (∀ L ∈ B69.blkFamily (autI hV H),
      L ⊓ ⨆ L' ∈ B69.blkFamily (autI hV H), ⨆ (_ : L' ≠ L), L' = ⊥) ∧
    (∀ L ∈ B69.blkFamily (autI hV H), ∀ L' ∈ B69.blkFamily (autI hV H),
      ∃ t ∈ autI hV T, B1.conjAut t L = L') ∧
    (∀ L ∈ B69.blkFamily (autI hV H),
      (∃ n : ℕ, E2.IsL2Natural L (fixV (autI hV (twoResidual H))) n) ∨ E2.IsA5Module L) := by
  have hHN : H ≤ Subgroup.normalizer (V : Set Γ) := hred.2.1
  have hHV : ¬ H ≤ Subgroup.centralizer (V : Set Γ) := fun hle =>
    hJ ((thompsonJ_le_self T).trans (h.isSylow.1.trans hle))
  have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set Γ) := fun hle =>
    hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf h.isSylow).trans hle)
  obtain ⟨hFF, hstab, hJeq, -⟩ := B2_7_of_not_le hV hred.1 hHN hJH
  have hB := blkCtx_star hV hP4 hComp h hsq hred hJ hns
  have hmp := minParabolic_star hV h hred hHV
  have hnsX := not_isSolvable_star hV h hred hHV hns
  have hsc := B69.structConcl_of_blkCtx hB hmp hFF
  have hX := isRankTwoQuotient_star hV hsq hHN
  have hKY := hmp.twoResidual_le_ffJ hB.hO2 hFF
  have hsqX := sqtk_star hV hsq hHN
  refine ⟨E2.twoResidual_le_thompsonJ h hred hJ, ?_, ?_, hsc.2.2.1, hsc.2.2.2.1, ?_, ?_⟩
  · have h2 := card_blocks_le_two hB hmp hFF hX
    have h1 : 0 < (B69.blkFamily (autI hV H)).card := by
      obtain ⟨A₀, hA₀⟩ := (B1_7 (fun v : IntMod V hV => IntMod.sq_eq_one v) hFF).1
      obtain ⟨L₀, hL₀, -⟩ := B69.exists_component_of_nonsolvable hB.hV hB.hP4 hmp hB.hO2 hnsX hA₀
      exact Finset.card_pos.2 ⟨B69.blk _ L₀, B69.mem_blkFamily.2 ⟨L₀, hL₀, rfl⟩⟩
    omega
  · rw [hJeq, ffJP_eq_ffJ hB hmp hnsX hstab]
    exact hsc.2.1
  · intro L hL L' hL'
    obtain ⟨t, ht, hconj⟩ := hsc.2.2.2.2.2.2.2.1 L hL L' hL'
    refine ⟨t, ht, ?_⟩
    rw [← hconj]
    exact Subgroup.ext fun x => by rw [B1.mem_conjAut, B6.mem_conjSub]
  · intro L hL
    rw [autI_twoResidual_eq hV hHN]
    rcases block_type hB hL with hN | ⟨k, hS⟩
    · exact Or.inl (hN.isL2Natural hB hKY)
    · right
      have hk := hS.k_eq_two h22 hmp hsqX hX
      subst hk
      exact hS.isA5Module hB

theorem e23_one_module (hP4 : AsB15Part4)
    (hComp : B69.AsB69Component) (h22 : E2.E22StatementNoN) (h : MinParabolic H T M)
    (hsq : SQTKGroup ↥H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ)) (hns : ¬ Group.IsSolvable ↥H) :
    fixV (autI hV (twoResidual H)) ⊔ ⨆ L ∈ B69.blkFamily (autI hV H), commV L = ⊤ ∧
    ∀ L ∈ B69.blkFamily (autI hV H), commV L ⊓
        (fixV (autI hV (twoResidual H)) ⊔
          ⨆ L' ∈ B69.blkFamily (autI hV H), ⨆ (_ : L' ≠ L), commV L') ≤
      fixV (autI hV (twoResidual H)) := by
  have hHN : H ≤ Subgroup.normalizer (V : Set Γ) := hred.2.1
  have hHV : ¬ H ≤ Subgroup.centralizer (V : Set Γ) := fun hle =>
    hJ ((thompsonJ_le_self T).trans (h.isSylow.1.trans hle))
  have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set Γ) := fun hle =>
    hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf h.isSylow).trans hle)
  obtain ⟨hFF, -⟩ := B2_7_of_not_le hV hred.1 hHN hJH
  have hB := blkCtx_star hV hP4 hComp h hsq hred hJ hns
  have hmp := minParabolic_star hV h hred hHV
  have hnsX := not_isSolvable_star hV h hred hHV hns
  have hsc := B69.structConcl_of_blkCtx hB hmp hFF
  have hX := isRankTwoQuotient_star hV hsq hHN
  have hsqX := sqtk_star hV hsq hHN
  have hKY := hmp.twoResidual_le_ffJ hB.hO2 hFF
  have hk2 : ∀ {H' : Subgroup (MulAut (IntMod V hV))} {k : ℕ},
      SymBlk (autI hV H) H' k → k = 2 := fun {H'} {k} hS => hS.k_eq_two h22 hmp hsqX hX
  rw [autI_twoResidual_eq hV hHN]
  refine ⟨?_, fun L hL => inf_le_fixV_twoResidual hB hmp hFF hnsX hL⟩
  rw [eq_top_iff]
  intro v _
  obtain ⟨w, hw, c, hc, rfl⟩ :=
    blocks_split hB hmp hFF hk2 (B69.blkFamily (autI hV H)) (fun _ h => h) v
  have hc' : c ∈ fixV (twoResidual (autI hV H)) := by
    rw [← hsc.2.1] at hc
    exact B1.fixV_le_fixV hKY hc
  rw [mul_comm]
  exact Subgroup.mul_mem_sup hc' hw

end One

end GE23

end CFSG.Quasithin
