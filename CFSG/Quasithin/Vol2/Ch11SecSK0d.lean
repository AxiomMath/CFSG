module

public import CFSG.Quasithin.Vol2.Ch11SecSK0c

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem perfectCore_sup_pCoreOf (h : StarHyp G T L I V₁ V₂ X K) {B : Subgroup G}
    (hB : ⁅B, B⁆ = B) (hTB : T ≤ Subgroup.normalizer (B : Set G)) :
    perfectCore (B ⊔ pCoreOf 2 K) = B :=
  perfectCore_sup_eq hB (isSolvable_pCoreOf_two K) (h.pCoreOf_le_normalizer hTB)

theorem eq_of_isLocal_le (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂)
    {J : Subgroup G} (hJ : quasithinIsLocal T J) (hJK : J ≤ K) :
    J = K ∨ J = LOf L V₁ ∨ J = k0Of K P₂ := by
  have hJc : J ∈ cComp (J ⊔ T) := hJ.2.1
  have hJp : ⁅J, J⁆ = J := perfect_of_mem_cComp hJc
  have hJne : J ≠ ⊥ := ne_bot_of_mem_cComp hJc
  have hNK : conjClosure J T ≤ K := conjClosure_le fun t ht z hz =>
    (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer_K ht) z).mp (hJK hz)
  have hNp : ⁅conjClosure J T, conjClosure J T⁆ = conjClosure J T := A3.conjClosure_perfect hJp
  have hJN : J ≤ conjClosure J T := le_conjClosure J T
  have hJsub : IsSubnormal J (conjClosure J T) :=
    A3.subnormal_of_le_of_le (subnormal_of_mem_cComp hJc) hJN (A3.conjClosure_le_sup J T)
  have hNne : conjClosure J T ≠ ⊥ := fun hb => hJne (eq_bot_iff.mpr (hb ▸ hJN))
  have hNbar := hP.cases _ (modO2Image_ne_bot hNK hNp hNne) (modO2Image_perfect hNK hNp)
    (modO2Image_le_normalizer (inf_le_left.trans (le_normalizer_conjClosure J T)))
  have hcN : quasithinIsCComponent (modO2Image K (conjClosure J T))
      (modO2Image K (conjClosure J T)) := by
    rcases hNbar with h1 | h1 | h1 <;> rw [h1]
    exacts [hP.c₁, hP.c₂, hP.cTop]
  have hJbar : modO2Image K J = modO2Image K (conjClosure J T) :=
    eq_of_subnormal_of_cSimple hcN (Subgroup.map_mono fun x hx => hJN hx)
      (modO2Image_ne_bot (hJN.trans hNK) hJp hJne) (modO2Image_perfect (hJN.trans hNK) hJp)
      (modO2Image_subnormal hJsub)
  have hJcore : perfectCore (J ⊔ pCoreOf 2 K) = J :=
    (cComp_commutator_perfectCore hJc (h.pCoreOf_le_T.trans le_sup_right)
      (isSolvable_pCoreOf_two K) (hJK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))).2
  have key : ∀ B : Subgroup G, B ≤ K → perfectCore (B ⊔ pCoreOf 2 K) = B →
      modO2Image K J = modO2Image K B → J = B := by
    intro B hBK hB heq
    rw [← hJcore, ← hB, sup_eq_of_modO2Image_eq hJK hBK heq]
  rw [hJbar] at key
  rcases hNbar with h1 | h1 | h1
  · exact Or.inr (Or.inl (key _ h.L₁_le_K (h.perfectCore_sup_pCoreOf h.perfect_L₁
      h.T_le_normalizer_L₁) (h1.trans hP.l₁.symm)))
  · exact Or.inr (Or.inr (key _ (k0Of_le K P₂) (h.perfectCore_sup_pCoreOf (k0Of_perfect K P₂)
      (h.T_le_normalizer_k0Of hP)) (h1.trans (modO2Image_k0Of K hP.c₂.2.1).symm)))
  · refine Or.inl (key _ le_rfl ?_ (h1.trans (modO2Image_self K).symm))
    rw [sup_eq_left.mpr (pCoreOf_le_self K), perfectCore_eq_self_of_perfect h.perfect]

theorem k0Of_ne_K (hP : ParData T K (LOf L V₁) P₁ P₂) : k0Of K P₂ ≠ K := by
  intro heq
  apply hP.ne_top₂
  rw [← modO2Image_k0Of K hP.c₂.2.1, heq, modO2Image_self]

theorem k0Of_ne_L₁ (hP : ParData T K (LOf L V₁) P₁ P₂) : k0Of K P₂ ≠ LOf L V₁ := by
  intro heq
  apply hP.ne
  rw [← hP.l₁, ← heq, modO2Image_k0Of K hP.c₂.2.1]

theorem le_sup_k0Of (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    K ≤ LOf L V₁ ⊔ k0Of K P₂ ⊔ pCoreOf 2 K := by
  refine le_sup_of_modO2Image_eq_top (sup_le h.L₁_le_K (k0Of_le K P₂)) ?_
  rw [modO2Image_sup h.L₁_le_K (k0Of_le K P₂), hP.l₁, modO2Image_k0Of K hP.c₂.2.1, hP.sup]

theorem k0Of_not_le (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    ¬ k0Of K P₂ ≤ Subgroup.normalizer (L : Set G) := by
  intro hK0
  apply h.not_le
  refine (h.le_sup_k0Of hP).trans (sup_le (sup_le ?_ hK0) (h.pCoreOf_le_T.trans h.hyp.normal))
  exact ((perfectCore_le _).trans inf_le_left).trans Subgroup.le_normalizer

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
