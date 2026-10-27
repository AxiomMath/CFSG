module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15R

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.pCoreOf_g0_le_rOf (c : Core3Ctx T M H K1 L M₁) :
    pCoreOf 2 (g0Of T M H K1) ≤ rOf T M K1 :=
  le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_g0 c.inM c.sylow)).trans le_sup_right)
    ((yOfL22_sup_sOf_le_g0Of T M H K1).trans (le_normalizer_pCoreOf 2 _))
    (pCoreOf_isPGroup 2 _)

omit [Finite G] in
theorem yOfL22_sup_sOf_le_normalizer_rOf (T M K1 : Subgroup G) :
    yOfL22 T M ⊔ sOf T K1 ≤ Subgroup.normalizer (rOf T M K1 : Set G) :=
  le_normalizer_pCoreOf 2 _

theorem Core3Ctx.T_le_normalizer_rOf (c : Core3Ctx T M H K1 L M₁) :
    T ≤ Subgroup.normalizer (rOf T M K1 : Set G) :=
  F7.le_normalizer_pCoreOf_of_le_normalizer
    (F1.le_normalizer_sup (T_le_normalizer_y c.st.hyp) (T_le_normalizer_sOf c.st c.lt.ne))

theorem Core3Ctx.yOfL22_sup_T_le_normalizer_rOf (c : Core3Ctx T M H K1 L M₁) :
    yOfL22 T M ⊔ T ≤ Subgroup.normalizer (rOf T M K1 : Set G) :=
  sup_le (le_sup_left.trans (yOfL22_sup_sOf_le_normalizer_rOf T M K1)) c.T_le_normalizer_rOf

theorem isTwoRadicalIn_g0_rOf (c : Core3Ctx T M H K1 L M₁) :
    IsTwoRadicalIn (S1421.g0Of T M H K1) (rOf T M K1) := by
  have hRG : rOf T M K1 ≤ g0Of T M H K1 := (rOf_le_sOf c).trans le_sup_right
  have hXN := yOfL22_sup_sOf_le_normalizer_rOf T M K1
  refine ⟨hRG, ?_, le_antisymm ?_ ?_⟩
  · intro h
    exact c.pCore_ne (le_bot_iff.mp (h ▸ c.pCoreOf_g0_le_rOf))
  · exact le_pCoreOf_of_le_normalizer 2 (le_inf hRG Subgroup.le_normalizer) inf_le_right
      (pCoreOf_isPGroup 2 _)
  · set N : Subgroup G := g0Of T M H K1 ⊓ Subgroup.normalizer (rOf T M K1 : Set G) with hN
    have hSN : sOf T K1 ≤ N := le_inf le_sup_right (le_sup_right.trans hXN)
    have hQS : pCoreOf 2 N ≤ sOf T K1 :=
      pCoreOf_two_le_of_isSylowTwoOf
        (A4.isSylowTwoOf_mono (isSylowTwoOf_g0 c.inM c.sylow) hSN inf_le_left)
    exact le_pCoreOf_of_le_normalizer 2 (hQS.trans le_sup_right)
      ((le_inf (yOfL22_sup_sOf_le_g0Of T M H K1) hXN).trans (le_normalizer_pCoreOf 2 N))
      (pCoreOf_isPGroup 2 _)

theorem normalizer_le_of_char_rOf (c : Core3Ctx T M H K1 L M₁) {C : Subgroup G} (hC : C ≠ ⊥)
    (hCR : C ≤ rOf T M K1) (hchar : (C.subgroupOf (rOf T M K1)).Characteristic) :
    Subgroup.normalizer (C : Set G) ≤ M := by
  have hC2 : IsPGroup 2 C := (pCoreOf_isPGroup 2 (yOfL22 T M ⊔ sOf T K1)).to_le hCR
  have hYT : yOfL22 T M ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
    c.yOfL22_sup_T_le_normalizer_rOf.trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hCR hchar)
  have hO : pCoreOf 2 (Subgroup.normalizer (C : Set G)) ≠ ⊥ := by
    intro h
    have h1 := le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer : C ≤ Subgroup.normalizer (C : Set G)) le_rfl hC2
    rw [h] at h1
    exact hC (le_bot_iff.mp h1)
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have heq := c.st.facts.unique.2 M' ⟨hM'.1, hYT.trans hM'.2⟩
  rw [heq] at hM'
  exact hM'.2

theorem cgsIn_g0_rOf_le (c : Core3Ctx T M H K1 L M₁) :
    cgsIn (S1421.g0Of T M H K1) (rOf T M K1) ≤ M := by
  unfold cgsIn
  refine iSup_le fun C => iSup_le fun hCR => iSup_le fun hC => iSup_le fun hchar => ?_
  exact inf_le_right.trans (normalizer_le_of_char_rOf c hC hCR hchar)

theorem isSQTKIn_g0 (c : Core3Ctx T M H K1 L M₁) : IsSQTKIn (S1421.g0Of T M H K1) :=
  sqtkGroup_of_pCoreOf_ne_bot c.st.hyp.qtke c.st.hyp.simple c.st.hyp.nonabelian c.pCore_ne

end S1421

end CFSG.Quasithin
