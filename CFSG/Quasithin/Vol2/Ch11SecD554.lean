module

public import CFSG.Quasithin.Vol2.Ch11SecDK
public import CFSG.Quasithin.Vol2.Ch11StatementsD
public import CFSG.Quasithin.Vol2.Ch11StatementsH

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem not_normalizer_V₁_le (h1003 : Stmt11_0_3) (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2)
    (h1153 : Stmt11_5_3) (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    ¬ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro hle
  by_cases hK : KOf L V₁ V₁ = LOf L V₁
  · apply (h1153 G T L I n V₁ h hV₁ hK).2.2.2
    obtain ⟨⟨hVMM, ⟨_, helem, _⟩⟩, -⟩ := h1003 G T L I n h
    have hc : IsMulCommutative ↥((VM T L I).subgroupOf (Subgroup.normalizer (L : Set G))) :=
      helem.toIsMulCommutative
    have hsub : conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤ VM T L I :=
      conjClosure_mono le_rfl hle
    exact ⟨⟨fun a b => Subtype.ext
      (commute_of_le_of_isMulCommutative hVMM hc (hsub a.2) (hsub b.2))⟩⟩
  · exact hK (kOf_eq_lOf_of_le (kOf_cComp h1110 h1112 h hV₁) (lOf_ne_bot h1110 h hV₁)
      ((kOf_le_normalizer (lOf_le_normalizer L V₁)).trans hle))

theorem stmt11_5_4_of (hTI : PointsTIFact) (h1003 : Stmt11_0_3) (h1102 : Stmt11_0_2)
    (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2) (h1123 : Stmt11_2_3) (h1141 : Stmt11_4_1)
    (h1143 : Stmt11_4_3) (h1153 : Stmt11_5_3) : Stmt11_5_4 := by
  intro G _ _ T L I n V₁ h hV₁
  have hG₁ := not_normalizer_V₁_le h1003 h1110 h1112 h1153 h hV₁
  refine ⟨fun hC => hG₁ ((h1123 G T L I n V₁ h hV₁).2 hC), ?_⟩
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  have hV₁T : V₁ ≤ T := hV₁V.trans (SecA.fsuV_le_T h)
  have hT2 : IsPGroup 2 T := h.fsu.sylow.1
  have hTG₁ : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  have hV₁2 : IsPGroup 2 V₁ := hT2.to_le hV₁T
  have hV₁1 : V₁ ≠ ⊥ := SecA.IsVi.ne_bot h hV₁ le_rfl
  have hKG₁ : KOf L V₁ V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    kOf_le_normalizer (lOf_le_normalizer L V₁)
  have hTK : T ≤ Subgroup.normalizer (KOf L V₁ V₁ : Set G) :=
    hTG₁.trans (normalizer_le_normalizer_kOf L V₁ V₁)
  obtain ⟨z, hzV₁, hz1, hzT⟩ := exists_z h hV₁
  have hdec := (h1143 G T L I n V₁ h hV₁ z ⟨hV₁V hzV₁, hzT⟩ hz1).2.2
  set Y := Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.centralizer (V₁ : Set G) ⊓
    sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) with hY
  have hcase : ¬ KOf L V₁ V₁ ≤ Subgroup.normalizer (L : Set G) ∨
      ¬ Y ≤ Subgroup.normalizer (L : Set G) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hKM, hYM⟩ := hcon
    refine hG₁ fun g hg => ?_
    have hg' : g ∈ ((Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) := hg
    rw [hdec] at hg'
    obtain ⟨_, ⟨k, hk, y, hy, rfl⟩, m, hm, rfl⟩ := hg'
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hKM hk) (hYM hy)) hm.1
  rcases hcase with hKM | hYM
  ·
    have hP : InH T (KOf L V₁ V₁ ⊔ T) :=
      inH_of_le le_sup_right (hV₁T.trans le_sup_right) hV₁2 hV₁1 (sup_le hKG₁ hTG₁)
    obtain ⟨H, hH, hHP⟩ := exists_isHStar_le _ _ rfl hP fun h' => hKM (le_sup_left.trans h')
    have hO2 : oTwoUpper H ≤ KOf L V₁ V₁ := oTwoUpper_le_of_le_sup' hHP hT2 hTK
    exact ⟨H, hH, hHP.trans (sup_le hKG₁ hTG₁),
      hO2.trans (kOf_le_centralizer hTI h1102 h1141 h1143 h hV₁), Or.inr hO2⟩
  ·
    have hYG₁ : Y ≤ Subgroup.normalizer (V₁ : Set G) := inf_le_left.trans inf_le_left
    have hCn : Subgroup.normalizer (V₁ : Set G) ≤
        Subgroup.normalizer (Subgroup.centralizer (V₁ : Set G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        inferInstance
    have hTY : T ≤ Subgroup.normalizer (Y : Set G) := fun t ht =>
      mem_normalizer_inf (mem_normalizer_inf (Subgroup.le_normalizer (hTG₁ ht)) (hCn (hTG₁ ht)))
        (mem_normalizer_sectionCentralizer (hTK ht)
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hTK ht)))
    have hP : InH T (Y ⊔ T) :=
      inH_of_le le_sup_right (hV₁T.trans le_sup_right) hV₁2 hV₁1 (sup_le hYG₁ hTG₁)
    obtain ⟨H, hH, hHP⟩ := exists_isHStar_le _ _ rfl hP fun h' => hYM (le_sup_left.trans h')
    have hO2 : oTwoUpper H ≤ Y := oTwoUpper_le_of_le_sup' hHP hT2 hTY
    refine ⟨H, hH, hHP.trans (sup_le hYG₁ hTG₁), hO2.trans (inf_le_left.trans inf_le_right),
      Or.inl ?_⟩
    rw [Subgroup.commutator_le]
    intro k hk y hy
    have hy' := ((hO2 hy).2).2.2 k hk
    have heq : ⁅k, y⁆ = (y * k * y⁻¹ * k⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact Subgroup.inv_mem _ hy'

end CFSG.Quasithin.Vol2.Ch11.SecD
