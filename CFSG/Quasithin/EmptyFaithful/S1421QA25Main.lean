module

public import CFSG.Quasithin.EmptyFaithful.S1421QA25Rows
public import CFSG.Quasithin.EmptyFaithful.S1421QA25Diag
public import CFSG.Quasithin.EmptyFaithful.S1421QA25Act
public import CFSG.Quasithin.EmptyFaithful.S1421Q9C
public import CFSG.Quasithin.Vol2.Ch1EightFourMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.Quasithin.Background.F9Comp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace QA25

theorem le_normalizer_of_unique {X : Type} [Group X] [Finite X] {Tb K' L₀ B : Subgroup X}
    (hK' : K' ∈ cComp (⊤ : Subgroup X)) (hB : B ≤ K')
    (huniq : ∀ L' ∈ cComp (⊤ : Subgroup X), B ≤ L' → L' = L₀)
    (hTB : Tb ≤ Subgroup.normalizer (B : Set X)) : Tb ≤ Subgroup.normalizer (K' : Set X) := by
  intro t ht
  have hc : conjSub t K' ∈ cComp (⊤ : Subgroup X) :=
    conjSub_mem_cComp_of_mem hK' (Subgroup.mem_top t)
  have hBc : B ≤ conjSub t K' := by
    intro y hy
    rw [mem_conjSub]
    have h1 : t⁻¹ * y * t ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (hTB (Tb.inv_mem ht)) y).mp hy
      simpa using this
    exact hB h1
  have h1 : conjSub t K' = L₀ := huniq _ hc hBc
  have h2 : K' = L₀ := huniq _ hK' hB
  have hmem : ∀ y : X, y ∈ K' ↔ t⁻¹ * y * t ∈ K' := by
    intro y
    have := h1.trans h2.symm
    rw [← mem_conjSub, this]
  refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
  have := hmem (t * h * t⁻¹)
  simpa [mul_assoc] using this.symm

end QA25

namespace Q9

theorem l34Maximal_of_diagram
    (h312 : A312ForSQTK) (hM : QA25.M23L34Diagram) : L34Maximal := by
  intro G _ _ hQ hs hnab T K hT hK hTK h34 hdiag
  refine ⟨hK, fun K' hK' hKK' => ?_⟩
  have hSyl : IsSylowTwoOf T (K' ⊔ T) := ⟨le_sup_right, hK'.1, hK'.2.2.1⟩
  have hKH : K ≤ K' ⊔ T := hKK'.trans le_sup_left
  have hTH : T ≤ K' ⊔ T := le_sup_right
  have hB : K ∈ lFamily T := mem_lFamily_of_isLocal hK
  have hK'c : K' ∈ cComp (K' ⊔ T) := cComp_of_isLocal hK'
  have hlist := lemma_1_2_4_list hQ hs hnab h312 hK'.2.2.2 hSyl hKH hB hK'c hKK'
  rcases hlist with heq | hcase | hnq
  · exact (Ch1Four.eq_of_modO2Image_eq hK hK' hKK' heq).symm
  all_goals exfalso
  all_goals
    obtain ⟨e⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hKH
    have h34B : IsPSL 3 2 2 (ModO2 (modO2Image (K' ⊔ T) K)) :=
      CFSG.SectionRank.statedClassicalModel_of_mulEquiv e.symm h34
    have hBL : modO2Image (K' ⊔ T) K ≤ modO2Image (K' ⊔ T) K' :=
      Subgroup.map_mono fun x hx => hKK' hx
  swap
  · exact QA25.nonquasi_l34 h34B hBL hnq
  obtain ⟨hA, hM23⟩ := QA25.rows_l34 h34B hcase
  have hSQTK : SQTKHyp (↥(K' ⊔ T) ⧸ CFSG.pCore 2 ↥(K' ⊔ T)) :=
    sqtkHyp_quotient_of_pCoreOf_ne_bot hQ hs hnab hK'.2.2.2
  have hTbSyl : IsSylowTwoOf (modO2Image (K' ⊔ T) T) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSyl)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(K' ⊔ T))) (QuotientGroup.mk'_surjective _)
  obtain ⟨L₀, -, -, huniq, -⟩ :=
    h312 _ hSQTK _ hTbSyl _ (modO2Image_mem_lFamily hSyl hKH hB)
  have hK'bar : modO2Image (K' ⊔ T) K' ∈
      cComp (⊤ : Subgroup (↥(K' ⊔ T) ⧸ CFSG.pCore 2 ↥(K' ⊔ T))) := modO2Image_mem_cComp hK'c
  have hTK' : modO2Image (K' ⊔ T) T ≤ Subgroup.normalizer
      ((modO2Image (K' ⊔ T) K' : Subgroup (↥(K' ⊔ T) ⧸ CFSG.pCore 2 ↥(K' ⊔ T))) :
        Set (↥(K' ⊔ T) ⧸ CFSG.pCore 2 ↥(K' ⊔ T))) :=
    QA25.le_normalizer_of_unique hK'bar hBL huniq (QA25.modO2Image_le_normalizer hTK)
  have hSylM : IsSylowTwoOf (modO2Image (K' ⊔ T) T ⊓ modO2Image (K' ⊔ T) K')
      (modO2Image (K' ⊔ T) K') :=
    L246C127.isSylowTwoOf_inf_of_isSubnormal' (subnormal_of_mem_cComp hK'bar) hTbSyl
  obtain ⟨P, hPA, hPne, hPmax, hBor, hPT⟩ := QA25.exists_stable_of_m23 hM hTbSyl.2.1 hSylM hM23 hA
    hBL hTK' (QA25.modO2Image_le_normalizer hTK)
  have hSTK : IsSylowTwoOf (T ⊓ K) K :=
    L246C127.isSylowTwoOf_inf_of_isSubnormal' (subnormal_of_mem_cComp (cComp_of_isLocal hK))
      ⟨le_sup_right, hK.1, hK.2.2.1⟩
  refine QA25.not_isDiagramNontrivial_of_bar hKH hTH hTK hSTK hPA hPne hPmax ?_ hPT hdiag
  rw [QA25.modO2Image_inf (pCoreOf_two_le_of_isSylowTwoOf hSyl)]
  exact hBor

end Q9

end CFSG.Quasithin
