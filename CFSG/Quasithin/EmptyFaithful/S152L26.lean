module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts2
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem autI_top_eq {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hN : Subgroup.normalizer (V : Set G) ≤ M) : autI hV (⊤ : Subgroup G) = autI hV M := by
  unfold autI
  congr 1
  rw [Subgroup.top_subgroupOf]
  exact (Subgroup.subgroupOf_eq_top.mpr hN).symm

section Finite

variable [Finite G]

theorem normalizer_V154_eq {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) :
    Subgroup.normalizer (V154 T Mc M : Set G) = M := by
  have hVe : IsElemAbelian 2 (V154 T Mc M) :=
    isElemAbelian_mono151 (V154_le_VZ T Mc M) (isElemAbelian_VZ h hM.1.1)
  have hVp : IsPGroup 2 (V154 T Mc M) := fun x => ⟨1, Subtype.ext (by simpa using hVe.2 x x.2)⟩
  have hloc : IsTwoLocal (Subgroup.normalizer (V154 T Mc M : Set G)) :=
    ⟨V154 T Mc M, V154_ne_bot h, hVp, rfl⟩
  exact hM.1.1.1.2 _ hloc (le_normalizer_V154 T Mc M)

theorem wClos_zero_le_centralizer {T H V : Subgroup G} (hQT : pCoreOf 2 H ≤ T)
    (hV2 : IsPGroup 2 V) (hW : E3.wClos V 0 T ≤ T ⊓ Subgroup.centralizer (V : Set G)) :
    E3.wClos V 0 (pCoreOf 2 H) ≤ H ⊓ Subgroup.centralizer (conjClosure V H : Set G) := by
  refine E3.wClos_le_of_forall fun A hA => ?_
  obtain ⟨hAQ, g, hAg, hm⟩ := E3.mem_gammaSet_iff.mp hA
  have hAeq : A = conjSubgroup V g :=
    (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV2 g) hAg).mp hm
  refine le_inf (hAQ.trans (pCoreOf_le 2 H)) ?_
  rw [Subgroup.le_centralizer_iff]
  refine conjClosure_le fun h hh v hv => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  set A' := conjSubgroup V (g * h) with hA'
  have hmemA : g * a * g⁻¹ ∈ V := mem_conjSubgroup_iff.mp (hAeq ▸ ha)
  have hmemA' : h⁻¹ * a * h ∈ A' := by
    rw [hA', mem_conjSubgroup_iff]
    have e : g * h * (h⁻¹ * a * h) * (g * h)⁻¹ = g * a * g⁻¹ := by group
    rw [e]
    exact hmemA
  have hA'Q : A' ≤ pCoreOf 2 H := by
    intro y hy
    have hy' : g * h * y * (g * h)⁻¹ ∈ V := mem_conjSubgroup_iff.mp hy
    have hy'' : h * y * h⁻¹ ∈ A := by
      rw [hAeq, mem_conjSubgroup_iff]
      have e : g * (h * y * h⁻¹) * g⁻¹ = g * h * y * (g * h)⁻¹ := by group
      rw [e]
      exact hy'
    have hyQ : h * y * h⁻¹ ∈ pCoreOf 2 H := hAQ hy''
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hh)) _).mp hyQ
    simpa [mul_assoc] using this
  have hA'W : A' ≤ E3.wClos V 0 T := by
    refine E3.le_wClos (E3.mem_gammaSet_iff.mpr ⟨hA'Q.trans hQT, g * h, le_rfl, ?_⟩)
    exact E3.mQuot_self _
  have hc := (hW (hA'W hmemA')).2
  have hcomm := Subgroup.mem_centralizer_iff.mp hc v hv
  have e1 : a * (h * v * h⁻¹) = h * ((h⁻¹ * a * h) * v) * h⁻¹ := by group
  have e2 : (h * v * h⁻¹) * a = h * (v * (h⁻¹ * a * h)) * h⁻¹ := by group
  rw [e1, e2, hcomm]

variable {T Mc M : Subgroup G}

theorem lemma_15_2_26_two (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hV : IsElemAbelian 2 (V154 T Mc M)) (hs : 1 < E3.sParam hV)
    (ha : E3.aParam (autI hV M) = 1) :
    E3.wClos (V154 T Mc M) 0 T ≤ T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) := by
  have hN := normalizer_V154_eq h hM
  have hTM : T ≤ M := hM.1.1.2
  have hVN : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    hTM.trans (le_normalizer_V154 T Mc M)
  have ha' : E3.aParam (autI hV (⊤ : Subgroup G)) = 1 := by
    rw [autI_top_eq hV hN.le]
    exact ha
  exact E3.e3_21_le hV hVN (i := 0) (by omega)

theorem stageLemma15226_of (h13 : StageLemma15213) (h14 : StageLemma15214)
    (h1 : StageLemma15226One) : StageLemma15226 := by
  intro G _ _ T Mc M hs
  obtain ⟨hV, hr, hsP⟩ := h1 G T Mc M hs
  obtain ⟨H₀, hH₀⟩ := exists_isHStar hs.qtfe.inM_mc hs.mf.1.1 hs.mf.2.1.symm
  obtain ⟨B₀, hB₀, -, -⟩ := (h13 G T Mc M hs H₀ hH₀).exists_B0
  obtain ⟨hV', -, ha⟩ := (h14 G T Mc M hs B₀ hB₀).params
  have hw : E3.wClos (V154 T Mc M) 0 T ≤ T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    lemma_15_2_26_two hs.qtfe hs.mf hV hsP ha
  refine ⟨⟨⟨hV, hr, hsP⟩, hw⟩, fun H hH => ?_⟩
  obtain ⟨S, hS⟩ := hs.qtfe.exists_sylow
  have hQT : pCoreOf 2 H ≤ T := by
    have := pCoreOf_two_le_sylow H S (hS ▸ hH.1.1)
    rwa [hS] at this
  have hVe : IsElemAbelian 2 (V154 T Mc M) := hV
  have hVp : IsPGroup 2 (V154 T Mc M) := fun x => ⟨1, Subtype.ext (by simpa using hVe.2 x x.2)⟩
  exact wClos_zero_le_centralizer hQT hVp hw

end Finite

end CFSG.Quasithin
