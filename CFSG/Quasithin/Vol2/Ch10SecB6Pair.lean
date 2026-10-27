module

public import CFSG.Quasithin.Vol2.Ch10SecB6Facts
public import CFSG.Quasithin.Vol2.Ch10SecB6Bar
public import CFSG.Quasithin.Vol2.Ch10SecB6Two

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem li_data (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) {X : Subgroup G}
    (hX : X = L ∨ X = CFSG.conjugate L t) :
    X ∈ cComp (fsuM T L) ∧ T1 T L ≤ Subgroup.normalizer (X : Set G) ∧ X ≤ fsuL0 T L ∧
      Nonempty (ModO2 X ≃* ModO2 L) := by
  have hloc := hyp.fsu.maximal.1
  rcases hX with rfl | rfl
  · exact ⟨SecA.mem_cComp_fsuM hloc, inf_le_right, SecA.le_fsuL0 T X,
      ⟨MulEquiv.refl _⟩⟩
  · exact ⟨SecA.conjugate_mem_cComp_fsuM hloc (le_fsuM T L ht),
      T1_le_normalizer_conjugate h37 h38 hyp ht, SecA.conjugate_le_fsuL0 ht,
      nonempty_modO2_conjugate L t⟩

theorem false_of_le_cComp (hF1 : Fact10_2_6Pair) (hK : LocalSQTK G)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {H : Subgroup G}
    (hH : InM (fsuL0 T L ⊔ T1 T L) H) (hS : IsSylowTwoOf (T1 T L) H) {K : Subgroup G}
    (hKc : K ∈ cComp H) (hLK : L ≤ K) (hLtK : CFSG.conjugate L t ≤ K) : False := by
  have hH2 : pCoreOf 2 H ≠ ⊥ := (inH_of_inM hH).2
  have hL0H : fsuL0 T L ≤ H := le_sup_left.trans hH.2
  have hT1M : T1 T L ≤ fsuM T L := inf_le_left.trans (le_fsuM T L)
  obtain ⟨hc₁, hn₁, hle₁, -⟩ := li_data h37 h38 hyp ht (X := L) (Or.inl rfl)
  obtain ⟨hc₂, hn₂, hle₂, ⟨e₂⟩⟩ := li_data h37 h38 hyp ht (X := CFSG.conjugate L t) (Or.inr rfl)
  have hfam₁ := cComp_subset_lFamily hT1M hc₁
  have hfam₂ := cComp_subset_lFamily hT1M hc₂
  obtain ⟨f₁⟩ := nonempty_modO2_modO2Image (hle₁.trans hL0H)
  obtain ⟨f₂⟩ := nonempty_modO2_modO2Image (hle₂.trans hL0H)
  have hcomm : ⁅modO2Image H L, modO2Image H (CFSG.conjugate L t)⁆ ≤
      pCoreOf 2 (modO2Image H L) ⊓ pCoreOf 2 (modO2Image H (CFSG.conjugate L t)) := by
    refine (commutator_modO2Image_le (SecA.commutator_conjugate_le h37 hyp ht htn)).trans ?_
    exact le_inf ((modO2Image_mono' inf_le_left).trans modO2Image_pCoreOf_le)
      ((modO2Image_mono' inf_le_right).trans modO2Image_pCoreOf_le)
  exact hF1 _ (Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH2) (modO2Image H (T1 T L))
    (modO2Image H K) (modO2Image H L) (modO2Image H (CFSG.conjugate L t))
    (isSylowTwoOf_modO2Image hS) (modO2Image_mem_cComp hKc)
    (modO2Image_mem_lFamily hS (hle₁.trans hL0H) hfam₁)
    (modO2Image_mem_lFamily hS (hle₂.trans hL0H) hfam₂)
    (modO2Image_le_normalizer' hn₁) (modO2Image_le_normalizer' hn₂)
    (modO2Image_mono' hLK) (modO2Image_mono' hLtK) hcomm ⟨(f₁.trans e₂.symm).trans f₂.symm⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
