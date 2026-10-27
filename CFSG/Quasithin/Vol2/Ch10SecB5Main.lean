module

public import CFSG.Quasithin.Vol2.Ch10SecE9He5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem normalizer_T1_le_XOf
    (h134 : EmptyFaithfulMultiple.Prop134E9He) (hRed : HeReduce) (hF : H13.FactAutHeSylow)
    (hFa : FactL33M11) (hFc : FactL4L5) (h311 : Theorem311Stmt) (hgap : Gap10_2_5L2p)
    (hobl : Obl10_2_5Even) (h : MaxCtx T L I t Ψ c) (h3 : Case10_1_1Three T L I)
    (hD : ParData A K E)
    (hA : A = L32.Pa ∨ A = L32.Pb) :
    Subgroup.normalizer (T1 T L : Set G) ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) := by
  have hP : IsMaxSubgroupIn (fsuL0 T L ⊔ T) (preIn Ψ (A.prod A) ⊔ T) :=
    isMax_preIn_sup h.h37 h.h38 h.hyp h.ht h.htn h.hC hA
  have hTP : T ≤ preIn Ψ (A.prod A) ⊔ T := le_sup_right
  have hH : InH (XOf T L Ψ A ⊔ T)
      (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) :=
    ⟨(sup_le (oTwoUpper_le _) le_sup_right).trans le_sup_right, pCoreOf_GA_ne_bot h311 h hD hA⟩
  rcases kof_cases h134 hFa hFc h hD hH with hK |
      ⟨K₁, s, hs, hK₁, hsn, hK, htype⟩ | ⟨hK, k, hk45, hk, haut⟩ | ⟨K₁, hK₁, hHK, hXK, he⟩
  · intro g hg
    have h1 := le_normalizer_conjClosure (XOf T L Ψ A)
      (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T))
      (Subgroup.mem_sup_left hg)
    rwa [hK] at h1
  · rcases htype with heven | hp
    · exact hobl G T L I h.hyp h3 _ hP hTP (Or.inl ⟨K₁, s, hs, hK₁, hsn, hK, heven⟩)
    · exact hgap G T L I h.hyp h3 _ hP hTP K₁ s hs hK₁ hsn hK hp
  · exact hobl G T L I h.hyp h3 _ hP hTP (Or.inr ⟨hK, k, hk45, hk, haut⟩)
  · exact normalizer_T1_le_XOf_of_he hRed hF h h3 hD hA hH hK₁ hHK hXK he

theorem normalizer_T1_le_of_case3 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h134 : EmptyFaithfulMultiple.Prop134E9He)
    (hRed : HeReduce) (hF : H13.FactAutHeSylow) (hFa : FactL33M11) (hFc : FactL4L5)
    (h311 : Theorem311Stmt)
    (hgap : Gap10_2_5L2p) (hobl : Obl10_2_5Even) (hyp : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) :
    Subgroup.normalizer (T1 T L : Set G) ≤ fsuM T L := by
  have hinner : T1Inner T L := fun s hs => by
    obtain ⟨x₀, hx₀, hx, -⟩ := inner_of_case3 hyp h3 hs
    exact ⟨x₀, hx₀, hx⟩
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨Ψ, c, hC⟩ := exists_L0Coord h37 h38 hyp h3.1 hinner ht htn
  have h : MaxCtx T L I t Ψ c := ⟨h37, h38, hyp, ht, htn, hC⟩
  have ha := normalizer_T1_le_XOf h134 hRed hF hFa hFc h311 hgap hobl h h3 parData_a (Or.inl rfl)
  have hb := normalizer_T1_le_XOf h134 hRed hF hFa hFc h311 hgap hobl h h3 parData_b (Or.inr rfl)
  intro g hg
  have h1 := ha hg
  have h2 := hb hg
  show g ∈ Subgroup.normalizer (fsuL0 T L : Set G)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
  rw [← XOf_sup_eq h, Subgroup.map_sup, h1, h2]

theorem stmt10_2_5_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h3210 : TmpL6_3_2_10_eight) (h1012 : Stmt10_1_2) (h1021 : Stmt10_2_1)
    (h311 : Theorem311Stmt) (h134 : EmptyFaithfulMultiple.Prop134E9He) (hRed : HeReduce)
    (hF : H13.FactAutHeSylow)
    (hFa : FactL33M11) (hFc : FactL4L5) (hgap : Gap10_2_5L2p) (hobl : Obl10_2_5Even) :
    Stmt10_2_5 := by
  intro G _ _ T L I hyp
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)
  · exact normalizer_T1_le_of_thompsonJ h3210 h1012 hyp hJ
  · rcases cases123_of_not_thompsonJ h1012 hyp hJ with h1 | h2 | h3
    · exact normalizer_T1_le_of_case12 h1012 h1021 hyp (Or.inl h1) hJ
    · exact normalizer_T1_le_of_case12 h1012 h1021 hyp (Or.inr h2) hJ
    · exact normalizer_T1_le_of_case3 h37 h38 h134 hRed hF hFa hFc h311 hgap hobl hyp h3

end CFSG.Quasithin.Vol2.Ch10.SecB
