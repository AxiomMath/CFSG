module

public import CFSG.OddTranspositions.PartFour.LineVmem

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem not_mem_blockLine_of_not_mem_perp {α' γ η η' : Set G}
    (hη' : η' ∈ perp D α' ∩ perp D γ) (hηη' : η ∉ perp D η') : η ∉ blockLine D α' γ := by
  intro hη
  exact hηη' (hη.2 η' hη')

variable [Finite G]

theorem exists_mem_Dalpha_not_mem_blockLine_of_conj (hC : HypothesisC D) {α' γ η : Set G}
    (hα' : α' ∈ blockClass hC.alpha) (hγ : γ ∈ blockClass hC.alpha)
    (hη : η ∈ blockClass hC.alpha) (hγα' : γ ∉ perp D α') (hηα' : η ∈ perp D α')
    (hηγ : η ∈ perp D γ) (hηℓ : η ∉ blockLine D α' γ) :
    ∃ α'' ∈ Dalpha D hC.alpha, ∃ γ'' ∈ Dalpha D hC.alpha,
      γ'' ∉ perp D α'' ∧ hC.alpha ∉ blockLine D α'' γ'' := by
  obtain ⟨g, hηg₀⟩ := mem_blockClass_iff.mp hη
  have hηg : η = cimg g hC.alpha := hηg₀
  have hDα' : α' ⊆ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hα'
  have hDγ : γ ⊆ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγ
  have hα'perpη : α' ∈ perp D η := mem_perp_symm hηα' hDα'
  have hα'ne : α' ≠ η := fun h => hγα' (mem_perp_symm (h.symm ▸ hηγ) hDγ)
  have hα'Dη : α' ∈ Dalpha D η := by
    rcases mem_perp_iff.mp hα'perpη with h | h
    · exact h
    · exact absurd h hα'ne
  have hγperpη : γ ∈ perp D η := mem_perp_symm hηγ hDγ
  have hγne : γ ≠ η := fun h => hγα' (h.symm ▸ hηα')
  have hγDη : γ ∈ Dalpha D η := by
    rcases mem_perp_iff.mp hγperpη with h | h
    · exact h
    · exact absurd h hγne
  have hDconj : (fun γ => cimg g⁻¹ γ) '' Dalpha D η = Dalpha D (cimg g⁻¹ η) :=
    Dalpha_conj_image hC.setup.normal g⁻¹
  have hgη : cimg g⁻¹ η = hC.alpha := by rw [hηg, cimg_inv_cimg]
  have hα'' : cimg g⁻¹ α' ∈ Dalpha D hC.alpha := by
    have hm : cimg g⁻¹ α' ∈ (fun γ => cimg g⁻¹ γ) '' Dalpha D η := ⟨α', hα'Dη, rfl⟩
    rwa [hDconj, hgη] at hm
  have hγ'' : cimg g⁻¹ γ ∈ Dalpha D hC.alpha := by
    have hm : cimg g⁻¹ γ ∈ (fun γ => cimg g⁻¹ γ) '' Dalpha D η := ⟨γ, hγDη, rfl⟩
    rwa [hDconj, hgη] at hm
  have hγ''notperp : cimg g⁻¹ γ ∉ perp D (cimg g⁻¹ α') := by
    intro hm
    exact hγα' ((perp_cimg_mem hC.setup.normal g⁻¹ (α := α') (γ := γ)).mp hm)
  have hαnotline : hC.alpha ∉ blockLine D (cimg g⁻¹ α') (cimg g⁻¹ γ) := by
    intro hm
    apply hηℓ
    have hm' : cimg g hC.alpha ∈ cimg g '' blockLine D (cimg g⁻¹ α') (cimg g⁻¹ γ) :=
      ⟨hC.alpha, hm, rfl⟩
    rw [← blockLine_cimg hC.setup.normal g (cimg g⁻¹ α') (cimg g⁻¹ γ)] at hm'
    rw [cimg_cimg_inv g α', cimg_cimg_inv g γ] at hm'
    rwa [hηg]
  exact ⟨cimg g⁻¹ α', hα'', cimg g⁻¹ γ, hγ'', hγ''notperp, hαnotline⟩

private theorem rootWitness_exists_point (hC : HypothesisC D) {x : Halpha D hC.alpha}
    (hx : x ∈ DstarH hC) : ∃ ξ ∈ Dalpha D hC.alpha, (x : G) ∈ ξ :=
  mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hx)

theorem mem_perp_of_commute_mk (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {δ ε : Set G} (hδ : δ ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha)
    {d e : Halpha D hC.alpha} (hd : (d : G) ∈ δ) (he : (e : G) ∈ ε)
    (hcomm : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) e)) :
    ε ∈ perp D δ := by
  have hdStar : d ∈ DstarH hC := ⟨δ, hδ, hd⟩
  have heStar : e ∈ DstarH hC := ⟨ε, hε, he⟩
  have hcommH : Commute d e := commute_of_commute_mk h113 hC hrad hn3 hdStar heStar hcomm
  exact mem_perp_of_commute hC hδ.1 hε.1 hd he (hcommH.map (Subgroup.subtype _))

theorem not_mem_perp_of_not_commute_mk (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha))
    {δ ε : Set G} (hδ : δ ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha)
    {d e : Halpha D hC.alpha} (hd : (d : G) ∈ δ) (he : (e : G) ∈ ε)
    (hne : ¬ Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) e)) :
    ε ∉ perp D δ := by
  intro hperp
  apply hne
  have hcomm : Commute d e := by
    rcases mem_perp_iff.mp hperp with hεD | hεeq
    · exact Subtype.ext ((mem_Dalpha_iff.mp hεD).2.2.2 d hd e he).eq
    · rw [hεeq] at he
      exact Subtype.ext (commute_of_mem_Dalpha h89 h113 hC hrad hW hn3 hMZ hδ hd he).eq
  exact hcomm.map (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))

theorem exists_four_points_of_four (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hfour : ∃ t ∈ imageClass hC, ∃ u ∈ imageClass hC, ∃ v ∈ imageClass hC,
      ∃ w ∈ imageClass hC, ¬ Commute t u ∧ ¬ Commute v w ∧
        Commute v t ∧ Commute v u ∧ Commute w t ∧ Commute w u) :
    ∃ α' ∈ Dalpha D hC.alpha, ∃ γ ∈ Dalpha D hC.alpha, ∃ η ∈ Dalpha D hC.alpha,
      ∃ η' ∈ Dalpha D hC.alpha, γ ∉ perp D α' ∧ η ∈ perp D α' ∩ perp D γ ∧
        η' ∈ perp D α' ∩ perp D γ ∧ η ∉ perp D η' := by
  obtain ⟨_, ⟨t₀, ht₀, rfl⟩, _, ⟨u₀, hu₀, rfl⟩, _, ⟨v₀, hv₀, rfl⟩, _, ⟨w₀, hw₀, rfl⟩,
    htu, hvw, hvt, hvu, hwt, hwu⟩ := hfour
  obtain ⟨α', hα', ht₀α'⟩ := rootWitness_exists_point hC ht₀
  obtain ⟨γ, hγ, hu₀γ⟩ := rootWitness_exists_point hC hu₀
  obtain ⟨η, hη, hv₀η⟩ := rootWitness_exists_point hC hv₀
  obtain ⟨η', hη', hw₀η'⟩ := rootWitness_exists_point hC hw₀
  have hγα' : γ ∉ perp D α' :=
    not_mem_perp_of_not_commute_mk h89 h113 hC hrad hW hn3 hMZ hα' hγ
      ht₀α' hu₀γ htu
  refine ⟨α', hα', γ, hγ, η, hη, η', hη', hγα', ?_, ?_, ?_⟩
  · exact ⟨mem_perp_of_commute_mk h113 hC hrad hn3 hα' hη ht₀α' hv₀η hvt.symm,
      mem_perp_of_commute_mk h113 hC hrad hn3 hγ hη hu₀γ hv₀η hvu.symm⟩
  · exact ⟨mem_perp_of_commute_mk h113 hC hrad hn3 hα' hη' ht₀α' hw₀η' hwt.symm,
      mem_perp_of_commute_mk h113 hC hrad hn3 hγ hη' hu₀γ hw₀η' hwu.symm⟩
  · exact not_mem_perp_of_not_commute_mk h89 h113 hC hrad hW hn3 hMZ hη' hη
      hw₀η' hv₀η (fun h => hvw h.symm)

theorem exists_kernel_config_of_four (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hfour : ∃ t ∈ imageClass hC, ∃ u ∈ imageClass hC, ∃ v ∈ imageClass hC,
      ∃ w ∈ imageClass hC, ¬ Commute t u ∧ ¬ Commute v w ∧
        Commute v t ∧ Commute v u ∧ Commute w t ∧ Commute w u) :
    ∃ α' ∈ Dalpha D hC.alpha, ∃ γ ∈ Dalpha D hC.alpha,
      γ ∉ perp D α' ∧ hC.alpha ∉ blockLine D α' γ := by
  obtain ⟨α', hα', γ, hγ, η, hη, η', -, hγα', hηp, hη'p, hηη'⟩ :=
    exists_four_points_of_four h89 h113 hC hrad hW hn3 hMZ hfour
  exact exists_mem_Dalpha_not_mem_blockLine_of_conj hC hα'.1 hγ.1 hη.1 hγα' hηp.1 hηp.2
    (not_mem_blockLine_of_not_mem_perp hη'p hηη')

end CFSG.OddTranspositions.PartFour
