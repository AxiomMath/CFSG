module

public import CFSG.OddTranspositions.PartFour.LineVmem

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem blockLine_subset_of_mem_of_mem {α β δ ε : Set G} (hα : α ⊆ D)
    (hδ : δ ∈ blockLine D α β) (hε : ε ∈ blockLine D α β) :
    blockLine D δ ε ⊆ blockLine D α β := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [← blockClass_eq_of_mem hδ.1]
    exact hx.1
  · intro γ hγ
    have hγD : γ ⊆ D := by
      rcases mem_perp_iff.mp hγ.1 with h | rfl
      · exact h.2.1
      · exact hα
    exact hx.2 γ ⟨mem_perp_symm (hδ.2 γ hγ) hγD, mem_perp_symm (hε.2 γ hγ) hγD⟩

theorem commute_of_mem_closure_of_mem_perp {α' δ : Set G}
    (hcomm : ∀ a ∈ α', ∀ b ∈ α', Commute a b) (hδ : δ ∈ perp D α') {z : G}
    (hz : z ∈ Subgroup.closure α') {x : G} (hx : x ∈ δ) : Commute z x := by
  have hle : α' ⊆ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    change a ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases mem_perp_iff.mp hδ with h | rfl
    · exact (mem_Dalpha_iff.mp h).2.2.2 a ha x hx
    · exact hcomm a ha x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (Subgroup.closure_le (K := Subgroup.centralizer ({x} : Set G)) |>.mpr hle hz)

theorem cimg_mem_blockLine_of_mem_closure (hN : IsNormalSet D) {α' γ : Set G} (hα' : α' ⊆ D)
    (hcomm : ∀ a ∈ α', ∀ b ∈ α', Commute a b) (hγ : γ ∈ blockClass α') {z : G}
    (hz : z ∈ Subgroup.closure α') : cimg z γ ∈ blockLine D α' γ := by
  refine ⟨?_, ?_⟩
  · rw [cimg_mem_blockClass_iff]
    exact hγ
  · intro ε hε
    have hεfix : cimg z ε = ε := by
      refine cimg_eq_self_of_mem_normalizer (OddLocal.mem_normalizer_of_commute ?_)
      intro c hc
      exact commute_of_mem_closure_of_mem_perp hcomm hε.1 hz hc
    have hγD : γ ⊆ D := by
      obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hγ
      rintro x ⟨y, hy, rfl⟩
      exact hN g y (hα' hy)
    have hperp : γ ∈ perp D ε := mem_perp_symm hε.2 hγD
    simpa [hεfix] using (perp_cimg_mem hN z (α := ε) (γ := γ)).mpr hperp

private theorem rootKernel_mem_center_of_closure_insert_eq_top {α' : Set G} {c z : G}
    (hcomm : ∀ a ∈ α', ∀ b ∈ α', Commute a b) (hz : z ∈ Subgroup.closure α')
    (hcz : Commute c z)
    (htop : Subgroup.closure (insert c (α' ∪ DalphaStar D α')) = ⊤) :
    z ∈ Subgroup.center G := by
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  have hgen : insert c (α' ∪ DalphaStar D α') ⊆ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    change x ∈ Subgroup.centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hcz
    · rcases hx with hx | hx
      · exact (commute_of_mem_closure_of_mem_perp hcomm
          ((mem_perp_iff (D := D) (α := α') (β := α')).mpr (Or.inr rfl)) hz hx).symm
      · obtain ⟨ε, hε, hxε⟩ := mem_DalphaStar_iff.mp hx
        exact (commute_of_mem_closure_of_mem_perp hcomm
          ((mem_perp_iff (D := D) (α := α') (β := ε)).mpr (Or.inl hε)) hz hxε).symm
  have hle : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [← htop]
    exact (Subgroup.closure_le (K := Subgroup.centralizer ({z} : Set G))).mpr hgen
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))

variable [Finite G]

private theorem rootKernel_closure_insert_eq_closure_inter (hC : HypothesisC D) {α' γ : Set G}
    (hα' : α' ∈ blockClass hC.alpha) (hγ : γ ∈ blockClass hC.alpha) {c : G} (hc : c ∈ γ) :
    Subgroup.closure (insert c (α' ∪ DalphaStar D α')) =
      Subgroup.closure
        ((Subgroup.closure (insert c (α' ∪ DalphaStar D α')) : Set G) ∩ D) := by
  have hα'block : IsBlock D α' :=
    isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hα'
  have hgenD : insert c (α' ∪ DalphaStar D α') ⊆ D := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγ hc
    · rcases hx with hx | hx
      · exact subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hα' hx
      · exact DalphaStar_subset hα'block hx
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hgenD hx⟩
  · rw [Subgroup.closure_le]
    intro x hx
    exact hx.1

private theorem rootKernel_inv_mul_conj_mem_Malpha (hC : HypothesisC D) {γ : Set G}
    (hγ : γ ∈ Dalpha D hC.alpha) {c z : G} (hc : c ∈ γ)
    (hzM : z ∈ Malpha D hC.alpha) :
    c⁻¹ * (z * c * z⁻¹) ∈ Malpha D hC.alpha := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  obtain ⟨y, hyR, hyz⟩ := Subgroup.mem_map.mp hzM
  let cH : H := ⟨c, Subgroup.subset_closure ⟨γ, hγ, hc⟩⟩
  refine Subgroup.mem_map.mpr ⟨cH⁻¹ * ((y : H) * cH * (y : H)⁻¹), ?_, ?_⟩
  · have h1 : cH⁻¹ * (y : H) * cH ∈ R := by
      simpa using (inferInstance : R.Normal).conj_mem (y : H) hyR cH⁻¹
    have h2 : (y : H)⁻¹ ∈ R := R.inv_mem hyR
    simpa [mul_assoc] using R.mul_mem h1 h2
  · change c⁻¹ * (((y : H) : G) * c * ((y : H) : G)⁻¹) = c⁻¹ * (z * c * z⁻¹)
    rw [show ((y : H) : G) = z from hyz]

theorem closure_insert_union_DalphaStar_eq_top (hC : HypothesisC D) {α' γ : Set G}
    (hα' : α' ∈ blockClass hC.alpha) (hγ : γ ∈ blockClass hC.alpha) (hγα' : γ ∉ perp D α')
    {c : G} (hc : c ∈ γ) : Subgroup.closure (insert c (α' ∪ DalphaStar D α')) = ⊤ := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hα'
  let hC' : HypothesisC D := hC.conj g
  have hαeq : hC'.alpha = α' := by
    change (hC.conj g).alpha = α'
    exact (HypothesisC.conj_alpha hC g).trans hg.symm
  let X : Subgroup G := Subgroup.closure (insert c (α' ∪ DalphaStar D α'))
  have hXeq : X = Subgroup.closure ((X : Set G) ∩ D) :=
    rootKernel_closure_insert_eq_closure_inter hC hα' hγ hc
  have hdα' : hC'.d ∈ α' := hαeq ▸ hC'.d_mem_alpha
  have hd' : hC'.d ∈ X :=
    Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr (Or.inl hdα')))
  have hE' : hC'.E ⊆ (X : Set G) := by
    intro x hx
    have hx' : x ∈ DalphaStar D α' := by
      rw [← hαeq, hC'.DalphaStar_alpha]
      exact hx
    exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr (Or.inr hx')))
  by_contra hproper
  have hsub := inter_D_subset_perp hC' hXeq hd' hE' hproper
  have hcX : c ∈ X := Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))
  have hcD : c ∈ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγ hc
  have hcUnion : c ∈ hC'.alpha ∪ DalphaStar D hC'.alpha := hsub ⟨hcX, hcD⟩
  rw [hαeq] at hcUnion
  rcases hcUnion with hcα' | hcStar
  · exact hγα' (mem_perp_of_commute hC hα' hγ hcα' hc (Commute.refl c))
  · obtain ⟨ε, hε, hcε⟩ := mem_DalphaStar_iff.mp hcStar
    obtain ⟨a, ha⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hα'
    exact hγα' (mem_perp_of_commute hC hα' hγ ha hc (hε.2.2.2 a ha c hcε))

theorem eq_one_of_mem_closure_of_mem_Malpha (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {α' γ : Set G} (hα' : α' ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    (hγα' : γ ∉ perp D α') (hαℓ : hC.alpha ∉ blockLine D α' γ) {z : G}
    (hz : z ∈ Subgroup.closure α') (hzM : z ∈ Malpha D hC.alpha) : z = 1 := by
  have hcomm : ∀ a ∈ α', ∀ b ∈ α', Commute a b :=
    fun a ha b hb => commute_of_mem_Dalpha h89 h113 hC hrad hW hn3 hMZ hα' ha hb
  have hclassα'γ : γ ∈ blockClass α' :=
    mem_blockClass_of_mem_blockClass hα'.1 hγ.1
  obtain ⟨y, hyR, hyz⟩ := Subgroup.mem_map.mp hzM
  have hb1 : cimg z γ ∈ blockLine D hC.alpha γ := by
    rw [← hyz]
    exact conj_mem_blockLine h113 hC hrad hn3 hγ (x := y) hyR
  have hb2 : cimg z γ ∈ blockLine D α' γ :=
    cimg_mem_blockLine_of_mem_closure hC.setup.normal hα'.2.1 hcomm hclassα'γ hz
  have hfix : cimg z γ = γ := by
    by_contra hne
    have hline : blockLine D γ (cimg z γ) = blockLine D hC.alpha γ :=
      blockLine_eq_of_mem_of_mem hC hγ (right_mem_blockLine hγ.1 hγ.2.1) hb1 (Ne.symm hne)
    have hsub : blockLine D γ (cimg z γ) ⊆ blockLine D α' γ :=
      blockLine_subset_of_mem_of_mem hα'.2.1 (right_mem_blockLine hclassα'γ hγ.2.1) hb2
    have hmem : hC.alpha ∈ blockLine D γ (cimg z γ) := by
      rw [hline]
      exact left_mem_blockLine hC.isBlock_alpha.subset
    exact hαℓ (hsub hmem)
  obtain ⟨c, hc⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγ.1
  have hc'γ : z * c * z⁻¹ ∈ γ := by
    rw [← hfix]
    exact ⟨c, hc, rfl⟩
  have hcc' : c⁻¹ * (z * c * z⁻¹) ∈ Malpha D hC.alpha :=
    rootKernel_inv_mul_conj_mem_Malpha hC hγ hc hzM
  have heq : c = z * c * z⁻¹ :=
    eq_of_mem_of_inv_mul_mem_Malpha h89 h113 hC hrad hW hn3 hHns hγ hc hc'γ hcc'
  have hcz : Commute c z := by
    have h : c * z = z * c := by
      calc c * z = (z * c * z⁻¹) * z := by conv_lhs => rw [heq]
        _ = z * c := by group
    exact h
  have htop := closure_insert_union_DalphaStar_eq_top hC hα'.1 hγ.1 hγα' hc
  have hcenter : z ∈ Subgroup.center G :=
    rootKernel_mem_center_of_closure_insert_eq_top hcomm hz hcz htop
  have hbot : Subgroup.center G = ⊥ := hrad _ inferInstance inferInstance
  rw [hbot] at hcenter
  exact Subgroup.mem_bot.mp hcenter

end CFSG.OddTranspositions.PartFour
