module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Frame
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Conj
import CFSG.OddTranspositions.SixEight

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity


variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenOneHyp

variable {hC : HypothesisC D}

private theorem perp_eq (h : ElevenOneHyp hC) :
    D ∩ (Subgroup.centralizer ({hC.d} : Set G) : Set G) =
      ({hC.d} : Set G) ∪ DalphaStar D hC.alpha := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxD, hxc⟩ := hx
    have hxc' : Commute x hC.d := Subgroup.mem_centralizer_singleton_iff.mp hxc
    have hx' : x ∈ hC.alpha ∪ DalphaStar D hC.alpha ∪ AalphaStar D hC.alpha :=
      hC.eq_alpha_union ▸ hxD
    rcases hx' with (hxα | hxE) | hxA
    · left
      rwa [h.alpha_eq] at hxα
    · exact Or.inr hxE
    · rw [hC.AalphaStar_eq_diff_alpha] at hxA
      exact absurd hxc' hxA.1.2
  · rintro x (rfl | hxE)
    · exact ⟨hC.hd, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl _)⟩
    · exact ⟨DalphaStar_subset hC.isBlock_alpha hxE,
        Subgroup.mem_centralizer_singleton_iff.mpr (hC.DalphaStar_subset_commute hxE).2⟩

private theorem inter_D_centralizer_eq (h : ElevenOneHyp hC) {a : G} (ha1 : a ≠ 1)
    (ha : ∀ x ∈ ({hC.d} : Set G) ∪ DalphaStar D hC.alpha, Commute a x) :
    D ∩ (Subgroup.centralizer ({a} : Set G) : Set G) =
      ({hC.d} : Set G) ∪ DalphaStar D hC.alpha := by
  set X : Subgroup G :=
    Subgroup.closure (D ∩ (Subgroup.centralizer ({a} : Set G) : Set G)) with hXdef
  have hXle : X ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [hXdef]
    exact (Subgroup.closure_le _).mpr (fun x hx => hx.2)
  have hXinter : (X : Set G) ∩ D =
      D ∩ (Subgroup.centralizer ({a} : Set G) : Set G) := by
    ext x
    constructor
    · rintro ⟨hxX, hxD⟩
      exact ⟨hxD, hXle hxX⟩
    · rintro ⟨hxD, hxC⟩
      exact ⟨Subgroup.subset_closure ⟨hxD, hxC⟩, hxD⟩
  have hXclosure : X = Subgroup.closure ((X : Set G) ∩ D) := by
    rw [hXinter, ← hXdef]
  have hdX : hC.d ∈ X := by
    rw [hXdef]
    exact Subgroup.subset_closure
      ⟨hC.hd, Subgroup.mem_centralizer_singleton_iff.mpr (ha hC.d (Or.inl rfl)).symm⟩
  have hEX : hC.E ⊆ (X : Set G) := by
    intro e he
    rw [← hC.DalphaStar_alpha] at he
    rw [hXdef]
    exact Subgroup.subset_closure
      ⟨DalphaStar_subset hC.isBlock_alpha he,
        Subgroup.mem_centralizer_singleton_iff.mpr (ha e (Or.inr he)).symm⟩
  have hproper : X ≠ ⊤ := by
    intro htop
    have hcenter : a ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hgX : g ∈ X := htop.symm ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp (hXle hgX)
    have hbot : Subgroup.center G = ⊥ :=
      h.rad (Subgroup.center G) inferInstance inferInstance
    have : a ∈ (⊥ : Subgroup G) := hbot ▸ hcenter
    exact ha1 (by simpa using this)
  have hsub := inter_D_subset_perp hC hXclosure hdX hEX hproper
  rw [hXinter] at hsub
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    have := hsub hx
    nth_rewrite 1 [h.alpha_eq] at this
    exact this
  · rintro x (rfl | hxE)
    · exact ⟨hC.hd, Subgroup.mem_centralizer_singleton_iff.mpr (ha hC.d (Or.inl rfl)).symm⟩
    · exact ⟨DalphaStar_subset hC.isBlock_alpha hxE,
        Subgroup.mem_centralizer_singleton_iff.mpr (ha x (Or.inr hxE)).symm⟩

private theorem false_of_centralizer_eq (h : ElevenOneHyp hC) {v : G}
    (hvE : v ∈ DalphaStar D hC.alpha)
    (hperp : D ∩ (Subgroup.centralizer ({hC.d} : Set G) : Set G) =
      D ∩ (Subgroup.centralizer ({v} : Set G) : Set G)) : False := by
  let vH : Halpha D hC.alpha := ⟨v, Subgroup.subset_closure hvE⟩
  have hvDstar : vH ∈ DstarH hC := hvE
  have hv_image : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) vH ∈
      imageClass hC := ⟨vH, hvDstar, rfl⟩
  obtain ⟨b, hb, hnc⟩ := h.facts.noncomm _ hv_image
  obtain ⟨y, hyH, hyb⟩ := hb
  rw [← hyb] at hnc
  have hyD : (y : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp hyH
  have hy_u : (y : G) ∈ D ∩ (Subgroup.centralizer ({hC.d} : Set G) : Set G) := by
    rw [perp_eq h]
    exact Or.inr hyD
  have hyv : Commute (y : G) v :=
    Subgroup.mem_centralizer_singleton_iff.mp (hperp ▸ hy_u).2
  have hyvH : y * vH = vH * y := Subtype.ext (by simpa [vH] using hyv.eq)
  have hcomm : Commute (QuotientGroup.mk' _ y)
      (QuotientGroup.mk' _ vH) :=
    (h.commute_iff hyH hvDstar).mp hyvH
  exact hnc hcomm.symm

private theorem centralizes_union_of_centralizes_Dv (h : ElevenOneHyp hC) {g a' : G}
    (hfix : ∀ x ∈ DalphaStar D (hC.conj g).alpha, a' * x * a'⁻¹ = x) :
    ∀ x ∈ ({(hC.conj g).d} : Set G) ∪ DalphaStar D (hC.conj g).alpha, Commute a' x := by
  have hcentral : a' ∈ Subgroup.centralizer (DalphaStar D (hC.conj g).alpha) :=
    Subgroup.mem_centralizer_iff.mpr
      (fun x hx => (mul_inv_eq_iff_eq_mul.mp (hfix x hx)).symm)
  intro x hx
  rcases hx with hx | hx
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have hv_closure : (hC.conj g).d ∈ Halpha D (hC.conj g).alpha :=
      (h.conj g).d_mem_Halpha
    have hC'c : a' ∈ Subgroup.centralizer (Halpha D (hC.conj g).alpha : Set G) := by
      change a' ∈ Subgroup.centralizer
        (Subgroup.closure (DalphaStar D (hC.conj g).alpha) : Set G)
      rw [Subgroup.centralizer_closure]
      exact hcentral
    exact (Subgroup.mem_centralizer_iff.mp hC'c (hC.conj g).d hv_closure).symm
  · exact mul_inv_eq_iff_eq_mul.mp (hfix x hx)

private theorem frame_commute (hC : HypothesisC D) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) {x y : G}
    (hx : x ∈ (S : Set G) ∩ D) (hy : y ∈ (S : Set G) ∩ D) : Commute x y := by
  have hx' : x ∈ insert hC.d (Set.range v) := by rwa [hv.inter_eq] at hx
  have hy' : y ∈ insert hC.d (Set.range v) := by rwa [hv.inter_eq] at hy
  rw [Set.mem_insert_iff] at hx' hy'
  rcases hx' with rfl | hx'
  · rcases hy' with rfl | hy'
    · exact Commute.refl _
    · obtain ⟨j, rfl⟩ := hy'
      exact (hC.DalphaStar_subset_commute (hv.mem j)).2.symm
  · obtain ⟨i, rfl⟩ := hx'
    rcases hy' with rfl | hy'
    · exact (hC.DalphaStar_subset_commute (hv.mem i)).2
    · obtain ⟨j, rfl⟩ := hy'
      by_cases hij : i = j
      · subst hij
        exact Commute.refl _
      · obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by
          fin_cases i <;> fin_cases j <;> decide
        have hD_i : v i ∈ D := DalphaStar_subset hC.isBlock_alpha (hv.mem i)
        have hD_j : v j ∈ D := DalphaStar_subset hC.isBlock_alpha (hv.mem j)
        have hP : IsPGroup 2 (Subgroup.closure (Set.range v \ {v k})) :=
          IsPGroup.of_card (p := 2) (n := 3) (by rw [hv.card_closure k]; norm_num)
        have hik : v i ≠ v k := fun h => hki (hv.injective h).symm
        have hjk : v j ≠ v k := fun h => hkj (hv.injective h).symm
        have hiP : v i ∈ Subgroup.closure (Set.range v \ {v k}) :=
          Subgroup.subset_closure ⟨Set.mem_range_self i, by simpa using hik⟩
        have hjP : v j ∈ Subgroup.closure (Set.range v \ {v k}) :=
          Subgroup.subset_closure ⟨Set.mem_range_self j, by simpa using hjk⟩
        exact hC.setup.oddT.commute_of_isPGroup hP hD_i hD_j hiP hjP

theorem centralizer_Halpha (h : ElevenOneHyp hC) :
    Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d := by
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr (d_mem_centralizer hC))
  intro a haC
  by_cases ha1 : a = 1
  · rw [ha1]
    exact Subgroup.one_mem _
  by_cases hau : a = hC.d
  · rw [hau]
    exact Subgroup.mem_zpowers _
  exfalso
  have ha : ∀ x ∈ ({hC.d} : Set G) ∪ DalphaStar D hC.alpha, Commute a x := by
    intro x hx
    have hxH : x ∈ Halpha D hC.alpha := by
      rcases hx with rfl | hxE
      · exact h.d_mem_Halpha
      · exact Subgroup.subset_closure hxE
    exact (Subgroup.mem_centralizer_iff.mp haC x hxH).symm
  have hDa : D ∩ (Subgroup.centralizer ({a} : Set G) : Set G) =
      ({hC.d} : Set G) ∪ DalphaStar D hC.alpha := inter_D_centralizer_eq h ha1 ha
  obtain ⟨x₀, hx₀⟩ := DstarH_nonempty hC
  obtain ⟨v, hvE⟩ : (DalphaStar D hC.alpha).Nonempty :=
    ⟨(x₀ : G), (mem_DstarH_iff hC).mp hx₀⟩
  have hvH : v ∈ Halpha D hC.alpha := Subgroup.subset_closure hvE
  have hav : Commute a v := (Subgroup.mem_centralizer_iff.mp haC v hvH).symm
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (CFSG.Timmesfeld.isConj_of_isClass hC.setup.isClass hC.hd
      (DalphaStar_subset hC.isBlock_alpha hvE))
  let hC' : HypothesisC D := hC.conj g
  have h' : ElevenOneHyp hC' := h.conj g
  have hC'd : hC'.d = v := by
    change (hC.conj g).d = v
    rw [HypothesisC.conj_d hC g, hg]
  have hC'alpha : hC'.alpha = {v} := by
    change (hC.conj g).alpha = {v}
    rw [HypothesisC.conj_alpha hC g, h.alpha_eq]
    simp only [cimg, Set.image_singleton, hg]
  have hsingle : ({hC.d} : Set G) ∈ Dalpha D hC'.alpha := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mem_blockClass_iff]
      refine ⟨g⁻¹, ?_⟩
      rw [hC'alpha, Set.image_singleton, Set.singleton_eq_singleton_iff, ← hg]
      group
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hC.hd
    · intro heq
      have hmem : hC.d ∈ hC'.alpha := heq ▸ (by simp : hC.d ∈ ({hC.d} : Set G))
      rw [hC'alpha, Set.mem_singleton_iff] at hmem
      exact d_not_mem_DalphaStar hC (by rwa [← hmem] at hvE)
    · intro y hy z hz
      rw [hC'alpha] at hy
      rw [Set.mem_singleton_iff] at hy hz
      subst hy
      subst hz
      exact (hC.DalphaStar_subset_commute hvE).2
  have hu_Dv : hC.d ∈ DalphaStar D hC'.alpha :=
    mem_DalphaStar_iff.mpr ⟨{hC.d}, hsingle, by simp⟩
  have hav' : a ∈ Subgroup.centralizer ({hC'.d} : Set G) := by
    rw [hC'd]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hav
  have hfix : ∀ b ∈ DalphaStar D hC'.alpha, Commute hC.d b → a * b * a⁻¹ = b := by
    intro b hbE hbc
    have hbD : b ∈ D := DalphaStar_subset hC'.isBlock_alpha hbE
    have hb_u : b ∈ ({hC.d} : Set G) ∪ DalphaStar D hC.alpha := by
      have : b ∈ D ∩ (Subgroup.centralizer ({hC.d} : Set G) : Set G) :=
        ⟨hbD, Subgroup.mem_centralizer_singleton_iff.mpr hbc.symm⟩
      rwa [perp_eq h] at this
    have hbCa : b ∈ D ∩ (Subgroup.centralizer ({a} : Set G) : Set G) := by
      rw [hDa]
      exact hb_u
    have hcomm : Commute b a := Subgroup.mem_centralizer_singleton_iff.mp hbCa.2
    calc a * b * a⁻¹ = b * a * a⁻¹ := by rw [hcomm.eq.symm]
      _ = b := by group
  have hperp_lift := perp_lift h' hav' hu_Dv hfix
  have hperp_of (a' : G) (ha'1 : a' ≠ 1)
      (ha'u : ∀ x ∈ ({hC.d} : Set G) ∪ DalphaStar D hC.alpha, Commute a' x)
      (ha'v : ∀ x ∈ ({hC'.d} : Set G) ∪ DalphaStar D hC'.alpha, Commute a' x) :
      D ∩ (Subgroup.centralizer ({hC.d} : Set G) : Set G) =
        D ∩ (Subgroup.centralizer ({v} : Set G) : Set G) := by
    have h1 : D ∩ (Subgroup.centralizer ({a'} : Set G) : Set G) =
        ({hC.d} : Set G) ∪ DalphaStar D hC.alpha :=
      inter_D_centralizer_eq h ha'1 ha'u
    have h2 : D ∩ (Subgroup.centralizer ({a'} : Set G) : Set G) =
        ({hC'.d} : Set G) ∪ DalphaStar D hC'.alpha :=
      inter_D_centralizer_eq (h := h') ha'1 ha'v
    calc D ∩ (Subgroup.centralizer ({hC.d} : Set G) : Set G)
        = ({hC.d} : Set G) ∪ DalphaStar D hC.alpha := perp_eq h
      _ = D ∩ (Subgroup.centralizer ({a'} : Set G) : Set G) := h1.symm
      _ = ({hC'.d} : Set G) ∪ DalphaStar D hC'.alpha := h2
      _ = D ∩ (Subgroup.centralizer ({hC'.d} : Set G) : Set G) := (perp_eq h').symm
      _ = D ∩ (Subgroup.centralizer ({v} : Set G) : Set G) := by rw [hC'd]
  rcases hperp_lift with htriv | hact
  · exact false_of_centralizer_eq h hvE
      (hperp_of a ha1 ha (centralizes_union_of_centralizes_Dv h htriv))
  · have ha'_fix : ∀ x ∈ DalphaStar D hC'.alpha, (hC.d * a) * x * (hC.d * a)⁻¹ = x := by
      intro x hx
      have hxact := hact x hx
      have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
      have hui : hC.d⁻¹ = hC.d := hC.setup.oddT.inv_eq hC.hd
      calc (hC.d * a) * x * (hC.d * a)⁻¹
          = hC.d * (a * x * a⁻¹) * hC.d⁻¹ := by group
        _ = hC.d * (hC.d * x * hC.d⁻¹) * hC.d⁻¹ := by rw [hxact]
        _ = (hC.d * hC.d) * x * (hC.d * hC.d) := by rw [hui]; group
        _ = x := by rw [hu2]; group
    have ha'1 : hC.d * a ≠ 1 := by
      intro h1
      apply hau
      calc a = 1 * a := by group
        _ = (hC.d * hC.d) * a := by rw [hC.setup.oddT.mul_self_eq_one hC.hd]
        _ = hC.d * (hC.d * a) := by group
        _ = hC.d * 1 := by rw [h1]
        _ = hC.d := by group
    have ha'u : ∀ x ∈ ({hC.d} : Set G) ∪ DalphaStar D hC.alpha,
        Commute (hC.d * a) x := by
      have ha'C : hC.d * a ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G) :=
        Subgroup.mul_mem _ (d_mem_centralizer hC) haC
      intro x hx
      have hxH : x ∈ Halpha D hC.alpha := by
        rcases hx with rfl | hxE
        · exact h.d_mem_Halpha
        · exact Subgroup.subset_closure hxE
      exact (Subgroup.mem_centralizer_iff.mp ha'C x hxH).symm
    exact false_of_centralizer_eq h hvE
      (hperp_of (hC.d * a) ha'1 ha'u (centralizes_union_of_centralizes_Dv h ha'_fix))

theorem centralizer_frame (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) :
    Subgroup.centralizer ((S : Set G) ∩ D) = Subgroup.closure ((S : Set G) ∩ D) := by
  refine le_antisymm ?_ ?_
  · intro b hb
    have hu_mem : hC.d ∈ (S : Set G) ∩ D := by rw [hv.inter_eq]; simp
    have hv_mem : ∀ i, v i ∈ (S : Set G) ∩ D := by
      intro i
      rw [hv.inter_eq]
      simp
    have hbu : Commute hC.d b := Subgroup.mem_centralizer_iff.mp hb hC.d hu_mem
    have hbvi : ∀ i, Commute (v i) b := fun i =>
      Subgroup.mem_centralizer_iff.mp hb (v i) (hv_mem i)
    have hbC : b ∈ Subgroup.centralizer ({hC.d} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hbu.symm
    have hbfix : ∀ i, b * v i * b⁻¹ = v i := by
      intro i
      calc b * v i * b⁻¹ = v i * b * b⁻¹ := by rw [(hbvi i).eq.symm]
        _ = v i := by group
    obtain ⟨c, hc_closure, hc_act⟩ := hv.aut b hbC hbfix
    have hcb_central : c⁻¹ * b ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G) := by
      change c⁻¹ * b ∈ Subgroup.centralizer
        (Subgroup.closure (DalphaStar D hC.alpha) : Set G)
      rw [Subgroup.centralizer_closure]
      exact Subgroup.mem_centralizer_iff.mpr (fun x hx => by
        have hact := hc_act x hx
        have hconj : (c⁻¹ * b) * x * (c⁻¹ * b)⁻¹ = x := by
          calc (c⁻¹ * b) * x * (c⁻¹ * b)⁻¹
              = c⁻¹ * (b * x * b⁻¹) * c := by group
            _ = c⁻¹ * (c * x * c⁻¹) * c := by rw [hact]
            _ = x := by group
        exact (mul_inv_eq_iff_eq_mul.mp hconj).symm)
    have hcb_zpow : c⁻¹ * b ∈ Subgroup.zpowers hC.d := by
      rw [← centralizer_Halpha h]
      exact hcb_central
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hcb_zpow
    have hc_mem : c ∈ Subgroup.closure ((S : Set G) ∩ D) :=
      Subgroup.closure_mono (fun y hy => by
        obtain ⟨i, rfl⟩ := hy
        exact hv_mem i) hc_closure
    have hz_mem : c⁻¹ * b ∈ Subgroup.closure ((S : Set G) ∩ D) := by
      rw [← hn]
      exact Subgroup.zpow_mem _ (Subgroup.subset_closure hu_mem) n
    have hb_eq : b = c * (c⁻¹ * b) := by group
    rw [hb_eq]
    exact Subgroup.mul_mem _ hc_mem hz_mem
  · rw [Subgroup.closure_le]
    intro x hx
    change x ∈ Subgroup.centralizer ((S : Set G) ∩ D)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact frame_commute hC hv hy hx

end ElevenOneHyp

end CFSG.OddTranspositions.PartThree
