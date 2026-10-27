module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.FrameLift

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity


variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenOneHyp

variable {hC : HypothesisC D}

private theorem s11f4b_conjAut {hC : HypothesisC D} (h : ElevenOneHyp hC)
    {g : G} (hg : g ∈ Subgroup.centralizer {hC.d}) :
    ∃ (φ : MulAut (Halpha D hC.alpha))
      (φ' : MulAut (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))),
      (∀ x : Halpha D hC.alpha, (φ x : G) = g * (x : G) * g⁻¹) ∧
      (∀ x : Halpha D hC.alpha,
        φ' (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x) =
          QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (φ x)) ∧
      φ' '' imageClass hC = imageClass hC ∧ φ '' DstarH hC = DstarH hC := by
  let K := CFSG.solvableRadical (Halpha D hC.alpha)
  have hgN_u : g ∈ Subgroup.normalizer ({hC.d} : Set G) :=
    Subgroup.centralizer_le_normalizer _ hg
  have hgN_alpha : g ∈ Subgroup.normalizer hC.alpha := by
    rw [h.alpha_eq]; exact hgN_u
  have hgN_H : g ∈ Subgroup.normalizer (Halpha D hC.alpha) :=
    normalizer_le_normalizer_Halpha hC.setup.normal hgN_alpha
  have hconj : ⇑(MulAut.conj g) '' (Halpha D hC.alpha : Set G) =
      (Halpha D hC.alpha : Set G) :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp hgN_H
  have hconj_inv : ⇑(MulAut.conj g⁻¹) '' (Halpha D hC.alpha : Set G) =
      (Halpha D hC.alpha : Set G) :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp (Subgroup.inv_mem _ hgN_H)
  let φ : MulAut (Halpha D hC.alpha) :=
    { toFun := fun x => ⟨g * (x : G) * g⁻¹, by
        have hx : MulAut.conj g (x : G) ∈
            ⇑(MulAut.conj g) '' (Halpha D hC.alpha : Set G) :=
          Set.mem_image_of_mem _ x.2
        rw [hconj] at hx
        rw [MulAut.conj_apply] at hx
        exact hx⟩
      invFun := fun x => ⟨g⁻¹ * (x : G) * g, by
        have hx : MulAut.conj g⁻¹ (x : G) ∈
            ⇑(MulAut.conj g⁻¹) '' (Halpha D hC.alpha : Set G) :=
          Set.mem_image_of_mem _ x.2
        rw [hconj_inv] at hx
        rw [MulAut.conj_apply, inv_inv] at hx
        exact hx⟩
      left_inv := fun x => by ext; group
      right_inv := fun x => by ext; group
      map_mul' := fun x y => by ext; simp only [Subgroup.coe_mul]; group }
  have hφcoe : ∀ x : Halpha D hC.alpha, (φ x : G) = g * (x : G) * g⁻¹ := fun _ => rfl
  have hKchar : Subgroup.map φ.toMonoidHom K = K :=
    Subgroup.characteristic_iff_map_eq.mp (inferInstance : K.Characteristic) φ
  let φ' : MulAut (Halpha D hC.alpha ⧸ K) := QuotientGroup.congr K K φ hKchar
  have hφ'apply : ∀ x : Halpha D hC.alpha,
      φ' (QuotientGroup.mk' K x) = QuotientGroup.mk' K (φ x) :=
    fun x => QuotientGroup.congr_apply K K φ hKchar x
  have hφDstar : φ '' DstarH hC = DstarH hC := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [mem_DstarH_iff, hφcoe]
      exact conj_mem h hg ((mem_DstarH_iff hC).mp hx)
    · intro y hy
      have hyD : (y : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp hy
      have hg'inv : g⁻¹ ∈ Subgroup.centralizer {hC.d} := Subgroup.inv_mem _ hg
      have hxD : g⁻¹ * (y : G) * g ∈ DalphaStar D hC.alpha := by
        simpa only [inv_inv] using conj_mem h hg'inv hyD
      let x : Halpha D hC.alpha := ⟨g⁻¹ * (y : G) * g, Subgroup.subset_closure hxD⟩
      have hxmem : x ∈ DstarH hC := (mem_DstarH_iff hC).mpr hxD
      refine ⟨x, hxmem, ?_⟩
      apply Subtype.ext
      rw [hφcoe]
      change g * (g⁻¹ * (y : G) * g) * g⁻¹ = (y : G)
      group
  have hφ'Θ : φ' '' imageClass hC = imageClass hC := by
    apply Set.Subset.antisymm
    · rintro z ⟨u, hu, rfl⟩
      rw [imageClass] at hu ⊢
      obtain ⟨y, hy, rfl⟩ := hu
      rw [hφ'apply]
      exact ⟨φ y, by rw [← hφDstar]; exact Set.mem_image_of_mem φ hy, rfl⟩
    · intro z hz
      rw [imageClass] at hz ⊢
      obtain ⟨y, hy, rfl⟩ := hz
      have hyD : (y : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp hy
      have hg'inv : g⁻¹ ∈ Subgroup.centralizer {hC.d} := Subgroup.inv_mem _ hg
      have hxD : g⁻¹ * (y : G) * g ∈ DalphaStar D hC.alpha := by
        simpa only [inv_inv] using conj_mem h hg'inv hyD
      let x : Halpha D hC.alpha := ⟨g⁻¹ * (y : G) * g, Subgroup.subset_closure hxD⟩
      have hxmem : x ∈ DstarH hC := (mem_DstarH_iff hC).mpr hxD
      have hφx : φ x = y := by
        apply Subtype.ext
        rw [hφcoe]
        change g * (g⁻¹ * (y : G) * g) * g⁻¹ = (y : G)
        group
      refine ⟨QuotientGroup.mk' K x, ⟨x, hxmem, rfl⟩, ?_⟩
      rw [hφ'apply, hφx]
  exact ⟨φ, φ', hφcoe, hφ'apply, hφ'Θ, hφDstar⟩

theorem aut_frameLift (h : ElevenOneHyp hC) {T : Sylow 2 (Halpha D hC.alpha)}
    {r : Fin 4 → Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hr : O4PlusFrame (imageClass hC) ((T : Subgroup (Halpha D hC.alpha)).map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))) r)
    {w : Fin 4 → Halpha D hC.alpha}
    (hwr : ∀ i, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w i) = r i)
    (hw : (T : Set (Halpha D hC.alpha)) ∩ DstarH hC = Set.range w) :
    ∀ g ∈ Subgroup.centralizer {hC.d}, (∀ i, g * (w i : G) * g⁻¹ = w i) →
      ∃ c ∈ Subgroup.closure (Set.range fun i => (w i : G)), ∀ x ∈ DalphaStar D hC.alpha,
        g * x * g⁻¹ = c * x * c⁻¹ := by
  let K := CFSG.solvableRadical (Halpha D hC.alpha)
  intro g hg hgfix
  have hr' : O4PlusFrame (imageClass hC) ((T : Subgroup (Halpha D hC.alpha)).map
      (QuotientGroup.mk' K)) r := hr
  have hwr' : ∀ i, QuotientGroup.mk' K (w i) = r i := hwr
  obtain ⟨φ, φ', hφcoe, hφ'apply, hφ'Θ, hφDstar⟩ := s11f4b_conjAut h hg
  have hφ'r : ∀ i, φ' (r i) = r i := by
    intro i
    have hφw : φ (w i) = w i := Subtype.ext (by rw [hφcoe]; exact hgfix i)
    rw [← hwr' i, hφ'apply, hφw, hwr' i]
  obtain ⟨dbar, hdbar_mem, hdbar_conj⟩ := hr'.aut φ' hφ'Θ hφ'r
  have hrw : r = QuotientGroup.mk' K ∘ w := funext fun i => (hwr' i).symm
  have hr_eq : Subgroup.closure (Set.range r) =
      Subgroup.map (QuotientGroup.mk' K) (Subgroup.closure (Set.range w)) := by
    rw [hrw, Set.range_comp, MonoidHom.map_closure]
  have hdbar_mem' : dbar ∈ Subgroup.map (QuotientGroup.mk' K)
      (Subgroup.closure (Set.range w)) := hr_eq ▸ hdbar_mem
  obtain ⟨cH, hcH_mem, hcH_eq⟩ := (Subgroup.mem_map).mp hdbar_mem'
  refine ⟨(cH : G), ?_, ?_⟩
  · have hsub_map : Subgroup.map (Halpha D hC.alpha).subtype
        (Subgroup.closure (Set.range w)) =
        Subgroup.closure (Set.range fun i => (w i : G)) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨w i, ⟨i, rfl⟩, rfl⟩
    have hmem : (cH : G) ∈ Subgroup.map (Halpha D hC.alpha).subtype
        (Subgroup.closure (Set.range w)) :=
      Subgroup.mem_map_of_mem _ hcH_mem
    rwa [hsub_map] at hmem
  · intro x hx
    let xH : Halpha D hC.alpha := ⟨x, Subgroup.subset_closure hx⟩
    have hxH : xH ∈ DstarH hC := (mem_DstarH_iff hC).mpr hx
    have hφxH : φ xH ∈ DstarH hC := by
      rw [← hφDstar]; exact Set.mem_image_of_mem φ hxH
    have hcxH : cH * xH * cH⁻¹ ∈ DstarH hC :=
      DstarH_conj_mem hC (h := cH) (x := xH) hxH
    have hπeq : QuotientGroup.mk' K (φ xH) =
        QuotientGroup.mk' K (cH * xH * cH⁻¹) := by
      rw [← hφ'apply, hdbar_conj]
      simp only [map_mul, map_inv, hcH_eq]
      rfl
    have hcong := h.injOn hφxH hcxH hπeq
    have h2 : (φ xH : G) = ((cH * xH * cH⁻¹ : Halpha D hC.alpha) : G) :=
      congrArg Subtype.val hcong
    rw [hφcoe] at h2
    simpa using h2

end ElevenOneHyp

end CFSG.OddTranspositions.PartThree
