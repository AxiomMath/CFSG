module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenOneHyp

variable {hC : HypothesisC D}

theorem commute_iff (h : ElevenOneHyp hC) {x y : Halpha D hC.alpha} (hx : x ∈ DstarH hC)
    (hy : y ∈ DstarH hC) :
    Commute x y ↔ Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y) := by
  constructor
  · intro hxy
    exact hxy.map (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
  · intro hcomm
    by_contra hnc
    let K := CFSG.solvableRadical (Halpha D hC.alpha)
    have hodd := DstarH_isOddTransp hC
    have hm_odd : Odd (orderOf (x * y)) := hodd.odd_of_not_commute hx hy hnc
    have hπx2 : (QuotientGroup.mk' K x) ^ 2 = 1 := by
      rw [pow_two, ← map_mul, hodd.mul_self_eq_one hx, map_one]
    have hπy2 : (QuotientGroup.mk' K y) ^ 2 = 1 := by
      rw [pow_two, ← map_mul, hodd.mul_self_eq_one hy, map_one]
    have hπx2' : QuotientGroup.mk' K x * QuotientGroup.mk' K x = 1 := by
      rw [← pow_two]; exact hπx2
    have hπxy2 : (QuotientGroup.mk' K (x * y)) ^ 2 = 1 := by
      rw [map_mul, hcomm.mul_pow, hπx2, hπy2, mul_one]
    have hπxy_m : (QuotientGroup.mk' K (x * y)) ^ orderOf (x * y) = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hπxy_one : QuotientGroup.mk' K (x * y) = 1 := by
      obtain ⟨k, hk⟩ := hm_odd
      have h1 : (QuotientGroup.mk' K (x * y)) ^ (2 * k + 1) = 1 := by
        rw [← hk]; exact hπxy_m
      rw [pow_succ, pow_mul, hπxy2, one_pow, one_mul] at h1
      exact h1
    have hπxy1 : QuotientGroup.mk' K x * QuotientGroup.mk' K y = 1 := by
      rw [← map_mul]; exact hπxy_one
    have hπ_eq : QuotientGroup.mk' K x = QuotientGroup.mk' K y := by
      have hsym : QuotientGroup.mk' K y = QuotientGroup.mk' K x := by
        calc QuotientGroup.mk' K y
            = (QuotientGroup.mk' K x * QuotientGroup.mk' K x) * QuotientGroup.mk' K y := by
              rw [hπx2', one_mul]
          _ = QuotientGroup.mk' K x * (QuotientGroup.mk' K x * QuotientGroup.mk' K y) := by
              group
          _ = QuotientGroup.mk' K x * 1 := by rw [hπxy1]
          _ = QuotientGroup.mk' K x := mul_one _
      exact hsym.symm
    have hxy_eq : x = y := h.injOn hx hy hπ_eq
    exact hnc (hxy_eq ▸ Commute.refl x)

theorem conj_mem (h : ElevenOneHyp hC) {g : G} (hg : g ∈ Subgroup.centralizer {hC.d})
    {x : G} (hx : x ∈ DalphaStar D hC.alpha) : g * x * g⁻¹ ∈ DalphaStar D hC.alpha := by
  rw [h.alpha_eq] at hx ⊢
  have hgu : g * hC.d * g⁻¹ = hC.d := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [this]; group
  have himg : (fun y => g * y * g⁻¹) '' ({hC.d} : Set G) = {hC.d} := by
    rw [Set.image_singleton, hgu]
  have hconj := DalphaStar.conj hC.setup.normal hx g
  rwa [himg] at hconj

theorem perp_lift (h : ElevenOneHyp hC) {g : G} (hg : g ∈ Subgroup.centralizer {hC.d})
    {a : G} (ha : a ∈ DalphaStar D hC.alpha)
    (hfix : ∀ b ∈ DalphaStar D hC.alpha, Commute a b → g * b * g⁻¹ = b) :
    (∀ x ∈ DalphaStar D hC.alpha, g * x * g⁻¹ = x) ∨
      ∀ x ∈ DalphaStar D hC.alpha, g * x * g⁻¹ = a * x * a⁻¹ := by
  set K := CFSG.solvableRadical (Halpha D hC.alpha) with hK
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
  have hKchar : K.map φ.toMonoidHom = K :=
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
    · rintro z ⟨w, hw, rfl⟩
      rw [imageClass] at hw ⊢
      obtain ⟨y, hy, rfl⟩ := hw
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
  let aH : Halpha D hC.alpha := ⟨a, Subgroup.subset_closure ha⟩
  have haH : aH ∈ DstarH hC := (mem_DstarH_iff hC).mpr ha
  have habar : QuotientGroup.mk' K aH ∈ imageClass hC := ⟨aH, haH, rfl⟩
  have hfixbar : ∀ b : Halpha D hC.alpha ⧸ K, b ∈ imageClass hC →
      Commute (QuotientGroup.mk' K aH) b → φ' b = b := by
    rintro b ⟨bH, hbH, rfl⟩ hcomm
    rw [hφ'apply]
    have hcommH : Commute aH bH := (commute_iff h haH hbH).mpr hcomm
    have hcommG : Commute a (bH : G) := hcommH.map (Subgroup.subtype (Halpha D hC.alpha))
    have hbD : (bH : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp hbH
    have hfixb : g * (bH : G) * g⁻¹ = (bH : G) := hfix (bH : G) hbD hcommG
    have hb : φ bH = bH := Subtype.ext (by rw [hφcoe]; exact hfixb)
    rw [hb]
  rcases h.facts.perp φ' hφ'Θ (QuotientGroup.mk' K aH) habar hfixbar with htriv | hadj
  · left
    intro x hx
    have hxH : (⟨x, Subgroup.subset_closure hx⟩ : Halpha D hC.alpha) ∈ DstarH hC :=
      (mem_DstarH_iff hC).mpr hx
    have hφxH : φ ⟨x, Subgroup.subset_closure hx⟩ ∈ DstarH hC := by
      rw [← hφDstar]; exact Set.mem_image_of_mem φ hxH
    have hπeq : QuotientGroup.mk' K (φ ⟨x, Subgroup.subset_closure hx⟩) =
        QuotientGroup.mk' K ⟨x, Subgroup.subset_closure hx⟩ := by
      rw [← hφ'apply, htriv]
    have hcong := h.injOn hφxH hxH hπeq
    have h2 : (φ ⟨x, Subgroup.subset_closure hx⟩ : G) = x := Subtype.ext_iff.mp hcong
    rw [hφcoe] at h2
    simpa using h2
  · right
    intro x hx
    have hxH : (⟨x, Subgroup.subset_closure hx⟩ : Halpha D hC.alpha) ∈ DstarH hC :=
      (mem_DstarH_iff hC).mpr hx
    have hφxH : φ ⟨x, Subgroup.subset_closure hx⟩ ∈ DstarH hC := by
      rw [← hφDstar]; exact Set.mem_image_of_mem φ hxH
    have haxH : aH * ⟨x, Subgroup.subset_closure hx⟩ * aH⁻¹ ∈ DstarH hC :=
      DstarH_conj_mem hC (h := aH) (x := ⟨x, Subgroup.subset_closure hx⟩) hxH
    have hπeq : QuotientGroup.mk' K (φ ⟨x, Subgroup.subset_closure hx⟩) =
        QuotientGroup.mk' K (aH * ⟨x, Subgroup.subset_closure hx⟩ * aH⁻¹) := by
      rw [← hφ'apply, hadj]
      simp only [map_mul, map_inv]
    have hcong := h.injOn hφxH haxH hπeq
    have h2 : (φ ⟨x, Subgroup.subset_closure hx⟩ : G) =
        ((aH * ⟨x, Subgroup.subset_closure hx⟩ * aH⁻¹ : Halpha D hC.alpha) : G) :=
      congrArg Subtype.val hcong
    rw [hφcoe] at h2
    simpa using h2

end ElevenOneHyp

end CFSG.OddTranspositions.PartThree
