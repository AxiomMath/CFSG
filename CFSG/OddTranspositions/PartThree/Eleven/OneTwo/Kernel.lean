module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.ConjShared
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Radical
import CFSG.OddTranspositions.SixNineUnconditional
import CFSG.OddTranspositions.PartFour.LineTransport
import CFSG.OddTranspositions.PartThree.Nine.Setup
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LieType.SteinbergBRMulEquivCores
public import Certificates.Kernel.SporSch.Th.Key2311
public import Certificates.Kernel.SporSch.Th.Orb2315
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section Kernel

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenTwoHyp

variable {hC : HypothesisC D}

private theorem conj (h : ElevenTwoHyp hC) (g : G) :
    ElevenTwoHyp (hC.conj g) where
  rad := h.rad
  center := by
    rw [← conjRadical_map hC g, h.center]
    exact Subgroup.map_center_eq (conjEquiv hC g)
  facts :=
    O4MinusFacts.of_mulEquiv
      (QuotientGroup.congr (CFSG.solvableRadical (Halpha D hC.alpha))
        (CFSG.solvableRadical (Halpha D (hC.conj g).alpha)) (conjEquiv hC g)
        (conjRadical_map hC g)) (imageClass_conj hC g) h.facts

private theorem perp_eq (h : ElevenTwoHyp hC) :
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

private theorem inter_D_centralizer_eq (h : ElevenTwoHyp hC) {a : G} (ha1 : a ≠ 1)
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

omit [Finite G] in
private theorem commute_of_mem_alpha_of_mem_DalphaStar (hC : HypothesisC D) {a e : G}
    (ha : a ∈ hC.alpha) (he : e ∈ DalphaStar D hC.alpha) : Commute a e := by
  obtain ⟨γ, hγ, heγ⟩ := he
  exact (mem_Dalpha_iff.mp hγ).2.2.2 a ha e heγ

omit [Finite G] in
private theorem Halpha_le_centralizer_of_forall_commute (hC : HypothesisC D) {y : G}
    (hy : ∀ e ∈ DalphaStar D hC.alpha, Commute e y) :
    Halpha D hC.alpha ≤ Subgroup.centralizer ({y} : Set G) := by
  rw [Halpha, Subgroup.closure_le]
  intro e he
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact (hy e he).eq

private theorem exists_not_commute_DalphaStar (h : ElevenTwoHyp hC) :
    ∃ x ∈ DalphaStar D hC.alpha, ∃ y ∈ DalphaStar D hC.alpha, ¬ Commute x y := by
  obtain ⟨x₀, hx₀⟩ := DstarH_nonempty hC
  have hx₀img : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x₀ ∈
      imageClass hC := ⟨x₀, hx₀, rfl⟩
  obtain ⟨z, hz, hnc⟩ := h.facts.noncomm _ hx₀img
  obtain ⟨y₀, hy₀, rfl⟩ := hz
  have hncG : ¬ Commute (x₀ : G) (y₀ : G) := by
    intro hc
    apply hnc
    have hcH : Commute x₀ y₀ := by
      apply Subtype.ext
      simpa using hc.eq
    exact hcH.map (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
  exact ⟨(x₀ : G), (mem_DstarH_iff hC).mp hx₀, (y₀ : G),
    (mem_DstarH_iff hC).mp hy₀, hncG⟩

private theorem mem_block_of_commute_imp_two (h : ElevenTwoHyp hC) {β : Set G}
    (hβ : β ∈ blockClass hC.alpha) {x y : G} (hx : x ∈ β) (hy : y ∈ D)
    (hcomm : ∀ e ∈ D, Commute e x → Commute e y) : y ∈ β := by
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := exists_not_commute_DalphaStar h
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hβ
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  have hy₀D : g⁻¹ * y * g⁻¹⁻¹ ∈ D := hC.setup.conj_mem g⁻¹ hy
  rw [inv_inv] at hy₀D
  refine ⟨g⁻¹ * y * g, ?_, by group⟩
  have hEcomm : ∀ e ∈ DalphaStar D hC.alpha, Commute e (g⁻¹ * y * g) := by
    intro e he
    have heD : e ∈ D := DalphaStar_subset hC.isBlock_alpha he
    have hex : Commute (g * e * g⁻¹) (g * x₀ * g⁻¹) :=
      (commute_of_mem_alpha_of_mem_DalphaStar hC hx₀ he).symm.conj g
    have hey := (hcomm (g * e * g⁻¹) (hC.setup.conj_mem g heD) hex).conj g⁻¹
    rwa [inv_inv, show g⁻¹ * (g * e * g⁻¹) * g = e by group] at hey
  rw [hC.alpha_eq_normSet_diff, ← hC.DalphaStar_alpha]
  refine ⟨⟨hy₀D, fun e => ⟨fun he => ?_, fun he => ?_⟩⟩, fun hy₀ => ?_⟩
  · rw [(hEcomm e he).symm.eq, mul_inv_cancel_right]
    exact he
  · have hc := (hEcomm _ he).eq
    have : e = (g⁻¹ * y * g) * e * (g⁻¹ * y * g)⁻¹ := by
      calc e = (g⁻¹ * y * g)⁻¹ * ((g⁻¹ * y * g) * e * (g⁻¹ * y * g)⁻¹) *
            (g⁻¹ * y * g) := by group
        _ = (g⁻¹ * y * g) * e * (g⁻¹ * y * g)⁻¹ := by
            rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact he
  · have hcent : Halpha D hC.alpha ≤ Subgroup.centralizer ({g⁻¹ * y * g} : Set G) :=
      Halpha_le_centralizer_of_forall_commute hC hEcomm
    have hfix : ∀ c ∈ DalphaStar D hC.alpha, c = g⁻¹ * y * g := by
      intro c hc
      obtain ⟨k, hk, hkc⟩ := hC.Halpha_transitive _ hy₀ c hc
      rw [← hkc, Subgroup.mem_centralizer_singleton_iff.mp (hcent hk), mul_inv_cancel_right]
    exact hab₀ (by rw [hfix a₀ ha₀, hfix b₀ hb₀])

private theorem commute_d_of_mem_centralizer (h : ElevenTwoHyp hC) {a : G}
    (haC : a ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G)) :
    Commute a hC.d := by
  have haE : ∀ e ∈ DalphaStar D hC.alpha, Commute a e := by
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp haC e (Subgroup.subset_closure he)).symm
  set w : G := a * hC.d * a⁻¹ with hw
  have hwD : w ∈ D := hw ▸ hC.setup.conj_mem a hC.hd
  have hwE : ∀ e ∈ DalphaStar D hC.alpha, Commute w e := by
    intro e he
    have hue : Commute hC.d e := (hC.DalphaStar_subset_commute he).2.symm
    have hae : Commute a e := haE e he
    have hconj := hue.conj a
    rw [← hw, show a * e * a⁻¹ = e by rw [hae.eq]; group] at hconj
    exact hconj
  have hwNorm : w ∈ Subgroup.normalizer hC.E := by
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ DalphaStar D hC.alpha := by
        rw [hC.DalphaStar_alpha]; exact hx
      rw [MulAut.conj_apply]
      rw [show w * x * w⁻¹ = x by rw [(hwE x hx').eq]; group]
      exact hx
    · intro he
      have he' : e ∈ DalphaStar D hC.alpha := by
        rw [hC.DalphaStar_alpha]; exact he
      refine ⟨e, he, ?_⟩
      rw [MulAut.conj_apply]
      rw [show w * e * w⁻¹ = e by rw [(hwE e he').eq]; group]
  have hwAlphaOrE : w ∈ hC.alpha ∪ hC.E := by
    by_cases hE : w ∈ hC.E
    · exact Or.inr hE
    · exact Or.inl (by
        rw [hC.alpha_eq_normSet_diff]
        exact ⟨⟨hwD, hwNorm⟩, hE⟩)
  have huNotMem : hC.d ∉ DalphaStar D hC.alpha := d_not_mem_DalphaStar hC
  have hwComm : ∀ e ∈ D, Commute e hC.d → Commute e w := by
    intro e heD hed
    have heu : e ∈ D ∩ (Subgroup.centralizer ({hC.d} : Set G) : Set G) :=
      ⟨heD, Subgroup.mem_centralizer_singleton_iff.mpr hed⟩
    rw [perp_eq h] at heu
    rcases heu with rfl | heE
    · rcases hwAlphaOrE with hwAlpha | hwE'
      · have hw_eq : w = hC.d := by
          rw [h.alpha_eq] at hwAlpha
          simpa using hwAlpha
        rw [hw_eq]
      · have hwDstar : w ∈ DalphaStar D hC.alpha := by
          rw [hC.DalphaStar_alpha]; exact hwE'
        exact (hC.DalphaStar_subset_commute hwDstar).2.symm
    · exact (hwE e heE).symm
  have hwAlpha : w ∈ hC.alpha :=
    mem_block_of_commute_imp_two h (mem_blockClass_self hC.alpha) hC.d_mem_alpha hwD hwComm
  have hw_eq : w = hC.d := by
    rw [h.alpha_eq] at hwAlpha
    simpa using hwAlpha
  calc a * hC.d = w * a := by rw [hw]; group
    _ = hC.d * a := by rw [hw_eq]

private theorem commute_iff (h : ElevenTwoHyp hC) {x y : Halpha D hC.alpha}
    (hx : x ∈ DstarH hC) (hy : y ∈ DstarH hC) :
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

private theorem conj_mem (h : ElevenTwoHyp hC) {g : G}
    (hg : g ∈ Subgroup.centralizer {hC.d}) {x : G} (hx : x ∈ DalphaStar D hC.alpha) :
    g * x * g⁻¹ ∈ DalphaStar D hC.alpha := by
  rw [h.alpha_eq] at hx ⊢
  have hgu : g * hC.d * g⁻¹ = hC.d := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [this]; group
  have himg : (fun y => g * y * g⁻¹) '' ({hC.d} : Set G) = {hC.d} := by
    rw [Set.image_singleton, hgu]
  have hconj := DalphaStar.conj hC.setup.normal hx g
  rwa [himg] at hconj

private theorem perp_lift (h : ElevenTwoHyp hC) {g : G}
    (hg : g ∈ Subgroup.centralizer {hC.d}) {a : G} (ha : a ∈ DalphaStar D hC.alpha)
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

private theorem false_of_centralizer_eq (h : ElevenTwoHyp hC) {v : G}
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
    (commute_iff h hyH hvDstar).mp hyvH
  exact hnc hcomm.symm

omit [Finite G] in
private theorem centralizes_union_of_centralizes_Dv {g a' : G}
    (hd : Commute a' ((hC.conj g).d))
    (hfix : ∀ x ∈ DalphaStar D (hC.conj g).alpha, a' * x * a'⁻¹ = x) :
    ∀ x ∈ ({(hC.conj g).d} : Set G) ∪ DalphaStar D (hC.conj g).alpha, Commute a' x := by
  intro x hx
  rcases hx with hx | hx
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hd
  · exact mul_inv_eq_iff_eq_mul.mp (hfix x hx)

theorem centralizer_Halpha (h : ElevenTwoHyp hC) :
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
  have hauComm : Commute a hC.d := commute_d_of_mem_centralizer h haC
  have ha : ∀ x ∈ ({hC.d} : Set G) ∪ DalphaStar D hC.alpha, Commute a x := by
    intro x hx
    rcases hx with rfl | hxE
    · exact hauComm
    · exact (Subgroup.mem_centralizer_iff.mp haC x (Subgroup.subset_closure hxE)).symm
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
  have h' : ElevenTwoHyp hC' := h.conj g
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
  · have hdav : Commute a ((hC.conj g).d) := by
      rw [hC'd]; exact hav
    exact false_of_centralizer_eq h hvE
      (hperp_of a ha1 ha (centralizes_union_of_centralizes_Dv (hC := hC) (g := g) hdav htriv))
  · have hduv : Commute hC.d v := (hC.DalphaStar_subset_commute hvE).2.symm
    have hdduv : Commute (hC.d * a) ((hC.conj g).d) := by
      rw [hC'd]
      exact hduv.mul_left hav
    have ha'_fix : ∀ x ∈ DalphaStar D hC'.alpha, (hC.d * a) * x * (hC.d * a)⁻¹ = x := by
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
      rcases hx with rfl | hxE
      · exact (Commute.refl hC.d).mul_left hauComm
      · exact (Subgroup.mem_centralizer_iff.mp ha'C x (Subgroup.subset_closure hxE)).symm
    exact false_of_centralizer_eq h hvE
      (hperp_of (hC.d * a) ha'1 ha'u
        (centralizes_union_of_centralizes_Dv (hC := hC) (g := g) hdduv ha'_fix))

theorem d_not_mem_Halpha (h : ElevenTwoHyp hC) : hC.d ∉ Halpha D hC.alpha := by
  intro hdH
  let uH : Halpha D hC.alpha := ⟨hC.d, hdH⟩
  have hdZ : uH ∈ Subgroup.center (Halpha D hC.alpha) := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (d_mem_centralizer hC) (x : G) x.2)
  have hdR : uH ∈ CFSG.solvableRadical (Halpha D hC.alpha) := by
    rw [h.center]
    exact hdZ
  have hbot : CFSG.solvableRadical (Halpha D hC.alpha) = ⊥ := h.radical_eq_bot
  have hu1 : uH = 1 := by simpa [hbot] using hdR
  have hd1 : hC.d = 1 := by
    simpa [uH] using congrArg (fun z : Halpha D hC.alpha => (z : G)) hu1
  exact hC.setup.oddT.ne_one hC.hd hd1

theorem centralizer_d (h : ElevenTwoHyp hC) :
    Subgroup.centralizer {hC.d} = Subgroup.zpowers hC.d ⊔ Halpha D hC.alpha := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxN : x ∈ Subgroup.normalizer (Halpha D hC.alpha) := by
      have hxNu : x ∈ Subgroup.normalizer ({hC.d} : Set G) :=
        Subgroup.centralizer_le_normalizer _ hx
      have hxNa : x ∈ Subgroup.normalizer hC.alpha := by
        rw [h.alpha_eq]; exact hxNu
      exact normalizer_le_normalizer_Halpha hC.setup.normal hxNa
    have hconj : ⇑(MulAut.conj x) '' (Halpha D hC.alpha : Set G) =
        (Halpha D hC.alpha : Set G) :=
      Subgroup.mem_normalizer_iff_conj_image_eq.mp hxN
    have hconj_inv : ⇑(MulAut.conj x⁻¹) '' (Halpha D hC.alpha : Set G) =
        (Halpha D hC.alpha : Set G) :=
      Subgroup.mem_normalizer_iff_conj_image_eq.mp (Subgroup.inv_mem _ hxN)
    let φ : MulAut (Halpha D hC.alpha) :=
      { toFun := fun y => ⟨x * (y : G) * x⁻¹, by
          have hy : MulAut.conj x (y : G) ∈
              ⇑(MulAut.conj x) '' (Halpha D hC.alpha : Set G) :=
            Set.mem_image_of_mem _ y.2
          rw [hconj] at hy
          rw [MulAut.conj_apply] at hy
          exact hy⟩
        invFun := fun y => ⟨x⁻¹ * (y : G) * x, by
          have hy : MulAut.conj x⁻¹ (y : G) ∈
              ⇑(MulAut.conj x⁻¹) '' (Halpha D hC.alpha : Set G) :=
            Set.mem_image_of_mem _ y.2
          rw [hconj_inv] at hy
          rw [MulAut.conj_apply, inv_inv] at hy
          exact hy⟩
        left_inv := fun y => by ext; group
        right_inv := fun y => by ext; group
        map_mul' := fun y z => by ext; simp only [Subgroup.coe_mul]; group }
    have hφcoe : ∀ y : Halpha D hC.alpha, (φ y : G) = x * (y : G) * x⁻¹ := fun _ => rfl
    have hφDstar : φ '' DstarH hC = DstarH hC := by
      apply Set.Subset.antisymm
      · rintro z ⟨y, hy, rfl⟩
        rw [mem_DstarH_iff, hφcoe]
        exact conj_mem h hx ((mem_DstarH_iff hC).mp hy)
      · intro z hz
        have hzD : (z : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp hz
        have hxinv : x⁻¹ ∈ Subgroup.centralizer {hC.d} := Subgroup.inv_mem _ hx
        have hyD : x⁻¹ * (z : G) * x ∈ DalphaStar D hC.alpha := by
          simpa only [inv_inv] using conj_mem h hxinv hzD
        let y : Halpha D hC.alpha := ⟨x⁻¹ * (z : G) * x, Subgroup.subset_closure hyD⟩
        have hymem : y ∈ DstarH hC := (mem_DstarH_iff hC).mpr hyD
        refine ⟨y, hymem, ?_⟩
        apply Subtype.ext
        rw [hφcoe]
        change x * (x⁻¹ * (z : G) * x) * x⁻¹ = (z : G)
        group
    obtain ⟨g, hg⟩ := h.factsH.aut φ hφDstar
    have hgconj : ∀ y : Halpha D hC.alpha, x * (y : G) * x⁻¹ = (g : G) * (y : G) * (g : G)⁻¹ := by
      intro y
      have := congrArg Subtype.val (hg y)
      simpa [hφcoe] using this
    have hcent : (g : G)⁻¹ * x ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hgy : x * y * x⁻¹ = (g : G) * y * (g : G)⁻¹ := hgconj ⟨y, hy⟩
      calc y * ((g : G)⁻¹ * x) = (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * x := by group
        _ = (g : G)⁻¹ * (x * y * x⁻¹) * x := by rw [← hgy]
        _ = ((g : G)⁻¹ * x) * y := by group
    have hz : (g : G)⁻¹ * x ∈ Subgroup.zpowers hC.d := by
      rw [← centralizer_Halpha h]
      exact hcent
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hx_eq : x = (g : G) * hC.d ^ n := by
      calc x = (g : G) * ((g : G)⁻¹ * x) := by group
        _ = (g : G) * hC.d ^ n := by rw [← hn]
    rw [hx_eq, sup_comm]
    exact Subgroup.mul_mem_sup (show (g : G) ∈ Halpha D hC.alpha from g.2)
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers hC.d) n)

  · intro x hx
    have hH : Halpha D hC.alpha ≤ Subgroup.centralizer {hC.d} := by
      rw [Halpha, Subgroup.closure_le]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hC.DalphaStar_subset_commute hy).2
    have hz : Subgroup.zpowers hC.d ≤ Subgroup.centralizer {hC.d} := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl _)
    exact sup_le hz hH hx

theorem card_centralizer_d (h : ElevenTwoHyp hC) :
    Nat.card (Subgroup.centralizer {hC.d}) = 31200 := by
  classical
  have hsup : Nat.card ↥(Subgroup.zpowers hC.d ⊔ Halpha D hC.alpha) = 31200 := by
    have hcomm : ∀ y ∈ Subgroup.zpowers hC.d, ∀ z ∈ Halpha D hC.alpha,
        y * z = z * y := by
      intro y hy z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hd : Commute hC.d z :=
        (Subgroup.mem_centralizer_iff.mp (d_mem_centralizer hC) z hz).symm
      exact (hd.zpow_left n).eq
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers hC.d) (Halpha D hC.alpha) hcomm).1
    have hinf : Subgroup.zpowers hC.d ⊓ Halpha D hC.alpha = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      have hyz : y ∈ Subgroup.zpowers hC.d := hy.1
      have hyH : y ∈ Halpha D hC.alpha := hy.2
      have hy_range : y ∈ (Finset.range (orderOf hC.d)).image (hC.d ^ ·) :=
        (mem_zpowers_iff_mem_range_orderOf).mp hyz
      rw [hC.setup.oddT.orderOf_eq_two hC.hd, Finset.mem_image] at hy_range
      obtain ⟨k, hk, rfl⟩ := hy_range
      rw [Finset.mem_range] at hk
      interval_cases k
      · simp
      · exact absurd (by simpa using hyH) (d_not_mem_Halpha h)
    rw [hinf, Subgroup.card_bot, mul_one] at hcard
    have hH : Nat.card (Halpha D hC.alpha) = 15600 := h.factsH.card
    have hz : Nat.card (Subgroup.zpowers hC.d) = 2 := by
      rw [Nat.card_zpowers, hC.setup.oddT.orderOf_eq_two hC.hd]
    rw [hH, hz] at hcard
    omega
  rw [centralizer_d h]
  exact hsup

theorem ncard_commSet (h : ElevenTwoHyp hC) : (commSet D hC.d).ncard = 65 := by
  rw [← CFSG.OddTranspositions.PartThree.Nine.DalphaStar_eq_commSet hC h.alpha_eq]
  have h1 : (DalphaStar D hC.alpha).ncard = (DstarH hC).ncard := by
    refine Set.ncard_congr
      (fun x hx => (⟨x, Subgroup.subset_closure hx⟩ : Halpha D hC.alpha)) ?_ ?_ ?_
    · intro x hx
      exact hx
    · intro x y hx hy hxy
      exact Subtype.ext_iff.mp hxy
    · intro y hy
      exact ⟨(y : G), (mem_DstarH_iff hC).mp hy, rfl⟩
  rw [h1]
  have h2 : (DstarH hC).ncard = (imageClass hC).ncard := by
    rw [imageClass]
    exact h.injOn.ncard_image.symm
  rw [h2, h.facts.ncard]

end ElevenTwoHyp

end Kernel

end CFSG.OddTranspositions.PartThree
