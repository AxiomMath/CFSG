module

public import CFSG.OddTranspositions.HypothesisC
public import CFSG.OddTranspositions.SevenThreeQuotient
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def DstarH (hC : HypothesisC (G := G) D) : Set (Halpha D hC.alpha) :=
  {x | (x : G) ∈ DalphaStar D hC.alpha}

theorem mem_DstarH_iff (hC : HypothesisC (G := G) D) {x : Halpha D hC.alpha} :
    x ∈ DstarH hC ↔ (x : G) ∈ DalphaStar D hC.alpha := Iff.rfl

theorem DstarH_conj_mem (hC : HypothesisC (G := G) D)
    {h x : Halpha D hC.alpha} (hx : x ∈ DstarH hC) :
    h * x * h⁻¹ ∈ DstarH hC := by
  have hhn : (h : G) ∈ Subgroup.normalizer (DalphaStar D hC.alpha) :=
    Halpha_le_normalizer hC.setup.normal h.2
  have hx' : (h : G) * (x : G) * (h : G)⁻¹ ∈ DalphaStar D hC.alpha :=
    (hhn (x : G)).mp hx
  simpa [DstarH] using hx'

theorem DstarH_transitive (hC : HypothesisC (G := G) D)
    {x y : Halpha D hC.alpha} (hx : x ∈ DstarH hC) (hy : y ∈ DstarH hC) :
    ∃ h : Halpha D hC.alpha, h * x * h⁻¹ = y := by
  obtain ⟨h, hh, hxy⟩ := hC.Halpha_transitive (x := (x : G)) (y := (y : G))
    ((mem_DstarH_iff hC).mp hx) ((mem_DstarH_iff hC).mp hy)
  exact ⟨⟨h, hh⟩, Subtype.ext (by simpa using hxy)⟩

theorem DstarH_nonempty (hC : HypothesisC (G := G) D) : (DstarH hC).Nonempty := by
  obtain ⟨e, he⟩ := OddLocal.nonempty hC.hE
  have he' : e ∈ DalphaStar D hC.alpha := by
    rw [hC.DalphaStar_alpha]
    exact he
  exact ⟨⟨e, Subgroup.subset_closure he'⟩, he'⟩

theorem DstarH_isClass (hC : HypothesisC (G := G) D) :
    ∃ d₀ : Halpha D hC.alpha, DstarH hC = {g | IsConj d₀ g} := by
  obtain ⟨d₀, hd₀⟩ := DstarH_nonempty hC
  refine ⟨d₀, ?_⟩
  ext g
  constructor
  · intro hg
    simp only [Set.mem_setOf_eq]
    obtain ⟨h, hh, hgh⟩ :=
      hC.Halpha_transitive (x := (g : G)) (y := (d₀ : G))
        ((mem_DstarH_iff hC).mp hg) ((mem_DstarH_iff hC).mp hd₀)
    rw [isConj_iff]
    refine ⟨⟨h⁻¹, (Halpha D hC.alpha).inv_mem hh⟩, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [← hgh]
    group
  · intro hg
    simp only [Set.mem_setOf_eq] at hg
    rw [isConj_iff] at hg
    obtain ⟨c, hc⟩ := hg
    rw [← hc]
    exact DstarH_conj_mem hC (h := c) (x := d₀) hd₀

theorem DstarH_closure_eq_top (hC : HypothesisC (G := G) D) :
    Subgroup.closure (DstarH hC) = ⊤ :=
  Subgroup.closure_preimage_eq_top (s := DalphaStar D hC.alpha)

theorem DstarH_isOddTransp (hC : HypothesisC (G := G) D) :
    IsOddTransp (DstarH hC) := by
  constructor
  · intro x hx
    rw [← Subgroup.orderOf_coe]
    exact hC.setup.oddT.1 (x : G)
      (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hx))
  · intro x hx y hy
    have hcoe : orderOf (x * y) = orderOf ((x : G) * (y : G)) := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rw [hcoe]
    exact hC.setup.oddT.2 (x : G)
      (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hx))
      (y : G) (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hy))

@[expose] def imageClass (hC : HypothesisC (G := G) D) :
    Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
  (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) '' DstarH hC

theorem imageClass_nonempty (hC : HypothesisC (G := G) D) :
    (imageClass hC).Nonempty := by
  obtain ⟨x, hx⟩ := DstarH_nonempty hC
  exact ⟨QuotientGroup.mk' _ x, x, hx, rfl⟩

theorem imageClass_isClass (hC : HypothesisC (G := G) D) :
    ∃ d₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha),
      imageClass hC = {x | IsConj d₀ x} := by
  obtain ⟨d₀, hclass⟩ := DstarH_isClass hC
  obtain ⟨c, hc⟩ := image_isClass_quotient hclass
    (CFSG.solvableRadical (Halpha D hC.alpha))
  exact ⟨c, by simpa [imageClass] using hc⟩

theorem imageClass_involutions (hC : HypothesisC (G := G) D)
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha)) :
    ∀ x ∈ imageClass hC, orderOf x = 2 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyD : (y : G) ∈ D :=
    DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hy)
  have hordy : orderOf y = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hC.setup.oddT.1 (y : G) hyD
  have hdvd :
      orderOf (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y) ∣ 2 := by
    have h := orderOf_map_dvd
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) y
    rwa [hordy] at h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exfalso
    have hyM : y ∈ CFSG.solvableRadical (Halpha D hC.alpha) := by
      have hq1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y = 1 := by
        rw [← orderOf_eq_one_iff]
        exact h1
      exact (QuotientGroup.eq_one_iff y).mp hq1
    have hsub : DstarH hC ⊆ CFSG.solvableRadical (Halpha D hC.alpha) := by
      intro z hz
      obtain ⟨h, hh, hzy⟩ :=
        hC.Halpha_transitive (x := (z : G)) (y := (y : G))
          ((mem_DstarH_iff hC).mp hz) ((mem_DstarH_iff hC).mp hy)
      have hz_eq : z = (⟨h, hh⟩ : Halpha D hC.alpha)⁻¹ * y * (⟨h, hh⟩ : Halpha D hC.alpha) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [← hzy]
        group
      rw [hz_eq]
      simpa using (inferInstance : (CFSG.solvableRadical (Halpha D hC.alpha)).Normal).conj_mem
        y hyM (⟨h, hh⟩ : Halpha D hC.alpha)⁻¹
    have hle : Subgroup.closure (DstarH hC) ≤ CFSG.solvableRadical (Halpha D hC.alpha) :=
      (Subgroup.closure_le _).mpr hsub
    have htop : CFSG.solvableRadical (Halpha D hC.alpha) = ⊤ :=
      top_le_iff.mp (DstarH_closure_eq_top hC ▸ hle)
    haveI : Group.IsSolvable (CFSG.solvableRadical (Halpha D hC.alpha)) :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
    have hsurj :
        Function.Surjective (Subgroup.subtype (CFSG.solvableRadical (Halpha D hC.alpha))) := by
      rw [← MonoidHom.range_eq_top, Subgroup.range_subtype, htop]
    exact hHns (Group.isSolvable_of_surjective
      (f := Subgroup.subtype (CFSG.solvableRadical (Halpha D hC.alpha))) hsurj)
  · exact h2

theorem imageClass_isOddTransp (hC : HypothesisC (G := G) D)
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha)) :
    IsOddTransp (imageClass hC) := by
  have hne : ∀ x ∈ DstarH hC,
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x ≠ 1 := by
    intro x hx hx1
    have h2 : orderOf (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x) = 2 :=
      imageClass_involutions hC hHns _
        ⟨x, hx, rfl⟩
    rw [hx1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  simpa [imageClass] using image_isOddTransp_quotient
    (Θ := DstarH hC) (CFSG.solvableRadical (Halpha D hC.alpha))
    (DstarH_isOddTransp hC) hne

theorem imageClass_gen (hC : HypothesisC (G := G) D) :
    Subgroup.closure (imageClass hC) = ⊤ := by
  simpa [imageClass] using image_closure_eq_top_quotient
    (Θ := DstarH hC) (CFSG.solvableRadical (Halpha D hC.alpha))
    (DstarH_closure_eq_top hC)

theorem setup_quotient (hC : HypothesisC (G := G) D)
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha)) :
    CFSG.Timmesfeld.Bridge.Asc72.Setup
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC) :=
  { isClass := imageClass_isClass hC
    oddT := imageClass_isOddTransp hC hHns
    gen := imageClass_gen hC }

theorem solvableRadical_quotient_H (hC : HypothesisC (G := G) D) :
    CFSG.solvableRadical
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) = ⊥ :=
  CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_quotient

end CFSG.OddTranspositions
