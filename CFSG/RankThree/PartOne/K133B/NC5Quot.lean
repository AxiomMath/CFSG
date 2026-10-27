module

public import CFSG.RankThree.PartOne.K133B.NC5Frame
public import CFSG.RankThree.PartOne.K133B.NC5Lift
public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.S12.Equivariance

public section

namespace CFSG.RankThree.PartOne.K133B

open Matrix CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.LocalRank CFSG.RankThree.PartOne

theorem normalizer_theta_of_normalizer {G : Type} [Group G] [Finite G] {I : Subgroup G} {f : G}
    (hfN : f ∈ Subgroup.normalizer (I : Set G)) :
    f ∈ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 5) I : Set G) := by
  have h1 : conjBy f (inSubgroup (aschbacherSolvableCore 5) I) =
      inSubgroup (aschbacherSolvableCore 5) I := by
    rw [← inSubgroup_theta_conjBy Nat.prime_five f I, Equivariance.conjBy_eq_of_mem_normalizer hfN]
  have key : ∀ x : G, f⁻¹ * x * f ∈ inSubgroup (aschbacherSolvableCore 5) I ↔
      x ∈ inSubgroup (aschbacherSolvableCore 5) I := fun x => by
    have := SetLike.ext_iff.1 h1 x
    rw [conjBy, Subgroup.mem_map_equiv] at this
    simpa [MulAut.conj_symm_apply] using this
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [← key (f * y * f⁻¹)]
  have : f⁻¹ * (f * y * f⁻¹) * f = y := by group
  rw [this]

theorem le_normalizer_theta_sup {G : Type} [Group G] [Finite G] {I : Subgroup G} {f : G}
    (hfN : f ∈ Subgroup.normalizer (I : Set G)) :
    I ⊔ Subgroup.zpowers f ≤
      Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 5) I : Set G) := by
  obtain ⟨hΘI, hΘn⟩ := theta_le_and_normal (G := G) 5 I
  exact sup_le ((Subgroup.normal_subgroupOf_iff_le_normalizer hΘI).1 hΘn)
    (Subgroup.zpowers_le.2 (normalizer_theta_of_normalizer hfN))

section Main

variable {F : Type} [Field F] {n : ℕ}

theorem four_le_twoLocalOddRank_of_outer {G : Type} [Group G] [Finite G] {I : Subgroup G} {f : G}
    (hfN : f ∈ Subgroup.normalizer (I : Set G)) (hf5 : f ^ 5 = 1) (hfI : f ∉ I)
    (hU : UnitaryFieldData 2 n F) (h5 : 5 ∣ 2 ^ n + 1)
    (ψ : gamma5 hU ≃* (↥I ⧸ aschbacherSolvableCore 5 ↥I))
    (hcen : Nat.card (Subgroup.center (↥I ⧸ aschbacherSolvableCore 5 ↥I)) = 5)
    {S₀ : Subgroup G} (hS₀I : S₀ ≤ I) (hS₀2 : IsPGroup 2 S₀)
    (hS₀θ : ¬ S₀ ≤ inSubgroup (aschbacherSolvableCore 5) I)
    (hfS : ∀ s ∈ S₀, f * s = s * f) :
    4 ≤ CFSG.twoLocalOddRank ↥(I ⊔ Subgroup.zpowers f) := by
  classical
  have hp5 : Nat.Prime 5 := Nat.prime_five
  have : Fact (Nat.Prime 5) := ⟨hp5⟩
  set θ : Subgroup ↥I := aschbacherSolvableCore 5 ↥I with hθ
  set Θ : Subgroup G := inSubgroup (aschbacherSolvableCore 5) I with hΘ
  set J : Subgroup G := I ⊔ Subgroup.zpowers f with hJ
  have hIJ : I ≤ J := le_sup_left
  have hfJ : f ∈ J := Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  have hΘI : Θ ≤ I := (theta_le_and_normal (G := G) 5 I).1
  have hΘJ : Θ ≤ J := hΘI.trans hIJ
  have hmemΘ : ∀ y : ↥I, (y : G) ∈ Θ ↔ y ∈ θ := fun y =>
    Subgroup.mem_map_iff_mem I.subtype_injective
  have hNn : (Θ.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hΘJ).2 (le_normalizer_theta_sup hfN)
  obtain ⟨H, hGH, ρ, hρs, hρ1⟩ : ∃ (H : Type) (_ : Group H) (ρ : ↥J →* H),
      Function.Surjective ρ ∧ ∀ y : ↥J, ρ y = 1 ↔ (y : G) ∈ Θ :=
    ⟨↥J ⧸ Θ.subgroupOf J, inferInstance, QuotientGroup.mk' (Θ.subgroupOf J),
      QuotientGroup.mk'_surjective _, fun y => by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]⟩
  have : Finite H := Finite.of_surjective ρ hρs
  set φ : ↥I →* H := ρ.comp (Subgroup.inclusion hIJ) with hφ
  set L : Subgroup H := φ.range with hL
  have hφapp : ∀ y : ↥I, φ y = ρ (Subgroup.inclusion hIJ y) := fun y => rfl
  have hφ1 : ∀ y : ↥I, φ y = 1 ↔ y ∈ θ := fun y => by
    rw [← hmemΘ]
    exact hρ1 (Subgroup.inclusion hIJ y)
  have hker : φ.ker = θ := by
    ext y
    exact hφ1 y
  let e' : (↥I ⧸ θ) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  let ψ' : gamma5 hU ≃* ↥L := ψ.trans e'
  have hcenL : Nat.card (Subgroup.center ↥L) = 5 := by
    rw [← Subgroup.map_center_eq e', Subgroup.card_map_of_injective e'.injective]
    exact hcen
  have hperf : Group.IsPerfect (gamma5 hU) :=
    CFSG.RankThree.Classical.isPerfect_gramSU_one hU (by norm_num) (fun hh => absurd hh.1
      (by norm_num))
  set x : H := ρ ⟨f, hfJ⟩ with hx
  have hx5 : x ^ 5 = 1 := by
    rw [hx, ← map_pow]
    have : (⟨f, hfJ⟩ : ↥J) ^ 5 = 1 := Subtype.ext hf5
    rw [this, map_one]
  have hxL : x ∉ L := by
    rintro ⟨y, hy⟩
    have h1 : ρ ((Subgroup.inclusion hIJ y)⁻¹ * ⟨f, hfJ⟩) = 1 := by
      rw [map_mul, map_inv]
      exact inv_mul_eq_one.2 hy
    have h2 : y⁻¹ * f ∈ Θ := (hρ1 _).1 h1
    apply hfI
    have h3 : (y : G) * (y⁻¹ * f) ∈ I := I.mul_mem y.2 (hΘI h2)
    simpa using h3
  have hfN' : f⁻¹ ∈ Subgroup.normalizer (I : Set G) := (Subgroup.normalizer _).inv_mem hfN
  have hconj : ∀ y : ↥I, ∃ y' : ↥I, x * φ y * x⁻¹ = φ y' := fun y => by
    refine ⟨⟨f * y * f⁻¹, (Subgroup.mem_normalizer_iff.1 hfN y).1 y.2⟩, ?_⟩
    rw [hφapp, hφapp, hx, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hconj' : ∀ y : ↥I, ∃ y' : ↥I, x⁻¹ * φ y * x = φ y' := fun y => by
    refine ⟨⟨f⁻¹ * y * f, ?_⟩, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 hfN' y).1 y.2
      simpa using this
    · rw [hφapp, hφapp, hx, ← map_inv, ← map_mul, ← map_mul]
      congr 1
  have hxN : x ∈ Subgroup.normalizer (L : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨y', hy'⟩ := hconj y
      exact ⟨y', hy'.symm⟩
    · rintro ⟨y', hy'⟩
      obtain ⟨y'', hy''⟩ := hconj' y'
      refine ⟨y'', ?_⟩
      rw [← hy'', hy']
      group
  set S : Subgroup H := (S₀.subgroupOf I).map φ with hS
  have hSne : S ≠ ⊥ := by
    intro hbot
    apply hS₀θ
    intro s hs
    have hsI : s ∈ I := hS₀I hs
    have h1 : φ ⟨s, hsI⟩ ∈ S := Subgroup.mem_map_of_mem φ (show (⟨s, hsI⟩ : ↥I) ∈ S₀.subgroupOf I
      from hs)
    rw [hbot, Subgroup.mem_bot] at h1
    exact (hmemΘ ⟨s, hsI⟩).2 ((hφ1 _).1 h1)
  have hS2 : IsPGroup 2 S := (hS₀2.comap_subtype (K := I)).map φ
  have hSL : S ≤ L := Subgroup.map_le_range φ _
  have hxS : x ∈ Subgroup.normalizer (S : Set H) := by
    refine Subgroup.centralizer_le_normalizer (S : Set H) ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have hsI : (s : G) ∈ S₀ := hs
    have : (⟨f, hfJ⟩ : ↥J) * Subgroup.inclusion hIJ s = Subgroup.inclusion hIJ s * ⟨f, hfJ⟩ :=
      Subtype.ext (hfS _ hsI)
    simp only [hφ, hx, MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, this]
  obtain ⟨y, A, r, hy5, hyL, hAel, hAcard, hr, hAr, hyA, hyr⟩ :=
    su5_core' hU h5 ψ' hperf hcenL hx5 hxL hxN hSne hS2 hSL hxS
  set Φ : gamma5 hU →* H := L.subtype.comp ψ'.toMonoidHom with hΦ
  have hΦinj : Function.Injective Φ := Subtype.val_injective.comp ψ'.injective
  have hNker : ρ.ker = Θ.subgroupOf J := by
    ext z
    rw [MonoidHom.mem_ker, hρ1, Subgroup.mem_subgroupOf]
  have hN : ¬ 5 ∣ Nat.card ρ.ker := by
    rw [hNker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΘJ).toEquiv]
    exact (theta_solvable_and_not_dvd hp5 I).2
  have hA'el : IsElementaryAbelian 5 ↥(A.map Φ) := by
    have := hAel
    exact IsElementaryAbelian.map Φ
  have hA'card : Nat.card (A.map Φ) = 5 ^ 3 := by
    rw [Subgroup.card_map_of_injective hΦinj]
    exact hAcard
  have hr' : orderOf (Φ r) = 2 := by
    rw [orderOf_injective Φ hΦinj r]
    exact hr
  have hA'r : ∀ a ∈ A.map Φ, a * Φ r = Φ r * a := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, hAr a ha]
  have hyA' : y ∉ A.map Φ := by
    rintro ⟨a, -, ha⟩
    exact hyL (by rw [← ha]; exact (ψ' a).2)
  have hyA'' : ∀ a ∈ A.map Φ, y * a = a * y := by
    rintro _ ⟨a, ha, rfl⟩
    exact hyA a ha
  exact four_le_twoLocalOddRank_of_quotient_frame ρ hρs hN hA'el hA'card hr' hA'r hy5 hyA' hyA''
    hyr

end Main

end CFSG.RankThree.PartOne.K133B
