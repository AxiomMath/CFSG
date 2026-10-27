module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Comp
public import CFSG.RankThree.GF2n.Stroth80.Sec4Quasi
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23GOCBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC (OutCyc)
open scoped commutatorElement

section FiniteGroup

variable {Γ : Type} [Group Γ] [Finite Γ]

private lemma injective_comp_inclusion_of_inf_eq_bot {Gc : Type} [Group Gc]
    {R N X : Subgroup Γ} {π : ↥R →* Gc} (hXR : X ≤ R)
    (hker : ∀ r : ↥R, π r = 1 ↔ (r : Γ) ∈ N) (hXN : X ⊓ N = ⊥) :
    Function.Injective (π.comp (Subgroup.inclusion hXR)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxN : (x : Γ) ∈ N := by
    have h1 := (hker (Subgroup.inclusion hXR x)).mp (by simpa using hx)
    simpa using h1
  have hx1 : (x : Γ) = 1 := by
    have hmem : (x : Γ) ∈ X ⊓ N := ⟨x.2, hxN⟩
    rwa [hXN, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact Subtype.ext hx1

private lemma normal_range_comp_inclusion {Gc : Type} [Group Gc]
    {R X : Subgroup Γ} (hXR : X ≤ R) (π : ↥R →* Gc) (hπ : Function.Surjective π)
    (hXn : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ ∈ X) :
    (π.comp (Subgroup.inclusion hXR)).range.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨x, rfl⟩ := hn
  obtain ⟨r, rfl⟩ := hπ g
  refine ⟨⟨(r : Γ) * (x : Γ) * (r : Γ)⁻¹, hXn r r.2 x x.2⟩, ?_⟩
  have hy : Subgroup.inclusion hXR
      ⟨(r : Γ) * (x : Γ) * (r : Γ)⁻¹, hXn r r.2 x x.2⟩ =
      r * Subgroup.inclusion hXR x * r⁻¹ := by
    apply Subtype.ext
    simp [Subgroup.coe_inclusion]
  rw [show (π.comp (Subgroup.inclusion hXR))
      ⟨(r : Γ) * (x : Γ) * (r : Γ)⁻¹, hXn r r.2 x x.2⟩ =
      π (Subgroup.inclusion hXR _) from rfl, hy, map_mul, map_mul, map_inv]
  rfl

theorem false_of_commuting_in_quasisimple {Gc : Type} [Group Gc] [Finite Gc]
    (hGc : CFSG.IsQuasisimple Gc) {R N X₂ X₃ : Subgroup Γ} (π : ↥R →* Gc)
    (hπ : Function.Surjective π) (hker : ∀ r : ↥R, π r = 1 ↔ (r : Γ) ∈ N)
    (hX₂R : X₂ ≤ R) (hX₃R : X₃ ≤ R) (hX₂n : ∀ r ∈ R, ∀ x ∈ X₂, r * x * r⁻¹ ∈ X₂)
    (hX₂N : X₂ ⊓ N = ⊥) (hX₃N : X₃ ⊓ N = ⊥) (hcomm : ∀ x ∈ X₂, ∀ y ∈ X₃, x * y = y * x)
    (hX₂ab : ∃ a b : ↥X₂, a * b ≠ b * a) (hX₃ab : ∃ a b : ↥X₃, a * b ≠ b * a) : False := by
  let f₂ : ↥X₂ →* Gc := π.comp (Subgroup.inclusion hX₂R)
  let f₃ : ↥X₃ →* Gc := π.comp (Subgroup.inclusion hX₃R)
  have hinj₂ : Function.Injective f₂ :=
    injective_comp_inclusion_of_inf_eq_bot hX₂R hker hX₂N
  have hinj₃ : Function.Injective f₃ :=
    injective_comp_inclusion_of_inf_eq_bot hX₃R hker hX₃N
  have hnorm₂ : f₂.range.Normal := normal_range_comp_inclusion hX₂R π hπ hX₂n
  rcases normal_le_center_or_eq_top hGc hnorm₂ with hcenter | htop
  · obtain ⟨a, b, hab⟩ := hX₂ab
    apply hab
    apply hinj₂
    rw [map_mul, map_mul]
    have ha := hcenter (show f₂ a ∈ f₂.range from ⟨a, rfl⟩)
    rw [Subgroup.mem_center_iff] at ha
    exact (ha (f₂ b)).symm
  · obtain ⟨a, b, hab⟩ := hX₃ab
    apply hab
    apply hinj₃
    rw [map_mul, map_mul]
    have hcenter₃ : f₃.range ≤ Subgroup.center Gc := by
      intro n hn
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ f₂.range := by rw [htop]; exact Subgroup.mem_top g
      obtain ⟨x, rfl⟩ := hg
      obtain ⟨y, rfl⟩ := hn
      have hR : Subgroup.inclusion hX₂R x * Subgroup.inclusion hX₃R y =
          Subgroup.inclusion hX₃R y * Subgroup.inclusion hX₂R x := by
        apply Subtype.ext
        simpa using hcomm x x.2 y y.2
      simpa [f₂, f₃, map_mul] using congrArg π hR
    have ha := hcenter₃ (show f₃ a ∈ f₃.range from ⟨a, rfl⟩)
    rw [Subgroup.mem_center_iff] at ha
    exact (ha (f₃ b)).symm

theorem isComponent_of_sup_eq_layer {X Y : Subgroup Γ} (hXY : X ⊔ Y = layer Γ)
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hXq : CFSG.IsQuasisimple ↥X) :
    IsComponent X := by
  refine ⟨hXq, ?_⟩
  have hN : (X.subgroupOf (X ⊔ Y)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (N := X) (sup_le_normalizer_of_commute hcomm)
  have hL : (X ⊔ Y).IsSubnormal := by
    haveI hchar : (layer Γ).Characteristic := CFSG.LocalCores.layer_characteristic
    rw [hXY]
    exact Subgroup.Normal.isSubnormal inferInstance
  exact Subgroup.IsSubnormal.step X (X ⊔ Y) le_sup_left hL hN

theorem eq_or_eq_of_sup_eq_layer {X Y : Subgroup Γ} (hXY : X ⊔ Y = layer Γ)
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hXc : IsComponent X) (hYc : IsComponent Y)
    {C : Subgroup Γ} (hC : IsComponent C) : C = X ∨ C = Y := by
  by_contra h
  obtain ⟨hCX, hCY⟩ := not_or.mp h
  have hXcent : X ≤ Subgroup.centralizer (C : Set Γ) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact comm_of_ne_component hC hXc hCX c hc x hx
  have hYcent : Y ≤ Subgroup.centralizer (C : Set Γ) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact comm_of_ne_component hC hYc hCY c hc y hy
  have hlayer : layer Γ ≤ Subgroup.centralizer (C : Set Γ) := by
    rw [← hXY]
    exact sup_le hXcent hYcent
  have hCcent : C ≤ Subgroup.centralizer (C : Set Γ) :=
    (CFSG.LocalCores.component_le_layer hC).trans hlayer
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hC
  apply hab
  have hmem := hCcent a.2
  rw [Subgroup.mem_centralizer_iff] at hmem
  exact Subtype.ext (hmem b b.2).symm

theorem eq_layer_of_isComponent (hq : CFSG.IsQuasisimple ↥(layer Γ))
    {K : Subgroup Γ} (hK : IsComponent K) : K = layer Γ := by
  have hL : IsComponent (layer Γ) := by
    refine ⟨hq, ?_⟩
    haveI hchar : (layer Γ).Characteristic := CFSG.LocalCores.layer_characteristic
    exact Subgroup.Normal.isSubnormal inferInstance
  by_contra hne
  have hKlayer : K ≤ layer Γ := CFSG.LocalCores.component_le_layer hK
  have hcomm := comm_of_ne_component hK hL hne
  have hKK : ⁅K, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y (hKlayer hy)).symm
  obtain ⟨a, b, hab⟩ := hK.1.2.2
  apply hab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have hcomm' : a * b = b * a := by
    have hmem : (⁅(a : Γ), (b : Γ)⁆ : Γ) ∈ ⁅K, K⁆ :=
      Subgroup.commutator_mem_commutator a.2 b.2
    rw [hKK, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact Subtype.ext hmem
  rw [← QuotientGroup.mk_mul, hcomm', QuotientGroup.mk_mul]

end FiniteGroup

theorem card_range_le_two_of_outCyc {L E : Type} [Group L] [Group E] [Finite E]
    (hout : OutCyc L) (hE : ∀ x : E, x * x = 1) (f : E →* Outer L) : Nat.card f.range ≤ 2 := by
  have hrange2 : ∀ x : ↥f.range, x * x = 1 := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := hx
    apply Subtype.ext
    simpa [map_mul] using congrArg f (hE y)
  have hexp : Monoid.exponent ↥f.range ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      simpa [pow_two] using hrange2 x
  have hP : IsPGroup 2 ↥f.range := IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa using hexp)
  have hcyc : IsCyclic ↥f.range := hout _ hP
  have hcard : Nat.card ↥f.range = Monoid.exponent ↥f.range :=
    (IsCyclic.exponent_eq_card).symm
  have hdvd : Nat.card ↥f.range ∣ 2 := by
    rw [hcard]
    exact hexp
  exact Nat.le_of_dvd (by norm_num) hdvd

end CFSG.RankThree.GF2n.Stroth80
