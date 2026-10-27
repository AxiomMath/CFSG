module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG
open scoped commutatorElement

variable {𝒢 P : Type*} [Group 𝒢] [Group P]

@[expose] def derivedPreimage (π : 𝒢 →* P) (D : Subgroup P) : Subgroup 𝒢 :=
  ⁅D.comap π, D.comap π⁆

theorem derivedPreimage_le_comap (π : 𝒢 →* P) (D : Subgroup P) :
    derivedPreimage π D ≤ D.comap π := by
  rw [derivedPreimage, Subgroup.commutator_le]
  intro a ha b hb
  exact (D.comap π).mul_mem ((D.comap π).mul_mem ((D.comap π).mul_mem ha hb)
    ((D.comap π).inv_mem ha)) ((D.comap π).inv_mem hb)

theorem derivedPreimage_le_centralizer {π : 𝒢 →* P} (hker : π.ker ≤ Subgroup.center 𝒢) {A : 𝒢}
    {D : Subgroup P} (hcent : D ≤ Subgroup.centralizer ({π A} : Set P)) :
    derivedPreimage π D ≤ Subgroup.centralizer ({A} : Set 𝒢) := by
  set H : Subgroup 𝒢 := D.comap π with hH
  set X : Subgroup 𝒢 := Subgroup.zpowers A with hX
  have h1 : ⁅H, X⁆ ≤ Subgroup.center 𝒢 := by
    rw [Subgroup.commutator_le]
    intro h hh a ha
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have hπa : π a ∈ Subgroup.zpowers (π A) := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact ⟨k, by simp⟩
    have hπh : π h ∈ Subgroup.centralizer ({π A} : Set P) := hcent hh
    have hc : Commute (π h) (π A) := Subgroup.mem_centralizer_singleton_iff.mp hπh
    obtain ⟨k, hk⟩ := hπa
    rw [← hk]
    exact (hc.zpow_right k).eq
  have h2 : ⁅⁅H, X⁆, H⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro c hc h _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (h1 hc) h).symm
  have h3 : ⁅⁅X, H⁆, H⁆ = ⊥ := by
    rw [Subgroup.commutator_comm X H]
    exact h2
  have h4 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := H) (H₂ := H) (H₃ := X) h2 h3
  intro y hy
  have hyX : ∀ a ∈ X, ⁅y, a⁆ = 1 := by
    intro a ha
    have : ⁅y, a⁆ ∈ (⊥ : Subgroup 𝒢) := h4 ▸ Subgroup.commutator_mem_commutator hy ha
    exact Subgroup.mem_bot.mp this
  rw [Subgroup.mem_centralizer_singleton_iff, ← commutatorElement_eq_one_iff_mul_comm]
  exact hyX A (Subgroup.mem_zpowers A)

theorem isQuasisimple_derivedPreimage {π : 𝒢 →* P} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center 𝒢) {D : Subgroup P} (hq : CFSG.IsQuasisimple ↥D) :
    CFSG.IsQuasisimple ↥(derivedPreimage π D) := by
  set H : Subgroup 𝒢 := D.comap π with hH
  let f : ↥H →* ↥D := (π.comp H.subtype).codRestrict D fun g => g.2
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg⟩ := hπ (x : P)
    exact ⟨⟨g, by rw [hH, Subgroup.mem_comap, hg]; exact x.2⟩, Subtype.ext hg⟩
  have hfker : f.ker ≤ Subgroup.center ↥H := by
    intro g hg
    have hg1 : π (g : 𝒢) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
    have hgc : (g : 𝒢) ∈ Subgroup.center 𝒢 := hker (MonoidHom.mem_ker.mpr hg1)
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (Subgroup.mem_center_iff.mp hgc (h : 𝒢))
  have hquasi : CFSG.IsQuasisimple ↥(commutator ↥H) :=
    CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective f hf hfker hq
  have hmap : (commutator ↥H).map H.subtype = derivedPreimage π D := by
    unfold derivedPreimage
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hmap]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective) hquasi

theorem map_derivedPreimage_of_perfect {π : 𝒢 →* P} (hπ : Function.Surjective π)
    {D : Subgroup P} (hD : Group.IsPerfect ↥D) : (derivedPreimage π D).map π = D := by
  unfold derivedPreimage
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπ]
  have h : ⁅D, D⁆ = D := by
    have := hD.commutator_eq_top
    have h2 : (commutator ↥D).map D.subtype = ⁅D, D⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [← h2, this, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact h

theorem isSubnormal_subgroupOf_of_le' {E Y X : Subgroup 𝒢} (hYX : Y ≤ X)
    (h : (E.subgroupOf X).IsSubnormal) : (E.subgroupOf Y).IsSubnormal := by
  have := h.comap (Subgroup.inclusion hYX)
  rwa [Subgroup.comap_inclusion_subgroupOf] at this

theorem isSubnormal_derivedPreimage {π : 𝒢 →* P} (hker : π.ker ≤ Subgroup.center 𝒢) {A : 𝒢}
    {D : Subgroup P} (hcent : D ≤ Subgroup.centralizer ({π A} : Set P))
    (hsub : (D.subgroupOf (Subgroup.centralizer ({π A} : Set P))).IsSubnormal) :
    ((derivedPreimage π D).subgroupOf (Subgroup.centralizer ({A} : Set 𝒢))).IsSubnormal := by
  set C : Subgroup P := Subgroup.centralizer ({π A} : Set P) with hC
  set N : Subgroup 𝒢 := C.comap π with hN
  set H : Subgroup 𝒢 := D.comap π with hH
  set D' : Subgroup 𝒢 := derivedPreimage π D with hD'
  have hCN : Subgroup.centralizer ({A} : Set 𝒢) ≤ N := by
    intro g hg
    rw [hN, Subgroup.mem_comap, hC, Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [← map_mul, ← map_mul, this]
  have hHN : H ≤ N := fun g hg => hcent hg
  have hD'H : D' ≤ H := derivedPreimage_le_comap π D
  have hD'C : D' ≤ Subgroup.centralizer ({A} : Set 𝒢) := derivedPreimage_le_centralizer hker hcent
  let π' : ↥N →* ↥C := (π.comp N.subtype).codRestrict C fun g => g.2
  have hHsub : (H.subgroupOf N).IsSubnormal := by
    have h1 : H.subgroupOf N = (D.subgroupOf C).comap π' := by
      ext g
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hH, Subgroup.mem_comap]
      rfl
    rw [h1]
    exact hsub.comap π'
  have hD1H : D'.subgroupOf N ≤ H.subgroupOf N := fun g hg => hD'H hg
  have hD'map : (commutator ↥H).map H.subtype = D' := by
    rw [hD']
    unfold derivedPreimage
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hnorm : ∀ g ∈ H, ∀ y ∈ D', g * y * g⁻¹ ∈ D' := by
    intro g hg y hy
    have hn : (commutator ↥H).Normal := inferInstance
    rw [← hD'map] at hy ⊢
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    exact ⟨⟨g, hg⟩ * y₀ * ⟨g, hg⟩⁻¹, hn.conj_mem y₀ hy₀ ⟨g, hg⟩, rfl⟩
  have hnormal : ((D'.subgroupOf N).subgroupOf (H.subgroupOf N)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hD1H]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hgH : (g : 𝒢) ∈ H := hg
    constructor
    · intro hh
      exact hnorm _ hgH _ hh
    · intro hh
      have := hnorm _ (H.inv_mem hgH) _ hh
      exact Subgroup.mem_subgroupOf.mpr (by simpa [mul_assoc] using this)
  have hD'N : (D'.subgroupOf N).IsSubnormal :=
    Subgroup.IsSubnormal.trans hD1H hnormal.isSubnormal hHsub
  exact isSubnormal_subgroupOf_of_le' hCN hD'N

theorem exists_lift_component {π : 𝒢 →* P} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center 𝒢) {A : 𝒢} {D : Subgroup P}
    (hq : CFSG.IsQuasisimple ↥D) (hcent : D ≤ Subgroup.centralizer ({π A} : Set P))
    (hsub : (D.subgroupOf (Subgroup.centralizer ({π A} : Set P))).IsSubnormal) :
    CFSG.IsQuasisimple ↥(derivedPreimage π D) ∧
      derivedPreimage π D ≤ Subgroup.centralizer ({A} : Set 𝒢) ∧
      ((derivedPreimage π D).subgroupOf (Subgroup.centralizer ({A} : Set 𝒢))).IsSubnormal ∧
      (derivedPreimage π D).map π = D :=
  ⟨isQuasisimple_derivedPreimage hπ hker hq, derivedPreimage_le_centralizer hker hcent,
    isSubnormal_derivedPreimage hker hcent hsub, map_derivedPreimage_of_perfect hπ hq.1⟩

theorem isComponentOf_derivedPreimage {π : 𝒢 →* P}
    (hker : π.ker ≤ Subgroup.center 𝒢) {A : 𝒢} {D : Subgroup P}
    (hD : CFSG.Assembly.IsComponentOf D
      (Subgroup.centralizer ({π A} : Set P) ⊓ π.range)) :
    CFSG.Assembly.IsComponentOf (derivedPreimage π D)
      (Subgroup.centralizer ({A} : Set 𝒢)) ∧ (derivedPreimage π D).map π = D := by
  let ρ : 𝒢 →* π.range := π.rangeRestrict
  let D₀ : Subgroup π.range := D.subgroupOf π.range
  have hDR : D ≤ π.range := hD.1.trans inf_le_right
  have hsurj : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hρker : ρ.ker ≤ Subgroup.center 𝒢 := by
    intro x hx
    exact hker (MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hx)))
  have hq₀ : CFSG.Assembly.IsQuasisimple D₀ :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDR) hD.2.2
  have : Group.IsPerfect D₀ := ⟨hq₀.1⟩
  have : IsSimpleGroup (D₀ ⧸ Subgroup.center D₀) := hq₀.2
  have hq : CFSG.IsQuasisimple D₀ := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    have h := Group.IsPerfect.not_isMulCommutative (G := D₀ ⧸ Subgroup.center D₀)
    simpa only [isMulCommutative_iff, not_forall] using h
  have hcent : D₀ ≤ Subgroup.centralizer ({ρ A} : Set π.range) := by
    intro x hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change x * ρ A = ρ A * x
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hD.1 hx).1
  have hC : (Subgroup.centralizer ({π A} : Set P) ⊓ π.range).comap π.range.subtype =
      Subgroup.centralizer ({ρ A} : Set π.range) := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, _⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      change x * ρ A = ρ A * x
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hx)
    · intro hx
      refine ⟨?_, x.2⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      change (x : P) * π A = π A * (x : P)
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx)
  have hsub : (D₀.subgroupOf (Subgroup.centralizer ({ρ A} : Set π.range))).IsSubnormal := by
    apply CFSG.Assembly.IsSubnormal.subgroupOf
    have h := CFSG.Assembly.IsSubnormal.comap (f := π.range.subtype) hD.2.1
    change CFSG.Assembly.IsSubnormal D₀ _ at h
    rw [hC] at h
    exact h
  have hlift := exists_lift_component hsurj hρker hq hcent hsub
  change CFSG.IsQuasisimple (derivedPreimage π D) ∧
    derivedPreimage π D ≤ Subgroup.centralizer ({A} : Set 𝒢) ∧
    ((derivedPreimage π D).subgroupOf (Subgroup.centralizer ({A} : Set 𝒢))).IsSubnormal ∧
    (derivedPreimage π D).map ρ = D₀ at hlift
  refine ⟨⟨hlift.2.1, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hlift.2.1).mpr hlift.2.2.1,
    ⟨hlift.1.1.commutator_eq_top, hlift.1.2.1⟩⟩, ?_⟩
  have h := congrArg (fun S : Subgroup π.range => S.map π.range.subtype) hlift.2.2.2
  simpa only [D₀, Subgroup.map_map, show π.range.subtype.comp ρ = π from rfl,
    Subgroup.map_subgroupOf_eq_of_le hDR] using h

theorem map_derivedPreimage_eq {π : 𝒢 →* P} (σ : MulAut 𝒢) (α : MulAut P)
    (hσ : ∀ g, π (σ g) = α (π g)) {D : Subgroup P} (hD : ∀ y, α y ∈ D ↔ y ∈ D) :
    (derivedPreimage π D).map σ.toMonoidHom = derivedPreimage π D := by
  have hH : (D.comap π).map σ.toMonoidHom = D.comap π := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [SetLike.mem_coe, Subgroup.mem_comap] at hy ⊢
      change π (σ y) ∈ D
      rw [hσ]
      exact (hD _).mpr hy
    · intro hg
      refine ⟨σ.symm g, ?_, by simp⟩
      simp only [SetLike.mem_coe, Subgroup.mem_comap]
      have h1 : α (π (σ.symm g)) = π g := by
        rw [← hσ, MulEquiv.apply_symm_apply]
      have := (hD (π (σ.symm g))).mp (by rw [h1]; exact hg)
      exact this
  unfold derivedPreimage
  rw [Subgroup.map_commutator, hH]

end CFSG.RankThree.PartOne
