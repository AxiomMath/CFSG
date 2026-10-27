module

public import CFSG.RankThree.PartOne.S11d.LayerDecomp
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

@[expose] def GoodConclusion (p : ℕ) (T : Type) [Group T] (α : MulAut T) (x : T) : Prop :=
  (∃ D : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D) ∧
  (∀ D : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D →
    (∀ g ∈ D, α g ∈ D) →
    (∀ e ∈ D, ¬ ∀ g ∈ D, α g = e * g * e⁻¹) ∧
    (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
      LieModel (↥D ⧸ Subgroup.center ↥D) t' n' 2 (p * f')) ∧
    ∃ t₁ ∈ D, α t₁ = t₁ ∧ ∃ t₂ ∈ D, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
      (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁) ∧
  ∀ g ∈ Subgroup.centralizer ({x} : Set T), α g = g → (∃ k : ℕ, orderOf g = 2 ^ k) →
    g ∈ inSubgroup layer (Subgroup.centralizer ({x} : Set T))

variable {T T' : Type} [Group T] [Group T']

theorem map_centralizer_singleton_mulEquiv_good (φ : T ≃* T') (x : T) :
    (Subgroup.centralizer ({x} : Set T)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ x} : Set T') := by
  ext g'
  constructor
  · rintro ⟨g, hg, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp hg
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    change φ g * φ x = φ x * φ g
    rw [← map_mul, ← map_mul, h]
  · intro hg
    have h := Subgroup.mem_centralizer_singleton_iff.mp hg
    refine ⟨φ.symm g', Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simp⟩
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h

theorem isComponentOf_map_mulEquiv (φ : T ≃* T') {X D : Subgroup T}
    (hD : IsComponentOf X D) : IsComponentOf (X.map φ.toMonoidHom) (D.map φ.toMonoidHom) := by
  refine ⟨Subgroup.map_mono hD.1, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective D φ.toMonoidHom φ.injective) hD.2.1
  · let ψ : ↥X ≃* ↥(X.map φ.toMonoidHom) := Subgroup.equivMapOfInjective X φ.toMonoidHom φ.injective
    have h : (D.map φ.toMonoidHom).subgroupOf (X.map φ.toMonoidHom) =
        (D.subgroupOf X).map ψ.toMonoidHom := by
      ext g
      constructor
      · intro hg
        have hg' : (g : T') ∈ D.map φ.toMonoidHom := hg
        obtain ⟨d, hd, hdg⟩ := hg'
        obtain ⟨y, hy, hyg⟩ := g.2
        have : y = d := φ.injective (by rw [show φ y = (g : T') from hyg, ← hdg]; rfl)
        refine ⟨⟨y, hy⟩, ?_, Subtype.ext hyg⟩
        change y ∈ D
        rw [this]
        exact hd
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(y : T), hy, rfl⟩
    rw [h]
    exact hD.2.2.map ψ.surjective

theorem map_inSubgroup_layer_mulEquiv (φ : T ≃* T') (X : Subgroup T) :
    (inSubgroup layer X).map φ.toMonoidHom = inSubgroup layer (X.map φ.toMonoidHom) := by
  rw [inSubgroup_layer_eq_sSup, inSubgroup_layer_eq_sSup]
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun E hE => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (isComponentOf_map_mulEquiv φ hE)
  · refine sSup_le fun E' hE' => ?_
    have hE : IsComponentOf X (E'.map φ.symm.toMonoidHom) := by
      have h := isComponentOf_map_mulEquiv φ.symm hE'
      have hX : (X.map φ.toMonoidHom).map φ.symm.toMonoidHom = X := by
        rw [Subgroup.map_map]
        convert Subgroup.map_id X
        ext g
        simp
      rwa [hX] at h
    have hle : E'.map φ.symm.toMonoidHom ≤ sSup {E : Subgroup T | IsComponentOf X E} := le_sSup hE
    have h := Subgroup.map_mono (f := φ.toMonoidHom) hle
    rwa [Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id T' from by
      ext; simp, Subgroup.map_id] at h

theorem GoodConclusion.of_mulEquiv {p : ℕ} (φ : T ≃* T') (α : MulAut T) (x : T)
    (h : GoodConclusion p T' (MulAut.congr φ α) (φ x)) : GoodConclusion p T α x := by
  obtain ⟨hex, hall, hlay⟩ := h
  have hαφ : ∀ g : T, MulAut.congr φ α (φ g) = φ (α g) := fun g => by
    simp [MulAut.congr_apply]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨D', hD'⟩ := hex
    have h1 := isComponentOf_map_mulEquiv φ.symm hD'
    rw [map_centralizer_singleton_mulEquiv_good φ.symm (φ x), MulEquiv.symm_apply_apply] at h1
    exact ⟨_, h1⟩
  · intro D hD hst
    have hD' := isComponentOf_map_mulEquiv φ hD
    rw [map_centralizer_singleton_mulEquiv_good] at hD'
    have hst' : ∀ g' ∈ D.map φ.toMonoidHom, MulAut.congr φ α g' ∈ D.map φ.toMonoidHom := by
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨α g, hst g hg, (hαφ g).symm⟩
    obtain ⟨hnon, ⟨t', n', f', hf', hmodel'⟩, t₁, ht₁, hα₁, t₂, ht₂, hα₂, ho₁, ho₂, hnc⟩ :=
      hall _ hD' hst'
    refine ⟨?_, ?_, ?_⟩
    · intro e he hcon
      apply hnon (φ e) ⟨e, he, rfl⟩
      rintro _ ⟨g, hg, rfl⟩
      change ((MulAut.congr φ) α) (φ g) = φ e * φ g * (φ e)⁻¹
      rw [hαφ g, hcon g hg, map_mul, map_mul, map_inv]
    · let e₁ : ↥D ≃* ↥(D.map φ.toMonoidHom) :=
        Subgroup.equivMapOfInjective D φ.toMonoidHom φ.injective
      let e₃ : ↥D ⧸ Subgroup.center ↥D ≃* ↥(D.map φ.toMonoidHom) ⧸
          Subgroup.center ↥(D.map φ.toMonoidHom) :=
        QuotientGroup.congr (Subgroup.center ↥D) (Subgroup.center ↥(D.map φ.toMonoidHom)) e₁
          (Subgroup.map_center_eq e₁)
      exact ⟨t', n', f', hf', lieModel_of_mulEquiv e₃.symm hmodel'⟩
    · obtain ⟨u₁, hu₁, rfl⟩ := ht₁
      obtain ⟨u₂, hu₂, rfl⟩ := ht₂
      refine ⟨u₁, hu₁, φ.injective ?_, u₂, hu₂, φ.injective ?_, ?_, ?_, ?_⟩
      · rw [← hαφ u₁]
        exact hα₁
      · rw [← hαφ u₂]
        exact hα₂
      · obtain ⟨k, hk⟩ := ho₁
        exact ⟨k, by rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hk⟩
      · obtain ⟨k, hk⟩ := ho₂
        exact ⟨k, by rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hk⟩
      · intro hcomm
        apply hnc
        change φ u₁ * φ u₂ = φ u₂ * φ u₁
        rw [← map_mul, ← map_mul, hcomm]
  · intro g hg hαg hgo
    have h1 : φ g ∈ Subgroup.centralizer ({φ x} : Set T') := by
      rw [← map_centralizer_singleton_mulEquiv_good φ x]
      exact ⟨g, hg, rfl⟩
    have h2 := hlay (φ g) h1 (by rw [hαφ, hαg]) (by
      obtain ⟨k, hk⟩ := hgo
      exact ⟨k, by rwa [MulEquiv.orderOf_eq]⟩)
    rw [← map_centralizer_singleton_mulEquiv_good φ x, ← map_inSubgroup_layer_mulEquiv] at h2
    obtain ⟨g₀, hg₀, hg₀g⟩ := h2
    have : g₀ = g := φ.injective hg₀g
    rwa [this] at hg₀

end CFSG.RankThree.PartOne
