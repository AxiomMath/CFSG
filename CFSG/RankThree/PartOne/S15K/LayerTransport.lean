module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeAbstract
public import CFSG.RankThree.PartOne.S15K.NormAct

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree.PartOne.KCUnitary

variable {G : Type*} [Group G] {Γ : Type*} [Group Γ]

@[expose] def centRestrict {I : Subgroup G} (ψ : ↥I →* Γ) (b : G) :
    ↥(I ⊓ Subgroup.centralizer ({b} : Set G)) →* Γ :=
  ψ.comp (Subgroup.inclusion inf_le_left)

theorem centRestrict_injective {I : Subgroup G} {ψ : ↥I →* Γ} (hψ : Function.Injective ψ)
    (b : G) : Function.Injective (centRestrict ψ b) :=
  hψ.comp (Subgroup.inclusion_injective _)

theorem range_centRestrict {I : Subgroup G} (ψ : ↥I →* Γ) (hψ : Function.Injective ψ) {b : G}
    (hb : b ∈ Subgroup.normalizer (I : Set G)) {t : Γ}
    (hcompat : ∀ x : ↥I, ψ (I.normalizerMonoidHom ⟨b, hb⟩ x) = t * ψ x * t⁻¹) :
    (centRestrict ψ b).range = ψ.range ⊓ Subgroup.centralizer ({t} : Set Γ) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    show centRestrict ψ b x ∈ Subgroup.centralizer ({t} : Set Γ)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    set x' : ↥I := Subgroup.inclusion inf_le_left x with hx'
    have hbx : b * (x : G) = (x : G) * b :=
      Subgroup.mem_centralizer_iff.mp x.2.2 b (Set.mem_singleton b)
    have hfix : I.normalizerMonoidHom ⟨b, hb⟩ x' = x' :=
      Subtype.ext (by
        rw [coe_normalizerMonoidHom_apply]
        show b * (x : G) * b⁻¹ = (x : G)
        rw [hbx, mul_inv_cancel_right])
    have := hcompat x'
    rw [hfix] at this
    show h * ψ x' = ψ x' * h
    calc h * ψ x' = (h * ψ x' * h⁻¹) * h := by group
      _ = ψ x' * h := by rw [← this]
  · rintro ⟨⟨x, rfl⟩, hy⟩
    have hy' : t * ψ x = ψ x * t := Subgroup.mem_centralizer_iff.mp hy t (Set.mem_singleton t)
    have h1 : ψ (I.normalizerMonoidHom ⟨b, hb⟩ x) = ψ x := by
      rw [hcompat x]
      calc t * ψ x * t⁻¹ = (ψ x * t) * t⁻¹ := by rw [hy']
        _ = ψ x := by group
    have h2 : I.normalizerMonoidHom ⟨b, hb⟩ x = x := hψ h1
    have hbx : b * (x : G) = (x : G) * b := by
      have h3 : b * (x : G) * b⁻¹ = (x : G) := by
        have := congrArg Subtype.val h2
        rwa [coe_normalizerMonoidHom_apply] at this
      calc b * (x : G) = (b * (x : G) * b⁻¹) * b := by group
        _ = (x : G) * b := by rw [h3]
    refine ⟨⟨(x : G), x.2, ?_⟩, rfl⟩
    show (x : G) ∈ Subgroup.centralizer ({b} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hbx

theorem isComponent_comap_of_range {H : Type*} [Group H] (Φ : H →* Γ)
    (hΦ : Function.Injective Φ) {J : Subgroup Γ}
    (h : IsComponent (J.subgroupOf Φ.range)) : IsComponent (J.comap Φ) := by
  let θ : H ≃* ↥Φ.range := MonoidHom.ofInjective hΦ
  have hθ : ∀ x : H, ((θ x : ↥Φ.range) : Γ) = Φ x := fun x => rfl
  have key : (J.subgroupOf Φ.range).map θ.symm.toMonoidHom = J.comap Φ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show Φ (θ.symm y) ∈ J
      have : Φ (θ.symm y) = (y : Γ) := by
        rw [← hθ, θ.apply_symm_apply]
      rw [this]
      exact hy
    · intro hx
      refine ⟨θ x, ?_, θ.symm_apply_apply x⟩
      show ((θ x : ↥Φ.range) : Γ) ∈ J
      rw [hθ]
      exact hx
  rw [← key]
  exact LocalCores.isComponent_map_mulEquiv θ.symm h

theorem layer_transport {H₀ : Subgroup G} (Φ : ↥H₀ →* Γ) (hΦ : Function.Injective Φ) {ι : Type*}
    (J : ι → Subgroup Γ) (hJ : ∀ i, J i ≤ Φ.range)
    (hcomp : ∀ i, IsComponent ((J i).subgroupOf Φ.range))
    (hder : ⁅Φ.range, Φ.range⁆ = ⨆ i, J i) :
    (∀ i, ((J i).comap Φ).map H₀.subtype ≤ H₀) ∧
      (∀ i, IsComponent ((((J i).comap Φ).map H₀.subtype).subgroupOf H₀)) ∧
      ⁅H₀, H₀⁆ = ⨆ i, ((J i).comap Φ).map H₀.subtype := by
  refine ⟨fun i => Subgroup.map_subtype_le _, fun i => ?_, ?_⟩
  · show IsComponent (Subgroup.comap H₀.subtype (Subgroup.map H₀.subtype ((J i).comap Φ)))
    rw [Subgroup.comap_map_eq_self_of_injective Subtype.val_injective]
    exact isComponent_comap_of_range Φ hΦ (hcomp i)
  · have h1 : Subgroup.map Φ ⁅(⊤ : Subgroup ↥H₀), ⊤⁆ = ⁅Φ.range, Φ.range⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map]
    have h2 : Subgroup.map Φ (⨆ i, (J i).comap Φ) = ⨆ i, J i := by
      rw [Subgroup.map_iSup]
      refine le_antisymm (iSup_le fun i => ?_) (iSup_le fun i => ?_)
      · exact (Subgroup.map_comap_le Φ (J i)).trans (le_iSup J i)
      · refine le_trans ?_ (le_iSup _ i)
        rw [Subgroup.map_comap_eq]
        exact le_inf (hJ i) le_rfl
    have h3 : (⁅(⊤ : Subgroup ↥H₀), ⊤⁆) = ⨆ i, (J i).comap Φ := by
      refine Subgroup.map_injective hΦ ?_
      rw [h1, hder, h2]
    have h4 : ⁅H₀, H₀⁆ = Subgroup.map H₀.subtype ⁅(⊤ : Subgroup ↥H₀), ⊤⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [h4, h3, Subgroup.map_iSup]

theorem layer_of_projSetting {I : Subgroup G} (ψ : ↥I →* Γ) (hψ : Function.Injective ψ) {b : G}
    (hb : b ∈ Subgroup.normalizer (I : Set G)) {t : Γ}
    (hcompat : ∀ x : ↥I, ψ (I.normalizerMonoidHom ⟨b, hb⟩ x) = t * ψ x * t⁻¹) {U : Type*} [Group U]
    {ρ : U →* Γ} (hBD : ψ.range ≤ ρ.range) {Hs M ZM : Subgroup U} {ι : Type*} {F : ι → Subgroup U}
    (S : ProjSetting ρ ψ.range t Hs M ZM F) :
    ∃ Q : ι → Subgroup G,
      (∀ i, Q i ≤ I ⊓ Subgroup.centralizer ({b} : Set G)) ∧
      (∀ i, IsComponent ((Q i).subgroupOf (I ⊓ Subgroup.centralizer ({b} : Set G)))) ∧
      ⁅I ⊓ Subgroup.centralizer ({b} : Set G), I ⊓ Subgroup.centralizer ({b} : Set G)⁆ =
        ⨆ i, Q i ∧
      ∀ i (x : G), x ∈ Q i ↔ ∃ hx : x ∈ I, ψ ⟨x, hx⟩ ∈ (F i).map ρ := by
  set H₀ := I ⊓ Subgroup.centralizer ({b} : Set G) with hH₀
  set Φ := centRestrict ψ b with hΦdef
  have hΦ : Function.Injective Φ := centRestrict_injective hψ b
  have hrange : Φ.range = ψ.range ⊓ Subgroup.centralizer ({t} : Set Γ) :=
    range_centRestrict ψ hψ hb hcompat
  have hJ : ∀ i, (F i).map ρ ≤ Φ.range := fun i => by
    rw [hrange]
    exact S.map_le_centralizerB i
  have hcomp : ∀ i, IsComponent (((F i).map ρ).subgroupOf Φ.range) := fun i => by
    rw [hrange]
    exact S.isComponent_image i
  have hder : ⁅Φ.range, Φ.range⁆ = ⨆ i, (F i).map ρ := by
    refine le_antisymm ?_ (iSup_le fun i => ?_)
    · rw [← S.commutator_image_eq, ← S.N_eq]
      refine Subgroup.commutator_mono ?_ ?_ <;> rw [hrange] <;> exact inf_le_inf_right _ hBD
    · have hp : Group.IsPerfect ↥((F i).map ρ) := (S.isQuasisimple_image i).1
      have h1 := (Subgroup.isPerfect_iff).1 hp
      calc (F i).map ρ = ⁅(F i).map ρ, (F i).map ρ⁆ := h1.symm
        _ ≤ ⁅Φ.range, Φ.range⁆ := Subgroup.commutator_mono (hJ i) (hJ i)
  obtain ⟨h1, h2, h3⟩ := layer_transport Φ hΦ (fun i => (F i).map ρ) hJ hcomp hder
  refine ⟨fun i => ((F i).map ρ |>.comap Φ).map H₀.subtype, h1, h2, h3, fun i x => ?_⟩
  simp only [Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2.1, hy⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨y, hyy⟩ := hJ i hy
    have hyx : Subgroup.inclusion (inf_le_left : H₀ ≤ I) y = ⟨x, hx⟩ := hψ hyy
    refine ⟨y, ?_, congrArg Subtype.val hyx⟩
    show Φ y ∈ (F i).map ρ
    rw [← hyy] at hy
    exact hy

end CFSG.RankThree.PartOne.S15K
