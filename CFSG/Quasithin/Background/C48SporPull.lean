module

public import CFSG.Quasithin.Background.C48SporImg
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique

variable {G : Type} [Group G] {X : Subgroup G} {N : Subgroup ↥X} [N.Normal]

theorem imgHom_conj {A₀ V₀ : Subgroup G} (hA : A₀ ≤ X) (hV : V₀ ≤ X) {a : ↥A₀} {u v : ↥V₀}
    (huv : (v : G) = a * u * a⁻¹) :
    ((imgHom (N := N) hV v : ↥(img N V₀)) : ↥X ⧸ N) =
      (imgHom (N := N) hA a : ↥X ⧸ N) * (imgHom (N := N) hV u : ↥X ⧸ N) *
        (imgHom (N := N) hA a : ↥X ⧸ N)⁻¹ := by
  rw [coe_imgHom, coe_imgHom, coe_imgHom, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (by simpa using huv)

theorem isNaturalSection_of_img {A₀ V₀ Z₀ : Subgroup G} (hA : A₀ ≤ X) (hV : V₀ ≤ X)
    {N₀ : Subgroup ↥A₀} {Z' : Subgroup (↥X ⧸ N)} {N' : Subgroup ↥(img N A₀)}
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    (h : IsNaturalSection (img N A₀) (img N V₀) Z' N' Γ)
    (hAV : A₀ ≤ Subgroup.normalizer (V₀ : Set G)) (hN : N'.comap (imgHom hA) = N₀)
    (hZ : ∀ v : ↥V₀, (imgHom (N := N) hV v : ↥X ⧸ N) ∈ Z' ↔ (v : G) ∈ Z₀) :
    IsNaturalSection A₀ V₀ Z₀ N₀ Γ := by
  obtain ⟨-, α, hα, hαk, β, hβ, hβk, heq⟩ := h
  refine ⟨hAV, α.comp (imgHom hA), hα.comp (imgHom_surjective hA), ?_, β.comp (imgHom hV),
    hβ.comp (imgHom_surjective hV), ?_, fun a u v huv => ?_⟩
  · rw [← MonoidHom.comap_ker, hαk, hN]
  · ext v
    rw [← MonoidHom.comap_ker, hβk, Subgroup.mem_comap, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    exact hZ v
  · exact heq (imgHom hA a) (imgHom hV u) (imgHom hV v) (imgHom_conj hA hV huv)

theorem isAltNaturalSection_of_img {A₀ V₀ Z₀ : Subgroup G} (hA : A₀ ≤ X) (hV : V₀ ≤ X)
    {N₀ : Subgroup ↥A₀} {Z' : Subgroup (↥X ⧸ N)} {N' : Subgroup ↥(img N A₀)} {m : ℕ}
    (h : IsAltNaturalSection (img N A₀) (img N V₀) Z' N' m)
    (hAV : A₀ ≤ Subgroup.normalizer (V₀ : Set G)) (hN : N'.comap (imgHom hA) = N₀)
    (hZ : ∀ v : ↥V₀, (imgHom (N := N) hV v : ↥X ⧸ N) ∈ Z' ↔ (v : G) ∈ Z₀) :
    IsAltNaturalSection A₀ V₀ Z₀ N₀ m := by
  obtain ⟨-, α, hα, hαk, β, hβ, hβk, heq⟩ := h
  refine ⟨hAV, α.comp (imgHom hA), hα.comp (imgHom_surjective hA), ?_, β.comp (imgHom hV),
    hβ.comp (imgHom_surjective hV), ?_, fun a u v huv => ?_⟩
  · rw [← MonoidHom.comap_ker, hαk, hN]
  · ext v
    rw [← MonoidHom.comap_ker, hβk, Subgroup.mem_comap, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    exact hZ v
  · exact heq (imgHom hA a) (imgHom hV u) (imgHom hV v) (imgHom_conj hA hV huv)

theorem isSumOfNaturalModules_of_img {A₀ V₀ Z₀ : Subgroup G} (hA : A₀ ≤ X) (hV : V₀ ≤ X)
    {N₀ : Subgroup ↥A₀} {Z' : Subgroup (↥X ⧸ N)} {N' : Subgroup ↥(img N A₀)}
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {dual : Bool} {k : ℕ}
    (h : IsSumOfNaturalModules (img N A₀) (img N V₀) Z' N' Γ dual k)
    (hAV : A₀ ≤ Subgroup.normalizer (V₀ : Set G)) (hZV : Z₀ ≤ V₀)
    (hN : N'.comap (imgHom hA) = N₀)
    (hZ : ∀ v : ↥V₀, (imgHom (N := N) hV v : ↥X ⧸ N) ∈ Z' ↔ (v : G) ∈ Z₀) :
    IsSumOfNaturalModules A₀ V₀ Z₀ N₀ Γ dual k := by
  obtain ⟨α, hα, hαk, -, -, β, hβ, hβk, heq⟩ := h
  refine ⟨α.comp (imgHom hA), hα.comp (imgHom_surjective hA), ?_, hAV, hZV, β.comp (imgHom hV),
    hβ.comp (imgHom_surjective hV), ?_, fun a u v huv => ?_⟩
  · rw [← MonoidHom.comap_ker, hαk, hN]
  · ext v
    rw [← MonoidHom.comap_ker, hβk, Subgroup.mem_comap, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    exact hZ v
  · exact heq (imgHom hA a) (imgHom hV u) (imgHom hV v) (imgHom_conj hA hV huv)

theorem isSumOfNaturalModules_img {A₀ V₀ : Subgroup G} (hA : A₀ ≤ X) (hV : V₀ ≤ X)
    {N₀ : Subgroup ↥A₀} {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {dual : Bool} {k : ℕ}
    (h : IsSumOfNaturalModules A₀ V₀ ⊥ N₀ Γ dual k)
    (hker : (imgHom (N := N) hA).ker ≤ N₀) (hinj : Function.Injective (imgHom (N := N) hV)) :
    IsSumOfNaturalModules (img N A₀) (img N V₀) ⊥ (N₀.map (imgHom hA)) Γ dual k := by
  obtain ⟨α, hα, hαk, hAV, -, β, hβ, hβk, heq⟩ := h
  set eA := QuotientGroup.quotientKerEquivOfSurjective (imgHom (N := N) hA)
    (imgHom_surjective hA) with heA
  set α' : ↥(img N A₀) →* ↥Γ :=
    (QuotientGroup.lift _ α (by rw [hαk]; exact hker)).comp eA.symm.toMonoidHom with hα'def
  have hα' : ∀ a, α' (imgHom hA a) = α a := fun a => by
    have : eA.symm (imgHom hA a) = (a : ↥A₀ ⧸ (imgHom (N := N) hA).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [hα'def, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, this,
      QuotientGroup.lift_mk]
  set eV := MulEquiv.ofBijective (imgHom (N := N) hV) ⟨hinj, imgHom_surjective hV⟩ with heV
  set β' := β.comp eV.symm.toMonoidHom with hβ'def
  have hβ' : ∀ v, β' (imgHom hV v) = β v := fun v => by
    have : eV.symm (imgHom hV v) = v := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [hβ'def, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, this]
  refine ⟨α', ?_, ?_, img_le_normalizer hAV, bot_le, β', ?_, ?_, ?_⟩
  · intro g
    obtain ⟨a, rfl⟩ := hα g
    exact ⟨imgHom hA a, hα' a⟩
  · ext a'
    obtain ⟨a, rfl⟩ := imgHom_surjective (N := N) hA a'
    rw [MonoidHom.mem_ker, hα', ← MonoidHom.mem_ker, hαk]
    constructor
    · intro ha
      exact ⟨a, ha, rfl⟩
    · rintro ⟨b, hb, hba⟩
      have : b⁻¹ * a ∈ (imgHom (N := N) hA).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hba, inv_mul_cancel]
      have := N₀.mul_mem hb (hker this)
      simpa using this
  · intro w
    obtain ⟨v, rfl⟩ := hβ w
    exact ⟨imgHom hV v, hβ' v⟩
  · ext v'
    obtain ⟨v, rfl⟩ := imgHom_surjective (N := N) hV v'
    rw [MonoidHom.mem_ker, hβ', ← MonoidHom.mem_ker, hβk]
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · intro hv
      rw [show v = 1 from Subtype.ext hv, map_one]
      rfl
    · intro hv
      have : imgHom (N := N) hV v = imgHom hV 1 := by
        rw [map_one]
        exact Subtype.ext hv
      rw [hinj this]
      rfl
  · intro a' u' v' huv
    obtain ⟨a, rfl⟩ := imgHom_surjective (N := N) hA a'
    obtain ⟨u, rfl⟩ := imgHom_surjective (N := N) hV u'
    obtain ⟨v, rfl⟩ := imgHom_surjective (N := N) hV v'
    have hw : (a : G) * u * (a : G)⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.mp (hAV a.2) u).mp u.2
    have hvw : v = ⟨(a : G) * u * (a : G)⁻¹, hw⟩ := by
      apply hinj
      apply Subtype.ext
      rw [huv, imgHom_conj hA hV (u := u) (v := ⟨(a : G) * u * (a : G)⁻¹, hw⟩) rfl]
      simp
    intro i
    rw [hβ', hβ', hα']
    exact heq a u v (by rw [hvw]; simp) i

end CFSG.Quasithin.C48Spor
