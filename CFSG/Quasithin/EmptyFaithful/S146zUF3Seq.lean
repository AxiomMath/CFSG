module

public import CFSG.Quasithin.Background.F918P3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S146zU

namespace UF3

section Hom

variable {G : Type} [Group G]

theorem tildeHom_eq_one_iff {V₁ H : Subgroup G} (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (x : ↥H) : tildeHom hV₁ x = 1 ↔ (x : G) ∈ V₁ := by
  rw [← secMk_eq_one_iff (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
    (x := ⟨x, hV₁ x.2⟩)]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem tildeHom_eq_iff {V₁ H : Subgroup G} (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (x y : ↥H) : tildeHom hV₁ x = tildeHom hV₁ y ↔ (x : G)⁻¹ * y ∈ V₁ := by
  rw [← secMk_eq_secMk_iff (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
    (x := ⟨x, hV₁ x.2⟩) (y := ⟨y, hV₁ y.2⟩)]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem actH_tildeHom {V₁ IH H : Subgroup G} (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H ≤ Subgroup.normalizer (IH : Set G)) (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G))
    (x : ↥H) (u v : ↥IH) (huv : (v : G) = (x : G) * u * (x : G)⁻¹) :
    actH hV₁ hIH x (tildeHom hIHN u) = tildeHom hIHN v := by
  apply Subtype.ext
  rw [actH_apply_coe]
  have e : (⟨(v : G), hIHN v.2⟩ : ↥(Subgroup.normalizer (V₁ : Set G))) =
      ⟨(x : G), hV₁ x.2⟩ * ⟨(u : G), hIHN u.2⟩ * (⟨(x : G), hV₁ x.2⟩)⁻¹ :=
    Subtype.ext (by simpa using huv)
  have h1 : (tildeHom hIHN v : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨(v : G), hIHN v.2⟩ := rfl
  have h2 : (tildeHom hIHN u : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨(u : G), hIHN u.2⟩ := rfl
  rw [h1, h2, e, map_mul, map_mul, map_inv]

end Hom

section Seq

variable {G : Type} [Group G] {H W J U : Subgroup G}

theorem tildeOf_le_tildeOf (W : Subgroup G) (hJU : J ≤ U) : tildeOf W J ≤ tildeOf W U :=
  secImg_mono (A := Subgroup.normalizer (W : Set G)) (B := W) hJU

@[expose] def secIncl (hJU : J ≤ U) : ↥(tildeOf W J) →* ↥(tildeOf W U) :=
  Subgroup.inclusion (tildeOf_le_tildeOf W hJU)

@[expose] noncomputable def secQuo (hWJ : W ≤ J) (hUW : U ≤ Subgroup.normalizer (W : Set G))
    (hUJ : U ≤ Subgroup.normalizer (J : Set G)) : ↥(tildeOf W U) →* ↥(tildeOf J U) :=
  (tildeHom hUW).liftOfSurjective (tildeHom_surjective hUW)
    ⟨tildeHom hUJ, fun x hx => by
      rw [MonoidHom.mem_ker, tildeHom_eq_one_iff] at hx ⊢
      exact hWJ hx⟩

theorem secQuo_tildeHom (hWJ : W ≤ J) (hUW : U ≤ Subgroup.normalizer (W : Set G))
    (hUJ : U ≤ Subgroup.normalizer (J : Set G)) (u : ↥U) :
    secQuo hWJ hUW hUJ (tildeHom hUW u) = tildeHom hUJ u := by
  unfold secQuo
  exact MonoidHom.liftOfRightInverse_comp_apply (tildeHom hUW) _ _ _ u

theorem secIncl_injective (hJU : J ≤ U) : Function.Injective (secIncl (W := W) hJU) :=
  Subgroup.inclusion_injective _

theorem secQuo_surjective (hWJ : W ≤ J) (hUW : U ≤ Subgroup.normalizer (W : Set G))
    (hUJ : U ≤ Subgroup.normalizer (J : Set G)) : Function.Surjective (secQuo hWJ hUW hUJ) := by
  intro y
  obtain ⟨u, rfl⟩ := tildeHom_surjective hUJ y
  exact ⟨tildeHom hUW u, secQuo_tildeHom hWJ hUW hUJ u⟩

theorem ker_secQuo (hWJ : W ≤ J) (hJU : J ≤ U) (hUW : U ≤ Subgroup.normalizer (W : Set G))
    (hUJ : U ≤ Subgroup.normalizer (J : Set G)) :
    (secQuo hWJ hUW hUJ).ker = (secIncl (W := W) hJU).range := by
  ext y
  obtain ⟨u, rfl⟩ := tildeHom_surjective hUW y
  rw [MonoidHom.mem_ker, secQuo_tildeHom, tildeHom_eq_one_iff, secIncl, Subgroup.inclusion_range,
    Subgroup.mem_subgroupOf]
  exact (secMk_mem_secImg_iff (A := Subgroup.normalizer (W : Set G)) (B := W) hWJ
    (x := ⟨(u : G), hUW u.2⟩)).symm

theorem secIncl_actH (hJU : J ≤ U) (hWN : H ≤ Subgroup.normalizer (W : Set G))
    (hJN : H ≤ Subgroup.normalizer (J : Set G)) (hUN : H ≤ Subgroup.normalizer (U : Set G))
    (g : ↥H) (v : ↥(tildeOf W J)) :
    secIncl hJU (actH hWN hJN g v) = actH hWN hUN g (secIncl hJU v) := by
  apply Subtype.ext
  show ((actH hWN hJN g v : ↥(tildeOf W J)) : SecQuot (Subgroup.normalizer (W : Set G)) W) =
    ((actH hWN hUN g (secIncl hJU v) : ↥(tildeOf W U)) :
      SecQuot (Subgroup.normalizer (W : Set G)) W)
  rw [actH_apply_coe, actH_apply_coe]
  rfl

theorem secQuo_actH (hWJ : W ≤ J) (hUW : U ≤ Subgroup.normalizer (W : Set G))
    (hUJ : U ≤ Subgroup.normalizer (J : Set G)) (hWN : H ≤ Subgroup.normalizer (W : Set G))
    (hJN : H ≤ Subgroup.normalizer (J : Set G)) (hUN : H ≤ Subgroup.normalizer (U : Set G))
    (g : ↥H) (y : ↥(tildeOf W U)) :
    secQuo hWJ hUW hUJ (actH hWN hUN g y) = actH hJN hUN g (secQuo hWJ hUW hUJ y) := by
  obtain ⟨u, rfl⟩ := tildeHom_surjective hUW y
  have hgu : (g : G) * u * (g : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hUN g.2) u).mp u.2
  have h1 := actH_tildeHom hWN hUN hUW g u ⟨_, hgu⟩ rfl
  have h2 := actH_tildeHom hJN hUN hUJ g u ⟨_, hgu⟩ rfl
  rw [h1, secQuo_tildeHom, secQuo_tildeHom, h2]

theorem sectionSeq (hWJ : W ≤ J) (hJU : J ≤ U)
    (hWN : H ≤ Subgroup.normalizer (W : Set G)) (hJN : H ≤ Subgroup.normalizer (J : Set G))
    (hUN : H ≤ Subgroup.normalizer (U : Set G)) (hUW : U ≤ Subgroup.normalizer (W : Set G))
    (hUJ : U ≤ Subgroup.normalizer (J : Set G)) :
    ∃ (ι : ↥(tildeOf W J) →* ↥(tildeOf W U)) (q : ↥(tildeOf W U) →* ↥(tildeOf J U)),
      Function.Injective ι ∧ Function.Surjective q ∧ q.ker = ι.range ∧
      (∀ (g : ↥H) (v : ↥(tildeOf W J)), ι (actH hWN hJN g v) = actH hWN hUN g (ι v)) ∧
      (∀ (g : ↥H) (y : ↥(tildeOf W U)), q (actH hWN hUN g y) = actH hJN hUN g (q y)) :=
  ⟨secIncl hJU, secQuo hWJ hUW hUJ, secIncl_injective hJU, secQuo_surjective hWJ hUW hUJ,
    ker_secQuo hWJ hJU hUW hUJ, secIncl_actH hJU hWN hJN hUN,
    secQuo_actH hWJ hUW hUJ hWN hJN hUN⟩

end Seq

end UF3

end S146zU

end CFSG.Quasithin
