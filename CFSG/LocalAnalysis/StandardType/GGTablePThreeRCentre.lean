module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem center_map_eq_bot_iff_of_injective {X R : Type*} [Group X] [Group R]
    (π : X →* R) (J : Subgroup X) (h : J ⊓ π.ker = ⊥) :
    Subgroup.center (J.map π) = ⊥ ↔ Subgroup.center J = ⊥ := by
  let f : J →* J.map π :=
    (π.domRestrict J).codRestrict (J.map π) fun x => Subgroup.mem_map_of_mem π x.2
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hπab : π (a : X) = π (b : X) :=
      congrArg Subtype.val hab
    have hmem : (a : X) / (b : X) ∈ J ⊓ π.ker := by
      refine ⟨J.div_mem a.2 b.2, MonoidHom.mem_ker.mpr ?_⟩
      rw [map_div, hπab, div_eq_one]
    have h1 : (a : X) / (b : X) = 1 :=
      Subgroup.mem_bot.mp ((eq_bot_iff.mp h) hmem)
    exact Subtype.ext (div_eq_one.mp h1)
  have hf_surj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Submonoid.map π J.toSubmonoid := by
      rw [← Subgroup.map_toSubmonoid]
      exact hy
    rcases Submonoid.mem_map.mp hy' with ⟨x, hxJ, hxy⟩
    exact ⟨⟨x, hxJ⟩, Subtype.ext hxy⟩
  let e : J ≃* J.map π := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hmap : Subgroup.map (e : J →* J.map π) (Subgroup.center J) =
      Subgroup.center (J.map π) := Subgroup.map_center_eq e
  have hker_e : (e : J →* J.map π).ker = ⊥ :=
    MonoidHom.ker_eq_bot _ (EquivLike.injective e)
  rw [← hmap, Subgroup.map_eq_bot_iff, hker_e]
  exact eq_bot_iff.symm

theorem leafRCentre_holds :
    ∀ (X : Type) [Group X] (R : Type) [Group R] (θ : X ⧸ Subgroup.center X ≃* R) (J : Subgroup X),
      (Subgroup.center J = ⊥ → Subgroup.center (J.map (proj θ)) = ⊥ ∧ J ⊓ Subgroup.center X = ⊥) ∧
        (Subgroup.center J ≠ ⊥ →
          Subgroup.center (J.map (proj θ)) ≠ ⊥ ∨ J ⊓ Subgroup.center X ≠ ⊥) := by
  intro X _ R _ θ J
  have hker : (proj θ).ker = Subgroup.center X := by
    show (((θ : X ⧸ Subgroup.center X →* R).comp
      (QuotientGroup.mk' (Subgroup.center X))).ker) = Subgroup.center X
    rw [MonoidHom.ker_comp_of_injective _ _ (EquivLike.injective θ), QuotientGroup.ker_mk']
  constructor
  · intro hJ
    have hdisj : J ⊓ Subgroup.center X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxJ : x ∈ J := hx.1
      have hxZ : x ∈ Subgroup.center X := hx.2
      have hcent : (⟨x, hxJ⟩ : J) ∈ Subgroup.center J := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_center_iff.mp hxZ (g : X))
      rw [hJ] at hcent
      have h1 : (⟨x, hxJ⟩ : J) = 1 := Subgroup.mem_bot.mp hcent
      exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val h1)
    have hdisjker : J ⊓ (proj θ).ker = ⊥ := by
      rw [hker]
      exact hdisj
    exact ⟨(center_map_eq_bot_iff_of_injective (proj θ) J hdisjker).mpr hJ, hdisj⟩
  · intro hJ
    by_cases hdisj : J ⊓ Subgroup.center X = ⊥
    · left
      have hdisjker : J ⊓ (proj θ).ker = ⊥ := by
        rw [hker]
        exact hdisj
      intro hc
      exact hJ ((center_map_eq_bot_iff_of_injective (proj θ) J hdisjker).mp hc)
    · right
      exact hdisj

end CFSG.StandardType.TablePThreeKG

end