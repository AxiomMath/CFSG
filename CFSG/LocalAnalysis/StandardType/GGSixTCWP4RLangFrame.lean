module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Lift

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section FrameLe

variable {τ : Tag} {Lf : Type} [Field Lf] {X : Type} [Group X] {Γ : Subgroup (ModGL τ Lf)}
  {G₀ B : Subgroup X}

theorem tc_le_of_JLang_le (fr : GGTCUFrame Γ G₀ B) {J K : Subgroup X} (hJG : J ≤ G₀)
    (_hKG : K ≤ G₀) (hJperf : commutator ↥J = ⊤) (h : fr.JLang J ≤ fr.JLang K) : J ≤ K := by
  have hperfJ : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJperf
  set J₀ : Subgroup ↥G₀ := J.subgroupOf G₀
  set K₀ : Subgroup ↥G₀ := K.subgroupOf G₀
  have hperf0 : Group.IsPerfect ↥J₀ :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJG).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJG).symm.surjective
  have hJ₀perf := Subgroup.isPerfect_iff.mp hperf0
  have hle : J₀ ≤ K₀ ⊔ Subgroup.center ↥G₀ := by
    intro j hj
    have hjL : fr.tcLangHom j ∈ fr.JLang J := ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    obtain ⟨_, ⟨k₀, hk₀, rfl⟩, hq⟩ := h hjL
    have hq' : fr.tcLangHom k₀ = fr.tcLangHom j := hq
    have hc : k₀⁻¹ * j ∈ Subgroup.center ↥G₀ := by
      refine fr.tcLangHom_ker _ ?_
      rw [map_mul, map_inv, hq', inv_mul_cancel]
    exact Subgroup.mem_sup_of_normal_right.2 ⟨k₀, hk₀, k₀⁻¹ * j, hc, by simp⟩
  have hJK := perfect_le_of_le_sup_center hJ₀perf hle
  intro x hx
  have hxG : (⟨x, hJG hx⟩ : ↥G₀) ∈ J₀ := Subgroup.mem_subgroupOf.2 hx
  exact Subgroup.mem_subgroupOf.1 (hJK hxG)

end FrameLe

section VecPow

theorem tc_vec_pow {G V : Type*} [Group G] [AddCommGroup V] (vv : G → V)
    (hmul : ∀ u u' : G, vv (u * u') = vv u + vv u') (h1 : vv 1 = 0) (u : G) (n : ℕ) :
    vv (u ^ n) = n • vv u := by
  let f : G →* Multiplicative V :=
    { toFun := fun g => Multiplicative.ofAdd (vv g), map_one' := h1, map_mul' := hmul }
  exact map_pow f u n

theorem tc_vec_of_mem_zpowers {G V : Type*} [Group G] [Finite G] [AddCommGroup V] (vv : G → V)
    (hmul : ∀ u u' : G, vv (u * u') = vv u + vv u') (h1 : vv 1 = 0) {xg u : G}
    (hu : u ∈ Subgroup.zpowers xg) : ∃ n : ℕ, vv u = n • vv xg := by
  have hu' : u ∈ Submonoid.powers xg := mem_powers_iff_mem_zpowers.mpr hu
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hu'
  exact ⟨n, tc_vec_pow vv hmul h1 xg n⟩

end VecPow

end CFSG.StandardType.TableCRes

end
