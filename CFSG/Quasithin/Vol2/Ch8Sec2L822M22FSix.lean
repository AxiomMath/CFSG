module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.HMathieuStatements

public section

namespace CFSG.Quasithin.H13.M22F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H.Mathieu
open scoped Pointwise

section Images

variable {G : Type} [Group G]

theorem autOn_eq_range_m22f {V H : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G)) :
    autOn H V = ((conjAct V).comp (Subgroup.inclusion hH)).range := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨n, hn, rfl⟩ := AutOn.mem_autOn_iff.mp hφ
    exact ⟨⟨(n : G), hn⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact AutOn.mem_autOn_iff.mpr ⟨Subgroup.inclusion hH x, x.2, rfl⟩

theorem autOn_eq_map_m22f {V T K : Subgroup G} (hTK : T ≤ K) (hKN : K ≤ Subgroup.normalizer (V : Set G)) :
    autOn T V = (T.subgroupOf K).map ((conjAct V).comp (Subgroup.inclusion hKN)) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨n, hn, rfl⟩ := AutOn.mem_autOn_iff.mp hφ
    exact ⟨⟨(n : G), hTK hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact AutOn.mem_autOn_iff.mpr ⟨Subgroup.inclusion hKN x, Subgroup.mem_subgroupOf.mp hx, rfl⟩

theorem autOn_inf_normalizer_m22f (M V : Subgroup G) :
    autOn (M ⊓ Subgroup.normalizer (V : Set G)) V = autOn M V := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨n, hn, rfl⟩ := AutOn.mem_autOn_iff.mp hφ
    exact AutOn.mem_autOn_iff.mpr ⟨n, (Subgroup.mem_inf.mp hn).1, rfl⟩
  · intro hφ
    obtain ⟨n, hn, rfl⟩ := AutOn.mem_autOn_iff.mp hφ
    exact AutOn.mem_autOn_iff.mpr ⟨n, Subgroup.mem_inf.mpr ⟨hn, n.2⟩, rfl⟩

theorem rk_eq_of_sylowTwo_m22f [Finite G] {T : Subgroup G} (hT : quasithinIsSylowTwo T) :
    rk ↥T = rk G := by
  have h := CFSG.Quasithin.rk_add_rkIdx T
  have h0 : CFSG.Quasithin.rkIdx T = 0 := by
    unfold CFSG.Quasithin.rkIdx
    exact padicValNat.eq_zero_of_not_dvd hT.2
  omega

end Images

section Core

variable {G : Type} [Group G] [Finite G]

theorem orderOf_conjAct_dvd_m22f {V : Subgroup G} {g : G} (hgN : g ∈ Subgroup.normalizer (V : Set G)) :
    orderOf (conjAct V ⟨g, hgN⟩) ∣ orderOf g := by
  have h := orderOf_map_dvd (conjAct V) (⟨g, hgN⟩ : Subgroup.normalizer (V : Set G))
  rwa [Subgroup.orderOf_mk] at h

end Core

end CFSG.Quasithin.H13.M22F
