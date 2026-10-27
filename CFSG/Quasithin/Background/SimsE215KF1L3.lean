module

public import CFSG.Quasithin.Background.SimsE215KF1Defs

public import CFSG.Quasithin.Vol2.Ch3E213MP5B
import CFSG.Quasithin.Vol2.Ch3E213MP5I
import CFSG.Quasithin.Vol2.E2SevenNS
import CFSG.Quasithin.Background.SimsE210Six
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.SimsE2.KF1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch3E213M
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem pzz_le_centralizer_projUnitriangular {k : Type} [Field k] :
    P5.pzz k ≤ Subgroup.centralizer
      ((projUnitriangular 3 k : Subgroup (projectiveSL 3 k)) :
        Set (projectiveSL 3 k)) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  obtain ⟨c, rfl⟩ := P5.mem_uzz.mp hz₀
  obtain ⟨a, b, d, rfl⟩ := P5.exists_eq_uu hu₀
  rw [← map_mul, ← map_mul, P5.uu_comm]

theorem le_and_centralizer_of_pzz {Y : Type} [Group Y] {K S E : Subgroup Y}
    {k : Type} [Field k] (θ : ↥K ≃* projectiveSL 3 k)
    (hθS : ((S ⊓ K).subgroupOf K).map θ.toMonoidHom = projUnitriangular 3 k)
    (hE : E ≤ ((P5.pzz k).map θ.symm.toMonoidHom).map K.subtype) :
    E ≤ K ∧ E ≤ Subgroup.centralizer ((S ⊓ K : Subgroup Y) : Set Y) := by
  have hθS' : (projUnitriangular 3 k).map θ.symm.toMonoidHom = (S ⊓ K).subgroupOf K := by
    rw [← hθS, P5.map_symm_map]
  have h1 : (P5.pzz k).map θ.symm.toMonoidHom ≤ (S ⊓ K).subgroupOf K := by
    rw [← hθS']
    exact Subgroup.map_mono (P5.pzz_le_pa1.trans P5.pa1_le)
  have h2 : ((P5.pzz k).map θ.symm.toMonoidHom).map K.subtype ≤ S ⊓ K := by
    refine (Subgroup.map_mono h1).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  refine ⟨fun x hx => (h2 (hE hx)).2, ?_⟩
  intro x hx
  have hxTK : x ∈ S ⊓ K := h2 (hE hx)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (hE hx)
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
  have hxθ : θ ⟨x, hxTK.2⟩ ∈ P5.pzz k := by
    have hxKz : (⟨x, hxTK.2⟩ : ↥K) = z := Subtype.ext hzx.symm
    rw [hxKz, ← hwz]
    simpa using hw
  have hyθ : θ ⟨y, hy.2⟩ ∈ projUnitriangular 3 k := by
    rw [← hθS]
    exact ⟨⟨y, hy.2⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp
    (pzz_le_centralizer_projUnitriangular (k := k) hxθ)
  have hxy : (⟨y, hy.2⟩ : ↥K) * ⟨x, hxTK.2⟩ = ⟨x, hxTK.2⟩ * ⟨y, hy.2⟩ := by
    apply θ.injective
    rw [map_mul, map_mul]
    exact hcomm _ hyθ
  exact congrArg Subtype.val hxy

theorem star_normal_centralizer_of_l3 {G : Type} [Group G] [Finite G]
    {H T M V K : Subgroup G} (hS : Setting H T M V K) (h2 : Case2 H T M K) {n : ℕ}
    (hPSL : IsPSL 3 2 n ↥(E2.star M H K)) :
    (E2.star M H K).Normal ∧
      ∀ a : E2.StarQuot M H, (∀ x ∈ E2.star M H K, a * x = x * a) → a = 1 := by
  have hFin := E2P.finite_starQuot M H
  have hmp := hS.hyp.minParabolic
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hKnH : (K.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH, hS.eq_sup]
    exact sup_le Subgroup.le_normalizer h2.1
  have hKn : (E2.star M H K).Normal := by
    have h := hKnH.map (E2P.starMap M H) (E2P.starMap_surjective M H)
    simpa [E2.star] using h
  have hKN : (⊤ : Subgroup (E2.StarQuot M H)) ≤
      Subgroup.normalizer (E2.star M H K : Set (E2.StarQuot M H)) := by
    simp [Subgroup.normalizer_eq_top_iff.mpr hKn]
  have hs : IsSimpleGroup ↥(E2.star M H K) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 n hPSL).2
  have hKperf : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hS.mem_cComp
  have hNontrivial := hs.toNontrivial
  have hnab : ∃ a b : ↥(E2.star M H K), a * b ≠ b * a :=
    E2.nonabelian_of_perfect_of_surjective
      (((E2P.starMap M H).subgroupMap (K.subgroupOf H)).comp
        (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      (((E2P.starMap M H).subgroupMap_surjective _).comp
        (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective)
  have hKT : E2.star M H K ⊔ E2.star M H T = ⊤ := by
    rw [← E2.star_sup hKH hmp.isSylow.1, ← hS.eq_sup, E2P.star_top]
  have hcent := E2.centralizer_eq_bot_of_simple (E2P.minParabolic_star hmp)
    (E2P.kerIn_star M H) hKn hs hnab hKT
  refine ⟨hKn, ?_⟩
  intro a ha
  have ha' : a ∈ Subgroup.centralizer (E2.star M H K : Set (E2.StarQuot M H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (ha x hx).symm
  rw [hcent, Subgroup.mem_bot] at ha'
  exact ha'

theorem pkgL3KF1 : PkgL3KF1 := by
  intro G _ _ H T M V K hS h2 n hn hPSL hD hB
  have hmp := hS.hyp.minParabolic
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  obtain ⟨hKn, hC⟩ := star_normal_centralizer_of_l3 hS h2 hPSL
  have hKN : (⊤ : Subgroup (E2.StarQuot M H)) ≤
      Subgroup.normalizer (E2.star M H K : Set (E2.StarQuot M H)) := by
    simp [Subgroup.normalizer_eq_top_iff.mpr hKn]
  have hTK' : E2.star M H (T ⊓ K) = E2.star M H T ⊓ E2.star M H K :=
    E2P.star_inf_T hmp.isSylow hS.mem_cComp.2.2.1 hKH
  rw [hTK'] at hD
  have hMK := E2.star_inf_eq_of_isBorelIn hmp hKN hB
  have hTsyl : IsSylowTwoOf (E2.star M H T) ⊤ :=
    CFSG.Quasithin.SimsE210.Six.isSylowTwoOf_star_of hmp.isSylow
  have hSB : E2.star M H T ≤ E2.star M H M := E2.star_mono hmp.le
  have hES : E2.star M H V ≤ E2.star M H T := E2.star_mono hS.hyp.le_T
  have hSE : E2.star M H T ≤
      Subgroup.normalizer (E2.star M H V : Set (E2.StarQuot M H)) := by
    rintro _ ⟨⟨t, htH⟩, ht, rfl⟩
    exact E2.starMap_mem_normalizer htH (hS.hyp.normal_T (Subgroup.mem_subgroupOf.mp ht))
  have hVstar : IsElemAbelian 2 (E2.star M H V) := by
    have h := (hS.hyp.elem.subgroupOf H).map (E2P.starMap M H)
    simpa [E2.star, E2P.starMap] using h
  have hE2 : ∀ x ∈ E2.star M H V, x * x = 1 := fun x hx =>
    IsElemAbelian.mul_self_eq_one hVstar hx
  have hBorel : ∃ S₀ : Subgroup (E2.StarQuot M H), IsSylowTwoOf S₀ (E2.star M H K) ∧
      E2.star M H M ⊓ E2.star M H K =
        E2.star M H K ⊓ Subgroup.normalizer (S₀ : Set (E2.StarQuot M H)) :=
    ⟨E2.star M H T ⊓ E2.star M H K, A4.isSylowTwoOf_inf_normal hTsyl le_top hKN, hMK⟩
  obtain ⟨k, _, _, _, θ, -, hθS, -, hEZ⟩ :=
    P5.model_of_setting hTsyl hC hPSL hD hBorel hSB hES hSE hE2
  obtain ⟨hVK, hVcent⟩ := le_and_centralizer_of_pzz θ hθS hEZ
  exact ⟨E2.star M H K, hKn, hVK, hVcent⟩

end CFSG.Quasithin.SimsE2.KF1
