module

public import CFSG.Quasithin.Background.SimsE215KF1Defs
public import CFSG.Quasithin.Vol2.Ch3E213MP6EJ
public import CFSG.Quasithin.Background.RonanE27Model
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
public import CFSG.Quasithin.Background.RonanE27S6

public section

namespace CFSG.Quasithin.SimsE2.KF1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch3E213M
  CFSG.Quasithin.Ch3E213M.P6E CFSG.Quasithin.RonanE27
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)

theorem centralizer_of_map_S06_Z6 {A : Type} [Group A] {K E S : Subgroup A}
    (χ : ↥(K ⊔ E) ≃* Equiv.Perm (Fin 6))
    (hSF : ((S ⊓ (K ⊔ E)).subgroupOf (K ⊔ E)).map χ.toMonoidHom = S06)
    (hEZ : (E.subgroupOf (K ⊔ E)).map χ.toMonoidHom = Z6) :
    E ≤ Subgroup.centralizer ((S ⊓ (K ⊔ E) : Subgroup A) : Set A) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hsv : (⟨s, hs.2⟩ : ↥(K ⊔ E)) * ⟨v, Subgroup.mem_sup_right hv⟩ =
      ⟨v, Subgroup.mem_sup_right hv⟩ * ⟨s, hs.2⟩ := by
    apply χ.injective
    rw [map_mul, map_mul]
    have hv' : χ ⟨v, Subgroup.mem_sup_right hv⟩ ∈ Z6 := by
      rw [← hEZ]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hv)
    have hs' : χ ⟨s, hs.2⟩ ∈ S06 := by
      rw [← hSF]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hs.1, hs.2⟩)
    exact (RonanE27.Z6_comm hv' hs').symm
  exact congrArg Subtype.val hsv

theorem sp4One_bar_central {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}
    (hS : Setting H T M V K) (h2 : Case2 H T M K)
    (hSp : E2.IsSp4Prime 1 ↥(E2.star M H K))
    (hD : E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)))
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) :
    (V.subgroupOf H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) ≤
      Subgroup.centralizer (((T.subgroupOf H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) ⊓
        ((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) ⊔
          (V.subgroupOf H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤))) :
        Subgroup (↥H ⧸ kerIn (M.subgroupOf H) ⊤)) : Set (↥H ⧸ kerIn (M.subgroupOf H) ⊤)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKN, hSsyl, hCK, hAlt, hKS, hdiag, hBorel, hSB, hES, hSE, hE2, hE4⟩ :=
    sp4One_model_hyps hS h2 hSp hD hB
  have hKbN : (barIn M H K).Normal := hKN
  obtain ⟨χ, -, hBF, hSF, hEZ, -⟩ :=
    RonanE27.model_sp4_one_coord (K := barIn M H K) (S := barIn M H T)
      (B := barIn M H M) (E := barIn M H V) hSsyl hCK hAlt hKS hdiag hBorel hSB hES hSE hE2 hE4
  have hK₀ := map_oddResidualPreimage_eq_of_case2 hS h2
  have hcent := centralizer_of_map_S06_Z6 χ hSF hEZ
  simpa only [barIn, hK₀] using hcent

theorem pkgSp4OneKF1 : PkgSp4OneKF1 := by
  intro G _ _ H T M V K hS h2 hSp hD hB
  have hmp := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hcent := sp4One_bar_central hS h2 hSp hD hB
  set D := kerIn (M.subgroupOf H) (⊤ : Subgroup H) with hDdef
  set π := QuotientGroup.mk' D with hπdef
  set e := starEquiv hMH with he
  have hK₀ := map_oddResidualPreimage_eq_of_case2 hS h2
  have hKe : ((oddResidualPreimage H).map π).map e.toMonoidHom = E2.star M H K := by
    rw [hK₀]
    exact map_barIn_starEquiv hMH K
  have hTe : ((T.subgroupOf H).map π).map e.toMonoidHom = E2.star M H T :=
    map_barIn_starEquiv hMH T
  have hVe : ((V.subgroupOf H).map π).map e.toMonoidHom = E2.star M H V :=
    map_barIn_starEquiv hMH V
  set Sbar := (T.subgroupOf H).map π ⊓
    ((oddResidualPreimage H).map π ⊔ (V.subgroupOf H).map π) with hSbar
  have hcent_star : E2.star M H V ≤
      Subgroup.centralizer ((E2.star M H T ⊓ (E2.star M H K ⊔ E2.star M H V) :
        Subgroup (E2.StarQuot M H)) : Set (E2.StarQuot M H)) := by
    have hmap_cent : (Subgroup.centralizer (Sbar : Set (↥H ⧸ D))).map e.toMonoidHom =
        Subgroup.centralizer ((Sbar.map e.toMonoidHom : Subgroup (E2.StarQuot M H)) :
          Set (E2.StarQuot M H)) := by
      rw [Subgroup.coe_map]
      exact CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv e _
    rw [← hVe, ← hTe, ← hKe, ← Subgroup.map_sup, ← Subgroup.map_inf _ _ _ e.injective,
      ← hSbar, ← hmap_cent]
    exact Subgroup.map_mono (hSbar.symm ▸ hcent)
  have hKnH : (K.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH, hS.eq_sup]
    exact sup_le Subgroup.le_normalizer h2.1
  have hKstar : (E2.star M H K).Normal := by
    rw [E2P.star_def]
    exact hKnH.map _ (E2P.starMap_surjective M H)
  have hTV : (T.subgroupOf H) ≤ Subgroup.normalizer (V.subgroupOf H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hVH]
    intro t ht
    exact hS.hyp.normal_T ht
  have hTnorm : E2.star M H T ≤
      Subgroup.normalizer (E2.star M H V : Set (E2.StarQuot M H)) := by
    rw [E2P.star_def, E2P.star_def]
    exact (Subgroup.map_mono hTV).trans (Subgroup.le_normalizer_map (E2P.starMap M H))
  have hKT : E2.star M H K ⊔ E2.star M H T = ⊤ := by
    rw [E2P.star_def, E2P.star_def, ← Subgroup.map_sup,
      ← Subgroup.subgroupOf_sup hKH hTH, hS.eq_sup, ← E2P.star_def, E2P.star_top]
  have hF0_normal : (E2.star M H K ⊔ E2.star M H V).Normal := by
    have hle : E2.star M H K ⊔ E2.star M H T ≤
        Subgroup.normalizer ((E2.star M H K ⊔ E2.star M H V :
          Subgroup (E2.StarQuot M H)) : Set (E2.StarQuot M H)) := by
      refine sup_le (le_sup_left.trans Subgroup.le_normalizer) fun s hs => ?_
      refine mem_normalizer_sup ?_ (hTnorm hs)
      rw [Subgroup.normalizer_eq_top_iff.mpr hKstar]
      exact Subgroup.mem_top _
    rw [hKT] at hle
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hle)
  exact ⟨E2.star M H K ⊔ E2.star M H V, hF0_normal, le_sup_right, hcent_star⟩

end CFSG.Quasithin.SimsE2.KF1
