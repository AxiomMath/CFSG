module

public import CFSG.Quasithin.Background.SimsE215KF1Star
import CFSG.Quasithin.Background.B682Ambient
import CFSG.Quasithin.Vol2.Ch3E213MOS2

public section

namespace CFSG.Quasithin.SimsE2.KF1

open scoped commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch3E213M

section Solvable

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem solvableKF1_twoResidual_star_isPGroup {H T M V : Subgroup Γ} (h : E2.Hyp28 H T M V)
    (hsolv : Group.IsSolvable ↥H) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p (twoResidual (⊤ : Subgroup (E2.StarQuot M H))) := by
  obtain ⟨p, hp, hp2, hpH, hZ⟩ := MinParabolic.exists_odd_prime_ambient h.minParabolic hsolv
  refine ⟨p, hp, hp2, ?_⟩
  have hJ : kerIn (E2.star M H M) ⊤ = ⊥ := E2P.kerIn_star M H
  have hsolv' : Group.IsSolvable (E2.StarQuot M H) := by
    let _ : Group.IsSolvable ↥H := hsolv
    exact Group.isSolvable_of_surjective (f := E2P.starMap M H) (E2P.starMap_surjective M H)
  have hZ' : ∀ q : ℕ, q.Prime → q ∣ Nat.card (E2.StarQuot M H) → q = 2 ∨ q = p := by
    intro q hq hqdvd
    have hqdvdH : q ∣ Nat.card ↥H := by
      exact hqdvd.trans (card_dvd_of_surjective _ (E2P.starMap_surjective M H))
    exact hZ q hq hqdvdH
  exact (MinParabolic.twoResidual_isPGroup_of_solvable
    (E2P.minParabolic_star h.minParabolic) hJ hsolv' hZ').1

theorem solvableKF1_twoResidual_star_le {H M I : Subgroup Γ} :
    twoResidual (E2.star M H I) ≤ twoResidual (⊤ : Subgroup (E2.StarQuot M H)) :=
  E1.twoResidual_mono le_top

theorem solvableKF1_exists_decomposition {H T M V I : Subgroup Γ} {g : Γ}
    (h : E2.Hyp28 H T M V) (hI : IsInIHTV H T M V I) (hg : g ∈ I) :
    ∃ y ∈ twoResidual (E2.star M H I), ∃ t ∈ E2.star M H T ⊓ E2.star M H I,
      E2P.starMap M H ⟨g, hI.1 hg⟩ = y * t := by
  have hTI : IsSylowTwoOf (E2.star M H T ⊓ E2.star M H I) (E2.star M H I) :=
    isSylowTwoOf_star_inf_star h.minParabolic.isSylow hI.1 hI.2.2.1
  have hsup : E2.star M H T ⊓ E2.star M H I ⊔ twoResidual (E2.star M H I) = E2.star M H I :=
    sup_twoResidual_eq hTI
  have hnorm : E2.star M H I ≤
      Subgroup.normalizer (twoResidual (E2.star M H I) : Set (E2.StarQuot M H)) :=
    le_normalizer_twoResidual _
  have hN : ((twoResidual (E2.star M H I)).subgroupOf (E2.star M H I)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidual_le _)]
    exact hnorm
  let gstar : ↥(E2.star M H I) := ⟨E2P.starMap M H ⟨g, hI.1 hg⟩, by
    rw [E2P.star_def]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hg)⟩
  have hle1 : twoResidual (E2.star M H I) ≤ E2.star M H I := twoResidual_le _
  have hle2 : E2.star M H T ⊓ E2.star M H I ≤ E2.star M H I := inf_le_right
  have hgmem : gstar ∈ (twoResidual (E2.star M H I)).subgroupOf (E2.star M H I) ⊔
      (E2.star M H T ⊓ E2.star M H I).subgroupOf (E2.star M H I) := by
    rw [← Subgroup.subgroupOf_sup hle1 hle2, sup_comm, hsup, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, t, ht, hyt⟩ := (Subgroup.mem_sup_of_normal_left
    (s := (twoResidual (E2.star M H I)).subgroupOf (E2.star M H I))
    (t := (E2.star M H T ⊓ E2.star M H I).subgroupOf (E2.star M H I))
    (x := gstar)).mp hgmem
  refine ⟨(y : E2.StarQuot M H), Subgroup.mem_subgroupOf.mp hy,
    (t : E2.StarQuot M H), Subgroup.mem_subgroupOf.mp ht, ?_⟩
  have := congrArg Subtype.val hyt
  exact this.symm

omit [Finite Γ] in
theorem solvableKF1_V_star_le_I_star {H M V I : Subgroup Γ} {g : Γ}
    (hgen : I = V ⊔ conjSubgroup V g) :
    E2.star M H V ≤ E2.star M H I := by
  apply Subgroup.map_mono
  rw [hgen]
  exact Subgroup.subgroupOf_mono H le_sup_left

omit [Finite Γ] in
theorem solvableKF1_conj_le_sup {H M V I : Subgroup Γ} {g : Γ} {y : E2.StarQuot M H}
    (hgen : I = V ⊔ conjSubgroup V g) (hy : y ∈ twoResidual (E2.star M H I)) :
    conjSubgroup (E2.star M H V) y ≤
      E2.star M H V ⊔ twoResidual (E2.star M H I) := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have hvy : y * x * y⁻¹ * y * (y * x * y⁻¹)⁻¹ ∈ twoResidual (E2.star M H I) :=
    (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_twoResidual _ (solvableKF1_V_star_le_I_star hgen hx)) y).mp hy
  have hx_eq : x = y⁻¹ * (y * x * y⁻¹ * y * (y * x * y⁻¹)⁻¹) * (y * x * y⁻¹) := by group
  rw [hx_eq, sup_comm]
  exact Subgroup.mul_mem_sup (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hvy) hx

theorem solvableKF1_conj_star_le_sup {H T M V I : Subgroup Γ} {g : Γ}
    (h : E2.Hyp28 H T M V) (hI : IsInIHTV H T M V I) (hg : g ∈ I)
    (hgen : I = V ⊔ conjSubgroup V g) :
    conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hI.1 hg⟩) ≤
      E2.star M H V ⊔ twoResidual (E2.star M H I) := by
  obtain ⟨y, hy, t, ht, hyt⟩ := solvableKF1_exists_decomposition h hI hg
  have hconj : conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hI.1 hg⟩) =
      conjSubgroup (conjSubgroup (E2.star M H V) y) t := by
    rw [hyt, conjSubgroup_conjSubgroup]
  have htV : t⁻¹ ∈ Subgroup.normalizer (E2.star M H V : Set (E2.StarQuot M H)) :=
    Subgroup.inv_mem _ (OS.star_le_normalizer h.normal_T ht.1)
  have htK : t⁻¹ ∈ Subgroup.normalizer (twoResidual (E2.star M H I) : Set (E2.StarQuot M H)) :=
    Subgroup.inv_mem _ (le_normalizer_twoResidual _ ht.2)
  have hmap : (E2.star M H V ⊔ twoResidual (E2.star M H I)).map
      (MulAut.conj t⁻¹).toMonoidHom = E2.star M H V ⊔ twoResidual (E2.star M H I) := by
    rw [Subgroup.map_sup]
    congr 1
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp htV
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp htK
  rw [hconj]
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  rw [← hmap, Subgroup.mem_map_equiv]
  simpa [MulAut.conj_symm_apply] using solvableKF1_conj_le_sup hgen hy hx

theorem solvableKF1_intersection_le {H T M V I : Subgroup Γ} {g : Γ}
    (h : E2.Hyp28 H T M V) (hsolv : Group.IsSolvable ↥H)
    (hI : IsInIHTV H T M V I) (hg : g ∈ I) (hgen : I = V ⊔ conjSubgroup V g) :
    conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hI.1 hg⟩) ⊓ pCoreOf 2 (E2.star M H I) ≤
      E2.star M H V := by
  have hVK := solvableKF1_conj_star_le_sup h hI hg hgen
  intro a ha
  obtain ⟨haV, haO⟩ := Subgroup.mem_inf.mp ha
  have ha_sup : a ∈ E2.star M H V ⊔ twoResidual (E2.star M H I) := hVK haV
  have hV_I : E2.star M H V ≤ E2.star M H I := solvableKF1_V_star_le_I_star hgen
  have haI : a ∈ E2.star M H I := by
    have hle : E2.star M H V ⊔ twoResidual (E2.star M H I) ≤ E2.star M H I :=
      sup_le hV_I (twoResidual_le _)
    exact hle ha_sup
  have hK_N : ((twoResidual (E2.star M H I)).subgroupOf (E2.star M H I)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidual_le _)]
    exact le_normalizer_twoResidual _
  let astar : ↥(E2.star M H I) := ⟨a, haI⟩
  have hastar_sup : astar ∈ (E2.star M H V).subgroupOf (E2.star M H I) ⊔
      (twoResidual (E2.star M H I)).subgroupOf (E2.star M H I) := by
    rw [← Subgroup.subgroupOf_sup hV_I (twoResidual_le _)]
    exact ha_sup
  obtain ⟨k, hk, v, hv, hvk⟩ := (Subgroup.mem_sup_of_normal_left
    (s := (twoResidual (E2.star M H I)).subgroupOf (E2.star M H I))
    (t := (E2.star M H V).subgroupOf (E2.star M H I))
    (x := astar)).mp (by
      rw [sup_comm] at hastar_sup
      exact hastar_sup)
  have hak : a = (k : E2.StarQuot M H) * (v : E2.StarQuot M H) := by
    have := congrArg Subtype.val hvk
    simpa using this.symm
  have hk_eq : (k : E2.StarQuot M H) = a * (v : E2.StarQuot M H)⁻¹ := by
    rw [hak]
    group
  have hk_sup : (k : E2.StarQuot M H) ∈ E2.star M H V ⊔ pCoreOf 2 (E2.star M H I) := by
    rw [hk_eq, sup_comm]
    exact Subgroup.mul_mem_sup haO
      (Subgroup.inv_mem (E2.star M H V) (Subgroup.mem_subgroupOf.mp hv))
  have hk_eq_one : (k : E2.StarQuot M H) = 1 := by
    obtain ⟨p, hp, hp2, hpK⟩ := solvableKF1_twoResidual_star_isPGroup h hsolv
    have : Fact p.Prime := ⟨hp⟩
    have hV2 : IsPGroup 2 (E2.star M H V) := by
      have hVab : IsElemAbelian 2 (E2.star M H V) := by
        simpa [E2P.star_def] using IsElemAbelian.map (h.elem.subgroupOf H) (E2P.starMap M H)
      exact CFSG.Open.IsElemAbelian.isPGroup hVab
    have h2 : IsPGroup 2 ↥(E2.star M H V ⊔ pCoreOf 2 (E2.star M H I)) :=
      hV2.to_sup_of_normal_right' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
        (hV_I.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    exact Subgroup.disjoint_def.mp (IsPGroup.disjoint_of_ne p 2 hp2 _ _ hpK h2)
      (solvableKF1_twoResidual_star_le (Subgroup.mem_subgroupOf.mp hk)) hk_sup
  rw [hak, hk_eq_one, one_mul]
  exact Subgroup.mem_subgroupOf.mp hv

theorem solvableKF1 : SolvableKF1 := by
  intro G _ _ H T M V h hchar hsolv I g hI hg hgen
  apply commutator_le_pCoreOf_of_star h hI.1 hg hgen
  have hI_eq : E2.star M H I = E2.star M H V ⊔
      conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hI.1 hg⟩) := by
    rw [← star_sup_conjSubgroup h (hI.1 hg), hgen]
  have hA_le : conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hI.1 hg⟩) ⊓
      pCoreOf 2 (E2.star M H V ⊔
        conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hI.1 hg⟩)) ≤
      E2.star M H V := by
    rw [← hI_eq]
    exact solvableKF1_intersection_le h hsolv hI hg hgen
  have hVab : IsElemAbelian 2 (E2.star M H V) := by
    have hVab_H : IsElemAbelian 2 (V.subgroupOf H) := h.elem.subgroupOf H
    simpa [E2P.star_def] using IsElemAbelian.map hVab_H (E2P.starMap M H)
  have hcomm_self : ⁅E2.star M H V, E2.star M H V⁆ = ⊥ :=
    Subgroup.commutator_self_eq_bot_iff.mpr hVab.1
  refine bot_unique ?_
  calc ⁅conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hI.1 hg⟩) ⊓
        pCoreOf 2 (E2.star M H V ⊔
          conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hI.1 hg⟩)),
        E2.star M H V⁆
      ≤ ⁅E2.star M H V, E2.star M H V⁆ := Subgroup.commutator_mono hA_le le_rfl
    _ = ⊥ := hcomm_self

end Solvable

end CFSG.Quasithin.SimsE2.KF1
