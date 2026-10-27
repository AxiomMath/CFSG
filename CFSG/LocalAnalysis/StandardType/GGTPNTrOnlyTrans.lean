module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTPNOnlyComp_of_amb {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B : Subgroup G} {x : G} {D J : Subgroup G} {y : G} {K : Subgroup G}
    (hn : GGNbr p B x D J y K) (hx : x ∈ Subgroup.normalizer (K : Set G))
    (h : ∀ S : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer (D : Set G)) S → S = J) :
    GGTPNOnlyComp p (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro J' hJ'
  have hKle : K ≤ Subgroup.centralizer ({y} : Set G) := hn.1.2.2.2.1
  have hKpc : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K := hn.1.2.2.2.2.1
  have hKsub : IsSubnormal K (Subgroup.centralizer ({y} : Set G)) := by
    have hpcK : CFSG.IsPComponent p
        (K.subgroupOf (Subgroup.centralizer ({y} : Set G))) :=
      ((ggLargeEvenPComponent_iff p (Subgroup.centralizer ({y} : Set G)) K).1 hKpc).2
    exact ((ggPComponent_iff_data p hKle).1 hpcK).1
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hn.2.1, Subgroup.centralizer_closure]
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have hCy : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.centralizer_le (fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [hn.2.1]
      exact Subgroup.subset_closure (by simp))
  have hsub : IsSubnormal (K ⊓ Subgroup.centralizer (D : Set G))
      (Subgroup.centralizer (D : Set G)) :=
    CFSG.Assembly.IsSubnormal.inf_of_le hKsub hCy
  have hKCD : K ⊓ Subgroup.centralizer ({x} : Set G) =
      K ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hCD, ← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left hKle)]
  have hσ : ggAutFixedSubgroup (K.normalizerMonoidHom ⟨x, hx⟩) =
      (K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K :=
    ggAutFixedSubgroup_normalizerMonoidHom hx
  rw [hσ] at hJ'
  obtain ⟨hle, hpc⟩ := (ggLargeEvenPComponent_iff p
    ((K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K) J').1 hJ'
  have hCmap : ((K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K).map K.subtype =
      K ⊓ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_left
  have hSle : J'.map K.subtype ≤ K ⊓ Subgroup.centralizer ({x} : Set G) := by
    rw [← hCmap]
    exact Subgroup.map_mono hle
  have hpcS : CFSG.IsPComponent p
      ((J'.map K.subtype).subgroupOf (K ⊓ Subgroup.centralizer ({x} : Set G))) := by
    rw [← hCmap]
    exact ggPComponent_map_subtype p hle hpc
  have hSleD : J'.map K.subtype ≤ K ⊓ Subgroup.centralizer (D : Set G) := by
    rw [← hKCD]
    exact hSle
  have hpcSD : CFSG.IsPComponent p
      ((J'.map K.subtype).subgroupOf (K ⊓ Subgroup.centralizer (D : Set G))) := by
    rw [← hKCD]
    exact hpcS
  have hLE : LargeEvenPComponent p (Subgroup.centralizer (D : Set G)) (J'.map K.subtype) :=
    (ggLargeEvenPComponent_iff p (Subgroup.centralizer (D : Set G)) (J'.map K.subtype)).2
      ⟨hSleD.trans inf_le_right,
        ggPComponent_subgroupOf_of_subnormal p hSleD hsub hpcSD⟩
  have hSJ : J'.map K.subtype = J := h (J'.map K.subtype) hLE
  have hcomap : (J'.map K.subtype).comap K.subtype = J' :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective J'
  rw [← hcomap, hSJ]
  rfl

end CFSG.StandardType

end
