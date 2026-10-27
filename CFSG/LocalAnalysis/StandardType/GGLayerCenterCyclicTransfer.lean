module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticCover
public import CFSG.RankThree.PartOne.S15K.CentralCover
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType

namespace LayerCC

open CFSG.Assembly

section Subnormal

variable {G : Type*} [Group G]

theorem isSubnormal_inf {A B : Subgroup G} (h : IsSubnormal A B) (D : Subgroup G) :
    IsSubnormal (A ⊓ D) (B ⊓ D) :=
  h.inf D

theorem isSubnormal_of_le {A B D : Subgroup G} (h : IsSubnormal A B) (hAD : A ≤ D)
    (hDB : D ≤ B) : IsSubnormal A D := by
  have h1 := isSubnormal_inf h D
  rwa [inf_eq_left.mpr hAD, inf_eq_right.mpr hDB] at h1

theorem commutator_largeEvenLayer (H : Subgroup G) :
    ⁅LargeEvenLayer H, LargeEvenLayer H⁆ = LargeEvenLayer H := by
  refine le_antisymm (CFSG.RankThree.PartOne.KCUnitary.commutator_self_le _)
    (sSup_le fun K hK => ?_)
  have hKp : ⁅K, K⁆ = K :=
    Subgroup.isPerfect_iff.1 ((TableBSymp.isQuasisimple_iff _).mp hK.2.2).1
  rw [← hKp]
  exact Subgroup.commutator_mono (le_sSup hK) (le_sSup hK)

theorem largeEvenLayer_le (H : Subgroup G) : LargeEvenLayer H ≤ H :=
  sSup_le fun _ hK => hK.1

end Subnormal

section Transfer

variable {X Y : Type*} [Group X] [Group Y] {f : X →* Y} {α : MulAut X} {β : MulAut Y}

theorem ggFix_le_comap (hαβ : ∀ x, f (α x) = β (f x)) : ggFix α ≤ (ggFix β).comap f := by
  intro x hx
  rw [Subgroup.mem_comap, mem_ggFix, ← hαβ, mem_ggFix.mp hx]

theorem inv_mul_apply_mem_ker (hαβ : ∀ x, f (α x) = β (f x)) {c : X}
    (hc : c ∈ (ggFix β).comap f) : c⁻¹ * α c ∈ f.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, hαβ, mem_ggFix.mp (Subgroup.mem_comap.mp hc),
    inv_mul_cancel]

theorem ggFix_normal_comap (hker : f.ker ≤ Subgroup.center X) (hαβ : ∀ x, f (α x) = β (f x)) :
    ((ggFix α).subgroupOf ((ggFix β).comap f)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (ggFix_le_comap hαβ)]
  intro k c hk hc
  have hz := Subgroup.mem_center_iff.mp (hker (inv_mul_apply_mem_ker hαβ hc))
  rw [mem_ggFix] at hk ⊢
  have hαc : α c = c * (c⁻¹ * α c) := (mul_inv_cancel_left c (α c)).symm
  rw [map_mul, map_mul, map_inv, hk, hαc]
  calc c * (c⁻¹ * α c) * k * (c * (c⁻¹ * α c))⁻¹
      = c * ((c⁻¹ * α c) * k) * (c⁻¹ * α c)⁻¹ * c⁻¹ := by group
    _ = c * (k * (c⁻¹ * α c)) * (c⁻¹ * α c)⁻¹ * c⁻¹ := by rw [hz k]
    _ = c * k * c⁻¹ := by group

theorem commutator_le_ggFix {Y' : Subgroup X} (h : ∀ y ∈ Y', y⁻¹ * α y ∈ Subgroup.center X) :
    ⁅Y', Y'⁆ ≤ ggFix α := by
  rw [Subgroup.commutator_le]
  intro y₁ hy₁ y₂ hy₂
  rw [mem_ggFix, map_commutatorElement]
  have e₁ : α y₁ = y₁ * (y₁⁻¹ * α y₁) := (mul_inv_cancel_left y₁ (α y₁)).symm
  have e₂ : α y₂ = y₂ * (y₂⁻¹ * α y₂) := (mul_inv_cancel_left y₂ (α y₂)).symm
  rw [e₁, e₂, CFSG.RankThree.PartOne.S15K.commutator_mul_central_left (h y₁ hy₁),
    CFSG.RankThree.PartOne.S15K.commutator_mul_central_right (h y₂ hy₂)]

theorem isComponentOf_map_ggFix (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center X)
    (hαβ : ∀ x, f (α x) = β (f x)) {K : Subgroup X} (hK : IsComponentOf K (ggFix α)) :
    IsComponentOf (K.map f) (ggFix β) := by
  refine ⟨(Subgroup.map_mono hK.1).trans (Subgroup.map_le_iff_le_comap.mpr (ggFix_le_comap hαβ)),
    ?_, ?_⟩
  · have h1 := TableBSymp.isSubnormal_trans_normal hK.2.1 (ggFix_le_comap hαβ)
      (ggFix_normal_comap hker hαβ)
    have h2 := isSubnormal_map_hom f h1
    rwa [Subgroup.map_comap_eq_self_of_surjective hf] at h2
  · have hKq : CFSG.IsQuasisimple K := (TableBSymp.isQuasisimple_iff _).mp hK.2.2
    have hrange : (f.comp K.subtype).range = K.map f := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_range hKq (f.comp K.subtype)
      (by
        intro x hx
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hx) y))
    rw [hrange] at h
    exact (TableBSymp.isQuasisimple_iff _).mpr h

theorem isComponentOf_commutator_comap_ggFix (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center X) (hαβ : ∀ x, f (α x) = β (f x)) {M : Subgroup Y}
    (hM : IsComponentOf M (ggFix β)) :
    IsComponentOf ⁅M.comap f, M.comap f⁆ (ggFix α) ∧ (⁅M.comap f, M.comap f⁆).map f = M := by
  have hMq : CFSG.IsQuasisimple M := (TableBSymp.isQuasisimple_iff _).mp hM.2.2
  have hMperf : ⁅M, M⁆ = M := Subgroup.isPerfect_iff.1 hMq.1
  have hfix : ⁅M.comap f, M.comap f⁆ ≤ ggFix α := commutator_le_ggFix fun y hy =>
    hker (inv_mul_apply_mem_ker hαβ (Subgroup.comap_mono hM.1 hy))
  refine ⟨⟨hfix, ?_, (TableBSymp.isQuasisimple_iff _).mpr
    (CFSG.RankThree.PartOne.S15K.isQuasisimple_commutator_comap hf hker hMq)⟩,
    CFSG.RankThree.PartOne.S15K.map_commutator_comap hf hMperf⟩
  have hn : ((⁅M.comap f, M.comap f⁆).subgroupOf (M.comap f)).Normal :=
    ⟨fun n hn g => CFSG.RankThree.PartOne.KCUnitary.conj_mem_commutator_self g.2 hn⟩
  have h1 : IsSubnormal ⁅M.comap f, M.comap f⁆ ((ggFix β).comap f) :=
    IsSubnormal.step (CFSG.RankThree.PartOne.KCUnitary.commutator_self_le _) hn
      (isSubnormal_comap_hom f hM.2.1)
  exact isSubnormal_of_le h1 hfix (ggFix_le_comap hαβ)

theorem map_largeEvenLayer_ggFix (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center X)
    (hαβ : ∀ x, f (α x) = β (f x)) :
    (LargeEvenLayer (ggFix α)).map f = LargeEvenLayer (ggFix β) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (isComponentOf_map_ggFix hf hker hαβ hK)
  · refine sSup_le fun M hM => ?_
    obtain ⟨hc, hmap⟩ := isComponentOf_commutator_comap_ggFix hf hker hαβ hM
    rw [← hmap]
    exact Subgroup.map_mono (le_sSup hc)

end Transfer

section Component

variable {X Y : Type*} [Group X] [Group Y]

theorem isComponentOf_largeEvenLayer_of_map (f : X →* Y) (hker : f.ker ≤ Subgroup.center X)
    (C : Subgroup X) (hq : CFSG.IsQuasisimple ((LargeEvenLayer C).map f)) :
    IsComponentOf (LargeEvenLayer C) C := by
  set E := LargeEvenLayer C with hE
  have hEC : E ≤ C := largeEvenLayer_le C
  refine ⟨hEC, IsSubnormal.step hEC ?_ (IsSubnormal.refl C), ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hEC]
    intro k x hk hx
    exact TableBSymp.largeEvenLayer_conj_mem hx hk
  · have hperf : Group.IsPerfect E := Subgroup.isPerfect_iff.2 (commutator_largeEvenLayer C)
    have hsurj := f.subgroupMap_surjective E
    have hkerE : (f.subgroupMap E).ker ≤ Subgroup.center E := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have hx1 : f (x : X) = 1 := by
        simpa using congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hx1)) y)
    exact (TableBSymp.isQuasisimple_iff _).mpr
      ((CFSG.LocalCores.isQuasisimple_iff_of_surjective hperf _ hsurj hkerE).mpr hq)

end Component

end LayerCC

end CFSG.StandardType

end
