module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (spScalars ker_proj proj_surjective spScalars_le_center)
open CFSG.HardMathSupport.Solomon.Coordinator
  (fixSubgroup mem_fixSubgroup map_fixSubgroup_le normal_map_fixSubgroup)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary

private theorem ggK1CCm_ggFixSub_eq_fixSubgroup {X : Type*} [Group X] (e : MulAut X) :
    ggFixSub e = fixSubgroup e := by
  ext l
  rw [mem_ggFixSub, mem_fixSubgroup]

private theorem ggK1CCm_fixSub_conj_eq_centralizer {X : Type*} [Group X] (x : X) :
    ggFixSub (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_ggFixSub, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

private theorem ggK1CCm_fixSubgroup_conj_eq_centralizer {X : Type*} [Group X] (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) :=
  (ggK1CCm_ggFixSub_eq_fixSubgroup (MulAut.conj x)).symm.trans
    (ggK1CCm_fixSub_conj_eq_centralizer x)

private theorem ggK1CCm_commutator_normal_self {G : Type*} [Group G] (H : Subgroup G) :
    ((⁅H, H⁆).subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.commutator_le_self H)]
  intro h k hh hk
  have hmap : H.map (MulAut.conj k).toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hk hy) (H.inv_mem hk)
  have h1 : (⁅H, H⁆).map (MulAut.conj k).toMonoidHom ≤ ⁅H, H⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmap hmap
  exact h1 ⟨h, hh, rfl⟩

private theorem ggK1CCm_iSup_conj_mem {G : Type*} [Group G] {ι : Type*}
    (A : ι → Subgroup G)
    (hc : ∀ i j : ι, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (i : ι) :
    ∀ c ∈ ⨆ j, A j, ∀ g ∈ A i, c * g * c⁻¹ ∈ A i := by
  intro c hc'
  refine Subgroup.iSup_induction A (C := fun c => ∀ g ∈ A i, c * g * c⁻¹ ∈ A i) hc' ?_ ?_ ?_
  · intro j y hy g hg
    by_cases hji : j = i
    · rw [← hji] at hg ⊢
      exact (A j).mul_mem ((A j).mul_mem hy hg) ((A j).inv_mem hy)
    · rw [(hc j i hji y hy g hg).eq, mul_inv_cancel_right]
      exact hg
  · intro g hg
    simpa using hg
  · intro u v hu hv g hg
    have e : u * v * g * (u * v)⁻¹ = u * (v * g * v⁻¹) * u⁻¹ := by group
    rw [e]
    exact hu _ (hv g hg)

private theorem ggK1CCm_iSup_normal {G : Type*} [Group G] {ι : Type*}
    (A : ι → Subgroup G)
    (hc : ∀ i j : ι, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (i : ι) :
    ((A i).subgroupOf (⨆ j, A j)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (le_iSup A i)]
  intro h k hh hk
  exact ggK1CCm_iSup_conj_mem A hc i k hk h hh

private theorem ggK1CCm_not_le_ker_of_isQuasisimple {X T : Type*} [Group X] [Group T]
    (π : X →* T) (hker : π.ker ≤ Subgroup.center X) {K : Subgroup X}
    (hK : CFSG.IsQuasisimple ↥K) : ¬ K ≤ π.ker := by
  intro hKπ
  obtain ⟨-, -, a, b, hab⟩ := hK
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine hab ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_center_iff.1 (hker (hKπ x.2)) y).symm

theorem ggK1CCo_component_eq {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {m : List ℕ} (F : ggK1CCo_Family p nf d r K x m)
    {J : Subgroup (StatedProj (StatedSp r K))}
    (hJ : CFSG.Assembly.IsComponentOf J (ggFixSub (MulAut.conj (proj r K x)))) :
    ∃ i : F.ι, CFSG.IsQuasisimple ↥⁅F.A i, F.A i⁆ ∧
      J = (⁅F.A i, F.A i⁆).map (proj r K) := by
  classical
  haveI : Finite F.ι := F.fin
  haveI : Finite (StatedProj (StatedSp r K)) := inferInstance
  have hJ' : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (proj r K x))) := by
    rw [ggK1CCm_ggFixSub_eq_fixSubgroup] at hJ
    exact (CFSG.Assembly.isComponentOf_iff_open).mp hJ
  have hker : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [ker_proj]
    exact spScalars_le_center
  have hmain :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_conj_of_orbit_family
      (X := StatedSp r K) (T := StatedProj (StatedSp r K)) (proj r K)
      (proj_surjective (r := r) (K := K)) hker x F.A F.hcomm F.hjoin F.htame
  obtain ⟨i, hq, hJeq⟩ := hmain J hJ'
  exact ⟨i, hq, hJeq⟩

theorem ggK1CCo_factor_component {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {m : List ℕ} (F : ggK1CCo_Family p nf d r K x m)
    (i : F.ι) (hq : CFSG.IsQuasisimple ↥⁅F.A i, F.A i⁆) :
    CFSG.Assembly.IsComponentOf ((⁅F.A i, F.A i⁆).map (proj r K))
      (ggFixSub (MulAut.conj (proj r K x))) := by
  classical
  have hαβ : ∀ k : StatedSp r K,
      proj r K (MulAut.conj x k) = MulAut.conj (proj r K x) (proj r K k) := by
    intro k
    simp only [MulAut.conj_apply, map_mul, map_inv]
  have hker : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [ker_proj]
    exact spScalars_le_center
  have hsub1 : CFSG.Assembly.IsSubnormal ⁅F.A i, F.A i⁆ (F.A i) :=
    CFSG.Assembly.IsSubnormal.step (Subgroup.commutator_le_self (F.A i))
      (ggK1CCm_commutator_normal_self (F.A i)) (CFSG.Assembly.IsSubnormal.refl _)
  have hsub2 : CFSG.Assembly.IsSubnormal (F.A i) (⨆ j : F.ι, F.A j) :=
    CFSG.Assembly.IsSubnormal.step (le_iSup F.A i)
      (ggK1CCm_iSup_normal F.A F.hcomm i) (CFSG.Assembly.IsSubnormal.refl _)
  have hsubX : CFSG.Assembly.IsSubnormal ⁅F.A i, F.A i⁆ (⨆ j : F.ι, F.A j) :=
    hsub1.trans hsub2
  have hsubXmap : CFSG.Assembly.IsSubnormal ((⁅F.A i, F.A i⁆).map (proj r K))
      ((⨆ j : F.ι, F.A j).map (proj r K)) :=
    hsubX.map (proj r K)
  have hC_le : (⨆ j : F.ι, F.A j).map (proj r K) ≤
      ggFixSub (MulAut.conj (proj r K x)) := by
    rw [F.hjoin, ← ggK1CCm_fixSubgroup_conj_eq_centralizer x,
      ggK1CCm_ggFixSub_eq_fixSubgroup (MulAut.conj (proj r K x))]
    exact map_fixSubgroup_le (proj r K) hker (MulAut.conj x)
      (MulAut.conj (proj r K x)) hαβ
  have hC_norm : (((⨆ j : F.ι, F.A j).map (proj r K)).subgroupOf
      (ggFixSub (MulAut.conj (proj r K x)))).Normal := by
    rw [F.hjoin, ← ggK1CCm_fixSubgroup_conj_eq_centralizer x,
      ggK1CCm_ggFixSub_eq_fixSubgroup (MulAut.conj (proj r K x))]
    exact normal_map_fixSubgroup (proj r K) hker (MulAut.conj x)
      (MulAut.conj (proj r K x)) hαβ (proj_surjective (r := r) (K := K))
  have hsubTop : CFSG.Assembly.IsSubnormal ((⨆ j : F.ι, F.A j).map (proj r K))
      (ggFixSub (MulAut.conj (proj r K x))) :=
    CFSG.Assembly.IsSubnormal.step hC_le hC_norm (CFSG.Assembly.IsSubnormal.refl _)
  have hsub : CFSG.Assembly.IsSubnormal ((⁅F.A i, F.A i⁆).map (proj r K))
      (ggFixSub (MulAut.conj (proj r K x))) :=
    hsubXmap.trans hsubTop
  have hnotker : ¬ ⁅F.A i, F.A i⁆ ≤ (proj r K).ker :=
    ggK1CCm_not_le_ker_of_isQuasisimple (proj r K) hker hq
  have hqs_img : CFSG.IsQuasisimple ↥((⁅F.A i, F.A i⁆).map (proj r K)) :=
    CFSG.LocalCores.isQuasisimple_map hq (proj r K) hnotker
  exact ⟨hsub.le, hsub, ⟨hqs_img.1.commutator_eq_top, hqs_img.2.1⟩⟩

end CFSG.StandardType

end
