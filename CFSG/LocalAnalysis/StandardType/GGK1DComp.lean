module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.Assembly.Subnormal
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial)
open CFSG.RankThree.Classical (IsReciprocalTransversal)

private theorem ggK1Dc_ggFixSub_eq_fixSubgroup {X : Type*} [Group X] (e : MulAut X) :
    ggFixSub e = fixSubgroup e := by
  ext l
  rw [mem_ggFixSub, mem_fixSubgroup]

private theorem ggK1Dc_fixSub_conj_eq_centralizer {X : Type*} [Group X] (x : X) :
    ggFixSub (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_ggFixSub, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

private theorem ggK1Dc_commutator_normal_self {G : Type*} [Group G] (H : Subgroup G) :
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

private theorem ggK1Dc_iSup_conj_mem {G : Type*} [Group G] {ι : Type*}
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

private theorem ggK1Dc_iSup_normal {G : Type*} [Group G] {ι : Type*}
    (A : ι → Subgroup G)
    (hc : ∀ i j : ι, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (i : ι) :
    ((A i).subgroupOf (⨆ j, A j)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (le_iSup A i)]
  intro h k hh hk
  exact ggK1Dc_iSup_conj_mem A hc i k hk h hh

theorem ggK1DCo_component_eq {p nf d : ℕ} {tw : Bool} {r : ℕ} {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι] {Q : (ι → K) → K}
    {x : ↥(LargeEvenOmega Q)} {m : List ℕ} (F : ggK1DCo_Family p nf d tw r m K Q x)
    {J : Subgroup (LargeEvenProj (LargeEvenOmega Q))}
    (hJ : CFSG.Assembly.IsComponentOf J
      (ggFixSub (MulAut.conj (LargeEvenProjMk (LargeEvenOmega Q) x)))) :
    ∃ q : Σ i, Fin (F.blk i).length,
      CFSG.IsQuasisimple ↥⁅F.A q.1 q.2, F.A q.1 q.2⁆ ∧
        J = ⁅F.A q.1 q.2, F.A q.1 q.2⁆ := by
  classical
  haveI : Finite (LargeEvenProj (LargeEvenOmega Q)) := inferInstance
  have hJ' : CFSG.Open.IsComponentOf J
      (fixSubgroup (MulAut.conj (LargeEvenProjMk (LargeEvenOmega Q) x))) := by
    rw [← ggK1Dc_ggFixSub_eq_fixSubgroup]
    exact (CFSG.Assembly.isComponentOf_iff_open).mp hJ
  haveI : Fintype F.blkIdx := F.fintype
  haveI : Finite (Σ i, Fin (F.blk i).length) := Finite.of_fintype _
  have hmain :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_conj_of_orbit_family
      (X := LargeEvenProj (LargeEvenOmega Q)) (T := LargeEvenProj (LargeEvenOmega Q))
      (MonoidHom.id (LargeEvenProj (LargeEvenOmega Q))) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact bot_le)
      (LargeEvenProjMk (LargeEvenOmega Q) x)
      (fun q : Σ i, Fin (F.blk i).length => F.A q.1 q.2) F.hcomm F.hjoin F.htame
  obtain ⟨q, hq, hJeq⟩ := hmain J hJ'
  refine ⟨q, hq, ?_⟩
  simpa using hJeq

theorem ggK1DCo_factor_component {p nf d : ℕ} {tw : Bool} {r : ℕ} {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι] {Q : (ι → K) → K}
    {x : ↥(LargeEvenOmega Q)} {m : List ℕ} (F : ggK1DCo_Family p nf d tw r m K Q x)
    (q : Σ i, Fin (F.blk i).length)
    (hq : CFSG.IsQuasisimple ↥⁅F.A q.1 q.2, F.A q.1 q.2⁆) :
    CFSG.Assembly.IsComponentOf ⁅F.A q.1 q.2, F.A q.1 q.2⁆
      (ggFixSub (MulAut.conj (LargeEvenProjMk (LargeEvenOmega Q) x))) := by
  classical
  have hsub1 : CFSG.Assembly.IsSubnormal ⁅F.A q.1 q.2, F.A q.1 q.2⁆ (F.A q.1 q.2) :=
    CFSG.Assembly.IsSubnormal.step (Subgroup.commutator_le_self (F.A q.1 q.2))
      (ggK1Dc_commutator_normal_self (F.A q.1 q.2)) (CFSG.Assembly.IsSubnormal.refl _)
  have hsub2 : CFSG.Assembly.IsSubnormal (F.A q.1 q.2)
      (⨆ q' : Σ i, Fin (F.blk i).length, F.A q'.1 q'.2) :=
    CFSG.Assembly.IsSubnormal.step
      (le_iSup (fun q' : Σ i, Fin (F.blk i).length => F.A q'.1 q'.2) q)
      (ggK1Dc_iSup_normal (fun q' : Σ i, Fin (F.blk i).length => F.A q'.1 q'.2) F.hcomm q)
      (CFSG.Assembly.IsSubnormal.refl _)
  have hsubX : CFSG.Assembly.IsSubnormal ⁅F.A q.1 q.2, F.A q.1 q.2⁆
      (⨆ q' : Σ i, Fin (F.blk i).length, F.A q'.1 q'.2) := hsub1.trans hsub2
  have htarget : (⨆ q' : Σ i, Fin (F.blk i).length, F.A q'.1 q'.2) =
      ggFixSub (MulAut.conj (LargeEvenProjMk (LargeEvenOmega Q) x)) := by
    rw [F.hjoin, ggK1Dc_fixSub_conj_eq_centralizer]
  have hsub : CFSG.Assembly.IsSubnormal ⁅F.A q.1 q.2, F.A q.1 q.2⁆
      (ggFixSub (MulAut.conj (LargeEvenProjMk (LargeEvenOmega Q) x))) := by
    rw [← htarget]
    exact hsubX
  exact ⟨hsub.le, hsub, ⟨hq.1.commutator_eq_top, hq.2.1⟩⟩

theorem ggK1DCo_component_inj {p nf d : ℕ} {tw : Bool} {r : ℕ} {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι] {Q : (ι → K) → K}
    {x : ↥(LargeEvenOmega Q)} {m : List ℕ} (F : ggK1DCo_Family p nf d tw r m K Q x)
    {q q' : Σ i, Fin (F.blk i).length}
    (hq : CFSG.IsQuasisimple ↥⁅F.A q.1 q.2, F.A q.1 q.2⁆)
    (hq' : CFSG.IsQuasisimple ↥⁅F.A q'.1 q'.2, F.A q'.1 q'.2⁆)
    (h : ⁅F.A q.1 q.2, F.A q.1 q.2⁆ = ⁅F.A q'.1 q'.2, F.A q'.1 q'.2⁆) : q = q' := by
  classical
  by_contra hne
  have hHle : (⁅F.A q.1 q.2, F.A q.1 q.2⁆ : Subgroup (LargeEvenProj (LargeEvenOmega Q))) ≤
      F.A q.1 q.2 := Subgroup.commutator_le_self _
  have hHle' : (⁅F.A q'.1 q'.2, F.A q'.1 q'.2⁆ : Subgroup (LargeEvenProj (LargeEvenOmega Q))) ≤
      F.A q'.1 q'.2 := Subgroup.commutator_le_self _
  have hcommH : ∀ a b : ↥⁅F.A q.1 q.2, F.A q.1 q.2⁆, a * b = b * a := by
    intro a b
    refine Subtype.ext ?_
    have hb : (b : LargeEvenProj (LargeEvenOmega Q)) ∈ F.A q'.1 q'.2 := hHle' (h ▸ b.2)
    exact (F.hcomm q q' hne a.1 (hHle a.2) b.1 hb).eq
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center ↥⁅F.A q.1 q.2, F.A q.1 q.2⁆) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center ↥⁅F.A q.1 q.2, F.A q.1 q.2⁆) b
  refine hab ?_
  have hxy : (QuotientGroup.mk' (Subgroup.center ↥⁅F.A q.1 q.2, F.A q.1 q.2⁆)) (x * y) =
      (QuotientGroup.mk' (Subgroup.center ↥⁅F.A q.1 q.2, F.A q.1 q.2⁆)) (y * x) := by
    rw [hcommH x y]
  simpa only [map_mul] using hxy

end CFSG.StandardType

end
