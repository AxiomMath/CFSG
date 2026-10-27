module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
public import CFSG.LieType.Steinberg.BruhatWeyl
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

private theorem conj_mem_ggTorus_of_actsAs {K : Type*} [Group K] {D : UniversalRootDatum K}
    {h m : K} {w : (coxeterMatrix D.isFiniteType).Group} (hh : h ∈ ggTorus D)
    (hm : ActsAs D m w) : m * h * m⁻¹ ∈ ggTorus D := by
  refine Subgroup.mem_iInf.mpr fun δ => Subgroup.mem_iInf.mpr fun hδ => ?_
  have hδ' : weylAction D.isFiniteType w⁻¹ δ ∈ D.roots := weylAction_mem_roots _ _ hδ
  have hN : h ∈ Subgroup.normalizer (D.rootGroup (weylAction D.isFiniteType w⁻¹ δ) : Set K) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh _) hδ'
  rw [mem_normalizer_iff_map_conj, mul_assoc, map_conj_mul, map_conj_mul, hm.inv δ hδ,
    mem_normalizer_iff_map_conj.mp hN, hm _ hδ', weylAction_apply_inv_apply]

private theorem torusElt_mem_ggTorus {K : Type*} [Group K] {D : UniversalRootDatum K}
    {F : Type*} [Field F] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O) (j : Fin D.rank) (s : Fˣ) :
    PsiDiag.torusElt x j s ∈ ggTorus D := by
  refine Subgroup.mem_iInf.mpr fun δ => Subgroup.mem_iInf.mpr fun hδ => ?_
  have hpar := (hE.param δ hδ).1
  have hc := PsiDiag.torusElt_conj hE j s hδ
  refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => ?_, fun hg => ?_⟩
  · obtain ⟨c, rfl⟩ := (hpar g).mp hg
    rw [hc c]
    exact (hpar _).mpr ⟨_, rfl⟩
  · obtain ⟨c, hcg⟩ := (hpar _).mp hg
    have e : g = (PsiDiag.torusElt x j s)⁻¹ * x δ c * PsiDiag.torusElt x j s := by
      rw [hcg]
      group
    rw [e, PsiDiag.inv_conj_of_conj hc c]
    exact (hpar _).mpr ⟨_, rfl⟩

theorem ggStdPos_transitive_of_chevalleyExtras {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {F : Type*} [Field F] [Finite F]
    [CharP F 2] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hE : ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅) :
    ∀ γ ∈ D.roots, ∀ y ∈ D.rootGroup γ, ∀ y' ∈ D.rootGroup γ, y ≠ 1 → y' ≠ 1 →
      ∃ t ∈ ggTorus D, t * y * t⁻¹ = y' := by
  rintro γ (⟨w, j, rfl⟩ | ⟨w, j, hj, -⟩) y hy y' hy' hy1 hy'1
  swap
  · rw [hdiv] at hj
    exact absurd hj (Set.notMem_empty j)
  have hγ : weylAction D.isFiniteType w (Pi.single j 1) ∈ D.roots :=
    weylAction_mem_roots _ w (single_mem_roots j)
  have hm := actsAs_nrep hct w
  set m := nrep hct w
  have hpar := hE.param (Pi.single j 1) (single_mem_roots j)
  have hx0 : x (Pi.single j 1) 0 = 1 := by
    have h := hpar.2.1 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  have hmem : ∀ z ∈ D.rootGroup (weylAction D.isFiniteType w (Pi.single j 1)), z ≠ 1 →
      ∃ a : F, a ≠ 0 ∧ x (Pi.single j 1) a = m⁻¹ * z * m := by
    intro z hz hz1
    have h := hm.inv_conj_mem hγ hz
    rw [weylAction_inv_apply_apply] at h
    obtain ⟨a, ha⟩ := (hpar.1 _).mp h
    refine ⟨a, fun ha0 => hz1 ?_, ha⟩
    rw [ha0, hx0] at ha
    calc z = m * (m⁻¹ * z * m) * m⁻¹ := by group
      _ = 1 := by rw [← ha]; group
  obtain ⟨a, ha0, ha⟩ := hmem y hy hy1
  obtain ⟨b, hb0, hb⟩ := hmem y' hy' hy'1
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (b / a)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact div_ne_zero hb0 ha0 hr
  set s : Fˣ := Units.mk0 r hr0
  have hs : PsiDiag.torusElt x j s * x (Pi.single j 1) a * (PsiDiag.torusElt x j s)⁻¹ =
      x (Pi.single j 1) b := by
    rw [PsiDiag.torusElt_conj hE j s (single_mem_roots j), coroot_single,
      D.isFiniteType.apply_self j]
    congr 1
    show ((s ^ (2 : ℤ) : Fˣ) : F) * a = b
    rw [zpow_two, Units.val_mul, Units.val_mk0, ← hr, div_mul_cancel₀ b ha0]
  refine ⟨m * PsiDiag.torusElt x j s * m⁻¹, conj_mem_ggTorus_of_actsAs
    (torusElt_mem_ggTorus hE j s) hm, ?_⟩
  calc m * PsiDiag.torusElt x j s * m⁻¹ * y * (m * PsiDiag.torusElt x j s * m⁻¹)⁻¹ =
      m * (PsiDiag.torusElt x j s * (m⁻¹ * y * m) * (PsiDiag.torusElt x j s)⁻¹) * m⁻¹ := by
        group
    _ = m * (m⁻¹ * y' * m) * m⁻¹ := by rw [← ha, hs, hb]
    _ = y' := by group

end CFSG.StandardType

end
