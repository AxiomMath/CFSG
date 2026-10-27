module

public import CFSG.LocalAnalysis.StandardType.GGStdPosTorusFix
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusBasic
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.ModelFacts

theorem ggStdPos_actsAs_weylLift {K : Type*} [Group K] {D : UniversalRootDatum K}
    {ν : GGWeyl D →* K} (hν : GGWeylLift D ν) (w : GGWeyl D) : ActsAs D (ν w) w := by
  intro γ hγ
  refine le_antisymm (map_conj_le_iff.mpr fun y hy => hν.conj_mem w γ hγ y hy) fun y hy => ?_
  have h1 := hν.conj_mem w⁻¹ _ (weylAction_mem_roots _ w hγ) y hy
  rw [weylAction_inv_apply_apply, map_inv, inv_inv] at h1
  refine ⟨(ν w)⁻¹ * y * ν w, h1, ?_⟩
  change ν w * ((ν w)⁻¹ * y * ν w) * (ν w)⁻¹ = y
  group

private theorem torusElt_mem_ggTorus_of_param {K : Type*} [Group K] {D : UniversalRootDatum K}
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

theorem ggStdPos_exists_fixFree {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {F : Type*} [Field F] [CharP F 2]
    {x : (Fin D.rank → ℤ) → F → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D F x C O)
    (hdiv : D.divisible = ∅) {s : Fˣ} (hs : s ≠ 1) :
    ∀ γ ∈ D.roots, ∃ t ∈ ⨆ i, H i, ∀ y ∈ D.rootGroup γ, t * y * t⁻¹ = y → y = 1 := by
  rintro γ (⟨w, j, rfl⟩ | ⟨w, j, hj, -⟩)
  swap
  · rw [hdiv] at hj
    exact absurd hj (Set.notMem_empty j)
  have hγ : weylAction D.isFiniteType w (Pi.single j 1) ∈ D.roots :=
    weylAction_mem_roots _ w (single_mem_roots j)
  have hm := actsAs_nrep hct w
  set m := nrep hct w
  set e := PsiDiag.torusElt x j s
  have ht : m * e * m⁻¹ ∈ ⨆ i, H i := by
    rw [← ggStdPos_ggTorus_eq hct hext hBU]
    exact ggStdPos_conj_mem_ggTorus_of_actsAs (torusElt_mem_ggTorus_of_param hE j s) hm
  refine ⟨_, ht, fun y hy hfix => ?_⟩
  have hpar := hE.param (Pi.single j 1) (single_mem_roots j)
  have h1 := hm.inv_conj_mem hγ hy
  rw [weylAction_inv_apply_apply] at h1
  obtain ⟨a, ha⟩ := (hpar.1 _).mp h1
  have h2 : e * x (Pi.single j 1) a * e⁻¹ = x (Pi.single j 1) a := by
    rw [ha]
    calc e * (m⁻¹ * y * m) * e⁻¹ = m⁻¹ * (m * e * m⁻¹ * y * (m * e * m⁻¹)⁻¹) * m := by group
      _ = m⁻¹ * y * m := by rw [hfix]
  rw [PsiDiag.torusElt_conj hE j s (single_mem_roots j), coroot_single,
    D.isFiniteType.apply_self j] at h2
  have h3 := hpar.2.2 h2
  have hs2 : ((s ^ (2 : ℤ) : Fˣ) : F) ≠ 1 := by
    intro h
    apply hs
    apply Units.ext
    apply CharTwo.sq_injective (R := F)
    simp only [zpow_two, Units.val_mul] at h
    simp only [Units.val_one, sq, mul_one]
    exact h
  have ha0 : a = 0 := by
    have h4 : (((s ^ (2 : ℤ) : Fˣ) : F) - 1) * a = 0 := by rw [sub_mul, one_mul, h3, sub_self]
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd (sub_eq_zero.mp h) hs2
    · exact h
  have hx0 : x (Pi.single j 1) 0 = 1 := by
    have h := hpar.2.1 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  calc y = m * (m⁻¹ * y * m) * m⁻¹ := by group
    _ = 1 := by rw [← ha, ha0, hx0]; group

theorem ggStdPos_exists_mem_iSup_mul_nrep_of_normalizer {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {F : Type*}
    [Field F] [CharP F 2] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D F x C O)
    (hdiv : D.divisible = ∅) {s : Fˣ} (hs : s ≠ 1) {k : K}
    (hk : k ∈ Subgroup.normalizer (ggTorus D : Set K)) :
    ∃ h ∈ ⨆ i, H i, ∃ w, k = h * nrep hct w := by
  have hT := ggStdPos_ggTorus_eq hct hext hBU
  exact ChevAut.exists_mem_iSup_mul_nrep_of_forall_conj_mem
    hct hext hBU (ggStdPos_exists_fixFree hct hext hBU hE hdiv hs) (g := k) fun t ht => by
      rw [← hT] at ht ⊢
      exact (Subgroup.mem_normalizer_iff.mp hk t).mp ht

theorem ggStdPos_exists_actsAs_of_mem_normalizer {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {F : Type*}
    [Field F] [CharP F 2] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D F x C O)
    (hdiv : D.divisible = ∅) {s : Fˣ} (hs : s ≠ 1) {k : K}
    (hk : k ∈ Subgroup.normalizer (ggTorus D : Set K)) : ∃ w, ActsAs D k w := by
  obtain ⟨h, hh, w, rfl⟩ :=
    ggStdPos_exists_mem_iSup_mul_nrep_of_normalizer hct hext hBU hE hdiv hs hk
  refine ⟨w, ?_⟩
  have h1 := (actsAs_of_mem_iSup hct hh).mul (actsAs_nrep hct w)
  rwa [one_mul] at h1

theorem ggStdPos_mem_normalizer_ggTorus_iff {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {F : Type*} [Field F] [CharP F 2]
    {x : (Fin D.rank → ℤ) → F → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D F x C O)
    (hdiv : D.divisible = ∅) {s : Fˣ} (hs : s ≠ 1) {ν : GGWeyl D →* K} (hν : GGWeylLift D ν)
    (k : K) :
    k ∈ Subgroup.normalizer (ggTorus D : Set K) ↔ ∃ h ∈ ggTorus D, ∃ w, k = h * ν w := by
  constructor
  · intro hk
    obtain ⟨w, hw⟩ := ggStdPos_exists_actsAs_of_mem_normalizer hct hext hBU hE hdiv hs hk
    have h1 := hw.mul (ggStdPos_actsAs_weylLift hν w).inv
    rw [mul_inv_cancel] at h1
    refine ⟨k * (ν w)⁻¹, Subgroup.mem_iInf.mpr fun γ => Subgroup.mem_iInf.mpr fun hγ => ?_, w,
      by group⟩
    rw [mem_normalizer_iff_map_conj, h1 γ hγ, map_one, Module.End.one_apply]
  · rintro ⟨h, hh, w, rfl⟩
    have hν' := ggStdPos_actsAs_weylLift hν w
    refine mul_mem (Subgroup.le_normalizer hh) (Subgroup.mem_normalizer_iff.mpr fun t => ⟨fun ht =>
      ggStdPos_conj_mem_ggTorus_of_actsAs ht hν', fun ht => ?_⟩)
    have h2 := ggStdPos_conj_mem_ggTorus_of_actsAs ht hν'.inv
    have e : (ν w)⁻¹ * (ν w * t * (ν w)⁻¹) * (ν w)⁻¹⁻¹ = t := by group
    rwa [e] at h2

end CFSG.StandardType

end
