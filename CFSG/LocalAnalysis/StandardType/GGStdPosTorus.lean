module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.TitsSimplicity.Core
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

private theorem conj_mul_center_eq {K : Type*} [Group K] {z : K} (hz : z ∈ Subgroup.center K)
    (a b : K) : a * (b * z) * a⁻¹ = a * b * a⁻¹ * z := by
  rw [Subgroup.mem_center_iff] at hz
  calc a * (b * z) * a⁻¹ = a * b * (z * a⁻¹) := by group
    _ = a * b * (a⁻¹ * z) := by rw [hz a⁻¹]
    _ = a * b * a⁻¹ * z := by group

private theorem mem_borel_of_conj_mem_mul_center {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) {g : K}
    (hg : ∀ γ ∈ D.roots, ∀ y ∈ D.rootGroup γ,
      ∃ y' ∈ D.rootGroup γ, ∃ z ∈ Subgroup.center K, g * y * g⁻¹ = y' * z) :
    g ∈ borel D H := by
  have hZ := LieType.TitsSimplicity.center_le_borel hct hext
  have hU : ∀ u ∈ posUnipotent D, g * u * g⁻¹ ∈ borel D H := fun u hu =>
    conj_mem_of_forall_mem (fun γ hγ y hy => by
      obtain ⟨y', hy', z, hz, he⟩ := hg γ hγ.1 y hy
      rw [he]
      exact mul_mem (rootGroup_le_borel hγ.1 hγ.2 hy') (hZ hz)) hu
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell hct hext g
  by_cases hw1 : w = 1
  · rwa [hw1, bruhatCell_one hct] at hw
  exfalso
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hw
  obtain ⟨i, hi⟩ :=
    (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_rightDescent_of_ne_one hw1
  have hγ : weylAction D.isFiniteType w (Pi.single i 1) ∈ D.roots :=
    weylAction_mem_roots _ w (single_mem_roots i)
  have hact := actsAs_nrep hct w (Pi.single i 1) (single_mem_roots i)
  have hle : D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1)) ≤ borel D H := by
    rw [← hact, map_conj_le_iff]
    intro x hx
    have hx' : b₂⁻¹ * x * b₂ ∈ posUnipotent D := by
      have h := (Subgroup.mem_normalizer_iff.mp
        (borel_le_normalizer_posUnipotent hct (inv_mem hb₂)) x).mp
        (rootGroup_le_posUnipotent (single_mem_roots i) (ht_single_pos i) hx)
      rwa [inv_inv] at h
    have e : nrep hct w * x * (nrep hct w)⁻¹ = b₁⁻¹ * ((b₁ * nrep hct w * b₂) *
        (b₂⁻¹ * x * b₂) * (b₁ * nrep hct w * b₂)⁻¹) * b₁ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hb₁) (hU _ hx')) hb₁
  have hbot : D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1)) = ⊥ := by
    rw [eq_bot_iff, ← hBU.borel_inf_negUnipotent]
    exact le_inf hle (rootGroup_le_negUnipotent hγ (ht_weylAction_single_neg hi))
  exact hext.ne_bot _ hγ hbot

theorem ggStdPos_mem_iSup_torus {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) {g : K}
    (hg : ∀ γ ∈ D.roots, ∀ y ∈ D.rootGroup γ,
      ∃ y' ∈ D.rootGroup γ, ∃ z ∈ Subgroup.center K, g * y * g⁻¹ = y' * z) :
    g ∈ ⨆ i, H i := by
  have hB := mem_borel_of_conj_mem_mul_center hct hext hBU hg
  rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at hB
  obtain ⟨t, ht, v, hv, rfl⟩ := hB
  have hv' : ∀ γ ∈ D.roots, ∀ y ∈ D.rootGroup γ,
      ∃ y' ∈ D.rootGroup γ, ∃ z ∈ Subgroup.center K, v * y * v⁻¹ = y' * z := by
    intro γ hγ y hy
    obtain ⟨y', hy', z, hz, he⟩ := hg γ hγ y hy
    have htN := iSup_le_normalizer_rootGroup hct hγ (inv_mem ht)
    refine ⟨t⁻¹ * y' * t, ?_, z, hz, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp htN y').mp hy'
      rwa [inv_inv] at h
    · calc v * y * v⁻¹ = t⁻¹ * (t * v * y * (t * v)⁻¹) * t⁻¹⁻¹ := by group
        _ = t⁻¹ * y' * t * z := by rw [he, conj_mul_center_eq hz, inv_inv]
  obtain ⟨w₀, hw₀⟩ := LieType.TitsSimplicity.exists_forall_isRightDescent (D := D)
  have hn₀ := actsAs_nrep hct w₀
  have hvB : nrep hct w₀ * v * (nrep hct w₀)⁻¹ ∈ borel D H := by
    refine mem_borel_of_conj_mem_mul_center hct hext hBU fun γ hγ y hy => ?_
    have hγ' : weylAction D.isFiniteType w₀⁻¹ γ ∈ D.roots := weylAction_mem_roots _ _ hγ
    obtain ⟨y', hy', z, hz, he⟩ := hv' _ hγ' _ (hn₀.inv_conj_mem hγ hy)
    refine ⟨nrep hct w₀ * y' * (nrep hct w₀)⁻¹, ?_, z, hz, ?_⟩
    · have h := hn₀.conj_mem hγ' hy'
      rwa [weylAction_apply_inv_apply] at h
    · calc nrep hct w₀ * v * (nrep hct w₀)⁻¹ * y * (nrep hct w₀ * v * (nrep hct w₀)⁻¹)⁻¹ =
          nrep hct w₀ * (v * ((nrep hct w₀)⁻¹ * y * nrep hct w₀) * v⁻¹) * (nrep hct w₀)⁻¹ := by
            group
        _ = nrep hct w₀ * y' * (nrep hct w₀)⁻¹ * z := by rw [he, conj_mul_center_eq hz]
  have hvU := LieType.TitsSimplicity.nrep_conj_mem_negUnipotent_of_forall_isRightDescent hct hw₀ hv
  have h1 : nrep hct w₀ * v * (nrep hct w₀)⁻¹ = 1 := by
    have h := Subgroup.mem_inf.2 ⟨hvB, hvU⟩
    rwa [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at h
  have hv1 : v = 1 := by
    calc v = (nrep hct w₀)⁻¹ * (nrep hct w₀ * v * (nrep hct w₀)⁻¹) * nrep hct w₀ := by group
      _ = 1 := by rw [h1]; group
  rw [hv1, mul_one]
  exact ht

theorem ggStdPos_ggTorus_eq {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) : ggTorus D = ⨆ i, H i := by
  refine le_antisymm (fun h hh => ggStdPos_mem_iSup_torus hct hext hBU fun γ hγ y hy => ?_)
    fun h hh => Subgroup.mem_iInf.mpr fun γ => Subgroup.mem_iInf.mpr fun hγ =>
      iSup_le_normalizer_rootGroup hct hγ hh
  have hN : h ∈ Subgroup.normalizer (D.rootGroup γ : Set K) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh γ) hγ
  exact ⟨h * y * h⁻¹, (Subgroup.mem_normalizer_iff.mp hN y).mp hy, 1, one_mem _,
    (mul_one _).symm⟩

end CFSG.StandardType

end
