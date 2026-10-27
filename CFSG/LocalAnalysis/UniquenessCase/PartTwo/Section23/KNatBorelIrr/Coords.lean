module

public import CFSG.Quasithin.Background.D2Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Fixed
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Quasithin Matrix Subgroup

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def toAut {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)} (π : ↥Γ ≃* ↥H) :
    ↥Γ →* MulAut W :=
  H.subtype.comp π.toMonoidHom

theorem toAut_apply {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)} (π : ↥Γ ≃* ↥H) (γ : ↥Γ) :
    toAut π γ = ((π γ : ↥H) : MulAut W) :=
  rfl

private lemma conj_mem_of_mem_normalizer_L05 {Γ : Subgroup (GL ι K)} {H S : Subgroup (MulAut W)}
    (π : ↥Γ ≃* ↥H) (hS : S ≤ H) {U : Subgroup ↥Γ} (hπU : U.map π.toMonoidHom = S.subgroupOf H)
    {t : ↥Γ} (ht : t ∈ normalizer (U : Set ↥Γ)) {n : MulAut W} (hn : n ∈ S) :
    toAut π t * n * (toAut π t)⁻¹ ∈ S := by
  have ht' : ∀ u : ↥Γ, u ∈ U ↔ t * u * t⁻¹ ∈ U := Subgroup.mem_set_normalizer_iff.mp ht
  have hmemH : (⟨n, hS hn⟩ : ↥H) ∈ U.map π.toMonoidHom := by
    rw [hπU]
    exact Subgroup.mem_subgroupOf.mpr hn
  obtain ⟨u, hu, hπu⟩ : ∃ u ∈ U, π u = ⟨n, hS hn⟩ := Subgroup.mem_map.mp hmemH
  have hconj : t * u * t⁻¹ ∈ U := (ht' u).mp hu
  have hmap : π (t * u * t⁻¹) ∈ U.map π.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨t * u * t⁻¹, hconj, rfl⟩
  rw [hπU] at hmap
  have hmem := Subgroup.mem_subgroupOf.mp hmap
  have hcoe : ((π (t * u * t⁻¹) : ↥H) : MulAut W) = toAut π t * n * (toAut π t)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hπu, toAut_apply]
    rfl
  rwa [hcoe] at hmem

theorem mem_fixV_iff_coord [Finite K] [CharP K 2] {Γ : Subgroup (GL ι K)}
    {H S : Subgroup (MulAut W)} (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K))
    (he : ∀ (γ : ↥Γ) (w : W), Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w))
    (hS : S ≤ H) (U : Sylow 2 ↥Γ) (hπU : (U : Subgroup ↥Γ).map π.toMonoidHom = S.subgroupOf H)
    {e₀ : ι → K} (he0 : e₀ ≠ 0) (hline : KTabC.SylowFixedLine Γ e₀)
    (hU : (U : Subgroup ↥Γ) ≤ KTabD.lineStab Γ e₀) (y : W) :
    y ∈ fixV S ↔ ∃ c : K, Multiplicative.toAdd (e y) = c • e₀ := by
  rw [mem_fixV]
  constructor
  · intro hy
    refine (fixed_iff_of_sylow_le_lineStab he0 hline U hU _).mp fun s hs => ?_
    have hmem : ((π s : ↥H) : MulAut W) ∈ S := by
      have hmap : π s ∈ U.map π.toMonoidHom := Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
      rw [hπU] at hmap
      exact Subgroup.mem_subgroupOf.mp hmap
    have h3 := he s y
    rw [hy ((π s : ↥H) : MulAut W) hmem] at h3
    exact h3.symm
  · rintro ⟨c, hc⟩ s hs
    obtain ⟨u, hu, hπu⟩ : ∃ u ∈ (U : Subgroup ↥Γ), π u = ⟨s, hS hs⟩ := by
      have hmap : (⟨s, hS hs⟩ : ↥H) ∈ U.map π.toMonoidHom := by
        rw [hπU]
        exact Subgroup.mem_subgroupOf.mpr hs
      exact Subgroup.mem_map.mp hmap
    apply e.injective
    apply Multiplicative.toAdd.injective
    have h3 := he u y
    rw [hπu] at h3
    simp only [h3, hc, Matrix.mulVec_smul, mulVec_eq_of_mem_sylow_le_lineStab he0 U hU hu]

theorem toAut_mem_normalizer {Γ : Subgroup (GL ι K)} {H S : Subgroup (MulAut W)}
    (π : ↥Γ ≃* ↥H) (hS : S ≤ H) {U : Subgroup ↥Γ}
    (hπU : U.map π.toMonoidHom = S.subgroupOf H) {t : ↥Γ}
    (ht : t ∈ normalizer (U : Set ↥Γ)) : toAut π t ∈ normalizer (S : Set (MulAut W)) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  constructor
  · exact conj_mem_of_mem_normalizer_L05 π hS hπU ht
  · intro hn
    have htinv : t⁻¹ ∈ normalizer (U : Set ↥Γ) := Subgroup.inv_mem _ ht
    have hh := conj_mem_of_mem_normalizer_L05 π hS hπU htinv hn
    rw [map_inv, inv_inv] at hh
    have hgoal : (toAut π t)⁻¹ * (toAut π t * n * (toAut π t)⁻¹) * toAut π t = n := by
      group
    rwa [hgoal] at hh

theorem normalizer_le_comap_toAut {Γ : Subgroup (GL ι K)} {H S P : Subgroup (MulAut W)}
    (π : ↥Γ ≃* ↥H) (hS : S ≤ H) {U : Subgroup ↥Γ} (hπU : U.map π.toMonoidHom = S.subgroupOf H)
    (hNP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) :
    normalizer (U : Set ↥Γ) ≤ P.comap (toAut π) := by
  intro t ht
  rw [Subgroup.mem_comap]
  exact hNP ⟨(π t).2, toAut_mem_normalizer π hS hπU ht⟩

theorem toAut_mem_hinf_inf_normalizer [Finite W] [Finite K] {Γ : Subgroup (GL ι K)}
    {H S P : Subgroup (MulAut W)} (π : ↥Γ ≃* ↥H) (hS : S ≤ H) (hPH : P ≤ H) {U : Subgroup ↥Γ}
    (hπU : U.map π.toMonoidHom = S.subgroupOf H) {t : ↥Γ}
    (ht : t ∈ Hinf (P.comap (toAut π)) ⊓ normalizer (U : Set ↥Γ)) :
    toAut π t ∈ Hinf P ⊓ normalizer (S : Set (MulAut W)) := by
  have hnorm : toAut π t ∈ normalizer (S : Set (MulAut W)) :=
    toAut_mem_normalizer π hS hπU ht.2
  refine ⟨?_, hnorm⟩
  have hle : P ≤ (toAut π).range := fun p hp =>
    ⟨π.symm ⟨p, hPH hp⟩, by simp [toAut_apply]⟩
  have hmap : (P.comap (toAut π)).map (toAut π) = P := Subgroup.map_comap_eq_self hle
  have h1 : toAut π t ∈ (Hinf (P.comap (toAut π))).map (toAut π) :=
    Subgroup.mem_map.mpr ⟨t, ht.1, rfl⟩
  rw [Hinf_map (toAut π) (P.comap (toAut π)), hmap] at h1
  exact h1

private lemma fixV_map_iff_L05 {Γ : Subgroup (GL ι K)} {H S P : Subgroup (MulAut W)}
    (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K))
    (he : ∀ (γ : ↥Γ) (w : W), Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w))
    (hPH : P ≤ H) {e₀ : ι → K}
    (hcoord : ∀ y : W, y ∈ fixV S ↔ ∃ c : K, Multiplicative.toAdd (e y) = c • e₀)
    {g : MulAut W} (hg : g ∈ P) (hle : P.comap (toAut π) ≤ KTabD.lineStab Γ e₀) (y : W) :
    g y ∈ fixV S ↔ y ∈ fixV S := by
  let γ : ↥Γ := π.symm ⟨g, hPH hg⟩
  have hγg : toAut π γ = g := by
    show ((π γ : ↥H) : MulAut W) = g
    simp [γ]
  have hγmem : γ ∈ P.comap (toAut π) := by
    rw [Subgroup.mem_comap, hγg]
    exact hg
  obtain ⟨c, hc⟩ := KTabD.mem_lineStab.mp (hle hγmem)
  constructor
  · intro hy
    have hginv : g⁻¹ ∈ P := Subgroup.inv_mem _ hg
    let γ' : ↥Γ := π.symm ⟨g⁻¹, hPH hginv⟩
    have hγ'g : toAut π γ' = g⁻¹ := by
      show ((π γ' : ↥H) : MulAut W) = g⁻¹
      simp [γ']
    have hγ'mem : γ' ∈ P.comap (toAut π) := by
      rw [Subgroup.mem_comap, hγ'g]
      exact hginv
    obtain ⟨d, hd⟩ := KTabD.mem_lineStab.mp (hle hγ'mem)
    obtain ⟨b, hb⟩ := (hcoord (g y)).mp hy
    refine (hcoord y).mpr ⟨b * d, ?_⟩
    have hmat : Multiplicative.toAdd (e (g⁻¹ (g y))) =
        ((γ' : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e (g y)) := by
      rw [← hγ'g, toAut_apply]
      exact he γ' (g y)
    rw [show g⁻¹ (g y) = y by simp] at hmat
    rw [hmat, hb, Matrix.mulVec_smul, hd, smul_smul]
  · intro hy
    obtain ⟨a, ha⟩ := (hcoord y).mp hy
    refine (hcoord (g y)).mpr ⟨a * c, ?_⟩
    have hmat : Multiplicative.toAdd (e (g y)) =
        ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e y) := by
      rw [← hγg, toAut_apply]
      exact he γ y
    rw [hmat, ha, Matrix.mulVec_smul, hc, smul_smul]

theorem not_comap_toAut_le_lineStab {Γ : Subgroup (GL ι K)} {H S P : Subgroup (MulAut W)}
    (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K))
    (he : ∀ (γ : ↥Γ) (w : W), Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w))
    (hPH : P ≤ H) {e₀ : ι → K}
    (hcoord : ∀ y : W, y ∈ fixV S ↔ ∃ c : K, Multiplicative.toAdd (e y) = c • e₀)
    (hP : ¬ P ≤ stabSub (fixV S)) : ¬ P.comap (toAut π) ≤ KTabD.lineStab Γ e₀ := by
  intro hle
  apply hP
  intro g hg
  rw [mem_stabSub]
  intro y
  exact fixV_map_iff_L05 π e he hPH hcoord hg hle y

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
