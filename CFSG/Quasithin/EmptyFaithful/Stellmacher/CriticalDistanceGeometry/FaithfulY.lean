module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.SitSigma
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits

namespace F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open CosetGeom

omit [Finite G] in
theorem conj_mem_omegaOneCenter {T : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) {y : G} (hy : y ∈ quasithinOmegaOneCenter T) :
    g * y * g⁻¹ ∈ quasithinOmegaOneCenter T := by
  obtain ⟨hyT, hyC, hy2⟩ := mem_quasithinOmegaOneCenter_iff.mp hy
  refine mem_quasithinOmegaOneCenter_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hyT,
    Subgroup.mem_centralizer_iff.mpr fun t ht => ?_, ?_⟩
  · have ht' : g⁻¹ * t * g⁻¹⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) t).mp ht
    have h1 := Subgroup.mem_centralizer_iff.mp hyC _ ht'
    calc t * (g * y * g⁻¹) = g * ((g⁻¹ * t * g⁻¹⁻¹) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * t * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * t := by group
  · have h2 : (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := by simp only [pow_two]; group
    rw [h2, hy2]; group

omit [Finite G] in
theorem normalizer_le_normalizer_omegaOneCenter (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer ((quasithinOmegaOneCenter T : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨conj_mem_omegaOneCenter hg, fun hy => ?_⟩
  have := conj_mem_omegaOneCenter (Subgroup.inv_mem _ hg) hy
  simpa [mul_assoc] using this

theorem Zv_le_omegaOneCenter_Qv (hA : F53Amalgam H M S) {δ ν : Geo H M} (hle : Qv δ ≤ Qv ν)
    (hZ : Zv ν ≤ Qv δ) : Zv ν ≤ quasithinOmegaOneCenter (Qv δ) := fun z hz =>
  mem_quasithinOmegaOneCenter_iff.mpr ⟨hZ hz, Subgroup.mem_centralizer_iff.mpr fun t ht =>
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA ν hz).2 t (hle ht),
    (isElemAbelian_Zv hA ν).2 z hz⟩

theorem centralizer_omegaOneCenter_Qv (hA : F53Amalgam H M S) {δ ν : Geo H M} (hν : ν ∈ nbrs δ)
    (hle : Qv δ ≤ Qv ν) (hZ : Zv ν ≤ Qv δ) :
    stab δ ⊓ Subgroup.centralizer ((quasithinOmegaOneCenter (Qv δ) : Subgroup G) : Set G) =
      Qv δ := by
  have hYN : stab δ ≤
      Subgroup.normalizer ((quasithinOmegaOneCenter (Qv δ) : Subgroup G) : Set G) :=
    (le_normalizer_pCoreOf 2 (stab δ)).trans
      (normalizer_le_normalizer_omegaOneCenter (Qv δ))
  have hZY := Zv_le_omegaOneCenter_Qv hA hle hZ
  refine le_antisymm ?_ (le_inf (pCoreOf_le 2 _) fun x hx => ?_)
  · by_contra hC
    have hC' : ¬ stab δ ⊓ Subgroup.centralizer
        ((quasithinOmegaOneCenter (Qv δ) : Subgroup G) : Set G) ≤ pCoreOf 2 (stab δ) := hC
    refine false_of_odd_normalizes_gen hA hν (U := stab δ) (P := stab δ ⊓ stab ν)
      (sylow_stab_inf_left hA hν) inf_le_right (sup_eq_left.mpr inf_le_left) ?_
    intro u hu huo
    obtain ⟨d, hd, e, he, rfl⟩ := odd_mem_of_normal hA le_rfl inf_le_left
      (SitSigma.normalizer_inf_centralizer hYN) hC' u hu huo
    have hecen : e ∈ Subgroup.centralizer (Zv ν : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA ν hz).2 e (hle he.2)).symm)
    have hdcen : d ∈ Subgroup.centralizer (Zv ν : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        Subgroup.mem_centralizer_iff.mp hd.2 z (hZY hz)
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mul_mem _ hdcen hecen)
  · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨hyQ, hyC, -⟩ := mem_quasithinOmegaOneCenter_iff.mp hy
    exact (Subgroup.mem_centralizer_iff.mp hyC x hx).symm

end F53

end CFSG.Quasithin
