module

public import CFSG.RankThree.PartOne.K1320.Sp
public import CFSG.RankThree.PartOne.K1320.Row7Gen
public import CFSG.RankThree.PartOne.KF.F132Row7Frame
public import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem conjBy_eq_self_of_mem {G : Type} [Group G] {x : G} {L : Subgroup G} (hx : x ∈ L) :
    conjBy x L = L := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)
  · intro y hy
    refine ⟨x⁻¹ * y * x, L.mul_mem (L.mul_mem (L.inv_mem hx) hy) hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem row7Data_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) : Row7Data := by
  intro G _ _ p A c L E f h hF hF13 hT hEA hf1 hpf hmodel
  obtain ⟨hZ, hall, K, _, _, _, hK, ε, hε, r₀, r₁, hr₀, hr₀L, hr₁, hr₁L, hord01, hmap₀, hmap₁,
    hconj⟩ := KF132.kf132Row7_frame hGA h hF hF13 hEA hf1 hpf hmodel
  refine ⟨hall, hZ, ?_⟩
  intro s hs hsL s' hs' hs'L hss'
  have hεinj : Function.Injective ε := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact eq_bot_iff.mpr (hε.central.trans hZ.le)
  have hkle : ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → kZero p E t ≤ L := fun t ht htL =>
    kZero_le_of_mem_torusImage h selected_prime_elements_normalize_theta_components htL
      (hF13.reflection t ht).1
  have hjoin : (kZero p E r₀).subgroupOf L ⊔ (kZero p E r₁).subgroupOf L = ⊤ := by
    refine Subgroup.map_injective hεinj ?_
    rw [Subgroup.map_sup, hmap₀, hmap₁, ← Subgroup.map_sup, spBlock_sup_spBlock'_eq_top,
      ← MonoidHom.range_eq_map, ← MonoidHom.range_eq_map]
    rw [MonoidHom.range_eq_top.mpr (isCentralPQuot_spQ p).surjective,
      MonoidHom.range_eq_top.mpr hε.surjective]
  have hgen : kZero p E r₀ ⊔ kZero p E r₁ = L := by
    refine le_antisymm (sup_le (hkle r₀ hr₀ hr₀L) (hkle r₁ hr₁ hr₁L)) ?_
    intro y hy
    have hy' : (⟨y, hy⟩ : L) ∈ (kZero p E r₀).subgroupOf L ⊔ (kZero p E r₁).subgroupOf L := by
      rw [hjoin]
      exact Subgroup.mem_top _
    have h1 := Subgroup.mem_map_of_mem L.subtype hy'
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (hkle r₀ hr₀ hr₀L),
      Subgroup.map_subgroupOf_eq_of_le (hkle r₁ hr₁ hr₁L)] at h1
  obtain ⟨x, hxL, hxE, hcase⟩ := hconj s hs hsL s' hs' hs'L hss'
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, kZero_conj p r₀ hxE, kZero_conj p r₁ hxE, ← conjBy_sup, hgen,
      conjBy_eq_self_of_mem hxL]
  · rw [h1, h2, kZero_conj p r₁ hxE, kZero_conj p r₀ hxE, ← conjBy_sup, sup_comm, hgen,
      conjBy_eq_self_of_mem hxL]

theorem kf1320Sp'_holds
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (h133 : S13K.KF133Two)
    (hDist : S13K.KFCommDistinct) : KF1320Sp' :=
  kf1320Sp'_of_inputs hGA hS h133 hDist (row7Data_holds hGA)

end CFSG.RankThree.PartOne.K1320
