module

public import CFSG.Quasithin.MS93.S4A441B2

public section

namespace CFSG.Quasithin.MS93.S4A.C441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S4A
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Good

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

theorem exists_commutator_not_mem_dloc {α α' : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1)
    {u d : 𝔘} (hu : u ∈ Uloc h.le L α) (hd : d ∈ Dloc h.le L α)
    (k : ↥(stab (puAmalgam h.le) α))
    (hk : ((toSL3 ψ k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ ⟨u, hu⟩ ∉
      fixN (natImage ψ (ZM (puAmalgam h.le) α'))) :
    ∃ w ∈ ZM (puAmalgam h.le) α', ⁅(k : 𝔘) * (u * d) * (k : 𝔘)⁻¹, w⁆ ∉ Dloc h.le L α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hUn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (Uloc h.le L α : Set 𝔘) :=
    stab_le_normalizer_uloc h α
  have hDn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (Dloc h.le L α : Set 𝔘) :=
    stab_le_normalizer_dloc h α
  rw [mem_fixN] at hk
  push Not at hk
  obtain ⟨g, hg, hgv⟩ := hk
  obtain ⟨z, hzZ, rfl⟩ := mem_natImage.mp hg
  refine ⟨z, hzZ, fun hmem => hgv ?_⟩
  obtain ⟨u', hu'⟩ : ∃ u', u' = (k : 𝔘) * u * (k : 𝔘)⁻¹ := ⟨_, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ d', d' = (k : 𝔘) * d * (k : 𝔘)⁻¹ := ⟨_, rfl⟩
  have hu'U : u' ∈ Uloc h.le L α := by
    rw [hu']; exact (Subgroup.mem_normalizer_iff.mp (hUn k.2) u).mp hu
  have hd'D : d' ∈ Dloc h.le L α := by
    rw [hd']; exact (Subgroup.mem_normalizer_iff.mp (hDn k.2) d).mp hd
  have hx' : (k : 𝔘) * (u * d) * (k : 𝔘)⁻¹ = u' * d' := by
    rw [hu', hd']
    group
  rw [hx'] at hmem
  have hdz : ⁅d', (z : 𝔘)⁆ ∈ Dloc h.le L α := by
    rw [commutatorElement_def]
    have h1 : (z : 𝔘) * d'⁻¹ * (z : 𝔘)⁻¹ ∈ Dloc h.le L α :=
      (Subgroup.mem_normalizer_iff.mp (hDn z.2) _).mp ((Dloc h.le L α).inv_mem hd'D)
    have : d' * z * d'⁻¹ * (z : 𝔘)⁻¹ = d' * ((z : 𝔘) * d'⁻¹ * (z : 𝔘)⁻¹) := by group
    rw [this]
    exact (Dloc h.le L α).mul_mem hd'D h1
  have huz : ⁅u', (z : 𝔘)⁆ ∈ Dloc h.le L α := by
    have hid : ⁅u', (z : 𝔘)⁆ = (u' * ⁅d', (z : 𝔘)⁆ * u'⁻¹)⁻¹ * ⁅u' * d', (z : 𝔘)⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hid]
    have hus : u' ∈ stab (puAmalgam h.le) α :=
      (uloc_le_zm h hfull hα).trans ((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ α))
        hu'U
    have h1 := (Subgroup.mem_normalizer_iff.mp (hDn hus) _).mp hdz
    exact (Dloc h.le L α).mul_mem ((Dloc h.le L α).inv_mem h1) hmem
  have huzU : ⁅u', (z : 𝔘)⁆ ∈ Uloc h.le L α := by
    rw [commutatorElement_def]
    have h1 : (z : 𝔘) * u'⁻¹ * (z : 𝔘)⁻¹ ∈ Uloc h.le L α :=
      (Subgroup.mem_normalizer_iff.mp (hUn z.2) _).mp ((Uloc h.le L α).inv_mem hu'U)
    have : u' * z * u'⁻¹ * (z : 𝔘)⁻¹ = u' * ((z : 𝔘) * u'⁻¹ * (z : 𝔘)⁻¹) := by group
    rw [this]
    exact (Uloc h.le L α).mul_mem hu'U h1
  have h1 : ⁅u', (z : 𝔘)⁆ = 1 := by
    have : ⁅u', (z : 𝔘)⁆ ∈ Uloc h.le L α ⊓ Dloc h.le L α := ⟨huzU, huz⟩
    rwa [uloc_inf_dloc h hφ α, Subgroup.mem_bot] at this
  have hcomm : (z : 𝔘) * u' = u' * z := by
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hfix := (commute_iff_natVec hψ z ⟨u', hu'U⟩).mp hcomm
  rwa [natVec_conj hψ k ⟨u, hu⟩ ⟨u', hu'U⟩ hu'] at hfix

end Good

end CFSG.Quasithin.MS93.S4A.C441
