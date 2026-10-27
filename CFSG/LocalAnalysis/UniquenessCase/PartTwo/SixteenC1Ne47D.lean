module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ne47C
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ne47A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ne47B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_conj_le_cTilde (D : Data G) (hkit : OmegaKit) (h43 : R16_43_1 D)
    (h45 : R16_45 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) (hne : V₀ ≠ ⊥) {z : G}
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)))
    (hcard : Nat.card ↥V = 2 * Nat.card ↥(uOne V z))
    (hC : V₀ ⊓ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) ≤
      pCoreOf 2 (centralizer ({z} : Set G)))
    {h : G} (hh : h ∈ centralizer ({z} : Set G))
    (hgap : V ≤ conjSubgroup D.M h → ¬ conjSubgroup V h ≤ D.M →
      conjSubgroup (V₀ ⊓ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G))
        h ≤ F11.CTilde D.M V₀ V) :
    conjSubgroup (V₀ ⊓ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G))
      h ≤ F11.CTilde D.M V₀ V := by
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1]
    exact Subgroup.one_mem _
  set c : G := h * y * h⁻¹ with hc_def
  have hc_mem : c ∈ V₀ ⊓ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) := by
    rw [hc_def]
    exact mem_conjSubgroup_iff.mp hy
  have hcV₀ : c ∈ V₀ := hc_mem.1
  have hcCent : c ∈ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) :=
    hc_mem.2
  have hcQ : c ∈ pCoreOf 2 (centralizer ({z} : Set G)) := hC hc_mem
  have hQh : conjSubgroup (pCoreOf 2 (centralizer ({z} : Set G))) h =
      pCoreOf 2 (centralizer ({z} : Set G)) := s16c1_conjSubgroup_pCoreOf_self _ hh
  have hQh_inv : conjSubgroup (pCoreOf 2 (centralizer ({z} : Set G))) h⁻¹ =
      pCoreOf 2 (centralizer ({z} : Set G)) :=
    s16c1_conjSubgroup_pCoreOf_self _ (Subgroup.inv_mem _ hh)
  have hQM : pCoreOf 2 (centralizer ({z} : Set G)) ≤ D.M := s16c1_pCoreOf_le_M D hSyl
  have hQS : pCoreOf 2 (centralizer ({z} : Set G)) ≤ D.T ⊓ centralizer ({z} : Set G) :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowIn hSyl
  have hyQ : y ∈ pCoreOf 2 (centralizer ({z} : Set G)) :=
    hQh ▸ E3.conjSubgroup_mono_left h hC hy
  have hyM : y ∈ D.M := hQM hyQ
  have hy_eq : y = h⁻¹ * c * h := by rw [hc_def]; group
  have hc_ne1 : c ≠ 1 := fun hc1 => hy1 (by rw [hy_eq, hc1]; group)
  have hU1 : ∀ u ∈ uOne V z, y * u * y⁻¹ = u := by
    intro u hu
    have huQ : u ∈ pCoreOf 2 (centralizer ({z} : Set G)) := hu.2
    have hhuQ : h * u * h⁻¹ ∈ pCoreOf 2 (centralizer ({z} : Set G)) := by
      rw [← hQh_inv]
      refine mem_conjSubgroup_iff.mpr ?_
      rw [show h⁻¹ * (h * u * h⁻¹) * h⁻¹⁻¹ = u by group]
      exact huQ
    have hcomm : (h * u * h⁻¹) * c = c * (h * u * h⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hcCent) _ (hQS hhuQ)
    have hc_conj : c * (h * u * h⁻¹) * c⁻¹ = h * u * h⁻¹ := by
      rw [← hcomm]; group
    calc y * u * y⁻¹ = h⁻¹ * c * h * u * (h⁻¹ * c * h)⁻¹ := by rw [hy_eq]
      _ = h⁻¹ * (c * (h * u * h⁻¹) * c⁻¹) * h := by group
      _ = h⁻¹ * (h * u * h⁻¹) * h := by rw [hc_conj]
      _ = u := by group
  have hy₀ : y ∈ conjSubgroup V₀ h := mem_conjSubgroup_iff.mpr (hc_def ▸ hcV₀)
  have hhcQ : h * c * h⁻¹ ∈ pCoreOf 2 (centralizer ({z} : Set G)) := by
    rw [← hQh_inv]
    refine mem_conjSubgroup_iff.mpr ?_
    rw [show h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ = c by group]
    exact hcQ
  have hc0 : V₀ ⊓ conjSubgroup D.M h ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨c, hcV₀, mem_conjSubgroup_iff.mpr (hQM hhcQ)⟩,
      fun h1 => hc_ne1 (congrArg Subtype.val h1)⟩
  have hy0 : conjSubgroup V₀ h ⊓ D.M ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨y, hy₀, hyM⟩, fun h1 => hy1 (congrArg Subtype.val h1)⟩
  by_cases hle : conjSubgroup V h ≤ D.M
  · exact s16c1_mem_cTilde_of_conjV_le_M D hkit h43 hS hc (U₁ := uOne V z)
      inf_le_left hcard hle hy₀ hyM hU1
  · by_cases hVM : V ≤ conjSubgroup D.M h
    · exact hgap hVM hle hy
    · have hO : InCalO 1 D.M V₀ V h :=
        s16c1_inCalO_one hV hQM hh hcard hle hVM hc0 hy0
      have hOstar : conjSubgroup V h ∈ calOStar 1 D.M V₀ V := by
        rw [← h45 V₀ V L hV hS hc]
        exact ⟨h, rfl, hO⟩
      exact s16c1_mem_cTilde_of_calOStar D (s16c1_inCalV0_of_sect16 hS hne).2.1
        (s16c1_inCalV0_of_sect16 hS hne).1 hOstar hy₀ hyM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
