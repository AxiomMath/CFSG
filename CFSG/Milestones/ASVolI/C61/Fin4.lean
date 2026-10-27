module

public import CFSG.Milestones.ASVolI.C61.Fin2

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

variable {G G' : Type} [Group G] [Group G'] {H Λ : Subgroup G} {ι : ↥H →* G'} {κ : ↥Λ →* G'}

section Dict

variable (hι : Function.Injective ι) (hκ : Function.Injective κ)
  (hag : ∀ g (hH : g ∈ H) (hΛ : g ∈ Λ), ι ⟨g, hH⟩ = κ ⟨g, hΛ⟩)
  (hmeet : ∀ h l, ι h = κ l → (h : G) = l)

include hag hmeet in
theorem burnsideC56_finL_C :
    (⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι = ((Λ ⊓ H).subgroupOf Λ).map κ :=
  (burnsideC56_fin_meet hag hmeet).trans (burnsideC56_fin_agree hag le_rfl)

theorem burnsideC56_finL_C' : ((Λ ⊓ H).subgroupOf Λ).map Λ.subtype = Λ ⊓ H :=
  burnsideC56_fin_sub inf_le_left

include hι hag in
theorem burnsideC56_finL_Q (hQ : pCoreOf 2 H ≤ Λ ⊓ H) :
    pCoreOf 2 ((⊤ : Subgroup ↥H).map ι) = ((pCoreOf 2 H).subgroupOf Λ).map κ := by
  rw [burnsideC56_finH_pCoreOf hι, ← burnsideC56_fin_agree hag hQ]
  congr 1
  rw [burnsideC56_finH_pCoreOf' (H := H) 2]
  exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm

theorem burnsideC56_finL_Q' (hQ : pCoreOf 2 H ≤ Λ ⊓ H) :
    ((pCoreOf 2 H).subgroupOf Λ).map Λ.subtype = pCoreOf 2 H :=
  burnsideC56_fin_sub (hQ.trans inf_le_left)

include hκ in
theorem burnsideC56_finL_N (X : Subgroup ↥Λ) :
    (⊤ : Subgroup ↥Λ).map κ ⊓ Subgroup.normalizer ((X.map κ : Subgroup G') : Set G') =
      ((⊤ : Subgroup ↥Λ) ⊓ Subgroup.normalizer (X : Set ↥Λ)).map κ :=
  (burnsideC56_tr_normalizer hκ ⊤ X).symm

theorem burnsideC56_finL_N' (X : Subgroup ↥Λ) :
    Λ ⊓ Subgroup.normalizer ((X.map Λ.subtype : Subgroup G) : Set G) =
      ((⊤ : Subgroup ↥Λ) ⊓ Subgroup.normalizer (X : Set ↥Λ)).map Λ.subtype := by
  have := burnsideC56_tr_normalizer Λ.subtype_injective ⊤ X
  rw [burnsideC56_fin_top] at this
  exact this.symm

end Dict

theorem burnsideC56_fin_c1 (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (hag : ∀ g (hH : g ∈ H) (hΛ : g ∈ Λ), ι ⟨g, hH⟩ = κ ⟨g, hΛ⟩)
    (hmeet : ∀ h l, ι h = κ l → (h : G) = l) (hsyl : IsSylowTwoOf (Λ ⊓ H) H)
    (c1 : (((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι).relIndex
        ((⊤ : Subgroup ↥Λ).map κ ⊓ Subgroup.normalizer
          (((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι : Subgroup G') : Set G')) = 2 ∧
      thompsonJ ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) =
        baum ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) ∧
      ∀ x ∈ (⊤ : Subgroup ↥Λ).map κ ⊓ Subgroup.normalizer
          (((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι : Subgroup G') : Set G'),
        x ∉ (⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι →
        (baum ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) : Set G') =
          (pCoreOf 2 ((⊤ : Subgroup ↥H).map ι) : Set G') *
            (ChC.rconj x (pCoreOf 2 ((⊤ : Subgroup ↥H).map ι)) : Set G'))) :
    ((Λ ⊓ H).relIndex (Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G)) = 2 ∧
      thompsonJ (Λ ⊓ H) = baum (Λ ⊓ H) ∧
      ∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
        (baum (Λ ⊓ H) : Set G) = (pCoreOf 2 H : Set G) * (ChC.rconj x (pCoreOf 2 H) : Set G)) := by
  have hsΛ := Λ.subtype_injective
  have hQ : pCoreOf 2 H ≤ Λ ⊓ H := hsyl.pCoreOf_le
  set CL := (Λ ⊓ H).subgroupOf Λ with hCLdef
  set QL := (pCoreOf 2 H).subgroupOf Λ with hQLdef
  have hC := burnsideC56_finL_C hag hmeet
  have hC' : CL.map Λ.subtype = Λ ⊓ H := burnsideC56_finL_C'
  have hQ' := burnsideC56_finL_Q hι hag hQ
  have hQ'' : QL.map Λ.subtype = pCoreOf 2 H := burnsideC56_finL_Q' hQ
  rw [hC, burnsideC56_finL_N hκ, hQ'] at c1
  obtain ⟨c1a, c1b, c1c⟩ := c1
  rw [← hC', burnsideC56_finL_N', ← hQ'']
  refine ⟨?_, ?_, ?_⟩
  · rw [burnsideC56_tr_relIndex hsΛ]
    rwa [burnsideC56_tr_relIndex hκ] at c1a
  · rw [burnsideC56_tr_thompsonJ hsΛ, burnsideC56_tr_baum hsΛ]
    rw [burnsideC56_tr_thompsonJ hκ, burnsideC56_tr_baum hκ] at c1b
    rw [Subgroup.map_injective hκ c1b]
  · rintro _ ⟨x₀, hx₀, rfl⟩ hxC
    have hx₀C : x₀ ∉ CL := fun h => hxC (Subgroup.mem_map_of_mem _ h)
    have h1 := c1c (κ x₀) (Subgroup.mem_map_of_mem κ hx₀)
      (fun h => hx₀C ((Subgroup.mem_map_iff_mem hκ).mp h))
    rw [burnsideC56_tr_baum hκ, burnsideC56_tr_rconj hκ, burnsideC56_tr_set_mul hκ] at h1
    rw [burnsideC56_tr_baum hsΛ, show (Λ.subtype x₀ : G) = Λ.subtype x₀ from rfl,
      burnsideC56_tr_rconj hsΛ, burnsideC56_tr_set_mul hsΛ]
    exact h1

end CFSG.ASVolI
