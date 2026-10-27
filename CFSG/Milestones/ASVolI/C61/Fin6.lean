module

public import CFSG.Milestones.ASVolI.C61.Fin5

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

variable {G G' : Type} [Group G] [Group G'] {H Λ : Subgroup G} {ι : ↥H →* G'} {κ : ↥Λ →* G'}

theorem burnsideC56_fin_relIndex_inf {A B : Type} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) (X Y : Subgroup A) :
    (X.map f ⊓ Y.map f).relIndex (X.map f) = (X ⊓ Y).relIndex X := by
  rw [← Subgroup.map_inf_eq _ _ f hf, burnsideC56_tr_relIndex hf]

theorem burnsideC56_fin_c4 (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (hag : ∀ g (hH : g ∈ H) (hΛ : g ∈ Λ), ι ⟨g, hH⟩ = κ ⟨g, hΛ⟩)
    (hmeet : ∀ h l, ι h = κ l → (h : G) = l) (hsyl : IsSylowTwoOf (Λ ⊓ H) H)
    (c4 : ∀ x ∈ (⊤ : Subgroup ↥Λ).map κ ⊓ Subgroup.normalizer
          (((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι : Subgroup G') : Set G'),
        x ∉ (⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι →
        ((IsBlock2 ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) ∧
            IsAltType (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) 5) ∨
          IsA3Product ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) 2) →
        ∃ (A₁ : Subgroup G') (r : G'), r ∈ (⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι ∧
          r ∉ thompsonJ ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) ∧
          (A₁ ⊓ pCoreOf 2 ((⊤ : Subgroup ↥H).map ι)).relIndex A₁ = 2 ∧
          AFam ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) =
            {pCoreOf 2 ((⊤ : Subgroup ↥H).map ι), ChC.rconj x (pCoreOf 2 ((⊤ : Subgroup ↥H).map ι)),
              A₁, ChC.rconj r A₁}) :
    ∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
      ((IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 5) ∨ IsA3Product H (oTwoUpper H) 2) →
      ∃ (A₁ : Subgroup G) (r : G), r ∈ Λ ⊓ H ∧ r ∉ thompsonJ (Λ ⊓ H) ∧
        (A₁ ⊓ pCoreOf 2 H).relIndex A₁ = 2 ∧
        AFam (Λ ⊓ H) = {pCoreOf 2 H, ChC.rconj x (pCoreOf 2 H), A₁, ChC.rconj r A₁} := by
  have hsΛ := Λ.subtype_injective
  have hQ : pCoreOf 2 H ≤ Λ ⊓ H := hsyl.pCoreOf_le
  set CL := (Λ ⊓ H).subgroupOf Λ with hCLdef
  set QL := (pCoreOf 2 H).subgroupOf Λ with hQLdef
  have hC := burnsideC56_finL_C hag hmeet
  have hC' : CL.map Λ.subtype = Λ ⊓ H := burnsideC56_finL_C'
  have hQ' := burnsideC56_finL_Q hι hag hQ
  have hQ'' : QL.map Λ.subtype = pCoreOf 2 H := burnsideC56_finL_Q' hQ
  intro x hx hxC hcond
  rw [← hC', burnsideC56_finL_N'] at hx
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  have hx₀C : x₀ ∉ CL := fun h => hxC (hC' ▸ Subgroup.mem_map_of_mem _ h)
  have hcond' := hcond
  simp only [burnsideC56_finH_isBlock2 hι, burnsideC56_finH_isAltType hι,
    burnsideC56_finH_isA3Product hι] at hcond'
  obtain ⟨A₁', r', hr', hrJ', hidx', hAF'⟩ := c4 (κ x₀)
    (by rw [hC, burnsideC56_finL_N hκ]; exact Subgroup.mem_map_of_mem κ hx₀)
    (by rw [hC]; exact fun h => hx₀C ((Subgroup.mem_map_iff_mem hκ).mp h)) hcond'
  have hA₁mem : A₁' ∈ AFam ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) := by
    rw [hAF']; simp
  have hA₁le : A₁' ≤ CL.map κ := hC ▸ hA₁mem.1
  set A₁₀ := A₁'.comap κ with hA₁₀def
  have hA₁ : A₁₀.map κ = A₁' := burnsideC56_tr_eq_map_comap hκ hA₁le
  rw [hC] at hr' hrJ' hAF'
  obtain ⟨r₀, hr₀, rfl⟩ := hr'
  rw [← hA₁, hQ', burnsideC56_fin_relIndex_inf hκ] at hidx'
  rw [← hA₁, hQ', burnsideC56_tr_rconj hκ, burnsideC56_tr_rconj hκ, ← burnsideC56_fin_image_four,
    burnsideC56_fin_AFam_eq hκ] at hAF'
  rw [burnsideC56_tr_thompsonJ hκ] at hrJ'
  refine ⟨A₁₀.map Λ.subtype, Λ.subtype r₀, ?_, ?_, ?_, ?_⟩
  · rw [← hC']; exact Subgroup.mem_map_of_mem _ hr₀
  · rw [← hC', burnsideC56_tr_thompsonJ hsΛ]
    intro h
    exact hrJ' (Subgroup.mem_map_of_mem κ ((Subgroup.mem_map_iff_mem hsΛ).mp h))
  · rw [← hQ'', burnsideC56_fin_relIndex_inf hsΛ]; exact hidx'
  · rw [← hC', ← hQ'', show (Λ.subtype x₀ : G) = Λ.subtype x₀ from rfl, burnsideC56_tr_rconj hsΛ,
      burnsideC56_tr_rconj hsΛ, ← burnsideC56_fin_image_four, burnsideC56_fin_AFam_eq hsΛ]
    exact hAF'

end CFSG.ASVolI
