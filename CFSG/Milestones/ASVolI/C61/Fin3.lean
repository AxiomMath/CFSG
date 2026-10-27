module

public import CFSG.Milestones.ASVolI.C61.Fin2

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

variable {G G' : Type} [Group G] [Group G'] {H Λ : Subgroup G} {ι : ↥H →* G'} {κ : ↥Λ →* G'}

theorem burnsideC56_fin_hyps (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (hag : ∀ g (hH : g ∈ H) (hΛ : g ∈ Λ), ι ⟨g, hH⟩ = κ ⟨g, hΛ⟩)
    (hmeet : ∀ h l, ι h = κ l → (h : G) = l)
    (hc : CharTwo H)
    (hi : (∃ n : ℕ, 1 ≤ n ∧ QuotHas (oTwoUpper H) (pCoreOf 2 H) (fun Y _ => IsPSL 2 2 n Y)) ∨
      QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∨
      QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* S3wrZ2)))
    (hΛ2 : IsPGroup 2 Λ) (hsyl : IsSylowTwoOf (Λ ⊓ H) H) (hlt : Λ ⊓ H < Λ)
    (hiv : ∀ T₀ : Subgroup G, T₀ ≠ ⊥ → T₀ ≤ Λ ⊓ H → H ≤ Subgroup.normalizer (T₀ : Set G) →
      Λ ⊓ Subgroup.normalizer (T₀ : Set G) = Λ ⊓ H) :
    CharTwo ((⊤ : Subgroup ↥H).map ι) ∧
    ((∃ n : ℕ, 1 ≤ n ∧ QuotHas (oTwoUpper ((⊤ : Subgroup ↥H).map ι))
        (pCoreOf 2 ((⊤ : Subgroup ↥H).map ι)) (fun Y _ => IsPSL 2 2 n Y)) ∨
      QuotHas ((⊤ : Subgroup ↥H).map ι) (pCoreOf 2 ((⊤ : Subgroup ↥H).map ι))
        (fun Y _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∨
      QuotHas ((⊤ : Subgroup ↥H).map ι) (pCoreOf 2 ((⊤ : Subgroup ↥H).map ι))
        (fun Y _ => Nonempty (Y ≃* S3wrZ2))) ∧
    IsPGroup 2 ((⊤ : Subgroup ↥Λ).map κ) ∧
    IsSylowTwoOf ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) ((⊤ : Subgroup ↥H).map ι) ∧
    (⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι < (⊤ : Subgroup ↥Λ).map κ ∧
    (∀ T₀ : Subgroup G', T₀ ≠ ⊥ → T₀ ≤ (⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι →
      (⊤ : Subgroup ↥H).map ι ≤ Subgroup.normalizer (T₀ : Set G') →
      (⊤ : Subgroup ↥Λ).map κ ⊓ Subgroup.normalizer (T₀ : Set G') =
        (⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) := by
  have hsH := H.subtype_injective
  have hsΛ := Λ.subtype_injective
  set CH := (Λ ⊓ H).subgroupOf H with hCHdef
  set CL := (Λ ⊓ H).subgroupOf Λ with hCLdef
  have hCH : CH.map H.subtype = Λ ⊓ H := burnsideC56_fin_sub inf_le_right
  have hCL : CL.map Λ.subtype = Λ ⊓ H := burnsideC56_fin_sub inf_le_left
  have hC' := burnsideC56_fin_meet hag hmeet
  have hCHL : CH.map ι = CL.map κ := burnsideC56_fin_agree hag le_rfl
  refine ⟨(burnsideC56_finH_charTwo hι).mp hc, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hi with ⟨n, hn, hq⟩ | hq | hq
    · exact Or.inl ⟨n, hn, (burnsideC56_finH_quotHas_L hι _).mp hq⟩
    · exact Or.inr (Or.inl ((burnsideC56_finH_quotHas_H hι _).mp hq))
    · exact Or.inr (Or.inr ((burnsideC56_finH_quotHas_H hι _).mp hq))
  · rw [burnsideC56_tr_isPGroup hκ, ← burnsideC56_tr_isPGroup hsΛ, burnsideC56_fin_top]
    exact hΛ2
  · rw [hC', burnsideC56_tr_isSylowTwoOf hι, ← burnsideC56_tr_isSylowTwoOf hsH, hCH,
      burnsideC56_fin_top]
    exact hsyl
  · rw [hC', hCHL, Subgroup.map_lt_map_iff_of_injective hκ,
      ← Subgroup.map_lt_map_iff_of_injective hsΛ, hCL, burnsideC56_fin_top]
    exact hlt
  · intro T₀' hne hle hHN
    rw [hC'] at hle ⊢
    set Y := T₀'.comap ι with hYdef
    have hY : Y.map ι = T₀' := burnsideC56_tr_eq_map_comap hι hle
    have hYC : Y ≤ CH := burnsideC56_tr_comap_le hι hle
    set T₀ := Y.map H.subtype with hT₀def
    have hT₀C : T₀ ≤ Λ ⊓ H := by
      rw [← hCH]
      exact Subgroup.map_mono hYC
    have hT₀ne : T₀ ≠ ⊥ := by
      intro h0
      apply hne
      rw [← hY, (Subgroup.map_eq_bot_iff_of_injective Y hsH).mp h0, Subgroup.map_bot]
    have hHT₀ : H ≤ Subgroup.normalizer (T₀ : Set G) := by
      rw [← hY] at hHN
      have h1 : ((⊤ : Subgroup ↥H) ⊓ Subgroup.normalizer (Y : Set ↥H)).map ι =
          (⊤ : Subgroup ↥H).map ι := by
        rw [burnsideC56_tr_normalizer hι]
        exact inf_eq_left.mpr hHN
      have h2 : (⊤ : Subgroup ↥H) ⊓ Subgroup.normalizer (Y : Set ↥H) = ⊤ :=
        Subgroup.map_injective hι h1
      have h3 := congrArg (Subgroup.map H.subtype) h2
      rw [burnsideC56_tr_normalizer hsH, burnsideC56_fin_top] at h3
      exact inf_eq_left.mp h3
    have h4 := hiv T₀ hT₀ne hT₀C hHT₀
    set Z := T₀.subgroupOf Λ with hZdef
    have hZ : Z.map Λ.subtype = T₀ := burnsideC56_fin_sub (hT₀C.trans inf_le_left)
    have hYT : T₀.subgroupOf H = Y := Subgroup.comap_map_eq_self_of_injective hsH Y
    have hZ' : Z.map κ = T₀' := by
      rw [← hY, ← hYT, burnsideC56_fin_agree hag hT₀C]
    have h5 : ((⊤ : Subgroup ↥Λ) ⊓ Subgroup.normalizer (Z : Set ↥Λ)).map Λ.subtype =
        Λ ⊓ Subgroup.normalizer (T₀ : Set G) := by
      rw [burnsideC56_tr_normalizer hsΛ, burnsideC56_fin_top, hZ]
    rw [h4, ← hCL] at h5
    have h6 : (⊤ : Subgroup ↥Λ) ⊓ Subgroup.normalizer (Z : Set ↥Λ) = CL :=
      Subgroup.map_injective hsΛ h5
    rw [← hZ', ← burnsideC56_tr_normalizer hκ, h6, hCHL]

end CFSG.ASVolI
