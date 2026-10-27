module

public import CFSG.Milestones.ASVolI.C61.Fin4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

theorem burnsideC56_fin_AFam_eq {A B : Type} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) (X : Subgroup A) (S : Set (Subgroup A)) :
    AFam (X.map f) = Subgroup.map f '' S ↔ AFam X = S := by
  rw [burnsideC56_tr_AFam hf]
  exact (Set.image_injective.mpr (Subgroup.map_injective hf)).eq_iff

theorem burnsideC56_fin_image_pair {A B : Type} [Group A] [Group B] (f : A →* B) (a b : Subgroup A) :
    Subgroup.map f '' ({a, b} : Set (Subgroup A)) = {a.map f, b.map f} := by
  rw [Set.image_insert_eq, Set.image_singleton]

theorem burnsideC56_fin_image_four {A B : Type} [Group A] [Group B] (f : A →* B)
    (a b c d : Subgroup A) :
    Subgroup.map f '' ({a, b, c, d} : Set (Subgroup A)) = {a.map f, b.map f, c.map f, d.map f} := by
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]

variable {G G' : Type} [Group G] [Group G'] {H Λ : Subgroup G} {ι : ↥H →* G'} {κ : ↥Λ →* G'}

theorem burnsideC56_fin_c2 (hι : Function.Injective ι)
    (c2 : (IsBlock2 ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) ∧
        ((∃ n : ℕ, 1 < n ∧ IsLin2Type (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) n) ∨
          IsAltType (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) 5)) ∨
      IsA3Product ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) 1 ∨
      IsA3Product ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) 2) :
    (IsBlock2 H (oTwoUpper H) ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type (oTwoUpper H) n) ∨
        IsAltType (oTwoUpper H) 5)) ∨
      IsA3Product H (oTwoUpper H) 1 ∨ IsA3Product H (oTwoUpper H) 2 := by
  simp only [← burnsideC56_finH_isBlock2 hι, ← burnsideC56_finH_isLin2Type hι,
    ← burnsideC56_finH_isAltType hι, ← burnsideC56_finH_isA3Product hι] at c2
  exact c2

theorem burnsideC56_finH_CL (hι : Function.Injective ι)
    (hag : ∀ g (hH : g ∈ H) (hΛ : g ∈ Λ), ι ⟨g, hH⟩ = κ ⟨g, hΛ⟩)
    (hmeet : ∀ h l, ι h = κ l → (h : G) = l) :
    ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) ⊓
        Subgroup.centralizer (oTwoUpper ((⊤ : Subgroup ↥H).map ι) : Set G') =
      (((Λ ⊓ H).subgroupOf H) ⊓ Subgroup.centralizer (oTwoUpper (⊤ : Subgroup ↥H) : Set ↥H)).map ι ∧
    (Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) =
      (((Λ ⊓ H).subgroupOf H) ⊓ Subgroup.centralizer (oTwoUpper (⊤ : Subgroup ↥H) : Set ↥H)).map
        H.subtype := by
  constructor
  · rw [burnsideC56_fin_meet hag hmeet, burnsideC56_finH_oTwoUpper hι, burnsideC56_tr_centralizer hι]
  · rw [burnsideC56_tr_centralizer H.subtype_injective, burnsideC56_fin_sub inf_le_right,
      ← burnsideC56_finH_oTwoUpper']

theorem burnsideC56_fin_c3 (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (hag : ∀ g (hH : g ∈ H) (hΛ : g ∈ Λ), ι ⟨g, hH⟩ = κ ⟨g, hΛ⟩)
    (hmeet : ∀ h l, ι h = κ l → (h : G) = l) (hsyl : IsSylowTwoOf (Λ ⊓ H) H)
    (c3 : ∀ x ∈ (⊤ : Subgroup ↥Λ).map κ ⊓ Subgroup.normalizer
          (((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι : Subgroup G') : Set G'),
        x ∉ (⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι →
        ((IsBlock2 ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) ∧
          ((∃ n : ℕ, 1 < n ∧ IsLin2Type (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) n) ∨
            IsAltType (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) 3)) →
          AFam ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) =
            {pCoreOf 2 ((⊤ : Subgroup ↥H).map ι),
              ChC.rconj x (pCoreOf 2 ((⊤ : Subgroup ↥H).map ι))}) ∧
        (∀ n : ℕ, 1 < n → IsBlock2 ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) →
          IsLin2Type (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) n →
          ∀ B : Subgroup G', B ≤ ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) ⊓
              Subgroup.centralizer (oTwoUpper ((⊤ : Subgroup ↥H).map ι) : Set G') →
            IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ n) ∧
        (IsBlock2 ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) →
          IsAltType (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) 3 →
          ∀ B : Subgroup G', B ≤ ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) ⊓
              Subgroup.centralizer (oTwoUpper ((⊤ : Subgroup ↥H).map ι) : Set G') →
            IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ 1)) :
    ∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
      ((IsBlock2 H (oTwoUpper H) ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type (oTwoUpper H) n) ∨
          IsAltType (oTwoUpper H) 3)) →
        AFam (Λ ⊓ H) = {pCoreOf 2 H, ChC.rconj x (pCoreOf 2 H)}) ∧
      (∀ n : ℕ, 1 < n → IsBlock2 H (oTwoUpper H) → IsLin2Type (oTwoUpper H) n →
        ∀ B : Subgroup G, B ≤ (Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) →
          IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ n) ∧
      (IsBlock2 H (oTwoUpper H) → IsAltType (oTwoUpper H) 3 →
        ∀ B : Subgroup G, B ≤ (Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) →
          IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ 1) := by
  have hsΛ := Λ.subtype_injective
  have hsH := H.subtype_injective
  have hQ : pCoreOf 2 H ≤ Λ ⊓ H := hsyl.pCoreOf_le
  set CL := (Λ ⊓ H).subgroupOf Λ with hCLdef
  set QL := (pCoreOf 2 H).subgroupOf Λ with hQLdef
  have hC := burnsideC56_finL_C hag hmeet
  have hC' : CL.map Λ.subtype = Λ ⊓ H := burnsideC56_finL_C'
  have hQ' := burnsideC56_finL_Q hι hag hQ
  have hQ'' : QL.map Λ.subtype = pCoreOf 2 H := burnsideC56_finL_Q' hQ
  obtain ⟨hCC', hCC⟩ := burnsideC56_finH_CL hι hag hmeet
  intro x hx hxC
  rw [← hC', burnsideC56_finL_N'] at hx
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  have hx₀C : x₀ ∉ CL := fun h => hxC (hC' ▸ Subgroup.mem_map_of_mem _ h)
  obtain ⟨c3a, c3b, c3c⟩ := c3 (κ x₀)
    (by rw [hC, burnsideC56_finL_N hκ]; exact Subgroup.mem_map_of_mem κ hx₀)
    (by rw [hC]; exact fun h => hx₀C ((Subgroup.mem_map_iff_mem hκ).mp h))
  refine ⟨?_, ?_, ?_⟩
  · intro hcond
    have hcond' := hcond
    simp only [burnsideC56_finH_isBlock2 hι, burnsideC56_finH_isLin2Type hι,
      burnsideC56_finH_isAltType hι] at hcond'
    have h1 := c3a hcond'
    rw [hC, hQ', burnsideC56_tr_rconj hκ, ← burnsideC56_fin_image_pair,
      burnsideC56_fin_AFam_eq hκ] at h1
    rw [← hC', ← hQ'', show (Λ.subtype x₀ : G) = Λ.subtype x₀ from rfl, burnsideC56_tr_rconj hsΛ,
      ← burnsideC56_fin_image_pair, burnsideC56_fin_AFam_eq hsΛ]
    exact h1
  · intro n hn hb hlin B hB hBe
    have hBH : B ≤ H := hB.trans (inf_le_left.trans inf_le_right)
    have hB0 := burnsideC56_fin_sub hBH
    rw [← hB0, hCC, Subgroup.map_le_map_iff_of_injective hsH] at hB
    rw [← hB0, burnsideC56_tr_isElemAbelian hsH] at hBe
    rw [← hB0, burnsideC56_tr_card hsH]
    have := c3b n hn ((burnsideC56_finH_isBlock2 hι).mp hb) ((burnsideC56_finH_isLin2Type hι n).mp hlin)
      ((B.subgroupOf H).map ι) (by rw [hCC']; exact Subgroup.map_mono hB)
      ((burnsideC56_tr_isElemAbelian hι 2 _).mpr hBe)
    rwa [burnsideC56_tr_card hι] at this
  · intro hb h3 B hB hBe
    have hBH : B ≤ H := hB.trans (inf_le_left.trans inf_le_right)
    have hB0 := burnsideC56_fin_sub hBH
    rw [← hB0, hCC, Subgroup.map_le_map_iff_of_injective hsH] at hB
    rw [← hB0, burnsideC56_tr_isElemAbelian hsH] at hBe
    rw [← hB0, burnsideC56_tr_card hsH]
    have := c3c ((burnsideC56_finH_isBlock2 hι).mp hb) ((burnsideC56_finH_isAltType hι 3).mp h3)
      ((B.subgroupOf H).map ι) (by rw [hCC']; exact Subgroup.map_mono hB)
      ((burnsideC56_tr_isElemAbelian hι 2 _).mpr hBe)
    rwa [burnsideC56_tr_card hι] at this

theorem burnsideC56_fin_c5 (hι : Function.Injective ι)
    (hag : ∀ g (hH : g ∈ H) (hΛ : g ∈ Λ), ι ⟨g, hH⟩ = κ ⟨g, hΛ⟩)
    (hmeet : ∀ h l, ι h = κ l → (h : G) = l)
    (c5 : (pCoreOf 2 ((⊤ : Subgroup ↥H).map ι) : Set G') =
      ((((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) ⊓
        Subgroup.centralizer (oTwoUpper ((⊤ : Subgroup ↥H).map ι) : Set G') : Subgroup G') : Set G') *
        (pCoreOf 2 (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) : Set G')) :
    (pCoreOf 2 H : Set G) =
      (((Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) : Subgroup G) : Set G) *
        (pCoreOf 2 (oTwoUpper H) : Set G) := by
  have hsH := H.subtype_injective
  obtain ⟨hCC', hCC⟩ := burnsideC56_finH_CL hι hag hmeet
  rw [hCC', burnsideC56_finH_pCoreOf hι, burnsideC56_finH_oTwoUpper hι, burnsideC56_tr_pCoreOf hι,
    burnsideC56_tr_set_mul hι] at c5
  rw [hCC, burnsideC56_finH_pCoreOf' (H := H), burnsideC56_finH_oTwoUpper' (H := H),
    burnsideC56_tr_pCoreOf hsH, burnsideC56_tr_set_mul hsH]
  exact c5

end CFSG.ASVolI
