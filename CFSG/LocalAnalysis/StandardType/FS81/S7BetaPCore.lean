module

public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
import CFSG.LocalAnalysis.StandardType.FS81.S7Coprime
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.QuasithinUnique CFSG.LieType.BorelTits

private theorem mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, K.one_mem, by simp⟩
    · exact ⟨1, H.one_mem, x, hx, by simp⟩
  · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
    calc (h₁ * h₂) * (k₁ * k₂) = h₁ * (h₂ * (k₁ * k₂)) := by group
      _ = h₁ * (h₂ * k₁) * k₂ := by group
      _ = h₁ * (k₁ * h₂) * k₂ := by rw [hcomm h₂ hh₂ k₁ hk₁]
      _ = (h₁ * k₁) * (h₂ * k₂) := by group
  · rintro _ _ ⟨h, hh, k, hk, rfl⟩
    refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
    rw [mul_inv_rev]
    have hcomm' : k⁻¹ * h⁻¹ = h⁻¹ * k⁻¹ := by
      have h1 : (h * k)⁻¹ = (k * h)⁻¹ := congrArg Inv.inv (hcomm h hh k hk)
      rw [mul_inv_rev, mul_inv_rev] at h1
      exact h1
    exact hcomm'.symm

private theorem mem_of_mem_sup_zpowers_of_pow_eq_one {G : Type*} [Group G] {β x : G}
    {L : Subgroup G} (hβL : ∀ l ∈ L, l * β = β * l)
    (hdisj : ∀ l ∈ L, l ∈ Subgroup.zpowers β → l = 1) (hβ3 : orderOf β = 3)
    (hx : x ∈ Subgroup.zpowers β ⊔ L) {n : ℕ} (hxn : x ^ (2 ^ n) = 1) : x ∈ L := by
  have hcomm : ∀ h ∈ Subgroup.zpowers β, ∀ k ∈ L, h * k = k * h := by
    intro h hh k hk
    have hle : Subgroup.zpowers β ≤ Subgroup.centralizer ({k} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hβL k hk
    have hmem := hle hh
    rw [Subgroup.mem_centralizer_iff] at hmem
    exact (hmem k (Set.mem_singleton k)).symm
  obtain ⟨h, hh, k, hk, hk_eq⟩ := mem_sup_of_commute hcomm hx
  have hcommhk : Commute h k := hcomm h hh k hk
  have hxpow : x ^ (2 ^ n) = h ^ (2 ^ n) * k ^ (2 ^ n) := by
    rw [← hk_eq, hcommhk.mul_pow]
  have hmul : h ^ (2 ^ n) * k ^ (2 ^ n) = 1 := by
    rw [← hxpow]
    exact hxn
  have hhk : h ^ (2 ^ n) = (k ^ (2 ^ n))⁻¹ := eq_inv_of_mul_eq_one_left hmul
  have hmemL : h ^ (2 ^ n) ∈ L := by
    rw [hhk]
    exact L.inv_mem (L.pow_mem hk (2 ^ n))
  have hmemZ : h ^ (2 ^ n) ∈ Subgroup.zpowers β := (Subgroup.zpowers β).pow_mem hh (2 ^ n)
  have hhpow1 : h ^ (2 ^ n) = 1 := hdisj _ hmemL hmemZ
  have horder : orderOf h = 1 := by
    have hdvd1 : orderOf h ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hhpow1
    have hdvd2 : orderOf h ∣ 3 := by
      have := orderOf_dvd_of_mem_zpowers hh
      rwa [hβ3] at this
    have hcop : Nat.Coprime 3 (2 ^ n) := (by norm_num : Nat.Coprime 3 2).pow_right n
    exact Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvd1
  have hh1 : h = 1 := orderOf_eq_one_iff.mp horder
  rw [← hk_eq, hh1, one_mul]
  exact hk

private theorem le_of_isPGroup_le_sup_zpowers {G : Type*} [Group G] {β : G} {L N : Subgroup G}
    (hβL : ∀ l ∈ L, l * β = β * l)
    (hdisj : ∀ l ∈ L, l ∈ Subgroup.zpowers β → l = 1) (hβ3 : orderOf β = 3)
    (hN : IsPGroup 2 N) (hle : N ≤ Subgroup.zpowers β ⊔ L) : N ≤ L := by
  intro x hx
  obtain ⟨k, hk⟩ := hN ⟨x, hx⟩
  exact mem_of_mem_sup_zpowers_of_pow_eq_one hβL hdisj hβ3 (hle hx)
    (by simpa using congrArg Subtype.val hk)

theorem pCoreOf_centralizer_inf_eq {G : Type} [Group G] [Finite G] {Y L A : Subgroup G}
    {b₀ β σ : G} (h : BetaData Y L A b₀ β σ) :
    pCoreOf 2 (Subgroup.centralizer ({β} : Set G) ⊓ Subgroup.centralizer ({σ} : Set G)) =
      pCoreOf 2 (L ⊓ Subgroup.centralizer ({σ} : Set G)) := by
  classical
  let Γ : Subgroup G := Subgroup.centralizer ({β} : Set G)
  let Cσ : Subgroup G := Subgroup.centralizer ({σ} : Set G)
  let P : Subgroup G := pCoreOf 2 (L ⊓ Cσ)
  let Q : Subgroup G := pCoreOf 2 Cσ
  let O : Subgroup G := pCoreOf 2 (Γ ⊓ Cσ)
  change O = P
  have hLΓ : L ≤ Γ := by
    intro l hl
    show l ∈ Subgroup.centralizer ({β} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (h.L_cent l hl).symm
  have hAΓC : A ≤ Γ ⊓ Cσ := by
    refine le_inf ?_ ?_
    · exact le_trans h.A_le hLΓ
    · intro a ha
      show a ∈ Subgroup.centralizer ({σ} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact (h.A_cent a ha).symm
  have hO2 : IsPGroup 2 O := pCoreOf_isPGroup 2 (Γ ⊓ Cσ)
  have h3O : ¬ 3 ∣ Nat.card O := by
    obtain ⟨n, hn⟩ := hO2.exists_card_eq
    rw [hn]
    intro hdiv
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdiv
    norm_num at h32
  have hO_le_Y : O ≤ Y :=
    le_of_hyperplane_conj h.b₀_cent h.A_elem h.A_card h.A_conj
      (le_trans hAΓC (le_normalizer_pCoreOf 2 (Γ ⊓ Cσ))) h3O
  have hO_le_Γ : O ≤ Γ := le_trans (pCoreOf_le 2 (Γ ⊓ Cσ)) inf_le_left
  have hO_le_sup : O ≤ Subgroup.zpowers β ⊔ L := by
    intro x hx
    have hxcomm : x * β = β * x :=
      ((Subgroup.mem_centralizer_iff.mp (hO_le_Γ hx)) β (Set.mem_singleton β)).symm
    exact h.Y_cent x (hO_le_Y hx) hxcomm
  have hO_le_L : O ≤ L :=
    le_of_isPGroup_le_sup_zpowers h.L_cent h.L_disj h.β_ord hO2 hO_le_sup
  have hLC_norm_O : L ⊓ Cσ ≤ Subgroup.normalizer (O : Set G) :=
    le_trans (le_inf (le_trans inf_le_left hLΓ) inf_le_right)
      (le_normalizer_pCoreOf 2 (Γ ⊓ Cσ))
  have hO_le_P : O ≤ P :=
    le_pCoreOf_of_le_normalizer 2
      (le_inf hO_le_L (le_trans (pCoreOf_le 2 (Γ ⊓ Cσ)) inf_le_right)) hLC_norm_O hO2
  have hP_le_ΓQ : P ≤ Γ ⊓ Q := by
    refine le_inf ?_ ?_
    · exact le_trans (pCoreOf_le 2 (L ⊓ Cσ)) (le_trans inf_le_left hLΓ)
    · exact h.P_le
  have hGQ_le_P : Γ ⊓ Q ≤ P := by
    let X : Subgroup G := Γ ⊓ Q
    change X ≤ P
    have hX2 : IsPGroup 2 X := (pCoreOf_isPGroup 2 Cσ).to_le inf_le_right
    have hXsup : X ≤ Subgroup.zpowers β ⊔ L := by
      intro x hx
      have hxcomm : x * β = β * x :=
        ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).1) β
          (Set.mem_singleton β)).symm
      exact h.Y_cent x (le_trans inf_le_right h.Q_le hx) hxcomm
    have hXL : X ≤ L :=
      le_of_isPGroup_le_sup_zpowers h.L_cent h.L_disj h.β_ord hX2 hXsup
    have hXLC : X ≤ L ⊓ Cσ := le_inf hXL (le_trans inf_le_right (pCoreOf_le 2 Cσ))
    have hLC_norm_X : L ⊓ Cσ ≤ Subgroup.normalizer (X : Set G) := by
      refine le_trans (le_inf ?_ ?_) Subgroup.inf_normalizer_le_normalizer_inf
      · exact le_trans inf_le_left (le_trans hLΓ Subgroup.le_normalizer)
      · exact le_trans inf_le_right (le_normalizer_pCoreOf 2 Cσ)
    exact le_pCoreOf_of_le_normalizer 2 hXLC hLC_norm_X hX2
  have hP_eq : P = Γ ⊓ Q := le_antisymm hP_le_ΓQ hGQ_le_P
  have hP_le_ΓC : P ≤ Γ ⊓ Cσ :=
    le_inf ((le_of_eq hP_eq).trans inf_le_left)
      ((le_of_eq hP_eq).trans (le_trans inf_le_right (pCoreOf_le 2 Cσ)))
  have hΓC_norm_P : Γ ⊓ Cσ ≤ Subgroup.normalizer (P : Set G) := by
    rw [hP_eq]
    refine le_trans (le_inf ?_ ?_) Subgroup.inf_normalizer_le_normalizer_inf
    · exact le_trans inf_le_left Subgroup.le_normalizer
    · exact le_trans inf_le_right (le_normalizer_pCoreOf 2 Cσ)
  exact le_antisymm hO_le_P
    (le_pCoreOf_of_le_normalizer 2 hP_le_ΓC hΓC_norm_P (pCoreOf_isPGroup 2 (L ⊓ Cσ)))

end CFSG.StandardType.FrameRoute.FS81

end
