module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X

public section

namespace CFSG.Quasithin.H13.Case4Fix

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.CZL32 CFSG.Quasithin.H13.X3324
open CFSG.Quasithin.H13.Gen3324

variable {G : Type} [Group G] [Finite G]

theorem exists_X {T Y W : Subgroup G} (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hYW : Y ≤ Subgroup.normalizer (W : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (β : ↥W ≃* Multiplicative L3.Vec)
    (α₃ : ↥Y →* L3.Γ) (hα₃s : Function.Surjective α₃)
    (hα₃k : ∀ y : ↥Y, α₃ y = 1 → (y : G) ∈ pCoreOf 2 Y)
    (hβe : ∀ (y : ↥Y) (u v : ↥W), (v : G) = y * u * y⁻¹ →
      Multiplicative.toAdd (β v) = L3.act (α₃ y) (Multiplicative.toAdd (β u)))
    {z₀ : G} (hz₀W : z₀ ∈ W) (hz₀Z : z₀ ∈ quasithinOmegaOneCenter T) (hz₀ : z₀ ≠ 1)
    (hZ : ∀ y (hy : y ∈ Y), L3.act (α₃ ⟨y, hy⟩) (Multiplicative.toAdd (β ⟨z₀, hz₀W⟩)) =
      Multiplicative.toAdd (β ⟨z₀, hz₀W⟩) →
        y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ∃ X : Subgroup G, oTwoUpper X = X ∧ T ≤ Subgroup.normalizer (X : Set G) ∧
      Nonempty (↥(X ⊔ T) ⧸ CFSG.pCore 2 ↥(X ⊔ T) ≃* Equiv.Perm (Fin 3)) ∧
      X ⊔ T = Y ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T ∧
      X ≤ Y ∧ X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZdef
  obtain ⟨σ, hσ⟩ := exists_twist hTW hT2 β
  set β' := β.trans (actEquiv σ) with hβ'
  have hρα : ∀ ℓ (hℓ : ℓ ∈ Y), rhoV β ⟨ℓ, hYW hℓ⟩ = α₃ ⟨ℓ, hℓ⟩ :=
    fun ℓ hℓ => rhoV_eq β hYW α₃ hβe ⟨ℓ, hℓ⟩
  have hρY : ∀ γ : L3.Γ, ∃ ℓ, ∃ hℓ : ℓ ∈ Y, rhoV β' ⟨ℓ, hYW hℓ⟩ = γ := by
    intro γ
    obtain ⟨ℓ, hℓ⟩ := hα₃s (σ⁻¹ * γ * σ)
    refine ⟨ℓ, ℓ.2, ?_⟩
    rw [rhoV_twist, hρα ℓ ℓ.2, show (⟨(ℓ : G), ℓ.2⟩ : ↥Y) = ℓ from rfl, hℓ]
    group
  have hρK : ∀ ℓ (hℓ : ℓ ∈ Y), rhoV β' ⟨ℓ, hYW hℓ⟩ = 1 → ℓ ∈ pCoreOf 2 Y := by
    intro ℓ hℓ h1
    apply hα₃k ⟨ℓ, hℓ⟩
    rw [rhoV_twist, hρα ℓ hℓ] at h1
    calc α₃ ⟨ℓ, hℓ⟩ = σ⁻¹ * (σ * α₃ ⟨ℓ, hℓ⟩ * σ⁻¹) * σ := by group
      _ = 1 := by rw [h1]; group
  have hsurj : Function.Surjective (rhoV β') := fun γ => by
    obtain ⟨ℓ, hℓ, e⟩ := hρY γ
    exact ⟨_, e⟩
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hcz : ∀ t ∈ T, t * z₀ * t⁻¹ = z₀ := fun t ht => by
    have := Subgroup.mem_centralizer_iff.mp (hTZ ht) z₀ hz₀Z
    rw [← this]
    group
  have hθz : Multiplicative.toAdd (β' ⟨z₀, hz₀W⟩) = e1 := by
    rcases fix_T (rhoV β') hTW hTidx hσ hsurj (v := Multiplicative.toAdd (β' ⟨z₀, hz₀W⟩))
        (fun t ht => act_rhoV_of_conj β' (g := ⟨t, hTW ht⟩) (u := ⟨z₀, hz₀W⟩) (hcz t ht))
      with h0 | h1
    · exact absurd (congrArg Subtype.val (eq_of_toAdd_beta β' (u := ⟨z₀, hz₀W⟩) (u' := 1)
        (by rw [toAdd_beta_one]; exact h0))) hz₀
    · exact h1
  have hZ' : ∀ y (hy : y ∈ Y), L3.act (rhoV β' ⟨y, hYW hy⟩) e1 = e1 →
      y ∈ Subgroup.centralizer (Z : Set G) := by
    intro y hy h1
    apply hZ y hy
    rw [← hθz, toAdd_actEquiv, rhoV_twist, hρα y hy, L3.act_mul, L3.act_mul,
      L3.act_inv_act] at h1
    have h2 := congrArg (L3.act σ⁻¹) h1
    rwa [L3.act_inv_act, L3.act_inv_act] at h2
  have hYTW : Y ⊔ T ≤ Subgroup.normalizer (W : Set G) := sup_le hYW hTW
  set ρ : ↥(Y ⊔ T) →* L3.Γ := (rhoV β').comp (Subgroup.inclusion hYTW) with hρdef
  have hsurjK : ∀ γ, ∃ k : ↥(Y ⊔ T), ρ k = γ := fun γ => by
    obtain ⟨ℓ, hℓ, e⟩ := hρY γ
    exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩
  have htop : ρ.range = ⊤ := eq_top_iff.mpr fun γ _ => MonoidHom.mem_range.mpr (hsurjK γ)
  have h6 : Nat.card ↥(ρ.range ⊓ L3.ptSub e1) = 6 * Nat.card ↥(ρ.range ⊓ rSub) := by
    rw [htop, top_inf_eq, top_inf_eq, card_ptSub, card_rSub]
  obtain ⟨ka, ea⟩ := hsurjK aW
  obtain ⟨kb, eb⟩ := hsurjK bW
  have hρK' : ∀ g : ↥(Y ⊔ T), ρ g = 1 → (g : G) ∈ pCoreOf 2 (Y ⊔ T) :=
    fun g hg => mem_qL_of_ker ρ hTY hT2 (fun ℓ hℓ h1 => hρK ℓ hℓ h1) g hg
  obtain ⟨hXX, hTX, hXT, ⟨eS3⟩, -, -⟩ := parabolic_gen₀ ρ le_sup_right hT2 hTidx hρK'
    (p := L3.ptSub e1) (r := rSub) (fun t ht => bSub_le_ptSub (hσ t ht)) rSub_le_ptSub
    ptSub_le_normalizer (fun x hx => sq_eq_one_of_mem_rSub hx) h6 (ka := ka) (kb := kb)
    (by rw [ea]; exact aW_mem) (by rw [eb]; exact bW_mem) (by rw [ea, eb]; exact comm_not_mem)
  set P := pre₀ ρ (L3.ptSub e1) with hP
  set X := oTwoUpper P with hX
  have hmemP : ∀ {g : G} (hg : g ∈ Y ⊔ T), rhoV β' ⟨g, hYTW hg⟩ ∈ L3.ptSub e1 → g ∈ P :=
    fun hg h1 => (mem_pre₀ ρ).mpr ⟨hg, h1⟩
  have hTP : T ≤ P := fun t ht => hmemP (Subgroup.mem_sup_right ht) (bSub_le_ptSub (hσ t ht))
  have hoddP : ∀ x ∈ P, Odd (orderOf x) → x ∈ Y ⊓ Subgroup.centralizer (Z : Set G) := by
    intro x hx ho
    obtain ⟨hxLT, hxp⟩ := (mem_pre₀ ρ).mp hx
    have hxY : x ∈ Y := One3323.mem_of_odd hT2 hTY hxLT ho
    exact ⟨hxY, hZ' x hxY hxp⟩
  have hXYZ : X ≤ Y ⊓ Subgroup.centralizer (Z : Set G) := by
    rw [hX, oTwoUpper, Subgroup.closure_le]
    rintro x ⟨hx, ho⟩
    exact hoddP x hx ho
  have hYZP : Y ⊓ Subgroup.centralizer (Z : Set G) ≤ P := by
    rintro y ⟨hyY, hyZ⟩
    refine hmemP (Subgroup.mem_sup_left hyY) ?_
    rw [L3.mem_ptSub, ← hθz]
    refine act_rhoV_of_conj β' (g := ⟨y, hYTW (Subgroup.mem_sup_left hyY)⟩)
      (u := ⟨z₀, hz₀W⟩) ?_
    have := Subgroup.mem_centralizer_iff.mp hyZ z₀ hz₀Z
    show y * z₀ * y⁻¹ = z₀
    rw [← this]
    group
  have hXTe : X ⊔ T = Y ⊓ Subgroup.centralizer (Z : Set G) ⊔ T :=
    le_antisymm (sup_le_sup_right hXYZ T) (by rw [hXT]; exact sup_le hYZP hTP)
  exact ⟨X, hXX, hTX, Par32.nonempty_quot_pCore_congr hXT ⟨eS3⟩, hXTe,
    hXYZ.trans inf_le_left, hXYZ.trans inf_le_right⟩

end CFSG.Quasithin.H13.Case4Fix
