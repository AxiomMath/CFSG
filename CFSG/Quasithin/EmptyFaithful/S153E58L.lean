module

public import CFSG.Quasithin.EmptyFaithful.S153E58K

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153E58

open S153E57

section Classify

variable {W : Type} [CommGroup W] {H K : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}
  {bil : W → W → ZMod 2}

theorem Setup58.eq_or_eq_of_irr (hS : Setup58 H K W₁ W₂ bil) {e : ↥W₁ ≃* V3} (hT : TransvIn K W₁ e)
    {S : Subgroup W} (hSirr : IsIrrOn153 K S) : S = W₁ ∨ S = W₂ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hS1, hS2⟩ := hcon
  have hSinv : ∀ k ∈ K, ∀ s ∈ S, k s ∈ S := hSirr.2.1
  have hSW₁ : S ⊓ W₁ = ⊥ := by
    rcases hSirr.2.2 (S ⊓ W₁) inf_le_left
        (fun k hk b hb => ⟨hSinv k hk b hb.1, hS.inv₁ k hk b hb.2⟩) with h | h
    · exact h
    · exfalso
      have hle : S ≤ W₁ := by
        intro x hx
        have : x ∈ S ⊓ W₁ := by
          rw [h]
          exact hx
        exact this.2
      rcases hS.irr₁.2.2 S hle hSinv with h' | h'
      · exact hSirr.1 h'
      · exact hS1 h'
  have hSW₂ : S ⊓ W₂ = ⊥ := by
    rcases hSirr.2.2 (S ⊓ W₂) inf_le_left
        (fun k hk b hb => ⟨hSinv k hk b hb.1, hS.inv₂ k hk b hb.2⟩) with h | h
    · exact h
    · exfalso
      have hle : S ≤ W₂ := by
        intro x hx
        have : x ∈ S ⊓ W₂ := by
          rw [h]
          exact hx
        exact this.2
      rcases hS.irr₂.2.2 S hle hSinv with h' | h'
      · exact hSirr.1 h'
      · exact hS2 h'
  obtain ⟨p, hp⟩ := exists_proj hS.dir
  have hpinj : ∀ s ∈ S, p s = 1 → s = 1 := by
    intro s hs hps
    have h1 : s ∈ W₂ := by
      have := (hp 1 s).2 hps
      simpa using this
    have : s ∈ S ⊓ W₂ := ⟨hs, h1⟩
    rw [hSW₂, Subgroup.mem_bot] at this
    exact this
  have hpeq : ∀ k ∈ K, ∀ w, ((p (k w) : ↥W₁) : W) = k (p w) := fun k hk w =>
    proj_equivariant hp (hS.inv₁ k hk) (hS.inv₂ k hk) w
  have hsurj : ∀ a ∈ W₁, ∃ s ∈ S, ((p s : ↥W₁) : W) = a := by
    let PS : Subgroup W := S.map (W₁.subtype.comp p)
    have hPSle : PS ≤ W₁ := by
      rintro _ ⟨s, -, rfl⟩
      exact (p s).2
    have hPSinv : ∀ k ∈ K, ∀ b ∈ PS, k b ∈ PS := by
      rintro k hk _ ⟨s, hs, rfl⟩
      exact ⟨k s, hSinv k hk s hs, by simp [hpeq k hk]⟩
    have hPSne : PS ≠ ⊥ := by
      intro hbot
      obtain ⟨s, hs, hs1⟩ : ∃ s ∈ S, s ≠ 1 := by
        by_contra hcon'
        push Not at hcon'
        exact hSirr.1 ((Subgroup.eq_bot_iff_forall S).2 hcon')
      have : (W₁.subtype.comp p) s ∈ PS := ⟨s, hs, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      apply hs1
      apply hpinj s hs
      exact Subtype.ext this
    rcases hS.irr₁.2.2 PS hPSle hPSinv with h | h
    · exact absurd h hPSne
    · intro a ha
      have : a ∈ PS := h ▸ ha
      obtain ⟨s, hs, hsa⟩ := this
      exact ⟨s, hs, hsa⟩
  let σ : W → W := fun a => if h : a ∈ W₁ then (hsurj a h).choose else 1
  have hσ : ∀ a ∈ W₁, σ a ∈ S ∧ ((p (σ a) : ↥W₁) : W) = a := by
    intro a ha
    simp only [σ, ha, ↓reduceDIte]
    exact (hsurj a ha).choose_spec
  have hσk : ∀ k ∈ K, ∀ a ∈ W₁, σ (k a) = k (σ a) := by
    intro k hk a ha
    obtain ⟨hσS, hσp⟩ := hσ a ha
    obtain ⟨hσS', hσp'⟩ := hσ (k a) (hS.inv₁ k hk a ha)
    have h1 : k (σ a) ∈ S := hSinv k hk _ hσS
    have h2 : ((p (k (σ a)) : ↥W₁) : W) = k a := by rw [hpeq k hk, hσp]
    have h3 : (σ (k a))⁻¹ * k (σ a) ∈ S := S.mul_mem (S.inv_mem hσS') h1
    have h4 : p ((σ (k a))⁻¹ * k (σ a)) = 1 := by
      rw [map_mul, map_inv]
      have : p (σ (k a)) = p (k (σ a)) := Subtype.ext (hσp'.trans h2.symm)
      rw [this, inv_mul_cancel]
    have := hpinj _ h3 h4
    exact (inv_mul_eq_one.1 this)
  have h0 := hS.bil_zero_W₁ hT
  have hf : ∀ a ∈ W₁, ∀ b ∈ W₁, bil (σ a) b = 0 :=
    form_zero_of_transv hT hS.inv₁ (fun a b => bil (σ a) b) (fun a b c => hS.bil_right (σ a) b c)
      (fun k hk a ha b _ => by
        show bil (σ (k a)) (k b) = bil (σ a) b
        rw [hσk k hk a ha]
        exact hS.bil_inv_K hk _ _)
  obtain ⟨a, haW₁, ha1⟩ : ∃ a ∈ W₁, a ≠ 1 := by
    by_contra hcon'
    push Not at hcon'
    exact hS.W₁_ne_bot ((Subgroup.eq_bot_iff_forall W₁).2 hcon')
  obtain ⟨hσS, hσp⟩ := hσ a haW₁
  set s := σ a with hs
  have hsy : ((p s : ↥W₁) : W)⁻¹ * s ∈ W₂ := (hp (p s) s).2 rfl
  have hy1 : ((p s : ↥W₁) : W)⁻¹ * s = 1 := by
    apply hS.eq_one_of_orth hT _ hsy
    intro b hb
    rw [hS.bil_symm]
    have e : s = ((p s : ↥W₁) : W) * (((p s : ↥W₁) : W)⁻¹ * s) := by group
    have h1 := hf a haW₁ b hb
    rw [← hs, e, hS.bil_left, h0 _ (p s).2 b hb, zero_add] at h1
    exact h1
  have hsW₁ : s ∈ W₁ := by
    have : s = ((p s : ↥W₁) : W) := by
      have := mul_eq_one_iff_eq_inv.1 hy1 |>.symm
      calc s = ((p s : ↥W₁) : W) * (((p s : ↥W₁) : W)⁻¹ * s) := by group
        _ = ((p s : ↥W₁) : W) := by rw [hy1, mul_one]
    rw [this]
    exact (p s).2
  have : s ∈ S ⊓ W₁ := ⟨hσS, hsW₁⟩
  rw [hSW₁, Subgroup.mem_bot] at this
  apply ha1
  rw [← hσp, this]
  simp

end Classify

end S153E58

end CFSG.Quasithin
