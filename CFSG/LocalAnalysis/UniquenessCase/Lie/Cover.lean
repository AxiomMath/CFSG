module

public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped commutatorElement

theorem uc22pwlie_comm_mul_central {X : Type} [Group X] (a b z w : X) (hz : ∀ g : X, g * z = z * g)
    (hw : ∀ g : X, g * w = w * g) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have e1 : z * (b * w) * z⁻¹ = b * w := by rw [← hz (b * w)]; group
  have e2 : w * a⁻¹ * w⁻¹ = a⁻¹ := by rw [← hw a⁻¹]; group
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * (w⁻¹ * b⁻¹) := by
        simp only [commutatorElement_def, mul_inv_rev]; group
    _ = a * (b * w) * a⁻¹ * (w⁻¹ * b⁻¹) := by rw [e1]
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [e2]
    _ = ⁅a, b⁆ := by simp [commutatorElement_def]

theorem uc22pwlie_exists_cover_of_closed {S X Q : Type} [Group S] [Group X] [Group Q]
    (hclosed : ∀ (E : Type) [Group E] (π : E →* S), Function.Surjective π → π.ker ≤ center E →
      ∃ σ : S →* E, ∀ g, π (σ g) = g)
    (hXp : commutator X = ⊤) (π : X →* Q) (hπ : Function.Surjective π) (hπc : π.ker ≤ center X)
    (ρ : S →* Q) (hρ : Function.Surjective ρ) (hρc : ρ.ker ≤ center S) :
    ∃ α : S →* X, Function.Surjective α ∧ α.ker ≤ center S ∧ ∀ s, π (α s) = ρ s := by
  classical
  let E : Subgroup (X × S) :=
    MonoidHom.eqLocus (π.comp (MonoidHom.fst X S)) (ρ.comp (MonoidHom.snd X S))
  let p : E →* S := (MonoidHom.snd X S).comp E.subtype
  have hp : Function.Surjective p := by
    intro s
    obtain ⟨x, hx⟩ := hπ (ρ s)
    exact ⟨⟨(x, s), hx⟩, rfl⟩
  have hpc : p.ker ≤ center E := by
    intro e he
    have hs : e.1.2 = 1 := he
    have hx : π e.1.1 = 1 := by
      have h : π e.1.1 = ρ e.1.2 := e.2
      rw [hs, map_one] at h
      exact h
    have hxc : e.1.1 ∈ center X := hπc hx
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    apply Prod.ext
    · exact mem_center_iff.1 hxc g.1.1
    · simp [hs]
  obtain ⟨σ, hσ⟩ := hclosed E p hp hpc
  let α : S →* X := (MonoidHom.fst X S).comp (E.subtype.comp σ)
  have hαπ : ∀ s, π (α s) = ρ s := by
    intro s
    have h : π ((σ s : E) : X × S).1 = ρ ((σ s : E) : X × S).2 := (σ s).2
    have h2 : ((σ s : E) : X × S).2 = s := hσ s
    rw [h2] at h
    exact h
  refine ⟨α, ?_, ?_, hαπ⟩
  ·
    have hcomm : ∀ x₁ x₂ : X, ⁅x₁, x₂⁆ ∈ α.range := by
      intro x₁ x₂
      obtain ⟨s₁, hs₁⟩ := hρ (π x₁)
      obtain ⟨s₂, hs₂⟩ := hρ (π x₂)
      have hz₁ : (α s₁)⁻¹ * x₁ ∈ center X := by
        apply hπc
        rw [MonoidHom.mem_ker, map_mul, map_inv, hαπ, hs₁]
        exact inv_mul_cancel _
      have hz₂ : (α s₂)⁻¹ * x₂ ∈ center X := by
        apply hπc
        rw [MonoidHom.mem_ker, map_mul, map_inv, hαπ, hs₂]
        exact inv_mul_cancel _
      have e₁ : x₁ = α s₁ * ((α s₁)⁻¹ * x₁) := by group
      have e₂ : x₂ = α s₂ * ((α s₂)⁻¹ * x₂) := by group
      set z₁ := (α s₁)⁻¹ * x₁ with hz₁def
      set z₂ := (α s₂)⁻¹ * x₂ with hz₂def
      have c₁ : ∀ g : X, g * z₁ = z₁ * g := mem_center_iff.1 hz₁
      have c₂ : ∀ g : X, g * z₂ = z₂ * g := mem_center_iff.1 hz₂
      have key : ⁅x₁, x₂⁆ = ⁅α s₁, α s₂⁆ := by
        rw [e₁, e₂]
        exact uc22pwlie_comm_mul_central _ _ _ _ c₁ c₂
      rw [key]
      exact ⟨⁅s₁, s₂⁆, by simp [map_commutatorElement]⟩
    have hle : commutator X ≤ α.range := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_le.2 fun x₁ _ x₂ _ => hcomm x₁ x₂
    intro x
    have hx : x ∈ α.range := by
      have h := hle
      rw [hXp] at h
      exact h (Subgroup.mem_top x)
    exact hx
  · intro s hs
    have : ρ s = 1 := by
      rw [← hαπ]
      have : α s = 1 := hs
      rw [this, map_one]
    exact hρc this

theorem uc22pwlie_exists_cover_of_closed_fin {S X Q : Type} [Group S] [Finite S] [Group X] [Finite X] [Group Q]
    (hclosed : ∀ (E : Type) [Group E] [Finite E] (π : E →* S), Function.Surjective π → π.ker ≤ center E →
      ∃ σ : S →* E, ∀ g, π (σ g) = g)
    (hXp : commutator X = ⊤) (π : X →* Q) (hπ : Function.Surjective π) (hπc : π.ker ≤ center X)
    (ρ : S →* Q) (hρ : Function.Surjective ρ) (hρc : ρ.ker ≤ center S) :
    ∃ α : S →* X, Function.Surjective α ∧ α.ker ≤ center S ∧ ∀ s, π (α s) = ρ s := by
  classical
  let E : Subgroup (X × S) :=
    MonoidHom.eqLocus (π.comp (MonoidHom.fst X S)) (ρ.comp (MonoidHom.snd X S))
  let p : E →* S := (MonoidHom.snd X S).comp E.subtype
  have hp : Function.Surjective p := by
    intro s
    obtain ⟨x, hx⟩ := hπ (ρ s)
    exact ⟨⟨(x, s), hx⟩, rfl⟩
  have hpc : p.ker ≤ center E := by
    intro e he
    have hs : e.1.2 = 1 := he
    have hx : π e.1.1 = 1 := by
      have h : π e.1.1 = ρ e.1.2 := e.2
      rw [hs, map_one] at h
      exact h
    have hxc : e.1.1 ∈ center X := hπc hx
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    apply Prod.ext
    · exact mem_center_iff.1 hxc g.1.1
    · simp [hs]
  obtain ⟨σ, hσ⟩ := hclosed E p hp hpc
  let α : S →* X := (MonoidHom.fst X S).comp (E.subtype.comp σ)
  have hαπ : ∀ s, π (α s) = ρ s := by
    intro s
    have h : π ((σ s : E) : X × S).1 = ρ ((σ s : E) : X × S).2 := (σ s).2
    have h2 : ((σ s : E) : X × S).2 = s := hσ s
    rw [h2] at h
    exact h
  refine ⟨α, ?_, ?_, hαπ⟩
  · have hcomm : ∀ x₁ x₂ : X, ⁅x₁, x₂⁆ ∈ α.range := by
      intro x₁ x₂
      obtain ⟨s₁, hs₁⟩ := hρ (π x₁)
      obtain ⟨s₂, hs₂⟩ := hρ (π x₂)
      have hz₁ : (α s₁)⁻¹ * x₁ ∈ center X := by
        apply hπc
        rw [MonoidHom.mem_ker, map_mul, map_inv, hαπ, hs₁]
        exact inv_mul_cancel _
      have hz₂ : (α s₂)⁻¹ * x₂ ∈ center X := by
        apply hπc
        rw [MonoidHom.mem_ker, map_mul, map_inv, hαπ, hs₂]
        exact inv_mul_cancel _
      have e₁ : x₁ = α s₁ * ((α s₁)⁻¹ * x₁) := by group
      have e₂ : x₂ = α s₂ * ((α s₂)⁻¹ * x₂) := by group
      set z₁ := (α s₁)⁻¹ * x₁ with hz₁def
      set z₂ := (α s₂)⁻¹ * x₂ with hz₂def
      have c₁ : ∀ g : X, g * z₁ = z₁ * g := mem_center_iff.1 hz₁
      have c₂ : ∀ g : X, g * z₂ = z₂ * g := mem_center_iff.1 hz₂
      have key : ⁅x₁, x₂⁆ = ⁅α s₁, α s₂⁆ := by
        rw [e₁, e₂]
        exact uc22pwlie_comm_mul_central _ _ _ _ c₁ c₂
      rw [key]
      exact ⟨⁅s₁, s₂⁆, by simp [map_commutatorElement]⟩
    have hle : commutator X ≤ α.range := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_le.2 fun x₁ _ x₂ _ => hcomm x₁ x₂
    intro x
    have hx : x ∈ α.range := by
      have h := hle
      rw [hXp] at h
      exact h (Subgroup.mem_top x)
    exact hx
  · intro s hs
    have : ρ s = 1 := by
      rw [← hαπ]
      have : α s = 1 := hs
      rw [this, map_one]
    exact hρc this

theorem uc22pwlie_exists_slCover {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] [Finite K] (hK : 5 ≤ Nat.card K)
    {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    (e : X ⧸ Subgroup.center X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (m + 1) K) :
    ∃ α : Matrix.SpecialLinearGroup (Fin (m + 1)) K →* X, Function.Surjective α ∧
      α.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) K) := by
  have hρ : Function.Surjective (e.symm.toMonoidHom.comp
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (m + 1) K)) :=
    e.symm.surjective.comp (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective (m + 1) K)
  have hρc : (e.symm.toMonoidHom.comp
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (m + 1) K)).ker ≤
        Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) K) := by
    intro s hs
    have h1 : e.symm (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (m + 1) K s) = 1 := hs
    have h2 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (m + 1) K s = 1 := by
      simpa using h1
    exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_le_center (m + 1) K
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_one_iff.1 h2)
  obtain ⟨α, hα, hαc, -⟩ := uc22pwlie_exists_cover_of_closed
    (fun E _ π hπ hc => CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central hm hK hπ hc)
    hq.1 (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) _ hρ hρc
  exact ⟨α, hα, hαc⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
