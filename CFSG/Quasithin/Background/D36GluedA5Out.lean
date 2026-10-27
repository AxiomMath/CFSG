module

public import CFSG.Quasithin.Background.D36GluedA5Fin
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveRho
public import CFSG.Quasithin.Background.D36GluedNDBase

public section

namespace CFSG.Quasithin

open CFSG.OddStandard

namespace A5Out

theorem conjEquiv5_coe (a : alternatingGroup (Fin 5)) :
    conjEquiv5 (a : Equiv.Perm (Fin 5)) = MulAut.conj a := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [conjEquiv5_apply]
  simp [MulAut.conj_apply]

theorem mulAut_congr_conj {G H : Type*} [Group G] [Group H] (e : G ≃* H) (l : G) :
    MulAut.congr e (MulAut.conj l) = MulAut.conj (e l) := by
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.congr_apply, MulAut.conj_apply]

end A5Out

open A5Out

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace NDSetup

variable (S : NDSetup X A L₀ U U')

include S

@[expose] noncomputable def rhoB (e : ↥L₀ ≃* alternatingGroup (Fin 5)) :
    ↥(A ⊓ stabSub U) →* Equiv.Perm (Fin 5) :=
  conjEquiv5.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp S.theta)

theorem conjEquiv5_rhoB (e : ↥L₀ ≃* alternatingGroup (Fin 5)) (b : ↥(A ⊓ stabSub U)) :
    conjEquiv5 (S.rhoB e b) = MulAut.congr e (S.theta b) := by
  simp [rhoB]

theorem rhoB_injective (e : ↥L₀ ≃* alternatingGroup (Fin 5)) : Function.Injective (S.rhoB e) := by
  intro a b h
  apply S.theta_injective
  apply (MulAut.congr e).injective
  have := congrArg conjEquiv5 h
  rwa [conjEquiv5_rhoB, conjEquiv5_rhoB] at this

theorem theta_eq_conj_of_rho (e : ↥L₀ ≃* alternatingGroup (Fin 5)) {b : ↥(A ⊓ stabSub U)}
    {l' : ↥L₀}
    (h : S.rhoB e b = ((e l' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))) :
    S.theta b = MulAut.conj l' := by
  apply (MulAut.congr e).injective
  rw [← conjEquiv5_rhoB, h, conjEquiv5_coe, mulAut_congr_conj]

theorem inner_of_rho (e : ↥L₀ ≃* alternatingGroup (Fin 5)) {b : ↥(A ⊓ stabSub U)} {l' : ↥L₀}
    (h : S.rhoB e b = ((e l' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))) :
    ∀ u ∈ U, (b : MulAut Y) u = (l' : MulAut Y) u := by
  have hθ := S.theta_eq_conj_of_rho e h
  refine S.inner b b.2 l' l'.2 (fun l hl => ?_)
  have := congrArg (fun φ : MulAut ↥L₀ => ((φ ⟨l, hl⟩ : ↥L₀) : MulAut Y)) hθ
  simpa [theta_apply, MulAut.conj_apply] using this

theorem sign_rhoB_eq_neg_one (e : ↥L₀ ≃* alternatingGroup (Fin 5)) {b : ↥(A ⊓ stabSub U)}
    (hnd : ∀ l ∈ L₀, ∃ u ∈ U, (b : MulAut Y) u ≠ l u) :
    Equiv.Perm.sign (S.rhoB e b) = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign (S.rhoB e b)) with h | h
  · exfalso
    have hmem : S.rhoB e b ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr h
    set l' : ↥L₀ := e.symm ⟨S.rhoB e b, hmem⟩ with hl'
    have h1 : S.rhoB e b = ((e l' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := by
      simp [hl']
    obtain ⟨u, hu, hne⟩ := hnd l' l'.2
    exact hne (S.inner_of_rho e h1 u hu)
  · exact h

theorem exists_outer_data (e : ↥L₀ ≃* alternatingGroup (Fin 5))
    (hk : rk ↥(A ⊓ stabSub U) = 2) :
    ∃ b l : MulAut Y, b ∈ A ⊓ stabSub U ∧ l ∈ A ⊓ stabSub U ∧ b ≠ 1 ∧ b * b = 1 ∧
      l * l = 1 ∧ b * l = l * b ∧ ∃ l₀ g : ↥L₀, (∀ u ∈ U, l u = (l₀ : MulAut Y) u) ∧
        l₀ * l₀ = 1 ∧ l₀ ≠ 1 ∧ g * g * g = 1 ∧ g ≠ 1 ∧
        b * (g : MulAut Y) = (g : MulAut Y) * b ∧ l₀ * g * l₀ = g⁻¹ := by
  obtain ⟨b₁, hb₁, hnd⟩ : ∃ b ∈ A ⊓ stabSub U, ∀ l ∈ L₀, ∃ u ∈ U, b u ≠ l u := by
    by_contra hcon
    push Not at hcon
    exact S.nondiag hcon
  set β₁ : ↥(A ⊓ stabSub U) := ⟨b₁, hb₁⟩ with hβ₁
  have hel := S.elemAb
  have hsq : ∀ x : ↥(A ⊓ stabSub U), x * x = 1 := fun x =>
    Subtype.ext (by simpa [pow_two] using hel.2 x x.2)
  have hcomm : ∀ x y : ↥(A ⊓ stabSub U), x * y = y * x := fun x y =>
    Subtype.ext (hel.1 x x.2 y y.2)
  have hcard : Nat.card ↥(A ⊓ stabSub U) = 4 := by
    rw [hel.card_eq_two_pow, hk]
    norm_num
  have hb₂ : ∃ β₂ : ↥(A ⊓ stabSub U), β₂ ≠ 1 ∧ β₂ ≠ β₁ := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set ↥(A ⊓ stabSub U)) ⊆ {1, β₁} := fun x _ => by
      by_cases h1 : x = 1
      · exact Or.inl h1
      · exact Or.inr (hcon x h1)
    have hle : Nat.card ↥(A ⊓ stabSub U) ≤ 2 := by
      calc Nat.card ↥(A ⊓ stabSub U) = (Set.univ : Set ↥(A ⊓ stabSub U)).ncard :=
            (Set.ncard_univ _).symm
        _ ≤ ({1, β₁} : Set ↥(A ⊓ stabSub U)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    omega
  obtain ⟨β₂, hβ₂1, hβ₂⟩ := hb₂
  have hs₁ : Equiv.Perm.sign (S.rhoB e β₁) = -1 := S.sign_rhoB_eq_neg_one e hnd
  obtain ⟨β₃, hβ₃1, hβ₃s⟩ : ∃ x : ↥(A ⊓ stabSub U), x ≠ 1 ∧
      Equiv.Perm.sign (S.rhoB e x) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (S.rhoB e β₂)) with h | h
    · exact ⟨β₂, hβ₂1, h⟩
    · refine ⟨β₁ * β₂, ?_, ?_⟩
      · intro h1
        apply hβ₂
        have h2 : β₂ = β₁⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [h2]
        exact inv_eq_of_mul_eq_one_right (hsq β₁)
      · rw [map_mul, map_mul, hs₁, h]
        norm_num
  have hmem3 : S.rhoB e β₃ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr hβ₃s
  set l₀ : ↥L₀ := e.symm ⟨S.rhoB e β₃, hmem3⟩ with hl₀
  have hρl₀ : S.rhoB e β₃ = ((e l₀ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := by
    simp [hl₀]
  have hinner : ∀ u ∈ U, (β₃ : MulAut Y) u = (l₀ : MulAut Y) u := S.inner_of_rho e hρl₀
  have hσ2 : S.rhoB e β₁ * S.rhoB e β₁ = 1 := by rw [← map_mul, hsq, map_one]
  have hk2 : S.rhoB e β₃ * S.rhoB e β₃ = 1 := by rw [← map_mul, hsq, map_one]
  have hk1 : S.rhoB e β₃ ≠ 1 := by
    intro h
    apply hβ₃1
    apply S.rhoB_injective e
    rw [h, map_one]
  have hσk : S.rhoB e β₁ * S.rhoB e β₃ = S.rhoB e β₃ * S.rhoB e β₁ := by
    rw [← map_mul, ← map_mul, hcomm]
  have hl₀sq : l₀ * l₀ = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    apply Subtype.ext
    rw [hρl₀] at hk2
    simpa using hk2
  have hl₀1 : l₀ ≠ 1 := by
    intro h
    apply hβ₃1
    apply S.rhoB_injective e
    rw [hρl₀, h, map_one, map_one]
    rfl
  obtain ⟨y, hys, hy3, hy1, hσy, hky⟩ := A5Fin.exists_inverted_three (S.rhoB e β₁)
    (S.rhoB e β₃) hs₁ hσ2 hβ₃s hk2 hk1 hσk
  set g : ↥L₀ := e.symm ⟨y, Equiv.Perm.mem_alternatingGroup.mpr hys⟩ with hg
  have heg : ((e g : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = y := by simp [hg]
  have hg3 : g * g * g = 1 := by
    apply e.injective
    rw [map_mul, map_mul, map_one]
    apply Subtype.ext
    simpa [heg] using hy3
  have hg1 : g ≠ 1 := by
    intro h
    apply hy1
    rw [← heg, h, map_one]
    rfl
  have hθg : S.theta β₁ g = g := by
    apply e.injective
    have h1 : (MulAut.congr e (S.theta β₁)) (e g) = e (S.theta β₁ g) := by
      simp [MulAut.congr_apply]
    rw [← h1, ← conjEquiv5_rhoB]
    apply Subtype.ext
    rw [conjEquiv5_apply, heg, hσy, mul_assoc, mul_inv_cancel, mul_one]
  have hβg : (β₁ : MulAut Y) * (g : MulAut Y) = (g : MulAut Y) * (β₁ : MulAut Y) := by
    have h1 := S.theta_apply β₁ g
    rw [hθg] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1.symm)
  have hlg : l₀ * g * l₀ = g⁻¹ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv]
    apply Subtype.ext
    have hk' : (S.rhoB e β₃)⁻¹ = S.rhoB e β₃ := inv_eq_of_mul_eq_one_right hk2
    rw [hk'] at hky
    show ((e l₀ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
      ((e g : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
        ((e l₀ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
      ((e g : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹
    rw [← hρl₀, heg]
    exact hky
  refine ⟨(β₁ : MulAut Y), (β₃ : MulAut Y), β₁.2, β₃.2, ?_, ?_, ?_, ?_, l₀, g, hinner, hl₀sq,
    hl₀1, hg3, hg1, hβg, hlg⟩
  · intro h
    obtain ⟨u, hu, hne⟩ := hnd 1 (one_mem _)
    apply hne
    rw [show b₁ = 1 from h]
  · exact congrArg Subtype.val (hsq β₁)
  · exact congrArg Subtype.val (hsq β₃)
  · exact congrArg Subtype.val (hcomm β₁ β₃)

end NDSetup

end CFSG.Quasithin
