module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BSpor
import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism
import CFSG.Sporadic.Th.Max3.Maximal

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)


theorem asc80ThmBCase_th : Asc80ThmBCase fun X _ => CFSG.Models.IsSporadic X .Th := by
  have hOut' : ∀ (X : Type) [Group X] [Finite X], CFSG.Models.IsSporadic X .Th →
      Nat.card (Outer X) = 1 := by
    intro X _ _ hX
    letI : Mul TauCeti.SporadicName.Th.Group := Monoid.toMul
    letI : Group (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
      CFSG.Blueprint.NativeSporadic.carrierGroup .Th
    obtain ⟨e₁⟩ := hX
    obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
    let e : X ≃* CFSG.Blueprint.NativeSporadic.Carrier .Th := e₁.trans e₂.symm
    have hTrans : Nat.card (Outer X) =
        Nat.card (Outer (CFSG.Blueprint.NativeSporadic.Carrier .Th)) :=
      Nat.card_congr (@CFSG.ComponentClassification.OuterAutomorphisms.equivalence X
        (CFSG.Blueprint.NativeSporadic.Carrier .Th) _
        (CFSG.Blueprint.NativeSporadic.carrierGroup .Th) e).toEquiv
    have hCarrier : Nat.card (Outer (CFSG.Blueprint.NativeSporadic.Carrier .Th)) = 1 := by
      change (inner (CFSG.Blueprint.NativeSporadic.Carrier .Th)).index = 1
      rw [show inner (CFSG.Blueprint.NativeSporadic.Carrier .Th) = ⊤ from
        CFSG.Sporadic.ThSchreier.inner_Th, Subgroup.index_top]
    exact hTrans.trans hCarrier
  have hSup' : ∀ (X : Type) [Group X] [Finite X], CFSG.Models.IsSporadic X .Th →
      ∀ t₁ t₂ : X, orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ ≠ t₂ →
        Subgroup.centralizer ({t₁} : Set X) ⊔ Subgroup.centralizer {t₂} = ⊤ := by
    intro X _ _ hX t₁ t₂ h₁ h₂ hne
    letI : Mul TauCeti.SporadicName.Th.Group := Monoid.toMul
    obtain ⟨e₁⟩ := hX
    obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
    let e : X ≃* Blueprint.NativeSporadic.Th := e₁.trans e₂.symm
    have hc : ∀ t : X, Subgroup.centralizer ({t} : Set X) =
        (Subgroup.centralizer ({(e t)} : Set Blueprint.NativeSporadic.Th)).comap
          (e : X →* Blueprint.NativeSporadic.Th) := by
      intro t
      ext u
      simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      change u * t = t * u ↔ e u * e t = e t * e u
      rw [← map_mul, ← map_mul, e.injective.eq_iff]
    have h1' : orderOf (e t₁) = 2 := by
      obtain ⟨h2, h1⟩ := orderOf_eq_prime_iff.mp h₁
      have h2m : t₁ * t₁ = 1 := by rwa [pow_two] at h2
      exact orderOf_eq_prime (by rw [pow_two, ← map_mul, h2m, map_one])
        (fun h => h1 (e.injective (by rw [h, map_one])))
    have h2' : orderOf (e t₂) = 2 := by
      obtain ⟨h2, h1⟩ := orderOf_eq_prime_iff.mp h₂
      have h2m : t₂ * t₂ = 1 := by rwa [pow_two] at h2
      exact orderOf_eq_prime (by rw [pow_two, ← map_mul, h2m, map_one])
        (fun h => h1 (e.injective (by rw [h, map_one])))
    have key := CFSG.Sporadic.Th.th_sup_centralizer_eq_top (e t₁) (e t₂) h1' h2'
      (fun h => hne (e.injective h))
    rw [hc t₁, hc t₂, Subgroup.comap_sup_eq (f := (e : X →* Blueprint.NativeSporadic.Th))
      _ _ e.surjective, key, Subgroup.comap_top]
  have hComm' : ∀ (X : Type) [Group X] [Finite X], CFSG.Models.IsSporadic X .Th →
      ∀ t : X, orderOf t = 2 →
        ∃ t' : X, orderOf t' = 2 ∧ t' ≠ t ∧ t * t' = t' * t := by
    intro X _ _ hX t ht
    letI : Mul TauCeti.SporadicName.Th.Group := Monoid.toMul
    obtain ⟨e₁⟩ := hX
    obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
    let e : X ≃* Blueprint.NativeSporadic.Th := e₁.trans e₂.symm
    have ht2 : t * t = 1 := by
      have h := (orderOf_eq_prime_iff.mp ht).1
      rwa [pow_two] at h
    have ht1 : t ≠ 1 := (orderOf_eq_prime_iff.mp ht).2
    have het2 : (e t) * (e t) = 1 := by rw [← map_mul, ht2, map_one]
    have het1 : e t ≠ 1 := fun h => ht1 (e.injective (by rw [h, map_one]))
    have het : orderOf (e t) = 2 := orderOf_eq_prime (by rw [pow_two]; exact het2) het1
    have hx2 : CFSG.Sporadic.Th.Max3.x * CFSG.Sporadic.Th.Max3.x = 1 :=
      CFSG.Sporadic.Th.Max3.x_mul_self
    have hx1 : CFSG.Sporadic.Th.Max3.x ≠ 1 := by
      intro h
      exact CFSG.Sporadic.Th.Max3.x_not_mem_Q (h ▸ Subgroup.one_mem _)
    have hxane : CFSG.Sporadic.Th.Max3.x ≠ CFSG.Sporadic.Th.a := by
      rw [← CFSG.Sporadic.Th.Max3.z_eq_a]
      intro h
      exact CFSG.Sporadic.Th.Max3.x_not_mem_Q (h ▸ CFSG.Sporadic.Th.Max3.z_mem_Q)
    have hax : CFSG.Sporadic.Th.a * CFSG.Sporadic.Th.Max3.x =
        CFSG.Sporadic.Th.Max3.x * CFSG.Sporadic.Th.a := by
      rw [← CFSG.Sporadic.Th.Max3.z_eq_a]
      exact (CFSG.Sporadic.Th.Max3.commute_z_of_mem_M
        CFSG.Sporadic.Th.Max3.x_mem_M).eq
    have hTh : ∀ u : Blueprint.NativeSporadic.Th, orderOf u = 2 →
        ∃ u' : Blueprint.NativeSporadic.Th, orderOf u' = 2 ∧ u' ≠ u ∧ u * u' = u' * u := by
      intro u hu
      obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.Sporadic.Th.Max3.th_involutions_conjugate u hu)
      obtain ⟨a₀, ha₀⟩ : ∃ a₀, CFSG.Sporadic.Th.thEquivJ.symm CFSG.Sporadic.Th.a = a₀ := ⟨_, rfl⟩
      obtain ⟨x₀, hx₀⟩ :
          ∃ x₀, CFSG.Sporadic.Th.thEquivJ.symm CFSG.Sporadic.Th.Max3.x = x₀ := ⟨_, rfl⟩
      rw [ha₀] at hc
      subst hc
      have hJ : ∀ y z : Blueprint.NativeSporadic.Th,
          CFSG.Sporadic.Th.thEquivJ y = CFSG.Sporadic.Th.thEquivJ z → y = z :=
        fun y z h => CFSG.Sporadic.Th.thEquivJ.injective h
      have hx₀1 : x₀ ≠ 1 := fun h => hx1 (by rw [← hx₀, MulEquiv.symm_apply_eq] at h; simpa using h)
      have hx₀a : x₀ ≠ a₀ := fun h => hxane (by
        rw [← hx₀, ← ha₀] at h
        simpa using congrArg CFSG.Sporadic.Th.thEquivJ h)
      have hx₀2 : x₀ * x₀ = 1 := by rw [← hx₀, ← map_mul, hx2, map_one]
      have hax₀ : a₀ * x₀ = x₀ * a₀ := hJ _ _ (by rw [← hx₀, ← ha₀]; simpa using hax)
      refine ⟨c * x₀ * c⁻¹, orderOf_eq_prime ?_ ?_, ?_, ?_⟩
      · calc (c * x₀ * c⁻¹) ^ 2 = c * (x₀ * x₀) * c⁻¹ := by rw [sq]; group
          _ = 1 := by rw [hx₀2]; group
      · intro h
        apply hx₀1
        calc x₀ = c⁻¹ * (c * x₀ * c⁻¹) * c := by group
          _ = 1 := by rw [h]; group
      · intro h
        apply hx₀a
        calc x₀ = c⁻¹ * (c * x₀ * c⁻¹) * c := by group
          _ = c⁻¹ * (c * a₀ * c⁻¹) * c := by rw [h]
          _ = a₀ := by group
      · calc c * a₀ * c⁻¹ * (c * x₀ * c⁻¹) = c * (a₀ * x₀) * c⁻¹ := by group
          _ = c * (x₀ * a₀) * c⁻¹ := by rw [hax₀]
          _ = c * x₀ * c⁻¹ * (c * a₀ * c⁻¹) := by group
    obtain ⟨u', hu'2, hu'ne, hu'comm⟩ := hTh (e t) het
    refine ⟨e.symm u', ?_, ?_, ?_⟩
    · obtain ⟨hsq, hne⟩ := orderOf_eq_prime_iff.mp hu'2
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two, ← map_mul, ← pow_two, hsq, map_one]
      · intro h
        exact hne (by rw [← e.apply_symm_apply u', h, map_one])
    · intro h
      exact hu'ne ((e.apply_symm_apply u').symm.trans (congrArg (⇑e) h))
    · apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hu'comm
  intro G _ _ H A M hs hnab hP hAH hA hM
  exact asc80ThmBCase_of_sup_centralizer (P := fun X _ => CFSG.Models.IsSporadic X .Th)
    hOut' hSup' hComm' H A M hs hnab hP hAH hA hM

theorem asc80ThmBCase_sporadicRep_of_noUMax
    (h : ∀ s : TauCeti.SporadicName, s ≠ .Th →
      Asc80NoUMax fun X _ => CFSG.Models.IsSporadic X s) :
    Asc80ThmBCase fun X _ => CFSG.Models.SporadicRep X := by
  intro G _ _ H A M hs hnab hP hAH hA hM
  obtain ⟨s, hsp⟩ := hP
  by_cases hTh : s = .Th
  · rw [hTh] at hsp
    exact asc80ThmBCase_th H A M hs hnab hsp hAH hA hM
  · exact asc80ThmBCase_isSporadic (h s hTh) H A M hs hnab hsp hAH hA hM

end CFSG.LocalAnalysis.WeakClosure81

end
