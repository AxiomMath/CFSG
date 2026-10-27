module

public import CFSG.RankThree.PartOne.TCP.AlCore
public import CFSG.RankThree.PartOne.S11d.ThreeCompAL
public import CFSG.RankThree.PartOne.TCP.AlSector

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.TCP
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedSp)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)

theorem clauseA_of_mulEquiv {T S : Type} [Group T] [Group S] (e : T ≃* S) (α : MulAut T)
    (σ' : MulAut S) (hcongr : MulAut.congr e α = σ') {p : ℕ} {D : Subgroup T}
    (h : (∀ E ∈ D.map e.toMonoidHom, ¬ ∀ g ∈ D.map e.toMonoidHom, σ' g = E * g * E⁻¹) ∧
      (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
        LieModel (↥(D.map e.toMonoidHom) ⧸ Subgroup.center ↥(D.map e.toMonoidHom)) t' n' 2
          (p * f')) ∧
      ∃ t₁ ∈ D.map e.toMonoidHom, σ' t₁ = t₁ ∧ ∃ t₂ ∈ D.map e.toMonoidHom, σ' t₂ = t₂ ∧
        (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧ (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁) :
    (∀ E ∈ D, ¬ ∀ g ∈ D, α g = E * g * E⁻¹) ∧
      (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
        LieModel (↥D ⧸ Subgroup.center ↥D) t' n' 2 (p * f')) ∧
      ∃ t₁ ∈ D, α t₁ = t₁ ∧ ∃ t₂ ∈ D, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
        (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁ := by
  obtain ⟨hnon, ⟨t', n', f', hf', hmodel'⟩, t₁, ht₁, hα₁, t₂, ht₂, hα₂, ho₁, ho₂, hnc⟩ := h
  have hαφ : ∀ g : T, σ' (e g) = e (α g) := fun g => by
    rw [← hcongr]
    simp [MulAut.congr_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro E hE hcon
    apply hnon (e E) ⟨E, hE, rfl⟩
    rintro _ ⟨g, hg, rfl⟩
    show σ' (e g) = e E * e g * (e E)⁻¹
    rw [hαφ g, hcon g hg, map_mul, map_mul, map_inv]
  · let e₁ : ↥D ≃* ↥(D.map e.toMonoidHom) :=
      Subgroup.equivMapOfInjective D e.toMonoidHom e.injective
    let e₃ : ↥D ⧸ Subgroup.center ↥D ≃* ↥(D.map e.toMonoidHom) ⧸
        Subgroup.center ↥(D.map e.toMonoidHom) :=
      QuotientGroup.congr (Subgroup.center ↥D) (Subgroup.center ↥(D.map e.toMonoidHom)) e₁
        (Subgroup.map_center_eq e₁)
    exact ⟨t', n', f', hf', lieModel_of_mulEquiv e₃.symm hmodel'⟩
  · obtain ⟨u₁, hu₁, rfl⟩ := ht₁
    obtain ⟨u₂, hu₂, rfl⟩ := ht₂
    refine ⟨u₁, hu₁, e.injective ?_, u₂, hu₂, e.injective ?_, ?_, ?_, ?_⟩
    · rw [← hαφ u₁]
      exact hα₁
    · rw [← hαφ u₂]
      exact hα₂
    · obtain ⟨k, hk⟩ := ho₁
      exact ⟨k, by rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hk⟩
    · obtain ⟨k, hk⟩ := ho₂
      exact ⟨k, by rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hk⟩
    · intro hcomm
      apply hnc
      change e u₁ * e u₂ = e u₂ * e u₁
      rw [← map_mul, ← map_mul, hcomm]

theorem threeCompAL_PSp : ThreeCompAL .PSp := by
  intro T _ _ p hp hp5 hrank h2 n f₀ hf₀ hM hLow α hαp hαinn hLR hFix x hxp hx1 hαx D hD hDα
  obtain ⟨hn2, hord⟩ := psp_sector hp hp5 hrank h2 hf₀ hM hLow hαp hαinn hLR hFix
  subst hn2
  obtain ⟨-, K, _, _, _, hK, e, σ, -, hkcard, hcongr⟩ := psp_model hp hp5 hM hf₀ hαp hαinn
  have hord' : orderOf (Nat.card K : ZMod p) = 2 := by rwa [hK]
  have hxp' : (e x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hx1' : e x ≠ 1 := fun h => hx1 (e.injective (by rw [h, map_one]))
  have hσx' : fieldSp 2 K σ (e x) = e x := by
    rw [← hcongr]
    simp [MulAut.congr_apply, hαx]
  have hD' : IsComponentOf (Subgroup.centralizer ({e x} : Set (StatedSp 2 K)))
      (D.map e.toMonoidHom) := by
    have h1 := isComponentOf_map_mulEquiv e hD
    rwa [map_centralizer_singleton_mulEquiv_good e x] at h1
  exact clauseA_of_mulEquiv e α (fieldSp 2 K σ) hcongr
    (psp_clauseA_core hp hp5 hf₀ hK hord' hkcard hxp' hx1' hσx' hD')

end CFSG.RankThree.PartOne.TCX
