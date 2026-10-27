module

public import CFSG.RankThree.PartTwo.Sec18.Item189ListBasic
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem map_pCoreOf_of_map_eq189 {Y : Type} [Group Y] (α : MulAut Y) {N : Subgroup Y}
    (hN : N.map α.toMonoidHom = N) :
    (CFSG.Open.pCoreOf 2 N).map α.toMonoidHom = CFSG.Open.pCoreOf 2 N := by
  let e : ↥N ≃* ↥N := (MulEquiv.subgroupMap (α : Y ≃* Y) N).trans (MulEquiv.subgroupCongr hN)
  have hcomp : α.toMonoidHom.comp N.subtype = N.subtype.comp e.toMonoidHom := by
    ext n
    rfl
  rw [CFSG.openPCoreOf_eq_map_pCore, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    CFSG.pCore_map_iso 2 e]

theorem pCoreOf_subgroupOf189 {Y : Type} [Group Y] {X K : Subgroup Y} (hKX : K ≤ X) :
    CFSG.Open.pCoreOf 2 (K.subgroupOf X) = (CFSG.Open.pCoreOf 2 K).subgroupOf X := by
  let ψ : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
  have hcomp : K.subtype.comp ψ.toMonoidHom = X.subtype.comp (K.subgroupOf X).subtype := by
    ext z
    rfl
  have hsub : ∀ H : Subgroup ↥X, (H.map X.subtype).subgroupOf X = H := fun H =>
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective H
  rw [CFSG.openPCoreOf_eq_map_pCore, CFSG.openPCoreOf_eq_map_pCore, ← CFSG.pCore_map_iso 2 ψ,
    Subgroup.map_map, hcomp, ← Subgroup.map_map, hsub]

namespace ListData189

variable {Y : Type} [Group Y] {X Q : Subgroup Y} {Γ : Subgroup (MulAut Y)} {x : Y}

theorem pCoreOf_normalizer_le [Finite Y] (h : ListData189 X Q Γ x) :
    CFSG.Open.pCoreOf 2 (Subgroup.normalizer ((Q ⊓ X : Subgroup Y) : Set Y) ⊓ X) ≤ Q ⊓ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h.normal
  set R : Subgroup Y := Q ⊓ X with hR
  set N : Subgroup Y := Subgroup.normalizer (R : Set Y) ⊓ X with hN
  have hRmap : ∀ α : MulAut Y, (∀ t ∈ R, α t ∈ R) → (∀ t ∈ R, α⁻¹ t ∈ R) →
      R.map α.toMonoidHom = R := by
    intro α h1 h2
    apply le_antisymm
    · rintro _ ⟨s, hs, rfl⟩
      exact h1 s hs
    · intro t ht
      exact ⟨α⁻¹ t, h2 t ht, by simp⟩
  have hNmap : ∀ α : MulAut Y, (∀ t ∈ R, α t ∈ R) → (∀ t ∈ R, α⁻¹ t ∈ R) →
      N.map α.toMonoidHom = N := by
    intro α h1 h2
    have e1 := hRmap α h1 h2
    have e2 := hRmap α⁻¹ h2 (by simpa using h1)
    apply le_antisymm
    · rintro _ ⟨n, ⟨hnN, hnX⟩, rfl⟩
      refine ⟨?_, h.apply_mem α hnX⟩
      have := mem_normalizer_map α hnN
      rwa [e1] at this
    · intro t ht
      refine ⟨α⁻¹ t, ⟨?_, h.apply_mem α⁻¹ ht.2⟩, by simp⟩
      have := mem_normalizer_map α⁻¹ ht.1
      rwa [e2] at this
  set O : Subgroup Y := CFSG.Open.pCoreOf 2 N with hO
  have hO2 : IsPGroup 2 O := by
    rw [hO, CFSG.openPCoreOf_eq_map_pCore]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥N)).map N.subtype
  have hOX : O ≤ X := (CFSG.openPCoreOf_le 2 N).trans inf_le_right
  have hconj : ∀ s ∈ Q, ∀ t ∈ R, (MulAut.conj s) t ∈ R := fun s hs t ht =>
    ⟨by simpa [MulAut.conj_apply] using Q.mul_mem (Q.mul_mem hs ht.1) (Q.inv_mem hs),
      by simpa [MulAut.conj_apply] using h.normal.conj_mem t ht.2 s⟩
  have hQN : Q ≤ Subgroup.normalizer (O : Set Y) := by
    intro σ hσ
    apply mem_normalizer_of_map_conj
    refine map_pCoreOf_of_map_eq189 (MulAut.conj σ) (hNmap (MulAut.conj σ) (hconj σ hσ) ?_)
    rw [← map_inv MulAut.conj σ]
    exact hconj σ⁻¹ (Q.inv_mem hσ)
  have hOΓ : GammaInv189 Γ O := by
    intro γ hγ t ht
    have hγ1 : ∀ t ∈ R, γ t ∈ R := h.gammaInv_inf γ hγ
    have hγ2 : ∀ t ∈ R, γ⁻¹ t ∈ R := h.gammaInv_inf γ⁻¹ (Γ.inv_mem hγ)
    have h1 := map_pCoreOf_of_map_eq189 γ (hNmap γ hγ1 hγ2)
    have h2 : γ t ∈ O.map γ.toMonoidHom := ⟨t, ht, rfl⟩
    rwa [h1] at h2
  exact le_inf (h.le_of_normalizes hO2 hQN hOΓ) hOX

end ListData189

end CFSG.RankThree.PartTwo.Sec18
