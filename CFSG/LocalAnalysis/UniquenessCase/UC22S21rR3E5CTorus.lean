module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CTorusA
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Blueprint CFSG.LieType.Ree Subgroup

theorem uc22r3e5c_sylowMap {S M : Type*} [Group S] [Group M] [Finite S] [Finite M]
    (e : S ≃* M) (U : Sylow 2 S) :
    ∃ U' : Sylow 2 M, (U' : Subgroup M) = (U : Subgroup S).map e.toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardS : Nat.card S = Nat.card M := Nat.card_congr e.toEquiv
  exact ⟨Sylow.ofCard ((U : Subgroup S).map e.toMonoidHom) (by
    rw [Subgroup.card_map_of_injective e.injective, Sylow.card_eq_multiplicity, hcardS]),
    rfl⟩

private theorem uc22r3e5c_transport_stable {S M : Type*} [Group S] [Group M]
    (ε : S ≃* M) {α : MulAut S} {β : MulAut M} (hβ : ∀ x : S, β (ε x) = ε (α x))
    {H : Subgroup S} (hH : H.map α.toMonoidHom = H) :
    (H.map ε.toMonoidHom).map β.toMonoidHom = H.map ε.toMonoidHom := by
  have hcomp : β.toMonoidHom.comp ε.toMonoidHom = ε.toMonoidHom.comp α.toMonoidHom := by
    refine MonoidHom.ext fun x => ?_
    exact hβ x
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hH]

private theorem uc22r3e5c_transport_le_normalizer {S M : Type*} [Group S] [Group M]
    (ε : S ≃* M) {U C : Subgroup S} {U' : Subgroup M} (hU' : U' = U.map ε.toMonoidHom)
    (hC : C ≤ Subgroup.normalizer (U : Set S)) :
    C.map ε.toMonoidHom ≤ Subgroup.normalizer (U' : Set M) := by
  have h1 : C.map ε.toMonoidHom ≤
      (Subgroup.normalizer (U : Set S)).map ε.toMonoidHom := Subgroup.map_mono hC
  rw [Subgroup.map_equiv_normalizer_eq, ← hU'] at h1
  exact h1

private theorem uc22r3e5c_transport_pow {S M : Type*} [Group S] [Group M]
    (ε : S ≃* M) {α : MulAut S} {β : MulAut M} (hβ : ∀ x : S, β (ε x) = ε (α x))
    {C : Subgroup S} {e : ℕ} (he : ∀ c ∈ C, α c = c ^ e) :
    ∀ y ∈ C.map ε.toMonoidHom, β y = y ^ e := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hy
  change β (ε c) = (ε c) ^ e
  rw [hβ c, he c hc, map_pow]

private theorem uc22r3e5c_transport_conclusion {S M : Type*} [Group S] [Group M]
    (ε : S ≃* M) {α : MulAut S} {β : MulAut M} (hβ : ∀ x : S, β (ε x) = ε (α x))
    {C : Subgroup S} {e : ℕ} (h : ∀ y ∈ C.map ε.toMonoidHom, β y = y ^ e) :
    ∀ c ∈ C, α c = c ^ e := by
  intro c hc
  have hy : ε c ∈ C.map ε.toMonoidHom := Subgroup.mem_map.2 ⟨c, hc, rfl⟩
  have h1 := h (ε c) hy
  rw [hβ c, ← map_pow] at h1
  exact ε.injective h1

theorem uc22r3e5c_torusExp_eq {S : Type} [Group S] [Finite S]
    {m : ℕ} (hSz : IsSz S m) (α : MulAut S) (U₁ U₂ : Sylow 2 S) (C₁ C₂ : Subgroup S)
    (hC₁ : C₁ ≤ Subgroup.normalizer ((U₁ : Subgroup S) : Set S))
    (hC₂ : C₂ ≤ Subgroup.normalizer ((U₂ : Subgroup S) : Set S))
    (hcard₁ : Nat.card C₁ = 2 ^ m - 1) (hcard₂ : Nat.card C₂ = 2 ^ m - 1)
    (hαU₁ : (U₁ : Subgroup S).map α.toMonoidHom = (U₁ : Subgroup S))
    (hαC₁ : C₁.map α.toMonoidHom = C₁)
    (hαU₂ : (U₂ : Subgroup S).map α.toMonoidHom = (U₂ : Subgroup S))
    (hαC₂ : C₂.map α.toMonoidHom = C₂)
    {e : ℕ} (he : ∀ c ∈ C₁, α c = c ^ e) :
    ∀ c ∈ C₂, α c = c ^ e := by
  obtain ⟨-, -, a, ha, K, _, _, hn, hcard, ⟨ε⟩⟩ := LieModel.suzukiModel hSz
  subst hn
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hcard
  let α' : MulAut (suzukiGroup a K) := ε.symm.trans (α.trans ε)
  have hα' : ∀ x : S, α' (ε x) = ε (α x) := by
    intro x
    simp only [α', MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  obtain ⟨U₁', hU₁'⟩ := uc22r3e5c_sylowMap ε U₁
  obtain ⟨U₂', hU₂'⟩ := uc22r3e5c_sylowMap ε U₂
  have hmodel := uc22r3e5c_torusExp_eq_suzuki ha hK α' U₁' U₂'
    (C₁.map ε.toMonoidHom) (C₂.map ε.toMonoidHom)
    (uc22r3e5c_transport_le_normalizer ε hU₁' hC₁)
    (uc22r3e5c_transport_le_normalizer ε hU₂' hC₂)
    (by rw [Subgroup.card_map_of_injective ε.injective, hcard₁])
    (by rw [Subgroup.card_map_of_injective ε.injective, hcard₂])
    (by rw [hU₁']; exact uc22r3e5c_transport_stable ε hα' hαU₁)
    (uc22r3e5c_transport_stable ε hα' hαC₁)
    (by rw [hU₂']; exact uc22r3e5c_transport_stable ε hα' hαU₂)
    (uc22r3e5c_transport_stable ε hα' hαC₂)
    (uc22r3e5c_transport_pow ε hα' he)
  exact uc22r3e5c_transport_conclusion ε hα' hmodel

end CFSG.LocalAnalysis.UniquenessCase.UC22
