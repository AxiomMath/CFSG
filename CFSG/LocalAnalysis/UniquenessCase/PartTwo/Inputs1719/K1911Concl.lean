module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

@[expose] def TorusFixedConcl (Y : Type) [Group Y] (n p : ℕ) : Prop :=
  ∀ (A : Subgroup Y) (t : Y), IsZModSq ↥A n → (∃ k : ℕ, orderOf t = 2 ^ k) →
      (∀ a ∈ A, t * a * t⁻¹ = a⁻¹) →
    ∀ Q : Subgroup (MulAut Y), IsPGroup 2 Q →
      (∀ b ∈ A ⊔ zpowers t, MulAut.conj b ∈ normalizer (Q : Set (MulAut Y))) →
      ∃ E : Subgroup Y, IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        ∀ α ∈ Q, ∀ e ∈ E, α e = e

theorem TorusFixedConcl.of_mulEquiv {X Y : Type} [Group X] [Group Y] {n p : ℕ} (e : X ≃* Y)
    (h : TorusFixedConcl Y n p) : TorusFixedConcl X n p := by
  intro A t hA ht hinv Q hQ hnorm
  let φ : MulAut X ≃* MulAut Y := MulAut.congr e
  let A' : Subgroup Y := A.map e.toMonoidHom
  let t' : Y := e t
  let Q' : Subgroup (MulAut Y) := Q.map φ.toMonoidHom
  have hA' : IsZModSq ↥A' n := by
    obtain ⟨f⟩ := hA
    exact ⟨(Subgroup.equivMapOfInjective A e.toMonoidHom e.injective).symm.trans f⟩
  have ht' : ∃ k : ℕ, orderOf t' = 2 ^ k := by
    obtain ⟨k, hk⟩ := ht
    exact ⟨k, by
      show orderOf (e.toMonoidHom t) = 2 ^ k
      rw [orderOf_injective e.toMonoidHom e.injective, hk]⟩
  have hinv' : ∀ a ∈ A', t' * a * t'⁻¹ = a⁻¹ := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := (Subgroup.mem_map).1 ha
    change e t * e x * (e t)⁻¹ = (e x)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, hinv x hx, map_inv]
  have hQ' : IsPGroup 2 Q' :=
    hQ.of_equiv (Subgroup.equivMapOfInjective Q φ.toMonoidHom φ.injective)
  have hnorm' : ∀ b ∈ A' ⊔ zpowers t', MulAut.conj b ∈ normalizer (Q' : Set (MulAut Y)) := by
    intro b hb
    have hb' : b ∈ (A ⊔ zpowers t).map e.toMonoidHom := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      exact hb
    obtain ⟨b₀, hb₀, rfl⟩ := (Subgroup.mem_map).1 hb'
    have hb₀norm : MulAut.conj b₀ ∈ normalizer (Q : Set (MulAut X)) := hnorm b₀ hb₀
    have hconj : MulAut.conj (e b₀) = φ (MulAut.conj b₀) := by
      ext y
      simp [φ, MulAut.congr_apply, MulAut.conj_apply]
    change MulAut.conj (e b₀) ∈ normalizer (Q' : Set (MulAut Y))
    rw [hconj]
    have hmap := Subgroup.map_equiv_normalizer_eq Q φ
    exact hmap ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hb₀norm
  obtain ⟨E', hE'el, hE'card, hE'fix⟩ := h A' t' hA' ht' hinv' Q' hQ' hnorm'
  haveI : IsMulCommutative E' := hE'el.1
  refine ⟨E'.comap e.toMonoidHom, ?_, ?_, ?_⟩
  · refine ⟨Subgroup.comap_injective_isMulCommutative E' (f := e.toMonoidHom) e.injective, ?_⟩
    intro x hx
    apply e.injective
    rw [map_pow, map_one]
    exact hE'el.2 (e x) hx
  · rw [Subgroup.comap_equiv_eq_map_symm' e E', ← hE'card]
    exact Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective
  · intro α hα x hx
    have hα' : φ α ∈ Q' := Subgroup.mem_map_of_mem φ.toMonoidHom hα
    have hx' : e.toMonoidHom x ∈ E' := hx
    have hfix := hE'fix (φ α) hα' (e x) hx'
    apply e.injective
    change e (α x) = e x
    simpa [φ, MulAut.congr_apply] using hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
