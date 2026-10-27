module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Exclusion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J1

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint
  CFSG.Sporadic.Schreier

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem autInner_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : ∀ φ : S ≃* S, ∃ s : S, ∀ x, φ x = s * x * s⁻¹) :
    ∀ φ : S' ≃* S', ∃ s : S', ∀ x, φ x = s * x * s⁻¹ := by
  intro φ
  obtain ⟨s, hs⟩ := h (e.trans (φ.trans e.symm))
  refine ⟨e s, fun x => ?_⟩
  have := hs (e.symm x)
  have h2 : e.symm (φ x) = s * e.symm x * s⁻¹ := by simpa using this
  have h3 := congrArg e h2
  simpa using h3

theorem elemAbelian_le_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {r : ℕ}
    (h : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r) :
    ∀ B : Subgroup S', (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r := by
  intro B hc h2
  have hB := h (B.comap e.toMonoidHom)
    (fun x hx y hy => e.injective (by simpa using hc _ hx _ hy))
    (fun x hx => e.injective (by simpa using h2 _ hx))
  have hcard : Nat.card (B.comap e.toMonoidHom) = Nat.card B := by
    conv_rhs => rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom)
      e.surjective B]
    exact (Subgroup.card_map_of_injective e.injective).symm
  rw [hcard] at hB
  exact hB

theorem false_of_M11
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M11)) : False := by
  obtain ⟨e⟩ := hM
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.M11 := e
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine false_of_autInner_prime h e' m11_autInner (r := 2) m11_elemAbelian_le
    (p := 11) (by norm_num) ?_ ?_
  · show 11 ∣ Nat.card NativeSporadic.M11
    rw [m11_card]
    norm_num
  · rw [orderOf_two_zmod_11]
    norm_num

theorem false_of_J1
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .J1)) : False := by
  obtain ⟨e⟩ := hM
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.J1 := e
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  refine false_of_autInner_prime h e'
    (autInner_of_mulEquiv CFSG.Walter.walterJ1EquivNative walterJ1_autInner) (r := 3)
    (elemAbelian_le_of_mulEquiv CFSG.Walter.walterJ1EquivNative walterJ1_elemAbelian_le)
    (p := 19) (by norm_num) ?_ ?_
  · rw [← Nat.card_congr CFSG.Walter.walterJ1EquivNative.toEquiv,
      CFSG.Walter.J1Props.J1_card]
    norm_num
  · rw [orderOf_two_zmod_19]
    norm_num

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
