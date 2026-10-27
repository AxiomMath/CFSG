module

public import CFSG.Quasithin.Background.JonesParshallOrthogonal
public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.SL2Modules

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem IsOrthModule.exists_eq_sub_of_cocycle (hF : Fintype.card F = 2 ^ (2 * l))
    (hl : 0 < l) {ρ : Representation (ZMod 2) SL(2, F) W} (hρ : IsOrthModule hF ρ)
    {c : SL(2, F) → W} (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) :
    ∃ w : W, ∀ g, c g = ρ g w - w := by
  classical
  obtain ⟨j, β, hβ⟩ := hρ
  set e : SL(2, F) ≃* SL(2, F) := fieldAutEquiv j
  set μ : SL(2, F) →* AddMonoid.End ↥(hermA l F) := hermAct l (sig_sig hF)
  let c' : SL(2, F) → ↥(hermA l F) := fun g => β (c g)
  let c₀ : SL(2, F) → ↥(hermA l F) := fun g => c' (e.symm g)
  have hc' : ∀ g h, c' (g * h) = c' g + μ (fieldAut F j g) (c' h) := by
    intro g h
    change β (c (g * h)) = β (c g) + μ (fieldAut F j g) (β (c h))
    rw [hc g h, map_add, hβ]
  have hc₀ : c₀ ∈ Z1A μ := by
    rw [mem_Z1A]
    intro g h
    have h1 : c₀ (g * h) = c' (e.symm g * e.symm h) := by simp [c₀, map_mul]
    have h2 : c' (e.symm g * e.symm h) =
        c' (e.symm g) + μ (fieldAut F j (e.symm g)) (c' (e.symm h)) := hc' _ _
    have h3 : fieldAut F j (e.symm g) = g := by
      rw [← fieldAutEquiv_apply]
      exact e.apply_symm_apply g
    rw [h1, h2, h3]
  obtain ⟨X, hX⟩ := mem_B1A_herm hF hl hc₀
  have hX' : ∀ g, μ g X - X = c₀ g := fun g => by
    have := congrFun hX g
    rwa [coboundaryA_apply] at this
  let w : W := β.symm X
  have hβw : β w = X := β.apply_symm_apply X
  have hw : ∀ g, ρ g w - w = c g := by
    intro g
    apply β.injective
    rw [map_sub, hβ, hβw, hX' (fieldAut F j g)]
    have h4 : e.symm (fieldAut F j g) = g := by
      rw [← fieldAutEquiv_apply]
      exact e.symm_apply_apply g
    simp [c₀, c', h4]
  exact ⟨w, fun g => (hw g).symm⟩

theorem IsOrthModule.exists_eq_sub_of_cocycle_comp {Γ : Type} [Group Γ]
    (hF : Fintype.card F = 2 ^ (2 * l)) (hl : 0 < l)
    {ρ : Representation (ZMod 2) SL(2, F) W} (hρ : IsOrthModule hF ρ)
    (π : Γ →* SL(2, F)) (hπ : Function.Surjective π)
    {c : Γ → W} (hc : ∀ a b, c (a * b) = c a + ρ (π a) (c b))
    (hker : ∀ a, π a = 1 → c a = 0) :
    ∃ w : W, ∀ a, c a = ρ (π a) w - w := by
  classical
  let σ : SL(2, F) → Γ := Function.surjInv hπ
  have hσ : ∀ g, π (σ g) = g := fun g => Function.surjInv_eq hπ g
  have hdep : ∀ a b, π a = π b → c a = c b := by
    intro a b hab
    have h2 : c b = c (a * (a⁻¹ * b)) := by rw [mul_inv_cancel_left]
    rw [h2, hc a]
    have hker' : c (a⁻¹ * b) = 0 := hker _ (by
      rw [map_mul, map_inv, hab, inv_mul_cancel])
    rw [hker', map_zero, add_zero]
  let c' : SL(2, F) → W := fun g => c (σ g)
  have hc' : ∀ g h, c' (g * h) = c' g + ρ g (c' h) := by
    intro g h
    rw [show c' (g * h) = c (σ g * σ h) from
      hdep (σ (g * h)) (σ g * σ h) (by rw [hσ, map_mul, hσ, hσ])]
    rw [hc (σ g) (σ h), hσ]
  obtain ⟨w, hw⟩ := hρ.exists_eq_sub_of_cocycle hF hl hc'
  refine ⟨w, fun a => ?_⟩
  rw [hdep a (σ (π a)) (by rw [hσ])]
  exact hw (π a)

end CFSG.RankThree.GF2n.Tim81.Sec2

end
