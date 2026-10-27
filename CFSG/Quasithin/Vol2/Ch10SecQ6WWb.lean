module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WWa

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open CFSG.Quasithin

theorem fix_stab : ∀ u : L3.Vec,
    (∀ γ : L3.Γ, L3.act γ ![1, 0, 0] = ![1, 0, 0] → L3.act γ u = u) → u = 0 ∨ u = ![1, 0, 0] := by
  unfold L3.act
  decide +kernel

variable {W W₁ : Type*} [CommGroup W] [CommGroup W₁]

@[expose] def L3Emb (Λ : Subgroup (MulAut W)) (j : W₁ →* W) (b : W₁ → L3.Vec) : Prop :=
  Function.Injective j ∧ (∀ w w', b (w * w') = b w + b w') ∧ Function.Bijective b ∧
    ∀ γ : L3.Γ, ∃ x ∈ Λ, ∀ w w', b w' = L3.act γ (b w) → x (j w) = j w'

theorem eq_one_of_L3Emb {Λ : Subgroup (MulAut W)} {j : W₁ →* W} {b : W₁ → L3.Vec}
    (hj : L3Emb Λ j b) {w : W₁} (hw : b w = 0) : w = 1 := by
  obtain ⟨-, hbadd, hbij, -⟩ := hj
  have h := hbadd 1 1
  rw [mul_one] at h
  exact hbij.1 (hw.trans (add_eq_left.mp h.symm).symm)

theorem mem_of_L3Emb {Λ : Subgroup (MulAut W)} {j : W₁ →* W} {b : W₁ → L3.Vec}
    (hj : L3Emb Λ j b) {X : Subgroup W} (hX : ∀ x ∈ Λ, ∀ w ∈ X, x w ∈ X) {w : W₁}
    (hw : j w ∈ X) (hw1 : w ≠ 1) (w' : W₁) : j w' ∈ X := by
  by_cases hw'0 : b w' = 0
  · rw [eq_one_of_L3Emb hj hw'0, map_one]
    exact X.one_mem
  · obtain ⟨γ, hγ⟩ := L3.act_trans (b w) (b w') (fun h => hw1 (eq_one_of_L3Emb hj h)) hw'0
    obtain ⟨x, hxΛ, hx⟩ := hj.2.2.2 γ
    rw [← hx w w' hγ.symm]
    exact hX x hxΛ _ hw

theorem eq_on_of_L3Emb {Λ : Subgroup (MulAut W)} {j : W₁ →* W} {b : W₁ → L3.Vec}
    (hj : L3Emb Λ j b) {f g : W →* W} (hfΛ : ∀ x ∈ Λ, ∀ w, f (x w) = x (f w))
    (hgΛ : ∀ x ∈ Λ, ∀ w, g (x w) = x (g w)) (hf : ∀ w, f (j w) = 1 → w = 1)
    (hg : ∀ w, g (j w) = 1 → w = 1) (hfg : ∀ w, ∃ w', g (j w) = f (j w')) (w : W₁) :
    f (j w) = g (j w) := by
  have hfinj : ∀ w w', f (j w) = f (j w') → w = w' := fun w w' h => by
    have h1 : f (j (w * w'⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_inv, map_inv, h, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hf _ h1)
  obtain ⟨w₀, hw₀⟩ := hj.2.2.1.2 ![1, 0, 0]
  obtain ⟨w', hw'⟩ := hfg w₀
  have hfix : ∀ γ : L3.Γ, L3.act γ ![1, 0, 0] = ![1, 0, 0] → L3.act γ (b w') = b w' := by
    intro γ hγ
    obtain ⟨x, hxΛ, hx⟩ := hj.2.2.2 γ
    obtain ⟨w'', hw''⟩ := hj.2.2.1.2 (L3.act γ (b w'))
    have h1 : x (j w₀) = j w₀ := hx w₀ w₀ (by rw [hw₀, hγ])
    have h2 : x (j w') = j w'' := hx w' w'' hw''
    have h3 : f (j w'') = f (j w') := by
      rw [← h2, hfΛ x hxΛ, ← hw', ← hgΛ x hxΛ, h1]
    rw [← hw'', hfinj _ _ h3]
  rcases fix_stab (b w') hfix with h0 | he
  · exfalso
    have h1 := eq_one_of_L3Emb hj h0
    rw [h1, map_one, map_one] at hw'
    have h2 := hg w₀ hw'
    rw [h2] at hw₀
    have h4 := hj.2.1 1 1
    rw [mul_one, hw₀] at h4
    exact absurd h4 (by decide)
  · rw [hj.2.2.1.1 (he.trans hw₀.symm)] at hw'
    by_cases hw0 : b w = 0
    · rw [eq_one_of_L3Emb hj hw0, map_one, map_one, map_one]
    · obtain ⟨γ, hγ⟩ := L3.act_trans ![1, 0, 0] (b w) (by decide) hw0
      obtain ⟨x, hxΛ, hx⟩ := hj.2.2.2 γ
      have h1 : x (j w₀) = j w := hx w₀ w (by rw [hw₀, hγ])
      rw [← h1, hfΛ x hxΛ, hgΛ x hxΛ, hw']

theorem card_of_L3Emb {Λ : Subgroup (MulAut W)} {j : W₁ →* W} {b : W₁ → L3.Vec}
    (hj : L3Emb Λ j b) : Nat.card W₁ = 8 := by
  rw [Nat.card_eq_of_bijective b hj.2.2.1]
  simp [Nat.card_eq_fintype_card, ZMod.card]

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
