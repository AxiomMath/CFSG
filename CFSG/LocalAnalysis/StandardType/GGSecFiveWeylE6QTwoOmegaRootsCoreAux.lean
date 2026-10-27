module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRoots

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

theorem rootRefl_noComm (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {K : Subgroup (V ≃ₗ[ZMod 3] V)} {x y : V} (hx : B x x = 1)
    (hyx : ∀ a : ZMod 3, y ≠ a • x)
    (h12 : 12 ≤ Set.ncard {v : V | B v v = 2 ∧ B v x = 0 ∧ B v y = 0})
    (hK : ∀ (v : V) (hv : B v v = 2), B v x = 0 → B v y = 0 →
      rootRefl (B := B) v hv ∈ K)
    {ψ : V ≃ₗ[ZMod 3] V} (hψ : ψ ∈ e6Weyl hα)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * (ψ * b * ψ⁻¹) = ψ * b * ψ⁻¹ * a) : False := by
  classical
  let Φ : Set V := {v : V | B v v = 2 ∧ B v x = 0 ∧ B v y = 0}
  obtain ⟨hΦ12, hperp, hthird, -⟩ := phiD_facts hP hV hB hα hx hyx h12
  have hψiso : ∀ a b : V, B (ψ a) (ψ b) = B a b := fun a b =>
    bilinForm_apply_e6Weyl hP hV hB hα hψ a b
  have hdisj : ∀ (v v' : V) (hv : B v v = 2) (hvx : B v x = 0) (hvy : B v y = 0)
      (hv' : B v' v' = 2) (hv'x : B v' x = 0) (hv'y : B v' y = 0),
      B v' (ψ v) = 0 ∨ ψ v = v' ∨ ψ v = -v' := by
    intro v v' hv hvx hvy hv' hv'x hv'y
    have hKv' : rootRefl (B := B) v' hv' ∈ K := hK v' hv' hv'x hv'y
    have hKv : rootRefl (B := B) v hv ∈ K := hK v hv hvx hvy
    have hconj := rootRefl_conj_iso (B := B) (g := ψ) hψiso hv
    have hcomm' := hcomm (rootRefl (B := B) v' hv') hKv'
      (rootRefl (B := B) v hv) hKv
    rw [hconj] at hcomm'
    exact rootRefl_commute hP hV hB hα hv' (by rw [hψiso, hv]) hcomm'
  have horth : ∀ (v v' : V) (hv : B v v = 2) (hvx : B v x = 0) (hvy : B v y = 0)
      (hv' : B v' v' = 2) (hv'x : B v' x = 0) (hv'y : B v' y = 0),
      B v' (ψ v) = 0 := by
    intro v v' hv hvx hvy hv' hv'x hv'y
    rcases hdisj v v' hv hvx hvy hv' hv'x hv'y with h0 | h1 | h1
    · exact h0
    · obtain ⟨w, hw, hwx, hwy, hwv', hwnv', hBvw⟩ := hthird v' hv' hv'x hv'y
      have hsymm : B w v' ≠ 0 := by
        rwa [bilinForm_symm hP hV hB]
      rcases hdisj v w hv hvx hvy hw hwx hwy with h0w | h1w | h1w
      · rw [h1] at h0w
        exact absurd h0w hsymm
      · exact absurd (h1w.symm.trans h1) hwv'
      · have hv'eq : v' = -w := h1.symm.trans h1w
        exact absurd (by rw [hv'eq]; simp) hwnv'
    · obtain ⟨w, hw, hwx, hwy, hwv', hwnv', hBvw⟩ := hthird v' hv' hv'x hv'y
      have hsymm : B w v' ≠ 0 := by
        rwa [bilinForm_symm hP hV hB]
      rcases hdisj v w hv hvx hvy hw hwx hwy with h0w | h1w | h1w
      · rw [h1, LinearMap.BilinForm.neg_right] at h0w
        exact absurd (neg_eq_zero.mp h0w) hsymm
      · have : w = -v' := by
          rw [← h1, h1w]
        exact absurd this hwnv'
      · have : w = v' := (neg_inj.mp (h1.symm.trans h1w)).symm
        exact absurd this hwv'
  let D : Set V := {u : V | ∃ a b : ZMod 3, u = a • x + b • y}
  have h0D : (0 : V) ∈ D := ⟨0, 0, by simp⟩
  have hDcard : D.ncard ≤ 9 := by
    let g : ZMod 3 × ZMod 3 → V := fun p => p.1 • x + p.2 • y
    have hDeq : D = g '' Set.univ := by
      ext u
      constructor
      · rintro ⟨a, b, rfl⟩
        exact ⟨(a, b), trivial, rfl⟩
      · rintro ⟨p, -, rfl⟩
        exact ⟨p.1, p.2, rfl⟩
    rw [hDeq]
    calc (g '' Set.univ).ncard ≤ (Set.univ : Set (ZMod 3 × ZMod 3)).ncard :=
          Set.ncard_image_le (Set.toFinite Set.univ)
      _ = Nat.card (ZMod 3 × ZMod 3) := Set.ncard_univ _
      _ = 9 := by rw [Nat.card_prod, Nat.card_zmod]
  have hDdiff : (D \ {0}).ncard = D.ncard - 1 := Set.ncard_diff_singleton_of_mem h0D
  have hψsub : ψ '' Φ ⊆ D \ {0} := by
    rintro z ⟨v, hvΦ, rfl⟩
    have hD : ∃ a b : ZMod 3, ψ v = a • x + b • y :=
      hperp (ψ v) (fun v' hv' hv'x hv'y =>
        horth v v' hvΦ.1 hvΦ.2.1 hvΦ.2.2 hv' hv'x hv'y)
    refine ⟨hD, ?_⟩
    rintro hz
    apply root_ne_zero hvΦ.1
    apply ψ.injective
    rw [hz, map_zero]
  have hψcard : (ψ '' Φ).ncard = 12 := by
    rw [Set.ncard_image_of_injective Φ ψ.injective, hΦ12]
  have : 12 ≤ (D \ {0}).ncard := by
    rw [← hψcard]
    exact Set.ncard_mono hψsub
  rw [hDdiff] at this
  omega

end CFSG.StandardType.E6QTwo

end
