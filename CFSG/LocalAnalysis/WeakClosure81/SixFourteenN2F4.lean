module

public import CFSG.Quasithin.Background.Module
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

variable {W : Type*} [CommGroup W] [Finite W]

theorem fixV_eq_bot_of_irreducible {G X : Subgroup (MulAut W)}
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hXne : X ≠ ⊥) :
    fixV X = ⊥ := by
  have hInv : ∀ g ∈ G, ∀ z ∈ fixV X, g z ∈ fixV X := by
    intro g hg z hz
    rw [mem_fixV] at hz ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ X := hXnorm g⁻¹ (G.inv_mem hg) x hx
    have hfix : (g⁻¹ * x * g) z = z := hz _ hx'
    calc x (g z) = (x * g) z := rfl
      _ = (g * (g⁻¹ * x * g)) z := by rw [mul_assoc, mul_inv_cancel_left]
      _ = g ((g⁻¹ * x * g) z) := rfl
      _ = g z := by rw [hfix]
  rcases hirr (fixV X) hInv with hbot | htop
  · exact hbot
  · exfalso
    apply hXne
    refine le_bot_iff.mp (fun x hx => ?_)
    refine MulEquiv.ext fun w => ?_
    have hw : w ∈ fixV X := htop ▸ Subgroup.mem_top w
    rw [mem_fixV] at hw
    exact hw x hx

theorem mulAut_norm_mul_eq_one {x : MulAut W} (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (w : W) :
    x (x w) * x w * w = 1 := by
  have hx3u : ∀ u : W, x (x (x u)) = u := by
    intro u
    simpa [pow_three] using congrArg (fun f : MulAut W => f u) hx3
  have hfixx : ∀ v : W, x v = v → v = 1 := by
    intro v hv
    let K : Subgroup (MulAut W) :=
      { carrier := {y | y v = v}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          show (a * b) v = v
          rw [MulAut.mul_apply, hb, ha]
        inv_mem' := by
          intro a ha
          show a⁻¹ v = v
          have h1 : a (a⁻¹ v) = a v := by rw [MulAut.apply_inv_self, ha]
          exact a.injective h1 }
    have hxK : x ∈ K := hv
    have hle : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.mpr hxK
    have hv' : v ∈ fixV (Subgroup.zpowers x) := by
      rw [mem_fixV]
      exact fun y hy => hle hy
    rw [hfix] at hv'
    exact Subgroup.mem_bot.mp hv'
  let φ : W → W := fun u => x u * u⁻¹
  have hφinj : Function.Injective φ := by
    intro u v h
    have h1 : x (u * v⁻¹) = u * v⁻¹ := by
      have hh : (x u * u⁻¹) * (u * (x v)⁻¹) =
          (x v * v⁻¹) * (u * (x v)⁻¹) := by
        change φ u * (u * (x v)⁻¹) = φ v * (u * (x v)⁻¹)
        rw [h]
      have e1 : (x u * u⁻¹) * (u * (x v)⁻¹) = x u * (x v)⁻¹ := by group
      have e2 : (x v * v⁻¹) * (u * (x v)⁻¹) = u * v⁻¹ := by
        calc (x v * v⁻¹) * (u * (x v)⁻¹)
            = (x v * (x v)⁻¹) * (v⁻¹ * u) := by ac_rfl
          _ = u * v⁻¹ := by rw [mul_inv_cancel, one_mul, mul_comm]
      have h2 : x u * (x v)⁻¹ = u * v⁻¹ := e1.symm.trans (hh.trans e2)
      simpa [map_mul, map_inv] using h2
    have huv : u * v⁻¹ = 1 := hfixx _ h1
    have h' : u * v⁻¹ = v * v⁻¹ := by rw [huv, mul_inv_cancel]
    exact mul_right_cancel h'
  have hφsurj : Function.Surjective φ := Finite.surjective_of_injective hφinj
  obtain ⟨u, rfl⟩ := hφsurj w
  show x (x (x u * u⁻¹)) * x (x u * u⁻¹) * (x u * u⁻¹) = 1
  simp only [map_mul, map_inv]
  rw [hx3u]
  group

end CFSG.LocalAnalysis.WeakClosure81
