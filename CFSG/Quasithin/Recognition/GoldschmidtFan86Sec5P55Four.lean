module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PSing
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalGcirc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P55

theorem units_inv_unique {p : ℕ} (hp : p = 3 ∨ p = 5) (a b : (ZMod p)ˣ) (ha : a ≠ 1)
    (ha2 : a ^ 2 = 1) (hb : b ≠ 1) (hb2 : b ^ 2 = 1) : a = b := by
  rcases hp with rfl | rfl <;> revert a b <;> decide

theorem z2u (F : FanTree Γ G) {v w : V} (hvw : Γ.Adj v w) {g₁ g₂ : G} (hg₁2 : g₁ * g₁ = 1)
    (hg₂2 : g₂ * g₂ = 1) (hg₁v : g₁ • v = v) (hg₁w : g₁ • w = w) (hg₂v : g₂ • v = v)
    (hg₂w : g₂ • w = w) (hg₁K : g₁ ∉ nbrStab Γ G v) (hg₂K : g₂ ∉ nbrStab Γ G v) :
    g₁ * g₂ ∈ nbrStab Γ G v := by
  obtain ⟨φ, key, -⟩ := F.exists_edge_char hvw
  let e₁ : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G w) :=
    ⟨g₁, MulAction.mem_stabilizer_iff.2 hg₁v, MulAction.mem_stabilizer_iff.2 hg₁w⟩
  let e₂ : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G w) :=
    ⟨g₂, MulAction.mem_stabilizer_iff.2 hg₂v, MulAction.mem_stabilizer_iff.2 hg₂w⟩
  have h1 : φ e₁ ≠ 1 := fun h => hg₁K ((key e₁).2 h)
  have h2 : φ e₂ ≠ 1 := fun h => hg₂K ((key e₂).2 h)
  have hsq : ∀ e : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G w),
      (e : G) * (e : G) = 1 → φ e ^ 2 = 1 := by
    intro e he
    rw [← map_pow, pow_two]
    have : e * e = 1 := Subtype.ext he
    rw [this, map_one]
  have hv35 : valence Γ v = 3 ∨ valence Γ v = 5 := F.valence v
  have heq : φ e₁ = φ e₂ := units_inv_unique hv35 _ _ h1 (hsq e₁ hg₁2) h2 (hsq e₂ hg₂2)
  have hmem : (((e₁⁻¹ * e₂ : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G w)) : G) ∈
      nbrStab Γ G v) := (key _).2 (by rw [map_mul, map_inv, heq, inv_mul_cancel])
  have hinv : g₁⁻¹ = g₁ := inv_eq_of_mul_eq_one_right hg₁2
  simpa [e₁, e₂, hinv] using hmem

section Arc

variable (F : FanTree Γ G) (ℓ : Line Γ)
include F

theorem z2_right {u v : G} {ρ : ℤ} (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hu0 : u • ℓ.vert ρ = ℓ.vert ρ) (hu1 : u • ℓ.vert (ρ - 1) = ℓ.vert (ρ - 1))
    (hu3 : u • ℓ.vert (ρ + 1) ≠ ℓ.vert (ρ + 1)) (hv0 : v • ℓ.vert ρ = ℓ.vert ρ)
    (hv1 : v • ℓ.vert (ρ - 1) = ℓ.vert (ρ - 1)) (hv3 : v • ℓ.vert (ρ + 1) ≠ ℓ.vert (ρ + 1)) :
    (u * v) • ℓ.vert (ρ + 1) = ℓ.vert (ρ + 1) :=
  mem_nbrStab.1 (z2u F (ℓ.adj_pred ρ) hu2 hv2 hu0 hu1 hv0 hv1
    (fun h => hu3 (mem_nbrStab.1 h _ (ℓ.adj ρ))) (fun h => hv3 (mem_nbrStab.1 h _ (ℓ.adj ρ))))
    _ (ℓ.adj ρ)

end Arc

end P55

end CFSG.Quasithin.Fan86
