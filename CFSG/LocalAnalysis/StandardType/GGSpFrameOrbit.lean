module

public import CFSG.LocalAnalysis.StandardType.GGSpFrameIso
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSingleSupport
public import CFSG.LocalAnalysis.StandardType.GGSpJoinOrbitBound

public section

namespace CFSG.StandardType.SpFrame

open CFSG.StandardType CFSG.StandardType.SpJoin CFSG.Open

theorem coord_eq_one_of_fixed {G : Type} [Group G] [Finite G] {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 3 ≤ m) {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B (m + 1)) A)
    (Φ : (Fin (m + 1) → Multiplicative (ZMod p)) ≃* ↥Bs)
    (hΦ : ∀ h ∈ spSignedGroup (m + 1) p, ∃ ψ ∈ A, ∀ a, ψ (Φ a) = Φ (h a))
    {H : Subgroup (MulAut ↥Bs)} (hHA : H ≤ A) {z : G} (hz : z ∈ Bs)
    (hfix : ∀ ψ ∈ H, ((ψ ⟨z, hz⟩ : ↥Bs) : G) = z) (hH : 2 ^ m * m.factorial ≤ Nat.card H)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    (Φ.symm ⟨z, hz⟩) i = 1 ∨ (Φ.symm ⟨z, hz⟩) j = 1 := by
  classical
  let v : Fin (m + 1) → Multiplicative (ZMod p) := Φ.symm ⟨z, hz⟩
  have hv : Φ v = ⟨z, hz⟩ := Φ.apply_symm_apply ⟨z, hz⟩
  let S : Set G := {w : G | ∃ ψ ∈ A, ((ψ ⟨z, hz⟩ : ↥Bs) : G) = w}
  have hS : S.ncard ≤ 2 * m + 2 := ncard_automizer_orbit_le (n := m) hA hHA hz hfix hH
  have hS' : S.ncard ≤ 2 * (m + 1) + 2 := by omega
  let tor : (Fin (m + 1) → Multiplicative (ZMod p)) →* G := Bs.subtype.comp Φ.toMonoidHom
  have htor : Function.Injective tor := Subtype.val_injective.comp Φ.injective
  have hmem : ∀ h ∈ spSignedGroup (m + 1) p, tor (h v) * 1 ∈ S := by
    intro h hh
    obtain ⟨ψ, hψ, hψval⟩ := hΦ h hh
    refine ⟨ψ, hψ, ?_⟩
    have h1 : ψ ⟨z, hz⟩ = Φ (h v) := by
      rw [← hv]
      exact hψval v
    show ((ψ ⟨z, hz⟩ : ↥Bs) : G) = tor (h v) * 1
    rw [h1, mul_one]
    rfl
  exact coord_eq_one_of_ncard_le hp hp2 (by omega : 4 ≤ m + 1) (tor := tor) htor 1 v S hS' hmem hij

end CFSG.StandardType.SpFrame
