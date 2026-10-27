module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CTableSmallAux

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.HdRo7C

lemma basis_smul_ne_of_ne {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin n) (ZMod 3) V) {i j : Fin n} {c d : ZMod 3}
    (hc : c ≠ 0) (hd : d ≠ 0) (h : c • b i = d • b j) : i = j := by
  by_contra hij
  have hrepr := congrArg b.repr h
  simp only [map_smul, Module.Basis.repr_self] at hrepr
  have hi := DFunLike.congr_fun hrepr i
  simp [hij] at hi
  exact hc hi

theorem c2sp_of_monomial_three {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (r : V ≃ₗ[ZMod 3] V)
    (hr0 : r (b 0) = b 0)
    (hmono : ∀ k : Fin (n + 1), ∃ j : Fin (n + 1), ∃ c : ZMod 3,
      c ≠ 0 ∧ r (b k) = c • b j) :
    C2SP 3 b r := by
  classical
  choose j c hc hspec using hmono
  have hcpm : ∀ k, c k = 1 ∨ c k = -1 := fun k => hdRo7CSmallAux_zmod3_ne_zero (hc k)
  have hjinj : Function.Injective j := by
    intro k₁ k₂ hjk
    by_contra hne
    have h1 : b k₁ = c k₁ • r.symm (b (j k₁)) := by
      calc b k₁ = r.symm (r (b k₁)) := by simp
        _ = r.symm (c k₁ • b (j k₁)) := by rw [hspec k₁]
        _ = c k₁ • r.symm (b (j k₁)) := by simp
    have h2 : b k₂ = c k₂ • r.symm (b (j k₂)) := by
      calc b k₂ = r.symm (r (b k₂)) := by simp
        _ = r.symm (c k₂ • b (j k₂)) := by rw [hspec k₂]
        _ = c k₂ • r.symm (b (j k₂)) := by simp
    rw [hjk] at h1
    have hlin : c k₂ • b k₁ = c k₁ • b k₂ := by
      rw [h1, h2, smul_smul, smul_smul, mul_comm (c k₂) (c k₁)]
    exact hne (basis_smul_ne_of_ne b (hc k₂) (hc k₁) hlin)
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.ofBijective j
    ⟨hjinj, Finite.injective_iff_surjective.mp hjinj⟩
  have hσ : ∀ k, σ k = j k := fun k => rfl
  have hσ0 : σ 0 = 0 := by
    rw [hσ]
    have h0 : c 0 • b (j 0) = b 0 := by
      rw [← hspec 0, hr0]
    exact basis_smul_ne_of_ne b (hc 0) (by norm_num : (1 : ZMod 3) ≠ 0) (by
      show c 0 • b (j 0) = (1 : ZMod 3) • b 0
      simpa using h0)
  have hc0 : c 0 = 1 := by
    have hj0 : j 0 = 0 := by rw [← hσ]; exact hσ0
    have h0' : b 0 = c 0 • b (j 0) := by rw [← hr0, hspec 0]
    have h0 : c 0 • b 0 = b 0 := by
      rw [hj0] at h0'
      exact h0'.symm
    have hcoord := congrArg (b.coord 0) h0
    simpa [Module.Basis.coord_apply] using hcoord
  exact ⟨σ, c, hσ0, hc0, hcpm, fun k => by rw [hσ]; exact hspec k⟩

end CFSG.StandardType

end
