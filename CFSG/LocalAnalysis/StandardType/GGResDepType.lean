module

public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem l05nL3_det_eq_of_reindex {n : ℕ} {M₀ : CoxeterMatrix (Fin n)}
    {C₀ : Matrix (Fin n) (Fin n) ℤ} (hC₀ : GGIntCartan M₀ C₀)
    (hone : GGAtMostOneMultipleEdge M₀) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Fin n ≃ ι) {C : Matrix ι ι ℤ} (hC : GGIntCartan (M₀.reindex e) C) :
    C.det = C₀.det := by
  rcases hC.eq_or_eq_transpose (hC₀.reindex e) (hone.reindex e) with rfl | h
  · rw [Matrix.det_reindex_self]
  · rw [h, Matrix.det_transpose, Matrix.det_reindex_self]

theorem l05nL3_det_cast_eq_zero {Λ : Type} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
    [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (C : Matrix Λ Λ ℤ)
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hind : ¬ LinearIndependent (ZMod p) h) :
    ((C.det : ℤ) : ZMod p) = 0 := by
  have hdet0 : (Matrix.of fun i j => α i (h j)).det = 0 := by
    by_contra hne
    exact hind (linearIndependent_of_det_ne_zero h α hne)
  have hmap : C.map (fun x : ℤ => (x : ZMod p)) = Matrix.of fun i j => α i (h j) := by
    ext i j
    simp only [Matrix.map_apply]
    exact (hP i j).symm
  rw [Int.cast_det C, hmap]
  exact hdet0

theorem l05nL3_det_of_weyl {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    {C : Matrix ι ι ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) :
    GGIsTypeA M ∨ (GGIsTypeE6 M ∧ C.det = 3) ∨ C.det = 1 ∨ C.det = 2 ∨ C.det = 4 := by
  rcases hM with ⟨n, e, hn, h | ⟨hn2, h⟩ | ⟨hn4, h⟩⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ |
    ⟨e, h⟩
  · exact Or.inl ⟨n, e, hn, h⟩
  · subst h
    have hd : C.det = 2 := by
      rw [l05nL3_det_eq_of_reindex (ggIntCartan_B n) (ggAtMostOneMultipleEdge_B n) e hC,
        CartanMatrix.B_det (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inl hd)))
  · subst h
    have hd : C.det = 4 := by
      rw [l05nL3_det_eq_of_reindex (ggIntCartan_D n) (ggAtMostOneMultipleEdge_D n) e hC,
        CartanMatrix.D_det (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr hd)))
  · subst h
    have hd : C.det = 3 := by
      rw [l05nL3_det_eq_of_reindex ggIntCartan_E₆ ggAtMostOneMultipleEdge_E₆ e hC,
        CartanMatrix.E₆_det]
    exact Or.inr (Or.inl ⟨⟨e, rfl⟩, hd⟩)
  · subst h
    have hd : C.det = 2 := by
      rw [l05nL3_det_eq_of_reindex ggIntCartan_E₇ ggAtMostOneMultipleEdge_E₇ e hC,
        CartanMatrix.E₇_det]
    exact Or.inr (Or.inr (Or.inr (Or.inl hd)))
  · subst h
    have hd : C.det = 1 := by
      rw [l05nL3_det_eq_of_reindex ggIntCartan_E₈ ggAtMostOneMultipleEdge_E₈ e hC,
        CartanMatrix.E₈_det]
    exact Or.inr (Or.inr (Or.inl hd))
  · subst h
    have hd : C.det = 1 := by
      rw [l05nL3_det_eq_of_reindex ggIntCartan_F₄ ggAtMostOneMultipleEdge_F₄ e hC,
        CartanMatrix.F₄_det]
    exact Or.inr (Or.inr (Or.inl hd))
  · subst h
    have hd : C.det = 1 := by
      rw [l05nL3_det_eq_of_reindex ggIntCartan_G₂ ggAtMostOneMultipleEdge_G₂ e hC,
        CartanMatrix.G₂_det]
    exact Or.inr (Or.inr (Or.inl hd))

theorem l05nL3_not_dvd_one_two_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : ℤ}
    (hc : c = 1 ∨ c = 2 ∨ c = 4) : ¬ (p : ℤ) ∣ c := by
  rintro h
  rcases hc with rfl | rfl | rfl
  · exact hp.ne_one (Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 h))
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (Int.natCast_dvd_natCast.1 h))
  · have h4 : p ∣ 4 := Int.natCast_dvd_natCast.1 h
    have h22 : p ∣ 2 * 2 := by norm_num at h4 ⊢; exact h4
    rcases hp.dvd_mul.1 h22 with h2 | h2
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem ggResDepTypeInput_holds : GGResDepTypeInput := by
  intro G _ _ p B Bs x L D J y K hH hpFact hD
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4, h5, h6, h7, h8,
    h9, h10, h11, h12, h13, h14, h15⟩ := hD
  have hdep : ¬ LinearIndependent (ZMod p) fun i : Λ => h (some i) := h10
  have hzero : ((CL.det : ℤ) : ZMod p) = 0 :=
    l05nL3_det_cast_eq_zero (fun i => h (some i)) (fun i => α (some i)) CL h8 hdep
  have hdvd : (p : ℤ) ∣ CL.det := (ZMod.intCast_zmod_eq_zero_iff_dvd CL.det p).1 hzero
  rcases l05nL3_det_of_weyl h1 h2 with hA | ⟨hE6, hdet3⟩ | hdet1 | hdet2 | hdet4
  · exact Or.inr ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4, hA, h6,
      h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  · have hp3 : p = 3 := by
      have h3 : (p : ℤ) ∣ (3 : ℤ) := by rw [← hdet3]; exact hdvd
      exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1
        (Int.natCast_dvd_natCast.1 h3)
    exact Or.inl ⟨hp3, ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4,
      hE6, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩⟩
  · exact absurd hdvd (l05nL3_not_dvd_one_two_four Fact.out hp2 (Or.inl hdet1))
  · exact absurd hdvd (l05nL3_not_dvd_one_two_four Fact.out hp2 (Or.inr (Or.inl hdet2)))
  · exact absurd hdvd (l05nL3_not_dvd_one_two_four Fact.out hp2 (Or.inr (Or.inr hdet4)))

end CFSG.StandardType
