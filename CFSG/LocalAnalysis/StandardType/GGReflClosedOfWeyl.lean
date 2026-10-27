module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterFaithfulE6Three
public import CFSG.LocalAnalysis.StandardType.GGCoxeterFaithfulTypeA
public import CFSG.LocalAnalysis.StandardType.GGReflClosedFaith
public import CFSG.LocalAnalysis.StandardType.GGReflConjSimpleOfClosed
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem rwm_det {Λ : Type} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (e : Fin N ≃ Λ)
    {M₀ : CoxeterMatrix (Fin N)} {C₀ : Matrix (Fin N) (Fin N) ℤ} (h₀ : GGIntCartan M₀ C₀)
    (hone : GGAtMostOneMultipleEdge M₀) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan (M₀.reindex e) C) :
    C.det = C₀.det := by
  rcases hC.eq_or_eq_transpose (h₀.reindex e) (hone.reindex e) with h | h
  · rw [h, Matrix.det_reindex_self]
  · rw [h, Matrix.det_transpose, Matrix.det_reindex_self]

private theorem rwm_indep {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {p : ℕ}
    [Fact p.Prime] (hdet : ¬ (p : ℤ) ∣ C.det) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (hP : ∀ i j, α i (h j) = (C i j : ZMod p)) :
    LinearIndependent (ZMod p) h := by
  refine linearIndependent_of_det_ne_zero h α ?_
  have hmap : (Matrix.of fun i j => α i (h j)) = C.map fun x : ℤ => (x : ZMod p) := by
    ext i j
    simp [hP]
  rw [hmap, ← Int.cast_det C]
  exact fun h0 => hdet ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0)

private theorem rwm_nd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {c : ℕ} (hc : 0 < c) (hc4 : c ≤ 4)
    (hc3 : p = 3 → c ≠ 3) : ¬ (p : ℤ) ∣ (c : ℤ) := by
  intro hd
  have hd' : p ∣ c := by exact_mod_cast hd
  have hpp : p.Prime := Fact.out
  have h2 := hpp.two_le
  have hp4 : p ≤ 4 := (Nat.le_of_dvd hc hd').trans hc4
  rcases (by omega : p = 3 ∨ p = 4) with rfl | rfl
  · have := hc3 rfl
    omega
  · exact absurd hpp (by decide)

theorem ggReflClosed_of_weylMatrix {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrixFixed M) (h3 : 3 ≤ Fintype.card Λ)
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p)) (s : Λ → V ≃ₗ[ZMod p] V)
    (hs : ∀ i v, s i v = v - α i v • h i) : GGReflClosed s := by
  have hFT := isFiniteType_of_ggIsWeylMatrixFixed hM hC
  have key : ¬ (p : ℤ) ∣ C.det → GGReflClosed s := fun hd =>
    ggReflClosed_of_indep hp hFT hC h α hpair (rwm_indep hd h α hpair) s hs
  rcases hM with ⟨n, e, hn1, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ |
    ⟨e, hE⟩ | ⟨e, hE⟩
  · subst hA
    have hn3 : 3 ≤ n := by rwa [Fintype.card_congr e.symm, Fintype.card_fin] at h3
    by_cases hpn : p ∣ n + 1
    · obtain ⟨f, hf⟩ := ggCoxeterIso_of_typeA_odd e rfl hn3 hp hC h α hpair s hs
      exact ggReflClosed_of_faithful hp hFT hC h α hpair s hs f hf
    · apply key
      rw [rwm_det e (ggIntCartan_A n) (ggAtMostOneMultipleEdge_A n) hC, CartanMatrix.A_det]
      exact fun hd => hpn (by exact_mod_cast hd)
  · subst hB
    apply key
    rw [rwm_det e (ggIntCartan_B n) (ggAtMostOneMultipleEdge_B n) hC,
      CartanMatrix.B_det (by omega)]
    exact rwm_nd hp (c := 2) (by norm_num) (by norm_num) (by norm_num)
  · subst hD
    apply key
    rw [rwm_det e (ggIntCartan_D n) (ggAtMostOneMultipleEdge_D n) hC,
      CartanMatrix.D_det (by omega)]
    exact rwm_nd hp (c := 4) (by norm_num) (by norm_num) (by norm_num)
  · subst hE
    by_cases hp3 : p = 3
    · subst hp3
      obtain ⟨f, hf⟩ := ggCoxeterIso_of_E6_three_reindex e rfl hC h α hpair s hs
      exact ggReflClosed_of_faithful hp hFT hC h α hpair s hs f hf
    · apply key
      rw [rwm_det e ggIntCartan_E₆ ggAtMostOneMultipleEdge_E₆ hC, CartanMatrix.E₆_det]
      exact rwm_nd hp (c := 3) (by norm_num) (by norm_num) fun h => absurd h hp3
  · subst hE
    apply key
    rw [rwm_det e ggIntCartan_E₇ ggAtMostOneMultipleEdge_E₇ hC, CartanMatrix.E₇_det]
    exact rwm_nd hp (c := 2) (by norm_num) (by norm_num) (by norm_num)
  · subst hE
    apply key
    rw [rwm_det e ggIntCartan_E₈ ggAtMostOneMultipleEdge_E₈ hC, CartanMatrix.E₈_det]
    exact rwm_nd hp (c := 1) (by norm_num) (by norm_num) (by norm_num)
  · subst hE
    apply key
    rw [rwm_det e ggIntCartan_F₄ ggAtMostOneMultipleEdge_F₄ hC, CartanMatrix.F₄_det]
    exact rwm_nd hp (c := 1) (by norm_num) (by norm_num) (by norm_num)
  · subst hE
    apply key
    rw [rwm_det e ggIntCartan_G₂ ggAtMostOneMultipleEdge_G₂ hC, CartanMatrix.G₂_det]
    exact rwm_nd hp (c := 1) (by norm_num) (by norm_num) (by norm_num)

theorem ggReflConjSimple_of_weylMatrix {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {G : Type} [Group G]
    [Finite G] {Bs L : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrixFixed M) (h3 : 3 ≤ Fintype.card Λ) {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    GGReflConjSimple p (ggAutomizer L Bs) φ :=
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  ggReflConjSimple_of_reflClosed ι φ hAL
    (ggReflClosed_of_weylMatrix hp hM h3 hC h α hpair _ hφ)

end CFSG.StandardType

end
