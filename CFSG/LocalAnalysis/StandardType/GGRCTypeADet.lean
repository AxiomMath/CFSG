module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggRC_det_cast_eq_zero_of_common_kernel_of_finrank_eq_card {p : ℕ} [Fact p.Prime]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hαh : ∀ i j, α i (h j) = (C i j : ZMod p))
    {z : V} (hz : z ≠ 0) (hzα : ∀ i, α i z = 0)
    (hdim : Module.finrank (ZMod p) V = Fintype.card Λ) :
    ((C.det : ℤ) : ZMod p) = 0 := by
  classical
  let f : (Λ → ZMod p) →ₗ[ZMod p] V := Fintype.linearCombination (ZMod p) h
  let a : V →ₗ[ZMod p] (Λ → ZMod p) := LinearMap.pi α
  have hcomp : a.comp f = (C.map (Int.castRingHom (ZMod p))).mulVecLin := by
    refine LinearMap.pi_ext fun j r => ?_
    funext i
    simp [f, a, hαh, Matrix.mulVec_single]
    exact mul_comm _ _
  have hzker : a z = 0 := by
    funext i
    exact hzα i
  by_contra hdet
  have hdetMap : (C.map (Int.castRingHom (ZMod p))).det ≠ 0 := by
    change ((Int.castRingHom (ZMod p)).mapMatrix C).det ≠ 0
    rw [← RingHom.map_det]
    exact hdet
  have hfull := Matrix.rank_of_det_ne_zero hdetMap
  have hrange : Module.finrank (ZMod p) (a.comp f).range = Fintype.card Λ := by
    have h1 : Module.finrank (ZMod p) (a.comp f).range =
        Matrix.rank (C.map (Int.castRingHom (ZMod p))) := by
      rw [hcomp]
      rfl
    rw [h1]
    exact hfull
  have hle : Module.finrank (ZMod p) (a.comp f).range ≤
      Module.finrank (ZMod p) a.range :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range f a)
  have hcodim : Module.finrank (ZMod p) (Λ → ZMod p) = Fintype.card Λ := by simp
  have hleTop : Module.finrank (ZMod p) a.range ≤ Fintype.card Λ := by
    simpa [hcodim] using Submodule.finrank_le a.range
  have htop : Module.finrank (ZMod p) a.range = Fintype.card Λ := by omega
  have hrangeTop : a.range = ⊤ := by
    exact Submodule.eq_top_of_finrank_eq (by simpa [finrank_top, hcodim] using htop)
  have hfinrank : Module.finrank (ZMod p) V =
      Module.finrank (ZMod p) (Λ → ZMod p) := by
    rw [hdim, hcodim]
  have hinj : Function.Injective a :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := a) hfinrank).mpr
      (LinearMap.range_eq_top.mp hrangeTop)
  have hz0 : a z = a 0 := by simpa using hzker
  exact hz (hinj hz0)

private theorem l05nC2d_det_eq_of_reindex {n : ℕ} {M₀ : CoxeterMatrix (Fin n)}
    {C₀ : Matrix (Fin n) (Fin n) ℤ} (hC₀ : GGIntCartan M₀ C₀)
    (hone : GGAtMostOneMultipleEdge M₀) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Fin n ≃ ι) {C : Matrix ι ι ℤ} (hC : GGIntCartan (M₀.reindex e) C) :
    C.det = C₀.det := by
  rcases hC.eq_or_eq_transpose (hC₀.reindex e) (hone.reindex e) with rfl | h
  · rw [Matrix.det_reindex_self]
  · rw [h, Matrix.det_transpose, Matrix.det_reindex_self]

private theorem l05nC2d_det_of_weyl {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    {C : Matrix ι ι ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) :
    GGIsTypeA M ∨ (GGIsTypeE6 M ∧ C.det = 3) ∨ C.det = 1 ∨ C.det = 2 ∨ C.det = 4 := by
  rcases hM with ⟨n, e, hn, h | ⟨hn2, h⟩ | ⟨hn4, h⟩⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ |
    ⟨e, h⟩
  · exact Or.inl ⟨n, e, hn, h⟩
  · subst h
    have hd : C.det = 2 := by
      rw [l05nC2d_det_eq_of_reindex (ggIntCartan_B n) (ggAtMostOneMultipleEdge_B n) e hC,
        CartanMatrix.B_det (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inl hd)))
  · subst h
    have hd : C.det = 4 := by
      rw [l05nC2d_det_eq_of_reindex (ggIntCartan_D n) (ggAtMostOneMultipleEdge_D n) e hC,
        CartanMatrix.D_det (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr hd)))
  · subst h
    have hd : C.det = 3 := by
      rw [l05nC2d_det_eq_of_reindex ggIntCartan_E₆ ggAtMostOneMultipleEdge_E₆ e hC,
        CartanMatrix.E₆_det]
    exact Or.inr (Or.inl ⟨⟨e, rfl⟩, hd⟩)
  · subst h
    have hd : C.det = 2 := by
      rw [l05nC2d_det_eq_of_reindex ggIntCartan_E₇ ggAtMostOneMultipleEdge_E₇ e hC,
        CartanMatrix.E₇_det]
    exact Or.inr (Or.inr (Or.inr (Or.inl hd)))
  · subst h
    have hd : C.det = 1 := by
      rw [l05nC2d_det_eq_of_reindex ggIntCartan_E₈ ggAtMostOneMultipleEdge_E₈ e hC,
        CartanMatrix.E₈_det]
    exact Or.inr (Or.inr (Or.inl hd))
  · subst h
    have hd : C.det = 1 := by
      rw [l05nC2d_det_eq_of_reindex ggIntCartan_F₄ ggAtMostOneMultipleEdge_F₄ e hC,
        CartanMatrix.F₄_det]
    exact Or.inr (Or.inr (Or.inl hd))
  · subst h
    have hd : C.det = 1 := by
      rw [l05nC2d_det_eq_of_reindex ggIntCartan_G₂ ggAtMostOneMultipleEdge_G₂ e hC,
        CartanMatrix.G₂_det]
    exact Or.inr (Or.inr (Or.inl hd))

private theorem l05nC2d_not_dvd_one_two_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : ℤ}
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

theorem ggRC_det_cast_eq_zero_of_kernel {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {V : Type} [AddCommGroup V] [Module (ZMod p) V] (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (C : Matrix Λ Λ ℤ)
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p))
    (w : V) (hw : w ∈ Submodule.span (ZMod p) (Set.range h)) (hw0 : w ≠ 0)
    (hαw : ∀ i, α i w = 0) : ((C.det : ℤ) : ZMod p) = 0 := by
  classical
  rw [Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨c, hc⟩ := hw
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [← hc]; simp)
  have hmul : (C.map fun x : ℤ => (x : ZMod p)).mulVec c = 0 := by
    funext i
    rw [Matrix.mulVec_apply_eq_sum, Pi.zero_apply]
    calc ∑ j, (C.map fun x : ℤ => (x : ZMod p)) i j * c j
        = ∑ j, c j * (C i j : ZMod p) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.map_apply, mul_comm]
      _ = 0 := by
          have h := hαw i
          rw [← hc] at h
          simpa only [map_sum, map_smul, hP, smul_eq_mul] using h
  have hdet0 : (C.map fun x : ℤ => (x : ZMod p)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hc0, hmul⟩
  rw [Int.cast_det C]
  exact hdet0

theorem ggRC_singular_typeA_or_E6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hdet : ((C.det : ℤ) : ZMod p) = 0) :
    (GGIsTypeA M ∧ p ∣ Fintype.card Λ + 1) ∨ (p = 3 ∧ GGIsTypeE6 M) := by
  have hdvd : (p : ℤ) ∣ C.det := (ZMod.intCast_zmod_eq_zero_iff_dvd C.det p).1 hdet
  rcases l05nC2d_det_of_weyl hM hC with hA | ⟨hE6, hdet3⟩ | hdet1 | hdet2 | hdet4
  · obtain ⟨n, e, hn, hMeq⟩ := hA
    have hCdet : C.det = (n : ℤ) + 1 := by
      rw [l05nC2d_det_eq_of_reindex (ggIntCartan_A n) (ggAtMostOneMultipleEdge_A n)
        e (hMeq ▸ hC), CartanMatrix.A_det]
    have hdiv : p ∣ n + 1 := by
      rw [hCdet] at hdvd
      exact_mod_cast hdvd
    have hcard : Fintype.card Λ = n := by
      simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm
    exact Or.inl ⟨⟨n, e, hn, hMeq⟩, hcard ▸ hdiv⟩
  · have hdiv : p ∣ 3 := by
      rw [hdet3] at hdvd
      exact_mod_cast hdvd
    exact Or.inr ⟨(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdiv, hE6⟩
  · exact absurd hdvd (l05nC2d_not_dvd_one_two_four hp hp2 (Or.inl hdet1))
  · exact absurd hdvd (l05nC2d_not_dvd_one_two_four hp hp2 (Or.inr (Or.inl hdet2)))
  · exact absurd hdvd (l05nC2d_not_dvd_one_two_four hp hp2 (Or.inr (Or.inr hdet4)))

theorem ggRC_singular_typeA_or_E6_of_rank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hrank : Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 = Fintype.card Λ) :
    (GGIsTypeA M ∧ p ∣ Fintype.card Λ + 1) ∨ (p = 3 ∧ GGIsTypeE6 M) := by
  let : Fact p.Prime := ⟨hp⟩
  apply ggRC_singular_typeA_or_E6 hp hp2 hM hC
  by_contra hdet
  have hdet' : (C.map (Int.castRingHom (ZMod p))).det ≠ 0 := by
    change ((Int.castRingHom (ZMod p)).mapMatrix C).det ≠ 0
    rw [← RingHom.map_det]
    exact hdet
  have hfull := Matrix.rank_of_det_ne_zero hdet'
  omega

theorem ggRC_typeA_of_dvd_det {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hM : GGIsWeylMatrix M)
    (hC : GGIntCartan M C) (h7 : 7 ≤ Fintype.card Λ) (hdet : ((C.det : ℤ) : ZMod p) = 0) :
    GGIsTypeA M := by
  rcases ggRC_singular_typeA_or_E6 hp hp2 hM hC hdet with ⟨hA, -⟩ | ⟨-, hE6⟩
  · exact hA
  · exfalso
    obtain ⟨e, -⟩ := hE6
    have hcard : Fintype.card Λ = 6 := by simpa using (Fintype.card_congr e).symm
    omega

end CFSG.StandardType
