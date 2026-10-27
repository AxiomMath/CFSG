module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Centralizer
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Pieces
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrame

public section

noncomputable section

open Module Matrix QuadraticMap
open scoped MatrixGroups

namespace CFSG.StandardType.OrthTorus

open CFSG.ClassicalInvolution.Models.OrthogonalPairs

variable {K D V : Type} [Field K] [CharP K 2]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

omit [CharP K 2] in
private theorem polar_pair_map (hD : finrank K D = 2)
    (φ : (D × D) →ₗ[K] V)
    (hQ : ∀ v : D × D, Q (φ v) = rk1Omega hD v.1 v.2)
    (v w : D × D) :
    polar Q (φ v) (φ w) = rk1Omega hD v.1 w.2 + rk1Omega hD w.1 v.2 := by
  rw [polar, ← map_add, hQ, hQ, hQ]
  simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
  ring

private def pairFrame (hD : finrank K D = 2)
    (φ : (D × D) →ₗ[K] V)
    (hQ : ∀ v : D × D, Q (φ v) = rk1Omega hD v.1 v.2) : Frame Q := by
  let b := Module.finBasisOfFinrankEq K D hD
  refine
    { P :=
        { e := φ (b 0, 0)
          f := φ (0, b 1)
          Q_e := ?_
          Q_f := ?_
          polar_ef := ?_ }
      P' :=
        { e := φ (b 1, 0)
          f := φ (0, b 0)
          Q_e := ?_
          Q_f := ?_
          polar_ef := ?_ }
      orth := { ee := ?_, ef := ?_, fe := ?_, ff := ?_ } }
  all_goals
    simp [hQ, polar_pair_map hD φ hQ, rk1Omega_apply, b,
      CharTwo.neg_eq]

private theorem pairFrame_incl (hD : finrank K D = 2)
    (φ : (D × D) →ₗ[K] V)
    (hQ : ∀ v : D × D, Q (φ v) = rk1Omega hD v.1 v.2)
    (X : Matrix (Fin 2) (Fin 2) K) :
    let b := Module.finBasisOfFinrankEq K D hD
    (pairFrame hD φ hQ).incl X =
      φ (X 0 0 • b 0 + X 0 1 • b 1, X 1 0 • b 0 + X 1 1 • b 1) := by
  let b := Module.finBasisOfFinrankEq K D hD
  change X 0 0 • φ (b 0, 0) + X 1 1 • φ (0, b 1) +
      (-X 0 1) • φ (b 1, 0) + X 1 0 • φ (0, b 0) = _
  rw [CharTwo.neg_eq]
  calc
    _ = φ (X 0 0 • (b 0, 0) + X 1 1 • (0, b 1) +
        X 0 1 • (b 1, 0) + X 1 0 • (0, b 0)) := by
      simp only [map_add, map_smul]
    _ = _ := by
      congr 1
      ext <;> simp [b, Prod.smul_mk, add_comm]

private def pairCoords (hD : finrank K D = 2) (v : D × D) :
    Matrix (Fin 2) (Fin 2) K :=
  let b := Module.finBasisOfFinrankEq K D hD
  !![b.repr v.1 0, b.repr v.1 1; b.repr v.2 0, b.repr v.2 1]

private theorem pairFrame_incl_coords (hD : finrank K D = 2)
    (φ : (D × D) →ₗ[K] V)
    (hQ : ∀ v : D × D, Q (φ v) = rk1Omega hD v.1 v.2) (v : D × D) :
    (pairFrame hD φ hQ).incl (pairCoords hD v) = φ v := by
  let b := Module.finBasisOfFinrankEq K D hD
  rw [pairFrame_incl]
  change φ (b.repr v.1 0 • b 0 + b.repr v.1 1 • b 1,
      b.repr v.2 0 • b 0 + b.repr v.2 1 • b 1) = φ v
  congr 1
  apply Prod.ext
  · simpa only [Fin.sum_univ_two] using b.sum_repr v.1
  · simpa only [Fin.sum_univ_two] using b.sum_repr v.2

private theorem pairFrame_La_apply (hD : finrank K D = 2)
    (φ : (D × D) →ₗ[K] V)
    (hQ : ∀ v : D × D, Q (φ v) = rk1Omega hD v.1 v.2)
    (g : SL(2, K)) (v : D × D) :
    (pairFrame hD φ hQ).La g (φ v) = φ (rk1ModelAct g v) := by
  let b := Module.finBasisOfFinrankEq K D hD
  have h0 : b.repr v.1 0 • b 0 + b.repr v.1 1 • b 1 = v.1 := by
    simpa only [Fin.sum_univ_two] using b.sum_repr v.1
  have h1 : b.repr v.2 0 • b 0 + b.repr v.2 1 • b 1 = v.2 := by
    simpa only [Fin.sum_univ_two] using b.sum_repr v.2
  rw [← pairFrame_incl_coords hD φ hQ v, Frame.La_apply_incl, pairFrame_incl,
    rk1ModelAct_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, pairCoords, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  apply congrArg φ
  apply Prod.ext
  · change (g 0 0 * b.repr v.1 0 + g 0 1 * b.repr v.2 0) • b 0 +
        (g 0 0 * b.repr v.1 1 + g 0 1 * b.repr v.2 1) • b 1 = _
    calc
      _ = g 0 0 • (b.repr v.1 0 • b 0 + b.repr v.1 1 • b 1) +
          g 0 1 • (b.repr v.2 0 • b 0 + b.repr v.2 1 • b 1) := by module
      _ = _ := by rw [h0, h1]
  · change (g 1 0 * b.repr v.1 0 + g 1 1 * b.repr v.2 0) • b 0 +
        (g 1 0 * b.repr v.1 1 + g 1 1 * b.repr v.2 1) • b 1 = _
    calc
      _ = g 1 0 • (b.repr v.1 0 • b 0 + b.repr v.1 1 • b 1) +
          g 1 1 • (b.repr v.2 0 • b 0 + b.repr v.2 1 • b 1) := by module
      _ = _ := by rw [h0, h1]

private theorem pairFrame_span (hD : finrank K D = 2)
    (φ : (D × D) →ₗ[K] V)
    (hQ : ∀ v : D × D, Q (φ v) = rk1Omega hD v.1 v.2) :
    (pairFrame hD φ hQ).span = LinearMap.range φ := by
  ext u
  constructor
  · rintro ⟨X, rfl⟩
    rw [pairFrame_incl]
    exact LinearMap.mem_range_self φ _
  · rintro ⟨v, rfl⟩
    exact ⟨pairCoords hD v, pairFrame_incl_coords hD φ hQ v⟩

open CFSG.RankThree.Classical2 (orthDerived)

theorem TBJOmData.exists_rankOne_frame [Finite K] [FiniteDimensional K V]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {A : Subgroup (V ≃ₗ[K] V)}
    (hAΩ : A ≤ orthDerived Q) {r : ℕ} (Δ : TBJOmData Q p A r)
    (hq : 4 ≤ Nat.card K) (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (i j : Fin r) (hij : i ≠ j) :
    ∃ F : Frame Q, F.span = Δ.F.U i ⊔ Δ.F.U j ∧ F.La.range = Δ.rankOne i j := by
  obtain ⟨φ, _hφinj, hφrange, hφQ, θ, _hθinj, hθrange, hθφ, hθfix⟩ :=
    Δ.exists_rankOne_model hp2 hAΩ hq hfix i j hij
  let F := pairFrame Δ.finrank_D φ hφQ
  let b := Module.finBasisOfFinrankEq K Δ.D Δ.finrank_D
  have hspan : F.span = Δ.F.U i ⊔ Δ.F.U j :=
    (pairFrame_span Δ.finrank_D φ hφQ).trans hφrange
  have horth (k : Fin r) (hki : k ≠ i) (hkj : k ≠ j) (u : V)
      (hu : u ∈ Δ.F.U k) (v : Δ.D × Δ.D) : polar Q u (φ v) = 0 := by
    have hv : φ v ∈ Δ.F.U i ⊔ Δ.F.U j := by
      rw [← hφrange]
      exact LinearMap.mem_range_self φ v
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hv
    rw [← hxy, polar_add_right,
      Δ.F.orth k i hki u hu x hx, Δ.F.orth k j hkj u hu y hy, add_zero]
  have hcoords (k : Fin r) (hki : k ≠ i) (hkj : k ≠ j) (u : V)
      (hu : u ∈ Δ.F.U k) : F.coords u = 0 := by
    change !![polar Q u (φ (0, b 1)), -polar Q u (φ (0, b 0));
      polar Q u (φ (b 1, 0)), polar Q u (φ (b 0, 0))] = 0
    ext a c
    fin_cases a <;> fin_cases c <;> simp [horth k hki hkj u hu]
  have hLa (g : SL(2, K)) : F.La g = θ g := by
    let Z := LinearMap.ker ((F.La g : V →ₗ[K] V) - (θ g : V →ₗ[K] V))
    have hle (k : Fin r) : Δ.F.U k ≤ Z := by
      intro u hu
      change F.La g u - θ g u = 0
      by_cases hki : k = i
      · subst k
        have hv : u ∈ Δ.F.U i ⊔ Δ.F.U j :=
          (le_sup_left : Δ.F.U i ≤ Δ.F.U i ⊔ Δ.F.U j) hu
        rw [← hφrange] at hv
        obtain ⟨v, rfl⟩ := hv
        rw [pairFrame_La_apply Δ.finrank_D φ hφQ, hθφ, sub_self]
      · by_cases hkj : k = j
        · subst k
          have hv : u ∈ Δ.F.U i ⊔ Δ.F.U j :=
            (le_sup_right : Δ.F.U j ≤ Δ.F.U i ⊔ Δ.F.U j) hu
          rw [← hφrange] at hv
          obtain ⟨v, rfl⟩ := hv
          rw [pairFrame_La_apply Δ.finrank_D φ hφQ, hθφ, sub_self]
        · rw [Frame.La_apply_of_coords_eq_zero F g (hcoords k hki hkj u hu),
            hθfix g k hki hkj u hu, sub_self]
    have hZ : ⊤ ≤ Z := by
      rw [← Δ.iSup_U_eq_top hfix]
      exact iSup_le hle
    apply LinearEquiv.ext
    intro u
    exact sub_eq_zero.mp (hZ (Submodule.mem_top : u ∈ (⊤ : Submodule K V)))
  refine ⟨F, hspan, ?_⟩
  have hhom : F.La = θ := by
    apply MonoidHom.ext
    intro g
    exact hLa g
  rw [hhom, hθrange]

theorem OrthWeakFrame.exists_rankOne_frame {G : Type} [Group G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs L : Subgroup G} (Φ : OrthWeakFrame p Bs L)
    (i j : Fin Φ.r) (hij : i ≠ j) :
    ∃ F : Frame Φ.Q, F.span = Φ.Δ.F.U i ⊔ Φ.Δ.F.U j ∧
      F.La.range = Φ.Δ.rankOne i j := by
  have hq : 4 ≤ Nat.card Φ.F := by
    rw [Φ.hcard]
    have hpow : 2 ^ 2 ≤ 2 ^ Φ.f :=
      Nat.pow_le_pow_right (by decide : 0 < 2) Φ.hf
    exact hpow
  exact Φ.Δ.exists_rankOne_frame hp2 Φ.hA hq Φ.hfix i j hij

end CFSG.StandardType.OrthTorus

end
