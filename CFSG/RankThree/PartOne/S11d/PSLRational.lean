module

public import CFSG.RankThree.PartOne.S11d.PSLRank

public section

namespace CFSG.RankThree.PartOne

open Matrix

variable {n : ℕ} {K : Type} [Field K]

structure RatBasis (σ : K ≃+* K) (P : Matrix (Fin n) (Fin n) K) (m : ℕ) where
  C : Matrix (Fin n) (Fin m) K
  L : Matrix (Fin m) (Fin n) K
  map_C : C.map σ = C
  LC : L * C = 1
  range_eq : LinearMap.range C.mulVecLin = LinearMap.range P.mulVecLin

theorem exists_rational_columns (σ : K ≃+* K) (P : Matrix (Fin n) (Fin n) K) (hP : P.map σ = P) :
    ∃ m : ℕ, Nonempty (RatBasis σ P m) ∧ Module.finrank K (LinearMap.range P.mulVecLin) = m := by
  classical
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent K (Set.range P.col)
  have : Finite b := Set.Finite.subset (Set.finite_range P.col) hbs |>.to_subtype
  have : Fintype b := Fintype.ofFinite b
  set m := Fintype.card b with hm
  let e : Fin m ≃ b := (Fintype.equivFin b).symm
  let C : Matrix (Fin n) (Fin m) K := Matrix.of fun i j => ((e j : b) : Fin n → K) i
  have hCcol : ∀ j, C.col j = ((e j : b) : Fin n → K) := fun j => by
    funext i
    rfl
  have hCli : LinearIndependent K C.col := by
    have h1 : LinearIndependent K (fun j : Fin m => ((e j : b) : Fin n → K)) :=
      hbli.comp e e.injective
    convert h1 using 1
    funext j
    exact hCcol j
  have hCinj : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.mpr hCli
  have hCσ : C.map σ = C := by
    ext i j
    have hj := hbs (e j).2
    obtain ⟨k, hk⟩ := hj
    have : ((e j : b) : Fin n → K) = P.col k := hk.symm
    simp only [Matrix.map_apply]
    change σ (((e j : b) : Fin n → K) i) = ((e j : b) : Fin n → K) i
    rw [this]
    change σ (P i k) = P i k
    exact congrFun (congrFun hP i) k
  have hrange : LinearMap.range C.mulVecLin = LinearMap.range P.mulVecLin := by
    rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
    have : Set.range C.col = (b : Set (Fin n → K)) := by
      ext v
      constructor
      · rintro ⟨j, rfl⟩
        rw [hCcol]
        exact (e j).2
      · intro hv
        exact ⟨e.symm ⟨v, hv⟩, by rw [hCcol]; simp⟩
    rw [this, hbspan]
  have hfin : Module.finrank K (LinearMap.range P.mulVecLin) = m := by
    rw [← hrange, Matrix.range_mulVecLin, finrank_span_eq_card hCli, Fintype.card_fin]
  have hker : LinearMap.ker (Matrix.toLin' C) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact hCinj
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C) hker
  refine ⟨m, ⟨⟨C, LinearMap.toMatrix' g, hCσ, ?_, hrange⟩⟩, hfin⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hg, Matrix.toLin'_one]

section Coord

variable {m : ℕ}

theorem exists_mul_eq_of_commute {P : Matrix (Fin n) (Fin n) K} {C : Matrix (Fin n) (Fin m) K}
    (hC : LinearMap.range C.mulVecLin = LinearMap.range P.mulVecLin)
    {g : Matrix (Fin n) (Fin n) K} (hg : g * P = P * g) :
    ∃ N : Matrix (Fin m) (Fin m) K, g * C = C * N := by
  classical
  have h : ∀ j, ∃ w : Fin m → K, C.mulVec w = g.mulVec (C.col j) := by
    intro j
    have hj : C.col j ∈ LinearMap.range C.mulVecLin :=
      ⟨Pi.single j 1, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]⟩
    rw [hC] at hj
    obtain ⟨u, hu⟩ := hj
    have hmem : g.mulVec (C.col j) ∈ LinearMap.range C.mulVecLin := by
      rw [hC]
      refine ⟨g.mulVec u, ?_⟩
      rw [Matrix.mulVecLin_apply] at hu ⊢
      rw [← hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hg]
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, hw⟩
  choose w hw using h
  refine ⟨Matrix.of fun i j => w j i, ?_⟩
  ext i j
  have := congrFun (hw j) i
  simp only [Matrix.mulVec, dotProduct] at this
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.of_apply]
  exact this.symm

theorem coord_spec {L : Matrix (Fin m) (Fin n) K} {C : Matrix (Fin n) (Fin m) K} (hLC : L * C = 1)
    {g : Matrix (Fin n) (Fin n) K} {N : Matrix (Fin m) (Fin m) K} (h : g * C = C * N) :
    L * g * C = N := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hLC, Matrix.one_mul]

theorem map_mul_eq_of_mul_eq (σ : K ≃+* K) {C : Matrix (Fin n) (Fin m) K} (hC : C.map σ = C)
    {g : Matrix (Fin n) (Fin n) K} {N : Matrix (Fin m) (Fin m) K} (h : g * C = C * N) :
    g.map σ * C = C * N.map σ := by
  have := congrArg (fun M => M.map σ) h
  simp only [Matrix.map_mul, hC] at this
  exact this


variable {σ : K ≃+* K} {P : Matrix (Fin n) (Fin n) K} (R : RatBasis σ P m)
  (B : Subgroup (GL (Fin n) K)) (hB : ∀ g ∈ B, (g : Matrix (Fin n) (Fin n) K) * P = P * g)

include hB in
@[expose] noncomputable def coordMon : B →* Matrix (Fin m) (Fin m) K where
  toFun g := R.L * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * R.C
  map_one' := by simp [R.LC]
  map_mul' g₁ g₂ := by
    obtain ⟨N₁, h₁⟩ := exists_mul_eq_of_commute R.range_eq (hB g₁ g₁.2)
    obtain ⟨N₂, h₂⟩ := exists_mul_eq_of_commute R.range_eq (hB g₂ g₂.2)
    have e₁ := coord_spec R.LC h₁
    have e₂ := coord_spec R.LC h₂
    show R.L * (((g₁ : GL (Fin n) K) * (g₂ : GL (Fin n) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * R.C = _
    rw [Units.val_mul, e₁, e₂]
    calc R.L * (((g₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * R.C
        = R.L * ((g₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (((g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * R.C) := by
          simp only [Matrix.mul_assoc]
      _ = R.L * ((g₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (R.C * N₂) := by rw [h₂]
      _ = (R.L * ((g₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * R.C) * N₂ := by
          simp only [Matrix.mul_assoc]
      _ = N₁ * N₂ := by rw [e₁]

include hB in
theorem mul_coordMon (g : B) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * R.C = R.C * coordMon R B hB g := by
  obtain ⟨N, h⟩ := exists_mul_eq_of_commute R.range_eq (hB g g.2)
  have := coord_spec R.LC h
  change _ = R.C * (R.L * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * R.C)
  rw [this, h]

include hB in
theorem coordMon_map (g g' : B)
    (h : ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ) :
    coordMon R B hB g' = (coordMon R B hB g).map σ := by
  have h1 := mul_coordMon R B hB g
  have h2 := map_mul_eq_of_mul_eq σ R.map_C h1
  rw [← h] at h2
  have := coord_spec R.LC h2
  exact this

end Coord

end CFSG.RankThree.PartOne
