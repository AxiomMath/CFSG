module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Defs
public import CFSG.RankThree.PartOne.CTP.SeitzDiag
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Open

variable {K : Type} [Field K] [Finite K]

private theorem isPrimitiveRoot_omega (ζ : CubeRoot K) :
    IsPrimitiveRoot (ζ.ω : K) 3 := by
  refine IsPrimitiveRoot.mk_of_lt (ζ.ω : K) (by norm_num) ?_ ?_
  · simpa using congrArg (fun u : Kˣ => (u : K)) ζ.pow_three
  · intro l hl0 hl3 h
    have h3 : (ζ.ω : K) ^ 3 = 1 := by
      simpa using congrArg (fun u : Kˣ => (u : K)) ζ.pow_three
    have hl : l = 1 ∨ l = 2 := by omega
    rcases hl with rfl | rfl
    · exact ζ.ne_one (Units.ext (by simpa using h))
    · have : (ζ.ω : K) = 1 := by
        calc (ζ.ω : K) = (ζ.ω : K) ^ 2 * (ζ.ω : K) := by rw [h]; ring
          _ = (ζ.ω : K) ^ 3 := by ring
          _ = 1 := h3
      exact ζ.ne_one (Units.ext this)

private theorem det_diagUnit (u : Fin 4 → Kˣ) :
    Matrix.GeneralLinearGroup.det (diagUnit u) = ∏ i, u i := by
  ext
  simp [diagUnit, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal]

theorem d₀_le_sl (ζ : CubeRoot K) : D₀ ζ ≤ StatedSL 4 K := by
  rintro g ⟨v, rfl⟩
  exact StatedAPI.mem_statedSL_of_det (det_stdDiagHom ζ v)

private theorem conjFact_sl_map_comm (A : Subgroup (StatedSL 4 K))
    (hA : IsElemAbelian 3 A) :
    ∀ x ∈ A.map (StatedSL 4 K).subtype, ∀ y ∈ A.map (StatedSL 4 K).subtype,
      x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
  simpa using congrArg (fun z : A => ((z : StatedSL 4 K) : GL (Fin 4) K))
    (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem conjFact_sl_map_pow_three (A : Subgroup (StatedSL 4 K))
    (hA : IsElemAbelian 3 A) :
    ∀ x ∈ A.map (StatedSL 4 K).subtype, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Subgroup.mem_map.1 hx
  rw [← hxa, ← map_pow, hA.2 a ha, map_one]

private theorem conjFact_sl_card (A : Subgroup (StatedSL 4 K)) (hcard : Nat.card A = 27) :
    Nat.card (A.map (StatedSL 4 K).subtype) = 27 :=
  (Subgroup.card_map_of_injective (K := A) (f := (StatedSL 4 K).subtype)
    (StatedSL 4 K).subtype_injective).trans hcard

private theorem conjFact_sl_conj_D0 (ζ : CubeRoot K) (A : Subgroup (StatedSL 4 K))
    (hA : IsElemAbelian 3 A) (hcard : Nat.card A = 27) :
    ∃ g : GL (Fin 4) K,
      (A.map (StatedSL 4 K).subtype).map (MulAut.conj g).toMonoidHom = D₀ ζ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime
    (F := K) (n := 4) (p := 3) ⟨(ζ.ω : K), isPrimitiveRoot_omega ζ⟩
    (A.map (StatedSL 4 K).subtype) (conjFact_sl_map_comm A hA) (conjFact_sl_map_pow_three A hA)
  refine ⟨g, ?_⟩
  have hmap_le : (A.map (StatedSL 4 K).subtype).map (MulAut.conj g).toMonoidHom ≤ D₀ ζ := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨a, ha, hxa⟩ := Subgroup.mem_map.1 hx
    have hxdet : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
      rw [← hxa]
      exact StatedAPI.det_of_mem_statedSL a.2
    have hxdet_gl : Matrix.GeneralLinearGroup.det x = 1 := by
      ext
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using hxdet
    refine mem_D₀_of_diag ζ ?_ ?_ ?_
    · intro i j hij
      exact hg x hx i j hij
    · rw [← map_pow, conjFact_sl_map_pow_three A hA x hx, map_one]
    · have h : Matrix.GeneralLinearGroup.det (MulAut.conj g x) = 1 := by
        rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hxdet_gl, mul_one, mul_inv_cancel]
      exact congrArg Units.val h
  refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, conjFact_sl_card A hcard,
    card_D₀ ζ]

private theorem conjFact_sl_diagUnit_comm (ζ : CubeRoot K) (u : Fin 4 → Kˣ)
    {y : GL (Fin 4) K} (hy : y ∈ D₀ ζ) : diagUnit u * y = y * diagUnit u := by
  obtain ⟨v, rfl⟩ := hy
  have hw : stdDiagHom ζ v =
      diagUnit (fun i => ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j)) :=
    rfl
  rw [hw, ← diagUnit_mul, ← diagUnit_mul]
  congr 1
  exact mul_comm u _

private theorem conjFact_sl_det (g : GL (Fin 4) K) :
    Matrix.GeneralLinearGroup.det
      (diagUnit (fun i : Fin 4 => if i = 0 then (Matrix.GeneralLinearGroup.det g)⁻¹ else 1) *
        g) = 1 := by
  let d : Kˣ := Matrix.GeneralLinearGroup.det g
  let u : Fin 4 → Kˣ := fun i => if i = 0 then d⁻¹ else 1
  change Matrix.GeneralLinearGroup.det (diagUnit u * g) = 1
  have hdet_t : Matrix.GeneralLinearGroup.det (diagUnit u) = d⁻¹ := by
    rw [det_diagUnit, Fintype.prod_eq_single (0 : Fin 4) (fun x hx => by simp [u, hx])]
    simp [u]
  rw [map_mul, hdet_t, show Matrix.GeneralLinearGroup.det g = d from rfl]
  exact inv_mul_cancel d

private theorem conjFact_sl_det_mat (g : GL (Fin 4) K) :
    ((diagUnit (fun i : Fin 4 => if i = 0 then (Matrix.GeneralLinearGroup.det g)⁻¹ else 1) * g :
        GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  have h := congrArg Units.val (conjFact_sl_det g)
  simpa [Matrix.GeneralLinearGroup.val_det_apply] using h

private theorem conjFact_sl_conj_D0_sl (ζ : CubeRoot K) (A : Subgroup (StatedSL 4 K))
    (hcard : Nat.card A = 27) {g : GL (Fin 4) K}
    (hg : (A.map (StatedSL 4 K).subtype).map (MulAut.conj g).toMonoidHom = D₀ ζ) :
    ∃ g' : StatedSL 4 K,
      (A.map (StatedSL 4 K).subtype).map
        (MulAut.conj (g' : GL (Fin 4) K)).toMonoidHom = D₀ ζ := by
  let t : GL (Fin 4) K :=
    diagUnit (fun i : Fin 4 => if i = 0 then (Matrix.GeneralLinearGroup.det g)⁻¹ else 1)
  have htg : ((t * g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    change ((diagUnit (fun i : Fin 4 =>
        if i = 0 then (Matrix.GeneralLinearGroup.det g)⁻¹ else 1) * g :
          GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1
    exact conjFact_sl_det_mat g
  refine ⟨⟨t * g, StatedAPI.mem_statedSL_of_det htg⟩, ?_⟩
  have hmap_le2 : (A.map (StatedSL 4 K).subtype).map
      (MulAut.conj (t * g)).toMonoidHom ≤ D₀ ζ := by
    rintro y ⟨x, hx, rfl⟩
    have hy : MulAut.conj g x ∈ D₀ ζ := by
      rw [← hg]
      exact Subgroup.mem_map_of_mem ((MulAut.conj g).toMonoidHom) hx
    have hconj : MulAut.conj (t * g) x = MulAut.conj g x := by
      rw [MulAut.conj_apply, MulAut.conj_apply]
      have hty : t * (g * x * g⁻¹) = (g * x * g⁻¹) * t :=
        conjFact_sl_diagUnit_comm ζ
          (fun i : Fin 4 => if i = 0 then (Matrix.GeneralLinearGroup.det g)⁻¹ else 1) hy
      calc (t * g) * x * (t * g)⁻¹ = t * (g * x * g⁻¹) * t⁻¹ := by group
        _ = (g * x * g⁻¹) * t * t⁻¹ := by rw [hty]
        _ = g * x * g⁻¹ := by group
    change MulAut.conj (t * g) x ∈ D₀ ζ
    rw [hconj]
    exact hy
  refine Subgroup.eq_of_le_of_card_ge hmap_le2 ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj (t * g)).injective, conjFact_sl_card A hcard,
    card_D₀ ζ]

private theorem conjFact_sl_subgroup_eq (ζ : CubeRoot K) (A : Subgroup (StatedSL 4 K))
    (g' : StatedSL 4 K)
    (hg' : (A.map (StatedSL 4 K).subtype).map
      (MulAut.conj (g' : GL (Fin 4) K)).toMonoidHom = D₀ ζ) :
    A.map (MulAut.conj g').toMonoidHom = (D₀ ζ).subgroupOf (StatedSL 4 K) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    show ((MulAut.conj g' a : StatedSL 4 K) : GL (Fin 4) K) ∈ D₀ ζ
    rw [show ((MulAut.conj g' a : StatedSL 4 K) : GL (Fin 4) K) =
        MulAut.conj (g' : GL (Fin 4) K) ((a : StatedSL 4 K) : GL (Fin 4) K) from rfl]
    rw [← hg']
    exact Subgroup.mem_map_of_mem ((MulAut.conj (g' : GL (Fin 4) K)).toMonoidHom)
      (Subgroup.mem_map_of_mem (StatedSL 4 K).subtype ha)
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [← hg'] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 hy
    refine ⟨a, ha, ?_⟩
    apply Subtype.ext
    show ((MulAut.conj g' a : StatedSL 4 K) : GL (Fin 4) K) = (x : GL (Fin 4) K)
    rw [show ((MulAut.conj g' a : StatedSL 4 K) : GL (Fin 4) K) =
        MulAut.conj (g' : GL (Fin 4) K) ((a : StatedSL 4 K) : GL (Fin 4) K) from rfl]
    rw [← hay] at hyx
    exact hyx

theorem conjFact_sl (ζ : CubeRoot K) : ConjFact (StatedSL 4 K) ζ := by
  refine ⟨d₀_le_sl ζ, ?_⟩
  intro A hA hcard
  obtain ⟨g, hg⟩ := conjFact_sl_conj_D0 ζ A hA hcard
  obtain ⟨g', hg'⟩ := conjFact_sl_conj_D0_sl ζ A hcard hg
  exact ⟨g', conjFact_sl_subgroup_eq ζ A g' hg'⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
