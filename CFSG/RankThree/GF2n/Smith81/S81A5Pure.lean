module

public import CFSG.RankThree.GF2n.Smith81.S81A5Types
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower

variable {K : Type*} [Field K]

theorem vecCons_triple_injective {i j k : Fin 6} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Injective (![i, j, k] : Fin 3 → Fin 6) := by
  intro s t h
  fin_cases s <;> fin_cases t <;>
    first
      | rfl
      | (exfalso; simp [hij, hik, hjk, hij.symm, hik.symm, hjk.symm] at h)

theorem mem_range_enum_of_triple {I : Set.powersetCard (Fin 6) 3} {i j k : Fin 6}
    (hI : I.val = {i, j, k}) (s : Fin 3) : ![i, j, k] s ∈ Set.range (enum I) := by
  refine (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I _).mpr ?_
  show ![i, j, k] s ∈ I.val
  rw [hI]
  fin_cases s <;> simp

theorem coord_ιMulti_triple (v : Fin 3 → Fin 6 → K) {I : Set.powersetCard (Fin 6) 3}
    {i j k : Fin 6} (hI : I.val = {i, j, k}) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    coord K (ιMulti K 3 v) I = minor3 v i j k ∨ coord K (ιMulti K 3 v) I = - minor3 v i j k := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 3), ∀ s, enum I (σ s) = ![i, j, k] s := by
    have hf := vecCons_triple_injective hij hik hjk
    have hg : ∀ s, enum I (Function.invFun (enum I) (![i, j, k] s)) = ![i, j, k] s :=
      fun s => Function.invFun_eq (Set.mem_range.mp (mem_range_enum_of_triple hI s))
    have hinj : Function.Injective (fun s => Function.invFun (enum I) (![i, j, k] s)) := by
      intro s t hst
      apply hf
      calc ![i, j, k] s = enum I (Function.invFun (enum I) (![i, j, k] s)) := (hg s).symm
        _ = enum I (Function.invFun (enum I) (![i, j, k] t)) := congrArg (⇑(enum I)) hst
        _ = ![i, j, k] t := hg t
    exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj), hg⟩
  have hM : (Matrix.of fun r (s : Fin 3) => v r (![i, j, k] s)) =
      (Matrix.of fun r (s : Fin 3) => v r (enum I s)).submatrix id σ := by
    ext r s
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id_eq]
    rw [hσ s]
  rw [coord_ιMulti]
  unfold minor3
  rw [hM, Matrix.det_permute']
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]

@[expose] def tripleSet (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Set.powersetCard (Fin 6) 3 :=
  ⟨{i, j, k}, Finset.card_eq_three.mpr ⟨i, j, k, hij, hik, hjk, rfl⟩⟩

theorem exists_triple (I : Set.powersetCard (Fin 6) 3) :
    ∃ i j k : Fin 6, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ I.val = {i, j, k} := by
  obtain ⟨i, j, k, hij, hik, hjk, h⟩ := Finset.card_eq_three.mp (Set.powersetCard.card_eq I)
  exact ⟨i, j, k, hij, hik, hjk, h⟩

@[expose] def J2 : Set.powersetCard (Fin 6) 3 :=
  tripleSet 3 4 5 (by decide) (by decide) (by decide)

theorem enum_tripleSet {i j k : Fin 6} (hij : i < j) (hjk : j < k) (s : Fin 3) :
    enum (tripleSet i j k hij.ne (hij.trans hjk).ne hjk.ne) s = ![i, j, k] s := by
  have hmono : StrictMono (![i, j, k] : Fin 3 → Fin 6) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro a
    fin_cases a <;> simp [hij, hjk]
  have hfs : ∀ x : Fin 3, (![i, j, k] : Fin 3 → Fin 6) x ∈
      (tripleSet i j k hij.ne (hij.trans hjk).ne hjk.ne).val := by
    intro x
    fin_cases x <;> simp [tripleSet]
  have heq : OrderEmbedding.ofStrictMono ![i, j, k] hmono =
      (tripleSet i j k hij.ne (hij.trans hjk).ne hjk.ne).val.orderEmbOfFin
        (tripleSet i j k hij.ne (hij.trans hjk).ne hjk.ne).prop :=
    Finset.orderEmbOfFin_unique' _ (fun x => hfs x)
  have key : enum (tripleSet i j k hij.ne (hij.trans hjk).ne hjk.ne) =
      OrderEmbedding.ofStrictMono ![i, j, k] hmono := heq.symm
  rw [key, OrderEmbedding.coe_ofStrictMono]

theorem coord_ιMulti_sorted (v : Fin 3 → Fin 6 → K) {i j k : Fin 6} (hij : i < j) (hjk : j < k) :
    coord K (ιMulti K 3 v) (tripleSet i j k hij.ne (hij.trans hjk).ne hjk.ne) =
      minor3 v i j k := by
  rw [coord_ιMulti]
  unfold minor3
  congr 1
  ext r s
  simp [enum_tripleSet hij hjk]

theorem eq_zero_of_coord_eq_zero {ξ : Cube K} (h : ∀ I, coord K ξ I = 0) : ξ = 0 := by
  refine (cubeBasis K).repr.map_eq_zero_iff.mp ?_
  ext I
  exact h I

theorem coord_sub (a b : Cube K) (I : Set.powersetCard (Fin 6) 3) :
    coord K (a - b) I = coord K a I - coord K b I := by
  simp [coord]

@[expose] def uMap (K : Type*) [Field K] : W4 K →ₗ[K] Cube K where
  toFun w := ιMulti K 3 ![e K 0, e K 1, (w : Fin 6 → K)]
  map_add' w w' := ι3_add_thd _ _ _ _
  map_smul' c w := ι3_smul_thd c _ _ _

theorem mem_Usp_iff {ξ : Cube K} :
    ξ ∈ Usp K ↔ ∃ w ∈ W4 K, ξ = ιMulti K 3 ![e K 0, e K 1, w] := by
  constructor
  · intro h
    have hle : Usp K ≤ LinearMap.range (uMap K) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, h2, h4, rfl⟩
      have h0 : a 0 ∈ W2 K := h2 0 (by decide)
      have h1 : a 1 ∈ W2 K := h2 1 (by decide)
      have h2' : a 2 ∈ W4 K := h4 2 (by decide)
      have ha : ιMulti K 3 a = ιMulti K 3 ![a 0, a 1, a 2] := congrArg _ (by
        funext i; fin_cases i <;> rfl)
      refine ⟨(a 0 0 * a 1 1 - a 0 1 * a 1 0) • ⟨a 2, h2'⟩, ?_⟩
      show ιMulti K 3 ![e K 0, e K 1, (a 0 0 * a 1 1 - a 0 1 * a 1 0) • a 2] = _
      rw [ι3_smul_thd, ha, ιMulti_W2_two h0 h1]
    obtain ⟨w, hw⟩ := hle h
    exact ⟨w, w.2, hw.symm⟩
  · rintro ⟨w, hw, rfl⟩
    refine Submodule.subset_span ⟨![e K 0, e K 1, w], ?_, ?_, rfl⟩
    · intro i hi
      fin_cases i
      · exact e_mem_W2 (by decide)
      · exact e_mem_W2 (by decide)
      · exact absurd hi (by decide)
    · intro i hi
      fin_cases i
      · exact absurd hi (by decide)
      · exact absurd hi (by decide)
      · exact hw

theorem isPure_of_mem_Usp {ξ : Cube K} (h : ξ ∈ Usp K) : IsPure K ξ := by
  obtain ⟨w, -, rfl⟩ := mem_Usp_iff.mp h
  exact ⟨_, rfl⟩

end CFSG.RankThree.GF2n.Smith81.A5Cube
