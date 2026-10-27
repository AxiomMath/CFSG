module

public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import CFSG.HardMathSupport.Lang.TwE6Step3.LangTorusMonomial
import Mathlib.Algebra.CharP.Two

public section

namespace CFSG.StandardType.TwE6D5Core

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.TwE6Step3

section KerTorus

@[expose] def charKerTorus (τ : Tag) (L : Type) [Field L] (Ψ : Set (Fin τ.rank → ℤ)) :
    Subgroup (ModGL τ L) where
  carrier := {g | ∃ b : Fin τ.rank → Lˣ, (∀ γ ∈ Ψ, rootChar b γ = 1) ∧ rootDiagUnit τ b = g}
  mul_mem' {x y} hx hy := by
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    refine ⟨a * b, fun γ hγ => ?_, rootDiagUnit_mul a b⟩
    have h : rootChar (a * b) γ = rootChar a γ * rootChar b γ := by
      simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
    rw [h, ha γ hγ, hb γ hγ, one_mul]
  one_mem' := ⟨1, fun γ _ => by simp [rootChar], rootDiagUnit_one⟩
  inv_mem' {x} hx := by
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨a⁻¹, fun γ hγ => ?_, (rootDiagUnit_inv a).symm⟩
    have h : rootChar a⁻¹ γ = (rootChar a γ)⁻¹ := by
      simp only [rootChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]
    rw [h, ha γ hγ, inv_one]

theorem mem_charKerTorus {τ : Tag} {L : Type} [Field L] {Ψ : Set (Fin τ.rank → ℤ)}
    {g : ModGL τ L} :
    g ∈ charKerTorus τ L Ψ ↔
      ∃ b : Fin τ.rank → Lˣ, (∀ γ ∈ Ψ, rootChar b γ = 1) ∧ rootDiagUnit τ b = g :=
  Iff.rfl

end KerTorus

section D5

private local instance kerTorusNeZeroRank : NeZero Tag.E6.rank := ⟨by decide +kernel⟩

private theorem exists_d5_finset {J : Set (Fin Tag.E6.rank)}
    (hJ : J = {j | 1 ≤ j.val} ∨ J = {j | j.val ≤ 4}) :
    ∃ Jf : Finset (Fin Tag.E6.rank), (∀ x, x ∈ Jf ↔ x ∈ J) ∧
      (Jf = {1, 2, 3, 4, 5} ∨ Jf = {0, 1, 2, 3, 4}) := by
  obtain rfl | rfl := hJ
  · refine ⟨{1, 2, 3, 4, 5}, ?_, Or.inl rfl⟩
    show ∀ x : Fin Tag.E6.rank, x ∈ ({1, 2, 3, 4, 5} : Finset (Fin Tag.E6.rank)) ↔ 1 ≤ x.val
    decide +kernel
  · refine ⟨{0, 1, 2, 3, 4}, ?_, Or.inr rfl⟩
    show ∀ x : Fin Tag.E6.rank, x ∈ ({0, 1, 2, 3, 4} : Finset (Fin Tag.E6.rank)) ↔ x.val ≤ 4
    decide +kernel

private theorem d5_matrices {Jf : Finset (Fin Tag.E6.rank)}
    (hJ : Jf = {1, 2, 3, 4, 5} ∨ Jf = {0, 1, 2, 3, 4}) :
    ∃ M N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ,
      (∀ i j, M i j = if i ∈ Jf then (if j ∈ Jf then Tag.E6.cartan j i else 0)
        else if j = i then 1 else 0) ∧
      M * N = Matrix.diagonal (fun _ => 4) ∧ N * M = Matrix.diagonal (fun _ => 4) := by
  obtain rfl | rfl := hJ
  · refine ⟨!![1, 0, 0, 0, 0, 0; 0, 2, 0, -1, 0, 0; 0, 0, 2, -1, 0, 0; 0, -1, -1, 2, -1, 0;
      0, 0, 0, -1, 2, -1; 0, 0, 0, 0, -1, 2], !![4, 0, 0, 0, 0, 0; 0, 5, 3, 6, 4, 2;
      0, 3, 5, 6, 4, 2; 0, 6, 6, 12, 8, 4; 0, 4, 4, 8, 8, 4; 0, 2, 2, 4, 4, 4],
      Prod.forall'.1 ?_, ?_, ?_⟩ <;> decide +kernel
  · refine ⟨!![2, 0, -1, 0, 0, 0; 0, 2, 0, -1, 0, 0; -1, 0, 2, -1, 0, 0; 0, -1, -1, 2, -1, 0;
      0, 0, 0, -1, 2, 0; 0, 0, 0, 0, 0, 1], !![4, 2, 4, 4, 2, 0; 2, 5, 4, 6, 3, 0;
      4, 4, 8, 8, 4, 0; 4, 6, 8, 12, 6, 0; 2, 3, 4, 6, 5, 0; 0, 0, 0, 0, 0, 4],
      Prod.forall'.1 ?_, ?_, ?_⟩ <;> decide +kernel

variable {L : Type} [Field L]

private theorem monoHom_diagonal (d : Fin Tag.E6.rank → ℤ) (t : Fin Tag.E6.rank → Lˣ)
    (i : Fin Tag.E6.rank) : monoHom (Matrix.diagonal d) t i = t i ^ d i := by
  rw [monoHom_apply, Finset.prod_eq_single i
    (fun j _ hj => by rw [Matrix.diagonal_apply_ne _ hj.symm, zpow_zero])
    (fun h => absurd (Finset.mem_univ i) h), Matrix.diagonal_apply_eq]

private theorem monoHom_apply_of_mem {Jf : Finset (Fin Tag.E6.rank)}
    {M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ}
    (hM : ∀ i j, M i j = if i ∈ Jf then (if j ∈ Jf then Tag.E6.cartan j i else 0)
      else if j = i then 1 else 0)
    (c : Fin Tag.E6.rank → Lˣ) {i : Fin Tag.E6.rank} (hi : i ∈ Jf) :
    monoHom M c i = ∏ j ∈ Jf, c j ^ Tag.E6.cartan j i := by
  rw [monoHom_apply]
  calc ∏ j, c j ^ M i j = ∏ j ∈ Jf, c j ^ M i j :=
        (Finset.prod_subset (Finset.subset_univ Jf) fun j _ hj => by
          rw [hM, if_pos hi, if_neg hj, zpow_zero]).symm
    _ = ∏ j ∈ Jf, c j ^ Tag.E6.cartan j i :=
        Finset.prod_congr rfl fun j hj => by rw [hM, if_pos hi, if_pos hj]

private theorem monoHom_apply_of_notMem {Jf : Finset (Fin Tag.E6.rank)}
    {M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ}
    (hM : ∀ i j, M i j = if i ∈ Jf then (if j ∈ Jf then Tag.E6.cartan j i else 0)
      else if j = i then 1 else 0)
    (c : Fin Tag.E6.rank → Lˣ) {i : Fin Tag.E6.rank} (hi : i ∉ Jf) : monoHom M c i = c i := by
  rw [monoHom_apply, Finset.prod_eq_single i
    (fun j _ hj => by rw [hM, if_neg hi, if_neg hj, zpow_zero])
    (fun h => absurd (Finset.mem_univ i) h), hM, if_neg hi, if_pos rfl, zpow_one]

theorem exists_d5_solution [IsAlgClosed L] {J : Set (Fin Tag.E6.rank)} [Fintype J]
    (hJ : J = {j | 1 ≤ j.val} ∨ J = {j | j.val ≤ 4}) (y : Fin Tag.E6.rank → Lˣ) :
    ∃ a : J → Lˣ, ∀ i ∈ J, ∏ j : J, a j ^ Tag.E6.cartan j i = y i := by
  obtain ⟨Jf, hJf, hJ'⟩ := exists_d5_finset hJ
  obtain ⟨M, N, hM, hMN, -⟩ := d5_matrices hJ'
  choose z hz using fun i => exists_unit_zpow_eq (y i) (show (4 : ℤ) ≠ 0 by norm_num)
  refine ⟨fun j => monoHom N z j, fun i hi => ?_⟩
  calc ∏ j : J, monoHom N z j ^ Tag.E6.cartan j i
      = ∏ j ∈ Jf, monoHom N z j ^ Tag.E6.cartan j i :=
        (Finset.prod_subtype Jf hJf fun j => monoHom N z j ^ Tag.E6.cartan j i).symm
    _ = monoHom M (monoHom N z) i := (monoHom_apply_of_mem hM _ ((hJf i).2 hi)).symm
    _ = y i := by rw [monoHom_monoHom, hMN, monoHom_diagonal, hz]

theorem eq_one_of_d5_solution [CharP L 2] {J : Set (Fin Tag.E6.rank)} [Fintype J]
    (hJ : J = {j | 1 ≤ j.val} ∨ J = {j | j.val ≤ 4}) {a : J → Lˣ}
    (ha : ∀ i ∈ J, ∏ j : J, a j ^ Tag.E6.cartan j i = 1) : a = 1 := by
  obtain ⟨Jf, hJf, hJ'⟩ := exists_d5_finset hJ
  obtain ⟨M, N, hM, -, hNM⟩ := d5_matrices hJ'
  have hsq : ∀ u : Lˣ, u ^ 2 = 1 → u = 1 := fun u hu =>
    Units.ext (CharTwo.sq_injective (by simpa using congrArg Units.val hu))
  let c : Fin Tag.E6.rank → Lˣ := fun k => if h : k ∈ Jf then a ⟨k, (hJf k).1 h⟩ else 1
  have h1 : monoHom M c = 1 := by
    funext i
    by_cases hi : i ∈ Jf
    · rw [monoHom_apply_of_mem hM c hi, Pi.one_apply, ← ha i ((hJf i).1 hi)]
      calc ∏ k ∈ Jf, c k ^ Tag.E6.cartan k i
          = ∏ k : J, c k ^ Tag.E6.cartan k i :=
            Finset.prod_subtype Jf hJf fun k => c k ^ Tag.E6.cartan k i
        _ = ∏ k : J, a k ^ Tag.E6.cartan k i :=
            Finset.prod_congr rfl fun k _ => by simp only [c, dif_pos ((hJf k).2 k.2)]
    · rw [monoHom_apply_of_notMem hM c hi, Pi.one_apply]
      simp only [c, dif_neg hi]
  funext j
  have h2 := congrFun (congrArg (monoHom N) h1) j
  rw [monoHom_monoHom, hNM, monoHom_diagonal, map_one, Pi.one_apply] at h2
  have h4 : c j ^ 4 = 1 := by simpa using h2
  have h5 : c j = 1 := hsq _ (hsq _ (by rw [← pow_mul]; exact h4))
  rw [Pi.one_apply]
  simpa only [c, dif_pos ((hJf j).2 j.2), Subtype.coe_eta] using h5

end D5

end CFSG.StandardType.TwE6D5Core
