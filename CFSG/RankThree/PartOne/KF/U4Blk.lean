module

public import CFSG.RankThree.PartOne.KC.UnitaryCoordBlocks

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryCoord

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] noncomputable def blk {i j : Fin n} (hij : i ≠ j) : Subgroup (GL (Fin n) K) :=
  (coordSU h hij).map (primeFormUnitary h (idGram K n)).subtype

variable {h}

theorem mem_blk_iff {i j : Fin n} (hij : i ≠ j) {g : GL (Fin n) K} :
    g ∈ blk h hij ↔ ∃ X : GL (Fin 2) K, X ∈ gramSU h (idGram K 2) ∧
      (g : Matrix (Fin n) (Fin n) K) = coordEmbed K i j (X : Matrix (Fin 2) (Fin 2) K) := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨X, hX, hXA⟩ := (mem_coordSU_iff h hij).mp hA
    exact ⟨X, hX, hXA⟩
  · rintro ⟨X, hX, hg⟩
    have hU : g ∈ primeFormUnitary h (idGram K n) := by
      have hu := coordEmbed_mem_primeFormUnitary h hij ((mem_gramSU_iff_unitary h).mp hX).1
      convert hu using 1
      exact Units.ext hg
    refine ⟨⟨g, hU⟩, ?_, rfl⟩
    exact (mem_coordSU_iff h hij).mpr ⟨X, hX, hg⟩

theorem det_coordEmbed {i j : Fin n} (hij : i ≠ j) (X : Matrix (Fin 2) (Fin 2) K) :
    (coordEmbed K i j X).det = X.det := by
  unfold coordEmbed
  rw [Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc (X - 1) (coordProj K i j),
    coordProj_mul_coordIncl hij, Matrix.mul_one]
  simp

theorem blk_le_unitarySU {i j : Fin n} (hij : i ≠ j) : blk h hij ≤ unitarySU 2 f K n := by
  intro g hg
  obtain ⟨X, hX, hgX⟩ := (mem_blk_iff hij).mp hg
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [hgX, det_coordEmbed hij, ((mem_gramSU_iff_unitary h).mp hX).2]
  · have hU : g ∈ primeFormUnitary h (idGram K n) := by
      obtain ⟨A, -, rfl⟩ := hg
      exact A.2
    have := mem_primeFormUnitary.mp hU
    simpa [idGram] using this

end CFSG.RankThree.PartOne.KFU
