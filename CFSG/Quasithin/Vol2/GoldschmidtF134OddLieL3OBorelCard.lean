module

public import CFSG.LieType.SteinbergBRTriangularSolvable

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SteinbergBR
open scoped MatrixGroups

@[expose] noncomputable def diagPair (K : Type) [Field K] :
    LinearFlag.upperTriangular 3 K →* Kˣ × Kˣ :=
  ((Pi.evalMonoidHom (fun _ : Fin 3 => Kˣ) 0).comp (upperDiagHom K 3)).prod
    ((Pi.evalMonoidHom (fun _ : Fin 3 => Kˣ) 1).comp (upperDiagHom K 3))

section Order

variable {K : Type} [Field K]

theorem ker_diagPair_le : (diagPair K).ker ≤ (upperDiagHom K 3).ker := by
  intro b hb
  rw [MonoidHom.mem_ker, diagPair, MonoidHom.prod_apply, Prod.mk_eq_one] at hb
  obtain ⟨h0, h1⟩ := hb
  have e0 : ((b : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := congrArg Units.val h0
  have e1 : ((b : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := congrArg Units.val h1
  have hdet : ((b : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).det = 1 := (b : SL(3, K)).2
  rw [Matrix.det_of_isUpperTriangular (LinearFlag.mem_upperTriangular_iff_isUpperTriangular.1 b.2),
    Fin.prod_univ_three, e0, e1, one_mul, one_mul] at hdet
  rw [MonoidHom.mem_ker]
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact Units.ext hdet

theorem card_upperTriangular_dvd [Finite K] :
    Nat.card (LinearFlag.upperTriangular 3 K) ∣ Nat.card K ^ 3 * (Nat.card K - 1) ^ 2 := by
  have hker : Nat.card (upperDiagHom K 3).ker = Nat.card K ^ 3 := by
    rw [ker_upperDiagHom, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (LinearFlag.unitriangular_le_upperTriangular 3 K)).toEquiv,
      LinearFlag.card_unitriangular]
  rw [← Subgroup.card_ker_mul_card_range (diagPair K)]
  refine mul_dvd_mul ?_ ?_
  · exact hker ▸ Subgroup.card_dvd_of_le ker_diagPair_le
  · calc Nat.card (diagPair K).range ∣ Nat.card (Kˣ × Kˣ) := Subgroup.card_subgroup_dvd_card _
      _ = (Nat.card K - 1) ^ 2 := by rw [Nat.card_prod, Nat.card_units, sq]

end Order

theorem card_dvd_of_le_upperTriangular {K : Type} [Field K] [Finite K]
    {B : Subgroup (LinearFlag.projectiveSL 3 K)}
    (hB : ∀ g : SL(3, K), LinearFlag.proj 3 K g ∈ B → g ∈ LinearFlag.upperTriangular 3 K) :
    Nat.card B ∣ Nat.card K ^ 3 * (Nat.card K - 1) ^ 2 := by
  have hle : B ≤ (LinearFlag.upperTriangular 3 K).map (LinearFlag.proj 3 K) := by
    intro x hx
    obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 K x
    exact ⟨g, hB g hx, rfl⟩
  exact ((Subgroup.card_dvd_of_le hle).trans (Subgroup.card_map_dvd _ _)).trans
    card_upperTriangular_dvd

end CFSG.Quasithin.H13.NQCore.L3Odd
