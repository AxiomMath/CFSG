module

public import CFSG.RankThree.SubgroupLists.CharacteristicExtraspecial
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.StronglyEmbedded.SteinbergBSPrimeFixedPointFreeNilpotent

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.RepresentationTheory

variable {K : Type*} [Field K] [Finite K]

theorem exists_extraspecial_gl3_of_odd_of_normalized
    {A : Type*} [Group A]
    (α : A →* MulAut (GL (Fin 3) K))
    {J Z : Subgroup (GL (Fin 3) K)}
    (hJ : IsIrreducibleMatrixRep J.subtype)
    (hodd : Odd (Nat.card J))
    (hnorm : ∀ N : Subgroup (GL (Fin 3) K),
      (∀ g ∈ J, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
      IsIrreducibleMatrixRep N.subtype ∨
        ∀ x ∈ N, ∃ c : K,
          (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    (habel : ∀ N ≤ J,
      (∀ g ∈ J, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
      (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) →
      ∀ x ∈ N, ∃ c : K,
        (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    (hAJ : ∀ a : A, J.map (α a).toMonoidHom = J)
    (hZJ : Z ≤ J)
    (hZscalar : ∀ z ∈ Z, ∃ c : K,
      (z : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    (hZcube : ∀ z ∈ Z, z ^ 3 = 1) :
    3 ∣ Nat.card K - 1 ∧
      ∃ H ≤ J,
        Z ≤ H ∧
        (H.subgroupOf J).Characteristic ∧
        (∀ a : A, H.map (α a).toMonoidHom = H) ∧
        IsIrreducibleMatrixRep H.subtype ∧
        Nat.card H = 3 ^ 3 ∧
        IsExtraspecialPGroup 3 H ∧
        (∀ x ∈ H, x ^ 3 = 1) ∧
        (∀ x : GL (Fin 3) K,
          x ∈ H ↔ x ∈ (CFSG.pCore 3 J).map J.subtype ∧ x ^ 3 = 1) := by
  classical
  have hsolv : Group.IsSolvable J := CFSG.FeitThompson.isSolvable_of_odd_natCard (G := J) hodd
  obtain ⟨hK3, H, hHJ, _hHn, hHchar, hHirr, hHcard, hHex, hcarrier⟩ :=
    exists_characteristic_extraspecial_gl3_of_solvable hJ hsolv hnorm habel
  have hZJcenter : Z.subgroupOf J ≤ Subgroup.center J := by
    intro z hz
    obtain ⟨c, hc⟩ := hZscalar (z : GL (Fin 3) K) (Subgroup.mem_subgroupOf.mp hz)
    exact mem_center_of_scalar (G := J) (x := z) hc
  have hZJnormal : (Z.subgroupOf J).Normal := Subgroup.normal_of_le_center hZJcenter
  have hZJcube : ∀ z : Z.subgroupOf J, z ^ 3 = 1 := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    have hzZ : ((z : J) : GL (Fin 3) K) ∈ Z := Subgroup.mem_subgroupOf.mp z.2
    have hz3 := hZcube ((z : J) : GL (Fin 3) K) hzZ
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using hz3
  have hZJp : IsPGroup 3 (Z.subgroupOf J) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro z
    exact ⟨1, by simpa using hZJcube z⟩
  have hZJcore : Z.subgroupOf J ≤ CFSG.pCore 3 J := le_sSup ⟨hZJnormal, hZJp⟩
  have hZH : Z ≤ H := by
    intro z hz
    have hzcore : z ∈ (CFSG.pCore 3 J).map J.subtype := by
      have hzmap : z ∈ (Z.subgroupOf J).map J.subtype := by
        rw [Subgroup.map_subgroupOf_eq_of_le hZJ]
        exact hz
      exact Subgroup.map_mono hZJcore hzmap
    exact (hcarrier z).mpr ⟨hzcore, hZcube z hz⟩
  have hHcube : ∀ x ∈ H, x ^ 3 = 1 := fun x hx => ((hcarrier x).mp hx).2
  have hHinv : ∀ a : A, H.map (α a).toMonoidHom = H := by
    intro a
    have h := CFSG.StronglyEmbedded.map_map_subtype_eq_of_characteristic
      (α := α a) (P := J) (hP := hAJ a) (K := H.subgroupOf J) (hK := hHchar)
    rwa [Subgroup.map_subgroupOf_eq_of_le hHJ] at h
  exact ⟨hK3, H, hHJ, hZH, hHchar, hHinv, hHirr, hHcard, hHex, hHcube, hcarrier⟩

end CFSG.RankThree.SubgroupLists
