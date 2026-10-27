module

public import CFSG.RankThree.SubgroupLists.QuasisimpleLayer

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.RepresentationTheory

variable {K : Type*} [Field K] [Finite K]

theorem exists_characteristic_extraspecial_gl3_of_solvable
    {J : Subgroup (GL (Fin 3) K)}
    (hJ : IsIrreducibleMatrixRep J.subtype)
    (hsolv : Group.IsSolvable J)
    (hnorm : ∀ N : Subgroup (GL (Fin 3) K),
      (∀ g ∈ J, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
      IsIrreducibleMatrixRep N.subtype ∨
        ∀ x ∈ N, ∃ c : K,
          (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    (habel : ∀ N ≤ J,
      (∀ g ∈ J, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
      (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) →
      ∀ x ∈ N, ∃ c : K,
        (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c) :
    3 ∣ Nat.card K - 1 ∧
      ∃ H ≤ J,
        (∀ g ∈ J, ∀ x ∈ H, g * x * g⁻¹ ∈ H) ∧
        (H.subgroupOf J).Characteristic ∧
        IsIrreducibleMatrixRep H.subtype ∧
        Nat.card H = 3 ^ 3 ∧
        IsExtraspecialPGroup 3 H ∧
        (∀ x : GL (Fin 3) K,
          x ∈ H ↔ x ∈ (CFSG.pCore 3 J).map J.subtype ∧ x ^ 3 = 1) := by
  classical
  have hcore_exists : ∃ r : ℕ, r.Prime ∧
      ∃ x ∈ (CFSG.pCore r J).map J.subtype,
        ∀ c : K, (x : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c := by
    by_contra h
    have hcore_scalar : ∀ (r : ℕ), r.Prime → ∀ x : GL (Fin 3) K,
        x ∈ (CFSG.pCore r J).map J.subtype →
        ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
      intro r hr x hx
      by_contra hc
      rw [not_exists] at hc
      exact h ⟨r, hr, x, hx, hc⟩
    have hcore : ∀ r : ℕ, r.Prime → ∀ R ≤ J,
        (∀ g ∈ J, ∀ x ∈ R, g * x * g⁻¹ ∈ R) → IsPGroup r R →
        ∀ x ∈ R, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
      intro r hr R hRJ hRn hRp x hx
      have hRj_normal : (R.subgroupOf J).Normal :=
        Subgroup.Normal.mk fun y hy g =>
          Subgroup.mem_subgroupOf.mpr (by
            simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
              hRn g g.2 (y : GL (Fin 3) K) (Subgroup.mem_subgroupOf.mp hy))
      have hRj_p : IsPGroup r (R.subgroupOf J) :=
        hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRJ).symm
      have hle : R.subgroupOf J ≤ CFSG.pCore r J := le_sSup ⟨hRj_normal, hRj_p⟩
      have hxcore : x ∈ (CFSG.pCore r J).map J.subtype := by
        have hxmap : x ∈ (R.subgroupOf J).map J.subtype := by
          rw [Subgroup.map_subgroupOf_eq_of_le hRJ]
          exact hx
        exact Subgroup.map_mono hle hxmap
      exact hcore_scalar r hr x hxcore
    obtain ⟨Q, hQJ, _hQn, hQ, _hQirr, _hQscal, _hQdet, _hQcenter⟩ :=
      exists_quasisimple_normal_gl3 hJ hnorm hcore
    have hQsolv : Group.IsSolvable Q :=
      @Group.isSolvable_of_isSolvable_injective Q J _ _ (Subgroup.inclusion hQJ)
        (Subgroup.inclusion_injective hQJ) hsolv
    have hQperfect : Group.IsPerfect Q := hQ.1
    have hQnontrivial : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
    exact @Group.IsPerfect.not_isSolvable Q _ hQnontrivial hQperfect hQsolv
  obtain ⟨r, hr, x, hxcore, hxns⟩ := hcore_exists
  obtain ⟨hr3, hK3, H, hHJ, hHn, hHirr, hHcard, hHex, hcarrier⟩ :=
    normal_pGroup_extraspecial_gl3_with_carrier (K := K) (hr := ⟨hr⟩) hnorm habel
      (R := (CFSG.pCore r J).map J.subtype)
      (Subgroup.map_subtype_le _)
      (map_subtype_conj_mem (CFSG.pCore r J))
      ((CFSG.pCore_isPGroup (p := r) (G := J)).map J.subtype)
      ⟨x, hxcore, hxns⟩
  have hcarrier3 : ∀ x : GL (Fin 3) K,
      x ∈ H ↔ x ∈ (CFSG.pCore 3 J).map J.subtype ∧ x ^ 3 = 1 := by
    intro x
    simpa only [hr3] using hcarrier x
  have hcarrierJ : ∀ x : J, x ∈ H.subgroupOf J ↔
      x ∈ CFSG.pCore 3 J ∧ x ^ 3 = 1 := by
    intro x
    rw [Subgroup.mem_subgroupOf, hcarrier3 (x : GL (Fin 3) K)]
    constructor
    · rintro ⟨hxcore, hx3⟩
      constructor
      · obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxcore
        have hyx' : y = x := Subtype.ext hyx
        simpa only [hyx'] using hy
      · apply Subtype.ext
        simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using hx3
    · rintro ⟨hxcore, hx3⟩
      refine ⟨Subgroup.mem_map.mpr ⟨x, hxcore, rfl⟩, ?_⟩
      have hx3' := congrArg (fun y : J => (y : GL (Fin 3) K)) hx3
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using hx3'
  have hHchar : (H.subgroupOf J).Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro φ y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    have hz' := (hcarrierJ z).mp hz
    refine (hcarrierJ (φ z)).mpr ⟨?_, ?_⟩
    · rw [← CFSG.pCore_map_iso 3 φ]
      exact Subgroup.mem_map.mpr ⟨z, hz'.1, rfl⟩
    · calc (φ z) ^ 3 = φ (z ^ 3) := (map_pow φ z 3).symm
        _ = φ 1 := by rw [hz'.2]
        _ = 1 := map_one φ
  exact ⟨hK3, H, hHJ, hHn, hHchar, hHirr, hHcard, hHex, hcarrier3⟩

end CFSG.RankThree.SubgroupLists
