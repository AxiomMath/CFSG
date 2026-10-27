module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r ε : ℕ}

theorem hypSU_ext' {g g' : hypSU h r ε}
    (e : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      ((g' : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) : g = g' :=
  Subtype.ext (Units.ext e)

theorem hypTorus_comm {a b : hypSU h r ε} (ha : a ∈ hypTorus h r ε) (hb : b ∈ hypTorus h r ε) :
    a * b = b * a := by
  obtain ⟨a₁, d₁, -, -, h₁⟩ := ha
  obtain ⟨a₂, d₂, -, -, h₂⟩ := hb
  apply hypSU_ext'
  change ((a : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      ((b : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
    ((b : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      ((a : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
  rw [h₁, h₂, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _

theorem hypTorus_le_normalizer (hr : 1 ≤ r) (hε : ε ≤ 1) :
    hypTorus h r ε ≤ Subgroup.normalizer (hypUnitriangular h r ε : Set (hypSU h r ε)) := by
  rw [UnitaryHigher.normalizer_hypUnitriangular h hr hε]
  exact hypTorus_le_hypBorel h

theorem hypUnitriangular_inf_hypTorus {x : hypSU h r ε} (hx : x ∈ hypUnitriangular h r ε)
    (hxT : x ∈ hypTorus h r ε) : x = 1 := by
  obtain ⟨a, d, -, -, hg⟩ := hxT
  have hd := (mem_hypUnitriangular.1 hx).2
  apply hypSU_ext'
  have e : torusEntries h a d = fun _ => 1 := funext fun y => by
    have := hd y
    rwa [hg, diagonal_apply_eq] at this
  change ((x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
    ((1 : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
  rw [hg, e, Units.val_one, ← diagonal_one]

theorem exists_mem_hypTorus_diag (hε : ε ≤ 1) {a : Fin r → Kˣ}
    (ha : a ∈ (hypDiagHom h r ε hε).range) (hr : 1 ≤ r) :
    ∃ (t : hypSU h r ε) (htB : t ∈ hypBorel h r ε), t ∈ hypTorus h r ε ∧
      hypDiagHom h r ε hε ⟨t, htB⟩ = a := by
  have key : ∀ {d : Fin ε → Kˣ} (hd : ∀ k, h.norm (d k : K) = 1) (hp : torusRatio h a d = 1),
      ∃ (t : hypSU h r ε) (htB : t ∈ hypBorel h r ε), t ∈ hypTorus h r ε ∧
        hypDiagHom h r ε hε ⟨t, htB⟩ = a := by
    intro d hd hp
    obtain ⟨t, htT, ht⟩ := torusMat_mem_hypSU h a hd hp
    refine ⟨t, hypTorus_le_hypBorel h htT, htT, funext fun i => Units.ext ?_⟩
    rw [coe_hypDiagHom]
    change ((t : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl i) (.inl i)
      = _
    rw [ht, diagonal_apply_eq]
    rfl
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [range_hypDiagHom_even, mem_evenDiagGroup] at ha
    refine key (d := isEmptyElim) (fun k => isEmptyElim k) ?_
    have e0 : ∏ k : Fin 0, (((isEmptyElim k : Kˣ)) : K) = 1 := Fin.prod_univ_zero _
    rw [torusRatio, e0, mul_one]
    exact ha
  · have hnorm : h.norm ((ratioHom h r a)⁻¹ : Kˣ) = 1 := by
      have : ratioHom h r a ∈ (Units.map h.normHom).ker := by
        rw [← range_ratioHom hr]
        exact ⟨a, rfl⟩
      rw [UnitaryFieldData.mem_ker_normUnits] at this
      rw [Units.val_inv_eq_inv_val, norm_inv_eq h, this, inv_one]
    refine key (d := fun _ => (ratioHom h r a)⁻¹) (fun _ => hnorm) ?_
    rw [torusRatio, ← coe_ratioHom, Fin.prod_univ_one, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]

theorem normalizer_eq_mul (hr : 1 ≤ r) (hε : ε ≤ 1) {g : hypSU h r ε}
    (hg : g ∈ Subgroup.normalizer (hypUnitriangular h r ε : Set (hypSU h r ε))) :
    ∃ u ∈ hypUnitriangular h r ε, ∃ t ∈ hypTorus h r ε, g = u * t := by
  rw [UnitaryHigher.normalizer_hypUnitriangular h hr hε] at hg
  obtain ⟨t, htB, htT, ht⟩ := exists_mem_hypTorus_diag h hε
    (a := hypDiagHom h r ε hε ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩ hr
  have hk : (⟨g, hg⟩ : hypBorel h r ε) * (⟨t, htB⟩ : hypBorel h r ε)⁻¹ ∈
      (hypDiagHom h r ε hε).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ht, mul_inv_cancel]
  rw [ker_hypDiagHom hε, Subgroup.mem_subgroupOf] at hk
  refine ⟨g * t⁻¹, hk, t, htT, ?_⟩
  group

end CFSG.Quasithin.H13.Sec53F.Unit
