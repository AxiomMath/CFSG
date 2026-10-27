module

public import CFSG.RankThree.SubgroupLists.RationalElements
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix Equiv

variable {K : Type*} [Field K]

theorem trace_ne_trace_sq_of_rational_five (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    {x : GL (Fin 3) K} (hdet : (x : Matrix (Fin 3) (Fin 3) K).det = 1) (hx5 : x ^ 5 = 1)
    (hx1 : x ≠ 1) (hconj : IsConj x (x ^ 4)) :
    (x : Matrix (Fin 3) (Fin 3) K).trace ≠ ((x : Matrix (Fin 3) (Fin 3) K) ^ 2).trace := by
  intro htr
  set t := (x : Matrix (Fin 3) (Fin 3) K).trace with ht
  have E1 : (2 * t - 1) ^ 2 = 5 := sq_two_mul_trace_sub_one_eq_five hdet hx5 hx1 h5 hconj
  have hinv : ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = t := by
    rw [trace_inv_eq_trace_pow x (n := 4) hx5, ← coe_pow_trace, ← trace_eq_of_isConj hconj]
  have E2 : t ^ 2 = 3 * t := by
    have h := trace_sq_sl3 x hdet
    rw [← htr, hinv, ← ht] at h
    linear_combination -h
  have e1 : 8 * t = 4 := by linear_combination E1 - 4 * E2
  have e2 : (16 : K) * 5 = 0 := by linear_combination (8 * t - 20) * e1 - 64 * E2
  have h16 : (16 : K) ≠ 0 := by
    have : (16 : K) = 2 ^ 4 := by norm_num
    rw [this]
    exact pow_ne_zero 4 h2
  exact h5 ((mul_eq_zero.mp e2).resolve_left h16)

@[expose] def cycleFive : alternatingGroup (Fin 5) :=
  ⟨finRotate 5, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def invertFive : alternatingGroup (Fin 5) :=
  ⟨swap 1 4 * swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def squareFive : Perm (Fin 5) := swap 1 2 * swap 2 4 * swap 4 3

theorem invertFive_conj : invertFive * cycleFive * invertFive⁻¹ = cycleFive ^ 4 :=
  Subtype.ext (by decide)

theorem squareFive_conj :
    squareFive * (cycleFive : Perm (Fin 5)) * squareFive⁻¹ = (cycleFive : Perm (Fin 5)) ^ 2 := by
  decide

theorem sign_squareFive : Perm.sign squareFive = -1 := by decide

theorem cycleFive_pow_five : cycleFive ^ 5 = 1 := Subtype.ext (by decide)

theorem cycleFive_ne_one : cycleFive ≠ 1 := fun h => by
  have := congrArg Subtype.val h
  revert this
  decide

theorem exists_eq_mul_scalar_of_normalizes (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    {H : Subgroup (GL (Fin 3) K)}
    (hscal : ∀ M : Matrix (Fin 3) (Fin 3) K,
      (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K) * M = M * x) →
        ∃ c : K, M = Matrix.scalar (Fin 3) c)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (φ : H ≃* alternatingGroup (Fin 5)) {g : GL (Fin 3) K} (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hg' : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    ∃ h ∈ H, ∃ c : K, (g : Matrix (Fin 3) (Fin 3) K) =
      (h : Matrix (Fin 3) (Fin 3) K) * Matrix.scalar (Fin 3) c := by
  classical
  let α : MulAut H :=
    { toFun := fun x => ⟨g * x * g⁻¹, hg x x.2⟩
      invFun := fun x => ⟨g⁻¹ * x * g, hg' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hα : ∀ x : H, ((α x : H) : GL (Fin 3) K) = g * x * g⁻¹ := fun x => rfl
  let α' : MulAut (alternatingGroup (Fin 5)) := (φ.symm.trans α).trans φ
  have hα' : ∀ y, α' y = φ (α (φ.symm y)) := fun y => rfl
  obtain ⟨π, hπ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
      (by norm_num)).2 α'
  have key : ∀ y : alternatingGroup (Fin 5),
      ((α' y : alternatingGroup (Fin 5)) : Perm (Fin 5)) = π * y * π⁻¹ := by
    intro y
    rw [← hπ, MulAut.conjNormal_apply]
  set ι : alternatingGroup (Fin 5) →* GL (Fin 3) K := H.subtype.comp φ.symm.toMonoidHom with hι
  set X : GL (Fin 3) K := ι cycleFive with hX
  have hXdet : (X : Matrix (Fin 3) (Fin 3) K).det = 1 := hdet _ (φ.symm cycleFive).2
  have hX5 : X ^ 5 = 1 := by rw [hX, ← map_pow, cycleFive_pow_five, map_one]
  have hX1 : X ≠ 1 := by
    intro h
    apply cycleFive_ne_one
    apply φ.symm.injective
    apply Subtype.ext
    rw [map_one]
    exact h
  have hιconj : ∀ y s : alternatingGroup (Fin 5), IsConj (ι y) (ι (s * y * s⁻¹)) := fun y s =>
    ι.map_isConj (isConj_iff.mpr ⟨s, rfl⟩)
  have hX4 : IsConj X (X ^ 4) := by
    have h := hιconj cycleFive invertFive
    rwa [invertFive_conj, map_pow] at h
  have htr := trace_ne_trace_sq_of_rational_five h2 h5 hXdet hX5 hX1 hX4
  have hπeven : Perm.sign π = 1 := by
    by_contra hodd
    have hπ1 : Perm.sign π = -1 := (Int.units_eq_one_or _).resolve_left hodd
    set σ : alternatingGroup (Fin 5) := ⟨π * squareFive⁻¹, Equiv.Perm.mem_alternatingGroup.mpr
      (by rw [Perm.sign_mul, Perm.sign_inv, hπ1, sign_squareFive]; rfl)⟩ with hσ
    have hc : α' cycleFive = σ * cycleFive ^ 2 * σ⁻¹ := by
      apply Subtype.ext
      rw [key, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hσ,
        ← squareFive_conj]
      simp only
      group
    have h1 : g * X * g⁻¹ = ι (σ * cycleFive ^ 2 * σ⁻¹) := by
      rw [← hc, hα']
      simp only [hι, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply, Subgroup.coe_subtype]
      rfl
    have h2' : IsConj X (g * X * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
    have h3 : IsConj (X ^ 2) (g * X * g⁻¹) := by
      rw [h1]
      have := hιconj (cycleFive ^ 2) σ
      rwa [map_pow] at this
    apply htr
    rw [trace_eq_of_isConj h2', ← trace_eq_of_isConj h3, coe_pow_trace]
  set π' : alternatingGroup (Fin 5) := ⟨π, Equiv.Perm.mem_alternatingGroup.mpr hπeven⟩
  set h : H := φ.symm π' with hh
  have hαh : ∀ x : H, α x = h * x * h⁻¹ := by
    intro x
    apply φ.injective
    have h1 : φ (α x) = α' (φ x) := by rw [hα', MulEquiv.symm_apply_apply]
    rw [h1]
    apply Subtype.ext
    rw [key, map_mul, map_mul, map_inv, hh, MulEquiv.apply_symm_apply]
    rfl
  have hcent : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K) *
      (((h : GL (Fin 3) K)⁻¹ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((h : GL (Fin 3) K)⁻¹ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x := by
    intro x hx
    have e1 : g * x * g⁻¹ = (h : GL (Fin 3) K) * x * (h : GL (Fin 3) K)⁻¹ := by
      have := congrArg Subtype.val (hαh ⟨x, hx⟩)
      rw [hα] at this
      exact this
    have e2 : x * ((h : GL (Fin 3) K)⁻¹ * g) = ((h : GL (Fin 3) K)⁻¹ * g) * x := by
      calc x * ((h : GL (Fin 3) K)⁻¹ * g)
          = (h : GL (Fin 3) K)⁻¹ * ((h : GL (Fin 3) K) * x * (h : GL (Fin 3) K)⁻¹) * g := by
            group
        _ = (h : GL (Fin 3) K)⁻¹ * (g * x * g⁻¹) * g := by rw [e1]
        _ = ((h : GL (Fin 3) K)⁻¹ * g) * x := by group
    rw [← Units.val_mul, e2, Units.val_mul]
  obtain ⟨c, hc⟩ := hscal _ hcent
  refine ⟨h, h.2, c, ?_⟩
  rw [← hc, ← Units.val_mul, mul_inv_cancel_left]

end CFSG.RankThree.SubgroupLists
