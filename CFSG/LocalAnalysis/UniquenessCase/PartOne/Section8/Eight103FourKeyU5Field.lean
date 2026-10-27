module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

private theorem phi_pow_four (h : UnitaryFieldData 2 2 K) (φ : K ≃+* K) : φ ^ 4 = 1 := by
  classical
  have hfin : Finite K := h.finite
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := h.charP
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let σ : K ≃ₐ[ZMod 2] K :=
    AlgEquiv.ofRingEquiv (f := φ) (by
      intro x
      have hcomm : (φ.toRingHom.comp (algebraMap (ZMod 2) K) : ZMod 2 →+* K) =
          algebraMap (ZMod 2) K := RingHom.ext_zmod _ _
      exact DFunLike.congr_fun hcomm x)
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 K σ
  have hcard2 : Nat.card (ZMod 2) = 2 := by simp
  have hφ_eq (x : K) : φ x = x ^ 2 ^ i := by
    rw [show φ x = σ x from rfl, hi x, hcard2]
  have hx16 (x : K) : x ^ 16 = x := by
    have hpow := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card] at hpow
    rw [h.card] at hpow
    norm_num at hpow
    exact hpow
  have hpow16 (x : K) (m : ℕ) : x ^ 16 ^ m = x := by
    induction m with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_mul, ih, hx16]
  have hφpow (k : ℕ) : ∀ y : K, (φ ^ k) y = y ^ 2 ^ (k * i) := by
    induction k with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, RingAut.mul_apply, ih, hφ_eq]
      rw [← pow_mul]
      congr 1
      ring
  ext x
  rw [hφpow]
  rw [show 2 ^ (4 * i) = 16 ^ i by rw [show 16 = 2^4 by norm_num, ← pow_mul]]
  exact hpow16 x i

theorem mem_range_uConjAut_five_of_pow_eq_one (h : UnitaryFieldData 2 2 K)
    {α : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K))} (hα : α ^ 5 = 1) :
    α ∈ (uConjAut h (n := 5) (by norm_num)).range := by
  obtain ⟨A, φ, hAφ⟩ := exists_uConjAut_mul_uFieldAut h (by norm_num) (by norm_num) α
  have hφ5 : φ ^ 5 = 1 := by
    have h1 := congrArg (uFactor h (by norm_num) (by norm_num)) hα
    rwa [hAφ, map_pow, uFactor_apply, map_one] at h1
  have hφ4 : φ ^ 4 = 1 := phi_pow_four h φ
  have hφ1 : φ = 1 := by
    have h := hφ5
    rw [show 5 = 4 + 1 by norm_num, pow_succ, hφ4, one_mul] at h
    exact h
  refine ⟨A, ?_⟩
  rw [hAφ, hφ1, map_one, mul_one]

private theorem scalar_mem_uU_iff_pow_five (h : UnitaryFieldData 2 2 K) (c : Kˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) ∈ uU h 5 ↔ c ^ 5 = 1 := by
  rw [mem_uU]
  have hbar_eq : h.bar (c : K) = (c : K) ^ 4 := by
    rw [h.bar_apply]
    norm_num
  have hmap : (((Matrix.GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K).map h.bar) =
      (Matrix.GeneralLinearGroup.scalar (Fin 5) (c ^ 4) : Matrix (Fin 5) (Fin 5) K) := by
    ext i j
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar]
    rw [Matrix.scalar_apply, Matrix.scalar_apply]
    rw [Matrix.map_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs with h
    · rw [hbar_eq, Units.val_pow_eq_pow_val]
    · simp
  rw [hmap]
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar]
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  constructor
  · intro hmat
    have h0 := congrFun (congrFun hmat 0) 0
    simp only [Matrix.diagonal_apply_eq] at h0
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    rw [pow_succ]
    exact h0
  · intro hc
    have hval : (c : K) ^ 5 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    have hval4 : (c : K) ^ 4 * (c : K) = 1 := by
      rw [pow_succ] at hval
      exact hval
    ext i j
    rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs
    · exact hval4
    · rfl

private def rootsOfUnityToUUScalars (h : UnitaryFieldData 2 2 K) :
    rootsOfUnity 5 K →* uU h 5 :=
  ((Matrix.GeneralLinearGroup.scalar (Fin 5)).comp (rootsOfUnity 5 K).subtype).codRestrict
    (uU h 5) fun c =>
      (scalar_mem_uU_iff_pow_five h (c : Kˣ)).2 ((mem_rootsOfUnity 5 (c : Kˣ)).1 c.property)

private theorem range_rootsOfUnityToUUScalars (h : UnitaryFieldData 2 2 K) :
    (rootsOfUnityToUUScalars h).range =
      CFSG.ClassicalGroups.UnitaryFlag.normOneScalars h (uU h 5) 5 := by
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    have hc5 : (c : Kˣ) ^ 5 = 1 := (mem_rootsOfUnity 5 (c : Kˣ)).1 c.property
    refine ⟨(c : Kˣ), ?_, hc5, rfl⟩
    have hval : ((c : Kˣ) : K) ^ 5 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc5, Units.val_one]
    rw [UnitaryFieldData.norm, h.bar_apply, show 2 ^ 2 = 4 by norm_num]
    calc
      ((c : Kˣ) : K) * ((c : Kˣ) : K) ^ 4 = ((c : Kˣ) : K) ^ 5 := by ring
      _ = 1 := hval
  · rintro ⟨c, hnorm, hc5, hg⟩
    exact ⟨⟨c, hc5⟩, Subtype.ext hg.symm⟩

private theorem ker_uConjAut_eq_normOneScalars (h : UnitaryFieldData 2 2 K) :
    (uConjAut h (n := 5) (by norm_num)).ker =
      CFSG.ClassicalGroups.UnitaryFlag.normOneScalars h (uU h 5) 5 := by
  ext g
  constructor
  · intro hg
    have hg' : uConjAut h (by norm_num) g = 1 := hg
    obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h (by norm_num) g).1 hg'
    have hc5 : c ^ 5 = 1 := by
      apply (scalar_mem_uU_iff_pow_five h c).1
      rw [← hc]
      exact g.property
    refine ⟨c, ?_, hc5, hc⟩
    have hval : (c : K) ^ 5 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc5, Units.val_one]
    rw [UnitaryFieldData.norm, h.bar_apply, show 2 ^ 2 = 4 by norm_num]
    calc
      (c : K) * (c : K) ^ 4 = (c : K) ^ 5 := by ring
      _ = 1 := hval
  · rintro ⟨c, hnorm, hc5, hg⟩
    change uConjAut h (by norm_num) g = 1
    rw [uConjAut_eq_one_iff h (by norm_num)]
    exact ⟨c, hg⟩

theorem card_ker_uConjAut_five (h : UnitaryFieldData 2 2 K) :
    Nat.card (uConjAut h (n := 5) (by norm_num)).ker = 5 := by
  let : Finite K := h.finite
  rw [ker_uConjAut_eq_normOneScalars h]
  rw [← range_rootsOfUnityToUUScalars h]
  have hinj : Function.Injective (rootsOfUnityToUUScalars h) := by
    intro x y hxy
    have hgl_eq : ((rootsOfUnityToUUScalars h x : uU h 5) : GL (Fin 5) K) =
        ((rootsOfUnityToUUScalars h y : uU h 5) : GL (Fin 5) K) :=
      congrArg (fun g : uU h 5 => (g : GL (Fin 5) K)) hxy
    have h00 := congrArg (fun M : GL (Fin 5) K => ((M : Matrix (Fin 5) (Fin 5) K) 0 0)) hgl_eq
    have hx : ((rootsOfUnityToUUScalars h x : uU h 5) : GL (Fin 5) K) =
        Matrix.GeneralLinearGroup.scalar (Fin 5) (x : Kˣ) := rfl
    have hy : ((rootsOfUnityToUUScalars h y : uU h 5) : GL (Fin 5) K) =
        Matrix.GeneralLinearGroup.scalar (Fin 5) (y : Kˣ) := rfl
    rw [hx, hy] at h00
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h00
    exact Subtype.ext (Units.ext h00)
  have hcard : Nat.card ((rootsOfUnityToUUScalars h).range) = Nat.card (rootsOfUnity 5 K) :=
    (Nat.card_congr (Equiv.ofInjective (rootsOfUnityToUUScalars h) hinj)).symm
  rw [hcard]
  rw [CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd 5]
  rw [h.card]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
