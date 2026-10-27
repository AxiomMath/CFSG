module

public import CFSG.RankThree.PartOne.KF.F132K0Proof

public section

namespace CFSG.RankThree.PartOne.K1320X

open Matrix
open scoped commutatorElement

section SL2

variable {F : Type} [Field F]

@[expose] def transv (v : Fin 2 → F) (a : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1 - a * v 0 * v 1, a * v 0 * v 0; -(a * v 1 * v 1), 1 + a * v 0 * v 1], by
    rw [Matrix.det_fin_two_of]; ring⟩

theorem transv_apply (v : Fin 2 → F) (a : F) :
    (transv v a : Matrix (Fin 2) (Fin 2) F) =
      !![1 - a * v 0 * v 1, a * v 0 * v 0; -(a * v 1 * v 1), 1 + a * v 0 * v 1] := rfl

theorem transv_zero (v : Fin 2 → F) : transv v 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transv_apply]

theorem transv_mul (v : Fin 2 → F) (a b : F) : transv v a * transv v b = transv v (a + b) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transv_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem transv_inv (v : Fin 2 → F) (a : F) : (transv v a)⁻¹ = transv v (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [transv_mul, add_neg_cancel, transv_zero]

theorem conj_transv {v : Fin 2 → F} {ν : F} (y : Matrix.SpecialLinearGroup (Fin 2) F)
    (hy : (y : Matrix (Fin 2) (Fin 2) F).mulVec v = ν • v) (a : F) :
    y * transv v a * y⁻¹ = transv v (ν ^ 2 * a) := by
  have hdet : (y : Matrix (Fin 2) (Fin 2) F).det = 1 := y.2
  rw [Matrix.det_fin_two] at hdet
  have h0 := congrFun hy 0
  have h1 := congrFun hy 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at h0 h1
  have W1 : ν * (-(v 1 * (y : Matrix (Fin 2) (Fin 2) F) 0 0) +
      v 0 * (y : Matrix (Fin 2) (Fin 2) F) 1 0) = -(v 1) := by
    linear_combination ((y : Matrix (Fin 2) (Fin 2) F) 0 0) * h1 -
      ((y : Matrix (Fin 2) (Fin 2) F) 1 0) * h0 - (v 1) * hdet
  have W2 : ν * (-(v 1 * (y : Matrix (Fin 2) (Fin 2) F) 0 1) +
      v 0 * (y : Matrix (Fin 2) (Fin 2) F) 1 1) = v 0 := by
    linear_combination ((y : Matrix (Fin 2) (Fin 2) F) 0 1) * h1 -
      ((y : Matrix (Fin 2) (Fin 2) F) 1 1) * h0 + (v 0) * hdet
  have key : y * transv v a = transv v (ν ^ 2 * a) * y := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transv_apply, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-(a * v 1)) * h0 + (-(a * ν * v 0)) * W1
    · linear_combination (a * v 0) * h0 - (ν * a * v 0) * W2
    · linear_combination (-(a * v 1)) * h1 + (-(ν * a * v 1)) * W1
    · linear_combination (a * v 0) * h1 - (ν * a * v 1) * W2
  exact (mul_inv_eq_iff_eq_mul).2 key

@[expose] def transvGroup (v : Fin 2 → F) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) where
  carrier := Set.range (transv v)
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, (transv_mul v a b).symm⟩
  one_mem' := ⟨0, transv_zero v⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, (transv_inv v a).symm⟩

theorem transv_mem (v : Fin 2 → F) (a : F) : transv v a ∈ transvGroup v := ⟨a, rfl⟩

theorem transv_ne_one {v : Fin 2 → F} (hv : v ≠ 0) : transv v 1 ≠ 1 := by
  intro h
  have h1 := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  have h2 := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 1 0) h
  simp [transv_apply] at h1 h2
  apply hv
  ext i
  fin_cases i <;> simp [h1, h2]

theorem isPGroup_transvGroup [CharP F 2] (v : Fin 2 → F) : IsPGroup 2 (transvGroup v) := by
  intro g
  obtain ⟨a, ha⟩ := g.2
  have h2 : g ^ 2 = 1 := by
    apply Subtype.ext
    show ((g : Matrix.SpecialLinearGroup (Fin 2) F)) ^ 2 = 1
    rw [← ha, pow_two, transv_mul, CharTwo.add_self_eq_zero, transv_zero]
  exact ⟨1, by simpa using h2⟩

theorem inv_mulVec_eigen {v : Fin 2 → F} {ν : F} (hν : ν ≠ 0)
    (y : Matrix.SpecialLinearGroup (Fin 2) F)
    (hy : (y : Matrix (Fin 2) (Fin 2) F).mulVec v = ν • v) :
    ((y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v =
      ν⁻¹ • v := by
  have h1 : ((y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
      ((y : Matrix (Fin 2) (Fin 2) F).mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [hy, Matrix.mulVec_smul] at h1
  calc ((y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v
      = ν⁻¹ • (ν • ((y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F).mulVec v) := by
        rw [smul_smul, inv_mul_cancel₀ hν, one_smul]
    _ = ν⁻¹ • v := by rw [h1]

theorem mem_normalizer_transvGroup {v : Fin 2 → F} {ν : F} (hν : ν ≠ 0)
    {y : Matrix.SpecialLinearGroup (Fin 2) F}
    (hy : (y : Matrix (Fin 2) (Fin 2) F).mulVec v = ν • v) :
    y ∈ Subgroup.normalizer ((transvGroup v : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
      Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨a, rfl⟩
    rw [conj_transv y hy a]
    exact transv_mem v _
  · rintro ⟨b, hb⟩
    have hy' := inv_mulVec_eigen hν y hy
    have h2 := conj_transv (y⁻¹) hy' b
    have hh : h = y⁻¹ * transv v b * (y⁻¹)⁻¹ := by
      rw [hb]; group
    rw [hh, h2]
    exact transv_mem v _

theorem transvGroup_le_commutator {v : Fin 2 → F} {ν : F} (hν1 : ν ^ 2 ≠ 1)
    {y : Matrix.SpecialLinearGroup (Fin 2) F}
    (hy : (y : Matrix (Fin 2) (Fin 2) F).mulVec v = ν • v) :
    transvGroup v ≤ ⁅transvGroup v, Subgroup.zpowers y⁆ := by
  rintro _ ⟨c, rfl⟩
  have hne : (1 : F) - ν ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hν1)
  set b : F := (1 - ν ^ 2)⁻¹ * c with hb
  have e1 : ⁅transv v b, y⁆ = transv v b * (y * transv v (-b) * y⁻¹) := by
    rw [commutatorElement_def, transv_inv]; group
  have e2 : ⁅transv v b, y⁆ = transv v c := by
    rw [e1, conj_transv y hy, transv_mul]
    congr 1
    rw [hb]
    field_simp
    ring
  rw [← e2]
  exact Subgroup.commutator_mem_commutator (transv_mem v b) (Subgroup.mem_zpowers y)

theorem exists_transvGroup [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card F - 1) {y : Matrix.SpecialLinearGroup (Fin 2) F} (hy1 : y ≠ 1)
    (hyp : y ^ p = 1) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧
      y ∈ Subgroup.normalizer ((transvGroup v : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      transvGroup v ≤ ⁅transvGroup v, Subgroup.zpowers y⁆ := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    exact hpF
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζ : IsPrimitiveRoot (z : F) p := by
    have := IsPrimitiveRoot.orderOf z
    rw [hz] at this
    exact IsPrimitiveRoot.coe_units_iff.2 this
  have hM : (y : Matrix (Fin 2) (Fin 2) F) ^ p = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hyp, Matrix.SpecialLinearGroup.coe_one]
  have hM1 : (y : Matrix (Fin 2) (Fin 2) F) ≠ 1 := fun h =>
    hy1 (Subtype.ext (h.trans Matrix.SpecialLinearGroup.coe_one.symm))
  obtain ⟨ν, hνp, hν1, v, hv0, hv⟩ :=
    CFSG.RankThree.PartOne.KFK0.exists_eigenvector_of_pow_eq_one hp.pos hζ hM hM1
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hνp
    exact zero_ne_one hνp
  have hν2 : ν ^ 2 ≠ 1 := by
    intro h
    apply hν1
    have h2 : (ν - 1) ^ 2 = 0 := by
      rw [CharTwo.sub_eq_add, CharTwo.add_sq, h, one_pow, CharTwo.add_self_eq_zero]
    exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h2)
  exact ⟨v, hv0, mem_normalizer_transvGroup hν0 hv, transvGroup_le_commutator hν2 hv⟩

end SL2

theorem exists_twoSub_of_psl2 {G : Type} [Group G] {K : Subgroup G} {g p : ℕ} (hp : p.Prime)
    (hmod : Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 2 2 g)
    (hpg : p ∣ 2 ^ g - 1) {x : G} (hxK : x ∈ K) (hx1 : x ≠ 1) (hxp : x ^ p = 1) :
    ∃ S : Subgroup G, S ≤ K ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ x ∈ Subgroup.normalizer (S : Set G) ∧
      S ≤ ⁅S, Subgroup.zpowers x⁆ := by
  classical
  obtain ⟨F, hF, hFin, hchar, hcard, ⟨ψ⟩⟩ := KF132.exists_SL2_equiv hmod
  set φ : Matrix.SpecialLinearGroup (Fin 2) F →* G := K.subtype.comp ψ.toMonoidHom with hφ
  have hφinj : Function.Injective φ := K.subtype_injective.comp ψ.injective
  set y : Matrix.SpecialLinearGroup (Fin 2) F := ψ.symm ⟨x, hxK⟩ with hy
  have hφy : φ y = x := by
    simp [hφ, hy]
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1
    rw [← hφy, h, map_one]
  have hyp : y ^ p = 1 := by
    apply hφinj
    rw [map_pow, hφy, hxp, map_one]
  have hpF : p ∣ Nat.card F - 1 := by rw [hcard]; exact hpg
  obtain ⟨v, hv0, hvn, hvc⟩ := exists_transvGroup hp hpF hy1 hyp
  set S₀ := transvGroup v with hS₀
  refine ⟨S₀.map φ, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact (ψ a).2
  · intro h
    have h1 : φ (transv v 1) ∈ S₀.map φ := ⟨_, transv_mem v 1, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one φ] at h1
    exact transv_ne_one hv0 (hφinj h1)
  · exact (isPGroup_transvGroup v).of_surjective (φ.subgroupMap S₀) (φ.subgroupMap_surjective S₀)
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨y * a * y⁻¹, (Subgroup.mem_normalizer_iff.1 hvn a).1 ha, ?_⟩
      rw [map_mul, map_mul, map_inv, hφy]
    · intro hh
      obtain ⟨b, hb, hbh⟩ := hh
      refine ⟨y⁻¹ * b * y, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hvn) b).1 hb
        simpa [mul_assoc] using this
      · rw [map_mul, map_mul, map_inv, hφy, hbh]
        group
  · calc S₀.map φ ≤ ⁅S₀, Subgroup.zpowers y⁆.map φ := Subgroup.map_mono hvc
      _ = ⁅S₀.map φ, (Subgroup.zpowers y).map φ⁆ := Subgroup.map_commutator _ _ _
      _ = ⁅S₀.map φ, Subgroup.zpowers x⁆ := by rw [MonoidHom.map_zpowers, hφy]

end CFSG.RankThree.PartOne.K1320X
