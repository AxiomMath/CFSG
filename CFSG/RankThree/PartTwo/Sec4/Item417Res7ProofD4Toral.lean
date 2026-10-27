module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Levi
import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2OddB
import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace Res417Seven

section SL2

variable {F : Type} [Field F]

theorem HSL_mul_uSL_mul_inv (t : Fˣ) (c : F) :
    HSL t * uSL c * (HSL t)⁻¹ = uSL ((t : F) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, uSL, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem HSL_mul_vSL_mul_inv (t : Fˣ) (c : F) :
    HSL t * vSL c * (HSL t)⁻¹ = vSL (((t⁻¹ : Fˣ) : F) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem HSL_inv (t : Fˣ) : (HSL t)⁻¹ = HSL t⁻¹ := by
  rw [inv_eq_iff_mul_eq_one]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [HSL, Matrix.mul_apply, Fin.sum_univ_two]

end SL2

section Torus


variable {K : Type} [Field K]

theorem orbitH_mem_graphFixedRootTorus (σ : K →+* K) (a : Fin TwistTag.D4.foldedTag.rank)
    (u : (orbitField TwistTag.D4 K σ a)ˣ) :
    (orbitH TwistTag.D4 K σ a u : ModGL TwistTag.D4.tag K) ∈
      graphFixedRootTorus TwistTag.D4 K σ := by
  have hC := orbitH_mem_graphFixedRootGroup TwistTag.D4 σ a u
  exact ⟨⟨orbitH_mem_torusGroup (t := TwistTag.D4) (σ := σ) a u,
    graphFixedRootGroup_le TwistTag.D4 K σ hC⟩, hC⟩

theorem orbitH_mem_range (σ : K →+* K) (a : Fin TwistTag.D4.foldedTag.rank)
    (u : (orbitField TwistTag.D4 K σ a)ˣ) :
    (orbitH TwistTag.D4 K σ a u : ModGL TwistTag.D4.tag K) ∈
      (orbitRankOneHom TwistTag.D4 K σ a).range :=
  ⟨HSL u, orbitRankOneHom_HSL a u⟩

theorem exists_mul_orbitH_inv_mem_centralizer [Finite K] [CharP K 2] (σ : K →+* K)
    (a : Fin TwistTag.D4.foldedTag.rank) {h : ModGL TwistTag.D4.tag K}
    (hh : h ∈ graphFixedRootTorus TwistTag.D4 K σ) :
    ∃ l : (orbitField TwistTag.D4 K σ a)ˣ,
      h * (orbitH TwistTag.D4 K σ a l : ModGL TwistTag.D4.tag K)⁻¹ ∈
        Subgroup.centralizer ((orbitRankOneHom TwistTag.D4 K σ a).range :
          Set (ModGL TwistTag.D4.tag K)) := by
  obtain ⟨⟨hT, -, hfix⟩, -⟩ := hh
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  obtain ⟨u, rfl⟩ := exists_compatDiag_eq (compat_of_twistHom_rootDiagUnit hfix)
  have : Finite (orbitField TwistTag.D4 K σ a) := Subtype.finite
  have hch : ringChar (orbitField TwistTag.D4 K σ a) = 2 := ringChar.eq _ 2
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hch ((u a : orbitField TwistTag.D4 K σ a))
  have hr0 : r ≠ 0 := fun h0 => (u a).ne_zero (by rw [hr, h0, mul_zero])
  refine ⟨Units.mk0 r hr0, ?_⟩
  set d := rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ u)
  set n := (orbitH TwistTag.D4 K σ a (Units.mk0 r hr0) : ModGL TwistTag.D4.tag K)
  set R := orbitRankOneHom TwistTag.D4 K σ a
  have hn : n = R (HSL (Units.mk0 r hr0)) := (orbitRankOneHom_HSL a _).symm
  have hnx : ∀ c, n⁻¹ * (orbitX TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) * n =
      orbitX TwistTag.D4 K σ a (((Units.mk0 r hr0)⁻¹ : (orbitField TwistTag.D4 K σ a)ˣ) ^ 2 *
        c : orbitField TwistTag.D4 K σ a) := fun c => by
    rw [hn, ← orbitRankOneHom_uSL, ← map_inv, ← map_mul, ← map_mul, HSL_inv]
    rw [show (HSL (Units.mk0 r hr0)) = (HSL (Units.mk0 r hr0)⁻¹)⁻¹ by rw [HSL_inv, inv_inv],
      HSL_mul_uSL_mul_inv, orbitRankOneHom_uSL]
  have hny : ∀ c, n⁻¹ * (orbitY TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) * n =
      orbitY TwistTag.D4 K σ a ((Units.mk0 r hr0 : orbitField TwistTag.D4 K σ a) ^ 2 * c) :=
    fun c => by
      rw [hn, ← orbitRankOneHom_vSL, ← map_inv, ← map_mul, ← map_mul, HSL_inv]
      rw [show (HSL (Units.mk0 r hr0)) = (HSL (Units.mk0 r hr0)⁻¹)⁻¹ by rw [HSL_inv, inv_inv],
        HSL_mul_vSL_mul_inv, orbitRankOneHom_vSL, inv_inv]
  have hgen : ∀ s ∈ Set.range (fun c : orbitField TwistTag.D4 K σ a =>
      (orbitX TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K)) ∪
      Set.range (fun c : orbitField TwistTag.D4 K σ a =>
        (orbitY TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K)),
      s ∈ Subgroup.centralizer ({d * n⁻¹} : Set (ModGL TwistTag.D4.tag K)) := by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) <;> rw [Subgroup.mem_centralizer_singleton_iff]
    · have e1 : d * n⁻¹ * (orbitX TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) * (d * n⁻¹)⁻¹ =
          (orbitX TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) := by
        have e2 : d * n⁻¹ * (orbitX TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) * (d * n⁻¹)⁻¹ =
            d * (n⁻¹ * (orbitX TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) * n) * d⁻¹ := by
          group
        have key : (u a : orbitField TwistTag.D4 K σ a) *
            ((((Units.mk0 r hr0)⁻¹ : (orbitField TwistTag.D4 K σ a)ˣ) :
              orbitField TwistTag.D4 K σ a) ^ 2 * c) = c := by
          rw [hr, Units.val_inv_eq_inv_val, Units.val_mk0]
          field_simp
        rw [e2, hnx, compatDiag_conj_orbitX, key]
      calc (orbitX TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) * (d * n⁻¹) =
          (d * n⁻¹ * (orbitX TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) * (d * n⁻¹)⁻¹) *
            (d * n⁻¹) := by rw [e1]
        _ = d * n⁻¹ * (orbitX TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) := by group
    · have e1 : d * n⁻¹ * (orbitY TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) * (d * n⁻¹)⁻¹ =
          (orbitY TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) := by
        have e2 : d * n⁻¹ * (orbitY TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) * (d * n⁻¹)⁻¹ =
            d * (n⁻¹ * (orbitY TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) * n) * d⁻¹ := by
          group
        have key : (((u a)⁻¹ : (orbitField TwistTag.D4 K σ a)ˣ) : orbitField TwistTag.D4 K σ a) *
            (((Units.mk0 r hr0 : (orbitField TwistTag.D4 K σ a)ˣ) :
              orbitField TwistTag.D4 K σ a) ^ 2 * c) = c := by
          rw [Units.val_inv_eq_inv_val, hr, Units.val_mk0]
          field_simp
        rw [e2, hny, compatDiag_conj_orbitY, key]
      calc (orbitY TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) * (d * n⁻¹) =
          (d * n⁻¹ * (orbitY TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) * (d * n⁻¹)⁻¹) *
            (d * n⁻¹) := by rw [e1]
        _ = d * n⁻¹ * (orbitY TwistTag.D4 K σ a c : ModGL TwistTag.D4.tag K) := by group
  have hle : R.range ≤ Subgroup.centralizer ({d * n⁻¹} : Set (ModGL TwistTag.D4.tag K)) := by
    rw [orbitRankOneHom_range, Subgroup.closure_le]
    exact hgen
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hm))

theorem eq_one_of_mem_range_of_mem_centralizer [CharP K 2] (σ : K ≃+* K) (hσ : σ ^ 3 = 1)
    (a : Fin TwistTag.D4.foldedTag.rank) {m : ModGL TwistTag.D4.tag K}
    (hm : m ∈ (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range)
    (hmc : m ∈ Subgroup.centralizer ((orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range :
      Set (ModGL TwistTag.D4.tag K))) : m = 1 := by
  set R := orbitRankOneHom TwistTag.D4 K σ.toRingHom a
  have hinj : Function.Injective R := orbitRankOneHom_injective_D4 hσ a
  obtain ⟨A, rfl⟩ := hm
  have : CharP (orbitField TwistTag.D4 K σ.toRingHom a) 2 := inferInstance
  have hcomm : ∀ B, A * B = B * A := fun B => hinj (by
    rw [map_mul, map_mul]
    exact ((Subgroup.mem_centralizer_iff.1 hmc) (R B) ⟨B, rfl⟩).symm)
  rw [sl2_eq_one_of_commute (hcomm _) (hcomm _), map_one]

theorem exists_conj_le_graphFixedRootTorus [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : σ ^ 3 = 1)
    (a : Fin TwistTag.D4.foldedTag.rank)
    (h3 : 3 ∣ Nat.card (orbitField TwistTag.D4 K σ.toRingHom a) - 1)
    {E : Subgroup (ModGL TwistTag.D4.tag K)}
    (hEL : E ≤ graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom {a})
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) :
    ∃ y ∈ (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range,
      E.map (MulAut.conj y).toMonoidHom ≤ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
  classical
  have hTcomm := (triangular_borel_structure.{0, 0} TwistTag.D4.tag K).1
  set R := orbitRankOneHom TwistTag.D4 K σ.toRingHom a
  have hinj : Function.Injective R := orbitRankOneHom_injective_D4 hσ a
  set M := R.range
  set H := graphFixedRootTorus TwistTag.D4 K σ.toRingHom
  set Z := H ⊓ Subgroup.centralizer (M : Set (ModGL TwistTag.D4.tag K))
  have hHM : H ≤ Subgroup.normalizer (M : Set (ModGL TwistTag.D4.tag K)) :=
    graphFixedRootTorus_le_normalizer _ a
  have hHcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := fun x hx y hy => hTcomm _ hx.1.1 _ hy.1.1
  have hdec : ∀ e ∈ E, ∃ z ∈ Z, ∃ m ∈ M, e = z * m := by
    intro e he
    have he' : e ∈ ((H ⊔ M : Subgroup (ModGL TwistTag.D4.tag K)) :
        Set (ModGL TwistTag.D4.tag K)) := graphFixedParabolicLevi_singleton_le_sup σ a (hEL he)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H M hHM] at he'
    obtain ⟨h, hh, m, hm, rfl⟩ := he'
    have hh' : h ∈ H := hh
    obtain ⟨l, hl⟩ := exists_mul_orbitH_inv_mem_centralizer σ.toRingHom a hh'
    refine ⟨h * (orbitH TwistTag.D4 K σ.toRingHom a l : ModGL TwistTag.D4.tag K)⁻¹,
      ⟨H.mul_mem hh' (H.inv_mem (orbitH_mem_graphFixedRootTorus _ a l)), hl⟩,
      (orbitH TwistTag.D4 K σ.toRingHom a l : ModGL TwistTag.D4.tag K) * m,
      mul_mem (orbitH_mem_range _ a l) hm, by group⟩
  have hZE : ∀ z ∈ Z, ∀ e ∈ E, e * z = z * e := by
    intro z hz e he
    obtain ⟨z', hz', m, hm, rfl⟩ := hdec e he
    have h1 : m * z = z * m := (Subgroup.mem_centralizer_iff.1 hz.2) m hm
    rw [mul_assoc, h1, ← mul_assoc, hHcomm z' hz'.1 z hz.1, mul_assoc]
  set E' := (E ⊔ Z) ⊓ M
  have hZEn : Z ≤ Subgroup.normalizer (E : Set (ModGL TwistTag.D4.tag K)) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      rw [← hZE z hz e he, mul_inv_cancel_right]
      exact he
    · intro he
      have h1 := hZE z hz _ he
      have h2 : z * e = z * (z * e * z⁻¹) := by
        calc z * e = z * e * z⁻¹ * z := by group
          _ = z * (z * e * z⁻¹) := h1
      have h3 : e = z * e * z⁻¹ := mul_left_cancel h2
      rw [h3]
      exact he
  have hE'3 : ∀ m ∈ E', m ^ 3 = 1 := by
    rintro m ⟨hmEZ, hmM⟩
    have hmEZ' : m ∈ ((E ⊔ Z : Subgroup (ModGL TwistTag.D4.tag K)) :
        Set (ModGL TwistTag.D4.tag K)) := hmEZ
    rw [Subgroup.coe_mul_of_right_le_normalizer_left E Z hZEn] at hmEZ'
    obtain ⟨e, he, z, hz, rfl⟩ := hmEZ'
    have hcomm : Commute e z := hZE z hz e he
    have hpow : (e * z) ^ 3 = z ^ 3 := by
      rw [hcomm.mul_pow, hE3 e he, one_mul]
    have hz3 : z ^ 3 = 1 := by
      refine eq_one_of_mem_range_of_mem_centralizer σ hσ a ?_ (pow_mem hz 3).2
      rw [← hpow]
      exact pow_mem hmM 3
    rw [hpow, hz3]
  set E'' := E'.comap R
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (orbitField TwistTag.D4 K σ.toRingHom a) := Subtype.finite
  have hE''3 : ∀ A ∈ E'', A ^ 3 = 1 := fun A hA => hinj (by
    rw [map_pow, map_one]
    exact hE'3 _ hA)
  have hp : IsPGroup 3 E'' := fun A => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hE''3 _ A.2)⟩
  have hcyc := CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic (by norm_num) E'' hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E'')
  obtain ⟨P, t, hPt⟩ := Sec11.KS11Lie4Proof.exists_conj_HSL_of_three h3 (g : SL2 _)
    ⟨1, by rw [pow_one]; exact hE''3 _ g.2⟩
  refine ⟨R P, ⟨P, rfl⟩, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨z, hz, m, hm, rfl⟩ := hdec e he
  obtain ⟨A, rfl⟩ := hm
  have hAE : A ∈ E'' := by
    refine ⟨?_, ⟨A, rfl⟩⟩
    have e1 : R A = z⁻¹ * (z * R A) := by group
    rw [e1]
    exact mul_mem (Subgroup.mem_sup_right (inv_mem hz)) (Subgroup.mem_sup_left he)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨A, hAE⟩)
  have hAk : A = (g : SL2 _) ^ k := by
    have h1 := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at h1
    exact h1.symm
  have hzc : R P * z = z * R P := (Subgroup.mem_centralizer_iff.1 hz.2) (R P) ⟨P, rfl⟩
  change R P * (z * R A) * (R P)⁻¹ ∈ H
  have e2 : R P * (z * R A) * (R P)⁻¹ = z * R (P * A * P⁻¹) := by
    rw [map_mul, map_mul, map_inv, ← mul_assoc, hzc]
    group
  have e3 : P * A * P⁻¹ = HSL t ^ k := by
    rw [hAk, ← hPt, ← conj_zpow]
  rw [e2, e3, map_zpow, orbitRankOneHom_HSL]
  exact mul_mem hz.1 (zpow_mem (orbitH_mem_graphFixedRootTorus _ a t) k)

end Torus

end Res417Seven

end CFSG.RankThree.PartTwo.Sec4
