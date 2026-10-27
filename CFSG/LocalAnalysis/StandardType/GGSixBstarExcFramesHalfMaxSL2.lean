module

public import CFSG.GH74.Generic.BProg.B3.S1IdentSl2
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxRational
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxSL2Tools
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxTorus

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE

open scoped Matrix

section FixedRoot


theorem eq_one_of_commute_uSL_vSL_charTwo {L : Type} [Field L] [CharP L 2] {M : SL2 L}
    (hu : M * uSL 1 = uSL 1 * M) (hv : M * vSL 1 = vSL 1 * M) : M = 1 := by
  have hu' := congrArg (fun N : SL2 L => (N : Matrix (Fin 2) (Fin 2) L)) hu
  have hv' := congrArg (fun N : SL2 L => (N : Matrix (Fin 2) (Fin 2) L)) hv
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hu' hv'
  have e00 := congrFun (congrFun hu' 0) 0
  have e01 := congrFun (congrFun hu' 0) 1
  have f00 := congrFun (congrFun hv' 0) 0
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 f00
  have hr : (M : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    linear_combination e00
  have hq : (M : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
    linear_combination f00
  have hps : (M : Matrix (Fin 2) (Fin 2) L) 0 0 = (M : Matrix (Fin 2) (Fin 2) L) 1 1 := by
    linear_combination e01
  have hdet := M.2
  rw [Matrix.det_fin_two] at hdet
  have hp : (M : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by
    have h2 : ((M : Matrix (Fin 2) (Fin 2) L) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hdet + (M : Matrix (Fin 2) (Fin 2) L) 0 0 * hps +
        (M : Matrix (Fin 2) (Fin 2) L) 0 1 * hr +
        (1 - (M : Matrix (Fin 2) (Fin 2) L) 0 0) * (CharTwo.two_eq_zero (R := L))
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  have hs : (M : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := hps ▸ hp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, hs]

theorem map_specialLinearGroup_injective {K L : Type} [Field K] [Field L] (φ : K →+* L) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) φ) := by
  intro X Y h
  apply Subtype.ext
  ext i j
  have h1 := congrFun (congrFun (congrArg Subtype.val h) i) j
  simpa using φ.injective h1

theorem exists_sl2_orderOf_prime {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K + 1) : ∃ b : SL2 K, orderOf b = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hdvd : p ∣ Nat.card (SL2 K) := by
    rw [CFSG.GH74.Generic.BProg.B3.S1IdentSl2.card_sl2]
    refine Dvd.dvd.mul_left ?_ _
    have : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
      zify [hq, Nat.one_le_pow 2 _ hq]
      ring
    rw [this]
    exact Dvd.dvd.mul_right hpq _
  exact exists_prime_orderOf_dvd_card' p hdvd

theorem commute_rootSL2_of_mem_twistedTorus {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {Fr : L →+* L} {q p : ℕ} (hFr : ∀ c, Fr c = c ^ q) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ q + 1) {w : WeylGroup τ} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hwβ : w • β = β) {t : ModGL τ L}
    (ht : t ∈ twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr) (htp : t ^ p = 1)
    (A : SL2 L) : t * rootSL2 τ L β A = rootSL2 τ L β A * t := by
  obtain ⟨a, ha, hap, rfl⟩ := exists_tuple_of_mem_twistedTorus w Fr ht htp
  have hχ : rootChar a β = 1 :=
    rootChar_eq_one_of_mem_fixedCharTuples hFr hp hp2 hpq ha hap
      (by rw [CFSG.RankThree.E6.weylMatrix_mulVec]; exact hwβ)
  have h := rootDiagUnit_conj_rootSL2 a hβ A
  rw [hχ, conjSL_diagUnitOne_one] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem false_of_fixed_root {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K L : Type} [Field K] [Finite K]
    [CharP K 2] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup τ K))
    (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E)
    (w : WeylGroup τ) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (g0 : ModGL τ L)
    (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ) L w)
    (hEin : ∀ x ∈ E, baseChangeGL (algebraMap K L) ((x : adjointGroup τ K) : ModGL τ K) ∈
      (twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr).map (MulAut.conj g0).toMonoidHom)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hwβ : w • β = β) : False := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hCharL : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hFrι : ∀ c : K, Fr (algebraMap K L c) = algebraMap K L c := by
    intro c
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card]
    exact congrArg (algebraMap K L) (FiniteField.pow_card c)
  obtain ⟨b, hb⟩ := exists_sl2_orderOf_prime hp hpq
  have hbp : b ^ p = 1 := hb ▸ pow_orderOf_eq_one b
  have hbLp : Matrix.SpecialLinearGroup.map (algebraMap K L) b ^ p = 1 := by
    rw [← map_pow, hbp, map_one]
  have hmapFr : Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map (algebraMap K L) b) =
      Matrix.SpecialLinearGroup.map (algebraMap K L) b := by
    apply Subtype.ext
    ext i j
    simp [hFrι]
  have hyC : rootSL2 τ L β (Matrix.SpecialLinearGroup.map (algebraMap K L) b) ∈
      adjointGroup τ L := (exceptional_Lang_root_rank_one_data τ L β).2.2.2.2.1 _
  have hyp : rootSL2 τ L β (Matrix.SpecialLinearGroup.map (algebraMap K L) b) ^ p = 1 := by
    rw [← map_pow, hbLp, map_one]
  have hyΦ : Units.map (entrywiseHom Fr)
      (rootSL2 τ L β (Matrix.SpecialLinearGroup.map (algebraMap K L) b)) =
      rootSL2 τ L β (Matrix.SpecialLinearGroup.map (algebraMap K L) b) := by
    rw [entrywise_rootSL2_of_field, hmapFr]
  have hn := canonicalRep_conj_rootSL2_of_fixed w hβ hwβ
    (Matrix.SpecialLinearGroup.map (algebraMap K L) b)
  generalize hy : rootSL2 τ L β (Matrix.SpecialLinearGroup.map (algebraMap K L) b) = y at hyC hyp hyΦ hn
  have hy2C : g0 * y * g0⁻¹ ∈ adjointGroup τ L := mul_mem (mul_mem hg0C hyC) (inv_mem hg0C)
  have hy2p : (g0 * y * g0⁻¹) ^ p = 1 := by
    rw [conj_pow, hyp]
    group
  have hy2Φ : Units.map (entrywiseHom Fr) (g0 * y * g0⁻¹) = g0 * y * g0⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg0, hyΦ]
    calc g0 * canonicalRep (coxeterSystem τ) L w * y * (g0 * canonicalRep (coxeterSystem τ) L w)⁻¹
        = g0 * (canonicalRep (coxeterSystem τ) L w * y *
            (canonicalRep (coxeterSystem τ) L w)⁻¹) * g0⁻¹ := by group
      _ = g0 * y * g0⁻¹ := by rw [hn]
  obtain ⟨c, hc⟩ := exists_rational_of_fixed_pTorsion hτ hp hp2 Fr hFr hy2C hy2Φ hy2p
  have hι_inj : ∀ a b : ModGL τ K, baseChangeGL (algebraMap K L) a =
      baseChangeGL (algebraMap K L) b → a = b := fun a b h => baseChangeGL_injective _ h
  have hcE : c ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.1 (hEin x hx)
    have htx' : g0 * t * g0⁻¹ = baseChangeGL (algebraMap K L) (x : ModGL τ K) := htx
    have htp : t ^ p = 1 := by
      have h1 : (g0 * t * g0⁻¹) ^ p = 1 := by
        rw [htx', ← map_pow]
        have : ((x : ModGL τ K)) ^ p = 1 := congrArg Subtype.val (hE.2 x hx)
        rw [this, map_one]
      rw [conj_pow] at h1
      calc t ^ p = g0⁻¹ * (g0 * t ^ p * g0⁻¹) * g0 := by group
        _ = 1 := by rw [h1]; group
    have hcomm := commute_rootSL2_of_mem_twistedTorus (q := Nat.card K) hFr hp hp2 hpq hβ hwβ ht
      htp (Matrix.SpecialLinearGroup.map (algebraMap K L) b)
    rw [hy] at hcomm
    have h3 : baseChangeGL (algebraMap K L) (x : ModGL τ K) *
        baseChangeGL (algebraMap K L) (c : ModGL τ K) =
        baseChangeGL (algebraMap K L) (c : ModGL τ K) *
          baseChangeGL (algebraMap K L) (x : ModGL τ K) := by
      rw [hc, ← htx']
      calc g0 * t * g0⁻¹ * (g0 * y * g0⁻¹) = g0 * (t * y) * g0⁻¹ := by group
        _ = g0 * (y * t) * g0⁻¹ := by rw [hcomm]
        _ = g0 * y * g0⁻¹ * (g0 * t * g0⁻¹) := by group
    have h4 : (x : ModGL τ K) * (c : ModGL τ K) = (c : ModGL τ K) * (x : ModGL τ K) := by
      apply hι_inj
      rw [map_mul, map_mul]
      exact h3
    exact Subtype.ext h4
  have hcp : c ^ p = 1 := by
    apply Subtype.ext
    apply hι_inj
    rw [Subgroup.coe_pow, map_pow, hc, hy2p, Subgroup.coe_one, map_one]
  have hcEmem : c ∈ E := hSC c hcE hcp
  obtain ⟨t', ht', htc⟩ := Subgroup.mem_map.1 (hEin c hcEmem)
  have htc' : g0 * t' * g0⁻¹ = baseChangeGL (algebraMap K L) (c : ModGL τ K) := htc
  rw [hc] at htc'
  have hty : t' = y := by
    calc t' = g0⁻¹ * (g0 * t' * g0⁻¹) * g0 := by group
      _ = g0⁻¹ * (g0 * y * g0⁻¹) * g0 := by rw [htc']
      _ = y := by group
  rw [hty] at ht'
  have hcommA : ∀ A : SL2 L,
      rootSL2 τ L β (Matrix.SpecialLinearGroup.map (algebraMap K L) b * A) =
        rootSL2 τ L β (A * Matrix.SpecialLinearGroup.map (algebraMap K L) b) := by
    intro A
    have := commute_rootSL2_of_mem_twistedTorus (q := Nat.card K) hFr hp hp2 hpq hβ hwβ ht' hyp A
    rw [← hy] at this
    rw [map_mul, map_mul]
    exact this
  have hbL1 : Matrix.SpecialLinearGroup.map (algebraMap K L) b = 1 := by
    refine eq_one_of_commute_uSL_vSL_charTwo ?_ ?_
    · exact (rootSL2_injective_of_field β (hcommA (uSL 1)))
    · exact (rootSL2_injective_of_field β (hcommA (vSL 1)))
  have hb1 : b = 1 := by
    apply map_specialLinearGroup_injective (algebraMap K L)
    rw [hbL1, map_one]
  rw [hb1, orderOf_one] at hb
  exact hp.one_lt.ne hb

end FixedRoot

end ExcFramesHalf

end CFSG.StandardType
