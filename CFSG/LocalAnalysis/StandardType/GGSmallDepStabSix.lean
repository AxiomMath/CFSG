module

public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
import CFSG.LocalAnalysis.StandardType.ZS.IsIsomStab
import CFSG.LocalAnalysis.StandardType.ZS.IsIsomCard
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassIndex

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggSmallDepWeylFive_card_le {n c : ℕ} (h : GGWeylTypeData 5 n c) : n ≤ 3840 := by
  rcases h with ⟨-, hn, -⟩ | ⟨-, hn, -⟩ | ⟨-, hn, -⟩ | ⟨hr, -, -⟩ | ⟨hr, -, -⟩ |
    ⟨hr, -, -⟩ | ⟨hr, -, -⟩ | ⟨hr, -, -⟩
  · rw [hn]; norm_num
  · rw [hn]; norm_num
  · rw [hn]; norm_num
  all_goals omega

theorem ggSmallDep_false_of_stab_six {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    [Module.Finite (ZMod 3) U] (hU : Module.finrank (ZMod 3) U = 6)
    {Q : QuadraticForm (ZMod 3) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {A : Subgroup (U ≃ₗ[ZMod 3] U)}
    (hA : (∀ g, g ∈ A ↔ ZS.IsIsom 3 Q g) ∨
      ∃ c : ZMod 3, c ≠ 0 ∧ A = Subgroup.closure (ZS.ClassRefl 3 Q c))
    {x : U} (hx : x ≠ 0) {H : Subgroup (U ≃ₗ[ZMod 3] U)}
    (hH : H ≤ A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod 3] U) x) {z : ℕ}
    (hHw : GGWeylTypeData 5 (Nat.card ↥H) z)
    (hstab : Nat.card ↥(A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod 3] U) x) ≤ 12 * Nat.card ↥H) :
    False := by
  have hdim : Module.finrank (ZMod 3) U = 2 * 3 := by omega
  have h5 : 5 ≤ Module.finrank (ZMod 3) U := by omega
  haveI : Finite U := Module.finite_of_finite (ZMod 3)
  haveI : Finite (U ≃ₗ[ZMod 3] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod 3] U => (e : U → U))
      fun _ _ h => LinearEquiv.ext (congrFun h)
  haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := Subtype.finite
  have hHcard : Nat.card ↥H ≤ 3840 := ggSmallDepWeylFive_card_le hHw
  have hAx_le : Nat.card ↥(A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod 3] U) x) ≤ 46080 := by
    omega
  have hOeq : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =
      Nat.card {g : U ≃ₗ[ZMod 3] U // ZS.IsIsom 3 Q g} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g =>
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff)
  have hO_ge : 93312 ≤ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      MulAction.stabilizer (U ≃ₗ[ZMod 3] U) x) := by
    by_cases hQx : Q x = 0
    · by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
      · have hOord := ZS.natCard_isIsom_of_isPlusType (p := 3) (by norm_num)
          (n := 3) (by norm_num) hdim hQ hplus
        have hOval : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) = 24261120 := by
          rw [hOeq, hOord]
          norm_num [Finset.prod_Icc_succ_top]
        have hsing := ZS.natCard_singular_of_isPlusType (p := 3) (n := 3)
          (by norm_num) hdim hQ hplus
        have hsingval : Nat.card {v : U // v ≠ 0 ∧ Q v = 0} = 260 := by
          rw [hsing]
          norm_num
        have hmult : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) ≤
            Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
              MulAction.stabilizer (U ≃ₗ[ZMod 3] U) x) *
              Nat.card {v : U // v ≠ 0 ∧ Q v = 0} := by
          have h := ZS.natCard_orthogonalGroup_le_mul (p := 3) Q hx
          simpa [hQx] using h
        rw [hOval, hsingval] at hmult
        have hdiv := Nat.div_le_of_le_mul hmult
        norm_num at hdiv
        omega
      · have hOord := ZS.natCard_isIsom_of_not_isPlusType (p := 3) (by norm_num)
          (n := 3) (by norm_num) hdim hQ hplus
        have hOval : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) = 26127360 := by
          rw [hOeq, hOord]
          norm_num [Finset.prod_Icc_succ_top]
        have hsing := ZS.natCard_singular_of_not_isPlusType (p := 3) (by norm_num)
          (n := 3) (by norm_num) hdim hQ hplus
        have hsingval : Nat.card {v : U // v ≠ 0 ∧ Q v = 0} = 224 := by
          rw [hsing]
          norm_num
        have hmult : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) ≤
            Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
              MulAction.stabilizer (U ≃ₗ[ZMod 3] U) x) *
              Nat.card {v : U // v ≠ 0 ∧ Q v = 0} := by
          have h := ZS.natCard_orthogonalGroup_le_mul (p := 3) Q hx
          simpa [hQx] using h
        rw [hOval, hsingval] at hmult
        have hdiv := Nat.div_le_of_le_mul hmult
        norm_num at hdiv
        omega
    · obtain ⟨W, hWdim, hWQ, hWcard⟩ :=
        ZS.exists_perp_natCard_isIsom_le (p := 3) (by norm_num) hQ hQx
      haveI : Module.Finite (ZMod 3) W := inferInstance
      have hW5 : Module.finrank (ZMod 3) W = 2 * 2 + 1 := by omega
      have hWord := ZS.natCard_isIsom_of_finrank_eq_odd (p := 3) (by norm_num)
        (n := 2) hW5 hWQ
      have hWval : Nat.card {g : W ≃ₗ[ZMod 3] W //
          ZS.IsIsom 3 (Q.comp W.subtype) g} = 103680 := by
        rw [hWord]
        norm_num [Finset.prod_Icc_succ_top]
      rw [hWval] at hWcard
      omega
  rcases hA with hA | ⟨c, hc, hAeq⟩
  · have hAO : A = TauCeti.QuadraticMap.orthogonalGroup Q := by
      ext g
      rw [hA g, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      rfl
    have hAx : Nat.card ↥(A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod 3] U) x) =
        Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
          MulAction.stabilizer (U ≃ₗ[ZMod 3] U) x) := by rw [hAO]
    omega
  · have hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
      intro g hg
      rw [hAeq] at hg
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
        (ZS.isIsom_of_mem_closure_classRefl hg)
    have hcos : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
        ∀ g' ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g ∉ A → g' ∉ A → g⁻¹ * g' ∈ A := by
      intro g hg g' hg' hgn hgn'
      rw [hAeq]
      exact ZS.inv_mul_mem_closure_classRefl (p := 3) (by norm_num) h5 hQ hc
        (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg)
        (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg')
        (by simpa [hAeq] using hgn) (by simpa [hAeq] using hgn')
    have hO_le : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
        MulAction.stabilizer (U ≃ₗ[ZMod 3] U) x) ≤
        2 * Nat.card ↥(A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod 3] U) x) :=
      ZS.natCard_inf_le_two_mul hAO hcos (MulAction.stabilizer (U ≃ₗ[ZMod 3] U) x)
    omega

end CFSG.StandardType

end
