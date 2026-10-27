module

public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
import CFSG.LocalAnalysis.StandardType.ZS.IsIsomStab
import CFSG.LocalAnalysis.StandardType.ZS.IsIsomCard
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassIndex

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggWeylTypeData_four_natCard {n c : ℕ} (h : GGWeylTypeData 4 n c) :
    n = 120 ∨ n = 384 ∨ n = 192 ∨ n = 1152 := by
  rcases h with ⟨-, hn, -⟩ | ⟨-, hn, -⟩ | ⟨-, hn, -⟩ | ⟨hr, -, -⟩ | ⟨hr, -, -⟩ |
    ⟨hr, -, -⟩ | ⟨-, hn, -⟩ | ⟨hr, -, -⟩
  · exact Or.inl (by rw [hn]; decide)
  · exact Or.inr (Or.inl (by rw [hn]; decide))
  · exact Or.inr (Or.inr (Or.inl (by rw [hn]; decide)))
  · exact absurd hr (by norm_num)
  · exact absurd hr (by norm_num)
  · exact absurd hr (by norm_num)
  · exact Or.inr (Or.inr (Or.inr hn))
  · exact absurd hr (by norm_num)

theorem ggSmallDep_false_of_stab_five {U : Type} [AddCommGroup U] [Module (ZMod 5) U]
    [Module.Finite (ZMod 5) U] (hU : Module.finrank (ZMod 5) U = 5)
    {Q : QuadraticForm (ZMod 5) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {A : Subgroup (U ≃ₗ[ZMod 5] U)}
    (hA : (∀ g, g ∈ A ↔ ZS.IsIsom 5 Q g) ∨
      ∃ c : ZMod 5, c ≠ 0 ∧ A = Subgroup.closure (ZS.ClassRefl 5 Q c))
    {x : U} (hx : x ≠ 0) {H : Subgroup (U ≃ₗ[ZMod 5] U)}
    (hH : H ≤ A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod 5] U) x) {z : ℕ}
    (hHw : GGWeylTypeData 4 (Nat.card ↥H) z)
    (hstab : Nat.card ↥(A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod 5] U) x) ≤ 24 * Nat.card ↥H) :
    False := by
  classical
  haveI : Finite U := Module.finite_of_finite (ZMod 5)
  let O : Subgroup (U ≃ₗ[ZMod 5] U) := TauCeti.QuadraticMap.orthogonalGroup Q
  let S : Subgroup (U ≃ₗ[ZMod 5] U) := MulAction.stabilizer (U ≃ₗ[ZMod 5] U) x
  have hOcard : Nat.card ↥O = 18720000 := by
    rw [show Nat.card ↥O = Nat.card {g : U ≃ₗ[ZMod 5] U // ZS.IsIsom 5 Q g} from
      Nat.card_congr (Equiv.subtypeEquivRight (fun g : U ≃ₗ[ZMod 5] U => by
        change g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ↔ ZS.IsIsom 5 Q g
        rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        rfl))]
    rw [ZS.natCard_isIsom_of_finrank_eq_odd (p := 5) (n := 2) (by norm_num) (by omega) hQ]
    decide
  have hHle : Nat.card ↥H ≤ 1152 := by
    rcases ggWeylTypeData_four_natCard hHw with h | h | h | h <;> omega
  have hOx : 28800 ≤ Nat.card ↥(O ⊓ S) := by
    by_cases hQx : Q x = 0
    · have hsing : Nat.card {v : U // v ≠ 0 ∧ Q v = Q x} = 5 ^ 4 - 1 :=
        (Nat.card_congr (Equiv.subtypeEquivRight (fun v : U => by rw [hQx]))).trans
          (ZS.natCard_singular_of_finrank_eq_odd (p := 5) (n := 2) (by norm_num) (by omega) hQ)
      have horb := ZS.natCard_orthogonalGroup_le_mul (p := 5) Q hx
      rw [hOcard, hsing] at horb
      rw [show (5 : ℕ) ^ 4 - 1 = 624 by norm_num] at horb
      have horb' : 18720000 ≤ Nat.card ↥(O ⊓ S) * 624 := horb
      omega
    · have hp5 : (5 : ℕ) ≠ 2 := by norm_num
      obtain ⟨W, hdim, hQw, hle⟩ :=
        ZS.exists_perp_natCard_isIsom_le (p := 5) (U := U) (Q := Q) hp5 hQ hQx
      haveI : Module.Finite (ZMod 5) W :=
        Module.Finite.of_injective (f := W.subtype) W.subtype_injective
      have hnW : Module.finrank (ZMod 5) W = 2 * 2 := by omega
      have hWge : 28800 ≤ Nat.card {g : W ≃ₗ[ZMod 5] W //
          ZS.IsIsom 5 (Q.comp W.subtype) g} := by
        by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp W.subtype)
        · rw [ZS.natCard_isIsom_of_isPlusType (p := 5) (n := 2) (by norm_num)
            (by norm_num) hnW hQw hplus]
          norm_num
        · rw [ZS.natCard_isIsom_of_not_isPlusType (p := 5) (n := 2) (by norm_num)
            (by norm_num) hnW hQw hplus]
          norm_num
      exact le_trans hWge hle
  rcases hA with hA | ⟨c, hc, hAeq⟩
  · have hAO : A = O := by
      ext g
      rw [hA g]
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.symm
    have hstabO : Nat.card ↥(O ⊓ S) ≤ 24 * Nat.card ↥H := by
      rw [← hAO]
      exact hstab
    have h := hOx.trans hstabO
    have h2 : 24 * Nat.card ↥H ≤ 24 * 1152 := Nat.mul_le_mul_left 24 hHle
    omega
  · have hAO : A ≤ O := by
      intro g hg
      rw [hAeq] at hg
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
        (ZS.isIsom_of_mem_closure_classRefl hg)
    have hcos : ∀ g ∈ O, ∀ g' ∈ O, g ∉ A → g' ∉ A → g⁻¹ * g' ∈ A := by
      intro g hgO g' hg'O hgA hgA'
      rw [hAeq] at hgA hgA' ⊢
      exact ZS.inv_mul_mem_closure_classRefl (p := 5) (hp := by norm_num) (h5 := by omega)
        hQ hc (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO)
        (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg'O) hgA hgA'
    have hOinf : Nat.card ↥(O ⊓ S) ≤ 2 * Nat.card ↥(A ⊓ S) :=
      ZS.natCard_inf_le_two_mul hAO hcos S
    have hstabA : Nat.card ↥(A ⊓ S) ≤ 24 * Nat.card ↥H := hstab
    have hAx_ge : 14400 ≤ Nat.card ↥(A ⊓ S) := by omega
    have hHge : 600 ≤ Nat.card ↥H := by omega
    have hH1152 : Nat.card ↥H = 1152 := by
      rcases ggWeylTypeData_four_natCard hHw with h | h | h | h <;> omega
    have hAx_le : Nat.card ↥(A ⊓ S) ≤ 27648 := by
      rw [hH1152] at hstabA
      omega
    have hdvdH : 1152 ∣ Nat.card ↥(A ⊓ S) := by
      rw [← hH1152]
      exact Subgroup.card_dvd_of_le (show H ≤ A ⊓ S from hH)
    have hdvdO : Nat.card ↥(A ⊓ S) ∣ 18720000 := by
      rw [← hOcard]
      exact Subgroup.card_dvd_of_le (show A ⊓ S ≤ O from fun g hg => hAO hg.1)
    obtain ⟨k, hk⟩ := hdvdH
    have hk_dvd : k ∣ 16250 := by
      have h : 1152 * k ∣ 18720000 := by
        rwa [hk] at hdvdO
      rw [show (18720000 : ℕ) = 1152 * 16250 by norm_num] at h
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
    have hk13 : k = 13 := by
      have h1 : 14400 ≤ 1152 * k := by
        rw [hk] at hAx_ge
        exact hAx_ge
      have h2 : 1152 * k ≤ 27648 := by
        rw [hk] at hAx_le
        exact hAx_le
      have h3 : 13 ≤ k := by omega
      have h4 : k ≤ 24 := by omega
      interval_cases k
      · rfl
      all_goals exfalso; norm_num at hk_dvd
    have hAx : Nat.card ↥(A ⊓ S) = 14976 := by
      rw [hk, hk13]
    have hdvdOx : 14976 ∣ Nat.card ↥(O ⊓ S) := by
      rw [← hAx]
      exact Subgroup.card_dvd_of_le
        (show A ⊓ S ≤ O ⊓ S from fun g hg => ⟨hAO hg.1, hg.2⟩)
    have hOx_le : Nat.card ↥(O ⊓ S) ≤ 29952 := by
      rw [hAx] at hOinf
      omega
    have hOx_eq : Nat.card ↥(O ⊓ S) = 29952 := by
      obtain ⟨m, hm⟩ := hdvdOx
      have h1 : 28800 ≤ 14976 * m := by
        rw [hm] at hOx
        exact hOx
      have h2 : 14976 * m ≤ 29952 := by
        rw [hm] at hOx_le
        exact hOx_le
      have hm2 : m = 2 := by
        have hm_ge : 2 ≤ m := by omega
        have hm_le : m ≤ 2 := by omega
        interval_cases m
        rfl
      rw [hm, hm2]
    have hdvd := ZS.two_mul_natCard_stabilizer_dvd (p := 5) (hp := by norm_num) Q hx
    rw [hOx_eq, hOcard] at hdvd
    norm_num at hdvd

end CFSG.StandardType

end
