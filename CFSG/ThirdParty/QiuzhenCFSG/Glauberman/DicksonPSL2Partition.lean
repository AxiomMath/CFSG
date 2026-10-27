module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonNonsplitTorus
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonCoprimeOrders
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonUnipotent
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorusMatrices
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_11
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace CFSG
end CFSG
open CFSG

/-!
# The three-family partition of PSL(2,q)

This module isolates Huppert II.8.5(a): nonidentity elements lie in unique
conjugates of a Sylow subgroup, the split torus, or the nonsplit torus.
-/

namespace CFSG.Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open BenderSuzuki.External
open scoped Pointwise
open scoped LinearAlgebra.Projectivization

universe u v

private theorem hconjugate_family_unique_of_weak_ti
    {G : Type u} [Group G] (U : Subgroup G)
    (hweakTI : ∀ y : G, y ∈ U → y ≠ 1 → ∀ g : G,
      g * y * g⁻¹ ∈ U → g ∈ Subgroup.normalizer (U : Set G)) :
    ∀ x : G, x ≠ 1 → ∀ g₁ g₂,
      x ∈ U.map (MulAut.conj g₁).toMonoidHom →
      x ∈ U.map (MulAut.conj g₂).toMonoidHom →
      U.map (MulAut.conj g₁).toMonoidHom =
        U.map (MulAut.conj g₂).toMonoidHom := by
  intro x hx g₁ g₂ hx₁ hx₂
  rcases hx₁ with ⟨a, haU, ha⟩
  rcases hx₂ with ⟨b, hbU, hb⟩
  have ha' : g₁ * a * g₁⁻¹ = x := by
    simpa [MulAut.conj_apply] using ha
  have hb' : g₂ * b * g₂⁻¹ = x := by
    simpa [MulAut.conj_apply] using hb
  have ha_ne : a ≠ 1 := by
    intro ha_one
    apply hx
    rw [← ha']
    simp [ha_one]
  have hb_ne : b ≠ 1 := by
    intro hb_one
    apply hx
    rw [← hb']
    simp [hb_one]
  let g : G := g₁⁻¹ * g₂
  have hconj : g * b * g⁻¹ = a := by
    change (g₁⁻¹ * g₂) * b * (g₁⁻¹ * g₂)⁻¹ = a
    calc
      (g₁⁻¹ * g₂) * b * (g₁⁻¹ * g₂)⁻¹ =
          g₁⁻¹ * (g₂ * b * g₂⁻¹) * g₁ := by group
      _ = g₁⁻¹ * x * g₁ := by rw [hb']
      _ = a := by rw [← ha']; group
  have hgN : g ∈ Subgroup.normalizer (U : Set G) :=
    hweakTI b hbU hb_ne g (by simpa [hconj] using haU)
  have hmapg :
      U.map (MulAut.conj g).toMonoidHom = U := by
    rw [← Subgroup.conjAct_pointwise_smul_iff] at hgN
    change U.map (MulAut.conj g).toMonoidHom = U at hgN
    exact hgN
  have hgprod : g₁ * g = g₂ := by
    simp [g]
  calc
    U.map (MulAut.conj g₁).toMonoidHom =
        (U.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj g₁).toMonoidHom := by rw [hmapg]
    _ = U.map (MulAut.conj (g₁ * g)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    _ = U.map (MulAut.conj g₂).toMonoidHom := by rw [hgprod]
private theorem hthree_family_unique_of_same_family
    {G : Type u} [Group G] [Finite G]
    (P U S : Subgroup G)
    (hPU : Nat.Coprime (Nat.card P) (Nat.card U))
    (hPS : Nat.Coprime (Nat.card P) (Nat.card S))
    (hUS : Nat.Coprime (Nat.card U) (Nat.card S))
    (hsameP : ∀ x : G, x ≠ 1 → ∀ g₁ g₂,
      x ∈ P.map (MulAut.conj g₁).toMonoidHom →
      x ∈ P.map (MulAut.conj g₂).toMonoidHom →
      P.map (MulAut.conj g₁).toMonoidHom =
        P.map (MulAut.conj g₂).toMonoidHom)
    (hsameU : ∀ x : G, x ≠ 1 → ∀ g₁ g₂,
      x ∈ U.map (MulAut.conj g₁).toMonoidHom →
      x ∈ U.map (MulAut.conj g₂).toMonoidHom →
      U.map (MulAut.conj g₁).toMonoidHom =
        U.map (MulAut.conj g₂).toMonoidHom)
    (hsameS : ∀ x : G, x ≠ 1 → ∀ g₁ g₂,
      x ∈ S.map (MulAut.conj g₁).toMonoidHom →
      x ∈ S.map (MulAut.conj g₂).toMonoidHom →
      S.map (MulAut.conj g₁).toMonoidHom =
        S.map (MulAut.conj g₂).toMonoidHom) :
    ∀ x : G, x ≠ 1 →
      ∀ T₁ T₂ : Subgroup G, x ∈ T₁ → x ∈ T₂ →
      ((∃ g, T₁ = P.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T₁ = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T₁ = S.map (MulAut.conj g).toMonoidHom)) →
      ((∃ g, T₂ = P.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T₂ = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T₂ = S.map (MulAut.conj g).toMonoidHom)) →
      T₁ = T₂ := by
  intro x hx T₁ T₂ hx₁ hx₂ hT₁ hT₂
  rcases hT₁ with ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩ <;>
    rcases hT₂ with ⟨g₂, rfl⟩ | ⟨g₂, rfl⟩ | ⟨g₂, rfl⟩
  · exact hsameP x hx g₁ g₂ hx₁ hx₂
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := U)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hPU) hx₁ hx₂)).elim
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := S)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hPS) hx₁ hx₂)).elim
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := U)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hPU.symm) hx₁ hx₂)).elim
  · exact hsameU x hx g₁ g₂ hx₁ hx₂
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := U)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := S)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hUS) hx₁ hx₂)).elim
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := S)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hPS.symm) hx₁ hx₂)).elim
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := S)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := U)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hUS.symm) hx₁ hx₂)).elim
  · exact hsameS x hx g₁ g₂ hx₁ hx₂

set_option backward.isDefEq.respectTransparency false in
/-- Huppert II.8.5(a), with the covering and TI uniqueness clauses tied to
the same standard split and nonsplit tori. -/
public theorem huppert_II_8_5_a_psl2_cover
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f)
    (P : Sylow p (PSL2MatrixGroup F)) :
    ∃ U S : Subgroup (PSL2MatrixGroup F),
      IsCyclic U ∧
      Nat.card U =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      ∀ x : PSL2MatrixGroup F, x ≠ 1 →
        ∃! T : Subgroup (PSL2MatrixGroup F),
          x ∈ T ∧
            ((∃ g, T = (P : Subgroup (PSL2MatrixGroup F)).map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = S.map (MulAut.conj g).toMonoidHom)) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  let qSL : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
    QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  let unipotentSL :
      AddChar F (Matrix.SpecialLinearGroup (Fin 2) F) :=
    unipotentSLAddChar F
  let unipotent : AddChar F (PSL2MatrixGroup F) :=
    qSL.compAddChar unipotentSL
  have h_unipotent_injective : Function.Injective unipotent := by
    simpa [unipotent, qSL, unipotentSL, projectiveUnipotentAddChar] using
      projectiveUnipotentAddChar_injective F
  let U₀ : Subgroup (PSL2MatrixGroup F) := unipotent.toMonoidHom.range
  have hU₀card : Nat.card U₀ = Nat.card F := by
    let e : Multiplicative F ≃ U₀ :=
      Equiv.ofInjective unipotent.toMonoidHom h_unipotent_injective
    exact Nat.card_congr e.symm
  have hU₀_isPGroup : IsPGroup p U₀ := by
    apply IsPGroup.of_card
    rw [hU₀card, hFcard]
  obtain ⟨Q, hU₀_le_Q⟩ := hU₀_isPGroup.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    rcases huppert_II_8_2_a_sylow_equiv_additive hFcard Q with ⟨eQ⟩
    exact (Nat.card_congr eQ.toEquiv).symm
  have hU₀_eq_Q : U₀ = (Q : Subgroup (PSL2MatrixGroup F)) :=
    Subgroup.eq_of_le_of_card_ge hU₀_le_Q (by rw [hQcard, hU₀card])
  obtain ⟨kP, hkP⟩ := MulAction.exists_smul_eq
    (α := Sylow p (PSL2MatrixGroup F)) (PSL2MatrixGroup F) P Q
  have hP_to_U₀ :
      (P : Subgroup (PSL2MatrixGroup F)).map
        (MulAut.conj kP).toMonoidHom = U₀ := by
    have hkP' := congrArg
      (fun R : Sylow p (PSL2MatrixGroup F) =>
        (R : Subgroup (PSL2MatrixGroup F))) hkP
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      ← hU₀_eq_Q] at hkP'
    exact hkP'
  have hupper_unipotent_conj
      (A : Matrix.SpecialLinearGroup (Fin 2) F)
      (hA10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
      (t : F) :
      A * unipotentSL t * A⁻¹ =
        unipotentSL
          ((A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t) := by
    simpa [unipotentSL] using
      unipotentSLAddChar_conj_of_lowerLeft_eq_zero A hA10 t
  have hU₀_weakTI :
      ∀ y : PSL2MatrixGroup F, y ∈ U₀ → y ≠ 1 →
        ∀ g : PSL2MatrixGroup F,
          g * y * g⁻¹ ∈ U₀ →
            g ∈ Subgroup.normalizer (U₀ : Set (PSL2MatrixGroup F)) := by
    intro y hy hy_ne g hgy
    rcases hy with ⟨a, rfl⟩
    have ha_ne_zero : a.toAdd ≠ 0 := by
      intro ha_zero
      apply hy_ne
      change unipotent a.toAdd = 1
      rw [ha_zero]
      exact unipotent.map_zero_eq_one
    refine QuotientGroup.induction_on g ?_ hgy
    intro A hAconj
    rcases hAconj with ⟨b, hb⟩
    have hq :
        qSL (unipotentSL b.toAdd) =
          qSL (A * unipotentSL a.toAdd * A⁻¹) := by
      simpa [qSL, unipotent] using hb
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hq with
      ⟨z, hz, hzeq⟩
    have hzeqA :
        unipotentSL b.toAdd * z * A =
          A * unipotentSL a.toAdd := by
      calc
        unipotentSL b.toAdd * z * A =
            (A * unipotentSL a.toAdd * A⁻¹) * A := by rw [hzeq]
        _ = A * unipotentSL a.toAdd := by group
    let r : F := (z : Matrix (Fin 2) (Fin 2) F) 0 0
    have hscalar :
        Matrix.scalar (Fin 2) r =
          (z : Matrix.SpecialLinearGroup (Fin 2) F) := by
      simpa [r] using
        Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hz (0 : Fin 2)
    have hmat := congrArg Subtype.val hzeqA
    change (unipotentSL b.toAdd : Matrix (Fin 2) (Fin 2) F) *
        (z : Matrix (Fin 2) (Fin 2) F) *
          (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) *
        (unipotentSL a.toAdd : Matrix (Fin 2) (Fin 2) F) at hmat
    rw [← hscalar] at hmat
    have h10 := congrFun (congrFun hmat (1 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hmat (1 : Fin 2)) (1 : Fin 2)
    simp [unipotentSL, Matrix.mul_apply] at h10 h11
    have hr_one : r = 1 := by
      by_cases hA10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      · have hA11_ne :
            (A : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
          intro hA11
          have hdet := A.property
          rw [Matrix.det_fin_two, hA10, hA11, mul_zero, mul_zero,
            sub_zero] at hdet
          exact zero_ne_one hdet
        apply mul_right_cancel₀ hA11_ne
        simpa [hA10, mul_assoc] using h11
      · apply mul_right_cancel₀ hA10
        simpa [mul_assoc] using h10
    have hA10 :
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have hprod :
          (A : Matrix (Fin 2) (Fin 2) F) 1 0 * a.toAdd = 0 := by
        simpa [hr_one, mul_comm, mul_left_comm, mul_assoc] using h11
      exact (mul_eq_zero.mp hprod).resolve_right ha_ne_zero
    have hmap_le :
        U₀.map (MulAut.conj (qSL A)).toMonoidHom ≤ U₀ := by
      intro v hv
      rcases hv with ⟨w, hw, rfl⟩
      rcases hw with ⟨t, rfl⟩
      refine ⟨Multiplicative.ofAdd
        ((A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t.toAdd), ?_⟩
      change unipotent
          ((A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t.toAdd) =
        (MulAut.conj (qSL A)).toMonoidHom (unipotent t.toAdd)
      have hc := congrArg qSL
        (hupper_unipotent_conj A hA10 t.toAdd)
      simpa [qSL, unipotent, MulAut.conj_apply] using hc.symm
    have hmap_eq :
        U₀.map (MulAut.conj (qSL A)).toMonoidHom = U₀ := by
      apply Subgroup.eq_of_le_of_card_ge hmap_le
      rw [Subgroup.card_map_of_injective
        (K := U₀) (f := (MulAut.conj (qSL A)).toMonoidHom)
          (MulAut.conj (qSL A)).injective]
    rw [← Subgroup.conjAct_pointwise_smul_iff]
    exact hmap_eq
  have hU₀_same_family :=
    hconjugate_family_unique_of_weak_ti U₀ hU₀_weakTI
  have hprojective_TI_P :
      ∀ x : PSL2MatrixGroup F, x ≠ 1 → ∀ g₁ g₂,
        x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₁).toMonoidHom →
        x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₂).toMonoidHom →
        (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₁).toMonoidHom =
          (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₂).toMonoidHom := by
    have hmap (g : PSL2MatrixGroup F) :
        (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g).toMonoidHom =
          U₀.map (MulAut.conj (g * kP⁻¹)).toMonoidHom := by
      rw [← hP_to_U₀, Subgroup.map_map]
      congr 1
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    intro x hx g₁ g₂ hx₁ hx₂
    rw [hmap g₁] at hx₁ ⊢
    rw [hmap g₂] at hx₂ ⊢
    exact hU₀_same_family x hx (g₁ * kP⁻¹) (g₂ * kP⁻¹) hx₁ hx₂
  let splitTorusSL : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F :=
    splitTorusSLHom F
  let splitTorus : Fˣ →* PSL2MatrixGroup F :=
    qSL.comp splitTorusSL
  have hsplit_props :
      IsCyclic splitTorus.range ∧
        Nat.card splitTorus.range =
          (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
    have hf_ne_zero : f ≠ 0 :=
      huppert_II_8_27_field_exponent_ne_zero hFcard
    have hcard_roots :
          Nat.card (rootsOfUnity 2 F) =
            Nat.gcd (Nat.card F - 1) 2 := by
        let e :=
          Equiv.Set.image ((↑) : Fˣ → F) (rootsOfUnity 2 F : Set Fˣ)
            Units.val_injective
        have he :
            Nat.card (rootsOfUnity 2 F) =
              Nat.card (((↑) : Fˣ → F) '' (rootsOfUnity 2 F : Set Fˣ)) :=
          Nat.card_congr e
        rw [Units.val_set_image_rootsOfUnity_two] at he
        by_cases hp_two : p = 2
        · have htwo : (2 : F) = 0 := by
            subst p
            exact CharP.cast_eq_zero F 2
          have hneg_one : (-1 : F) = 1 := by
            apply (neg_eq_iff_add_eq_zero).2
            have hone_add_one : (1 : F) + 1 = 0 := by
              rw [show (1 : F) + 1 = 2 by norm_num, htwo]
            exact hone_add_one
          have hleft : Nat.card (rootsOfUnity 2 F) = 1 := by
            simpa [hneg_one] using he
          have hq_even : Even (Nat.card F) := by
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hf_ne_zero
            rw [hFcard, hp_two, hk, pow_succ]
            use 2 ^ k
            ring
          have hq_sub_one_odd : Odd (Nat.card F - 1) := by
            rw [← Nat.not_even_iff_odd]
            intro heven
            have hparity :=
              (Nat.even_sub (show 1 ≤ Nat.card F from (Finite.one_lt_card (α := F)).le)).mp
                heven
            exact Nat.not_even_one (hparity.mp hq_even)
          have hgcd : Nat.gcd (Nat.card F - 1) 2 = 1 :=
            Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
          rw [hleft, hgcd]
        · have hring_char_ne_two : ringChar F ≠ 2 := by
            rw [ringChar.eq F p]
            exact hp_two
          have hneg_one : (-1 : F) ≠ 1 :=
            Ring.neg_one_ne_one_of_char_ne_two hring_char_ne_two
          have hleft : Nat.card (rootsOfUnity 2 F) = 2 := by
            simpa [hneg_one, Ne.symm hneg_one] using he
          have hq_odd : Odd (Nat.card F) := by
            rw [hFcard]
            exact ((Fact.out : p.Prime).odd_of_ne_two hp_two).pow
          have htwo_dvd : 2 ∣ Nat.card F - 1 := by
            rcases hq_odd with ⟨k, hk⟩
            use k
            omega
          have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
            Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
              (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
          rw [hleft, hgcd]
    have hsplit_mem_ker_iff (a : Fˣ) :
        a ∈ splitTorus.ker ↔ a ∈ rootsOfUnity 2 F := by
      rw [MonoidHom.mem_ker, mem_rootsOfUnity]
      constructor
      · intro ha
        have hcenter :
            splitTorusSL a ∈
              Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
          (QuotientGroup.eq_one_iff (splitTorusSL a)).mp ha
        have hscalar :=
          Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
        have ha_inv_val := congrFun (congrFun hscalar (1 : Fin 2)) (1 : Fin 2)
        have ha_inv : a = a⁻¹ := by
          apply Units.ext
          simpa [splitTorusSL] using ha_inv_val
        simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp ha_inv)
      · intro ha
        apply (QuotientGroup.eq_one_iff (splitTorusSL a)).mpr
        rw [Matrix.SpecialLinearGroup.mem_center_iff]
        refine ⟨(a : F), ?_, ?_⟩
        · simpa using congrArg Units.val ha
        · have ha_inv : a = a⁻¹ :=
            eq_inv_iff_mul_eq_one.mpr (by simpa [pow_two] using ha)
          have ha_inv_val : (a : F) = (a⁻¹ : F) := by
            simpa using congrArg Units.val ha_inv
          simpa [splitTorusSL] using
            splitTorusSLHom_eq_scalar_of_val_eq_inv a ha_inv_val
    have hsplit_ker_eq : splitTorus.ker = rootsOfUnity 2 F := by
      ext a
      exact hsplit_mem_ker_iff a
    have hsplit_ker_card :
        Nat.card splitTorus.ker = Nat.gcd (Nat.card F - 1) 2 := by
      rw [hsplit_ker_eq, hcard_roots]
    have hsplit_range_mul :
        Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
          Nat.card F - 1 := by
      calc
        Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
            splitTorus.ker.index * Nat.card splitTorus.ker := by
          rw [Subgroup.index_ker, hsplit_ker_card]
        _ = Nat.card Fˣ := splitTorus.ker.index_mul_card
        _ = Nat.card F - 1 := by
          simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := F))
    have hsplit_range_card :
        Nat.card splitTorus.range =
          (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
      apply Nat.eq_div_of_mul_eq_left
      · rw [← hcard_roots]
        exact Nat.ne_of_gt Nat.card_pos
      · exact hsplit_range_mul
    have hsplit_range_cyclic : IsCyclic splitTorus.range := by
      have hUnitsCyclic : IsCyclic Fˣ := by
        let : IsCyclic (⊤ : Subgroup Fˣ) := isCyclic_subgroup_units ⊤
        exact isCyclic_of_surjective
          ((⊤ : Subgroup Fˣ).subtype) (by
            intro a
            exact ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩)
      let : IsCyclic Fˣ := hUnitsCyclic
      exact isCyclic_of_surjective splitTorus.rangeRestrict
        splitTorus.rangeRestrict_surjective
    exact ⟨hsplit_range_cyclic, hsplit_range_card⟩
  have h85_split_semisimple
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hdisc_nonzero :
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 ≠ (4 : F))
    (heigen : ∃ (μ : F) (v : Fin 2 → F), v ≠ 0 ∧
      (A : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v) :
    ∃ g : PSL2MatrixGroup F,
      qSL A ∈ splitTorus.range.map (MulAut.conj g).toMonoidHom := by
    classical
    let trA : F := Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)
    change trA ^ 2 ≠ (4 : F) at hdisc_nonzero
    rcases heigen with ⟨μ, v, hv_ne, hAv⟩
    have hμ_ne : μ ≠ 0 := by
      intro hμ
      subst μ
      have hzero :
          (A : Matrix (Fin 2) (Fin 2) F).mulVec v = 0 := by
        simpa using hAv
      have hrecover :
          ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F).mulVec
              ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) = v := by
        calc
          _ = (((A⁻¹ * A : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F).mulVec v) :=
            Matrix.mulVec_mulVec v _ _
          _ = v := by rw [inv_mul_cancel]; simp
      apply hv_ne
      calc
        v = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F).mulVec
                ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) := hrecover.symm
        _ = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F).mulVec 0 := by rw [hzero]
        _ = 0 := by simp
    let a : Fˣ := Units.mk0 μ hμ_ne
    have hdetA :
        Matrix.det (A : Matrix (Fin 2) (Fin 2) F) = 1 := A.property
    have hkernel :
        (Matrix.scalar (Fin 2) μ -
          (A : Matrix (Fin 2) (Fin 2) F)).mulVec v = 0 := by
      rw [Matrix.sub_mulVec]
      have hscalar :
          (Matrix.scalar (Fin 2) μ).mulVec v = μ • v := by
        ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct]
      rw [hscalar, hAv, sub_self]
    have hdet_zero :
        (Matrix.scalar (Fin 2) μ -
          (A : Matrix (Fin 2) (Fin 2) F)).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv_ne, hkernel⟩
    have hdet_formula (x : F) :
        (Matrix.scalar (Fin 2) x -
          (A : Matrix (Fin 2) (Fin 2) F)).det =
            x ^ 2 - trA * x + 1 := by
      calc
        _ = x ^ 2 - trA * x +
            Matrix.det (A : Matrix (Fin 2) (Fin 2) F) := by
              simp [Matrix.det_fin_two, Matrix.trace_fin_two, trA]
              have hdetCoord := hdetA
              rw [Matrix.det_fin_two] at hdetCoord
              linear_combination hdetCoord
        _ = _ := by rw [hdetA]
    have hpoly : μ ^ 2 - trA * μ + 1 = 0 := by
      rw [← hdet_formula]
      exact hdet_zero
    have htrace_mu : trA = μ + μ⁻¹ := by
      apply mul_right_cancel₀ hμ_ne
      calc
        trA * μ = μ ^ 2 + 1 := by
          linear_combination -hpoly
        _ = (μ + μ⁻¹) * μ := by
          field_simp [hμ_ne]
    have hμ_ne_inv : μ ≠ μ⁻¹ := by
      intro hμ
      apply hdisc_nonzero
      have hμ_sq : μ ^ 2 = 1 := by
        calc
          μ ^ 2 = μ * μ := by rw [pow_two]
          _ = μ * μ⁻¹ := congrArg (fun z : F => μ * z) hμ
          _ = 1 := mul_inv_cancel₀ hμ_ne
      rw [htrace_mu, ← hμ]
      calc
        (μ + μ) ^ 2 = 4 * μ ^ 2 := by ring
        _ = 4 := by rw [hμ_sq, mul_one]
    have hother_eigen :
        ∃ w : Fin 2 → F, w ≠ 0 ∧
          (A : Matrix (Fin 2) (Fin 2) F).mulVec w = μ⁻¹ • w := by
      have hpoly_inv : (μ⁻¹) ^ 2 - trA * μ⁻¹ + 1 = 0 := by
        rw [htrace_mu]
        field_simp [hμ_ne]
        ring
      have hdet_inv :
          (Matrix.scalar (Fin 2) μ⁻¹ -
            (A : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
        rw [hdet_formula]
        exact hpoly_inv
      obtain ⟨w, hw_ne, hw⟩ :=
        Matrix.exists_mulVec_eq_zero_iff.mpr hdet_inv
      refine ⟨w, hw_ne, ?_⟩
      have hscalar :
          (Matrix.scalar (Fin 2) μ⁻¹).mulVec w = μ⁻¹ • w := by
        ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct]
      rw [Matrix.sub_mulVec, hscalar] at hw
      exact (sub_eq_zero.mp hw).symm
    rcases hother_eigen with ⟨w, hw_ne, hAw⟩
    have hbasis_conjugates :
        ∃ G : Matrix.SpecialLinearGroup (Fin 2) F,
          A = G * splitTorusSL a * G⁻¹ := by
      let fA : Module.End F (Fin 2 → F) :=
        Matrix.mulVecLin (A : Matrix (Fin 2) (Fin 2) F)
      let eigenvalue : Fin 2 → F := ![μ, μ⁻¹]
      let eigenvector : Fin 2 → (Fin 2 → F) := ![v, w]
      have heigenvalue_injective : Function.Injective eigenvalue := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact (hμ_ne_inv (by simpa [eigenvalue] using hij)).elim
        · exact (hμ_ne_inv (by simpa [eigenvalue] using hij.symm)).elim
        · rfl
      have heigenvector :
          ∀ i, fA.HasEigenvector (eigenvalue i) (eigenvector i) := by
        intro i
        fin_cases i
        · refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
          · simpa [fA, eigenvalue, eigenvector,
              Matrix.mulVecLin_apply] using hAv
          · simpa [eigenvector] using hv_ne
        · refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
          · simpa [fA, eigenvalue, eigenvector,
              Matrix.mulVecLin_apply] using hAw
          · simpa [eigenvector] using hw_ne
      have hlinearIndependent :
          LinearIndependent F eigenvector :=
        Module.End.eigenvectors_linearIndependent' fA eigenvalue
          heigenvalue_injective eigenvector heigenvector
      let δ : F := v 0 * w 1 - w 0 * v 1
      have hδ_ne : δ ≠ 0 := by
        intro hδ
        have hcoeff := Fintype.linearIndependent_iff.mp hlinearIndependent
        by_cases hv1 : v 1 = 0
        · have hv0 : v 0 ≠ 0 := by
            intro hv0
            apply hv_ne
            funext i
            fin_cases i <;> assumption
          have hw1 : w 1 = 0 := by
            apply mul_left_cancel₀ hv0
            have : v 0 * w 1 = 0 := by
              simpa [δ, hv1] using hδ
            simpa using this
          let c : Fin 2 → F := ![w 0, -v 0]
          have hsum : ∑ i, c i • eigenvector i = 0 := by
            funext j
            fin_cases j
            all_goals simp [Fin.sum_univ_two, c, eigenvector, hv1, hw1,
              mul_comm]
            all_goals ring
          have hc := hcoeff c hsum 1
          exact hv0 (by simpa [c] using neg_eq_zero.mp hc)
        · let c : Fin 2 → F := ![w 1, -v 1]
          have hsum : ∑ i, c i • eigenvector i = 0 := by
            funext j
            fin_cases j
            · simpa [Fin.sum_univ_two, c, eigenvector, δ,
                sub_eq_add_neg, mul_comm] using hδ
            · simp [Fin.sum_univ_two, c, eigenvector]
              ring
          have hc := hcoeff c hsum 1
          exact hv1 (by simpa [c] using neg_eq_zero.mp hc)
      let G : Matrix.SpecialLinearGroup (Fin 2) F :=
        ⟨!![v 0, δ⁻¹ * w 0; v 1, δ⁻¹ * w 1], by
          rw [Matrix.det_fin_two]
          change v 0 * (δ⁻¹ * w 1) -
            (δ⁻¹ * w 0) * v 1 = 1
          calc
            _ = δ⁻¹ * δ := by simp [δ]; ring
            _ = 1 := inv_mul_cancel₀ hδ_ne⟩
      have hAG : A * G = G * splitTorusSL a := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j
        · simpa [G, splitTorusSL, Matrix.mul_apply, Matrix.mulVec,
            dotProduct, a, mul_comm] using congrFun hAv 0
        · have hw := congrFun hAw 0
          simp [Matrix.mulVec, dotProduct] at hw
          simp [G, splitTorusSL, Matrix.mul_apply, a]
          linear_combination δ⁻¹ * hw
        · simpa [G, splitTorusSL, Matrix.mul_apply, Matrix.mulVec,
            dotProduct, a, mul_comm] using congrFun hAv 1
        · have hw := congrFun hAw 1
          simp [Matrix.mulVec, dotProduct] at hw
          simp [G, splitTorusSL, Matrix.mul_apply, a]
          linear_combination δ⁻¹ * hw
      refine ⟨G, ?_⟩
      apply mul_right_cancel (b := G)
      calc
        A * G = G * splitTorusSL a := hAG
        _ = (G * splitTorusSL a * G⁻¹) * G := by group
    rcases hbasis_conjugates with ⟨G, hG⟩
    refine ⟨qSL G, ?_⟩
    refine ⟨splitTorus a, ⟨a, rfl⟩, ?_⟩
    change qSL G * splitTorus a * (qSL G)⁻¹ = qSL A
    rw [hG]
    simp [splitTorus, qSL]
  have h85_repeated_root
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hA_one : qSL A ≠ 1)
    (hdisc_zero :
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 = (4 : F)) :
    (∃ g : PSL2MatrixGroup F,
      qSL A ∈ U₀.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : PSL2MatrixGroup F,
      qSL A ∈ splitTorus.range.map (MulAut.conj g).toMonoidHom) := by
    classical
    let trA : F := Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)
    change trA ^ 2 = (4 : F) at hdisc_zero
    by_cases hA_split : qSL A ∈ splitTorus.range
    · right
      refine ⟨1, ?_⟩
      exact ⟨qSL A, hA_split, by simp⟩
    · have hA_parabolic :
          ((A : Matrix (Fin 2) (Fin 2) F).IsParabolic) := by
        refine ⟨?_, ?_⟩
        · rintro ⟨r, hr⟩
          apply hA_one
          apply (QuotientGroup.eq_one_iff A).mpr
          rw [Matrix.SpecialLinearGroup.mem_center_iff]
          refine ⟨r, ?_, ?_⟩
          · have hdet := A.property
            rw [← hr, Matrix.det_fin_two] at hdet
            change r ^ 2 = 1
            simpa [pow_two] using hdet
          · exact hr
        · have hdisc : (A : Matrix (Fin 2) (Fin 2) F).discr = trA ^ 2 - (4 : F) := by
            simp [Matrix.discr_fin_two, trA, A.property]
          rw [hdisc, hdisc_zero, sub_self]
      have h85_repeated_root_fixed_line :
          ∃ v : Fin 2 → F, v ≠ 0 ∧
            ∃ μ : F, ((A : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v) := by
        have htrace :
            Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) = (2 : F) ∨
              Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) = -(2 : F) := by
          apply (sq_eq_sq_iff_eq_or_eq_neg).mp
          calc
            _ = (4 : F) := hdisc_zero
            _ = (2 : F) ^ 2 := by norm_num
        have hdet_coord :
            (A : Matrix (Fin 2) (Fin 2) F) 0 0 *
                (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
              (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
          have hdetA := A.property
          change Matrix.det (A : Matrix (Fin 2) (Fin 2) F) = 1 at hdetA
          rw [Matrix.det_fin_two] at hdetA
          exact hdetA
        rcases htrace with htrace | htrace
        · have htrace_coord :
              (A : Matrix (Fin 2) (Fin 2) F) 0 0 +
                (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 2 := by
            simpa [Matrix.trace_fin_two] using htrace
          have hdet_zero :
              (Matrix.scalar (Fin 2) (1 : F) -
                (A : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
            calc
              _ = 1 -
                  ((A : Matrix (Fin 2) (Fin 2) F) 0 0 +
                    (A : Matrix (Fin 2) (Fin 2) F) 1 1) +
                  ((A : Matrix (Fin 2) (Fin 2) F) 0 0 *
                      (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
                    (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                      (A : Matrix (Fin 2) (Fin 2) F) 1 0) := by
                        simp [Matrix.det_fin_two]
                        ring
              _ = 0 := by rw [htrace_coord, hdet_coord]; ring
          obtain ⟨v, hv_ne, hv⟩ :=
            Matrix.exists_mulVec_eq_zero_iff.mpr hdet_zero
          refine ⟨v, hv_ne, 1, ?_⟩
          have hscalar :
              (Matrix.scalar (Fin 2) (1 : F)).mulVec v = (1 : F) • v := by
            ext i
            fin_cases i <;> simp [Matrix.mulVec, dotProduct]
          rw [Matrix.sub_mulVec, hscalar] at hv
          exact (sub_eq_zero.mp hv).symm
        · have htrace_coord :
              (A : Matrix (Fin 2) (Fin 2) F) 0 0 +
                (A : Matrix (Fin 2) (Fin 2) F) 1 1 = -2 := by
            simpa [Matrix.trace_fin_two] using htrace
          have hdet_zero :
              (Matrix.scalar (Fin 2) (-1 : F) -
                (A : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
            calc
              _ = 1 +
                  ((A : Matrix (Fin 2) (Fin 2) F) 0 0 +
                    (A : Matrix (Fin 2) (Fin 2) F) 1 1) +
                  ((A : Matrix (Fin 2) (Fin 2) F) 0 0 *
                      (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
                    (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                      (A : Matrix (Fin 2) (Fin 2) F) 1 0) := by
                        simp [Matrix.det_fin_two]
                        ring
              _ = 0 := by rw [htrace_coord, hdet_coord]; ring
          obtain ⟨v, hv_ne, hv⟩ :=
            Matrix.exists_mulVec_eq_zero_iff.mpr hdet_zero
          refine ⟨v, hv_ne, -1, ?_⟩
          have hscalar :
              (Matrix.scalar (Fin 2) (-1 : F)).mulVec v = (-1 : F) • v := by
            ext i
            fin_cases i <;> simp [Matrix.mulVec, dotProduct]
          rw [Matrix.sub_mulVec, hscalar] at hv
          exact (sub_eq_zero.mp hv).symm
      have h85_repeated_root_jordan_basis :
          ∃ (G : Matrix.SpecialLinearGroup (Fin 2) F) (t : F),
            qSL A = qSL (G * unipotentSL t * G⁻¹) := by
        rcases h85_repeated_root_fixed_line with ⟨v, hv_ne, μ, heigen⟩
        have hw :
            ∃ w : Fin 2 → F, v 0 * w 1 - w 0 * v 1 = 1 := by
          by_cases hv0 : v 0 = 0
          · have hv1 : v 1 ≠ 0 := by
              intro hv1
              apply hv_ne
              funext i
              fin_cases i <;> assumption
            refine ⟨![(-(v 1)⁻¹), 0], ?_⟩
            simp [hv0, hv1]
          · refine ⟨![0, (v 0)⁻¹], ?_⟩
            simp [hv0]
        rcases hw with ⟨w, hw⟩
        let G : Matrix.SpecialLinearGroup (Fin 2) F :=
          ⟨!![v 0, w 0; v 1, w 1], by
            simpa [Matrix.det_fin_two] using hw⟩
        let e0 : Fin 2 → F := ![1, 0]
        have hG_e0 :
            (G : Matrix (Fin 2) (Fin 2) F).mulVec e0 = v := by
          ext i
          fin_cases i <;>
            simp [G, e0, Matrix.mulVec, dotProduct]
        let B : Matrix.SpecialLinearGroup (Fin 2) F :=
          G⁻¹ * A * G
        have hGinv_v :
            (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec v =
              e0 := by
          calc
            _ = (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
                ((G : Matrix (Fin 2) (Fin 2) F).mulVec e0) := by
                  rw [hG_e0]
            _ = (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 *
                (G : Matrix (Fin 2) (Fin 2) F)).mulVec e0) :=
                  Matrix.mulVec_mulVec e0 _ _
            _ = e0 := by
              change (((G⁻¹ * G : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F).mulVec e0) = e0
              rw [inv_mul_cancel]
              simp
        have hB_e0 :
            (B : Matrix (Fin 2) (Fin 2) F).mulVec e0 =
              μ • e0 := by
          calc
            _ = (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
                ((A : Matrix (Fin 2) (Fin 2) F).mulVec
                  ((G : Matrix (Fin 2) (Fin 2) F).mulVec e0)) := by
                    simp only [B, Matrix.SpecialLinearGroup.coe_mul]
                    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
            _ = (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
                ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) := by
                  rw [hG_e0]
            _ = (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
                (μ • v) := by rw [heigen]
            _ = μ •
                (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec v :=
                  Matrix.mulVec_smul _ _ _
            _ = μ • e0 := by rw [hGinv_v]
        have hB10 :
            (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
          have h := congrFun hB_e0 1
          simpa [e0, Matrix.mulVec, dotProduct] using h
        have hB_parabolic :
            (B : Matrix (Fin 2) (Fin 2) F).IsParabolic := by
          have h := (Matrix.isParabolic_conj'_iff
            (Matrix.SpecialLinearGroup.toGL G)
            (m := (A : Matrix (Fin 2) (Fin 2) F))).mpr
              hA_parabolic
          rw [← Matrix.coe_units_inv] at h
          have hcoe_inv :
              ((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F) =
                (((Matrix.SpecialLinearGroup.toGL G)⁻¹ :
                    GL (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F) := by
            exact congrArg
              (fun X : GL (Fin 2) F =>
                (X : Matrix (Fin 2) (Fin 2) F))
              (map_inv
                (Matrix.SpecialLinearGroup.toGL
                  (n := Fin 2) (R := F)) G)
          rw [← hcoe_inv] at h
          simpa [B] using h
        have hBdiag :
            (B : Matrix (Fin 2) (Fin 2) F) 0 0 =
              (B : Matrix (Fin 2) (Fin 2) F) 1 1 :=
          (Matrix.isParabolic_iff_of_upperTriangular hB10).mp
            hB_parabolic |>.1
        let a : F := (B : Matrix (Fin 2) (Fin 2) F) 0 0
        have ha_sq : a ^ 2 = 1 := by
          have hdetB := B.property
          change Matrix.det (B : Matrix (Fin 2) (Fin 2) F) = 1
            at hdetB
          rw [Matrix.det_fin_two, hB10, mul_zero, sub_zero,
            ← hBdiag] at hdetB
          simpa [a, pow_two] using hdetB
        have ha_ne : a ≠ 0 := by
          intro ha
          rw [ha, zero_pow (by norm_num)] at ha_sq
          exact zero_ne_one ha_sq
        let t : F :=
          a⁻¹ * (B : Matrix (Fin 2) (Fin 2) F) 0 1
        let z : Matrix.SpecialLinearGroup (Fin 2) F :=
          ⟨Matrix.scalar (Fin 2) a, by
            simpa [Matrix.det_fin_two, pow_two] using ha_sq⟩
        have hz_center :
            z ∈ Subgroup.center
              (Matrix.SpecialLinearGroup (Fin 2) F) := by
          rw [Matrix.SpecialLinearGroup.mem_center_iff]
          exact ⟨a, ha_sq, rfl⟩
        have hB_factor : B = z * unipotentSL t := by
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j
          · simp [z, t, unipotentSL, Matrix.mul_apply, a]
          · simp [z, t, unipotentSL, Matrix.mul_apply, a, ha_ne]
          · simp [z, t, unipotentSL, Matrix.mul_apply, hB10]
          · simp [z, t, unipotentSL, Matrix.mul_apply, a, hBdiag]
        have hqz : qSL z = 1 :=
          (QuotientGroup.eq_one_iff z).mpr hz_center
        have hqB : qSL B = qSL (unipotentSL t) := by
          rw [hB_factor, map_mul, hqz, one_mul]
        refine ⟨G, t, ?_⟩
        calc
          qSL A = qSL (G * B * G⁻¹) := by
            simp [B, mul_assoc]
          _ = qSL G * qSL B * qSL G⁻¹ := by simp
          _ = qSL G * qSL (unipotentSL t) * qSL G⁻¹ := by
            rw [hqB]
          _ = qSL (G * unipotentSL t * G⁻¹) := by simp
      have h85_repeated_root_nonsplit_unipotent :
          ∃ g : PSL2MatrixGroup F,
            qSL A ∈ U₀.map (MulAut.conj g).toMonoidHom := by
        rcases h85_repeated_root_jordan_basis with ⟨G, t, hG⟩
        refine ⟨qSL G, ?_⟩
        refine ⟨unipotent t, ⟨Multiplicative.ofAdd t, rfl⟩, ?_⟩
        rw [hG]
        change qSL G * qSL (unipotentSL t) * (qSL G)⁻¹ =
          qSL (G * unipotentSL t * G⁻¹)
        simp [qSL]
      exact Or.inl h85_repeated_root_nonsplit_unipotent
  obtain ⟨S, hS_cyclic, hS_card, _hS_normalizer, _hS_reflection,
      hS_weakTI,
      hS_noEigen⟩ :=
    h84_nonsplit_torus_data hFcard
  refine ⟨splitTorus.range, S, hsplit_props.1, hsplit_props.2,
    hS_cyclic, hS_card, ?_⟩
  have hprojective_cover :
      ∀ x : PSL2MatrixGroup F, x ≠ 1 →
        (∃ g, x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
          (MulAut.conj g).toMonoidHom) ∨
        (∃ g, x ∈ splitTorus.range.map
          (MulAut.conj g).toMonoidHom) ∨
        (∃ g, x ∈ S.map (MulAut.conj g).toMonoidHom) := by
    intro x hx
    refine QuotientGroup.induction_on x ?_ hx
    intro A hxA
    have hA_ne : qSL A ≠ 1 := by
      simpa [qSL] using hxA
    by_cases hdisc_zero :
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 = (4 : F)
    · rcases h85_repeated_root A hA_ne hdisc_zero with hU₀ | hsplit
      · rcases hU₀ with ⟨g, hg⟩
        left
        refine ⟨g * kP, ?_⟩
        have hmap :
            U₀.map (MulAut.conj g).toMonoidHom =
              (P : Subgroup (PSL2MatrixGroup F)).map
                (MulAut.conj (g * kP)).toMonoidHom := by
          rw [← hP_to_U₀, Subgroup.map_map]
          congr 1
          ext y
          simp [MulAut.conj_apply, mul_assoc]
        rw [← hmap]
        exact hg
      · exact Or.inr (Or.inl hsplit)
    · by_cases heigen : ∃ (μ : F) (v : Fin 2 → F), v ≠ 0 ∧
          (A : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v
      · exact Or.inr (Or.inl (h85_split_semisimple A hdisc_zero heigen))
      · exact Or.inr (Or.inr (by
          simpa [qSL] using hS_noEigen A hdisc_zero heigen))
  have hPcard :
      Nat.card (P : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    obtain ⟨eP⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard P
    exact (Nat.card_congr eP.toEquiv).symm
  have hP_split_coprime :
      Nat.Coprime (Nat.card (P : Subgroup (PSL2MatrixGroup F)))
        (Nat.card splitTorus.range) := by
    rw [hPcard, hsplit_props.2]
    exact hq_coprime_split_order (Nat.card F) Nat.card_pos
  have hP_nonsplit_coprime :
      Nat.Coprime (Nat.card (P : Subgroup (PSL2MatrixGroup F)))
        (Nat.card S) := by
    rw [hPcard, hS_card]
    exact hq_coprime_nonsplit_order (Nat.card F) Nat.card_pos
  have hsplit_nonsplit_coprime :
      Nat.Coprime (Nat.card splitTorus.range) (Nat.card S) := by
    rw [hsplit_props.2, hS_card]
    exact hsplit_nonsplit_order_coprime (Nat.card F)
      (Finite.one_lt_card (α := F))
  have hsplit_weakTI :
      ∀ y : PSL2MatrixGroup F, y ∈ splitTorus.range → y ≠ 1 →
        ∀ g : PSL2MatrixGroup F,
          g * y * g⁻¹ ∈ splitTorus.range →
            g ∈ Subgroup.normalizer
              (splitTorus.range : Set (PSL2MatrixGroup F)) := by
    intro y hy hy_ne g hgy
    rcases hy with ⟨a, rfl⟩
    have ha_ne_inv : (a : F) ≠ (a⁻¹ : F) := by
      intro hai
      apply hy_ne
      change qSL (splitTorusSL a) = 1
      apply (QuotientGroup.eq_one_iff (splitTorusSL a)).mpr
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      have haiU : a = a⁻¹ := by
        apply Units.ext
        simpa using hai
      have ha_sq : (a : F) ^ 2 = 1 := by
        have hsqU := congrArg (fun u : Fˣ => (u : F))
          (eq_inv_iff_mul_eq_one.mp haiU)
        simpa [pow_two] using hsqU
      refine ⟨(a : F), ha_sq, ?_⟩
      simpa [splitTorusSL] using
        splitTorusSLHom_eq_scalar_of_val_eq_inv a hai
    refine QuotientGroup.induction_on g ?_ hgy
    intro A hAconj
    rcases hAconj with ⟨b, hb⟩
    have hq :
        qSL (splitTorusSL b) =
          qSL (A * splitTorusSL a * A⁻¹) := by
      simpa [qSL, splitTorus] using hb
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hq with
      ⟨z, hz, hzeq⟩
    have hzeqA :
        splitTorusSL b * z * A = A * splitTorusSL a := by
      calc
        splitTorusSL b * z * A =
            (A * splitTorusSL a * A⁻¹) * A := by rw [hzeq]
        _ = A * splitTorusSL a := by group
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz (0 : Fin 2)
    have hmat := congrArg Subtype.val hzeqA
    change (!![(b : F), 0; 0, (b⁻¹ : F)] :
          Matrix (Fin 2) (Fin 2) F) *
        (z : Matrix (Fin 2) (Fin 2) F) *
          (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) *
        !![(a : F), 0; 0, (a⁻¹ : F)] at hmat
    rw [← hscalar] at hmat
    rcases split_matrix_diag_or_antidiag A a b
        ((z : Matrix (Fin 2) (Fin 2) F) 0 0)
        ha_ne_inv hmat with hdiag | hanti
    · rcases hdiag with ⟨h01, h10⟩
      have hmap_le :
          splitTorus.range.map
              (MulAut.conj (qSL A)).toMonoidHom ≤
            splitTorus.range := by
        intro v hv
        rcases hv with ⟨w, hw, rfl⟩
        rcases hw with ⟨c, rfl⟩
        refine ⟨c, ?_⟩
        have hcomm :
            A * splitTorusSL c = splitTorusSL c * A := by
          simpa [splitTorusSL] using
            mul_splitTorusSLHom_eq_splitTorusSLHom_mul_of_offDiagonal_eq_zero
              A h01 h10 c
        have hconj :
            A * splitTorusSL c * A⁻¹ = splitTorusSL c := by
          rw [hcomm]
          simp [mul_assoc]
        simpa [qSL, splitTorus, MulAut.conj_apply] using
          (congrArg qSL hconj).symm
      have hmap_eq :
          splitTorus.range.map
              (MulAut.conj (qSL A)).toMonoidHom =
            splitTorus.range := by
        apply Subgroup.eq_of_le_of_card_ge hmap_le
        rw [Subgroup.card_map_of_injective
          (K := splitTorus.range)
          (f := (MulAut.conj (qSL A)).toMonoidHom)
          (MulAut.conj (qSL A)).injective]
      rw [← Subgroup.conjAct_pointwise_smul_iff]
      exact hmap_eq
    · rcases hanti with ⟨h00, h11⟩
      have hmap_le :
          splitTorus.range.map
              (MulAut.conj (qSL A)).toMonoidHom ≤
            splitTorus.range := by
        intro v hv
        rcases hv with ⟨w, hw, rfl⟩
        rcases hw with ⟨c, rfl⟩
        refine ⟨c⁻¹, ?_⟩
        have hcomm :
            A * splitTorusSL c = splitTorusSL c⁻¹ * A := by
          simpa [splitTorusSL] using
            mul_splitTorusSLHom_eq_inv_mul_of_diagonal_eq_zero A h00 h11 c
        have hconj :
            A * splitTorusSL c * A⁻¹ = splitTorusSL c⁻¹ := by
          rw [hcomm]
          simp [mul_assoc]
        simpa [qSL, splitTorus, MulAut.conj_apply] using
          (congrArg qSL hconj).symm
      have hmap_eq :
          splitTorus.range.map
              (MulAut.conj (qSL A)).toMonoidHom =
            splitTorus.range := by
        apply Subgroup.eq_of_le_of_card_ge hmap_le
        rw [Subgroup.card_map_of_injective
          (K := splitTorus.range)
          (f := (MulAut.conj (qSL A)).toMonoidHom)
          (MulAut.conj (qSL A)).injective]
      rw [← Subgroup.conjAct_pointwise_smul_iff]
      exact hmap_eq
  have hprojective_TI_split :=
    hconjugate_family_unique_of_weak_ti splitTorus.range hsplit_weakTI
  have hprojective_TI_nonsplit :=
    hconjugate_family_unique_of_weak_ti S hS_weakTI
  have hprojective_TI_same_family :
      (∀ x : PSL2MatrixGroup F, x ≠ 1 → ∀ g₁ g₂,
        x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₁).toMonoidHom →
        x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₂).toMonoidHom →
        (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₁).toMonoidHom =
          (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₂).toMonoidHom) ∧
      (∀ x : PSL2MatrixGroup F, x ≠ 1 → ∀ g₁ g₂,
        x ∈ splitTorus.range.map (MulAut.conj g₁).toMonoidHom →
        x ∈ splitTorus.range.map (MulAut.conj g₂).toMonoidHom →
        splitTorus.range.map (MulAut.conj g₁).toMonoidHom =
          splitTorus.range.map (MulAut.conj g₂).toMonoidHom) ∧
      (∀ x : PSL2MatrixGroup F, x ≠ 1 → ∀ g₁ g₂,
        x ∈ S.map (MulAut.conj g₁).toMonoidHom →
        x ∈ S.map (MulAut.conj g₂).toMonoidHom →
        S.map (MulAut.conj g₁).toMonoidHom =
          S.map (MulAut.conj g₂).toMonoidHom) := by
    exact ⟨hprojective_TI_P, hprojective_TI_split,
      hprojective_TI_nonsplit⟩
  have hprojective_TI :
      ∀ x : PSL2MatrixGroup F, x ≠ 1 →
        ∀ T₁ T₂ : Subgroup (PSL2MatrixGroup F),
          x ∈ T₁ → x ∈ T₂ →
          ((∃ g, T₁ = (P : Subgroup (PSL2MatrixGroup F)).map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T₁ = splitTorus.range.map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T₁ = S.map (MulAut.conj g).toMonoidHom)) →
          ((∃ g, T₂ = (P : Subgroup (PSL2MatrixGroup F)).map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T₂ = splitTorus.range.map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T₂ = S.map (MulAut.conj g).toMonoidHom)) →
          T₁ = T₂ := by
    rcases hprojective_TI_same_family with
      ⟨hsameP, hsameSplit, hsameS⟩
    exact hthree_family_unique_of_same_family
      (P : Subgroup (PSL2MatrixGroup F)) splitTorus.range S
      hP_split_coprime hP_nonsplit_coprime hsplit_nonsplit_coprime
      hsameP hsameSplit hsameS
  intro x hx
  rcases hprojective_cover x hx with hP | hU | hS
  · let T := (P : Subgroup (PSL2MatrixGroup F)).map
      (MulAut.conj hP.choose).toMonoidHom
    refine ⟨T, ⟨hP.choose_spec, Or.inl ⟨hP.choose, rfl⟩⟩, ?_⟩
    intro T' hT'
    exact hprojective_TI x hx T' T hT'.1 hP.choose_spec
      hT'.2 (Or.inl ⟨hP.choose, rfl⟩)
  · let T := splitTorus.range.map
      (MulAut.conj hU.choose).toMonoidHom
    refine ⟨T, ⟨hU.choose_spec, Or.inr (Or.inl ⟨hU.choose, rfl⟩)⟩, ?_⟩
    intro T' hT'
    exact hprojective_TI x hx T' T hT'.1 hU.choose_spec
      hT'.2 (Or.inr (Or.inl ⟨hU.choose, rfl⟩))
  · let T := S.map (MulAut.conj hS.choose).toMonoidHom
    refine ⟨T, ⟨hS.choose_spec, Or.inr (Or.inr ⟨hS.choose, rfl⟩)⟩, ?_⟩
    intro T' hT'
    exact hprojective_TI x hx T' T hT'.1 hS.choose_spec
      hT'.2 (Or.inr (Or.inr ⟨hS.choose, rfl⟩))

/-- Huppert II.8.5(a): the nonidentity elements of PSL(2,p^f) are
partitioned by the conjugates of a Sylow p-subgroup and the split and
nonsplit cyclic tori. -/
public theorem huppert_II_8_5_a_psl2_partition
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f)
    (P : Sylow p (PSL2MatrixGroup F)) :
    ∃ U S : Subgroup (PSL2MatrixGroup F),
      IsCyclic U ∧
      Nat.card U =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      ∀ x : PSL2MatrixGroup F, x ≠ 1 →
        ∃! T : Subgroup (PSL2MatrixGroup F),
          x ∈ T ∧
            ((∃ g, T = (P : Subgroup (PSL2MatrixGroup F)).map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = S.map (MulAut.conj g).toMonoidHom)) := by
  exact huppert_II_8_5_a_psl2_cover hFcard P

end Dickson
end CFSG.Glauberman
