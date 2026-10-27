module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Tools
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L35Words
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutClass
import CFSG.ClassicalInvolution.Q3.TL4E3S3GenL3
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofGraphConj

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable [Fact (Nat.Prime 5)]

theorem card_galoisField_five_one : Nat.card (GaloisField 5 1) = 5 := by
  rw [GaloisField.card 5 1 one_ne_zero, pow_one]

theorem five_eq_zero_galoisField_five_one : (5 : GaloisField 5 1) = 0 := by
  have := CharP.cast_eq_zero (GaloisField 5 1) 5
  exact_mod_cast this

theorem exists_natCast_galoisField_five_one (a : GaloisField 5 1) :
    ∃ n : ℕ, (n : GaloisField 5 1) = a := by
  set e := GaloisField.equivZmodP 5
  refine ⟨(e a).val, ?_⟩
  have h1 : ((e a).val : GaloisField 5 1) = algebraMap (ZMod 5) (GaloisField 5 1) (e a) := by
    rw [← map_natCast (algebraMap (ZMod 5) (GaloisField 5 1)), ZMod.natCast_zmod_val]
  rw [h1]
  have h2 := e.symm.commutes (e a)
  simp only [Algebra.algebraMap_self, RingHom.id_apply, AlgEquiv.symm_apply_apply] at h2
  exact h2.symm

theorem proj_injective_five : Function.Injective (proj 3 (GaloisField 5 1)) :=
  CFSG.RankThree.PartTwo.KFacts.proj_three_injective (by rw [card_galoisField_five_one])

@[expose] noncomputable def l35XSL : SL(3, GaloisField 5 1) := ⟨l35X, det_l35X⟩

@[expose] noncomputable def l35TSL : SL(3, GaloisField 5 1) :=
  ⟨l35T, by simp [l35T, Matrix.det_fin_three]⟩

@[expose] noncomputable def l35ESL (a b : GaloisField 5 1) : SL(3, GaloisField 5 1) :=
  ⟨l35E a b, det_l35E a b⟩

theorem l35ESL_mul (a b c d : GaloisField 5 1) :
    l35ESL a b * l35ESL c d = l35ESL (a + c) (b + d) :=
  Subtype.ext (l35E_mul a b c d)

theorem l35ESL_zero : l35ESL 0 0 = 1 := Subtype.ext l35E_zero

theorem l35TSL_mul_self : l35TSL * l35TSL = 1 := Subtype.ext l35T_mul_self

theorem l35TSL_ne_one : l35TSL ≠ 1 := by
  intro h
  have e := congrArg (fun g : SL(3, GaloisField 5 1) =>
    (g : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) 0 0) h
  have e' : (-1 : GaloisField 5 1) = 1 := by simpa [l35TSL, l35T] using e
  have h5 := five_eq_zero_galoisField_five_one
  exact one_ne_zero (α := GaloisField 5 1) (by linear_combination h5 + 2 * e')

theorem orderOf_l35XSL : orderOf l35XSL = 31 := by
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ fun h => ?_
  · have h32 : l35XSL ^ 32 = l35XSL :=
      Subtype.ext (l35X_pow_thirtyTwo five_eq_zero_galoisField_five_one)
    rw [pow_succ] at h32
    exact mul_eq_right.mp h32
  · have e := congrArg (fun g : SL(3, GaloisField 5 1) =>
      (g : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) 0 0) h
    simp [l35XSL, l35X] at e

theorem inv_transpose_l35XSL : (l35XSL⁻¹).transpose = l35XSL⁻¹ := by
  apply Subtype.ext
  change ((l35X : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)).adjugate)ᵀ =
    (l35X : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)).adjugate
  rw [Matrix.adjugate_transpose, transpose_l35X]

theorem excl1411_dualAut_L3_5 : Excl1411 (dualAut 3 (GaloisField 5 1)) := by
  refine Or.inl ⟨proj 3 _ l35XSL, 31, 1, by norm_num, by norm_num, le_rfl,
    fun e he1 he4 => by interval_cases e <;> norm_num, ?_⟩
  have hδ : dualAut 3 (GaloisField 5 1) (proj 3 _ l35XSL) = (proj 3 _ l35XSL)⁻¹ := by
    rw [dualAut_proj, inv_transpose_l35XSL, map_inv]
  have hord : orderOf (proj 3 (GaloisField 5 1) l35XSL) = 31 := by
    rw [orderOf_injective _ proj_injective_five, orderOf_l35XSL]
  have hw : dualAut 3 (GaloisField 5 1) (proj 3 _ l35XSL) * (proj 3 _ l35XSL)⁻¹ =
      ((proj 3 (GaloisField 5 1) l35XSL) ^ 2)⁻¹ := by
    rw [hδ, sq, _root_.mul_inv_rev]
  rw [pow_one, hw, orderOf_inv, Nat.Coprime.orderOf_pow (by rw [hord]; norm_num), hord]

@[expose] noncomputable def l35EHom :
    Multiplicative (GaloisField 5 1 × GaloisField 5 1) →* projectiveSL 3 (GaloisField 5 1) :=
  (proj 3 _).comp
    { toFun := fun ab => l35ESL (Multiplicative.toAdd ab).1 (Multiplicative.toAdd ab).2
      map_one' := l35ESL_zero
      map_mul' := fun a b => by
        rw [l35ESL_mul]
        rfl }

theorem l35EHom_apply (a b : GaloisField 5 1) :
    l35EHom (Multiplicative.ofAdd (a, b)) = proj 3 _ (l35ESL a b) := rfl

theorem l35EHom_injective : Function.Injective l35EHom := by
  intro x y h
  have h1 := proj_injective_five h
  have h2 : l35E (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 =
      l35E (Multiplicative.toAdd y).1 (Multiplicative.toAdd y).2 := by
    have := congrArg (fun g : SL(3, GaloisField 5 1) =>
      (g : Matrix (Fin 3) (Fin 3) (GaloisField 5 1))) h1
    exact this
  have h3 := l35E_injective h2
  exact Multiplicative.toAdd.injective h3

theorem excl1411_conj_l35T :
    Excl1411 (MulAut.conj (proj 3 (GaloisField 5 1) l35TSL)) := by
  have h5 := five_eq_zero_galoisField_five_one
  refine Or.inr (Or.inr (Or.inl ⟨proj 3 _ (l35ESL 2 0), proj 3 _ (l35ESL 0 2), 5, by norm_num,
    by norm_num, fun e he1 he6 => by interval_cases e <;> norm_num, ?_, ?_⟩))
  · intro e₁ e₂ h₁ h₁' h₂ h₂'
    interval_cases e₁ <;> interval_cases e₂ <;> decide
  have hT : (proj 3 (GaloisField 5 1) l35TSL)⁻¹ = proj 3 _ l35TSL := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right l35TSL_mul_self]
  have hE1 : (l35ESL 2 0)⁻¹ = l35ESL (-2) 0 :=
    inv_eq_of_mul_eq_one_right (by rw [l35ESL_mul, add_neg_cancel, add_zero, l35ESL_zero])
  have hE2 : (l35ESL 0 2)⁻¹ = l35ESL 0 (-2) :=
    inv_eq_of_mul_eq_one_right (by rw [l35ESL_mul, add_neg_cancel, add_zero, l35ESL_zero])
  have hw₁ : MulAut.conj (proj 3 (GaloisField 5 1) l35TSL) (proj 3 _ (l35ESL 2 0)) *
      (proj 3 _ (l35ESL 2 0))⁻¹ = l35EHom (Multiplicative.ofAdd (1, 0)) := by
    rw [MulAut.conj_apply, hT, ← map_inv, hE1, ← map_mul, ← map_mul, ← map_mul, l35EHom_apply]
    congr 1
    exact Subtype.ext (l35T_conj_l35X₁ h5)
  have hw₂ : MulAut.conj (proj 3 (GaloisField 5 1) l35TSL) (proj 3 _ (l35ESL 0 2)) *
      (proj 3 _ (l35ESL 0 2))⁻¹ = l35EHom (Multiplicative.ofAdd (0, 1)) := by
    rw [MulAut.conj_apply, hT, ← map_inv, hE2, ← map_mul, ← map_mul, ← map_mul, l35EHom_apply]
    congr 1
    exact Subtype.ext (l35T_conj_l35X₂ h5)
  rw [hw₁, hw₂]
  have hle : l35EHom.range ≤ Subgroup.closure
      ({l35EHom (Multiplicative.ofAdd (1, 0)), l35EHom (Multiplicative.ofAdd (0, 1))} :
        Set (projectiveSL 3 (GaloisField 5 1))) := by
    rintro _ ⟨ab, rfl⟩
    obtain ⟨n, hn⟩ := exists_natCast_galoisField_five_one (Multiplicative.toAdd ab).1
    obtain ⟨m, hm⟩ := exists_natCast_galoisField_five_one (Multiplicative.toAdd ab).2
    have hab : ab = Multiplicative.ofAdd ((1 : GaloisField 5 1), (0 : GaloisField 5 1)) ^ n *
        Multiplicative.ofAdd ((0 : GaloisField 5 1), (1 : GaloisField 5 1)) ^ m := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_pow, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd]
      ext
      · simp [hn]
      · simp [hm]
    rw [hab, map_mul, map_pow, map_pow]
    exact mul_mem (pow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) n)
      (pow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) m)
  have hcard : Nat.card l35EHom.range = 5 ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective l35EHom_injective).toEquiv]
    change Nat.card (GaloisField 5 1 × GaloisField 5 1) = 5 ^ 2
    rw [Nat.card_prod, card_galoisField_five_one]
    norm_num
  exact hcard ▸ Subgroup.card_dvd_of_le hle

theorem excl1411_L3_5 (β : MulAut (projectiveSL 3 (GaloisField 5 1))) (hβ : orderOf β = 2) :
    Excl1411 β := by
  have hF := card_galoisField_five_one
  have h2 : (2 : GaloisField 5 1) ≠ 0 := fun h0 => one_ne_zero (α := GaloisField 5 1)
    (by linear_combination five_eq_zero_galoisField_five_one - 2 * h0)
  have hodd : Odd (Nat.card (GaloisField 5 1)) := by rw [hF]; decide
  have hβ2 : β * β = 1 := by rw [← sq, ← hβ, pow_orderOf_eq_one]
  rcases CFSG.QuasithinUnique.Ch1.classify_involution hF h2 β hβ2 with ⟨g, hg⟩ | ⟨A, -, hβA⟩
  ·
    have hβs : β = MulAut.conj g⁻¹ := by
      ext x
      rw [hg x, MulAut.conj_apply, inv_inv]
    have hZ := CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (k := GaloisField 5 1)
      (n := 3) le_rfl
    have hs : orderOf g⁻¹ = 2 := by
      refine orderOf_eq_prime ?_ fun h1 => ?_
      · have hc : MulAut.conj (g⁻¹ ^ 2) = 1 := by rw [map_pow, ← hβs, ← hβ, pow_orderOf_eq_one]
        have hmem : g⁻¹ ^ 2 ∈ Subgroup.center (projectiveSL 3 (GaloisField 5 1)) := by
          rw [Subgroup.mem_center_iff]
          intro y
          have e := congrArg (fun φ : MulAut (projectiveSL 3 (GaloisField 5 1)) => φ y) hc
          simp only [MulAut.conj_apply, MulAut.one_apply] at e
          calc y * g⁻¹ ^ 2 = g⁻¹ ^ 2 * y * (g⁻¹ ^ 2)⁻¹ * g⁻¹ ^ 2 := by rw [e]
            _ = g⁻¹ ^ 2 * y := by group
        rw [hZ, Subgroup.mem_bot] at hmem
        exact hmem
      · rw [h1, map_one] at hβs
        rw [hβs, orderOf_one] at hβ
        exact absurd hβ (by norm_num)
    have ht : orderOf (proj 3 (GaloisField 5 1) l35TSL) = 2 := by
      rw [orderOf_injective _ proj_injective_five]
      exact orderOf_eq_prime (by rw [sq]; exact l35TSL_mul_self) l35TSL_ne_one
    obtain ⟨k, hk⟩ := CFSG.ClassicalInvolution.Q3.TL4.E3S3Gen.exists_conj_psl3 hodd hs ht
    have hβk : β = MulAut.conj k⁻¹ * MulAut.conj (proj 3 (GaloisField 5 1) l35TSL) *
        (MulAut.conj k⁻¹)⁻¹ := by
      rw [hβs, ← hk]
      simp only [map_mul, map_inv]
      group
    rw [hβk]
    exact excl1411_conj_l35T.conj _
  ·
    have h1 : fieldAut 3 (GaloisField 5 1) 1 = 1 := map_one _
    obtain ⟨k, -, hk⟩ := CFSG.RankThree.PartTwo.Sec21.Item211Res6Proof.exists_graph_conj
      (K := GaloisField 5 1) (p := 5) (by norm_num) (A := A) (σ := 1) (ρ := 1)
      (by rw [h1, mul_one, mul_one, one_mul]) (m := 0)
      (by rw [h1, mul_one, zpow_zero, ← hβA, sq, hβ2])
    rw [h1, mul_one, one_mul, ← hβA] at hk
    rw [hk]
    exact excl1411_dualAut_L3_5.conj _

end CFSG.RankThree.PartTwo.Sec20
