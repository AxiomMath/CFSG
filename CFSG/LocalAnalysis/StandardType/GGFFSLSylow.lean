module

public import CFSG.LocalAnalysis.StandardType.GGFFModelDefs
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFWreath
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFLin
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
import CFSG.RankThree.PartTwo.Sec8.Statements

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF

open Matrix
open scoped MatrixGroups
open CFSG.RankThree.PartTwo.Sec4.RonanK429F
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt baseA wreathW)
open CFSG.RankThree.PartTwo.Sec4.RonanK429F (W6.T W6.tw W7.T W7.tw)

private theorem conj_toMonoidHom_apply {G : Type*} [Group G] (g y : G) :
    (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ :=
  MulAut.conj_apply g y

private def bOf (a : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 := ![0, a 1, -a 0]

private def bOf2 (a : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 := ![0, -a 0, a 2]

private theorem key1_SL6 : ∀ a : Fin 3 → ZMod 3,
    (vecElt W6.T a * W6.tw) ^ 3 = 1 →
    vecElt W6.T a * W6.tw * vecElt W6.T (bOf a) = vecElt W6.T (bOf a) * W6.tw := by
  decide +kernel

private theorem key2_SL6 : ∀ a : Fin 3 → ZMod 3,
    (vecElt W6.T a * W6.tw ^ 2) ^ 3 = 1 →
    vecElt W6.T a * W6.tw ^ 2 * vecElt W6.T (bOf2 a) = vecElt W6.T (bOf2 a) * W6.tw ^ 2 := by
  decide +kernel

private def c6M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 1, 0, 1;
    1, 0, 1, 0, 1, 0;
    0, 1, 1, 0, 1, 1;
    1, 0, 1, 1, 0, 1;
    1, 1, 1, 0, 0, 1;
    1, 0, 0, 1, 1, 1]

private def c6Mi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 1, 0, 1;
    1, 0, 1, 0, 1, 1;
    0, 1, 1, 0, 1, 0;
    1, 0, 1, 1, 0, 1;
    0, 1, 1, 1, 1, 1;
    1, 0, 0, 1, 1, 0]

private def c6 : SL(6, ZMod 2) := W6.mkSL6 c6M c6Mi (by decide +kernel)

private theorem c6_spec : c6 * W6.tw = (W6.T 1 * W6.T 2) * c6 := by decide +kernel

private theorem base12_SL6 : W6.T 1 * W6.T 2 = vecElt W6.T ![0, 1, 1] := by decide +kernel

private theorem base12_sq_SL6 : (W6.T 1 * W6.T 2) ^ 2 = vecElt W6.T ![0, 2, 2] := by
  decide +kernel

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound) in
private theorem card_outer_SL_zmod_two_dvd_two {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer SL(n, ZMod 2)) ∣ 2 := by
  have hd := higher_linear_outer_order_divides_field_gcd_bound
    (k := GaloisField 2 1) Nat.prime_two le_rfl hn (GaloisField.card 2 1 one_ne_zero)
  rw [show 2 * 1 * Nat.gcd n (2 ^ 1 - 1) = 2 by norm_num] at hd
  rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (projSLEquivSLZMod (show 1 ≤ n by omega))).toEquiv,
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL n (GaloisField 2 1))).toEquiv]
  exact hd

theorem inner_odd_SL {n : ℕ} (hn : 3 ≤ n) : ∀ α : MulAut SL(n, ZMod 2), ∀ m : ℕ, Odd m →
    α ^ m = 1 → ∃ h, α = MulAut.conj h := by
  intro α m hm hα
  have hout := card_outer_SL_zmod_two_dvd_two hn
  have : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer SL(n, ZMod 2)) :=
    Nat.finite_of_card_ne_zero fun h0 => by rw [h0] at hout; exact absurd hout (by norm_num)
  set t : CFSG.ComponentClassification.OuterAutomorphisms.Outer SL(n, ZMod 2) :=
    (α : CFSG.ComponentClassification.OuterAutomorphisms.Outer SL(n, ZMod 2)) with ht
  have htm : t ^ m = 1 := by rw [ht, ← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have hcop : Nat.Coprime m
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer SL(n, ZMod 2))) :=
    Nat.Coprime.coprime_dvd_right hout (Nat.coprime_two_right.mpr hm)
  have hord : orderOf t ∣ Nat.gcd m
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer SL(n, ZMod 2))) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one htm) (orderOf_dvd_natCard t)
  rw [hcop] at hord
  have h : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner SL(n, ZMod 2) :=
    (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord))
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner] at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk.symm⟩

private theorem wreath_SL6_not_commuting : W6.tw * W6.T 0 ≠ W6.T 0 * W6.tw := by
  decide +kernel

private theorem wreath_SL7_not_commuting : W7.tw * W7.T 0 ≠ W7.T 0 * W7.tw := by
  decide +kernel

theorem rank_SL6 : ∀ E : Subgroup SL(6, ZMod 2), CFSG.Assembly.IsElemAbelian 3 E →
    Nat.card E ≤ 27 := by
  intro E hE
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW W6.T W6.tw)
    (by rw [W6.card_wreathW, W6.factorization_card_SL6]; norm_num)
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hE)
  have hle : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ wreathW W6.T W6.tw :=
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_inv_le hg
  have hdvd : Nat.card E ∣ 3 ^ 4 := by
    have h := Subgroup.card_dvd_of_le hle
    rw [W6.card_wreathW, show (81 : ℕ) = 3 ^ 4 by norm_num,
      Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective] at h
    exact h
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rcases Nat.lt_or_ge k 4 with hklt | hkge
  · calc Nat.card E = 3 ^ k := hk
      _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 27 := by norm_num
  · exfalso
    have hk4' : k = 4 := by omega
    have hcardE : Nat.card E = 81 := by rw [hk, hk4']; norm_num
    have hcardE' : Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom) = 81 := by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective, hcardE]
    have heq : E.map (MulAut.conj g⁻¹).toMonoidHom = wreathW W6.T W6.tw := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [hcardE', W6.card_wreathW]
    have hcomm := (CFSG.Open.IsElemAbelian.map hE
      (MulAut.conj g⁻¹).toMonoidHom).1.is_comm.comm
    have htw : W6.tw ∈ E.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have ht0 : W6.T 0 ∈ E.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [heq]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
    have hctw : W6.tw * W6.T 0 = W6.T 0 * W6.tw :=
      congrArg Subtype.val (hcomm ⟨_, htw⟩ ⟨_, ht0⟩)
    exact wreath_SL6_not_commuting hctw

theorem torus_SL6 : ∀ E : Subgroup SL(6, ZMod 2), CFSG.Assembly.IsElemAbelian 3 E →
    Nat.card E = 27 → ∃ g : SL(6, ZMod 2), ∀ x : SL(6, ZMod 2),
      x ∈ E ↔ ∃ v, x = g * vecElt W6.T v * g⁻¹ := by
  intro E hE h27
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW W6.T W6.tw)
    (by rw [W6.card_wreathW, W6.factorization_card_SL6]; norm_num)
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hE)
  have hle : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ wreathW W6.T W6.tw :=
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_inv_le hg
  have hcard : Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective, h27]
  have hEq : E.map (MulAut.conj g⁻¹).toMonoidHom = baseA W6.T :=
    CFSG.RankThree.PartTwo.Sec4.Item434Kit.eq_baseA_of_le_wreathW W6.wreathFacts
      W6.card_wreathW hle (CFSG.Open.IsElemAbelian.map hE _) hcard
  refine ⟨g, fun x => ?_⟩
  constructor
  · intro hx
    have hx' : (MulAut.conj g⁻¹).toMonoidHom x ∈ baseA W6.T := by
      rw [← hEq]
      exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨v, hv⟩ :=
      (CFSG.RankThree.PartTwo.Sec4.Item434Kit.mem_baseA_iff W6.wreathFacts).mp hx'
    refine ⟨v, ?_⟩
    rw [hv, conj_toMonoidHom_apply]
    group
  · rintro ⟨v, rfl⟩
    have hb : (MulAut.conj g⁻¹).toMonoidHom (g * vecElt W6.T v * g⁻¹) ∈ baseA W6.T := by
      have h1 : (MulAut.conj g⁻¹).toMonoidHom (g * vecElt W6.T v * g⁻¹) = vecElt W6.T v := by
        rw [conj_toMonoidHom_apply]
        group
      rw [h1]
      exact CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_mem_baseA W6.wreathFacts v
    have hmem : (MulAut.conj g⁻¹).toMonoidHom (g * vecElt W6.T v * g⁻¹) ∈
        E.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [hEq]
      exact hb
    obtain ⟨y, hy, hfy⟩ := hmem
    have hyx : y = g * vecElt W6.T v * g⁻¹ := (MulAut.conj g⁻¹).injective hfy
    rwa [hyx] at hy

theorem fus_SL6 : ∀ x : SL(6, ZMod 2), x ^ 3 = 1 →
    ∃ g : SL(6, ZMod 2), ∃ v, x = g * vecElt W6.T v * g⁻¹ := by
  intro x hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW W6.T W6.tw)
    (by rw [W6.card_wreathW, W6.factorization_card_SL6]; norm_num)
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian
      (CFSG.Open.isElemAbelian_zpowers hx))
  have hx' : x ∈ (wreathW W6.T W6.tw).map (MulAut.conj g).toMonoidHom :=
    hg (Subgroup.mem_zpowers x)
  obtain ⟨w, hw, hwx⟩ := hx'
  have hwx' : x = g * w * g⁻¹ := by
    rw [← hwx, conj_toMonoidHom_apply]
  have hw3 : w ^ 3 = 1 := by
    have h1 : w = g⁻¹ * x * g := by
      rw [← hwx, conj_toMonoidHom_apply]
      group
    calc w ^ 3 = (g⁻¹ * x * g) ^ 3 := by rw [h1]
      _ = (g⁻¹ * x * (g⁻¹)⁻¹) ^ 3 := by rw [inv_inv]
      _ = g⁻¹ * x ^ 3 * (g⁻¹)⁻¹ := by rw [conj_pow]
      _ = g⁻¹ * x ^ 3 * g := by rw [inv_inv]
      _ = 1 := by rw [hx]; group
  obtain ⟨a, j, ha⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item434Kit.mem_wreathW W6.wreathFacts hw
  have htw : W6.tw = c6⁻¹ * (W6.T 1 * W6.T 2) * c6 := by
    calc W6.tw = c6⁻¹ * (c6 * W6.tw) := by group
      _ = c6⁻¹ * ((W6.T 1 * W6.T 2) * c6) := by rw [c6_spec]
      _ = c6⁻¹ * (W6.T 1 * W6.T 2) * c6 := by group
  have hj : (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 := by
    have := j.isLt
    omega
  rcases hj with hj | hj | hj
  · rw [hj] at ha
    rw [pow_zero, mul_one] at ha
    exact ⟨g, a, by rw [hwx', ha]⟩
  · rw [hj] at ha
    rw [pow_one] at ha
    have hkey : (vecElt W6.T a * W6.tw) ^ 3 = 1 := by rw [← ha]; exact hw3
    have hb := key1_SL6 a hkey
    have hb' : vecElt W6.T a * W6.tw =
        vecElt W6.T (bOf a) * W6.tw * (vecElt W6.T (bOf a))⁻¹ := by
      rw [← hb, mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨g * vecElt W6.T (bOf a) * c6⁻¹, ![0, 1, 1], ?_⟩
    rw [hwx', ha, hb', htw, base12_SL6]
    group
  · rw [hj] at ha
    have hkey : (vecElt W6.T a * W6.tw ^ 2) ^ 3 = 1 := by rw [← ha]; exact hw3
    have hb := key2_SL6 a hkey
    have hb' : vecElt W6.T a * W6.tw ^ 2 =
        vecElt W6.T (bOf2 a) * W6.tw ^ 2 * (vecElt W6.T (bOf2 a))⁻¹ := by
      rw [← hb, mul_assoc, mul_inv_cancel, mul_one]
    have htw2 : W6.tw ^ 2 = c6⁻¹ * (W6.T 1 * W6.T 2) ^ 2 * c6 := by
      calc W6.tw ^ 2 = (c6⁻¹ * (W6.T 1 * W6.T 2) * c6) ^ 2 := by rw [htw]
        _ = (c6⁻¹ * (W6.T 1 * W6.T 2) * (c6⁻¹)⁻¹) ^ 2 := by rw [inv_inv]
        _ = c6⁻¹ * (W6.T 1 * W6.T 2) ^ 2 * (c6⁻¹)⁻¹ := by rw [conj_pow]
        _ = c6⁻¹ * (W6.T 1 * W6.T 2) ^ 2 * c6 := by rw [inv_inv]
    refine ⟨g * vecElt W6.T (bOf2 a) * c6⁻¹, ![0, 2, 2], ?_⟩
    rw [hwx', ha, hb', htw2, base12_sq_SL6]
    group

private theorem key1_SL7 : ∀ a : Fin 3 → ZMod 3,
    (vecElt W7.T a * W7.tw) ^ 3 = 1 →
    vecElt W7.T a * W7.tw * vecElt W7.T (bOf a) = vecElt W7.T (bOf a) * W7.tw := by
  decide +kernel

private theorem key2_SL7 : ∀ a : Fin 3 → ZMod 3,
    (vecElt W7.T a * W7.tw ^ 2) ^ 3 = 1 →
    vecElt W7.T a * W7.tw ^ 2 * vecElt W7.T (bOf2 a) = vecElt W7.T (bOf2 a) * W7.tw ^ 2 := by
  decide +kernel

private def c7M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 1, 1, 1, 1, 1, 0;
    1, 0, 1, 0, 1, 0, 0;
    0, 0, 1, 0, 1, 0, 0;
    1, 0, 1, 0, 0, 0, 0;
    1, 1, 0, 0, 1, 1, 0;
    0, 0, 1, 1, 1, 1, 0;
    0, 1, 0, 1, 0, 1, 1]

private def c7Mi : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![0, 1, 1, 0, 0, 0, 0;
    1, 1, 1, 0, 0, 1, 0;
    0, 1, 1, 1, 0, 0, 0;
    1, 1, 1, 1, 1, 0, 0;
    0, 1, 0, 1, 0, 0, 0;
    1, 1, 0, 1, 1, 1, 0;
    1, 1, 0, 0, 0, 0, 1]

private def c7 : SL(7, ZMod 2) := W7.mkSL7 c7M c7Mi (by decide +kernel)

private theorem c7_spec : c7 * W7.tw = (W7.T 1 * W7.T 2) * c7 := by decide +kernel

private theorem base12_SL7 : W7.T 1 * W7.T 2 = vecElt W7.T ![0, 1, 1] := by decide +kernel

private theorem base12_sq_SL7 : (W7.T 1 * W7.T 2) ^ 2 = vecElt W7.T ![0, 2, 2] := by
  decide +kernel

theorem rank_SL7 : ∀ E : Subgroup SL(7, ZMod 2), CFSG.Assembly.IsElemAbelian 3 E →
    Nat.card E ≤ 27 := by
  intro E hE
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW W7.T W7.tw)
    (by rw [W7.card_wreathW, W7.factorization_card_SL7]; norm_num)
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hE)
  have hle : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ wreathW W7.T W7.tw :=
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_inv_le hg
  have hdvd : Nat.card E ∣ 3 ^ 4 := by
    have h := Subgroup.card_dvd_of_le hle
    rw [W7.card_wreathW, show (81 : ℕ) = 3 ^ 4 by norm_num,
      Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective] at h
    exact h
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rcases Nat.lt_or_ge k 4 with hklt | hkge
  · calc Nat.card E = 3 ^ k := hk
      _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 27 := by norm_num
  · exfalso
    have hk4' : k = 4 := by omega
    have hcardE : Nat.card E = 81 := by rw [hk, hk4']; norm_num
    have hcardE' : Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom) = 81 := by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective, hcardE]
    have heq : E.map (MulAut.conj g⁻¹).toMonoidHom = wreathW W7.T W7.tw := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [hcardE', W7.card_wreathW]
    have hcomm := (CFSG.Open.IsElemAbelian.map hE
      (MulAut.conj g⁻¹).toMonoidHom).1.is_comm.comm
    have htw : W7.tw ∈ E.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have ht0 : W7.T 0 ∈ E.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [heq]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
    have hctw : W7.tw * W7.T 0 = W7.T 0 * W7.tw :=
      congrArg Subtype.val (hcomm ⟨_, htw⟩ ⟨_, ht0⟩)
    exact wreath_SL7_not_commuting hctw

theorem torus_SL7 : ∀ E : Subgroup SL(7, ZMod 2), CFSG.Assembly.IsElemAbelian 3 E →
    Nat.card E = 27 → ∃ g : SL(7, ZMod 2), ∀ x : SL(7, ZMod 2),
      x ∈ E ↔ ∃ v, x = g * vecElt W7.T v * g⁻¹ := by
  intro E hE h27
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW W7.T W7.tw)
    (by rw [W7.card_wreathW, W7.factorization_card_SL7]; norm_num)
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hE)
  have hle : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ wreathW W7.T W7.tw :=
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_inv_le hg
  have hcard : Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective, h27]
  have hEq : E.map (MulAut.conj g⁻¹).toMonoidHom = baseA W7.T :=
    CFSG.RankThree.PartTwo.Sec4.Item434Kit.eq_baseA_of_le_wreathW W7.wreathFacts
      W7.card_wreathW hle (CFSG.Open.IsElemAbelian.map hE _) hcard
  refine ⟨g, fun x => ?_⟩
  constructor
  · intro hx
    have hx' : (MulAut.conj g⁻¹).toMonoidHom x ∈ baseA W7.T := by
      rw [← hEq]
      exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨v, hv⟩ :=
      (CFSG.RankThree.PartTwo.Sec4.Item434Kit.mem_baseA_iff W7.wreathFacts).mp hx'
    refine ⟨v, ?_⟩
    rw [hv, conj_toMonoidHom_apply]
    group
  · rintro ⟨v, rfl⟩
    have hb : (MulAut.conj g⁻¹).toMonoidHom (g * vecElt W7.T v * g⁻¹) ∈ baseA W7.T := by
      have h1 : (MulAut.conj g⁻¹).toMonoidHom (g * vecElt W7.T v * g⁻¹) = vecElt W7.T v := by
        rw [conj_toMonoidHom_apply]
        group
      rw [h1]
      exact CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_mem_baseA W7.wreathFacts v
    have hmem : (MulAut.conj g⁻¹).toMonoidHom (g * vecElt W7.T v * g⁻¹) ∈
        E.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [hEq]
      exact hb
    obtain ⟨y, hy, hfy⟩ := hmem
    have hyx : y = g * vecElt W7.T v * g⁻¹ := (MulAut.conj g⁻¹).injective hfy
    rwa [hyx] at hy

theorem fus_SL7 : ∀ x : SL(7, ZMod 2), x ^ 3 = 1 →
    ∃ g : SL(7, ZMod 2), ∃ v, x = g * vecElt W7.T v * g⁻¹ := by
  intro x hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW W7.T W7.tw)
    (by rw [W7.card_wreathW, W7.factorization_card_SL7]; norm_num)
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian
      (CFSG.Open.isElemAbelian_zpowers hx))
  have hx' : x ∈ (wreathW W7.T W7.tw).map (MulAut.conj g).toMonoidHom :=
    hg (Subgroup.mem_zpowers x)
  obtain ⟨w, hw, hwx⟩ := hx'
  have hwx' : x = g * w * g⁻¹ := by
    rw [← hwx, conj_toMonoidHom_apply]
  have hw3 : w ^ 3 = 1 := by
    have h1 : w = g⁻¹ * x * g := by
      rw [← hwx, conj_toMonoidHom_apply]
      group
    calc w ^ 3 = (g⁻¹ * x * g) ^ 3 := by rw [h1]
      _ = (g⁻¹ * x * (g⁻¹)⁻¹) ^ 3 := by rw [inv_inv]
      _ = g⁻¹ * x ^ 3 * (g⁻¹)⁻¹ := by rw [conj_pow]
      _ = g⁻¹ * x ^ 3 * g := by rw [inv_inv]
      _ = 1 := by rw [hx]; group
  obtain ⟨a, j, ha⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item434Kit.mem_wreathW W7.wreathFacts hw
  have htw : W7.tw = c7⁻¹ * (W7.T 1 * W7.T 2) * c7 := by
    calc W7.tw = c7⁻¹ * (c7 * W7.tw) := by group
      _ = c7⁻¹ * ((W7.T 1 * W7.T 2) * c7) := by rw [c7_spec]
      _ = c7⁻¹ * (W7.T 1 * W7.T 2) * c7 := by group
  have hj : (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 := by
    have := j.isLt
    omega
  rcases hj with hj | hj | hj
  · rw [hj] at ha
    rw [pow_zero, mul_one] at ha
    exact ⟨g, a, by rw [hwx', ha]⟩
  · rw [hj] at ha
    rw [pow_one] at ha
    have hkey : (vecElt W7.T a * W7.tw) ^ 3 = 1 := by rw [← ha]; exact hw3
    have hb := key1_SL7 a hkey
    have hb' : vecElt W7.T a * W7.tw =
        vecElt W7.T (bOf a) * W7.tw * (vecElt W7.T (bOf a))⁻¹ := by
      rw [← hb, mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨g * vecElt W7.T (bOf a) * c7⁻¹, ![0, 1, 1], ?_⟩
    rw [hwx', ha, hb', htw, base12_SL7]
    group
  · rw [hj] at ha
    have hkey : (vecElt W7.T a * W7.tw ^ 2) ^ 3 = 1 := by rw [← ha]; exact hw3
    have hb := key2_SL7 a hkey
    have hb' : vecElt W7.T a * W7.tw ^ 2 =
        vecElt W7.T (bOf2 a) * W7.tw ^ 2 * (vecElt W7.T (bOf2 a))⁻¹ := by
      rw [← hb, mul_assoc, mul_inv_cancel, mul_one]
    have htw2 : W7.tw ^ 2 = c7⁻¹ * (W7.T 1 * W7.T 2) ^ 2 * c7 := by
      calc W7.tw ^ 2 = (c7⁻¹ * (W7.T 1 * W7.T 2) * c7) ^ 2 := by rw [htw]
        _ = (c7⁻¹ * (W7.T 1 * W7.T 2) * (c7⁻¹)⁻¹) ^ 2 := by rw [inv_inv]
        _ = c7⁻¹ * (W7.T 1 * W7.T 2) ^ 2 * (c7⁻¹)⁻¹ := by rw [conj_pow]
        _ = c7⁻¹ * (W7.T 1 * W7.T 2) ^ 2 * c7 := by rw [inv_inv]
    refine ⟨g * vecElt W7.T (bOf2 a) * c7⁻¹, ![0, 2, 2], ?_⟩
    rw [hwx', ha, hb', htw2, base12_sq_SL7]
    group

end CFSG.StandardType.GGFF

end
