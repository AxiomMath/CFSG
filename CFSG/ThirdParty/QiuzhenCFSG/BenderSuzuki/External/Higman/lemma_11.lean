module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_5
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_6
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_9
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_10
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.CentralExtensionCoordinates
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Higman Lemma 11
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII
open scoped IsMulCommutative commutatorElement

universe u

private theorem lemma11_two_pow_gap_add_one_dvd_sum (i j : ℕ) :
    2 ^ ((i - j) + (j - i)) + 1 ∣ 2 ^ i + 2 ^ j := by
  rcases le_total i j with hij | hji
  · refine ⟨2 ^ i, ?_⟩
    calc
      2 ^ i + 2 ^ j = 2 ^ i + 2 ^ (i + (j - i)) := by
        rw [Nat.add_sub_of_le hij]
      _ = (2 ^ ((i - j) + (j - i)) + 1) * 2 ^ i := by
        rw [Nat.sub_eq_zero_of_le hij, zero_add, pow_add]
        ring
  · refine ⟨2 ^ j, ?_⟩
    calc
      2 ^ i + 2 ^ j = 2 ^ (j + (i - j)) + 2 ^ j := by
        rw [Nat.add_sub_of_le hji]
      _ = (2 ^ ((i - j) + (j - i)) + 1) * 2 ^ j := by
        rw [Nat.sub_eq_zero_of_le hji, add_zero, pow_add]
        ring

private theorem lemma11_odd_div_gcd_of_coprime_two_pow_add
    {n r : ℕ} (hn : 0 < n)
    (hcop : Nat.Coprime (2 ^ n - 1) (2 ^ r + 1)) :
    Odd (n / n.gcd r) := by
  let d := n.gcd r
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left r hn
  have hquot_coprime : (n / d).Coprime (r / d) := by
    simpa [d] using Nat.coprime_div_gcd_div_gcd hd_pos
  apply Nat.not_even_iff_odd.mp
  intro hn_even
  have htwo_dvd : 2 ∣ n / d := by
    rcases (show Even (n / d) by simpa [d] using hn_even) with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hr_odd : Odd (r / d) := by
    apply Nat.Coprime.odd_of_left
    exact Nat.Coprime.of_dvd htwo_dvd (dvd_refl _) hquot_coprime
  have hd_dvd_n : d ∣ n := by simpa [d] using Nat.gcd_dvd_left n r
  have hd_dvd_r : d ∣ r := by simpa [d] using Nat.gcd_dvd_right n r
  have hn_eq : d * (n / d) = n := Nat.mul_div_cancel' hd_dvd_n
  have hr_eq : d * (r / d) = r := Nat.mul_div_cancel' hd_dvd_r
  let c := 2 ^ d + 1
  have hc_base : c ∣ (2 ^ d) ^ 2 - 1 := by
    refine ⟨2 ^ d - 1, ?_⟩
    simpa [c, pow_two] using mul_self_tsub_one (2 ^ d)
  have hc_dvd_n : c ∣ 2 ^ n - 1 := by
    have h := hc_base.trans
      (Nat.pow_sub_one_dvd_pow_sub_one (2 ^ d) htwo_dvd)
    simpa [c, ← pow_mul, hn_eq] using h
  have hc_dvd_r : c ∣ 2 ^ r + 1 := by
    have h := hr_odd.nat_add_dvd_pow_add_pow (2 ^ d) 1
    simpa [c, ← pow_mul, hr_eq] using h
  have hc_one := Nat.eq_one_of_dvd_coprimes hcop hc_dvd_n hc_dvd_r
  have hc_gt : 1 < c := by simp [c]
  exact (ne_of_gt hc_gt) hc_one

private theorem lemma11_target_order_dvd_source_of_bilinear_span
    {V W : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (T : V ≃ₗ[ZMod 2] V) (S : W ≃ₗ[ZMod 2] W)
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (hB_equivariant : ∀ x y : V, B (T x) (T y) = S (B x y))
    (hB_span : Submodule.span (ZMod 2)
      (Set.range fun p : V × V => B p.1 p.2) = ⊤) :
    orderOf S ∣ orderOf T := by
  have hB_pow : ∀ k : ℕ, ∀ x y : V,
      B ((T ^ k) x) ((T ^ k) y) = (S ^ k) (B x y) := by
    intro k
    induction k with
    | zero =>
        intro x y
        simp
    | succ k ih =>
        intro x y
        simpa only [pow_succ, LinearEquiv.mul_apply] using
          (calc
            B ((T ^ k) (T x)) ((T ^ k) (T y)) =
                (S ^ k) (B (T x) (T y)) := ih (T x) (T y)
            _ = (S ^ k) (S (B x y)) :=
              congrArg (fun z => (S ^ k) z) (hB_equivariant x y))
  apply (orderOf_dvd_iff_pow_eq_one).2
  apply LinearEquiv.ext
  intro y
  have hfix : ∀ z : W,
      z ∈ Submodule.span (ZMod 2)
          (Set.range fun p : V × V => B p.1 p.2) →
        (S ^ orderOf T) z = z := by
    intro z hz
    refine Submodule.span_induction
      (p := fun z _ => (S ^ orderOf T) z = z) ?_ ?_ ?_ ?_ hz
    · intro z hz
      rcases hz with ⟨⟨x, y⟩, rfl⟩
      rw [← hB_pow]
      simp
    · simp
    · intro x y _ _ hx hy
      simp only [map_add, hx, hy]
    · intro a x _ hx
      simp only [map_smul, hx]
  simpa [hB_span] using hfix y (by rw [hB_span]; trivial)

public theorem lemma11_singer_equivariant_function_eq_monomial
    {K : Type u} [Field K] [Finite K]
    (lambda : K) (hlambda : lambda ≠ 0)
    (hlambda_order : orderOf (Units.mk0 lambda hlambda) = Nat.card Kˣ)
    (q : K → K) (hq_zero : q 0 = 0) (e : ℕ) (he : 0 < e)
    (hq_equivariant : ∀ a : K, q (lambda * a) = lambda ^ e * q a) :
    ∀ a : K, q a = q 1 * a ^ e := by
  let lambdaUnit : Kˣ := Units.mk0 lambda hlambda
  have hlambda_zpowers : Subgroup.zpowers lambdaUnit = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hlambda_order]
  have hq_pow : ∀ t : ℕ, ∀ a : K,
      q ((lambdaUnit ^ t : Kˣ) * a) =
        ((lambdaUnit ^ t : Kˣ) : K) ^ e * q a := by
    intro t
    induction t with
    | zero =>
        intro a
        simp
    | succ t ih =>
        intro a
        calc
          q ((lambdaUnit ^ (t + 1) : Kˣ) * a) =
              q (lambda * (((lambdaUnit ^ t : Kˣ) : K) * a)) := by
                simp [lambdaUnit, pow_succ', mul_assoc]
          _ = lambda ^ e *
              q (((lambdaUnit ^ t : Kˣ) : K) * a) :=
                hq_equivariant _
          _ = lambda ^ e *
              (((lambdaUnit ^ t : Kˣ) : K) ^ e * q a) := by
                rw [ih]
          _ = ((lambdaUnit ^ (t + 1) : Kˣ) : K) ^ e * q a := by
                simp [lambdaUnit, pow_succ', mul_pow, mul_assoc]
  intro a
  by_cases ha : a = 0
  · simp [ha, hq_zero, he.ne']
  · let aUnit : Kˣ := Units.mk0 a ha
    have ha_mem : aUnit ∈ Subgroup.zpowers lambdaUnit := by
      rw [hlambda_zpowers]
      trivial
    obtain ⟨t, ht⟩ := mem_powers_iff_mem_zpowers.mpr ha_mem
    have htval : a = ((lambdaUnit ^ t : Kˣ) : K) := by
      exact (congrArg Units.val ht).symm
    calc
      q a = q (((lambdaUnit ^ t : Kˣ) : K) * 1) := by rw [htval, mul_one]
      _ = ((lambdaUnit ^ t : Kˣ) : K) ^ e * q 1 := hq_pow t 1
      _ = q 1 * a ^ e := by rw [htval]; exact mul_comm _ _

/-- The Type-A coordinates of Higman Lemma 11, aligned with the given regular
cyclic actor on the central quotient and the center. -/
@[expose] public def IsSuzukiTwoTypeAWithActor
    (X P : Type u) [Group X] [Group P] [MulDistribMulAction X P] : Prop :=
  ∃ (n : ℕ) (_ : n ≠ 0)
      (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
      (pairLift : BinaryGaloisField n → BinaryGaloisField n → P)
      (cocycle : BinaryGaloisField n → BinaryGaloisField n → BinaryGaloisField n)
      (eX : X ≃* (BinaryGaloisField n)ˣ)
      (eQ : (P ⧸ Subgroup.center P) ≃*
        Multiplicative (BinaryGaloisField n))
      (eZ : Subgroup.center P ≃*
        Multiplicative (BinaryGaloisField n)),
    (∃ r : ℕ, Odd r ∧ 0 < r ∧
      ∀ x : BinaryGaloisField n, theta^[r] x = x) ∧
    (∃ x : BinaryGaloisField n, theta x ≠ x) ∧
    (∀ a b c : BinaryGaloisField n,
      cocycle (a + b) c = cocycle a c + cocycle b c) ∧
    (∀ a b c : BinaryGaloisField n,
      cocycle a (b + c) = cocycle a b + cocycle a c) ∧
    (∀ a : BinaryGaloisField n, cocycle a a = a * theta a) ∧
    (∀ a z : BinaryGaloisField n, pairLift a z ∈ (⊤ : Subgroup P)) ∧
    pairLift 0 0 = 1 ∧
    (∀ x : P, ∃ a z : BinaryGaloisField n, x = pairLift a z) ∧
    (∀ a z b w : BinaryGaloisField n,
      pairLift a z = pairLift b w → a = b ∧ z = w) ∧
    (∀ a z b w : BinaryGaloisField n,
      pairLift a z * pairLift b w =
        pairLift (a + b) (z + w + cocycle a b)) ∧
    Nat.card (Subgroup.center P) = 2 ^ n ∧
    (∀ x : X, ∀ p : P,
      (eQ (QuotientGroup.mk' (Subgroup.center P) (x • p))).toAdd =
        (eX x : BinaryGaloisField n) *
          (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd) ∧
    (∀ x : X, ∀ z : BinaryGaloisField n,
      x • ((eZ.symm (Multiplicative.ofAdd z) : Subgroup.center P) : P) =
        ((eZ.symm (Multiplicative.ofAdd
          ((eX x : BinaryGaloisField n) *
            theta (eX x : BinaryGaloisField n) * z)) :
              Subgroup.center P) : P)) ∧
    (∀ a z : BinaryGaloisField n,
      (eQ (QuotientGroup.mk' (Subgroup.center P) (pairLift a z))).toAdd = a) ∧
    ∀ z : BinaryGaloisField n,
      pairLift 0 z =
        ((eZ.symm (Multiplicative.ofAdd z) : Subgroup.center P) : P)
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Higman Lemma 11: a Suzuki `2`-group of Omega-length two is type A. -/
public theorem lemma11_length_two_typeA_actor_coordinates
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (_hP : IsSuzukiTwoGroup P)
    (_hXcyclic : IsCyclic X) (_hXfaithful : FaithfulSMul X P)
    (_hXregular : ActionRegularOn X P (involutions P))
    (_hLen : OmegaLength X P 2) :
    IsSuzukiTwoTypeAWithActor X P := by
  classical
  have _hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x := by
    intro x hx y hy
    rcases _hXregular.2 x hx y hy with ⟨k, hk, _hunique⟩
    exact ⟨k, hk⟩
  let : Finite P := finite_of_isSuzukiTwoGroup _hP
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 P) := ⟨isPGroup_of_isSuzukiTwoGroup _hP⟩
  let : Group.IsNilpotent P :=
    IsPGroup.isNilpotent (isPGroup_of_isSuzukiTwoGroup _hP)
  rcases _hLen with ⟨subgroups, htop, hbot, _hle, hsteps⟩
  let A : Subgroup P := subgroups ⟨1, by decide⟩
  have hupper :
      A < ⊤ ∧ (⊤ : Subgroup P).Normal ∧ A.Normal ∧
        IsXInvariantSubgroup X (⊤ : Subgroup P) ∧ IsXInvariantSubgroup X A ∧
        ∀ L : Subgroup P, L.Normal → IsXInvariantSubgroup X L →
          A ≤ L → L ≤ ⊤ → L = A ∨ L = ⊤ := by
    have h := hsteps (0 : Fin 2)
    simpa [A, htop] using h
  have hlower :
      (⊥ : Subgroup P) < A ∧ A.Normal ∧ (⊥ : Subgroup P).Normal ∧
        IsXInvariantSubgroup X A ∧ IsXInvariantSubgroup X (⊥ : Subgroup P) ∧
        ∀ L : Subgroup P, L.Normal → IsXInvariantSubgroup X L →
          ⊥ ≤ L → L ≤ A → L = ⊥ ∨ L = A := by
    have hs2 : subgroups (2 : Fin 3) = (⊥ : Subgroup P) := by
      simpa using hbot
    have h := hsteps (1 : Fin 2)
    simpa [A, hs2] using h
  have hA_abelian : IsMulCommutative A := by
    let : A.Normal := hlower.2.1
    let D : Subgroup P := (commutator A).map A.subtype
    have hA_ne : A ≠ ⊥ := ne_of_gt hlower.1
    have hD_lt : D < A := by
      rw [show D = ⁅A, A⁆ by exact A.map_subtype_commutator]
      exact Group.IsSolvable.commutator_lt_of_ne_bot hA_ne
    have hD_normal : D.Normal := by
      dsimp [D]
      infer_instance
    have hD_X : IsXInvariantSubgroup X D := by
      let : IsInvariant X P A := ⟨hlower.2.2.2.1⟩
      have hforward : ∀ x : X, ∀ p : P, p ∈ D → x • p ∈ D := by
        intro x p hp
        rcases hp with ⟨a, ha, rfl⟩
        refine ⟨x • a, ?_, rfl⟩
        exact
          (Subgroup.characteristic_iff_le_comap.mp
            (show (commutator A).Characteristic from inferInstance)
            (MulDistribMulAction.toMulAut X A x)) ha
      intro x p
      constructor
      · exact hforward x p
      · intro hp
        have hpinv := hforward x⁻¹ (x • p) hp
        simpa [smul_smul] using hpinv
    have hD_bot : D = ⊥ := by
      rcases hlower.2.2.2.2.2 D hD_normal hD_X bot_le hD_lt.le with hbot | hA
      · exact hbot
      · exact False.elim (hD_lt.ne hA)
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
    apply Subtype.ext
    have hmem : ⁅(x : P), (y : P)⁆ ∈ D := by
      rw [show D = ⁅A, A⁆ by exact A.map_subtype_commutator]
      exact Subgroup.commutator_mem_commutator x.property y.property
    rw [hD_bot] at hmem
    have hcomm_one : ⁅(x : P), (y : P)⁆ = 1 := by
      simpa using hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hcomm_one
  have hA_maximal_abelian :
      ∀ B : Subgroup P, B.Normal → IsMulCommutative B →
        IsXInvariantSubgroup X B → A < B → False := by
    intro B hB_normal hB_abelian hB_X hAB
    rcases hupper.2.2.2.2.2 B hB_normal hB_X hAB.le le_top with hBA | hBtop
    · exact hAB.ne hBA.symm
    · apply _hP.2.1
      let : IsMulCommutative B := hB_abelian
      refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
      let bx : B := ⟨x, by rw [hBtop]; trivial⟩
      let by' : B := ⟨y, by rw [hBtop]; trivial⟩
      exact congrArg Subtype.val (mul_comm bx by')
  have hlemma9_data :
      (∀ x : A, x ^ 4 = 1) ∧
        (frattini (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype ≤ A :=
    lemma9_maximal_abelian_contains_frattini
      _hP _hXcyclic _hXfaithful _hXtrans
        hlower.2.1 hA_abelian hlower.2.2.2.1 hA_maximal_abelian
  have hcommutator_map_top :
      commutator P =
        (commutator (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype := by
    rw [_root_.commutator_def]
    exact (Subgroup.map_subtype_commutator (⊤ : Subgroup P)).symm
  have hcommutator_eq_A :
      (commutator (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype = A := by
    let D : Subgroup P :=
      (commutator (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype
    have hD_normal : D.Normal := by
      dsimp [D]
      infer_instance
    have hD_X : IsXInvariantSubgroup X D := by
      let : IsInvariant X P (⊤ : Subgroup P) := ⟨hupper.2.2.2.1⟩
      have hforward : ∀ x : X, ∀ p : P, p ∈ D → x • p ∈ D := by
        intro x p hp
        rcases hp with ⟨a, ha, rfl⟩
        refine ⟨x • a, ?_, rfl⟩
        exact
          (Subgroup.characteristic_iff_le_comap.mp
            (show (commutator (⊤ : Subgroup P)).Characteristic from inferInstance)
            (MulDistribMulAction.toMulAut X (⊤ : Subgroup P) x)) ha
      intro x p
      constructor
      · exact hforward x p
      · intro hp
        have hpinv := hforward x⁻¹ (x • p) hp
        simpa [smul_smul] using hpinv
    have hD_le_A : D ≤ A := by
      have : Fact (IsPGroup 2 (⊤ : Subgroup P)) :=
        ⟨(isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup ⊤⟩
      rintro _ ⟨d, hd, rfl⟩
      apply hlemma9_data.2
      exact ⟨d, commutator_le_frattini_of_isPGroup
        (R := (⊤ : Subgroup P)) (p := 2) hd, rfl⟩
    have hD_ne : D ≠ ⊥ := by
      intro hD_bot
      apply _hP.2.1
      have hcomm_bot : commutator P = ⊥ := by
        rw [← hD_bot]
        simpa only [D] using hcommutator_map_top
      have hcenter_top : Subgroup.center P = ⊤ :=
        (commutator_eq_bot_iff_center_eq_top P).mp hcomm_bot
      let : CommGroup P := Group.commGroupOfCenterEqTop hcenter_top
      exact IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => mul_comm x y
    rcases hlower.2.2.2.2.2 D hD_normal hD_X bot_le hD_le_A with hbot | hA
    · exact False.elim (hD_ne hbot)
    · exact hA
  have hA_exponent_two : ∀ x : A, x ^ 2 = 1 := by
    apply lemma8_cover_commutator_case_exponent_two
      _hP _hXcyclic _hXfaithful _hXtrans
        hlower.2.1 hA_abelian hlower.2.2.2.1
          hupper.2.1 hupper.2.2.2.1 hupper.1
    · intro B hB_normal hB_X hAB hBtop
      rcases hupper.2.2.2.2.2 B hB_normal hB_X hAB.le hBtop.le with hBA | htop
      · exact hAB.ne hBA.symm
      · exact hBtop.ne htop
    · exact hcommutator_eq_A
  have hfrattini_eq_A :
      (frattini (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype = A := by
    apply le_antisymm hlemma9_data.2
    have : Fact (IsPGroup 2 (⊤ : Subgroup P)) :=
      ⟨(isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup ⊤⟩
    intro a ha
    rw [← hcommutator_eq_A] at ha
    rcases ha with ⟨c, hc, rfl⟩
    exact ⟨c, commutator_le_frattini_of_isPGroup
      (R := (⊤ : Subgroup P)) (p := 2) hc, rfl⟩
  have hclass_two : higmanLowerCentralSeries P 2 = ⊥ := by
    have hL1 : higmanLowerCentralSeries P 1 = A := by
      calc
        higmanLowerCentralSeries P 1 = commutator P :=
          Subgroup.top_lowerCentralSeries_one
        _ =
            (commutator (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype := by
              exact hcommutator_map_top
        _ = A := hcommutator_eq_A
    have hL2_normal : (higmanLowerCentralSeries P 2).Normal := by infer_instance
    have hL2_X : IsXInvariantSubgroup X (higmanLowerCentralSeries P 2) :=
      (isInvariant_of_characteristic (A := X) (G := P)
        (higmanLowerCentralSeries P 2)).invariant
    have hL2_le_A : higmanLowerCentralSeries P 2 ≤ A := by
      calc
        higmanLowerCentralSeries P 2 ≤ higmanLowerCentralSeries P 1 :=
          (⊤ : Subgroup P).lowerCentralSeries_antitone (by omega)
        _ = A := hL1
    rcases hlower.2.2.2.2.2 (higmanLowerCentralSeries P 2) hL2_normal hL2_X
        bot_le hL2_le_A with hbot | hA
    · exact hbot
    · exfalso
      have hstable : ∀ n : ℕ, 1 ≤ n → higmanLowerCentralSeries P n = A := by
        intro n hn
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
        induction k with
        | zero => simpa using hL1
        | succ k ih =>
            change ⁅higmanLowerCentralSeries P (1 + k), (⊤ : Subgroup P)⁆ = A
            rw [ih (by omega)]
            calc
              ⁅A, (⊤ : Subgroup P)⁆ =
                  ⁅higmanLowerCentralSeries P 1, (⊤ : Subgroup P)⁆ := by rw [hL1]
              _ = higmanLowerCentralSeries P 2 := rfl
              _ = A := hA
      let c := Group.nilpotencyClass P
      have hc_pos : 0 < c := by
        apply Nat.pos_of_ne_zero
        intro hc
        have hsub : Subsingleton P :=
          (Group.nilpotencyClass_zero_iff_subsingleton (G := P)).mp hc
        rcases _hP.2.2.1 with ⟨x, y, _hx, _hy, hxy⟩
        exact hxy (hsub.elim x y)
      have hcA : higmanLowerCentralSeries P c = A := hstable c (by omega)
      have hcbot : higmanLowerCentralSeries P c = ⊥ := by
        dsimp [c]
        exact Subgroup.lowerCentralSeries_nilpotencyClass
      exact hlower.1.ne (hcA.symm.trans hcbot).symm
  have hA_eq_center : A = Subgroup.center P := by
    have hcommutatorP_eq_A : commutator P = A := by
      calc
        commutator P =
            (commutator (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype := by
              exact hcommutator_map_top
        _ = A := hcommutator_eq_A
    have hcommutator_le_center : commutator P ≤ Subgroup.center P := by
      have hclass := hclass_two
      change (⊤ : Subgroup P).lowerCentralSeries (1 + 1) = ⊥ at hclass
      rw [Subgroup.lowerCentralSeries_succ,
        Subgroup.top_lowerCentralSeries_one] at hclass
      change ⁅commutator P, (⊤ : Subgroup P)⁆ = ⊥ at hclass
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hclass
      simpa [← Subgroup.centralizer_univ, ← Subgroup.coe_top] using hclass
    have hA_le_center : A ≤ Subgroup.center P := by
      rw [← hcommutatorP_eq_A]
      exact hcommutator_le_center
    have hcenter_normal : (Subgroup.center P).Normal := by infer_instance
    have hcenter_X : IsXInvariantSubgroup X (Subgroup.center P) :=
      isXInvariantSubgroup_center X P
    rcases hupper.2.2.2.2.2 (Subgroup.center P) hcenter_normal hcenter_X
        hA_le_center le_top with hcenterA | hcenterTop
    · exact hcenterA.symm
    · exfalso
      apply _hP.2.1
      let : CommGroup P := Group.commGroupOfCenterEqTop hcenterTop
      exact IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => mul_comm x y
  have hinvolutions_center :
      involutions P = {z : P | z ∈ Subgroup.center P ∧ z ≠ 1} := by
    ext z
    constructor
    · intro hz
      have hzA : z ∈ A :=
        lemma1_involutions_mem_of_nontrivial_invariant
          _hP _hXtrans hlower.2.2.2.1 (ne_of_gt hlower.1) z hz
      exact ⟨hA_eq_center ▸ hzA, hz.ne_one⟩
    · rintro ⟨hzcenter, hz_ne⟩
      have hzA : z ∈ A := by
        rw [hA_eq_center]
        exact hzcenter
      refine ⟨hz_ne, ?_⟩
      let za : A := ⟨z, hzA⟩
      simpa [za] using congrArg A.subtype (hA_exponent_two za)
  have hfactor_action_data :
      ∃ (actor : X) (xi : MulAut P) (n : ℕ),
        (∀ x : X, x ∈ Subgroup.zpowers actor) ∧
        xi = MulDistribMulAction.toMulAut X P actor ∧
        orderOf actor = 2 ^ n - 1 ∧
        Odd (orderOf xi) ∧ 2 ≤ n ∧
        Nat.card (LowerCentralFactor P 1) = 2 ^ n ∧
        orderOf xi = 2 ^ n - 1 ∧
        lowerCentralFactorKernel P 1 = ⊥ ∧
        (lowerCentralFactorKernel P 0).map
          (higmanLowerCentralSeries P 0).subtype = A ∧
        (∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)),
          (∀ v : Additive (LowerCentralFactor P 0), v ∈ W →
            lowerCentralFactorLinearAut xi 0 v ∈ W) →
          W = ⊥ ∨ W = ⊤) ∧
        (∀ x : Additive (LowerCentralFactor P 1), x ≠ 0 →
          ∀ y : Additive (LowerCentralFactor P 1), y ≠ 0 →
            ∃ k : ℕ, (lowerCentralFactorLinearAut xi 1 ^ k) x = y) ∧
        squaresSubgroup P ≤ higmanLowerCentralSeries P 1 := by
    let : FaithfulSMul X P := _hXfaithful
    have htoMulAut_injective :
        Function.Injective (MulDistribMulAction.toMulAut X P) := by
      intro x y hxy
      apply FaithfulSMul.eq_of_smul_eq_smul (α := P)
      intro p
      exact congrArg (fun f : MulAut P => f p) hxy
    let : Finite X := Finite.of_injective
      (MulDistribMulAction.toMulAut X P) htoMulAut_injective
    let : IsCyclic X := _hXcyclic
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X)
    let tau : MulAut P := MulDistribMulAction.toMulAut X P g
    obtain ⟨k, m, hm_odd, htau_order⟩ :=
      Nat.exists_eq_two_pow_mul_odd (orderOf_pos tau).ne'
    let xi : MulAut P := tau ^ (2 ^ k)
    have hxi_odd : Odd (orderOf xi) := by
      have hk_dvd : 2 ^ k ∣ orderOf tau := by
        rw [htau_order]
        exact dvd_mul_right (2 ^ k) m
      have horder : orderOf (tau ^ (2 ^ k)) = m := by
        rw [orderOf_pow_of_dvd (by positivity : 2 ^ k ≠ 0) hk_dvd,
          htau_order]
        exact Nat.mul_div_cancel_left m (by positivity)
      change Odd (orderOf (tau ^ (2 ^ k)))
      rw [horder]
      exact hm_odd
    have hL1_eq_A : higmanLowerCentralSeries P 1 = A := by
      calc
        higmanLowerCentralSeries P 1 = commutator P :=
          Subgroup.top_lowerCentralSeries_one
        _ =
            (commutator (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype := by
              exact hcommutator_map_top
        _ = A := hcommutator_eq_A
    have hkernel1_bot : lowerCentralFactorKernel P 1 = ⊥ := by
      apply le_antisymm
      · rw [lowerCentralFactorKernel]
        apply sup_le
        · rw [squaresSubgroup, Subgroup.closure_le]
          rintro _ ⟨x, rfl⟩
          change x ^ 2 = 1
          apply Subtype.ext
          change (x : P) ^ 2 = 1
          let a : A := ⟨x, hL1_eq_A ▸ x.property⟩
          simpa [a] using congrArg Subtype.val (hA_exponent_two a)
        · intro x hx
          change (x : P) ∈ higmanLowerCentralSeries P 2 at hx
          rw [hclass_two] at hx
          exact Subgroup.mem_bot.mpr
            (Subtype.ext (Subgroup.mem_bot.mp hx))
      · exact bot_le
    have hsquares_le : squaresSubgroup P ≤ higmanLowerCentralSeries P 1 := by
      rw [squaresSubgroup, Subgroup.closure_le]
      rintro _ ⟨y, rfl⟩
      rw [hL1_eq_A]
      apply hlemma9_data.2
      let yt : (⊤ : Subgroup P) := ⟨y, trivial⟩
      refine ⟨yt ^ 2, ?_, rfl⟩
      let : Fact (IsPGroup 2 (⊤ : Subgroup P)) :=
        ⟨(isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup ⊤⟩
      rw [frattini_eq_closure_commutator_union_powers
        (R := (⊤ : Subgroup P)) (p := 2)]
      exact Subgroup.subset_closure (Or.inr ⟨yt, rfl⟩)
    have hkernel0_map_A :
        (lowerCentralFactorKernel P 0).map
          (higmanLowerCentralSeries P 0).subtype = A := by
      have hsquares_map :
          (squaresSubgroup (higmanLowerCentralSeries P 0)).map
              (higmanLowerCentralSeries P 0).subtype = squaresSubgroup P := by
        apply le_antisymm
        · rw [squaresSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
          rintro y ⟨z, hz, rfl⟩
          rcases hz with ⟨w, rfl⟩
          exact Subgroup.subset_closure ⟨(w : P), rfl⟩
        · rw [squaresSubgroup, Subgroup.closure_le]
          rintro _ ⟨p, rfl⟩
          let p0 : higmanLowerCentralSeries P 0 := ⟨p, by simp⟩
          refine ⟨p0 ^ 2, Subgroup.subset_closure ⟨p0, rfl⟩, rfl⟩
      have hnext_map :
          ((higmanLowerCentralSeries P 1).subgroupOf
              (higmanLowerCentralSeries P 0)).map
            (higmanLowerCentralSeries P 0).subtype = higmanLowerCentralSeries P 1 :=
        Subgroup.map_subgroupOf_eq_of_le
          ((⊤ : Subgroup P).lowerCentralSeries_antitone (by omega : 0 ≤ 1))
      rw [lowerCentralFactorKernel, Subgroup.map_sup, hsquares_map, hnext_map,
        hL1_eq_A]
      rw [hL1_eq_A] at hsquares_le
      exact sup_eq_right.mpr hsquares_le
    have hfactor1_card :
        ∃ n : ℕ, 2 ≤ n ∧ Nat.card (LowerCentralFactor P 1) = 2 ^ n := by
      let n := Module.finrank (ZMod 2) (Additive (LowerCentralFactor P 1))
      have hcard : Nat.card (LowerCentralFactor P 1) = 2 ^ n := by
        have h := Module.natCard_eq_pow_finrank
          (K := ZMod 2) (V := Additive (LowerCentralFactor P 1))
        calc
          Nat.card (LowerCentralFactor P 1) =
              Nat.card (Additive (LowerCentralFactor P 1)) :=
            (Nat.card_congr Additive.toMul).symm
          _ = 2 ^ n := by simpa [n] using h
      have hfactor_card_eq_A :
          Nat.card (LowerCentralFactor P 1) = Nat.card A := by
        change
          Nat.card ((higmanLowerCentralSeries P 1) ⧸ lowerCentralFactorKernel P 1) =
            Nat.card A
        rw [hkernel1_bot]
        calc
          Nat.card ((higmanLowerCentralSeries P 1) ⧸
                (⊥ : Subgroup (higmanLowerCentralSeries P 1))) =
              Nat.card (higmanLowerCentralSeries P 1) :=
            Nat.card_congr (QuotientGroup.quotientBot
              (G := higmanLowerCentralSeries P 1)).toEquiv
          _ = Nat.card A := by rw [hL1_eq_A]
      rcases _hP.2.2.1 with ⟨x, y, hx, hy, hxy⟩
      have hxcenter : x ∈ Subgroup.center P := by
        have hx' : x ∈ {z : P | z ∈ Subgroup.center P ∧ z ≠ 1} := by
          rw [← hinvolutions_center]
          exact hx
        exact hx'.1
      have hycenter : y ∈ Subgroup.center P := by
        have hy' : y ∈ {z : P | z ∈ Subgroup.center P ∧ z ≠ 1} := by
          rw [← hinvolutions_center]
          exact hy
        exact hy'.1
      let oneA : A := 1
      let xA : A := ⟨x, hA_eq_center ▸ hxcenter⟩
      let yA : A := ⟨y, hA_eq_center ▸ hycenter⟩
      have hxA : xA ≠ oneA := by
        intro h
        exact hx.1 (congrArg Subtype.val h)
      have hyA : yA ≠ oneA := by
        intro h
        exact hy.1 (congrArg Subtype.val h)
      have hxyA : xA ≠ yA := by
        intro h
        exact hxy (congrArg Subtype.val h)
      let : Fintype A := Fintype.ofFinite A
      have hthree : ({oneA, xA, yA} : Finset A).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxA.symm, hyA.symm])]
        rw [Finset.card_insert_of_notMem (by simp [hxyA])]
        simp
      have hle : 3 ≤ Nat.card (LowerCentralFactor P 1) := by
        rw [hfactor_card_eq_A, Nat.card_eq_fintype_card, ← hthree]
        exact Finset.card_le_card (Finset.subset_univ _)
      refine ⟨n, ?_, hcard⟩
      by_contra hn
      have hnle : n ≤ 1 := by omega
      rw [hcard] at hle
      interval_cases n <;> norm_num at hle
    have htau_irreducible :
        ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)),
          (∀ v : Additive (LowerCentralFactor P 0), v ∈ W →
            lowerCentralFactorLinearAut tau 0 v ∈ W) →
          W = ⊥ ∨ W = ⊤ := by
      intro W hW
      let Wsub : Subgroup (LowerCentralFactor P 0) :=
        AddSubgroup.toSubgroup' W.toAddSubgroup
      let qP : P →* LowerCentralFactor P 0 :=
        (QuotientGroup.mk' (lowerCentralFactorKernel P 0)).comp
          Subgroup.topEquiv.symm.toMonoidHom
      have hqker : qP.ker = A := by
        ext p
        change
          (QuotientGroup.mk' (lowerCentralFactorKernel P 0)
            (Subgroup.topEquiv.symm p) = 1) ↔ p ∈ A
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          ← hkernel0_map_A]
        constructor
        · intro hp
          exact ⟨Subgroup.topEquiv.symm p, hp, rfl⟩
        · rintro ⟨z, hz, hzp⟩
          have hz_eq : z = Subgroup.topEquiv.symm p := by
            apply Subtype.ext
            exact hzp
          rw [← hz_eq]
          exact hz
      let B : Subgroup P := Wsub.comap qP
      have hqP_equivariant (x : X) (p : P) :
          Additive.ofMul (qP (x • p)) =
            lowerCentralFactorLinearAut
              (MulDistribMulAction.toMulAut X P x) 0
              (Additive.ofMul (qP p)) := by
        change
          Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel P 0)
                (Subgroup.topEquiv.symm (x • p))) =
            lowerCentralFactorLinearAut
              (MulDistribMulAction.toMulAut X P x) 0
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel P 0)
                  (Subgroup.topEquiv.symm p)))
        rw [lowerCentralFactorLinearAut_ofMul_mk]
        apply Additive.toMul.injective
        apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel P 0))
        apply Subtype.ext
        rfl
      have hA_le_B : A ≤ B := by
        intro a ha
        change qP a ∈ Wsub
        have haKer : a ∈ qP.ker := by
          rw [hqker]
          exact ha
        rw [MonoidHom.mem_ker.mp haKer]
        exact Wsub.one_mem
      have hcomm_le_A : commutator P ≤ A := by
        rw [hcommutator_map_top, hcommutator_eq_A]
      have hB_normal : B.Normal := by
        constructor
        intro b hb p
        have hcommB : ⁅p, b⁆ ∈ B :=
          hA_le_B (hcomm_le_A
            (Subgroup.commutator_mem_commutator
              (show p ∈ (⊤ : Subgroup P) from trivial)
              (show b ∈ (⊤ : Subgroup P) from trivial)))
        have hprod := B.mul_mem hcommB hb
        simpa [commutatorElement_def] using hprod
      have hB_X : IsXInvariantSubgroup X B := by
        have hWpow : ∀ n : ℕ,
            ∀ v : Additive (LowerCentralFactor P 0), v ∈ W →
              (lowerCentralFactorLinearAut tau 0 ^ n) v ∈ W := by
          intro n v hv
          induction n with
          | zero => simpa using hv
          | succ n ih =>
              rw [pow_succ', LinearEquiv.mul_apply]
              exact hW _ ih
        have hforward : ∀ x : X, ∀ p : P, p ∈ B → x • p ∈ B := by
          intro x p hp
          obtain ⟨n, rfl⟩ :=
            mem_powers_iff_mem_zpowers.mpr (hg x)
          change qP (g ^ n • p) ∈ Wsub
          change qP p ∈ Wsub at hp
          have hpW : Additive.ofMul (qP p) ∈ W := by
            simpa [Wsub] using hp
          have hactW :
              lowerCentralFactorLinearAut
                  (MulDistribMulAction.toMulAut X P (g ^ n)) 0
                  (Additive.ofMul (qP p)) ∈ W := by
            rw [map_pow, lowerCentralFactorLinearAut_pow]
            simpa [tau] using hWpow n _ hpW
          have hout : Additive.ofMul (qP (g ^ n • p)) ∈ W := by
            rw [hqP_equivariant]
            exact hactW
          simpa [Wsub] using hout
        intro x p
        constructor
        · exact hforward x p
        · intro hp
          have hpinv := hforward x⁻¹ (x • p) hp
          simpa [smul_smul] using hpinv
      by_cases hWbot : W = ⊥
      · exact Or.inl hWbot
      · right
        have hqP_surj : Function.Surjective qP := by
          intro v
          obtain ⟨z, rfl⟩ :=
            QuotientGroup.mk'_surjective (lowerCentralFactorKernel P 0) v
          refine ⟨Subgroup.topEquiv z, ?_⟩
          exact congrArg (QuotientGroup.mk' (lowerCentralFactorKernel P 0))
            (Subgroup.topEquiv.symm_apply_apply z)
        have hbot_lt : (⊥ : Submodule (ZMod 2)
            (Additive (LowerCentralFactor P 0))) < W :=
          bot_lt_iff_ne_bot.mpr hWbot
        obtain ⟨v, hvW, hv0⟩ := SetLike.exists_of_lt hbot_lt
        have hv_ne : v ≠ 0 := by simpa using hv0
        obtain ⟨p, hpval⟩ := hqP_surj v.toMul
        have hpB : p ∈ B := by
          change qP p ∈ Wsub
          rw [hpval]
          simpa [Wsub] using hvW
        have hpA : p ∉ A := by
          intro hpA
          have hpKer : p ∈ qP.ker := by
            rw [hqker]
            exact hpA
          have hqone : qP p = 1 := MonoidHom.mem_ker.mp hpKer
          apply hv_ne
          apply Additive.toMul.injective
          simp [← hpval, hqone]
        have hB_ne_A : B ≠ A := by
          intro hEq
          exact hpA (hEq ▸ hpB)
        have hB_eq_top : B = ⊤ := by
          rcases hupper.2.2.2.2.2 B hB_normal hB_X hA_le_B le_top with
            hA | htop
          · exact False.elim (hB_ne_A hA)
          · exact htop
        apply eq_top_iff.mpr
        intro v _hv
        obtain ⟨p, hpval⟩ := hqP_surj v.toMul
        have hpB : p ∈ B := by
          rw [hB_eq_top]
          trivial
        change qP p ∈ Wsub at hpB
        rw [hpval] at hpB
        simpa [Wsub] using hpB
    have hxi_irreducible :
        ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)),
          (∀ v : Additive (LowerCentralFactor P 0), v ∈ W →
            lowerCentralFactorLinearAut xi 0 v ∈ W) →
          W = ⊥ ∨ W = ⊤ := by
      have htau_power_on_L1 :
          ∃ r : ℕ, lowerCentralFactorLinearAut tau 0 =
            (lowerCentralFactorLinearAut xi 0) ^ r := by
        have hT_odd :
            Odd (orderOf (lowerCentralFactorLinearAut tau 0)) := by
          rw [← Nat.not_even_iff_odd]
          intro hEven
          let T := lowerCentralFactorLinearAut tau 0
          have hT_finite : IsOfFinOrder T := by
            rw [isOfFinOrder_iff_pow_eq_one]
            refine ⟨orderOf tau, orderOf_pos tau, ?_⟩
            change (lowerCentralFactorLinearAut tau 0) ^ orderOf tau = 1
            rw [← lowerCentralFactorLinearAut_pow, pow_orderOf_eq_one]
            exact map_one (lowerCentralFactorLinearAutHom (H := P) 0)
          obtain ⟨d, hd⟩ := hEven
          have hord : orderOf T = 2 * d := by
            change orderOf T = d + d at hd
            omega
          have hord_pos : 0 < orderOf T :=
            orderOf_pos_iff.mpr hT_finite
          have hd_pos : 0 < d := by omega
          let U := T ^ d
          have hU_sq : U ^ 2 = 1 := by
            change (T ^ d) ^ 2 = 1
            rw [← pow_mul, Nat.mul_comm, ← hord, pow_orderOf_eq_one]
          have hU_ne : U ≠ 1 := by
            intro hU
            have hle : orderOf T ≤ d :=
              orderOf_le_of_pow_eq_one hd_pos (by simpa [U] using hU)
            omega
          have hfixed_ne_top : U.fixedSubmodule ≠ ⊤ := by
            intro htop
            have hU_refl : U = LinearEquiv.refl (ZMod 2)
                (Additive (LowerCentralFactor P 0)) :=
              LinearEquiv.fixedSubmodule_eq_top_iff.mp htop
            apply hU_ne
            rw [hU_refl]
            rfl
          obtain ⟨v, hv⟩ :
              ∃ v : Additive (LowerCentralFactor P 0), U v ≠ v := by
            by_contra h
            push Not at h
            apply hU_ne
            ext v
            simpa using h v
          let w := U v - v
          have hw_ne : w ≠ 0 := by
            simpa [w] using sub_ne_zero.mpr hv
          have hU_apply_apply : U (U v) = v := by
            calc
              U (U v) = (U * U) v := by
                rw [LinearEquiv.mul_apply]
              _ = v := by
                rw [← pow_two, hU_sq]
                rfl
          have hw_fixed : U w = w := by
            dsimp [w]
            rw [map_sub, hU_apply_apply]
            simp only [sub_eq_add_neg, ZModModule.neg_eq_self, add_comm]
          have hw_mem : w ∈ U.fixedSubmodule := by
            rw [LinearMap.mem_fixedSubmodule_iff]
            exact hw_fixed
          have hfixed_ne_bot : U.fixedSubmodule ≠ ⊥ := by
            intro hbot
            have hw_bot : w ∈
                (⊥ : Submodule (ZMod 2)
                  (Additive (LowerCentralFactor P 0))) := by
              rw [← hbot]
              exact hw_mem
            exact hw_ne (by simpa using hw_bot)
          have hfixed_T :
              ∀ z : Additive (LowerCentralFactor P 0),
                z ∈ U.fixedSubmodule → T z ∈ U.fixedSubmodule := by
            intro z hz
            rw [LinearMap.mem_fixedSubmodule_iff] at hz ⊢
            change U z = z at hz
            change U (T z) = T z
            calc
              U (T z) = (U * T) z := rfl
              _ = (T * U) z := by
                change (T ^ d * T) z = (T * T ^ d) z
                rw [← pow_succ, pow_succ']
              _ = T (U z) := rfl
              _ = T z := by rw [hz]
          rcases htau_irreducible U.fixedSubmodule hfixed_T with hbot | htop
          · exact hfixed_ne_bot hbot
          · exact hfixed_ne_top htop
        have hcoprime :
            Nat.Coprime (2 ^ k)
              (orderOf (lowerCentralFactorLinearAut tau 0)) :=
          Nat.Coprime.pow_left k hT_odd.coprime_two_left
        obtain ⟨r, hr⟩ :=
          exists_pow_eq_self_of_coprime
            (x := lowerCentralFactorLinearAut tau 0) hcoprime
        refine ⟨r, ?_⟩
        simpa [xi, lowerCentralFactorLinearAut_pow] using hr.symm
      intro W hW
      apply htau_irreducible W
      obtain ⟨r, hr⟩ := htau_power_on_L1
      intro v hv
      rw [hr]
      have hpow_mem : ∀ j : ℕ,
          (lowerCentralFactorLinearAut xi 0 ^ j) v ∈ W := by
        intro j
        induction j with
        | zero => simpa using hv
        | succ j ih =>
            rw [pow_succ', LinearEquiv.mul_apply]
            exact hW _ ih
      exact hpow_mem r
    have htau_transitive :
        ∀ x : Additive (LowerCentralFactor P 1), x ≠ 0 →
          ∀ y : Additive (LowerCentralFactor P 1), y ≠ 0 →
            ∃ j : ℕ, (lowerCentralFactorLinearAut tau 1 ^ j) x = y := by
      intro x hx y hy
      obtain ⟨a, ha⟩ :=
        QuotientGroup.mk'_surjective (lowerCentralFactorKernel P 1) x.toMul
      obtain ⟨b, hb⟩ :=
        QuotientGroup.mk'_surjective (lowerCentralFactorKernel P 1) y.toMul
      have ha_ne : (a : P) ≠ 1 := by
        intro ha1
        apply hx
        apply Additive.toMul.injective
        change x.toMul = 1
        rw [← ha]
        have ha_one : a = 1 := Subtype.ext ha1
        rw [ha_one]
        exact map_one _
      have hb_ne : (b : P) ≠ 1 := by
        intro hb1
        apply hy
        apply Additive.toMul.injective
        change y.toMul = 1
        rw [← hb]
        have hb_one : b = 1 := Subtype.ext hb1
        rw [hb_one]
        exact map_one _
      let aA : A := ⟨a, hL1_eq_A ▸ a.property⟩
      let bA : A := ⟨b, hL1_eq_A ▸ b.property⟩
      have ha_sq : (a : P) ^ 2 = 1 := by
        simpa [aA] using congrArg Subtype.val (hA_exponent_two aA)
      have hb_sq : (b : P) ^ 2 = 1 := by
        simpa [bA] using congrArg Subtype.val (hA_exponent_two bA)
      obtain ⟨z, hz⟩ :=
        _hXtrans (a : P) ⟨ha_ne, ha_sq⟩ (b : P) ⟨hb_ne, hb_sq⟩
      obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hg z)
      refine ⟨j, ?_⟩
      have hx_repr : x =
          Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel P 1) a) := by
        apply Additive.toMul.injective
        exact ha.symm
      have hy_repr : y =
          Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel P 1) b) := by
        apply Additive.toMul.injective
        exact hb.symm
      rw [← lowerCentralFactorLinearAut_pow, hx_repr, hy_repr,
        lowerCentralFactorLinearAut_ofMul_mk]
      apply Additive.toMul.injective
      apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel P 1))
      apply Subtype.ext
      change (tau ^ j) (a : P) = (b : P)
      have hpow_aut :
          tau ^ j = MulDistribMulAction.toMulAut X P (g ^ j) := by
        change (MulDistribMulAction.toMulAut X P g) ^ j =
          MulDistribMulAction.toMulAut X P (g ^ j)
        exact (map_pow (MulDistribMulAction.toMulAut X P) g j).symm
      rw [hpow_aut]
      exact hz.symm
    have hxi_transitive :
        ∀ x : Additive (LowerCentralFactor P 1), x ≠ 0 →
          ∀ y : Additive (LowerCentralFactor P 1), y ≠ 0 →
            ∃ j : ℕ, (lowerCentralFactorLinearAut xi 1 ^ j) x = y := by
      let Ttau := lowerCentralFactorLinearAut tau 1
      let Txi := lowerCentralFactorLinearAut xi 1
      have hTxi_pow : Txi = Ttau ^ (2 ^ k) := by
        simpa [Ttau, Txi, xi] using
          (lowerCentralFactorLinearAut_pow tau 1 (2 ^ k))
      obtain ⟨n, hn, hcard⟩ := hfactor1_card
      have horder : orderOf Ttau = 2 ^ n - 1 :=
        lemma4_transitive_linearAut_order Ttau
          (by simpa [Ttau] using htau_transitive) n hn hcard
      have hodd : Odd (orderOf Ttau) := by
        rw [horder]
        obtain ⟨d, hd⟩ :=
          Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        subst n
        refine ⟨2 ^ d - 1, ?_⟩
        rw [pow_succ]
        have hpow_pos : 0 < 2 ^ d := by positivity
        omega
      have hcoprime : Nat.Coprime (2 ^ k) (orderOf Ttau) :=
        Nat.Coprime.pow_left k hodd.coprime_two_left
      obtain ⟨u, hu⟩ :=
        exists_pow_eq_self_of_coprime (x := Ttau) hcoprime
      have hrecover : Ttau = Txi ^ u := by
        simpa [hTxi_pow] using hu.symm
      intro x hx y hy
      obtain ⟨j, hj⟩ := htau_transitive x hx y hy
      refine ⟨u * j, ?_⟩
      simpa [Ttau, Txi, pow_mul, ← hrecover] using hj
    obtain ⟨n, hn, hcard⟩ := hfactor1_card
    let S := lowerCentralFactorLinearAut xi 1
    have hS_order : orderOf S = 2 ^ n - 1 :=
      lemma4_transitive_linearAut_order S
        (by simpa [S] using hxi_transitive) n hn hcard
    rcases _hP.2.2.1 with ⟨x0, _y0, hx0, _hy0, _hxy0⟩
    have hx0A : x0 ∈ A :=
      lemma1_involutions_mem_of_nontrivial_invariant
        _hP _hXtrans hlower.2.2.2.1 (ne_of_gt hlower.1) x0 hx0
    let x1 : higmanLowerCentralSeries P 1 :=
      ⟨x0, hL1_eq_A.symm ▸ hx0A⟩
    let v : Additive (LowerCentralFactor P 1) :=
      Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel P 1) x1)
    have hS_pow : S ^ (2 ^ n - 1) = 1 := by
      rw [← hS_order]
      exact pow_orderOf_eq_one S
    have hvfix :
        lowerCentralFactorLinearAut (xi ^ (2 ^ n - 1)) 1 v = v := by
      rw [lowerCentralFactorLinearAut_pow, hS_pow]
      rfl
    rw [show v = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel P 1) x1) by rfl,
      lowerCentralFactorLinearAut_ofMul_mk] at hvfix
    have hqeq :
        QuotientGroup.mk' (lowerCentralFactorKernel P 1)
            (lowerCentralSeriesMulAut (xi ^ (2 ^ n - 1)) 1 x1) =
          QuotientGroup.mk' (lowerCentralFactorKernel P 1) x1 :=
      Additive.ofMul.injective hvfix
    have hdiv :
        lowerCentralSeriesMulAut (xi ^ (2 ^ n - 1)) 1 x1 / x1 ∈
          lowerCentralFactorKernel P 1 :=
      QuotientGroup.eq_iff_div_mem.mp hqeq
    rw [hkernel1_bot] at hdiv
    have hx1fix :
        lowerCentralSeriesMulAut (xi ^ (2 ^ n - 1)) 1 x1 = x1 := by
      apply div_eq_one.mp
      exact Subgroup.mem_bot.mp hdiv
    have hxi_fix : (xi ^ (2 ^ n - 1)) x0 = x0 :=
      congrArg Subtype.val hx1fix
    have hxi_actor :
        xi = MulDistribMulAction.toMulAut X P (g ^ (2 ^ k)) := by
      change (MulDistribMulAction.toMulAut X P g) ^ (2 ^ k) =
        MulDistribMulAction.toMulAut X P (g ^ (2 ^ k))
      exact (map_pow (MulDistribMulAction.toMulAut X P) g (2 ^ k)).symm
    have hactor_aut :
        xi ^ (2 ^ n - 1) =
          MulDistribMulAction.toMulAut X P
            ((g ^ (2 ^ k)) ^ (2 ^ n - 1)) := by
      rw [hxi_actor]
      exact (map_pow (MulDistribMulAction.toMulAut X P)
        (g ^ (2 ^ k)) (2 ^ n - 1)).symm
    have hactor_fix :
        (g ^ (2 ^ k)) ^ (2 ^ n - 1) • x0 = x0 := by
      change MulDistribMulAction.toMulAut X P
          ((g ^ (2 ^ k)) ^ (2 ^ n - 1)) x0 = x0
      rw [← hactor_aut]
      exact hxi_fix
    rcases _hXregular.2 x0 hx0 x0 hx0 with ⟨z, _hz, hunique⟩
    have hactor_eq : (g ^ (2 ^ k)) ^ (2 ^ n - 1) = z :=
      hunique _ hactor_fix.symm
    have hone_eq : (1 : X) = z := hunique 1 (by simp)
    have hactor_one : (g ^ (2 ^ k)) ^ (2 ^ n - 1) = 1 :=
      hactor_eq.trans hone_eq.symm
    have hxi_pow : xi ^ (2 ^ n - 1) = 1 := by
      rw [hactor_aut, hactor_one]
      exact map_one (MulDistribMulAction.toMulAut X P)
    have hxi_dvd : orderOf xi ∣ 2 ^ n - 1 :=
      (orderOf_dvd_iff_pow_eq_one).2 hxi_pow
    have hq_dvd : 2 ^ n - 1 ∣ orderOf xi := by
      rw [← hS_order]
      change orderOf ((lowerCentralFactorLinearAutHom (H := P) 1) xi) ∣
        orderOf xi
      exact orderOf_map_dvd (lowerCentralFactorLinearAutHom (H := P) 1) xi
    have hxi_order : orderOf xi = 2 ^ n - 1 :=
      Nat.dvd_antisymm hxi_dvd hq_dvd
    have hfactor1_card_eq_A :
        Nat.card (LowerCentralFactor P 1) = Nat.card A := by
      change Nat.card
          ((higmanLowerCentralSeries P 1) ⧸ lowerCentralFactorKernel P 1) =
        Nat.card A
      rw [hkernel1_bot]
      calc
        Nat.card ((higmanLowerCentralSeries P 1) ⧸
              (⊥ : Subgroup (higmanLowerCentralSeries P 1))) =
            Nat.card (higmanLowerCentralSeries P 1) := by
              exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
        _ = Nat.card A := Nat.card_congr
          (Set.equivOfEq (congrArg (fun R : Subgroup P => (R : Set P))
            hL1_eq_A))
    have hA_card : Nat.card A = 2 ^ n :=
      hfactor1_card_eq_A.symm.trans hcard
    let involEquiv : {x : P // x ∈ involutions P} ≃ {a : A // a ≠ 1} :=
      { toFun := fun x =>
          ⟨⟨x, lemma1_involutions_mem_of_nontrivial_invariant
            _hP _hXtrans hlower.2.2.2.1 (ne_of_gt hlower.1)
              x x.property⟩, fun hx => x.property.1 (congrArg Subtype.val hx)⟩
        invFun := fun a =>
          ⟨a.1, ⟨fun ha => a.2 (Subtype.ext ha), by
            simpa using congrArg Subtype.val (hA_exponent_two a.1)⟩⟩
        left_inv := by
          intro x
          apply Subtype.ext
          rfl
        right_inv := by
          intro a
          apply Subtype.ext
          apply Subtype.ext
          rfl }
    have hinvolution_card :
        Nat.card {x : P // x ∈ involutions P} = 2 ^ n - 1 := by
      calc
        Nat.card {x : P // x ∈ involutions P} =
            Nat.card {a : A // a ≠ 1} := Nat.card_congr involEquiv
        _ = Nat.card A - 1 := by
          let : Fintype A := Fintype.ofFinite A
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          simp
        _ = 2 ^ n - 1 := by rw [hA_card]
    obtain ⟨x0, _y0, hx0, _hy0, _hxy0⟩ := _hP.2.2.1
    let orbit : X → {x : P // x ∈ involutions P} :=
      fun x => ⟨x • x0, _hXregular.1 x0 hx0 x⟩
    have horbit_injective : Function.Injective orbit := by
      intro x y hxy
      have heq : x • x0 = y • x0 := congrArg Subtype.val hxy
      rcases _hXregular.2 x0 hx0 (x • x0)
          (_hXregular.1 x0 hx0 x) with ⟨a, _ha, huniq⟩
      exact (huniq x rfl).trans (huniq y heq).symm
    have horbit_surjective : Function.Surjective orbit := by
      rintro ⟨y, hy⟩
      rcases _hXregular.2 x0 hx0 y hy with ⟨x, hx, _huniq⟩
      exact ⟨x, Subtype.ext hx.symm⟩
    have hX_card : Nat.card X = 2 ^ n - 1 := by
      calc
        Nat.card X = Nat.card {x : P // x ∈ involutions P} :=
          Nat.card_congr (Equiv.ofBijective orbit
            ⟨horbit_injective, horbit_surjective⟩)
        _ = 2 ^ n - 1 := hinvolution_card
    let actor : X := g ^ (2 ^ k)
    have hactor_order : orderOf actor = 2 ^ n - 1 := by
      calc
        orderOf actor =
            orderOf (MulDistribMulAction.toMulAut X P actor) :=
          (orderOf_injective (MulDistribMulAction.toMulAut X P)
            htoMulAut_injective actor).symm
        _ = orderOf xi := by rw [← hxi_actor]
        _ = 2 ^ n - 1 := hxi_order
    have hactor_zpowers : Subgroup.zpowers actor = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers,
        hactor_order, hX_card]
    exact ⟨actor, xi, n, (fun x => by rw [hactor_zpowers]; trivial),
      by simpa [actor] using hxi_actor, hactor_order,
      hxi_odd, hn, hcard, hxi_order, hkernel1_bot,
      hkernel0_map_A, hxi_irreducible,
      hxi_transitive, hsquares_le⟩
  have hspectral_typeA : IsSuzukiTwoTypeAWithActor X P := by
    let : FaithfulSMul X P := _hXfaithful
    have htoMulAut_injective :
        Function.Injective (MulDistribMulAction.toMulAut X P) := by
      intro x y hxy
      apply FaithfulSMul.eq_of_smul_eq_smul (α := P)
      intro p
      exact congrArg (fun f : MulAut P => f p) hxy
    let : Finite X := Finite.of_injective
      (MulDistribMulAction.toMulAut X P) htoMulAut_injective
    rcases hfactor_action_data with
      ⟨actor, xi, n, hactor_generator, hxi_actor, hactor_order,
        hxi_odd, hn, hL2_card, hxi_order, hkernel1_bot, hkernel0_map_A,
        hL1_irreducible, hL2_transitive, hP_square⟩
    obtain ⟨m, hm, lambda, coordinates, u, xiK, bracket, bracketK,
        squareMap, hL1_card, hlambda, hcoordinates, hxiK_tmul, hu_eigen,
        hu_expansion, hbracketK_tmul, hbracket_mk, hsquare_mk,
        hsquare_equivariant, hsquare_add, hsquare_formula⟩ :=
      lemma5_square_map_normal_form
        (isPGroup_of_isSuzukiTwoGroup _hP) _hP.2.1 xi hxi_odd
        hL1_irreducible hL2_transitive n hn hL2_card hP_square
    rcases lemma5_lowerCentralBracket_interfaces
        xi m xiK bracket bracketK hxiK_tmul hbracketK_tmul hbracket_mk with
      ⟨hbracket_equivariant, hbracketK_equivariant, hbracket_self,
        hbracketK_self, hbracket_span⟩
    let T := lowerCentralFactorLinearAut xi 0
    let S := lowerCentralFactorLinearAut xi 1
    have hS_order : orderOf S = 2 ^ n - 1 :=
      lemma4_transitive_linearAut_order S
        (by simpa [S] using hL2_transitive) n hn hL2_card
    have hS_dvd_T : orderOf S ∣ orderOf T :=
      lemma11_target_order_dvd_source_of_bilinear_span T S bracket
        (by simpa [T, S] using hbracket_equivariant) hbracket_span
    have hq_dvd_T : 2 ^ n - 1 ∣ orderOf T := by
      rw [← hS_order]
      exact hS_dvd_T
    have hT_dvd_q : orderOf T ∣ 2 ^ n - 1 := by
      rw [← hxi_order]
      change orderOf ((lowerCentralFactorLinearAutHom (H := P) 0) xi) ∣
        orderOf xi
      exact orderOf_map_dvd (lowerCentralFactorLinearAutHom (H := P) 0) xi
    have hT_order : orderOf T = 2 ^ n - 1 :=
      Nat.dvd_antisymm hT_dvd_q hq_dvd_T
    have hL1_card_n : Nat.card (LowerCentralFactor P 0) = 2 ^ n :=
      lemma5_irreducible_card_of_order T
        (by simpa [T] using hL1_irreducible) n hn hT_order
    have hmn : m = n := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      exact hL1_card.symm.trans hL1_card_n
    subst m
    have hL2_add_card :
        Nat.card (Additive (LowerCentralFactor P 1)) = 2 ^ n := by
      exact (Nat.card_congr Additive.toMul).trans hL2_card
    have hL2_card_gt :
        1 < Nat.card (Additive (LowerCentralFactor P 1)) := by
      rw [hL2_add_card]
      exact one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega)
    let : Nontrivial (Additive (LowerCentralFactor P 1)) :=
      Finite.one_lt_card_iff_nontrivial.mp hL2_card_gt
    have hS_irreducible :=
      lemma6_irreducible_of_transitive S
        (by simpa [S] using hL2_transitive)
    obtain ⟨d, hd, mu, centerCoordinates, centerBasis, hcenter_card,
        hmu, hcenterCoordinates, hcenterBasis_eigen,
        hcenterBasis_expansion⟩ :=
      lemma5_irreducible_conjugate_eigenbasis S hS_irreducible
    have hdn : d = n := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      exact hcenter_card.symm.trans hL2_add_card
    subst d
    have hlambda_order :
        orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1 := by
      calc
        orderOf (Units.mk0 lambda hlambda) = orderOf T :=
          (lemma6_coordinate_unit_order T coordinates lambda hlambda
            (by simpa [T] using hcoordinates)).symm
        _ = 2 ^ n - 1 := hT_order
    have hmu_order : orderOf (Units.mk0 mu hmu) = 2 ^ n - 1 := by
      calc
        orderOf (Units.mk0 mu hmu) = orderOf S :=
          (lemma6_coordinate_unit_order S centerCoordinates mu hmu
            hcenterCoordinates).symm
        _ = 2 ^ n - 1 := hS_order
    have hbracketK_span :=
      lemma6_scalarExtendedBilinear_span
        bracket bracketK hbracketK_tmul hbracket_span
    obtain ⟨i, j, hij⟩ :=
      lemma6_exists_basis_pair_ne_zero_of_span_eq_top
        bracketK u hbracketK_span
    have hij_ne : i ≠ j := by
      intro hij_eq
      subst j
      exact hij (hbracketK_self (u i))
    obtain ⟨s, hseed⟩ :=
      lemma6_nonzero_equivariant_bilinear_basis_value_spectrum
        xiK
        (S.baseChange (ZMod 2) (BinaryGaloisField n)
          (Additive (LowerCentralFactor P 1))
          (Additive (LowerCentralFactor P 1)))
        bracketK (by simpa [S] using hbracketK_equivariant)
        u (fun t : Fin n => lambda ^ (2 ^ (t : ℕ))) hu_eigen
        centerBasis (fun t : Fin n => mu ^ (2 ^ (t : ℕ)))
        (by simpa [S] using hcenterBasis_eigen) i j hij
    let r := lemma6_finPairGap i j
    have hr_pos : 0 < r := lemma6_finPairGap_pos_of_ne hij_ne
    have hr_lt : r < n := lemma6_finPairGap_lt i j
    have hbracket_support : ∀ x y : Fin n,
        bracketK (u x) (u y) ≠ 0 →
          lemma6_finPairSupported r x y := by
      intro x y hxy
      have hxy_ne : x ≠ y := by
        intro hxy_eq
        subst y
        exact hxy (hbracketK_self (u x))
      obtain ⟨t, hpair⟩ :=
        lemma6_nonzero_equivariant_bilinear_basis_value_spectrum
          xiK
          (S.baseChange (ZMod 2) (BinaryGaloisField n)
            (Additive (LowerCentralFactor P 1))
            (Additive (LowerCentralFactor P 1)))
          bracketK (by simpa [S] using hbracketK_equivariant)
          u (fun a : Fin n => lambda ^ (2 ^ (a : ℕ))) hu_eigen
          centerBasis (fun a : Fin n => mu ^ (2 ^ (a : ℕ)))
          (by simpa [S] using hcenterBasis_eigen) x y hxy
      exact lemma6_finPairSupported_of_primitive_pair_eigenvalue_eq
        (by omega : 0 < n) lambda mu hlambda hmu hlambda_order
        i j x y hij_ne hxy_ne s t hseed hpair
    have hsquare_anisotropic : ∀ v : Additive (LowerCentralFactor P 0),
        squareMap v = 0 → v = 0 := by
      intro v hv
      obtain ⟨x, hx⟩ :=
        QuotientGroup.mk'_surjective (lowerCentralFactorKernel P 0) v.toMul
      have hv_repr : v = Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel P 0) x) := by
        apply Additive.toMul.injective
        exact hx.symm
      have hxsquare_mem : (x : P) ^ 2 ∈ higmanLowerCentralSeries P 1 :=
        hP_square (Subgroup.subset_closure ⟨(x : P), rfl⟩)
      have hmk_zero :
          Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel P 1)
                ⟨(x : P) ^ 2, hxsquare_mem⟩) = 0 := by
        rw [← hsquare_mk x hxsquare_mem, ← hv_repr]
        exact hv
      have hmk_one :
          QuotientGroup.mk' (lowerCentralFactorKernel P 1)
              ⟨(x : P) ^ 2, hxsquare_mem⟩ = 1 := by
        apply Additive.ofMul.injective
        simpa using hmk_zero
      have hsqker :
          (⟨(x : P) ^ 2, hxsquare_mem⟩ : higmanLowerCentralSeries P 1) ∈
            lowerCentralFactorKernel P 1 :=
        (QuotientGroup.eq_one_iff
          (N := lowerCentralFactorKernel P 1)
          (⟨(x : P) ^ 2, hxsquare_mem⟩ : higmanLowerCentralSeries P 1)).mp hmk_one
      rw [hkernel1_bot] at hsqker
      have hxsquare : (x : P) ^ 2 = 1 := by
        have hsquare_one :
            (⟨(x : P) ^ 2, hxsquare_mem⟩ : higmanLowerCentralSeries P 1) = 1 := by
          exact Subgroup.mem_bot.mp hsqker
        exact congrArg Subtype.val hsquare_one
      by_cases hxone : (x : P) = 1
      · apply Additive.toMul.injective
        change v.toMul = 1
        rw [← hx]
        have xone : x = 1 := Subtype.ext hxone
        rw [xone]
        exact map_one _
      · have hxinv : (x : P) ∈ involutions P := ⟨hxone, hxsquare⟩
        have hxcenter : (x : P) ∈ Subgroup.center P := by
          have hxset : (x : P) ∈
              {z : P | z ∈ Subgroup.center P ∧ z ≠ 1} := by
            rw [← hinvolutions_center]
            exact hxinv
          exact hxset.1
        have hxA : (x : P) ∈ A := by
          rw [hA_eq_center]
          exact hxcenter
        have hxmap : (x : P) ∈
            (lowerCentralFactorKernel P 0).map
              (higmanLowerCentralSeries P 0).subtype := by
          rw [hkernel0_map_A]
          exact hxA
        rcases hxmap with ⟨z, hz, hzx⟩
        have hzx' : z = x := by
          apply Subtype.ext
          exact hzx
        have hxker : x ∈ lowerCentralFactorKernel P 0 := hzx' ▸ hz
        have hxquot :
            QuotientGroup.mk' (lowerCentralFactorKernel P 0) x = 1 :=
          (QuotientGroup.eq_one_iff
            (N := lowerCentralFactorKernel P 0) x).mpr hxker
        apply Additive.toMul.injective
        change v.toMul = 1
        rw [← hx]
        exact hxquot
    let sigma : BinaryGaloisField n ≃ₐ[ZMod 2] BinaryGaloisField n :=
      FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod 2) (BinaryGaloisField n)
    have hsigma_apply (a : BinaryGaloisField n) (t : ℕ) :
        (sigma ^ t) a = a ^ (2 ^ t) := by
      rw [AlgEquiv.coe_pow,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
      simp [ZMod.card]
    let qBase : BinaryGaloisField n → BinaryGaloisField n :=
      fun a => centerCoordinates.symm (squareMap (coordinates a))
    have hqBase_equivariant (a : BinaryGaloisField n) :
        qBase (lambda * a) = mu * qBase a := by
      apply centerCoordinates.injective
      calc
        centerCoordinates (qBase (lambda * a)) =
            squareMap (coordinates (lambda * a)) := by
              simp [qBase]
        _ = squareMap (T (coordinates a)) := by rw [hcoordinates]
        _ = S (squareMap (coordinates a)) := by
          simpa [T, S] using hsquare_equivariant (coordinates a)
        _ = S (centerCoordinates (qBase a)) := by simp [qBase]
        _ = centerCoordinates (mu * qBase a) := hcenterCoordinates _
    let e : ℕ := 2 ^ (i : ℕ) + 2 ^ (j : ℕ)
    have he_pos : 0 < e := by positivity
    let qTwist : BinaryGaloisField n → BinaryGaloisField n :=
      fun a => (sigma ^ (s : ℕ)) (qBase a)
    have hmu_twist :
        (sigma ^ (s : ℕ)) mu = lambda ^ e := by
      calc
        (sigma ^ (s : ℕ)) mu = mu ^ (2 ^ (s : ℕ)) :=
          hsigma_apply mu s
        _ = lambda ^ (2 ^ (i : ℕ)) * lambda ^ (2 ^ (j : ℕ)) :=
          hseed.symm
        _ = lambda ^ e := by simp [e, pow_add]
    have hqTwist_equivariant (a : BinaryGaloisField n) :
        qTwist (lambda * a) = lambda ^ e * qTwist a := by
      dsimp [qTwist]
      rw [hqBase_equivariant, map_mul, hmu_twist]
    have hsquare_zero : squareMap 0 = 0 := by
      simpa using hsquare_add 0 0
    have hqBase_zero : qBase 0 = 0 := by
      simp [qBase, hsquare_zero]
    have hqTwist_zero : qTwist 0 = 0 := by
      simp [qTwist, hqBase_zero]
    have hqBase_one_ne : qBase 1 ≠ 0 := by
      intro hzero
      have hsquare_one_zero : squareMap (coordinates 1) = 0 := by
        have h := congrArg centerCoordinates hzero
        simpa [qBase] using h
      have hcoord_one_zero :=
        hsquare_anisotropic (coordinates 1) hsquare_one_zero
      exact one_ne_zero
        (coordinates.injective (hcoord_one_zero.trans coordinates.map_zero.symm))
    have hqTwist_one_ne : qTwist 1 ≠ 0 := by
      intro hzero
      apply hqBase_one_ne
      apply (sigma ^ (s : ℕ)).injective
      simpa [qTwist] using hzero
    have hlambda_units_card :
        Nat.card (BinaryGaloisField n)ˣ = 2 ^ n - 1 := by
      rw [Nat.card_units, GaloisField.card 2 n (by omega)]
    have hqTwist_formula : ∀ a : BinaryGaloisField n,
        qTwist a = qTwist 1 * a ^ e :=
      lemma11_singer_equivariant_function_eq_monomial
        lambda hlambda (hlambda_order.trans hlambda_units_card.symm)
        qTwist hqTwist_zero e he_pos hqTwist_equivariant
    let rho : BinaryGaloisField n ≃ₐ[ZMod 2] BinaryGaloisField n :=
      (sigma ^ (i : ℕ)).symm
    let thetaAlg : BinaryGaloisField n ≃ₐ[ZMod 2]
        BinaryGaloisField n :=
      sigma ^ (j : ℕ) * rho
    let theta : BinaryGaloisField n ≃+* BinaryGaloisField n :=
      thetaAlg.toRingEquiv
    have hpower_transform (a : BinaryGaloisField n) :
        (rho a) ^ e = a * theta a := by
      rw [show e = 2 ^ (i : ℕ) + 2 ^ (j : ℕ) by rfl, pow_add,
        ← hsigma_apply (rho a) i, ← hsigma_apply (rho a) j]
      simp [rho, theta, thetaAlg, AlgEquiv.mul_apply]
    let quotientCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
        Additive (LowerCentralFactor P 0) :=
      rho.toLinearEquiv.trans coordinates
    let lambdaFinal : BinaryGaloisField n := rho.symm lambda
    have hlambdaFinal : lambdaFinal ≠ 0 := by
      intro hzero
      apply hlambda
      have := congrArg rho hzero
      simpa [lambdaFinal] using this
    have hquotientCoordinates_actor (a : BinaryGaloisField n) :
        lowerCentralFactorLinearAut xi 0 (quotientCoordinates a) =
          quotientCoordinates (lambdaFinal * a) := by
      change T (coordinates (rho a)) =
        coordinates (rho (lambdaFinal * a))
      rw [hcoordinates]
      simp [lambdaFinal]
    let c : BinaryGaloisField n := qTwist 1
    have hc : c ≠ 0 := hqTwist_one_ne
    let cUnit : (BinaryGaloisField n)ˣ := Units.mk0 c hc
    let outputTransform : BinaryGaloisField n ≃ₗ[ZMod 2]
        BinaryGaloisField n :=
      (sigma ^ (s : ℕ)).toLinearEquiv.trans
        ((cUnit⁻¹).mulLeftLinearEquiv (ZMod 2) (BinaryGaloisField n))
    let finalCenterCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1) :=
      outputTransform.symm.trans centerCoordinates
    have hcenterCoordinates_actor (z : BinaryGaloisField n) :
        lowerCentralFactorLinearAut xi 1 (finalCenterCoordinates z) =
          finalCenterCoordinates
            (lambdaFinal * theta lambdaFinal * z) := by
      change S (centerCoordinates (outputTransform.symm z)) =
        centerCoordinates
          (outputTransform.symm (lambdaFinal * theta lambdaFinal * z))
      rw [hcenterCoordinates]
      congr 1
      apply outputTransform.injective
      calc
        outputTransform (mu * outputTransform.symm z) =
            (sigma ^ (s : ℕ)) mu *
              outputTransform (outputTransform.symm z) := by
          change c⁻¹ * (sigma ^ (s : ℕ))
              (mu * outputTransform.symm z) =
            (sigma ^ (s : ℕ)) mu *
              (c⁻¹ * (sigma ^ (s : ℕ)) (outputTransform.symm z))
          rw [map_mul]
          ring
        _ = lambda ^ e * z := by
          rw [hmu_twist, outputTransform.apply_symm_apply]
        _ = lambdaFinal * theta lambdaFinal * z := by
          rw [← hpower_transform lambdaFinal]
          simp [lambdaFinal]
        _ = outputTransform
            (outputTransform.symm
              (lambdaFinal * theta lambdaFinal * z)) := by
          rw [outputTransform.apply_symm_apply]
    have hsquare_coordinates (a : BinaryGaloisField n) :
        finalCenterCoordinates.symm
            (squareMap (quotientCoordinates a)) = a * theta a := by
      change c⁻¹ * qTwist (rho a) = a * theta a
      rw [hqTwist_formula, hpower_transform]
      simp [c, hc]
    have hsigma_order : orderOf sigma = n := by
      rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
        GaloisField.finrank 2 (by omega)]
    have hlambda_field_order : orderOf lambda = 2 ^ n - 1 := by
      calc
        orderOf lambda = orderOf (Units.mk0 lambda hlambda) :=
          by simpa using (orderOf_units
            (G := BinaryGaloisField n) (y := Units.mk0 lambda hlambda))
        _ = 2 ^ n - 1 := hlambda_order
    have hlambda_e_order : orderOf (lambda ^ e) = 2 ^ n - 1 := by
      calc
        orderOf (lambda ^ e) = orderOf ((sigma ^ (s : ℕ)) mu) := by
          rw [hmu_twist]
        _ = orderOf mu := orderOf_injective
          (sigma ^ (s : ℕ)).toAlgHom.toMonoidHom
          (sigma ^ (s : ℕ)).injective mu
        _ = orderOf (Units.mk0 mu hmu) := by
          simpa using (orderOf_units
            (G := BinaryGaloisField n) (y := Units.mk0 mu hmu))
        _ = 2 ^ n - 1 := hmu_order
    have hcop_e : Nat.Coprime (2 ^ n - 1) e := by
      have hformula := orderOf_pow' lambda he_pos.ne'
      rw [hlambda_field_order] at hformula
      have hdiv : (2 ^ n - 1) / (2 ^ n - 1).gcd e = 2 ^ n - 1 :=
        hformula.symm.trans hlambda_e_order
      have hcancel := Nat.div_mul_cancel (Nat.gcd_dvd_left (2 ^ n - 1) e)
      rw [hdiv] at hcancel
      have hq_pos : 0 < 2 ^ n - 1 := by omega
      apply Nat.coprime_iff_gcd_eq_one.mpr
      apply (mul_left_cancel_iff_of_pos hq_pos).mp
      simpa using hcancel
    have hgap_dvd : 2 ^ r + 1 ∣ e := by
      simpa only [r, e, lemma6_finPairGap] using
        lemma11_two_pow_gap_add_one_dvd_sum (i : ℕ) (j : ℕ)
    have hcop_gap : Nat.Coprime (2 ^ n - 1) (2 ^ r + 1) :=
      hcop_e.of_dvd_right hgap_dvd
    let period := n / n.gcd r
    have hperiod_odd : Odd period := by
      exact lemma11_odd_div_gcd_of_coprime_two_pow_add (by omega) hcop_gap
    have hsigma_gap_order : orderOf (sigma ^ r) = period := by
      dsimp [period]
      rw [orderOf_pow, hsigma_order]
    have hthetaAlg_gap : thetaAlg = sigma ^ r ∨ thetaAlg = (sigma ^ r)⁻¹ := by
      rcases le_total (i : ℕ) (j : ℕ) with hij_le | hji_le
      · left
        change sigma ^ (j : ℕ) * (sigma ^ (i : ℕ))⁻¹ = sigma ^ r
        rw [← pow_sub sigma hij_le]
        congr 1
        simp [r, lemma6_finPairGap, Nat.sub_eq_zero_of_le hij_le]
      · right
        change sigma ^ (j : ℕ) * (sigma ^ (i : ℕ))⁻¹ = (sigma ^ r)⁻¹
        rw [show r = (i : ℕ) - (j : ℕ) by
          simp [r, lemma6_finPairGap, Nat.sub_eq_zero_of_le hji_le]]
        rw [pow_sub sigma hji_le, mul_inv_rev, inv_inv]
    have hthetaAlg_order : orderOf thetaAlg = period := by
      rcases hthetaAlg_gap with hthetaAlg | hthetaAlg
      · rw [hthetaAlg, hsigma_gap_order]
      · rw [hthetaAlg, orderOf_inv, hsigma_gap_order]
    have hthetaAlg_pow : thetaAlg ^ period = 1 := by
      rw [← hthetaAlg_order]
      exact pow_orderOf_eq_one thetaAlg
    have htheta_period : ∀ x : BinaryGaloisField n, theta^[period] x = x := by
      intro x
      have h := DFunLike.congr_fun hthetaAlg_pow x
      simpa [theta, AlgEquiv.coe_pow] using h
    have htheta_ne_one : theta ≠ 1 := by
      intro htheta
      have hthetaAlg_one : thetaAlg = 1 := by
        apply AlgEquiv.ext
        intro a
        exact DFunLike.congr_fun htheta a
      have hsigma_eq : sigma ^ (j : ℕ) = sigma ^ (i : ℕ) := by
        have h : sigma ^ (j : ℕ) * (sigma ^ (i : ℕ))⁻¹ = 1 := by
          change sigma ^ (j : ℕ) * (sigma ^ (i : ℕ)).symm = 1
          simpa only [thetaAlg, rho] using hthetaAlg_one
        exact mul_inv_eq_one.mp h
      have hmod : Nat.ModEq n (j : ℕ) (i : ℕ) := by
        have h := pow_eq_pow_iff_modEq.mp hsigma_eq
        simpa [hsigma_order] using h
      exact hij_ne (Fin.ext (hmod.eq_of_lt_of_lt j.isLt i.isLt).symm)
    have htheta_nontrivial :
        ∃ a : BinaryGaloisField n, theta a ≠ a := by
      by_contra h
      push Not at h
      apply htheta_ne_one
      ext a
      simpa using h a
    have hlambdaFinal_field_order : orderOf lambdaFinal = 2 ^ n - 1 := by
      calc
        orderOf lambdaFinal = orderOf (rho lambdaFinal) :=
          (orderOf_injective rho.toAlgHom.toMonoidHom rho.injective
            lambdaFinal).symm
        _ = orderOf lambda := by simp [lambdaFinal]
        _ = 2 ^ n - 1 := hlambda_field_order
    let lambdaFinalUnit : (BinaryGaloisField n)ˣ :=
      Units.mk0 lambdaFinal hlambdaFinal
    have hlambdaFinalUnit_order :
        orderOf lambdaFinalUnit = 2 ^ n - 1 := by
      calc
        orderOf lambdaFinalUnit = orderOf lambdaFinal := by
          simpa [lambdaFinalUnit] using
            (orderOf_units (G := BinaryGaloisField n)
              (y := lambdaFinalUnit)).symm
        _ = 2 ^ n - 1 := hlambdaFinal_field_order
    have hlambdaFinal_generator :
        ∀ x : (BinaryGaloisField n)ˣ,
          x ∈ Subgroup.zpowers lambdaFinalUnit := by
      have htop : Subgroup.zpowers lambdaFinalUnit = ⊤ := by
        rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers,
          hlambdaFinalUnit_order, hlambda_units_card]
      intro x
      rw [htop]
      trivial
    let eX : X ≃* (BinaryGaloisField n)ˣ :=
      mulEquivOfOrderOfEq hactor_generator hlambdaFinal_generator
        (hactor_order.trans hlambdaFinalUnit_order.symm)
    have heX_actor : eX actor = lambdaFinalUnit := by
      exact mulEquivOfOrderOfEq_apply_gen _ _ _
    have hsquare_normal_form_typeA : IsSuzukiTwoTypeAWithActor X P := by
      let factorZeroQuotient : P →* LowerCentralFactor P 0 :=
        (QuotientGroup.mk' (lowerCentralFactorKernel P 0)).comp
          Subgroup.topEquiv.symm.toMonoidHom
      let factorZeroCoordinates : LowerCentralFactor P 0 ≃*
          Multiplicative (BinaryGaloisField n) :=
        (MulEquiv.multiplicativeAdditive _).symm.trans
          quotientCoordinates.symm.toAddEquiv.toMultiplicative
      let pi : P →* Multiplicative (BinaryGaloisField n) :=
        factorZeroCoordinates.toMonoidHom.comp factorZeroQuotient
      have hfactorZeroQuotient_surj : Function.Surjective factorZeroQuotient := by
        intro v
        obtain ⟨x, hx⟩ :=
          QuotientGroup.mk'_surjective (lowerCentralFactorKernel P 0) v
        refine ⟨Subgroup.topEquiv x, ?_⟩
        change QuotientGroup.mk' (lowerCentralFactorKernel P 0)
            (Subgroup.topEquiv.symm (Subgroup.topEquiv x)) = v
        rw [MulEquiv.symm_apply_apply]
        exact hx
      have hpi_surj : Function.Surjective pi :=
        factorZeroCoordinates.surjective.comp hfactorZeroQuotient_surj
      have hfactorZero_actor (p : P) :
          Additive.ofMul (factorZeroQuotient (actor • p)) =
            lowerCentralFactorLinearAut xi 0
              (Additive.ofMul (factorZeroQuotient p)) := by
        change Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel P 0)
              (Subgroup.topEquiv.symm (actor • p))) =
          lowerCentralFactorLinearAut xi 0
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel P 0)
                (Subgroup.topEquiv.symm p)))
        rw [lowerCentralFactorLinearAut_ofMul_mk]
        apply Additive.toMul.injective
        apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel P 0))
        apply Subtype.ext
        change actor • p = xi p
        rw [hxi_actor]
        rfl
      have hpi_actor (p : P) :
          (pi (actor • p)).toAdd =
            lambdaFinal * (pi p).toAdd := by
        change quotientCoordinates.symm
            (Additive.ofMul (factorZeroQuotient (actor • p))) =
          lambdaFinal * quotientCoordinates.symm
            (Additive.ofMul (factorZeroQuotient p))
        rw [hfactorZero_actor]
        let a := quotientCoordinates.symm
          (Additive.ofMul (factorZeroQuotient p))
        have ha : Additive.ofMul (factorZeroQuotient p) =
            quotientCoordinates a := by
          exact (quotientCoordinates.apply_symm_apply _).symm
        rw [ha, hquotientCoordinates_actor]
        calc
          quotientCoordinates.symm
              (quotientCoordinates (lambdaFinal * a)) =
            lambdaFinal * a :=
              quotientCoordinates.symm_apply_apply (lambdaFinal * a)
          _ = lambdaFinal *
              quotientCoordinates.symm (quotientCoordinates a) := by
                rw [quotientCoordinates.symm_apply_apply]
      let factorOneEquiv : LowerCentralFactor P 1 ≃*
          higmanLowerCentralSeries P 1 := by
        exact (QuotientGroup.quotientMulEquivOfEq hkernel1_bot).trans
          (QuotientGroup.quotientBot (G := higmanLowerCentralSeries P 1))
      let centerCoordinatesMul : Multiplicative (BinaryGaloisField n) ≃*
          LowerCentralFactor P 1 :=
        finalCenterCoordinates.toAddEquiv.toMultiplicative.trans
          (MulEquiv.multiplicativeAdditive _)
      let iota : Multiplicative (BinaryGaloisField n) →* P :=
        (higmanLowerCentralSeries P 1).subtype.comp
          (factorOneEquiv.toMonoidHom.comp centerCoordinatesMul.toMonoidHom)
      have hiota : Function.Injective iota := by
        intro z w h
        apply centerCoordinatesMul.injective
        apply factorOneEquiv.injective
        apply Subtype.ext
        exact h
      have hL1_eq_A : higmanLowerCentralSeries P 1 = A := by
        calc
          higmanLowerCentralSeries P 1 = commutator P :=
            Subgroup.top_lowerCentralSeries_one
          _ =
              (commutator (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype := by
                exact hcommutator_map_top
          _ = A := hcommutator_eq_A
      have hiota_range : iota.range = Subgroup.center P := by
        rw [← hA_eq_center, ← hL1_eq_A]
        ext p
        constructor
        · rintro ⟨z, rfl⟩
          exact (factorOneEquiv (centerCoordinatesMul z)).property
        · intro hp
          let p1 : higmanLowerCentralSeries P 1 := ⟨p, hp⟩
          let z : Multiplicative (BinaryGaloisField n) :=
            centerCoordinatesMul.symm (factorOneEquiv.symm p1)
          refine ⟨z, ?_⟩
          change ((factorOneEquiv (centerCoordinatesMul z) :
            higmanLowerCentralSeries P 1) : P) = p
          have hz : centerCoordinatesMul z = factorOneEquiv.symm p1 := by
            simp [z]
          rw [hz]
          exact congrArg Subtype.val (factorOneEquiv.apply_symm_apply p1)
      have hpi_ker : pi.ker = Subgroup.center P := by
        rw [← hA_eq_center]
        ext p
        change pi p = 1 ↔ p ∈ A
        change factorZeroCoordinates (factorZeroQuotient p) = 1 ↔ p ∈ A
        rw [factorZeroCoordinates.map_eq_one_iff]
        change QuotientGroup.mk' (lowerCentralFactorKernel P 0)
            (Subgroup.topEquiv.symm p) = 1 ↔ p ∈ A
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          ← hkernel0_map_A]
        constructor
        · intro hp
          exact ⟨Subgroup.topEquiv.symm p, hp, rfl⟩
        · rintro ⟨z, hz, hzp⟩
          have hz_eq : z = Subgroup.topEquiv.symm p := by
            apply Subtype.ext
            exact hzp
          exact hz_eq ▸ hz
      let eQ : (P ⧸ Subgroup.center P) ≃*
          Multiplicative (BinaryGaloisField n) :=
        (QuotientGroup.quotientMulEquivOfEq hpi_ker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective pi hpi_surj)
      have heQ_mk (p : P) :
          eQ (QuotientGroup.mk' (Subgroup.center P) p) = pi p := by
        change QuotientGroup.kerLift pi
            (QuotientGroup.quotientMulEquivOfEq hpi_ker.symm
              (QuotientGroup.mk' (Subgroup.center P) p)) = pi p
        calc
          QuotientGroup.kerLift pi
              (QuotientGroup.quotientMulEquivOfEq hpi_ker.symm
                (QuotientGroup.mk' (Subgroup.center P) p)) =
            QuotientGroup.kerLift pi
              (QuotientGroup.mk' pi.ker p) := by
                exact congrArg (QuotientGroup.kerLift pi)
                  (QuotientGroup.quotientMulEquivOfEq_mk hpi_ker.symm p)
          _ = pi p := QuotientGroup.kerLift_mk pi p
      have hpi_action : ∀ x : X, ∀ p : P,
          (pi (x • p)).toAdd =
            (eX x : BinaryGaloisField n) * (pi p).toAdd := by
        intro x
        obtain ⟨j, rfl⟩ :=
          mem_powers_iff_mem_zpowers.mpr (hactor_generator x)
        intro p
        induction j generalizing p with
        | zero => simp
        | succ j ih =>
            change (pi ((actor ^ (j + 1)) • p)).toAdd =
              (eX (actor ^ (j + 1)) : BinaryGaloisField n) * (pi p).toAdd
            rw [pow_succ, mul_smul, ih, hpi_actor]
            simp [map_pow, heX_actor, lambdaFinalUnit, mul_assoc]
      have hquotient_action : ∀ x : X, ∀ p : P,
          (eQ (QuotientGroup.mk' (Subgroup.center P) (x • p))).toAdd =
            (eX x : BinaryGaloisField n) *
              (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd := by
        intro x p
        rw [heQ_mk, heQ_mk]
        exact hpi_action x p
      have hfactorOne_mk_outer (y : higmanLowerCentralSeries P 1) :
          factorOneEquiv
            (QuotientGroup.mk' (lowerCentralFactorKernel P 1) y) = y := by
        have hmk :
            (QuotientGroup.quotientMulEquivOfEq hkernel1_bot)
                ((QuotientGroup.mk' (lowerCentralFactorKernel P 1)) y) =
              (QuotientGroup.mk y :
                higmanLowerCentralSeries P 1 ⧸
                  (⊥ : Subgroup (higmanLowerCentralSeries P 1))) := by
          simpa only [QuotientGroup.mk'_apply] using
            (QuotientGroup.quotientMulEquivOfEq_mk hkernel1_bot y)
        calc
          factorOneEquiv
              ((QuotientGroup.mk' (lowerCentralFactorKernel P 1)) y) =
            QuotientGroup.quotientBot
              ((QuotientGroup.quotientMulEquivOfEq hkernel1_bot)
                ((QuotientGroup.mk'
                  (lowerCentralFactorKernel P 1)) y)) := by
                    rfl
          _ = QuotientGroup.quotientBot
              (QuotientGroup.mk y :
                higmanLowerCentralSeries P 1 ⧸
                  (⊥ : Subgroup (higmanLowerCentralSeries P 1))) := by
                    rw [hmk]
          _ = y := by
            change (QuotientGroup.kerLift
              (MonoidHom.id (higmanLowerCentralSeries P 1))) ↑y = y
            rw [QuotientGroup.kerLift_mk]
            rfl
      have hfactorOne_mk_equiv (v : LowerCentralFactor P 1) :
          QuotientGroup.mk' (lowerCentralFactorKernel P 1)
              (factorOneEquiv v) = v := by
        apply factorOneEquiv.injective
        rw [hfactorOne_mk_outer]
      have hcenter_factor_actor (z : BinaryGaloisField n) :
          QuotientGroup.mk' (lowerCentralFactorKernel P 1)
              (lowerCentralSeriesMulAut xi 1
                (factorOneEquiv
                  (centerCoordinatesMul (Multiplicative.ofAdd z)))) =
            centerCoordinatesMul
              (Multiplicative.ofAdd
                (lambdaFinal * theta lambdaFinal * z)) := by
        apply Additive.ofMul.injective
        rw [← lowerCentralFactorLinearAut_ofMul_mk]
        rw [hfactorOne_mk_equiv]
        change lowerCentralFactorLinearAut xi 1
            (finalCenterCoordinates z) =
          finalCenterCoordinates
            (lambdaFinal * theta lambdaFinal * z)
        exact hcenterCoordinates_actor z
      have hiota_actor (z : BinaryGaloisField n) :
          actor • iota (Multiplicative.ofAdd z) =
            iota (Multiplicative.ofAdd
              (lambdaFinal * theta lambdaFinal * z)) := by
        let y : higmanLowerCentralSeries P 1 :=
          factorOneEquiv (centerCoordinatesMul (Multiplicative.ofAdd z))
        have hy_action : actor • (y : P) =
            ((lowerCentralSeriesMulAut xi 1 y :
              higmanLowerCentralSeries P 1) : P) := by
          change actor • (y : P) = xi (y : P)
          rw [hxi_actor]
          rfl
        change actor • (y : P) =
          ((factorOneEquiv
            (centerCoordinatesMul
              (Multiplicative.ofAdd
                (lambdaFinal * theta lambdaFinal * z))) :
                  higmanLowerCentralSeries P 1) : P)
        rw [hy_action]
        apply congrArg Subtype.val
        calc
          lowerCentralSeriesMulAut xi 1 y =
              factorOneEquiv
                (QuotientGroup.mk' (lowerCentralFactorKernel P 1)
                  (lowerCentralSeriesMulAut xi 1 y)) :=
            (hfactorOne_mk_outer
              (lowerCentralSeriesMulAut xi 1 y)).symm
          _ = factorOneEquiv
              (centerCoordinatesMul
                (Multiplicative.ofAdd
                  (lambdaFinal * theta lambdaFinal * z))) := by
            rw [hcenter_factor_actor]
      let iotaCenter : Multiplicative (BinaryGaloisField n) →*
          Subgroup.center P :=
        { toFun := fun z =>
            ⟨iota z, by rw [← hiota_range]; exact ⟨z, rfl⟩⟩
          map_one' := by
            apply Subtype.ext
            exact map_one iota
          map_mul' := by
            intro z w
            apply Subtype.ext
            exact map_mul iota z w }
      have hiotaCenter_injective : Function.Injective iotaCenter := by
        intro z w hzw
        apply hiota
        simpa [iotaCenter] using congrArg Subtype.val hzw
      have hiotaCenter_surjective : Function.Surjective iotaCenter := by
        intro z
        have hz : (z : P) ∈ iota.range := by
          rw [hiota_range]
          exact z.property
        rcases hz with ⟨w, hw⟩
        exact ⟨w, Subtype.ext hw⟩
      let eZ : Subgroup.center P ≃*
          Multiplicative (BinaryGaloisField n) :=
        (MulEquiv.ofBijective iotaCenter
          ⟨hiotaCenter_injective, hiotaCenter_surjective⟩).symm
      have hiota_action : ∀ x : X, ∀ z : BinaryGaloisField n,
          x • iota (Multiplicative.ofAdd z) =
            iota (Multiplicative.ofAdd
              ((eX x : BinaryGaloisField n) *
                theta (eX x : BinaryGaloisField n) * z)) := by
        intro x
        obtain ⟨j, rfl⟩ :=
          mem_powers_iff_mem_zpowers.mpr (hactor_generator x)
        intro z
        induction j generalizing z with
        | zero => simp
        | succ j ih =>
            change (actor ^ (j + 1)) • iota (Multiplicative.ofAdd z) =
              iota (Multiplicative.ofAdd
                ((eX (actor ^ (j + 1)) : BinaryGaloisField n) *
                  theta (eX (actor ^ (j + 1)) : BinaryGaloisField n) * z))
            rw [pow_succ, mul_smul, hiota_actor, ih]
            simp [map_pow, map_mul, heX_actor, lambdaFinalUnit]
            apply congrArg iota
            apply congrArg Multiplicative.ofAdd
            ring
      have hcenter_action : ∀ x : X, ∀ z : BinaryGaloisField n,
          x • ((eZ.symm (Multiplicative.ofAdd z) :
              Subgroup.center P) : P) =
            ((eZ.symm (Multiplicative.ofAdd
              ((eX x : BinaryGaloisField n) *
                theta (eX x : BinaryGaloisField n) * z)) :
                  Subgroup.center P) : P) := by
        intro x z
        change x • iota (Multiplicative.ofAdd z) =
          iota (Multiplicative.ofAdd
            ((eX x : BinaryGaloisField n) *
              theta (eX x : BinaryGaloisField n) * z))
        exact hiota_action x z
      have hcenter_card_final :
          Nat.card (Subgroup.center P) = 2 ^ n := by
        calc
          Nat.card (Subgroup.center P) =
              Nat.card (Multiplicative (BinaryGaloisField n)) :=
            Nat.card_congr eZ.toEquiv
          _ = 2 ^ n := by
            change Nat.card (BinaryGaloisField n) = 2 ^ n
            exact GaloisField.card 2 n (by omega)
      have hexact : iota.range = pi.ker := hiota_range.trans hpi_ker.symm
      have hcentral : iota.range ≤ Subgroup.center P := by rw [hiota_range]
      let q : BinaryGaloisField n → BinaryGaloisField n :=
        fun a => a * theta a
      have hsquare_extension (x : P) :
          iota (Multiplicative.ofAdd (q (pi x).toAdd)) = x ^ 2 := by
        let x0 : higmanLowerCentralSeries P 0 := Subgroup.topEquiv.symm x
        have hx2mem : x ^ 2 ∈ higmanLowerCentralSeries P 1 :=
          hP_square (Subgroup.subset_closure ⟨x, rfl⟩)
        have hpi_coordinates :
            quotientCoordinates (pi x).toAdd =
              Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel P 0) x0) := by
          change quotientCoordinates
              (quotientCoordinates.symm
                (Additive.ofMul
                  (QuotientGroup.mk'
                    (lowerCentralFactorKernel P 0) x0))) = _
          exact quotientCoordinates.apply_symm_apply _
        have hcenter_coordinates :
            finalCenterCoordinates (q (pi x).toAdd) =
              Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel P 1)
                  ⟨x ^ 2, hx2mem⟩) := by
          calc
            finalCenterCoordinates (q (pi x).toAdd) =
                finalCenterCoordinates
                  (finalCenterCoordinates.symm
                    (squareMap
                      (quotientCoordinates (pi x).toAdd))) := by
                        rw [hsquare_coordinates]
            _ = squareMap (quotientCoordinates (pi x).toAdd) :=
              finalCenterCoordinates.apply_symm_apply _
            _ = squareMap
                (Additive.ofMul
                  (QuotientGroup.mk'
                    (lowerCentralFactorKernel P 0) x0)) := by
                      rw [hpi_coordinates]
            _ = Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel P 1)
                  ⟨x ^ 2, hx2mem⟩) := hsquare_mk x0 hx2mem
        have hcenter_mul :
            centerCoordinatesMul
                (Multiplicative.ofAdd (q (pi x).toAdd)) =
              QuotientGroup.mk' (lowerCentralFactorKernel P 1)
                ⟨x ^ 2, hx2mem⟩ := by
          change (finalCenterCoordinates (q (pi x).toAdd)).toMul = _
          exact congrArg Additive.toMul hcenter_coordinates
        have hfactorOne_mk (y : higmanLowerCentralSeries P 1) :
            factorOneEquiv
              (QuotientGroup.mk' (lowerCentralFactorKernel P 1) y) = y := by
          have hmk :
              (QuotientGroup.quotientMulEquivOfEq hkernel1_bot)
                  ((QuotientGroup.mk'
                    (lowerCentralFactorKernel P 1)) y) =
                (QuotientGroup.mk y :
                  higmanLowerCentralSeries P 1 ⧸
                    (⊥ : Subgroup (higmanLowerCentralSeries P 1))) := by
            simpa only [QuotientGroup.mk'_apply] using
              (QuotientGroup.quotientMulEquivOfEq_mk hkernel1_bot y)
          calc
            factorOneEquiv
                ((QuotientGroup.mk'
                  (lowerCentralFactorKernel P 1)) y) =
              QuotientGroup.quotientBot
                ((QuotientGroup.quotientMulEquivOfEq hkernel1_bot)
                  ((QuotientGroup.mk'
                    (lowerCentralFactorKernel P 1)) y)) := by
                      rfl
            _ = QuotientGroup.quotientBot
                (QuotientGroup.mk y :
                  higmanLowerCentralSeries P 1 ⧸
                    (⊥ : Subgroup (higmanLowerCentralSeries P 1))) := by
                      rw [hmk]
            _ = y := by
              change (QuotientGroup.kerLift
                (MonoidHom.id (higmanLowerCentralSeries P 1))) ↑y = y
              rw [QuotientGroup.kerLift_mk]
              rfl
        change ((factorOneEquiv
          (centerCoordinatesMul
            (Multiplicative.ofAdd (q (pi x).toAdd))) :
              higmanLowerCentralSeries P 1) : P) = x ^ 2
        rw [hcenter_mul, hfactorOne_mk]
      obtain ⟨pairLift, cocycle, hcocLeft, hcocRight, hcocDiag,
          hpairOne, hpairSurj, hpairInj, hpairMul,
          hpairPi, hpairCenter⟩ :=
        exists_bilinear_coordinates_of_central_extension
          iota pi hiota hpi_surj hexact hcentral q hsquare_extension
      have hpairQuotient (a z : BinaryGaloisField n) :
          (eQ (QuotientGroup.mk' (Subgroup.center P) (pairLift a z))).toAdd = a := by
        rw [heQ_mk, hpairPi]
        rfl
      have hpairCenter' (z : BinaryGaloisField n) :
          pairLift 0 z =
            ((eZ.symm (Multiplicative.ofAdd z) : Subgroup.center P) : P) := by
        change pairLift 0 z = iota (Multiplicative.ofAdd z)
        exact hpairCenter z
      refine ⟨n, by omega, theta, pairLift, cocycle, eX, eQ, eZ,
        ⟨period, hperiod_odd, hperiod_odd.pos, htheta_period⟩,
        htheta_nontrivial, hcocLeft, hcocRight, hcocDiag, ?_, hpairOne,
        hpairSurj, hpairInj, hpairMul, hcenter_card_final,
        hquotient_action, hcenter_action, hpairQuotient, hpairCenter'⟩
      intro a z
      trivial
    exact hsquare_normal_form_typeA
  exact hspectral_typeA

set_option maxHeartbeats 800000 in
/-- Higman Lemma 11: a Suzuki `2`-group of Omega-length two is type A. -/
public theorem lemma11_length_two_typeA
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P)
    (hXcyclic : IsCyclic X) (hXfaithful : FaithfulSMul X P)
    (hXregular : ActionRegularOn X P (involutions P))
    (hLen : OmegaLength X P 2) :
    IsSuzukiTwoTypeA (⊤ : Subgroup P) := by
  rcases lemma11_length_two_typeA_actor_coordinates
      hP hXcyclic hXfaithful hXregular hLen with
    ⟨n, hn, theta, pairLift, cocycle, _eX, _eQ, _eZ,
      hperiod, htheta_nontrivial, hcocLeft, hcocRight, hcocDiag,
      hpairMem, hpairOne, hpairSurj, hpairInj, hpairMul,
      _hcenterCard, _hquotientAction, _hcenterAction,
      _hpairQuotient, _hpairCenter⟩
  exact ⟨n, hn, theta, pairLift, cocycle,
    hperiod, htheta_nontrivial, hcocLeft, hcocRight, hcocDiag,
    hpairMem, hpairOne, (fun x _hx => hpairSurj x), hpairInj, hpairMul⟩
end Higman
end External
end CFSG.BenderSuzuki
