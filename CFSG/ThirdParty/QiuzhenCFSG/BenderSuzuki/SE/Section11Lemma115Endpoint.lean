module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115PartD
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Suzuki
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_6
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.NumberTheory.Multiplicity

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: the recognized centralizer torus endpoint

The cyclic centralizer torus is constructed directly in the Lemma 11.5
configuration.  Its cardinality is bounded by transport to the recognized
PSL or Suzuki model, proving the nontriviality of `B₁` without an additional
source callback.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1 MatrixGroups
open scoped Pointwise

universe u v

/-- In `PSL₂(2^n)`, the centralizer of an element of order three has at
least `2^(n-1)` elements.

The II.8 partition puts the element in a conjugate of the split or nonsplit
cyclic torus; the Sylow-two branch is impossible.  Those tori have orders
`2^n-1` and `2^n+1`, respectively. -/
public theorem lemma115_psl2_centralizer_torus_lower_bound
    (n : ℕ) (hn : 1 ≤ n)
    (x : MatrixGroups.PSL2BinaryMatrixGroup n)
    (hxorder : orderOf x = 3) :
    2 ^ (n - 1) ≤ Nat.card
      (Subgroup.centralizer
        ({x} : Set (MatrixGroups.PSL2BinaryMatrixGroup n))) := by
  let K := BinaryGaloisField n
  have hKcard : Nat.card K = 2 ^ n := by
    simpa [K, BinaryGaloisField] using
      GaloisField.card 2 n (by omega : n ≠ 0)
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, S, hUc, hUcard, hSc, hScard, hpart⟩ :=
    External.huppert_II_8_5_a_psl2_partition
      (F := K) (p := 2) (f := n) hKcard
      (default : Sylow 2 (PSL2MatrixGroup K))
  have hxne : x ≠ 1 := by
    intro hx
    rw [hx, orderOf_one] at hxorder
    norm_num at hxorder
  obtain ⟨T, hxT, _hTuniq⟩ := hpart x hxne
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hqEven : Even (Nat.card K) := by
    rw [hKcard]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hqSubOneOdd : Odd (Nat.card K - 1) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have hparity :=
      (Nat.even_sub (by omega : 1 ≤ Nat.card K)).mp heven
    exact Nat.not_even_one (hparity.mp hqEven)
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp hqSubOneOdd.coprime_two_right
  have hlowerQ : 2 ^ (n - 1) ≤ Nat.card K - 1 := by
    rw [hKcard]
    have hnEq : n = (n - 1) + 1 := by omega
    have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
      calc
        2 ^ n = 2 ^ ((n - 1) + 1) :=
          congrArg (fun k : ℕ => 2 ^ k) hnEq
        _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
    have hpos : 0 < 2 ^ (n - 1) := pow_pos (by norm_num) _
    rw [hpow]
    omega
  rcases hxT.2 with hTP | hTU | hTS
  · exfalso
    rcases hTP with ⟨g, rfl⟩
    let T2 : Subgroup (PSL2MatrixGroup K) :=
      ((default : Sylow 2 (PSL2MatrixGroup K)) :
          Subgroup (PSL2MatrixGroup K)).map
        (MulAut.conj g).toMonoidHom
    have hT2 : IsPGroup 2 T2 :=
      (default : Sylow 2 (MatrixGroups.PSL2MatrixGroup K)).isPGroup'.map
        (MulAut.conj g).toMonoidHom
    let xT2 : T2 := ⟨x, hxT.1⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hT2) xT2
    have hj' : orderOf x = 2 ^ j := by
      calc
        orderOf x = orderOf xT2 := Subgroup.orderOf_coe xT2
        _ = 2 ^ j := hj
    rw [hxorder] at hj'
    by_cases hj0 : j = 0
    · simp [hj0] at hj'
    · have heven : Even (3 : ℕ) := by
        rw [hj']
        exact Nat.even_pow.mpr ⟨even_two, hj0⟩
      exact (by decide : ¬ Even 3) heven
  · rcases hTU with ⟨g, rfl⟩
    have hTcyclic : IsCyclic
        (U.map (MulAut.conj g).toMonoidHom) :=
      (MulEquiv.subgroupMap (MulAut.conj g) U).isCyclic.mp hUc
    have hTle : U.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.centralizer
          ({x} : Set (MatrixGroups.PSL2MatrixGroup K)) := by
      letI : IsMulCommutative (U.map (MulAut.conj g).toMonoidHom) :=
        hTcyclic.isMulCommutative
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val ((IsMulCommutative.is_comm
          (M := U.map (MulAut.conj g).toMonoidHom)).comm
          (⟨y, hy⟩ : U.map (MulAut.conj g).toMonoidHom)
          (⟨x, hxT.1⟩ : U.map (MulAut.conj g).toMonoidHom)))
    have hTcard : Nat.card (U.map (MulAut.conj g).toMonoidHom) =
        Nat.card K - 1 := by
      calc
        Nat.card (U.map (MulAut.conj g).toMonoidHom) = Nat.card U :=
          Subgroup.card_map_of_injective (MulAut.conj g).injective
        _ = Nat.card K - 1 := by rw [hUcard, hgcd]; simp
    apply hlowerQ.trans
    rw [← hTcard]
    exact Subgroup.card_le_of_le hTle
  · rcases hTS with ⟨g, rfl⟩
    have hTcyclic : IsCyclic
        (S.map (MulAut.conj g).toMonoidHom) :=
      (MulEquiv.subgroupMap (MulAut.conj g) S).isCyclic.mp hSc
    have hTle : S.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.centralizer
          ({x} : Set (MatrixGroups.PSL2MatrixGroup K)) := by
      letI : IsMulCommutative (S.map (MulAut.conj g).toMonoidHom) :=
        hTcyclic.isMulCommutative
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val ((IsMulCommutative.is_comm
          (M := S.map (MulAut.conj g).toMonoidHom)).comm
          (⟨y, hy⟩ : S.map (MulAut.conj g).toMonoidHom)
          (⟨x, hxT.1⟩ : S.map (MulAut.conj g).toMonoidHom)))
    have hTcard : Nat.card (S.map (MulAut.conj g).toMonoidHom) =
        Nat.card K + 1 := by
      calc
        Nat.card (S.map (MulAut.conj g).toMonoidHom) = Nat.card S :=
          Subgroup.card_map_of_injective (MulAut.conj g).injective
        _ = Nat.card K + 1 := by rw [hScard, hgcd]; simp
    have hqle : Nat.card K - 1 ≤ Nat.card K + 1 := by omega
    apply hlowerQ.trans (hqle.trans ?_)
    rw [← hTcard]
    exact Subgroup.card_le_of_le hTle

/-- Order formula for `PSL₂` over the binary field of degree `n`. -/
public theorem lemma115_psl2Binary_card_formula (n : ℕ) (hn : n ≠ 0) :
    Nat.card (PSL2BinaryMatrixGroup n) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  let K := BinaryGaloisField n
  have hKcard : Nat.card K = 2 ^ n := by
    simpa [K, BinaryGaloisField] using
      (GaloisField.card 2 n hn)
  have hneg : (-1 : K) = 1 := by
    apply (neg_eq_iff_add_eq_zero).2
    have hone_add_one : (1 : K) + 1 = 0 := by
      rw [show (1 : K) + 1 = 2 by norm_num]
      exact CharP.cast_eq_zero K 2
    exact hone_add_one
  have hcenter :=
    External.huppert614_card_center_of_neg_one_eq_one hneg
  have hpsl := External.huppert614_card_psl_mul_center (K := K)
  rw [hcenter, hKcard] at hpsl
  simpa [K] using hpsl

/-- Order formula for a positive-parameter Suzuki matrix group. -/
public theorem lemma115_suzukiMatrixGroup_card_formula
    (m : ℕ) (hm : 0 < m) :
    Nat.card (SuzukiMatrixGroup m) =
      ((2 ^ (2 * m + 1)) ^ 2 + 1) *
        (2 ^ (2 * m + 1)) ^ 2 *
          (2 ^ (2 * m + 1) - 1) := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (m + 1) x
  rcases External.huppert_blackburn_XI_3_3 m hm pi hpi with
    ⟨_, _, _, _, _, _, hcard, _⟩
  exact hcard

private theorem lemma115_emultiplicity_three_two_pow_add_one
    (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    emultiplicity 3 (2 ^ p + 1) = 1 := by
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have h3notp : ¬ 3 ∣ p := by
    intro h3p
    have hp3 : p = 3 :=
      ((Nat.dvd_prime hp).mp h3p |>.resolve_left (by norm_num)).symm
    omega
  have h := Nat.emultiplicity_pow_add_pow Nat.prime_three (by decide : Odd 3)
    (x := 2) (y := 1) (by norm_num) (by norm_num) hpOdd
  simpa using h.trans (by
    rw [Nat.Prime.emultiplicity_self Nat.prime_three,
      emultiplicity_eq_zero.mpr h3notp]
    norm_num)

private theorem lemma115_emultiplicity_five_four_pow_add_one
    (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    emultiplicity 5 (4 ^ p + 1) = 1 := by
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have h5notp : ¬ 5 ∣ p := by
    intro h5p
    have hp5 : p = 5 :=
      ((Nat.dvd_prime hp).mp h5p |>.resolve_left (by norm_num)).symm
    omega
  have h := Nat.emultiplicity_pow_add_pow Nat.prime_five (by decide : Odd 5)
    (x := 4) (y := 1) (by norm_num) (by norm_num) hpOdd
  simpa using h.trans (by
    rw [Nat.Prime.emultiplicity_self Nat.prime_five,
      emultiplicity_eq_zero.mpr h5notp]
    norm_num)

/-- For an odd prime exponent at least seven, the PSL model order has only
one factor of three. -/
public theorem lemma115_psl2_card_not_dvd_nine
    (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ 9 ∣ Nat.card (PSL2BinaryMatrixGroup p) := by
  rw [lemma115_psl2Binary_card_formula p (by omega)]
  let q := 2 ^ p
  have hqpos : 0 < q := by positivity
  have hqone : 1 ≤ q := hqpos
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hqone
    have honeSq : 1 ≤ q ^ 2 := by nlinarith
    apply (Nat.sub_eq_iff_eq_add honeSq).2
    nlinarith
  have hqNot : ¬ 3 ∣ q := by
    intro h
    have h32 : 3 ∣ 2 :=
      Nat.prime_three.dvd_of_dvd_pow (by simpa [q] using h)
    norm_num at h32
  have hplusMult : emultiplicity 3 (q + 1) = 1 := by
    simpa [q] using lemma115_emultiplicity_three_two_pow_add_one p hp hp7
  have hplus : 3 ∣ q + 1 := by
    have hpow : 3 ^ 1 ∣ q + 1 :=
      pow_dvd_iff_le_emultiplicity.mpr (by simp [hplusMult])
    simpa using hpow
  have hminusNot : ¬ 3 ∣ q - 1 := by
    intro hminus
    obtain ⟨k, hk⟩ := hminus
    obtain ⟨l, hl⟩ := hplus
    omega
  have hmult : emultiplicity 3 (q * (q ^ 2 - 1)) = 1 := by
    rw [hfactor, Nat.prime_three.emultiplicity_mul,
      Nat.prime_three.emultiplicity_mul,
      emultiplicity_eq_zero.mpr hqNot,
      emultiplicity_eq_zero.mpr hminusNot, hplusMult]
    norm_num
  intro h9
  have hpow : 3 ^ 2 ∣ q * (q ^ 2 - 1) := by simpa [q] using h9
  have hle := pow_dvd_iff_le_emultiplicity.mp hpow
  rw [hmult] at hle
  norm_num at hle

/-- For an odd prime exponent at least seven, the PSL model order is not
divisible by five. -/
public theorem lemma115_psl2_card_not_dvd_five
    (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ 5 ∣ Nat.card (PSL2BinaryMatrixGroup p) := by
  rw [lemma115_psl2Binary_card_formula p (by omega)]
  let q := 2 ^ p
  have hqSq : q ^ 2 = 4 ^ p := by
    calc
      q ^ 2 = (2 ^ p) ^ 2 := rfl
      _ = 2 ^ (p * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * p) := by rw [Nat.mul_comm]
      _ = (2 ^ 2) ^ p := by rw [pow_mul]
      _ = 4 ^ p := by norm_num
  have hplusMult : emultiplicity 5 (q ^ 2 + 1) = 1 := by
    rw [hqSq]
    exact lemma115_emultiplicity_five_four_pow_add_one p hp hp7
  have hplus : 5 ∣ q ^ 2 + 1 := by
    have hpow : 5 ^ 1 ∣ q ^ 2 + 1 :=
      pow_dvd_iff_le_emultiplicity.mpr (by simp [hplusMult])
    simpa using hpow
  intro hfive
  rcases Nat.prime_five.dvd_mul.mp hfive with hq | hminus
  · have hfiveTwo : 5 ∣ 2 :=
      Nat.prime_five.dvd_of_dvd_pow (by simpa [q] using hq)
    norm_num at hfiveTwo
  · have hfiveTwo : 5 ∣ 2 := by
      change 5 ∣ q ^ 2 - 1 at hminus
      have hdiff : q ^ 2 + 1 - (q ^ 2 - 1) = 2 := by
        have hqpos : 0 < q := by positivity
        omega
      have hdiv := Nat.dvd_sub hplus hminus
      rw [hdiff] at hdiv
      exact hdiv
    norm_num at hfiveTwo

/-- For a prime Suzuki exponent at least seven, the model order has only one
factor of five. -/
public theorem lemma115_suzuki_card_not_dvd_twentyFive
    (m : ℕ) (hm : 0 < m)
    (hp : (2 * m + 1).Prime) (hp7 : 7 ≤ 2 * m + 1) :
    ¬ 25 ∣ Nat.card (SuzukiMatrixGroup m) := by
  rw [lemma115_suzukiMatrixGroup_card_formula m hm]
  let p := 2 * m + 1
  let q := 2 ^ p
  have hqpos : 0 < q := by positivity
  have hqone : 1 ≤ q := hqpos
  have hqSq : q ^ 2 = 4 ^ p := by
    calc
      q ^ 2 = (2 ^ p) ^ 2 := rfl
      _ = 2 ^ (p * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * p) := by rw [Nat.mul_comm]
      _ = (2 ^ 2) ^ p := by rw [pow_mul]
      _ = 4 ^ p := by norm_num
  have hqSqSubFactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hqone
    have honeSq : 1 ≤ q ^ 2 := by nlinarith
    apply (Nat.sub_eq_iff_eq_add honeSq).2
    nlinarith
  have hqSqNot : ¬ 5 ∣ q ^ 2 := by
    intro h
    have h5q : 5 ∣ q := Nat.prime_five.dvd_of_dvd_pow (by simpa using h)
    have h52 : 5 ∣ 2 :=
      Nat.prime_five.dvd_of_dvd_pow (by simpa [q] using h5q)
    norm_num at h52
  have hplusMult : emultiplicity 5 (q ^ 2 + 1) = 1 := by
    rw [hqSq]
    exact lemma115_emultiplicity_five_four_pow_add_one p hp (by simpa [p] using hp7)
  have hplus : 5 ∣ q ^ 2 + 1 := by
    have hpow : 5 ^ 1 ∣ q ^ 2 + 1 :=
      pow_dvd_iff_le_emultiplicity.mpr (by simp [hplusMult])
    simpa using hpow
  have hminusNot : ¬ 5 ∣ q - 1 := by
    intro hminus
    have hminusSq : 5 ∣ q ^ 2 - 1 := by
      rw [hqSqSubFactor]
      exact dvd_mul_of_dvd_left hminus _
    obtain ⟨k, hk⟩ := hminusSq
    obtain ⟨l, hl⟩ := hplus
    omega
  have hmult :
      emultiplicity 5 ((q ^ 2 + 1) * q ^ 2 * (q - 1)) = 1 := by
    rw [Nat.prime_five.emultiplicity_mul,
      Nat.prime_five.emultiplicity_mul, hplusMult,
      emultiplicity_eq_zero.mpr hqSqNot,
      emultiplicity_eq_zero.mpr hminusNot]
    norm_num
  intro h25
  have hpow : 5 ^ 2 ∣ (q ^ 2 + 1) * q ^ 2 * (q - 1) := by
    simpa [q, p] using h25
  have hle := pow_dvd_iff_le_emultiplicity.mp hpow
  rw [hmult] at hle
  norm_num at hle

/-- A prime-power subgroup containing an element of order `f` has order
exactly `f` when the ambient group order is not divisible by `f²`. -/
public theorem lemma115_card_eq_prime_of_isPGroup_of_square_not_dvd
    {G : Type u} [Group G] [Finite G]
    (T F : Subgroup G) (a : G) (f : ℕ)
    (hTF : T ≤ F) (haT : a ∈ T) (haorder : orderOf a = f)
    (hf : f.Prime) (hfsq : ¬ f ^ 2 ∣ Nat.card F)
    (hTp : IsPGroup f T) :
    Nat.card T = f := by
  letI : Fact f.Prime := ⟨hf⟩
  obtain ⟨k, hk⟩ := hTp.exists_card_eq
  let aT : T := ⟨a, haT⟩
  have hfT : f ∣ Nat.card T := by
    simpa [aT, haorder] using orderOf_dvd_natCard aT
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := by omega
    rw [hk, hkzero] at hfT
    exact hf.not_dvd_one (by simpa using hfT)
  have hklt : k < 2 := by
    by_contra hk2
    have h2k : 2 ≤ k := by omega
    apply hfsq
    apply (pow_dvd_pow f h2k).trans
    rw [← hk]
    exact Subgroup.card_dvd_of_le hTF
  have hkone : k = 1 := by omega
  simpa [hkone] using hk

private theorem lemma115_zpowers_eq_sylow_of_order_five
    {G : Type u} [Group G] [Finite G]
    (x : G) (hx : orderOf x = 5)
    (S : Sylow 5 G) (hxS : x ∈ (S : Subgroup G))
    (h25 : ¬ 25 ∣ Nat.card G) :
    Subgroup.zpowers x = (S : Subgroup G) := by
  have hzle : Subgroup.zpowers x ≤ (S : Subgroup G) :=
    Subgroup.zpowers_le.mpr hxS
  have hzcard : Nat.card (Subgroup.zpowers x) = 5 := by
    rw [Nat.card_zpowers, hx]
  have hSCard : Nat.card S = 5 := by
    apply lemma115_card_eq_prime_of_isPGroup_of_square_not_dvd
      (S : Subgroup G) (⊤ : Subgroup G) x 5
    · exact le_top
    · exact hxS
    · exact hx
    · exact Nat.prime_five
    · simpa using h25
    · exact S.isPGroup'
  exact Subgroup.eq_of_le_of_card_ge hzle (by rw [hSCard, hzcard])

private def lemma115_infCentralizerSingletonMulEquiv
    {G : Type u} [Group G]
    (F : Subgroup G) (a : G) (haF : a ∈ F) :
    (F ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ≃*
      Subgroup.centralizer ({(⟨a, haF⟩ : F)} : Set F) where
  toFun x := ⟨⟨x, x.property.1⟩, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp x.property.2⟩
  invFun x := ⟨(x : F), ⟨x.1.property, by
    change (x : G) ∈ Subgroup.centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp
        (show (x : F) ∈
          Subgroup.centralizer ({(⟨a, haF⟩ : F)} : Set F) from
            x.property))⟩⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_mul' x y := by ext; rfl

private def lemma115_centralizerSingletonMulEquiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (x : G) :
    Subgroup.centralizer ({x} : Set G) ≃*
      Subgroup.centralizer ({e x} : Set H) where
  toFun y := ⟨e y.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy :=
      congrArg e (Subgroup.mem_centralizer_singleton_iff.mp y.property)
    simpa using hy⟩
  invFun z := ⟨e.symm z.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz :=
      congrArg e.symm (Subgroup.mem_centralizer_singleton_iff.mp z.property)
    simpa using hz⟩
  left_inv y := by ext; simp
  right_inv z := by ext; simp
  map_mul' y z := by ext; simp

private theorem lemma115_centralizer_eq_of_zpowers_eq
    {G : Type u} [Group G] (x y : G)
    (hxy : Subgroup.zpowers x = Subgroup.zpowers y) :
    Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
  apply le_antisymm
  · intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    have hy : y ∈ Subgroup.zpowers x := by
      rw [hxy]
      exact Subgroup.mem_zpowers y
    rcases hy with ⟨n, rfl⟩
    exact (show Commute z x from hz).zpow_right n |>.eq
  · intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    have hx : x ∈ Subgroup.zpowers y := by
      rw [← hxy]
      exact Subgroup.mem_zpowers x
    rcases hx with ⟨n, rfl⟩
    exact (show Commute z y from hz).zpow_right n |>.eq

/-- Every order-five element in the positive-parameter Suzuki model has a
singleton centralizer of cardinality at least `2^(2m)`. -/
public theorem lemma115_suzuki_centralizer_torus_lower_bound
    (m : ℕ) (hm : 0 < m)
    (hp : (2 * m + 1).Prime) (hp7 : 7 ≤ 2 * m + 1)
    (x : SuzukiMatrixGroup m) (hx : orderOf x = 5) :
    2 ^ (2 * m) ≤ Nat.card
      (Subgroup.centralizer ({x} : Set (SuzukiMatrixGroup m))) := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let g0 := lemma115_suzukiStandardElement m
  have h25 : ¬ 25 ∣ Nat.card (SuzukiMatrixGroup m) :=
    lemma115_suzuki_card_not_dvd_twentyFive m hm hp hp7
  have hxP : IsPGroup 5 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (p := 5) (G := Subgroup.zpowers x) (n := 1)
    rw [Nat.card_zpowers, hx, pow_one]
  obtain ⟨Sx, hxSx⟩ := hxP.exists_le_sylow
  have hg0P : IsPGroup 5 (Subgroup.zpowers g0) := by
    apply IsPGroup.of_card (p := 5) (G := Subgroup.zpowers g0) (n := 1)
    rw [Nat.card_zpowers, lemma115_suzuki_standard_order_five, pow_one]
  obtain ⟨S0, hg0S0⟩ := hg0P.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) Sx S0
  let y : SuzukiMatrixGroup m := g * x * g⁻¹
  have hyS0 : y ∈ (S0 : Subgroup (SuzukiMatrixGroup m)) := by
    rw [← hg]
    rw [Sylow.coe_subgroup_smul]
    exact Set.mem_smul_set.mpr
      ⟨x, hxSx (Subgroup.mem_zpowers x), rfl⟩
  have hyorder : orderOf y = 5 := by
    simpa [y, MulAut.conj_apply] using
      ((MulAut.conj g).orderOf_eq x).trans hx
  have hyS0eq : Subgroup.zpowers y =
      (S0 : Subgroup (SuzukiMatrixGroup m)) :=
    lemma115_zpowers_eq_sylow_of_order_five y hyorder S0 hyS0 h25
  have hg0S0eq : Subgroup.zpowers g0 =
      (S0 : Subgroup (SuzukiMatrixGroup m)) :=
    lemma115_zpowers_eq_sylow_of_order_five g0
      (lemma115_suzuki_standard_order_five m)
      S0 (hg0S0 (Subgroup.mem_zpowers g0)) h25
  have hcent : Subgroup.centralizer ({y} : Set (SuzukiMatrixGroup m)) =
      Subgroup.centralizer ({g0} : Set (SuzukiMatrixGroup m)) :=
    lemma115_centralizer_eq_of_zpowers_eq y g0
      (hyS0eq.trans hg0S0eq.symm)
  have hcardConj :
      Nat.card (Subgroup.centralizer ({x} : Set (SuzukiMatrixGroup m))) =
        Nat.card (Subgroup.centralizer ({y} : Set (SuzukiMatrixGroup m))) := by
    simpa [y, MulAut.conj_apply] using Nat.card_congr
      (lemma115_centralizerSingletonMulEquiv (MulAut.conj g) x).toEquiv
  calc
    2 ^ (2 * m) ≤ Nat.card
        (Subgroup.centralizer ({g0} : Set (SuzukiMatrixGroup m))) := by
      simpa [g0] using lemma115_suzuki_standard_centralizer_lower_bound m
    _ = Nat.card
        (Subgroup.centralizer ({y} : Set (SuzukiMatrixGroup m))) := by
      rw [hcent]
    _ = Nat.card
        (Subgroup.centralizer ({x} : Set (SuzukiMatrixGroup m))) :=
      hcardConj.symm

/-- Transport the ambient intersection centralizer to the singleton
centralizer in a recognized model. -/
public theorem lemma115_inf_centralizer_card_eq_model
    {G : Type u} {H : Type v} [Group G] [Group H]
    (F : Subgroup G) (a : G) (haF : a ∈ F) (e : F ≃* H) :
    Nat.card (F ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) =
      Nat.card (Subgroup.centralizer ({e ⟨a, haF⟩} : Set H)) := by
  exact Nat.card_congr
    ((lemma115_infCentralizerSingletonMulEquiv F a haF).trans
      (lemma115_centralizerSingletonMulEquiv e ⟨a, haF⟩)).toEquiv

/-- In the actual Lemma 11.5 configuration, the centralizer torus
`T = F₀ ∩ C_X(tu)` is cyclic and is inverted by `u`.

The key point is that conjugation by `u` is fixed-point-free on `T`: a fixed
element lies in the fixed factor of `C_X(tu)`, hence in `V ∩ F₀`, which is
central in the recognized centerless PSL/Suzuki model.  The resulting
fixed-point-free involution makes `T` commutative and odd.  Every odd Sylow
subgroup of `F₀` is cyclic by the model theorems proved for Lemma 11.4, so
`T` is a cyclic Z-group. -/
public theorem lemma115_centralizer_torus_inversion_cyclic
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t)
    (d83 : Lemma83Data M t)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    (h114 : Lemma114Conclusion d83 d) :
    let A := d.choice.initial.A1
    let F0 := lemma114FZero A
    let a := t * d83.u
    let T := F0 ⊓ Subgroup.centralizer ({a} : Set X)
    IsCyclic T ∧
      Odd (Nat.card T) ∧
      ∀ x : X, x ∈ T → rightConjugateElem x d83.u = x⁻¹ := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  let A : Subgroup X := d.choice.initial.A1
  let P : Subgroup X := d.choice.P
  let F0 : Subgroup X := lemma114FZero A
  let a : X := t * d83.u
  let C : Subgroup X := Subgroup.centralizer ({a} : Set X)
  let T : Subgroup X := F0 ⊓ C
  change IsCyclic T ∧ Odd (Nat.card T) ∧
    ∀ x : X, x ∈ T → rightConjugateElem x d83.u = x⁻¹
  have hAV : A ≤ V := by
    dsimp [A, V]
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hVeq : V = D ⊓ Subgroup.centralizer ({d83.u} : Set X) := by
    simpa [V, D, peterfalviV] using d83.centralizer_eq
  have huCA : d83.u ∈ Subgroup.centralizer (A : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hxA
    have hxV : x ∈ V := hAV hxA
    have hxCu : x ∈ Subgroup.centralizer ({d83.u} : Set X) := by
      rw [hVeq] at hxV
      exact hxV.2
    exact Subgroup.mem_centralizer_singleton_iff.mp hxCu
  have huF0 : d83.u ∈ F0 := by
    exact zpowers_le_centralizerTwoPrimeResidual_of_isInvolution
      A d83.u_involution huCA (Subgroup.mem_zpowers d83.u)
  have haInv : rightConjugateElem a d83.u = a⁻¹ := by
    have huu : d83.u * d83.u = 1 := by
      simpa [pow_two] using d83.u_involution.sq_eq_one
    calc
      rightConjugateElem a d83.u =
          d83.u * (t * d83.u) * d83.u := by
            rw [rightConjugateElem, d83.u_involution.inv_eq_self]
      _ = d83.u * t * (d83.u * d83.u) := by group
      _ = d83.u * t := by rw [huu, mul_one]
      _ = (t * d83.u)⁻¹ := by
        rw [mul_inv_rev, ht.inv_eq_self, d83.u_involution.inv_eq_self]
      _ = a⁻¹ := rfl
  have huNC : d83.u ∈ Subgroup.normalizer (C : Set X) := by
    simpa [C] using
      lemma115_inverter_mem_normalizer_centralizer_singleton
        d83.u_involution haInv
  have huNT : d83.u ∈ Subgroup.normalizer (T : Set X) := by
    apply Subgroup.inf_normalizer_le_normalizer_inf
    exact ⟨F0.le_normalizer huF0, huNC⟩
  have hmodelF0 : IsSimpleBenderGroupAtExponent (Nat.card P) F0 := by
    rcases h114.modelTransport.model with hpsl | hsuz
    · exact IsSimpleBenderGroupAtExponent.isPSL2 hpsl.1
    · rcases hsuz with ⟨m, hm, e0, _eHat, _eCore⟩
      exact IsSimpleBenderGroupAtExponent.isSuzuki
        ⟨m, by simpa [P] using hm, e0⟩
  have hPtwo : 2 ≤ Nat.card P := by
    simpa [P] using d.choice.initial.card_P_prime.two_le
  have hcenterF0 : Subgroup.center F0 = ⊥ := by
    exact center_eq_bot_of_isSimpleGroup_of_not_commutative
      (hmodelF0.isSimple hPtwo)
      ((hmodelF0.toIsSimpleBenderGroup hPtwo).not_commutative)
  have hVF0center : V ⊓ F0 ≤
      (Subgroup.center F0).map F0.subtype := by
    have h := lemma114_V_inf_residual_le_center
      (lemma114_V_inf_centralizer_A1_le_A1 d h102)
    change V ⊓ F0 ≤ (Subgroup.center F0).map F0.subtype at h
    exact h
  let uN : Subgroup.normalizer (T : Set X) := ⟨d83.u, huNT⟩
  let phi : MulAut T := T.normalizerMonoidHom uN
  have hphiInvolutive : Function.Involutive phi := by
    intro x
    apply Subtype.ext
    simp only [phi, uN, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [d83.u_involution.inv_eq_self]
    have huu : d83.u * d83.u = 1 := by
      simpa [pow_two] using d83.u_involution.sq_eq_one
    calc
      d83.u * (d83.u * (x : X) * d83.u) * d83.u =
          (d83.u * d83.u) * (x : X) * (d83.u * d83.u) := by group
      _ = (x : X) := by rw [huu]; simp
  have hphiFixedPointFree : MonoidHom.FixedPointFree phi := by
    intro x hx
    apply Subtype.ext
    have hxconj : d83.u * (x : X) * d83.u⁻¹ = (x : X) := by
      simpa [phi, uN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val hx
    have hxu : Commute (x : X) d83.u := by
      have h := congrArg (fun z : X => z * d83.u) hxconj
      have hux : d83.u * (x : X) = (x : X) * d83.u := by
        simpa [mul_assoc] using h
      exact hux.symm
    have hxa : Commute (x : X) a :=
      Subgroup.mem_centralizer_singleton_iff.mp x.property.2
    have hxt : Commute (x : X) t := by
      have h := hxa.mul_right hxu.inv_right
      have huu : d83.u * d83.u = 1 := by
        simpa [pow_two] using d83.u_involution.sq_eq_one
      simpa [a, d83.u_involution.inv_eq_self, mul_assoc, huu] using h
    have hxVC : (x : X) ∈ peterfalviV C t := by
      exact ⟨x.property.2,
        Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩
    have hxV : (x : X) ∈ V := by
      have hxV' : (x : X) ∈
          peterfalviV (M ⊓ rightConjugate M t) t := by
        rw [← lemma115_peterfalviV_centralizer_tu_eq hM ht d83]
        simpa [C, a] using hxVC
      simpa [V, D] using hxV'
    have hxCenter : (x : X) ∈ (Subgroup.center F0).map F0.subtype :=
      hVF0center ⟨hxV, x.property.1⟩
    rw [hcenterF0] at hxCenter
    simpa using hxCenter
  letI : CommGroup T :=
    hphiFixedPointFree.commGroupOfInvolutive hphiInvolutive
  have hTodd : Odd (Nat.card T) :=
    hphiFixedPointFree.odd_card_of_involutive hphiInvolutive
  have hF0OddSylowCyclic : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 →
      ∀ R : Sylow r F0, IsCyclic R := by
    rcases h114.modelTransport.model with hpsl | hsuz
    · exact lemma114_psl2_oddSylow_isCyclic_of_equiv
        hPtwo hpsl.1.some
    · rcases hsuz with ⟨m, _hm, e0, _eHat, _eCore⟩
      exact lemma114_suzuki_oddSylow_isCyclic_of_equiv e0.some
  have hInv : ∀ x : X, x ∈ T →
      rightConjugateElem x d83.u = x⁻¹ := by
    intro x hxT
    have hx := congrFun
      (hphiFixedPointFree.coe_eq_inv_of_involutive hphiInvolutive)
      (⟨x, hxT⟩ : T)
    simpa [phi, uN, rightConjugateElem,
      d83.u_involution.inv_eq_self,
      Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val hx
  refine ⟨?_, hTodd, hInv⟩
  letI : IsZGroup T :=
    { isZGroup := by
        intro r hr R
        letI : Fact r.Prime := ⟨hr⟩
        by_cases hr2 : r = 2
        · subst r
          have hRodd : Odd (Nat.card R) :=
            Odd.of_dvd_nat hTodd
              (R : Subgroup T).card_subgroup_dvd_card
          have hRcard : Nat.card R = 1 :=
            R.isPGroup'.card_eq_or_dvd.resolve_right
              hRodd.not_two_dvd_nat
          letI : Subsingleton R :=
            (Nat.card_eq_one_iff_unique.mp hRcard).1
          exact isCyclic_of_subsingleton
        · let iTF : T →* F0 := Subgroup.inclusion inf_le_left
          let Rmap : Subgroup F0 := (R : Subgroup T).map iTF
          have hRmapP : IsPGroup r Rmap := R.isPGroup'.map iTF
          obtain ⟨S, hRS⟩ := hRmapP.exists_le_sylow
          letI : IsCyclic S := hF0OddSylowCyclic r hr2 S
          have hRmapCyclic : IsCyclic Rmap :=
            Subgroup.isCyclic_of_le hRS
          letI : IsCyclic Rmap := hRmapCyclic
          let f0 : R →* F0 :=
            iTF.comp (R : Subgroup T).subtype
          let fR : R →* Rmap :=
            f0.codRestrict Rmap (by
              intro x
              exact ⟨(x : T), x.property, by simp [f0]⟩)
          exact isCyclic_of_injective fR (by
            intro x y hxy
            apply Subtype.ext
            apply Subtype.ext
            have hxy' := congrArg (fun z : Rmap => (z : F0)) hxy
            change f0 x = f0 y at hxy'
            exact congrArg (fun z : F0 => (z : X)) hxy') }
  infer_instance

/-- The centralizer torus embeds into the anti-fixed subgroup `B`.  Its
recognized-model cardinal bound rules out an `f`-group torus, so the generic
torus core proves that `B₁` is nontrivial. -/
public theorem lemma115_BOne_ne_bot_of_model_endpoint
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    (h113 : Lemma113Conclusion d)
    (h114 : Lemma114Conclusion d83 d) :
    let C := Subgroup.centralizer ({t * d83.u} : Set X)
    let B := Subgroup.closure (peterfalviKSet C t)
    let f := orderOf (t * d83.u)
    lemma115BOne B f ≠ ⊥ := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  let A : Subgroup X := d.choice.initial.A1
  let P : Subgroup X := d.choice.P
  let F0 : Subgroup X := lemma114FZero A
  let a : X := t * d83.u
  let C : Subgroup X := Subgroup.centralizer ({a} : Set X)
  let T : Subgroup X := F0 ⊓ C
  let B : Subgroup X := Subgroup.closure (peterfalviKSet C t)
  let f : ℕ := orderOf a
  obtain ⟨hTcyclic, _hTodd, hTinv⟩ :=
    lemma115_centralizer_torus_inversion_cyclic
      hM ht d83 d h102 h114
  obtain ⟨_hcomp, _hBsetT, hBsetU, hBcomm, _hBodd, _hBcop⟩ :=
    lemma115_B_normal_complement
      hM ht htM d83 h42 htwo d h102 h114
  have hTleC : T ≤ C := inf_le_right
  have hBsetU' : (B : Set X) = peterfalviKSet C d83.u := by
    simpa [B, C, a] using hBsetU
  have hTleB : T ≤ B := by
    intro x hx
    have hxB : x ∈ (B : Set X) := by
      rw [hBsetU']
      exact ⟨hTleC hx, hTinv x hx⟩
    exact hxB
  have hAV : A ≤ V := by
    dsimp [A, V]
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hVeq : V = D ⊓ Subgroup.centralizer ({d83.u} : Set X) := by
    simpa [V, D, peterfalviV] using d83.centralizer_eq
  have huCA : d83.u ∈ Subgroup.centralizer (A : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hxA
    have hxV : x ∈ V := hAV hxA
    have hxCu : x ∈ Subgroup.centralizer ({d83.u} : Set X) := by
      rw [hVeq] at hxV
      exact hxV.2
    exact Subgroup.mem_centralizer_singleton_iff.mp hxCu
  have htF0 : t ∈ F0 := by
    have h := lemma114_t_mem_residual_A1 ht hAV
    change t ∈ F0 at h
    exact h
  have huF0 : d83.u ∈ F0 := by
    exact zpowers_le_centralizerTwoPrimeResidual_of_isInvolution
      A d83.u_involution huCA (Subgroup.mem_zpowers d83.u)
  have haF0 : a ∈ F0 := F0.mul_mem htF0 huF0
  have haT : a ∈ T := by
    exact ⟨haF0,
      Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl a)⟩
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hPD : d.choice.P ≤ D := d.choice.P_le_V.trans inf_le_left
  have hPodd : Odd (Nat.card d.choice.P) :=
    Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hPD)
  have hpodd : Odd d.choice.p := by
    simpa [d.P_card] using hPodd
  have hp2 : d.choice.p ≠ 2 := by
    intro hp
    rw [hp] at hpodd
    exact (by decide : ¬ Odd 2) hpodd
  have hp7 : 7 ≤ d.choice.p := by
    by_contra h
    have hp3 : d.choice.p ≠ 3 := h113.p_ne_three
    have hp5 : d.choice.p ≠ 5 := h113.p_ne_five
    have hp4 : d.choice.p ≠ 4 := by
      intro hp
      exact (by decide : ¬ Nat.Prime 4)
        (by simpa [hp] using d.choice.p_prime)
    have hp6 : d.choice.p ≠ 6 := by
      intro hp
      exact (by decide : ¬ Nat.Prime 6)
        (by simpa [hp] using d.choice.p_prime)
    have hge : 2 ≤ d.choice.p := d.choice.p_prime.two_le
    exact h (by omega)
  have hPcard : Nat.card P = d.choice.p := by
    simpa [P] using d.P_card
  have hPprime : (Nat.card P).Prime := by
    rw [hPcard]
    exact d.choice.p_prime
  have hP7 : 7 ≤ Nat.card P := by
    simpa [hPcard] using hp7
  have hfsmall : f = 3 ∨ f = 5 := by
    simpa [f, a] using h114.modelTransport.order_tu
  have hfprime : f.Prime := by
    rcases hfsmall with h3 | h5
    · simpa [h3] using Nat.prime_three
    · simpa [h5] using Nat.prime_five
  have hmodelBounds :
      2 ^ (d.choice.p - 1) ≤ Nat.card T ∧
        ¬ f ^ 2 ∣ Nat.card F0 := by
    rcases h114.modelTransport.model with hpsl | hsuz
    · obtain ⟨e⟩ := hpsl.1
      let x : PSL2BinaryMatrixGroup (Nat.card P) := e ⟨a, haF0⟩
      have hxorderF : orderOf x = f := by
        calc
          orderOf x = orderOf (⟨a, haF0⟩ : F0) :=
            MulEquiv.orderOf_eq e ⟨a, haF0⟩
          _ = orderOf a := (Subgroup.orderOf_coe ⟨a, haF0⟩).symm
          _ = f := rfl
      have hf3 : f = 3 := by
        rcases hfsmall with h3 | h5
        · exact h3
        · exfalso
          apply lemma115_psl2_card_not_dvd_five
            (Nat.card P) hPprime hP7
          have hxdiv := orderOf_dvd_natCard x
          simpa [hxorderF, h5] using hxdiv
      have hxorder : orderOf x = 3 := hxorderF.trans hf3
      have hcardT : Nat.card T = Nat.card
          (Subgroup.centralizer
            ({x} : Set (PSL2BinaryMatrixGroup (Nat.card P)))) := by
        simpa [T, C, x] using
          lemma115_inf_centralizer_card_eq_model F0 a haF0 e
      have hcardF0 : Nat.card F0 =
          Nat.card (PSL2BinaryMatrixGroup (Nat.card P)) :=
        Nat.card_congr e.toEquiv
      refine ⟨?_, ?_⟩
      · calc
          2 ^ (d.choice.p - 1) = 2 ^ (Nat.card P - 1) := by
            rw [hPcard]
          _ ≤ Nat.card (Subgroup.centralizer
                ({x} : Set (PSL2BinaryMatrixGroup (Nat.card P)))) :=
            lemma115_psl2_centralizer_torus_lower_bound
              (Nat.card P) hPprime.one_le x hxorder
          _ = Nat.card T := hcardT.symm
      · simpa [hf3, hcardF0] using
          lemma115_psl2_card_not_dvd_nine
            (Nat.card P) hPprime hP7
    · rcases hsuz with ⟨m, hmP, ⟨e⟩, _eHat, _eCore⟩
      have hmP' : Nat.card P = 2 * m + 1 := by
        simpa [P] using hmP
      have hm : 0 < m := by omega
      have hmp : (2 * m + 1).Prime := by
        rw [← hmP']
        exact hPprime
      have hmp7 : 7 ≤ 2 * m + 1 := by
        rw [← hmP']
        exact hP7
      let x : SuzukiMatrixGroup m := e ⟨a, haF0⟩
      have hxorderF : orderOf x = f := by
        calc
          orderOf x = orderOf (⟨a, haF0⟩ : F0) :=
            MulEquiv.orderOf_eq e ⟨a, haF0⟩
          _ = orderOf a := (Subgroup.orderOf_coe ⟨a, haF0⟩).symm
          _ = f := rfl
      have hf5 : f = 5 := by
        rcases hfsmall with h3 | h5
        · exfalso
          apply (External.huppert_blackburn_XI_3_6 m hm).2
          have hxdiv := orderOf_dvd_natCard x
          simpa [hxorderF, h3] using hxdiv
        · exact h5
      have hxorder : orderOf x = 5 := hxorderF.trans hf5
      have hcardT : Nat.card T = Nat.card
          (Subgroup.centralizer ({x} : Set (SuzukiMatrixGroup m))) := by
        simpa [T, C, x] using
          lemma115_inf_centralizer_card_eq_model F0 a haF0 e
      have hcardF0 : Nat.card F0 = Nat.card (SuzukiMatrixGroup m) :=
        Nat.card_congr e.toEquiv
      refine ⟨?_, ?_⟩
      · have hpEq : d.choice.p = 2 * m + 1 :=
          hPcard.symm.trans hmP'
        have hexp : d.choice.p - 1 = 2 * m := by omega
        rw [hexp, hcardT]
        exact lemma115_suzuki_centralizer_torus_lower_bound
          m hm hmp hmp7 x hxorder
      · simpa [hf5, hcardF0] using
          lemma115_suzuki_card_not_dvd_twentyFive m hm hmp hmp7
  have hTnot : ¬ IsPGroup f T := by
    intro hTf
    have hTcard : Nat.card T = f :=
      lemma115_card_eq_prime_of_isPGroup_of_square_not_dvd
        T F0 a f inf_le_left haT rfl hfprime hmodelBounds.2 hTf
    have h64 : 64 ≤ 2 ^ (d.choice.p - 1) := by
      have hexp : 6 ≤ d.choice.p - 1 := by omega
      calc
        64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (d.choice.p - 1) :=
          Nat.pow_le_pow_right (by norm_num) hexp
    have hbig : 64 ≤ Nat.card T := h64.trans hmodelBounds.1
    rw [hTcard] at hbig
    rcases hfsmall with h3 | h5 <;> omega
  exact lemma115_BOne_ne_bot_of_cyclic_subgroup_not_isPGroup
    hfprime hBcomm hTleB hTcyclic hTnot

end CFSG.BenderSuzuki
