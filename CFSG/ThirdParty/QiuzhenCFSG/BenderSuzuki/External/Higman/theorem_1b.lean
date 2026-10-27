module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_13
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.lemma_2

namespace CFSG
end CFSG
open CFSG

/-!
# Higman's classification theorem for Suzuki 2-groups: extracted branch
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII

universe u
public theorem theorem1b_typeA_data
    {P : Type u} [Group P] (hA : IsSuzukiTwoTypeA (⊤ : Subgroup P)) :
    let q := Nat.card (Subgroup.center P)
    Nat.card P = q ^ 2 ∧
      (∀ z : Subgroup.center P, z ^ 2 = 1) ∧
      ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
  classical
  rcases hA with
    ⟨n, hn, theta, pairLift, cocycle, _hperiod, htheta_nontrivial,
      haddLeft, haddRight, hdiag, hmem, hone, hsurj, hinj, hmul⟩
  let F := BinaryGaloisField n
  have hzeroLeft : ∀ a : F, cocycle 0 a = 0 := by
    intro a
    have h := haddLeft 0 0 a
    simpa only [zero_add, CharTwo.add_self_eq_zero] using h
  have hzeroRight : ∀ a : F, cocycle a 0 = 0 := by
    intro a
    have h := haddRight a 0 0
    simpa only [zero_add, CharTwo.add_self_eq_zero] using h
  let pairFun : F × F → P := fun az => pairLift az.1 az.2
  have hpairBijective : Function.Bijective pairFun := by
    constructor
    · intro az bw hab
      rcases hinj az.1 az.2 bw.1 bw.2 hab with ⟨h1, h2⟩
      exact Prod.ext h1 h2
    · intro x
      rcases hsurj x (Subgroup.mem_top x) with ⟨a, z, hx⟩
      exact ⟨(a, z), hx.symm⟩
  let pairEquiv : F × F ≃ P := Equiv.ofBijective pairFun hpairBijective
  let centerMap : F → Subgroup.center P := fun z =>
    ⟨pairLift 0 z, by
      rw [Subgroup.mem_center_iff]
      intro x
      rcases hsurj x (Subgroup.mem_top x) with ⟨a, w, hx⟩
      rw [hx, hmul, hmul, hzeroLeft, hzeroRight]
      simp [add_comm]⟩
  have hcenterMapInjective : Function.Injective centerMap := by
    intro z w hzw
    have hval := congrArg
      (fun x : Subgroup.center P => (x : P)) hzw
    exact (hinj 0 z 0 w hval).2
  have hcenterMapSurjective : Function.Surjective centerMap := by
    intro x
    rcases hsurj (x : P) (Subgroup.mem_top x) with ⟨a, z, hx⟩
    have hcocycleSymm : ∀ b : F, cocycle a b = cocycle b a := by
      intro b
      have hcomm := Subgroup.mem_center_iff.mp x.property (pairLift b 0)
      have hcommEq :
          pairLift a z * pairLift b 0 =
            pairLift b 0 * pairLift a z := by
        simpa [hx] using hcomm.symm
      rw [hmul, hmul] at hcommEq
      have hcoord := (hinj _ _ _ _ hcommEq).2
      have hcoord' :
          z + 0 + cocycle a b = z + 0 + cocycle b a := by
        calc
          z + 0 + cocycle a b = 0 + z + cocycle b a := hcoord
          _ = z + 0 + cocycle b a := by abel
      exact add_left_cancel hcoord'
    have hpolar : ∀ b : F, a * theta b + b * theta a = 0 := by
      intro b
      calc
        a * theta b + b * theta a =
            (a + b) * theta (a + b) +
              a * theta a + b * theta b := by
                rw [map_add]
                ring_nf
                simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
        _ = cocycle (a + b) (a + b) +
              cocycle a a + cocycle b b := by
                rw [hdiag, hdiag, hdiag]
        _ = (cocycle a a + cocycle a b +
              (cocycle b a + cocycle b b)) +
              cocycle a a + cocycle b b := by
                rw [haddLeft, haddRight, haddRight]
        _ = 0 := by
          rw [hcocycleSymm b]
          calc
            (cocycle a a + cocycle b a +
                (cocycle b a + cocycle b b)) +
                cocycle a a + cocycle b b =
              (cocycle a a + cocycle a a) +
                (cocycle b a + cocycle b a) +
                (cocycle b b + cocycle b b) := by abel
            _ = 0 := by
              simp only [CharTwo.add_self_eq_zero]
    have ha : a = 0 := by
      by_contra ha
      have hthetaFixed : ∀ y : F, theta y = y := by
        intro y
        have hfactor : a * theta a * (theta y + y) = 0 := by
          calc
            a * theta a * (theta y + y) =
                a * theta (a * y) + (a * y) * theta a := by
                  rw [map_mul]
                  ring
            _ = 0 := hpolar (a * y)
        have hsum : theta y + y = 0 :=
          (mul_eq_zero.mp hfactor).resolve_left
            (mul_ne_zero ha ((map_ne_zero theta).mpr ha))
        exact (eq_neg_of_add_eq_zero_left hsum).trans (CharTwo.neg_eq y)
      rcases htheta_nontrivial with ⟨y, hy⟩
      exact hy (hthetaFixed y)
    subst a
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hx.symm
  let centerEquiv : F ≃ Subgroup.center P :=
    Equiv.ofBijective centerMap
      ⟨hcenterMapInjective, hcenterMapSurjective⟩
  have hFcard : Nat.card F = 2 ^ n := by
    simpa [F, BinaryGaloisField] using GaloisField.card 2 n hn
  have hPcard : Nat.card P = (2 ^ n) ^ 2 := by
    calc
      Nat.card P = Nat.card (F × F) :=
        (Nat.card_congr pairEquiv).symm
      _ = Nat.card F * Nat.card F := Nat.card_prod F F
      _ = (2 ^ n) ^ 2 := by rw [hFcard]; ring
  have hcenterCard : Nat.card (Subgroup.center P) = 2 ^ n := by
    calc
      Nat.card (Subgroup.center P) = Nat.card F :=
        (Nat.card_congr centerEquiv).symm
      _ = 2 ^ n := hFcard
  have hcenterExponent :
      ∀ z : Subgroup.center P, z ^ 2 = 1 := by
    intro z
    obtain ⟨c, rfl⟩ := hcenterMapSurjective z
    apply Subtype.ext
    change pairLift 0 c ^ 2 = 1
    rw [pow_two, hmul, hzeroLeft]
    simpa only [CharTwo.add_self_eq_zero, zero_add] using hone
  have hsquareCenter : ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
    intro x
    rcases hsurj x (Subgroup.mem_top x) with ⟨a, z, hx⟩
    have hsquare :
        x ^ 2 = (centerMap (a * theta a) : P) := by
      rw [hx, pow_two, hmul, hdiag]
      simp only [CharTwo.add_self_eq_zero, zero_add]
      rfl
    rw [hsquare]
    exact (centerMap (a * theta a)).property
  dsimp
  rw [hPcard, hcenterCard]
  exact ⟨rfl, hcenterExponent, hsquareCenter⟩
public theorem theorem1b_typeB_data
    {P : Type u} [Group P] (hB : IsSuzukiTwoTypeB (⊤ : Subgroup P)) :
    let q := Nat.card (Subgroup.center P)
    Nat.card P = q ^ 3 ∧
      (∀ z : Subgroup.center P, z ^ 2 = 1) ∧
      ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
  classical
  rcases hB with
    ⟨n, hn, theta, epsilon, tripleLift, cocycle, hepsilon,
      _hperiod, _hanisotropic, haddLeft, haddRight, hdiag,
      hmem, hone, hsurj, hinj, hmul⟩
  let F := BinaryGaloisField n
  have hzeroLeft : ∀ a b : F, cocycle 0 0 a b = 0 := by
    intro a b
    have h := haddLeft 0 0 0 0 a b
    simpa only [zero_add, CharTwo.add_self_eq_zero] using h
  have hzeroRight : ∀ a b : F, cocycle a b 0 0 = 0 := by
    intro a b
    have h := haddRight a b 0 0 0 0
    simpa only [zero_add, CharTwo.add_self_eq_zero] using h
  let tripleFun : F × F × F → P := fun cab =>
    tripleLift cab.1 cab.2.1 cab.2.2
  have htripleBijective : Function.Bijective tripleFun := by
    constructor
    · intro cab dbf hEq
      rcases hinj cab.1 cab.2.1 cab.2.2
          dbf.1 dbf.2.1 dbf.2.2 hEq with ⟨h1, h2, h3⟩
      exact Prod.ext h1 (Prod.ext h2 h3)
    · intro x
      rcases hsurj x (Subgroup.mem_top x) with ⟨c, a, b, hx⟩
      exact ⟨(c, a, b), hx.symm⟩
  let tripleEquiv : F × F × F ≃ P :=
    Equiv.ofBijective tripleFun htripleBijective
  let centerMap : F → Subgroup.center P := fun c =>
    ⟨tripleLift c 0 0, by
      rw [Subgroup.mem_center_iff]
      intro x
      rcases hsurj x (Subgroup.mem_top x) with ⟨d, a, b, hx⟩
      rw [hx, hmul, hmul, hzeroLeft, hzeroRight]
      simp [add_comm]⟩
  have hcenterMapInjective : Function.Injective centerMap := by
    intro c d hEq
    have hval := congrArg
      (fun x : Subgroup.center P => (x : P)) hEq
    exact (hinj c 0 0 d 0 0 hval).1
  have hcenterMapSurjective : Function.Surjective centerMap := by
    intro x
    rcases hsurj (x : P) (Subgroup.mem_top x) with ⟨c, a, b, hx⟩
    have hcocycleSymm :
        ∀ e f : F, cocycle a b e f = cocycle e f a b := by
      intro e f
      have hcomm :=
        Subgroup.mem_center_iff.mp x.property (tripleLift 0 e f)
      have hcommEq :
          tripleLift c a b * tripleLift 0 e f =
            tripleLift 0 e f * tripleLift c a b := by
        simpa [hx] using hcomm.symm
      rw [hmul, hmul] at hcommEq
      have hcoord := (hinj _ _ _ _ _ _ hcommEq).1
      have hcoord' :
          c + 0 + cocycle a b e f =
            c + 0 + cocycle e f a b := by
        calc
          c + 0 + cocycle a b e f =
              0 + c + cocycle e f a b := hcoord
          _ = c + 0 + cocycle e f a b := by abel
      exact add_left_cancel hcoord'
    have hpolar : ∀ e f : F,
        a * theta e + e * theta a +
            epsilon * (a * theta f + e * theta b) +
            b * theta f + f * theta b = 0 := by
      intro e f
      calc
        a * theta e + e * theta a +
              epsilon * (a * theta f + e * theta b) +
              b * theta f + f * theta b =
            ((a + e) * theta (a + e) +
              epsilon * (a + e) * theta (b + f) +
              (b + f) * theta (b + f)) +
              (a * theta a + epsilon * a * theta b + b * theta b) +
              (e * theta e + epsilon * e * theta f + f * theta f) := by
                rw [map_add, map_add]
                ring_nf
                simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
        _ = cocycle (a + e) (b + f) (a + e) (b + f) +
              cocycle a b a b + cocycle e f e f := by
                rw [hdiag, hdiag, hdiag]
        _ = (cocycle a b a b + cocycle a b e f +
              (cocycle e f a b + cocycle e f e f)) +
              cocycle a b a b + cocycle e f e f := by
                rw [haddLeft, haddRight, haddRight]
        _ = 0 := by
          rw [hcocycleSymm e f]
          calc
            (cocycle a b a b + cocycle e f a b +
                (cocycle e f a b + cocycle e f e f)) +
                cocycle a b a b + cocycle e f e f =
              (cocycle a b a b + cocycle a b a b) +
                (cocycle e f a b + cocycle e f a b) +
                (cocycle e f e f + cocycle e f e f) := by abel
            _ = 0 := by
              simp only [CharTwo.add_self_eq_zero]
    have hab : a = 0 ∧ b = 0 := by
      by_cases ha : a = 0
      · subst a
        by_cases hb : b = 0
        · exact ⟨rfl, hb⟩
        · have h := hpolar 1 0
          simp only [map_zero, map_one, zero_mul, one_mul, mul_zero,
            add_zero, zero_add] at h
          exact False.elim
            ((mul_ne_zero hepsilon ((map_ne_zero theta).mpr hb)) h)
      · by_cases hb : b = 0
        · subst b
          have h := hpolar 0 1
          simp only [map_zero, map_one, zero_mul, mul_zero,
            add_zero, zero_add] at h
          have h' : epsilon * a = 0 := by simpa [mul_assoc] using h
          exact False.elim ((mul_ne_zero hepsilon ha) h')
        · have h := hpolar a 0
          simp only [map_zero, mul_zero, add_zero,
            CharTwo.add_self_eq_zero, zero_add] at h
          have h' : epsilon * a * theta b = 0 := by
            simpa [mul_assoc] using h
          exact False.elim
            ((mul_ne_zero (mul_ne_zero hepsilon ha)
              ((map_ne_zero theta).mpr hb)) h')
    rcases hab with ⟨rfl, rfl⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact hx.symm
  let centerEquiv : F ≃ Subgroup.center P :=
    Equiv.ofBijective centerMap
      ⟨hcenterMapInjective, hcenterMapSurjective⟩
  have hFcard : Nat.card F = 2 ^ n := by
    simpa [F, BinaryGaloisField] using GaloisField.card 2 n hn
  have hPcard : Nat.card P = (2 ^ n) ^ 3 := by
    calc
      Nat.card P = Nat.card (F × F × F) :=
        (Nat.card_congr tripleEquiv).symm
      _ = Nat.card F * (Nat.card F * Nat.card F) := by
        rw [Nat.card_prod, Nat.card_prod]
      _ = (2 ^ n) ^ 3 := by rw [hFcard]; ring
  have hcenterCard : Nat.card (Subgroup.center P) = 2 ^ n := by
    calc
      Nat.card (Subgroup.center P) = Nat.card F :=
        (Nat.card_congr centerEquiv).symm
      _ = 2 ^ n := hFcard
  have hcenterExponent :
      ∀ z : Subgroup.center P, z ^ 2 = 1 := by
    intro z
    obtain ⟨c, rfl⟩ := hcenterMapSurjective z
    apply Subtype.ext
    change tripleLift c 0 0 ^ 2 = 1
    rw [pow_two, hmul, hzeroLeft]
    simpa only [CharTwo.add_self_eq_zero, zero_add] using hone
  have hsquareCenter : ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
    intro x
    rcases hsurj x (Subgroup.mem_top x) with ⟨c, a, b, hx⟩
    have hsquare :
        x ^ 2 =
          (centerMap
            (a * theta a + epsilon * a * theta b + b * theta b) : P) := by
      rw [hx, pow_two, hmul, hdiag]
      simp only [CharTwo.add_self_eq_zero, zero_add]
      rfl
    rw [hsquare]
    exact (centerMap
      (a * theta a + epsilon * a * theta b + b * theta b)).property
  dsimp
  rw [hPcard, hcenterCard]
  exact ⟨rfl, hcenterExponent, hsquareCenter⟩
public theorem theorem1b_typeC_data
    {P : Type u} [Group P] (hC : IsSuzukiTwoTypeC (⊤ : Subgroup P)) :
    let q := Nat.card (Subgroup.center P)
    Nat.card P = q ^ 3 ∧
      (∀ z : Subgroup.center P, z ^ 2 = 1) ∧
      ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
  classical
  rcases hC with
    ⟨n, hn, theta, epsilon, tripleLift, hepsilon, _hperiod,
      _hthetaSq, _havoid, hmem, hone, hsurj, hinj, hmul⟩
  let F := BinaryGaloisField n
  let tripleFun : F × F × F → P := fun zab =>
    tripleLift zab.1 zab.2.1 zab.2.2
  have htripleBijective : Function.Bijective tripleFun := by
    constructor
    · intro zab wcd hEq
      rcases hinj zab.1 zab.2.1 zab.2.2
          wcd.1 wcd.2.1 wcd.2.2 hEq with ⟨h1, h2, h3⟩
      exact Prod.ext h1 (Prod.ext h2 h3)
    · intro x
      rcases hsurj x (Subgroup.mem_top x) with ⟨z, a, b, hx⟩
      exact ⟨(z, a, b), hx.symm⟩
  let tripleEquiv : F × F × F ≃ P :=
    Equiv.ofBijective tripleFun htripleBijective
  let centerMap : F → Subgroup.center P := fun z =>
    ⟨tripleLift z 0 0, by
      rw [Subgroup.mem_center_iff]
      intro x
      rcases hsurj x (Subgroup.mem_top x) with ⟨w, c, d, hx⟩
      rw [hx, hmul, hmul]
      simp [add_comm]⟩
  have hcenterMapInjective : Function.Injective centerMap := by
    intro z w hEq
    have hval := congrArg
      (fun x : Subgroup.center P => (x : P)) hEq
    exact (hinj z 0 0 w 0 0 hval).1
  have hcenterMapSurjective : Function.Surjective centerMap := by
    intro x
    rcases hsurj (x : P) (Subgroup.mem_top x) with ⟨z, a, b, hx⟩
    have hcommCoord : ∀ w c d : F,
        z + w + a * theta c +
            epsilon * a ^ (2 ^ (n - 1)) * theta (d ^ 2) + b * d =
          w + z + c * theta a +
            epsilon * c ^ (2 ^ (n - 1)) * theta (b ^ 2) + d * b := by
      intro w c d
      have hcomm :=
        Subgroup.mem_center_iff.mp x.property (tripleLift w c d)
      have hcommEq :
          tripleLift z a b * tripleLift w c d =
            tripleLift w c d * tripleLift z a b := by
        simpa [hx] using hcomm.symm
      rw [hmul, hmul] at hcommEq
      exact (hinj _ _ _ _ _ _ hcommEq).1
    have hpowPos : 0 < 2 ^ (n - 1) := pow_pos (by norm_num) _
    have haTerm : epsilon * a ^ (2 ^ (n - 1)) = 0 := by
      have h := hcommCoord 0 0 1
      simp only [map_zero, map_one, zero_mul, mul_zero, zero_add,
        one_pow, mul_one, add_zero, zero_pow hpowPos.ne'] at h
      have h' :
          z + (epsilon * a ^ (2 ^ (n - 1)) + b) =
            z + (0 + b) := by
        simpa [add_assoc] using h
      exact add_right_cancel (add_left_cancel h')
    have haPow : a ^ (2 ^ (n - 1)) = 0 :=
      (mul_eq_zero.mp haTerm).resolve_left hepsilon
    have ha : a = 0 := eq_zero_of_pow_eq_zero haPow
    subst a
    have hbTerm : epsilon * theta (b ^ 2) = 0 := by
      have h := hcommCoord 0 1 0
      simp only [map_zero, zero_mul, mul_zero, zero_add,
        one_pow, add_zero, zero_pow hpowPos.ne'] at h
      have h' : z + 0 = z + epsilon * theta (b ^ 2) := by
        simpa using h
      exact (add_left_cancel h').symm
    have hthetaB : theta (b ^ 2) = 0 :=
      (mul_eq_zero.mp hbTerm).resolve_left hepsilon
    have hbSq : b ^ 2 = 0 := (map_eq_zero theta).mp hthetaB
    have hb : b = 0 := eq_zero_of_pow_eq_zero hbSq
    subst b
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hx.symm
  let centerEquiv : F ≃ Subgroup.center P :=
    Equiv.ofBijective centerMap
      ⟨hcenterMapInjective, hcenterMapSurjective⟩
  have hFcard : Nat.card F = 2 ^ n := by
    simpa [F, BinaryGaloisField] using GaloisField.card 2 n hn
  have hPcard : Nat.card P = (2 ^ n) ^ 3 := by
    calc
      Nat.card P = Nat.card (F × F × F) :=
        (Nat.card_congr tripleEquiv).symm
      _ = Nat.card F * (Nat.card F * Nat.card F) := by
        rw [Nat.card_prod, Nat.card_prod]
      _ = (2 ^ n) ^ 3 := by rw [hFcard]; ring
  have hcenterCard : Nat.card (Subgroup.center P) = 2 ^ n := by
    calc
      Nat.card (Subgroup.center P) = Nat.card F :=
        (Nat.card_congr centerEquiv).symm
      _ = 2 ^ n := hFcard
  have hcenterExponent :
      ∀ z : Subgroup.center P, z ^ 2 = 1 := by
    intro z
    obtain ⟨c, rfl⟩ := hcenterMapSurjective z
    apply Subtype.ext
    change tripleLift c 0 0 ^ 2 = 1
    have hpowPos : 0 < 2 ^ (n - 1) := pow_pos (by norm_num) _
    rw [pow_two, hmul]
    simpa only [map_zero, zero_mul, mul_zero, zero_pow hpowPos.ne',
      CharTwo.add_self_eq_zero, zero_add] using hone
  have hsquareCenter : ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
    intro x
    rcases hsurj x (Subgroup.mem_top x) with ⟨z, a, b, hx⟩
    let s : F :=
      a * theta a +
        epsilon * a ^ (2 ^ (n - 1)) * theta (b ^ 2) + b * b
    have hsquare : x ^ 2 = (centerMap s : P) := by
      rw [hx, pow_two, hmul]
      simp only [CharTwo.add_self_eq_zero, zero_add]
      rfl
    rw [hsquare]
    exact (centerMap s).property
  dsimp
  rw [hPcard, hcenterCard]
  exact ⟨rfl, hcenterExponent, hsquareCenter⟩
public theorem theorem1b_typeD_data
    {P : Type u} [Group P] (hD : IsSuzukiTwoTypeD (⊤ : Subgroup P)) :
    let q := Nat.card (Subgroup.center P)
    Nat.card P = q ^ 3 ∧
      (∀ z : Subgroup.center P, z ^ 2 = 1) ∧
      ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
  classical
  rcases hD with
    ⟨n, hn, theta, epsilon, tripleLift, hepsilon, hperiod,
      hthetaNontrivial, _havoid, hmem, hone, hsurj, hinj, hmul⟩
  let F := BinaryGaloisField n
  let tripleFun : F × F × F → P := fun zab =>
    tripleLift zab.1 zab.2.1 zab.2.2
  have htripleBijective : Function.Bijective tripleFun := by
    constructor
    · intro zab wcd hEq
      rcases hinj zab.1 zab.2.1 zab.2.2
          wcd.1 wcd.2.1 wcd.2.2 hEq with ⟨h1, h2, h3⟩
      exact Prod.ext h1 (Prod.ext h2 h3)
    · intro x
      rcases hsurj x (Subgroup.mem_top x) with ⟨z, a, b, hx⟩
      exact ⟨(z, a, b), hx.symm⟩
  let tripleEquiv : F × F × F ≃ P :=
    Equiv.ofBijective tripleFun htripleBijective
  let centerMap : F → Subgroup.center P := fun z =>
    ⟨tripleLift z 0 0, by
      rw [Subgroup.mem_center_iff]
      intro x
      rcases hsurj x (Subgroup.mem_top x) with ⟨w, c, d, hx⟩
      rw [hx, hmul, hmul]
      simp [add_comm]⟩
  have hcenterMapInjective : Function.Injective centerMap := by
    intro z w hEq
    have hval := congrArg
      (fun x : Subgroup.center P => (x : P)) hEq
    exact (hinj z 0 0 w 0 0 hval).1
  have hthetaPowFive : theta ^ 5 = 1 := by
    apply DFunLike.ext _ _
    intro x
    change (theta ^ 5) x = x
    exact hperiod x
  have hthetaNeOne : theta ≠ 1 := by
    rintro rfl
    rcases hthetaNontrivial with ⟨x, hx⟩
    exact hx rfl
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hthetaOrder : orderOf theta = 5 :=
    orderOf_eq_prime hthetaPowFive hthetaNeOne
  have hpowNe {i j : ℕ} (hi : i < 5) (hj : j < 5) (hij : i ≠ j) :
      theta ^ i ≠ theta ^ j := by
    intro hEq
    apply hij
    apply pow_injOn_Iio_orderOf (x := theta)
    · simpa [hthetaOrder] using hi
    · simpa [hthetaOrder] using hj
    · exact hEq
  let theta3 : F ≃+* F := theta ^ 3
  have hthetaNeTheta3 : theta ≠ theta3 := by
    simpa [theta3] using
      (hpowNe (i := 1) (j := 3) (by omega) (by omega) (by omega))
  have hthetaNeOne' : theta ≠ 1 := by
    simpa using
      (hpowNe (i := 1) (j := 0) (by omega) (by omega) (by omega))
  letI : Fintype F := Fintype.ofFinite F
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨autBasis, hAutBasis⟩ :=
    lemma2a_fieldAutomorphisms_basis_linearMaps F
  have hcenterMapSurjective : Function.Surjective centerMap := by
    intro x
    rcases hsurj (x : P) (Subgroup.mem_top x) with ⟨z, a, b, hx⟩
    have hcommCoord : ∀ w c d : F,
        z + w + a * theta c +
            epsilon * (theta^[3]) a * theta d + b * (theta^[2]) d =
          w + z + c * theta a +
            epsilon * (theta^[3]) c * theta b + d * (theta^[2]) b := by
      intro w c d
      have hcomm :=
        Subgroup.mem_center_iff.mp x.property (tripleLift w c d)
      have hcommEq :
          tripleLift z a b * tripleLift w c d =
            tripleLift w c d * tripleLift z a b := by
        simpa [hx] using hcomm.symm
      rw [hmul, hmul] at hcommEq
      exact (hinj _ _ _ _ _ _ hcommEq).1
    have hcommLinear (c : F) :
        a * theta c =
          c * theta a + epsilon * theta3 c * theta b := by
      have h := hcommCoord 0 c 0
      simp only [map_zero, mul_zero, zero_add, add_zero] at h
      have h' : z + (a * theta c) =
          z + (c * theta a + epsilon * theta3 c * theta b) := by
        simpa [theta3, Equiv.Perm.iterate_eq_pow,
          add_assoc] using h
      exact add_left_cancel h'
    have hlinearRelation :
        a • autBasis theta +
            (epsilon * theta b) • autBasis theta3 +
              theta a • autBasis (1 : F ≃+* F) = 0 := by
      ext c
      simp only [LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.zero_apply, smul_eq_mul, hAutBasis]
      change a * theta c + epsilon * theta b * theta3 c +
        theta a * c = 0
      rw [hcommLinear c]
      calc
        (c * theta a + epsilon * theta3 c * theta b) +
              epsilon * theta b * theta3 c + theta a * c =
            (c * theta a + theta a * c) +
              (epsilon * theta3 c * theta b +
                epsilon * theta b * theta3 c) := by ring
        _ = 0 := by
          calc
            (c * theta a + theta a * c) +
                  (epsilon * theta3 c * theta b +
                    epsilon * theta b * theta3 c) =
                (c * theta a + c * theta a) +
                  (epsilon * theta3 c * theta b +
                    epsilon * theta3 c * theta b) := by ring
            _ = 0 := by
              rw [CharTwo.add_self_eq_zero,
                CharTwo.add_self_eq_zero, zero_add]
    have haCoord := congrArg (autBasis.coord theta) hlinearRelation
    have ha : a = 0 := by
      simpa [map_add, map_smul, Module.Basis.coord_apply,
        hthetaNeTheta3, hthetaNeOne'] using haCoord
    subst a
    have hbTerm : epsilon * theta b = 0 := by
      have h := hcommLinear 1
      simpa using h.symm
    have hthetaB : theta b = 0 :=
      (mul_eq_zero.mp hbTerm).resolve_left hepsilon
    have hb : b = 0 := (map_eq_zero theta).mp hthetaB
    subst b
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hx.symm
  let centerEquiv : F ≃ Subgroup.center P :=
    Equiv.ofBijective centerMap
      ⟨hcenterMapInjective, hcenterMapSurjective⟩
  have hFcard : Nat.card F = 2 ^ n := by
    simpa [F, BinaryGaloisField] using GaloisField.card 2 n hn
  have hPcard : Nat.card P = (2 ^ n) ^ 3 := by
    calc
      Nat.card P = Nat.card (F × F × F) :=
        (Nat.card_congr tripleEquiv).symm
      _ = Nat.card F * (Nat.card F * Nat.card F) := by
        rw [Nat.card_prod, Nat.card_prod]
      _ = (2 ^ n) ^ 3 := by rw [hFcard]; ring
  have hcenterCard : Nat.card (Subgroup.center P) = 2 ^ n := by
    calc
      Nat.card (Subgroup.center P) = Nat.card F :=
        (Nat.card_congr centerEquiv).symm
      _ = 2 ^ n := hFcard
  have hcenterExponent :
      ∀ z : Subgroup.center P, z ^ 2 = 1 := by
    intro z
    obtain ⟨c, rfl⟩ := hcenterMapSurjective z
    apply Subtype.ext
    change tripleLift c 0 0 ^ 2 = 1
    rw [pow_two, hmul]
    simpa only [map_zero, mul_zero, zero_mul,
      CharTwo.add_self_eq_zero, zero_add] using hone
  have hsquareCenter : ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
    intro x
    rcases hsurj x (Subgroup.mem_top x) with ⟨z, a, b, hx⟩
    let s : F :=
      a * theta a + epsilon * (theta^[3]) a * theta b +
        b * (theta^[2]) b
    have hsquare : x ^ 2 = (centerMap s : P) := by
      rw [hx, pow_two, hmul]
      simp only [CharTwo.add_self_eq_zero, zero_add]
      rfl
    rw [hsquare]
    exact (centerMap s).property
  dsimp
  rw [hPcard, hcenterCard]
  exact ⟨rfl, hcenterExponent, hsquareCenter⟩
public theorem theorem1b_abcdAlternatives
    {P : Type u} [Group P] (hP : IsSuzukiTwoGroup P) :
    IsSuzukiTwoTypeA (⊤ : Subgroup P) ∨
      IsSuzukiTwoTypeB (⊤ : Subgroup P) ∨
      IsSuzukiTwoTypeC (⊤ : Subgroup P) ∨
      IsSuzukiTwoTypeD (⊤ : Subgroup P) := by
  rcases hP.2.2.2 with
    ⟨X, hXGroup, hXAction, hXcyclic, hXfaithful, hXregular⟩
  letI : Group X := hXGroup
  letI : MulDistribMulAction X P := hXAction
  have hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x := by
    intro x hx y hy
    rcases hXregular.2 x hx y hy with ⟨k, hk, _huniq⟩
    exact ⟨k, hk⟩
  have hXprimeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card X →
      p ∣ Nat.card {x : P // x ∈ involutions P} := by
    obtain ⟨x0, _y0, hx0, _hy0, _hxy0⟩ := hP.2.2.1
    let orbit : X → {x : P // x ∈ involutions P} :=
      fun k => ⟨k • x0, hXregular.1 x0 hx0 k⟩
    have horbit_injective : Function.Injective orbit := by
      intro k l hkl
      have heq : k • x0 = l • x0 := congrArg Subtype.val hkl
      rcases hXregular.2 x0 hx0 (k • x0)
          (hXregular.1 x0 hx0 k) with ⟨a, _ha, huniq⟩
      exact (huniq k rfl).trans (huniq l heq).symm
    have horbit_surjective : Function.Surjective orbit := by
      rintro ⟨y, hy⟩
      rcases hXregular.2 x0 hx0 y hy with ⟨k, hk, _huniq⟩
      exact ⟨k, Subtype.ext hk.symm⟩
    have hcard : Nat.card X =
        Nat.card {x : P // x ∈ involutions P} :=
      Nat.card_congr (Equiv.ofBijective orbit
        ⟨horbit_injective, horbit_surjective⟩)
    intro p _hp hpdiv
    rw [← hcard]
    exact hpdiv
  rcases omegaLength_trichotomy_of_exists_omegaLength
      (X := X) (P := P) hP
      (exists_omegaLength_of_isSuzukiTwoGroup (X := X) (P := P) hP) with
    h2 | h3 | hlong
  · exact Or.inl
      (lemma11_length_two_typeA hP hXcyclic hXfaithful hXregular h2)
  · rcases lemma12_length_three_typeBCD hP hXcyclic hXfaithful hXtrans
      hXprimeSupport h3 with hB | hC | hD
    · exact Or.inr <| Or.inl hB
    · exact Or.inr <| Or.inr <| Or.inl hC
    · exact Or.inr <| Or.inr <| Or.inr hD
  · exact False.elim ((lemma13_no_length_greater_than_three
      hP hXcyclic hXfaithful hXregular hXtrans hXprimeSupport) hlong)
/-- Theorem 1(b), in the form quoted in Peterfalvi Appendix III. -/
public theorem theorem1_center_quotient_orders_and_exponent
    {P : Type u} [Group P] (hP : IsSuzukiTwoGroup P) :
    let q := Nat.card (Subgroup.center P)
    IsMulCommutative (P ⧸ Subgroup.center P) ∧
    (∀ x : P ⧸ Subgroup.center P, x ^ 2 = 1) ∧
    (Nat.card (P ⧸ Subgroup.center P) = q ∨
      Nat.card (P ⧸ Subgroup.center P) = q ^ 2) ∧
    (Nat.card P = q ^ 2 ∨ Nat.card P = q ^ 3) ∧
    ∀ x : P, x ^ 4 = 1 := by
  let q := Nat.card (Subgroup.center P)
  change IsMulCommutative (P ⧸ Subgroup.center P) ∧
    (∀ x : P ⧸ Subgroup.center P, x ^ 2 = 1) ∧
    (Nat.card (P ⧸ Subgroup.center P) = q ∨
      Nat.card (P ⧸ Subgroup.center P) = q ^ 2) ∧
    (Nat.card P = q ^ 2 ∨ Nat.card P = q ^ 3) ∧
    ∀ x : P, x ^ 4 = 1
  classical
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  have hcoordinateData :
      (Nat.card P = q ^ 2 ∨ Nat.card P = q ^ 3) ∧
        (∀ z : Subgroup.center P, z ^ 2 = 1) ∧
        ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
    rcases theorem1b_abcdAlternatives hP with hA | hB | hC | hD
    · rcases theorem1b_typeA_data hA with ⟨hcard, hcenter, hsquare⟩
      exact ⟨Or.inl hcard, hcenter, hsquare⟩
    · rcases theorem1b_typeB_data hB with ⟨hcard, hcenter, hsquare⟩
      exact ⟨Or.inr hcard, hcenter, hsquare⟩
    · rcases theorem1b_typeC_data hC with ⟨hcard, hcenter, hsquare⟩
      exact ⟨Or.inr hcard, hcenter, hsquare⟩
    · rcases theorem1b_typeD_data hD with ⟨hcard, hcenter, hsquare⟩
      exact ⟨Or.inr hcard, hcenter, hsquare⟩
  have hcenter_exponent_two :
      ∀ z : Subgroup.center P, z ^ 2 = 1 :=
    hcoordinateData.2.1
  have hsquare_center :
      ∀ x : P, x ^ 2 ∈ Subgroup.center P :=
    hcoordinateData.2.2
  have hquotient_exponent_two :
      ∀ x : P ⧸ Subgroup.center P, x ^ 2 = 1 := by
    intro x
    obtain ⟨p, rfl⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center P) x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (p ^ 2)).2 (hsquare_center p)
  have hquotient_commutative :
      IsMulCommutative (P ⧸ Subgroup.center P) := by
    refine IsMulCommutative.mk <| Std.Commutative.mk ?_
    intro a b
    have hinv : ∀ x : P ⧸ Subgroup.center P, x⁻¹ = x := by
      intro x
      apply inv_eq_of_mul_eq_one_right
      simpa [pow_two] using hquotient_exponent_two x
    calc
      a * b = (a * b)⁻¹ := (hinv (a * b)).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv b, hinv a]
  have hgroup_card_cases :
      Nat.card P = q ^ 2 ∨ Nat.card P = q ^ 3 :=
    hcoordinateData.1
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Nat.card_pos
  have hcard_formula :
      Nat.card P =
        Nat.card (P ⧸ Subgroup.center P) * q := by
    simpa [q] using
      Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center P)
  have hquotient_card_cases :
      Nat.card (P ⧸ Subgroup.center P) = q ∨
        Nat.card (P ⧸ Subgroup.center P) = q ^ 2 := by
    rcases hgroup_card_cases with hsquare | hcube
    · left
      apply Nat.mul_right_cancel hq_pos
      calc
        Nat.card (P ⧸ Subgroup.center P) * q =
            Nat.card P := hcard_formula.symm
        _ = q ^ 2 := hsquare
        _ = q * q := by ring
    · right
      apply Nat.mul_right_cancel hq_pos
      calc
        Nat.card (P ⧸ Subgroup.center P) * q =
            Nat.card P := hcard_formula.symm
        _ = q ^ 3 := hcube
        _ = q ^ 2 * q := by ring
  have hgroup_exponent_four :
      ∀ x : P, x ^ 4 = 1 := by
    intro x
    have hsquareSquare :
        (x ^ 2) ^ 2 = 1 := by
      simpa using congrArg Subtype.val
        (hcenter_exponent_two ⟨x ^ 2, hsquare_center x⟩)
    calc
      x ^ 4 = x ^ (2 * 2) := by norm_num
      _ = (x ^ 2) ^ 2 := pow_mul x 2 2
      _ = 1 := hsquareSquare
  exact ⟨hquotient_commutative, hquotient_exponent_two,
    hquotient_card_cases, hgroup_card_cases, hgroup_exponent_four⟩

private theorem theorem1b_primeSupport_of_regular
    {K P : Type u} [Group K] [Group P] [MulDistribMulAction K P]
    (hP : IsSuzukiTwoGroup P)
    (hKregular : ActionRegularOn K P (involutions P)) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card K →
      p ∣ Nat.card {x : P // x ∈ involutions P} := by
  obtain ⟨x0, _y0, hx0, _hy0, _hxy0⟩ := hP.2.2.1
  let orbit : K → {x : P // x ∈ involutions P} :=
    fun k => ⟨k • x0, hKregular.1 x0 hx0 k⟩
  have horbit_injective : Function.Injective orbit := by
    intro k l hkl
    have heq : k • x0 = l • x0 := congrArg Subtype.val hkl
    rcases hKregular.2 x0 hx0 (k • x0)
        (hKregular.1 x0 hx0 k) with ⟨a, _ha, huniq⟩
    exact (huniq k rfl).trans (huniq l heq).symm
  have horbit_surjective : Function.Surjective orbit := by
    rintro ⟨y, hy⟩
    rcases hKregular.2 x0 hx0 y hy with ⟨k, hk, _huniq⟩
    exact ⟨k, Subtype.ext hk.symm⟩
  have hcard : Nat.card K =
      Nat.card {x : P // x ∈ involutions P} :=
    Nat.card_congr (Equiv.ofBijective orbit
      ⟨horbit_injective, horbit_surjective⟩)
  intro p _hp hpdiv
  rw [← hcard]
  exact hpdiv

public theorem omegaLength_two_of_card_center_sq
    {K P : Type u} [Group K] [Group P] [MulDistribMulAction K P]
    (hP : IsSuzukiTwoGroup P)
    (hKcyclic : IsCyclic K) (hKfaithful : FaithfulSMul K P)
    (hKregular : ActionRegularOn K P (involutions P))
    (hcard : Nat.card P = Nat.card (Subgroup.center P) ^ 2) :
    OmegaLength K P 2 := by
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hP.2.2.1 with ⟨x, y, _hx, _hy, hxy⟩
  letI : Nontrivial P := ⟨⟨x, y, hxy⟩⟩
  have hcenter_ne : Subgroup.center P ≠ ⊥ :=
    ne_of_gt (isPGroup_of_isSuzukiTwoGroup hP).bot_lt_center
  have hq_gt : 1 < Nat.card (Subgroup.center P) :=
    (Subgroup.one_lt_card_iff_ne_bot (Subgroup.center P)).2 hcenter_ne
  have hKtrans : ∀ a : P, a ∈ involutions P →
      ∀ b : P, b ∈ involutions P → ∃ k : K, b = k • a := by
    intro a ha b hb
    rcases hKregular.2 a ha b hb with ⟨k, hk, _huniq⟩
    exact ⟨k, hk⟩
  have hKprimeSupport :=
    theorem1b_primeSupport_of_regular hP hKregular
  rcases omegaLength_trichotomy_of_exists_omegaLength
      (X := K) (P := P) hP
      (exists_omegaLength_of_isSuzukiTwoGroup (X := K) (P := P) hP) with
    h2 | h3 | hlong
  · exact h2
  · have hcube :
        Nat.card P = Nat.card (Subgroup.center P) ^ 3 := by
      rcases lemma12_length_three_typeBCD hP hKcyclic hKfaithful hKtrans
          hKprimeSupport h3 with hB | hC | hD
      · exact (theorem1b_typeB_data hB).1
      · exact (theorem1b_typeC_data hC).1
      · exact (theorem1b_typeD_data hD).1
    have heq :
        Nat.card (Subgroup.center P) ^ 2 =
          Nat.card (Subgroup.center P) ^ 3 :=
      hcard.symm.trans hcube
    nlinarith
  · exact False.elim ((lemma13_no_length_greater_than_three
      hP hKcyclic hKfaithful hKregular hKtrans hKprimeSupport) hlong)

public theorem omegaLength_three_of_card_center_cube
    {K P : Type u} [Group K] [Group P] [MulDistribMulAction K P]
    (hP : IsSuzukiTwoGroup P)
    (hKcyclic : IsCyclic K) (hKfaithful : FaithfulSMul K P)
    (hKregular : ActionRegularOn K P (involutions P))
    (hcard : Nat.card P = Nat.card (Subgroup.center P) ^ 3) :
    OmegaLength K P 3 := by
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hP.2.2.1 with ⟨x, y, _hx, _hy, hxy⟩
  letI : Nontrivial P := ⟨⟨x, y, hxy⟩⟩
  have hcenter_ne : Subgroup.center P ≠ ⊥ :=
    ne_of_gt (isPGroup_of_isSuzukiTwoGroup hP).bot_lt_center
  have hq_gt : 1 < Nat.card (Subgroup.center P) :=
    (Subgroup.one_lt_card_iff_ne_bot (Subgroup.center P)).2 hcenter_ne
  have hKtrans : ∀ a : P, a ∈ involutions P →
      ∀ b : P, b ∈ involutions P → ∃ k : K, b = k • a := by
    intro a ha b hb
    rcases hKregular.2 a ha b hb with ⟨k, hk, _huniq⟩
    exact ⟨k, hk⟩
  have hKprimeSupport :=
    theorem1b_primeSupport_of_regular hP hKregular
  rcases omegaLength_trichotomy_of_exists_omegaLength
      (X := K) (P := P) hP
      (exists_omegaLength_of_isSuzukiTwoGroup (X := K) (P := P) hP) with
    h2 | h3 | hlong
  · have hA :=
      lemma11_length_two_typeA hP hKcyclic hKfaithful hKregular h2
    have hsquare :
        Nat.card P = Nat.card (Subgroup.center P) ^ 2 :=
      (theorem1b_typeA_data hA).1
    have heq :
        Nat.card (Subgroup.center P) ^ 2 =
          Nat.card (Subgroup.center P) ^ 3 :=
      hsquare.symm.trans hcard
    nlinarith
  · exact h3
  · exact False.elim ((lemma13_no_length_greater_than_three
      hP hKcyclic hKfaithful hKregular hKtrans hKprimeSupport) hlong)
end Higman
end External
end CFSG.BenderSuzuki
