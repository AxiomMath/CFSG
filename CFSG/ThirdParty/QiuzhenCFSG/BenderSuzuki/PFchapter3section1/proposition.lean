module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.corollary
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_5
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.proposition_1_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_5
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.Semidirect
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.theorem
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.lemma_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.FixedPointProduct
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter3section1.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter3section1

open PFchapter1section1 PFAppendixIII External.Higman
open PFchapter1section2
open PFchapter1section3
open MatrixGroups
open scoped LinearAlgebra.Projectivization Pointwise

universe u v

/-!
# Peterfalvi, Part II, Chapter III, Section 1 Proposition
-/

private theorem typeA_same_square_quotient_eq
    {G : Type*} [Group G] {U : Subgroup G}
    (hU : IsSuzukiTwoTypeA U) (x y : U) (hxy : x ^ 2 = y ^ 2) :
    QuotientGroup.mk' (Subgroup.center U) x =
      QuotientGroup.mk' (Subgroup.center U) y := by
  classical
  rcases hU with
    ⟨n, _hn, theta, pairLift, cocycle, hperiod, _htheta,
      haddLeft, haddRight, hdiag, hmem, _hone, hsurj, hinj, hmul⟩
  let F := BinaryGaloisField n
  have hnormInjective :
      Function.Injective (fun a : F => a * theta a) := by
    intro a b hab
    change a * theta a = b * theta b at hab
    by_cases ha : a = 0
    · subst a
      have hbProd : b * theta b = 0 := by simpa using hab.symm
      rcases mul_eq_zero.mp hbProd with hb | hthetaB
      · exact hb.symm
      · exact (theta.map_eq_zero_iff.mp hthetaB).symm
    have hb : b ≠ 0 := by
      intro hb
      subst b
      have haProd : a * theta a = 0 := by simpa using hab
      exact (mul_ne_zero ha ((map_ne_zero theta).mpr ha)) haProd
    let c : F := a * b⁻¹
    have hc : c ≠ 0 := mul_ne_zero ha (inv_ne_zero hb)
    have hcNorm : c * theta c = 1 := by
      calc
        c * theta c = (a * theta a) * (b * theta b)⁻¹ := by
          dsimp [c]
          rw [map_mul, map_inv₀]
          simp only [mul_inv_rev, mul_assoc]
          apply congrArg (fun z : F => a * z)
          calc
            b⁻¹ * (theta a * (theta b)⁻¹) =
                theta a * (b⁻¹ * (theta b)⁻¹) := by rw [mul_left_comm]
            _ = theta a * ((theta b)⁻¹ * b⁻¹) := by
              rw [mul_comm b⁻¹ (theta b)⁻¹]
        _ = 1 := by
          rw [hab]
          exact mul_inv_cancel₀ (mul_ne_zero hb ((map_ne_zero theta).mpr hb))
    have hthetaC : theta c = c⁻¹ := by
      calc
        theta c = c⁻¹ * (c * theta c) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
        _ = c⁻¹ := by rw [hcNorm, mul_one]
    have hthetaTwo : theta^[2] c = c := by
      calc
        theta^[2] c = theta (theta c) := by
          simp [Function.iterate_succ_apply']
        _ = theta (c⁻¹) := by rw [hthetaC]
        _ = (theta c)⁻¹ := map_inv₀ theta c
        _ = (c⁻¹)⁻¹ := by rw [hthetaC]
        _ = c := inv_inv c
    have hEvenIter : ∀ j : ℕ, theta^[2 * j] c = c := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          rw [Nat.mul_succ, Function.iterate_add_apply, hthetaTwo, ih]
    rcases hperiod with ⟨period, hperiodOdd, _hperiodPos, hperiodEq⟩
    rcases hperiodOdd with ⟨j, hj⟩
    have hOddIter : theta^[period] c = c⁻¹ := by
      rw [hj]
      calc
        theta^[2 * j + 1] c = theta^[1 + 2 * j] c := by (congr 1; omega)
        _ = theta (theta^[2 * j] c) := by
          rw [Function.iterate_add_apply]
          simp
        _ = theta c := by rw [hEvenIter]
        _ = c⁻¹ := hthetaC
    have hcInv : c = c⁻¹ := (hperiodEq c).symm.trans hOddIter
    have hcSq : c * c = 1 := by
      nth_rw 1 [hcInv]
      exact inv_mul_cancel₀ hc
    have hcOne : c = 1 := by
      rcases mul_self_eq_one_iff.mp hcSq with hcOne | hcNeg
      · exact hcOne
      · simpa only [CharTwo.neg_eq] using hcNeg
    exact (mul_inv_eq_one₀ hb).mp hcOne
  rcases hsurj (x : G) x.property with ⟨a, z, hx⟩
  rcases hsurj (y : G) y.property with ⟨b, w, hy⟩
  have hzeroLeft : ∀ c : F, cocycle 0 c = 0 := by
    intro c
    have h := haddLeft 0 0 c
    simpa only [zero_add, CharTwo.add_self_eq_zero] using h
  have hzeroRight : ∀ c : F, cocycle c 0 = 0 := by
    intro c
    have h := haddRight c 0 0
    simpa only [zero_add, CharTwo.add_self_eq_zero] using h
  have hpairSquare : ∀ c d : F,
      pairLift c d ^ 2 = pairLift 0 (c * theta c) := by
    intro c d
    calc
      pairLift c d ^ 2 =
          pairLift (c + c) (d + d + cocycle c c) := by
        simpa [pow_two] using hmul c d c d
      _ = pairLift 0 (c * theta c) := by
        rw [hdiag, CharTwo.add_self_eq_zero c,
          CharTwo.add_self_eq_zero d, zero_add]
  have hnormEq : a * theta a = b * theta b := by
    have hxyG : ((x : U) : G) ^ 2 = ((y : U) : G) ^ 2 :=
      congrArg (fun u : U => (u : G)) hxy
    have hcoordEq :
        pairLift 0 (a * theta a) = pairLift 0 (b * theta b) := by
      calc
        pairLift 0 (a * theta a) = pairLift a z ^ 2 :=
          (hpairSquare a z).symm
        _ = ((x : U) : G) ^ 2 := by rw [hx]
        _ = ((y : U) : G) ^ 2 := hxyG
        _ = pairLift b w ^ 2 := by rw [hy]
        _ = pairLift 0 (b * theta b) := hpairSquare b w
    exact (hinj 0 (a * theta a) 0 (b * theta b) hcoordEq).2
  have hab : a = b := hnormInjective hnormEq
  let delta : F := w - z
  let cU : U := ⟨pairLift 0 delta, hmem 0 delta⟩
  have hcCenter : cU ∈ Subgroup.center U := by
    rw [Subgroup.mem_center_iff]
    intro q
    rcases hsurj (q : G) q.property with ⟨d, e, hq⟩
    apply Subtype.ext
    change (q : G) * pairLift 0 delta = pairLift 0 delta * (q : G)
    rw [hq, hmul, hmul, hzeroLeft, hzeroRight]
    simp [add_comm]
  have hyEq : y = x * cU := by
    apply Subtype.ext
    change (y : G) = (x : G) * pairLift 0 delta
    rw [hy, hx, hmul, hzeroRight, hab]
    dsimp [delta]
    simp only [add_zero]
    apply congrArg (pairLift b)
    rw [CharTwo.sub_eq_add]
    calc
      w = 0 + w := by simp
      _ = (z + z) + w := by rw [CharTwo.add_self_eq_zero]
      _ = z + (w + z) := by abel
  have hcQuotient : QuotientGroup.mk' (Subgroup.center U) cU = 1 :=
    (QuotientGroup.eq_one_iff cU).mpr hcCenter
  calc
    QuotientGroup.mk' (Subgroup.center U) x =
        QuotientGroup.mk' (Subgroup.center U) x * 1 := by simp
    _ = QuotientGroup.mk' (Subgroup.center U) x *
        QuotientGroup.mk' (Subgroup.center U) cU := by rw [hcQuotient]
    _ = QuotientGroup.mk' (Subgroup.center U) (x * cU) :=
      (map_mul (QuotientGroup.mk' (Subgroup.center U)) x cU).symm
    _ = QuotientGroup.mk' (Subgroup.center U) y :=
      congrArg (QuotientGroup.mk' (Subgroup.center U)) hyEq.symm

private theorem cubic_line_root_card
    {K S : Type u} [Group K] [Group S] [Finite K] [Finite S]
    [MulDistribMulAction K S]
    (hSuzuki : IsSuzukiTwoGroup S)
    (hKregular : ActionRegularOn K S (involutions S))
    (hKcard : Nat.card K = Nat.card (Subgroup.center S) - 1)
    (quotientAction : MulDistribMulAction K (S ⧸ Subgroup.center S))
    (hquotientAction : ∀ k : K, ∀ x : S,
      @SMul.smul K (S ⧸ Subgroup.center S) quotientAction.toSMul k
          (QuotientGroup.mk' (Subgroup.center S) x) =
        QuotientGroup.mk' (Subgroup.center S) (k • x))
    (T : Subgroup (S ⧸ Subgroup.center S))
    (hTinv : @IsXInvariantSubgroup K (S ⧸ Subgroup.center S)
      _ _ quotientAction T)
    (hTcard : Nat.card T = Nat.card (Subgroup.center S))
    (s : S) (hs : IsInvolution s) :
    Nat.card {x : T.comap (QuotientGroup.mk' (Subgroup.center S)) //
      ((x : T.comap (QuotientGroup.mk' (Subgroup.center S))) : S) ^ 2 = s} =
      Nat.card (Subgroup.center S) := by
  classical
  let qmap : S →* S ⧸ Subgroup.center S :=
    QuotientGroup.mk' (Subgroup.center S)
  let Plane : Subgroup S := T.comap qmap
  let q := Nat.card (Subgroup.center S)
  letI : MulDistribMulAction K (S ⧸ Subgroup.center S) := quotientAction
  have hPlaneInv : IsInvariant K S Plane := by
    refine ⟨?_⟩
    intro k x
    change qmap x ∈ T ↔ qmap (k • x) ∈ T
    rw [← hquotientAction k x]
    exact hTinv k (qmap x)
  letI : IsInvariant K S Plane := hPlaneInv
  have hPlaneCard : Nat.card Plane = q ^ 2 := by
    have hcardQuotPlane :
        Nat.card (Plane ⧸ qmap.ker.subgroupOf Plane) = Nat.card T := by
      simpa [Plane, qmap] using
        (card_quotient_subgroupOf_comap_eq
          (f := qmap) (hf := QuotientGroup.mk'_surjective (Subgroup.center S))
          (H := T))
    have hcardKerPlane :
        Nat.card (qmap.ker.subgroupOf Plane) = q := by
      have hkerLe : qmap.ker ≤ Plane := Subgroup.ker_le_comap qmap T
      calc
        Nat.card (qmap.ker.subgroupOf Plane) = Nat.card qmap.ker :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerLe).toEquiv
        _ = q := by simp [qmap, q, QuotientGroup.ker_mk']
    calc
      Nat.card Plane =
          Nat.card (Plane ⧸ qmap.ker.subgroupOf Plane) *
            Nat.card (qmap.ker.subgroupOf Plane) := by
        simpa using
          (Subgroup.card_eq_card_quotient_mul_card_subgroup
            (s := qmap.ker.subgroupOf Plane))
      _ = q * q := by rw [hcardQuotPlane, hcardKerPlane, hTcard]
      _ = q ^ 2 := by ring
  let CenterPlane := {x : Plane // (x : S) ∈ Subgroup.center S}
  have hCenterPlaneCard : Nat.card CenterPlane = q := by
    let centerToPlane : Subgroup.center S ≃ CenterPlane :=
      { toFun := fun z =>
          ⟨⟨(z : S), by
            change qmap (z : S) ∈ T
            have hzOne : qmap (z : S) = 1 :=
              (QuotientGroup.eq_one_iff (z : S)).mpr z.property
            rw [hzOne]
            exact T.one_mem⟩, z.property⟩
        invFun := fun z => ⟨((z : Plane) : S), z.property⟩
        left_inv := by intro z; rfl
        right_inv := by intro z; rfl }
    exact (Nat.card_congr centerToPlane).symm
  let NoncentralPlane := {x : Plane // (x : S) ∉ Subgroup.center S}
  have hNoncentralCard : Nat.card NoncentralPlane = q ^ 2 - q := by
    letI : Fintype Plane := Fintype.ofFinite Plane
    letI : Fintype CenterPlane := Fintype.ofFinite CenterPlane
    letI : Fintype NoncentralPlane := Fintype.ofFinite NoncentralPlane
    have hsplit := Fintype.card_subtype_compl
      (fun x : Plane => (x : S) ∈ Subgroup.center S)
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
      Fintype.card_eq_nat_card, hPlaneCard, hCenterPlaneCard] at hsplit
    omega
  let Root := {x : Plane // (x : S) ^ 2 = s}
  have hRootNoncentral : ∀ r : Root, (r.1 : S) ∉ Subgroup.center S := by
    intro r hrCenter
    have hrPow :=
      (higmanTheorem_involutions_center hSuzuki).2
        (⟨(r.1 : S), hrCenter⟩ : Subgroup.center S)
    apply hs.ne_one
    calc
      s = (r.1 : S) ^ 2 := r.property.symm
      _ = 1 := congrArg
        (fun z : Subgroup.center S => ((z : S))) hrPow
  have hFourth : ∀ x : S, x ^ 4 = 1 :=
    (higmanTheorem_center_quotient_orders_and_exponent hSuzuki).2.2.2.2
  have hSquareInvolution : ∀ x : NoncentralPlane,
      IsInvolution ((x.1 : S) ^ 2) := by
    intro x
    have hsqNe : (x.1 : S) ^ 2 ≠ 1 := by
      intro hsq
      by_cases hxOne : (x.1 : S) = 1
      · exact x.property (hxOne ▸ (Subgroup.center S).one_mem)
      · have hxInv : (x.1 : S) ∈ involutions S := ⟨hxOne, hsq⟩
        rw [(higmanTheorem_involutions_center hSuzuki).1] at hxInv
        exact x.property hxInv.1
    exact ⟨hsqNe, by
      calc
        ((x.1 : S) ^ 2) ^ 2 = (x.1 : S) ^ 4 := by group
        _ = 1 := hFourth (x.1 : S)⟩
  let squareActor (x : NoncentralPlane) : K :=
    Classical.choose (hKregular.2 s hs ((x.1 : S) ^ 2) (hSquareInvolution x))
  have squareActor_spec (x : NoncentralPlane) :
      (x.1 : S) ^ 2 = squareActor x • s :=
    (Classical.choose_spec
      (hKregular.2 s hs ((x.1 : S) ^ 2) (hSquareInvolution x))).1
  have squareActor_unique (x : NoncentralPlane) (k : K)
      (hk : (x.1 : S) ^ 2 = k • s) : k = squareActor x := by
    exact (Classical.choose_spec
      (hKregular.2 s hs ((x.1 : S) ^ 2) (hSquareInvolution x))).2 k hk
  let orbitRoot : K × Root → NoncentralPlane := fun kr =>
    ⟨kr.1 • kr.2.1, by
      intro hcenter
      have hback : kr.1⁻¹ • (kr.1 • (kr.2.1 : S)) ∈ Subgroup.center S :=
        (isXInvariantSubgroup_center K S kr.1⁻¹ (kr.1 • (kr.2.1 : S))).1 hcenter
      have hrCenter : (kr.2.1 : S) ∈ Subgroup.center S := by
        simpa [smul_smul] using hback
      exact hRootNoncentral kr.2 hrCenter⟩
  let unorbitRoot : NoncentralPlane → K × Root := fun x =>
    (squareActor x, ⟨(squareActor x)⁻¹ • x.1, by
      change ((squareActor x)⁻¹ • (x.1 : S)) ^ 2 = s
      rw [← smul_pow', squareActor_spec x]
      simp [smul_smul]⟩)
  have horbitLeft : Function.LeftInverse unorbitRoot orbitRoot := by
    intro kr
    rcases kr with ⟨k, r⟩
    have hsq : ((orbitRoot (k, r)).1 : S) ^ 2 = k • s := by
      change (k • (r.1 : S)) ^ 2 = k • s
      rw [← smul_pow', r.property]
    have hk : squareActor (orbitRoot (k, r)) = k :=
      (squareActor_unique (orbitRoot (k, r)) k hsq).symm
    apply Prod.ext
    · exact hk
    · change (unorbitRoot (orbitRoot (k, r))).2 = r
      apply Subtype.ext
      apply Subtype.ext
      change (squareActor (orbitRoot (k, r)))⁻¹ •
          (k • (r.1 : S)) = (r.1 : S)
      rw [hk]
      simp [smul_smul]
  have horbitRight : Function.RightInverse unorbitRoot orbitRoot := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change squareActor x • (squareActor x)⁻¹ • (x.1 : S) = (x.1 : S)
    simp [smul_smul]
  let orbitEquiv : K × Root ≃ NoncentralPlane :=
    Equiv.mk orbitRoot unorbitRoot horbitLeft horbitRight
  have hcardEq : Nat.card K * Nat.card Root = q ^ 2 - q := by
    calc
      Nat.card K * Nat.card Root = Nat.card (K × Root) :=
        (Nat.card_prod K Root).symm
      _ = Nat.card NoncentralPlane := Nat.card_congr orbitEquiv
      _ = q ^ 2 - q := hNoncentralCard
  have hqTwo : 2 ≤ q := by
    have hsCenter : s ∈ Subgroup.center S := by
      have hsMem : s ∈ involutions S := hs
      rw [(higmanTheorem_involutions_center hSuzuki).1] at hsMem
      exact hsMem.1
    have hsCenterNe : (⟨s, hsCenter⟩ : Subgroup.center S) ≠ 1 := by
      intro h
      exact hs.ne_one (congrArg (fun z : Subgroup.center S => (z : S)) h)
    have hcenterNe : Subgroup.center S ≠ ⊥ := by
      intro hbot
      apply hsCenterNe
      apply Subtype.ext
      have hsBot : s ∈ (⊥ : Subgroup S) := by simpa [hbot] using hsCenter
      simpa using hsBot
    have hcardGt := (Subgroup.center S).one_lt_card_iff_ne_bot.mpr hcenterNe
    have hq1lt : 1 < q := by simpa [q] using hcardGt
    exact Nat.succ_le_of_lt hq1lt
  have hcardRoot : Nat.card Root = q := by
    rw [hKcard] at hcardEq
    have hfactor : q ^ 2 - q = (q - 1) * q := by
      rw [pow_two, Nat.sub_mul]
      simp
    rw [hfactor] at hcardEq
    exact Nat.mul_left_cancel (Nat.sub_pos_of_lt hqTwo) hcardEq
  simpa [Root, Plane, qmap, q] using hcardRoot

private theorem cubic_full_root_card
    {K S : Type u} [Group K] [Group S] [Finite K] [Finite S]
    [MulDistribMulAction K S]
    (hSuzuki : IsSuzukiTwoGroup S)
    (hKregular : ActionRegularOn K S (involutions S))
    (hKcard : Nat.card K = Nat.card (Subgroup.center S) - 1)
    (hSCard : Nat.card S = Nat.card (Subgroup.center S) ^ 3)
    (s : S) (hs : IsInvolution s) :
    Nat.card {x : S // x ^ 2 = s} =
      Nat.card (Subgroup.center S) * (Nat.card (Subgroup.center S) + 1) := by
  classical
  let q := Nat.card (Subgroup.center S)
  let CenterS := {x : S // x ∈ Subgroup.center S}
  let NoncentralS := {x : S // x ∉ Subgroup.center S}
  have hCenterCard : Nat.card CenterS = q := by
    let e : Subgroup.center S ≃ CenterS :=
      { toFun := fun z => ⟨(z : S), z.property⟩
        invFun := fun z => ⟨(z : S), z.property⟩
        left_inv := by intro z; rfl
        right_inv := by intro z; rfl }
    exact (Nat.card_congr e).symm
  have hNoncentralCard : Nat.card NoncentralS = q ^ 3 - q := by
    letI : Fintype S := Fintype.ofFinite S
    letI : Fintype CenterS := Fintype.ofFinite CenterS
    letI : Fintype NoncentralS := Fintype.ofFinite NoncentralS
    have hsplit := Fintype.card_subtype_compl
      (fun x : S => x ∈ Subgroup.center S)
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
      Fintype.card_eq_nat_card, hSCard, hCenterCard] at hsplit
    omega
  let Root := {x : S // x ^ 2 = s}
  have hRootNoncentral : ∀ r : Root, (r.1 : S) ∉ Subgroup.center S := by
    intro r hrCenter
    have hrPow :=
      (higmanTheorem_involutions_center hSuzuki).2
        (⟨(r.1 : S), hrCenter⟩ : Subgroup.center S)
    apply hs.ne_one
    calc
      s = (r.1 : S) ^ 2 := r.property.symm
      _ = 1 := congrArg
        (fun z : Subgroup.center S => (z : S)) hrPow
  have hFourth : ∀ x : S, x ^ 4 = 1 :=
    (higmanTheorem_center_quotient_orders_and_exponent hSuzuki).2.2.2.2
  have hSquareInvolution : ∀ x : NoncentralS, IsInvolution ((x.1 : S) ^ 2) := by
    intro x
    have hsqNe : (x.1 : S) ^ 2 ≠ 1 := by
      intro hsq
      by_cases hxOne : (x.1 : S) = 1
      · exact x.property (hxOne ▸ (Subgroup.center S).one_mem)
      · have hxInv : (x.1 : S) ∈ involutions S := ⟨hxOne, hsq⟩
        rw [(higmanTheorem_involutions_center hSuzuki).1] at hxInv
        exact x.property hxInv.1
    exact ⟨hsqNe, by
      calc
        ((x.1 : S) ^ 2) ^ 2 = (x.1 : S) ^ 4 := by group
        _ = 1 := hFourth (x.1 : S)⟩
  let squareActor (x : NoncentralS) : K :=
    Classical.choose (hKregular.2 s hs ((x.1 : S) ^ 2) (hSquareInvolution x))
  have squareActor_spec (x : NoncentralS) :
      (x.1 : S) ^ 2 = squareActor x • s :=
    (Classical.choose_spec
      (hKregular.2 s hs ((x.1 : S) ^ 2) (hSquareInvolution x))).1
  have squareActor_unique (x : NoncentralS) (k : K)
      (hk : (x.1 : S) ^ 2 = k • s) : k = squareActor x := by
    exact (Classical.choose_spec
      (hKregular.2 s hs ((x.1 : S) ^ 2) (hSquareInvolution x))).2 k hk
  let orbitRoot : K × Root → NoncentralS := fun kr =>
    ⟨kr.1 • kr.2.1, by
      intro hcenter
      have hback : kr.1⁻¹ • (kr.1 • (kr.2.1 : S)) ∈ Subgroup.center S :=
        (isXInvariantSubgroup_center K S kr.1⁻¹ (kr.1 • (kr.2.1 : S))).1 hcenter
      have hrCenter : (kr.2.1 : S) ∈ Subgroup.center S := by
        simpa [smul_smul] using hback
      exact hRootNoncentral kr.2 hrCenter⟩
  let unorbitRoot : NoncentralS → K × Root := fun x =>
    (squareActor x, ⟨(squareActor x)⁻¹ • x.1, by
      rw [← smul_pow', squareActor_spec x]
      simp [smul_smul]⟩)
  have horbitLeft : Function.LeftInverse unorbitRoot orbitRoot := by
    intro kr
    rcases kr with ⟨k, r⟩
    have hsq : ((orbitRoot (k, r)).1 : S) ^ 2 = k • s := by
      change (k • (r.1 : S)) ^ 2 = k • s
      rw [← smul_pow', r.property]
    have hk : squareActor (orbitRoot (k, r)) = k :=
      (squareActor_unique (orbitRoot (k, r)) k hsq).symm
    apply Prod.ext
    · exact hk
    · apply Subtype.ext
      change (squareActor (orbitRoot (k, r)))⁻¹ •
          (k • (r.1 : S)) = (r.1 : S)
      rw [hk]
      simp [smul_smul]
  have horbitRight : Function.RightInverse unorbitRoot orbitRoot := by
    intro x
    apply Subtype.ext
    change squareActor x • (squareActor x)⁻¹ • (x.1 : S) = (x.1 : S)
    simp [smul_smul]
  let orbitEquiv : K × Root ≃ NoncentralS :=
    Equiv.mk orbitRoot unorbitRoot horbitLeft horbitRight
  have hcardEq : Nat.card K * Nat.card Root = q ^ 3 - q := by
    calc
      Nat.card K * Nat.card Root = Nat.card (K × Root) :=
        (Nat.card_prod K Root).symm
      _ = Nat.card NoncentralS := Nat.card_congr orbitEquiv
      _ = q ^ 3 - q := hNoncentralCard
  have hqTwo : 2 ≤ q := by
    have hsCenter : s ∈ Subgroup.center S := by
      have hsMem : s ∈ involutions S := hs
      rw [(higmanTheorem_involutions_center hSuzuki).1] at hsMem
      exact hsMem.1
    have hcenterNe : Subgroup.center S ≠ ⊥ := by
      intro hbot
      have hsBot : s ∈ (⊥ : Subgroup S) := by simpa [hbot] using hsCenter
      exact hs.ne_one (by simpa using hsBot)
    have hq1lt : 1 < q := by
      simpa [q] using (Subgroup.center S).one_lt_card_iff_ne_bot.mpr hcenterNe
    exact Nat.succ_le_of_lt hq1lt
  have hfactor : q ^ 3 - q = (q - 1) * (q * (q + 1)) := by
    calc
      q ^ 3 - q = q * q ^ 2 - q * 1 := by congr 1 <;> ring
      _ = q * (q ^ 2 - 1) := (Nat.mul_sub_left_distrib q (q ^ 2) 1).symm
      _ = q * ((q + 1) * (q - 1)) := by
        rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by
          simpa using Nat.pow_two_sub_pow_two q 1]
      _ = (q - 1) * (q * (q + 1)) := by ac_rfl
  have hcardRoot : Nat.card Root = q * (q + 1) := by
    rw [hKcard] at hcardEq
    change (q - 1) * Nat.card Root = q ^ 3 - q at hcardEq
    rw [hfactor] at hcardEq
    exact Nat.mul_left_cancel (Nat.sub_pos_of_lt hqTwo) hcardEq
  simpa [Root, q] using hcardRoot

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem cubic_linear_contradiction
    {G : Type u} {Ω : Type v} [Group G] [Finite G]
    [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    [Subgroup.Normalizes K S]
    (hch : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
      K ≤ D ∧
        (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
          V = peterfalviV D t ∧ W ≤ V ∧ W = peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
                S ≤ Q ∧ Q1 ≤ Q ∧
                  (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                    Odd (Nat.card Q1) ∧ Disjoint S Q1 ∧
                      (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 →
                        s * q1 = q1 * s) ∧ S ⊔ Q1 = Q) ∧
      s ∈ H ∧ IsInvolution s ∧
        ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
      HypothesisC1 G V)
    (hSQ : S = Q) (hVleD : V ≤ D)
    (hDnormS : D ≤ Subgroup.normalizer (S : Set G))
    (hKnormalD : (K.subgroupOf D).Normal)
    (hKcyclic : IsCyclic K) (_hKfaithful : FaithfulSMul K S)
    (hKregular : ActionRegularOn K S (involutions S))
    (hSuzuki : IsSuzukiTwoGroup S)
    (hcardCube : Nat.card S = Nat.card (Subgroup.center S) ^ 3)
    (P : Subgroup G) (p : ℕ) (hPV : P ≤ V)
    (hp : Nat.Prime p) (hPcard : Nat.card P = p)
    (hPne : P ≠ ⊥)
    (hlinearCX : IsElementaryAbelian 2
      ((Subgroup.centralizer (P : Set G)) ⊓ Q : Subgroup G))
    (hWbot : W = ⊥) : False := by
  classical
  let CX : Subgroup G := Subgroup.centralizer (P : Set G) ⊓ Q
  let Z := Subgroup.center S
  let E := S ⧸ Z
  let q := Nat.card Z
  have hsQ0 : s ∈ Q0 :=
    (hch.1.1.Q0_def s).mpr
      (Or.inr ⟨hch.1.2.1, hch.1.2.2.1⟩)
  have hsS : s ∈ S := by
    rw [hSQ]
    exact hch.1.1.Q0_le_Q hsQ0
  let sS : S := ⟨s, hsS⟩
  have hsSInv : IsInvolution sS :=
    ⟨fun h => hch.1.2.2.1.ne_one
        (congrArg (fun z : S => (z : G)) h),
      Subtype.ext hch.1.2.2.1.sq_eq_one⟩
  have hSpgroup : IsPGroup 2 S :=
    External.Higman.isPGroup_of_isSuzukiTwoGroup hSuzuki
  have hZpgroup : IsPGroup 2 Z := hSpgroup.to_subgroup Z
  obtain ⟨n, hqPow⟩ := hZpgroup.exists_card_eq
  change q = 2 ^ n at hqPow
  have hqTwo : 2 ≤ q := by
    have hsCenter : sS ∈ Z := by
      have hsMem : sS ∈ involutions S := hsSInv
      rw [(higmanTheorem_involutions_center hSuzuki).1] at hsMem
      exact hsMem.1
    have hZne : Z ≠ ⊥ := by
      intro hbot
      have hsOne : sS = 1 := by
        have : sS ∈ (⊥ : Subgroup S) := by simpa [hbot] using hsCenter
        simpa using this
      exact hsSInv.ne_one hsOne
    have hq1lt : 1 < q := by simpa [q] using Z.one_lt_card_iff_ne_bot.mpr hZne
    exact Nat.succ_le_of_lt hq1lt
  have hKcard : Nat.card K = q - 1 := by
    let Inv : Type u := {x : S // x ∈ involutions S}
    let orbit : K → Inv := fun k =>
      ⟨k • sS, hKregular.1 sS hsSInv k⟩
    have horbitBij : Function.Bijective orbit := by
      constructor
      · intro k l hkl
        have hval : k • sS = l • sS := congrArg Subtype.val hkl
        rcases hKregular.2 sS hsSInv (k • sS)
            (hKregular.1 sS hsSInv k) with ⟨a, _ha, huniq⟩
        exact (huniq k rfl).trans (huniq l hval).symm
      · rintro ⟨x, hx⟩
        rcases hKregular.2 sS hsSInv x hx with ⟨k, hk, _huniq⟩
        exact ⟨k, Subtype.ext hk.symm⟩
    let orbitEquiv : K ≃ Inv := Equiv.ofBijective orbit horbitBij
    let ZSharp : Type u := {z : Z // (z : S) ≠ 1}
    let invCenterEquiv : Inv ≃ ZSharp :=
      { toFun := fun x =>
          ⟨⟨(x : S), by
            have hx : (x : S) ∈
                {z : S | z ∈ Subgroup.center S ∧ z ≠ 1} := by
              rw [← (higmanTheorem_involutions_center hSuzuki).1]
              exact x.property
            exact hx.1⟩, x.property.ne_one⟩
        invFun := fun z =>
          ⟨(z : S), by
            rw [(higmanTheorem_involutions_center hSuzuki).1]
            exact ⟨z.1.property, z.property⟩⟩
        left_inv := by intro x; rfl
        right_inv := by intro z; rfl }
    have hZSharpCard : Nat.card ZSharp = q - 1 := by
      letI : Fintype Z := Fintype.ofFinite Z
      letI : Fintype {z : Z // (z : S) = 1} := Fintype.ofFinite _
      letI : Fintype ZSharp := Fintype.ofFinite ZSharp
      have hsplit := Fintype.card_subtype_compl
        (fun z : Z => (z : S) = 1)
      have honeCard : Nat.card {z : Z // (z : S) = 1} = 1 := by
        let oneEquiv : {z : Z // (z : S) = 1} ≃ PUnit.{0} :=
          { toFun := fun _ => PUnit.unit
            invFun := fun _ => ⟨1, rfl⟩
            left_inv := by
              intro z
              apply Subtype.ext
              apply Subtype.ext
              exact z.property.symm
            right_inv := by intro z; cases z; rfl }
        simp
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
        Fintype.card_eq_nat_card, honeCard] at hsplit
      omega
    calc
      Nat.card K = Nat.card Inv := Nat.card_congr orbitEquiv
      _ = Nat.card ZSharp := Nat.card_congr invCenterEquiv
      _ = q - 1 := hZSharpCard
  have hVeq : V = D ⊓ Subgroup.centralizer ({s} : Set G) := by
    calc
      V = peterfalviV D t := hch.1.1.V_eq
      _ = D ⊓ Subgroup.centralizer ({s} : Set G) :=
        (PFchapter1section1.proposition_5 H D Q t s
          hch.1.1.hA.A1 hch.1.2.1 hch.1.2.2.1 hch.1.2.2.2).1
  have hPcentralizesS : P ≤ Subgroup.centralizer ({s} : Set G) := by
    intro c hc
    have hcV := hPV hc
    rw [hVeq] at hcV
    exact hcV.2
  have hPnormS : P ≤ Subgroup.normalizer (S : Set G) :=
    hPV.trans (hVleD.trans hDnormS)
  letI : Subgroup.Normalizes P S := ⟨hPnormS⟩
  let Root : SubMulAction P S :=
    { carrier := {r : S | r ^ 2 = sS}
      smul_mem' := by
        intro c r hr
        change (c • r) ^ 2 = sS
        rw [← smul_pow', hr]
        apply Subtype.ext
        change (c : G) * s * (c : G)⁻¹ = s
        have hcComm : (c : G) * s = s * (c : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp
            (hPcentralizesS c.property)
        rw [hcComm]
        simp }
  have hRootCard : Nat.card Root = q * (q + 1) := by
    have hcard := cubic_full_root_card hSuzuki hKregular hKcard
      hcardCube sS hsSInv
    have hEquiv : Root ≃ {x : S // x ^ 2 = sS} := by
      refine
        { toFun := λ x => ⟨x.1, ?_⟩
          invFun := λ x => ⟨x.1, ?_⟩
          left_inv := λ _ => rfl
          right_inv := λ _ => rfl }
      · have hxRoot : x.1 ∈ (Root : Set S) := x.2
        have hRootSet : (Root : Set S) = {r | r ^ 2 = sS} := rfl
        rw [hRootSet] at hxRoot
        have : x.1 ^ 2 = sS := hxRoot
        exact this
      · show x.1 ∈ Root
        simp [Root]
    calc
      Nat.card Root = Nat.card {x : S // x ^ 2 = sS} := Nat.card_congr hEquiv
      _ = q * (q + 1) := by simpa [q] using hcard
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hPpgroup : IsPGroup p P :=
    IsPGroup.of_card (n := 1) (by simpa using hPcard)
  have hpDvdD : p ∣ Nat.card D := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le (hPV.trans hVleD)
  have hpOdd : Odd p := hch.1.1.hA.A1.D_odd.of_dvd_nat hpDvdD
  have hpNeTwo : p ≠ 2 := by
    intro hpTwo
    apply hpOdd.not_two_dvd_nat
    simp [hpTwo]
  have hpNotDvdQ : ¬ p ∣ q := by
    intro hpq
    rw [hqPow] at hpq
    have hpTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpq
    rcases (Nat.dvd_prime Nat.prime_two).mp hpTwo with hpOne | hpTwo
    · exact hp.ne_one hpOne
    · exact hpNeTwo hpTwo
  have hpDvdRoot : p ∣ Nat.card Root := by
    by_contra hpNot
    rcases hPpgroup.nonempty_fixed_point_of_prime_not_dvd_card
        Root hpNot with ⟨r, hrFixed⟩
    have hrFix : ∀ c : P, c • r = r :=
      MulAction.mem_fixedPoints.mp hrFixed
    have hrCentralizer : ((r : S) : G) ∈
        Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hcP
      let cP : P := ⟨c, hcP⟩
      have hfixS : cP • (r : S) = (r : S) :=
        congrArg Subtype.val (hrFix cP)
      have hfixG : c * ((r : S) : G) * c⁻¹ = ((r : S) : G) := by
        simpa [cP,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            congrArg (fun z : S => (z : G)) hfixS
      have hmul := congrArg (fun z : G => z * c) hfixG
      simpa [mul_assoc] using hmul
    have hrCX : ((r : S) : G) ∈ CX := by
      refine ⟨hrCentralizer, ?_⟩
      rw [← hSQ]
      exact (r : S).property
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : IsElementaryAbelian 2 CX := hlinearCX
    let rCX : CX := ⟨((r : S) : G), hrCX⟩
    have hrSqSub : rCX ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 CX) rCX
    have hrSqG : ((r : S) : G) ^ 2 = 1 :=
      congrArg (fun z : CX => (z : G)) hrSqSub
    apply hch.1.2.2.1.ne_one
    calc
      s = ((r : S) : G) ^ 2 :=
        (congrArg (fun z : S => (z : G)) r.property).symm
      _ = 1 := hrSqG
  have hpDvdQPlus : p ∣ q + 1 := by
    have hpMul : p ∣ q * (q + 1) := by
      simpa [hRootCard] using hpDvdRoot
    exact (hp.dvd_mul.mp hpMul).resolve_left hpNotDvdQ
  have hpNotDvdQSub : ¬ p ∣ q - 1 := by
    intro hpSub
    have hpTwo : p ∣ 2 := by
      have h := Nat.dvd_sub hpDvdQPlus hpSub
      (convert h using 1; omega)
    rcases (Nat.dvd_prime Nat.prime_two).mp hpTwo with hpOne | hpTwo
    · exact hp.ne_one hpOne
    · exact hpNeTwo hpTwo
  have hPKcoprime : Nat.Coprime (Nat.card P) (Nat.card K) := by
    rw [hPcard, hKcard]
    exact hp.coprime_iff_not_dvd.mpr hpNotDvdQSub
  have hPnormK : P ≤ Subgroup.normalizer (K : Set G) := by
    intro c hcP
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hkK
      let cD : D := ⟨c, hVleD (hPV hcP)⟩
      let kD : D := ⟨k, hch.1.1.K_le_D hkK⟩
      have hmem := hKnormalD.conj_mem kD hkK cD
      simpa [cD, kD, Subgroup.mem_subgroupOf] using hmem
    · intro hconjK
      let cD : D := ⟨c, hVleD (hPV hcP)⟩
      let kcD : D := ⟨c * k * c⁻¹, hch.1.1.K_le_D hconjK⟩
      have hmem := hKnormalD.conj_mem kcD hconjK cD⁻¹
      simpa [cD, kcD, Subgroup.mem_subgroupOf, mul_assoc] using hmem
  letI : Subgroup.Normalizes P K := ⟨hPnormK⟩
  have hKcomm : IsMulCommutative K := hKcyclic.isMulCommutative
  let Cfix : Subgroup K := fixedPointSubgroup P K
  let Ccomm : Subgroup K := commutatorAction (A := P) (G := K)
  have hKsolvable : Group.IsSolvable K := by
    letI : IsMulCommutative K := hKcomm
    infer_instance
  have hcompl : IsCompl Cfix Ccomm := by
    simpa [Cfix, Ccomm] using
      (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := K) (A := P) hKsolvable hPKcoprime hKcomm)
  have hCcommNe : Ccomm ≠ ⊥ := by
    intro hCcommBot
    have hCfixTop : Cfix = ⊤ := by
      simpa [hCcommBot] using hcompl.sup_eq_top
    have hPleW : P ≤ W := by
      intro c hcP
      rw [hch.1.1.W_eq]
      refine ⟨hPV hcP, ?_⟩
      change c ∈ Subgroup.centralizer (K : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro k hkK
      let cP : P := ⟨c, hcP⟩
      let kK : K := ⟨k, hkK⟩
      have hkFix : cP • kK = kK := by
        have hkMem : kK ∈ Cfix := by
          rw [hCfixTop]
          exact Subgroup.mem_top kK
        simpa [Cfix] using hkMem cP
      have hkConj : c * k * c⁻¹ = k := by
        simpa [cP, kK,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            congrArg (fun z : K => (z : G)) hkFix
      have hmul := congrArg (fun z : G => z * c) hkConj
      simpa [mul_assoc] using hmul.symm
    have hPbot : P = ⊥ := by
      apply le_antisymm
      · intro c hcP
        have hcW := hPleW hcP
        rw [hWbot] at hcW
        simpa using hcW
      · exact bot_le
    exact hPne hPbot
  have hCcommInv : IsInvariant P K Ccomm := by
    simpa [Ccomm] using
      (commutatorAction_isInvariant (G := K) (A := P))
  letI : IsInvariant P K Ccomm := hCcommInv
  letI : MulDistribMulAction P Ccomm := inferInstance
  have hPcardPrime : Nat.Prime (Nat.card P) := by
    simpa [hPcard] using hp
  have hCcommRegular : ActsRegularly P Ccomm := by
    intro a ha
    have hzpTop : Subgroup.zpowers a = ⊤ :=
      zpowers_eq_top_of_prime_card_of_ne_one hPcardPrime ha
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    have hcFixK : (c : K) ∈ Cfix := by
      change ∀ b : P, b • (c : K) = (c : K)
      intro b
      let bz : Subgroup.zpowers a :=
        ⟨b, by rw [hzpTop]; exact Subgroup.mem_top b⟩
      have hbc : bz • c = c := hc bz
      exact congrArg Subtype.val hbc
    have hcInf : (c : K) ∈ Cfix ⊓ Ccomm := ⟨hcFixK, c.property⟩
    have hcBot : (c : K) ∈ (⊥ : Subgroup K) := by
      rw [← hcompl.inf_eq_bot]
      exact hcInf
    have hcOne : (c : K) = 1 := by simpa using hcBot
    exact Subtype.ext hcOne
  letI : Nontrivial Ccomm :=
    (Subgroup.nontrivial_iff_ne_bot Ccomm).2 hCcommNe
  letI : Nontrivial P :=
    (Subgroup.nontrivial_iff_ne_bot P).2 hPne
  let phi : P →* MulAut Ccomm := MulDistribMulAction.toMulAut P Ccomm
  let SD := Ccomm ⋊[phi] P
  let KSD : Subgroup SD := MonoidHom.range (SemidirectProduct.inl : Ccomm →* SD)
  let RSD : Subgroup SD := MonoidHom.range (SemidirectProduct.inr : P →* SD)
  have hfrob : IsFrobeniusGroupWithKernelComplement KSD RSD := by
    simpa [KSD, RSD, SD, phi] using
      (External.hkt_regularSemidirect_isFrobenius
        (A := Ccomm) (B := P) hCcommRegular)
  have hn : n ≠ 0 := by
    intro hn0
    subst n
    norm_num at hqPow
    omega
  letI : IsInvariant K S Z := center_isInvariant
  let defaultKAction : MulDistribMulAction K E :=
    quotientMulDistribMulAction (A := K) (G := S) Z
      (inferInstance : IsInvariant K S Z)
  letI : MulDistribMulAction K E := defaultKAction
  have hKfixedFree :
      ∀ k : K, k ≠ 1 → ∀ x : E,
        @SMul.smul K E defaultKAction.toSMul k x = x → x = 1 := by
    intro k hk x hkx
    by_contra hxOne
    let A : Subgroup K := Subgroup.zpowers k
    letI : MulDistribMulAction A S := inferInstance
    letI : IsInvariant A S Z := center_isInvariant
    let quotientActionA : MulDistribMulAction A E :=
      quotientMulDistribMulAction (A := A) (G := S) Z
        (inferInstance : IsInvariant A S Z)
    letI : MulDistribMulAction A E := quotientActionA
    have hgenAction :
        (⟨k, Subgroup.mem_zpowers k⟩ : A) • x = x := by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z x
      change QuotientGroup.mk' Z (k • y) = QuotientGroup.mk' Z y
      dsimp [defaultKAction] at hkx
      exact hkx
    have hxFixed : x ∈ fixedPointSubgroup A E := by
      change ∀ a : A, a • x = x
      intro a
      exact smul_eq_self_of_mem_zpowers a.property hgenAction
    have hAcardDvd : Nat.card A ∣ Nat.card K :=
      Subgroup.card_subgroup_dvd_card A
    have hKodd : Odd (Nat.card K) := by
      rw [hKcard]
      rw [hqPow]
      exact Nat.Even.sub_odd (pow_pos (by norm_num : 0 < (2 : ℕ)) n)
        (Nat.even_pow.mpr ⟨even_two, hn⟩) odd_one
    have hAodd : Odd (Nat.card A) := hKodd.of_dvd_nat hAcardDvd
    have hScardPow : ∃ m : ℕ, Nat.card S = 2 ^ m := by
      rcases hSuzuki.1 with ⟨m, hm⟩
      exact ⟨m, by simpa using hm⟩
    have hcoprime : Nat.Coprime (Nat.card A) (Nat.card S) := by
      rcases hScardPow with ⟨m, hm⟩
      rw [hm]
      exact hAodd.coprime_two_right.pow_right m
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Group.IsNilpotent S := hSpgroup.isNilpotent
    have hSsolvable : Group.IsSolvable S := by infer_instance
    have hfixedEq :=
      fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
        (G := S) (A := A) hSsolvable hcoprime (∅ : Set Nat.Primes)
        Z (inferInstance : IsInvariant A S Z)
    have hxMap : x ∈ (fixedPointSubgroup A S).map
        (QuotientGroup.mk' Z) := by
      rw [← hfixedEq]
      exact hxFixed
    rcases Subgroup.mem_map.mp hxMap with ⟨f, hfFixed, hfx⟩
    let B : Subgroup S := fixedPointSubgroup A S
    have hBne : B ≠ ⊥ := by
      intro hBbot
      have hfOne : f = 1 := by
        have : f ∈ (⊥ : Subgroup S) := by
          simpa [B, hBbot] using hfFixed
        simpa using this
      apply hxOne
      rw [← hfx, hfOne, map_one]
    have hBInv : IsXInvariantSubgroup K B := by
      have hpreserve : ∀ l : K, ∀ b : S, b ∈ B → l • b ∈ B := by
        intro l b hb
        change ∀ a : A, a • (l • b) = l • b
        intro a
        have hcomm : (a : K) * l = l * (a : K) :=
          hKcomm.is_comm.comm (a : K) l
        have hab : (a : K) • b = b := by
          simpa only [Subgroup.smul_def] using hb a
        calc
          a • (l • b) = (a : K) • (l • b) := by rw [Subgroup.smul_def]
          _ = ((a : K) * l) • b := by rw [mul_smul]
          _ = (l * (a : K)) • b := by rw [hcomm]
          _ = l • ((a : K) • b) := by rw [mul_smul]
          _ = l • b := by rw [hab]
      intro l b
      constructor
      · exact hpreserve l b
      · intro hlb
        have hback := hpreserve l⁻¹ (l • b) hlb
        simpa [smul_smul] using hback
    have hKtrans : ∀ a : S, a ∈ involutions S →
        ∀ b : S, b ∈ involutions S → ∃ l : K, b = l • a := by
      intro a ha b hb
      rcases hKregular.2 a ha b hb with ⟨l, hl, _huniq⟩
      exact ⟨l, hl⟩
    have hsB : sS ∈ B :=
      lemma1_involutions_mem_of_nontrivial_invariant
        hSuzuki hKtrans hBInv hBne sS hsSInv
    have hks : k • sS = sS := by
      have := hsB (⟨k, Subgroup.mem_zpowers k⟩ : A)
      simpa using this
    have hkOne : k = 1 :=
      (hKregular.2 sS hsSInv sS hsSInv).unique hks.symm (by simp)
    exact hk hkOne
  letI : Subgroup.Normalizes D S := ⟨hDnormS⟩
  letI : IsInvariant D S Z := center_isInvariant
  let defaultDAction : MulDistribMulAction D E :=
    quotientMulDistribMulAction (A := D) (G := S) Z
      (inferInstance : IsInvariant D S Z)
  letI : MulDistribMulAction D E := defaultDAction
  let cToD : Ccomm →* D :=
    { toFun := fun c =>
        ⟨((c : Ccomm) : K), hch.1.1.K_le_D (c : K).property⟩
      map_one' := rfl
      map_mul' := by intro x y; rfl }
  let pToD : P →* D :=
    { toFun := fun a => ⟨(a : G), hVleD (hPV a.property)⟩
      map_one' := rfl
      map_mul' := by intro x y; rfl }
  have hsemiCompat : ∀ a,
      cToD.comp (phi a).toMonoidHom =
        (MulAut.conj (pToD a)).toMonoidHom.comp cToD := by
    intro a
    ext c
    change ((a • (c : K) : K) : G) =
      (a : G) * ((c : K) : G) * (a : G)⁻¹
    exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
      P K a (c : K)
  let sdToD : SD →* D :=
    SemidirectProduct.lift cToD pToD hsemiCompat
  letI : MulDistribMulAction SD E :=
    MulDistribMulAction.compHom E sdToD
  have hEdata := higmanTheorem_center_quotient_orders_and_exponent hSuzuki
  have hEcomm : IsMulCommutative E := by
    simpa [E, Z] using hEdata.1
  have hEpow : ∀ x : E, x ^ 2 = 1 := by
    simpa [E, Z] using hEdata.2.1
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsElementaryAbelian 2 E :=
    { toIsMulCommutative := hEcomm
      exponent_dvd_p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hEpow }
  have hQ0leS : Q0 ≤ S := by
    rw [hSQ]
    exact hch.1.1.Q0_le_Q
  let Q0S : Subgroup S := Q0.subgroupOf S
  have hQ0SCenter : Q0S = Z := by
    ext x
    change (x : G) ∈ Q0 ↔ x ∈ Subgroup.center S
    constructor
    · intro hxQ0
      rcases (hch.1.1.Q0_def (x : G)).mp hxQ0 with hxOne | hxInv
      · have hxOneS : x = 1 := Subtype.ext hxOne
        rw [hxOneS]
        exact (Subgroup.center S).one_mem
      · have hxInvS : IsInvolution x :=
          ⟨fun hx => hxInv.2.ne_one
              (congrArg (fun z : S => (z : G)) hx),
            Subtype.ext hxInv.2.sq_eq_one⟩
        have hxMem : x ∈ involutions S := hxInvS
        rw [(higmanTheorem_involutions_center hSuzuki).1] at hxMem
        exact hxMem.1
    · intro hxCenter
      by_cases hxOne : x = 1
      · exact (congrArg (fun z : S => (z : G)) hxOne) ▸ Q0.one_mem
      · have hxMem : x ∈ involutions S := by
          rw [(higmanTheorem_involutions_center hSuzuki).1]
          exact ⟨hxCenter, hxOne⟩
        have hxInvG : IsInvolution (x : G) :=
          ⟨fun hx => hxMem.ne_one (Subtype.ext hx),
            congrArg (fun z : S => (z : G)) hxMem.sq_eq_one⟩
        exact (hch.1.1.Q0_def (x : G)).mpr <| Or.inr
          ⟨hch.1.1.hA.A1.Q_le_H
            (by rw [← hSQ]; exact x.property), hxInvG⟩
  have hfixedSLeZ : fixedPointSubgroup P S ≤ Z := by
    intro x hxFixed
    have hxCentralizer : ((x : S) : G) ∈
        Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hcP
      let cP : P := ⟨c, hcP⟩
      have hfixS : cP • (x : S) = (x : S) := hxFixed cP
      have hfixG : c * ((x : S) : G) * c⁻¹ = ((x : S) : G) := by
        simpa [cP,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            congrArg (fun z : S => (z : G)) hfixS
      have hmul := congrArg (fun z : G => z * c) hfixG
      simpa [mul_assoc] using hmul
    have hxCX : ((x : S) : G) ∈ CX := by
      refine ⟨hxCentralizer, ?_⟩
      rw [← hSQ]
      exact (x : S).property
    letI : IsElementaryAbelian 2 CX := hlinearCX
    let xCX : CX := ⟨((x : S) : G), hxCX⟩
    have hxSqSub : xCX ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 CX) xCX
    have hxSq : ((x : S) : G) ^ 2 = 1 :=
      congrArg (fun z : CX => (z : G)) hxSqSub
    have hxQ0 : ((x : S) : G) ∈ Q0 := by
      rw [hch.1.1.Q0_def]
      by_cases hxOne : (x : S) = 1
      · exact Or.inl (congrArg (fun z : S => (z : G)) hxOne)
      · exact Or.inr
          ⟨hch.1.1.hA.A1.Q_le_H (by rw [← hSQ]; exact (x : S).property),
            ⟨fun h => hxOne (Subtype.ext h), hxSq⟩⟩
    have hxQ0S : (x : S) ∈ Q0S := hxQ0
    rw [hQ0SCenter] at hxQ0S
    exact hxQ0S
  letI : IsInvariant P S Z := center_isInvariant
  let defaultPAction : MulDistribMulAction P E :=
    quotientMulDistribMulAction (A := P) (G := S) Z
      (inferInstance : IsInvariant P S Z)
  letI : MulDistribMulAction P E := defaultPAction
  have hScardPow : ∃ m : ℕ, Nat.card S = 2 ^ m := by
    rcases hSuzuki.1 with ⟨m, hm⟩
    exact ⟨m, by simpa using hm⟩
  have hPScoprime : Nat.Coprime (Nat.card P) (Nat.card S) := by
    rcases hScardPow with ⟨m, hm⟩
    rw [hPcard, hm]
    exact hpOdd.coprime_two_right.pow_right m
  letI : Group.IsNilpotent S := hSpgroup.isNilpotent
  have hSsolvable : Group.IsSolvable S := by infer_instance
  have hfixedEq :=
    fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
      (G := S) (A := P) hSsolvable hPScoprime (∅ : Set Nat.Primes)
      Z (inferInstance : IsInvariant P S Z)
  have hfixedMapBot : (fixedPointSubgroup P S).map
      (QuotientGroup.mk' Z) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hxZ : x ∈ Z := hfixedSLeZ hx
    have hxOne : QuotientGroup.mk' Z x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hxZ
    simp [hxOne]
  have hPfixedE : fixedPointSubgroup P E = ⊥ := by
    rw [hfixedEq]
    exact hfixedMapBot
  letI : MulDistribMulAction KSD E :=
    MulDistribMulAction.compHom E KSD.subtype
  have hKSDfixedE : fixedPointSubgroup KSD E = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨c, hc⟩ := exists_ne (1 : Ccomm)
    let kc : KSD :=
      ⟨SemidirectProduct.inl c, ⟨c, rfl⟩⟩
    have hkcFix : kc • x = x := hx kc
    have hsdFix : (SemidirectProduct.inl c : SD) • x = x := by
      have : (kc : KSD) • x = (SemidirectProduct.inl c : SD) • x := by
        calc
          (kc : KSD) • x = (KSD.subtype (kc : KSD) : SD) • x := by
            simpa using (MulAction.compHom_smul_def (KSD.subtype : KSD →* SD) (kc : KSD) x)
          _ = (SemidirectProduct.inl c : SD) • x := by simp [kc]
      rw [← this, hkcFix]
    have hcFix :
        @SMul.smul K E defaultKAction.toSMul (c : K) x = x := by
      have hK_smul_eq : (c : K) • x = (SemidirectProduct.inl c : SD) • x := by
        calc
          (c : K) • x = (cToD c : D) • x := by
            obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective Z x
            calc
              (c : K) • QuotientGroup.mk' Z s = QuotientGroup.mk' Z ((c : K) • s) := by
                simp
              _ = QuotientGroup.mk' Z ((cToD c : D) • s) := by
                have : (cToD c : D) • s = (c : K) • s := by
                  dsimp [cToD]; rfl
                rw [this]
              _ = (cToD c : D) • QuotientGroup.mk' Z s := by
                simp
          _ = sdToD (SemidirectProduct.inl c) • x := by
            dsimp [sdToD]; rw [SemidirectProduct.lift_inl]
          _ = (SemidirectProduct.inl c : SD) • x := by
            simpa using (MulAction.compHom_smul_def sdToD (SemidirectProduct.inl c : SD) x).symm
      calc
        @SMul.smul K E defaultKAction.toSMul (c : K) x = (c : K) • x := rfl
        _ = (SemidirectProduct.inl c : SD) • x := hK_smul_eq
        _ = x := hsdFix
    have hcKne : (c : K) ≠ 1 := by
      intro hcOne
      apply hc
      exact Subtype.ext hcOne
    have hxOne : x = 1 := hKfixedFree (c : K) hcKne x hcFix
    simp [hxOne]
  letI : MulDistribMulAction RSD E :=
    MulDistribMulAction.compHom E RSD.subtype
  have hRSDfixedE : fixedPointSubgroup RSD E = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxP : x ∈ fixedPointSubgroup P E := by
      change ∀ a : P, a • x = x
      intro a
      let ra : RSD :=
        ⟨SemidirectProduct.inr a, ⟨a, rfl⟩⟩
      have hraFix : ra • x = x := hx ra
      have hsdFix : (SemidirectProduct.inr a : SD) • x = x := by
        have : (ra : RSD) • x = (SemidirectProduct.inr a : SD) • x := by
          calc
            (ra : RSD) • x = (RSD.subtype (ra : RSD) : SD) • x := by
              simpa using (MulAction.compHom_smul_def (RSD.subtype : RSD →* SD) (ra : RSD) x)
            _ = (SemidirectProduct.inr a : SD) • x := by simp [ra]
        rw [← this, hraFix]
      have haFix : (a : P) • x = x := by
        have hP_smul_eq : (a : P) • x = (SemidirectProduct.inr a : SD) • x := by
          calc
            (a : P) • x = (pToD a : D) • x := by
              obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective Z x
              calc
                (a : P) • QuotientGroup.mk' Z s = QuotientGroup.mk' Z ((a : P) • s) := by
                  simp
                _ = QuotientGroup.mk' Z ((pToD a : D) • s) := by
                  have : (pToD a : D) • s = (a : P) • s := by
                    dsimp [pToD]; rfl
                  rw [this]
                _ = (pToD a : D) • QuotientGroup.mk' Z s := by
                  simp
            _ = sdToD (SemidirectProduct.inr a) • x := by
              dsimp [sdToD]; rw [SemidirectProduct.lift_inr]
            _ = (SemidirectProduct.inr a : SD) • x := by
              simpa using (MulAction.compHom_smul_def sdToD (SemidirectProduct.inr a : SD) x).symm
        calc
          @SMul.smul P E defaultPAction.toSMul (a : P) x = (a : P) • x := rfl
          _ = (SemidirectProduct.inr a : SD) • x := hP_smul_eq
          _ = x := hsdFix
      exact haFix
    have hxBot : x ∈ (⊥ : Subgroup E) := by
      rw [← hPfixedE]
      exact hxP
    simpa using hxBot
  have hcenterOne : 1 < Nat.card (Subgroup.center S) := by
    have : 1 < q := by omega
    simpa [q, Z] using this
  have hEcardGt : 1 < Nat.card E := by
    rcases hEdata.2.2.1 with hEcard | hEcard
    · rw [hEcard]
      exact hcenterOne
    · rw [hEcard]
      exact one_lt_pow' hcenterOne (by norm_num)
  letI : Nontrivial E :=
    Finite.one_lt_card_iff_nontrivial.mp hEcardGt
  letI : Finite SD :=
    Finite.of_equiv (Ccomm × P)
      (SemidirectProduct.equivProd (φ := phi)).symm
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : CommGroup E := IsMulCommutative.instCommGroup
  let rho :=
    Theory.Representation.ofElementaryAbelianAction (A := SD) (G := E) (p := 2)
  have hKSDNotKer : ¬ KSD ≤ rho.ker := by
    intro hKSDker
    have hKSDcent : KSD ≤ rho.centralizerIn KSD := by
      exact (le_centralizerIn_iff_le_ker
        (ρ := rho) (H := KSD) (K := KSD) le_rfl).2 hKSDker
    have hfixTop : fixedPointSubgroup KSD E = ⊤ := by
      simpa [rho] using
        (theorem_3_7_fixedPointSubgroup_eq_top_of_le_centralizerIn
          (A := SD) (V := E) (q := 2) KSD hKSDcent)
    exact top_ne_bot (hfixTop.symm.trans hKSDfixedE)
  let eKSD : Ccomm ≃* KSD :=
    MulEquiv.ofBijective
      (SemidirectProduct.inl : Ccomm →* SD).rangeRestrict
      ⟨(fun x y h => SemidirectProduct.inl_injective
          (congrArg Subtype.val h)),
        (SemidirectProduct.inl : Ccomm →* SD).rangeRestrict_surjective⟩
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard, hqPow]
    exact Nat.Even.sub_odd (pow_pos (by norm_num : 0 < (2 : ℕ)) n)
      (Nat.even_pow.mpr ⟨even_two, hn⟩) odd_one
  have hCcommOdd : Odd (Nat.card Ccomm) :=
    hKodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Ccomm)
  have hKSDOdd : Odd (Nat.card KSD) := by
    rw [← Nat.card_congr eKSD.toEquiv]
    exact hCcommOdd
  have hchar : ringChar (ZMod 2) = 0 ∨
      (Nat.Prime (ringChar (ZMod 2)) ∧
        Nat.Coprime (ringChar (ZMod 2)) (Nat.card KSD)) := by
    exact Or.inr
      ⟨by simpa [ZMod.ringChar_zmod_n] using Nat.prime_two,
        by
          simpa [ZMod.ringChar_zmod_n] using
            (Nat.prime_two.coprime_iff_not_dvd.mpr
              hKSDOdd.not_two_dvd_nat)⟩
  have hRfixedNe : rho.fixedSubspace RSD ≠ ⊥ :=
    lemma_3_3 KSD RSD rho hfrob hchar hKSDNotKer
  have hRfixedBot : rho.fixedSubspace RSD = ⊥ := by
    simpa [rho] using
      (theorem_3_7_fixedSubspace_eq_bot_of_fixedPointSubgroup_eq_bot
        (A := SD) (V := E) (q := 2) RSD hRSDfixedE)
  exact hRfixedNe hRfixedBot

set_option maxHeartbeats 800000 in
private theorem psu_sylow_normalizer_center_witness
    {E : Type u} [Field E] [Finite E] (J : HermitianForm 3 E) (q : ℕ)
    (hqPower : ∃ n : ℕ, q = 2 ^ n) (hqGt : 2 < q)
    (hEcard : Nat.card E = q ^ 2)
    (hfixedCard : Nat.card {z : E // J.conj z = z} = q)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (P0 : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hP0p : IsPGroup 2 P0) (hP0card : Nat.card P0 = q ^ 3) :
    ∃ g : ProjectiveSpecialUnitaryMatrixGroup J,
      g ∉ P0 ∧
      g ∈ Subgroup.normalizer (P0 : Set _) ∧
      ∀ z : P0, z ∈ Subgroup.center P0 →
        Commute g (z : ProjectiveSpecialUnitaryMatrixGroup J) := by
  classical
  let G0 := ProjectiveSpecialUnitaryMatrixGroup J
  letI : Fintype E := Fintype.ofFinite E
  let projSU : J.specialSubgroup → G0 := fun x =>
    ⟨Matrix.ProjGenLinGroup.mk x, Subgroup.mem_map_of_mem
      Matrix.ProjGenLinGroup.mk x.property⟩
  have hprojSUsurjective : Function.Surjective projSU := by
    rintro ⟨y, hy⟩
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  letI : Finite G0 := Finite.of_surjective projSU hprojSUsurjective
  rcases External.huppert_II_10_12 J q hEcard hfixedCard hJstandard with
    ⟨_hOmegaCard, _rho, _pinf, _hrhoInjective, _hnatural,
      _hUcard, hroot, _htwoTransitive, hGcard, _hthreeFixed⟩
  rcases hroot with
    ⟨R, T, hRleU, hTleU, hUnormalizesR, hRTinf, _hRTsup,
      _hTcyclic, hRcard, hcommCenter, hcommCard, _hTcard,
      _hRregular, hcoord, _hTcoord, hTcoordSurjective⟩
  rcases hcoord with ⟨coordR, hcoordMatrix⟩
  let rootPSU := External.hermitianUnipotentPSU J hJstandard
  have hcoordEqRoot (z : External.hermitianUnipotentCoord J) :
      ((coordR z : R) : G0) = rootPSU z := by
    rcases hcoordMatrix z with ⟨M, hM, hMproj⟩
    have hMroot : M = External.hermitianUnipotentGL J z := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change (M : Matrix (Fin 3) (Fin 3) E) i j =
        (External.hermitianUnipotentGL J z : Matrix (Fin 3) (Fin 3) E) i j
      rw [hM, External.hermitianUnipotentGL_val,
        External.hermitianUnipotentMatrix_eq]
    apply Subtype.ext
    show (((coordR z : R) : G0) : Matrix.ProjGenLinGroup (Fin 3) E) =
      (rootPSU z : Matrix.ProjGenLinGroup (Fin 3) E)
    calc
      (((coordR z : R) : G0) : Matrix.ProjGenLinGroup (Fin 3) E) =
          Matrix.ProjGenLinGroup.mk M := hMproj
      _ = Matrix.ProjGenLinGroup.mk
          (External.hermitianUnipotentGL J z) := by rw [hMroot]
      _ = (rootPSU z : Matrix.ProjGenLinGroup (Fin 3) E) := by
        rw [External.hermitianUnipotentPSU_val]
  let coordMul : External.hermitianUnipotentCoord J ≃* R :=
    { coordR with
      map_mul' := by
        intro z w
        apply Subtype.ext
        calc
          ((coordR (z * w) : R) : G0) = rootPSU (z * w) :=
            hcoordEqRoot (z * w)
          _ = rootPSU z * rootPSU w := map_mul rootPSU z w
          _ = ((coordR z : R) : G0) * ((coordR w : R) : G0) := by
            rw [hcoordEqRoot, hcoordEqRoot] }
  rcases hqPower with ⟨n, hqPow⟩
  have hn : n ≠ 0 := by
    intro hn0
    subst n
    norm_num at hqPow
    omega
  have hqEven : Even q := by
    rw [hqPow]
    exact Nat.even_pow.mpr ⟨even_two, hn⟩
  have hEeven : Even (Nat.card E) := by
    rw [hEcard]
    exact hqEven.pow_of_ne_zero (by norm_num)
  have hcharE : ringChar E = 2 :=
    FiniteField.even_card_iff_char_two.mpr
      (Nat.even_iff.mp (by simpa using hEeven))
  have htwoE : (2 : E) = 0 := by
    simpa [hcharE] using (CharP.cast_eq_zero E (ringChar E))
  have haddSelf (a : E) : a + a = 0 := by
    rw [← two_mul, htwoE, zero_mul]
  have hnegSelf (a : E) : -a = a :=
    neg_eq_iff_add_eq_zero.mpr (haddSelf a)
  let CenterCoord : Subgroup (External.hermitianUnipotentCoord J) :=
    { carrier := {z | z.1.1 = 0}
      one_mem' := by rfl
      mul_mem' := by
        intro z w hz hw
        change (External.hermitianUnipotentMul J z w).1.1 = 0
        change z.1.1 + w.1.1 = 0
        rw [hz, hw, add_zero]
      inv_mem' := by
        intro z hz
        change (External.hermitianUnipotentInv J z).1.1 = 0
        change -z.1.1 = 0
        rw [hz, neg_zero] }
  let CenterR : Subgroup R := CenterCoord.map coordMul.toMonoidHom
  have hCenterCoordCard : Nat.card CenterCoord = q := by
    let eCenter : {b : E // J.conj b = b} ≃ CenterCoord :=
      { toFun := fun b =>
          ⟨⟨(0, b), by
            change (b : E) + J.conj b + 0 * J.conj 0 = 0
            rw [b.property]
            simpa using haddSelf (b : E)⟩, rfl⟩
        invFun := fun z => ⟨z.1.1.2, by
          have hz := z.1.property
          have hza : z.1.1.1 = 0 := z.property
          change z.1.1.2 + J.conj z.1.1.2 +
              z.1.1.1 * J.conj z.1.1.1 = 0 at hz
          rw [hza] at hz
          simp only [map_zero, zero_mul, add_zero] at hz
          have hneg : z.1.1.2 = -J.conj z.1.1.2 :=
            eq_neg_of_add_eq_zero_left hz
          rw [hnegSelf] at hneg
          exact hneg.symm⟩
        left_inv := by
          intro b
          apply Subtype.ext
          rfl
        right_inv := by
          intro z
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext z.property.symm rfl }
    calc
      Nat.card CenterCoord = Nat.card {b : E // J.conj b = b} :=
        Nat.card_congr eCenter.symm
      _ = q := hfixedCard
  have hCenterRCard : Nat.card CenterR = q := by
    calc
      Nat.card CenterR = Nat.card CenterCoord :=
        Subgroup.card_map_of_injective
          (K := CenterCoord) (f := coordMul.toMonoidHom) coordMul.injective
      _ = q := hCenterCoordCard
  have hCenterRle : CenterR ≤ Subgroup.center R := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := coordMul.surjective y
    have hcommCoord : w * z = z * w := by
      change External.hermitianUnipotentMul J w z =
        External.hermitianUnipotentMul J z w
      apply Subtype.ext
      apply Prod.ext
      · simp only [External.hermitianUnipotentMul]
        exact add_comm _ _
      · change w.1.2 + z.1.2 - w.1.1 * J.conj z.1.1 =
          z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1
        change z.1.1 = 0 at hz
        rw [hz, map_zero, mul_zero, zero_mul, sub_zero, sub_zero, add_comm]
    change coordMul w * coordMul z = coordMul z * coordMul w
    rw [← map_mul, ← map_mul, hcommCoord]
  have hCenterCard : Nat.card (Subgroup.center R) = q := by
    rw [← hcommCenter, hcommCard]
  have hCenterReq : CenterR = Subgroup.center R :=
    Subgroup.eq_of_le_of_card_ge hCenterRle (by
      rw [hCenterRCard, hCenterCard])
  have hRpgroup : IsPGroup 2 R := by
    apply IsPGroup.of_card (n := n * 3)
    rw [hRcard, hqPow, pow_mul]
  obtain ⟨Pstd, hRlePstd⟩ := hRpgroup.exists_le_sylow
  have hqSqEven : Even (q ^ 2) := hqEven.pow_of_ne_zero (by norm_num)
  have hqCubeEven : Even (q ^ 3) := hqEven.pow_of_ne_zero (by norm_num)
  have hqSqPos : 0 < q ^ 2 := pow_pos (by omega) 2
  have hqSqSubOneOdd : Odd (q ^ 2 - 1) :=
    Nat.Even.sub_odd hqSqPos hqSqEven odd_one
  have houterOdd : Odd ((q ^ 3 + 1) * (q ^ 2 - 1)) :=
    hqCubeEven.add_one.mul hqSqSubOneOdd
  have hqFactor : (q + 1) * (q - 1) = q ^ 2 - 1 := by
    have hqLeSq : q ≤ q * q := by nlinarith
    rw [add_mul, one_mul, Nat.mul_sub_left_distrib]
    simp only [mul_one, pow_two]
    omega
  have hdenDvdSq : Nat.gcd 3 (q + 1) ∣ q ^ 2 - 1 :=
    dvd_trans (Nat.gcd_dvd_right 3 (q + 1)) ⟨q - 1, hqFactor.symm⟩
  have hdenDvdNumerator : Nat.gcd 3 (q + 1) ∣
      (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) :=
    dvd_mul_of_dvd_right hdenDvdSq ((q ^ 3 + 1) * q ^ 3)
  have hGdvdNumerator : Nat.card G0 ∣
      (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
    rw [hGcard]
    exact Nat.div_dvd_of_dvd hdenDvdNumerator
  obtain ⟨mP, hPstdPower⟩ := IsPGroup.iff_card.mp Pstd.isPGroup'
  have hPstdDvdG : Nat.card Pstd ∣ Nat.card G0 :=
    (Pstd : Subgroup G0).card_subgroup_dvd_card
  have hPstdDvdProduct : Nat.card Pstd ∣
      q ^ 3 * ((q ^ 3 + 1) * (q ^ 2 - 1)) := by
    have := hPstdDvdG.trans hGdvdNumerator
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  have hPstdCoprimeOuter :
      Nat.Coprime (Nat.card Pstd) ((q ^ 3 + 1) * (q ^ 2 - 1)) := by
    rw [hPstdPower]
    exact Nat.Coprime.pow_left mP houterOdd.coprime_two_left
  have hPstdDvdCube : Nat.card Pstd ∣ q ^ 3 :=
    hPstdCoprimeOuter.dvd_of_dvd_mul_right hPstdDvdProduct
  have hCubeDvdPstd : q ^ 3 ∣ Nat.card Pstd := by
    rw [← hRcard]
    exact Subgroup.card_dvd_of_le hRlePstd
  have hPstdCard : Nat.card Pstd = q ^ 3 :=
    Nat.dvd_antisymm hPstdDvdCube hCubeDvdPstd
  have hReqPstd : R = (Pstd : Subgroup G0) :=
    Subgroup.eq_of_le_of_card_ge hRlePstd (by rw [hPstdCard, hRcard])
  obtain ⟨Pin, hP0lePin⟩ := hP0p.exists_le_sylow
  have hPinCard : Nat.card Pin = q ^ 3 := by
    calc
      Nat.card Pin = Nat.card Pstd := Nat.card_congr (Sylow.equiv Pin Pstd)
      _ = q ^ 3 := hPstdCard
  have hP0eq : P0 = (Pin : Subgroup G0) :=
    Subgroup.eq_of_le_of_card_ge hP0lePin (by rw [hPinCard, hP0card])
  subst P0
  have hcardUnits : Nat.card Eˣ = q ^ 2 - 1 := by
    rw [Nat.card_units, hEcard]
  have hqOneDvd : q + 1 ∣ q ^ 2 - 1 := by
    rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by
      simpa [mul_comm] using Nat.sq_sub_sq q 1]
    exact dvd_mul_left (q + 1) (q - 1)
  have hNormRootsCard : Nat.card (rootsOfUnity (q + 1) E) = q + 1 := by
    letI : IsCyclic Eˣ := inferInstance
    rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker,
      hcardUnits, Nat.gcd_eq_right hqOneDvd]
  have hThreeLt : 3 < Nat.card (rootsOfUnity (q + 1) E) := by
    rw [hNormRootsCard]
    omega
  letI : IsCyclic (rootsOfUnity (q + 1) E) := inferInstance
  obtain ⟨k, hkThree⟩ :=
    exists_pow_ne_one_of_isCyclic (G := rootsOfUnity (q + 1) E)
      (by decide : (3 : ℕ) ≠ 0) hThreeLt
  let ku : Eˣ := (k : Eˣ)
  have hkqUnits : ku ^ (q + 1) = 1 :=
    (mem_rootsOfUnity (q + 1) (k : Eˣ)).mp k.property
  have hkq : (ku : E) ^ (q + 1) = 1 := by
    simpa using congrArg Units.val hkqUnits
  rcases hTcoordSurjective ku with ⟨h, M, hM, hMproj⟩
  have hMtorus : M = External.hermitianTorusGL J ku := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change (M : Matrix (Fin 3) (Fin 3) E) i j =
      (External.hermitianTorusGL J ku : Matrix (Fin 3) (Fin 3) E) i j
    rw [hM, External.hermitianTorusGL_val]
    rfl
  have hhTorus : (h : G0) = External.hermitianTorusPSU J hJstandard ku := by
    apply Subtype.ext
    exact hMproj.trans (by rw [hMtorus, External.hermitianTorusPSU_val])
  have hTorusNe : External.hermitianTorusPSU J hJstandard ku ≠ 1 := by
    intro htorus
    have hpgl : Matrix.ProjGenLinGroup.mk
        (External.hermitianTorusGL J ku) = 1 :=
      congrArg Subtype.val htorus
    have hcenter : External.hermitianTorusGL J ku ∈
        Subgroup.center (GL (Fin 3) E) := by
      rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hpgl
    rcases Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
        hcenter with ⟨c, hc⟩
    have h00 := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A 0 0) hc
    have h11 := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A 1 1) hc
    have h22 := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A 2 2) hc
    rw [External.hermitianTorusGL_val] at h00 h11 h22
    simp [External.hermitianTorusMatrix, Matrix.scalar_apply] at h00 h11 h22
    have hd0 : (J.conj (ku : E))⁻¹ = (ku : E) := h00.symm.trans h22
    have hmid : J.conj (ku : E) * (ku : E)⁻¹ = (ku : E) :=
      h11.symm.trans h22
    have hku0 : (ku : E) ≠ 0 := Units.ne_zero ku
    have hconj0 : J.conj (ku : E) ≠ 0 := (map_ne_zero J.conj).mpr hku0
    have hnorm : J.conj (ku : E) * (ku : E) = 1 := by
      have h := congrArg (fun x : E => J.conj (ku : E) * x) hd0
      simpa [hconj0] using h.symm
    have hsq : J.conj (ku : E) = (ku : E) * (ku : E) := by
      have h := congrArg (fun x : E => x * (ku : E)) hmid
      simpa [mul_assoc, hku0] using h
    have hcube : (ku : E) ^ 3 = 1 := by
      calc
        (ku : E) ^ 3 = ((ku : E) * (ku : E)) * (ku : E) := by ring
        _ = J.conj (ku : E) * (ku : E) := by rw [← hsq]
        _ = 1 := hnorm
    apply hkThree
    apply Subtype.ext
    apply Units.ext
    simpa [ku] using hcube
  have hhNe : h ≠ 1 := by
    intro hh
    apply hTorusNe
    calc
      External.hermitianTorusPSU J hJstandard ku = (h : G0) := hhTorus.symm
      _ = 1 := congrArg (fun x : T => (x : G0)) hh
  have hconjPow : J.conj (ku : E) = (ku : E) ^ q :=
    External.huppert_II_10_4_conj_eq_frobenius
      J q hEcard hfixedCard (ku : E)
  have hnorm : J.conj (ku : E) * (ku : E) = 1 := by
    rw [hconjPow]
    simpa [pow_succ] using hkq
  have hscale : (J.conj (ku : E))⁻¹ * (ku : E)⁻¹ = 1 := by
    rw [← mul_inv_rev, mul_comm, hnorm, inv_one]
  have hhCentralizesCenterR :
      ∀ z : R, z ∈ Subgroup.center R → Commute (h : G0) (z : G0) := by
    intro z hz
    rw [← hCenterReq] at hz
    rcases Subgroup.mem_map.mp hz with ⟨w, hw, hwz⟩
    have hwa : w.1.1 = 0 := hw
    have haction : External.hermitianTorusAction J ku w = w := by
      apply Subtype.ext
      apply Prod.ext
      · change w.1.1 * (ku : E) * (J.conj (ku : E))⁻¹ ^ 2 = w.1.1
        rw [hwa]
        simp
      · change w.1.2 * (J.conj (ku : E))⁻¹ * (ku : E)⁻¹ = w.1.2
        rw [mul_assoc, hscale, mul_one]
    have hmul := External.hermitianTorusPSU_mul_unipotent
      J hJstandard ku w
    rw [haction] at hmul
    change (h : G0) * (z : G0) = (z : G0) * (h : G0)
    calc
      (h : G0) * (z : G0) =
          External.hermitianTorusPSU J hJstandard ku * rootPSU w := by
        rw [← hhTorus, ← hcoordEqRoot w]
        exact congrArg (fun x : R => ((h : G0) * (x : G0))) hwz.symm
      _ = rootPSU w * External.hermitianTorusPSU J hJstandard ku := hmul
      _ = (z : G0) * (h : G0) := by
        rw [← hhTorus, ← hcoordEqRoot w]
        exact congrArg (fun x : R => ((x : G0) * (h : G0))) hwz
  have hhNormR : (h : G0) ∈ Subgroup.normalizer (R : Set G0) :=
    hUnormalizesR (hTleU h.property)
  have hhNotR : (h : G0) ∉ R := by
    intro hhR
    have hhBot : (h : G0) ∈ (⊥ : Subgroup G0) := by
      rw [← hRTinf]
      exact ⟨hhR, h.property⟩
    exact hhNe (Subtype.ext (by simpa using hhBot))
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G0 Pin Pstd
  let g : G0 := c⁻¹ * (h : G0) * c
  have hhNormPstd : (h : G0) ∈
      Subgroup.normalizer (Pstd : Set G0) := by
    simpa [hReqPstd] using hhNormR
  have hgSmul : g • Pin = Pin := by
    calc
      g • Pin = c⁻¹ • ((h : G0) • (c • Pin)) := by simp [g, mul_smul]
      _ = c⁻¹ • ((h : G0) • Pstd) := by rw [hc]
      _ = c⁻¹ • Pstd := by
        rw [Sylow.smul_eq_iff_mem_normalizer.mpr hhNormPstd]
      _ = Pin := by rw [← hc, inv_smul_smul]
  have hgNorm : g ∈ Subgroup.normalizer (Pin : Set G0) :=
    Sylow.smul_eq_iff_mem_normalizer.mp hgSmul
  have hgNotP : g ∉ (Pin : Subgroup G0) := by
    intro hgP
    have hcg : c * g * c⁻¹ ∈ (Pstd : Subgroup G0) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact ⟨g, hgP, by simp [MulAut.conj_apply]⟩
    apply hhNotR
    rw [hReqPstd]
    have hcgEq : c * g * c⁻¹ = (h : G0) := by
      dsimp [g]
      group
    rw [hcgEq] at hcg
    exact hcg
  refine ⟨g, hgNotP, hgNorm, ?_⟩
  intro z hz
  have hzcMem : c * (z : G0) * c⁻¹ ∈ (Pstd : Subgroup G0) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact ⟨(z : G0), z.property, by simp [MulAut.conj_apply]⟩
  let zc : Pstd := ⟨c * (z : G0) * c⁻¹, hzcMem⟩
  have hzcCenter : zc ∈ Subgroup.center Pstd := by
    refine (Subgroup.mem_center_iff (G := Pstd) (z := zc)).2 ?_
    intro y
    have hyMem : (y : G0) ∈ ((c • Pin : Sylow 2 G0) : Subgroup G0) := by
      rw [hc]
      exact y.property
    rw [Sylow.coe_subgroup_smul] at hyMem
    rcases hyMem with ⟨x, hxP, hxy⟩
    let xP : Pin := ⟨x, hxP⟩
    have hzx := (Subgroup.mem_center_iff.mp hz) xP
    apply Subtype.ext
    change (y : G0) * (c * (z : G0) * c⁻¹) =
      (c * (z : G0) * c⁻¹) * (y : G0)
    have hxy' : c * x * c⁻¹ = (y : G0) := by
      simpa [MulAut.conj_apply] using hxy
    rw [← hxy']
    have hzxG : x * (z : G0) = (z : G0) * x := congrArg Subtype.val hzx
    calc
      c * x * c⁻¹ * (c * (z : G0) * c⁻¹) =
          c * (x * (z : G0)) * c⁻¹ := by group
      _ = c * ((z : G0) * x) * c⁻¹ := by rw [hzxG]
      _ = c * (z : G0) * c⁻¹ * (c * x * c⁻¹) := by group
  have hhCentralizesCenterPstd :
      ∀ z : Pstd, z ∈ Subgroup.center Pstd →
        Commute (h : G0) (z : G0) := by
    rw [hReqPstd] at hhCentralizesCenterR
    exact hhCentralizesCenterR
  have hhComm := hhCentralizesCenterPstd zc hzcCenter
  change g * (z : G0) = (z : G0) * g
  calc
    g * (z : G0) =
        c⁻¹ * ((h : G0) * (c * (z : G0) * c⁻¹)) * c := by
      simp [g]
      group
    _ = c⁻¹ * ((c * (z : G0) * c⁻¹) * (h : G0)) * c := by
      rw [hhComm.eq]
    _ = (z : G0) * g := by
      simp [g]
      group

private theorem semilinear_map_isInvariant
    {K P E : Type u} [Group K] [Group P] [Group E]
    (kAction : MulDistribMulAction K E)
    (pAction : MulDistribMulAction P E)
    (conj : P → K → K)
    (hsem : ∀ c k x,
      @SMul.smul K E kAction.toSMul k
          (@SMul.smul P E pAction.toSMul c x) =
        @SMul.smul P E pAction.toSMul c
          (@SMul.smul K E kAction.toSMul (conj c k) x))
    (c : P) (T : Subgroup E)
    (hT : @IsXInvariantSubgroup K E _ _ kAction T) :
    @IsXInvariantSubgroup K E _ _ kAction
      (T.map ((@MulDistribMulAction.toMonoidEnd P E _ _ pAction) c)) := by
  letI : MulDistribMulAction K E := kAction
  letI : MulDistribMulAction P E := pAction
  have hpreserve : ∀ k : K, ∀ x : E,
      x ∈ T.map ((@MulDistribMulAction.toMonoidEnd P E _ _ pAction) c) →
        k • x ∈ T.map ((@MulDistribMulAction.toMonoidEnd P E _ _ pAction) c) := by
    intro k x hx
    change x ∈ c • T at hx
    change k • x ∈ c • T
    rw [Subgroup.pointwise_smul_def] at hx ⊢
    rcases hx with ⟨y, hyT, rfl⟩
    refine ⟨conj c k • y, (hT (conj c k) y).mp hyT, ?_⟩
    exact (hsem c k y).symm
  intro k x
  constructor
  · exact hpreserve k x
  · intro hkx
    have hback := hpreserve k⁻¹ (k • x) hkx
    rw [inv_smul_smul] at hback
    exact hback

private def are_equivariantly_isomorphic
    {K E : Type u} [Group K] [Group E]
    (action : MulDistribMulAction K E)
    (U V : Subgroup E)
    (hU : @IsXInvariantSubgroup K E _ _ action U) : Prop :=
  ∃ e : U ≃* V, ∀ k : K, ∀ u : U,
    ((e ⟨@SMul.smul K E action.toSMul k (u : E),
      (hU k (u : E)).mp u.property⟩ : V) : E) =
      @SMul.smul K E action.toSMul k ((e u : V) : E)

private theorem card_map_action
    {P E : Type*} [Group P] [Group E]
    (pAction : MulDistribMulAction P E) (c : P) (T : Subgroup E) :
    Nat.card
      (T.map ((@MulDistribMulAction.toMonoidEnd P E _ _ pAction) c)) =
      Nat.card T :=
  Subgroup.card_map_of_injective
    (K := T)
    (f := (@MulDistribMulAction.toMonoidEnd P E _ _ pAction) c)
    ((@MulDistribMulAction.toMulEquiv P E _ _ pAction c).injective)


private theorem subgroup_normal_of_isMulCommutative
    {E : Type*} [Group E] (hcomm : IsMulCommutative E)
    (T : Subgroup E) : T.Normal := by
  constructor
  intro n hn g
  have hgn : g * n = n * g := hcomm.is_comm.comm g n
  have heq : g * n * g⁻¹ = n := by
    rw [hgn, mul_assoc, mul_inv_cancel, mul_one]
  rw [heq]
  exact hn

private theorem isXInvariantSubgroup_of_pointwise_smul_eq
    {P E : Type u} [Group P] [Group E] [MulDistribMulAction P E]
    (T : Subgroup E) (hfix : ∀ c : P, c • T = T) :
    IsXInvariantSubgroup P T := by
  intro c x
  constructor
  · intro hx
    have hmem : c • x ∈ c • T :=
      Subgroup.smul_mem_pointwise_smul x c T hx
    simpa [hfix c] using hmem
  · intro hcx
    have hmem : c⁻¹ • (c • x) ∈ c⁻¹ • T :=
      Subgroup.smul_mem_pointwise_smul (c • x) c⁻¹ T hcx
    simpa [smul_smul, hfix c⁻¹] using hmem

set_option maxHeartbeats 800000 in
private theorem cubic_fixed_root
    {G : Type u} [Group G] [Finite G]
    (K P S : Subgroup G) [Subgroup.Normalizes K S]
    [Subgroup.Normalizes P S]
    (s : S) (hs : IsInvolution s)
    (hPcentralizes : P ≤ Subgroup.centralizer ({(s : G)} : Set G))
    (hSuzuki : IsSuzukiTwoGroup S)
    (hKregular : ActionRegularOn K S (involutions S))
    (hKcard : Nat.card K = Nat.card (Subgroup.center S) - 1)
    (kAction : MulDistribMulAction K (S ⧸ Subgroup.center S))
    (pAction : MulDistribMulAction P (S ⧸ Subgroup.center S))
    (hKquotient : ∀ k : K, ∀ x : S,
      @SMul.smul K (S ⧸ Subgroup.center S) kAction.toSMul k
          (QuotientGroup.mk' (Subgroup.center S) x) =
        QuotientGroup.mk' (Subgroup.center S) (k • x))
    (hPquotient : ∀ c : P, ∀ x : S,
      @SMul.smul P (S ⧸ Subgroup.center S) pAction.toSMul c
          (QuotientGroup.mk' (Subgroup.center S) x) =
        QuotientGroup.mk' (Subgroup.center S) (c • x))
    (T : Subgroup (S ⧸ Subgroup.center S))
    (hTinv : @IsXInvariantSubgroup K (S ⧸ Subgroup.center S)
      _ _ kAction T)
    (hTcard : Nat.card T = Nat.card (Subgroup.center S))
    (hTPinv : ∀ c : P, ∀ x : S ⧸ Subgroup.center S,
      x ∈ T ↔ @SMul.smul P (S ⧸ Subgroup.center S)
        pAction.toSMul c x ∈ T)
    (p : ℕ) (hp : Nat.Prime p) (hPcard : Nat.card P = p)
    (hpNotDvdCenter : ¬ p ∣ Nat.card (Subgroup.center S)) :
    ∃ r : S,
      QuotientGroup.mk' (Subgroup.center S) r ∈ T ∧
        ((r : G) ^ 2 = (s : G)) ∧
          (r : G) ∈ Subgroup.centralizer (P : Set G) := by
  classical
  let Z := Subgroup.center S
  let E := S ⧸ Z
  letI : MulDistribMulAction K E := kAction
  letI : MulDistribMulAction P E := pAction
  let Plane : Subgroup S := T.comap (QuotientGroup.mk' Z)
  have hPlaneInv : IsInvariant P S Plane := by
    refine ⟨?_⟩
    intro c x
    change QuotientGroup.mk' Z x ∈ T ↔
      QuotientGroup.mk' Z (c • x) ∈ T
    have hmem := hTPinv c (QuotientGroup.mk' Z x)
    rw [hPquotient c x] at hmem
    exact hmem
  letI : IsInvariant P S Plane := hPlaneInv
  let Root : SubMulAction P Plane :=
    { carrier := {r : Plane | (r : S) ^ 2 = s}
      smul_mem' := by
        intro c r hr
        change (c • (r : Plane) : S) ^ 2 = s
        rw [← smul_pow', hr]
        apply Subtype.ext
        change (c : G) * (s : G) * (c : G)⁻¹ = (s : G)
        have hcComm : (c : G) * (s : G) = (s : G) * (c : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp
            (hPcentralizes c.property)
        rw [hcComm]
        simp }
  have hRootCard : Nat.card Root = Nat.card (Subgroup.center S) := by
    have hcard := cubic_line_root_card hSuzuki hKregular hKcard
      kAction hKquotient T hTinv hTcard s hs
    let rootEquiv : Root ≃
        {x : Plane // ((x : Plane) : S) ^ 2 = s} :=
      { toFun := fun x ↦ ⟨x, x.property⟩
        invFun := fun x ↦ ⟨x, x.property⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    calc
      Nat.card Root = Nat.card {x : Plane // ((x : Plane) : S) ^ 2 = s} :=
        Nat.card_congr rootEquiv
      _ = Nat.card (Subgroup.center S) := by
        simpa [Plane, Z, E] using hcard
  have hpNotDvdRoot : ¬ p ∣ Nat.card Root := by
    rw [hRootCard]
    exact hpNotDvdCenter
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hPpgroup : IsPGroup p P :=
    IsPGroup.of_card (n := 1) (by simpa using hPcard)
  rcases hPpgroup.nonempty_fixed_point_of_prime_not_dvd_card
      Root hpNotDvdRoot with ⟨r, hrFixed⟩
  have hrFix : ∀ c : P, c • r = r :=
    MulAction.mem_fixedPoints.mp hrFixed
  refine ⟨((r : Plane) : S), r.1.property, ?_, ?_⟩
  · exact congrArg (fun z : S => (z : G)) r.property
  · rw [Subgroup.mem_centralizer_iff]
    intro c hcP
    let cP : P := ⟨c, hcP⟩
    have hfixPlane : cP • (r : Plane) = (r : Plane) :=
      congrArg Subtype.val (hrFix cP)
    have hfixS : cP • ((r : Plane) : S) = ((r : Plane) : S) :=
      congrArg Subtype.val hfixPlane
    have hfixG : c * (((r : Plane) : S) : G) * c⁻¹ =
        (((r : Plane) : S) : G) := by
      simpa only [
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
          congrArg (fun z : S => (z : G)) hfixS
    have hmul := congrArg (fun z : G => z * c) hfixG
    simpa [mul_assoc] using hmul


set_option maxHeartbeats 800000 in
private theorem cubic_fixed_roots_contradiction
    {G : Type u} [Group G]
    (P Q S : Subgroup G) (s : G) (hSQ : S = Q)
    (hSuzuki : IsSuzukiTwoGroup S)
    (hCXtypeA : IsSuzukiTwoTypeA
      (Subgroup.centralizer (P : Set G) ⊓ Q))
    (X Y : Subgroup (S ⧸ Subgroup.center S)) (hXYinf : X ⊓ Y = ⊥)
    (x y : S)
    (hxX : QuotientGroup.mk' (Subgroup.center S) x ∈ X)
    (hyY : QuotientGroup.mk' (Subgroup.center S) y ∈ Y)
    (hxsq : (x : G) ^ 2 = s) (hysq : (y : G) ^ 2 = s)
    (hxCent : (x : G) ∈ Subgroup.centralizer (P : Set G))
    (hyCent : (y : G) ∈ Subgroup.centralizer (P : Set G))
    (hsInv : IsInvolution s) : False := by
  classical
  let Z := Subgroup.center S
  let CX := Subgroup.centralizer (P : Set G) ⊓ Q
  have hxS : (x : G) ∈ S := x.property
  have hyS : (y : G) ∈ S := y.property
  let xCX : CX := ⟨x, hxCent, by rw [← hSQ]; exact hxS⟩
  let yCX : CX := ⟨y, hyCent, by rw [← hSQ]; exact hyS⟩
  have hxySqCX : xCX ^ 2 = yCX ^ 2 := by
    apply Subtype.ext
    exact hxsq.trans hysq.symm
  have hxyQuot := typeA_same_square_quotient_eq hCXtypeA xCX yCX hxySqCX
  let zCX : CX := xCX⁻¹ * yCX
  have hzCXCenter : zCX ∈ Subgroup.center CX := by
    apply (QuotientGroup.eq_one_iff zCX).mp
    calc
      QuotientGroup.mk' (Subgroup.center CX) zCX =
          (QuotientGroup.mk' (Subgroup.center CX) xCX)⁻¹ *
            QuotientGroup.mk' (Subgroup.center CX) yCX := by
        simp [zCX]
      _ = 1 := by
        rw [hxyQuot]
        exact inv_mul_cancel _
  have hyEq : yCX = xCX * zCX := by simp [zCX]
  have hzSqCX : zCX ^ 2 = 1 := by
    have hcomm : Commute xCX zCX :=
      Subgroup.mem_center_iff.mp hzCXCenter xCX
    have hsq := congrArg (fun z : CX => xCX⁻¹ ^ 2 * z)
      (show (xCX * zCX) ^ 2 = xCX ^ 2 by rw [← hyEq, hxySqCX])
    simpa [hcomm.mul_pow, mul_assoc] using hsq
  let zS : S := ⟨((zCX : CX) : G), by
    rw [hSQ]
    exact zCX.property.2⟩
  have hzCenterS : zS ∈ Z := by
    by_cases hzOne : zS = 1
    · simp [zS, hzOne]
    · have hzInv : zS ∈ involutions S :=
        ⟨hzOne, Subtype.ext (congrArg (fun z : CX => (z : G)) hzSqCX)⟩
      rw [(higmanTheorem_involutions_center hSuzuki).1] at hzInv
      exact hzInv.1
  have hquotEq : QuotientGroup.mk' Z (⟨x, hxS⟩ : S) =
      QuotientGroup.mk' Z (⟨y, hyS⟩ : S) := by
    have hyEqG := congrArg (fun z : CX => (z : G)) hyEq
    have hzOne : QuotientGroup.mk' Z zS = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hzCenterS
    have hyx : QuotientGroup.mk' Z (⟨y, hyS⟩ : S) =
        QuotientGroup.mk' Z (⟨x, hxS⟩ : S) := by
      calc
        QuotientGroup.mk' Z (⟨y, hyS⟩ : S) =
            QuotientGroup.mk' Z ((⟨x, hxS⟩ : S) * zS) := by
          apply congrArg (QuotientGroup.mk' Z)
          apply Subtype.ext
          exact hyEqG
        _ = QuotientGroup.mk' Z (⟨x, hxS⟩ : S) := by
          rw [map_mul, hzOne, mul_one]
    exact hyx.symm
  have hxInf : QuotientGroup.mk' Z (⟨x, hxS⟩ : S) ∈ X ⊓ Y :=
    ⟨hxX, by simpa [hquotEq] using hyY⟩
  rw [hXYinf] at hxInf
  have hxQuotOne : QuotientGroup.mk' Z (⟨x, hxS⟩ : S) = 1 := by
    simpa using hxInf
  have hxCenterS : (⟨x, hxS⟩ : S) ∈ Z :=
    (QuotientGroup.eq_one_iff _).mp hxQuotOne
  have hxSqOne : (⟨x, hxS⟩ : S) ^ 2 = 1 := by
    have hcenterSq := (higmanTheorem_involutions_center hSuzuki).2
      ⟨⟨x, hxS⟩, hxCenterS⟩
    exact congrArg (fun z : Subgroup.center S => (z : S)) hcenterSq
  exact hsInv.ne_one <| by
    calc
      s = x ^ 2 := hxsq.symm
      _ = 1 := congrArg (fun z : S => (z : G)) hxSqOne


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem invariant_line_through_equivariant_summands
    {K E : Type u} [Group K] [Finite K] [Group E] [Finite E]
    [MulDistribMulAction K E]
    (q : ℕ) (hKcard : Nat.card K = q - 1)
    (U Vline : Subgroup E)
    (hUinv : IsXInvariantSubgroup K U)
    (hVinv : IsXInvariantSubgroup K Vline)
    (hUcardq : Nat.card U = q)
    (hVcardq : Nat.card Vline = q)
    (hUVinf : U ⊓ Vline = ⊥)
    (hEcomm : IsMulCommutative E)
    (hKcomm : IsMulCommutative K)
    (hKfixedFree :
      ∀ k : K, k ≠ 1 → ∀ x : E, k • x = x → x = 1)
    (eUV : U ≃* Vline)
    (heUV : ∀ (k : K) (u : U),
      ((eUV ⟨k • (u : E), (hUinv k (u : E)).mp u.property⟩ : Vline) : E) =
        k • ((eUV u : Vline) : E))
    (rbar u v : E) (huU : u ∈ U) (hvV : v ∈ Vline)
    (huv : u * v = rbar) :
    ∃ X : Subgroup E,
      IsXInvariantSubgroup K X ∧ Nat.card X = q ∧ rbar ∈ X := by
  letI : U.Normal := subgroup_normal_of_isMulCommutative hEcomm U
  letI : Vline.Normal := subgroup_normal_of_isMulCommutative hEcomm Vline
  let uU : U := ⟨u, huU⟩
  let vV : Vline := ⟨v, hvV⟩
  by_cases huOne : u = 1
  · refine ⟨Vline, hVinv, hVcardq, ?_⟩
    rw [← huv, huOne, one_mul]
    exact hvV
  by_cases hvOne : v = 1
  · refine ⟨U, hUinv, hUcardq, ?_⟩
    rw [← huv, hvOne, mul_one]
    exact huU
  have huUNe : uU ≠ 1 := by
    intro h
    exact huOne (congrArg Subtype.val h)
  have hvVNe : vV ≠ 1 := by
    intro h
    exact hvOne (congrArg Subtype.val h)
  have heuNe : ((eUV uU : Vline) : E) ≠ 1 := by
    intro h
    apply huUNe
    apply eUV.injective
    apply Subtype.ext
    simpa using h
  let orbitWithOne : Option K → Vline
    | none => 1
    | some l =>
        ⟨l • ((eUV uU : Vline) : E),
          (hVinv l ((eUV uU : Vline) : E)).mp (eUV uU).property⟩
  have horbitInjective : Function.Injective orbitWithOne := by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some l =>
            exfalso
            apply heuNe
            have hla : l • ((eUV uU : Vline) : E) = 1 := by
              exact congrArg Subtype.val hij.symm
            have hback := congrArg (fun z : E => l⁻¹ • z) hla
            simpa [smul_smul] using hback
    | some k =>
        cases j with
        | none =>
            exfalso
            apply heuNe
            have hka : k • ((eUV uU : Vline) : E) = 1 :=
              congrArg Subtype.val hij
            have hback := congrArg (fun z : E => k⁻¹ • z) hka
            simpa [smul_smul] using hback
        | some l =>
            have hkl : k • ((eUV uU : Vline) : E) =
                l • ((eUV uU : Vline) : E) :=
              congrArg Subtype.val hij
            have hfix : (l⁻¹ * k) • ((eUV uU : Vline) : E) =
                ((eUV uU : Vline) : E) := by
              calc
                (l⁻¹ * k) • ((eUV uU : Vline) : E) =
                    l⁻¹ • (k • ((eUV uU : Vline) : E)) := by
                  rw [mul_smul]
                _ = l⁻¹ • (l • ((eUV uU : Vline) : E)) := by
                  rw [hkl]
                _ = ((eUV uU : Vline) : E) := by
                  simp [smul_smul]
            have hactor : l⁻¹ * k = 1 := by
              by_contra hne
              exact heuNe
                (hKfixedFree (l⁻¹ * k) hne
                  ((eUV uU : Vline) : E) hfix)
            have hEq : k = l := by
              have := congrArg (fun z : K => l * z) hactor
              simpa [mul_assoc] using this
            exact congrArg some hEq
  have horbitCard : Nat.card (Option K) = Nat.card Vline := by
    calc
      Nat.card (Option K) = Nat.card K + 1 := by simp
      _ = q := by
        have hqPos : 0 < q := by
          rw [← hVcardq]
          exact Nat.card_pos
        omega
      _ = Nat.card Vline := hVcardq.symm
  have horbitSurjective : Function.Surjective orbitWithOne :=
    ((Nat.bijective_iff_injective_and_card orbitWithOne).2
      ⟨horbitInjective, horbitCard⟩).2
  obtain ⟨k, hkv⟩ : ∃ k : K,
      (vV : E) = k • ((eUV uU : Vline) : E) := by
    rcases horbitSurjective vV with ⟨i, hi⟩
    cases i with
    | none =>
        exfalso
        apply hvVNe
        exact Subtype.ext (congrArg Subtype.val hi).symm
    | some k =>
        exact ⟨k, (congrArg Subtype.val hi).symm⟩
  let graphPoint : U → E := fun a =>
    (a : E) * k • ((eUV a : Vline) : E)
  let X : Subgroup E :=
    { carrier := Set.range graphPoint
      one_mem' := ⟨1, by simp [graphPoint]⟩
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        refine ⟨a * b, ?_⟩
        dsimp [graphPoint]
        rw [map_mul eUV, Subgroup.coe_mul, smul_mul']
        rw [mul_assoc (a : E) (k • ((eUV a : Vline) : E))
              ((b : E) * k • ((eUV b : Vline) : E)),
          ← mul_assoc (k • ((eUV a : Vline) : E)) (b : E)
            (k • ((eUV b : Vline) : E)),
          hEcomm.is_comm.comm (k • ((eUV a : Vline) : E)) (b : E),
          mul_assoc]
        simp only [mul_assoc]
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        refine ⟨a⁻¹, ?_⟩
        dsimp [graphPoint]
        rw [mul_inv_rev, map_inv eUV, Subgroup.coe_inv, smul_inv']
        exact hEcomm.is_comm.comm _ _ }
  have hgraphPointInjective : Function.Injective graphPoint := by
    intro a b hab
    have hkaV : k • ((eUV a : Vline) : E) ∈ Vline :=
      (hVinv k ((eUV a : Vline) : E)).mp (eUV a).property
    have hkbV : k • ((eUV b : Vline) : E) ∈ Vline :=
      (hVinv k ((eUV b : Vline) : E)).mp (eUV b).property
    have hq := congrArg (QuotientGroup.mk' Vline) hab
    change QuotientGroup.mk' Vline
        ((a : E) * k • ((eUV a : Vline) : E)) =
      QuotientGroup.mk' Vline
        ((b : E) * k • ((eUV b : Vline) : E)) at hq
    have hqa : QuotientGroup.mk' Vline
        (k • ((eUV a : Vline) : E)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hkaV
    have hqb : QuotientGroup.mk' Vline
        (k • ((eUV b : Vline) : E)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hkbV
    rw [map_mul, hqa, mul_one, map_mul, hqb, mul_one] at hq
    have habV : (a : E) / (b : E) ∈ Vline :=
      QuotientGroup.eq_iff_div_mem.mp hq
    have habU : (a : E) / (b : E) ∈ U :=
      U.div_mem a.property b.property
    have habBot : (a : E) / (b : E) ∈ (⊥ : Subgroup E) := by
      rw [← hUVinf]
      exact ⟨habU, habV⟩
    have habOne : (a : E) / (b : E) = 1 := by
      simpa using habBot
    apply Subtype.ext
    exact div_eq_one.mp habOne
  have hXinvGraph : IsXInvariantSubgroup K X := by
    have hpreserve : ∀ l : K, ∀ x : E, x ∈ X → l • x ∈ X := by
      intro l x hx
      rcases hx with ⟨a, rfl⟩
      let la : U :=
        ⟨l • (a : E), (hUinv l (a : E)).mp a.property⟩
      refine ⟨la, ?_⟩
      dsimp [graphPoint, la]
      rw [smul_mul']
      have he : ((eUV la : Vline) : E) =
          l • ((eUV a : Vline) : E) := by
        simpa only [la] using heUV l a
      have hsecond : l • (k • ((eUV a : Vline) : E)) =
          k • ((eUV la : Vline) : E) := by
        calc
          l • (k • ((eUV a : Vline) : E)) =
              (l * k) • ((eUV a : Vline) : E) := by
            rw [smul_smul]
          _ = (k * l) • ((eUV a : Vline) : E) := by
            rw [hKcomm.is_comm.comm l k]
          _ = k • (l • ((eUV a : Vline) : E)) := by
            rw [smul_smul]
          _ = k • ((eUV la : Vline) : E) := by
            rw [he]
      rw [hsecond]
    intro l x
    constructor
    · exact hpreserve l x
    · intro hlx
      have hback := hpreserve l⁻¹ (l • x) hlx
      simpa [smul_smul] using hback
  let toX : U → X := fun a =>
    ⟨graphPoint a, ⟨a, rfl⟩⟩
  have htoXInjective : Function.Injective toX := by
    intro a b hab
    apply hgraphPointInjective
    exact congrArg Subtype.val hab
  have htoXSurjective : Function.Surjective toX := by
    rintro ⟨x, hx⟩
    rcases hx with ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  have hXcardGraph : Nat.card X = q := by
    calc
      Nat.card X = Nat.card U :=
        Nat.card_congr
          (Equiv.ofBijective toX
            ⟨htoXInjective, htoXSurjective⟩).symm
      _ = q := hUcardq
  have hrbarXGraph : rbar ∈ X := by
    refine ⟨uU, ?_⟩
    dsimp [graphPoint]
    calc
      (uU : E) * k • ((eUV uU : Vline) : E) =
          (uU : E) * (vV : E) := by
        rw [hkv]
      _ = rbar := huv
  exact ⟨X, hXinvGraph, hXcardGraph, hrbarXGraph⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem cubic_order_five_contradiction
    {G : Type u} {Ω : Type v} [Group G] [Finite G]
    [MulAction G Ω] [Finite Ω]
    (H D Q K V Q0 S : Subgroup G) (t s : G)
    [Subgroup.Normalizes K S]
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hKleD : K ≤ D)
    (hVdef : V = peterfalviV D t)
    (hQ0leQ : Q0 ≤ Q)
    (hQ0def : ∀ x : G, x ∈ Q0 ↔
      x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hsH : s ∈ H) (hsInv : IsInvolution s)
    (hsConj : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)
    (hSQ : S = Q)
    (hVleD : V ≤ D)
    (hDnormS : D ≤ Subgroup.normalizer (S : Set G))
    (hKnormalD : (K.subgroupOf D).Normal)
    (hKcyclic : IsCyclic K) (hKfaithful : FaithfulSMul K S)
    (hKregular : ActionRegularOn K S (involutions S))
    (hSuzuki : IsSuzukiTwoGroup S)
    (hcardCube : Nat.card S = Nat.card (Subgroup.center S) ^ 3) :
    ∀ (P : Subgroup G) (p : ℕ),
      P ≤ V → Nat.Prime p → Nat.card P = p →
        IsSuzukiTwoTypeA (Subgroup.centralizer (P : Set G) ⊓ Q) → False := by
  classical
  intro P p hPV hp hPcard hCXtypeA
  let Z := Subgroup.center S
  let E := S ⧸ Z
  let q := Nat.card Z
  have hsQ0 : s ∈ Q0 :=
    (hQ0def s).mpr
      (Or.inr ⟨hsH, hsInv⟩)
  have hsS : s ∈ S := by
    rw [hSQ]
    exact hQ0leQ hsQ0
  let sS : S := ⟨s, hsS⟩
  have hsSInv : IsInvolution sS :=
    ⟨fun h => hsInv.ne_one
        (congrArg (fun z : S => (z : G)) h),
      Subtype.ext hsInv.sq_eq_one⟩
  have hSpgroup : IsPGroup 2 S := by
    rcases hSuzuki.1 with ⟨m, hm⟩
    exact IsPGroup.of_card (by simpa using hm)
  have hZpgroup : IsPGroup 2 Z := hSpgroup.to_subgroup Z
  obtain ⟨n, hqPow⟩ := hZpgroup.exists_card_eq
  have hn : n ≠ 0 := by
    intro hn0
    subst n
    have hqOne : q = 1 := by simpa [q] using hqPow
    have hsCenter : sS ∈ Z := by
      have hsMem : sS ∈ involutions S := hsSInv
      rw [(higmanTheorem_involutions_center hSuzuki).1] at hsMem
      exact hsMem.1
    have hZne : Z ≠ ⊥ := by
      intro hbot
      have hsOne : sS = 1 := by
        have : sS ∈ (⊥ : Subgroup S) := by simpa [hbot] using hsCenter
        simpa using this
      exact hsSInv.ne_one hsOne
    exact (Z.one_lt_card_iff_ne_bot.mpr hZne).ne' hqOne
  have hqTwo : 2 ≤ q := by
    change 2 ≤ Nat.card Z
    rw [hqPow]
    exact Nat.one_lt_pow hn (by norm_num)
  have hKcard : Nat.card K = q - 1 := by
    let Inv : Type u := {x : S // x ∈ involutions S}
    let orbit : K → Inv := fun k => ⟨k • sS, hKregular.1 sS hsSInv k⟩
    have horbitBij : Function.Bijective orbit := by
      constructor
      · intro k l hkl
        have hval : k • sS = l • sS := congrArg Subtype.val hkl
        rcases hKregular.2 sS hsSInv (k • sS)
            (hKregular.1 sS hsSInv k) with ⟨a, _ha, huniq⟩
        exact (huniq k rfl).trans (huniq l hval).symm
      · rintro ⟨x, hx⟩
        rcases hKregular.2 sS hsSInv x hx with ⟨k, hk, _huniq⟩
        exact ⟨k, Subtype.ext hk.symm⟩
    let orbitEquiv : K ≃ Inv := Equiv.ofBijective orbit horbitBij
    let ZSharp : Type u := {z : Z // (z : S) ≠ 1}
    let invCenterEquiv : Inv ≃ ZSharp :=
      { toFun := fun x =>
          ⟨⟨(x : S), by
            have hx : (x : S) ∈ {z : S | z ∈ Subgroup.center S ∧ z ≠ 1} := by
              rw [← (higmanTheorem_involutions_center hSuzuki).1]
              exact x.property
            exact hx.1⟩, x.property.ne_one⟩
        invFun := fun z =>
          ⟨(z : S), by
            rw [(higmanTheorem_involutions_center hSuzuki).1]
            exact ⟨z.1.property, z.property⟩⟩
        left_inv := by intro x; rfl
        right_inv := by intro z; rfl }
    have hZSharpCard : Nat.card ZSharp = q - 1 := by
      letI : Fintype Z := Fintype.ofFinite Z
      letI : Fintype {z : Z // (z : S) = 1} := Fintype.ofFinite _
      letI : Fintype ZSharp := Fintype.ofFinite ZSharp
      have hsplit := Fintype.card_subtype_compl
        (fun z : Z => (z : S) = 1)
      have honeCard : Nat.card {z : Z // (z : S) = 1} = 1 := by
        let oneEquiv : {z : Z // (z : S) = 1} ≃ PUnit.{0} :=
          { toFun := fun _ => PUnit.unit
            invFun := fun _ => ⟨1, rfl⟩
            left_inv := by
              intro z
              apply Subtype.ext
              apply Subtype.ext
              exact z.property.symm
            right_inv := by intro z; cases z; rfl }
        simp
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
        Fintype.card_eq_nat_card, honeCard] at hsplit
      omega
    calc
      Nat.card K = Nat.card Inv := Nat.card_congr orbitEquiv
      _ = Nat.card ZSharp := Nat.card_congr invCenterEquiv
      _ = q - 1 := hZSharpCard
  rcases higmanTheorem_order_center_cube_two_summands
      hSuzuki hKcyclic hKfaithful hKregular hcardCube with
    ⟨quotientAction, U, Vline, hquotientAction,
      hUinv, hVinv, hUcard, hVcard, hUVinf, hUVsup⟩
  letI : IsInvariant K S Z := center_isInvariant
  let defaultKAction : MulDistribMulAction K E :=
    quotientMulDistribMulAction (A := K) (G := S) Z
      (inferInstance : IsInvariant K S Z)
  have hquotientActionEq : quotientAction = defaultKAction := by
    apply MulDistribMulAction.ext
    funext k x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z x
    calc
      @SMul.smul K E quotientAction.toSMul k (QuotientGroup.mk' Z y) =
          QuotientGroup.mk' Z (k • y) := hquotientAction k y
      _ = @SMul.smul K E defaultKAction.toSMul k (QuotientGroup.mk' Z y) := by
        rfl
  subst quotientAction
  letI : MulDistribMulAction K E := defaultKAction
  have hPnormS : P ≤ Subgroup.normalizer (S : Set G) :=
    hPV.trans (hVleD.trans hDnormS)
  letI : Subgroup.Normalizes P S := ⟨hPnormS⟩
  letI : IsInvariant P S Z := center_isInvariant
  let defaultPAction : MulDistribMulAction P E :=
    quotientMulDistribMulAction (A := P) (G := S) Z
      (inferInstance : IsInvariant P S Z)
  letI : MulDistribMulAction P E := defaultPAction
  have hVeq : V = D ⊓ Subgroup.centralizer ({s} : Set G) := by
    calc
      V = peterfalviV D t := hVdef
      _ = D ⊓ Subgroup.centralizer ({s} : Set G) :=
        (PFchapter1section1.proposition_5 H D Q t s
          hA1 hsH hsInv hsConj).1
  have hPcentralizesS : P ≤ Subgroup.centralizer ({s} : Set G) := by
    intro c hc
    have hcV := hPV hc
    rw [hVeq] at hcV
    exact hcV.2
  have hKcomm : IsMulCommutative K := hKcyclic.isMulCommutative
  have hKfixedFree :
      ∀ k : K, k ≠ 1 → ∀ x : E,
        @SMul.smul K E defaultKAction.toSMul k x = x → x = 1 := by
    intro k hk x hkx
    by_contra hxOne
    let A : Subgroup K := Subgroup.zpowers k
    letI : MulDistribMulAction A S := inferInstance
    letI : IsInvariant A S Z := center_isInvariant
    let quotientActionA : MulDistribMulAction A E :=
      quotientMulDistribMulAction (A := A) (G := S) Z
        (inferInstance : IsInvariant A S Z)
    letI : MulDistribMulAction A E := quotientActionA
    have hgenAction :
        (⟨k, Subgroup.mem_zpowers k⟩ : A) • x = x := by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z x
      change QuotientGroup.mk' Z (k • y) = QuotientGroup.mk' Z y
      dsimp [defaultKAction] at hkx
      exact hkx
    have hxFixed : x ∈ fixedPointSubgroup A E := by
      change ∀ a : A, a • x = x
      intro a
      exact smul_eq_self_of_mem_zpowers a.property hgenAction
    have hAcardDvd : Nat.card A ∣ Nat.card K :=
      Subgroup.card_subgroup_dvd_card A
    have hKodd : Odd (Nat.card K) := by
      rw [hKcard]
      change Odd (Nat.card Z - 1)
      rw [hqPow]
      exact Nat.Even.sub_odd (pow_pos (by norm_num : 0 < (2 : ℕ)) n)
        (Nat.even_pow.mpr ⟨even_two, hn⟩) odd_one
    have hAodd : Odd (Nat.card A) := hKodd.of_dvd_nat hAcardDvd
    have hScardPow : ∃ m : ℕ, Nat.card S = 2 ^ m := by
      rcases hSuzuki.1 with ⟨m, hm⟩
      exact ⟨m, by simpa using hm⟩
    have hcoprime : Nat.Coprime (Nat.card A) (Nat.card S) := by
      rcases hScardPow with ⟨m, hm⟩
      rw [hm]
      exact hAodd.coprime_two_right.pow_right m
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Group.IsNilpotent S := hSpgroup.isNilpotent
    have hSsolvable : Group.IsSolvable S := by infer_instance
    have hfixedEq :=
      fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
        (G := S) (A := A) hSsolvable hcoprime (∅ : Set Nat.Primes)
        Z (inferInstance : IsInvariant A S Z)
    have hxMap : x ∈ (fixedPointSubgroup A S).map
        (QuotientGroup.mk' Z) := by
      rw [← hfixedEq]
      exact hxFixed
    rcases Subgroup.mem_map.mp hxMap with ⟨f, hfFixed, hfx⟩
    let B : Subgroup S := fixedPointSubgroup A S
    have hBne : B ≠ ⊥ := by
      intro hBbot
      have hfOne : f = 1 := by
        have : f ∈ (⊥ : Subgroup S) := by simpa [B, hBbot] using hfFixed
        simpa using this
      apply hxOne
      rw [← hfx, hfOne, map_one]
    have hBInv : IsXInvariantSubgroup K B := by
      have hpreserve : ∀ l : K, ∀ b : S, b ∈ B → l • b ∈ B := by
        intro l b hb
        change ∀ a : A, a • (l • b) = l • b
        intro a
        have hcomm : (a : K) * l = l * (a : K) :=
          hKcomm.is_comm.comm (a : K) l
        have hab : (a : K) • b = b := by
          simpa only [Subgroup.smul_def] using hb a
        calc
          a • (l • b) = (a : K) • (l • b) := by rw [Subgroup.smul_def]
          _ = ((a : K) * l) • b := by rw [mul_smul]
          _ = (l * (a : K)) • b := by rw [hcomm]
          _ = l • ((a : K) • b) := by rw [mul_smul]
          _ = l • b := by rw [hab]
      intro l b
      constructor
      · exact hpreserve l b
      · intro hlb
        have hback := hpreserve l⁻¹ (l • b) hlb
        simpa [smul_smul] using hback
    have hKtrans : ∀ a : S, a ∈ involutions S →
        ∀ b : S, b ∈ involutions S → ∃ l : K, b = l • a := by
      intro a ha b hb
      rcases hKregular.2 a ha b hb with ⟨l, hl, _huniq⟩
      exact ⟨l, hl⟩
    have hsB : sS ∈ B :=
      lemma1_involutions_mem_of_nontrivial_invariant
        hSuzuki hKtrans hBInv hBne sS hsSInv
    have hks : k • sS = sS := by
      have := hsB (⟨k, Subgroup.mem_zpowers k⟩ : A)
      simpa using this
    have hkOne : k = 1 :=
      (hKregular.2 sS hsSInv sS hsSInv).unique hks.symm (by simp)
    exact hk hkOne
  have htwoStableLines :
      ∃ X Y : Subgroup E,
        @IsXInvariantSubgroup K E _ _ defaultKAction X ∧
        @IsXInvariantSubgroup K E _ _ defaultKAction Y ∧
        Nat.card X = q ∧ Nat.card Y = q ∧ X ⊓ Y = ⊥ ∧
        (∀ c : P, c • X = X) ∧ (∀ c : P, c • Y = Y) := by
    have hEdata := higmanTheorem_center_quotient_orders_and_exponent hSuzuki
    have hEcomm : IsMulCommutative E := by simpa [E, Z] using hEdata.1
    have hEpow : ∀ x : E, x ^ 2 = 1 := by simpa [E, Z] using hEdata.2.1
    letI : IsElementaryAbelian 2 E :=
      { toIsMulCommutative := hEcomm
        exponent_dvd_p :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hEpow }
    have hlineIrreducible :
        ∀ (T A : Subgroup E),
          @IsXInvariantSubgroup K E _ _ defaultKAction T →
          @IsXInvariantSubgroup K E _ _ defaultKAction A →
          Nat.card T = q → A ≤ T → A ≠ ⊥ → A = T := by
      intro T A _hTinv hAinv hTcard hAle hAne
      obtain ⟨aA, haAOne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
      let a : E := aA
      have haA : a ∈ A := aA.property
      have haOne : a ≠ 1 := by
        intro ha
        apply haAOne
        exact Subtype.ext ha
      let orbitWithOne : Option K → A
        | none => 1
        | some k => ⟨k • a, hAinv k a |>.mp haA⟩
      have horbitInjective : Function.Injective orbitWithOne := by
        intro i j hij
        cases i with
        | none =>
            cases j with
            | none => rfl
            | some l =>
                exfalso
                apply haOne
                have hla : l • a = 1 := by
                  exact congrArg Subtype.val hij.symm
                have hback := congrArg (fun z : E => l⁻¹ • z) hla
                simpa [smul_smul] using hback
        | some k =>
            cases j with
            | none =>
                exfalso
                apply haOne
                have hka : k • a = 1 := congrArg Subtype.val hij
                have hback := congrArg (fun z : E => k⁻¹ • z) hka
                simpa [smul_smul] using hback
            | some l =>
                have hkl : k • a = l • a := congrArg Subtype.val hij
                have hfix : (l⁻¹ * k) • a = a := by
                  calc
                    (l⁻¹ * k) • a = l⁻¹ • (k • a) := by rw [mul_smul]
                    _ = l⁻¹ • (l • a) := by rw [hkl]
                    _ = a := by simp [smul_smul]
                have hactor : l⁻¹ * k = 1 := by
                  by_contra hne
                  exact haOne (hKfixedFree (l⁻¹ * k) hne a hfix)
                have hEq : k = l := by
                  have := congrArg (fun z : K => l * z) hactor
                  simpa [mul_assoc] using this
                exact congrArg some hEq
      have hqLeA : q ≤ Nat.card A := by
        calc
          q = Nat.card K + 1 := by omega
          _ = Nat.card (Option K) := by simp
          _ ≤ Nat.card A := Nat.card_le_card_of_injective
            orbitWithOne horbitInjective
      have hAleCard : Nat.card A ≤ Nat.card T :=
        Nat.card_le_card_of_injective
          (fun a : A => (⟨a, hAle a.property⟩ : T))
          (fun x y h => by
            apply Subtype.ext
            exact congrArg (fun z : T => (z : E)) h)
      have hAcard : Nat.card A = Nat.card T := by omega
      exact Subgroup.eq_of_le_of_card_ge hAle hAcard.ge
    have hUVcompl : IsCompl U Vline := by
      constructor
      · rw [disjoint_iff]
        simpa using hUVinf
      · rw [codisjoint_iff]
        simpa using hUVsup
    have hEcard : Nat.card E = q ^ 2 := by
      apply Nat.mul_right_cancel (Nat.card_pos (α := Z))
      calc
        Nat.card E * Nat.card Z = Nat.card S := by
          simpa [E] using
            (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Z)).symm
        _ = Nat.card Z ^ 3 := hcardCube
        _ = q ^ 2 * Nat.card Z := by simp [q, pow_succ]
    have hPnormK : P ≤ Subgroup.normalizer (K : Set G) := by
      intro c hcP
      rw [Subgroup.mem_normalizer_iff]
      intro k
      constructor
      · intro hkK
        let cD : D := ⟨c, hVleD (hPV hcP)⟩
        let kD : D := ⟨k, hKleD hkK⟩
        have hmem := hKnormalD.conj_mem kD hkK cD
        simpa [cD, kD, Subgroup.mem_subgroupOf] using hmem
      · intro hconjK
        let cD : D := ⟨c, hVleD (hPV hcP)⟩
        let kcD : D :=
          ⟨c * k * c⁻¹, hKleD hconjK⟩
        have hmem := hKnormalD.conj_mem kcD hconjK cD⁻¹
        simpa [cD, kcD, Subgroup.mem_subgroupOf, mul_assoc] using hmem
    let conjK (c : P) (k : K) : K :=
      ⟨(c : G)⁻¹ * (k : G) * (c : G), by
        have hcNorm := hPnormK c.property
        have hcNormInv : (c : G)⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
          (Subgroup.normalizer (K : Set G)).inv_mem hcNorm
        have hmem :=
          (Subgroup.mem_normalizer_iff.mp hcNormInv (k : G)).1 k.property
        simpa [mul_assoc] using hmem⟩
    have hKPsemilinear : ∀ c : P, ∀ k : K, ∀ x : E,
        k • (c • x) = c • (conjK c k • x) := by
      intro c k x
      obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective Z x
      change QuotientGroup.mk' Z (k • (c • r)) =
        QuotientGroup.mk' Z (c • (conjK c k • r))
      apply congrArg (QuotientGroup.mk' Z)
      apply Subtype.ext
      simp only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      change (k : G) * ((c : G) * (r : G) * (c : G)⁻¹) * (k : G)⁻¹ =
        (c : G) * (((c : G)⁻¹ * (k : G) * (c : G)) * (r : G) *
          ((c : G)⁻¹ * (k : G) * (c : G))⁻¹) * (c : G)⁻¹
      group
    let pSub (c : P) (T : Subgroup E) : Subgroup E :=
      T.map ((@MulDistribMulAction.toMonoidEnd P E _ _ defaultPAction) c)
    have hconjInvariant : ∀ c : P, ∀ T : Subgroup E,
        @IsXInvariantSubgroup K E _ _ defaultKAction T →
          @IsXInvariantSubgroup K E _ _ defaultKAction (pSub c T) := by
      intro c T hTinv
      exact semilinear_map_isInvariant defaultKAction defaultPAction
        conjK hKPsemilinear c T hTinv
    have hconjCard : ∀ c : P, ∀ T : Subgroup E,
        Nat.card (pSub c T) = Nat.card T := by
      intro c T
      exact card_map_action defaultPAction c T
    let hIso : Prop :=
      are_equivariantly_isomorphic defaultKAction U Vline hUinv
    by_cases hiso : hIso
    · rcases hiso with ⟨eUV, heUV⟩
      let CXlocal := Subgroup.centralizer (P : Set G) ⊓ Q
      rcases hCXtypeA with
        ⟨aN, _haN, aTheta, pairLift, aCocycle, _aPeriod,
          _aThetaNontrivial, aAddLeft, _aAddRight, aDiag,
          aMem, aOne, _aSurj, aInj, aMul⟩
      have aZeroLeft : ∀ z : BinaryGaloisField aN, aCocycle 0 z = 0 := by
        intro z
        have h := aAddLeft 0 0 z
        simpa only [zero_add, CharTwo.add_self_eq_zero] using h
      let rCX : CXlocal := ⟨pairLift 1 0, aMem 1 0⟩
      have hrSq : ((rCX : CXlocal) : G) ^ 2 = pairLift 0 1 := by
        calc
          ((rCX : CXlocal) : G) ^ 2 =
              pairLift (1 + 1) (0 + 0 + aCocycle 1 1) := by
            simpa [rCX, pow_two] using aMul 1 0 1 0
          _ = pairLift 0 1 := by
            rw [CharTwo.add_self_eq_zero, aDiag]
            simp
      have hrSqNe : ((rCX : CXlocal) : G) ^ 2 ≠ 1 := by
        rw [hrSq, ← aOne]
        intro h
        have := (aInj 0 1 0 0 h).2
        exact one_ne_zero this
      have hrS : ((rCX : CXlocal) : G) ∈ S := by
        rw [hSQ]
        exact rCX.property.2
      let rS : S := ⟨((rCX : CXlocal) : G), hrS⟩
      let rbar : E := QuotientGroup.mk' Z rS
      have hrbarNe : rbar ≠ 1 := by
        intro hOne
        have hrCenter : rS ∈ Z :=
          (QuotientGroup.eq_one_iff rS).mp hOne
        have hrCenterSq : (⟨rS, hrCenter⟩ : Z) ^ 2 = 1 :=
          (higmanTheorem_involutions_center hSuzuki).2 ⟨rS, hrCenter⟩
        apply hrSqNe
        exact congrArg (fun z : Z => (((z : Z) : S) : G)) hrCenterSq
      have hrbarFixed : ∀ c : P, c • rbar = rbar := by
        intro c
        change QuotientGroup.mk' Z (c • rS) = QuotientGroup.mk' Z rS
        apply congrArg (QuotientGroup.mk' Z)
        apply Subtype.ext
        simp only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        have hcComm : (c : G) * ((rCX : CXlocal) : G) =
            ((rCX : CXlocal) : G) * (c : G) :=
          Subgroup.mem_centralizer_iff.mp rCX.property.1
            (c : G) c.property
        rw [hcComm]
        simp [rS]
      have hUcardq : Nat.card U = q := by
        change Nat.card U = Nat.card (Subgroup.center S)
        exact hUcard
      have hVcardq : Nat.card Vline = q := by
        change Nat.card Vline = Nat.card (Subgroup.center S)
        exact hVcard
      letI : U.Normal := subgroup_normal_of_isMulCommutative hEcomm U
      letI : Vline.Normal := subgroup_normal_of_isMulCommutative hEcomm Vline
      have hrbarSup : rbar ∈ U ⊔ Vline := by
        rw [hUVsup]
        exact Subgroup.mem_top rbar
      rcases Subgroup.mem_sup_of_normal_left.mp hrbarSup with
        ⟨u, huU, v, hvV, huv⟩
      let uU : U := ⟨u, huU⟩
      let vV : Vline := ⟨v, hvV⟩
      have hXbase : ∃ X : Subgroup E,
          @IsXInvariantSubgroup K E _ _ defaultKAction X ∧
            Nat.card X = q ∧ rbar ∈ X := by
        exact invariant_line_through_equivariant_summands
          (q := q) (hKcard := hKcard)
          (U := U) (Vline := Vline)
          (hUinv := hUinv) (hVinv := hVinv)
          (hUcardq := hUcardq) (hVcardq := hVcardq)
          (hUVinf := hUVinf) (hEcomm := hEcomm)
          (hKcomm := hKcomm) (hKfixedFree := hKfixedFree)
          (eUV := eUV) (heUV := heUV)
          (rbar := rbar) (u := u) (v := v)
          (huU := huU) (hvV := hvV) (huv := huv)
      rcases hXbase with ⟨X, hXinv, hXcard, hrbarX⟩
      have hXorbit : ∀ x : E, x ∈ X ↔ x = 1 ∨ ∃ k : K, x = k • rbar := by
        let orbitWithOne : Option K → X
          | none => 1
          | some k => ⟨k • rbar, (hXinv k rbar).mp hrbarX⟩
        have horbitInjective : Function.Injective orbitWithOne := by
          intro i j hij
          cases i with
          | none =>
              cases j with
              | none => rfl
              | some l =>
                  exfalso
                  apply hrbarNe
                  have hla : l • rbar = 1 := by
                    exact congrArg Subtype.val hij.symm
                  have hback := congrArg (fun z : E => l⁻¹ • z) hla
                  simpa [smul_smul] using hback
          | some k =>
              cases j with
              | none =>
                  exfalso
                  apply hrbarNe
                  have hka : k • rbar = 1 := congrArg Subtype.val hij
                  have hback := congrArg (fun z : E => k⁻¹ • z) hka
                  simpa [smul_smul] using hback
              | some l =>
                  have hkl : k • rbar = l • rbar :=
                    congrArg Subtype.val hij
                  have hfix : (l⁻¹ * k) • rbar = rbar := by
                    calc
                      (l⁻¹ * k) • rbar = l⁻¹ • (k • rbar) := by
                        rw [mul_smul]
                      _ = l⁻¹ • (l • rbar) := by rw [hkl]
                      _ = rbar := by simp [smul_smul]
                  have hactor : l⁻¹ * k = 1 := by
                    by_contra hne
                    exact hrbarNe (hKfixedFree (l⁻¹ * k) hne rbar hfix)
                  have hEq : k = l := by
                    have := congrArg (fun z : K => l * z) hactor
                    simpa [mul_assoc] using this
                  exact congrArg some hEq
        have horbitCard : Nat.card (Option K) = Nat.card X := by
          calc
            Nat.card (Option K) = Nat.card K + 1 := by simp
            _ = q := by omega
            _ = Nat.card X := hXcard.symm
        have horbitSurjective : Function.Surjective orbitWithOne :=
          ((Nat.bijective_iff_injective_and_card orbitWithOne).2
            ⟨horbitInjective, horbitCard⟩).2
        intro x
        constructor
        · intro hx
          rcases horbitSurjective ⟨x, hx⟩ with ⟨i, hi⟩
          cases i with
          | none =>
              left
              exact (congrArg Subtype.val hi).symm
          | some k =>
              right
              exact ⟨k, (congrArg Subtype.val hi).symm⟩
        · rintro (rfl | ⟨k, rfl⟩)
          · exact X.one_mem
          · exact (hXinv k rbar).mp hrbarX
      have hPfixX : ∀ c : P, c • X = X := by
        have hsmulLe : ∀ c : P, c • X ≤ X := by
          intro c x hx
          rw [Subgroup.pointwise_smul_def, Subgroup.mem_map] at hx
          rcases hx with ⟨y, hyX, rfl⟩
          rcases (hXorbit y).mp hyX with rfl | ⟨k, rfl⟩
          · simp
          · apply (hXorbit _).mpr
            let k' : K := conjK c⁻¹ k
            have hback : conjK c k' = k := by
              apply Subtype.ext
              simp [conjK, k']
              group
            refine Or.inr ⟨k', ?_⟩
            calc
              c • (k • rbar) = c • (conjK c k' • rbar) := by rw [hback]
              _ = k' • (c • rbar) := (hKPsemilinear c k' rbar).symm
              _ = k' • rbar := by rw [hrbarFixed]
        intro c
        apply le_antisymm
        · exact hsmulLe c
        · intro x hx
          have hmem : c⁻¹ • x ∈ c⁻¹ • X :=
            Subgroup.smul_mem_pointwise_smul x c⁻¹ X hx
          have hxBack : c⁻¹ • x ∈ X := hsmulLe c⁻¹ hmem
          have hxForward : c • (c⁻¹ • x) ∈ c • X :=
            Subgroup.smul_mem_pointwise_smul (c⁻¹ • x) c X hxBack
          simpa [smul_smul] using hxForward
      have hYdata : ∃ Y : Subgroup E,
          IsXInvariantSubgroup K Y ∧ Nat.card Y = q ∧ X ⊓ Y = ⊥ ∧
            ∀ c : P, c • Y = Y := by
        have hPleD : P ≤ D := hPV.trans hVleD
        let KD : Subgroup D := K.subgroupOf D
        let PD : Subgroup D := P.subgroupOf D
        let A : Subgroup D := KD ⊔ PD
        letI : KD.Normal := hKnormalD
        letI : Subgroup.Normalizes D S := ⟨hDnormS⟩
        letI : IsInvariant D S Z := center_isInvariant
        letI : MulDistribMulAction D E :=
          quotientMulDistribMulAction (A := D) (G := S) Z
            (inferInstance : IsInvariant D S Z)
        have hDActionK : ∀ k : KD, ∀ x : E,
            ((k : D) • x) =
              (⟨((k : D) : G), by
                exact k.property⟩ : K) • x := by
          intro k x
          obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective Z x
          change QuotientGroup.mk' Z ((k : D) • r) =
            QuotientGroup.mk' Z
              ((⟨((k : D) : G), by
                exact k.property⟩ : K) • r)
          apply congrArg (QuotientGroup.mk' Z)
          apply Subtype.ext
          rfl
        have hDActionP : ∀ c : PD, ∀ x : E,
            ((c : D) • x) =
              (⟨((c : D) : G), by
                exact c.property⟩ : P) • x := by
          intro c x
          obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective Z x
          change QuotientGroup.mk' Z ((c : D) • r) =
            QuotientGroup.mk' Z
              ((⟨((c : D) : G), by
                exact c.property⟩ : P) • r)
          apply congrArg (QuotientGroup.mk' Z)
          apply Subtype.ext
          rfl
        have hAinvX : IsInvariant A E X := by
          have hpreserve : ∀ a : A, ∀ x : E, x ∈ X → a • x ∈ X := by
            intro a x hx
            rcases Subgroup.mem_sup_of_normal_left.mp a.property with
              ⟨k, hk, c, hc, hkc⟩
            let kKD : KD := ⟨k, hk⟩
            let cPD : PD := ⟨c, hc⟩
            let kK : K := ⟨((k : D) : G), by
              exact hk⟩
            let cP : P := ⟨((c : D) : G), by
              exact hc⟩
            have hcMem : cP • x ∈ X := by
              have : cP • x ∈ cP • X :=
                Subgroup.smul_mem_pointwise_smul x cP X hx
              simpa [hPfixX cP] using this
            have hkMem : kK • (cP • x) ∈ X :=
              (hXinv kK (cP • x)).mp hcMem
            change (a : D) • x ∈ X
            rw [← hkc, mul_smul, hDActionK kKD, hDActionP cPD]
            exact hkMem
          refine ⟨?_⟩
          intro a x
          constructor
          · exact hpreserve a x
          · intro hax
            have hback := hpreserve a⁻¹ (a • x) hax
            simpa [smul_smul] using hback
        letI : IsInvariant A E X := hAinvX
        have hAcardDvd : Nat.card A ∣ Nat.card D :=
          Subgroup.card_subgroup_dvd_card A
        have hAodd : Odd (Nat.card A) :=
          hA1.D_odd.of_dvd_nat hAcardDvd
        letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
        letI : CommGroup E := IsMulCommutative.instCommGroup
        let ρ :=
          Theory.Representation.ofElementaryAbelianAction (A := A) (G := E) (p := 2)
        let instAdd : AddCommGroup ρ.asModule :=
          Representation.instAddCommGroupAsModule ρ
        letI : AddCommGroup ρ.asModule := instAdd
        let instMod : Module (MonoidAlgebra (ZMod 2) A) ρ.asModule :=
          Representation.instModuleMonoidAlgebraAsModule ρ
        letI : Module (MonoidAlgebra (ZMod 2) A) ρ.asModule := instMod
        let eta : Subgroup E ≃o Submodule (ZMod 2) (Additive E) :=
          Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := 2))
        have hXinvariant : eta X ∈ ρ.invtSubmodule := by
          rw [Representation.mem_invtSubmodule]
          intro a
          rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
          intro x hx
          have hxX : Additive.toMul x ∈ X := by simpa [eta] using hx
          simpa [ρ, eta] using
            (IsInvariant.invariant (A := A) (G := E) (H := X)
              a (Additive.toMul x)).mp hxX
        let Xpack : ρ.invtSubmodule := ⟨eta X, hXinvariant⟩
        haveI : Fintype A := Fintype.ofFinite A
        haveI : NeZero (Fintype.card A : ZMod 2) := by
          constructor
          intro hzero
          have hEven : 2 ∣ Fintype.card A :=
            (ZMod.natCast_eq_zero_iff (Fintype.card A) 2).mp hzero
          exact hAodd.not_two_dvd_nat
            (by simpa [Nat.card_eq_fintype_card] using hEven)
        let Xmod : @Submodule (MonoidAlgebra (ZMod 2) A) ρ.asModule _
            instAdd.toAddCommMonoid instMod :=
          ρ.mapSubmodule Xpack
        obtain ⟨Ymod, hXYmod⟩ :=
          @MonoidAlgebra.Submodule.exists_isCompl'
            (ZMod 2) inferInstance A inferInstance inferInstance
            ρ.asModule instAdd instMod inferInstance Xmod
        let Ypack : ρ.invtSubmodule := ρ.mapSubmodule.symm Ymod
        let Y : Subgroup E := eta.symm
          (Ypack : Submodule (ZMod 2) (Additive E))
        have hYinvA : IsInvariant A E Y := by
          refine ⟨?_⟩
          intro a y
          constructor
          · intro hy
            have hyY : Additive.ofMul y ∈
                (Ypack : Submodule (ZMod 2) (Additive E)) := by
              simpa [Y, eta] using hy
            have hmem := (Representation.mem_invtSubmodule (ρ := ρ)).mp
              Ypack.2 a
            have hsmul :=
              (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ρ a)).mp
                hmem (Additive.ofMul y) hyY
            simpa [ρ, Y, eta] using hsmul
          · intro hy
            have hyY : Additive.ofMul (a • y) ∈
                (Ypack : Submodule (ZMod 2) (Additive E)) := by
              simpa [Y, eta] using hy
            have hmem := (Representation.mem_invtSubmodule (ρ := ρ)).mp
              Ypack.2 a⁻¹
            have hsmul :=
              (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ρ a⁻¹)).mp
                hmem (Additive.ofMul (a • y)) hyY
            simpa [ρ, Y, eta, inv_smul_smul] using hsmul
        have hXYcompl : IsCompl X Y := by
          have hcomplSub : IsCompl (eta X) (eta Y) := by
            have hcomplPack : IsCompl Xpack Ypack :=
              (ρ.mapSubmodule.isCompl_iff).mpr
                (by simpa [Xmod, Ypack] using hXYmod)
            have hEtaY : eta Y =
                (Ypack : Submodule (ZMod 2) (Additive E)) := by
              dsimp [Y]
              exact eta.apply_symm_apply _
            rw [hEtaY]
            rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcomplPack ⊢
            have hinf := congrArg Subtype.val hcomplPack.1
            have hsup := congrArg Subtype.val hcomplPack.2
            change
              (Xpack : Submodule (ZMod 2) (Additive E)) ⊓
                (Ypack : Submodule (ZMod 2) (Additive E)) = ⊥ at hinf
            change
              (Xpack : Submodule (ZMod 2) (Additive E)) ⊔
                (Ypack : Submodule (ZMod 2) (Additive E)) = ⊤ at hsup
            exact ⟨hinf, hsup⟩
          exact (OrderIso.isCompl_iff (f := eta) (x := X) (y := Y)).mpr
            hcomplSub
        have hYcard : Nat.card Y = q := by
          letI : X.Normal := subgroup_normal_of_isMulCommutative hEcomm X
          have hXYcompl' : X.IsComplement' Y := by
            refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
              hXYcompl.disjoint ?_
            apply Set.eq_univ_iff_forall.mpr
            intro z
            have hz : z ∈ X ⊔ Y := by
              rw [hXYcompl.sup_eq_top]
              exact Subgroup.mem_top z
            rcases Subgroup.mem_sup_of_normal_left.mp hz with
              ⟨x, hx, y, hy, rfl⟩
            exact Set.mem_mul.mpr ⟨x, hx, y, hy, rfl⟩
          have hmul := hXYcompl'.card_mul
          rw [hXcard, hEcard, pow_two] at hmul
          exact Nat.mul_left_cancel (by omega) hmul
        have hYinvK : IsXInvariantSubgroup K Y := by
          intro k y
          let kKD : KD := ⟨⟨(k : G), hKleD k.property⟩, by
            exact k.property⟩
          let kA : A := ⟨(kKD : D), Subgroup.mem_sup_left kKD.property⟩
          have hact : kA • y = k • y := by
            exact hDActionK kKD y
          constructor
          · intro hy
            rw [← hact]
            exact (hYinvA.invariant kA y).mp hy
          · intro hky
            apply (hYinvA.invariant kA y).mpr
            simpa [hact] using hky
        have hPfixY : ∀ c : P, c • Y = Y := by
          intro c
          let cPD : PD := ⟨⟨(c : G), hPleD c.property⟩, by
            exact c.property⟩
          let cA : A := ⟨(cPD : D), Subgroup.mem_sup_right cPD.property⟩
          have hact : ∀ y : E, cA • y = c • y := hDActionP cPD
          apply le_antisymm
          · intro y hy
            rw [Subgroup.pointwise_smul_def, Subgroup.mem_map] at hy
            rcases hy with ⟨x, hxY, rfl⟩
            change c • x ∈ Y
            rw [← hact x]
            exact (hYinvA.invariant cA x).mp hxY
          · intro y hyY
            have hback : c⁻¹ • y ∈ Y := by
              let ciPD : PD := ⟨⟨((c⁻¹ : P) : G), hPleD (c⁻¹).property⟩, by
                exact (c⁻¹).property⟩
              let ciA : A :=
                ⟨(ciPD : D), Subgroup.mem_sup_right ciPD.property⟩
              have hacti : ciA • y = c⁻¹ • y := hDActionP ciPD y
              rw [← hacti]
              exact (hYinvA.invariant ciA y).mp hyY
            have : c • (c⁻¹ • y) ∈ c • Y :=
              Subgroup.smul_mem_pointwise_smul (c⁻¹ • y) c Y hback
            simpa [smul_smul] using this
        exact ⟨Y, hYinvK, hYcard, hXYcompl.inf_eq_bot, hPfixY⟩
      rcases hYdata with ⟨Y, hYinv, hYcard, hXYinf, hPfixY⟩
      exact ⟨X, Y, hXinv, hYinv, hXcard, hYcard, hXYinf,
        hPfixX, hPfixY⟩
    · have hnoThird :
          ∀ (T : Subgroup E),
            @IsXInvariantSubgroup K E _ _ defaultKAction T →
            Nat.card T = q → T = U ∨ T = Vline := by
        intro T hTinv hTcard
        by_cases hTU : T = U
        · exact Or.inl hTU
        by_cases hTV : T = Vline
        · exact Or.inr hTV
        have hTUinfInv : IsXInvariantSubgroup K (T ⊓ U) := by
          intro k x
          simp only [Subgroup.mem_inf]
          exact and_congr (hTinv k x) (hUinv k x)
        have hTVinfInv : IsXInvariantSubgroup K (T ⊓ Vline) := by
          intro k x
          simp only [Subgroup.mem_inf]
          exact and_congr (hTinv k x) (hVinv k x)
        have hTUinf : T ⊓ U = ⊥ := by
          by_contra hne
          have heq := hlineIrreducible T (T ⊓ U) hTinv hTUinfInv
            hTcard inf_le_left hne
          have hTleU : T ≤ U := by rw [← heq]; exact inf_le_right
          exact hTU (Subgroup.eq_of_le_of_card_ge hTleU (by
            rw [hTcard, hUcard]))
        have hTVinf : T ⊓ Vline = ⊥ := by
          by_contra hne
          have heq := hlineIrreducible T (T ⊓ Vline) hTinv hTVinfInv
            hTcard inf_le_left hne
          have hTleV : T ≤ Vline := by rw [← heq]; exact inf_le_right
          exact hTV (Subgroup.eq_of_le_of_card_ge hTleV (by
            rw [hTcard, hVcard]))
        letI : T.Normal := subgroup_normal_of_isMulCommutative hEcomm T
        have hUTcomp : U.IsComplement' T :=
          Subgroup.isComplement'_of_card_mul_and_disjoint
            (by rw [hUcard, hTcard, hEcard, pow_two])
            (by
              rw [disjoint_iff]
              calc
                U ⊓ T = T ⊓ U := inf_comm U T
                _ = ⊥ := hTUinf)
        have hVTcomp : Vline.IsComplement' T :=
          Subgroup.isComplement'_of_card_mul_and_disjoint
            (by rw [hVcard, hTcard, hEcard, pow_two])
            (by
              rw [disjoint_iff]
              calc
                Vline ⊓ T = T ⊓ Vline := inf_comm Vline T
                _ = ⊥ := hTVinf)
        have hTInvariant : IsInvariant K E T := ⟨hTinv⟩
        letI : IsInvariant K E T := hTInvariant
        letI : MulDistribMulAction K (E ⧸ T) :=
          quotientMulDistribMulAction (A := K) (G := E) T hTInvariant
        let e : U ≃* Vline :=
          hUTcomp.QuotientMulEquiv.symm.trans hVTcomp.QuotientMulEquiv
        exfalso
        apply hiso
        refine ⟨e, ?_⟩
        intro k u
        let kuV : Vline :=
          ⟨k • ((e u : Vline) : E),
            (hVinv k ((e u : Vline) : E)).mp (e u).property⟩
        have hsub :
            e ⟨k • (u : E), (hUinv k (u : E)).mp u.property⟩ = kuV := by
          apply hVTcomp.QuotientMulEquiv.symm.injective
          simp only [e, kuV, MulEquiv.trans_apply,
            MulEquiv.symm_apply_apply]
          change k • QuotientGroup.mk' T (u : E) =
            k • QuotientGroup.mk' T ((e u : Vline) : E)
          apply congrArg (fun z : E ⧸ T => k • z)
          change hUTcomp.QuotientMulEquiv.symm u =
            hVTcomp.QuotientMulEquiv.symm (e u)
          simp [e]
        exact congrArg Subtype.val hsub
      have hUne : U ≠ ⊥ := by
        intro hbot
        have hUcardq : Nat.card U = q := by
          simpa [q, Z] using hUcard
        have hUone : Nat.card U = 1 := by rw [hbot]; simp
        omega
      have hVne : Vline ≠ ⊥ := by
        intro hbot
        have hVcardq : Nat.card Vline = q := by
          simpa [q, Z] using hVcard
        have hVone : Nat.card Vline = 1 := by rw [hbot]; simp
        omega
      have hUVne : U ≠ Vline := by
        intro hEq
        have hUbot : U = ⊥ := by
          calc
            U = U ⊓ Vline := by rw [hEq, inf_idem]
            _ = ⊥ := hUVinf
        exact hUne hUbot
      have hPfixU : ∀ c : P, c • U = U := by
        intro c
        have hcUcases := hnoThird (pSub c U)
          (hconjInvariant c U hUinv) (by rw [hconjCard, hUcard])
        rcases hcUcases with hcU | hcU
        · change c • U = U at hcU
          exact hcU
        · change c • U = Vline at hcU
          exfalso
          have hcVcases := hnoThird (pSub c Vline)
            (hconjInvariant c Vline hVinv) (by rw [hconjCard, hVcard])
          have hcV : c • Vline = U := by
            rcases hcVcases with h | h
            · change c • Vline = U at h
              exact h
            · change c • Vline = Vline at h
              have hsame : c • U = c • Vline := hcU.trans h.symm
              exfalso
              apply hUVne
              have hback := congrArg (fun T : Subgroup E => c⁻¹ • T) hsame
              simpa [smul_smul] using hback
          have hcSqU : (c ^ 2) • U = U := by
            rw [pow_two, mul_smul, hcU, hcV]
          have hcNe : c ≠ 1 := by
            intro hcOne
            apply hUVne
            simpa [hcOne] using hcU
          have hpDvdD : p ∣ Nat.card D := by
            rw [← hPcard]
            exact Subgroup.card_dvd_of_le (hPV.trans hVleD)
          have hpOdd : Odd p := hA1.D_odd.of_dvd_nat hpDvdD
          rcases hpOdd with ⟨m, hm⟩
          have hEvenFix : (c ^ 2) ^ m • U = U :=
            smul_eq_self_of_mem_zpowers
              (Subgroup.pow_mem (Subgroup.zpowers (c ^ 2))
                (Subgroup.mem_zpowers (c ^ 2)) m) hcSqU
          have hcpow : c ^ p = 1 := by
            rw [← hPcard]
            exact pow_card_eq_one'
          have hOddMove : c ^ p • U = Vline := by
            rw [hm, show c ^ (2 * m + 1) = c * (c ^ 2) ^ m by group,
              mul_smul, hEvenFix, hcU]
          rw [hcpow, one_smul] at hOddMove
          exact hUVne hOddMove
      have hPfixV : ∀ c : P, c • Vline = Vline := by
        intro c
        have hcVcases := hnoThird (pSub c Vline)
          (hconjInvariant c Vline hVinv) (by rw [hconjCard, hVcard])
        rcases hcVcases with hcV | hcV
        · change c • Vline = U at hcV
          have hsame : c • U = c • Vline := (hPfixU c).trans hcV.symm
          exfalso
          apply hUVne
          have hback := congrArg (fun T : Subgroup E => c⁻¹ • T) hsame
          simpa [smul_smul] using hback
        · change c • Vline = Vline at hcV
          exact hcV
      have hUcardq : Nat.card U = q := by
        change Nat.card U = Nat.card (Subgroup.center S)
        exact hUcard
      have hVcardq : Nat.card Vline = q := by
        change Nat.card Vline = Nat.card (Subgroup.center S)
        exact hVcard
      exact ⟨U, Vline, hUinv, hVinv, hUcardq, hVcardq,
        hUVinf, hPfixU, hPfixV⟩
  rcases htwoStableLines with
    ⟨X, Y, hXinv, hYinv, hXcard, hYcard, hXYinf,
      hPfixX, hPfixY⟩
  have hPquotientAction : ∀ c : P, ∀ x : S,
      @SMul.smul P E defaultPAction.toSMul c
          (QuotientGroup.mk' Z x) =
        QuotientGroup.mk' Z (c • x) := by
    intro c x
    rfl
  have hpDvdD : p ∣ Nat.card D := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le (hPV.trans hVleD)
  have hpOdd : Odd p := hA1.D_odd.of_dvd_nat hpDvdD
  have hpNeTwo : p ≠ 2 := by
    intro hpTwo
    exact hpOdd.not_two_dvd_nat (by simp [hpTwo])
  have hpNotDvdCenter : ¬ p ∣ Nat.card (Subgroup.center S) := by
    rw [show Nat.card (Subgroup.center S) = 2 ^ n by
      simpa only [Z] using hqPow]
    intro hpPow
    have hpTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpPow
    rcases (Nat.dvd_prime Nat.prime_two).mp hpTwo with hpOne | hpTwo
    · exact hp.ne_one hpOne
    · exact hpNeTwo hpTwo
  have hXPinv :
      @IsXInvariantSubgroup P E _ _ defaultPAction X :=
    isXInvariantSubgroup_of_pointwise_smul_eq X hPfixX
  have hYPinv :
      @IsXInvariantSubgroup P E _ _ defaultPAction Y :=
    isXInvariantSubgroup_of_pointwise_smul_eq Y hPfixY
  have hXcardCenter : Nat.card X = Nat.card (Subgroup.center S) := by
    simpa only [q, Z] using hXcard
  have hYcardCenter : Nat.card Y = Nat.card (Subgroup.center S) := by
    simpa only [q, Z] using hYcard
  rcases cubic_fixed_root K P S sS hsSInv
      (by simpa only [sS] using hPcentralizesS)
      hSuzuki hKregular hKcard defaultKAction defaultPAction
      hquotientAction hPquotientAction X hXinv hXcardCenter hXPinv
      p hp hPcard hpNotDvdCenter with
    ⟨x, hxX, hxsq, hxCent⟩
  rcases cubic_fixed_root K P S sS hsSInv
      (by simpa only [sS] using hPcentralizesS)
      hSuzuki hKregular hKcard defaultKAction defaultPAction
      hquotientAction hPquotientAction Y hYinv hYcardCenter hYPinv
      p hp hPcard hpNotDvdCenter with
    ⟨y, hyY, hysq, hyCent⟩
  exact cubic_fixed_roots_contradiction P Q S s hSQ hSuzuki
    hCXtypeA X Y hXYinf x y hxX hyY hxsq hysq hxCent hyCent hsInv


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
public theorem proposition
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hch : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
    HypothesisC1 G V)
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              ∃ (M : Subgroup L) (_ : M.Normal) (q : ℕ),
                Odd (Nat.card (L ⧸ M)) ∧ (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
                  ((∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ k)
      (eL : M ≃* PSL2BinaryMatrixGroup k)
      (rho : PSL2BinaryMatrixGroup k →*
        Equiv.Perm (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)))
      (eΩ : ΩL ≃ ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)),
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField k),
      ∀ z : ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k),
        rho (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
            (BinaryGaloisField k))) A) z =
          Matrix.SpecialLinearGroup.toLin' A • z) ∧
    ∀ l : M, ∀ ω : ΩL,
      eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ (2 * k + 1)),
    let K := BinaryGaloisField (2 * k + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
          y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∃ (eL : M ≃* SuzukiMatrixGroup k)
        (rho : SuzukiMatrixGroup k →* Equiv.Perm {z // z ∈ O})
        (eΩ : ΩL ≃ {z // z ∈ O}),
      (∀ g : SuzukiMatrixGroup k, ∀ z : {z // z ∈ O},
        ((rho g z : {z // z ∈ O}) : ℙ K (Fin 4 → K)) =
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv •
              (z : ℙ K (Fin 4 → K))) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    Nat.card E = q ^ 2 ∧
    Nat.card {z : E // J.conj z = z} = q ∧
    let P := ℙ E (Fin 3 → E)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let X := {x : P // x ∈ A}
    ∃ (eL : M ≃* ProjectiveSpecialUnitaryMatrixGroup J)
        (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm X)
        (eΩ : ΩL ≃ X),
      (∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : X,
        ∀ M : J.specialSubgroup,
          Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) E) =
              (g : Matrix.ProjGenLinGroup (Fin 3) E) →
            ((rho g z : X) : P) =
              (Matrix.GeneralLinearGroup.toLin
                (M : GL (Fin 3) E)).toLinearEquiv • (z : P)) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω))))
    (hSQ : S = Q) :
    (S = Q0 ∧ orderOf (s * t) = 3) ∨
      (IsSuzukiTwoTypeA S ∧
        orderOf (s * t) = 5 ∧ W = ⊥) ∨
      (IsSuzukiTwoTypeB S ∧
        orderOf (s * t) = 3 ∧ W ≠ ⊥) := by
  classical
  have hprimeSubgroup :
      ∀ U : Subgroup G, U ≠ ⊥ →
        ∃ (P : Subgroup G) (p : ℕ),
          P ≤ U ∧ Nat.Prime p ∧ Nat.card P = p := by
    intro U hU
    let p := (Nat.card U).minFac
    have hp : Nat.Prime p :=
      Nat.minFac_prime (U.one_lt_card_iff_ne_bot.mpr hU).ne'
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    obtain ⟨x, hx⟩ :=
      exists_prime_orderOf_dvd_card' p (Nat.minFac_dvd (Nat.card U))
    refine ⟨Subgroup.zpowers (x : G), p,
      Subgroup.zpowers_le.mpr x.property, hp, ?_⟩
    calc
      Nat.card (Subgroup.zpowers (x : G)) = orderOf (x : G) :=
        Nat.card_zpowers (x : G)
      _ = orderOf x := Subgroup.orderOf_coe x
      _ = p := hx
  have hVleD : V ≤ D := by
    intro x hxV
    rw [hch.1.1.V_eq] at hxV
    exact hxV.1
  have hD_faithful_on_S :
      D ⊓ Subgroup.centralizer (S : Set G) = ⊥ := by
    have hcore := (PFchapter1section1.proposition_4_c H D Q t s
      hch.1.1.hA.A1 hch.1.2.1 hch.1.2.2.1 hch.1.2.2.2).1
    rw [← hSQ] at hcore
    rw [← hcore, eq_bot_iff]
    intro x hxCore
    have hfix : ∀ omega : Ω, x • omega = omega := by
      have hxAll : ∀ point : Ω, x ∈ MulAction.stabilizer G point := by
        simpa [pointStabilizerCore] using hxCore
      intro omega
      exact MulAction.mem_stabilizer_iff.mp (hxAll omega)
    have hxOne : x = 1 :=
      (faithfulSMul_iff.mp hch.1.1.hA.A2) x hfix
    simp [hxOne]
  letI : (Q.subgroupOf H).Normal := hch.1.1.hA.A1.Q_normal_in_H
  have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hch.1.1.hA.A1.Q_le_H
  have hDnormS : D ≤ Subgroup.normalizer (S : Set G) := by
    rw [hSQ]
    exact hch.1.1.hA.A1.D_le_H.trans hHnormQ
  have hKnormS : K ≤ Subgroup.normalizer (S : Set G) :=
    hch.1.1.K_le_D.trans hDnormS
  letI : Subgroup.Normalizes K S := ⟨hKnormS⟩
  have hKcyclic : IsCyclic K :=
    (PFchapter1section2.proposition_2
      H D Q K V W Q0 S Q1 t hch.1.1).1
  have hKfaithful : FaithfulSMul K S := by
    rw [faithfulSMul_iff]
    intro k hkfix
    have hkCentralizer : (k : G) ∈
        Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hxS
      let xS : S := ⟨x, hxS⟩
      have hfix := hkfix xS
      have hconj : (k : G) * x * (k : G)⁻¹ = x := by
        simpa [xS,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            congrArg (fun z : S => (z : G)) hfix
      have hmul := congrArg (fun z : G => z * (k : G)) hconj
      simpa [mul_assoc] using hmul.symm
    have hkBot : (k : G) ∈ (⊥ : Subgroup G) := by
      rw [← hD_faithful_on_S]
      exact ⟨hch.1.1.K_le_D k.property, hkCentralizer⟩
    apply Subtype.ext
    simpa using hkBot
  have hrightConjugateInjective :
      ∀ (x : S) (hx : IsInvolution x),
        Function.Injective
          (fun k : {a : G // a ∈ peterfalviKSet D t} =>
            (⟨rightConjugateElem (x : G) (k : G),
              ((PFchapter1section1.proposition_3 H D Q t
                  hch.1.1.hA.A1).2
                (x : G)
                (hch.1.1.hA.A1.Q_le_H
                  (by rw [← hSQ]; exact x.property))
                ⟨(by
                    intro hxOne
                    exact hx.ne_one (Subtype.ext hxOne)),
                  congrArg (fun z : S => (z : G)) hx.sq_eq_one⟩
                (rightConjugateElem (x : G) (k : G))).2
                  ⟨k, k.property, rfl⟩⟩ :
              {y : G // y ∈ H ∧ IsInvolution y})) := by
    intro x hx
    let KSet : Type _ := {a : G // a ∈ peterfalviKSet D t}
    let HInv : Type _ := {y : G // y ∈ H ∧ IsInvolution y}
    have hxG : IsInvolution (x : G) := by
      exact ⟨fun hxOne => hx.ne_one (Subtype.ext hxOne),
        congrArg (fun z : S => (z : G)) hx.sq_eq_one⟩
    have hxH : (x : G) ∈ H :=
      hch.1.1.hA.A1.Q_le_H (by rw [← hSQ]; exact x.property)
    let phi : KSet → HInv := fun k =>
      ⟨rightConjugateElem (x : G) (k : G),
        ((PFchapter1section1.proposition_3 H D Q t
            hch.1.1.hA.A1).2 (x : G) hxH hxG
          (rightConjugateElem (x : G) (k : G))).2
            ⟨k, k.property, rfl⟩⟩
    have hphiSurjective : Function.Surjective phi := by
      rintro ⟨y, hy⟩
      rcases ((PFchapter1section1.proposition_3 H D Q t
          hch.1.1.hA.A1).2 (x : G) hxH hxG y).1 hy with
        ⟨k, hk, hkEq⟩
      refine ⟨⟨k, hk⟩, ?_⟩
      apply Subtype.ext
      exact hkEq
    have hphiInjective : Function.Injective phi :=
      (hphiSurjective.bijective_of_nat_card_le
        (by simpa [KSet, HInv] using
          le_of_eq (PFchapter1section1.proposition_3 H D Q t
            hch.1.1.hA.A1).1)).1
    simpa [phi, KSet, HInv, hxG, hxH] using hphiInjective
  have hKregular : ActionRegularOn K S (involutions S) := by
    constructor
    · intro x hx k
      have hxG : IsInvolution (x : G) :=
        ⟨fun hxOne => hx.ne_one (Subtype.ext hxOne),
          congrArg (fun z : S => (z : G)) hx.sq_eq_one⟩
      have hconj := isInvolution_rightConjugateElem
        (g := ((k⁻¹ : K) : G)) hxG
      constructor
      · intro hOne
        apply hconj.ne_one
        simpa [rightConjugateElem,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            congrArg (fun z : S => (z : G)) hOne
      · apply Subtype.ext
        simpa [rightConjugateElem,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            hconj.sq_eq_one
    · intro x hx y hy
      have hxG : IsInvolution (x : G) :=
        ⟨fun hxOne => hx.ne_one (Subtype.ext hxOne),
          congrArg (fun z : S => (z : G)) hx.sq_eq_one⟩
      have hyG : IsInvolution (y : G) :=
        ⟨fun hyOne => hy.ne_one (Subtype.ext hyOne),
          congrArg (fun z : S => (z : G)) hy.sq_eq_one⟩
      have hxH : (x : G) ∈ H :=
        hch.1.1.hA.A1.Q_le_H (by rw [← hSQ]; exact x.property)
      have hyH : (y : G) ∈ H :=
        hch.1.1.hA.A1.Q_le_H (by rw [← hSQ]; exact y.property)
      rcases ((PFchapter1section1.proposition_3 H D Q t
          hch.1.1.hA.A1).2 (x : G) hxH hxG (y : G)).1
          ⟨hyH, hyG⟩ with ⟨a, haSet, haEq⟩
      have haK : a ∈ K := (hch.1.1.K_def a).mpr haSet
      let k : K := ⟨a⁻¹, K.inv_mem haK⟩
      refine ⟨k, ?_, ?_⟩
      · apply Subtype.ext
        simpa [k, rightConjugateElem,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using haEq.symm
      · intro b hb
        let aSet : {z : G // z ∈ peterfalviKSet D t} := ⟨a, haSet⟩
        let bSet : {z : G // z ∈ peterfalviKSet D t} :=
          ⟨((b⁻¹ : K) : G),
            (hch.1.1.K_def ((b⁻¹ : K) : G)).mp (b⁻¹ : K).property⟩
        have hbRight :
            rightConjugateElem (x : G) (bSet : G) = (y : G) := by
          have hbVal := congrArg (fun z : S => (z : G)) hb
          simpa [bSet, rightConjugateElem,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hbVal.symm
        have hba : bSet = aSet :=
          hrightConjugateInjective x hx
            (by apply Subtype.ext; exact hbRight.trans haEq.symm)
        apply Subtype.ext
        change (b : G) = a⁻¹
        have hval : ((b⁻¹ : K) : G) = a :=
          congrArg Subtype.val hba
        simpa using congrArg Inv.inv hval
  have htypeANotCommutative :
      ∀ U : Subgroup G, IsSuzukiTwoTypeA U → ¬ IsMulCommutative U := by
    intro U htypeA hcomm
    rcases htypeA with
      ⟨n, hn, theta, pairLift, cocycle, _hperiod, htheta,
        haddLeft, haddRight, hdiag, hmem, _hone, _hsurj, hinj, hmul⟩
    rcases htheta with ⟨a, ha⟩
    have hsumNe : a + theta a ≠ 0 := by
      intro hzero
      apply ha
      have hzero' : theta a + a = 0 := by simpa [add_comm] using hzero
      have hneg : theta a = -a := eq_neg_of_add_eq_zero_left hzero'
      simpa only [CharTwo.neg_eq] using hneg
    have hcocNe : cocycle a 1 ≠ cocycle 1 a := by
      intro hcoc
      have hcalc :
          (a + 1) * theta (a + 1) =
            a * theta a + cocycle a 1 + cocycle 1 a + 1 := by
        calc
          (a + 1) * theta (a + 1) = cocycle (a + 1) (a + 1) :=
            (hdiag (a + 1)).symm
          _ = cocycle a (a + 1) + cocycle 1 (a + 1) := by rw [haddLeft]
          _ = (cocycle a a + cocycle a 1) +
              (cocycle 1 a + cocycle 1 1) := by rw [haddRight, haddRight]
          _ = a * theta a + cocycle a 1 + cocycle 1 a + 1 := by
            rw [hdiag, hdiag]
            simp only [map_one, mul_one]
            ring
      rw [map_add, map_one, hcoc] at hcalc
      have hcalc' :
          (a + 1) * (theta a + 1) = a * theta a + 1 := by
        calc
          (a + 1) * (theta a + 1) =
              a * theta a + cocycle 1 a + cocycle 1 a + 1 := hcalc
          _ = a * theta a + (cocycle 1 a + cocycle 1 a) + 1 := by ring
          _ = a * theta a + 1 := by
            rw [CharTwo.add_self_eq_zero]
            simp
      have hcalc'' :
          a * theta a + a + theta a + 1 = a * theta a + 1 := by
        calc
          a * theta a + a + theta a + 1 =
              (a + 1) * (theta a + 1) := by ring
          _ = a * theta a + 1 := hcalc'
      have : a + theta a = 0 := by linear_combination hcalc''
      exact hsumNe this
    let pa : U := ⟨pairLift a 0, hmem a 0⟩
    let p1 : U := ⟨pairLift 1 0, hmem 1 0⟩
    have hcommEq : pairLift a 0 * pairLift 1 0 =
        pairLift 1 0 * pairLift a 0 := by
      exact congrArg Subtype.val
        ((@IsMulCommutative.is_comm U _ hcomm).comm pa p1)
    rw [hmul, hmul] at hcommEq
    have hcommEq' : pairLift (a + 1) (cocycle a 1) =
        pairLift (a + 1) (cocycle 1 a) := by
      simpa [add_comm] using hcommEq
    exact hcocNe (hinj (a + 1) (cocycle a 1)
      (a + 1) (cocycle 1 a) hcommEq').2
  have hcommutativeCase :
      IsMulCommutative S → S = Q0 ∧ orderOf (s * t) = 3 := by
    intro hcomm
    have hVleD : V ≤ D := by
      intro x hxV
      rw [hch.1.1.V_eq] at hxV
      exact hxV.1
    rcases hprimeSubgroup V hch.2.V_ne_bot with
      ⟨P, p, hPV, hp, hPcard⟩
    have hPne : P ≠ ⊥ := by
      intro hPbot
      apply hp.ne_one
      calc
        p = Nat.card P := hPcard.symm
        _ = 1 := by rw [hPbot]; simp
    have hPprime : ∃ q : ℕ, Nat.Prime q ∧ Nat.card P = q :=
      ⟨p, hp, hPcard⟩
    have h2rank :
        TwoRankAtLeastTwo (Subgroup.centralizer (P : Set G)) :=
      hch.2.centralizers_two_rank P hPV hPprime
    let CX : Subgroup G := Subgroup.centralizer (P : Set G) ⊓ Q
    have hlocal :=
      PFchapter1section3.proposition_1_c.{u, v}
        H D Q K V W Q0 S Q1 P t s hch.1 hind hPne hPV h2rank
    rcases hlocal.2.2 with
      ⟨ell, hellPower, hellGt, hellCard, hlocalCases⟩
    have hCXcomm : IsMulCommutative CX := by
      refine IsMulCommutative.mk <| Std.Commutative.mk ?_
      intro x y
      let xS : S := ⟨x, by rw [hSQ]; exact x.property.2⟩
      let yS : S := ⟨y, by rw [hSQ]; exact y.property.2⟩
      apply Subtype.ext
      exact congrArg (fun z : S => (z : G))
        ((@IsMulCommutative.is_comm S _ hcomm).comm xS yS)
    have hfirst :
        orderOf (s * t) = 3 ∧ IsElementaryAbelian 2 CX := by
      rcases hlocalCases with hlinear | hSuzuki | hunitary
      · rcases hlinear with
          ⟨_k, _hk, _hell, _hmodel, horder, hCX, _hcard⟩
        exact ⟨horder, by simpa [CX] using hCX⟩
      · rcases hSuzuki with
          ⟨_k, _hk, _hell, _hmodel, _horder, hCX, _hcard⟩
        exact False.elim
          (htypeANotCommutative CX (by simpa [CX] using hCX) hCXcomm)
      · rcases hunitary with
          ⟨_E, _hEfield, _hEfinite, _J, _hform, _hEcard,
            _hfixedCard, _hmodel, _horder, hCX, _hcard⟩
        exact False.elim ((by simpa [CX] using hCX : IsSuzukiTwoGroup CX).2.1 hCXcomm)
    have hcentralizer_le_Q0 : CX ≤ Q0 := by
      letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      letI : IsElementaryAbelian 2 CX := hfirst.2
      intro x hxCX
      have hxSqSub : (⟨x, hxCX⟩ : CX) ^ 2 = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 CX) ⟨x, hxCX⟩
      have hxSq : x ^ 2 = 1 := congrArg Subtype.val hxSqSub
      rw [hch.1.1.Q0_def]
      by_cases hxOne : x = 1
      · exact Or.inl hxOne
      · exact Or.inr ⟨hch.1.1.hA.A1.Q_le_H hxCX.2,
          ⟨hxOne, hxSq⟩⟩
    refine ⟨?_, hfirst.1⟩
    by_contra hSne
    have hQ0leS : Q0 ≤ S := by
      rw [hSQ]
      exact hch.1.1.Q0_le_Q
    have hSnotleQ0 : ¬ S ≤ Q0 := by
      intro hSle
      exact hSne (le_antisymm hSle hQ0leS)
    obtain ⟨a, haS, haQ0⟩ := Set.not_subset.mp hSnotleQ0
    have hSpgroup : IsPGroup 2 S := by
      obtain ⟨T, hS⟩ := hch.1.1.S_sylow_in_Q
      rw [hS]
      exact T.isPGroup'.map Q.subtype
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let aS : S := ⟨a, haS⟩
    obtain ⟨m, haOrder⟩ := IsPGroup.iff_orderOf.mp hSpgroup aS
    have haOrderNeOne : orderOf aS ≠ 1 := by
      intro haOne
      apply haQ0
      exact (hch.1.1.Q0_def a).mpr <| Or.inl
        (congrArg (fun z : S => (z : G))
          (orderOf_eq_one_iff.mp haOne))
    have haOrderNeTwo : orderOf aS ≠ 2 := by
      intro haTwo
      have haSqSub : aS ^ 2 = 1 := by
        rw [← haTwo]
        exact pow_orderOf_eq_one aS
      have haSq : a ^ 2 = 1 :=
        congrArg (fun z : S => (z : G)) haSqSub
      have haNe : a ≠ 1 := by
        intro haOne
        exact haQ0 (haOne ▸ Q0.one_mem)
      apply haQ0
      exact (hch.1.1.Q0_def a).mpr <| Or.inr
        ⟨hch.1.1.hA.A1.Q_le_H (by rw [← hSQ]; exact haS),
          ⟨haNe, haSq⟩⟩
    have hm : 2 ≤ m := by
      by_contra hm
      have hm' : m = 0 ∨ m = 1 := by omega
      rcases hm' with rfl | rfl
      · exact haOrderNeOne (by simpa using haOrder)
      · exact haOrderNeTwo (by simpa using haOrder)
    have hFourDvd : 4 ∣ orderOf aS := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ∣ 2 ^ m := Nat.pow_dvd_pow 2 hm
        _ = orderOf aS := haOrder.symm
    let yS : S := aS ^ (orderOf aS / 4)
    have hyOrder : orderOf yS = 4 :=
      orderOf_pow_orderOf_div (orderOf_pos aS).ne' hFourDvd
    let z : G := ((yS ^ 2 : S) : G)
    have hzOrder : orderOf z = 2 := by
      calc
        orderOf z = orderOf (yS ^ 2) := Subgroup.orderOf_coe (yS ^ 2)
        _ = orderOf yS / Nat.gcd (orderOf yS) 2 :=
          orderOf_pow' (x := yS) (n := 2) (by norm_num)
        _ = 2 := by norm_num [hyOrder]
    have hzInvolution : IsInvolution z := by
      rcases orderOf_eq_prime_iff.mp hzOrder with ⟨hzSq, hzNe⟩
      exact ⟨hzNe, hzSq⟩
    have hzH : z ∈ H := by
      exact hch.1.1.hA.A1.Q_le_H
        (by rw [← hSQ]; exact (yS ^ 2).property)
    rcases
        ((PFchapter1section1.proposition_3 H D Q t hch.1.1.hA.A1).2
          z hzH hzInvolution s).1 ⟨hch.1.2.1, hch.1.2.2.1⟩ with
      ⟨k, hkSet, hkSquare⟩
    have hkK : k ∈ K := (hch.1.1.K_def k).mpr hkSet
    letI : (Q.subgroupOf H).Normal := hch.1.1.hA.A1.Q_normal_in_H
    have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf hch.1.1.hA.A1.Q_le_H
    have hDnormS : D ≤ Subgroup.normalizer (S : Set G) := by
      rw [hSQ]
      exact hch.1.1.hA.A1.D_le_H.trans hHnormQ
    have hkNormS : k ∈ Subgroup.normalizer (S : Set G) :=
      hDnormS (hch.1.1.K_le_D hkK)
    let x : G := rightConjugateElem (yS : G) k
    have hxS : x ∈ S := by
      have hkInvNorm : k⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
        (Subgroup.normalizer (S : Set G)).inv_mem hkNormS
      have hyMem : (yS : G) ∈ S := yS.property
      have hconj :=
        (Subgroup.mem_normalizer_iff.mp hkInvNorm (yS : G)).1 hyMem
      simpa [x, rightConjugateElem] using hconj
    have hxSquare : x ^ 2 = s := by
      calc
        x ^ 2 = rightConjugateElem z k := by
          simp [x, z, rightConjugateElem, pow_two, mul_assoc]
        _ = s := hkSquare
    have hsQ0 : s ∈ Q0 :=
      (hch.1.1.Q0_def s).mpr (Or.inr ⟨hch.1.2.1, hch.1.2.2.1⟩)
    have hsS : s ∈ S := hQ0leS hsQ0
    let xSub : S := ⟨x, hxS⟩
    let sSub : S := ⟨s, hsS⟩
    have hxSquareSub : xSub ^ 2 = sSub := by
      apply Subtype.ext
      exact hxSquare
    have hQ0Square : ∀ q : Q0, q ^ 2 = 1 :=
      (PFchapter1section2.proposition_1_c
        H D Q K V W Q0 S Q1 t hch.1.1).2.2
    letI : IsMulCommutative S := hcomm
    letI : CommGroup S := IsMulCommutative.instCommGroup
    have hVeq :
        V = D ⊓ Subgroup.centralizer ({s} : Set G) := by
      calc
        V = peterfalviV D t := hch.1.1.V_eq
        _ = D ⊓ Subgroup.centralizer ({s} : Set G) :=
          (PFchapter1section1.proposition_5 H D Q t s
            hch.1.1.hA.A1 hch.1.2.1 hch.1.2.2.1 hch.1.2.2.2).1
    have hVleCentralizerS : V ≤ Subgroup.centralizer ({s} : Set G) := by
      rw [hVeq]
      exact inf_le_right
    have hPnormS : P ≤ Subgroup.normalizer (S : Set G) :=
      hPV.trans (hVleD.trans hDnormS)
    letI : Subgroup.Normalizes P S := ⟨hPnormS⟩
    let Root : SubMulAction P S :=
      { carrier := {r : S | r ^ 2 = sSub}
        smul_mem' := by
          intro c r hr
          change (c • r) ^ 2 = sSub
          rw [← smul_pow', hr]
          apply Subtype.ext
          change (c : G) * s * (c : G)⁻¹ = s
          have hcCent := hVleCentralizerS (hPV c.property)
          have hcComm : (c : G) * s = s * (c : G) :=
            Subgroup.mem_centralizer_singleton_iff.mp hcCent
          rw [hcComm]
          simp }
    let rootEquiv : Q0 ≃ Root :=
      { toFun := fun q =>
          let qS : S := ⟨q, hQ0leS q.property⟩
          ⟨xSub * qS, by
            change (xSub * qS) ^ 2 = sSub
            have hqSq : qS ^ 2 = 1 := by
              apply Subtype.ext
              exact congrArg (fun z : Q0 => (z : G)) (hQ0Square q)
            rw [mul_pow, hxSquareSub, hqSq, mul_one]⟩
        invFun := fun r =>
          let qS : S := xSub⁻¹ * (r : S)
          ⟨(qS : G), by
            have hqSq : qS ^ 2 = 1 := by
              dsimp [qS]
              rw [mul_pow, inv_pow, hxSquareSub, r.property]
              simp
            rw [hch.1.1.Q0_def]
            by_cases hqOne : (qS : G) = 1
            · exact Or.inl hqOne
            · exact Or.inr
                ⟨hch.1.1.hA.A1.Q_le_H
                    (by rw [← hSQ]; exact qS.property),
                  ⟨hqOne, congrArg (fun z : S => (z : G)) hqSq⟩⟩⟩
        left_inv := by
          intro q
          apply Subtype.ext
          dsimp
          simp
        right_inv := by
          intro r
          apply Subtype.ext
          change xSub * (xSub⁻¹ * (r : S)) = (r : S)
          simp }
    have hRootCard : Nat.card Root = Nat.card Q0 :=
      (Nat.card_congr rootEquiv).symm
    have hpDvdD : p ∣ Nat.card D := by
      rw [← hPcard]
      exact Subgroup.card_dvd_of_le (hPV.trans hVleD)
    have hpOdd : Odd p := hch.1.1.hA.A1.D_odd.of_dvd_nat hpDvdD
    have hpNeTwo : p ≠ 2 := by
      intro hpTwo
      apply hpOdd.not_two_dvd_nat
      simp [hpTwo]
    have hpNotDvdRoot : ¬ p ∣ Nat.card Root := by
      intro hpRoot
      have hpQ0 : p ∣ Nat.card Q0 := by
        rw [← hRootCard]
        exact hpRoot
      have hpSCard : p ∣ Nat.card S :=
        hpQ0.trans (Subgroup.card_dvd_of_le hQ0leS)
      obtain ⟨n, hSCard⟩ := hSpgroup.exists_card_eq
      rw [hSCard] at hpSCard
      have hpTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpSCard
      rcases (Nat.dvd_prime Nat.prime_two).mp hpTwo with hpOne | hpTwo
      · exact hp.ne_one hpOne
      · exact hpNeTwo hpTwo
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    have hPpgroup : IsPGroup p P :=
      IsPGroup.of_card (n := 1) (by simpa using hPcard)
    rcases hPpgroup.nonempty_fixed_point_of_prime_not_dvd_card
        Root hpNotDvdRoot with ⟨r, hrFixed⟩
    have hrFix : ∀ c : P, c • r = r :=
      MulAction.mem_fixedPoints.mp hrFixed
    have hrCentralizer : ((r : S) : G) ∈
        Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hcP
      let cP : P := ⟨c, hcP⟩
      have hfixS : cP • (r : S) = (r : S) :=
        congrArg Subtype.val (hrFix cP)
      have hfixG : c * ((r : S) : G) * c⁻¹ = ((r : S) : G) := by
        simpa [cP,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            congrArg (fun z : S => (z : G)) hfixS
      have hmul := congrArg (fun z : G => z * c) hfixG
      have hcomm : c * ((r : S) : G) = ((r : S) : G) * c := by
        simpa [mul_assoc] using hmul
      exact hcomm
    have hrCX : ((r : S) : G) ∈ CX :=
      ⟨hrCentralizer, by rw [← hSQ]; exact (r : S).property⟩
    have hrQ0 : ((r : S) : G) ∈ Q0 := hcentralizer_le_Q0 hrCX
    have hrSqOne : (r : S) ^ 2 = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : Q0 => (z : G))
        (hQ0Square ⟨((r : S) : G), hrQ0⟩)
    have hsSubOne : sSub = 1 := by
      calc
        sSub = (r : S) ^ 2 := r.property.symm
        _ = 1 := hrSqOne
    exact hch.1.2.2.1.ne_one
      (congrArg (fun z : S => (z : G)) hsSubOne)
  have htypeACase :
      IsSuzukiTwoTypeA S → orderOf (s * t) = 5 ∧ W = ⊥ := by
    intro htypeA
    have hVleD : V ≤ D := by
      intro x hxV
      rw [hch.1.1.2.2.2.1] at hxV
      exact hxV.1
    have hD_faithful_on_S :
        D ⊓ Subgroup.centralizer (S : Set G) = ⊥ := by
      have hcore := (PFchapter1section1.proposition_4_c H D Q t s
        hch.1.1.1.A1 hch.1.2.1 hch.1.2.2.1 hch.1.2.2.2).1
      rw [← hSQ] at hcore
      rw [← hcore, eq_bot_iff]
      intro x hxCore
      have hfix : ∀ omega : Ω, x • omega = omega := by
        have hxAll : ∀ point : Ω, x ∈ MulAction.stabilizer G point := by
          simpa [pointStabilizerCore] using hxCore
        intro omega
        exact MulAction.mem_stabilizer_iff.mp (hxAll omega)
      have hxOne : x = 1 :=
        (faithfulSMul_iff.mp hch.1.1.1.A2) x hfix
      simp [hxOne]
    have hSuzuki : IsSuzukiTwoGroup S := by
      rcases PFchapter1section2.corollary
          H D Q K V W Q0 S Q1 t hch.1.1 with hcomm | hSuzuki
      · exact False.elim (htypeANotCommutative S htypeA hcomm)
      · exact hSuzuki
    letI : (Q.subgroupOf H).Normal := hch.1.1.hA.A1.Q_normal_in_H
    have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf hch.1.1.hA.A1.Q_le_H
    have hDnormS : D ≤ Subgroup.normalizer (S : Set G) := by
      rw [hSQ]
      exact hch.1.1.hA.A1.D_le_H.trans hHnormQ
    have hKnormS : K ≤ Subgroup.normalizer (S : Set G) :=
      hch.1.1.K_le_D.trans hDnormS
    letI : Subgroup.Normalizes K S := ⟨hKnormS⟩
    have hKcyclic : IsCyclic K :=
      (PFchapter1section2.proposition_2
        H D Q K V W Q0 S Q1 t hch.1.1).1
    have hKfaithful : FaithfulSMul K S := by
      rw [faithfulSMul_iff]
      intro k hkfix
      have hkCentralizer : (k : G) ∈
          Subgroup.centralizer (S : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hxS
        let xS : S := ⟨x, hxS⟩
        have hfix := hkfix xS
        have hconj : (k : G) * x * (k : G)⁻¹ = x := by
          simpa [xS,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
              congrArg (fun z : S => (z : G)) hfix
        have hmul := congrArg (fun z : G => z * (k : G)) hconj
        simpa [mul_assoc] using hmul.symm
      have hkBot : (k : G) ∈ (⊥ : Subgroup G) := by
        rw [← hD_faithful_on_S]
        exact ⟨hch.1.1.K_le_D k.property, hkCentralizer⟩
      apply Subtype.ext
      simpa using hkBot
    have hrightConjugateInjective :
        ∀ (x : S) (hx : IsInvolution x),
          Function.Injective
            (fun k : {a : G // a ∈ peterfalviKSet D t} =>
              (⟨rightConjugateElem (x : G) (k : G),
                ((PFchapter1section1.proposition_3 H D Q t
                    hch.1.1.hA.A1).2
                  (x : G)
                  (hch.1.1.hA.A1.Q_le_H
                    (by rw [← hSQ]; exact x.property))
                  ⟨(by
                      intro hxOne
                      exact hx.ne_one (Subtype.ext hxOne)),
                    congrArg (fun z : S => (z : G)) hx.sq_eq_one⟩
                  (rightConjugateElem (x : G) (k : G))).2
                    ⟨k, k.property, rfl⟩⟩ :
                {y : G // y ∈ H ∧ IsInvolution y})) := by
      intro x hx
      let KSet : Type _ := {a : G // a ∈ peterfalviKSet D t}
      let HInv : Type _ := {y : G // y ∈ H ∧ IsInvolution y}
      have hxG : IsInvolution (x : G) := by
        exact ⟨fun hxOne => hx.ne_one (Subtype.ext hxOne),
          congrArg (fun z : S => (z : G)) hx.sq_eq_one⟩
      have hxH : (x : G) ∈ H :=
        hch.1.1.hA.A1.Q_le_H (by rw [← hSQ]; exact x.property)
      let phi : KSet → HInv := fun k =>
        ⟨rightConjugateElem (x : G) (k : G),
          ((PFchapter1section1.proposition_3 H D Q t
              hch.1.1.hA.A1).2 (x : G) hxH hxG
            (rightConjugateElem (x : G) (k : G))).2
              ⟨k, k.property, rfl⟩⟩
      have hphiSurjective : Function.Surjective phi := by
        rintro ⟨y, hy⟩
        rcases ((PFchapter1section1.proposition_3 H D Q t
            hch.1.1.hA.A1).2 (x : G) hxH hxG y).1 hy with
          ⟨k, hk, hkEq⟩
        refine ⟨⟨k, hk⟩, ?_⟩
        apply Subtype.ext
        exact hkEq
      have hphiInjective : Function.Injective phi :=
        (hphiSurjective.bijective_of_nat_card_le
          (by simpa [KSet, HInv] using
            le_of_eq (PFchapter1section1.proposition_3 H D Q t
              hch.1.1.hA.A1).1)).1
      simpa [phi, KSet, HInv, hxG, hxH] using hphiInjective
    have hKregular : ActionRegularOn K S (involutions S) := by
      constructor
      · intro x hx k
        have hxG : IsInvolution (x : G) :=
          ⟨fun hxOne => hx.ne_one (Subtype.ext hxOne),
            congrArg (fun z : S => (z : G)) hx.sq_eq_one⟩
        have hconj := isInvolution_rightConjugateElem
          (g := ((k⁻¹ : K) : G)) hxG
        constructor
        · intro hOne
          apply hconj.ne_one
          simpa [rightConjugateElem,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
              congrArg (fun z : S => (z : G)) hOne
        · apply Subtype.ext
          simpa [rightConjugateElem,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
              hconj.sq_eq_one
      · intro x hx y hy
        have hxG : IsInvolution (x : G) :=
          ⟨fun hxOne => hx.ne_one (Subtype.ext hxOne),
            congrArg (fun z : S => (z : G)) hx.sq_eq_one⟩
        have hyG : IsInvolution (y : G) :=
          ⟨fun hyOne => hy.ne_one (Subtype.ext hyOne),
            congrArg (fun z : S => (z : G)) hy.sq_eq_one⟩
        have hxH : (x : G) ∈ H :=
          hch.1.1.hA.A1.Q_le_H (by rw [← hSQ]; exact x.property)
        have hyH : (y : G) ∈ H :=
          hch.1.1.hA.A1.Q_le_H (by rw [← hSQ]; exact y.property)
        rcases ((PFchapter1section1.proposition_3 H D Q t
            hch.1.1.hA.A1).2 (x : G) hxH hxG (y : G)).1
            ⟨hyH, hyG⟩ with ⟨a, haSet, haEq⟩
        have haK : a ∈ K := (hch.1.1.K_def a).mpr haSet
        let k : K := ⟨a⁻¹, K.inv_mem haK⟩
        refine ⟨k, ?_, ?_⟩
        · apply Subtype.ext
          simpa [k, rightConjugateElem,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using haEq.symm
        · intro b hb
          let aSet : {z : G // z ∈ peterfalviKSet D t} := ⟨a, haSet⟩
          let bSet : {z : G // z ∈ peterfalviKSet D t} :=
            ⟨((b⁻¹ : K) : G),
              (hch.1.1.K_def ((b⁻¹ : K) : G)).mp (b⁻¹ : K).property⟩
          have hbRight :
              rightConjugateElem (x : G) (bSet : G) = (y : G) := by
            have hbVal := congrArg (fun z : S => (z : G)) hb
            simpa [bSet, rightConjugateElem,
              Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hbVal.symm
          have hba : bSet = aSet :=
            hrightConjugateInjective x hx
              (by apply Subtype.ext; exact hbRight.trans haEq.symm)
          apply Subtype.ext
          change (b : G) = a⁻¹
          have hval : ((b⁻¹ : K) : G) = a :=
            congrArg Subtype.val hba
          simpa using congrArg Inv.inv hval
    have htypeACardCenterSquare :
        Nat.card S = Nat.card (Subgroup.center S) ^ 2 := by
      rcases htypeA with
        ⟨n, hn, theta, pairLift, cocycle, _hperiod, _htheta,
          haddLeft, haddRight, _hdiag, hmem, _hone, hsurj, hinj, hmul⟩
      let F := BinaryGaloisField n
      let pairFun : F × F → S := fun az =>
        ⟨pairLift az.1 az.2, hmem az.1 az.2⟩
      have hpairBijective : Function.Bijective pairFun := by
        constructor
        · intro az bw hab
          have hval := congrArg (fun z : S => (z : G)) hab
          rcases hinj az.1 az.2 bw.1 bw.2 hval with ⟨h1, h2⟩
          exact Prod.ext h1 h2
        · intro x
          rcases hsurj x x.property with ⟨a, z, hx⟩
          exact ⟨(a, z), Subtype.ext hx.symm⟩
      let pairEquiv : F × F ≃ S := Equiv.ofBijective pairFun hpairBijective
      have hzeroLeft : ∀ a : F, cocycle 0 a = 0 := by
        intro a
        have h := haddLeft 0 0 a
        simpa only [zero_add, CharTwo.add_self_eq_zero] using h
      have hzeroRight : ∀ a : F, cocycle a 0 = 0 := by
        intro a
        have h := haddRight a 0 0
        simpa only [zero_add, CharTwo.add_self_eq_zero] using h
      let centerMap : F → Subgroup.center S := fun z =>
        ⟨⟨pairLift 0 z, hmem 0 z⟩, by
          rw [Subgroup.mem_center_iff]
          intro x
          rcases hsurj x x.property with ⟨a, w, hx⟩
          apply Subtype.ext
          change (x : G) * pairLift 0 z = pairLift 0 z * (x : G)
          rw [hx]
          rw [hmul, hmul, hzeroLeft, hzeroRight]
          simp [add_comm]⟩
      have hcenterMapInjective : Function.Injective centerMap := by
        intro z w hzw
        have hval := congrArg (fun x : Subgroup.center S => ((x : S) : G)) hzw
        exact (hinj 0 z 0 w hval).2
      have hFcard : Nat.card F = 2 ^ n := by
        simpa [F, BinaryGaloisField] using GaloisField.card 2 n hn
      have hSCard : Nat.card S = (2 ^ n) ^ 2 := by
        calc
          Nat.card S = Nat.card (F × F) := (Nat.card_congr pairEquiv).symm
          _ = Nat.card F * Nat.card F := Nat.card_prod F F
          _ = (2 ^ n) ^ 2 := by rw [hFcard]; ring
      have hcenterLower : 2 ^ n ≤ Nat.card (Subgroup.center S) := by
        rw [← hFcard]
        exact Nat.card_le_card_of_injective centerMap hcenterMapInjective
      rcases (higmanTheorem_center_quotient_orders_and_exponent
          hSuzuki).2.2.2.1 with hSquare | hCube
      · exact hSquare
      · have hqTwo : 2 ≤ 2 ^ n := by
          exact Nat.one_lt_two_pow hn
        have hle : (2 ^ n) ^ 3 ≤ (2 ^ n) ^ 2 := by
          calc
            (2 ^ n) ^ 3 ≤ Nat.card (Subgroup.center S) ^ 3 :=
              Nat.pow_le_pow_left hcenterLower 3
            _ = Nat.card S := hCube.symm
            _ = (2 ^ n) ^ 2 := hSCard
        nlinarith [sq_nonneg ((2 ^ n : ℤ) - 1)]
    rcases higmanTheorem_order_center_sq_typeA
        hSuzuki hKcyclic hKfaithful hKregular htypeACardCenterSquare with
      ⟨typeAN, _htypeAN, typeATheta, typeAPairLift, typeACocycle,
        typeAEK, typeAEQ, typeAEZ, _typeAPeriod, _typeAThetaNontrivial,
        _typeAAddLeft, _typeAAddRight, _typeADiag, _typeAMem,
        _typeAOne, _typeASurj, _typeAInj, _typeAMul, _typeACenterCard,
        typeAQuotientAction, _typeACenterAction⟩
    have htypeAInfrastructure :
        (∀ (P : Subgroup G) (p : ℕ),
          P ≤ V → Nat.Prime p → Nat.card P = p →
            ∃ r : G,
              r ∈ Subgroup.centralizer (P : Set G) ⊓ S ∧ r ^ 2 = s) ∧
        (∀ x y : S, x ^ 2 = y ^ 2 →
          QuotientGroup.mk' (Subgroup.center S) x =
            QuotientGroup.mk' (Subgroup.center S) y) := by
      rcases htypeA with
        ⟨n, hn, theta, pairLift, cocycle, hperiod, _htheta,
          haddLeft, haddRight, hdiag, hmem, hone, hsurj, hinj, hmul⟩
      let F := BinaryGaloisField n
      have hnormInjective :
          Function.Injective (fun a : F => a * theta a) := by
        intro a b hab
        change a * theta a = b * theta b at hab
        by_cases ha : a = 0
        · subst a
          have hbProd : b * theta b = 0 := by simpa using hab.symm
          rcases mul_eq_zero.mp hbProd with hb | hthetaB
          · exact hb.symm
          · exact (theta.map_eq_zero_iff.mp hthetaB).symm
        have hb : b ≠ 0 := by
          intro hb
          subst b
          have haProd : a * theta a = 0 := by simpa using hab
          exact (mul_ne_zero ha ((map_ne_zero theta).mpr ha)) haProd
        let c : F := a * b⁻¹
        have hc : c ≠ 0 := mul_ne_zero ha (inv_ne_zero hb)
        have hcNorm : c * theta c = 1 := by
          calc
            c * theta c =
                (a * theta a) * (b * theta b)⁻¹ := by
              dsimp [c]
              rw [map_mul, map_inv₀]
              simp only [mul_inv_rev]
              simp only [mul_assoc]
              apply congrArg (fun z : F => a * z)
              calc
                b⁻¹ * (theta a * (theta b)⁻¹) =
                    theta a * (b⁻¹ * (theta b)⁻¹) := by rw [mul_left_comm]
                _ = theta a * ((theta b)⁻¹ * b⁻¹) := by
                  rw [mul_comm b⁻¹ (theta b)⁻¹]
            _ = 1 := by rw [hab]; exact mul_inv_cancel₀ (mul_ne_zero hb
              ((map_ne_zero theta).mpr hb))
        have hthetaC : theta c = c⁻¹ := by
          calc
            theta c = c⁻¹ * (c * theta c) := by
              rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
            _ = c⁻¹ := by rw [hcNorm, mul_one]
        have hthetaTwo : theta^[2] c = c := by
          calc
            theta^[2] c = theta (theta c) := by
              simp [Function.iterate_succ_apply']
            _ = theta (c⁻¹) := by rw [hthetaC]
            _ = (theta c)⁻¹ := map_inv₀ theta c
            _ = (c⁻¹)⁻¹ := by rw [hthetaC]
            _ = c := inv_inv c
        have hEvenIter : ∀ j : ℕ, theta^[2 * j] c = c := by
          intro j
          induction j with
          | zero => simp
          | succ j ih =>
              rw [Nat.mul_succ, Function.iterate_add_apply, hthetaTwo, ih]
        rcases hperiod with ⟨period, hperiodOdd, _hperiodPos, hperiodEq⟩
        rcases hperiodOdd with ⟨j, hj⟩
        have hOddIter : theta^[period] c = c⁻¹ := by
          rw [hj]
          calc
            theta^[2 * j + 1] c = theta^[1 + 2 * j] c := by (congr 1; omega)
            _ = theta (theta^[2 * j] c) := by
              rw [Function.iterate_add_apply]
              simp
            _ = theta c := by rw [hEvenIter]
            _ = c⁻¹ := hthetaC
        have hcInv : c = c⁻¹ := (hperiodEq c).symm.trans hOddIter
        have hcSq : c * c = 1 := by
          nth_rw 1 [hcInv]
          exact inv_mul_cancel₀ hc
        have hcOne : c = 1 := by
          rcases mul_self_eq_one_iff.mp hcSq with hcOne | hcNeg
          · exact hcOne
          · simpa only [CharTwo.neg_eq] using hcNeg
        exact (mul_inv_eq_one₀ hb).mp hcOne
      have hnormBijective :
          Function.Bijective (fun a : F => a * theta a) :=
        hnormInjective.bijective_of_finite
      let pairFun : F × F → S := fun az =>
        ⟨pairLift az.1 az.2, hmem az.1 az.2⟩
      have hpairBijective : Function.Bijective pairFun := by
        constructor
        · intro az bw hab
          have hval := congrArg (fun z : S => (z : G)) hab
          rcases hinj az.1 az.2 bw.1 bw.2 hval with ⟨h1, h2⟩
          exact Prod.ext h1 h2
        · intro x
          rcases hsurj x x.property with ⟨a, z, hx⟩
          exact ⟨(a, z), Subtype.ext hx.symm⟩
      let pairEquiv : F × F ≃ S := Equiv.ofBijective pairFun hpairBijective
      have hpairSquare : ∀ a z : F,
          pairLift a z ^ 2 = pairLift 0 (a * theta a) := by
        intro a z
        calc
          pairLift a z ^ 2 =
              pairLift (a + a) (z + z + cocycle a a) := by
            simpa [pow_two] using hmul a z a z
          _ = pairLift 0 (a * theta a) := by
            rw [hdiag, CharTwo.add_self_eq_zero a,
              CharTwo.add_self_eq_zero z, zero_add]
      have hsS : s ∈ S := by
        have hsQ0 : s ∈ Q0 :=
          (hch.1.1.Q0_def s).mpr (Or.inr ⟨hch.1.2.1, hch.1.2.2.1⟩)
        rw [hSQ]
        exact hch.1.1.Q0_le_Q hsQ0
      let sSub : S := ⟨s, hsS⟩
      let sc : F × F := pairEquiv.symm sSub
      have hsCoord : pairLift sc.1 sc.2 = s := by
        exact congrArg (fun z : S => (z : G)) (pairEquiv.apply_symm_apply sSub)
      have hsNormZero : sc.1 * theta sc.1 = 0 := by
        have hsq : pairLift sc.1 sc.2 ^ 2 = 1 := by
          rw [hsCoord]
          exact hch.1.2.2.1.sq_eq_one
        have hcoordEq : pairLift 0 (sc.1 * theta sc.1) = pairLift 0 0 := by
          calc
            pairLift 0 (sc.1 * theta sc.1) =
                pairLift sc.1 sc.2 ^ 2 := (hpairSquare sc.1 sc.2).symm
            _ = 1 := hsq
            _ = pairLift 0 0 := hone.symm
        exact (hinj 0 (sc.1 * theta sc.1) 0 0 hcoordEq).2
      have hsFirst : sc.1 = 0 := by
        rcases mul_eq_zero.mp hsNormZero with hzero | hzero
        · exact hzero
        · exact theta.map_eq_zero_iff.mp hzero
      have hsCoordZero : pairLift 0 sc.2 = s := by
        simpa [hsFirst] using hsCoord
      obtain ⟨rootFirst, hrootFirst⟩ := hnormBijective.surjective sc.2
      change rootFirst * theta rootFirst = sc.2 at hrootFirst
      constructor
      · intro P p hPV' hp hPcard
        have hPnormS : P ≤ Subgroup.normalizer (S : Set G) := by
          letI : (Q.subgroupOf H).Normal := hch.1.1.hA.A1.Q_normal_in_H
          have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) :=
            Subgroup.le_normalizer_of_normal_subgroupOf hch.1.1.hA.A1.Q_le_H
          have hDnormS : D ≤ Subgroup.normalizer (S : Set G) := by
            rw [hSQ]
            exact hch.1.1.hA.A1.D_le_H.trans hHnormQ
          exact hPV'.trans (hVleD.trans hDnormS)
        have hVeq : V = D ⊓ Subgroup.centralizer ({s} : Set G) := by
          calc
            V = peterfalviV D t := hch.1.1.V_eq
            _ = D ⊓ Subgroup.centralizer ({s} : Set G) :=
              (PFchapter1section1.proposition_5 H D Q t s
                hch.1.1.hA.A1 hch.1.2.1 hch.1.2.2.1 hch.1.2.2.2).1
        have hPcentralizesS : P ≤ Subgroup.centralizer ({s} : Set G) := by
          intro c hc
          have hcV := hPV' hc
          rw [hVeq] at hcV
          exact hcV.2
        letI : Subgroup.Normalizes P S := ⟨hPnormS⟩
        let Root : SubMulAction P S :=
          { carrier := {r : S | r ^ 2 = sSub}
            smul_mem' := by
              intro c r hr
              change (c • r) ^ 2 = sSub
              rw [← smul_pow', hr]
              apply Subtype.ext
              change (c : G) * s * (c : G)⁻¹ = s
              have hcComm : (c : G) * s = s * (c : G) :=
                Subgroup.mem_centralizer_singleton_iff.mp
                  (hPcentralizesS c.property)
              rw [hcComm]
              simp }
        let rootEquiv : F ≃ Root :=
          { toFun := fun z =>
              ⟨pairEquiv (rootFirst, z), by
                apply Subtype.ext
                change pairLift rootFirst z ^ 2 = s
                rw [hpairSquare, hrootFirst, hsCoordZero]⟩
            invFun := fun r => (pairEquiv.symm (r : S)).2
            left_inv := by
              intro z
              exact congrArg Prod.snd (pairEquiv.symm_apply_apply (rootFirst, z))
            right_inv := by
              intro r
              let rc : F × F := pairEquiv.symm (r : S)
              have hrCoord : pairLift rc.1 rc.2 = ((r : S) : G) := by
                exact congrArg (fun z : S => (z : G))
                  (pairEquiv.apply_symm_apply (r : S))
              have hrNorm : rc.1 * theta rc.1 = sc.2 := by
                have hcoordEq :
                    pairLift 0 (rc.1 * theta rc.1) = pairLift 0 sc.2 := by
                  calc
                    pairLift 0 (rc.1 * theta rc.1) =
                        pairLift rc.1 rc.2 ^ 2 := (hpairSquare rc.1 rc.2).symm
                    _ = ((r : S) : G) ^ 2 := by rw [hrCoord]
                    _ = s := congrArg (fun z : S => (z : G)) r.property
                    _ = pairLift 0 sc.2 := hsCoordZero.symm
                exact (hinj 0 (rc.1 * theta rc.1) 0 sc.2 hcoordEq).2
              have hrFirst : rc.1 = rootFirst :=
                hnormInjective (hrNorm.trans hrootFirst.symm)
              apply Subtype.ext
              change pairEquiv (rootFirst, rc.2) = (r : S)
              calc
                pairEquiv (rootFirst, rc.2) = pairEquiv rc := by rw [← hrFirst]
                _ = (r : S) := pairEquiv.apply_symm_apply (r : S) }
        have hRootCard : Nat.card Root = 2 ^ n := by
          calc
            Nat.card Root = Nat.card F := (Nat.card_congr rootEquiv).symm
            _ = 2 ^ n := by
              simpa [F, BinaryGaloisField] using GaloisField.card 2 n hn
        have hpDvdD : p ∣ Nat.card D := by
          rw [← hPcard]
          exact Subgroup.card_dvd_of_le (hPV'.trans hVleD)
        have hpOdd : Odd p := hch.1.1.hA.A1.D_odd.of_dvd_nat hpDvdD
        have hpNeTwo : p ≠ 2 := by
          intro hpTwo
          apply hpOdd.not_two_dvd_nat
          simp [hpTwo]
        have hpNotDvdRoot : ¬ p ∣ Nat.card Root := by
          rw [hRootCard]
          intro hpPow
          have hpTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpPow
          rcases (Nat.dvd_prime Nat.prime_two).mp hpTwo with hpOne | hpTwo
          · exact hp.ne_one hpOne
          · exact hpNeTwo hpTwo
        letI : Fact (Nat.Prime p) := ⟨hp⟩
        have hPpgroup : IsPGroup p P :=
          IsPGroup.of_card (n := 1) (by simpa using hPcard)
        rcases hPpgroup.nonempty_fixed_point_of_prime_not_dvd_card
            Root hpNotDvdRoot with ⟨r, hrFixed⟩
        have hrFix : ∀ c : P, c • r = r :=
          MulAction.mem_fixedPoints.mp hrFixed
        have hrCentralizer : ((r : S) : G) ∈
            Subgroup.centralizer (P : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro c hcP
          let cP : P := ⟨c, hcP⟩
          have hfixS : cP • (r : S) = (r : S) :=
            congrArg Subtype.val (hrFix cP)
          have hfixG : c * ((r : S) : G) * c⁻¹ = ((r : S) : G) := by
            simpa [cP,
              Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
                congrArg (fun z : S => (z : G)) hfixS
          have hmul := congrArg (fun z : G => z * c) hfixG
          simpa [mul_assoc] using hmul
        exact ⟨((r : S) : G), ⟨hrCentralizer, (r : S).property⟩,
          congrArg (fun z : S => (z : G)) r.property⟩
      · intro x y hxySquare
        let xc : F × F := pairEquiv.symm x
        let yc : F × F := pairEquiv.symm y
        have hxCoord : pairLift xc.1 xc.2 = (x : G) :=
          congrArg (fun z : S => (z : G)) (pairEquiv.apply_symm_apply x)
        have hyCoord : pairLift yc.1 yc.2 = (y : G) :=
          congrArg (fun z : S => (z : G)) (pairEquiv.apply_symm_apply y)
        have hnormEq : xc.1 * theta xc.1 = yc.1 * theta yc.1 := by
          have hcoordEq :
              pairLift 0 (xc.1 * theta xc.1) =
                pairLift 0 (yc.1 * theta yc.1) := by
            calc
              pairLift 0 (xc.1 * theta xc.1) =
                  pairLift xc.1 xc.2 ^ 2 := (hpairSquare xc.1 xc.2).symm
              _ = (x : G) ^ 2 := by rw [hxCoord]
              _ = (y : G) ^ 2 := congrArg (fun z : S => (z : G)) hxySquare
              _ = pairLift yc.1 yc.2 ^ 2 := by rw [hyCoord]
              _ = pairLift 0 (yc.1 * theta yc.1) := hpairSquare yc.1 yc.2
          exact (hinj 0 (xc.1 * theta xc.1)
            0 (yc.1 * theta yc.1) hcoordEq).2
        have hfirstEq : xc.1 = yc.1 := hnormInjective hnormEq
        have hzeroLeft : ∀ a : F, cocycle 0 a = 0 := by
          intro a
          have h := haddLeft 0 0 a
          simpa only [zero_add, CharTwo.add_self_eq_zero] using h
        have hzeroRight : ∀ a : F, cocycle a 0 = 0 := by
          intro a
          have h := haddRight a 0 0
          simpa only [zero_add, CharTwo.add_self_eq_zero] using h
        let delta : F := yc.2 - xc.2
        let zS : S := ⟨pairLift 0 delta, hmem 0 delta⟩
        have hzCenter : zS ∈ Subgroup.center S := by
          rw [Subgroup.mem_center_iff]
          intro q
          rcases hsurj q q.property with ⟨a, w, hq⟩
          apply Subtype.ext
          change (q : G) * pairLift 0 delta = pairLift 0 delta * (q : G)
          rw [hq, hmul, hmul, hzeroLeft, hzeroRight]
          simp [add_comm]
        have hyEq : y = x * zS := by
          apply Subtype.ext
          change (y : G) = (x : G) * pairLift 0 delta
          rw [← hyCoord, ← hxCoord, hmul, hzeroRight]
          simp only [add_zero, add_zero]
          rw [hfirstEq]
          congr 1
          dsimp [delta]
          ring
        have hzQuotient :
            QuotientGroup.mk' (Subgroup.center S) zS = 1 := by
          change (zS : S ⧸ Subgroup.center S) = 1
          exact (QuotientGroup.eq_one_iff zS).mpr hzCenter
        calc
          QuotientGroup.mk' (Subgroup.center S) x =
              QuotientGroup.mk' (Subgroup.center S) x * 1 := by simp
          _ = QuotientGroup.mk' (Subgroup.center S) x *
              QuotientGroup.mk' (Subgroup.center S) zS := by
                rw [hzQuotient]
          _ = QuotientGroup.mk' (Subgroup.center S) (x * zS) :=
            (map_mul (QuotientGroup.mk' (Subgroup.center S)) x zS).symm
          _ = QuotientGroup.mk' (Subgroup.center S) y :=
            congrArg (QuotientGroup.mk' (Subgroup.center S)) hyEq.symm
    have htypeAFixedSquareRoot := htypeAInfrastructure.1
    have htypeASquareCosetInjective := htypeAInfrastructure.2
    have htypeA_fixed_of_prime_in_W :
        ∀ (P : Subgroup G) (p : ℕ),
          P ≤ W → Nat.Prime p → Nat.card P = p →
            Subgroup.centralizer (P : Set G) ⊓ S = S := by
      intro P p hPW hp hPcard
      have hPV' : P ≤ V := hPW.trans hch.1.1.W_le_V
      rcases htypeAFixedSquareRoot P p hPV' hp hPcard with
        ⟨r, hrFixed, hrSquare⟩
      have hPnormS : P ≤ Subgroup.normalizer (S : Set G) :=
        hPV'.trans (hVleD.trans hDnormS)
      letI : Subgroup.Normalizes P S := ⟨hPnormS⟩
      have hPcommK : ∀ c : P, ∀ k : K,
          ((c : G) * (k : G)) = (k : G) * (c : G) := by
        intro c k
        have hcW := hPW c.property
        rw [hch.1.1.W_eq] at hcW
        have hcCent : (c : G) ∈ Subgroup.centralizer (K : Set G) := hcW.2
        exact (Subgroup.mem_centralizer_iff.mp hcCent (k : G) k.property).symm
      have hWleCentralizerInvolutions :
          W ≤ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) := by
        have hWEq :=
          (PFchapter1section1.proposition_5 H D Q t s
            hch.1.1.hA.A1 hch.1.2.1 hch.1.2.2.1 hch.1.2.2.2).2
        have hKSet : (K : Set G) = peterfalviKSet D t :=
          Set.ext fun x => hch.1.1.K_def x
        rw [hch.1.1.W_eq, hch.1.1.V_eq, hKSet, hWEq]
        exact inf_le_right
      have hPfixCenter : ∀ c : P, ∀ z : Subgroup.center S,
          c • (z : S) = (z : S) := by
        intro c z
        by_cases hzOne : (z : S) = 1
        · simp [hzOne]
        have hzInv : IsInvolution (z : S) := by
          have hzMem : (z : S) ∈ involutions S := by
            rw [(higmanTheorem_involutions_center hSuzuki).1]
            exact ⟨z.property, hzOne⟩
          exact hzMem
        have hzInvG : IsInvolution ((z : S) : G) :=
          ⟨fun hz => hzInv.ne_one (Subtype.ext hz),
            congrArg (fun x : S => (x : G)) hzInv.sq_eq_one⟩
        have hzH : ((z : S) : G) ∈ H :=
          hch.1.1.hA.A1.Q_le_H (by rw [← hSQ]; exact (z : S).property)
        have hcCent := hWleCentralizerInvolutions (hPW c.property)
        have hcComm : (c : G) * ((z : S) : G) =
            ((z : S) : G) * (c : G) :=
          (Subgroup.mem_centralizer_iff.mp hcCent ((z : S) : G)
            ⟨hzH, hzInvG⟩).symm
        apply Subtype.ext
        simp only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        rw [hcComm]
        simp
      letI : IsInvariant P S (Subgroup.center S) := center_isInvariant
      letI : MulDistribMulAction P (S ⧸ Subgroup.center S) :=
        quotientMulDistribMulAction (A := P) (G := S)
          (Subgroup.center S) (inferInstance : IsInvariant P S (Subgroup.center S))
      let rS : S := ⟨r, hrFixed.2⟩
      have hrSsquare : rS ^ 2 = ⟨s, by
          rw [hSQ]
          exact hch.1.1.Q0_le_Q
            ((hch.1.1.Q0_def s).mpr
              (Or.inr ⟨hch.1.2.1, hch.1.2.2.1⟩))⟩ := by
        apply Subtype.ext
        exact hrSquare
      have hrNotCenter : rS ∉ Subgroup.center S := by
        intro hrCenter
        have hrPow : (⟨rS, hrCenter⟩ : Subgroup.center S) ^ 2 = 1 :=
          (higmanTheorem_involutions_center hSuzuki).2
            ⟨rS, hrCenter⟩
        apply hch.1.2.2.1.ne_one
        calc
          s = r ^ 2 := hrSquare.symm
          _ = 1 := congrArg (fun z : Subgroup.center S => ((z : S) : G)) hrPow
      let rbar : S ⧸ Subgroup.center S := QuotientGroup.mk' (Subgroup.center S) rS
      have hrbarNe : rbar ≠ 1 := by
        intro hrOne
        exact hrNotCenter ((QuotientGroup.eq_one_iff rS).mp hrOne)
      have hrCoordNe :
          (typeAEQ rbar).toAdd ≠ 0 := by
        intro hrZero
        apply hrbarNe
        apply typeAEQ.injective
        apply Multiplicative.toAdd.injective
        simpa using hrZero
      have hquotientTransitive :
          ∀ y : S ⧸ Subgroup.center S, y ≠ 1 →
            ∃ k : K,
              QuotientGroup.mk' (Subgroup.center S) (k • rS) = y := by
        intro y hy
        have hyCoordNe : (typeAEQ y).toAdd ≠ 0 := by
          intro hyZero
          apply hy
          apply typeAEQ.injective
          apply Multiplicative.toAdd.injective
          simpa using hyZero
        let u : (BinaryGaloisField typeAN)ˣ :=
          Units.mk0 ((typeAEQ y).toAdd * (typeAEQ rbar).toAdd⁻¹)
            (mul_ne_zero hyCoordNe (inv_ne_zero hrCoordNe))
        let k : K := typeAEK.symm u
        refine ⟨k, ?_⟩
        apply typeAEQ.injective
        apply Multiplicative.toAdd.injective
        rw [typeAQuotientAction]
        dsimp [k, u]
        rw [typeAEK.apply_symm_apply]
        change ((typeAEQ y).toAdd * (typeAEQ rbar).toAdd⁻¹) *
            (typeAEQ rbar).toAdd = (typeAEQ y).toAdd
        field_simp
      have hPfixQuotient : ∀ c : P, ∀ y : S ⧸ Subgroup.center S,
          c • y = y := by
        intro c y
        by_cases hyOne : y = 1
        · simp [hyOne]
        rcases hquotientTransitive y hyOne with ⟨k, hk⟩
        have hcR : Commute (c : G) r := by
          exact Subgroup.mem_centralizer_iff.mp hrFixed.1 (c : G) c.property
        have hcK : Commute (c : G) (k : G) := hPcommK c k
        have hcConj : Commute (c : G)
            ((k : G) * r * (k : G)⁻¹) :=
          (hcK.mul_right hcR).mul_right hcK.inv_right
        have hfixRepresentative : c • (k • rS) = k • rS := by
          apply Subtype.ext
          simp only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
          exact hcConj.mul_inv_cancel
        rw [← hk]
        change c • (QuotientGroup.mk (k • rS) :
          S ⧸ Subgroup.center S) = QuotientGroup.mk (k • rS)
        rw [MulAction.Quotient.smul_mk]
        exact congrArg (QuotientGroup.mk' (Subgroup.center S)) hfixRepresentative
      have hfixedQuotientTop :
          fixedPointSubgroup P (S ⧸ Subgroup.center S) = ⊤ := by
        rw [eq_top_iff]
        intro y _hy
        change ∀ c : P, c • y = y
        exact fun c => hPfixQuotient c y
      have hSpgroup : IsPGroup 2 S := by
        rcases hSuzuki.1 with ⟨m, hm⟩
        exact IsPGroup.of_card (by simpa using hm)
      letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      letI : Group.IsNilpotent S := hSpgroup.isNilpotent
      have hSsolvable : Group.IsSolvable S := by infer_instance
      have hpDvdD : p ∣ Nat.card D := by
        rw [← hPcard]
        exact Subgroup.card_dvd_of_le (hPV'.trans hVleD)
      have hpOdd : Odd p := hch.1.1.hA.A1.D_odd.of_dvd_nat hpDvdD
      have hcoprime : Nat.Coprime (Nat.card P) (Nat.card S) := by
        rcases hSuzuki.1 with ⟨m, hm⟩
        have hmS : Nat.card S = 2 ^ m := by simpa using hm
        rw [hPcard, hmS]
        exact hpOdd.coprime_two_right.pow_right m
      have hfixedQuotientMap :=
        fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
          (G := S) (A := P) hSsolvable hcoprime (∅ : Set Nat.Primes)
          (Subgroup.center S)
          (inferInstance : IsInvariant P S (Subgroup.center S))
      rw [hfixedQuotientTop] at hfixedQuotientMap
      have hfixedTop : fixedPointSubgroup P S = ⊤ := by
        rw [eq_top_iff]
        intro y _hy
        have hyMap : QuotientGroup.mk' (Subgroup.center S) y ∈
            (fixedPointSubgroup P S).map
              (QuotientGroup.mk' (Subgroup.center S)) := by
          rw [← hfixedQuotientMap]
          trivial
        rcases Subgroup.mem_map.mp hyMap with ⟨f, hfFixed, hfEq⟩
        let z : S := f⁻¹ * y
        have hzCenter : z ∈ Subgroup.center S := by
          rw [← QuotientGroup.ker_mk' (Subgroup.center S)]
          apply MonoidHom.mem_ker.mpr
          change (QuotientGroup.mk' (Subgroup.center S) f)⁻¹ *
              QuotientGroup.mk' (Subgroup.center S) y = 1
          rw [hfEq]
          simp
        have hzFixed : z ∈ fixedPointSubgroup P S := by
          change ∀ c : P, c • z = z
          intro c
          have := hPfixCenter c ⟨z, hzCenter⟩
          exact this
        have hyEq : f * z = y := by
          dsimp [z]
          simp
        rw [← hyEq]
        exact (fixedPointSubgroup P S).mul_mem hfFixed hzFixed
      apply le_antisymm inf_le_right
      intro x hxS
      refine ⟨?_, hxS⟩
      change x ∈ Subgroup.centralizer (P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro c hcP
      let cP : P := ⟨c, hcP⟩
      have hxFixed : (⟨x, hxS⟩ : S) ∈ fixedPointSubgroup P S := by
        rw [hfixedTop]
        trivial
      have hfix := hxFixed cP
      have hfixG : c * x * c⁻¹ = x := by
        simpa [cP,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            congrArg (fun z : S => (z : G)) hfix
      have hmul := congrArg (fun z : G => z * c) hfixG
      simpa [mul_assoc] using hmul
    have hWbot : W = ⊥ := by
      by_contra hWne
      rcases hprimeSubgroup W hWne with ⟨P, p, hPW, hp, hPcard⟩
      have hfixed :=
        htypeA_fixed_of_prime_in_W P p hPW hp hPcard
      have hPbot : P = ⊥ := by
        rw [eq_bot_iff]
        intro x hxP
        have hxD : x ∈ D :=
          hVleD (hch.1.1.2.2.2.2.1 (hPW hxP))
        have hxCS : x ∈ Subgroup.centralizer (S : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hyS
          have hyCP : y ∈ Subgroup.centralizer (P : Set G) := by
            have hyInf :
                y ∈ Subgroup.centralizer (P : Set G) ⊓ S := by
              rw [hfixed]
              exact hyS
            exact hyInf.1
          exact ((Subgroup.mem_centralizer_iff.mp hyCP) x hxP).symm
        have hxBot : x ∈ (⊥ : Subgroup G) := by
          rw [← hD_faithful_on_S]
          exact ⟨hxD, hxCS⟩
        exact hxBot
      apply hp.ne_one
      calc
        p = Nat.card P := hPcard.symm
        _ = 1 := by rw [hPbot]; simp
    rcases hprimeSubgroup V hch.2.V_ne_bot with
      ⟨P, p, hPV, hp, hPcard⟩
    have hPne : P ≠ ⊥ := by
      intro hPbot
      apply hp.ne_one
      calc
        p = Nat.card P := hPcard.symm
        _ = 1 := by rw [hPbot]; simp
    have hPprime : ∃ q : ℕ, Nat.Prime q ∧ Nat.card P = q :=
      ⟨p, hp, hPcard⟩
    have h2rank :
        TwoRankAtLeastTwo (Subgroup.centralizer (P : Set G)) :=
      hch.2.centralizers_two_rank P hPV hPprime
    let CX : Subgroup G := Subgroup.centralizer (P : Set G) ⊓ Q
    have hlocal :=
      PFchapter1section3.proposition_1_c.{u, v}
        H D Q K V W Q0 S Q1 P t s hch.1 hind hPne hPV h2rank
    rcases hlocal.2.2 with
      ⟨ell, hellPower, hellGt, hellCard, hlocalCases⟩
    have hCX_not_elementary : ¬ IsElementaryAbelian 2 CX := by
      intro hCXElementary
      rcases htypeAFixedSquareRoot P p hPV hp hPcard with
        ⟨r, hrFixed, hrSquare⟩
      have hrCX : r ∈ CX := by
        exact ⟨hrFixed.1, by rw [← hSQ]; exact hrFixed.2⟩
      letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      letI : IsElementaryAbelian 2 CX := hCXElementary
      have hrSqSub : (⟨r, hrCX⟩ : CX) ^ 2 = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 CX) ⟨r, hrCX⟩
      have hrSq : r ^ 2 = 1 := congrArg (fun z : CX => (z : G)) hrSqSub
      apply hch.1.2.2.1.ne_one
      calc
        s = r ^ 2 := hrSquare.symm
        _ = 1 := hrSq
    have hCX_not_unitary_case (hCXCube : Nat.card CX = ell ^ 3) : False := by
      have hQ0leS : Q0 ≤ S := by
        rw [hSQ]
        exact hch.1.1.Q0_le_Q
      let Q0S : Subgroup S := Q0.subgroupOf S
      have hQ0SCenter : Q0S = Subgroup.center S := by
        ext x
        change (x : G) ∈ Q0 ↔ x ∈ Subgroup.center S
        constructor
        · intro hxQ0
          rcases (hch.1.1.Q0_def (x : G)).mp hxQ0 with hxOne | hxInv
          · have hxOneS : x = 1 := Subtype.ext hxOne
            rw [hxOneS]
            exact (Subgroup.center S).one_mem
          · have hxInvS : IsInvolution x :=
              ⟨fun hx => hxInv.2.ne_one (congrArg (fun z : S => (z : G)) hx),
                Subtype.ext hxInv.2.sq_eq_one⟩
            have hxMem : x ∈ involutions S := hxInvS
            rw [(higmanTheorem_involutions_center hSuzuki).1] at hxMem
            exact hxMem.1
        · intro hxCenter
          by_cases hxOne : x = 1
          · exact (congrArg (fun z : S => (z : G)) hxOne) ▸ Q0.one_mem
          · have hxMem : x ∈ involutions S := by
              rw [(higmanTheorem_involutions_center hSuzuki).1]
              exact ⟨hxCenter, hxOne⟩
            have hxInvG : IsInvolution (x : G) :=
              ⟨fun hx => hxMem.ne_one (Subtype.ext hx),
                congrArg (fun z : S => (z : G)) hxMem.sq_eq_one⟩
            exact (hch.1.1.Q0_def (x : G)).mpr <| Or.inr
              ⟨hch.1.1.hA.A1.Q_le_H (by rw [← hSQ]; exact x.property), hxInvG⟩
      have hPnormS : P ≤ Subgroup.normalizer (S : Set G) :=
        hPV.trans (hVleD.trans hDnormS)
      letI : Subgroup.Normalizes P S := ⟨hPnormS⟩
      letI : IsInvariant P S (Subgroup.center S) := center_isInvariant
      letI : MulDistribMulAction P (S ⧸ Subgroup.center S) :=
        quotientMulDistribMulAction (A := P) (G := S)
          (Subgroup.center S) (inferInstance : IsInvariant P S (Subgroup.center S))
      have hSpgroup : IsPGroup 2 S := by
        rcases hSuzuki.1 with ⟨m, hm⟩
        exact IsPGroup.of_card (by simpa using hm)
      letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      letI : Group.IsNilpotent S := hSpgroup.isNilpotent
      have hSsolvable : Group.IsSolvable S := by infer_instance
      have hpDvdD : p ∣ Nat.card D := by
        rw [← hPcard]
        exact Subgroup.card_dvd_of_le (hPV.trans hVleD)
      have hpOdd : Odd p := hch.1.1.hA.A1.D_odd.of_dvd_nat hpDvdD
      have hcoprime : Nat.Coprime (Nat.card P) (Nat.card S) := by
        rcases hSuzuki.1 with ⟨m, hm⟩
        have hmS : Nat.card S = 2 ^ m := by simpa using hm
        rw [hPcard, hmS]
        exact hpOdd.coprime_two_right.pow_right m
      let CSG : Subgroup G := Subgroup.centralizer (P : Set G) ⊓ S
      let CS : Subgroup S := CSG.subgroupOf S
      have hFixSEq : fixedPointSubgroup P S = CS := by
        ext x
        constructor
        · intro hxFix
          change (x : G) ∈ Subgroup.centralizer (P : Set G) ⊓ S
          refine ⟨?_, x.property⟩
          change (x : G) ∈ Subgroup.centralizer (P : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro c hcP
          let cP : P := ⟨c, hcP⟩
          have hfix := hxFix cP
          have hfixG : c * (x : G) * c⁻¹ = (x : G) := by
            simpa [cP,
              Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
                congrArg (fun z : S => (z : G)) hfix
          have hmul := congrArg (fun z : G => z * c) hfixG
          simpa [mul_assoc] using hmul
        · intro hxCS
          change (x : G) ∈ Subgroup.centralizer (P : Set G) ⊓ S at hxCS
          change ∀ c : P, c • x = x
          intro c
          apply Subtype.ext
          simp only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
          have hcComm : Commute (c : G) (x : G) :=
            Subgroup.mem_centralizer_iff.mp hxCS.1 (c : G) c.property
          exact hcComm.mul_inv_cancel
      have hFixSCard : Nat.card (fixedPointSubgroup P S) = Nat.card CX := by
        rw [hFixSEq]
        calc
          Nat.card CS = Nat.card CSG :=
            Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (H := CSG) (K := S)
                (show CSG ≤ S from inf_le_right)).toEquiv
          _ = Nat.card CX := by simp [CSG, CX, hSQ]
      let CQ0 : Subgroup G := Subgroup.centralizer (P : Set G) ⊓ Q0
      have hCQ0leS : CQ0 ≤ S := inf_le_right.trans hQ0leS
      let CQ0S : Subgroup S := CQ0.subgroupOf S
      have hCenterFixEq :
          Subgroup.center S ⊓ fixedPointSubgroup P S = CQ0S := by
        rw [← hQ0SCenter, hFixSEq]
        ext x
        simp only [Subgroup.mem_inf]
        change ((x : G) ∈ Q0 ∧
            (x : G) ∈ Subgroup.centralizer (P : Set G) ∧ (x : G) ∈ S) ↔
          (x : G) ∈ Subgroup.centralizer (P : Set G) ∧ (x : G) ∈ Q0
        constructor
        · exact fun hx => ⟨hx.2.1, hx.1⟩
        · exact fun hx => ⟨hx.2, hx.1, hQ0leS hx.2⟩
      have hFixCenterCard :
          Nat.card (fixedPointSubgroup P (Subgroup.center S)) = ell := by
        have hMapCenter :=
          fixedPointSubgroup_map_subtype_eq_inf
            (A := P) (G := S) (Subgroup.center S)
        calc
          Nat.card (fixedPointSubgroup P (Subgroup.center S)) =
              Nat.card ((fixedPointSubgroup P (Subgroup.center S)).map
                (Subgroup.center S).subtype) :=
            (Subgroup.card_map_of_injective
              (K := fixedPointSubgroup P (Subgroup.center S))
              (f := (Subgroup.center S).subtype)
              (Subgroup.center S).subtype_injective).symm
          _ = Nat.card (show Subgroup S from
              Subgroup.center S ⊓ fixedPointSubgroup P S) := by
            rw [hMapCenter]
          _ = Nat.card CQ0S := by rw [hCenterFixEq]
          _ = Nat.card CQ0 :=
            Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe hCQ0leS).toEquiv
          _ = ell := hellCard.symm
      have hFixedQuotientEq :=
        fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
          (G := S) (A := P) hSsolvable hcoprime (∅ : Set Nat.Primes)
          (Subgroup.center S)
          (inferInstance : IsInvariant P S (Subgroup.center S))
      have hLiftFixed :
          ∀ y : fixedPointSubgroup P (S ⧸ Subgroup.center S),
            ∃ f : fixedPointSubgroup P S,
              QuotientGroup.mk' (Subgroup.center S) (f : S) = (y : S ⧸ Subgroup.center S) := by
        intro y
        have hyMap : (y : S ⧸ Subgroup.center S) ∈
            (fixedPointSubgroup P S).map
              (QuotientGroup.mk' (Subgroup.center S)) := by
          rw [← hFixedQuotientEq]
          exact y.property
        rcases Subgroup.mem_map.mp hyMap with ⟨f, hf, hfy⟩
        exact ⟨⟨f, hf⟩, hfy⟩
      let liftFixed
          (y : fixedPointSubgroup P (S ⧸ Subgroup.center S)) :
          fixedPointSubgroup P S := Classical.choose (hLiftFixed y)
      have hLiftFixedSpec
          (y : fixedPointSubgroup P (S ⧸ Subgroup.center S)) :
          QuotientGroup.mk' (Subgroup.center S) (liftFixed y : S) =
            (y : S ⧸ Subgroup.center S) :=
        Classical.choose_spec (hLiftFixed y)
      have hSquareCenter (f : S) : f ^ 2 ∈ Subgroup.center S := by
        by_cases hfSq : f ^ 2 = 1
        · simp [hfSq]
        · have hfFourth : f ^ 4 = 1 :=
            (higmanTheorem_center_quotient_orders_and_exponent hSuzuki).2.2.2.2 f
          have hfInv : IsInvolution (f ^ 2) := by
            refine ⟨hfSq, ?_⟩
            calc
              (f ^ 2) ^ 2 = f ^ 4 := by group
              _ = 1 := hfFourth
          have hmem : f ^ 2 ∈ involutions S := hfInv
          rw [(higmanTheorem_involutions_center hSuzuki).1] at hmem
          exact hmem.1
      let squareFixed
          (y : fixedPointSubgroup P (S ⧸ Subgroup.center S)) :
          fixedPointSubgroup P (Subgroup.center S) :=
        ⟨⟨(liftFixed y : S) ^ 2, hSquareCenter (liftFixed y : S)⟩, by
          change ∀ c : P, c •
              (⟨(liftFixed y : S) ^ 2,
                hSquareCenter (liftFixed y : S)⟩ : Subgroup.center S) =
              ⟨(liftFixed y : S) ^ 2, hSquareCenter (liftFixed y : S)⟩
          intro c
          apply Subtype.ext
          change c • (liftFixed y : S) ^ 2 = (liftFixed y : S) ^ 2
          rw [smul_pow', (liftFixed y).property c]⟩
      have hSquareFixedInjective : Function.Injective squareFixed := by
        intro a b hab
        have hsq : (liftFixed a : S) ^ 2 = (liftFixed b : S) ^ 2 := by
          exact congrArg
            (fun z : fixedPointSubgroup P (Subgroup.center S) => ((z : Subgroup.center S) : S))
            hab
        have hquot := htypeASquareCosetInjective
          (liftFixed a : S) (liftFixed b : S) hsq
        apply Subtype.ext
        calc
          (a : S ⧸ Subgroup.center S) =
              QuotientGroup.mk' (Subgroup.center S) (liftFixed a : S) :=
            (hLiftFixedSpec a).symm
          _ = QuotientGroup.mk' (Subgroup.center S) (liftFixed b : S) := hquot
          _ = (b : S ⧸ Subgroup.center S) := hLiftFixedSpec b
      have hFixQuotientLe :
          Nat.card (fixedPointSubgroup P (S ⧸ Subgroup.center S)) ≤ ell := by
        calc
          Nat.card (fixedPointSubgroup P (S ⧸ Subgroup.center S)) ≤
              Nat.card (fixedPointSubgroup P (Subgroup.center S)) :=
            Nat.card_le_card_of_injective squareFixed hSquareFixedInjective
          _ = ell := hFixCenterCard
      have hFactor := Wielandt.fixedPointSubgroup_card_eq_mul_quotient_action
        (A := P) (M := S) (N := Subgroup.center S)
        (inferInstance : IsInvariant P S (Subgroup.center S))
        hSsolvable hcoprime
      have hCXLe : Nat.card CX ≤ ell ^ 2 := by
        rw [← hFixSCard, hFactor, hFixCenterCard]
        calc
          ell * Nat.card (fixedPointSubgroup P (S ⧸ Subgroup.center S)) ≤
              ell * ell := Nat.mul_le_mul_left ell hFixQuotientLe
          _ = ell ^ 2 := by ring
      rw [hCXCube] at hCXLe
      nlinarith
    have horder : orderOf (s * t) = 5 := by
      rcases hlocalCases with hlinear | hSuzuki | hunitary
      · rcases hlinear with
          ⟨_k, _hk, _hell, _hmodel, _horder, hCXElementary, _hcard⟩
        exact False.elim (hCX_not_elementary (by simpa [CX] using hCXElementary))
      · rcases hSuzuki with
          ⟨_k, _hk, _hell, _hmodel, horder, _hCX, _hcard⟩
        exact horder
      · rcases hunitary with
          ⟨_E, _hEfield, _hEfinite, _J, _hform, _hEcard,
            _hfixedCard, _hmodel, _horder, _hCX, hCXCard⟩
        exact False.elim
          (hCX_not_unitary_case (by simpa [CX] using hCXCard.1))
    exact ⟨horder, hWbot⟩
  have htypeBNotCommutative :
      IsSuzukiTwoTypeB S → ¬ IsMulCommutative S := by
    rintro ⟨n, hn, theta, epsilon, tripleLift, cocycle, hepsilon,
      _hperiod, _hnonzero, haddLeft, haddRight, hdiag, hmem, _hone,
      _hsurj, hinj, hmul⟩ hcomm
    let x : S := ⟨tripleLift 0 1 0, hmem 0 1 0⟩
    let y : S := ⟨tripleLift 0 0 1, hmem 0 0 1⟩
    have hcommEq : tripleLift 0 1 0 * tripleLift 0 0 1 =
        tripleLift 0 0 1 * tripleLift 0 1 0 := by
      exact congrArg (fun z : S => (z : G))
        ((@IsMulCommutative.is_comm S _ hcomm).comm x y)
    rw [hmul, hmul] at hcommEq
    have hcross : cocycle 1 0 0 1 = cocycle 0 1 1 0 := by
      simpa only [zero_add, add_zero] using
        (hinj _ _ _ _ _ _ hcommEq).1
    have hsplitLeft :
        cocycle 1 1 1 1 =
          cocycle 1 0 1 1 + cocycle 0 1 1 1 := by
      simpa using haddLeft 1 0 0 1 1 1
    have hsplitFirst :
        cocycle 1 0 1 1 =
          cocycle 1 0 1 0 + cocycle 1 0 0 1 := by
      simpa using haddRight 1 0 1 0 0 1
    have hsplitSecond :
        cocycle 0 1 1 1 =
          cocycle 0 1 1 0 + cocycle 0 1 0 1 := by
      simpa using haddRight 0 1 1 0 0 1
    have hepsilonZero : epsilon = 0 := by
      calc
        epsilon = 1 * theta 1 + epsilon * 1 * theta 1 + 1 * theta 1 := by
          simp only [map_one, mul_one]
          rw [show (1 : BinaryGaloisField n) + epsilon + 1 =
              epsilon + (1 + 1) by ring,
            CharTwo.add_self_eq_zero, add_zero]
        _ = cocycle 1 1 1 1 := (hdiag 1 1).symm
        _ = cocycle 1 0 1 1 + cocycle 0 1 1 1 := hsplitLeft
        _ = (cocycle 1 0 1 0 + cocycle 1 0 0 1) +
              (cocycle 0 1 1 0 + cocycle 0 1 0 1) := by
          rw [hsplitFirst, hsplitSecond]
        _ = (1 + cocycle 1 0 0 1) +
              (cocycle 0 1 1 0 + 1) := by
          rw [hdiag, hdiag]
          simp only [map_one, map_zero, mul_one, mul_zero, add_zero, zero_add]
        _ = cocycle 1 0 0 1 + cocycle 0 1 1 0 := by
          rw [show (1 + cocycle 1 0 0 1) +
              (cocycle 0 1 1 0 + 1) =
                (1 + 1) +
                  (cocycle 1 0 0 1 + cocycle 0 1 1 0) by abel,
            CharTwo.add_self_eq_zero, zero_add]
        _ = 0 := by rw [hcross, CharTwo.add_self_eq_zero]
    exact hepsilon hepsilonZero
  have htypeBCardCenterCube :
      IsSuzukiTwoGroup S → IsSuzukiTwoTypeB S →
        Nat.card S = Nat.card (Subgroup.center S) ^ 3 := by
    intro hSuzuki htypeB
    rcases htypeB with
      ⟨n, hn, theta, epsilon, tripleLift, cocycle, _hepsilon,
        hperiod, hnonzero, haddLeft, haddRight, hdiag, hmem, hone,
        hsurj, hinj, hmul⟩
    let F := BinaryGaloisField n
    let tripleFun : F × F × F → S := fun cab =>
      ⟨tripleLift cab.1 cab.2.1 cab.2.2,
        hmem cab.1 cab.2.1 cab.2.2⟩
    have htripleBijective : Function.Bijective tripleFun := by
      constructor
      · intro cab dbf hEq
        have hval := congrArg (fun z : S => (z : G)) hEq
        rcases hinj cab.1 cab.2.1 cab.2.2
            dbf.1 dbf.2.1 dbf.2.2 hval with ⟨h1, h2, h3⟩
        exact Prod.ext h1 (Prod.ext h2 h3)
      · intro x
        rcases hsurj x x.property with ⟨c, a, b, hx⟩
        exact ⟨(c, a, b), Subtype.ext hx.symm⟩
    let tripleEquiv : F × F × F ≃ S :=
      Equiv.ofBijective tripleFun htripleBijective
    have hzeroLeft : ∀ a b : F, cocycle 0 0 a b = 0 := by
      intro a b
      have h := haddLeft 0 0 0 0 a b
      simpa only [zero_add, CharTwo.add_self_eq_zero] using h
    have hzeroRight : ∀ a b : F, cocycle a b 0 0 = 0 := by
      intro a b
      have h := haddRight a b 0 0 0 0
      simpa only [zero_add, CharTwo.add_self_eq_zero] using h
    let centerMap : F → Subgroup.center S := fun c =>
      ⟨⟨tripleLift c 0 0, hmem c 0 0⟩, by
        rw [Subgroup.mem_center_iff]
        intro x
        rcases hsurj x x.property with ⟨d, a, b, hx⟩
        apply Subtype.ext
        change (x : G) * tripleLift c 0 0 =
          tripleLift c 0 0 * (x : G)
        rw [hx, hmul, hmul, hzeroLeft, hzeroRight]
        simp [add_comm]⟩
    have hcenterMapInjective : Function.Injective centerMap := by
      intro c d hEq
      have hval := congrArg
        (fun z : Subgroup.center S => ((z : S) : G)) hEq
      exact (hinj c 0 0 d 0 0 hval).1
    have hquadZeroOnly : ∀ a b : F,
        a * theta a + epsilon * a * theta b + b * theta b = 0 →
          a = 0 ∧ b = 0 := by
      intro a b hquad
      by_contra hab
      have hpair : (a, b) ≠ (0, 0) := by
        simpa [Prod.ext_iff] using hab
      have hquadNe :
          a * theta a + epsilon * a * theta b + b * theta b ≠ 0 := by
        by_cases ha : a = 0
        · subst a
          have hb : b ≠ 0 := by
            intro hb
            exact hpair (Prod.ext rfl hb)
          simpa using mul_ne_zero hb ((map_ne_zero theta).mpr hb)
        · by_cases hb : b = 0
          · subst b
            simpa using mul_ne_zero ha ((map_ne_zero theta).mpr ha)
          · exact hnonzero a b ha hb
      exact hquadNe hquad
    have hcenterMapSurjective : Function.Surjective centerMap := by
      intro z
      rcases hsurj (z : S) (z : S).property with ⟨c, a, b, hz⟩
      have hsqS : (z : S) ^ 2 = 1 :=
        congrArg (fun x : Subgroup.center S => (x : S))
          ((higmanTheorem_involutions_center hSuzuki).2 z)
      have hsqG : ((z : S) : G) ^ 2 = 1 :=
        congrArg (fun x : S => (x : G)) hsqS
      have hcoordEq :
          tripleLift
              (a * theta a + epsilon * a * theta b + b * theta b) 0 0 =
            tripleLift 0 0 0 := by
        calc
          tripleLift
                (a * theta a + epsilon * a * theta b + b * theta b) 0 0 =
              tripleLift c a b ^ 2 := by
                rw [pow_two, hmul, hdiag]
                simp only [CharTwo.add_self_eq_zero, zero_add]
          _ = ((z : S) : G) ^ 2 := by rw [hz]
          _ = 1 := hsqG
          _ = tripleLift 0 0 0 := hone.symm
      have hquad :
          a * theta a + epsilon * a * theta b + b * theta b = 0 :=
        (hinj
          (a * theta a + epsilon * a * theta b + b * theta b) 0 0
          0 0 0 hcoordEq).1
      rcases hquadZeroOnly a b hquad with ⟨rfl, rfl⟩
      refine ⟨c, ?_⟩
      apply Subtype.ext
      exact Subtype.ext hz.symm
    let centerEquiv : F ≃ Subgroup.center S :=
      Equiv.ofBijective centerMap
        ⟨hcenterMapInjective, hcenterMapSurjective⟩
    have hFcard : Nat.card F = 2 ^ n := by
      simpa [F, BinaryGaloisField] using GaloisField.card 2 n hn
    have hSCard : Nat.card S = (2 ^ n) ^ 3 := by
      calc
        Nat.card S = Nat.card (F × F × F) :=
          (Nat.card_congr tripleEquiv).symm
        _ = Nat.card F * (Nat.card F * Nat.card F) := by
          rw [Nat.card_prod, Nat.card_prod]
        _ = (2 ^ n) ^ 3 := by rw [hFcard]; ring
    have hCenterCard : Nat.card (Subgroup.center S) = 2 ^ n := by
      calc
        Nat.card (Subgroup.center S) = Nat.card F :=
          (Nat.card_congr centerEquiv).symm
        _ = 2 ^ n := hFcard
    rw [hSCard, hCenterCard]
  have htypeCCardCenterCube :
      IsSuzukiTwoTypeC S →
        Nat.card S = Nat.card (Subgroup.center S) ^ 3 := by
    rintro ⟨n, hn, theta, epsilon, tripleLift, hepsilon, _hperiod,
      _hthetaSq, _havoid, hmem, hone, hsurj, hinj, hmul⟩
    let F := BinaryGaloisField n
    let tripleFun : F × F × F → S := fun zab =>
      ⟨tripleLift zab.1 zab.2.1 zab.2.2,
        hmem zab.1 zab.2.1 zab.2.2⟩
    have htripleBijective : Function.Bijective tripleFun := by
      constructor
      · intro zab wcd hEq
        have hval := congrArg (fun z : S => (z : G)) hEq
        rcases hinj zab.1 zab.2.1 zab.2.2
            wcd.1 wcd.2.1 wcd.2.2 hval with ⟨h1, h2, h3⟩
        exact Prod.ext h1 (Prod.ext h2 h3)
      · intro x
        rcases hsurj x x.property with ⟨z, a, b, hx⟩
        exact ⟨(z, a, b), Subtype.ext hx.symm⟩
    let tripleEquiv : F × F × F ≃ S :=
      Equiv.ofBijective tripleFun htripleBijective
    let centerMap : F → Subgroup.center S := fun z =>
      ⟨⟨tripleLift z 0 0, hmem z 0 0⟩, by
        rw [Subgroup.mem_center_iff]
        intro x
        rcases hsurj x x.property with ⟨w, c, d, hx⟩
        apply Subtype.ext
        change (x : G) * tripleLift z 0 0 =
          tripleLift z 0 0 * (x : G)
        rw [hx, hmul, hmul]
        simp [add_comm]⟩
    have hcenterMapInjective : Function.Injective centerMap := by
      intro z w hEq
      have hval := congrArg
        (fun x : Subgroup.center S => ((x : S) : G)) hEq
      exact (hinj z 0 0 w 0 0 hval).1
    have hcenterMapSurjective : Function.Surjective centerMap := by
      intro x
      rcases hsurj (x : S) (x : S).property with ⟨z, a, b, hx⟩
      have hcommCoord : ∀ w c d : F,
          z + w + a * theta c +
              epsilon * a ^ (2 ^ (n - 1)) * theta (d ^ 2) + b * d =
            w + z + c * theta a +
              epsilon * c ^ (2 ^ (n - 1)) * theta (b ^ 2) + d * b := by
        intro w c d
        have hcomm :=
          Subgroup.mem_center_iff.mp x.property
            (⟨tripleLift w c d, hmem w c d⟩ : S)
        have hval := congrArg (fun y : S => (y : G)) hcomm
        have hval' :
            tripleLift z a b * tripleLift w c d =
              tripleLift w c d * tripleLift z a b := by
          simpa [hx] using hval.symm
        rw [hmul, hmul] at hval'
        exact (hinj _ _ _ _ _ _ hval').1
      have hpowPos : 0 < 2 ^ (n - 1) := pow_pos (by norm_num) _
      have haTerm : epsilon * a ^ (2 ^ (n - 1)) = 0 := by
        have h := hcommCoord 0 0 1
        simp only [map_zero, map_one, zero_mul, mul_zero, zero_add,
          one_pow, mul_one, add_zero, zero_pow hpowPos.ne'] at h
        have h' :
            z + (epsilon * a ^ (2 ^ (n - 1)) + b) = z + (0 + b) := by
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
      exact Subtype.ext hx.symm
    let centerEquiv : F ≃ Subgroup.center S :=
      Equiv.ofBijective centerMap
        ⟨hcenterMapInjective, hcenterMapSurjective⟩
    have hFcard : Nat.card F = 2 ^ n := by
      simpa [F, BinaryGaloisField] using GaloisField.card 2 n hn
    have hSCard : Nat.card S = (2 ^ n) ^ 3 := by
      calc
        Nat.card S = Nat.card (F × F × F) :=
          (Nat.card_congr tripleEquiv).symm
        _ = Nat.card F * (Nat.card F * Nat.card F) := by
          rw [Nat.card_prod, Nat.card_prod]
        _ = (2 ^ n) ^ 3 := by rw [hFcard]; ring
    have hCenterCard : Nat.card (Subgroup.center S) = 2 ^ n := by
      calc
        Nat.card (Subgroup.center S) = Nat.card F :=
          (Nat.card_congr centerEquiv).symm
        _ = 2 ^ n := hFcard
    rw [hSCard, hCenterCard]
  have htypeDCardCenterCube :
      IsSuzukiTwoTypeD S →
        Nat.card S = Nat.card (Subgroup.center S) ^ 3 := by
    rintro ⟨n, hn, theta, epsilon, tripleLift, hepsilon, hperiod,
      hthetaNontrivial, _havoid, hmem, hone, hsurj, hinj, hmul⟩
    let F := BinaryGaloisField n
    let tripleFun : F × F × F → S := fun zab =>
      ⟨tripleLift zab.1 zab.2.1 zab.2.2,
        hmem zab.1 zab.2.1 zab.2.2⟩
    have htripleBijective : Function.Bijective tripleFun := by
      constructor
      · intro zab wcd hEq
        have hval := congrArg (fun z : S => (z : G)) hEq
        rcases hinj zab.1 zab.2.1 zab.2.2
            wcd.1 wcd.2.1 wcd.2.2 hval with ⟨h1, h2, h3⟩
        exact Prod.ext h1 (Prod.ext h2 h3)
      · intro x
        rcases hsurj x x.property with ⟨z, a, b, hx⟩
        exact ⟨(z, a, b), Subtype.ext hx.symm⟩
    let tripleEquiv : F × F × F ≃ S :=
      Equiv.ofBijective tripleFun htripleBijective
    let centerMap : F → Subgroup.center S := fun z =>
      ⟨⟨tripleLift z 0 0, hmem z 0 0⟩, by
        rw [Subgroup.mem_center_iff]
        intro x
        rcases hsurj x x.property with ⟨w, c, d, hx⟩
        apply Subtype.ext
        change (x : G) * tripleLift z 0 0 =
          tripleLift z 0 0 * (x : G)
        rw [hx, hmul, hmul]
        simp [add_comm]⟩
    have hcenterMapInjective : Function.Injective centerMap := by
      intro z w hEq
      have hval := congrArg
        (fun x : Subgroup.center S => ((x : S) : G)) hEq
      exact (hinj z 0 0 w 0 0 hval).1
    have hthetaPowFive : theta ^ 5 = 1 := by
      apply DFunLike.ext _ _
      intro x
      change theta (theta (theta (theta (theta x)))) = x
      simpa [Function.iterate_succ_apply] using hperiod x
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
    have hthetaNeOne : theta ≠ 1 := by
      simpa using
        (hpowNe (i := 1) (j := 0) (by omega) (by omega) (by omega))
    letI : Fintype F := Fintype.ofFinite F
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    obtain ⟨autBasis, hAutBasis⟩ :=
      lemma2a_fieldAutomorphisms_basis_linearMaps F
    have hcenterMapSurjective : Function.Surjective centerMap := by
      intro x
      rcases hsurj (x : S) (x : S).property with ⟨z, a, b, hx⟩
      have hcommCoord : ∀ w c d : F,
          z + w + a * theta c +
              epsilon * (theta^[3]) a * theta d + b * (theta^[2]) d =
            w + z + c * theta a +
              epsilon * (theta^[3]) c * theta b + d * (theta^[2]) b := by
        intro w c d
        have hcomm :=
          Subgroup.mem_center_iff.mp x.property
            (⟨tripleLift w c d, hmem w c d⟩ : S)
        have hval := congrArg (fun y : S => (y : G)) hcomm
        have hval' :
            tripleLift z a b * tripleLift w c d =
              tripleLift w c d * tripleLift z a b := by
          simpa [hx] using hval.symm
        rw [hmul, hmul] at hval'
        exact (hinj _ _ _ _ _ _ hval').1
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
          hthetaNeTheta3, hthetaNeOne] using haCoord
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
      exact Subtype.ext hx.symm
    let centerEquiv : F ≃ Subgroup.center S :=
      Equiv.ofBijective centerMap
        ⟨hcenterMapInjective, hcenterMapSurjective⟩
    have hFcard : Nat.card F = 2 ^ n := by
      simpa [F, BinaryGaloisField] using GaloisField.card 2 n hn
    have hSCard : Nat.card S = (2 ^ n) ^ 3 := by
      calc
        Nat.card S = Nat.card (F × F × F) :=
          (Nat.card_congr tripleEquiv).symm
        _ = Nat.card F * (Nat.card F * Nat.card F) := by
          rw [Nat.card_prod, Nat.card_prod]
        _ = (2 ^ n) ^ 3 := by rw [hFcard]; ring
    have hCenterCard : Nat.card (Subgroup.center S) = 2 ^ n := by
      calc
        Nat.card (Subgroup.center S) = Nat.card F :=
          (Nat.card_congr centerEquiv).symm
        _ = 2 ^ n := hFcard
    rw [hSCard, hCenterCard]
  have hcubicSuzuki
      (hcardCube : Nat.card S = Nat.card (Subgroup.center S) ^ 3) :
      IsSuzukiTwoGroup S := by
    rcases PFchapter1section2.corollary
        H D Q K V W Q0 S Q1 t hch.1.1 with hcomm | hSuzuki
    · exfalso
      have hcenterTop : Subgroup.center S = ⊤ := by
        apply top_unique
        intro x _hx
        rw [Subgroup.mem_center_iff]
        intro y
        exact (@IsMulCommutative.is_comm S _ hcomm).comm y x
      have hsQ0 : s ∈ Q0 :=
        (hch.1.1.Q0_def s).mpr
          (Or.inr ⟨hch.1.2.1, hch.1.2.2.1⟩)
      have hsS : s ∈ S := by
        rw [hSQ]
        exact hch.1.1.Q0_le_Q hsQ0
      have hSne : S ≠ ⊥ := by
        intro hSbot
        have hsOne : s = 1 := by
          have : s ∈ (⊥ : Subgroup G) := by simpa [hSbot] using hsS
          simpa using this
        exact hch.1.2.2.1.ne_one hsOne
      have hcardGt : 1 < Nat.card S := S.one_lt_card_iff_ne_bot.mpr hSne
      rw [hcenterTop] at hcardCube
      have hcardEq : Nat.card S = Nat.card S ^ 3 := by
        simpa using hcardCube
      have hcardLt : Nat.card S < Nat.card S ^ 3 := by
        simpa using Nat.pow_lt_pow_right hcardGt (by omega : 1 < 3)
      exact (ne_of_lt hcardLt) hcardEq
    · exact hSuzuki
  have hQ0Center (hSuzuki : IsSuzukiTwoGroup S) :
      Nat.card Q0 = Nat.card (Subgroup.center S) := by
    have hQ0leS : Q0 ≤ S := by
      rw [hSQ]
      exact hch.1.1.Q0_le_Q
    let Q0S : Subgroup S := Q0.subgroupOf S
    have hQ0SCenter : Q0S = Subgroup.center S := by
      ext x
      change (x : G) ∈ Q0 ↔ x ∈ Subgroup.center S
      constructor
      · intro hxQ0
        rcases (hch.1.1.Q0_def (x : G)).mp hxQ0 with hxOne | hxInv
        · have hxOneS : x = 1 := Subtype.ext hxOne
          rw [hxOneS]
          exact (Subgroup.center S).one_mem
        · have hxInvS : IsInvolution x :=
            ⟨fun hx => hxInv.2.ne_one
                (congrArg (fun z : S => (z : G)) hx),
              Subtype.ext hxInv.2.sq_eq_one⟩
          have hxMem : x ∈ involutions S := hxInvS
          rw [(higmanTheorem_involutions_center hSuzuki).1] at hxMem
          exact hxMem.1
      · intro hxCenter
        by_cases hxOne : x = 1
        · exact (congrArg (fun z : S => (z : G)) hxOne) ▸ Q0.one_mem
        · have hxMem : x ∈ involutions S := by
            rw [(higmanTheorem_involutions_center hSuzuki).1]
            exact ⟨hxCenter, hxOne⟩
          have hxInvG : IsInvolution (x : G) :=
            ⟨fun hx => hxMem.ne_one (Subtype.ext hx),
              congrArg (fun z : S => (z : G)) hxMem.sq_eq_one⟩
          exact (hch.1.1.Q0_def (x : G)).mpr <| Or.inr
            ⟨hch.1.1.hA.A1.Q_le_H
              (by rw [← hSQ]; exact x.property), hxInvG⟩
    calc
      Nat.card Q0 = Nat.card Q0S :=
        (Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hQ0leS).toEquiv).symm
      _ = Nat.card (Subgroup.center S) := by rw [hQ0SCenter]
  have hfixedFieldCentralizer
      (P : Subgroup G) (hPV : P ≤ V) (hWbot : W = ⊥) :
      V ⊓ Subgroup.centralizer
          ((Q0 ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) = P := by
    apply le_antisymm
    · intro v hv
      rcases PFchapter1section2.proposition_3_field_model_with_q0_card
          H D Q K V W Q0 S Q1 t hch.1.1 with
        ⟨fieldN, _hfieldN, _hQ0pow, A, hWnormalV, _hWnormalD,
          _rhoD, _rhoMul, _rhoAut, q0Add, _kUnits, vmodWAut, _modelIso,
          _hQ0card, _hrhoMul, _hrhoAutInl, _hrhoAutInr, _hrhoD,
          _hmodelQ, _hmodelK, _hmodelV, _hkAction, hvAction⟩
      let F : Type := GaloisField 2 fieldN
      letI : Field F := inferInstance
      letI : Finite F := inferInstance
      letI : (W.subgroupOf V).Normal := hWnormalV
      let pToV : P →* V := Subgroup.inclusion hPV
      let rhoP : P →* (F ≃+* F) :=
        A.subtype.comp
          (vmodWAut.toMonoidHom.comp
            ((QuotientGroup.mk' (W.subgroupOf V)).comp pToV))
      letI : MulSemiringAction P F := MulSemiringAction.compHom F rhoP
      let vV : V := ⟨v, hv.1⟩
      have hvFixes :
          ∀ x : FixedPoints.subfield P F,
            (vmodWAut (QuotientGroup.mk vV) : F ≃+* F) (x : F) = x := by
        intro x
        let q : Q0 := q0Add.symm (Multiplicative.ofAdd (x : F))
        have hqCentralizerP : (q : G) ∈ Subgroup.centralizer (P : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro p hpP
          let pP : P := ⟨p, hpP⟩
          let pV : V := pToV pP
          rcases hvAction pV q with ⟨hqConj, hqImage⟩
          have hxFixed : rhoP pP (x : F) = x := x.property pP
          have hrhoP : rhoP pP =
              (vmodWAut (QuotientGroup.mk pV) : F ≃+* F) := by
            rfl
          have hforward :
              (vmodWAut (QuotientGroup.mk pV) : F ≃+* F) (x : F) = x := by
            rw [← hrhoP]
            exact hxFixed
          have hbackward :
              (vmodWAut (QuotientGroup.mk pV) : F ≃+* F).symm (x : F) = x := by
            apply (vmodWAut (QuotientGroup.mk pV) : F ≃+* F).injective
            simpa using hforward.symm
          have hqImage' :
              q0Add ⟨rightConjugateElem (q : G) p, hqConj⟩ = q0Add q := by
            simpa [q, hbackward, pV, pToV, pP] using hqImage
          have hright : rightConjugateElem (q : G) p = (q : G) :=
            congrArg Subtype.val (q0Add.injective hqImage')
          calc
            p * (q : G) = p * rightConjugateElem (q : G) p := by rw [hright]
            _ = (q : G) * p := by simp [rightConjugateElem, mul_assoc]
        have hqInf :
            (q : G) ∈ Q0 ⊓ Subgroup.centralizer (P : Set G) :=
          ⟨q.property, hqCentralizerP⟩
        have hvComm : v * (q : G) = (q : G) * v :=
          (Subgroup.mem_centralizer_iff.mp hv.2 (q : G) hqInf).symm
        rcases hvAction vV q with ⟨hqConj, hqImage⟩
        have hright : rightConjugateElem (q : G) v = (q : G) := by
          calc
            rightConjugateElem (q : G) v = v⁻¹ * ((q : G) * v) := by
              simp [rightConjugateElem, mul_assoc]
            _ = v⁻¹ * (v * (q : G)) := by rw [hvComm]
            _ = (q : G) := by simp
        have hbackward :
            (vmodWAut (QuotientGroup.mk vV) : F ≃+* F).symm (x : F) = x := by
          apply Multiplicative.ofAdd.injective
          calc
            Multiplicative.ofAdd
                ((vmodWAut (QuotientGroup.mk vV) : F ≃+* F).symm (x : F)) =
                q0Add ⟨rightConjugateElem (q : G) v, hqConj⟩ := by
              simpa [q] using hqImage.symm
            _ = q0Add q := by simp [hright]
            _ = Multiplicative.ofAdd (x : F) := by
              change q0Add (q0Add.symm (Multiplicative.ofAdd (x : F))) =
                Multiplicative.ofAdd (x : F)
              exact q0Add.apply_symm_apply _
        apply (vmodWAut (QuotientGroup.mk vV) : F ≃+* F).symm.injective
        simpa using hbackward.symm
      let sigma : F ≃ₐ[FixedPoints.subfield P F] F :=
        AlgEquiv.ofRingEquiv
          (f := (vmodWAut (QuotientGroup.mk vV) : F ≃+* F))
          (by
            intro r
            have htemp : algebraMap (FixedPoints.subfield P F) F r = (r : F) := rfl
            simpa [htemp] using hvFixes r)
      obtain ⟨p, hpSigma⟩ :=
        FixedPoints.toAlgAut_surjective P F sigma
      have hAutEq :
          (vmodWAut (QuotientGroup.mk vV) : F ≃+* F) =
            rhoP p := by
        have htemp : (sigma : F ≃+* F) =
            (vmodWAut (QuotientGroup.mk vV) : F ≃+* F) := by
          dsimp [sigma]
          rfl
        have htemp' : (sigma : F ≃+* F) = (rhoP p : F ≃+* F) := by
          calc
            (sigma : F ≃+* F) =
                ((MulSemiringAction.toAlgAut (↥P)
                  (↥(FixedPoints.subfield (↥P) F)) F) p : F ≃+* F) := by
              simpa using congrArg
                (fun e : F ≃ₐ[FixedPoints.subfield P F] F => (e : F ≃+* F))
                hpSigma.symm
            _ = (rhoP p : F ≃+* F) := by
              ext x
              calc
                ((MulSemiringAction.toAlgAut (↥P)
                    (↥(FixedPoints.subfield (↥P) F)) F) p : F → F) x =
                    p • x := rfl
                _ = rhoP p x := rfl
        calc
          (vmodWAut (QuotientGroup.mk vV) : F ≃+* F) =
              (sigma : F ≃+* F) := htemp.symm
          _ = (rhoP p : F ≃+* F) := htemp'
      have hQuotientEq :
          QuotientGroup.mk' (W.subgroupOf V) vV =
            QuotientGroup.mk' (W.subgroupOf V) (pToV p) := by
        apply vmodWAut.injective
        apply Subtype.ext
        exact hAutEq
      have hdivW : vV / pToV p ∈ W.subgroupOf V :=
        (QuotientGroup.eq_iff_div_mem (N := W.subgroupOf V)).mp hQuotientEq
      have hdivOne : vV / pToV p = 1 := by
        have : vV / pToV p ∈ (⊥ : Subgroup V) := by simpa [hWbot] using hdivW
        simpa using this
      have hvEq : vV = pToV p := div_eq_one.mp hdivOne
      have hvG : v = (p : G) := by
        simpa [vV, pToV] using congrArg (fun z : V => (z : G)) hvEq
      simp [hvG]
    · intro p hpP
      refine ⟨hPV hpP, ?_⟩
      change ∀ q : G,
        q ∈ (Q0 ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) →
          q * p = p * q
      intro q hq
      exact (Subgroup.mem_centralizer_iff.mp hq.2 p hpP).symm
  have hcubicEndpoint :
      IsSuzukiTwoGroup S →
        Nat.card S = Nat.card (Subgroup.center S) ^ 3 →
          orderOf (s * t) = 3 ∧ W ≠ ⊥ := by
    intro hSuzuki hcardCube
    have hcubicOrderFiveContradiction :
        ∀ (P : Subgroup G) (p : ℕ),
          P ≤ V → Nat.Prime p → Nat.card P = p →
            IsSuzukiTwoTypeA (Subgroup.centralizer (P : Set G) ⊓ Q) → False := by
      exact cubic_order_five_contradiction H D Q K V Q0 S t s
        hch.1.1.hA.A1 hch.1.1.K_le_D hch.1.1.V_eq
        hch.1.1.Q0_le_Q hch.1.1.Q0_def hch.1.2.1
        hch.1.2.2.1 hch.1.2.2.2 hSQ hVleD hDnormS
        ((PFchapter1section2.proposition_2
          H D Q K V W Q0 S Q1 t hch.1.1).2)
        hKcyclic hKfaithful hKregular hSuzuki hcardCube
    have horderThree : orderOf (s * t) = 3 := by
      rcases hprimeSubgroup V hch.2.V_ne_bot with
        ⟨P, p, hPV, hp, hPcard⟩
      have hPne : P ≠ ⊥ := by
        intro hPbot
        apply hp.ne_one
        calc
          p = Nat.card P := hPcard.symm
          _ = 1 := by rw [hPbot]; simp
      have hPprime : ∃ q : ℕ, Nat.Prime q ∧ Nat.card P = q :=
        ⟨p, hp, hPcard⟩
      have h2rank :
          TwoRankAtLeastTwo (Subgroup.centralizer (P : Set G)) :=
        hch.2.centralizers_two_rank P hPV hPprime
      have hlocal :=
        PFchapter1section3.proposition_1_c.{u, v}
          H D Q K V W Q0 S Q1 P t s hch.1 hind hPne hPV h2rank
      rcases hlocal.2.2 with
        ⟨_ell, _hellPower, _hellGt, _hellCard, hlocalCases⟩
      rcases hlocalCases with hlinear | hSuzukiLocal | hunitary
      · rcases hlinear with
          ⟨_k, _hk, _hell, _hmodel, horder, _hCX, _hcard⟩
        exact horder
      · rcases hSuzukiLocal with
          ⟨_k, _hk, _hell, _hmodel, _horder, hCXtypeA, _hcard⟩
        exact False.elim
          (hcubicOrderFiveContradiction P p hPV hp hPcard hCXtypeA)
      · rcases hunitary with
          ⟨_E, _hEfield, _hEfinite, _J, _hform, _hEcard,
            _hfixedCard, _hmodel, horder, _hCX, _hcard⟩
        exact horder
    have hWne : W ≠ ⊥ := by
      intro hWbot
      rcases hprimeSubgroup V hch.2.V_ne_bot with
        ⟨P, p, hPV, hp, hPcard⟩
      have hPne : P ≠ ⊥ := by
        intro hPbot
        apply hp.ne_one
        calc
          p = Nat.card P := hPcard.symm
          _ = 1 := by rw [hPbot]; simp
      have hPprime : ∃ r : ℕ, Nat.Prime r ∧ Nat.card P = r :=
        ⟨p, hp, hPcard⟩
      have h2rank : TwoRankAtLeastTwo (Subgroup.centralizer (P : Set G)) :=
        hch.2.centralizers_two_rank P hPV hPprime
      let L : Subgroup G := Subgroup.centralizer (P : Set G)
      let ΩP : Type v := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω P}
      letI : MulAction L ΩP := fixedPointCentralizerAction G Ω P
      let HP : Subgroup L := H.comap L.subtype
      let DP : Subgroup L := D.comap L.subtype
      let QP : Subgroup L := Q.comap L.subtype
      let tP : L :=
        ⟨t, t_mem_centralizer_of_le_peterfalviV D V P t hPV hch.1.1.V_eq⟩
      let N : Subgroup L := pointStabilizerCore L ΩP
      let F : Subgroup G := (twoPrimeResidual L).map L.subtype
      let NL : Subgroup G := N.map L.subtype
      let CX : Subgroup G := L ⊓ Q
      have hlocal := PFchapter1section3.proposition_1_c.{u, v}
        H D Q K V W Q0 S Q1 P t s hch.1 hind hPne hPV h2rank
      have hlocalA := PFchapter1section3.proposition_1_a
        H D Q K V W Q0 S Q1 P t s hch.1 hPne hPV
      have hA1P : HypothesisA1 L ΩP HP DP QP tP := hlocalA.1
      have hcoreMem : ∀ n : L,
          n ∈ N ↔ ((n : G) ∈ (L ⊓ D) ⊓
            Subgroup.centralizer ((L ⊓ Q : Subgroup G) : Set G)) := by
        simpa [N, L, ΩP] using hlocalA.2.1
      have hNLleLV :
          ((L ⊓ D) ⊓ Subgroup.centralizer
            ((L ⊓ Q : Subgroup G) : Set G)) ≤ L ⊓ V := hlocalA.2.2
      have hNLF : NL ⊓ F = (Subgroup.center F).map F.subtype := by
        simpa [L, ΩP, N, F, NL] using hlocal.2.1
      rcases hlocal.2.2 with
        ⟨ell, hellPower, hellGt, hellCard, hlocalCases⟩
      have hlinearCX : IsElementaryAbelian 2 CX := by
        rcases hlocalCases with hlinear | hSuzukiLocal | hunitary
        · rcases hlinear with
            ⟨_k, _hk, _hell, _hmodel, _horder, hCXElementary, _hcard⟩
          simpa [CX] using hCXElementary
        · exact False.elim (by
            rcases hSuzukiLocal with
              ⟨_k, _hk, _hell, _hmodel, hfive, _hCX, _hcard⟩
            omega)
        · rcases hunitary with
            ⟨E, hEfield, hEfinite, J, hJstandard, hEcard,
              hfixedCard, hFmodel, _horder, hCXsuzuki, hCXcard⟩
          letI : Field E := hEfield
          letI : Finite E := hEfinite
          rcases hFmodel with ⟨eF⟩
          have hCXp : IsPGroup 2 CX :=
            External.Higman.isPGroup_of_isSuzukiTwoGroup
              (by simpa [CX] using hCXsuzuki)
          have hQPmapCX : QP.map L.subtype = CX := by
            ext x
            constructor
            · rintro ⟨y, hy, rfl⟩
              exact ⟨y.property, hy⟩
            · intro hx
              exact ⟨(⟨x, hx.1⟩ : L), hx.2, rfl⟩
          let eQPCX : QP ≃* CX :=
            (Subgroup.equivMapOfInjective QP L.subtype
              L.subtype_injective).trans (MulEquiv.subgroupCongr hQPmapCX)
          have hQPp : IsPGroup 2 QP := hCXp.of_equiv eQPCX.symm
          have hQPsylow : ∃ PL : Sylow 2 L, QP = (PL : Subgroup L) := by
            rcases PFchapter1section1.proposition_1_c HP DP QP tP hA1P with
              ⟨PL, hPLle⟩
            exact ⟨PL, PL.is_maximal' hQPp hPLle⟩
          have hQPleResidual : QP ≤ twoPrimeResidual L := by
            rcases hQPsylow with ⟨PL, hQPeq⟩
            rw [hQPeq, twoPrimeResidual]
            exact le_iSup (fun T : Sylow 2 L => (T : Subgroup L)) PL
          have hCXleF : CX ≤ F := by
            rw [← hQPmapCX]
            exact Subgroup.map_mono hQPleResidual
          have hNLodd : Odd (Nat.card NL) := by
            have hNLleD : NL ≤ D := by
              rintro x ⟨n, hn, rfl⟩
              have hnLocal := (hcoreMem n).1 hn
              exact hVleD (hNLleLV hnLocal).2
            exact hch.1.1.hA.A1.D_odd.of_dvd_nat
              (Subgroup.card_dvd_of_le hNLleD)
          let ZFG : Subgroup G := (Subgroup.center F).map F.subtype
          have hZFGleNL : ZFG ≤ NL := by
            change (Subgroup.center F).map F.subtype ≤ NL
            rw [← hNLF]
            exact inf_le_left
          have hZFGodd : Odd (Nat.card ZFG) :=
            hNLodd.of_dvd_nat (Subgroup.card_dvd_of_le hZFGleNL)
          have hCXZinf : CX ⊓ ZFG = ⊥ := by
            let I : Subgroup G := CX ⊓ ZFG
            change I = ⊥
            have hIp : IsPGroup 2 I := hCXp.to_le (by
              intro x hx
              exact hx.1)
            have hIodd : Odd (Nat.card I) :=
              hZFGodd.of_dvd_nat (Subgroup.card_dvd_of_le (by
                intro x hx
                exact hx.2))
            rcases IsPGroup.iff_card.mp hIp with ⟨m, hm⟩
            cases m with
            | zero =>
                exact I.eq_bot_of_card_eq (by simpa using hm)
            | succ m =>
                exfalso
                apply hIodd.not_two_dvd_nat
                rw [hm]
                exact dvd_pow_self 2 (Nat.succ_ne_zero m)
          let qF : F →* F ⧸ Subgroup.center F :=
            QuotientGroup.mk' (Subgroup.center F)
          let CFX : Subgroup F := CX.subgroupOf F
          have hqInjective : Function.Injective (qF.subgroupMap CFX) := by
            intro x y hxy
            have hxyQ : qF (x : F) = qF (y : F) := congrArg Subtype.val hxy
            have hdivZ : (x : F) / (y : F) ∈ Subgroup.center F :=
              (QuotientGroup.eq_iff_div_mem (N := Subgroup.center F)).mp hxyQ
            have hdivCX : ((x : F) : G) / ((y : F) : G) ∈ CX :=
              CX.div_mem x.property y.property
            have hdivZG : ((x : F) : G) / ((y : F) : G) ∈ ZFG :=
              ⟨(x : F) / (y : F), hdivZ, rfl⟩
            have hbot : ((x : F) : G) / ((y : F) : G) ∈ (⊥ : Subgroup G) := by
              rw [← hCXZinf]
              exact ⟨hdivCX, hdivZG⟩
            apply Subtype.ext
            apply Subtype.ext
            exact div_eq_one.mp (by simpa using hbot)
          let P0 : Subgroup (F ⧸ Subgroup.center F) := CFX.map qF
          let eCXCFX : CX ≃* CFX :=
            (Subgroup.subgroupOfEquivOfLe hCXleF).symm
          let eCFXP0 : CFX ≃* P0 :=
            MulEquiv.ofBijective (qF.subgroupMap CFX)
              ⟨hqInjective, MonoidHom.subgroupMap_surjective qF CFX⟩
          let eCXP0 : CX ≃* P0 := eCXCFX.trans eCFXP0
          let Pmodel : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
            P0.map eF.toMonoidHom
          let eP0Model : P0 ≃* Pmodel :=
            Subgroup.equivMapOfInjective P0 eF.toMonoidHom eF.injective
          let eCXModel : CX ≃* Pmodel := eCXP0.trans eP0Model
          have hPmodelP : IsPGroup 2 Pmodel := hCXp.of_equiv eCXModel
          have hPmodelCard : Nat.card Pmodel = ell ^ 3 := by
            calc
              Nat.card Pmodel = Nat.card CX := Nat.card_congr eCXModel.symm
              _ = ell ^ 3 := by simpa [CX] using hCXcard.1
          rcases psu_sylow_normalizer_center_witness J ell hellPower hellGt
              hEcard hfixedCard hJstandard Pmodel hPmodelP hPmodelCard with
            ⟨gM, hgMnot, hgMnorm, hgMcenter⟩
          exfalso
          let gQ : F ⧸ Subgroup.center F := eF.symm gM
          have hgQnot : gQ ∉ P0 := by
            intro hgQ
            apply hgMnot
            change gM ∈ P0.map eF.toMonoidHom
            rw [Subgroup.mem_map_equiv]
            simpa [gQ] using hgQ
          have hgQnorm : gQ ∈ Subgroup.normalizer P0 := by
            have hgMmap :
                gM ∈ (Subgroup.normalizer P0).map eF.toMonoidHom := by
              rw [Subgroup.map_equiv_normalizer_eq]
              simpa [Pmodel] using hgMnorm
            simpa [gQ] using (Subgroup.mem_map_equiv.mp hgMmap)
          have hgQcomm : ∀ z : CFX, z ∈ Subgroup.center CFX →
              Commute gQ (qF (z : F)) := by
            intro z hz
            let z0 : P0 := eCFXP0 z
            have hz0 : z0 ∈ Subgroup.center P0 := by
              exact (Subgroup.centerCongr eCFXP0 ⟨z, hz⟩).property
            let zM : Pmodel := eP0Model z0
            have hzM : zM ∈ Subgroup.center Pmodel := by
              exact (Subgroup.centerCongr eP0Model ⟨z0, hz0⟩).property
            have hcommM := (hgMcenter zM hzM).eq
            apply eF.injective
            rw [map_mul, map_mul]
            have hgEq : eF gQ = gM := eF.apply_symm_apply gM
            rw [hgEq]
            have hzEq : eF (qF (z : F)) = (zM : ProjectiveSpecialUnitaryMatrixGroup J) := by
              rfl
            rw [hzEq]
            exact hcommM
          have hZFGcard :
              Nat.card ZFG = Nat.card (Subgroup.center F) := by
            simpa [ZFG] using
              (Subgroup.card_map_of_injective
                (K := Subgroup.center F) (f := F.subtype)
                F.subtype_injective)
          have hZFodd : Odd (Nat.card (Subgroup.center F)) := by
            rw [← hZFGcard]
            exact hZFGodd
          letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          letI : Fact (IsPGroup 2 (↥CFX)) :=
            ⟨hCXp.of_equiv eCXCFX⟩
          have hnormEq :
              Subgroup.normalizer P0 =
                (Subgroup.normalizer CFX).map qF := by
            simpa [P0, qF] using
              (normalizer_map_quotient_eq_map_normalizer
                (G := F) (p := 2) (T := CFX)
                (M := Subgroup.center F) inferInstance
                hZFodd.coprime_two_left)
          have hgQmap : gQ ∈ (Subgroup.normalizer CFX).map qF := by
            rw [← hnormEq]
            exact hgQnorm
          rcases Subgroup.mem_map.mp hgQmap with ⟨gF, hgFnorm, hgFmap⟩
          have hgFCenter : ∀ z : CFX, z ∈ Subgroup.center CFX →
              Commute (gF : F) (z : F) := by
            intro z hz
            have hqComm := (hgQcomm z hz).eq
            have hqConj :
                gQ * qF (z : F) * gQ⁻¹ = qF (z : F) := by
              rw [hqComm]
              simp
            let zConj : CFX :=
              ⟨(gF : F) * (z : F) * (gF : F)⁻¹,
                (Subgroup.mem_normalizer_iff.mp hgFnorm (z : F)).1 z.property⟩
            have hzMap : qF.subgroupMap CFX zConj = qF.subgroupMap CFX z := by
              apply Subtype.ext
              simpa [zConj, hgFmap] using hqConj
            have hzConj : zConj = z := hqInjective hzMap
            have hzConjF :
                (gF : F) * (z : F) * (gF : F)⁻¹ = (z : F) :=
              congrArg Subtype.val hzConj
            rw [Commute]
            apply mul_right_cancel (b := (gF : F)⁻¹)
            simpa [mul_assoc] using hzConjF
          have hFleL : F ≤ L := by
            rintro x ⟨y, hy, rfl⟩
            exact y.property
          let gL : L := ⟨((gF : F) : G), hFleL gF.property⟩
          have hgGnorm : ((gF : F) : G) ∈ Subgroup.normalizer CX := by
            have hgSub : gF ∈ (Subgroup.normalizer CX).subgroupOf F := by
              rw [Subgroup.subgroupOf_normalizer_eq hCXleF]
              exact hgFnorm
            exact hgSub
          have hCXsubL : CX.subgroupOf L = QP := by
            ext x
            change (x : G) ∈ CX ↔ x ∈ QP
            rw [← hQPmapCX]
            constructor
            · rintro ⟨y, hy, hxy⟩
              exact L.subtype_injective hxy ▸ hy
            · intro hx
              exact ⟨x, hx, rfl⟩
          have hgLnorm : gL ∈ Subgroup.normalizer QP := by
            rw [← hCXsubL, ← Subgroup.subgroupOf_normalizer_eq (inf_le_left : CX ≤ L)]
            exact hgGnorm
          have hgHP : gL ∈ HP := by
            rw [← (PFchapter1section1.proposition_1_d HP DP QP tP hA1P).1]
            exact hgLnorm
          let QPH : Subgroup HP := QP.subgroupOf HP
          let DPH : Subgroup HP := DP.subgroupOf HP
          letI : QPH.Normal := hA1P.Q_normal_in_H
          let gH : HP := ⟨gL, hgHP⟩
          have hgSup : gH ∈ QPH ⊔ DPH := by
            have hsup : QPH ⊔ DPH = ⊤ := by
              change QP.subgroupOf HP ⊔ DP.subgroupOf HP = ⊤
              rw [← Subgroup.subgroupOf_sup hA1P.Q_le_H hA1P.D_le_H,
                hA1P.Q_sup_D, Subgroup.subgroupOf_self]
            rw [hsup]
            exact Subgroup.mem_top gH
          rcases (Subgroup.mem_sup_of_normal_left.mp hgSup) with
            ⟨qH, hqH, dH, hdH, hqdH⟩
          let qL : L := (qH : HP)
          let dL : L := (dH : HP)
          have hqL : qL ∈ QP := hqH
          have hdL : dL ∈ DP := hdH
          have hqd : qL * dL = gL := by
            exact congrArg (fun z : HP => (z : L)) hqdH
          have hqCX : (qL : G) ∈ CX := by
            rw [← hQPmapCX]
            exact ⟨qL, hqL, rfl⟩
          let qF0 : F := ⟨(qL : G), hCXleF hqCX⟩
          have hqF0CFX : qF0 ∈ CFX := hqCX
          let dF : F := qF0⁻¹ * gF
          have hdFEq : ((dF : F) : G) = (dL : G) := by
            have hdEqL : qL⁻¹ * gL = dL := by
              calc
                qL⁻¹ * gL = qL⁻¹ * (qL * dL) := by rw [hqd]
                _ = dL := by simp
            exact congrArg (fun z : L => (z : G)) hdEqL
          have hdFCenter : ∀ z : CFX, z ∈ Subgroup.center CFX →
              Commute (dF : F) (z : F) := by
            intro z hz
            let qC : CFX := ⟨qF0, hqF0CFX⟩
            have hqComm : Commute (qF0 : F) (z : F) := by
              rw [Commute]
              exact congrArg Subtype.val
                (Subgroup.mem_center_iff.mp hz qC)
            exact hqComm.inv_left.mul_left (hgFCenter z hz)
          have hdTarget :
              ((dF : F) : G) ∈ V ⊓ Subgroup.centralizer
                ((Q0 ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := by
            have hCXSuzuki : IsSuzukiTwoGroup CX := by
              simpa [CX] using hCXsuzuki
            have hVeq :
                V = D ⊓ Subgroup.centralizer ({s} : Set G) := by
              calc
                V = peterfalviV D t := hch.1.1.V_eq
                _ = D ⊓ Subgroup.centralizer ({s} : Set G) :=
                  (PFchapter1section1.proposition_5 H D Q t s
                    hch.1.1.hA.A1 hch.1.2.1 hch.1.2.2.1
                    hch.1.2.2.2).1
            have hdCentral : ((dF : F) : G) ∈ Subgroup.centralizer
                ((Q0 ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := by
              apply (Subgroup.mem_centralizer_iff).2
              intro x hx
              have hxCX : x ∈ CX := ⟨hx.2, hch.1.1.Q0_le_Q hx.1⟩
              let xCX : CX := ⟨x, hxCX⟩
              let xC : CFX := eCXCFX xCX
              have hxCenterCX : xCX ∈ Subgroup.center CX := by
                rcases (hch.1.1.Q0_def x).mp hx.1 with hxOne | hxInv
                · have hxOneCX : xCX = 1 := Subtype.ext hxOne
                  simp [hxOneCX]
                · have hxInvCX : IsInvolution xCX :=
                    ⟨fun hxOne => hxInv.2.ne_one
                        (congrArg (fun z : CX => (z : G)) hxOne),
                      Subtype.ext hxInv.2.sq_eq_one⟩
                  have hxMem : xCX ∈ involutions CX := hxInvCX
                  rw [(higmanTheorem_involutions_center hCXSuzuki).1] at hxMem
                  exact hxMem.1
              have hxCenterCFX : xC ∈ Subgroup.center CFX := by
                exact (Subgroup.centerCongr eCXCFX ⟨xCX, hxCenterCX⟩).property
              have hcommF := (hdFCenter xC hxCenterCFX).eq
              have hcommG := congrArg (fun z : F => ((z : F) : G)) hcommF
              have hxCG : (((xC : CFX) : F) : G) = x := by
                rfl
              calc
                x * ((dF : F) : G) = (((xC : CFX) : F) : G) * ((dF : F) : G) := by rw [hxCG]
                _ = ((dF : F) : G) * (((xC : CFX) : F) : G) := hcommG.symm
                _ = ((dF : F) : G) * x := by rw [hxCG]
            have hsQ0 : s ∈ Q0 :=
              (hch.1.1.Q0_def s).mpr
                (Or.inr ⟨hch.1.2.1, hch.1.2.2.1⟩)
            have hsCentP : s ∈ Subgroup.centralizer (P : Set G) := by
              apply (Subgroup.mem_centralizer_iff).2
              intro a ha
              have haV := hPV ha
              rw [hVeq] at haV
              exact (Subgroup.mem_centralizer_iff.mp haV.2 s (by rfl)).symm
            have hdCentS : ((dF : F) : G) ∈
                Subgroup.centralizer ({s} : Set G) := by
              apply (Subgroup.mem_centralizer_iff).2
              intro x hx
              have hxEq : x = s := hx
              subst x
              exact Subgroup.mem_centralizer_iff.mp hdCentral s ⟨hsQ0, hsCentP⟩
            have hdD : ((dF : F) : G) ∈ D := by
              change (dL : G) ∈ D at hdL
              simpa [hdFEq] using hdL
            refine ⟨?_, hdCentral⟩
            rw [hVeq]
            exact ⟨hdD, hdCentS⟩
          have hdP : ((dF : F) : G) ∈ P := by
            rw [← hfixedFieldCentralizer P hPV hWbot]
            exact hdTarget
          have hdN : dL ∈ N := by
            rw [hcoreMem]
            refine ⟨⟨dL.property, ?_⟩, ?_⟩
            · change (dL : G) ∈ D at hdL ⊢
              exact hdL
            · apply (Subgroup.mem_centralizer_iff).2
              intro x hxCX
              have hxL : x ∈ L := hxCX.1
              exact (Subgroup.mem_centralizer_iff.mp hxL (dL : G)
                (by simpa [hdFEq] using hdP)).symm
          have hdNL : ((dF : F) : G) ∈ NL := by
            refine ⟨dL, hdN, ?_⟩
            exact hdFEq.symm
          have hdZFG : ((dF : F) : G) ∈ ZFG := by
            change ((dF : F) : G) ∈ (Subgroup.center F).map F.subtype
            rw [← hNLF]
            exact ⟨hdNL, dF.property⟩
          have hdFcenter : dF ∈ Subgroup.center F := by
            rcases hdZFG with ⟨z, hz, hzEq⟩
            have hdz : dF = z := by
              apply Subtype.ext
              exact hzEq.symm
            simpa [hdz] using hz
          have hdFmap : qF dF = 1 :=
            (QuotientGroup.eq_one_iff dF).mpr hdFcenter
          apply hgQnot
          rw [← hgFmap]
          have hgFdecomp : gF = qF0 * dF := by
            simp [dF]
          rw [hgFdecomp, map_mul, hdFmap, mul_one]
          exact Subgroup.mem_map_of_mem qF hqF0CFX
      exact cubic_linear_contradiction H D Q K V W Q0 S Q1 t s
        hch hSQ hVleD hDnormS
        ((PFchapter1section2.proposition_2
          H D Q K V W Q0 S Q1 t hch.1.1).2)
        hKcyclic hKfaithful hKregular hSuzuki hcardCube
        P p hPV hp hPcard hPne hlinearCX hWbot
    exact ⟨horderThree, hWne⟩
  have htypeBCase :
      IsSuzukiTwoTypeB S → orderOf (s * t) = 3 ∧ W ≠ ⊥ := by
    intro htypeB
    have hSuzuki : IsSuzukiTwoGroup S := by
      rcases PFchapter1section2.corollary
          H D Q K V W Q0 S Q1 t hch.1.1 with hcomm | hSuzuki
      · exact False.elim (htypeBNotCommutative htypeB hcomm)
      · exact hSuzuki
    have hcardCube := htypeBCardCenterCube hSuzuki htypeB
    exact hcubicEndpoint hSuzuki hcardCube
  have hcubicTypeBConclusion
      (hcardCube : Nat.card S = Nat.card (Subgroup.center S) ^ 3) :
      IsSuzukiTwoTypeB S ∧ orderOf (s * t) = 3 ∧ W ≠ ⊥ := by
    have hSuzuki := hcubicSuzuki hcardCube
    have hendpoint := hcubicEndpoint hSuzuki hcardCube
    have hQ_suzuki : IsSuzukiTwoGroup Q := by
      rw [← hSQ]
      exact hSuzuki
    have hQ_card : Nat.card Q = Nat.card Q0 ^ 3 := by
      calc
        Nat.card Q = Nat.card S := by rw [hSQ]
        _ = Nat.card (Subgroup.center S) ^ 3 := hcardCube
        _ = Nat.card Q0 ^ 3 := by rw [hQ0Center hSuzuki]
    have hlemma := PFchapter1section3.lemma_5
      H D Q K V W Q0 S Q1 t s hch.1 hind hendpoint.1 hQ_suzuki hQ_card
    have htypeBQ : IsSuzukiTwoTypeB Q := hlemma.2.2 hendpoint.2
    exact ⟨by rw [hSQ]; exact htypeBQ, hendpoint⟩
  have htypeCCase :
      IsSuzukiTwoTypeC S →
        IsSuzukiTwoTypeB S ∧ orderOf (s * t) = 3 ∧ W ≠ ⊥ := by
    intro htypeC
    exact hcubicTypeBConclusion (htypeCCardCenterCube htypeC)
  have htypeDCase :
      IsSuzukiTwoTypeD S →
        IsSuzukiTwoTypeB S ∧ orderOf (s * t) = 3 ∧ W ≠ ⊥ := by
    intro htypeD
    exact hcubicTypeBConclusion (htypeDCardCenterCube htypeD)
  have htrichotomy :
      IsMulCommutative S ∨
        (IsSuzukiTwoTypeA S ∨ IsSuzukiTwoTypeB S ∨
          IsSuzukiTwoTypeC S ∨ IsSuzukiTwoTypeD S) := by
    have htransportA :
        IsSuzukiTwoTypeA (⊤ : Subgroup S) → IsSuzukiTwoTypeA S := by
      rintro ⟨n, hn, theta, pairLift, cocycle, hperiod, hnontrivial,
        haddLeft, haddRight, hdiag, hmem, hone, hsurj, hinj, hmul⟩
      let pairLiftG :
          BinaryGaloisField n → BinaryGaloisField n → G :=
        fun a z => pairLift a z
      refine ⟨n, hn, theta, pairLiftG, cocycle, hperiod, hnontrivial,
        haddLeft, haddRight, hdiag, ?_, ?_, ?_, ?_, ?_⟩
      · intro a z
        exact (pairLift a z).property
      · exact congrArg Subtype.val hone
      · intro x hx
        let xS : S := ⟨x, hx⟩
        rcases hsurj xS (by simp) with ⟨a, z, hxEq⟩
        exact ⟨a, z, congrArg Subtype.val hxEq⟩
      · intro a z b w hEq
        apply hinj a z b w
        apply Subtype.ext
        exact hEq
      · intro a z b w
        exact congrArg Subtype.val (hmul a z b w)
    have htransportB :
        IsSuzukiTwoTypeB (⊤ : Subgroup S) → IsSuzukiTwoTypeB S := by
      rintro ⟨n, hn, theta, epsilon, tripleLift, cocycle, hepsilon,
        hperiod, hnonzero, haddLeft, haddRight, hdiag, hmem, hone,
        hsurj, hinj, hmul⟩
      let tripleLiftG : BinaryGaloisField n → BinaryGaloisField n →
          BinaryGaloisField n → G := fun c a b => tripleLift c a b
      refine ⟨n, hn, theta, epsilon, tripleLiftG, cocycle, hepsilon,
        hperiod, hnonzero, haddLeft, haddRight, hdiag, ?_, ?_, ?_,
        ?_, ?_⟩
      · intro c a b
        exact (tripleLift c a b).property
      · exact congrArg Subtype.val hone
      · intro x hx
        let xS : S := ⟨x, hx⟩
        rcases hsurj xS (by simp) with ⟨c, a, b, hxEq⟩
        exact ⟨c, a, b, congrArg Subtype.val hxEq⟩
      · intro c a b d e f hEq
        apply hinj c a b d e f
        apply Subtype.ext
        exact hEq
      · intro c a b d e f
        exact congrArg Subtype.val (hmul c a b d e f)
    have htransportC :
        IsSuzukiTwoTypeC (⊤ : Subgroup S) → IsSuzukiTwoTypeC S := by
      rintro ⟨n, hn, theta, epsilon, tripleLift, hepsilon, hperiod,
        hthetaSq, havoid, hmem, hone, hsurj, hinj, hmul⟩
      let tripleLiftG : BinaryGaloisField n → BinaryGaloisField n →
          BinaryGaloisField n → G := fun z a b => tripleLift z a b
      refine ⟨n, hn, theta, epsilon, tripleLiftG, hepsilon, hperiod,
        hthetaSq, havoid, ?_, ?_, ?_, ?_, ?_⟩
      · intro z a b
        exact (tripleLift z a b).property
      · exact congrArg Subtype.val hone
      · intro x hx
        let xS : S := ⟨x, hx⟩
        rcases hsurj xS (by simp) with ⟨z, a, b, hxEq⟩
        exact ⟨z, a, b, congrArg Subtype.val hxEq⟩
      · intro z a b w c d hEq
        apply hinj z a b w c d
        apply Subtype.ext
        exact hEq
      · intro z a b w c d
        exact congrArg Subtype.val (hmul z a b w c d)
    have htransportD :
        IsSuzukiTwoTypeD (⊤ : Subgroup S) → IsSuzukiTwoTypeD S := by
      rintro ⟨n, hn, theta, epsilon, tripleLift, hepsilon, hperiod,
        hnontrivial, havoid, hmem, hone, hsurj, hinj, hmul⟩
      let tripleLiftG : BinaryGaloisField n → BinaryGaloisField n →
          BinaryGaloisField n → G := fun z a b => tripleLift z a b
      refine ⟨n, hn, theta, epsilon, tripleLiftG, hepsilon, hperiod,
        hnontrivial, havoid, ?_, ?_, ?_, ?_, ?_⟩
      · intro z a b
        exact (tripleLift z a b).property
      · exact congrArg Subtype.val hone
      · intro x hx
        let xS : S := ⟨x, hx⟩
        rcases hsurj xS (by simp) with ⟨z, a, b, hxEq⟩
        exact ⟨z, a, b, congrArg Subtype.val hxEq⟩
      · intro z a b w c d hEq
        apply hinj z a b w c d
        apply Subtype.ext
        exact hEq
      · intro z a b w c d
        exact congrArg Subtype.val (hmul z a b w c d)
    rcases PFchapter1section2.corollary
        H D Q K V W Q0 S Q1 t hch.1.1 with hcomm | hSuzuki
    · exact Or.inl hcomm
    · right
      rcases theorem1_abcdAlternatives_of_suzukiTwoGroup hSuzuki with
        hA | hB | hC | hD
      · exact Or.inl (htransportA hA)
      · exact Or.inr <| Or.inl (htransportB hB)
      · exact Or.inr <| Or.inr <| Or.inl (htransportC hC)
      · exact Or.inr <| Or.inr <| Or.inr (htransportD hD)
  rcases htrichotomy with hcomm | htypes
  · exact Or.inl
      (hcommutativeCase hcomm)
  · rcases htypes with hA | hB | hC | hD
    · exact Or.inr <| Or.inl
        ⟨hA, htypeACase hA⟩
    · exact Or.inr <| Or.inr
        ⟨hB, htypeBCase hB⟩
    · exact Or.inr <| Or.inr (htypeCCase hC)
    · exact Or.inr <| Or.inr (htypeDCase hD)

end PFchapter3section1
end CFSG.BenderSuzuki
