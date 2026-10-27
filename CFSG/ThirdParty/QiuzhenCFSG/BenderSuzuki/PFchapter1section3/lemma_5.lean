module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.proposition_1_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1e_isomorphic_summands
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.corollary
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.AppendixIInput
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.theorem
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.lemma_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.TwoDimensionalOddOrder
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section3

open PFchapter1section1 PFAppendixIII External.Higman
open scoped Pointwise LinearAlgebra.Projectivization IsMulCommutative

universe u v

/-!
# Peterfalvi, Part II, Chapter I, Section 3, Lemma 5
-/

private theorem lemma_5_twoRank_Q0_of_suzuki
    {G : Type*} [Group G] [Finite G]
    (H Q Q0 : Subgroup G) (hQleH : Q ≤ H)
    (hQ0def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hQ : IsSuzukiTwoGroup Q) : TwoRankAtLeastTwo Q0 := by
  have hsq : ∀ x : Q0, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    rcases (hQ0def (x : G)).mp x.property with hx | hx
    · simp [hx]
    · exact hx.2.sq_eq_one
  have hP : IsPGroup 2 Q0 := by
    intro x
    refine ⟨1, ?_⟩
    simpa using hsq x
  rcases hQ.2.2.1 with ⟨x, y, hx, hy, hxy⟩
  have hxG : IsInvolution (x : G) := by
    exact ⟨fun h => hx.ne_one (Subtype.ext h),
      congrArg Subtype.val hx.sq_eq_one⟩
  have hyG : IsInvolution (y : G) := by
    exact ⟨fun h => hy.ne_one (Subtype.ext h),
      congrArg Subtype.val hy.sq_eq_one⟩
  let x0 : Q0 :=
    ⟨x, (hQ0def x).mpr (Or.inr ⟨hQleH x.property, hxG⟩)⟩
  let y0 : Q0 :=
    ⟨y, (hQ0def y).mpr (Or.inr ⟨hQleH y.property, hyG⟩)⟩
  have hx0 : x0 ≠ 1 := fun h => hxG.ne_one (by
    simpa [x0] using congrArg Subtype.val h)
  have hy0 : y0 ≠ 1 := fun h => hyG.ne_one (by
    simpa [y0] using congrArg Subtype.val h)
  have hxy0 : x0 ≠ y0 := fun h => hxy (by
    apply Subtype.ext
    simpa [x0, y0] using congrArg Subtype.val h)
  letI : Fintype Q0 := Fintype.ofFinite Q0
  have hcard_gt : 2 < Nat.card Q0 := by
    simpa [Nat.card_eq_fintype_card] using
      (Fintype.two_lt_card_iff.mpr
        ⟨1, x0, y0, hx0.symm, hy0.symm, hxy0⟩)
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra hn2
    have hn_cases : n = 0 ∨ n = 1 := by omega
    rcases hn_cases with rfl | rfl <;>
      rw [hn] at hcard_gt <;> norm_num at hcard_gt
  have hcard4 : 2 ^ 2 ≤ Nat.card Q0 := by
    rw [hn]
    exact pow_le_pow_right' (by norm_num) hn2
  obtain ⟨E, hEcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hP hcard4
  refine ⟨E, by norm_num at hEcard ⊢; exact hEcard, ?_⟩
  intro z
  apply Subtype.ext
  change (z : Q0) ^ 2 = 1
  exact hsq (z : Q0)

private theorem lemma_5_twoRank_of_le
    {G : Type*} [Group G] [Finite G] (P C : Subgroup G) (hPC : P ≤ C)
    (hP : TwoRankAtLeastTwo P) : TwoRankAtLeastTwo C := by
  obtain ⟨E0, hcard, hsq⟩ := hP
  let inclusion : P →* C := Subgroup.inclusion hPC
  let E : Subgroup C := E0.map inclusion
  have hEcard : Nat.card E = 4 := by
    rw [Subgroup.card_map_of_injective]
    · exact hcard
    · exact Subgroup.inclusion_injective hPC
  refine ⟨E, hEcard, ?_⟩
  rintro ⟨x, hx⟩
  rcases hx with ⟨y, hy, rfl⟩
  apply Subtype.ext
  have hy2 : y ^ 2 = 1 := congrArg Subtype.val (hsq ⟨y, hy⟩)
  change inclusion y ^ 2 = 1
  rw [← map_pow, hy2, map_one]

private theorem lemma_5_Q0_le_centralizer_zpowers_of_mem_W
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 : Subgroup G) (t w : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hKdef : ∀ x : G, x ∈ K ↔
      x ∈ D ∧ rightConjugateElem x t = x⁻¹)
    (hVeq : V = peterfalviV D t) (hWeq : W = peterfalviW V (K : Set G))
    (hQ0def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hwW : w ∈ W) :
    Q0 ≤ Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
  have hWdesc :=
    PFchapter1section2.peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
      H D Q K V W t hA1 hKdef hVeq hWeq
  have hwI : w ∈
      Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) := by
    have hw := hwW
    rw [hWdesc] at hw
    exact hw.2
  intro q hqQ0
  rw [Subgroup.mem_centralizer_iff]
  intro x hxX
  rcases Subgroup.mem_zpowers_iff.mp hxX with ⟨n, rfl⟩
  have hqw : Commute q w := by
    rcases (hQ0def q).mp hqQ0 with hq | hq
    · subst q
      exact Commute.one_left w
    · exact Subgroup.mem_centralizer_iff.mp hwI q hq
  exact (hqw.zpow_right n).eq.symm

private theorem lemma_5_D_inf_centralizer_Q_eq_bot
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t s : G)
    (hA : HypothesisA G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) :
    D ⊓ Subgroup.centralizer (Q : Set G) = ⊥ := by
  have hcore :=
    (PFchapter1section1.proposition_4_c H D Q t s hA.A1 hsH hsI hsStructure).1
  rw [← hcore, eq_bot_iff]
  intro x hxCore
  have hfix : ∀ omega : Ω, x • omega = omega := by
    have hxAll : ∀ point : Ω, x ∈ MulAction.stabilizer G point := by
      simpa [pointStabilizerCore] using hxCore
    intro omega
    exact MulAction.mem_stabilizer_iff.mp (hxAll omega)
  have hxOne : x = 1 := (faithfulSMul_iff.mp hA.A2) x hfix
  simpa [hxOne]

private theorem lemma_5_centralizer_eq_Q0_of_classification
    {G : Type*} [Group G] [Finite G]
    (D Q Q0 X : Subgroup G) (w st : G)
    (hQ0leQ : Q0 ≤ Q)
    (hQ0leCX : Q0 ≤ Subgroup.centralizer (X : Set G))
    (hwX : w ∈ X) (hwD : w ∈ D) (hwne : w ≠ 1)
    (hDcap : D ⊓ Subgroup.centralizer (Q : Set G) = ⊥)
    (hst : orderOf st = 3)
    (hQcard : Nat.card Q = Nat.card Q0 ^ 3)
    (hclass :
      ∃ ell : ℕ,
        ell = Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ Q0) ∧
          ((orderOf st = 3 ∧
              Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ Q) = ell) ∨
            (orderOf st = 5 ∧
              Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ Q) = ell ^ 2) ∨
            (orderOf st = 3 ∧
              Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ Q) = ell ^ 3))) :
    Subgroup.centralizer (X : Set G) ⊓ Q = Q0 := by
  let C := Subgroup.centralizer (X : Set G) ⊓ Q
  have hQ0leC : Q0 ≤ C := fun x hx => ⟨hQ0leCX hx, hQ0leQ hx⟩
  have hCQ0 : Subgroup.centralizer (X : Set G) ⊓ Q0 = Q0 :=
    inf_eq_right.mpr hQ0leCX
  obtain ⟨ell, hell, hcases⟩ := hclass
  have hellQ0 : ell = Nat.card Q0 := by simpa [hCQ0] using hell
  rcases hcases with hsmall | hmiddle | hlarge
  · exact (Subgroup.eq_of_le_of_card_ge hQ0leC (by
      rw [hsmall.2, hellQ0])).symm
  · omega
  · have hCQ : C = Q := by
      have hcardC : Nat.card C = Nat.card Q := by
        calc
          Nat.card C = ell ^ 3 := hlarge.2
          _ = Nat.card Q0 ^ 3 := by rw [hellQ0]
          _ = Nat.card Q := hQcard.symm
      exact Subgroup.eq_of_le_of_card_ge
        (H := C) (K := Q) inf_le_right hcardC.ge
    have hwCQ : w ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqC : q ∈ C := by simpa [hCQ] using hq
      have hcomm :=
        (Subgroup.mem_centralizer_iff.mp hqC.1) w hwX
      exact hcomm.symm
    have hwbot : w ∈ (⊥ : Subgroup G) := by
      rw [← hDcap]
      exact ⟨hwD, hwCQ⟩
    exact False.elim (hwne (by simpa using hwbot))

public theorem lemma_5_nontrivial_W_centralizer_eq_Q0
    {G : Type u} {Ω : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s w : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
      K ≤ D ∧
        (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
          V = peterfalviV D t ∧
            W ≤ V ∧ W = peterfalviW V (K : Set G) ∧
              Q0 ≤ Q ∧
                (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
                  S ≤ Q ∧ Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧ Disjoint S Q1 ∧
                        (∀ a : G, a ∈ S → ∀ b : G, b ∈ Q1 → a * b = b * a) ∧
                          S ⊔ Q1 = Q) ∧
        s ∈ H ∧ IsInvolution s ∧
          ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G → HypothesisA L ΩL HL DL QL tL →
            suzukiConclusion L ΩL)
    (hst : orderOf (s * t) = 3)
    (hQ : IsSuzukiTwoGroup Q)
    (hQcard : Nat.card Q = Nat.card Q0 ^ 3)
    (hwW : w ∈ W) (hwne : w ≠ 1) :
    Subgroup.centralizer (Subgroup.zpowers w : Set G) ⊓ Q = Q0 := by
  let X := Subgroup.zpowers w
  have hXne : X ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hwne
  have hXleV : X ≤ V := Subgroup.zpowers_le.mpr (hsec.section2.W_le_V hwW)
  have hQ0leCX : Q0 ≤ Subgroup.centralizer (X : Set G) :=
    lemma_5_Q0_le_centralizer_zpowers_of_mem_W H D Q K V W Q0 t w
      hsec.section2.hA.A1 hsec.section2.K_def hsec.section2.V_eq
      hsec.section2.W_eq hsec.section2.Q0_def hwW
  have hQ0rank : TwoRankAtLeastTwo Q0 :=
    lemma_5_twoRank_Q0_of_suzuki H Q Q0 hsec.section2.hA.A1.Q_le_H
      hsec.section2.Q0_def hQ
  have hXrank : TwoRankAtLeastTwo (Subgroup.centralizer (X : Set G)) :=
    lemma_5_twoRank_of_le Q0 (Subgroup.centralizer (X : Set G))
      hQ0leCX hQ0rank
  rcases proposition_1_c H D Q K V W Q0 S Q1 X t s hsec hind
      hXne hXleV hXrank with
    ⟨_hCQ1, _hNLF, ell, _hellPow, _hellGt, hell, hcases⟩
  have hclass :
      ∃ ell : ℕ,
        ell = Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ Q0) ∧
          ((orderOf (s * t) = 3 ∧
              Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ Q) = ell) ∨
            (orderOf (s * t) = 5 ∧
              Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ Q) = ell ^ 2) ∨
            (orderOf (s * t) = 3 ∧
              Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ Q) = ell ^ 3)) := by
    refine ⟨ell, hell, ?_⟩
    rcases hcases with hpsl | hsuzuki | hunitary
    · rcases hpsl with ⟨k, hk, hkell, hmodel, horder, htype, hcard⟩
      exact Or.inl ⟨horder, hcard⟩
    · rcases hsuzuki with ⟨k, hk, hkell, hmodel, horder, htype, hcard⟩
      exact Or.inr (Or.inl ⟨horder, hcard⟩)
    · rcases hunitary with
        ⟨E, hEfield, hEfinite, J, hJ, hEcard, hfixed, hmodel,
          horder, htype, hcard, _hliftedSeed⟩
      exact Or.inr (Or.inr ⟨horder, hcard⟩)
  have hVleD : V ≤ D := by
    intro x hx
    rw [hsec.section2.V_eq] at hx
    exact hx.1
  have hwD : w ∈ D := hVleD (hsec.section2.W_le_V hwW)
  have hDcap : D ⊓ Subgroup.centralizer (Q : Set G) = ⊥ :=
    lemma_5_D_inf_centralizer_Q_eq_bot H D Q t s hsec.section2.hA
      hsec.s_mem_H hsec.s_involution hsec.s_conjugate
  exact lemma_5_centralizer_eq_Q0_of_classification D Q Q0 X w (s * t)
    hsec.section2.Q0_le_Q hQ0leCX (Subgroup.mem_zpowers w) hwD hwne
    hDcap hst hQcard hclass

private theorem lemma_5_cubic_line_root_card
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
      Fintype.card_eq_nat_card] at hsplit
    rw [hPlaneCard, hCenterPlaneCard] at hsplit
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
    change orbitRoot (unorbitRoot x) = x
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
    have hlt : 1 < q := by
      simpa [q] using (Subgroup.center S).one_lt_card_iff_ne_bot.mpr hcenterNe
    omega
  have hcardRoot : Nat.card Root = q := by
    rw [hKcard] at hcardEq
    have hfactor : q ^ 2 - q = (q - 1) * q := by
      rw [pow_two, Nat.sub_mul]
      simp
    rw [hfactor] at hcardEq
    exact Nat.mul_left_cancel (Nat.sub_pos_of_lt hqTwo) hcardEq
  simpa [Root, Plane, qmap, q] using hcardRoot

private theorem lemma_5_Q0_order_four_subgroup
    {G : Type u} {Ω : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
                            S ⊔ Q1 = Q)) :
    ∃ E0 : Subgroup G, E0 ≤ Q0 ∧ Nat.card E0 = 4 ∧
      ∀ x : E0, x ^ 2 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E0, hE0card, hE0sq⟩ :=
    TwoRankAtLeastTwo.exists_subgroup hsec.hA.A3
  have hE0p : IsPGroup 2 E0 := by
    refine IsPGroup.of_card (p := 2) (G := E0) (n := 2) ?_
    norm_num [hE0card]
  obtain ⟨T0, hE0T⟩ := IsPGroup.exists_le_sylow (G := G) (p := 2) hE0p
  obtain ⟨S0, hS0Q⟩ :=
    PFchapter1section1.proposition_1_c H D Q t hsec.hA.A1
  obtain ⟨g, hgTS⟩ := MulAction.exists_smul_eq G T0 S0
  let A0 : Subgroup G := E0.map (MulAut.conj g).toMonoidHom
  have hA0_le_S0 : A0 ≤ (S0 : Subgroup G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyE, rfl⟩
    have hyT : y ∈ (T0 : Subgroup G) := hE0T hyE
    rw [← hgTS, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g)
      (T0 : Subgroup G) hyT
  have hA0card : Nat.card A0 = 4 := by
    calc
      Nat.card A0 = Nat.card E0 :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
      _ = 4 := hE0card
  have hA0sq : ∀ x : A0, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    change (x : G) ^ 2 = 1
    rcases Subgroup.mem_map.mp x.property with ⟨y, hyE, hyx⟩
    have hy2 : y ^ 2 = (1 : G) :=
      congrArg Subtype.val (hE0sq ⟨y, hyE⟩)
    rw [← hyx]
    simpa [pow_two] using congrArg (fun z : G => (MulAut.conj g) z) hy2
  have hA0Q0 : A0 ≤ Q0 := by
    intro x hx
    apply (hsec.Q0_def x).mpr
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr ⟨hsec.hA.A1.Q_le_H (hS0Q (hA0_le_S0 hx)),
        ⟨hx1, congrArg Subtype.val (hA0sq ⟨x, hx⟩)⟩⟩
  exact ⟨A0, hA0Q0, hA0card, hA0sq⟩


set_option maxHeartbeats 800000 in
private theorem cyclic_and_card_dvd_of_projective_stabilizers_bot
    {F W X : Type*} [Field F] [Finite F] [Group W] [Finite W]
    [AddCommGroup X] [Module F X] [FiniteDimensional F X] [Nontrivial X]
    [DistribMulAction W X] [SMulCommClass W F X] [Nontrivial W]
    (hdim : Module.finrank F X = 2)
    (hWodd : Odd (Nat.card W))
    (hcharNotDvd : ¬ ringChar F ∣ Nat.card W)
    (hprojectiveStabilizer : ∀ z : ℙ F X,
      MulAction.stabilizer W z = ⊥) :
    IsCyclic W ∧ Nat.card W ∣ Nat.card F + 1 := by
  let rho : Representation F W X :=
    Representation.ofDistribMulAction F W X
  have hrhoApply : ∀ w : W, ∀ x : X, rho w x = w • x := by
    intro w x
    rfl
  have hprojectiveCard : Nat.card (ℙ F X) = Nat.card F + 1 :=
    Projectivization.card_of_finrank_two F X hdim
  have hdivF : Nat.card W ∣ Nat.card F + 1 := by
    let OrbitQuot := Quotient (MulAction.orbitRel W (ℙ F X))
    have hcardEquiv :=
      Nat.card_congr
        (MulAction.selfEquivOrbitsQuotientProd hprojectiveStabilizer)
    refine ⟨Nat.card OrbitQuot, ?_⟩
    calc
      Nat.card F + 1 = Nat.card (ℙ F X) := hprojectiveCard.symm
      _ = Nat.card OrbitQuot * Nat.card W := by
        simpa [OrbitQuot, Nat.card_prod] using hcardEquiv
      _ = Nat.card W * Nat.card OrbitQuot := by rw [mul_comm]
  have hrhoInjective : Function.Injective rho := by
    intro a b hab
    let g : W := b⁻¹ * a
    have hgRho : rho g = 1 := by
      calc
        rho g = rho b⁻¹ * rho a := by exact map_mul rho b⁻¹ a
        _ = rho b⁻¹ * rho b := by rw [hab]
        _ = rho (b⁻¹ * b) := (map_mul rho b⁻¹ b).symm
        _ = 1 := by simp
    have hgvec : ∀ x : X, g • x = x := by
      intro x
      have hx := DFunLike.congr_fun hgRho x
      change rho g x = x at hx
      exact (hrhoApply g x).symm.trans hx
    obtain ⟨v0, hv0⟩ := exists_ne (0 : X)
    let z0 : ℙ F X := Projectivization.mk F v0 hv0
    have hgz0 : g • z0 = z0 := by
      change Projectivization.mk F (g • v0) _ =
        Projectivization.mk F v0 hv0
      apply (Projectivization.mk_eq_mk_iff' F (g • v0) v0
        ((smul_ne_zero_iff_ne g).mpr hv0) hv0).2
      exact ⟨1, by simpa using (hgvec v0).symm⟩
    have hgmem : g ∈ MulAction.stabilizer W z0 :=
      MulAction.mem_stabilizer_iff.mpr hgz0
    have hgOne : g = 1 := by
      have : g ∈ (⊥ : Subgroup W) := by
        rw [← hprojectiveStabilizer z0]
        exact hgmem
      simpa using this
    have hmul := congrArg (fun z : W => b * z) hgOne
    simpa [g, mul_assoc] using hmul
  have hrhoIrreducible : Representation.IsIrreducible rho := by
    refine
      { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩
        eq_bot_or_eq_top := ?_ }
    intro R
    by_cases hRbot : R = ⊥
    · exact Or.inl hRbot
    by_cases hRtop : R = ⊤
    · exact Or.inr hRtop
    exfalso
    have hSubBot : R.toSubmodule ≠ ⊥ := by
      intro h
      apply hRbot
      apply Subrepresentation.toSubmodule_injective
      simpa
    have hSubTop : R.toSubmodule ≠ ⊤ := by
      intro h
      apply hRtop
      apply Subrepresentation.toSubmodule_injective
      simpa
    rcases R.toSubmodule.ne_bot_iff.mp hSubBot with ⟨v, hvR, hv⟩
    have hspanLe : F ∙ v ≤ R.toSubmodule :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvR)
    have hdimLower : 1 ≤ Module.finrank F R.toSubmodule := by
      rw [← finrank_span_singleton (K := F) hv]
      exact Submodule.finrank_mono hspanLe
    have hdimUpper : Module.finrank F R.toSubmodule < 2 := by
      have hlt := Submodule.finrank_lt hSubTop
      simpa [hdim] using hlt
    have hdimR : Module.finrank F R.toSubmodule = 1 := by omega
    let z : ℙ F X := Projectivization.mk F v hv
    have hWfixZ : ∀ w : W, w • z = z := by
      intro w
      have hwRrho : rho w v ∈ R.toSubmodule :=
        R.apply_mem_toSubmodule w hvR
      have hwR : w • v ∈ R.toSubmodule := by
        rw [← hrhoApply w v]
        exact hwRrho
      let vR : R.toSubmodule := ⟨v, hvR⟩
      let wvR : R.toSubmodule := ⟨w • v, hwR⟩
      have hvRne : vR ≠ 0 := by
        intro h
        exact hv (congrArg Subtype.val h)
      rcases exists_smul_eq_of_finrank_eq_one (K := F) hdimR hvRne wvR with
        ⟨a, ha⟩
      change Projectivization.mk F (w • v) _ =
        Projectivization.mk F v hv
      apply (Projectivization.mk_eq_mk_iff' F (w • v) v
        ((smul_ne_zero_iff_ne w).mpr hv) hv).2
      exact ⟨a, congrArg Subtype.val ha⟩
    have hsub : Subsingleton W := by
      constructor
      intro a b
      have haMem : a ∈ MulAction.stabilizer W z :=
        MulAction.mem_stabilizer_iff.mpr (hWfixZ a)
      have hbMem : b ∈ MulAction.stabilizer W z :=
        MulAction.mem_stabilizer_iff.mpr (hWfixZ b)
      have haOne : a = 1 := by
        rw [hprojectiveStabilizer z] at haMem
        simpa using haMem
      have hbOne : b = 1 := by
        rw [hprojectiveStabilizer z] at hbMem
        simpa using hbMem
      exact haOne.trans hbOne.symm
    exact not_subsingleton W hsub
  letI : Representation.IsIrreducible rho := hrhoIrreducible
  have hWcomm : IsMulCommutative W :=
    theorem_2_6_a hWodd hdim hrhoInjective hcharNotDvd
  have hcenterCyclic : IsCyclic (Subgroup.center W) :=
    center_cyclic_of_representation_faithful_irreducible rho hrhoInjective
  have hWcyclic : IsCyclic W := by
    letI : IsMulCommutative W := hWcomm
    have hcenterTop : Subgroup.center W = ⊤ := by
      ext x; constructor
      · intro hx; exact Subgroup.mem_top x
      · intro hx
        rw [Subgroup.mem_center_iff]
        intro y
        haveI : IsMulCommutative W := hWcomm
        exact mul_comm y x
    have htopCyclic : IsCyclic (⊤ : Subgroup W) := by
      rw [← hcenterTop]
      exact hcenterCyclic
    exact (MulEquiv.isCyclic Subgroup.topEquiv).1 htopCyclic
  exact ⟨hWcyclic, hdivF⟩

public theorem quotient_scalar_coordinates_of_isomorphic_summands
    {K E : Type u} [Group K] [Finite K] [Group E] [Finite E]
    [MulDistribMulAction K E]
    (hEcomm : IsMulCommutative E)
    (hEsq : ∀ x : E, x ^ 2 = 1)
    (hKcyclic : IsCyclic K)
    (hKfixedFree : ∀ k : K, k ≠ 1 → ∀ x : E, k • x = x → x = 1)
    (q : ℕ) (hKcard : Nat.card K = q - 1)
    (U V : Subgroup E)
    (hUinv : IsXInvariantSubgroup K U)
    (hVinv : IsXInvariantSubgroup K V)
    (hUcard : Nat.card U = q)
    (hVcard : Nat.card V = q)
    (hUVinf : U ⊓ V = ⊥)
    (hUVsup : U ⊔ V = ⊤)
    (e : U ≃* V)
    (he : ∀ k : K, ∀ u : U,
      ((e ⟨k • (u : E), (hUinv k (u : E)).mp u.property⟩ : V) : E) =
        k • ((e u : V) : E)) :
    ∃ (n : ℕ) (_ : n ≠ 0)
        (eK : K ≃* (BinaryGaloisField n)ˣ)
        (eQ : E ≃*
          Multiplicative (BinaryGaloisField n × BinaryGaloisField n)),
      Nat.card (BinaryGaloisField n) = q ∧
      ∀ k : K, ∀ x : E,
        (eQ (k • x)).toAdd =
          (((eK k : BinaryGaloisField n) * (eQ x).toAdd.1,
            (eK k : BinaryGaloisField n) * (eQ x).toAdd.2)) := by
  classical
  letI : IsMulCommutative E := hEcomm
  letI : CommGroup E := IsMulCommutative.instCommGroup
  have hq_gt : 1 < q := by
    have hpos : 0 < Nat.card K := Nat.card_pos
    omega
  letI : Nontrivial U :=
    Finite.one_lt_card_iff_nontrivial.mp (by simpa [hUcard] using hq_gt)
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsInvariant K E U := ⟨hUinv⟩
  letI : IsElementaryAbelian 2 U := by
    refine
      { toIsMulCommutative := inferInstance
        exponent_dvd_p :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_ }
    intro u
    apply Subtype.ext
    exact hEsq (u : E)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  let rhoU :=
    Theory.Representation.ofElementaryAbelianAction (A := K) (G := U) (p := 2)
  let rhoEquiv : K →* (Additive U ≃ₗ[ZMod 2] Additive U) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod 2) (Additive U)).toMonoidHom.comp rhoU.asGroupHom
  let T : Additive U ≃ₗ[ZMod 2] Additive U := rhoEquiv g
  have hrho_val (k : K) (v : Additive U) :
      rhoEquiv k v = Additive.ofMul (k • v.toMul) := by
    change rhoU k v = Additive.ofMul (k • v.toMul)
    exact Theory.Representation.ofElementaryAbelianAction_apply k v
  have hT_val (v : Additive U) :
      T v = Additive.ofMul (g • v.toMul) := by
    exact hrho_val g v
  have hT_pow_val :
      ∀ j : ℕ, ∀ v : Additive U,
        (T ^ j) v = Additive.ofMul (g ^ j • v.toMul) := by
    intro j
    induction j with
    | zero => intro v; simp
    | succ j ih =>
        intro v
        rw [show T ^ (j + 1) = T * T ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply, hT_val, ih]
        simp [pow_succ', smul_smul]
  have hT_irreducible :
      ∀ W : Submodule (ZMod 2) (Additive U),
        (∀ v : Additive U, v ∈ W → T v ∈ W) →
        W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_cases hWbot : W = ⊥
    · exact Or.inl hWbot
    right
    obtain ⟨vW, hv0W⟩ :=
      W.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hWbot)
    let v : Additive U := vW
    have hvW : v ∈ W := vW.property
    have hv0 : v ≠ 0 := by
      intro hv
      apply hv0W
      apply Subtype.ext
      exact hv
    have hW_pow :
        ∀ j : ℕ, ∀ w : Additive U, w ∈ W → (T ^ j) w ∈ W := by
      intro j
      induction j with
      | zero => intro w hw; simpa using hw
      | succ j ih =>
          intro w hw
          rw [show T ^ (j + 1) = T * T ^ j by rw [pow_succ'],
            LinearEquiv.mul_apply]
          exact hW _ (ih w hw)
    let f : Option K → W
      | none => 0
      | some k =>
          ⟨Additive.ofMul (k • v.toMul), by
            obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hg k)
            have hmem := hW_pow j v hvW
            rw [hT_pow_val] at hmem
            exact hmem⟩
    have hf : Function.Injective f := by
      intro a b hab
      cases a with
      | none =>
          cases b with
          | none => rfl
          | some k =>
              exfalso
              have hzero : Additive.ofMul (k • v.toMul) = 0 := by
                exact (congrArg (fun z : W => (z : Additive U)) hab).symm
              have hkone : k • v.toMul = 1 := by
                apply Additive.ofMul.injective
                simpa using hzero
              have hvone : v.toMul = 1 := by
                calc
                  v.toMul = k⁻¹ • (k • v.toMul) := by
                    simp [smul_smul]
                  _ = k⁻¹ • 1 := by rw [hkone]
                  _ = 1 := by simp
              apply hv0
              apply Additive.toMul.injective
              simpa using hvone
      | some k =>
          cases b with
          | none =>
              exfalso
              have hzero : Additive.ofMul (k • v.toMul) = 0 := by
                exact congrArg (fun z : W => (z : Additive U)) hab
              have hkone : k • v.toMul = 1 := by
                apply Additive.ofMul.injective
                simpa using hzero
              have hvone : v.toMul = 1 := by
                calc
                  v.toMul = k⁻¹ • (k • v.toMul) := by
                    simp [smul_smul]
                  _ = k⁻¹ • 1 := by rw [hkone]
                  _ = 1 := by simp
              apply hv0
              apply Additive.toMul.injective
              simpa using hvone
          | some l =>
              congr 1
              have hact : k • v.toMul = l • v.toMul := by
                apply Additive.ofMul.injective
                exact congrArg (fun z : W => (z : Additive U)) hab
              have hfix : (l⁻¹ * k) • v.toMul = v.toMul := by
                calc
                  (l⁻¹ * k) • v.toMul = l⁻¹ • (k • v.toMul) := by
                    rw [mul_smul]
                  _ = l⁻¹ • (l • v.toMul) := by rw [hact]
                  _ = v.toMul := by simp [smul_smul]
              have hfactor : l⁻¹ * k = 1 := by
                by_contra hne
                have hvone :=
                  hKfixedFree (l⁻¹ * k) hne (v.toMul : E)
                    (by exact congrArg Subtype.val hfix)
                apply hv0
                apply Additive.toMul.injective
                apply Subtype.ext
                simpa using hvone
              calc
                k = l * (l⁻¹ * k) := by group
                _ = l := by rw [hfactor]; simp
    have hcard_lower : q ≤ Nat.card W := by
      calc
        q = Nat.card K + 1 := by omega
        _ = Nat.card (Option K) := Finite.card_option.symm
        _ ≤ Nat.card W := Nat.card_le_card_of_injective f hf
    have hcard_upper : Nat.card W ≤ Nat.card (Additive U) :=
      Nat.card_le_card_of_injective (Subtype.val : W → Additive U) Subtype.val_injective
    have hUcard_add : Nat.card (Additive U) = q := by
      have hcard_eq : Nat.card (Additive U) = Nat.card U :=
        Nat.card_congr
          { toFun := Additive.toMul
            invFun := Additive.ofMul
            left_inv := by intro x; cases x; rfl
            right_inv := by intro x; rfl }
      rw [hcard_eq, hUcard]
    have hWcard : Nat.card W = Nat.card (Additive U) := by
      apply Nat.le_antisymm hcard_upper
      simpa [hUcard_add] using hcard_lower
    have hWtop :
        W.toAddSubgroup = (⊤ : AddSubgroup (Additive U)) :=
      AddSubgroup.eq_top_of_card_eq W.toAddSubgroup hWcard
    apply Submodule.toAddSubgroup_injective
    simpa using hWtop
  obtain ⟨n, hnpos, lambda, uCoordinates, _basis,
      hUcardField, hlambda, hTcoordinates, _heigen, _hexpansion⟩ :=
    lemma5_irreducible_conjugate_eigenbasis T hT_irreducible
  have hrhoEquiv_injective : Function.Injective rhoEquiv := by
    intro k l hkl
    obtain ⟨u, hu⟩ := exists_ne (1 : U)
    have hact : k • u = l • u := by
      apply Additive.ofMul.injective
      calc
        Additive.ofMul (k • u) =
            rhoEquiv k (Additive.ofMul u) := (hrho_val k (Additive.ofMul u)).symm
        _ = rhoEquiv l (Additive.ofMul u) := by rw [hkl]
        _ = Additive.ofMul (l • u) := hrho_val l (Additive.ofMul u)
    have hfix : (l⁻¹ * k) • u = u := by
      calc
        (l⁻¹ * k) • u = l⁻¹ • (k • u) := by rw [mul_smul]
        _ = l⁻¹ • (l • u) := by rw [hact]
        _ = u := by simp [smul_smul]
    have hfactor : l⁻¹ * k = 1 := by
      by_contra hne
      have huone :=
        hKfixedFree (l⁻¹ * k) hne (u : E)
          (by exact congrArg Subtype.val hfix)
      apply hu
      apply Subtype.ext
      simpa using huone
    calc
      k = l * (l⁻¹ * k) := by group
      _ = l := by rw [hfactor]; simp
  have hg_order : orderOf g = Nat.card K :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hT_order : orderOf T = q - 1 := by
    calc
      orderOf T = orderOf g := by
        simpa [T] using orderOf_injective rhoEquiv hrhoEquiv_injective g
      _ = Nat.card K := hg_order
      _ = q - 1 := hKcard
  let F := BinaryGaloisField n
  let lambdaUnit : Fˣ := Units.mk0 lambda hlambda
  have hT_coordinate_pow : ∀ j : ℕ, ∀ alpha : F,
      (T ^ j) (uCoordinates alpha) =
        uCoordinates (((lambdaUnit ^ j : Fˣ) : F) * alpha) := by
    intro j
    induction j with
    | zero =>
        intro alpha
        simp
    | succ j ih =>
        intro alpha
        simpa only [pow_succ, LinearEquiv.mul_apply, Units.val_mul] using
          (calc
            (T ^ j) (T (uCoordinates alpha)) =
                (T ^ j) (uCoordinates (lambda * alpha)) := by
                  rw [hTcoordinates]
            _ = uCoordinates
                (((lambdaUnit ^ j : Fˣ) : F) * (lambda * alpha)) :=
              ih (lambda * alpha)
            _ = uCoordinates
                ((((lambdaUnit ^ j * lambdaUnit : Fˣ) : F) * alpha)) := by
              congr 1
              simp only [lambdaUnit, Units.val_mul, Units.val_mk0]
              rw [mul_assoc])
  have hT_dvd_lambda : orderOf T ∣ orderOf lambdaUnit := by
    apply (orderOf_dvd_iff_pow_eq_one).2
    apply LinearEquiv.ext
    intro x
    obtain ⟨alpha, rfl⟩ := uCoordinates.surjective x
    rw [hT_coordinate_pow]
    have hpow := pow_orderOf_eq_one lambdaUnit
    rw [hpow]
    simp
  have hlambda_dvd_T : orderOf lambdaUnit ∣ orderOf T := by
    apply (orderOf_dvd_iff_pow_eq_one).2
    apply Units.ext
    have hpow := LinearEquiv.congr_fun (pow_orderOf_eq_one T)
      (uCoordinates (1 : F))
    rw [hT_coordinate_pow] at hpow
    simpa using uCoordinates.injective hpow
  have hlambda_order : orderOf lambdaUnit = q - 1 := by
    calc
      orderOf lambdaUnit = orderOf T :=
        Nat.dvd_antisymm hlambda_dvd_T hT_dvd_lambda
      _ = q - 1 := hT_order
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
  have hq_pow : q = 2 ^ n := by
    calc
      q = Nat.card U := hUcard.symm
      _ = Nat.card (Additive U) := rfl
      _ = 2 ^ n := hUcardField
  have hFcard : Nat.card F = q := by
    calc
      Nat.card F = 2 ^ n := GaloisField.card 2 n hn
      _ = q := hq_pow.symm
  have hlambda_units_card : Nat.card Fˣ = q - 1 := by
    rw [Nat.card_units, hFcard]
  have hlambda_generator : ∀ x : Fˣ, x ∈ Subgroup.zpowers lambdaUnit := by
    have htop : Subgroup.zpowers lambdaUnit = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers,
        hlambda_order, hlambda_units_card]
    intro x
    rw [htop]
    trivial
  let eK : K ≃* Fˣ :=
    mulEquivOfOrderOfEq hg hlambda_generator
      (hg_order.trans (hKcard.trans hlambda_order.symm))
  have heK_g : eK g = lambdaUnit := by
    exact mulEquivOfOrderOfEq_apply_gen _ _ _
  let eU : U ≃* Multiplicative F :=
    (MulEquiv.multiplicativeAdditive _).symm.trans
      uCoordinates.symm.toAddEquiv.toMultiplicative
  letI : IsInvariant K E V := ⟨hVinv⟩
  let eV : V ≃* Multiplicative F := e.symm.trans eU
  have heU_pow (j : ℕ) (u : U) :
      (eU (g ^ j • u)).toAdd =
        (((lambdaUnit ^ j : Fˣ) : F) * (eU u).toAdd) := by
    change uCoordinates.symm (Additive.ofMul (g ^ j • u)) =
      (((lambdaUnit ^ j : Fˣ) : F) *
        uCoordinates.symm (Additive.ofMul u))
    have hpow : (T ^ j) (Additive.ofMul u) =
        Additive.ofMul (g ^ j • u) := by
      simpa using hT_pow_val j (Additive.ofMul u)
    rw [← hpow]
    conv_lhs =>
      rw [← uCoordinates.apply_symm_apply (Additive.ofMul u)]
    rw [hT_coordinate_pow, uCoordinates.symm_apply_apply]
  have heU_action (k : K) (u : U) :
      (eU (k • u)).toAdd =
        ((eK k : F) * (eU u).toAdd) := by
    obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hg k)
    simpa [map_pow, heK_g] using heU_pow j u
  have he_subtype (k : K) (u : U) : e (k • u) = k • e u := by
    apply Subtype.ext
    exact he k u
  have he_symm_subtype (k : K) (v : V) :
      e.symm (k • v) = k • e.symm v := by
    apply e.injective
    rw [e.apply_symm_apply, he_subtype, e.apply_symm_apply]
  have heV_action (k : K) (v : V) :
      (eV (k • v)).toAdd =
        ((eK k : F) * (eV v).toAdd) := by
    simpa [eV, he_symm_subtype] using heU_action k (e.symm v)
  letI : U.Normal := Subgroup.normal_of_isMulCommutative U
  have hUVdisjoint : Disjoint U V :=
    disjoint_iff.mpr hUVinf
  have hUVmul : (U : Set E) * (V : Set E) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ U ⊔ V := by
      rw [hUVsup]
      simp
    rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := U) (t := V)).1 hx with
      ⟨u, hu, v, hv, huv⟩
    exact ⟨u, hu, v, hv, huv⟩
  have hUVcomp : U.IsComplement' V :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hUVdisjoint hUVmul
  let decompFun : U × V → E := fun uv => (uv.1 : E) * (uv.2 : E)
  have hdecompBijective : Function.Bijective decompFun := hUVcomp
  let decompEquiv : U × V ≃ E :=
    Equiv.ofBijective decompFun hdecompBijective
  let decomp : U × V ≃* E :=
    { decompEquiv with
      map_mul' := by
        intro a b
        change ((a.1 * b.1 : U) : E) * ((a.2 * b.2 : V) : E) =
          ((a.1 : E) * (a.2 : E)) * ((b.1 : E) * (b.2 : E))
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        ac_rfl }
  let pairMultiplicative :
      Multiplicative F × Multiplicative F ≃*
        Multiplicative (F × F) :=
    MulEquiv.refl _
  let eQ : E ≃* Multiplicative (F × F) :=
    decomp.symm.trans ((eU.prodCongr eV).trans pairMultiplicative)
  have hscalar : ∀ k : K, ∀ x : E,
      (eQ (k • x)).toAdd =
        (((eK k : F) * (eQ x).toAdd.1,
          (eK k : F) * (eQ x).toAdd.2)) := by
    intro k x
    obtain ⟨⟨u, v⟩, rfl⟩ := decomp.surjective x
    have hact :
        k • decomp (u, v) = decomp (k • u, k • v) := by
      change k • ((u : E) * (v : E)) =
        ((k • u : U) : E) * ((k • v : V) : E)
      exact smul_mul' k (u : E) (v : E)
    rw [hact]
    simp only [eQ, MulEquiv.trans_apply, decomp.symm_apply_apply]
    change ((eU (k • u)).toAdd, (eV (k • v)).toAdd) =
      ((eK k : F) * (eU u).toAdd, (eK k : F) * (eV v).toAdd)
    rw [heU_action, heV_action]
  exact ⟨n, hn, eK, eQ, by simpa [F] using hFcard, hscalar⟩
set_option maxHeartbeats 800000 in
/--
Peterfalvi source obligation for Lemma 5's cyclicity and divisibility
conclusion for `W`.

The current interfaces know only the abstract Section 3 setup and an untyped
Higman coordinate classification for `S`; they do not contain Appendix III's
module/action calculation proving that `W` is cyclic and that
`|W| ∣ |Q₀| + 1`.
-/
private theorem lemma_5_W_cyclic_and_divides_obligation
    {G : Type u} {Ω : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion.{u, v} L ΩL)
    (hst : orderOf (s * t) = 3)
    (hQ : IsSuzukiTwoGroup Q)
    (hQ_card : Nat.card Q = Nat.card Q0 ^ 3) :
    IsCyclic W ∧ Nat.card W ∣ Nat.card Q0 + 1 ∧
      (W ≠ ⊥ → IsSuzukiTwoTypeB Q) ∧
      (W ≠ ⊥ → ∃ hKnormQ : K ≤ Subgroup.normalizer (Q : Set G),
        letI : MulDistribMulAction K Q :=
          Subgroup.conjMulDistribMulActionOfLeNormalizer K Q hKnormQ
        Theorem1IsomorphicSummands K Q) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 Q :=
    External.Higman.isPGroup_of_isSuzukiTwoGroup hQ
  obtain ⟨P2, hS_eq⟩ := hsec.section2.S_sylow_in_Q
  have hP2_top : (P2 : Subgroup Q) = ⊤ :=
    (P2.is_maximal' (hQp.to_subgroup (⊤ : Subgroup Q)) le_top).symm
  have hSQ : S = Q := by
    rw [hS_eq, hP2_top]
    ext q
    constructor
    · rintro ⟨q, _hq, rfl⟩
      exact q.property
    · intro hq
      exact ⟨⟨q, hq⟩, trivial, rfl⟩
  letI : (Q.subgroupOf H).Normal := hsec.section2.hA.A1.Q_normal_in_H
  have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hsec.section2.hA.A1.Q_le_H
  have hKnormQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    hsec.section2.K_le_D.trans
      (hsec.section2.hA.A1.D_le_H.trans hHnormQ)
  letI : Subgroup.Normalizes K Q := ⟨hKnormQ⟩
  have hKcyclic : IsCyclic K :=
    (PFchapter1section2.proposition_2
      H D Q K V W Q0 S Q1 t hsec.section2).1
  have hD_faithful_on_Q :
      D ⊓ Subgroup.centralizer (Q : Set G) = ⊥ := by
    have hcore := (PFchapter1section1.proposition_4_c H D Q t s
      hsec.section2.hA.A1 hsec.s_mem_H hsec.s_involution hsec.s_conjugate).1
    rw [← hcore, eq_bot_iff]
    intro x hxCore
    have hfix : ∀ omega : Ω, x • omega = omega := by
      have hxAll : ∀ point : Ω, x ∈ MulAction.stabilizer G point := by
        simpa [pointStabilizerCore] using hxCore
      intro omega
      exact MulAction.mem_stabilizer_iff.mp (hxAll omega)
    have hxOne : x = 1 :=
      (faithfulSMul_iff.mp hsec.section2.hA.A2) x hfix
    simpa [hxOne]
  have hKfaithful : FaithfulSMul K Q := by
    rw [faithfulSMul_iff]
    intro k hkfix
    have hkCentralizer : (k : G) ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hxQ
      let xQ : Q := ⟨x, hxQ⟩
      have hfix := hkfix xQ
      have hconj : (k : G) * x * (k : G)⁻¹ = x := by
        simpa [xQ,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            congrArg (fun z : Q => (z : G)) hfix
      have hmul := congrArg (fun z : G => z * (k : G)) hconj
      simpa [mul_assoc] using hmul.symm
    have hkBot : (k : G) ∈ (⊥ : Subgroup G) := by
      rw [← hD_faithful_on_Q]
      exact ⟨hsec.section2.K_le_D k.property, hkCentralizer⟩
    apply Subtype.ext
    simpa using hkBot
  have hrightConjugateInjective :
      ∀ (x : Q) (hx : IsInvolution x),
        Function.Injective
          (fun k : {a : G // a ∈ peterfalviKSet D t} =>
            (⟨rightConjugateElem (x : G) (k : G),
              ((PFchapter1section1.proposition_3 H D Q t
                  hsec.section2.hA.A1).2
                (x : G) (hsec.section2.hA.A1.Q_le_H x.property)
                ⟨(fun hxOne => hx.ne_one (Subtype.ext hxOne)),
                  congrArg (fun z : Q => (z : G)) hx.sq_eq_one⟩
                (rightConjugateElem (x : G) (k : G))).2
                  ⟨k, k.property, rfl⟩⟩ :
              {y : G // y ∈ H ∧ IsInvolution y})) := by
    intro x hx
    let KSet : Type _ := {a : G // a ∈ peterfalviKSet D t}
    let HInv : Type _ := {y : G // y ∈ H ∧ IsInvolution y}
    have hxG : IsInvolution (x : G) :=
      ⟨(fun hxOne => hx.ne_one (Subtype.ext hxOne)),
        congrArg (fun z : Q => (z : G)) hx.sq_eq_one⟩
    have hxH : (x : G) ∈ H := hsec.section2.hA.A1.Q_le_H x.property
    let phi : KSet → HInv := fun k =>
      ⟨rightConjugateElem (x : G) (k : G),
        ((PFchapter1section1.proposition_3 H D Q t
            hsec.section2.hA.A1).2 (x : G) hxH hxG
          (rightConjugateElem (x : G) (k : G))).2
            ⟨k, k.property, rfl⟩⟩
    have hphiSurjective : Function.Surjective phi := by
      rintro ⟨y, hy⟩
      rcases ((PFchapter1section1.proposition_3 H D Q t
          hsec.section2.hA.A1).2 (x : G) hxH hxG y).1 hy with
        ⟨k, hk, hkEq⟩
      refine ⟨⟨k, hk⟩, ?_⟩
      apply Subtype.ext
      exact hkEq
    have hphiInjective : Function.Injective phi :=
      (hphiSurjective.bijective_of_nat_card_le
        (by simpa [KSet, HInv] using
          le_of_eq (PFchapter1section1.proposition_3 H D Q t
            hsec.section2.hA.A1).1)).1
    simpa [phi, KSet, HInv, hxG, hxH] using hphiInjective
  have hKregular : ActionRegularOn K Q (involutions Q) := by
    constructor
    · intro x hx k
      have hxG : IsInvolution (x : G) :=
        ⟨(fun hxOne => hx.ne_one (Subtype.ext hxOne)),
          congrArg (fun z : Q => (z : G)) hx.sq_eq_one⟩
      have hconj := isInvolution_rightConjugateElem
        (g := ((k⁻¹ : K) : G)) hxG
      constructor
      · intro hOne
        apply hconj.ne_one
        simpa [rightConjugateElem,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            congrArg (fun z : Q => (z : G)) hOne
      · apply Subtype.ext
        simpa [rightConjugateElem,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            hconj.sq_eq_one
    · intro x hx y hy
      have hxG : IsInvolution (x : G) :=
        ⟨(fun hxOne => hx.ne_one (Subtype.ext hxOne)),
          congrArg (fun z : Q => (z : G)) hx.sq_eq_one⟩
      have hyG : IsInvolution (y : G) :=
        ⟨(fun hyOne => hy.ne_one (Subtype.ext hyOne)),
          congrArg (fun z : Q => (z : G)) hy.sq_eq_one⟩
      have hxH : (x : G) ∈ H := hsec.section2.hA.A1.Q_le_H x.property
      rcases ((PFchapter1section1.proposition_3 H D Q t
          hsec.section2.hA.A1).2 (x : G) hxH hxG (y : G)).1
          ⟨hsec.section2.hA.A1.Q_le_H y.property, hyG⟩ with
        ⟨a, haSet, haEq⟩
      have haK : a ∈ K := (hsec.section2.K_def a).mpr haSet
      let k : K := ⟨a⁻¹, K.inv_mem haK⟩
      refine ⟨k, ?_, ?_⟩
      · apply Subtype.ext
        simpa [k, rightConjugateElem,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            haEq.symm
      · intro b hb
        let aSet : {z : G // z ∈ peterfalviKSet D t} := ⟨a, haSet⟩
        let bSet : {z : G // z ∈ peterfalviKSet D t} :=
          ⟨((b⁻¹ : K) : G),
            (hsec.section2.K_def ((b⁻¹ : K) : G)).mp (b⁻¹ : K).property⟩
        have hbRight :
            rightConjugateElem (x : G) (bSet : G) = (y : G) := by
          have hbVal := congrArg (fun z : Q => (z : G)) hb
          simpa [bSet, rightConjugateElem,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
              hbVal.symm
        have hba : bSet = aSet :=
          hrightConjugateInjective x hx
            (by apply Subtype.ext; exact hbRight.trans haEq.symm)
        apply Subtype.ext
        change (b : G) = a⁻¹
        have hval : ((b⁻¹ : K) : G) = a := congrArg Subtype.val hba
        simpa using congrArg Inv.inv hval
  let Q0Q : Subgroup Q := Q0.subgroupOf Q
  have hcenterQ : Subgroup.center Q = Q0Q := by
    ext x
    have hInvCenter := (higmanTheorem_involutions_center hQ).1
    constructor
    · intro hxCenter
      by_cases hxOne : x = 1
      · simpa [Q0Q, hxOne]
      · have hxInv : x ∈ involutions Q := by
          rw [hInvCenter]
          exact ⟨hxCenter, hxOne⟩
        apply (hsec.section2.Q0_def (x : G)).mpr
        exact Or.inr ⟨hsec.section2.hA.A1.Q_le_H x.property,
          ⟨fun h => hxInv.ne_one (Subtype.ext h),
            congrArg (fun z : Q => (z : G)) hxInv.sq_eq_one⟩⟩
    · intro hxQ0
      by_cases hxOne : x = 1
      · simpa [hxOne]
      · have hxQ0G : (x : G) ∈ Q0 := hxQ0
        have hxData := (hsec.section2.Q0_def (x : G)).mp hxQ0G
        have hxInvG : IsInvolution (x : G) := by
          rcases hxData with h | h
          · exact False.elim (hxOne (Subtype.ext h))
          · exact h.2
        have hxInv : x ∈ involutions Q :=
          ⟨fun h => hxInvG.ne_one (congrArg Subtype.val h),
            Subtype.ext hxInvG.sq_eq_one⟩
        rw [hInvCenter] at hxInv
        exact hxInv.1
  have hcenterCard : Nat.card (Subgroup.center Q) = Nat.card Q0 := by
    rw [hcenterQ]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hsec.section2.Q0_le_Q).toEquiv
  have hcube : Nat.card Q = Nat.card (Subgroup.center Q) ^ 3 := by
    rw [hcenterCard]
    exact hQ_card
  rcases higmanTheorem_order_center_cube_two_summands
      hQ hKcyclic hKfaithful hKregular hcube with
    ⟨quotientAction, U, T, hquotientAction,
      hUinv, hTinv, hUcard, hTcard, hUTinf, hUTsup⟩
  let E := Q ⧸ Subgroup.center Q
  letI : IsInvariant K Q (Subgroup.center Q) := center_isInvariant
  let quotientActionK : MulDistribMulAction K E :=
    quotientMulDistribMulAction (A := K) (G := Q) (Subgroup.center Q)
      (inferInstance : IsInvariant K Q (Subgroup.center Q))
  letI : MulDistribMulAction K E := quotientActionK
  have hquotientActionK : ∀ k : K, ∀ x : Q,
      k • QuotientGroup.mk' (Subgroup.center Q) x =
        QuotientGroup.mk' (Subgroup.center Q) (k • x) := by
    intro k x
    exact MulAction.Quotient.smul_mk (H := Subgroup.center Q) k x
  have hquotientActionsEq : ∀ k : K, ∀ x : E,
      @SMul.smul K E quotientAction.toSMul k x = k • x := by
    intro k x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) x
    exact (hquotientAction k y).trans (hquotientActionK k y).symm
  have hUinvK : @IsXInvariantSubgroup K E _ _ quotientActionK U := by
    intro k x
    rw [← hquotientActionsEq k x]
    exact hUinv k x
  have hTinvK : @IsXInvariantSubgroup K E _ _ quotientActionK T := by
    intro k x
    rw [← hquotientActionsEq k x]
    exact hTinv k x
  have hVleD : V ≤ D := by
    intro x hx
    rw [hsec.section2.V_eq] at hx
    exact hx.1
  have hWleD : W ≤ D := hsec.section2.W_le_V.trans hVleD
  have hWnormQ : W ≤ Subgroup.normalizer (Q : Set G) :=
    hWleD.trans (hsec.section2.hA.A1.D_le_H.trans hHnormQ)
  letI : Subgroup.Normalizes W Q := ⟨hWnormQ⟩
  letI : IsInvariant W Q (Subgroup.center Q) := center_isInvariant
  let quotientActionW : MulDistribMulAction W E :=
    quotientMulDistribMulAction (A := W) (G := Q) (Subgroup.center Q)
      (inferInstance : IsInvariant W Q (Subgroup.center Q))
  letI : MulDistribMulAction W E := quotientActionW
  have hquotientActionW : ∀ w : W, ∀ x : Q,
      w • QuotientGroup.mk' (Subgroup.center Q) x =
        QuotientGroup.mk' (Subgroup.center Q) (w • x) := by
    intro w x
    exact MulAction.Quotient.smul_mk (H := Subgroup.center Q) w x
  have hWcentralizer :
      W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) :=
    _root_.CFSG.BenderSuzuki.PFchapter1section2.peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
        H D Q K V W t hsec.section2.hA.A1 hsec.section2.K_def
          hsec.section2.V_eq hsec.section2.W_eq
  have hQ0_le_centralizer :
      ∀ (P : Subgroup G), P ≤ W → Q0 ≤ Subgroup.centralizer (P : Set G) := by
    intro P hPW q hqQ0
    rw [Subgroup.mem_centralizer_iff]
    intro x hxP
    have hxW : x ∈ W := hPW hxP
    have hxCentralizer :
        x ∈ Subgroup.centralizer ({y : G | y ∈ H ∧ IsInvolution y}) := by
      rw [hWcentralizer] at hxW
      exact hxW.2
    rcases (hsec.section2.Q0_def q).mp hqQ0 with hqOne | hqInv
    · subst q
      simp
    · exact ((Subgroup.mem_centralizer_iff.mp hxCentralizer) q hqInv).symm
  obtain ⟨E0, hE0Q0, hE0card, hE0sq⟩ :=
    lemma_5_Q0_order_four_subgroup H D Q K V W Q0 S Q1 t hsec.section2
  have hcentralizerTwoRank :
      ∀ (P : Subgroup G), P ≤ W →
        TwoRankAtLeastTwo (Subgroup.centralizer (P : Set G)) := by
    intro P hPW
    let C := Subgroup.centralizer (P : Set G)
    have hE0C : E0 ≤ C := hE0Q0.trans (hQ0_le_centralizer P hPW)
    let EC : Subgroup C := E0.subgroupOf C
    refine ⟨EC, ?_, ?_⟩
    · simpa [EC] using
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE0C).toEquiv).trans hE0card
    · intro x
      apply Subtype.ext
      apply Subtype.ext
      change ((((x : EC) : C) : G) ^ 2) = 1
      simpa using congrArg Subtype.val
        (hE0sq ((Subgroup.subgroupOfEquivOfLe hE0C) x))
  have hprimeSubgroup :
      ∀ U0 : Subgroup G, U0 ≠ ⊥ →
        ∃ (P : Subgroup G) (p : ℕ),
          P ≤ U0 ∧ Nat.Prime p ∧ Nat.card P = p := by
    intro U0 hU0
    let p := (Nat.card U0).minFac
    have hp : Nat.Prime p :=
      Nat.minFac_prime (U0.one_lt_card_iff_ne_bot.mpr hU0).ne'
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    obtain ⟨x, hx⟩ :=
      exists_prime_orderOf_dvd_card' p (Nat.minFac_dvd (Nat.card U0))
    refine ⟨Subgroup.zpowers (x : G), p,
      Subgroup.zpowers_le.mpr x.property, hp, ?_⟩
    calc
      Nat.card (Subgroup.zpowers (x : G)) = orderOf (x : G) :=
        Nat.card_zpowers (x : G)
      _ = orderOf x := Subgroup.orderOf_coe x
      _ = p := hx
  have hcentralizerPrime :
      ∀ (P : Subgroup G) (p : ℕ) (hPW : P ≤ W), Nat.Prime p →
        Nat.card P = p →
          Subgroup.centralizer (P : Set G) ⊓ Q = Q0 := by
    intro P p hPW hp hPcard
    let CX := Subgroup.centralizer (P : Set G)
    let R := CX ⊓ Q
    have hPne : P ≠ ⊥ := by
      intro hPbot
      have hpOne : p = 1 := by
        rw [← hPcard, hPbot]
        simp
      exact hp.ne_one hpOne
    have hPV : P ≤ V := hPW.trans hsec.section2.W_le_V
    have hprop := PFchapter1section3.proposition_1_c.{u, v}
      H D Q K V W Q0 S Q1 P t s hsec hind hPne hPV
        (hcentralizerTwoRank P hPW)
    dsimp only at hprop
    rcases hprop with
      ⟨_hCXQ1, _hNLF, ell, _hellPower, _hellGt, hellCard, hcases⟩
    have hQ0CX : Q0 ≤ CX := hQ0_le_centralizer P hPW
    have hCXQ0 : CX ⊓ Q0 = Q0 := inf_eq_right.mpr hQ0CX
    have hellQ0 : ell = Nat.card Q0 := by
      simpa [CX, hCXQ0] using hellCard
    have hQ0R : Q0 ≤ R := by
      intro q hq
      exact ⟨hQ0CX hq, hsec.section2.Q0_le_Q hq⟩
    rcases hcases with hlinear | hSuzukiLocal | hunitary
    · rcases hlinear with
        ⟨_k, _hk, _hell, _e, _horder, _hElementary, hRcard⟩
      have hQ0eqR : Q0 = R :=
        Subgroup.eq_of_le_of_card_ge hQ0R (by
          rw [hRcard, hellQ0])
      exact hQ0eqR.symm
    · rcases hSuzukiLocal with
        ⟨_k, _hk, _hell, _e, horderFive, _hTypeA, _hRcard⟩
      exact False.elim (by omega)
    · rcases hunitary with
        ⟨_F, _hField, _hFinite, _J, _hJ, _hFcard, _hFixedCard,
          _e, _horder, _hSuzukiR, hRcard⟩
      have hRcardQ : Nat.card R = Nat.card Q := by
        rw [hRcard.1, hellQ0]
        exact hQ_card.symm
      have hReqQ : R = Q :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq hRcardQ.symm)
      have hPcentralizesQ : P ≤ Subgroup.centralizer (Q : Set G) := by
        intro x hxP
        rw [Subgroup.mem_centralizer_iff]
        intro q hqQ
        have hqR : q ∈ R := by simpa [hReqQ] using hqQ
        exact ((Subgroup.mem_centralizer_iff.mp hqR.1) x hxP).symm
      apply False.elim
      apply hPne
      rw [eq_bot_iff]
      intro x hxP
      rw [← hD_faithful_on_Q]
      exact ⟨hWleD (hPW hxP), hPcentralizesQ hxP⟩
  have hsQ0 : s ∈ Q0 :=
    (hsec.section2.Q0_def s).mpr
      (Or.inr ⟨hsec.s_mem_H, hsec.s_involution⟩)
  let sQ : Q := ⟨s, hsec.section2.Q0_le_Q hsQ0⟩
  have hsQInv : IsInvolution sQ := by
    constructor
    · intro hOne
      exact hsec.s_involution.ne_one (congrArg Subtype.val hOne)
    · apply Subtype.ext
      exact hsec.s_involution.sq_eq_one
  let q := Nat.card (Subgroup.center Q)
  have hKcard : Nat.card K = q - 1 := by
    let Inv : Type u := {x : Q // x ∈ involutions Q}
    let orbit : K → Inv := fun k => ⟨k • sQ, hKregular.1 sQ hsQInv k⟩
    have horbitBij : Function.Bijective orbit := by
      constructor
      · intro k l hkl
        have hval : k • sQ = l • sQ := congrArg Subtype.val hkl
        rcases hKregular.2 sQ hsQInv (k • sQ)
            (hKregular.1 sQ hsQInv k) with ⟨a, _ha, huniq⟩
        exact (huniq k rfl).trans (huniq l hval).symm
      · rintro ⟨x, hx⟩
        rcases hKregular.2 sQ hsQInv x hx with ⟨k, hk, _huniq⟩
        exact ⟨k, Subtype.ext hk.symm⟩
    let orbitEquiv : K ≃ Inv := Equiv.ofBijective orbit horbitBij
    let ZSharp : Type u :=
      {z : Subgroup.center Q // (z : Q) ≠ 1}
    let invCenterEquiv : Inv ≃ ZSharp :=
      { toFun := fun x =>
          ⟨⟨(x : Q), by
            have hx : (x : Q) ∈
                {z : Q | z ∈ Subgroup.center Q ∧ z ≠ 1} := by
              rw [← (higmanTheorem_involutions_center hQ).1]
              exact x.property
            exact hx.1⟩, x.property.ne_one⟩
        invFun := fun z =>
          ⟨(z : Q), by
            rw [(higmanTheorem_involutions_center hQ).1]
            exact ⟨z.1.property, z.property⟩⟩
        left_inv := by intro x; rfl
        right_inv := by intro z; rfl }
    have hZSharpCard : Nat.card ZSharp = q - 1 := by
      letI : Fintype (Subgroup.center Q) := Fintype.ofFinite _
      letI : Fintype {z : Subgroup.center Q // (z : Q) = 1} :=
        Fintype.ofFinite _
      letI : Fintype ZSharp := Fintype.ofFinite ZSharp
      have hsplit := Fintype.card_subtype_compl
        (fun z : Subgroup.center Q => (z : Q) = 1)
      have honeCard :
          Nat.card {z : Subgroup.center Q // (z : Q) = 1} = 1 := by
        let oneEquiv :
            {z : Subgroup.center Q // (z : Q) = 1} ≃ PUnit.{u} :=
          { toFun := fun _ => PUnit.unit
            invFun := fun _ => ⟨1, rfl⟩
            left_inv := by
              intro z
              apply Subtype.ext
              apply Subtype.ext
              exact z.property.symm
            right_inv := by intro z; cases z; rfl }
        simpa using Nat.card_congr oneEquiv
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
        Fintype.card_eq_nat_card, honeCard] at hsplit
      omega
    calc
      Nat.card K = Nat.card Inv := Nat.card_congr orbitEquiv
      _ = Nat.card ZSharp := Nat.card_congr invCenterEquiv
      _ = q - 1 := hZSharpCard
  obtain ⟨nq, hqPow⟩ :=
    (hQp.to_subgroup (Subgroup.center Q)).exists_card_eq
  have hKcomm : IsMulCommutative K := inferInstance
  have hKfixedFree :
      ∀ k : K, k ≠ 1 → ∀ x : E,
        k • x = x → x = 1 := by
    intro k hk x hkx
    by_contra hxOne
    let A : Subgroup K := Subgroup.zpowers k
    letI : MulDistribMulAction A Q := inferInstance
    letI : IsInvariant A Q (Subgroup.center Q) := center_isInvariant
    let quotientActionA : MulDistribMulAction A E :=
      quotientMulDistribMulAction (A := A) (G := Q) (Subgroup.center Q)
        (inferInstance : IsInvariant A Q (Subgroup.center Q))
    letI : MulDistribMulAction A E := quotientActionA
    have hgenAction :
        (⟨k, Subgroup.mem_zpowers k⟩ : A) • x = x := by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) x
      change QuotientGroup.mk' (Subgroup.center Q) (k • y) =
        QuotientGroup.mk' (Subgroup.center Q) y
      rw [← hquotientActionK]
      exact hkx
    have hxFixed : x ∈ fixedPointSubgroup A E := by
      change ∀ a : A, a • x = x
      intro a
      exact smul_eq_self_of_mem_zpowers a.property hgenAction
    have hAcardDvd : Nat.card A ∣ Nat.card K :=
      Subgroup.card_subgroup_dvd_card A
    have hKodd : Odd (Nat.card K) := by
      rw [hKcard]
      dsimp [q]
      rw [hqPow]
      exact Nat.Even.sub_odd (one_le_pow₀ one_le_two)
        (even_two.pow_of_ne_zero (by
        intro hnq
        subst nq
        have hsCenter : sQ ∈ Subgroup.center Q := by
          rw [hcenterQ]
          exact hsQ0
        let z : Subgroup.center Q := ⟨sQ, hsCenter⟩
        have hzNe : z ≠ 1 := by
          intro hz
          exact hsQInv.ne_one (congrArg Subtype.val hz)
        have hnontrivial : Nontrivial (Subgroup.center Q) :=
          ⟨⟨z, 1, hzNe⟩⟩
        have hgt : 1 < Nat.card (Subgroup.center Q) :=
          Finite.one_lt_card_iff_nontrivial.mpr hnontrivial
        have hcardOne : Nat.card (Subgroup.center Q) = 1 := by
          simpa using hqPow
        exact (Nat.ne_of_gt hgt) hcardOne)) odd_one
    have hAodd : Odd (Nat.card A) := hKodd.of_dvd_nat hAcardDvd
    have hQcardPow : ∃ m : ℕ, Nat.card Q = 2 ^ m := by
      rcases hQ.1 with ⟨m, hm⟩
      exact ⟨m, by simpa using hm⟩
    have hcoprime : Nat.Coprime (Nat.card A) (Nat.card Q) := by
      rcases hQcardPow with ⟨m, hm⟩
      rw [hm]
      exact hAodd.coprime_two_right.pow_right m
    letI : Group.IsNilpotent Q := hQp.isNilpotent
    have hQsolvable : Group.IsSolvable Q := by infer_instance
    have hfixedEq :=
      fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
        (G := Q) (A := A) hQsolvable hcoprime (∅ : Set Nat.Primes)
        (Subgroup.center Q) (inferInstance : IsInvariant A Q (Subgroup.center Q))
    have hxMap : x ∈ (fixedPointSubgroup A Q).map
        (QuotientGroup.mk' (Subgroup.center Q)) := by
      rw [← hfixedEq]
      exact hxFixed
    rcases Subgroup.mem_map.mp hxMap with ⟨f, hfFixed, hfx⟩
    let B : Subgroup Q := fixedPointSubgroup A Q
    have hBne : B ≠ ⊥ := by
      intro hBbot
      have hfOne : f = 1 := by
        have : f ∈ (⊥ : Subgroup Q) := by simpa [B, hBbot] using hfFixed
        simpa using this
      apply hxOne
      rw [← hfx, hfOne, map_one]
    have hBInv : IsXInvariantSubgroup K B := by
      have hpreserve : ∀ l : K, ∀ b : Q, b ∈ B → l • b ∈ B := by
        intro l b hb
        change ∀ a : A, a • (l • b) = l • b
        intro a
        have hcomm : (a : K) * l = l * (a : K) :=
          hKcomm.is_comm.comm (a : K) l
        have hab : (a : K) • b = b := by exact hb a
        calc
          a • (l • b) = ((a : K) * l) • b := by
            change (a : K) • (l • b) = ((a : K) * l) • b
            rw [mul_smul]
          _ = (l * (a : K)) • b := by rw [hcomm]
          _ = l • ((a : K) • b) := by rw [mul_smul]
          _ = l • b := by rw [hab]
      intro l b
      constructor
      · exact hpreserve l b
      · intro hlb
        have hback := hpreserve l⁻¹ (l • b) hlb
        simpa [smul_smul] using hback
    have hKtrans : ∀ a : Q, a ∈ involutions Q →
        ∀ b : Q, b ∈ involutions Q → ∃ l : K, b = l • a := by
      intro a ha b hb
      rcases hKregular.2 a ha b hb with ⟨l, hl, _huniq⟩
      exact ⟨l, hl⟩
    have hsB : sQ ∈ B :=
      lemma1_involutions_mem_of_nontrivial_invariant
        hQ hKtrans hBInv hBne sQ hsQInv
    have hks : k • sQ = sQ := by
      have := hsB (⟨k, Subgroup.mem_zpowers k⟩ : A)
      simpa using this
    have hkOne : k = 1 :=
      (hKregular.2 sQ hsQInv sQ hsQInv).unique hks.symm (by simp)
    exact hk hkOne
  have hlineIrreducible :
      ∀ (L A : Subgroup E),
        @IsXInvariantSubgroup K E _ _ quotientActionK L →
        @IsXInvariantSubgroup K E _ _ quotientActionK A →
        Nat.card L = q → A ≤ L → A ≠ ⊥ → A = L := by
    intro L A _hLinv hAinv hLcard hAle hAne
    obtain ⟨a, haOne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
    let orbitWithOne : Option K → A
      | none => 1
      | some k => ⟨k • (a : E), (hAinv k (a : E)).mp a.property⟩
    have horbitInjective : Function.Injective orbitWithOne := by
      intro i j hij
      cases i with
      | none =>
          cases j with
          | none => rfl
          | some l =>
              exfalso
              apply haOne
              apply Subtype.ext
              have hla : l • (a : E) = 1 := congrArg Subtype.val hij.symm
              have hback := congrArg (fun z : E => l⁻¹ • z) hla
              simpa [smul_smul] using hback
      | some k =>
          cases j with
          | none =>
              exfalso
              apply haOne
              apply Subtype.ext
              have hka : k • (a : E) = 1 := congrArg Subtype.val hij
              have hback := congrArg (fun z : E => k⁻¹ • z) hka
              simpa [smul_smul] using hback
          | some l =>
              have hkl : k • (a : E) = l • (a : E) := congrArg Subtype.val hij
              have hfix : (l⁻¹ * k) • (a : E) = (a : E) := by
                calc
                  (l⁻¹ * k) • (a : E) = l⁻¹ • (k • (a : E)) := by rw [mul_smul]
                  _ = l⁻¹ • (l • (a : E)) := by rw [hkl]
                  _ = (a : E) := by simp [smul_smul]
              have hactor : l⁻¹ * k = 1 := by
                by_contra hne
                exact haOne (Subtype.ext (hKfixedFree (l⁻¹ * k) hne (a : E) hfix))
              have hEq : k = l := by
                have := congrArg (fun z : K => l * z) hactor
                simpa [mul_assoc] using this
              exact congrArg some hEq
    have hqLeA : q ≤ Nat.card A := by
      calc
        q = Nat.card K + 1 := by
          have hqPos : 0 < q := Nat.card_pos
          rw [hKcard]
          omega
        _ = Nat.card (Option K) := Finite.card_option.symm
        _ ≤ Nat.card A := Nat.card_le_card_of_injective
          orbitWithOne horbitInjective
    have hAleCard : Nat.card A ≤ Nat.card L :=
      Nat.card_le_card_of_injective
        (fun a : A => (⟨a, hAle a.property⟩ : L))
        (fun x y h => by
          apply Subtype.ext
          change (x : E) = (y : E)
          exact congrArg (fun z : L => (z : E)) h)
    have hAcard : Nat.card A = Nat.card L := by omega
    exact Subgroup.eq_of_le_of_card_ge hAle hAcard.ge
  have hprimeMovesLine :
      ∀ (P : Subgroup G) (p : ℕ) (hPW : P ≤ W), Nat.Prime p →
        Nat.card P = p →
          ∀ (L : Subgroup E),
            @IsXInvariantSubgroup K E _ _ quotientActionK L →
              Nat.card L = q →
                ¬ ∀ c : P, (⟨(c : G), hPW c.property⟩ : W) • L = L := by
    intro P p hPW hp hPcard L hLinv hLcard hPfixL
    let pToW : P →* W := Subgroup.inclusion hPW
    letI : MulDistribMulAction P Q :=
      MulDistribMulAction.compHom Q pToW
    letI : MulDistribMulAction P E :=
      MulDistribMulAction.compHom E pToW
    have hPcentralizesS : P ≤ Subgroup.centralizer ({s} : Set G) := by
      intro c hcP
      have hcW : c ∈ W := hPW hcP
      rw [hWcentralizer] at hcW
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hcW.2) s
        ⟨hsec.s_mem_H, hsec.s_involution⟩).symm
    let qmap : Q →* E := QuotientGroup.mk' (Subgroup.center Q)
    let Plane : Subgroup Q := L.comap qmap
    have hPlaneInv : IsInvariant P Q Plane := by
      refine ⟨?_⟩
      intro c x
      change qmap x ∈ L ↔ qmap (c • x) ∈ L
      have hqmap : qmap (c • x) = pToW c • qmap x := by
        change QuotientGroup.mk' (Subgroup.center Q) (pToW c • x) =
          pToW c • QuotientGroup.mk' (Subgroup.center Q) x
        exact (hquotientActionW (pToW c) x).symm
      rw [hqmap]
      constructor
      · intro hx
        have : pToW c • qmap x ∈ pToW c • L :=
          Subgroup.smul_mem_pointwise_smul (qmap x) (pToW c) L hx
        have hfixL : pToW c • L = L := by
          apply hPfixL c
        rw [hfixL] at this
        exact this
      · intro hx
        have : (pToW c)⁻¹ • (pToW c • qmap x) ∈ (pToW c)⁻¹ • L :=
          Subgroup.smul_mem_pointwise_smul
            (pToW c • qmap x) (pToW c)⁻¹ L hx
        have hfixInv : (pToW c)⁻¹ • L = L := by
          apply hPfixL c⁻¹
        rw [hfixInv] at this
        simpa [smul_smul] using this
    letI : IsInvariant P Q Plane := hPlaneInv
    let Root : SubMulAction P Plane :=
      { carrier := {r : Plane | (r : Q) ^ 2 = sQ}
        smul_mem' := by
          intro c r hr
          change (c • (r : Plane) : Q) ^ 2 = sQ
          rw [← smul_pow', hr]
          apply Subtype.ext
          change (c : G) * s * (c : G)⁻¹ = s
          have hcComm : (c : G) * s = s * (c : G) :=
            Subgroup.mem_centralizer_singleton_iff.mp
              (hPcentralizesS c.property)
          rw [hcComm]
          simp }
    have hRootCard : Nat.card Root = q := by
      have hcard := lemma_5_cubic_line_root_card hQ hKregular hKcard
        quotientActionK hquotientActionK L hLinv hLcard sQ hsQInv
      have hRootEquiv : Root ≃ {r : Plane // (r : Q) ^ 2 = sQ} :=
        { toFun := fun r => ⟨r.1, r.2⟩
          invFun := fun r => ⟨r, r.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have hcardRootEq : Nat.card Root = Nat.card {r : Plane // (r : Q) ^ 2 = sQ} :=
        Nat.card_congr hRootEquiv
      calc
        Nat.card Root = Nat.card {r : Plane // (r : Q) ^ 2 = sQ} := hcardRootEq
        _ = Nat.card (Subgroup.center Q) := hcard
        _ = q := rfl
    have hpDvdD : p ∣ Nat.card D := by
      rw [← hPcard]
      exact Subgroup.card_dvd_of_le (hPW.trans hWleD)
    have hpOdd : Odd p := hsec.section2.hA.A1.D_odd.of_dvd_nat hpDvdD
    have hpNeTwo : p ≠ 2 := by
      intro hpTwo
      exact hpOdd.not_two_dvd_nat (by simpa [hpTwo])
    obtain ⟨n, hqPow⟩ :=
      (hQp.to_subgroup (Subgroup.center Q)).exists_card_eq
    have hpNotDvdRoot : ¬ p ∣ Nat.card Root := by
      rw [hRootCard]
      change ¬ p ∣ Nat.card (Subgroup.center Q)
      rw [hqPow]
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
    have hrCentralizer : (((r : Plane) : Q) : G) ∈
        Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hcP
      let cP : P := ⟨c, hcP⟩
      have hfixPlane : cP • (r : Plane) = (r : Plane) :=
        congrArg Subtype.val (hrFix cP)
      have hfixQ : cP • ((r : Plane) : Q) = ((r : Plane) : Q) := by
        exact congrArg (fun z : Plane => (z : Q)) hfixPlane
      have hfixQW :
          pToW cP • ((r : Plane) : Q) = ((r : Plane) : Q) := by
        exact hfixQ
      have hfixG : c * ((((r : Plane) : Q) : G)) * c⁻¹ =
          (((r : Plane) : Q) : G) := by
        change ((pToW cP : W) : G) * ((((r : Plane) : Q) : G)) *
          ((pToW cP : W) : G)⁻¹ = (((r : Plane) : Q) : G)
        simpa only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
          congrArg (fun z : Q => (z : G)) hfixQW
      have hmul := congrArg (fun z : G => z * c) hfixG
      simpa [mul_assoc] using hmul
    have hrQ0 : (((r : Plane) : Q) : G) ∈ Q0 := by
      rw [← hcentralizerPrime P p hPW hp hPcard]
      exact ⟨hrCentralizer, ((r : Plane) : Q).property⟩
    have hrCenter : ((r : Plane) : Q) ∈ Subgroup.center Q := by
      rw [hcenterQ]
      exact hrQ0
    have hrSqOne : (⟨((r : Plane) : Q), hrCenter⟩ :
        Subgroup.center Q) ^ 2 = 1 :=
      (higmanTheorem_involutions_center hQ).2
        ⟨((r : Plane) : Q), hrCenter⟩
    exact hsec.s_involution.ne_one <| by
      calc
        s = (((r : Plane) : Q) : G) ^ 2 :=
          (congrArg (fun z : Q => (z : G)) r.property).symm
        _ = 1 := congrArg
          (fun z : Subgroup.center Q => (((z : Subgroup.center Q) : Q) : G))
          hrSqOne
  by_cases hWbot : W = ⊥
  · haveI : Subsingleton W := by
      constructor
      intro x y
      apply Subtype.ext
      have hx : (x : G) = 1 := by
        have : (x : G) ∈ (⊥ : Subgroup G) := by simpa [hWbot] using x.property
        simpa using this
      have hy : (y : G) = 1 := by
        have : (y : G) ∈ (⊥ : Subgroup G) := by simpa [hWbot] using y.property
        simpa using this
      rw [hx, hy]
    exact ⟨isCyclic_of_subsingleton, by simp [hWbot],
      by simp [hWbot], by simp [hWbot]⟩
  obtain ⟨P, p, hPW, hp, hPcard⟩ := hprimeSubgroup W hWbot
  let A : Subgroup W := P.subgroupOf W
  have hmoveU := hprimeMovesLine P p hPW hp hPcard U hUinvK hUcard
  push Not at hmoveU
  rcases hmoveU with ⟨c, hcU⟩
  let cW : W := ⟨(c : G), hPW c.property⟩
  have hcWU : cW • U ≠ U := by simpa [cW] using hcU
  have hWKcomm : ∀ w : W, ∀ k : K,
      (w : G) * (k : G) = (k : G) * (w : G) := by
    intro w k
    have hw : (w : G) ∈ peterfalviW V (K : Set G) :=
      (le_of_eq hsec.section2.W_eq) w.property
    have hwK : (w : G) ∈ Subgroup.centralizer (K : Set G) := by
      exact hw.2
    exact ((Subgroup.mem_centralizer_iff.mp hwK) (k : G) k.property).symm
  have hKWsmul : ∀ w : W, ∀ k : K, ∀ x : E,
      k • (w • x) = w • (k • x) := by
    intro w k x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) x
    rw [hquotientActionW, hquotientActionK, hquotientActionK,
      hquotientActionW]
    apply congrArg (QuotientGroup.mk' (Subgroup.center Q))
    apply Subtype.ext
    simp only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    change (k : G) * ((w : G) * (y : G) * (w : G)⁻¹) * (k : G)⁻¹ =
      (w : G) * ((k : G) * (y : G) * (k : G)⁻¹) * (w : G)⁻¹
    calc
      (k : G) * ((w : G) * (y : G) * (w : G)⁻¹) * (k : G)⁻¹ =
          ((k : G) * (w : G)) * (y : G) *
            ((k : G) * (w : G))⁻¹ := by group
      _ = ((w : G) * (k : G)) * (y : G) *
            ((w : G) * (k : G))⁻¹ := by rw [hWKcomm w k]
      _ = (w : G) * ((k : G) * (y : G) * (k : G)⁻¹) * (w : G)⁻¹ := by
        group
  have hWconjInvariant : ∀ w : W, ∀ L : Subgroup E,
      @IsXInvariantSubgroup K E _ _ quotientActionK L →
        @IsXInvariantSubgroup K E _ _ quotientActionK (w • L) := by
    intro w L hLinv
    have hpreserve : ∀ k : K, ∀ x : E, x ∈ w • L → k • x ∈ w • L := by
      intro k x hx
      have hxBack : w⁻¹ • x ∈ w⁻¹ • (w • L) :=
        Subgroup.smul_mem_pointwise_smul x w⁻¹ (w • L) hx
      have hxL : w⁻¹ • x ∈ L := by
        simpa [smul_smul] using hxBack
      have hmem : k • (w⁻¹ • x) ∈ L :=
        (hLinv k (w⁻¹ • x)).mp hxL
      have hforward : w • (k • (w⁻¹ • x)) ∈ w • L :=
        Subgroup.smul_mem_pointwise_smul (k • (w⁻¹ • x)) w L hmem
      have heq : w • (k • (w⁻¹ • x)) = k • x := by
        calc
          w • (k • (w⁻¹ • x)) = k • (w • (w⁻¹ • x)) :=
            (hKWsmul w k (w⁻¹ • x)).symm
          _ = k • x := by simp [smul_smul]
      rw [heq] at hforward
      exact hforward
    intro k x
    constructor
    · exact hpreserve k x
    · intro hkx
      have hback := hpreserve k⁻¹ (k • x) hkx
      simpa [smul_smul] using hback
  have hWconjCard : ∀ w : W, ∀ L : Subgroup E,
      Nat.card (w • L : Subgroup E) = Nat.card L := by
    intro w L
    let e : L ≃ (w • L : Subgroup E) :=
      { toFun := fun x =>
          ⟨w • (x : E),
            Subgroup.smul_mem_pointwise_smul (x : E) w L x.property⟩
        invFun := fun y =>
          ⟨w⁻¹ • (y : E), by
            have hy := Subgroup.smul_mem_pointwise_smul
              (y : E) w⁻¹ (w • L) y.property
            simpa [smul_smul] using hy⟩
        left_inv := by intro x; apply Subtype.ext; simp [smul_smul]
        right_inv := by intro y; apply Subtype.ext; simp [smul_smul] }
    exact Nat.card_congr e.symm
  let Vline : Subgroup E := cW • U
  have hVinv : @IsXInvariantSubgroup K E _ _ quotientActionK Vline :=
    hWconjInvariant cW U hUinvK
  have hVcard : Nat.card Vline = q := by
    rw [show Nat.card Vline = Nat.card U from hWconjCard cW U,
      hUcard]
  have hUVinf : U ⊓ Vline = ⊥ := by
    by_contra hne
    have hInfInv : @IsXInvariantSubgroup K E _ _ quotientActionK (U ⊓ Vline) := by
      intro k x
      simp only [Subgroup.mem_inf]
      exact and_congr (hUinvK k x) (hVinv k x)
    have heq := hlineIrreducible U (U ⊓ Vline) hUinvK hInfInv
      (by simpa [q] using hUcard) inf_le_left hne
    have hUleV : U ≤ Vline := by rw [← heq]; exact inf_le_right
    have hUVeq : U = Vline :=
      Subgroup.eq_of_le_of_card_ge hUleV (by rw [hUcard, hVcard])
    exact hcWU hUVeq.symm
  have hEdata := higmanTheorem_center_quotient_orders_and_exponent hQ
  have hEcomm : IsMulCommutative E := by simpa [E] using hEdata.1
  letI : IsMulCommutative E := hEcomm
  letI : CommGroup E := IsMulCommutative.instCommGroup
  letI : U.Normal := Subgroup.normal_of_isMulCommutative U
  have hUTcompl : U.IsComplement' T := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      simpa using hUTinf
    · rw [Set.eq_univ_iff_forall]
      intro x
      have hx : x ∈ U ⊔ T := by rw [hUTsup]; simp
      rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := U) (t := T)).1 hx with
        ⟨u, hu, v, hv, huv⟩
      exact ⟨u, hu, v, hv, huv⟩
  have hEcard : Nat.card E = q ^ 2 := by
    have hmul := hUTcompl.card_mul
    rw [hUcard, hTcard] at hmul
    simpa [E, q, pow_two] using hmul.symm
  letI : Vline.Normal := Subgroup.normal_of_isMulCommutative Vline
  have hUVcomp : U.IsComplement' Vline :=
    Subgroup.isComplement'_of_card_mul_and_disjoint
      (by rw [hUcard, hVcard, hEcard, pow_two])
      (by rw [disjoint_iff]; simpa using hUVinf)
  have hUVsup : U ⊔ Vline = ⊤ := hUVcomp.sup_eq_top
  let eUV : U ≃* Vline :=
    { toFun := fun x =>
        ⟨cW • (x : E),
          Subgroup.smul_mem_pointwise_smul (x : E) cW U x.property⟩
      invFun := fun y =>
        ⟨cW⁻¹ • (y : E), by
          have hy := Subgroup.smul_mem_pointwise_smul
            (y : E) cW⁻¹ (cW • U) y.property
          simpa [Vline, smul_smul] using hy⟩
      left_inv := by intro x; apply Subtype.ext; simp [smul_smul]
      right_inv := by intro y; apply Subtype.ext; simp [smul_smul]
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact smul_mul' cW (x : E) (y : E) }
  have heUV : ∀ k : K, ∀ u : U,
      ((eUV ⟨k • (u : E), (hUinvK k (u : E)).mp u.property⟩ : Vline) : E) =
        k • ((eUV u : Vline) : E) := by
    intro k u
    exact (hKWsmul cW k (u : E)).symm
  have hIso : Theorem1IsomorphicSummands K Q :=
    ⟨quotientActionK, U, Vline, hUinvK, hVinv, eUV,
      hquotientActionK, hUcard, hVcard, hUVinf, hUVsup, heUV⟩
  have hBtop : IsSuzukiTwoTypeB (⊤ : Subgroup Q) :=
    theorem1_typeB_of_isomorphic_summands
      hQ hKcyclic hKfaithful hKregular hIso
  have htypeB : IsSuzukiTwoTypeB Q := by
    rcases hBtop with
      ⟨n, hn, theta, epsilon, tripleLift, cocycle, hepsilon,
        hperiod, hnonzero, haddLeft, haddRight, hdiag, hmem, hone,
        hsurj, hinj, hmul⟩
    let tripleLiftG : BinaryGaloisField n → BinaryGaloisField n →
        BinaryGaloisField n → G := fun z a b => tripleLift z a b
    refine ⟨n, hn, theta, epsilon, tripleLiftG, cocycle, hepsilon,
      hperiod, hnonzero, haddLeft, haddRight, hdiag, ?_, ?_, ?_, ?_, ?_⟩
    · intro z a b
      exact (tripleLift z a b).property
    · exact congrArg Subtype.val hone
    · intro x hx
      let xQ : Q := ⟨x, hx⟩
      rcases hsurj xQ (by simp) with ⟨z, a, b, hxEq⟩
      exact ⟨z, a, b, congrArg Subtype.val hxEq⟩
    · intro z a b w d e hEq
      apply hinj z a b w d e
      apply Subtype.ext
      exact hEq
    · intro z a b w d e
      exact congrArg Subtype.val (hmul z a b w d e)
  rcases quotient_scalar_coordinates_of_isomorphic_summands
      hEcomm hEdata.2.1 hKcyclic hKfixedFree q hKcard U Vline
      hUinvK hVinv hUcard hVcard hUVinf hUVsup eUV heUV with
    ⟨n, hn, eK, eQ, hFcard, hscalarQuot⟩
  let F := BinaryGaloisField n
  let X := F × F
  let eAdd : X ≃+ Additive E :=
    (MulEquiv.toAdditiveLeft eQ).symm
  let instWAddAction : DistribMulAction W (Additive E) :=
    { smul := fun w x => Additive.ofMul (w • Additive.toMul x)
      one_smul := by
        intro x
        apply Additive.toMul.injective
        change (1 : W) • Additive.toMul x = Additive.toMul x
        exact one_smul W (Additive.toMul x)
      mul_smul := by
        intro a b x
        apply Additive.toMul.injective
        change (a * b) • Additive.toMul x =
          a • (b • Additive.toMul x)
        exact mul_smul a b (Additive.toMul x)
      smul_zero := by
        intro w
        apply Additive.toMul.injective
        change w • (1 : E) = 1
        exact smul_one w
      smul_add := by
        intro w x y
        apply Additive.toMul.injective
        change w • (Additive.toMul x * Additive.toMul y) =
          w • Additive.toMul x * w • Additive.toMul y
        exact smul_mul' w (Additive.toMul x) (Additive.toMul y) }
  letI : DistribMulAction W (Additive E) := instWAddAction
  let instWAction : DistribMulAction W X :=
    { smul := fun w x => eAdd.symm (w • eAdd x)
      one_smul := by
        intro x
        change eAdd.symm ((1 : W) • eAdd x) = x
        rw [one_smul, eAdd.symm_apply_apply]
      mul_smul := by
        intro a b x
        change eAdd.symm ((a * b) • eAdd x) =
          eAdd.symm (a • eAdd (eAdd.symm (b • eAdd x)))
        apply eAdd.injective
        simp [smul_smul]
      smul_zero := by
        intro w
        change eAdd.symm (w • eAdd 0) = 0
        apply eAdd.injective
        simp
      smul_add := by
        intro w x y
        change eAdd.symm (w • eAdd (x + y)) =
          eAdd.symm (w • eAdd x) + eAdd.symm (w • eAdd y)
        apply eAdd.injective
        simp [smul_add] }
  letI : DistribMulAction W X := instWAction
  have hWAction : ∀ w : W, ∀ x : X,
      eAdd (w • x) = Additive.ofMul (w • Additive.toMul (eAdd x)) := by
    intro w x
    change eAdd (eAdd.symm (w • eAdd x)) =
      Additive.ofMul (w • Additive.toMul (eAdd x))
    rw [eAdd.apply_symm_apply]
    rfl

  have hscalarE : ∀ (a : F) (ha : a ≠ 0) (x : X),
      let k : K := eK.symm (Units.mk0 a ha)
      eAdd (a • x) = Additive.ofMul (k • Additive.toMul (eAdd x)) := by
    intro a ha x
    let k : K := eK.symm (Units.mk0 a ha)
    apply Additive.toMul.injective
    apply eQ.injective
    apply Multiplicative.toAdd.injective
    have ha_smul : (a • x : X) = (a * x.1, a * x.2) := by
      calc
        a • (x.1, x.2) = (a • x.1, a • x.2) := rfl
        _ = (a * x.1, a * x.2) := by simp
    have hs := hscalarQuot k (Additive.toMul (eAdd x))
    simpa [eAdd, k, eK.apply_symm_apply, Units.val_mk0, ha_smul, smul_eq_mul] using hs.symm
  have hWscalar : ∀ w : W, ∀ a : F, ∀ x : X,
      w • (a • x) = a • (w • x) := by
    intro w a x
    by_cases ha : a = 0
    · subst a
      simp
    · let k : K := eK.symm (Units.mk0 a ha)
      apply eAdd.injective
      calc
        eAdd (w • (a • x)) =
            Additive.ofMul (w • Additive.toMul (eAdd (a • x))) :=
          hWAction w (a • x)
        _ = Additive.ofMul
            (w • (k • Additive.toMul (eAdd x))) := by
          rw [hscalarE a ha x]
          simp
          rfl
        _ = Additive.ofMul
            (k • (w • Additive.toMul (eAdd x))) := by
          exact congrArg Additive.ofMul
            (hKWsmul w k (Additive.toMul (eAdd x))).symm
        _ = Additive.ofMul
            (k • Additive.toMul (eAdd (w • x))) := by
          rw [hWAction w x]
          simp
        _ = eAdd (a • (w • x)) := (hscalarE a ha (w • x)).symm
  letI : SMulCommClass W F X := ⟨hWscalar⟩
  let rho : Representation F W X :=
    Representation.ofDistribMulAction F W X
  have hdim : Module.finrank F X = 2 := by
    simp [F, X]
  have hWodd : Odd (Nat.card W) := by
    exact hsec.section2.hA.A1.D_odd.of_dvd_nat
      (Subgroup.card_dvd_of_le hWleD)
  have hchar : ringChar F = 2 := by
    exact ringChar.eq F 2
  have hcharNotDvd : ¬ ringChar F ∣ Nat.card W := by
    rw [hchar]
    exact hWodd.not_two_dvd_nat

  let line : ℙ F X → Subgroup E := fun z =>
    z.submodule.toAddSubgroup.toSubgroup.comap eQ.toMonoidHom
  let lineEquiv (z : ℙ F X) : line z ≃ z.submodule :=
    { toFun := fun x => ⟨(eQ x).toAdd, x.property⟩
      invFun := fun y =>
        ⟨eQ.symm (Multiplicative.ofAdd (y : X)), by
          change (eQ (eQ.symm (Multiplicative.ofAdd (y : X)))).toAdd ∈ z.submodule
          simpa using y.property⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro y; apply Subtype.ext; simp }
  have hlineKinv : ∀ z : ℙ F X,
      @IsXInvariantSubgroup K E _ _ quotientActionK (line z) := by
    intro z
    have hpreserve : ∀ k : K, ∀ x : E, x ∈ line z → k • x ∈ line z := by
      intro k x hx
      change (eQ (k • x)).toAdd ∈ z.submodule
      rw [hscalarQuot]
      exact z.submodule.smul_mem (eK k : F) hx
    intro k x
    constructor
    · exact hpreserve k x
    · intro hkx
      have hback := hpreserve k⁻¹ (k • x) hkx
      simpa [smul_smul] using hback
  have hlineCard : ∀ z : ℙ F X, Nat.card (line z) = q := by
    intro z
    calc
      Nat.card (line z) = Nat.card z.submodule :=
        Nat.card_congr (lineEquiv z)
      _ = Nat.card F ^ Module.finrank F z.submodule :=
        Module.natCard_eq_pow_finrank (K := F) (V := z.submodule)
      _ = q := by rw [z.finrank_submodule, pow_one, hFcard]
  have hcoordW : ∀ w : W, ∀ x : E,
      (eQ (w • x)).toAdd = w • (eQ x).toAdd := by
    intro w x
    apply eAdd.injective
    calc
      eAdd (eQ (w • x)).toAdd = Additive.ofMul (w • x) := by
        simp [eAdd]
      _ = eAdd (w • (eQ x).toAdd) := by
        rw [hWAction]
        simp [eAdd]
  have hsubmodule_smul : ∀ w : W, ∀ z : ℙ F X, ∀ x : X,
      x ∈ z.submodule → w • x ∈ (w • z).submodule := by
    intro w z
    induction z using Projectivization.ind with
    | h v hv =>
        intro x hx
        rw [Projectivization.submodule_mk] at hx
        rw [Projectivization.smul_mk, Projectivization.submodule_mk]
        rcases Submodule.mem_span_singleton.mp hx with ⟨a, rfl⟩
        apply Submodule.mem_span_singleton.mpr
        exact ⟨a, (hWscalar w a v).symm⟩
  have hlineFixed : ∀ w : W, ∀ z : ℙ F X, w • z = z →
      w • line z = line z := by
    intro w z hwz
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      change y ∈ w • line z at hy
      rw [Subgroup.pointwise_smul_def] at hy
      rcases hy with ⟨x, hx, rfl⟩
      change (eQ (w • x)).toAdd ∈ z.submodule
      rw [hcoordW]
      rw [← hwz]
      exact hsubmodule_smul w z (eQ x).toAdd hx
    · rw [hWconjCard]
  have hprojectiveStabilizer : ∀ z : ℙ F X,
      MulAction.stabilizer W z = ⊥ := by
    intro z
    by_contra hstab
    let Stab : Subgroup W := MulAction.stabilizer W z
    let StabG : Subgroup G := Stab.map W.subtype
    have hStabGne : StabG ≠ ⊥ := by
      intro hbot
      apply hstab
      rw [eq_bot_iff]
      intro w hw
      have hwMap : (w : G) ∈ StabG := ⟨w, hw, rfl⟩
      rw [hbot] at hwMap
      apply Subtype.ext
      simpa using hwMap
    obtain ⟨P0, p0, hPStab, hp0, hP0card⟩ :=
      hprimeSubgroup StabG hStabGne
    have hP0W : P0 ≤ W := by
      intro g hg
      have hgStab : g ∈ StabG := hPStab hg
      rcases hgStab with ⟨w, _hw, hwg⟩
      simpa [← hwg] using w.property
    have hPfixLine : ∀ c : P0,
        (⟨(c : G), hP0W c.property⟩ : W) • line z = line z := by
      intro c
      let cW0 : W := ⟨(c : G), hP0W c.property⟩
      have hcStabG : (c : G) ∈ StabG := hPStab c.property
      rcases hcStabG with ⟨w, hwStab, hwc⟩
      have hwcW : w = cW0 := by
        apply Subtype.ext
        exact hwc
      have hwFix : w • z = z :=
        MulAction.mem_stabilizer_iff.mp hwStab
      simpa [cW0, hwcW] using hlineFixed w z hwFix
    exact hprimeMovesLine P0 p0 hP0W hp0 hP0card
      (line z) (hlineKinv z) (hlineCard z) hPfixLine
  letI : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).2 hWbot
  have hcycDiv := cyclic_and_card_dvd_of_projective_stabilizers_bot
    hdim hWodd hcharNotDvd hprojectiveStabilizer
  have hqQ0 : q = Nat.card Q0 := hcenterCard
  have hdivQ0 : Nat.card W ∣ Nat.card Q0 + 1 := by
    rw [← hqQ0]
    exact hFcard ▸ hcycDiv.2
  exact ⟨hcycDiv.1, hdivQ0, fun _ => htypeB,
    fun _ => ⟨hKnormQ, hIso⟩⟩


public theorem lemma_5
    {G : Type u} {Ω : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion.{u, v} L ΩL)
    (hst : orderOf (s * t) = 3)
    (hQ : IsSuzukiTwoGroup Q)
    (hQ_card : Nat.card Q = Nat.card Q0 ^ 3) :
    IsCyclic W ∧ Nat.card W ∣ Nat.card Q0 + 1 ∧
      (W ≠ ⊥ → IsSuzukiTwoTypeB Q) := by
  have h := lemma_5_W_cyclic_and_divides_obligation
    H D Q K V W Q0 S Q1 t s hsec hind hst hQ hQ_card
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- The explicit quotient-summand witness constructed in Lemma 5's nontrivial-`W` branch. -/
public theorem lemma_5_isomorphic_summands
    {G : Type u} {Ω : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion.{u, v} L ΩL)
    (hst : orderOf (s * t) = 3)
    (hQ : IsSuzukiTwoGroup Q)
    (hQ_card : Nat.card Q = Nat.card Q0 ^ 3) :
    W ≠ ⊥ → ∃ hKnormQ : K ≤ Subgroup.normalizer (Q : Set G),
      letI : MulDistribMulAction K Q :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer K Q hKnormQ
      Theorem1IsomorphicSummands K Q := by
  exact (lemma_5_W_cyclic_and_divides_obligation
    H D Q K V W Q0 S Q1 t s hsec hind hst hQ hQ_card).2.2.2


end PFchapter1section3
end CFSG.BenderSuzuki
