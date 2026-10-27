module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter3section3.proposition
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.AppendixIInput
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_11
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_5_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_8
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H4_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H4_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H5
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H6_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_15
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 2 Proposition -/

public theorem natCard_eq_cube_of_isSuzukiTwoTypeB
    {G : Type*} [Group G] [Finite G]
    (H Q Q0 S : Subgroup G)
    (hB : IsSuzukiTwoTypeB S) (hSleQ : S ≤ Q) (hQleH : Q ≤ H)
    (hQ0leQ : Q0 ≤ Q)
    (hQ0def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hSQ : S = Q) :
    Nat.card Q = Nat.card Q0 ^ 3 := by
  classical
  rcases hB with ⟨r, hr, theta, epsilon, tripleLift, cocycle, hepsilon,
    hperiod, hnonzero, haddLeft, haddRight, hdiag, hmem, hone,
    hsurj, hinj, hmul⟩
  let R := BinaryGaloisField r
  let liftS : R × R × R → S := fun p ↦
    ⟨tripleLift p.1 p.2.1 p.2.2, hmem p.1 p.2.1 p.2.2⟩
  have hliftS_bijective : Function.Bijective liftS := by
    constructor
    · intro p q hpq
      have hval := congrArg (fun z : S ↦ (z : G)) hpq
      have hcoords := hinj p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 hval
      exact Prod.ext hcoords.1 (Prod.ext hcoords.2.1 hcoords.2.2)
    · intro x
      obtain ⟨c, a, b, hx⟩ := hsurj (x : G) x.property
      exact ⟨(c, a, b), Subtype.ext hx.symm⟩
  let eS : R × R × R ≃ S := Equiv.ofBijective liftS hliftS_bijective
  have hcardS : Nat.card S = Nat.card R ^ 3 := by
    calc
      Nat.card S = Nat.card (R × R × R) := (Nat.card_congr eS).symm
      _ = Nat.card R ^ 3 := by
        rw [Nat.card_prod, Nat.card_prod]
        ring
  have hcocycle_zero : cocycle 0 0 0 0 = 0 := by
    simpa using hdiag 0 0
  have hcentral_mem_Q0 : ∀ c : R, tripleLift c 0 0 ∈ Q0 := by
    intro c
    have hsq : tripleLift c 0 0 ^ 2 = 1 := by
      rw [pow_two, hmul, hcocycle_zero]
      simp only [CharTwo.add_self_eq_zero]
      exact hone
    by_cases hone' : tripleLift c 0 0 = 1
    · exact hone' ▸ Q0.one_mem
    · exact (hQ0def _).2 (Or.inr
        ⟨hQleH (hSleQ (hmem c 0 0)), hone', hsq⟩)
  let liftQ0 : R → Q0 := fun c ↦ ⟨tripleLift c 0 0, hcentral_mem_Q0 c⟩
  have hliftQ0_bijective : Function.Bijective liftQ0 := by
    constructor
    · intro c d hcd
      have hval := congrArg (fun z : Q0 ↦ (z : G)) hcd
      exact (hinj c 0 0 d 0 0 hval).1
    · intro q
      have hqS : (q : G) ∈ S := by
        rw [hSQ]
        exact hQ0leQ q.property
      obtain ⟨c, a, b, hq⟩ := hsurj (q : G) hqS
      have hab : a = 0 ∧ b = 0 := by
        rcases (hQ0def (q : G)).1 q.property with hq_one | ⟨_hqH, hqI⟩
        · have hcoords : c = 0 ∧ a = 0 ∧ b = 0 := by
            apply hinj c a b 0 0 0
            rw [← hq, hq_one, hone]
          exact hcoords.2
        · have hsquare :
              tripleLift c a b * tripleLift c a b = tripleLift 0 0 0 := by
            rw [← pow_two, ← hq, hqI.sq_eq_one, hone]
          have hsquare' :
              tripleLift (c + c + cocycle a b a b) (a + a) (b + b) =
                tripleLift 0 0 0 := by
            rw [← hmul]
            exact hsquare
          have hcoords := hinj _ _ _ 0 0 0 hsquare'
          have hcocycle : cocycle a b a b = 0 := by
            have hc := hcoords.1
            rw [CharTwo.add_self_eq_zero, zero_add] at hc
            exact hc
          have hquad :
              a * theta a + epsilon * a * theta b + b * theta b = 0 := by
            rw [← hdiag]
            exact hcocycle
          by_cases ha : a = 0
          · subst a
            simp only [map_zero, zero_mul, mul_zero, add_zero, zero_add] at hquad
            rcases mul_eq_zero.mp hquad with hb | htb
            · exact ⟨rfl, hb⟩
            · exact ⟨rfl, theta.injective (by simpa using htb)⟩
          · by_cases hb : b = 0
            · subst b
              simp only [map_zero, mul_zero, add_zero] at hquad
              rcases mul_eq_zero.mp hquad with ha' | hta
              · exact ⟨ha', rfl⟩
              · exact ⟨theta.injective (by simpa using hta), rfl⟩
            · exact False.elim (hnonzero a b ha hb hquad)
      refine ⟨c, Subtype.ext ?_⟩
      simpa [liftQ0, hab.1, hab.2] using hq.symm
  let eQ0 : R ≃ Q0 := Equiv.ofBijective liftQ0 hliftQ0_bijective
  have hcardQ0 : Nat.card Q0 = Nat.card R := (Nat.card_congr eQ0).symm
  rw [← hSQ, hcardS, hcardQ0]

private theorem isZGroup_of_fixedPointFree_quotient
    {G : Type*} [Group G] [Finite G]
    (H D Q Q0 : Subgroup G)
    (hDleH : D ≤ H) (hQleH : Q ≤ H)
    (hQnormal : (Q.subgroupOf H).Normal)
    (hQ0leQ : Q0 ≤ Q)
    (hQ0comm : ∀ x : G, x ∈ Q0 → ∀ q : G, q ∈ Q → x * q = q * x)
    (hQ0stable : ∀ d : D, ∀ q : Q0,
      rightConjugateElem (q : G) (d : G)⁻¹ ∈ Q0)
    (hDodd : Odd (Nat.card D))
    (hfixed : ∀ d : G, d ∈ D → d ≠ 1 →
      ∀ x : G, x ∈ Q → x ∉ Q0 →
        rightConjugateElem x d * x⁻¹ ∉ Q0)
    (x0 : G) (hx0Q : x0 ∈ Q) (hx0Q0 : x0 ∉ Q0) :
    IsZGroup D := by
  classical
  have hDnormQ : D ≤ Subgroup.normalizer Q :=
    hDleH.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQleH).1 hQnormal)
  letI : MulDistribMulAction D Q :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) D Q hDnormQ
  let Q0Q : Subgroup Q := Q0.subgroupOf Q
  have hQ0Qnormal : Q0Q.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0leQ).2
    intro q hqQ
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyQ0
      have hcomm := hQ0comm y hyQ0 q hqQ
      have hconj : q * y * q⁻¹ = y := by
        rw [← hcomm]
        simp
      simpa [hconj] using hyQ0
    · intro hyQ0
      have hcomm := hQ0comm (q * y * q⁻¹) hyQ0 q hqQ
      have hy_eq : y = q * y * q⁻¹ := by
        calc
          y = q⁻¹ * (q * y * q⁻¹) * q := by group
          _ = q⁻¹ * ((q * y * q⁻¹) * q) := by rw [mul_assoc]
          _ = q⁻¹ * (q * (q * y * q⁻¹)) := by rw [hcomm]
          _ = q * y * q⁻¹ := by group
      rwa [hy_eq]
  letI : Q0Q.Normal := hQ0Qnormal
  have hQ0Qinv : IsInvariant D Q Q0Q := by
    refine ⟨?_⟩
    have hforward : ∀ (d : D) (q : Q), q ∈ Q0Q → d • q ∈ Q0Q := by
      intro d q hq
      have hstable := hQ0stable d ⟨q, hq⟩
      change (d : G) * (q : G) * (d : G)⁻¹ ∈ Q0
      simpa [rightConjugateElem, mul_assoc] using hstable
    intro d q
    constructor
    · exact hforward d q
    · intro hdq
      have hinv : d⁻¹ • (d • q) ∈ Q0Q := hforward d⁻¹ (d • q) hdq
      simpa using hinv
  letI : MulAction.QuotientAction D Q0Q :=
    quotientAction_of_isInvariant (A := D) (G := Q) Q0Q hQ0Qinv
  letI : MulDistribMulAction D (Q ⧸ Q0Q) :=
    quotientMulDistribMulAction (A := D) (G := Q) Q0Q hQ0Qinv
  let rho : D →* MulAut (Q ⧸ Q0Q) :=
    MulDistribMulAction.toMulAut D (Q ⧸ Q0Q)
  have hfixedRho : ∀ d : D, d ≠ 1 → ∀ qbar : Q ⧸ Q0Q,
      rho d qbar = qbar → qbar = 1 := by
    intro d hd qbar hfix
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective Q0Q qbar
    change (q : Q ⧸ Q0Q) = 1
    rw [QuotientGroup.eq_one_iff]
    by_contra hqQ0
    apply hfixed (d : G)⁻¹ (D.inv_mem d.property)
    · intro hdG
      apply hd
      apply Subtype.ext
      simpa using congrArg Inv.inv hdG
    · exact q.property
    · exact hqQ0
    · have hquot :
          QuotientGroup.mk' Q0Q (d • q) = QuotientGroup.mk' Q0Q q := by
        simpa [rho, MulDistribMulAction.toMulAut_apply] using hfix
      have hdiv : (d • q) / q ∈ Q0Q :=
        (QuotientGroup.eq_iff_div_mem).1 hquot
      have hdivG : (((d • q) / q : Q) : G) ∈ Q0 := hdiv
      have hsmul : ((d • q : Q) : G) =
          (d : G) * (q : G) * (d : G)⁻¹ := by rfl
      simpa only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv,
        hsmul, div_eq_mul_inv, rightConjugateElem, inv_inv, mul_assoc] using hdivG
  have hrho : Function.Injective rho := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro d hdker
    by_contra hd
    let x0Q : Q := ⟨x0, hx0Q⟩
    let x0bar : Q ⧸ Q0Q := QuotientGroup.mk' Q0Q x0Q
    have hrhod : rho d = 1 := MonoidHom.mem_ker.mp hdker
    have hfixx : rho d x0bar = x0bar := by rw [hrhod]; rfl
    have hxone := hfixedRho d hd x0bar hfixx
    apply hx0Q0
    have hxmem : x0Q ∈ Q0Q := (QuotientGroup.eq_one_iff x0Q).1 hxone
    exact hxmem
  let A : Subgroup (MulAut (Q ⧸ Q0Q)) := rho.range
  have hfixedA : ∀ phi : A, phi ≠ 1 → ∀ qbar : Q ⧸ Q0Q,
      (phi : MulAut (Q ⧸ Q0Q)) qbar = qbar → qbar = 1 := by
    intro phi hphi qbar hphi_q
    rcases phi.property with ⟨d, hd⟩
    apply hfixedRho d
    · intro hd_one
      apply hphi
      apply Subtype.ext
      simpa [hd_one] using hd.symm
    · simpa [hd] using hphi_q
  have hclass :=
    BenderSuzuki.External.huppert_V_8_15_fixedPointFree_automorphism_subgroup_classification
      A hfixedA
  let eA : D ≃* A := MonoidHom.ofInjective hrho
  have hAodd : Odd (Nat.card A) := by
    simpa only [Nat.card_congr eA.toEquiv] using hDodd
  have hZA : IsZGroup A := by
    refine ⟨?_⟩
    intro p hp P
    letI : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p = 2
    · subst p
      have hPodd : Odd (Nat.card P) :=
        Odd.of_dvd_nat hAodd P.card_subgroup_dvd_card
      obtain ⟨k, hk⟩ := P.2.exists_card_eq
      have hk0 : k = 0 := by
        by_contra hk0
        apply hPodd.not_two_dvd_nat
        rw [hk]
        exact dvd_pow_self 2 hk0
      have hPcard : Nat.card P = 1 := by simp [hk, hk0]
      exact @isCyclic_of_subsingleton P _
        (Nat.card_eq_one_iff_unique.mp hPcard).1
    · exact hclass.1 p hp2 P
  letI : IsZGroup A := hZA
  exact IsZGroup.of_injective (f := eA.toMonoidHom) eA.injective

set_option maxHeartbeats 1000000 in
/-- If `D` acts without fixed points on `(Q / Q0)#`, one of the normalized
`KW`-orbit representatives has the form asserted in the source proposition.

The choices follow `docs/PFchapter4.tex` in their source order.  Before Claim
(8), `omega 1, ..., omega n` are chosen to represent the `KW`-orbits on
`(Q / Q0)#`.  Immediately before Claim (9), `zeta` is chosen as a generator
of `W`; (C2) gives `zeta != 1`.  Claim (9) then replaces each `omega i` by an
element in the same `KW`-orbit so that
`f (omega i) = (omega i * y_i) ^ zeta` for some `y_i in Q0#`.
Consequently `horbit_representatives` and `hnormalized` describe the final
normalized family, rather than two independent choices or a condition on the
original arbitrary representatives.

The source has already proved Theorem C before introducing (C2), so `Q` is
a `2`-group.  The proof derives that its chosen Sylow `2`-subgroup `S` is all
of `Q`; this is what permits use of the Chapter III, Section 3 coordinate
model. -/
public theorem proposition
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s zeta : G) (f g h : G → G)
    (omega : ℕ → G) (n : ℕ)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (hC3 : TypeBChapter3Data G K Q0 S W s)
    (hQ_two : IsPGroup 2 Q)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W)
    (hzeta : zeta ∈ W) (hzeta_ne : zeta ≠ 1)
    (hzeta_gen : Subgroup.closure ({zeta} : Set G) = W)
    (horbit_representatives :
      (∀ j : ℕ, 1 ≤ j → j ≤ n → omega j ∈ Q ∧ omega j ∉ Q0) ∧
      (∀ x : G, x ∈ Q → x ∉ Q0 →
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧
          ∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
            x = rightConjugateElem (omega j) d * q0) ∧
      (∀ j k : ℕ, 1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
        (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
          omega j = rightConjugateElem (omega k) d * q0) → j = k))
    (hnormalized : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∃ y : G, y ∈ Q0 ∧ y ≠ 1 ∧
        f (omega i) = rightConjugateElem (omega i * y) zeta)
    (hD_fixed_point_free : ∀ d : G, d ∈ D → d ≠ 1 →
      ∀ x : G, x ∈ Q → x ∉ Q0 → rightConjugateElem x d * x⁻¹ ∉ Q0) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧
      f (omega i) = rightConjugateElem (omega i)⁻¹ zeta ∧ h (omega i) ∈ W := by
  classical
  have hsec := hsection3.1
  have hQ0_commutes_Q : ∀ x : G, x ∈ Q0 → ∀ q : G, q ∈ Q → x * q = q * x :=
    Q0_commutes_Q H D Q K V W Q0 S Q1 t s hsection3 hC2
  obtain ⟨P, hS_eq⟩ := hsec.S_sylow_in_Q
  have hP_top : (P : Subgroup Q) = ⊤ :=
    (P.is_maximal' (hQ_two.to_subgroup ⊤) le_top).symm
  have hSQ : S = Q := by
    rw [hS_eq, hP_top]
    ext q
    constructor
    · rintro ⟨q, _hq, rfl⟩
      exact q.property
    · intro hq
      exact ⟨⟨q, hq⟩, trivial, rfl⟩
  obtain ⟨x, hxQ, hx_not_Q0⟩ :=
    PFchapter4section2.IsSuzukiTwoTypeB.exists_mem_Q_not_mem_Q0
      H Q Q0 S hC2.S_type_B
      hsec.S_le_Q hsec.Q0_def
  obtain ⟨i₀, hi₀_one, hi₀_n, _d₀, _q₀, _hd₀, _hq₀, _hx_orbit⟩ :=
    horbit_representatives.2.1 x hxQ hx_not_Q0
  have hn_pos : 0 < n := Nat.zero_lt_one.trans_le (hi₀_one.trans hi₀_n)
  have homega_sq : ∀ i : ℕ, 1 ≤ i → i ≤ n → omega i ^ 2 ∈ Q0 := by
    intro i hi_one hi_n
    have homega_S : omega i ∈ S := by
      simpa [hSQ] using (horbit_representatives.1 i hi_one hi_n).1
    exact PFchapter4section2.IsSuzukiTwoTypeB.square_mem_Q0
      H Q Q0 S hC2.S_type_B hsec.S_le_Q hsec.hA.A1.Q_le_H
        hsec.Q0_def (omega i) homega_S
  rcases hC3 with
    ⟨E, hEField, hEFinite, hEChar, F, theta, sigma, phi,
      K1, W1, S1, hS1Group, coord, rho, rho1, sIso, kwIso, modelIso,
      hfinrank, hcardF, hthetaOdd, hsigmaF, hsigmaFrob, hK1, hW1ne,
      hW1norm, hW1inv, hphiThetaOne, hphiThetaNe, hcoordMul, hrho,
      hrho1, hmodelS, hmodelKW, hmapK, hmapW, hsCoord⟩
  letI : Field E := hEField
  letI : Finite E := hEFinite
  letI : CharP E 2 := hEChar
  letI : Group S1 := hS1Group
  have hphi_zero_left : ∀ x : E, phi 0 x = 0 := by
    intro x
    by_cases htheta : theta = 1
    · rw [hphiThetaOne htheta]
      simp
    · have hzero := (hphiThetaNe htheta).2.1 0 0 x
      simpa using hzero
  have hphi_zero_right : ∀ x : E, phi x 0 = 0 := by
    intro x
    by_cases htheta : theta = 1
    · rw [hphiThetaOne htheta]
      simp
    · have hzero := (hphiThetaNe htheta).2.2.1 x 0 0
      simpa using hzero
  have hcoord_one :
      ((coord (1 : S1) :
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) = (0, 0) := by
    let p : E × E :=
      ((coord (1 : S1) :
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E)
    have hp := hcoordMul (1 : S1) 1
    have hp_eq : p =
        (p.1 + p.1, p.2 + p.2 + phi p.1 p.1) := by
      simpa [p] using hp
    have hp_one : p.1 = 0 := by
      have hfirst := congrArg Prod.fst hp_eq
      simpa using hfirst
    have hp_two : p.2 = 0 := by
      have hsecond := congrArg Prod.snd hp_eq
      rw [hp_one, hphi_zero_left] at hsecond
      simpa using hsecond
    exact Prod.ext hp_one hp_two
  have hsIso_rho : ∀ (a : (K ⊔ W : Subgroup G)) (x : S),
      sIso (rho a x) = rho1 (kwIso a) (sIso x) := by
    intro a x
    apply (SemidirectProduct.inl_injective (φ := rho1))
    calc
      SemidirectProduct.inl (sIso (rho a x)) =
          modelIso (SemidirectProduct.inl (rho a x)) :=
        (hmodelS (rho a x)).symm
      _ = modelIso
          (SemidirectProduct.inr a * SemidirectProduct.inl x *
            SemidirectProduct.inr a⁻¹) := by
        rw [← SemidirectProduct.inl_aut]
      _ = modelIso (SemidirectProduct.inr a) *
          modelIso (SemidirectProduct.inl x) *
            modelIso (SemidirectProduct.inr a⁻¹) := by
        rw [map_mul, map_mul]
      _ = SemidirectProduct.inr (kwIso a) *
          SemidirectProduct.inl (sIso x) *
            SemidirectProduct.inr (kwIso a)⁻¹ := by
        rw [hmodelKW a, hmodelS x, hmodelKW a⁻¹, map_inv]
      _ = SemidirectProduct.inl (rho1 (kwIso a) (sIso x)) :=
        (SemidirectProduct.inl_aut (kwIso a) (sIso x)).symm
  let centerCoord (u : F) :
      {p : E × E //
        (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
          (theta ≠ 1 ∧ p.2 ∈ F)} :=
    ⟨(0, (u : E)), by
      by_cases htheta : theta = 1
      · left
        refine ⟨htheta, ?_⟩
        rw [hsigmaF]
        rw [htheta]
        simpa using CharTwo.add_self_eq_zero (u : E)
      · exact Or.inr ⟨htheta, u.property⟩⟩
  let centerS (u : F) : S := sIso.symm (coord.symm (centerCoord u))
  let center (u : F) : G := (centerS u : G)
  have hcenter_coord : ∀ u : F,
      ((coord (sIso (centerS u)) :
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) = (0, (u : E)) := by
    intro u
    simp [centerS, centerCoord]
  have hcenterS_zero : centerS 0 = 1 := by
    apply sIso.injective
    apply coord.injective
    apply Subtype.ext
    simpa [centerS, centerCoord] using hcoord_one.symm
  have hcenter_zero : center 0 = 1 := by
    exact congrArg Subtype.val hcenterS_zero
  have hcenterS_add : ∀ u v : F, centerS (u + v) = centerS u * centerS v := by
    intro u v
    apply sIso.injective
    rw [map_mul]
    apply coord.injective
    apply Subtype.ext
    rw [hcoordMul]
    simp [hcenter_coord, hphi_zero_left]
  have hcenter_add : ∀ u v : F, center (u + v) = center u * center v := by
    intro u v
    exact congrArg Subtype.val (hcenterS_add u v)
  have hcenter_sq : ∀ u : F, center u ^ 2 = 1 := by
    intro u
    rw [pow_two, ← hcenter_add, CharTwo.add_self_eq_zero, hcenter_zero]
  have hcenter_mem_Q0 : ∀ u : F, center u ∈ Q0 := by
    intro u
    by_cases hcenter_one : center u = 1
    · simp [hcenter_one, Q0.one_mem]
    · apply (hsec.Q0_def (center u)).2
      refine Or.inr ⟨?_, hcenter_one, hcenter_sq u⟩
      apply hsec.hA.A1.Q_le_H
      simpa [hSQ, center] using (centerS u).property
  have hcenter_injective : Function.Injective center := by
    intro u v huv
    apply Subtype.ext
    have huvS : centerS u = centerS v := Subtype.ext huv
    have hcoords := congrArg
      (fun x : S =>
        ((coord (sIso x) :
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E)) huvS
    have hsecond := congrArg Prod.snd hcoords
    simpa [hcenter_coord] using hsecond
  let centerToQ0 : F → Q0 := fun u => ⟨center u, hcenter_mem_Q0 u⟩
  have hcenterToQ0_injective : Function.Injective centerToQ0 := by
    intro u v huv
    apply hcenter_injective
    exact congrArg (fun q : Q0 => (q : G)) huv
  have hcenterToQ0_bijective : Function.Bijective centerToQ0 :=
    hcenterToQ0_injective.bijective_of_nat_card_le (by rw [hcardF])
  have hcenter_surjective : ∀ y : G, y ∈ Q0 → ∃ u : F, center u = y := by
    intro y hy
    obtain ⟨u, hu⟩ := hcenterToQ0_bijective.2 ⟨y, hy⟩
    exact ⟨u, congrArg Subtype.val hu⟩
  let conjS (x : S) (a : (K ⊔ W : Subgroup G)) : S := rho a⁻¹ x
  have hconjS_coe : ∀ (x : S) (a : (K ⊔ W : Subgroup G)),
      ((conjS x a : S) : G) = rightConjugateElem (x : G) (a : G) := by
    intro x a
    simpa [conjS, rightConjugateElem] using hrho a⁻¹ x
  have hconjS_coord : ∀ (x : S) (a : (K ⊔ W : Subgroup G)),
      ((coord (sIso (conjS x a)) :
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) =
        (((((kwIso a : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E)) *
            ((coord (sIso x) :
              {p : E × E //
                (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
                  (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E).1,
          ((((kwIso a : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E)) *
            sigma ((((kwIso a : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E)) *
              ((coord (sIso x) :
                {p : E × E //
                  (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
                    (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E).2) := by
    intro x a
    change
      ((coord (sIso (rho a⁻¹ x)) :
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) = _
    rw [hsIso_rho]
    simpa using hrho1 (kwIso a) (sIso x)
  have hkwIso_mem_K1 : ∀ (a : G), ∀ ha : a ∈ K,
      (((kwIso (⟨a, Subgroup.mem_sup_left ha⟩ : (K ⊔ W : Subgroup G)) :
          (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) ∈ K1) := by
    intro a ha
    let aKW : (K ⊔ W : Subgroup G) := ⟨a, Subgroup.mem_sup_left ha⟩
    have ha_sub : aKW ∈ K.subgroupOf (K ⊔ W) := ha
    have ha_map : kwIso aKW ∈
        Subgroup.map kwIso.toMonoidHom (K.subgroupOf (K ⊔ W)) :=
      ⟨aKW, ha_sub, rfl⟩
    rw [hmapK] at ha_map
    exact ha_map
  have hkwIso_mem_W1 : ∀ (a : G), ∀ ha : a ∈ W,
      (((kwIso (⟨a, Subgroup.mem_sup_right ha⟩ : (K ⊔ W : Subgroup G)) :
          (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) ∈ W1) := by
    intro a ha
    let aKW : (K ⊔ W : Subgroup G) := ⟨a, Subgroup.mem_sup_right ha⟩
    have ha_sub : aKW ∈ W.subgroupOf (K ⊔ W) := ha
    have ha_map : kwIso aKW ∈
        Subgroup.map kwIso.toMonoidHom (W.subgroupOf (K ⊔ W)) :=
      ⟨aKW, ha_sub, rfl⟩
    rw [hmapW] at ha_map
    exact ha_map
  have hK_scalar : ∀ (a : G), ∀ ha : a ∈ K,
      ∃ b : Fˣ,
        (((kwIso (⟨a, Subgroup.mem_sup_left ha⟩ : (K ⊔ W : Subgroup G)) :
          (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) = ((b : F) : E) := by
    intro a ha
    exact (hK1 _).1 (hkwIso_mem_K1 a ha)
  have hK_of_scalar : ∀ b : Fˣ,
      ∃ a : G, ∃ ha : a ∈ K,
        (((kwIso (⟨a, Subgroup.mem_sup_left ha⟩ : (K ⊔ W : Subgroup G)) :
          (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) = ((b : F) : E) := by
    intro b
    let bE : Eˣ := Units.map F.subtype.toMonoidHom b
    have hbE_K1 : bE ∈ K1 := by
      apply (hK1 bE).2
      refine ⟨b, ?_⟩
      simp [bE]
    let bKW : (K1 ⊔ W1 : Subgroup Eˣ) :=
      ⟨bE, Subgroup.mem_sup_left hbE_K1⟩
    have hb_sub : bKW ∈ K1.subgroupOf (K1 ⊔ W1) := hbE_K1
    rw [← hmapK] at hb_sub
    obtain ⟨aKW, haK, ha_image⟩ := hb_sub
    refine ⟨(aKW : G), haK, ?_⟩
    have haKW_eq :
        (⟨(aKW : G), Subgroup.mem_sup_left haK⟩ : (K ⊔ W : Subgroup G)) =
          aKW := Subtype.ext rfl
    rw [haKW_eq]
    have himage := congrArg
      (fun z : (K1 ⊔ W1 : Subgroup Eˣ) => (((z : Eˣ) : E))) ha_image
    simpa [bKW, bE] using himage
  let kOf (b : Fˣ) : G := Classical.choose (hK_of_scalar b)
  have hkOf_mem : ∀ b : Fˣ, kOf b ∈ K := by
    intro b
    exact Classical.choose (Classical.choose_spec (hK_of_scalar b))
  have hkOf_coord : ∀ b : Fˣ,
      (((kwIso (⟨kOf b, Subgroup.mem_sup_left (hkOf_mem b)⟩ :
          (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
        ((b : F) : E) := by
    intro b
    exact Classical.choose_spec (Classical.choose_spec (hK_of_scalar b))
  have hkOf_mul : ∀ b c : Fˣ, kOf (b * c) = kOf b * kOf c := by
    intro b c
    let bcKW : (K ⊔ W : Subgroup G) :=
      ⟨kOf (b * c), Subgroup.mem_sup_left (hkOf_mem (b * c))⟩
    let prodKW : (K ⊔ W : Subgroup G) :=
      ⟨kOf b * kOf c,
        Subgroup.mul_mem _ (Subgroup.mem_sup_left (hkOf_mem b))
          (Subgroup.mem_sup_left (hkOf_mem c))⟩
    have himage : kwIso bcKW = kwIso prodKW := by
      apply Subtype.ext
      apply Units.ext
      rw [show prodKW =
          (⟨kOf b, Subgroup.mem_sup_left (hkOf_mem b)⟩ :
              (K ⊔ W : Subgroup G)) *
            ⟨kOf c, Subgroup.mem_sup_left (hkOf_mem c)⟩ from Subtype.ext rfl,
        map_mul]
      rw [show bcKW =
          ⟨kOf (b * c), Subgroup.mem_sup_left (hkOf_mem (b * c))⟩ from rfl]
      change
        (((kwIso
            (⟨kOf (b * c), Subgroup.mem_sup_left (hkOf_mem (b * c))⟩ :
              (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
          (((kwIso
            (⟨kOf b, Subgroup.mem_sup_left (hkOf_mem b)⟩ :
              (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) *
          (((kwIso
            (⟨kOf c, Subgroup.mem_sup_left (hkOf_mem c)⟩ :
              (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E)
      rw [hkOf_coord, hkOf_coord, hkOf_coord]
      rfl
    have hsub : bcKW = prodKW := kwIso.injective himage
    exact congrArg Subtype.val hsub
  have hkOf_one : kOf 1 = 1 := by
    have hmul := hkOf_mul 1 1
    apply mul_left_cancel (a := kOf 1)
    simpa using hmul.symm
  have hkOf_inv : ∀ b : Fˣ, kOf b⁻¹ = (kOf b)⁻¹ := by
    intro b
    apply eq_inv_of_mul_eq_one_right
    rw [← hkOf_mul]
    simp [hkOf_one]
  let normEquiv : F ≃ F :=
    Equiv.ofBijective (fun x : F => x * theta x)
      (norm_bijective_of_odd_order theta hthetaOdd)
  let tau : F → F := normEquiv.symm
  have htau_norm : ∀ a : F, tau (a * theta a) = a := by
    intro a
    exact normEquiv.symm_apply_apply a
  have hnorm_tau : ∀ x : F, tau x * theta (tau x) = x := by
    intro x
    exact normEquiv.apply_symm_apply x
  have htau_zero : tau 0 = 0 := by
    apply (norm_bijective_of_odd_order theta hthetaOdd).1
    simpa using hnorm_tau 0
  have htau_one : tau 1 = 1 := by
    apply (norm_bijective_of_odd_order theta hthetaOdd).1
    simpa using hnorm_tau 1
  have htau_mul : ∀ x y : F, tau (x * y) = tau x * tau y := by
    intro x y
    apply (norm_bijective_of_odd_order theta hthetaOdd).1
    change
      tau (x * y) * theta (tau (x * y)) =
        (tau x * tau y) * theta (tau x * tau y)
    calc
      tau (x * y) * theta (tau (x * y)) = x * y := hnorm_tau (x * y)
      _ = (tau x * theta (tau x)) * (tau y * theta (tau y)) := by
        rw [hnorm_tau x, hnorm_tau y]
      _ = (tau x * tau y) * theta (tau x * tau y) := by
        rw [map_mul]
        ring
  have htau_ne_zero : ∀ x : F, x ≠ 0 → tau x ≠ 0 := by
    intro x hx hzero
    apply hx
    rw [← hnorm_tau x, hzero]
    simp
  have htau_inv : ∀ x : F, tau x⁻¹ = (tau x)⁻¹ := by
    intro x
    by_cases hx : x = 0
    · simp [hx, htau_zero]
    · apply eq_inv_of_mul_eq_one_right
      rw [← htau_mul, mul_inv_cancel₀ hx, htau_one]
  have hcenter_conj_K_exact : ∀ (a : G), ∀ ha : a ∈ K, ∀ (b : Fˣ),
      (((kwIso (⟨a, Subgroup.mem_sup_left ha⟩ : (K ⊔ W : Subgroup G)) :
          (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) = ((b : F) : E) →
      ∀ u : F, rightConjugateElem (center u) a =
        center ((b : F) * theta (b : F) * u) := by
    intro a ha b hb u
    let aKW : (K ⊔ W : Subgroup G) := ⟨a, Subgroup.mem_sup_left ha⟩
    have hsub : conjS (centerS u) aKW =
        centerS ((b : F) * theta (b : F) * u) := by
      apply sIso.injective
      apply coord.injective
      apply Subtype.ext
      rw [hconjS_coord, hcenter_coord, hcenter_coord]
      change
        (((((kwIso aKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E)) * 0,
          ((((kwIso aKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E)) *
            sigma ((((kwIso aKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E)) *
              (u : E)) =
        (0, (((b : F) * theta (b : F) * u : F) : E))
      rw [hb, hsigmaF]
      simp
    calc
      rightConjugateElem (center u) a =
          ((conjS (centerS u) aKW : S) : G) := by
        rw [hconjS_coe]
      _ = center ((b : F) * theta (b : F) * u) :=
        congrArg Subtype.val hsub
  have hcenter_conj_K : ∀ (a : G), ∀ ha : a ∈ K, ∀ u : F,
      ∃ b : Fˣ, rightConjugateElem (center u) a =
        center ((b : F) * theta (b : F) * u) := by
    intro a ha u
    obtain ⟨b, hb⟩ := hK_scalar a ha
    exact ⟨b, hcenter_conj_K_exact a ha b hb u⟩
  have hcenter_conj_W : ∀ (a : G), a ∈ W → ∀ u : F,
      rightConjugateElem (center u) a = center u := by
    intro a ha u
    let aKW : (K ⊔ W : Subgroup G) := ⟨a, Subgroup.mem_sup_right ha⟩
    let aUnit : Eˣ :=
      ((kwIso aKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ)
    have haUnit_W1 : aUnit ∈ W1 := hkwIso_mem_W1 a ha
    have ha_sigma : sigma (aUnit : E) = (aUnit : E)⁻¹ :=
      hW1inv aUnit haUnit_W1
    have hsub : conjS (centerS u) aKW = centerS u := by
      apply sIso.injective
      apply coord.injective
      apply Subtype.ext
      rw [hconjS_coord, hcenter_coord]
      change
        (((aUnit : E) * 0),
          (aUnit : E) * sigma (aUnit : E) * (u : E)) = (0, (u : E))
      rw [ha_sigma]
      simp
    calc
      rightConjugateElem (center u) a =
          ((conjS (centerS u) aKW : S) : G) := by
        rw [hconjS_coe]
      _ = center u := congrArg Subtype.val hsub
  have hKW_commute : ∀ (a b : G), a ∈ K ⊔ W → b ∈ K ⊔ W → Commute a b := by
    intro a b ha hb
    let aKW : (K ⊔ W : Subgroup G) := ⟨a, ha⟩
    let bKW : (K ⊔ W : Subgroup G) := ⟨b, hb⟩
    have hsub : Commute aKW bKW := by
      rw [Commute]
      apply kwIso.injective
      simpa only [map_mul] using mul_comm (kwIso aKW) (kwIso bKW)
    exact congrArg Subtype.val hsub.eq
  obtain ⟨hsS, hs_coord⟩ := hsCoord
  have hs_centerS : (⟨s, hsS⟩ : S) = centerS 1 := by
    apply sIso.injective
    apply coord.injective
    apply Subtype.ext
    rw [hs_coord, hcenter_coord]
    simp
  have hs_center : s = center 1 := by
    exact congrArg Subtype.val hs_centerS
  let ValidIndex := {i : ℕ // 1 ≤ i ∧ i ≤ n}
  let omegaAt (i : ValidIndex) (u : F) : G := omega (i : ℕ) * center u
  have homega_valid : ∀ i : ValidIndex, omega (i : ℕ) ∈ Q ∧ omega (i : ℕ) ∉ Q0 := by
    intro i
    exact horbit_representatives.1 i i.property.1 i.property.2
  have hnormalized_valid : ∀ i : ValidIndex,
      ∃ y : G, y ∈ Q0 ∧ y ≠ 1 ∧
        f (omega (i : ℕ)) = rightConjugateElem (omega (i : ℕ) * y) zeta := by
    intro i
    exact hnormalized i i.property.1 i.property.2
  let yOf (i : ValidIndex) : G := Classical.choose (hnormalized_valid i)
  have hyOf_mem : ∀ i : ValidIndex, yOf i ∈ Q0 := by
    intro i
    exact (Classical.choose_spec (hnormalized_valid i)).1
  have hyOf_ne : ∀ i : ValidIndex, yOf i ≠ 1 := by
    intro i
    exact (Classical.choose_spec (hnormalized_valid i)).2.1
  have hfomega_valid : ∀ i : ValidIndex,
      f (omega (i : ℕ)) =
        rightConjugateElem (omega (i : ℕ) * yOf i) zeta := by
    intro i
    exact (Classical.choose_spec (hnormalized_valid i)).2.2
  have halpha_exists : ∀ i : ValidIndex, ∃ alpha : F, center alpha = yOf i := by
    intro i
    exact hcenter_surjective (yOf i) (hyOf_mem i)
  let alphaOf (i : ValidIndex) : F := Classical.choose (halpha_exists i)
  have hyOf_eq : ∀ i : ValidIndex, center (alphaOf i) = yOf i := by
    intro i
    exact Classical.choose_spec (halpha_exists i)
  have halpha_ne : ∀ i : ValidIndex, alphaOf i ≠ 0 := by
    intro i halpha
    apply hyOf_ne i
    rw [← hyOf_eq i, halpha, hcenter_zero]
  have hfomega_alpha : ∀ i : ValidIndex,
      f (omega (i : ℕ)) =
        rightConjugateElem (omegaAt i (alphaOf i)) zeta := by
    intro i
    simpa [omegaAt, hyOf_eq i] using hfomega_valid i
  let uSeq (i : ValidIndex) : ℕ → F :=
    Classical.choose (claim_11 F (1 : F) (alphaOf i) theta tau)
  let vSeq (i : ValidIndex) : ℕ → F :=
    Classical.choose
      (Classical.choose_spec (claim_11 F (1 : F) (alphaOf i) theta tau))
  let cSeq (i : ValidIndex) : ℕ → F :=
    Classical.choose
      (Classical.choose_spec
        (Classical.choose_spec (claim_11 F (1 : F) (alphaOf i) theta tau)))
  have hseq : ∀ i : ValidIndex,
      uSeq i 1 = 0 ∧ vSeq i 1 = alphaOf i ∧ cSeq i 1 = 1 ∧
      (∀ j : ℕ, uSeq i j ≠ alphaOf i →
        uSeq i (j + 1) = (alphaOf i + uSeq i j)⁻¹) ∧
      (∀ j : ℕ, uSeq i j ≠ alphaOf i →
        vSeq i (j + 1) = vSeq i j +
          uSeq i (j + 1) * (cSeq i j * theta (cSeq i j))⁻¹) ∧
      (∀ j : ℕ, uSeq i j ≠ alphaOf i →
        cSeq i (j + 1) = cSeq i j *
          tau ((uSeq i (j + 1))⁻¹ ^ 2)) := by
    intro i
    have hraw := Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec (claim_11 F (1 : F) (alphaOf i) theta tau)))
    dsimp only [uSeq, vSeq, cSeq]
    simpa only [mul_one] using hraw
  let unitOrOne (x : F) : Fˣ := if hx : x = 0 then 1 else Units.mk0 x hx
  have hunitOrOne_coe : ∀ (x : F), x ≠ 0 → ((unitOrOne x : Fˣ) : F) = x := by
    intro x hx
    simp [unitOrOne, hx]
  let dSeq (i : ValidIndex) (j : ℕ) : G :=
    zeta ^ j * kOf (unitOrOne (cSeq i j))
  have hdSeq_mem : ∀ (i : ValidIndex) (j : ℕ), dSeq i j ∈ K ⊔ W := by
    intro i j
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (W.pow_mem hzeta j))
      (Subgroup.mem_sup_left (hkOf_mem _))
  have hcenter_conj_dSeq : ∀ (i : ValidIndex) (j : ℕ),
      cSeq i j ≠ 0 → ∀ x : F,
        rightConjugateElem (center x) (dSeq i j) =
          center (cSeq i j * theta (cSeq i j) * x) := by
    intro i j hc x
    let cUnit : Fˣ := unitOrOne (cSeq i j)
    have hcUnit : ((cUnit : Fˣ) : F) = cSeq i j :=
      hunitOrOne_coe _ hc
    have hzpow : zeta ^ j ∈ W := W.pow_mem hzeta j
    calc
      rightConjugateElem (center x) (dSeq i j) =
          rightConjugateElem
            (rightConjugateElem (center x) (zeta ^ j)) (kOf cUnit) := by
        simp [dSeq, cUnit, rightConjugateElem, mul_assoc]
      _ = rightConjugateElem (center x) (kOf cUnit) := by
        rw [hcenter_conj_W (zeta ^ j) hzpow]
      _ = center ((cUnit : F) * theta (cUnit : F) * x) :=
        hcenter_conj_K_exact (kOf cUnit) (hkOf_mem cUnit) cUnit
          (hkOf_coord cUnit) x
      _ = center (cSeq i j * theta (cSeq i j) * x) := by
        rw [hcUnit]
  have huSeq_succ_ne_zero : ∀ (i : ValidIndex) (j : ℕ),
      uSeq i j ≠ alphaOf i → uSeq i (j + 1) ≠ 0 := by
    intro i j hu
    rw [(hseq i).2.2.2.1 j hu]
    apply inv_ne_zero
    intro hsum
    apply hu
    exact (CharTwo.add_eq_zero.mp hsum).symm
  have hcSeq_succ_ne_zero : ∀ (i : ValidIndex) (j : ℕ),
      uSeq i j ≠ alphaOf i → cSeq i j ≠ 0 →
        cSeq i (j + 1) ≠ 0 := by
    intro i j hu hc
    rw [(hseq i).2.2.2.2.2 j hu]
    apply mul_ne_zero hc
    apply htau_ne_zero
    exact pow_ne_zero 2 (inv_ne_zero (huSeq_succ_ne_zero i j hu))
  let aStep (i : ValidIndex) (j : ℕ) : G :=
    kOf (unitOrOne (tau (uSeq i (j + 1))))
  have haStep_mem : ∀ (i : ValidIndex) (j : ℕ), aStep i j ∈ K := by
    intro i j
    exact hkOf_mem _
  have haStep_coord : ∀ (i : ValidIndex) (j : ℕ),
      uSeq i (j + 1) ≠ 0 →
      (((kwIso
          (⟨aStep i j, Subgroup.mem_sup_left (haStep_mem i j)⟩ :
            (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
        ((unitOrOne (tau (uSeq i (j + 1))) : Fˣ) : F) := by
    intro i j _hu
    exact hkOf_coord _
  have hdSeq_succ : ∀ (i : ValidIndex) (j : ℕ),
      uSeq i j ≠ alphaOf i → cSeq i j ≠ 0 →
        dSeq i (j + 1) = dSeq i j * zeta * (aStep i j)⁻¹ ^ 2 := by
    intro i j hu hc
    have huNext : uSeq i (j + 1) ≠ 0 := huSeq_succ_ne_zero i j hu
    have htauNext : tau (uSeq i (j + 1)) ≠ 0 :=
      htau_ne_zero _ huNext
    have hcNext : cSeq i (j + 1) ≠ 0 :=
      hcSeq_succ_ne_zero i j hu hc
    let cUnit : Fˣ := unitOrOne (cSeq i j)
    let stepUnit : Fˣ := unitOrOne (tau (uSeq i (j + 1)))
    let nextUnit : Fˣ := unitOrOne (cSeq i (j + 1))
    have htauTerm :
        tau ((uSeq i (j + 1))⁻¹ ^ 2) =
          (tau (uSeq i (j + 1)))⁻¹ ^ 2 := by
      rw [pow_two, htau_mul, htau_inv]
      rw [pow_two]
    have hunit : nextUnit = cUnit * stepUnit⁻¹ ^ 2 := by
      apply Units.ext
      dsimp only [nextUnit, cUnit, stepUnit]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
      rw [hunitOrOne_coe _ hcNext, hunitOrOne_coe _ hc,
        hunitOrOne_coe _ htauNext]
      rw [(hseq i).2.2.2.2.2 j hu, htauTerm]
    have hk : kOf nextUnit = kOf cUnit * (kOf stepUnit)⁻¹ ^ 2 := by
      rw [hunit, pow_two, hkOf_mul, hkOf_mul, hkOf_inv]
      rw [pow_two]
    have hcomm : Commute (kOf cUnit) zeta :=
      hKW_commute (kOf cUnit) zeta
        (Subgroup.mem_sup_left (hkOf_mem cUnit)) (Subgroup.mem_sup_right hzeta)
    change
      zeta ^ (j + 1) * kOf nextUnit =
        (zeta ^ j * kOf cUnit) * zeta * (kOf stepUnit)⁻¹ ^ 2
    rw [pow_succ, hk]
    calc
      zeta ^ j * zeta * (kOf cUnit * (kOf stepUnit)⁻¹ ^ 2) =
          zeta ^ j * (zeta * kOf cUnit) * (kOf stepUnit)⁻¹ ^ 2 := by
        simp only [mul_assoc]
      _ = zeta ^ j * (kOf cUnit * zeta) * (kOf stepUnit)⁻¹ ^ 2 := by
        rw [← hcomm.eq]
      _ = (zeta ^ j * kOf cUnit) * zeta * (kOf stepUnit)⁻¹ ^ 2 := by
        simp only [mul_assoc]
  have hzetaD : zeta ∈ D :=
    PFchapter1section2.proposition_3_W_le_D
      H D Q K V W Q0 S Q1 t hsec hzeta
  have hzeta_t : rightConjugateElem zeta t = zeta := by
    have htC : t ∈ Subgroup.centralizer (W : Set G) :=
      PFchapter1section1.t_mem_centralizer_of_le_peterfalviV
        D V W t hsec.W_le_V hsec.V_eq
    have hcomm : Commute zeta t :=
      Subgroup.mem_centralizer_iff.mp htC zeta hzeta
    simp [rightConjugateElem, hcomm.eq, mul_assoc]
  have hs_zeta : Commute s zeta := by
    have hconj : rightConjugateElem s zeta = s := by
      rw [hs_center]
      exact hcenter_conj_W zeta hzeta 1
    have hmul := congrArg (zeta * ·) hconj
    change s * zeta = zeta * s
    simpa [rightConjugateElem, mul_assoc] using hmul
  have hrightConjugateElem_mul : ∀ x y d : G,
      rightConjugateElem (x * y) d =
        rightConjugateElem x d * rightConjugateElem y d := by
    intro x y d
    simp [rightConjugateElem, mul_assoc]
  have hrightConjugateElem_comp : ∀ x a b : G,
      rightConjugateElem (rightConjugateElem x a) b =
        rightConjugateElem x (a * b) := by
    intro x a b
    simp [rightConjugateElem, mul_assoc]
  have hrightConjugateElem_one : ∀ x : G, rightConjugateElem x 1 = x := by
    intro x
    simp [rightConjugateElem]
  have hrightConjugateElem_pow : ∀ x a : G, ∀ j : ℕ,
      rightConjugateElem (x ^ j) a = (rightConjugateElem x a) ^ j := by
    intro x a j
    induction j with
    | zero => simp [rightConjugateElem]
    | succ j ih => rw [pow_succ, hrightConjugateElem_mul, ih, pow_succ]
  have hclaim10 : ∀ (i : ValidIndex) (a b : G), ∀ (ha : a ∈ K), ∀ (hb : b ∈ K),
      ∀ (aCoord bCoord : Fˣ),
      (((kwIso (⟨a, Subgroup.mem_sup_left ha⟩ : (K ⊔ W : Subgroup G)) :
          (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) = ((aCoord : F) : E) →
      (((kwIso (⟨b, Subgroup.mem_sup_left hb⟩ : (K ⊔ W : Subgroup G)) :
          (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) = ((bCoord : F) : E) →
      (bCoord : F) * theta (bCoord : F) =
        alphaOf i + ((aCoord : F) * theta (aCoord : F))⁻¹ →
      f (omega (i : ℕ) * rightConjugateElem s a) =
        rightConjugateElem
          (f (omega (i : ℕ) * rightConjugateElem s b) *
            rightConjugateElem s a)
          (zeta * a⁻¹ ^ 2) := by
    intro i a b ha hb aCoord bCoord haCoord hbCoord hrel
    let aKW : (K ⊔ W : Subgroup G) :=
      ⟨a, Subgroup.mem_sup_left ha⟩
    have haInvCoord :
        (((kwIso
            (⟨a⁻¹, Subgroup.mem_sup_left (K.inv_mem ha)⟩ :
              (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
          (((aCoord⁻¹ : Fˣ) : F) : E) := by
      have hainv :
          (⟨a⁻¹, Subgroup.mem_sup_left (K.inv_mem ha)⟩ :
              (K ⊔ W : Subgroup G)) = aKW⁻¹ := Subtype.ext rfl
      rw [hainv, map_inv]
      have hcoe := congrArg Inv.inv haCoord
      simpa [aKW] using hcoe
    have hs_a_inv : rightConjugateElem s a⁻¹ =
        center (((aCoord : F) * theta (aCoord : F))⁻¹) := by
      rw [hs_center]
      have hact := hcenter_conj_K_exact a⁻¹ (K.inv_mem ha) aCoord⁻¹
        haInvCoord 1
      rw [hact]
      congr 1
      simp only [Units.val_inv_eq_inv_val, map_inv₀, mul_one]
      rw [mul_inv]
    have hs_b : rightConjugateElem s b =
        center ((bCoord : F) * theta (bCoord : F)) := by
      rw [hs_center]
      simpa using hcenter_conj_K_exact b hb bCoord hbCoord 1
    have hcenter_relation :
        center (alphaOf i) * rightConjugateElem s a⁻¹ =
          rightConjugateElem s b := by
      rw [hs_a_inv, hs_b, ← hcenter_add, hrel]
    have hs_a_inv_zeta :
        rightConjugateElem (rightConjugateElem s a⁻¹) zeta =
          rightConjugateElem s a⁻¹ := by
      rw [hs_a_inv, hcenter_conj_W zeta hzeta]
    have hargument :
        f (omega (i : ℕ)) * rightConjugateElem s a⁻¹ =
          rightConjugateElem
            (omega (i : ℕ) * rightConjugateElem s b) zeta := by
      calc
        f (omega (i : ℕ)) * rightConjugateElem s a⁻¹ =
            rightConjugateElem
                (omega (i : ℕ) * center (alphaOf i)) zeta *
              rightConjugateElem s a⁻¹ := by
          rw [hfomega_alpha i]
        _ = rightConjugateElem (omega (i : ℕ)) zeta *
              rightConjugateElem (center (alphaOf i)) zeta *
                rightConjugateElem
                  (rightConjugateElem s a⁻¹) zeta := by
          rw [hs_a_inv_zeta]
          simp [rightConjugateElem, mul_assoc]
        _ = rightConjugateElem
              (omega (i : ℕ) *
                (center (alphaOf i) * rightConjugateElem s a⁻¹)) zeta := by
          simp [rightConjugateElem, mul_assoc]
        _ = rightConjugateElem
              (omega (i : ℕ) * rightConjugateElem s b) zeta := by
          rw [hcenter_relation]
    have hs_b_Q0 : rightConjugateElem s b ∈ Q0 := by
      rw [hs_b]
      exact hcenter_mem_Q0 _
    have hbaseQ : omega (i : ℕ) * rightConjugateElem s b ∈ Q :=
      Q.mul_mem (homega_valid i).1 (hsec.Q0_le_Q hs_b_Q0)
    have hbase_not_Q0 : omega (i : ℕ) * rightConjugateElem s b ∉ Q0 := by
      intro hprod
      apply (homega_valid i).2
      have heq : omega (i : ℕ) =
          (omega (i : ℕ) * rightConjugateElem s b) *
            (rightConjugateElem s b)⁻¹ := by simp [mul_assoc]
      rw [heq]
      exact Q0.mul_mem hprod (Q0.inv_mem hs_b_Q0)
    have hbase_ne : omega (i : ℕ) * rightConjugateElem s b ≠ 1 := by
      intro hbase
      exact hbase_not_Q0 (hbase ▸ Q0.one_mem)
    have hf_conj :
        f (rightConjugateElem
            (omega (i : ℕ) * rightConjugateElem s b) zeta) =
          rightConjugateElem
            (f (omega (i : ℕ) * rightConjugateElem s b)) zeta := by
      simpa [hzeta_t] using
        PFchapter4section1.claim_H3 H Q D t f g h
          htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
          hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq (omega (i : ℕ) * rightConjugateElem s b) zeta
          hbaseQ hbase_ne hzetaD
    rw [claim_2 H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (omega (i : ℕ)) a (homega_valid i).1 (homega_valid i).2 ha]
    rw [hargument, hf_conj]
    have hazeta : Commute a zeta :=
      hKW_commute a zeta (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hzeta)
    have hword : a * (zeta * a⁻¹ ^ 2) = zeta * a⁻¹ := by
      calc
        a * (zeta * a⁻¹ ^ 2) = (a * zeta) * a⁻¹ ^ 2 := by
          simp only [mul_assoc]
        _ = (zeta * a) * a⁻¹ ^ 2 := by rw [hazeta.eq]
        _ = zeta * a⁻¹ := by group
    have hsz : rightConjugateElem s zeta = s := by
      simp only [rightConjugateElem, mul_assoc]
      rw [hs_zeta.eq]
      simp
    have hs_word : rightConjugateElem s (zeta * a⁻¹) =
        rightConjugateElem s a⁻¹ := by
      calc
        rightConjugateElem s (zeta * a⁻¹) =
            rightConjugateElem (rightConjugateElem s zeta) a⁻¹ :=
          (hrightConjugateElem_comp s zeta a⁻¹).symm
        _ = rightConjugateElem s a⁻¹ := by rw [hsz]
    rw [hrightConjugateElem_comp, hrightConjugateElem_mul,
      hrightConjugateElem_comp, hword, hs_word]
  have hformula_step : ∀ (i : ValidIndex) (j : ℕ), 1 ≤ j →
      uSeq i j ≠ alphaOf i → cSeq i j ≠ 0 →
      f (omega (i : ℕ) * center (uSeq i j)) =
        rightConjugateElem
          (omega (i : ℕ) * center (vSeq i j)) (dSeq i j) →
      cSeq i (j + 1) ≠ 0 ∧
        f (omega (i : ℕ) * center (uSeq i (j + 1))) =
          rightConjugateElem
            (omega (i : ℕ) * center (vSeq i (j + 1))) (dSeq i (j + 1)) := by
    intro i j _hj hu hc hformula
    let next := uSeq i (j + 1)
    have hnext : next ≠ 0 := huSeq_succ_ne_zero i j hu
    have htauNext : tau next ≠ 0 := htau_ne_zero next hnext
    let aUnit : Fˣ := unitOrOne (tau next)
    let a : G := aStep i j
    have ha : a ∈ K := haStep_mem i j
    have haCoord :
        (((kwIso (⟨a, Subgroup.mem_sup_left ha⟩ :
            (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
          ((aUnit : F) : E) := by
      exact haStep_coord i j hnext
    have haNorm : (aUnit : F) * theta (aUnit : F) = next := by
      rw [hunitOrOne_coe _ htauNext]
      exact hnorm_tau next
    have hs_a : rightConjugateElem s a = center next := by
      rw [hs_center]
      simpa [haNorm] using hcenter_conj_K_exact a ha aUnit haCoord 1
    have haInvCoord :
        (((kwIso
            (⟨a⁻¹, Subgroup.mem_sup_left (K.inv_mem ha)⟩ :
              (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
          (((aUnit⁻¹ : Fˣ) : F) : E) := by
      let aKW : (K ⊔ W : Subgroup G) :=
        ⟨a, Subgroup.mem_sup_left ha⟩
      have hainv :
          (⟨a⁻¹, Subgroup.mem_sup_left (K.inv_mem ha)⟩ :
              (K ⊔ W : Subgroup G)) = aKW⁻¹ := Subtype.ext rfl
      rw [hainv, map_inv]
      have hcoe := congrArg Inv.inv haCoord
      simpa [aKW] using hcoe
    have hs_a_inv : rightConjugateElem s a⁻¹ = center next⁻¹ := by
      rw [hs_center]
      have hact := hcenter_conj_K_exact a⁻¹ (K.inv_mem ha) aUnit⁻¹
        haInvCoord 1
      rw [hact]
      congr 1
      simp only [Units.val_inv_eq_inv_val, map_inv₀, mul_one]
      simpa only [mul_inv] using congrArg Inv.inv haNorm
    have hcenter_relation :
        center (alphaOf i) * rightConjugateElem s a⁻¹ =
          center (uSeq i j) := by
      rw [hs_a_inv, ← hcenter_add]
      congr 1
      have hrec := (hseq i).2.2.2.1 j hu
      change next = (alphaOf i + uSeq i j)⁻¹ at hrec
      have hinv := congrArg Inv.inv hrec
      have hnextInv : next⁻¹ = alphaOf i + uSeq i j := by
        simpa only [inv_inv] using hinv
      rw [hnextInv]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have hs_a_inv_zeta :
        rightConjugateElem (rightConjugateElem s a⁻¹) zeta =
          rightConjugateElem s a⁻¹ := by
      rw [hs_a_inv, hcenter_conj_W zeta hzeta]
    have hargument :
        f (omega (i : ℕ)) * rightConjugateElem s a⁻¹ =
          rightConjugateElem
            (omega (i : ℕ) * center (uSeq i j)) zeta := by
      calc
        f (omega (i : ℕ)) * rightConjugateElem s a⁻¹ =
            rightConjugateElem
                (omega (i : ℕ) * center (alphaOf i)) zeta *
              rightConjugateElem s a⁻¹ := by
          rw [hfomega_alpha i]
        _ = rightConjugateElem (omega (i : ℕ)) zeta *
              rightConjugateElem (center (alphaOf i)) zeta *
                rightConjugateElem (rightConjugateElem s a⁻¹) zeta := by
          rw [hs_a_inv_zeta]
          simp [rightConjugateElem, mul_assoc]
        _ = rightConjugateElem
              (omega (i : ℕ) *
                (center (alphaOf i) * rightConjugateElem s a⁻¹)) zeta := by
          simp [rightConjugateElem, mul_assoc]
        _ = rightConjugateElem
              (omega (i : ℕ) * center (uSeq i j)) zeta := by
          rw [hcenter_relation]
    have hbaseQ : omega (i : ℕ) * center (uSeq i j) ∈ Q :=
      Q.mul_mem (homega_valid i).1 (hsec.Q0_le_Q (hcenter_mem_Q0 _))
    have hbase_not_Q0 : omega (i : ℕ) * center (uSeq i j) ∉ Q0 := by
      intro hprod
      apply (homega_valid i).2
      have heq : omega (i : ℕ) =
          (omega (i : ℕ) * center (uSeq i j)) *
            (center (uSeq i j))⁻¹ := by simp [mul_assoc]
      rw [heq]
      exact Q0.mul_mem hprod (Q0.inv_mem (hcenter_mem_Q0 _))
    have hbase_ne : omega (i : ℕ) * center (uSeq i j) ≠ 1 := by
      intro hbase
      exact hbase_not_Q0 (hbase ▸ Q0.one_mem)
    have hf_conj :
        f (rightConjugateElem
            (omega (i : ℕ) * center (uSeq i j)) zeta) =
          rightConjugateElem
            (f (omega (i : ℕ) * center (uSeq i j))) zeta := by
      simpa [hzeta_t] using
        PFchapter4section1.claim_H3 H Q D t f g h
          htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
          hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq (omega (i : ℕ) * center (uSeq i j)) zeta
          hbaseQ hbase_ne hzetaD
    have hclaim2 := claim_2 H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (omega (i : ℕ)) a (homega_valid i).1 (homega_valid i).2 ha
    have hcentral_a_sq :
        rightConjugateElem (center next) (a⁻¹ ^ 2) = center next⁻¹ := by
      calc
        rightConjugateElem (center next) (a⁻¹ ^ 2) =
            rightConjugateElem (rightConjugateElem s a) (a⁻¹ ^ 2) := by
          rw [hs_a]
        _ = rightConjugateElem s a⁻¹ := by
          simp [rightConjugateElem, pow_two, mul_assoc]
        _ = center next⁻¹ := hs_a_inv
    let scale := cSeq i j * theta (cSeq i j)
    have hscale : scale ≠ 0 :=
      mul_ne_zero hc ((map_ne_zero theta).2 hc)
    let delta := next * scale⁻¹
    have hdelta_action :
        rightConjugateElem (center delta) (dSeq i j) = center next := by
      rw [hcenter_conj_dSeq i j hc]
      congr 1
      change scale * delta = next
      dsimp only [delta]
      field_simp [hscale]
    have hvNext : vSeq i (j + 1) = vSeq i j + delta := by
      rw [(hseq i).2.2.2.2.1 j hu]
    refine ⟨hcSeq_succ_ne_zero i j hu hc, ?_⟩
    calc
      f (omega (i : ℕ) * center (uSeq i (j + 1))) =
          rightConjugateElem
              (f (f (omega (i : ℕ)) * rightConjugateElem s a⁻¹))
              (a⁻¹ ^ 2) * rightConjugateElem s a⁻¹ := by
        rw [← hs_a]
        exact hclaim2
      _ = rightConjugateElem
              (rightConjugateElem
                (f (omega (i : ℕ) * center (uSeq i j))) zeta)
              (a⁻¹ ^ 2) * center next⁻¹ := by
        rw [hargument, hf_conj, hs_a_inv]
      _ = rightConjugateElem
              (rightConjugateElem
                (f (omega (i : ℕ) * center (uSeq i j)) * center next) zeta)
              (a⁻¹ ^ 2) := by
        rw [← hcentral_a_sq]
        rw [hrightConjugateElem_mul, hcenter_conj_W zeta hzeta]
        rw [hrightConjugateElem_mul]
      _ = rightConjugateElem
              (rightConjugateElem
                (rightConjugateElem
                  (omega (i : ℕ) * center (vSeq i j + delta))
                  (dSeq i j)) zeta)
              (a⁻¹ ^ 2) := by
        rw [hformula, ← hdelta_action, ← hrightConjugateElem_mul]
        rw [mul_assoc, ← hcenter_add]
      _ = rightConjugateElem
            (omega (i : ℕ) * center (vSeq i (j + 1)))
            (dSeq i (j + 1)) := by
        rw [hvNext, hdSeq_succ i j hu hc]
        dsimp only [a]
        simp [rightConjugateElem, mul_assoc]
  have hformula_until : ∀ (i : ValidIndex) (j : ℕ), 1 ≤ j →
      (∀ r : ℕ, 1 ≤ r → r < j → uSeq i r ≠ alphaOf i) →
      cSeq i j ≠ 0 ∧
        f (omega (i : ℕ) * center (uSeq i j)) =
          rightConjugateElem
            (omega (i : ℕ) * center (vSeq i j)) (dSeq i j) := by
    intro i j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    induction k with
    | zero =>
        intro _hbefore
        have hdOne : dSeq i 1 = zeta := by
          simp [dSeq, (hseq i).2.2.1, unitOrOne, hkOf_one]
        refine ⟨by simp [(hseq i).2.2.1], ?_⟩
        simpa [omegaAt, (hseq i).1, (hseq i).2.1, hcenter_zero, hdOne] using
          hfomega_alpha i
    | succ k ih =>
        intro hbefore
        have hprevBefore : ∀ r : ℕ, 1 ≤ r → r < 1 + k →
            uSeq i r ≠ alphaOf i := by
          intro r hr hrk
          exact hbefore r hr (by omega)
        obtain ⟨hc, hformula⟩ := ih (by omega) hprevBefore
        have hu : uSeq i (1 + k) ≠ alphaOf i :=
          hbefore (1 + k) (by omega) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hformula_step i (1 + k) (by omega) hu hc hformula
  let m := Nat.card W
  have hzeta_order : orderOf zeta = m := by
    change orderOf zeta = Nat.card W
    rw [← hzeta_gen, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have hm_two : 2 ≤ m := by
    have horder_ne_one : orderOf zeta ≠ 1 := by
      intro horder
      exact hzeta_ne (orderOf_eq_one_iff.mp horder)
    have horder_pos : 0 < orderOf zeta := orderOf_pos zeta
    rw [← hzeta_order]
    omega
  have hK_inter_W : ∀ x : G, x ∈ K → x ∈ W → x = 1 := by
    intro x hxK hxW
    obtain ⟨b, hb⟩ := hK_scalar x hxK
    let xKW : (K ⊔ W : Subgroup G) :=
      ⟨x, Subgroup.mem_sup_left hxK⟩
    let xUnit : Eˣ := ((kwIso xKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ)
    have hxUnitW : xUnit ∈ W1 := by
      have hmem := hkwIso_mem_W1 x hxW
      simpa [xKW, xUnit] using hmem
    have hsigma : sigma (xUnit : E) = (xUnit : E)⁻¹ :=
      hW1inv xUnit hxUnitW
    have htheta : theta (b : F) = (b : F)⁻¹ := by
      apply F.subtype.injective
      have hcoe : (xUnit : E) = ((b : F) : E) := by
        simpa [xKW, xUnit] using hb
      rw [hcoe] at hsigma
      calc
        ((theta (b : F) : F) : E) = sigma (((b : F) : F) : E) :=
          (hsigmaF (b : F)).symm
        _ = (((b : F) : E))⁻¹ := hsigma
        _ = ((((b : F)⁻¹ : F)) : E) :=
          (map_inv₀ F.subtype (b : F)).symm
    have hnorm : (b : F) * theta (b : F) = 1 := by
      rw [htheta]
      exact mul_inv_cancel₀ (Units.ne_zero b)
    have hb_one : (b : F) = 1 := by
      apply (norm_bijective_of_odd_order theta hthetaOdd).1
      simpa using hnorm
    have hxImage : kwIso xKW = 1 := by
      apply Subtype.ext
      apply Units.ext
      change (xUnit : E) = 1
      rw [show (xUnit : E) = ((b : F) : E) by simpa [xKW, xUnit] using hb,
        hb_one]
      rfl
    have hxKW : xKW = 1 := kwIso.injective (by simpa using hxImage)
    exact congrArg Subtype.val hxKW
  have hstop_exists : ∀ i : ValidIndex, ∃ l : ℕ,
      1 ≤ l ∧ l ≤ m - 1 ∧ uSeq i l = alphaOf i := by
    intro i
    by_contra hnone
    have hnostop : ∀ r : ℕ, 1 ≤ r → r ≤ m - 1 →
        uSeq i r ≠ alphaOf i := by
      intro r hr hrm heq
      exact hnone ⟨r, hr, hrm, heq⟩
    have hbeforeM : ∀ r : ℕ, 1 ≤ r → r < m →
        uSeq i r ≠ alphaOf i := by
      intro r hr hrm
      exact hnostop r hr (by omega)
    obtain ⟨hcM, hformulaM⟩ := hformula_until i m (by omega) hbeforeM
    have hzpow : zeta ^ m = 1 := by
      rw [← hzeta_order, pow_orderOf_eq_one]
    have hdM_K : dSeq i m ∈ K := by
      change zeta ^ m * kOf (unitOrOne (cSeq i m)) ∈ K
      rw [hzpow, one_mul]
      exact hkOf_mem _
    have hbaseQ : omega (i : ℕ) * center (uSeq i m) ∈ Q :=
      Q.mul_mem (homega_valid i).1 (hsec.Q0_le_Q (hcenter_mem_Q0 _))
    have hbase_not_Q0 : omega (i : ℕ) * center (uSeq i m) ∉ Q0 := by
      intro hprod
      apply (homega_valid i).2
      have heq : omega (i : ℕ) =
          (omega (i : ℕ) * center (uSeq i m)) *
            (center (uSeq i m))⁻¹ := by simp [mul_assoc]
      rw [heq]
      exact Q0.mul_mem hprod (Q0.inv_mem (hcenter_mem_Q0 _))
    let y := center (uSeq i m + vSeq i m)
    have hyQ0 : y ∈ Q0 := hcenter_mem_Q0 _
    have hbase_y :
        (omega (i : ℕ) * center (uSeq i m)) * y =
          omega (i : ℕ) * center (vSeq i m) := by
      dsimp [y]
      rw [mul_assoc, ← hcenter_add]
      congr 2
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have hshape :
        f (omega (i : ℕ) * center (uSeq i m)) =
          rightConjugateElem
            ((omega (i : ℕ) * center (uSeq i m)) * y) (dSeq i m) := by
      rw [hbase_y]
      exact hformulaM
    have hdM_not_K :=
      claim_5_b H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
        (omega (i : ℕ) * center (uSeq i m)) y (dSeq i m)
        hbaseQ hbase_not_Q0 hyQ0 (hsec.K_le_D hdM_K) hshape
    exact hdM_not_K hdM_K
  let stopIndex (i : ValidIndex) : ℕ := Nat.find (hstop_exists i)
  have hstop_spec : ∀ i : ValidIndex,
      1 ≤ stopIndex i ∧ stopIndex i ≤ m - 1 ∧
        uSeq i (stopIndex i) = alphaOf i := by
    intro i
    exact Nat.find_spec (hstop_exists i)
  have hstop_before : ∀ (i : ValidIndex) (r : ℕ),
      1 ≤ r → r < stopIndex i → uSeq i r ≠ alphaOf i := by
    intro i r hr hrlt heq
    have hle := Nat.find_min' (hstop_exists i)
      ⟨hr, hrlt.le.trans (hstop_spec i).2.1, heq⟩
    exact (Nat.not_le_of_gt hrlt) hle
  have hstop_formula : ∀ i : ValidIndex,
      cSeq i (stopIndex i) ≠ 0 ∧
        f (omega (i : ℕ) * center (alphaOf i)) =
          rightConjugateElem
            (omega (i : ℕ) * center (vSeq i (stopIndex i)))
            (dSeq i (stopIndex i)) := by
    intro i
    obtain ⟨hc, hf⟩ := hformula_until i (stopIndex i) (hstop_spec i).1
      (fun r hr hrlt => hstop_before i r hr hrlt)
    exact ⟨hc, by simpa [(hstop_spec i).2.2] using hf⟩
  have hf_at_alpha : ∀ i : ValidIndex,
      f (omega (i : ℕ) * center (alphaOf i)) =
        rightConjugateElem (omega (i : ℕ)) zeta⁻¹ := by
    intro i
    have hbaseQ : omega (i : ℕ) * center (alphaOf i) ∈ Q :=
      Q.mul_mem (homega_valid i).1 (hsec.Q0_le_Q (hcenter_mem_Q0 _))
    have hbase_not_Q0 : omega (i : ℕ) * center (alphaOf i) ∉ Q0 := by
      intro hprod
      apply (homega_valid i).2
      have heq : omega (i : ℕ) =
          (omega (i : ℕ) * center (alphaOf i)) *
            (center (alphaOf i))⁻¹ := by simp [mul_assoc]
      rw [heq]
      exact Q0.mul_mem hprod (Q0.inv_mem (hcenter_mem_Q0 _))
    have hbase_ne : omega (i : ℕ) * center (alphaOf i) ≠ 1 := by
      intro hone
      exact hbase_not_Q0 (hone ▸ Q0.one_mem)
    have htransport :=
      PFchapter4section1.claim_H3 H Q D t f g h
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
        hcanonical_eq (omega (i : ℕ) * center (alphaOf i)) zeta
        hbaseQ hbase_ne hzetaD
    have hdouble :=
      PFchapter4section1.claim_H2 H Q D t f g h
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
        hcanonical_eq (omega (i : ℕ)) (homega_valid i).1
        (fun hone => (homega_valid i).2 (hone ▸ Q0.one_mem))
    have hconj :
        rightConjugateElem
            (f (omega (i : ℕ) * center (alphaOf i))) zeta =
          omega (i : ℕ) := by
      calc
        rightConjugateElem
            (f (omega (i : ℕ) * center (alphaOf i))) zeta =
            f (rightConjugateElem
              (omega (i : ℕ) * center (alphaOf i)) zeta) := by
          simpa [hzeta_t] using htransport.symm
        _ = f (f (omega (i : ℕ))) := by rw [hfomega_alpha i]
        _ = omega (i : ℕ) := hdouble
    have hback := congrArg (fun x : G => rightConjugateElem x zeta⁻¹) hconj
    simpa [rightConjugateElem, mul_assoc] using hback
  have hd_stop : ∀ i : ValidIndex, dSeq i (stopIndex i) = zeta⁻¹ := by
    intro i
    let l := stopIndex i
    let c := cSeq i l
    let v := vSeq i l
    let d := dSeq i l
    let e := d * zeta
    have hc : c ≠ 0 := (hstop_formula i).1
    have hdKW : d ∈ K ⊔ W := hdSeq_mem i l
    have hKWleD : K ⊔ W ≤ D :=
      sup_le hsec.K_le_D
        (PFchapter1section2.proposition_3_W_le_D H D Q K V W Q0 S Q1 t hsec)
    have heD : e ∈ D := D.mul_mem (hKWleD hdKW) hzetaD
    have heq :
        rightConjugateElem
            (omega (i : ℕ) * center v) e = omega (i : ℕ) := by
      calc
        rightConjugateElem (omega (i : ℕ) * center v) e =
            rightConjugateElem
              (rightConjugateElem (omega (i : ℕ) * center v) d) zeta := by
          dsimp only [e]
          exact (hrightConjugateElem_comp _ d zeta).symm
        _ = rightConjugateElem
              (f (omega (i : ℕ) * center (alphaOf i))) zeta := by
          exact congrArg (fun x : G => rightConjugateElem x zeta)
            (hstop_formula i).2.symm
        _ = rightConjugateElem
              (rightConjugateElem (omega (i : ℕ)) zeta⁻¹) zeta := by
          exact congrArg (fun x : G => rightConjugateElem x zeta) (hf_at_alpha i)
        _ = omega (i : ℕ) := by
          rw [hrightConjugateElem_comp]
          rw [inv_mul_cancel, hrightConjugateElem_one]
    have hcenter_e :
        rightConjugateElem (center v) e =
          center (c * theta c * v) := by
      calc
        rightConjugateElem (center v) e =
            rightConjugateElem
              (rightConjugateElem (center v) d) zeta := by
          dsimp only [e]
          exact (hrightConjugateElem_comp _ d zeta).symm
        _ = rightConjugateElem (center (c * theta c * v)) zeta := by
          exact congrArg (fun x : G => rightConjugateElem x zeta)
            (hcenter_conj_dSeq i l hc v)
        _ = center (c * theta c * v) := hcenter_conj_W zeta hzeta _
    have hcenter_e_Q0 : rightConjugateElem (center v) e ∈ Q0 := by
      exact hcenter_e.symm ▸ hcenter_mem_Q0 _
    have hcomm_center_omega : Commute
        (rightConjugateElem (center v) e) (omega (i : ℕ)) :=
      hQ0_commutes_Q _ hcenter_e_Q0 _ (homega_valid i).1
    have hproduct :
        rightConjugateElem (omega (i : ℕ)) e *
            rightConjugateElem (center v) e = omega (i : ℕ) := by
      rw [← hrightConjugateElem_mul]
      exact heq
    have hfirst : rightConjugateElem (omega (i : ℕ)) e =
        omega (i : ℕ) * (rightConjugateElem (center v) e)⁻¹ :=
      eq_mul_inv_of_mul_eq hproduct
    have hfixedQ0 :
        rightConjugateElem (omega (i : ℕ)) e * (omega (i : ℕ))⁻¹ ∈ Q0 := by
      have heqdiff :
          rightConjugateElem (omega (i : ℕ)) e * (omega (i : ℕ))⁻¹ =
            (rightConjugateElem (center v) e)⁻¹ := by
        rw [hfirst]
        rw [← hcomm_center_omega.inv_left.eq]
        group
      rw [heqdiff]
      exact Q0.inv_mem hcenter_e_Q0
    have he_one : e = 1 := by
      by_contra he_ne
      exact (hD_fixed_point_free e heD he_ne (omega (i : ℕ))
        (homega_valid i).1 (homega_valid i).2) hfixedQ0
    exact eq_inv_of_mul_eq_one_left he_one
  have hstop_eq : ∀ i : ValidIndex, stopIndex i = m - 1 := by
    intro i
    let l := stopIndex i
    let cUnit : Fˣ := unitOrOne (cSeq i l)
    have hc : cSeq i l ≠ 0 := (hstop_formula i).1
    have hcomm : Commute (kOf cUnit) zeta :=
      hKW_commute (kOf cUnit) zeta
        (Subgroup.mem_sup_left (hkOf_mem cUnit)) (Subgroup.mem_sup_right hzeta)
    have hd : zeta ^ l * kOf cUnit = zeta⁻¹ := by
      simpa [dSeq, l, cUnit] using hd_stop i
    have hpow : zeta ^ (l + 1) = (kOf cUnit)⁻¹ := by
      calc
        zeta ^ (l + 1) = (zeta ^ l * kOf cUnit) * zeta * (kOf cUnit)⁻¹ := by
          rw [pow_succ]
          symm
          calc
            (zeta ^ l * kOf cUnit) * zeta * (kOf cUnit)⁻¹ =
                zeta ^ l * (kOf cUnit * zeta) * (kOf cUnit)⁻¹ := by
              simp [mul_assoc]
            _ = zeta ^ l * (zeta * kOf cUnit) * (kOf cUnit)⁻¹ := by
              rw [hcomm.eq]
            _ = zeta ^ l * zeta := by simp [mul_assoc]
        _ = zeta⁻¹ * zeta * (kOf cUnit)⁻¹ := by rw [hd]
        _ = (kOf cUnit)⁻¹ := by simp
    have hpowK : zeta ^ (l + 1) ∈ K := by
      rw [hpow]
      exact K.inv_mem (hkOf_mem cUnit)
    have hpowW : zeta ^ (l + 1) ∈ W := W.pow_mem hzeta _
    have hpowOne : zeta ^ (l + 1) = 1 := hK_inter_W _ hpowK hpowW
    have hle : l + 1 ≤ m := by
      have := (hstop_spec i).2.1
      omega
    have hnotlt : ¬ l + 1 < m := by
      intro hlt
      have hne := pow_ne_one_of_lt_orderOf (x := zeta) (n := l + 1)
        (by omega) (by simpa [hzeta_order] using hlt)
      exact hne hpowOne
    have heq : l + 1 = m := Nat.le_antisymm hle (Nat.le_of_not_gt hnotlt)
    have hl_one := (hstop_spec i).1
    dsimp [l] at heq ⊢
    omega
  have huSeq_ne_before_end : ∀ (i : ValidIndex) (j : ℕ),
      1 ≤ j → j < m - 1 → uSeq i j ≠ alphaOf i := by
    intro i j hj hjm
    apply hstop_before i j hj
    simpa [hstop_eq i] using hjm
  have hcSeq_ne_zero_to_end : ∀ (i : ValidIndex) (j : ℕ),
      1 ≤ j → j ≤ m - 1 → cSeq i j ≠ 0 := by
    intro i j hj hjm
    exact (hformula_until i j hj
      (fun r hr hrj => huSeq_ne_before_end i r hr (hrj.trans_le hjm))).1
  let scaleSeq (i : ValidIndex) (j : ℕ) : F :=
    cSeq i j * theta (cSeq i j)
  have hscaleSeq_ne_zero : ∀ (i : ValidIndex) (j : ℕ),
      1 ≤ j → j ≤ m - 1 → scaleSeq i j ≠ 0 := by
    intro i j hj hjm
    have hc := hcSeq_ne_zero_to_end i j hj hjm
    exact mul_ne_zero hc ((map_ne_zero theta).2 hc)
  have hscaleSeq_succ : ∀ (i : ValidIndex) (j : ℕ),
      1 ≤ j → j < m - 1 →
      scaleSeq i (j + 1) =
        scaleSeq i j * (uSeq i (j + 1))⁻¹ ^ 2 := by
    intro i j hj hjm
    have hu := huSeq_ne_before_end i j hj hjm
    let x := (uSeq i (j + 1))⁻¹ ^ 2
    have hnormx : tau x * theta (tau x) = x := hnorm_tau x
    change
      cSeq i (j + 1) * theta (cSeq i (j + 1)) =
        (cSeq i j * theta (cSeq i j)) * (uSeq i (j + 1))⁻¹ ^ 2
    rw [(hseq i).2.2.2.2.2 j hu, map_mul]
    change
      (cSeq i j * tau x) * (theta (cSeq i j) * theta (tau x)) =
        (cSeq i j * theta (cSeq i j)) * x
    calc
      (cSeq i j * tau x) * (theta (cSeq i j) * theta (tau x)) =
          (cSeq i j * theta (cSeq i j)) *
            (tau x * theta (tau x)) := by ring
      _ = (cSeq i j * theta (cSeq i j)) * x := by rw [hnormx]
  have hscale_relation : ∀ (i : ValidIndex) (j : ℕ),
      1 ≤ j → j ≤ m - 2 →
      uSeq i (j + 1) * (scaleSeq i j)⁻¹ =
        uSeq i j + uSeq i (j + 1) := by
    intro i j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    induction k with
    | zero =>
        intro _hm
        simp [scaleSeq, (hseq i).1, (hseq i).2.2.1]
    | succ k ih =>
        intro hbound
        let j := 1 + k
        let x := uSeq i j
        let y := uSeq i (j + 1)
        let z := uSeq i (j + 2)
        let scale := scaleSeq i j
        have hj : 1 ≤ j := by omega
        have hjBound : j ≤ m - 2 := by omega
        have hjLt : j < m - 1 := by omega
        have hjsuccLt : j + 1 < m - 1 := by omega
        have huj := huSeq_ne_before_end i j hj hjLt
        have hujsucc := huSeq_ne_before_end i (j + 1) (by omega) hjsuccLt
        have hsumx : alphaOf i + x ≠ 0 := by
          intro hzero
          exact huj (CharTwo.add_eq_zero.mp hzero).symm
        have hsumy : alphaOf i + y ≠ 0 := by
          intro hzero
          exact hujsucc (CharTwo.add_eq_zero.mp hzero).symm
        have hy : y = (alphaOf i + x)⁻¹ := by
          simpa [j, x, y] using (hseq i).2.2.2.1 j huj
        have hz : z = (alphaOf i + y)⁻¹ := by
          simpa [j, y, z, Nat.add_assoc] using
            (hseq i).2.2.2.1 (j + 1) hujsucc
        have hyprod : y * (alphaOf i + x) = 1 := by
          rw [hy]
          exact inv_mul_cancel₀ hsumx
        have hzprod : z * (alphaOf i + y) = 1 := by
          rw [hz]
          exact inv_mul_cancel₀ hsumy
        have hprev : y * scale⁻¹ = x + y := by
          simpa [j, x, y, scale] using ih (by omega) hjBound
        have hscaleNe : scale ≠ 0 :=
          hscaleSeq_ne_zero i j hj (by omega)
        have hyNe : y ≠ 0 := huSeq_succ_ne_zero i j huj
        have halgebra : z * y * (x + y) = y + z := by
          have hxy : x * y = 1 + alphaOf i * y := by
            have hsum : y * alphaOf i + y * x = 1 := by
              simpa only [mul_add] using hyprod
            have hcancel :
                (y * alphaOf i + y * x) + y * alphaOf i = y * x := by
              calc
                (y * alphaOf i + y * x) + y * alphaOf i =
                    (y * alphaOf i + y * alphaOf i) + y * x := by ac_rfl
                _ = y * x := by
                  rw [CharTwo.add_self_eq_zero, zero_add]
            calc
              x * y = y * x := mul_comm _ _
              _ = (y * alphaOf i + y * x) + y * alphaOf i := hcancel.symm
              _ = 1 + y * alphaOf i := by rw [hsum]
              _ = 1 + alphaOf i * y := by rw [mul_comm]
          calc
            z * y * (x + y) = z * (x * y + y ^ 2) := by ring
            _ = z * (1 + alphaOf i * y + y ^ 2) := by rw [hxy]
            _ = z + y * (z * alphaOf i + z * y) := by ring
            _ = z + y := by rw [← mul_add, hzprod, mul_one]
            _ = y + z := add_comm _ _
        change z * (scaleSeq i (j + 1))⁻¹ = y + z
        calc
          z * (scaleSeq i (j + 1))⁻¹ =
              z * (scale * y⁻¹ ^ 2)⁻¹ := by
            rw [hscaleSeq_succ i j hj hjLt]
          _ = z * scale⁻¹ * y ^ 2 := by
            field_simp [hscaleNe, hyNe]
          _ = z * y * (y * scale⁻¹) := by ring
          _ = z * y * (x + y) := by rw [hprev]
          _ = y + z := halgebra
  have hvSeq_shift : ∀ (i : ValidIndex) (j : ℕ),
      1 ≤ j → j ≤ m - 1 →
        vSeq i j = uSeq i j + alphaOf i := by
    intro i j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    induction k with
    | zero =>
        intro _hm
        rw [(hseq i).1, (hseq i).2.1]
        simp
    | succ k ih =>
        intro hbound
        let j := 1 + k
        have hj : 1 ≤ j := by omega
        have hjBound : j ≤ m - 2 := by omega
        have hjLt : j < m - 1 := by omega
        have hu := huSeq_ne_before_end i j hj hjLt
        have hvrec := (hseq i).2.2.2.2.1 j hu
        have hrel := hscale_relation i j hj hjBound
        have hprev := ih (by omega) (by omega : j ≤ m - 1)
        change vSeq i (j + 1) = uSeq i (j + 1) + alphaOf i
        rw [hvrec]
        change vSeq i j + uSeq i (j + 1) * (scaleSeq i j)⁻¹ = _
        rw [hprev, hrel]
        calc
          (uSeq i j + alphaOf i) +
              (uSeq i j + uSeq i (j + 1)) =
              (uSeq i j + uSeq i j) +
                (alphaOf i + uSeq i (j + 1)) := by ac_rfl
          _ = uSeq i (j + 1) + alphaOf i := by
            rw [CharTwo.add_self_eq_zero, zero_add, add_comm]
  have hclaim17 : ∀ (i : ValidIndex) (j : ℕ),
      1 ≤ j → j ≤ m - 1 →
      f (omega (i : ℕ) * center (uSeq i j)) =
        rightConjugateElem
          (omega (i : ℕ) * center (uSeq i j + alphaOf i)) (dSeq i j) := by
    intro i j hj hjm
    obtain ⟨_hc, hf⟩ := hformula_until i j hj
      (fun r hr hrj => huSeq_ne_before_end i r hr (hrj.trans_le hjm))
    rw [hf, hvSeq_shift i j hj hjm]
  have huSeq_ne_zero_from_two : ∀ (i : ValidIndex) (j : ℕ),
      2 ≤ j → j ≤ m - 1 → uSeq i j ≠ 0 := by
    intro i j hj hjm
    obtain ⟨r, hr⟩ : ∃ r : ℕ, j = r + 1 := by
      exact ⟨j - 1, by omega⟩
    subst j
    apply huSeq_succ_ne_zero i r
    apply huSeq_ne_before_end i r (by omega)
    omega
  have hhSeq_succ : ∀ (i : ValidIndex) (j : ℕ),
      1 ≤ j → j < m - 1 →
      h (omega (i : ℕ) * center (uSeq i (j + 1))) =
        (h (omega (i : ℕ)) * zeta⁻¹) *
          h (omega (i : ℕ) * center (uSeq i j)) *
            (zeta * (aStep i j) ^ 2) := by
    intro i j hj hjm
    let next := uSeq i (j + 1)
    let a := aStep i j
    have hu := huSeq_ne_before_end i j hj hjm
    have hnext : next ≠ 0 := huSeq_succ_ne_zero i j hu
    have ha : a ∈ K := haStep_mem i j
    let aUnit : Fˣ := unitOrOne (tau next)
    have htauNext : tau next ≠ 0 := htau_ne_zero next hnext
    have haCoord :
        (((kwIso (⟨a, Subgroup.mem_sup_left ha⟩ :
            (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
          ((aUnit : F) : E) := haStep_coord i j hnext
    have haNorm : (aUnit : F) * theta (aUnit : F) = next := by
      rw [hunitOrOne_coe _ htauNext]
      exact hnorm_tau next
    have hs_a : rightConjugateElem s a = center next := by
      rw [hs_center]
      simpa [haNorm] using hcenter_conj_K_exact a ha aUnit haCoord 1
    have haInvCoord :
        (((kwIso
            (⟨a⁻¹, Subgroup.mem_sup_left (K.inv_mem ha)⟩ :
              (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
          (((aUnit⁻¹ : Fˣ) : F) : E) := by
      let aKW : (K ⊔ W : Subgroup G) := ⟨a, Subgroup.mem_sup_left ha⟩
      have hainv :
          (⟨a⁻¹, Subgroup.mem_sup_left (K.inv_mem ha)⟩ :
              (K ⊔ W : Subgroup G)) = aKW⁻¹ := Subtype.ext rfl
      rw [hainv, map_inv]
      have hcoe := congrArg Inv.inv haCoord
      simpa [aKW] using hcoe
    have hs_a_inv : rightConjugateElem s a⁻¹ = center next⁻¹ := by
      rw [hs_center]
      have hact := hcenter_conj_K_exact a⁻¹ (K.inv_mem ha) aUnit⁻¹
        haInvCoord 1
      rw [hact]
      congr 1
      simp only [Units.val_inv_eq_inv_val, map_inv₀, mul_one]
      simpa only [mul_inv] using congrArg Inv.inv haNorm
    have hg_center : g (center next) = center next⁻¹ := by
      rw [← hs_a, (claim_1_a H D Q K V W Q0 S Q1 t s f g h hsection3
        hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H
        hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
        hcanonical_eq a ha).2, hs_a_inv]
    have hh_center : h (center next) = a ^ 2 := by
      rw [← hs_a]
      exact claim_1_b H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
        hcanonical_eq a ha
    have hinside :
        f (omega (i : ℕ)) * g (center next) =
          rightConjugateElem
            (omega (i : ℕ) * center (uSeq i j)) zeta := by
      calc
        f (omega (i : ℕ)) * g (center next) =
            rightConjugateElem
                (omega (i : ℕ) * center (alphaOf i)) zeta *
              center next⁻¹ := by rw [hfomega_alpha i, hg_center]
        _ = rightConjugateElem
              (omega (i : ℕ) * center (uSeq i j)) zeta := by
          rw [← hcenter_conj_W zeta hzeta next⁻¹]
          rw [← hrightConjugateElem_mul]
          rw [mul_assoc, ← hcenter_add]
          congr 1
          have hrec := (hseq i).2.2.2.1 j hu
          change next = (alphaOf i + uSeq i j)⁻¹ at hrec
          have hinv := congrArg Inv.inv hrec
          have hnextInv : next⁻¹ = alphaOf i + uSeq i j := by
            simpa only [inv_inv] using hinv
          rw [hnextInv, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have hprevQ : omega (i : ℕ) * center (uSeq i j) ∈ Q :=
      Q.mul_mem (homega_valid i).1 (hsec.Q0_le_Q (hcenter_mem_Q0 _))
    have hprevNotQ0 : omega (i : ℕ) * center (uSeq i j) ∉ Q0 := by
      intro hprod
      apply (homega_valid i).2
      have heq : omega (i : ℕ) =
          (omega (i : ℕ) * center (uSeq i j)) * (center (uSeq i j))⁻¹ := by
        simp [mul_assoc]
      rw [heq]
      exact Q0.mul_mem hprod (Q0.inv_mem (hcenter_mem_Q0 _))
    have hh_inside :
        h (f (omega (i : ℕ)) * g (center next)) =
          zeta⁻¹ * h (omega (i : ℕ) * center (uSeq i j)) * zeta := by
      rw [hinside]
      simpa [hzeta_t] using
        PFchapter4section1.claim_H4_a H Q D t f g h
          htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
          hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq (omega (i : ℕ) * center (uSeq i j)) zeta
          hprevQ (fun hone => hprevNotQ0 (hone ▸ Q0.one_mem)) hzetaD
    have homega_ne : omega (i : ℕ) ≠ 1 :=
      fun hone => (homega_valid i).2 (hone ▸ Q0.one_mem)
    have hcenter_ne : center next ≠ 1 := by
      intro hone
      apply hnext
      apply hcenter_injective
      rw [hcenter_zero, hone]
    have hprod_ne : omega (i : ℕ) * center next ≠ 1 := by
      intro hone
      apply (homega_valid i).2
      have homega_eq : omega (i : ℕ) = (center next)⁻¹ :=
        eq_inv_of_mul_eq_one_left hone
      rw [homega_eq]
      exact Q0.inv_mem (hcenter_mem_Q0 _)
    have hh6 := PFchapter4section1.claim_H6_c H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (omega (i : ℕ)) (center next) (homega_valid i).1
      (hsec.Q0_le_Q (hcenter_mem_Q0 _)) homega_ne hcenter_ne hprod_ne
    rw [hh6, hh_inside, hh_center]
    dsimp only [a]
    group
  let rSeq (i : ValidIndex) (j : ℕ) : G :=
    zeta ^ j * (kOf (unitOrOne (cSeq i j)))⁻¹
  have hkSeq_succ : ∀ (i : ValidIndex) (j : ℕ),
      1 ≤ j → j < m - 1 →
      kOf (unitOrOne (cSeq i (j + 1))) =
        kOf (unitOrOne (cSeq i j)) * (aStep i j)⁻¹ ^ 2 := by
    intro i j hj hjm
    have hu := huSeq_ne_before_end i j hj hjm
    have hc := hcSeq_ne_zero_to_end i j hj (by omega)
    have hd := hdSeq_succ i j hu hc
    let kNow := kOf (unitOrOne (cSeq i j))
    let kNext := kOf (unitOrOne (cSeq i (j + 1)))
    let a := aStep i j
    have hkz : Commute kNow zeta :=
      hKW_commute kNow zeta
        (Subgroup.mem_sup_left (hkOf_mem _)) (Subgroup.mem_sup_right hzeta)
    have hright :
        (zeta ^ j * kNow) * zeta * a⁻¹ ^ 2 =
          zeta ^ (j + 1) * (kNow * a⁻¹ ^ 2) := by
      rw [pow_succ zeta j]
      calc
        (zeta ^ j * kNow) * zeta * a⁻¹ ^ 2 =
            zeta ^ j * (kNow * zeta) * a⁻¹ ^ 2 := by
          simp only [mul_assoc]
        _ = zeta ^ j * (zeta * kNow) * a⁻¹ ^ 2 := by rw [hkz.eq]
        _ = (zeta ^ j * zeta) * (kNow * a⁻¹ ^ 2) := by
          simp only [mul_assoc]
    change zeta ^ (j + 1) * kNext =
      (zeta ^ j * kNow) * zeta * a⁻¹ ^ 2 at hd
    rw [hright] at hd
    exact mul_left_cancel hd
  have hrSeq_succ : ∀ (i : ValidIndex) (j : ℕ),
      1 ≤ j → j < m - 1 →
        rSeq i (j + 1) = rSeq i j * zeta * (aStep i j) ^ 2 := by
    intro i j hj hjm
    let kNow := kOf (unitOrOne (cSeq i j))
    let a := aStep i j
    have hkz : Commute kNow⁻¹ zeta :=
      (hKW_commute kNow zeta
        (Subgroup.mem_sup_left (hkOf_mem _)) (Subgroup.mem_sup_right hzeta)).inv_left
    have hka : Commute kNow⁻¹ (a ^ 2) :=
      (hKW_commute kNow a
        (Subgroup.mem_sup_left (hkOf_mem _))
        (Subgroup.mem_sup_left (haStep_mem i j))).inv_left.pow_right 2
    change
      zeta ^ (j + 1) * (kOf (unitOrOne (cSeq i (j + 1))))⁻¹ =
        (zeta ^ j * (kOf (unitOrOne (cSeq i j)))⁻¹) * zeta *
          (aStep i j) ^ 2
    rw [hkSeq_succ i j hj hjm]
    change zeta ^ (j + 1) * (kNow * a⁻¹ ^ 2)⁻¹ =
      (zeta ^ j * kNow⁻¹) * zeta * a ^ 2
    calc
      zeta ^ (j + 1) * (kNow * a⁻¹ ^ 2)⁻¹ =
          zeta ^ j * zeta * (a ^ 2 * kNow⁻¹) := by
        simp [pow_succ, mul_inv_rev, mul_assoc]
      _ = (zeta ^ j * kNow⁻¹) * zeta * a ^ 2 := by
        symm
        calc
          (zeta ^ j * kNow⁻¹) * zeta * a ^ 2 =
              zeta ^ j * (kNow⁻¹ * zeta) * a ^ 2 := by
            simp [mul_assoc]
          _ = zeta ^ j * (zeta * kNow⁻¹) * a ^ 2 := by rw [hkz.eq]
          _ = zeta ^ j * zeta * (kNow⁻¹ * a ^ 2) := by
            simp [mul_assoc]
          _ = zeta ^ j * zeta * (a ^ 2 * kNow⁻¹) := by rw [hka.eq]
  have hhSeq_formula : ∀ (i : ValidIndex) (j : ℕ),
      1 ≤ j → j ≤ m - 1 →
      h (omega (i : ℕ) * center (uSeq i j)) =
        (h (omega (i : ℕ)) * zeta⁻¹) ^ j * rSeq i j := by
    intro i j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    induction k with
    | zero =>
        intro _hm
        have hrOne : rSeq i 1 = zeta := by
          simp [rSeq, (hseq i).2.2.1, unitOrOne, hkOf_one]
        rw [(hseq i).1, hcenter_zero, mul_one, hrOne]
        simp
    | succ k ih =>
        intro hbound
        let j := 1 + k
        have hj : 1 ≤ j := by omega
        have hjm : j < m - 1 := by omega
        have hprev := ih (by omega) (by omega : j ≤ m - 1)
        change h (omega (i : ℕ) * center (uSeq i j)) =
          (h (omega (i : ℕ)) * zeta⁻¹) ^ j * rSeq i j at hprev
        change h (omega (i : ℕ) * center (uSeq i (j + 1))) =
          (h (omega (i : ℕ)) * zeta⁻¹) ^ (j + 1) * rSeq i (j + 1)
        rw [hhSeq_succ i j hj hjm, hprev, hrSeq_succ i j hj hjm]
        rw [pow_succ']
        group
  have hzeta_pred : zeta ^ (m - 1) = zeta⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc
      zeta ^ (m - 1) * zeta = zeta ^ (m - 1 + 1) := (pow_succ _ _).symm
      _ = zeta ^ m := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
      _ = 1 := by rw [← hzeta_order, pow_orderOf_eq_one]
  have hrSeq_end : ∀ i : ValidIndex, rSeq i (m - 1) = zeta⁻¹ := by
    intro i
    let cUnit : Fˣ := unitOrOne (cSeq i (m - 1))
    have hdEnd : dSeq i (m - 1) = zeta⁻¹ := by
      rw [← hstop_eq i]
      exact hd_stop i
    have hkOne : kOf cUnit = 1 := by
      change zeta ^ (m - 1) * kOf cUnit = zeta⁻¹ at hdEnd
      rw [hzeta_pred] at hdEnd
      apply mul_left_cancel (a := zeta⁻¹)
      simpa using hdEnd
    simp [rSeq, cUnit, hzeta_pred, hkOne]
  have hh_terminal : ∀ i : ValidIndex,
      h (omega (i : ℕ) * center (alphaOf i)) =
        (h (omega (i : ℕ)) * zeta⁻¹) ^ (m - 1) * zeta⁻¹ := by
    intro i
    have huEnd : uSeq i (m - 1) = alphaOf i := by
      rw [← hstop_eq i]
      exact (hstop_spec i).2.2
    simpa [huEnd, hrSeq_end i] using
      hhSeq_formula i (m - 1) (by omega) (by omega)
  have hclaim18 : ∀ i : ValidIndex,
      (h (omega (i : ℕ)) * zeta⁻¹) ^ m = 1 := by
    intro i
    have homega_ne : omega (i : ℕ) ≠ 1 :=
      fun hone => (homega_valid i).2 (hone ▸ Q0.one_mem)
    have hfomega_mem := hf_mem (omega (i : ℕ)) (homega_valid i).1 homega_ne
    have hconj_back :
        rightConjugateElem (f (omega (i : ℕ))) zeta⁻¹ =
          omega (i : ℕ) * center (alphaOf i) := by
      rw [hfomega_alpha i]
      simp [rightConjugateElem, mul_assoc]
      rfl
    have hzeta_inv_t : rightConjugateElem zeta⁻¹ t = zeta⁻¹ := by
      simpa [rightConjugateElem, mul_assoc] using congrArg Inv.inv hzeta_t
    have hh_conjugate :=
      PFchapter4section1.claim_H4_a H Q D t f g h
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
        hcanonical_eq (f (omega (i : ℕ))) zeta⁻¹ hfomega_mem.1
        hfomega_mem.2 (D.inv_mem hzetaD)
    have hh_fomega :=
      PFchapter4section1.claim_H4_c H Q D t f g h
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
        hcanonical_eq (omega (i : ℕ)) (homega_valid i).1 homega_ne
    have hterminal_comparison :
        h (omega (i : ℕ) * center (alphaOf i)) =
          zeta * (h (omega (i : ℕ)))⁻¹ * zeta⁻¹ := by
      rw [← hconj_back, hh_conjugate, hzeta_inv_t, hh_fomega]
      simp
    have hprev : (h (omega (i : ℕ)) * zeta⁻¹) ^ (m - 1) =
        (h (omega (i : ℕ)) * zeta⁻¹)⁻¹ := by
      calc
        (h (omega (i : ℕ)) * zeta⁻¹) ^ (m - 1) =
            ((h (omega (i : ℕ)) * zeta⁻¹) ^ (m - 1) * zeta⁻¹) *
              zeta := by group
        _ = (zeta * (h (omega (i : ℕ)))⁻¹ * zeta⁻¹) * zeta := by
          rw [← hh_terminal i, hterminal_comparison]
        _ = (h (omega (i : ℕ)) * zeta⁻¹)⁻¹ := by group
    calc
      (h (omega (i : ℕ)) * zeta⁻¹) ^ m =
          (h (omega (i : ℕ)) * zeta⁻¹) ^ (m - 1 + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
      _ = (h (omega (i : ℕ)) * zeta⁻¹) ^ (m - 1) *
          (h (omega (i : ℕ)) * zeta⁻¹) := by rw [pow_succ]
      _ = (h (omega (i : ℕ)) * zeta⁻¹)⁻¹ *
          (h (omega (i : ℕ)) * zeta⁻¹) := by rw [hprev]
      _ = 1 := inv_mul_cancel _
  have hQ0_stable_D : ∀ d : D, ∀ q : Q0,
      rightConjugateElem (q : G) (d : G)⁻¹ ∈ Q0 := by
    intro d q
    rcases (hsec.Q0_def (q : G)).1 q.property with hq_one | ⟨hqH, hqI⟩
    · rw [hq_one]
      simp [rightConjugateElem]
    · apply (hsec.Q0_def _).2
      refine Or.inr ⟨?_, isInvolution_rightConjugateElem hqI⟩
      have hdH : (d : G) ∈ H := hsec.hA.A1.D_le_H d.property
      exact H.mul_mem
        (H.mul_mem (H.inv_mem (H.inv_mem hdH)) hqH) (H.inv_mem hdH)
  letI : IsZGroup D :=
    isZGroup_of_fixedPointFree_quotient H D Q Q0
      hsec.hA.A1.D_le_H hsec.hA.A1.Q_le_H hQ_normal_in_H hsec.Q0_le_Q
      hQ0_commutes_Q hQ0_stable_D hsec.hA.A1.D_odd hD_fixed_point_free
      x hxQ hx_not_Q0
  have hV_le_D : V ≤ D := by
    rw [hsec.V_eq]
    exact inf_le_left
  have hW_le_D : W ≤ D := hsec.W_le_V.trans hV_le_D
  letI : (W.subgroupOf D).Normal :=
    _root_.CFSG.BenderSuzuki.PFchapter1section2.peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_normal_D
        H D Q K V W t hsec.hA.A1 hsec.K_def hsec.V_eq hsec.W_le_V
        hsec.W_eq hV_le_D
  have hh_mem_W : ∀ i : ValidIndex, h (omega (i : ℕ)) ∈ W := by
    intro i
    have homega_ne : omega (i : ℕ) ≠ 1 :=
      fun hone => (homega_valid i).2 (hone ▸ Q0.one_mem)
    have hhD : h (omega (i : ℕ)) ∈ D :=
      hh_mem (omega (i : ℕ)) (homega_valid i).1 homega_ne
    let a : D := ⟨h (omega (i : ℕ)) * zeta⁻¹,
      D.mul_mem hhD (D.inv_mem hzetaD)⟩
    have ha_pow : a ^ Nat.card (W.subgroupOf D) = 1 := by
      apply Subtype.ext
      change (h (omega (i : ℕ)) * zeta⁻¹) ^ Nat.card (W.subgroupOf D) = 1
      have hcard : Nat.card (W.subgroupOf D) = m := by
        rw [show m = Nat.card W from rfl]
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := W) (K := D) hW_le_D).toEquiv
      rw [hcard]
      exact hclaim18 i
    have haW : a ∈ W.subgroupOf D :=
      mem_normal_of_pow_card_eq_one_of_isZGroup (W.subgroupOf D) ha_pow
    have hprodW : h (omega (i : ℕ)) * zeta⁻¹ ∈ W := haW
    have heq : h (omega (i : ℕ)) =
        (h (omega (i : ℕ)) * zeta⁻¹) * zeta := by group
    rw [heq]
    exact W.mul_mem hprodW hzeta
  let liftK : Fˣ → K := fun b ↦ ⟨kOf b, hkOf_mem b⟩
  have hliftK_bijective : Function.Bijective liftK := by
    constructor
    · intro b c hbc
      have hval : kOf b = kOf c := congrArg (fun a : K ↦ (a : G)) hbc
      let bKW : (K ⊔ W : Subgroup G) :=
        ⟨kOf b, Subgroup.mem_sup_left (hkOf_mem b)⟩
      let cKW : (K ⊔ W : Subgroup G) :=
        ⟨kOf c, Subgroup.mem_sup_left (hkOf_mem c)⟩
      have hbcKW : bKW = cKW := Subtype.ext hval
      have himage := congrArg
        (fun a : (K ⊔ W : Subgroup G) ↦
          ((((kwIso a : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E))) hbcKW
      apply Units.ext
      apply F.subtype.injective
      simpa [bKW, cKW, hkOf_coord] using himage
    · intro a
      obtain ⟨b, hb⟩ := hK_scalar (a : G) a.property
      let kKW : (K ⊔ W : Subgroup G) :=
        ⟨kOf b, Subgroup.mem_sup_left (hkOf_mem b)⟩
      let aKW : (K ⊔ W : Subgroup G) :=
        ⟨(a : G), Subgroup.mem_sup_left a.property⟩
      have himage : kwIso kKW = kwIso aKW := by
        apply Subtype.ext
        apply Units.ext
        calc
          ((((kwIso kKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E)) =
              ((b : F) : E) := hkOf_coord b
          _ = ((((kwIso aKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E)) := hb.symm
      have hka : kKW = aKW := kwIso.injective himage
      refine ⟨b, ?_⟩
      apply Subtype.ext
      exact congrArg (fun x : (K ⊔ W : Subgroup G) ↦ (x : G)) hka
  let kEquiv : Fˣ ≃ K := Equiv.ofBijective liftK hliftK_bijective
  have hcardK : Nat.card K = Nat.card Q0 - 1 := by
    calc
      Nat.card K = Nat.card Fˣ := (Nat.card_congr kEquiv).symm
      _ = Nat.card F - 1 := Nat.card_units (F)
      _ = Nat.card Q0 - 1 := by rw [hcardF]
  have hW_centralizes_K : W ≤ Subgroup.centralizer (K : Set G) := by
    intro w hw
    rw [hsec.W_eq] at hw
    exact hw.2
  have hW_normalizes_K : W ≤ Subgroup.normalizer (K : Set G) :=
    hW_centralizes_K.trans (centralizer_le_normalizer K)
  let mulKW : K × W → KW := fun p ↦
    ⟨(p.1 : G) * (p.2 : G), by
      rw [hKW]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.property)
        (Subgroup.mem_sup_right p.2.property)⟩
  have hmulKW_bijective : Function.Bijective mulKW := by
    constructor
    · rintro ⟨k₁, w₁⟩ ⟨k₂, w₂⟩ hp
      have hval : (k₁ : G) * (w₁ : G) = (k₂ : G) * (w₂ : G) :=
        congrArg (fun a : KW ↦ (a : G)) hp
      have hcross : (k₂ : G)⁻¹ * (k₁ : G) =
          (w₂ : G) * (w₁ : G)⁻¹ := by
        calc
          (k₂ : G)⁻¹ * (k₁ : G) =
              (k₂ : G)⁻¹ * ((k₁ : G) * (w₁ : G)) * (w₁ : G)⁻¹ := by
            simp [mul_assoc]
          _ = (k₂ : G)⁻¹ * ((k₂ : G) * (w₂ : G)) * (w₁ : G)⁻¹ := by
            rw [hval]
          _ = (w₂ : G) * (w₁ : G)⁻¹ := by simp
      have hcrossK : (k₂ : G)⁻¹ * (k₁ : G) ∈ K :=
        K.mul_mem (K.inv_mem k₂.property) k₁.property
      have hcrossW : (k₂ : G)⁻¹ * (k₁ : G) ∈ W := by
        rw [hcross]
        exact W.mul_mem w₂.property (W.inv_mem w₁.property)
      have hcrossOne := hK_inter_W _ hcrossK hcrossW
      have hk : (k₁ : G) = (k₂ : G) := by
        calc
          (k₁ : G) = (k₂ : G) * ((k₂ : G)⁻¹ * (k₁ : G)) := by group
          _ = (k₂ : G) * 1 := by rw [hcrossOne]
          _ = (k₂ : G) := mul_one _
      have hw : (w₁ : G) = (w₂ : G) := by
        rw [hk] at hval
        exact mul_left_cancel hval
      exact Prod.ext (Subtype.ext hk) (Subtype.ext hw)
    · intro d
      have hdSup : (d : G) ∈ K ⊔ W := by simpa [hKW] using d.property
      change (d : G) ∈ ((K ⊔ W : Subgroup G) : Set G) at hdSup
      rw [Subgroup.coe_mul_of_right_le_normalizer_left K W hW_normalizes_K] at hdSup
      rcases Set.mem_mul.mp hdSup with ⟨k, hk, w, hw, hkw⟩
      exact ⟨(⟨k, hk⟩, ⟨w, hw⟩), Subtype.ext hkw⟩
  let kwEquiv : K × W ≃ KW := Equiv.ofBijective mulKW hmulKW_bijective
  have hcardKW : Nat.card KW = (Nat.card Q0 - 1) * m := by
    calc
      Nat.card KW = Nat.card (K × W) := (Nat.card_congr kwEquiv).symm
      _ = Nat.card K * Nat.card W := Nat.card_prod K W
      _ = (Nat.card Q0 - 1) * m := by rw [hcardK]
  have hsQ0 : s ∈ Q0 :=
    (hsec.Q0_def s).2 (Or.inr ⟨hsection3.2.1, hsection3.2.2.1⟩)
  have hcardQ0_two : 2 ≤ Nat.card Q0 := by
    let embed : Bool → Q0 := fun b ↦ if b then ⟨s, hsQ0⟩ else 1
    have hembed : Function.Injective embed := by
      intro a b hab
      cases a <;> cases b
      · rfl
      · exfalso
        have hsone : s = 1 := by
          simpa [embed] using congrArg (fun q : Q0 ↦ (q : G)) hab.symm
        exact hsection3.2.2.1.ne_one hsone
      · exfalso
        have hsone : s = 1 := by
          simpa [embed] using congrArg (fun q : Q0 ↦ (q : G)) hab
        exact hsection3.2.2.1.ne_one hsone
      · rfl
    simpa using Nat.card_le_card_of_injective embed hembed
  let Q0Q : Subgroup Q := Q0.subgroupOf Q
  have hQ0Q_normal : Q0Q.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hsec.Q0_le_Q).2
    intro q hqQ
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyQ0
      have hcomm := hQ0_commutes_Q y hyQ0 q hqQ
      have hconj : q * y * q⁻¹ = y := by
        rw [← hcomm]
        simp
      simpa [hconj] using hyQ0
    · intro hyQ0
      have hcomm := hQ0_commutes_Q (q * y * q⁻¹) hyQ0 q hqQ
      have hy_eq : y = q * y * q⁻¹ := by
        calc
          y = q⁻¹ * (q * y * q⁻¹) * q := by group
          _ = q⁻¹ * ((q * y * q⁻¹) * q) := by rw [mul_assoc]
          _ = q⁻¹ * (q * (q * y * q⁻¹)) := by rw [hcomm]
          _ = q * y * q⁻¹ := by group
      rwa [hy_eq]
  letI : Q0Q.Normal := hQ0Q_normal
  have hD_normalizes_Q : D ≤ Subgroup.normalizer Q :=
    hsec.hA.A1.D_le_H.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hsec.hA.A1.Q_le_H).1
        hQ_normal_in_H)
  letI : MulDistribMulAction D Q :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) D Q hD_normalizes_Q
  have hD_smul_coe : ∀ (d : D) (q : Q),
      ((d • q : Q) : G) = (d : G) * (q : G) * (d : G)⁻¹ := by
    intro d q
    exact
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
        D Q hD_normalizes_Q d q
  have hQ0Q_invariant : IsInvariant D Q Q0Q := by
    refine ⟨?_⟩
    have hforward : ∀ (d : D) (q : Q), q ∈ Q0Q → d • q ∈ Q0Q := by
      intro d q hq
      have hstable := hQ0_stable_D d ⟨q, hq⟩
      change (d : G) * (q : G) * (d : G)⁻¹ ∈ Q0
      simpa [rightConjugateElem, mul_assoc] using hstable
    intro d q
    constructor
    · exact hforward d q
    · intro hdq
      have hinv : d⁻¹ • (d • q) ∈ Q0Q := hforward d⁻¹ (d • q) hdq
      simpa using hinv
  letI : MulAction.QuotientAction D Q0Q :=
    quotientAction_of_isInvariant (A := D) (G := Q) Q0Q hQ0Q_invariant
  letI : MulDistribMulAction D (Q ⧸ Q0Q) :=
    quotientMulDistribMulAction (A := D) (G := Q) Q0Q hQ0Q_invariant
  have hquotient_card : Nat.card (Q ⧸ Q0Q) = Nat.card Q0 ^ 2 := by
    have hcardQ := natCard_eq_cube_of_isSuzukiTwoTypeB H Q Q0 S
      hC2.S_type_B hsec.S_le_Q hsec.hA.A1.Q_le_H hsec.Q0_le_Q hsec.Q0_def hSQ
    have hcardQ0Q : Nat.card Q0Q = Nat.card Q0 :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := Q0) (K := Q) hsec.Q0_le_Q).toEquiv
    have hprod : Nat.card (Q ⧸ Q0Q) * Nat.card Q0 =
        Nat.card Q0 ^ 2 * Nat.card Q0 := by
      calc
        Nat.card (Q ⧸ Q0Q) * Nat.card Q0 =
            Nat.card (Q ⧸ Q0Q) * Nat.card Q0Q := by rw [hcardQ0Q]
        _ = Nat.card Q :=
          (Subgroup.card_eq_card_quotient_mul_card_subgroup Q0Q).symm
        _ = Nat.card Q0 ^ 3 := hcardQ
        _ = Nat.card Q0 ^ 2 * Nat.card Q0 := by ring
    apply Nat.mul_right_cancel (Nat.card_pos (α := Q0))
    exact hprod
  have hquotient_fixed : ∀ d : D, d ≠ 1 → ∀ qbar : Q ⧸ Q0Q,
      d • qbar = qbar → qbar = 1 := by
    intro d hd qbar hfix
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective Q0Q qbar
    change (q : Q ⧸ Q0Q) = 1
    rw [QuotientGroup.eq_one_iff]
    by_contra hqQ0
    apply hD_fixed_point_free (d : G)⁻¹ (D.inv_mem d.property)
    · intro hdG
      apply hd
      apply Subtype.ext
      simpa using congrArg Inv.inv hdG
    · exact q.property
    · exact hqQ0
    · have hquot :
          QuotientGroup.mk' Q0Q (d • q) = QuotientGroup.mk' Q0Q q := by
        simpa using hfix
      have hdiv : (d • q) / q ∈ Q0Q :=
        (QuotientGroup.eq_iff_div_mem).1 hquot
      have hdivG : (((d • q) / q : Q) : G) ∈ Q0 := hdiv
      have hsmul : ((d • q : Q) : G) =
          (d : G) * (q : G) * (d : G)⁻¹ := by rfl
      simpa only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv,
        hsmul, div_eq_mul_inv, rightConjugateElem, inv_inv, mul_assoc] using hdivG
  have hKW_le_D : KW ≤ D := by
    rw [hKW]
    exact sup_le hsec.K_le_D hW_le_D
  let omegaQ (i : ValidIndex) : Q :=
    ⟨omega (i : ℕ), (homega_valid i).1⟩
  let kwD (a : KW) : D := ⟨(a : G), hKW_le_D a.property⟩
  let QuotientNontrivial := {qbar : Q ⧸ Q0Q // qbar ≠ 1}
  let orbitMap : ValidIndex × KW → QuotientNontrivial := fun p ↦
    ⟨(kwD p.2)⁻¹ • QuotientGroup.mk' Q0Q (omegaQ p.1), by
      intro hone
      have homega_one : QuotientGroup.mk' Q0Q (omegaQ p.1) = 1 := by
        calc
          QuotientGroup.mk' Q0Q (omegaQ p.1) =
              kwD p.2 • ((kwD p.2)⁻¹ • QuotientGroup.mk' Q0Q (omegaQ p.1)) := by
            simp
          _ = kwD p.2 • 1 := by rw [hone]
          _ = 1 := by simp
      exact (homega_valid p.1).2
        ((QuotientGroup.eq_one_iff (omegaQ p.1)).1 homega_one)⟩
  have horbitMap_surjective : Function.Surjective orbitMap := by
    intro qbar
    obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective Q0Q (qbar : Q ⧸ Q0Q)
    have hq_not_Q0 : (q : G) ∉ Q0 := by
      intro hqQ0
      apply qbar.property
      rw [← hq]
      exact (QuotientGroup.eq_one_iff q).2 hqQ0
    obtain ⟨j, hj_one, hj_n, d, q0, hdKW, hq0, hq_rep⟩ :=
      horbit_representatives.2.1 (q : G) q.property hq_not_Q0
    let i : ValidIndex := ⟨j, hj_one, hj_n⟩
    let dKW : KW := ⟨d, hdKW⟩
    let dD : D := kwD dKW
    let q0Q : Q := ⟨q0, hsec.Q0_le_Q hq0⟩
    let conjugateQ : Q := dD⁻¹ • omegaQ i
    have hq_eq : q = conjugateQ * q0Q := by
      apply Subtype.ext
      change (q : G) = (conjugateQ : G) * (q0Q : G)
      rw [show (conjugateQ : G) =
          (dD⁻¹ : D) * (omegaQ i : Q) * (dD⁻¹ : D)⁻¹ from
        hD_smul_coe dD⁻¹ (omegaQ i)]
      simpa [q0Q, dD, dKW, kwD, omegaQ, i,
        rightConjugateElem, mul_assoc] using hq_rep
    refine ⟨(i, dKW), Subtype.ext ?_⟩
    rw [← hq]
    change QuotientGroup.mk' Q0Q conjugateQ = QuotientGroup.mk' Q0Q q
    change (conjugateQ : Q ⧸ Q0Q) = (q : Q ⧸ Q0Q)
    rw [QuotientGroup.eq_iff_div_mem, hq_eq]
    have hnormal := hQ0Q_normal.conj_mem q0Q⁻¹
      (show q0Q⁻¹ ∈ Q0Q from Q0.inv_mem hq0) conjugateQ
    simpa [div_eq_mul_inv, mul_assoc] using hnormal
  have horbitMap_injective : Function.Injective orbitMap := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    have hbar :
        (kwD a)⁻¹ • QuotientGroup.mk' Q0Q (omegaQ i) =
          (kwD b)⁻¹ • QuotientGroup.mk' Q0Q (omegaQ j) :=
      congrArg (fun q : QuotientNontrivial ↦ (q : Q ⧸ Q0Q)) hab
    let relativeKW : KW := ⟨(b : G) * (a : G)⁻¹,
      KW.mul_mem b.property (KW.inv_mem a.property)⟩
    let relativeD : D := kwD relativeKW
    have hrelativeD : relativeD⁻¹ = kwD a * (kwD b)⁻¹ := by
      apply Subtype.ext
      simp [relativeD, relativeKW, kwD]
    have hindices_bar : QuotientGroup.mk' Q0Q (omegaQ i) =
        relativeD⁻¹ • QuotientGroup.mk' Q0Q (omegaQ j) := by
      calc
        QuotientGroup.mk' Q0Q (omegaQ i) =
            kwD a • ((kwD a)⁻¹ • QuotientGroup.mk' Q0Q (omegaQ i)) := by
          simp
        _ = kwD a • ((kwD b)⁻¹ • QuotientGroup.mk' Q0Q (omegaQ j)) := by
          rw [hbar]
        _ = (kwD a * (kwD b)⁻¹) • QuotientGroup.mk' Q0Q (omegaQ j) := by
          rw [mul_smul]
        _ = relativeD⁻¹ • QuotientGroup.mk' Q0Q (omegaQ j) := by
          rw [hrelativeD]
    let conjugateQ : Q := relativeD⁻¹ • omegaQ j
    have hquot_indices : QuotientGroup.mk' Q0Q (omegaQ i) =
        QuotientGroup.mk' Q0Q conjugateQ := by
      simpa [conjugateQ] using hindices_bar
    have hdiv : omegaQ i / conjugateQ ∈ Q0Q :=
      (QuotientGroup.eq_iff_div_mem).1 hquot_indices
    let q0 : G := ((omegaQ i / conjugateQ : Q) : G)
    have hq0 : q0 ∈ Q0 := hdiv
    have hconjugateQ_mem : (conjugateQ : G) ∈ Q := conjugateQ.property
    have hcomm : q0 * (conjugateQ : G) = (conjugateQ : G) * q0 :=
      hQ0_commutes_Q q0 hq0 (conjugateQ : G) hconjugateQ_mem
    have hconjugateQ_coe : (conjugateQ : G) =
        rightConjugateElem (omega (j : ℕ)) (relativeKW : G) := by
      rw [show (conjugateQ : G) =
          (relativeD⁻¹ : D) * (omegaQ j : Q) * (relativeD⁻¹ : D)⁻¹ from
        hD_smul_coe relativeD⁻¹ (omegaQ j)]
      simp [relativeD, relativeKW, kwD, omegaQ, rightConjugateElem, mul_assoc]
    have homega_eq : omega (i : ℕ) =
        rightConjugateElem (omega (j : ℕ)) (relativeKW : G) * q0 := by
      calc
        omega (i : ℕ) = (omegaQ i : G) := rfl
        _ = (conjugateQ : G) * q0 := by
          symm
          calc
            (conjugateQ : G) * q0 = q0 * (conjugateQ : G) := hcomm.symm
            _ = (omegaQ i : G) := by
              simp [q0, div_eq_mul_inv, mul_assoc]
        _ = rightConjugateElem (omega (j : ℕ)) (relativeKW : G) * q0 := by
          rw [hconjugateQ_coe]
    have hij_nat : (i : ℕ) = (j : ℕ) :=
      horbit_representatives.2.2 (i : ℕ) (j : ℕ)
        i.property.1 i.property.2 j.property.1 j.property.2
        ⟨(relativeKW : G), q0, relativeKW.property, hq0, homega_eq⟩
    have hij : i = j := Subtype.ext hij_nat
    subst j
    have homega_bar_ne : QuotientGroup.mk' Q0Q (omegaQ i) ≠ 1 := by
      intro hone
      exact (homega_valid i).2 ((QuotientGroup.eq_one_iff (omegaQ i)).1 hone)
    let fixedD : D := kwD a * (kwD b)⁻¹
    have hfixed : fixedD • QuotientGroup.mk' Q0Q (omegaQ i) =
        QuotientGroup.mk' Q0Q (omegaQ i) := by
      calc
        fixedD • QuotientGroup.mk' Q0Q (omegaQ i) =
            kwD a • ((kwD b)⁻¹ • QuotientGroup.mk' Q0Q (omegaQ i)) := by
          rw [mul_smul]
        _ = kwD a • ((kwD a)⁻¹ • QuotientGroup.mk' Q0Q (omegaQ i)) := by
          rw [← hbar]
        _ = QuotientGroup.mk' Q0Q (omegaQ i) := by simp
    have hfixed_one : fixedD = 1 := by
      by_contra hne
      exact homega_bar_ne (hquotient_fixed fixedD hne _ hfixed)
    have habD : kwD a = kwD b := by
      apply mul_inv_eq_one.mp hfixed_one
    have habKW : a = b := by
      apply Subtype.ext
      exact congrArg (fun d : D ↦ (d : G)) habD
    exact Prod.ext rfl habKW
  let orbitEquiv : ValidIndex × KW ≃ QuotientNontrivial :=
    Equiv.ofBijective orbitMap ⟨horbitMap_injective, horbitMap_surjective⟩
  have hcardValid : Nat.card ValidIndex = n := by
    let validEquiv : {i : ℕ // 1 ≤ i ∧ i ≤ n} ≃ Fin n := {
      toFun i := ⟨(i : ℕ) - 1, by omega⟩
      invFun j := ⟨(j : ℕ) + 1, by omega⟩
      left_inv i := by
        apply Subtype.ext
        exact Nat.sub_add_cancel i.property.1
      right_inv j := by
        apply Fin.ext
        simp }
    calc
      Nat.card ValidIndex = Nat.card (Fin n) := by
        apply Nat.card_congr
        simpa [ValidIndex] using validEquiv
      _ = n := Nat.card_fin n
  have hcardQuotientNontrivial :
      Nat.card QuotientNontrivial = Nat.card (Q ⧸ Q0Q) - 1 := by
    letI := Fintype.ofFinite (Q ⧸ Q0Q)
    simp [QuotientNontrivial, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl]
  have horbit_card : n * ((Nat.card Q0 - 1) * m) = Nat.card Q0 ^ 2 - 1 := by
    calc
      n * ((Nat.card Q0 - 1) * m) = Nat.card ValidIndex * Nat.card KW := by
        rw [hcardValid, hcardKW]
      _ = Nat.card (ValidIndex × KW) := (Nat.card_prod ValidIndex KW).symm
      _ = Nat.card QuotientNontrivial := Nat.card_congr orbitEquiv
      _ = Nat.card (Q ⧸ Q0Q) - 1 := hcardQuotientNontrivial
      _ = Nat.card Q0 ^ 2 - 1 := by rw [hquotient_card]
  have hn_card : n * m = Nat.card Q0 + 1 := by
    have hfactor : Nat.card Q0 ^ 2 - 1 =
        (Nat.card Q0 + 1) * (Nat.card Q0 - 1) := by
      let q := Nat.card Q0 - 1
      have hq : q + 1 = Nat.card Q0 := Nat.sub_add_cancel (by omega)
      calc
        Nat.card Q0 ^ 2 - 1 = (q + 1) ^ 2 - 1 := by rw [hq]
        _ = q ^ 2 + 2 * q := by ring_nf; omega
        _ = (q + 2) * q := by ring
        _ = (Nat.card Q0 + 1) * (Nat.card Q0 - 1) := by
          rw [← hq]
          simp
    have hcancel : (n * m) * (Nat.card Q0 - 1) =
        (Nat.card Q0 + 1) * (Nat.card Q0 - 1) := by
      calc
        (n * m) * (Nat.card Q0 - 1) =
            n * ((Nat.card Q0 - 1) * m) := by ring
        _ = Nat.card Q0 ^ 2 - 1 := horbit_card
        _ = (Nat.card Q0 + 1) * (Nat.card Q0 - 1) := hfactor
    apply Nat.mul_right_cancel (by omega : 0 < Nat.card Q0 - 1)
    exact hcancel
  have hQ0_conj_D : ∀ q a : G, q ∈ Q0 → a ∈ D →
      rightConjugateElem q a ∈ Q0 := by
    intro q a hq ha
    let d : D := ⟨a⁻¹, D.inv_mem ha⟩
    have hstable := hQ0_stable_D d ⟨q, hq⟩
    simpa [d] using hstable
  have horbit_index_of_conjugates : ∀ (i j : ValidIndex) (u v : F)
      (a b : G), a ∈ KW → b ∈ KW →
      rightConjugateElem (omega (i : ℕ) * center u) a =
        rightConjugateElem (omega (j : ℕ) * center v) b → i = j := by
    intro i j u v a b ha hb heq
    let r := b * a⁻¹
    have hrKW : r ∈ KW := KW.mul_mem hb (KW.inv_mem ha)
    have hrD : r ∈ D := hKW_le_D hrKW
    let q0 := rightConjugateElem (center v) r * (center u)⁻¹
    have hq0 : q0 ∈ Q0 := Q0.mul_mem
      (hQ0_conj_D (center v) r (hcenter_mem_Q0 v) hrD)
      (Q0.inv_mem (hcenter_mem_Q0 u))
    have homega_eq : omega (i : ℕ) =
        rightConjugateElem (omega (j : ℕ)) r * q0 := by
      have heq' := congrArg (fun x : G ↦ rightConjugateElem x a⁻¹) heq
      calc
        omega (i : ℕ) =
            (omega (i : ℕ) * center u) * (center u)⁻¹ := by simp [mul_assoc]
        _ = rightConjugateElem
              (rightConjugateElem (omega (i : ℕ) * center u) a) a⁻¹ *
              (center u)⁻¹ := by simp [rightConjugateElem, mul_assoc]
        _ = rightConjugateElem
              (rightConjugateElem (omega (j : ℕ) * center v) b) a⁻¹ *
              (center u)⁻¹ := by rw [heq]
        _ = rightConjugateElem (omega (j : ℕ) * center v) r *
              (center u)⁻¹ := by
            simp [r, rightConjugateElem, mul_assoc]
        _ = rightConjugateElem (omega (j : ℕ)) r * q0 := by
            simp [q0, rightConjugateElem, mul_assoc]
    have hij := horbit_representatives.2.2 (i : ℕ) (j : ℕ)
      i.property.1 i.property.2 j.property.1 j.property.2
      ⟨r, q0, hrKW, hq0, homega_eq⟩
    exact Subtype.ext hij
  have hconjugate_exponent_unique : ∀ (i : ValidIndex) (u v : F)
      (a b : G), a ∈ KW → b ∈ KW →
      rightConjugateElem (omega (i : ℕ) * center u) a =
        rightConjugateElem (omega (i : ℕ) * center v) b → a = b := by
    intro i u v a b ha hb heq
    let aKW : KW := ⟨a, ha⟩
    let bKW : KW := ⟨b, hb⟩
    let aD : D := kwD aKW
    let bD : D := kwD bKW
    let cu : Q := ⟨center u, hsec.Q0_le_Q (hcenter_mem_Q0 u)⟩
    let cv : Q := ⟨center v, hsec.Q0_le_Q (hcenter_mem_Q0 v)⟩
    let baseU : Q := omegaQ i * cu
    let baseV : Q := omegaQ i * cv
    let conjU : Q := aD⁻¹ • baseU
    let conjV : Q := bD⁻¹ • baseV
    have hconjU : (conjU : G) =
        rightConjugateElem (omega (i : ℕ) * center u) a := by
      rw [show (conjU : G) =
          (aD⁻¹ : D) * (baseU : Q) * (aD⁻¹ : D)⁻¹ from
        hD_smul_coe aD⁻¹ baseU]
      simp [aD, aKW, kwD, baseU, omegaQ, cu, rightConjugateElem, mul_assoc]
    have hconjV : (conjV : G) =
        rightConjugateElem (omega (i : ℕ) * center v) b := by
      rw [show (conjV : G) =
          (bD⁻¹ : D) * (baseV : Q) * (bD⁻¹ : D)⁻¹ from
        hD_smul_coe bD⁻¹ baseV]
      simp [bD, bKW, kwD, baseV, omegaQ, cv, rightConjugateElem, mul_assoc]
    have hconj : conjU = conjV := by
      apply Subtype.ext
      rw [hconjU, hconjV, heq]
    have hbaseU_bar : QuotientGroup.mk' Q0Q baseU =
        QuotientGroup.mk' Q0Q (omegaQ i) := by
      change (baseU : Q ⧸ Q0Q) = (omegaQ i : Q ⧸ Q0Q)
      rw [show baseU = omegaQ i * cu from rfl]
      change (omegaQ i : Q ⧸ Q0Q) * (cu : Q ⧸ Q0Q) = _
      rw [show (cu : Q ⧸ Q0Q) = 1 from
        (QuotientGroup.eq_one_iff cu).2 (hcenter_mem_Q0 u)]
      simp
    have hbaseV_bar : QuotientGroup.mk' Q0Q baseV =
        QuotientGroup.mk' Q0Q (omegaQ i) := by
      change (baseV : Q ⧸ Q0Q) = (omegaQ i : Q ⧸ Q0Q)
      rw [show baseV = omegaQ i * cv from rfl]
      change (omegaQ i : Q ⧸ Q0Q) * (cv : Q ⧸ Q0Q) = _
      rw [show (cv : Q ⧸ Q0Q) = 1 from
        (QuotientGroup.eq_one_iff cv).2 (hcenter_mem_Q0 v)]
      simp
    have horbit_eq : orbitMap (i, aKW) = orbitMap (i, bKW) := by
      apply Subtype.ext
      change aD⁻¹ • QuotientGroup.mk' Q0Q (omegaQ i) =
        bD⁻¹ • QuotientGroup.mk' Q0Q (omegaQ i)
      calc
        aD⁻¹ • QuotientGroup.mk' Q0Q (omegaQ i) =
            aD⁻¹ • QuotientGroup.mk' Q0Q baseU := by rw [hbaseU_bar]
        _ = QuotientGroup.mk' Q0Q conjU := by rfl
        _ = QuotientGroup.mk' Q0Q conjV := by rw [hconj]
        _ = bD⁻¹ • QuotientGroup.mk' Q0Q baseV := by rfl
        _ = bD⁻¹ • QuotientGroup.mk' Q0Q (omegaQ i) := by rw [hbaseV_bar]
    have hab := congrArg Prod.snd (horbitMap_injective horbit_eq)
    exact congrArg (fun x : KW ↦ (x : G)) hab
  let aFor (x : F) : G := kOf (unitOrOne (tau x))
  have haFor_mem : ∀ x : F, aFor x ∈ K := by
    intro x
    exact hkOf_mem _
  have haFor_coord : ∀ x : F, x ≠ 0 →
      (((kwIso (⟨aFor x, Subgroup.mem_sup_left (haFor_mem x)⟩ :
          (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
        ((tau x : F) : E) := by
    intro x hx
    simpa [aFor, hunitOrOne_coe _ (htau_ne_zero x hx)] using
      hkOf_coord (unitOrOne (tau x))
  have hcenter_conj_aFor : ∀ x : F, x ≠ 0 → ∀ u : F,
      rightConjugateElem (center u) (aFor x) = center (x * u) := by
    intro x hx u
    have hcoord := haFor_coord x hx
    have hcoord' :
        (((kwIso (⟨aFor x, Subgroup.mem_sup_left (haFor_mem x)⟩ :
            (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
          (((unitOrOne (tau x) : Fˣ) : F) : E) := by
      rw [hunitOrOne_coe _ (htau_ne_zero x hx)]
      exact hcoord
    rw [hcenter_conj_K_exact (aFor x) (haFor_mem x)
      (unitOrOne (tau x))]
    · rw [hunitOrOne_coe _ (htau_ne_zero x hx), hnorm_tau]
    · exact hcoord'
  have hdSeq_index_injective : ∀ (i : ValidIndex) (j l : ℕ),
      1 ≤ j → j ≤ m - 1 → 1 ≤ l → l ≤ m - 1 →
        dSeq i j = dSeq i l → j = l := by
    intro i j l hj hjm hl hlm heq
    let r (a : ℕ) := kOf (unitOrOne (cSeq i a))
    have hrK : ∀ a : ℕ, r a ∈ K := fun a => hkOf_mem _
    have hdecomp : zeta ^ j * r j = zeta ^ l * r l := by
      simpa [dSeq, r] using heq
    let z := zeta ^ j * (zeta ^ l)⁻¹
    have hzW : z ∈ W :=
      W.mul_mem (W.pow_mem hzeta j) (W.inv_mem (W.pow_mem hzeta l))
    have hcomm_pow : Commute (zeta ^ j) (zeta ^ l)⁻¹ :=
      (hKW_commute (zeta ^ j) (zeta ^ l)
        (Subgroup.mem_sup_right (W.pow_mem hzeta j))
        (Subgroup.mem_sup_right (W.pow_mem hzeta l))).inv_right
    have hz_eq : z = r l * (r j)⁻¹ := by
      calc
        z = (zeta ^ l)⁻¹ * zeta ^ j := hcomm_pow.eq
        _ = (zeta ^ l)⁻¹ * (zeta ^ j * r j) * (r j)⁻¹ := by group
        _ = (zeta ^ l)⁻¹ * (zeta ^ l * r l) * (r j)⁻¹ := by rw [hdecomp]
        _ = r l * (r j)⁻¹ := by group
    have hzK : z ∈ K := by
      rw [hz_eq]
      exact K.mul_mem (hrK l) (K.inv_mem (hrK j))
    have hz_one : z = 1 := hK_inter_W z hzK hzW
    have hpows : zeta ^ j = zeta ^ l := by
      apply eq_of_mul_inv_eq_one
      exact hz_one
    have hmod : j ≡ l [MOD m] := by
      rw [← hzeta_order]
      exact pow_eq_pow_iff_modEq.mp hpows
    exact hmod.eq_of_lt_of_lt (by omega) (by omega)
  have huSeq_index_injective : ∀ (i : ValidIndex) (j l : ℕ),
      1 ≤ j → j ≤ m - 1 → 1 ≤ l → l ≤ m - 1 →
        uSeq i j = uSeq i l → j = l := by
    intro i j l hj hjm hl hlm hu
    have hconjugates :
        rightConjugateElem
            (omega (i : ℕ) * center (uSeq i j + alphaOf i)) (dSeq i j) =
          rightConjugateElem
            (omega (i : ℕ) * center (uSeq i l + alphaOf i)) (dSeq i l) := by
      calc
        rightConjugateElem
            (omega (i : ℕ) * center (uSeq i j + alphaOf i)) (dSeq i j) =
            f (omega (i : ℕ) * center (uSeq i j)) :=
          (hclaim17 i j hj hjm).symm
        _ = f (omega (i : ℕ) * center (uSeq i l)) := by rw [hu]
        _ = rightConjugateElem
            (omega (i : ℕ) * center (uSeq i l + alphaOf i)) (dSeq i l) :=
          hclaim17 i l hl hlm
    have hd := hconjugate_exponent_unique i
      (uSeq i j + alphaOf i) (uSeq i l + alphaOf i)
      (dSeq i j) (dSeq i l)
      (by simpa [hKW] using hdSeq_mem i j)
      (by simpa [hKW] using hdSeq_mem i l) hconjugates
    exact hdSeq_index_injective i j l hj hjm hl hlm hd
  have hclaim17_exhaustive : ∀ (i : ValidIndex) (x : F),
      (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
        f (omega (i : ℕ) * center x) =
          rightConjugateElem (omega (i : ℕ)) d * q0) →
      ∃ d : G, d ∈ KW ∧
        f (omega (i : ℕ) * center x) =
          rightConjugateElem
            (omega (i : ℕ) * center (x + alphaOf i)) d := by
    intro i x hx
    let J := {j : ℕ // j ∈ Finset.Icc 1 (m - 1)}
    have hJ_bounds : ∀ j : J, 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ m - 1 := fun j =>
      Finset.mem_Icc.mp j.property
    let Fiber := {q0 : G // q0 ∈ Q0 ∧
      (∃ d q0' : G, d ∈ KW ∧ q0' ∈ Q0 ∧
        f (omega (i : ℕ) * q0) =
          rightConjugateElem (omega (i : ℕ)) d * q0')}
    have hcardFiber : Nat.card Fiber = m - 1 := by
      have hcard := claim_8 H D Q K V W Q0 S Q1 KW
        t s (omega (i : ℕ)) f g h m n (i : ℕ) (i : ℕ) omega hsection3 hC1 hC2
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
        hcanonical_eq hKW rfl hn_card i.property i.property
        horbit_representatives rfl
      simpa [Fiber] using hcard
    have hcandidate_mem : ∀ j : J,
        center (uSeq i (j : ℕ)) ∈ Q0 ∧
          ∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
            f (omega (i : ℕ) * center (uSeq i (j : ℕ))) =
              rightConjugateElem (omega (i : ℕ)) d * q0 := by
      intro j
      let q0 := rightConjugateElem
        (center (uSeq i (j : ℕ) + alphaOf i)) (dSeq i (j : ℕ))
      have hdKW : dSeq i (j : ℕ) ∈ KW := by
        simpa [hKW] using hdSeq_mem i (j : ℕ)
      have hq0 : q0 ∈ Q0 := hQ0_conj_D _ _ (hcenter_mem_Q0 _)
        (hKW_le_D hdKW)
      refine ⟨hcenter_mem_Q0 _, dSeq i (j : ℕ), q0, hdKW, hq0, ?_⟩
      rw [← hrightConjugateElem_mul]
      exact hclaim17 i (j : ℕ) (hJ_bounds j).1 (hJ_bounds j).2
    let candidate : J → Fiber := fun j =>
      ⟨center (uSeq i (j : ℕ)), hcandidate_mem j⟩
    have hcandidate_injective : Function.Injective candidate := by
      intro j l hjl
      apply Subtype.ext
      apply huSeq_index_injective i (j : ℕ) (l : ℕ)
        (hJ_bounds j).1 (hJ_bounds j).2 (hJ_bounds l).1 (hJ_bounds l).2
      apply hcenter_injective
      exact congrArg (fun q : Fiber => (q : G)) hjl
    letI : Fintype J := by
      dsimp [J]
      infer_instance
    have hcardJ : Nat.card J = m - 1 := by
      rw [Nat.card_eq_fintype_card]
      simp [J, Nat.card_Icc]
    have hcandidate_bijective : Function.Bijective candidate :=
      hcandidate_injective.bijective_of_nat_card_le (by rw [hcardFiber, hcardJ])
    let xf : Fiber := ⟨center x, hcenter_mem_Q0 x, hx⟩
    obtain ⟨j, hj⟩ := hcandidate_bijective.2 xf
    have hxj : x = uSeq i (j : ℕ) := by
      apply hcenter_injective
      have hv := congrArg (fun q : Fiber => (q : G)) hj
      simpa [candidate, xf] using hv.symm
    subst x
    exact ⟨dSeq i (j : ℕ), by simpa [hKW] using hdSeq_mem i (j : ℕ),
      hclaim17 i (j : ℕ) (hJ_bounds j).1 (hJ_bounds j).2⟩
  have hKW_conj_t : ∀ d : G, d ∈ KW → rightConjugateElem d t ∈ KW := by
    intro d hd
    obtain ⟨⟨k, w⟩, hkw⟩ := hmulKW_bijective.2 (⟨d, hd⟩ : KW)
    have hd_eq : d = (k : G) * (w : G) := by
      exact (congrArg (fun a : KW => (a : G)) hkw).symm
    have hk_t : rightConjugateElem (k : G) t = (k : G)⁻¹ :=
      (hsec.K_def (k : G)).mp k.property |>.2
    have htC : t ∈ Subgroup.centralizer (W : Set G) :=
      PFchapter1section1.t_mem_centralizer_of_le_peterfalviV
        D V W t hsec.W_le_V hsec.V_eq
    have hwt : rightConjugateElem (w : G) t = (w : G) := by
      have hcomm : Commute (w : G) t :=
        Subgroup.mem_centralizer_iff.mp htC (w : G) w.property
      simp [rightConjugateElem, hcomm.eq, mul_assoc]
    rw [hd_eq, hrightConjugateElem_mul, hk_t, hwt, hKW]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (K.inv_mem k.property))
      (Subgroup.mem_sup_right w.property)
  have hT_conj : ∀ (x a : G), x ∈ Q → x ≠ 1 → a ∈ KW →
      f (rightConjugateElem x a)⁻¹ =
        rightConjugateElem (f x⁻¹) (rightConjugateElem a t) := by
    intro x a hxQ hxne ha
    have hxinvQ : x⁻¹ ∈ Q := Q.inv_mem hxQ
    have hxinvne : x⁻¹ ≠ 1 := fun h => hxne (inv_eq_one.mp h)
    calc
      f (rightConjugateElem x a)⁻¹ =
          f (rightConjugateElem x⁻¹ a) := by
        simp [rightConjugateElem, mul_assoc]
      _ = rightConjugateElem (f x⁻¹) (rightConjugateElem a t) :=
        PFchapter4section1.claim_H3 H Q D t f g h
          htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
          hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq x⁻¹ a hxinvQ hxinvne (hKW_le_D ha)
  have hreverse_f : ∀ (x y d : G), x ∈ Q → x ≠ 1 → y ∈ Q → y ≠ 1 →
      d ∈ KW → f x = rightConjugateElem y d →
      ∃ e : G, e ∈ KW ∧ f y = rightConjugateElem x e := by
    intro x y d hxQ hxne hyQ hyne hd hxy
    let dt := rightConjugateElem d t
    have hdtKW : dt ∈ KW := hKW_conj_t d hd
    have hdouble := PFchapter4section1.claim_H2 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq x hxQ hxne
    have htransport := PFchapter4section1.claim_H3 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq y d hyQ hyne (hKW_le_D hd)
    have hforward : x = rightConjugateElem (f y) dt := by
      calc
        x = f (f x) := hdouble.symm
        _ = f (rightConjugateElem y d) := by rw [← hxy]
        _ = rightConjugateElem (f y) dt := htransport
    refine ⟨dt⁻¹, KW.inv_mem hdtKW, ?_⟩
    calc
      f y = rightConjugateElem (rightConjugateElem (f y) dt) dt⁻¹ := by
        simp [rightConjugateElem, mul_assoc]
      _ = rightConjugateElem x dt⁻¹ := by rw [hforward]
  have hh_conj_mem_KW : ∀ (x a : G), x ∈ Q → x ≠ 1 →
      h x ∈ KW → a ∈ KW → h (rightConjugateElem x a) ∈ KW := by
    intro x a hxQ hxne hhx ha
    have hformula := PFchapter4section1.claim_H4_a H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq x a hxQ hxne (hKW_le_D ha)
    rw [hformula]
    exact KW.mul_mem (KW.mul_mem (KW.inv_mem (hKW_conj_t a ha)) hhx) ha
  have hh_of_f_mem_KW : ∀ x : G, x ∈ Q → x ≠ 1 → h (f x) ∈ KW → h x ∈ KW := by
    intro x hxQ hxne hhfx
    have hformula := PFchapter4section1.claim_H4_c H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq x hxQ hxne
    have heq : h x = (h (f x))⁻¹ := by
      calc
        h x = ((h x)⁻¹)⁻¹ := by simp
        _ = (h (f x))⁻¹ := by rw [hformula]
    rw [heq]
    exact KW.inv_mem hhfx
  have hh_inv_mem_KW : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ KW → h x⁻¹ ∈ KW := by
    intro x hxQ hxne hhx
    have hformula := PFchapter4section1.claim_H4_b H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq x hxQ hxne
    rw [hformula]
    exact KW.inv_mem (hKW_conj_t (h x) hhx)
  have hcenter_inv : ∀ x : F, (center x)⁻¹ = center x := by
    intro x
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using hcenter_sq x
  have homega_center_Q : ∀ (i : ValidIndex) (x : F),
      omega (i : ℕ) * center x ∈ Q := by
    intro i x
    exact Q.mul_mem (homega_valid i).1 (hsec.Q0_le_Q (hcenter_mem_Q0 x))
  have homega_center_not_Q0 : ∀ (i : ValidIndex) (x : F),
      omega (i : ℕ) * center x ∉ Q0 := by
    intro i x hprod
    apply (homega_valid i).2
    have heq : omega (i : ℕ) =
        (omega (i : ℕ) * center x) * (center x)⁻¹ := by simp [mul_assoc]
    rw [heq]
    exact Q0.mul_mem hprod (Q0.inv_mem (hcenter_mem_Q0 x))
  have homega_center_ne : ∀ (i : ValidIndex) (x : F),
      omega (i : ℕ) * center x ≠ 1 := by
    intro i x hone
    exact homega_center_not_Q0 i x (hone ▸ Q0.one_mem)
  have homega_inv_of_square : ∀ (i : ValidIndex) (r : F),
      center r = omega (i : ℕ) ^ 2 →
      (omega (i : ℕ))⁻¹ = omega (i : ℕ) * center r := by
    intro i r hr
    calc
      (omega (i : ℕ))⁻¹ = omega (i : ℕ) * (omega (i : ℕ) ^ 2)⁻¹ := by group
      _ = omega (i : ℕ) * (center r)⁻¹ := by rw [← hr]
      _ = omega (i : ℕ) * center r := by rw [hcenter_inv]
  have homega_center_inv_of_square : ∀ (i : ValidIndex) (r x : F),
      center r = omega (i : ℕ) ^ 2 →
      (omega (i : ℕ) * center x)⁻¹ =
        omega (i : ℕ) * center (r + x) := by
    intro i r x hr
    have hcomm : center x * omega (i : ℕ) = omega (i : ℕ) * center x :=
      hQ0_commutes_Q (center x) (hcenter_mem_Q0 x)
        (omega (i : ℕ)) (homega_valid i).1
    calc
      (omega (i : ℕ) * center x)⁻¹ =
          (center x)⁻¹ * (omega (i : ℕ))⁻¹ := by rw [mul_inv_rev]
      _ = center x * (omega (i : ℕ) * center r) := by
        rw [hcenter_inv, homega_inv_of_square i r hr]
      _ = omega (i : ℕ) * (center x * center r) := by
        calc
          center x * (omega (i : ℕ) * center r) =
              (center x * omega (i : ℕ)) * center r := by group
          _ = (omega (i : ℕ) * center x) * center r := by rw [hcomm]
          _ = omega (i : ℕ) * (center x * center r) := by group
      _ = omega (i : ℕ) * center (r + x) := by
        rw [add_comm, hcenter_add]
  let baseIndex : ValidIndex := ⟨1, le_rfl, hn_pos⟩
  have hfinish :
      (∀ i : ValidIndex, alphaOf i = alphaOf baseIndex) →
      (∀ (i j : ValidIndex) (x : F),
        (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
          f (omega (i : ℕ) * center x) =
            rightConjugateElem (omega (j : ℕ)) d * q0) →
        ∃ d : G, d ∈ KW ∧
          f (omega (i : ℕ) * center x) =
            rightConjugateElem
              (omega (j : ℕ) * center (x + alphaOf i)) d) →
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧
        f (omega i) = rightConjugateElem (omega i)⁻¹ zeta ∧ h (omega i) ∈ W := by
    intro halpha_all htranslate
    let alpha := alphaOf baseIndex
    have htarget : ∀ (i : ValidIndex) (x : F),
        ∃ j : ValidIndex, ∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
          f (omega (i : ℕ) * center x) =
            rightConjugateElem (omega (j : ℕ)) d * q0 := by
      intro i x
      let z := omega (i : ℕ) * center x
      have hzQ : z ∈ Q := homega_center_Q i x
      have hzNot : z ∉ Q0 := homega_center_not_Q0 i x
      have hzNe : z ≠ 1 := homega_center_ne i x
      have hfz := hf_mem z hzQ hzNe
      have hfzNot : f z ∉ Q0 := by
        intro hfzQ0
        exact hzNot ((claim_4_f_mem_Q0_iff H D Q K V W Q0 S Q1
          t s f g h hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer
          ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D
          hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq z hzQ hzNe).mp hfzQ0)
      obtain ⟨j, hj1, hjn, d, q0, hd, hq0, heq⟩ :=
        horbit_representatives.2.1 (f z) hfz.1 hfzNot
      exact ⟨⟨j, hj1, hjn⟩, d, q0, hd, hq0, heq⟩
    obtain ⟨r, hr⟩ := hcenter_surjective (omega 1 ^ 2)
      (homega_sq 1 le_rfl hn_pos)
    have hr_base : center r = omega (baseIndex : ℕ) ^ 2 := by
      simpa [baseIndex] using hr
    obtain ⟨i, hi⟩ := htarget baseIndex r
    obtain ⟨di, hdiKW, hcycle_three⟩ := htranslate baseIndex i r hi
    have hcycle_three' :
        f (omega (baseIndex : ℕ))⁻¹ =
          rightConjugateElem
            (omega (i : ℕ) * center (r + alpha)) di := by
      rw [homega_inv_of_square baseIndex r hr_base]
      simpa [alpha] using hcycle_three
    obtain ⟨k, hk⟩ := htarget baseIndex (r + alpha)
    obtain ⟨dk, hdkKW, hk_translated⟩ :=
      htranslate baseIndex k (r + alpha) hk
    have hk_translated' :
        f (omega (baseIndex : ℕ) * center (r + alpha)) =
          rightConjugateElem (omega (k : ℕ) * center r) dk := by
      simpa [alpha, CharTwo.add_self_eq_zero, add_assoc] using hk_translated
    obtain ⟨da, hdaKW, hcycle_one⟩ := hreverse_f
      (omega (baseIndex : ℕ) * center (r + alpha))
      (omega (k : ℕ) * center r) dk
      (homega_center_Q baseIndex (r + alpha))
      (homega_center_ne baseIndex (r + alpha))
      (homega_center_Q k r) (homega_center_ne k r)
      hdkKW hk_translated'
    have hcycle_two :
        f (omega (baseIndex : ℕ) * center (r + alpha))⁻¹ =
          rightConjugateElem (omega (baseIndex : ℕ)) zeta⁻¹ := by
      rw [homega_center_inv_of_square baseIndex r (r + alpha) hr_base]
      have hrr : r + (r + alpha) = alpha := by
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      rw [hrr]
      exact hf_at_alpha baseIndex
    let x0 := (omega (k : ℕ))⁻¹ * center r
    let z := omega (baseIndex : ℕ) * center (r + alpha)
    let w := omega (i : ℕ) * center (r + alpha)
    let T : G → G := fun x => f x⁻¹
    have hx0_inv : x0⁻¹ = omega (k : ℕ) * center r := by
      have hcomm : center r * omega (k : ℕ) = omega (k : ℕ) * center r :=
        hQ0_commutes_Q (center r) (hcenter_mem_Q0 r)
          (omega (k : ℕ)) (homega_valid k).1
      simp [x0, hcenter_inv, hcomm]
    have hTx0 : T x0 = rightConjugateElem z da := by
      simpa [T, z, hx0_inv] using hcycle_one
    have hTz : T z = rightConjugateElem (omega (baseIndex : ℕ)) zeta⁻¹ := by
      simpa [T, z] using hcycle_two
    have hTbase : T (omega (baseIndex : ℕ)) = rightConjugateElem w di := by
      simpa [T, w] using hcycle_three'
    let dat := rightConjugateElem da t
    have hdatKW : dat ∈ KW := hKW_conj_t da hdaKW
    let e2 := zeta⁻¹ * dat
    have hzetaKW : zeta ∈ KW := by
      rw [hKW]
      exact Subgroup.mem_sup_right hzeta
    have he2KW : e2 ∈ KW := KW.mul_mem (KW.inv_mem hzetaKW) hdatKW
    have hT2 : T (T x0) = rightConjugateElem (omega (baseIndex : ℕ)) e2 := by
      rw [hTx0]
      calc
        T (rightConjugateElem z da) =
            rightConjugateElem (T z) dat := by
          simpa [T, dat] using hT_conj z da
            (homega_center_Q baseIndex (r + alpha))
            (homega_center_ne baseIndex (r + alpha)) hdaKW
        _ = rightConjugateElem
            (rightConjugateElem (omega (baseIndex : ℕ)) zeta⁻¹) dat := by rw [hTz]
        _ = rightConjugateElem (omega (baseIndex : ℕ)) e2 := by
          rw [hrightConjugateElem_comp]
    let e2t := rightConjugateElem e2 t
    have he2tKW : e2t ∈ KW := hKW_conj_t e2 he2KW
    let e3 := di * e2t
    have he3KW : e3 ∈ KW := KW.mul_mem hdiKW he2tKW
    have hT3 : T (T (T x0)) = rightConjugateElem w e3 := by
      rw [hT2]
      calc
        T (rightConjugateElem (omega (baseIndex : ℕ)) e2) =
            rightConjugateElem (T (omega (baseIndex : ℕ))) e2t := by
          simpa [T, e2t] using hT_conj (omega (baseIndex : ℕ)) e2
            (homega_valid baseIndex).1
            (fun hone => (homega_valid baseIndex).2 (hone ▸ Q0.one_mem)) he2KW
        _ = rightConjugateElem (rightConjugateElem w di) e2t := by rw [hTbase]
        _ = rightConjugateElem w e3 := by
          rw [hrightConjugateElem_comp]
    have hhomega1KW : h (omega (baseIndex : ℕ)) ∈ KW := by
      rw [hKW]
      exact Subgroup.mem_sup_right (hh_mem_W baseIndex)
    have hhTzKW : h (T z) ∈ KW := by
      rw [hTz]
      exact hh_conj_mem_KW (omega (baseIndex : ℕ)) zeta⁻¹
        (homega_valid baseIndex).1
        (fun hone => (homega_valid baseIndex).2 (hone ▸ Q0.one_mem))
        hhomega1KW (KW.inv_mem hzetaKW)
    have hzInvQ : z⁻¹ ∈ Q := Q.inv_mem (homega_center_Q baseIndex (r + alpha))
    have hzInvNe : z⁻¹ ≠ 1 := fun h =>
      homega_center_ne baseIndex (r + alpha) (inv_eq_one.mp h)
    have hhzInvKW : h z⁻¹ ∈ KW := by
      exact hh_of_f_mem_KW z⁻¹ hzInvQ hzInvNe (by simpa [T] using hhTzKW)
    have hhzKW : h z ∈ KW := by
      simpa using hh_inv_mem_KW z⁻¹ hzInvQ hzInvNe hhzInvKW
    have hhyKW : h (omega (k : ℕ) * center r) ∈ KW := by
      apply hh_of_f_mem_KW (omega (k : ℕ) * center r)
        (homega_center_Q k r) (homega_center_ne k r)
      rw [hcycle_one]
      exact hh_conj_mem_KW z da
        (homega_center_Q baseIndex (r + alpha))
        (homega_center_ne baseIndex (r + alpha)) hhzKW hdaKW
    have hhx0KW : h x0 ∈ KW := by
      have := hh_inv_mem_KW (omega (k : ℕ) * center r)
        (homega_center_Q k r) (homega_center_ne k r) hhyKW
      have hcomm : Commute (center r) (omega (k : ℕ)) :=
        hQ0_commutes_Q (center r) (hcenter_mem_Q0 r)
          (omega (k : ℕ)) (homega_valid k).1
      have hy_inv : (omega (k : ℕ) * center r)⁻¹ = x0 := by
        calc
          (omega (k : ℕ) * center r)⁻¹ =
              center r * (omega (k : ℕ))⁻¹ := by rw [mul_inv_rev, hcenter_inv]
          _ = (omega (k : ℕ))⁻¹ * center r := hcomm.inv_right.eq
          _ = x0 := rfl
      rw [hy_inv] at this
      exact this
    obtain ⟨rk, hrk⟩ := hcenter_surjective (omega (k : ℕ) ^ 2)
      (homega_sq (k : ℕ) k.property.1 k.property.2)
    have hx0_standard : x0 = omega (k : ℕ) * center (rk + r) := by
      dsimp [x0]
      rw [homega_inv_of_square k rk hrk]
      rw [mul_assoc, ← hcenter_add]
    have hx0Q : x0 ∈ Q := by rw [hx0_standard]; exact homega_center_Q k (rk + r)
    have hx0Ne : x0 ≠ 1 := by rw [hx0_standard]; exact homega_center_ne k (rk + r)
    have hH5 := PFchapter4section1.claim_H5 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq x0 hx0Q hx0Ne
    have horbit_eq :
        rightConjugateElem x0 (h x0)⁻¹ = rightConjugateElem w e3 := by
      calc
        rightConjugateElem x0 (h x0)⁻¹ = T (T (T x0)) := by
          simpa [T] using hH5.symm
        _ = rightConjugateElem w e3 := hT3
    have hki : k = i := by
      apply horbit_index_of_conjugates k i (rk + r) (r + alpha)
        (h x0)⁻¹ e3 (KW.inv_mem hhx0KW) he3KW
      simpa [hx0_standard, w] using horbit_eq
    subst i
    have hexponents : (h x0)⁻¹ = e3 := by
      apply hconjugate_exponent_unique k (rk + r) (r + alpha)
        (h x0)⁻¹ e3 (KW.inv_mem hhx0KW) he3KW
      simpa [hx0_standard, w] using horbit_eq
    have hbases : omega (k : ℕ) * center (rk + r) =
        omega (k : ℕ) * center (r + alpha) := by
      have heq : rightConjugateElem
          (omega (k : ℕ) * center (rk + r)) e3 =
          rightConjugateElem (omega (k : ℕ) * center (r + alpha)) e3 := by
        calc
          rightConjugateElem (omega (k : ℕ) * center (rk + r)) e3 =
              rightConjugateElem x0 (h x0)⁻¹ := by
            rw [← hexponents, hx0_standard]
          _ = rightConjugateElem
              (omega (k : ℕ) * center (r + alpha)) e3 := by
            simpa [w] using horbit_eq
      have heq' := congrArg (fun x : G => rightConjugateElem x e3⁻¹) heq
      simpa [rightConjugateElem, mul_assoc] using heq'
    have hcoords : rk + r = r + alpha := by
      apply hcenter_injective
      exact mul_left_cancel hbases
    have hrk_alpha : rk = alpha := by
      apply add_right_cancel (b := r)
      simpa [add_comm] using hcoords
    refine ⟨(k : ℕ), k.property.1, k.property.2, ?_, hh_mem_W k⟩
    calc
      f (omega (k : ℕ)) =
          rightConjugateElem
            (omega (k : ℕ) * center (alphaOf k)) zeta := hfomega_alpha k
      _ = rightConjugateElem (omega (k : ℕ) * center alpha) zeta := by
        rw [halpha_all k]
      _ = rightConjugateElem (omega (k : ℕ) * center rk) zeta := by
        rw [hrk_alpha]
      _ = rightConjugateElem (omega (k : ℕ))⁻¹ zeta := by
        rw [← homega_inv_of_square k rk hrk]
  by_cases hn_two : 2 ≤ n
  · have hclaim20_general : ∀ (i₁ i₂ : ValidIndex), i₁ ≠ i₂ →
        alphaOf i₁ = alphaOf i₂ ∧
          ∀ x : F,
            (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
              f (omega (i₁ : ℕ) * center x) =
                rightConjugateElem (omega (i₂ : ℕ)) d * q0) →
            ∃ d : G, d ∈ KW ∧
              f (omega (i₁ : ℕ) * center x) =
                rightConjugateElem
                  (omega (i₂ : ℕ) * center (x + alphaOf i₁)) d := by
      intro i₁ i₂ hindices_ne
      have hindices_ne_nat : (i₂ : ℕ) ≠ (i₁ : ℕ) := by
        intro hval
        exact hindices_ne (Subtype.ext hval.symm)
      obtain ⟨x₁G, x₂G, k, hx₁G, hx₂G, hk, hstartG⟩ :=
        claim_8_exists_crossing_in_K H D Q K V W Q0 S Q1 KW
          t s (omega (i₁ : ℕ)) f g h m n (i₁ : ℕ) (i₂ : ℕ) omega hsection3 hC1 hC2
          htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
          hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq hKW rfl hn_card i₁.property i₂.property hindices_ne_nat
          horbit_representatives rfl
      obtain ⟨x₁, hx₁⟩ := hcenter_surjective x₁G hx₁G
      obtain ⟨x₂, hx₂⟩ := hcenter_surjective x₂G hx₂G
      have hstart :
          f (omega (i₁ : ℕ) * center x₁) =
            rightConjugateElem (omega (i₂ : ℕ) * center x₂) k := by
        simpa [hx₁, hx₂] using hstartG
      obtain ⟨kCoord, hkCoord⟩ := hK_scalar k hk
      let kNorm : F := (kCoord : F) * theta (kCoord : F)
      have hkNorm_ne : kNorm ≠ 0 := by
        exact mul_ne_zero (Units.ne_zero kCoord) ((map_ne_zero theta).2 (Units.ne_zero kCoord))
      have hcenter_conj_k : ∀ u : F,
          rightConjugateElem (center u) k = center (kNorm * u) := by
        intro u
        rw [hcenter_conj_K_exact k hk kCoord hkCoord]
      have hA_Q : omega (i₁ : ℕ) * center x₁ ∈ Q :=
        Q.mul_mem (homega_valid i₁).1 (hsec.Q0_le_Q (hcenter_mem_Q0 x₁))
      have hA_ne : omega (i₁ : ℕ) * center x₁ ≠ 1 := by
        intro hone
        apply (homega_valid i₁).2
        have : omega (i₁ : ℕ) =
            (omega (i₁ : ℕ) * center x₁) * (center x₁)⁻¹ := by simp [mul_assoc]
        rw [this, hone]
        simpa using Q0.inv_mem (hcenter_mem_Q0 x₁)
      have hB_Q : omega (i₂ : ℕ) * center x₂ ∈ Q :=
        Q.mul_mem (homega_valid i₂).1 (hsec.Q0_le_Q (hcenter_mem_Q0 x₂))
      have hB_ne : omega (i₂ : ℕ) * center x₂ ≠ 1 := by
        intro hone
        apply (homega_valid i₂).2
        have : omega (i₂ : ℕ) =
            (omega (i₂ : ℕ) * center x₂) * (center x₂)⁻¹ := by simp [mul_assoc]
        rw [this, hone]
        simpa using Q0.inv_mem (hcenter_mem_Q0 x₂)
      have hkD : k ∈ D := hsec.K_le_D hk
      have hk_t : rightConjugateElem k t = k⁻¹ := (hsec.K_def k).mp hk |>.2
      have hreverse :
          f (omega (i₂ : ℕ) * center x₂) =
            rightConjugateElem (omega (i₁ : ℕ) * center x₁) k := by
        have hdouble := PFchapter4section1.claim_H2 H Q D t f g h
          htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
          hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
          (omega (i₁ : ℕ) * center x₁) hA_Q hA_ne
        have htransport := PFchapter4section1.claim_H3 H Q D t f g h
          htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
          hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
          (omega (i₂ : ℕ) * center x₂) k hB_Q hB_ne hkD
        have hback : omega (i₁ : ℕ) * center x₁ =
            rightConjugateElem (f (omega (i₂ : ℕ) * center x₂)) k⁻¹ := by
          calc
            omega (i₁ : ℕ) * center x₁ =
                f (f (omega (i₁ : ℕ) * center x₁)) := hdouble.symm
            _ = f (rightConjugateElem (omega (i₂ : ℕ) * center x₂) k) := by
              rw [← hstart]
            _ = rightConjugateElem (f (omega (i₂ : ℕ) * center x₂))
                  (rightConjugateElem k t) := htransport
            _ = rightConjugateElem (f (omega (i₂ : ℕ) * center x₂)) k⁻¹ := by
              rw [hk_t]
        have hconj := congrArg (fun z : G ↦ rightConjugateElem z k) hback
        simpa [rightConjugateElem, mul_assoc] using hconj.symm
      have hdelta₁ : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          x₁ + uSeq i₁ j ≠ 0 := by
        intro j hj hjm hzero
        have hx : x₁ = uSeq i₁ j := CharTwo.add_eq_zero.mp hzero
        obtain ⟨_hc, hformula⟩ := hformula_until i₁ j hj
          (fun r hr hrj => huSeq_ne_before_end i₁ r hr (hrj.trans_le hjm))
        have heq :
            rightConjugateElem
                (omega (i₁ : ℕ) * center (vSeq i₁ j)) (dSeq i₁ j) =
              rightConjugateElem (omega (i₂ : ℕ) * center x₂) k := by
          rw [← hformula, ← hx, hstart]
        exact hindices_ne (horbit_index_of_conjugates i₁ i₂
          (vSeq i₁ j) x₂ (dSeq i₁ j) k (by simpa [hKW] using hdSeq_mem i₁ j)
          (by rw [hKW]; exact Subgroup.mem_sup_left hk) heq)
      have hdelta₂ : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          x₂ + uSeq i₂ j ≠ 0 := by
        intro j hj hjm hzero
        have hx : x₂ = uSeq i₂ j := CharTwo.add_eq_zero.mp hzero
        obtain ⟨_hc, hformula⟩ := hformula_until i₂ j hj
          (fun r hr hrj => huSeq_ne_before_end i₂ r hr (hrj.trans_le hjm))
        have heq :
            rightConjugateElem
                (omega (i₂ : ℕ) * center (vSeq i₂ j)) (dSeq i₂ j) =
              rightConjugateElem (omega (i₁ : ℕ) * center x₁) k := by
          rw [← hformula, ← hx, hreverse]
        have hi₂i₁ := horbit_index_of_conjugates i₂ i₁
          (vSeq i₂ j) x₁ (dSeq i₂ j) k (by simpa [hKW] using hdSeq_mem i₂ j)
          (by rw [hKW]; exact Subgroup.mem_sup_left hk) heq
        exact hindices_ne hi₂i₁.symm
      have hclaim19_formula : ∀ (p q : ValidIndex) (xP xQ : F),
          f (omega (p : ℕ) * center xP) =
            rightConjugateElem (omega (q : ℕ) * center xQ) k →
          ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → xP + uSeq p j ≠ 0 →
            f (omega (q : ℕ) *
                center (xQ + (kNorm * (xP + uSeq p j))⁻¹)) =
              rightConjugateElem
                (omega (p : ℕ) * center
                  (vSeq p j +
                    (scaleSeq p j * (xP + uSeq p j))⁻¹))
                (k * dSeq p j * (aFor (xP + uSeq p j)) ^ 2) := by
        intro p q xP xQ hcross j hj hjm hdelta
        let delta := xP + uSeq p j
        let a := aFor delta
        let shift := (kNorm * delta)⁻¹
        let offset := (scaleSeq p j * delta)⁻¹
        let e := k * dSeq p j * a ^ 2
        have ha : a ∈ K := haFor_mem delta
        have hsa : rightConjugateElem s a = center delta := by
          rw [hs_center]
          simpa [a] using hcenter_conj_aFor delta hdelta 1
        have hsa_inv : rightConjugateElem s a⁻¹ = center delta⁻¹ := by
          have hforward : rightConjugateElem (center delta⁻¹) a = center 1 := by
            calc
              rightConjugateElem (center delta⁻¹) a =
                  center (delta * delta⁻¹) := by
                simpa [a] using hcenter_conj_aFor delta hdelta delta⁻¹
              _ = center 1 := by rw [mul_inv_cancel₀ hdelta]
          have hconj := congrArg (fun z : G ↦ rightConjugateElem z a⁻¹) hforward
          calc
            rightConjugateElem s a⁻¹ = rightConjugateElem (center 1) a⁻¹ := by
              rw [← hs_center]
            _ = center delta⁻¹ := by
              simpa [rightConjugateElem, mul_assoc] using hconj.symm
        have hleft_arg :
            (omega (p : ℕ) * center xP) * rightConjugateElem s a =
              omega (p : ℕ) * center (uSeq p j) := by
          calc
            (omega (p : ℕ) * center xP) * rightConjugateElem s a =
                omega (p : ℕ) * (center xP * center delta) := by
              rw [hsa]
              group
            _ = omega (p : ℕ) * center (xP + delta) :=
              congrArg (omega (p : ℕ) * ·) (hcenter_add xP delta).symm
            _ = omega (p : ℕ) * center (uSeq p j) := by
              congr 2
              dsimp [delta]
              rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
        have hshift_action :
            rightConjugateElem (center shift) k = center delta⁻¹ := by
          rw [hcenter_conj_k]
          congr 1
          dsimp [shift]
          field_simp [hkNorm_ne, hdelta]
        have hinner :
            f (omega (p : ℕ) * center xP) * rightConjugateElem s a⁻¹ =
              rightConjugateElem
                (omega (q : ℕ) * center (xQ + shift)) k := by
          calc
            f (omega (p : ℕ) * center xP) * rightConjugateElem s a⁻¹ =
                rightConjugateElem (omega (q : ℕ) * center xQ) k *
                  center delta⁻¹ := by rw [hcross, hsa_inv]
            _ = rightConjugateElem (omega (q : ℕ) * center xQ) k *
                  rightConjugateElem (center shift) k := by rw [hshift_action]
            _ = rightConjugateElem
                  ((omega (q : ℕ) * center xQ) * center shift) k := by
              exact (hrightConjugateElem_mul
                (omega (q : ℕ) * center xQ) (center shift) k).symm
            _ = rightConjugateElem
                  (omega (q : ℕ) * center (xQ + shift)) k := by
              rw [mul_assoc, hcenter_add]
        have hXQ : omega (q : ℕ) * center (xQ + shift) ∈ Q :=
          Q.mul_mem (homega_valid q).1
            (hsec.Q0_le_Q (hcenter_mem_Q0 (xQ + shift)))
        have hXne : omega (q : ℕ) * center (xQ + shift) ≠ 1 := by
          intro hone
          apply (homega_valid q).2
          have heq : omega (q : ℕ) =
              (omega (q : ℕ) * center (xQ + shift)) *
                (center (xQ + shift))⁻¹ := by simp [mul_assoc]
          rw [heq, hone]
          simpa using Q0.inv_mem (hcenter_mem_Q0 (xQ + shift))
        have hf_inner :
            f (f (omega (p : ℕ) * center xP) * rightConjugateElem s a⁻¹) =
              rightConjugateElem
                (f (omega (q : ℕ) * center (xQ + shift))) k⁻¹ := by
          rw [hinner]
          simpa [hk_t] using
            PFchapter4section1.claim_H3 H Q D t f g h
              htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
              hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
              hcanonical_eq (omega (q : ℕ) * center (xQ + shift)) k
              hXQ hXne hkD
        have hbaseQ : omega (p : ℕ) * center xP ∈ Q :=
          Q.mul_mem (homega_valid p).1 (hsec.Q0_le_Q (hcenter_mem_Q0 xP))
        have hbase0 : omega (p : ℕ) * center xP ∉ Q0 := by
          intro hprod
          apply (homega_valid p).2
          have heq : omega (p : ℕ) =
              (omega (p : ℕ) * center xP) * (center xP)⁻¹ := by simp [mul_assoc]
          rw [heq]
          exact Q0.mul_mem hprod (Q0.inv_mem (hcenter_mem_Q0 xP))
        have hclaim2 := claim_2 H D Q K V W Q0 S Q1 t s f g h
          hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution
          ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D
          hf_mem hg_mem hh_mem hcanonical_eq
          (omega (p : ℕ) * center xP) a hbaseQ hbase0 ha
        obtain ⟨hc, hformula⟩ := hformula_until p j hj
          (fun r hr hrj => huSeq_ne_before_end p r hr (hrj.trans_le hjm))
        have hmain :
            rightConjugateElem
                (omega (p : ℕ) * center (vSeq p j)) (dSeq p j) =
              rightConjugateElem
                  (rightConjugateElem
                    (f (omega (q : ℕ) * center (xQ + shift))) k⁻¹)
                  (a⁻¹ ^ 2) * center delta⁻¹ := by
          calc
            rightConjugateElem
                (omega (p : ℕ) * center (vSeq p j)) (dSeq p j) =
                f (omega (p : ℕ) * center (uSeq p j)) := hformula.symm
            _ = f ((omega (p : ℕ) * center xP) * rightConjugateElem s a) := by
              rw [hleft_arg]
            _ = rightConjugateElem
                  (f (f (omega (p : ℕ) * center xP) *
                    rightConjugateElem s a⁻¹)) (a⁻¹ ^ 2) *
                  rightConjugateElem s a⁻¹ := hclaim2
            _ = rightConjugateElem
                  (rightConjugateElem
                    (f (omega (q : ℕ) * center (xQ + shift))) k⁻¹)
                  (a⁻¹ ^ 2) * center delta⁻¹ := by rw [hf_inner, hsa_inv]
        have hscale : scaleSeq p j ≠ 0 := hscaleSeq_ne_zero p j hj hjm
        have hoffset_action :
            rightConjugateElem (center offset) (dSeq p j) = center delta⁻¹ := by
          rw [hcenter_conj_dSeq p j hc]
          congr 1
          change scaleSeq p j * offset = delta⁻¹
          dsimp [offset]
          field_simp [hscale, hdelta]
        have hcleared :
            rightConjugateElem
                (omega (p : ℕ) * center (vSeq p j + offset)) (dSeq p j) =
              rightConjugateElem
                  (rightConjugateElem
                    (f (omega (q : ℕ) * center (xQ + shift))) k⁻¹)
                  (a⁻¹ ^ 2) := by
          calc
            rightConjugateElem
                (omega (p : ℕ) * center (vSeq p j + offset)) (dSeq p j) =
                rightConjugateElem
                  ((omega (p : ℕ) * center (vSeq p j)) * center offset)
                  (dSeq p j) := by rw [mul_assoc, hcenter_add]
            _ = rightConjugateElem
                  (omega (p : ℕ) * center (vSeq p j)) (dSeq p j) *
                rightConjugateElem (center offset) (dSeq p j) := by
              rw [hrightConjugateElem_mul]
            _ = rightConjugateElem
                  (omega (p : ℕ) * center (vSeq p j)) (dSeq p j) *
                center delta⁻¹ := by rw [hoffset_action]
            _ = (rightConjugateElem
                  (rightConjugateElem
                    (f (omega (q : ℕ) * center (xQ + shift))) k⁻¹)
                  (a⁻¹ ^ 2) * center delta⁻¹) * center delta⁻¹ := by
              rw [hmain]
            _ = rightConjugateElem
                  (rightConjugateElem
                    (f (omega (q : ℕ) * center (xQ + shift))) k⁻¹)
                  (a⁻¹ ^ 2) := by
              rw [mul_assoc, ← pow_two, hcenter_sq, mul_one]
        let c := k⁻¹ * a⁻¹ ^ 2
        have hcleared' :
            rightConjugateElem
                (omega (p : ℕ) * center (vSeq p j + offset)) (dSeq p j) =
              rightConjugateElem
                (f (omega (q : ℕ) * center (xQ + shift))) c := by
          rw [hcleared, hrightConjugateElem_comp]
        have hsolve := congrArg (fun z : G ↦ rightConjugateElem z c⁻¹) hcleared'
        have hsolve' :
            rightConjugateElem
                (omega (p : ℕ) * center (vSeq p j + offset))
                (dSeq p j * c⁻¹) =
              f (omega (q : ℕ) * center (xQ + shift)) := by
          simpa [hrightConjugateElem_comp, hrightConjugateElem_one] using hsolve
        have hka : Commute a k := hKW_commute a k
          (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_left hk)
        have hdk : Commute (dSeq p j) k := hKW_commute (dSeq p j) k
          (hdSeq_mem p j) (Subgroup.mem_sup_left hk)
        have hword : dSeq p j * c⁻¹ = e := by
          calc
            dSeq p j * c⁻¹ = dSeq p j * (a ^ 2 * k) := by
              simp [c, mul_inv_rev]
            _ = dSeq p j * (k * a ^ 2) := by rw [(hka.pow_left 2).eq]
            _ = (dSeq p j * k) * a ^ 2 := (mul_assoc _ _ _).symm
            _ = (k * dSeq p j) * a ^ 2 := by rw [hdk.eq]
            _ = e := rfl
        rw [hword] at hsolve'
        simpa [delta, shift, offset, e, a] using hsolve'.symm
      have hclaim19a := hclaim19_formula i₁ i₂ x₁ x₂ hstart
      have hclaim19b := hclaim19_formula i₂ i₁ x₂ x₁ hreverse
      have hinvert_crossing : ∀ A B e : G,
          A ∈ Q → A ≠ 1 → B ∈ Q → B ≠ 1 → e ∈ D →
          f A = rightConjugateElem B e →
          f B = rightConjugateElem A (rightConjugateElem e⁻¹ t) := by
        intro A B e hAQ hAne hBQ hBne heD hAB
        have hdouble := PFchapter4section1.claim_H2 H Q D t f g h
          htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
          hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq A hAQ hAne
        have htransport := PFchapter4section1.claim_H3 H Q D t f g h
          htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
          hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq B e hBQ hBne heD
        have hback : A = rightConjugateElem (f B) (rightConjugateElem e t) := by
          calc
            A = f (f A) := hdouble.symm
            _ = f (rightConjugateElem B e) := by rw [← hAB]
            _ = rightConjugateElem (f B) (rightConjugateElem e t) := htransport
        have hconj := congrArg
          (fun z : G ↦ rightConjugateElem z (rightConjugateElem e t)⁻¹) hback
        have heinv : (rightConjugateElem e t)⁻¹ = rightConjugateElem e⁻¹ t := by
          simp [rightConjugateElem, mul_assoc]
        rw [heinv] at hconj
        simpa [rightConjugateElem, mul_assoc] using hconj.symm
      let delta₁ (j : ℕ) := x₁ + uSeq i₁ j
      let delta₂ (j : ℕ) := x₂ + uSeq i₂ j
      let input₁ (j : ℕ) := x₂ + (kNorm * delta₁ j)⁻¹
      let input₂ (j : ℕ) := x₁ + (kNorm * delta₂ j)⁻¹
      let output₁ (j : ℕ) :=
        vSeq i₁ j + (scaleSeq i₁ j * delta₁ j)⁻¹
      let output₂ (j : ℕ) :=
        vSeq i₂ j + (scaleSeq i₂ j * delta₂ j)⁻¹
      let e₁ (j : ℕ) := k * dSeq i₁ j * (aFor (delta₁ j)) ^ 2
      let e₂ (j : ℕ) := k * dSeq i₂ j * (aFor (delta₂ j)) ^ 2
      have he₁KW : ∀ j : ℕ, e₁ j ∈ KW := by
        intro j
        rw [hKW]
        exact Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (hdSeq_mem i₁ j))
          (Subgroup.pow_mem _ (Subgroup.mem_sup_left (haFor_mem _)) 2)
      have he₂KW : ∀ j : ℕ, e₂ j ∈ KW := by
        intro j
        rw [hKW]
        exact Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (hdSeq_mem i₂ j))
          (Subgroup.pow_mem _ (Subgroup.mem_sup_left (haFor_mem _)) 2)
      have hclaim19a' : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          f (omega (i₂ : ℕ) * center (input₁ j)) =
            rightConjugateElem (omega (i₁ : ℕ) * center (output₁ j)) (e₁ j) := by
        intro j hj hjm
        simpa [delta₁, input₁, output₁, e₁] using
          hclaim19a j hj hjm (hdelta₁ j hj hjm)
      have hclaim19b' : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          f (omega (i₁ : ℕ) * center (input₂ j)) =
            rightConjugateElem (omega (i₂ : ℕ) * center (output₂ j)) (e₂ j) := by
        intro j hj hjm
        simpa [delta₂, input₂, output₂, e₂] using
          hclaim19b j hj hjm (hdelta₂ j hj hjm)
      have hclaim19a_inverse : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          f (omega (i₁ : ℕ) * center (output₁ j)) =
            rightConjugateElem (omega (i₂ : ℕ) * center (input₁ j))
              (rightConjugateElem (e₁ j)⁻¹ t) := by
        intro j hj hjm
        let A := omega (i₂ : ℕ) * center (input₁ j)
        let B := omega (i₁ : ℕ) * center (output₁ j)
        have hAQ : A ∈ Q := Q.mul_mem (homega_valid i₂).1
          (hsec.Q0_le_Q (hcenter_mem_Q0 _))
        have hBQ : B ∈ Q := Q.mul_mem (homega_valid i₁).1
          (hsec.Q0_le_Q (hcenter_mem_Q0 _))
        have hAne : A ≠ 1 := by
          intro hone
          apply (homega_valid i₂).2
          have heq : omega (i₂ : ℕ) = A * (center (input₁ j))⁻¹ := by
            simp [A, mul_assoc]
          rw [heq, hone]
          simpa using Q0.inv_mem (hcenter_mem_Q0 (input₁ j))
        have hBne : B ≠ 1 := by
          intro hone
          apply (homega_valid i₁).2
          have heq : omega (i₁ : ℕ) = B * (center (output₁ j))⁻¹ := by
            simp [B, mul_assoc]
          rw [heq, hone]
          simpa using Q0.inv_mem (hcenter_mem_Q0 (output₁ j))
        exact hinvert_crossing A B (e₁ j) hAQ hAne hBQ hBne
          (hKW_le_D (he₁KW j)) (hclaim19a' j hj hjm)
      have hzeta_sub_eq_inv : ∀ j : ℕ, j ≤ m →
          zeta ^ (m - j) = (zeta ^ j)⁻¹ := by
        intro j hj
        apply eq_inv_of_mul_eq_one_left
        calc
          zeta ^ (m - j) * zeta ^ j = zeta ^ (m - j + j) := (pow_add _ _ _).symm
          _ = zeta ^ m := by rw [Nat.sub_add_cancel hj]
          _ = 1 := by rw [← hzeta_order, pow_orderOf_eq_one]
      let r₁ (j : ℕ) :=
        k * kOf (unitOrOne (cSeq i₁ j)) * (aFor (delta₁ j)) ^ 2
      let r₂ (j : ℕ) :=
        k * kOf (unitOrOne (cSeq i₂ j)) * (aFor (delta₂ j)) ^ 2
      have hr₁K : ∀ j : ℕ, r₁ j ∈ K := by
        intro j
        exact K.mul_mem (K.mul_mem hk (hkOf_mem _)) (K.pow_mem (haFor_mem _) 2)
      have hr₂K : ∀ j : ℕ, r₂ j ∈ K := by
        intro j
        exact K.mul_mem (K.mul_mem hk (hkOf_mem _)) (K.pow_mem (haFor_mem _) 2)
      have he₁_decomp : ∀ j : ℕ, e₁ j = zeta ^ j * r₁ j := by
        intro j
        have hcomm : Commute k (zeta ^ j) := hKW_commute k (zeta ^ j)
          (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right (W.pow_mem hzeta j))
        calc
          e₁ j = k * (zeta ^ j * kOf (unitOrOne (cSeq i₁ j))) *
              (aFor (delta₁ j)) ^ 2 := by rfl
          _ = (k * zeta ^ j) * kOf (unitOrOne (cSeq i₁ j)) *
              (aFor (delta₁ j)) ^ 2 := by rw [← mul_assoc k]
          _ = (zeta ^ j * k) * kOf (unitOrOne (cSeq i₁ j)) *
              (aFor (delta₁ j)) ^ 2 := by rw [hcomm.eq]
          _ = zeta ^ j * r₁ j := by simp [r₁, mul_assoc]
      have he₂_decomp : ∀ j : ℕ, e₂ j = zeta ^ j * r₂ j := by
        intro j
        have hcomm : Commute k (zeta ^ j) := hKW_commute k (zeta ^ j)
          (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right (W.pow_mem hzeta j))
        calc
          e₂ j = k * (zeta ^ j * kOf (unitOrOne (cSeq i₂ j))) *
              (aFor (delta₂ j)) ^ 2 := by rfl
          _ = (k * zeta ^ j) * kOf (unitOrOne (cSeq i₂ j)) *
              (aFor (delta₂ j)) ^ 2 := by rw [← mul_assoc k]
          _ = (zeta ^ j * k) * kOf (unitOrOne (cSeq i₂ j)) *
              (aFor (delta₂ j)) ^ 2 := by rw [hcomm.eq]
          _ = zeta ^ j * r₂ j := by simp [r₂, mul_assoc]
      have hnegT_decomp : ∀ j : ℕ, j ≤ m →
          rightConjugateElem (e₁ j)⁻¹ t = zeta ^ (m - j) * r₁ j := by
        intro j hj
        have hr_t : rightConjugateElem (r₁ j) t = (r₁ j)⁻¹ :=
          ((hsec.K_def (r₁ j)).mp (hr₁K j)).2
        have hr_inv_t : rightConjugateElem (r₁ j)⁻¹ t = r₁ j := by
          simpa [rightConjugateElem, mul_assoc] using congrArg Inv.inv hr_t
        have hzpow_t : rightConjugateElem (zeta ^ j) t = zeta ^ j := by
          rw [hrightConjugateElem_pow, hzeta_t]
        have hzpow_inv_t : rightConjugateElem (zeta ^ j)⁻¹ t = (zeta ^ j)⁻¹ := by
          simpa [rightConjugateElem, mul_assoc] using congrArg Inv.inv hzpow_t
        have hcomm : Commute (r₁ j) (zeta ^ j)⁻¹ :=
          (hKW_commute (r₁ j) (zeta ^ j)
            (Subgroup.mem_sup_left (hr₁K j))
            (Subgroup.mem_sup_right (W.pow_mem hzeta j))).inv_right
        calc
          rightConjugateElem (e₁ j)⁻¹ t =
              rightConjugateElem ((r₁ j)⁻¹ * (zeta ^ j)⁻¹) t := by
            rw [he₁_decomp]
            simp only [mul_inv_rev]
          _ = rightConjugateElem (r₁ j)⁻¹ t *
                rightConjugateElem (zeta ^ j)⁻¹ t :=
            hrightConjugateElem_mul _ _ _
          _ = r₁ j * (zeta ^ j)⁻¹ := by rw [hr_inv_t, hzpow_inv_t]
          _ = (zeta ^ j)⁻¹ * r₁ j := hcomm.eq
          _ = zeta ^ (m - j) * r₁ j := by rw [hzeta_sub_eq_inv j hj]
      have hexponent_coset : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          ∃ r : G, r ∈ K ∧
            rightConjugateElem (e₁ j)⁻¹ t = e₂ (m - j) * r := by
        intro j hj hjm
        let r := (r₂ (m - j))⁻¹ * r₁ j
        have hrK : r ∈ K := K.mul_mem (K.inv_mem (hr₂K _)) (hr₁K j)
        refine ⟨r, hrK, ?_⟩
        rw [hnegT_decomp j (by omega), he₂_decomp, hzeta_sub_eq_inv j (by omega)]
        dsimp [r]
        group
      have hmatch : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          output₁ j = input₂ (m - j) ∧
            input₁ j = output₂ (m - j) ∧
              rightConjugateElem (e₁ j)⁻¹ t = e₂ (m - j) := by
        intro j hj hjm
        have hl_one : 1 ≤ m - j := by omega
        have hl_end : m - j ≤ m - 1 := by omega
        let p := rightConjugateElem (e₁ j)⁻¹ t
        let q := e₂ (m - j)
        obtain ⟨r, hrK, hpq⟩ := hexponent_coset j hj hjm
        have hpKW : p ∈ KW := by
          dsimp [p]
          rw [hnegT_decomp j (by omega), hKW]
          exact Subgroup.mul_mem _
            (Subgroup.mem_sup_right (W.pow_mem hzeta (m - j)))
            (Subgroup.mem_sup_left (hr₁K j))
        have hqKW : q ∈ KW := he₂KW (m - j)
        have hpD : p ∈ D := hKW_le_D hpKW
        have hqD : q ∈ D := hKW_le_D hqKW
        have hq_coset : q = p * r⁻¹ := by
          dsimp [p, q]
          rw [hpq]
          group
        have hinput : output₁ j = input₂ (m - j) := by
          by_contra hne
          have hcenter_ne : center (output₁ j) ≠ center (input₂ (m - j)) := by
            intro heq
            exact hne (hcenter_injective heq)
          have hnot := claim_7 H D Q K V W Q0 S Q1 t s f g h
            hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution
            ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D
            hf_mem hg_mem hh_mem hcanonical_eq
            (omega (i₁ : ℕ)) (omega (i₂ : ℕ))
            (center (output₁ j)) (center (input₂ (m - j)))
            (center (input₁ j)) (center (output₂ (m - j))) p q
            (homega_valid i₁).1 (homega_valid i₁).2
            (homega_valid i₂).1 (homega_valid i₂).2
            (hcenter_mem_Q0 _) (hcenter_mem_Q0 _)
            (hcenter_mem_Q0 _) (hcenter_mem_Q0 _)
            hpD hqD hcenter_ne
            (hclaim19a_inverse j hj hjm)
            (hclaim19b' (m - j) hl_one hl_end)
          exact hnot ⟨r⁻¹, K.inv_mem hrK, hq_coset⟩
        have hconjugates :
            rightConjugateElem
                (omega (i₂ : ℕ) * center (input₁ j)) p =
              rightConjugateElem
                (omega (i₂ : ℕ) * center (output₂ (m - j))) q := by
          calc
            rightConjugateElem
                (omega (i₂ : ℕ) * center (input₁ j)) p =
                f (omega (i₁ : ℕ) * center (output₁ j)) :=
              (hclaim19a_inverse j hj hjm).symm
            _ = f (omega (i₁ : ℕ) * center (input₂ (m - j))) := by rw [hinput]
            _ = rightConjugateElem
                (omega (i₂ : ℕ) * center (output₂ (m - j))) q :=
              hclaim19b' (m - j) hl_one hl_end
        have hpq_eq : p = q := hconjugate_exponent_unique i₂
          (input₁ j) (output₂ (m - j)) p q hpKW hqKW hconjugates
        have houtput : input₁ j = output₂ (m - j) := by
          rw [hpq_eq] at hconjugates
          have hbase := congrArg (fun z : G ↦ rightConjugateElem z q⁻¹) hconjugates
          have hprod : omega (i₂ : ℕ) * center (input₁ j) =
              omega (i₂ : ℕ) * center (output₂ (m - j)) := by
            simpa [rightConjugateElem, mul_assoc] using hbase
          exact hcenter_injective (mul_left_cancel hprod)
        exact ⟨hinput, houtput, hpq_eq⟩
      have hr_eq : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          r₁ j = r₂ (m - j) := by
        intro j hj hjm
        have heq := (hmatch j hj hjm).2.2
        rw [hnegT_decomp j (by omega), he₂_decomp] at heq
        exact mul_left_cancel heq
      have hu_end : ∀ i : ValidIndex, uSeq i (m - 1) = alphaOf i := by
        intro i
        rw [← hstop_eq i]
        exact (hstop_spec i).2.2
      have hk_end : ∀ i : ValidIndex,
          kOf (unitOrOne (cSeq i (m - 1))) = 1 := by
        intro i
        have hdEnd : dSeq i (m - 1) = zeta⁻¹ := by
          rw [← hstop_eq i]
          exact hd_stop i
        change zeta ^ (m - 1) * kOf (unitOrOne (cSeq i (m - 1))) = zeta⁻¹ at hdEnd
        rw [hzeta_pred] at hdEnd
        apply mul_left_cancel (a := zeta⁻¹)
        simpa using hdEnd
      have haFor_sq_injective : ∀ x y : F, x ≠ 0 → y ≠ 0 →
          (aFor x) ^ 2 = (aFor y) ^ 2 → x = y := by
        intro x y hx hy hsq
        have haction_sq : ∀ z : F, z ≠ 0 →
            rightConjugateElem (center 1) ((aFor z) ^ 2) = center (z ^ 2) := by
          intro z hz
          calc
            rightConjugateElem (center 1) ((aFor z) ^ 2) =
                rightConjugateElem
                  (rightConjugateElem (center 1) (aFor z)) (aFor z) := by
              rw [pow_two, hrightConjugateElem_comp]
            _ = rightConjugateElem (center (z * 1)) (aFor z) := by
              rw [hcenter_conj_aFor z hz 1]
            _ = center (z * (z * 1)) := hcenter_conj_aFor z hz (z * 1)
            _ = center (z ^ 2) := by simp [pow_two]
        apply CharTwo.sq_injective
        apply hcenter_injective
        calc
          center (x ^ 2) = rightConjugateElem (center 1) ((aFor x) ^ 2) :=
            (haction_sq x hx).symm
          _ = rightConjugateElem (center 1) ((aFor y) ^ 2) := by rw [hsq]
          _ = center (y ^ 2) := haction_sq y hy
      have hendpoint_left : x₁ = x₂ + alphaOf i₂ := by
        have heq := hr_eq 1 (by omega) (by omega)
        have hsquares : (aFor (delta₁ 1)) ^ 2 =
            (aFor (delta₂ (m - 1))) ^ 2 := by
          dsimp [r₁, r₂] at heq
          rw [(hseq i₁).2.2.1, hk_end i₂] at heq
          simp [unitOrOne, hkOf_one] at heq
          exact heq
        have hdelta₁_one : delta₁ 1 ≠ 0 := hdelta₁ 1 (by omega) (by omega)
        have hdelta₂_end : delta₂ (m - 1) ≠ 0 :=
          hdelta₂ (m - 1) (by omega) (by omega)
        have hdelta := haFor_sq_injective _ _ hdelta₁_one hdelta₂_end hsquares
        simpa [delta₁, delta₂, (hseq i₁).1, hu_end i₂] using hdelta
      have hendpoint_right : x₁ + alphaOf i₁ = x₂ := by
        have heq := hr_eq (m - 1) (by omega) (by omega)
        have hsquares : (aFor (delta₁ (m - 1))) ^ 2 =
            (aFor (delta₂ 1)) ^ 2 := by
          have hm_sub : m - (m - 1) = 1 := by omega
          dsimp [r₁, r₂] at heq
          rw [hk_end i₁, hm_sub, (hseq i₂).2.2.1] at heq
          simp [unitOrOne, hkOf_one] at heq
          exact heq
        have hdelta₁_end : delta₁ (m - 1) ≠ 0 :=
          hdelta₁ (m - 1) (by omega) (by omega)
        have hdelta₂_one : delta₂ 1 ≠ 0 := hdelta₂ 1 (by omega) (by omega)
        have hdelta := haFor_sq_injective _ _ hdelta₁_end hdelta₂_one hsquares
        simpa [delta₁, delta₂, hu_end i₁, (hseq i₂).1] using hdelta
      have halpha : alphaOf i₁ = alphaOf i₂ := by
        calc
          alphaOf i₁ = (x₁ + x₁) + alphaOf i₁ := by
            rw [CharTwo.add_self_eq_zero, zero_add]
          _ = x₁ + (x₁ + alphaOf i₁) := by rw [add_assoc]
          _ = x₁ + x₂ := by rw [hendpoint_right]
          _ = (x₂ + alphaOf i₂) + x₂ := by rw [hendpoint_left]
          _ = (x₂ + x₂) + alphaOf i₂ := by ac_rfl
          _ = alphaOf i₂ := by rw [CharTwo.add_self_eq_zero, zero_add]
      have hseq_eq : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          uSeq i₁ j = uSeq i₂ j ∧
            vSeq i₁ j = vSeq i₂ j ∧ cSeq i₁ j = cSeq i₂ j := by
        intro j
        induction j using Nat.strong_induction_on with
        | h j ih =>
            intro hj hend
            by_cases hj_one : j = 1
            · subst j
              exact ⟨by rw [(hseq i₁).1, (hseq i₂).1],
                by rw [(hseq i₁).2.1, (hseq i₂).2.1, halpha],
                by rw [(hseq i₁).2.2.1, (hseq i₂).2.2.1]⟩
            · let p := j - 1
              have hp_one : 1 ≤ p := by omega
              have hp_lt : p < m - 1 := by omega
              have hpj : p + 1 = j := Nat.sub_add_cancel hj
              have hprev := ih p (by omega) hp_one (by omega)
              have hu₁ := huSeq_ne_before_end i₁ p hp_one hp_lt
              have hu₂ := huSeq_ne_before_end i₂ p hp_one hp_lt
              have huNext : uSeq i₁ (p + 1) = uSeq i₂ (p + 1) := by
                calc
                  uSeq i₁ (p + 1) = (alphaOf i₁ + uSeq i₁ p)⁻¹ :=
                    (hseq i₁).2.2.2.1 p hu₁
                  _ = (alphaOf i₂ + uSeq i₂ p)⁻¹ := by
                    rw [halpha, hprev.1]
                  _ = uSeq i₂ (p + 1) := ((hseq i₂).2.2.2.1 p hu₂).symm
              have hvNext : vSeq i₁ (p + 1) = vSeq i₂ (p + 1) := by
                rw [(hseq i₁).2.2.2.2.1 p hu₁, (hseq i₂).2.2.2.2.1 p hu₂,
                  hprev.2.1, huNext, hprev.2.2]
              have hcNext : cSeq i₁ (p + 1) = cSeq i₂ (p + 1) := by
                rw [(hseq i₁).2.2.2.2.2 p hu₁, (hseq i₂).2.2.2.2.2 p hu₂,
                  hprev.2.2, huNext]
              simpa [hpj] using And.intro huNext (And.intro hvNext hcNext)
      have hu_reverse : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          uSeq i₁ (m - j) = uSeq i₁ j + alphaOf i₁ := by
        intro j
        induction j using Nat.strong_induction_on with
        | h j ih =>
            intro hj hend
            by_cases hj_one : j = 1
            · subst j
              rw [hu_end i₁, (hseq i₁).1, zero_add]
            · let p := j - 1
              let q := m - j
              have hp_one : 1 ≤ p := by omega
              have hp_lt : p < m - 1 := by omega
              have hq_one : 1 ≤ q := by omega
              have hq_lt : q < m - 1 := by omega
              have hpj : p + 1 = j := Nat.sub_add_cancel hj
              have hqj : q + 1 = m - p := by omega
              have hprev := ih p (by omega) hp_one (by omega)
              have hup := huSeq_ne_before_end i₁ p hp_one hp_lt
              have huq := huSeq_ne_before_end i₁ q hq_one hq_lt
              have hrecp : uSeq i₁ (p + 1) =
                  (alphaOf i₁ + uSeq i₁ p)⁻¹ :=
                (hseq i₁).2.2.2.1 p hup
              have hrecq : uSeq i₁ (q + 1) =
                  (alphaOf i₁ + uSeq i₁ q)⁻¹ :=
                (hseq i₁).2.2.2.1 q huq
              have hback : uSeq i₁ q =
                  (uSeq i₁ (q + 1))⁻¹ + alphaOf i₁ := by
                have hinv := congrArg Inv.inv hrecq
                have hinv' : (uSeq i₁ (q + 1))⁻¹ =
                    alphaOf i₁ + uSeq i₁ q := by
                  simpa only [inv_inv] using hinv
                calc
                  uSeq i₁ q =
                      alphaOf i₁ + (alphaOf i₁ + uSeq i₁ q) := by
                    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
                  _ = alphaOf i₁ + (uSeq i₁ (q + 1))⁻¹ := by rw [hinv']
                  _ = (uSeq i₁ (q + 1))⁻¹ + alphaOf i₁ := add_comm _ _
              calc
                uSeq i₁ (m - j) = uSeq i₁ q := rfl
                _ = (uSeq i₁ (q + 1))⁻¹ + alphaOf i₁ := hback
                _ = (uSeq i₁ (m - p))⁻¹ + alphaOf i₁ := by rw [hqj]
                _ = (uSeq i₁ p + alphaOf i₁)⁻¹ + alphaOf i₁ := by rw [hprev]
                _ = (alphaOf i₁ + uSeq i₁ p)⁻¹ + alphaOf i₁ := by
                  rw [add_comm (uSeq i₁ p)]
                _ = uSeq i₁ (p + 1) + alphaOf i₁ := by rw [hrecp]
                _ = uSeq i₁ j + alphaOf i₁ := by rw [hpj]
      have hdelta_reverse : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          delta₁ (m - j) = delta₂ j := by
        intro j hj hjm
        have huEq := (hseq_eq j hj hjm).1
        dsimp [delta₁, delta₂]
        rw [hu_reverse j hj hjm, huEq, halpha]
        calc
          x₁ + (uSeq i₂ j + alphaOf i₂) =
              (x₁ + alphaOf i₁) + uSeq i₂ j := by rw [halpha]; ac_rfl
          _ = x₂ + uSeq i₂ j := by rw [hendpoint_right]
      have hclaim20_candidates : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          output₂ j = input₂ j + alphaOf i₁ := by
        intro j hj hjm
        have hr_one : 1 ≤ m - j := by omega
        have hr_end : m - j ≤ m - 1 := by omega
        have heq := (hmatch (m - j) hr_one hr_end).2.1
        have hsub : m - (m - j) = j := by omega
        rw [hsub] at heq
        rw [← heq]
        dsimp [input₁, input₂]
        rw [hdelta_reverse j hj hjm]
        calc
          x₂ + (kNorm * delta₂ j)⁻¹ =
              (x₁ + alphaOf i₁) + (kNorm * delta₂ j)⁻¹ := by
            rw [hendpoint_right]
          _ = (x₁ + (kNorm * delta₂ j)⁻¹) + alphaOf i₁ := by ac_rfl
      have hclaim20_at_candidate : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          ∃ d : G, d ∈ KW ∧
            f (omega (i₁ : ℕ) * center (input₂ j)) =
              rightConjugateElem
                (omega (i₂ : ℕ) * center (input₂ j + alphaOf i₁)) d := by
        intro j hj hjm
        refine ⟨e₂ j, he₂KW j, ?_⟩
        rw [← hclaim20_candidates j hj hjm]
        exact hclaim19b' j hj hjm
      have hclaim20_at_base : ∃ d : G, d ∈ KW ∧
          f (omega (i₁ : ℕ) * center x₁) =
            rightConjugateElem
              (omega (i₂ : ℕ) * center (x₁ + alphaOf i₁)) d := by
        refine ⟨k, ?_, ?_⟩
        · rw [hKW]
          exact Subgroup.mem_sup_left hk
        · rw [hendpoint_right]
          exact hstart
      have he₂_index_injective : ∀ j l : ℕ,
          1 ≤ j → j ≤ m - 1 → 1 ≤ l → l ≤ m - 1 →
            e₂ j = e₂ l → j = l := by
        intro j l hj hjm hl hlm heq
        have hdecomp : zeta ^ j * r₂ j = zeta ^ l * r₂ l := by
          rw [← he₂_decomp, ← he₂_decomp]
          exact heq
        let z := zeta ^ j * (zeta ^ l)⁻¹
        have hzW : z ∈ W := W.mul_mem (W.pow_mem hzeta j) (W.inv_mem (W.pow_mem hzeta l))
        have hcomm_pow : Commute (zeta ^ j) (zeta ^ l)⁻¹ :=
          (hKW_commute (zeta ^ j) (zeta ^ l)
            (Subgroup.mem_sup_right (W.pow_mem hzeta j))
            (Subgroup.mem_sup_right (W.pow_mem hzeta l))).inv_right
        have hz_eq : z = r₂ l * (r₂ j)⁻¹ := by
          calc
            z = (zeta ^ l)⁻¹ * zeta ^ j := hcomm_pow.eq
            _ = (zeta ^ l)⁻¹ * (zeta ^ j * r₂ j) * (r₂ j)⁻¹ := by
              group
            _ = (zeta ^ l)⁻¹ * (zeta ^ l * r₂ l) * (r₂ j)⁻¹ := by
              rw [hdecomp]
            _ = r₂ l * (r₂ j)⁻¹ := by group
        have hzK : z ∈ K := by
          rw [hz_eq]
          exact K.mul_mem (hr₂K l) (K.inv_mem (hr₂K j))
        have hz_one : z = 1 := hK_inter_W z hzK hzW
        have hpows : zeta ^ j = zeta ^ l := by
          apply eq_of_mul_inv_eq_one
          exact hz_one
        have hmod : j ≡ l [MOD m] := by
          rw [← hzeta_order]
          exact pow_eq_pow_iff_modEq.mp hpows
        exact hmod.eq_of_lt_of_lt (by omega) (by omega)
      have hinput₂_ne_base : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
          input₂ j ≠ x₁ := by
        intro j hj hjm heq
        have hterm_ne : (kNorm * delta₂ j)⁻¹ ≠ 0 :=
          inv_ne_zero (mul_ne_zero hkNorm_ne (hdelta₂ j hj hjm))
        apply hterm_ne
        apply add_left_cancel (a := x₁)
        simpa [input₂] using heq
      have hinput₂_injective : ∀ j l : ℕ,
          1 ≤ j → j ≤ m - 1 → 1 ≤ l → l ≤ m - 1 →
            input₂ j = input₂ l → j = l := by
        intro j l hj hjm hl hlm hinput
        have hconjugates :
            rightConjugateElem (omega (i₂ : ℕ) * center (output₂ j)) (e₂ j) =
              rightConjugateElem (omega (i₂ : ℕ) * center (output₂ l)) (e₂ l) := by
          calc
            rightConjugateElem (omega (i₂ : ℕ) * center (output₂ j)) (e₂ j) =
                f (omega (i₁ : ℕ) * center (input₂ j)) :=
              (hclaim19b' j hj hjm).symm
            _ = f (omega (i₁ : ℕ) * center (input₂ l)) := by rw [hinput]
            _ = rightConjugateElem (omega (i₂ : ℕ) * center (output₂ l)) (e₂ l) :=
              hclaim19b' l hl hlm
        have heq := hconjugate_exponent_unique i₂ (output₂ j) (output₂ l)
          (e₂ j) (e₂ l) (he₂KW j) (he₂KW l) hconjugates
        exact he₂_index_injective j l hj hjm hl hlm heq
      let J := {j : ℕ // j ∈ Finset.Icc 1 (m - 1)}
      have hJ_bounds : ∀ j : J, 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ m - 1 := by
        intro j
        exact Finset.mem_Icc.mp j.property
      let candidateCoord : Option J → F
        | none => x₁
        | some j => input₂ (j : ℕ)
      have hcandidateCoord_injective : Function.Injective candidateCoord := by
        intro a b hab
        cases a with
        | none =>
            cases b with
            | none => rfl
            | some j =>
                exfalso
                exact hinput₂_ne_base (j : ℕ) (hJ_bounds j).1 (hJ_bounds j).2 hab.symm
        | some j =>
            cases b with
            | none =>
                exfalso
                exact hinput₂_ne_base (j : ℕ) (hJ_bounds j).1 (hJ_bounds j).2 hab
            | some l =>
                congr 1
                apply Subtype.ext
                exact hinput₂_injective (j : ℕ) (l : ℕ)
                  (hJ_bounds j).1 (hJ_bounds j).2 (hJ_bounds l).1 (hJ_bounds l).2 hab
      let Fiber₁₂ := {x : G // x ∈ Q0 ∧
        (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
          f (omega (i₁ : ℕ) * x) = rightConjugateElem (omega (i₂ : ℕ)) d * q0)}
      have hcardFiber₁₂ : Nat.card Fiber₁₂ = m := by
        have hcard := claim_8 H D Q K V W Q0 S Q1 KW
          t s (omega (i₁ : ℕ)) f g h m n (i₁ : ℕ) (i₂ : ℕ) omega hsection3 hC1 hC2
          htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
          hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq hKW rfl hn_card i₁.property i₂.property
          horbit_representatives rfl
        simpa [Fiber₁₂, hindices_ne_nat] using hcard
      have hbase_mem : center x₁ ∈ Q0 ∧
          ∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
            f (omega (i₁ : ℕ) * center x₁) =
              rightConjugateElem (omega (i₂ : ℕ)) d * q0 := by
        let q0 := rightConjugateElem (center x₂) k
        have hkD : k ∈ D := hsec.K_le_D hk
        have hq0 : q0 ∈ Q0 := hQ0_conj_D (center x₂) k (hcenter_mem_Q0 x₂) hkD
        refine ⟨hcenter_mem_Q0 x₁, k, q0, ?_, hq0, ?_⟩
        · rw [hKW]
          exact Subgroup.mem_sup_left hk
        · rw [← hrightConjugateElem_mul]
          exact hstart
      have hcandidate_mem : ∀ j : J, center (input₂ (j : ℕ)) ∈ Q0 ∧
          ∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
            f (omega (i₁ : ℕ) * center (input₂ (j : ℕ))) =
              rightConjugateElem (omega (i₂ : ℕ)) d * q0 := by
        intro j
        let q0 := rightConjugateElem (center (output₂ (j : ℕ))) (e₂ (j : ℕ))
        have heD : e₂ (j : ℕ) ∈ D := hKW_le_D (he₂KW (j : ℕ))
        have hq0 : q0 ∈ Q0 := hQ0_conj_D _ _ (hcenter_mem_Q0 _) heD
        refine ⟨hcenter_mem_Q0 _, e₂ (j : ℕ), q0, he₂KW (j : ℕ), hq0, ?_⟩
        rw [← hrightConjugateElem_mul]
        exact hclaim19b' (j : ℕ) (hJ_bounds j).1 (hJ_bounds j).2
      let candidateFiber : Option J → Fiber₁₂
        | none => ⟨center x₁, hbase_mem⟩
        | some j => ⟨center (input₂ (j : ℕ)), hcandidate_mem j⟩
      have hcandidateFiber_injective : Function.Injective candidateFiber := by
        intro a b hab
        have hv := congrArg (fun x : Fiber₁₂ ↦ (x : G)) hab
        apply hcandidateCoord_injective
        cases a <;> cases b <;>
          simp [candidateFiber, candidateCoord] at hv ⊢
        all_goals exact hcenter_injective hv
      letI : Fintype J := by
        dsimp [J]
        infer_instance
      have hcardJ : Nat.card J = m - 1 := by
        rw [Nat.card_eq_fintype_card]
        simp [J, Nat.card_Icc]
      have hcardOptionJ : Nat.card (Option J) = m := by
        rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card, hcardJ]
        omega
      have hcandidateFiber_bijective : Function.Bijective candidateFiber :=
        hcandidateFiber_injective.bijective_of_nat_card_le (by
          rw [hcardFiber₁₂, hcardOptionJ])
      have hclaim20 : ∀ x : F,
          (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
            f (omega (i₁ : ℕ) * center x) =
              rightConjugateElem (omega (i₂ : ℕ)) d * q0) →
          ∃ d : G, d ∈ KW ∧
            f (omega (i₁ : ℕ) * center x) =
              rightConjugateElem
                (omega (i₂ : ℕ) * center (x + alphaOf i₁)) d := by
        intro x hx
        let xf : Fiber₁₂ := ⟨center x, hcenter_mem_Q0 x, hx⟩
        obtain ⟨o, ho⟩ := hcandidateFiber_bijective.2 xf
        cases o with
        | none =>
            have hxone : x = x₁ := by
              apply hcenter_injective
              have hv := congrArg (fun z : Fiber₁₂ ↦ (z : G)) ho
              simpa [candidateFiber, xf] using hv.symm
            subst x
            exact hclaim20_at_base
        | some j =>
            have hxj : x = input₂ (j : ℕ) := by
              apply hcenter_injective
              have hv := congrArg (fun z : Fiber₁₂ ↦ (z : G)) ho
              simpa [candidateFiber, xf] using hv.symm
            subst x
            exact hclaim20_at_candidate (j : ℕ) (hJ_bounds j).1 (hJ_bounds j).2
      exact ⟨halpha, hclaim20⟩
    have halpha_all : ∀ i : ValidIndex, alphaOf i = alphaOf baseIndex := by
      intro i
      by_cases hi : i = baseIndex
      · rw [hi]
      · exact (hclaim20_general i baseIndex hi).1
    have htranslate : ∀ (i j : ValidIndex) (x : F),
        (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
          f (omega (i : ℕ) * center x) =
            rightConjugateElem (omega (j : ℕ)) d * q0) →
        ∃ d : G, d ∈ KW ∧
          f (omega (i : ℕ) * center x) =
            rightConjugateElem
              (omega (j : ℕ) * center (x + alphaOf i)) d := by
      intro i j x hx
      by_cases hij : i = j
      · subst j
        exact hclaim17_exhaustive i x hx
      · exact (hclaim20_general i j hij).2 x hx
    exact hfinish halpha_all htranslate
  · have hn_one : n = 1 := by omega
    have hindex_unique : ∀ i : ValidIndex, i = baseIndex := by
      intro i
      apply Subtype.ext
      dsimp [baseIndex]
      omega
    have halpha_all : ∀ i : ValidIndex, alphaOf i = alphaOf baseIndex := by
      intro i
      rw [hindex_unique i]
    have htranslate : ∀ (i j : ValidIndex) (x : F),
        (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
          f (omega (i : ℕ) * center x) =
            rightConjugateElem (omega (j : ℕ)) d * q0) →
        ∃ d : G, d ∈ KW ∧
          f (omega (i : ℕ) * center x) =
            rightConjugateElem
              (omega (j : ℕ) * center (x + alphaOf i)) d := by
      intro i j x hx
      have hij : i = j := (hindex_unique i).trans (hindex_unique j).symm
      subst j
      exact hclaim17_exhaustive i x hx
    exact hfinish halpha_all htranslate

end PFchapter4section2
end CFSG.BenderSuzuki
