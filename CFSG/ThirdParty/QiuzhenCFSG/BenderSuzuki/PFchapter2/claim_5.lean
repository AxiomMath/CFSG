module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_2_b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_15
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.corollary
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_b
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.GroupTheory.NoncommCoprod

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixIII
open PFchapter1section3

universe u v

/-!
# Peterfalvi, Part II, Chapter II, Claim (5)
-/

private theorem claim_5_Q1_eq_bot_from_star_card
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hStarF92 : Nat.card (nearFieldStar Q P) = 8) :
    Q1 = ⊥ := by
  have hQcard : Nat.card Q = 8 ^ p := by
    calc
      Nat.card Q = Nat.card (nearFieldStar Q P) ^ p := by
        simpa [nearFieldStar] using claim_4 H D Q K V W Q0 S Q1 P t s p hch
      _ = 8 ^ p := by rw [hStarF92]
  have hQ1_dvd_Q : Nat.card Q1 ∣ Nat.card Q := by
    simpa [Nat.card] using
      (Subgroup.card_dvd_of_le hch.section3.section2.Q1_le_Q :
        Nat.card Q1 ∣ Nat.card Q)
  have hQ1_dvd_two_pow : Nat.card Q1 ∣ 2 ^ (3 * p) := by
    have hQ1_dvd_eight_pow : Nat.card Q1 ∣ 8 ^ p := by
      exact hQ1_dvd_Q.trans (by rw [hQcard])
    have h8pow : 8 ^ p = 2 ^ (3 * p) := by
      rw [show 8 = 2 ^ 3 by norm_num, pow_mul]
    simpa [h8pow] using hQ1_dvd_eight_pow
  have hQ1_odd : Odd (Nat.card Q1) := hch.section3.section2.Q1_odd_order
  have hcoprime : Nat.Coprime (Nat.card Q1) (2 ^ (3 * p)) := by
    simpa [Nat.card] using (hQ1_odd.coprime_two_left.pow_left (3 * p)).symm
  have hQ1_card : Nat.card Q1 = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime dvd_rfl hQ1_dvd_two_pow
  exact Subgroup.eq_bot_of_card_eq (H := Q1) (by simpa [Nat.card] using hQ1_card)

set_option backward.isDefEq.respectTransparency false in
private theorem claim5_classify_dickson_of_cyclic_index_two_center_index
    {F : Type*} [PFAppendixII.RightNearField F] [Finite F]
    (A : Subgroup Fˣ) (hAcyc : IsCyclic A) (hAidx : A.index = 2)
    (hnoncomm : ¬ IsMulCommutative F)
    (hcenterIndex : (Subgroup.center Fˣ).index = 4) :
    Nat.card Fˣ = 8 ∧ PFAppendixII.IsDicksonIndexTwoModel F 3 1 := by
  rcases PFAppendixII.proposition_2 A hAcyc hAidx with
      hcomm | ⟨q, n, hmodel⟩
  · exfalso
    apply hnoncomm
    exact ⟨⟨hcomm⟩⟩
  rcases hmodel with ⟨hq, _hq2, hn, hmodel⟩
  dsimp at hmodel
  rcases hmodel with
    ⟨hqFact, e, he1, hsquare, hnonsquare, hcenterCard⟩
  let : Fact q.Prime := hqFact
  have hFcard : Nat.card F = q ^ (2 * n) := by
    calc
      Nat.card F = Nat.card (GaloisField q (2 * n)) := Nat.card_congr e.toEquiv
      _ = q ^ (2 * n) :=
        GaloisField.card (p := q) (n := 2 * n) (by omega)
  have hUnitsCard : Nat.card Fˣ = q ^ (2 * n) - 1 := by
    rw [Nat.card_units, hFcard]
  have hcenterMul : (q ^ n - 1) * 4 = q ^ (2 * n) - 1 := by
    calc
      (q ^ n - 1) * 4 = Nat.card (Subgroup.center Fˣ) *
          (Subgroup.center Fˣ).index := by rw [hcenterCard, hcenterIndex]
      _ = Nat.card Fˣ := (Subgroup.center Fˣ).card_mul_index
      _ = q ^ (2 * n) - 1 := hUnitsCard
  let r := q ^ n
  have hrgt : 1 < r := by
    dsimp [r]
    exact one_lt_pow₀ hq.one_lt hn.ne'
  have hsq : q ^ (2 * n) = r ^ 2 := by
    rw [show 2 * n = n + n by omega, pow_add, pow_two]
  have hfactor : r ^ 2 - 1 = (r - 1) * (r + 1) := by
    simpa [Nat.mul_comm] using Nat.sq_sub_sq r 1
  have hcancel : (r - 1) * 4 = (r - 1) * (r + 1) := by
    rw [← hfactor, ← hsq]
    simpa [r] using hcenterMul
  have hrpred : 0 < r - 1 := by omega
  have hr : r = 3 := by
    have := Nat.eq_of_mul_eq_mul_left hrpred hcancel
    omega
  have hq_dvd_three : q ∣ 3 := by
    rw [← hr]
    exact dvd_pow_self q hn.ne'
  have hqeq : q = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp hq_dvd_three |>.resolve_left hq.ne_one
  have hneq : n = 1 := by
    have hpow3 : 3 ^ n = 3 := by simpa [r, hqeq] using hr
    apply Nat.pow_right_injective (by omega : 2 ≤ 3)
    simpa using hpow3
  subst q
  subst n
  constructor
  · simpa using hUnitsCard
  · exact ⟨Nat.prime_three, by omega, by omega,
      inferInstance, e, he1, hsquare, hnonsquare, hcenterCard⟩

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem claim5_huppert_units_classification
    {F : Type*} [PFAppendixII.RightNearField F] [Finite F] :
    (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p Fˣ, IsCyclic P) ∧
      (∀ P : Sylow 2 Fˣ,
        IsCyclic P ∨ ∃ k : ℕ, 2 ≤ k ∧ IsPGroup 2 (QuaternionGroup k) ∧
          Nonempty (P ≃* QuaternionGroup k)) := by
  classical
  let rhoAdd : (Fˣ)ᵐᵒᵖ →* Multiplicative (F ≃+ F) :=
    PFAppendixII.rightNearFieldRightMulAction
  let rho : (Fˣ)ᵐᵒᵖ →* MulAut (Multiplicative F) :=
    { toFun := fun a => (Multiplicative.toAdd (rhoAdd a)).toMultiplicative
      map_one' := by
        ext x
        change Multiplicative.ofAdd (rhoAdd 1 (Multiplicative.toAdd x)) = x
        rw [map_one]
        rfl
      map_mul' := by
        intro a b
        ext x
        change Multiplicative.ofAdd (rhoAdd (a * b) (Multiplicative.toAdd x)) =
          Multiplicative.ofAdd (rhoAdd a (rhoAdd b (Multiplicative.toAdd x)))
        rw [map_mul]
        rfl }
  have hrho : Function.Injective rho := by
    intro a b hab
    apply MulOpposite.unop_injective
    apply Units.ext
    have h := congrArg
      (fun phi : MulAut (Multiplicative F) =>
        Multiplicative.toAdd (phi (Multiplicative.ofAdd (1 : F)))) hab
    simpa [rho, rhoAdd, PFAppendixII.rightNearFieldRightMulAction_apply] using h
  let A : Subgroup (MulAut (Multiplicative F)) := rho.range
  have hfixed : ∀ phi : A, phi ≠ 1 → ∀ x : Multiplicative F,
      (phi : MulAut (Multiplicative F)) x = x → x = 1 := by
    intro phi hphi x hx
    rcases phi.2 with ⟨a, ha⟩
    have hx' : rho a x = x := by rw [ha]; exact hx
    change Multiplicative.toAdd x = 0
    by_contra hx0
    have hmul : Multiplicative.toAdd x * (a.unop : F) =
        Multiplicative.toAdd x := by
      simpa [rho, rhoAdd, PFAppendixII.rightNearFieldRightMulAction_apply] using
        congrArg Multiplicative.toAdd hx'
    have haone : a.unop = 1 :=
      PFAppendixII.rightNearField_mul_right_fixed_of_ne_zero hx0 a.unop hmul
    have haop : a = 1 := MulOpposite.unop_injective (by simpa using haone)
    apply hphi
    apply Subtype.ext
    rw [← ha, haop, map_one]
    rfl
  have hclass :=
    External.huppert_V_8_15_fixedPointFree_automorphism_subgroup_classification
      A hfixed
  let eRange : (Fˣ)ᵐᵒᵖ ≃* A := MonoidHom.ofInjective hrho
  let eUnits : Fˣ ≃* A := (MulEquiv.inv' Fˣ).trans eRange
  constructor
  · intro p hpFact hp2 P
    let Pmap : Sylow p A :=
      P.mapSurjective (f := eUnits.toMonoidHom) eUnits.surjective
    have hcyc : IsCyclic Pmap := hclass.1 p hp2 Pmap
    let eP : P ≃* Pmap :=
      (Subgroup.equivMapOfInjective (P : Subgroup Fˣ) eUnits.toMonoidHom
        eUnits.injective).trans (MulEquiv.subgroupCongr (by rfl))
    exact eP.isCyclic.mpr hcyc
  · intro P
    let Pmap : Sylow 2 A :=
      P.mapSurjective (f := eUnits.toMonoidHom) eUnits.surjective
    let eP : P ≃* Pmap :=
      (Subgroup.equivMapOfInjective (P : Subgroup Fˣ) eUnits.toMonoidHom
        eUnits.injective).trans (MulEquiv.subgroupCongr (by rfl))
    rcases hclass.2.1 Pmap with hcyc | ⟨k, hk, hkP, eQ⟩
    · exact Or.inl (eP.isCyclic.mpr hcyc)
    · exact Or.inr ⟨k, hk, hkP, eQ.map fun e => eP.trans e⟩

private theorem quaternionGroup_two_not_commutative :
    ¬ IsMulCommutative (QuaternionGroup 2) := by
  intro h
  let : IsMulCommutative (QuaternionGroup 2) := h
  have hcomm := (IsMulCommutative.is_comm (M := QuaternionGroup 2)).comm
      (QuaternionGroup.a 1 : QuaternionGroup 2)
      (QuaternionGroup.xa 0 : QuaternionGroup 2)
  simp only [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hcomm
  have hbad := QuaternionGroup.xa.inj hcomm
  exact (by decide : (-(1 : ZMod 4)) ≠ 1) hbad

private theorem quaternionGroup_not_commutative_of_two_le
    (k : ℕ) (hk : 2 ≤ k) :
    ¬ IsMulCommutative (QuaternionGroup k) := by
  intro h
  let : IsMulCommutative (QuaternionGroup k) := h
  have hcomm := (IsMulCommutative.is_comm (M := QuaternionGroup k)).comm
      (QuaternionGroup.a 1 : QuaternionGroup k)
      (QuaternionGroup.xa 0 : QuaternionGroup k)
  simp only [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hcomm
  have hbad : (-(1 : ZMod (2 * k))) = 1 := by
    simpa using QuaternionGroup.xa.inj hcomm
  have hzeroTwo : (2 : ZMod (2 * k)) = 0 := by
    calc
      (2 : ZMod (2 * k)) = 1 + 1 := by norm_num
      _ = -1 + 1 := congrArg (fun z : ZMod (2 * k) => z + 1) hbad.symm
      _ = 0 := neg_add_cancel 1
  have hdvd : 2 * k ∣ 2 :=
    (ZMod.natCast_eq_zero_iff 2 (2 * k)).mp hzeroTwo
  have hle : 2 * k ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

private theorem quaternion_sylow_exponent_four_data
    {P : Type u} [Group P] [Finite P]
    (hclass : ∃ k : ℕ, 2 ≤ k ∧ IsPGroup 2 (QuaternionGroup k) ∧
      Nonempty (P ≃* QuaternionGroup k))
    (hexponent : ∀ x : P, x ^ 4 = 1) :
    ∃ X : Subgroup P,
      IsCyclic X ∧ X.index = 2 ∧
        Nat.card P = 8 ∧ Nat.card (Subgroup.center P) = 2 := by
  classical
  rcases hclass with ⟨k, hk, _hQk, ⟨e⟩⟩
  have hpow : (QuaternionGroup.a 1 : QuaternionGroup k) ^ 4 = 1 := by
    simpa using congrArg e (hexponent (e.symm (QuaternionGroup.a 1)))
  have hkdvd : 2 * k ∣ 4 := by
    rw [← QuaternionGroup.orderOf_a_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hk2 : k = 2 := by
    have hle : 2 * k ≤ 4 := Nat.le_of_dvd (by norm_num) hkdvd
    omega
  subst k
  have hPcard : Nat.card P = 8 := by
    calc
      Nat.card P = Nat.card (QuaternionGroup 2) := Nat.card_congr e.toEquiv
      _ = 8 := by
        rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hPnoncomm : ¬ IsMulCommutative P := by
    intro hPcomm
    let : IsMulCommutative P := hPcomm
    apply quaternionGroup_two_not_commutative
    refine ⟨⟨fun x y => ?_⟩⟩
    rw [← e.symm.injective.eq_iff, map_mul, map_mul]
    exact (IsMulCommutative.is_comm (M := P)).comm _ _
  have hPp : IsPGroup 2 P := by
    exact IsPGroup.of_card (p := 2) (G := P) (n := 3) (by simpa using hPcard)
  let X0 : Subgroup (QuaternionGroup 2) :=
    Subgroup.zpowers (QuaternionGroup.a 1 : QuaternionGroup 2)
  let X : Subgroup P := X0.map e.symm.toMonoidHom
  have hXcyclic : IsCyclic X := by
    exact isCyclic_of_surjective (e.symm.subgroupMap X0)
      (e.symm.subgroupMap X0).surjective
  have hXcard : Nat.card X = 4 := by
    calc
      Nat.card X = Nat.card X0 :=
        (Nat.card_congr (e.symm.subgroupMap X0).toEquiv).symm
      _ = 4 := by
        rw [Nat.card_zpowers, QuaternionGroup.orderOf_a_one]
  have hXindex : X.index = 2 := by
    have hmul := X.card_mul_index
    rw [hXcard, hPcard] at hmul
    omega
  have hcenterP : Nat.card (Subgroup.center P) = 2 := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Nontrivial P :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hPcard]; norm_num)
    have hcenter_ne_bot : Subgroup.center P ≠ ⊥ :=
      ne_of_gt hPp.bot_lt_center
    have hcenter_ne_one : Nat.card (Subgroup.center P) ≠ 1 := by
      intro h
      exact hcenter_ne_bot
        (Subgroup.eq_bot_of_card_eq (H := Subgroup.center P) (by simpa using h))
    have hcenter_two_dvd : 2 ∣ Nat.card (Subgroup.center P) :=
      (hPp.to_subgroup (Subgroup.center P)).card_eq_or_dvd.resolve_left
        hcenter_ne_one
    have hcenter_dvd_eight : Nat.card (Subgroup.center P) ∣ 8 := by
      simpa [hPcard] using
        (Subgroup.card_dvd_of_le (show Subgroup.center P ≤ (⊤ : Subgroup P) from le_top))
    have hcenter_le_eight : Nat.card (Subgroup.center P) ≤ 8 :=
      Nat.le_of_dvd (by norm_num) hcenter_dvd_eight
    have hcenter_ne_eight : Nat.card (Subgroup.center P) ≠ 8 := by
      intro hcenter
      have htop : Subgroup.center P = ⊤ :=
        Subgroup.eq_top_of_card_eq (Subgroup.center P) (by simpa [hPcard] using hcenter)
      apply hPnoncomm
      refine ⟨⟨fun x y => ?_⟩⟩
      exact ((Subgroup.mem_center_iff.mp (by rw [htop]; simp)) y).symm
    have hcenter_ne_four : Nat.card (Subgroup.center P) ≠ 4 := by
      intro hcenter
      have hquotcard : Nat.card (P ⧸ Subgroup.center P) = 2 := by
        have hmul :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
        rw [hPcard, hcenter] at hmul
        omega
      let : IsCyclic (P ⧸ Subgroup.center P) :=
        isCyclic_of_prime_card hquotcard
      let hPcomm : CommGroup P :=
        commGroupOfCyclicCenterQuotient
          (QuotientGroup.mk' (Subgroup.center P)) (by
            rw [QuotientGroup.ker_mk'])
      exact hPnoncomm ⟨⟨hPcomm.mul_comm⟩⟩
    interval_cases hz : Nat.card (Subgroup.center P)
    all_goals norm_num [hz] at *
  exact ⟨X, hXcyclic, hXindex, hPcard, hcenterP⟩

private theorem odd_normal_complement_isCyclic
    {A : Type u} [Group A] [Finite A]
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∀ P : Sylow p A, IsCyclic P)
    (N : Subgroup A) [N.Normal]
    (hNcop : Nat.Coprime 2 (Nat.card N))
    (hnil : Group.IsNilpotent A) :
    IsCyclic N := by
  let : Group.IsNilpotent A := hnil
  have hNZ : IsZGroup N := by
    constructor
    intro q hq R
    let : Fact q.Prime := ⟨hq⟩
    by_cases hq2 : q = 2
    · subst q
      have hRcard : Nat.card R = 1 := by
        rcases R.isPGroup'.card_eq_or_dvd with h | hdvd
        · exact h
        · exfalso
          exact (Nat.prime_two.coprime_iff_not_dvd.mp hNcop)
            (hdvd.trans R.card_subgroup_dvd_card)
      have : Subsingleton R := (Nat.card_eq_one_iff_unique.mp hRcard).1
      exact isCyclic_of_subsingleton
    · let RA : Subgroup A := (R : Subgroup N).map N.subtype
      have hRAp : IsPGroup q RA :=
        R.isPGroup'.map N.subtype
      obtain ⟨Q, hRA_le_Q⟩ := hRAp.exists_le_sylow
      have hQcyclic : IsCyclic Q := hodd q hq2 Q
      have hRAcyclic : IsCyclic RA := Subgroup.isCyclic_of_le hRA_le_Q
      let : IsCyclic RA := hRAcyclic
      let eR : R ≃* RA :=
        Subgroup.equivMapOfInjective (R : Subgroup N) N.subtype N.subtype_injective
      exact isCyclic_of_surjective eR.symm eR.symm.surjective
  let : IsZGroup N := hNZ
  let : Group.IsNilpotent N := Subgroup.isNilpotent N
  infer_instance

private theorem nilpotent_two_sylow_complement
    {A : Type u} [Group A] [Finite A]
    (hnil : Group.IsNilpotent A) (P : Sylow 2 A) :
    ∃ N : Subgroup A, ∃ _hNnormal : N.Normal,
      Nat.Coprime 2 (Nat.card N) ∧ (P : Subgroup A).IsComplement' N := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases External.hkt_hasNormalPComplement_of_nilpotent (p := 2) hnil with
    ⟨N, hNnormal, hNcop, hquotp⟩
  let : N.Normal := hNnormal
  obtain ⟨n, hquotcard⟩ := hquotp.exists_card_eq
  have hNindex : N.index = 2 ^ n := by
    rw [N.index_eq_card]
    exact hquotcard
  have hcop_index : (Nat.card N).Coprime N.index := by
    rw [hNindex]
    exact hNcop.symm.pow_right n
  obtain ⟨H, hNH⟩ := Subgroup.exists_right_complement'_of_coprime hcop_index
  have hHcard : Nat.card H = 2 ^ n := by
    rw [← hNH.symm.index_eq_card, hNindex]
  have hHp : IsPGroup 2 H :=
    IsPGroup.of_card (p := 2) (G := H) (n := n) hHcard
  have hHindex : H.index = Nat.card N := hNH.index_eq_card
  have hHnotdvd : ¬ 2 ∣ H.index := by
    rw [hHindex]
    exact Nat.prime_two.coprime_iff_not_dvd.mp hNcop
  let Hsyl : Sylow 2 A := hHp.toSylow hHnotdvd
  have hPnormal : (P : Subgroup A).Normal :=
    Group.IsNilpotent.sylow_normal hnil 2 P
  let : Unique (Sylow 2 A) := Sylow.unique_of_normal P hPnormal
  have hHP : H = (P : Subgroup A) := by
    exact congrArg (fun S : Sylow 2 A => (S : Subgroup A))
      (Subsingleton.elim Hsyl P)
  exact ⟨N, hNnormal, hNcop, by simpa [hHP] using hNH.symm⟩

private theorem claim5_nilpotent_core
    {A : Type u} [Group A] [Finite A]
    (hnil : Group.IsNilpotent A)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∀ P : Sylow p A, IsCyclic P)
    (htwo : ∀ P : Sylow 2 A,
      IsCyclic P ∨
        ∃ k : ℕ, 2 ≤ k ∧ IsPGroup 2 (QuaternionGroup k) ∧
          Nonempty (P ≃* QuaternionGroup k))
    (hnoncomm : ¬ IsMulCommutative A)
    (hexponent : ∀ P : Sylow 2 A, ¬ IsCyclic P → ∀ x : P, x ^ 4 = 1) :
    (∃ C : Subgroup A, IsCyclic C ∧ C.index = 2) ∧
      Nat.card A = 4 * Nat.card (Subgroup.center A) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 A := default
  have hPnormal : (P : Subgroup A).Normal :=
    Group.IsNilpotent.sylow_normal hnil 2 P
  have hPnotcyclic : ¬ IsCyclic P := by
    intro hPcyclic
    have hAZ : IsZGroup A := by
      constructor
      intro q hq Q
      let : Fact q.Prime := ⟨hq⟩
      by_cases hq2 : q = 2
      · subst q
        let : Unique (Sylow 2 A) := Sylow.unique_of_normal P hPnormal
        have hQP : Q = P := Subsingleton.elim Q P
        subst Q
        exact hPcyclic
      · exact hodd q hq2 Q
    let : Group.IsNilpotent A := hnil
    let : IsZGroup A := hAZ
    have : IsCyclic A := inferInstance
    exact hnoncomm (inferInstance : IsMulCommutative A)
  rcases (htwo P).resolve_left hPnotcyclic with hPclass
  rcases quaternion_sylow_exponent_four_data hPclass (hexponent P hPnotcyclic) with
    ⟨X, hXcyclic, hXindex, hPcard, hcenterP⟩
  rcases nilpotent_two_sylow_complement hnil P with
    ⟨N, hNnormal, hNcop, hPN⟩
  let : N.Normal := hNnormal
  have hNcyclic : IsCyclic N :=
    odd_normal_complement_isCyclic hodd N hNcop hnil
  have hPnormal' : (P : Subgroup A).Normal := hPnormal
  have hcommPN : ∀ p : P, ∀ n : N,
      Commute ((P : Subgroup A).subtype p) (N.subtype n) := by
    intro p n
    exact Subgroup.commute_of_normal_of_disjoint
      (P : Subgroup A) N hPnormal' hNnormal hPN.disjoint
        p n p.property n.property
  let fPN : P × N →* A :=
    (P : Subgroup A).subtype.noncommCoprod N.subtype hcommPN
  have hfPNbij : Function.Bijective fPN := by
    change Function.Bijective
      (fun x : P × N => ((x.1 : A) * (x.2 : A)))
    exact (Subgroup.isComplement_iff_bijective (P : Subgroup A) N).mp hPN
  let ePN : P × N ≃* A := MulEquiv.ofBijective fPN hfPNbij
  let fX : X →* A := (P : Subgroup A).subtype.comp X.subtype
  have hcommXN : ∀ x : X, ∀ n : N, Commute (fX x) (N.subtype n) := by
    intro x n
    exact hcommPN x n
  let fXN : X × N →* A := fX.noncommCoprod N.subtype hcommXN
  have hfXinj : Function.Injective fX :=
    (P : Subgroup A).subtype_injective.comp X.subtype_injective
  have hdisXN : Disjoint fX.range N.subtype.range := by
    have hfXrange : fX.range ≤ (P : Subgroup A) := by
      rintro a ⟨x, rfl⟩
      exact x.val.property
    simpa [N.range_subtype] using hPN.disjoint.mono hfXrange le_rfl
  have hfXNinj : Function.Injective fXN := by
    change Function.Injective (fX.noncommCoprod N.subtype hcommXN)
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨hfXinj, N.subtype_injective, hdisXN⟩
  let C : Subgroup A := fXN.range
  have hXNcyclic : IsCyclic (X × N) := by
    rw [Group.isCyclic_prod_iff]
    refine ⟨hXcyclic, hNcyclic, ?_⟩
    have hXcard : Nat.card X = 4 := by
      have hmul := X.card_mul_index
      rw [hXindex, hPcard] at hmul
      omega
    rw [hXcard]
    exact hNcop.pow_left 2
  have hCcyclic : IsCyclic C := by
    let : IsCyclic (X × N) := hXNcyclic
    exact isCyclic_of_surjective fXN.rangeRestrict fXN.rangeRestrict_surjective
  have hCcard : Nat.card C = 4 * Nat.card N := by
    calc
      Nat.card C = Nat.card (X × N) := by
        exact (Nat.card_congr
          (Equiv.ofBijective fXN.rangeRestrict
            ⟨fun x y h => hfXNinj (congrArg Subtype.val h),
              fXN.rangeRestrict_surjective⟩)).symm
      _ = Nat.card X * Nat.card N := Nat.card_prod X N
      _ = 4 * Nat.card N := by
        have hmul := X.card_mul_index
        rw [hXindex, hPcard] at hmul
        have hXcard : Nat.card X = 4 := by omega
        rw [hXcard]
  have hAcard : Nat.card A = 8 * Nat.card N := by
    rw [← hPN.card_mul_card, hPcard]
  have hCindex : C.index = 2 := by
    have hmul := C.card_mul_index
    rw [hCcard, hAcard] at hmul
    have hNpos : 0 < Nat.card N := Nat.card_pos
    nlinarith
  have hcenterNtop : Subgroup.center N = ⊤ := by
    apply le_antisymm le_top
    intro n _hn
    rw [Subgroup.mem_center_iff]
    let : IsCyclic N := hNcyclic
    exact fun g => mul_comm' g n
  have hcenterProd :
      Subgroup.center (P × N) =
        (Subgroup.center P).prod (Subgroup.center N) := by
    ext x
    simp only [Subgroup.mem_center_iff, Subgroup.mem_prod, Prod.fst_mul,
      Prod.snd_mul, Prod.ext_iff]
    constructor
    · intro h
      exact ⟨fun p => (h (p, 1)).1, fun n => (h (1, n)).2⟩
    · rintro ⟨hp, hn⟩ ⟨p, n⟩
      exact ⟨hp p, hn n⟩
  have hcenterProdCard :
      Nat.card (Subgroup.center (P × N)) = 2 * Nat.card N := by
    rw [hcenterProd]
    calc
      Nat.card ((Subgroup.center P).prod (Subgroup.center N)) =
          Nat.card (Subgroup.center P) * Nat.card (Subgroup.center N) := by
        rw [Nat.card_congr ((Subgroup.center P).prodEquiv (Subgroup.center N)).toEquiv,
          Nat.card_prod]
      _ = 2 * Nat.card N := by
        rw [hcenterP, hcenterNtop, Subgroup.card_top]
  have hcenterAcard : Nat.card (Subgroup.center A) = 2 * Nat.card N := by
    calc
      Nat.card (Subgroup.center A) = Nat.card (Subgroup.center (P × N)) :=
        Nat.card_congr (Subgroup.centerCongr ePN.symm).toEquiv
      _ = 2 * Nat.card N := hcenterProdCard
  refine ⟨⟨C, hCcyclic, hCindex⟩, ?_⟩
  rw [hAcard, hcenterAcard]
  ring

private theorem claim5_noncyclic_sylow_two_exponent
    {G F : Type*} [Group G] [Finite G]
    [PFAppendixII.RightNearField F] [Finite F]
    (Q S P : Subgroup G) (hQnil : Group.IsNilpotent Q)
    (hS_sylow : ∃ P2 : Sylow 2 Q, S = (P2 : Subgroup Q).map Q.subtype)
    (hSclass : IsMulCommutative S ∨ PFAppendixIII.IsSuzukiTwoGroup S)
    (unitEquiv : nearFieldStar Q P ≃* Fˣ)
    (htwo : ∀ R : Sylow 2 Fˣ,
      IsCyclic R ∨ ∃ k : ℕ, 2 ≤ k ∧ IsPGroup 2 (QuaternionGroup k) ∧
        Nonempty (R ≃* QuaternionGroup k))
    (R : Sylow 2 Fˣ) (hRnotcyclic : ¬ IsCyclic R) :
    ∀ x : R, x ^ 4 = 1 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hS_sylow with ⟨P2, hS⟩
  have hP2normal : (P2 : Subgroup Q).Normal :=
    Group.IsNilpotent.sylow_normal hQnil 2 P2
  let : Unique (Sylow 2 Q) := Sylow.unique_of_normal P2 hP2normal
  let starToQ : nearFieldStar Q P →* Q :=
    Subgroup.inclusion (show nearFieldStar Q P ≤ Q from inf_le_left)
  let rToQ : R →* Q :=
    starToQ.comp (unitEquiv.symm.toMonoidHom.comp
      (R : Subgroup Fˣ).subtype)
  have hrToQinj : Function.Injective rToQ :=
    (Subgroup.inclusion_injective
      (show nearFieldStar Q P ≤ Q from inf_le_left)).comp
        (unitEquiv.symm.injective.comp
          (R : Subgroup Fˣ).subtype_injective)
  have hRangeP : IsPGroup 2 rToQ.range :=
    R.isPGroup'.of_surjective rToQ.rangeRestrict
      rToQ.rangeRestrict_surjective
  obtain ⟨T, hRange_le⟩ := hRangeP.exists_le_sylow
  have hT : T = P2 := Subsingleton.elim T P2
  have hr_mem_P2 (x : R) : rToQ x ∈ (P2 : Subgroup Q) := by
    rw [← hT]
    apply hRange_le
    exact ⟨x, rfl⟩
  have hr_mem_S (x : R) : ((rToQ x : Q) : G) ∈ S := by
    rw [hS]
    exact ⟨rToQ x, hr_mem_P2 x, rfl⟩
  have hRnoncomm : ¬ IsMulCommutative R := by
    rcases (htwo R).resolve_left hRnotcyclic with ⟨k, hk, _hkP, ⟨e⟩⟩
    intro hRcomm
    apply quaternionGroup_not_commutative_of_two_le k hk
    let : IsMulCommutative R := hRcomm
    refine ⟨⟨fun a b => ?_⟩⟩
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact (IsMulCommutative.is_comm (M := R)).comm _ _
  have hSnotcomm : ¬ IsMulCommutative S := by
    intro hScomm
    apply hRnoncomm
    let : IsMulCommutative S := hScomm
    refine ⟨⟨fun x y => ?_⟩⟩
    apply hrToQinj
    rw [map_mul, map_mul]
    apply Subtype.ext
    let sx : S := ⟨((rToQ x : Q) : G), hr_mem_S x⟩
    let sy : S := ⟨((rToQ y : Q) : G), hr_mem_S y⟩
    have hxy := (IsMulCommutative.is_comm (M := S)).comm sx sy
    exact congrArg (fun z : S => (z : G)) hxy
  have hSuzuki : PFAppendixIII.IsSuzukiTwoGroup S :=
    hSclass.resolve_left hSnotcomm
  have hSexp : ∀ y : S, y ^ 4 = 1 :=
    (External.Higman.theorem1_center_quotient_orders_and_exponent
      hSuzuki).2.2.2.2
  intro x
  apply hrToQinj
  rw [map_pow, map_one]
  apply Subtype.ext
  let sx : S := ⟨((rToQ x : Q) : G), hr_mem_S x⟩
  exact congrArg (fun z : S => (z : G)) (hSexp sx)

/-- The group-theoretic core of Claim (5): a noncommutative near-field unit
group occurring inside the nilpotent group `Q` has a cyclic subgroup of index
two and center of index four. -/
private theorem claim5_units_structure_core
    {G F : Type*} [Group G] [Finite G]
    [PFAppendixII.RightNearField F] [Finite F]
    (Q S P : Subgroup G) (hQnil : Group.IsNilpotent Q)
    (hS_sylow : ∃ P2 : Sylow 2 Q, S = (P2 : Subgroup Q).map Q.subtype)
    (hSclass : IsMulCommutative S ∨ PFAppendixIII.IsSuzukiTwoGroup S)
    (unitEquiv : nearFieldStar Q P ≃* Fˣ)
    (hnotcomm : ¬ IsMulCommutative (nearFieldStar Q P)) :
    (¬ IsMulCommutative F) ∧
      ∃ A : Subgroup Fˣ, IsCyclic A ∧ A.index = 2 ∧
        (Subgroup.center Fˣ).index = 4 := by
  have hFnoncomm : ¬ IsMulCommutative F := by
    intro hFcomm
    apply hnotcomm
    refine ⟨⟨fun a b => ?_⟩⟩
    apply unitEquiv.injective
    rw [map_mul, map_mul]
    apply Units.ext
    exact (IsMulCommutative.is_comm (M := F)).comm _ _
  have hUnitsNoncomm : ¬ IsMulCommutative Fˣ := by
    intro hUnitsComm
    apply hnotcomm
    let : IsMulCommutative Fˣ := hUnitsComm
    refine ⟨⟨fun a b => ?_⟩⟩
    apply unitEquiv.injective
    rw [map_mul, map_mul]
    exact (IsMulCommutative.is_comm (M := Fˣ)).comm _ _
  have hClass := claim5_huppert_units_classification (F := F)
  have hUnitsNilpotent : Group.IsNilpotent Fˣ := by
    let : Group.IsNilpotent Q := hQnil
    let starInQ : Subgroup Q :=
      (nearFieldStar Q P).subgroupOf Q
    have hStarNilpotent : Group.IsNilpotent (nearFieldStar Q P) := by
      let : Group.IsNilpotent starInQ := Subgroup.isNilpotent starInQ
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe
          (show nearFieldStar Q P ≤ Q from inf_le_left))
    let : Group.IsNilpotent (nearFieldStar Q P) := hStarNilpotent
    exact Group.nilpotent_of_mulEquiv unitEquiv
  obtain ⟨⟨A, hAcyclic, hAindex⟩, hcenterCard⟩ :=
    claim5_nilpotent_core hUnitsNilpotent hClass.1 hClass.2 hUnitsNoncomm
      (fun R hRnotcyclic =>
        claim5_noncyclic_sylow_two_exponent Q S P hQnil hS_sylow
          hSclass unitEquiv hClass.2 R hRnotcyclic)
  have hcenterIndex : (Subgroup.center Fˣ).index = 4 := by
    have hmul := (Subgroup.center Fˣ).card_mul_index
    rw [hcenterCard] at hmul
    have hcenterPos : 0 < Nat.card (Subgroup.center Fˣ) := Nat.card_pos
    nlinarith
  exact ⟨hFnoncomm, A, hAcyclic, hAindex, hcenterIndex⟩

/-- Claim (5)'s classification endpoint for a specified Claim-(2b)
near-field witness. -/
public theorem claim_5_classify_nearFieldWitness
    {G F : Type*} [Group G] [Finite G]
    [PFAppendixII.RightNearField F] [Finite F]
    (Q S P : Subgroup G) (hQnil : Group.IsNilpotent Q)
    (hS_sylow : ∃ P2 : Sylow 2 Q, S = (P2 : Subgroup Q).map Q.subtype)
    (hSclass : IsMulCommutative S ∨ PFAppendixIII.IsSuzukiTwoGroup S)
    (unitEquiv : nearFieldStar Q P ≃* Fˣ)
    (hnotcomm : ¬ IsMulCommutative (nearFieldStar Q P)) :
    ¬ IsMulCommutative F ∧ Nat.card Fˣ = 8 ∧
      PFAppendixII.IsDicksonIndexTwoModel F 3 1 := by
  obtain ⟨hFnoncomm, A, hAcyclic, hAindex, hcenterIndex⟩ :=
    claim5_units_structure_core Q S P hQnil hS_sylow hSclass
      unitEquiv hnotcomm
  obtain ⟨hcard, hmodel⟩ :=
    claim5_classify_dickson_of_cyclic_index_two_center_index
      A hAcyclic hAindex hFnoncomm hcenterIndex
  exact ⟨hFnoncomm, hcard, hmodel⟩

public theorem claim_5
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hnearfield_not_field : ¬ IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (P : Set G))) :
    Nat.card (nearFieldStar Q P) = 8 ∧ Q1 = ⊥ ∧
      let C : Subgroup G := Subgroup.centralizer (P : Set G)
      let OmegaP : Type _ := {w : Ω // w ∈ fixedPointsOfSubgroup G Ω P}
      letI : MulAction C OmegaP := fixedPointCentralizerAction G Ω P
      let HP : Subgroup C := H.comap C.subtype
      let DP : Subgroup C := D.comap C.subtype
      let QP : Subgroup C := Q.comap C.subtype
      let core : Subgroup C := pointStabilizerCore C OmegaP
      ∃ hnormal : core.Normal,
        letI : core.Normal := hnormal
        let pi : C →* C ⧸ core := QuotientGroup.mk' core
        ∃ (F : Type v) (_ : PFAppendixII.RightNearField F) (_ : Finite F)
            (_ : Nontrivial F) (_unitEquiv : nearFieldStar Q P ≃* Fˣ),
          PFAppendixII.PropositionOneConclusion
              (HP.map pi) (DP.map pi) (QP.map pi) F ∧
            PFAppendixII.IsDicksonIndexTwoModel F 3 1 := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let OmegaP : Type _ := {w : Ω // w ∈ fixedPointsOfSubgroup G Ω P}
  let : MulAction C OmegaP := fixedPointCentralizerAction G Ω P
  let HP : Subgroup C := H.comap C.subtype
  let DP : Subgroup C := D.comap C.subtype
  let QP : Subgroup C := Q.comap C.subtype
  let core : Subgroup C := pointStabilizerCore C OmegaP
  have h2b := claim_2_b H D Q K V W Q0 S Q1 P t s p hch
  dsimp only at h2b
  rcases h2b with
    ⟨_hNcore, hnormal, _quotientAction, _hsmul, _hAbar,
      F, hF, hFfinite, hFnontrivial, unitEquiv, hPO, _hcharacteristic⟩
  let : core.Normal := hnormal
  let : PFAppendixII.RightNearField F := hF
  let : Finite F := hFfinite
  let : Nontrivial F := hFnontrivial
  have hQnil : Group.IsNilpotent Q :=
    PFchapter1section2.proposition_1_b H D Q K V W Q0 S Q1 t
      hch.section3.section2
  have hSclass : IsMulCommutative S ∨ PFAppendixIII.IsSuzukiTwoGroup S :=
    PFchapter1section2.corollary H D Q K V W Q0 S Q1 t
      hch.section3.section2
  obtain ⟨hFnoncomm, A, hAcyc, hAidx, hcenterIndex⟩ :=
    claim5_units_structure_core Q S P hQnil
      hch.section3.section2.S_sylow_in_Q hSclass unitEquiv
      hnearfield_not_field
  obtain ⟨hFstar, hDickson⟩ :=
    claim5_classify_dickson_of_cyclic_index_two_center_index
      A hAcyc hAidx hFnoncomm hcenterIndex
  have hStarCard : Nat.card (nearFieldStar Q P) = 8 := by
    calc
      Nat.card (nearFieldStar Q P) = Nat.card Fˣ :=
        Nat.card_congr unitEquiv.toEquiv
      _ = 8 := hFstar
  have hQ1 : Q1 = ⊥ :=
    claim_5_Q1_eq_bot_from_star_card
      H D Q K V W Q0 S Q1 P t s p hch hStarCard
  refine ⟨hStarCard, hQ1, ?_⟩
  dsimp only
  exact ⟨hnormal, F, hF, hFfinite, hFnontrivial,
    unitEquiv, hPO, hDickson⟩

end PFchapter2
end CFSG.BenderSuzuki
