module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.proposition_1_a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section3

open PFchapter1section1 PFAppendixIII
open PFchapter1section2

/-!
# Peterfalvi, Part II, Chapter I, Section 3, Proposition 1(b)
-/

private theorem eq_one_of_mem_odd_subgroup_of_sq_eq_one
    {G : Type*} [Group G] [Finite G] {D : Subgroup G}
    (hDodd : Odd (Nat.card D)) {x : G} (hxD : x ∈ D)
    (hx2 : x ^ 2 = 1) :
    x = 1 := by
  let xd : D := ⟨x, hxD⟩
  have hxd2 : xd ^ 2 = 1 := by
    ext
    simpa [xd] using hx2
  have horder_two : orderOf xd ∣ 2 := orderOf_dvd_of_pow_eq_one hxd2
  have horder_card : orderOf xd ∣ Nat.card D := orderOf_dvd_natCard xd
  have hcop : Nat.Coprime (Nat.card D) 2 := hDodd.coprime_two_right
  have horder_one : orderOf xd = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horder_card horder_two
  have hxd_one : xd = 1 := orderOf_eq_one_iff.mp horder_one
  simpa [xd] using congrArg Subtype.val hxd_one

private theorem t_mem_normalizer_D_of_A1_for_prop1b
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    t ∈ Subgroup.normalizer (D : Set G) := by
  classical
  rw [Subgroup.mem_normalizer_iff]
  intro d
  have ht_inv : t⁻¹ = t :=
    hA1.involution_t.inv_eq_self
  have ht_sq : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  have hforward : ∀ d : G, d ∈ D → t * d * t⁻¹ ∈ D := by
    intro d hdD
    have hdInf : d ∈ H ⊓ rightConjugate H t := by
      simpa [hA1.D_eq] using hdD
    rw [hA1.D_eq]
    have hdRight : d ∈ rightConjugate H t := hdInf.2
    rcases
      (show d ∈ H.conjBy t⁻¹ from by
        simpa [rightConjugate] using hdRight) with
      ⟨h, hhH, hmap⟩
    have hd_eq : t⁻¹ * h * t = d := by
      simpa [MulAut.conj_apply] using hmap
    have htarget : t * d * t⁻¹ = h := by
      calc
        t * d * t⁻¹ = t * (t⁻¹ * h * t) * t⁻¹ := by rw [hd_eq]
        _ = h := by
          simp [mul_assoc]
    constructor
    · simpa [htarget] using hhH
    · change t * d * t⁻¹ ∈ H.conjBy t⁻¹
      refine ⟨d, hdInf.1, ?_⟩
      calc
        (MulAut.conj t⁻¹) d = t⁻¹ * d * (t⁻¹)⁻¹ := rfl
        _ = t * d * t⁻¹ := by simp [ht_inv]
  constructor
  · exact hforward d
  · intro htdD
    have hback := hforward (t * d * t⁻¹) htdD
    have hcollapse : t * (t * (d * (t * t))) = d := by
      calc
        t * (t * (d * (t * t))) = (t * t) * (d * (t * t)) := by
          rw [← mul_assoc]
        _ = d := by simp [ht_sq]
    simpa [ht_inv, hcollapse, mul_assoc] using hback


public theorem k_inf_normalizer_le_centralizer_of_le_V
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 X : Subgroup G) (t s : G)
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
    (hX_le_V : X ≤ V) :
    K ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.centralizer (X : Set G) := by
  classical
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hkK : k ∈ K := hk.1
  have hkN : k ∈ Subgroup.normalizer (X : Set G) := hk.2
  have hxV : x ∈ V := hX_le_V hx
  have hVleD : V ≤ D :=
    PFchapter1section2.proposition_3_V_le_D H D Q K V W Q0 S Q1 t hsec.section2
  have hK_normal_in_D : (K.subgroupOf D).Normal :=
    (PFchapter1section2.proposition_2 H D Q K V W Q0 S Q1 t hsec.section2).2
  have hxD : x ∈ D := hVleD hxV
  have hkD : k ∈ D := hsec.section2.K_le_D hkK
  let y : G := k * x * k⁻¹ * x⁻¹
  have hyX : y ∈ X := by
    have hkxX : k * x * k⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hkN x).1 hx
    exact X.mul_mem hkxX (X.inv_mem hx)
  have hyD : y ∈ D := by
    exact D.mul_mem (D.mul_mem (D.mul_mem hkD hxD) (D.inv_mem hkD)) (D.inv_mem hxD)
  have hyK : y ∈ K := by
    let kD : D := ⟨k, hkD⟩
    let xD : D := ⟨x, hxD⟩
    have hkSub : kD ∈ K.subgroupOf D := by
      simpa [kD, Subgroup.mem_subgroupOf] using hkK
    have hkInvSub : kD⁻¹ ∈ K.subgroupOf D :=
      (K.subgroupOf D).inv_mem hkSub
    have hconjSub : xD * kD⁻¹ * xD⁻¹ ∈ K.subgroupOf D :=
      hK_normal_in_D.conj_mem kD⁻¹ hkInvSub xD
    have hconjK : x * k⁻¹ * x⁻¹ ∈ K := by
      simpa [xD, kD, Subgroup.mem_subgroupOf, mul_assoc] using hconjSub
    simpa [y, mul_assoc] using K.mul_mem hkK hconjK
  have hyV : y ∈ V := hX_le_V hyX
  have hyVpet : y ∈ peterfalviV D t := by
    simpa [hsec.section2.V_eq] using hyV
  have hy_right_conj_inv : rightConjugateElem y t = y⁻¹ :=
    (hsec.section2.K_def y).mp hyK |>.2
  have ht_inv : t⁻¹ = t :=
    hsec.section2.hA.A1.involution_t.inv_eq_self
  have ht_comm_y : t * y = y * t :=
    (Subgroup.mem_centralizer_iff.mp hyVpet.2) t (by simp)
  have hy_right_conj_self : rightConjugateElem y t = y := by
    calc
      rightConjugateElem y t = t⁻¹ * y * t := rfl
      _ = t * y * t := by rw [ht_inv]
      _ = y * t * t := by rw [ht_comm_y]
      _ = y := by
        have htt : t * t = 1 := by
          simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
        simp [mul_assoc, htt]
  have hy_eq_inv : y = y⁻¹ := by
    calc
      y = rightConjugateElem y t := hy_right_conj_self.symm
      _ = y⁻¹ := hy_right_conj_inv
  have hy2 : y ^ 2 = 1 := by
    have hy2mul : y * y = 1 := by
      calc
        y * y = y * y⁻¹ := by nth_rw 2 [hy_eq_inv]
        _ = 1 := by simp
    simpa [pow_two] using hy2mul
  have hy_one : y = 1 :=
    eq_one_of_mem_odd_subgroup_of_sq_eq_one hsec.section2.hA.A1.D_odd hyD hy2
  have hcomm : k * x = x * k := by
    have hy_one' : k * x * k⁻¹ * x⁻¹ = 1 := by
      simpa [y] using hy_one
    have hkxk : k * x * k⁻¹ = x := by
      calc
        k * x * k⁻¹ = (k * x * k⁻¹ * x⁻¹) * x := by simp [mul_assoc]
        _ = x := by rw [hy_one']; simp
    calc
      k * x = (k * x * k⁻¹) * k := by simp [mul_assoc]
      _ = x * k := by rw [hkxk]
  exact hcomm.symm

private theorem normalizer_le_centralizer_sup_D_inf_normalizer_of_fixed_pair
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 X : Subgroup G) (t s : G)
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
    (hX_ne : X ≠ ⊥) (hX_le_V : X ≤ V) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.centralizer (X : Set G) ⊔
        (D ⊓ Subgroup.normalizer (X : Set G)) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  obtain ⟨α, hH⟩ := hsec.section2.hA.A1.point_stabilizer
  let β : Ω := t⁻¹ • α
  have ht_inv : t⁻¹ = t :=
    hsec.section2.hA.A1.involution_t.inv_eq_self
  have hVleD : V ≤ D :=
    PFchapter1section2.proposition_3_V_le_D H D Q K V W Q0 S Q1 t hsec.section2
  have hX_le_D : X ≤ D := by
    intro x hx
    exact hVleD (hX_le_V hx)
  have hfix_alpha : α ∈ fixedPointsOfSubgroup G Ω X := by
    intro x hx
    have hxH : x ∈ H := hsec.section2.hA.A1.D_le_H (hX_le_D hx)
    change x ∈ MulAction.stabilizer G α
    simpa [hH] using hxH
  have hfix_beta : β ∈ fixedPointsOfSubgroup G Ω X := by
    intro x hx
    have hxVpet : x ∈ peterfalviV D t := by
      simpa [hsec.section2.V_eq] using hX_le_V hx
    have hcomm_xt : x * t = t * x :=
      ((Subgroup.mem_centralizer_iff.mp hxVpet.2) t (by simp)).symm
    have hcomm_xt_inv : x * t⁻¹ = t⁻¹ * x := by
      calc
        x * t⁻¹ = x * t := by rw [ht_inv]
        _ = t * x := hcomm_xt
        _ = t⁻¹ * x := by rw [ht_inv]
    calc
      x • β = x • (t⁻¹ • α) := rfl
      _ = (x * t⁻¹) • α := by rw [smul_smul]
      _ = (t⁻¹ * x) • α := by rw [hcomm_xt_inv]
      _ = t⁻¹ • (x • α) := by rw [smul_smul]
      _ = β := by rw [hfix_alpha x hx]
  have hαβ : α ≠ β := by
    intro h
    apply hsec.section2.hA.A1.t_not_mem_H
    rw [hH]
    change t • α = α
    simpa [β, ht_inv] using h.symm
  have hD_stab :
      D = MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := by
    simpa [β, hH, rightConjugate_stabilizer] using
      hsec.section2.hA.A1.D_eq
  have fixed_smul_of_mem_normalizer :
      ∀ {g : G}, g ∈ N → ∀ {ω : Ω},
        ω ∈ fixedPointsOfSubgroup G Ω X → g • ω ∈ fixedPointsOfSubgroup G Ω X := by
    intro g hgN ω hω x hx
    have hginvN : g⁻¹ ∈ N := N.inv_mem hgN
    have hx_conj : g⁻¹ * x * g ∈ X :=
      by
        have hx_conj' := (Subgroup.mem_normalizer_iff.mp hginvN x).1 hx
        simpa using hx_conj'
    calc
      x • (g • ω) = (x * g) • ω := by rw [smul_smul]
      _ = (g * (g⁻¹ * x * g)) • ω := by
        rw [show x * g = g * (g⁻¹ * x * g) by group]
      _ = g • ((g⁻¹ * x * g) • ω) := by rw [smul_smul]
      _ = g • ω := by rw [hω (g⁻¹ * x * g) hx_conj]
  intro g hgN
  have hgα : g • α ∈ fixedPointsOfSubgroup G Ω X :=
    fixed_smul_of_mem_normalizer hgN hfix_alpha
  have hgβ : g • β ∈ fixedPointsOfSubgroup G Ω X :=
    fixed_smul_of_mem_normalizer hgN hfix_beta
  have hgαβ : g • α ≠ g • β := by
    intro h
    apply hαβ
    have h' := congrArg (fun ω => g⁻¹ • ω) h
    simpa [smul_smul] using h'
  obtain ⟨c, hcC, hcα, hcβ⟩ :=
    proposition_1_a_pair_transitive_on_fixed_points
      H D Q K V W Q0 S Q1 X t s hsec hX_ne hX_le_V
      (g • α) (g • β) α β hgα hgβ hfix_alpha hfix_beta hgαβ hαβ
  let d : G := c * g
  have hdα : d ∈ MulAction.stabilizer G α := by
    change d • α = α
    calc
      d • α = c • (g • α) := by simp [d, smul_smul]
      _ = α := hcα
  have hdβ : d ∈ MulAction.stabilizer G β := by
    change d • β = β
    calc
      d • β = c • (g • β) := by simp [d, smul_smul]
      _ = β := hcβ
  have hdD : d ∈ D := by
    rw [hD_stab]
    exact ⟨hdα, hdβ⟩
  have hcN : c ∈ N := by
    exact centralizer_le_normalizer X hcC
  have hdN : d ∈ N := by
    exact N.mul_mem hcN hgN
  have hc_sup : c ∈ C ⊔ (D ⊓ N) :=
    (le_sup_left : C ≤ C ⊔ (D ⊓ N)) hcC
  have hd_sup : d ∈ C ⊔ (D ⊓ N) :=
    (le_sup_right : D ⊓ N ≤ C ⊔ (D ⊓ N)) ⟨hdD, hdN⟩
  have hmem : c⁻¹ * d ∈ C ⊔ (D ⊓ N) :=
    (C ⊔ (D ⊓ N)).mul_mem ((C ⊔ (D ⊓ N)).inv_mem hc_sup) hd_sup
  simpa [C, N, d] using hmem

public theorem section1_normalizer_factorization_for_X_le_V
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 X : Subgroup G) (t s : G)
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
    (hX_le_V : X ≤ V) :
    D ⊓ Subgroup.normalizer (X : Set G) ≤
      (K ⊓ Subgroup.normalizer (X : Set G)) ⊔
        (V ⊓ Subgroup.normalizer (X : Set G)) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let A : Subgroup G := D ⊓ N
  let Y : Subgroup G := A ⊓ Subgroup.centralizer ({t} : Set G)
  let Z : Set G := {z : G | z ∈ A ∧ rightConjugateElem z t = z⁻¹}
  have hAodd : Odd (Nat.card A) := by
    exact odd_of_card_dvd hsec.section2.hA.A1.D_odd
      (Subgroup.card_dvd_of_le (show A ≤ D from inf_le_left))
  have htC_X : t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxVpet : x ∈ peterfalviV D t := by
      simpa [hsec.section2.V_eq] using hX_le_V hx
    exact ((Subgroup.mem_centralizer_iff.mp hxVpet.2) t (by simp)).symm
  have htN_X : t ∈ N := by
    exact centralizer_le_normalizer X htC_X
  have htN_D : t ∈ Subgroup.normalizer (D : Set G) :=
    t_mem_normalizer_D_of_A1_for_prop1b H D Q t hsec.section2.hA.A1
  have ht_inv : t⁻¹ = t :=
    hsec.section2.hA.A1.involution_t.inv_eq_self
  have ht_sq : t * t = 1 := by
    simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
  have hN_forward : ∀ a : G, a ∈ N → t * a * t⁻¹ ∈ N := by
    intro a haN
    exact N.mul_mem (N.mul_mem htN_X haN) (N.inv_mem htN_X)
  have htN_A : t ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact ⟨(Subgroup.mem_normalizer_iff.mp htN_D a).1 ha.1,
        hN_forward a ha.2⟩
    · intro ha
      have hbackN := hN_forward (t * a * t⁻¹) ha.2
      have hcollapse : t * (t * (a * (t * t))) = a := by
        calc
          t * (t * (a * (t * t))) = (t * t) * (a * (t * t)) := by
            rw [← mul_assoc]
          _ = a := by simp [ht_sq]
      exact ⟨(Subgroup.mem_normalizer_iff.mp htN_D a).2 ha.1,
        by simpa [ht_inv, hcollapse, mul_assoc] using hbackN⟩
  have hbij :
      Set.BijOn (fun p : Y × Z => (p.1 : G) * (p.2 : G)) Set.univ (A : Set G) := by
    simpa [A, Y, Z] using
      (lemma_a (M := G) t A hsec.section2.hA.A1.involution_t hAodd htN_A).1
  intro d hd
  have hdA : d ∈ A := hd
  rcases hbij.2.2 hdA with ⟨p, _hp_univ, hp_eq⟩
  have hyY : (p.1 : G) ∈ Y := p.1.property
  have hyA : (p.1 : G) ∈ A := hyY.1
  have hyC_t : (p.1 : G) ∈ Subgroup.centralizer ({t} : Set G) := hyY.2
  have hyV : (p.1 : G) ∈ V := by
    rw [hsec.section2.V_eq]
    exact ⟨hyA.1, hyC_t⟩
  have hyN : (p.1 : G) ∈ N := hyA.2
  have hzZ : (p.2 : G) ∈ Z := p.2.property
  have hzA : (p.2 : G) ∈ A := hzZ.1
  have hzK : (p.2 : G) ∈ K :=
    (hsec.section2.K_def (p.2 : G)).2 ⟨hzA.1, hzZ.2⟩
  have hzN : (p.2 : G) ∈ N := hzA.2
  have hy_sup :
      (p.1 : G) ∈ (K ⊓ N) ⊔ (V ⊓ N) :=
    (le_sup_right : V ⊓ N ≤ (K ⊓ N) ⊔ (V ⊓ N)) ⟨hyV, hyN⟩
  have hz_sup :
      (p.2 : G) ∈ (K ⊓ N) ⊔ (V ⊓ N) :=
    (le_sup_left : K ⊓ N ≤ (K ⊓ N) ⊔ (V ⊓ N)) ⟨hzK, hzN⟩
  have hprod :
      (p.1 : G) * (p.2 : G) ∈ (K ⊓ N) ⊔ (V ⊓ N) :=
    ((K ⊓ N) ⊔ (V ⊓ N)).mul_mem hy_sup hz_sup
  simpa [N] using hp_eq ▸ hprod

private theorem d_inf_normalizer_le_centralizer_sup_V_inf_normalizer_of_factorization
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 X : Subgroup G) (t s : G)
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
    (hX_le_V : X ≤ V) :
    D ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.centralizer (X : Set G) ⊔
        (V ⊓ Subgroup.normalizer (X : Set G)) := by
  have hfactor :=
    section1_normalizer_factorization_for_X_le_V
      H D Q K V W Q0 S Q1 X t s hsec hX_le_V
  have hKcent :=
    k_inf_normalizer_le_centralizer_of_le_V
      H D Q K V W Q0 S Q1 X t s hsec hX_le_V
  exact hfactor.trans (sup_le (hKcent.trans le_sup_left) le_sup_right)

public theorem proposition_1_b
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 X : Subgroup G) (t s : G)
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
    (hX_ne : X ≠ ⊥) (hX_le_V : X ≤ V) :
    Subgroup.normalizer (X : Set G) =
      Subgroup.centralizer (X : Set G) ⊔ (V ⊓ Subgroup.normalizer (X : Set G)) := by
  classical
  apply le_antisymm
  · have h_to_D :
        Subgroup.normalizer (X : Set G) ≤
          Subgroup.centralizer (X : Set G) ⊔
            (D ⊓ Subgroup.normalizer (X : Set G)) :=
      normalizer_le_centralizer_sup_D_inf_normalizer_of_fixed_pair
        H D Q K V W Q0 S Q1 X t s hsec hX_ne hX_le_V
    have hD_to_V :
        D ⊓ Subgroup.normalizer (X : Set G) ≤
          Subgroup.centralizer (X : Set G) ⊔
            (V ⊓ Subgroup.normalizer (X : Set G)) :=
      d_inf_normalizer_le_centralizer_sup_V_inf_normalizer_of_factorization
        H D Q K V W Q0 S Q1 X t s hsec hX_le_V
    exact h_to_D.trans (sup_le le_sup_left hD_to_V)
  · exact sup_le (centralizer_le_normalizer X) inf_le_right

end PFchapter1section3
end CFSG.BenderSuzuki
