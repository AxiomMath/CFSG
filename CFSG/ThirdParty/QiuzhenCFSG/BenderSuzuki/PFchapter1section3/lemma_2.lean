module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.proposition_1_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_d
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section3

open PFchapter1section1 PFAppendixIII
open PFchapter1section2

/-!
# Peterfalvi, Part II, Chapter I, Section 3, Lemma 2
-/

private theorem lemma_2_rightConjugateSet_empty
    {G : Type*} [Group G] (g : G) :
    rightConjugateSet (∅ : Set G) g = ∅ := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, _⟩
    cases hx
  · intro hy
    cases hy

private theorem lemma_2_rightConjugateSet_comp
    {G : Type*} [Group G] (X : Set G) (g h : G) :
    rightConjugateSet (rightConjugateSet X g) h =
      rightConjugateSet X (g * h) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hz, hyz⟩
    rcases hz with ⟨x, hx, hzx⟩
    refine ⟨x, hx, ?_⟩
    rw [hyz, hzx]
    simp [rightConjugateElem, mul_assoc]
  · intro hy
    rcases hy with ⟨x, hx, hyx⟩
    refine ⟨rightConjugateElem x g, ⟨x, hx, rfl⟩, ?_⟩
    rw [hyx]
    simp [rightConjugateElem, mul_assoc]

private theorem lemma_2_rightConjugateSet_eq_self_of_mem_centralizer
    {G : Type*} [Group G] {Y : Set G} {h : G}
    (hC : h ∈ Subgroup.centralizer Y) :
    rightConjugateSet Y h = Y := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hzY, hyz⟩
    have hfix : rightConjugateElem z h = z := by
      have hcomm := (Subgroup.mem_centralizer_iff.mp hC) z hzY
      calc
        rightConjugateElem z h = h⁻¹ * z * h := rfl
        _ = h⁻¹ * (z * h) := by rw [mul_assoc]
        _ = h⁻¹ * (h * z) := by rw [← hcomm]
        _ = z := by simp
    rw [hyz, hfix]
    exact hzY
  · intro hy
    have hfix : rightConjugateElem y h = y := by
      have hcomm := (Subgroup.mem_centralizer_iff.mp hC) y hy
      calc
        rightConjugateElem y h = h⁻¹ * y * h := rfl
        _ = h⁻¹ * (y * h) := by rw [mul_assoc]
        _ = h⁻¹ * (h * y) := by rw [← hcomm]
        _ = y := by simp
    exact ⟨y, hy, hfix.symm⟩

private theorem lemma_2_same_conjugate_after_centralizer_adjustment
    {G : Type*} [Group G] {X Y : Set G} {g h : G}
    (hY : Y = rightConjugateSet X g)
    (hC : h ∈ Subgroup.centralizer Y) :
    Y = rightConjugateSet X (g * h) := by
  calc
    Y = rightConjugateSet Y h :=
      (lemma_2_rightConjugateSet_eq_self_of_mem_centralizer hC).symm
    _ = rightConjugateSet (rightConjugateSet X g) h := by rw [hY]
    _ = rightConjugateSet X (g * h) :=
      lemma_2_rightConjugateSet_comp X g h

private theorem lemma_2_rightConjugate_comp_subgroup
    {G : Type*} [Group G] (H : Subgroup G) (g h : G) :
    rightConjugate (rightConjugate H g) h =
      rightConjugate H (g * h) := by
  simp [rightConjugate, Subgroup.conjBy_conjBy, mul_inv_rev]

private theorem lemma_2_fixed_of_closure
    {G Ω : Type*} [Group G] [MulAction G Ω] {X : Set G} {ω : Ω}
    (hfix : ∀ x : G, x ∈ X → x • ω = ω) :
    ω ∈ fixedPointsOfSubgroup G Ω (Subgroup.closure X) := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      exact hfix y hy
  | one =>
      simp
  | mul a b _ha _hb ha hb =>
      calc
        (a * b) • ω = a • (b • ω) := by rw [mul_smul]
        _ = a • ω := by rw [hb]
        _ = ω := ha
  | inv a _ha ha =>
      have h := congrArg (fun z : Ω => a⁻¹ • z) ha
      simpa [smul_smul] using h.symm

private theorem lemma_2_rightConjugateElem_mem_rightConjugate
    {G : Type*} [Group G] {H : Subgroup G} {x g : G}
    (hx : x ∈ H) :
    rightConjugateElem x g ∈ rightConjugate H g := by
  rw [rightConjugate, rightConjugateElem, Subgroup.conjBy, Subgroup.mem_map]
  exact ⟨x, hx, by simp⟩

private theorem lemma_2_mem_rightConjugate_iff_conj_mem
    {G : Type*} [Group G] {H : Subgroup G} {t x : G} :
    x ∈ rightConjugate H t ↔ t * x * t⁻¹ ∈ H := by
  constructor
  · intro hx
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨t * x * t⁻¹, hx, ?_⟩
    simp [mul_assoc]

private theorem lemma_2_mem_normalizer_of_conjBy_eq
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : H.conjBy g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hxconj : g * x * g⁻¹ ∈ H.conjBy g := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    simpa [h] using hxconj
  · intro hx
    have h_inv : H.conjBy g⁻¹ = H := by
      simpa [h] using (Subgroup.conjBy_inv H g)
    have hxpre : x ∈ H.conjBy g⁻¹ := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨g * x * g⁻¹, hx, ?_⟩
      simp [mul_assoc]
    simpa [h_inv] using hxpre

private theorem lemma_2_mem_normalizer_of_rightConjugate_eq_self
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : rightConjugate H g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  apply lemma_2_mem_normalizer_of_conjBy_eq
  have h' : H.conjBy g⁻¹ = H := by
    simpa [rightConjugate] using h
  simpa [h'] using (Subgroup.conjBy_inv' H g)

private theorem lemma_2_conjugate_mem_normalizer_of_mem_rightConjugate_normalizer
    {G : Type*} [Group G] {H : Subgroup G} {t a : G}
    (haNorm : a ∈ Subgroup.normalizer ((rightConjugate H t) : Set G)) :
    t * a * t⁻¹ ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hyHt : rightConjugateElem x t ∈ rightConjugate H t :=
      lemma_2_rightConjugateElem_mem_rightConjugate (H := H) (g := t) hx
    have hzHt :
        a * rightConjugateElem x t * a⁻¹ ∈ rightConjugate H t :=
      (Subgroup.mem_normalizer_iff.mp haNorm (rightConjugateElem x t)).1 hyHt
    have hzH : t * (a * rightConjugateElem x t * a⁻¹) * t⁻¹ ∈ H :=
      (lemma_2_mem_rightConjugate_iff_conj_mem (H := H) (t := t)
        (x := a * rightConjugateElem x t * a⁻¹)).mp hzHt
    simpa [rightConjugateElem, mul_assoc] using hzH
  · intro hx
    have hzHt :
        a * rightConjugateElem x t * a⁻¹ ∈ rightConjugate H t := by
      apply (lemma_2_mem_rightConjugate_iff_conj_mem (H := H) (t := t)
        (x := a * rightConjugateElem x t * a⁻¹)).mpr
      simpa [rightConjugateElem, mul_assoc] using hx
    have hyHt : rightConjugateElem x t ∈ rightConjugate H t :=
      (Subgroup.mem_normalizer_iff.mp haNorm (rightConjugateElem x t)).2 hzHt
    have hxH : t * rightConjugateElem x t * t⁻¹ ∈ H :=
      (lemma_2_mem_rightConjugate_iff_conj_mem (H := H) (t := t)
        (x := rightConjugateElem x t)).mp hyHt
    simpa [rightConjugateElem, mul_assoc] using hxH

private theorem lemma_2_mem_D_of_adjusted_stabilizers
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s a : G)
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
    (haH : rightConjugate H a = H)
    (htaH : rightConjugate H (t * a) = rightConjugate H t) :
    a ∈ D := by
  have haNormH : a ∈ Subgroup.normalizer (H : Set G) :=
    lemma_2_mem_normalizer_of_rightConjugate_eq_self haH
  have hnormH := (proposition_1_d H D Q t hsec.section2.hA.A1).2
  have haHmem : a ∈ H := by
    simpa [hnormH] using haNormH
  have hfixHt :
      rightConjugate (rightConjugate H t) a = rightConjugate H t := by
    calc
      rightConjugate (rightConjugate H t) a =
          rightConjugate H (t * a) :=
        lemma_2_rightConjugate_comp_subgroup H t a
      _ = rightConjugate H t := htaH
  have haNormHt : a ∈ Subgroup.normalizer ((rightConjugate H t) : Set G) :=
    lemma_2_mem_normalizer_of_rightConjugate_eq_self hfixHt
  have htatNormH : t * a * t⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
    lemma_2_conjugate_mem_normalizer_of_mem_rightConjugate_normalizer haNormHt
  have htatH : t * a * t⁻¹ ∈ H := by
    simpa [hnormH] using htatNormH
  have haHt : a ∈ rightConjugate H t :=
    (lemma_2_mem_rightConjugate_iff_conj_mem (H := H) (t := t)
      (x := a)).mpr htatH
  rw [hsec.section2.hA.A1.D_eq]
  exact ⟨haHmem, haHt⟩

private theorem lemma_2_eq_one_of_mem_odd_subgroup_of_sq_eq_one
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

private theorem lemma_2_rightConjugateElem_eq_self_of_mem_centralizer
    {G : Type*} [Group G] {t x : G}
    (ht : IsInvolution t) (hx : x ∈ Subgroup.centralizer ({t} : Set G)) :
    rightConjugateElem x t = x := by
  change ∀ y ∈ ({t} : Set G), y * x = x * y at hx
  have hcomm : t * x = x * t := hx t (by simp)
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  calc
    rightConjugateElem x t = t * x * t := by
      rw [rightConjugateElem, ht.inv_eq_self]
    _ = x * (t * t) := by rw [hcomm, mul_assoc]
    _ = x := by simp [htt]

private theorem lemma_2_t_mem_normalizer_D
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
        _ = h := by simp [mul_assoc]
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

public theorem lemma_2_D_mem_decompose_VK
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s d : G)
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
    (hdD : d ∈ D) :
    ∃ v k : G, v ∈ V ∧ k ∈ K ∧ d = v * k := by
  classical
  let Y : Subgroup G := D ⊓ Subgroup.centralizer ({t} : Set G)
  let Z : Set G := {z : G | z ∈ D ∧ rightConjugateElem z t = z⁻¹}
  have htNormD : t ∈ Subgroup.normalizer (D : Set G) :=
    lemma_2_t_mem_normalizer_D H D Q t hsec.section2.hA.A1
  have hbij :
      Set.BijOn (fun p : Y × Z => (p.1 : G) * (p.2 : G)) Set.univ (D : Set G) := by
    simpa [Y, Z] using
      (lemma_a (M := G) t D hsec.section2.hA.A1.involution_t
        hsec.section2.hA.A1.D_odd htNormD).1
  rcases hbij.2.2 hdD with ⟨p, _hp_univ, hp_eq⟩
  have hvV : (p.1 : G) ∈ V := by
    rw [hsec.section2.V_eq]
    exact p.1.property
  have hkK : (p.2 : G) ∈ K :=
    (hsec.section2.K_def (p.2 : G)).mpr p.2.property
  exact ⟨p.1, p.2, hvV, hkK, hp_eq.symm⟩

private theorem lemma_2_rightConjugateElem_eq_self_of_K_mem_of_mem_V
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s a k : G)
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
    (haV : a ∈ V) (hkK : k ∈ K)
    (hconjV : rightConjugateElem a k ∈ V) :
    rightConjugateElem a k = a := by
  classical
  have hK_normal_in_D : (K.subgroupOf D).Normal :=
    (PFchapter1section2.proposition_2 H D Q K V W Q0 S Q1 t hsec.section2).2
  have haVpet : a ∈ peterfalviV D t := by
    simpa [hsec.section2.V_eq] using haV
  have hconjVpet : rightConjugateElem a k ∈ peterfalviV D t := by
    simpa [hsec.section2.V_eq] using hconjV
  have haD : a ∈ D := haVpet.1
  have hkD : k ∈ D := hsec.section2.K_le_D hkK
  let y : G := rightConjugateElem a k * a⁻¹
  have hyD : y ∈ D := by
    exact D.mul_mem hconjVpet.1 (D.inv_mem haD)
  have hyV : y ∈ V := by
    exact V.mul_mem hconjV (V.inv_mem haV)
  have hyK : y ∈ K := by
    let kD : D := ⟨k, hkD⟩
    let aD : D := ⟨a, haD⟩
    have hkSub : kD ∈ K.subgroupOf D := by
      simpa [kD, Subgroup.mem_subgroupOf] using hkK
    have hconjSub : aD * kD * aD⁻¹ ∈ K.subgroupOf D :=
      hK_normal_in_D.conj_mem kD hkSub aD
    have ha_k_a : a * k * a⁻¹ ∈ K := by
      simpa [aD, kD, Subgroup.mem_subgroupOf, mul_assoc] using hconjSub
    simpa [y, rightConjugateElem, mul_assoc] using K.mul_mem (K.inv_mem hkK) ha_k_a
  have hyVpet : y ∈ peterfalviV D t := by
    simpa [hsec.section2.V_eq] using hyV
  have hy_anti : rightConjugateElem y t = y⁻¹ :=
    (hsec.section2.K_def y).mp hyK |>.2
  have hy_fixed : rightConjugateElem y t = y :=
    lemma_2_rightConjugateElem_eq_self_of_mem_centralizer
      hsec.section2.hA.A1.involution_t hyVpet.2
  have hy_eq_inv : y = y⁻¹ := by
    calc
      y = rightConjugateElem y t := hy_fixed.symm
      _ = y⁻¹ := hy_anti
  have hy2 : y ^ 2 = 1 := by
    have hy2mul : y * y = 1 := by
      calc
        y * y = y * y⁻¹ := by nth_rw 2 [hy_eq_inv]
        _ = 1 := by simp
    simpa [pow_two] using hy2mul
  have hy_one : y = 1 :=
    lemma_2_eq_one_of_mem_odd_subgroup_of_sq_eq_one
      hsec.section2.hA.A1.D_odd hyD hy2
  have hy_one' : rightConjugateElem a k * a⁻¹ = 1 := by
    simpa [y] using hy_one
  calc
    rightConjugateElem a k =
        (rightConjugateElem a k * a⁻¹) * a := by simp [mul_assoc]
    _ = a := by rw [hy_one']; simp

private theorem lemma_2_double_transitive_centralizer_adjustment_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ X Y : Set G, (∃ x : G, x ∈ X) →
      X ⊆ (V : Set G) → Y ⊆ (V : Set G) →
      ∀ g : G, Y = rightConjugateSet X g →
        ∃ h : G, h ∈ Subgroup.centralizer Y ∧
          rightConjugate H (g * h) = H ∧
            rightConjugate H (t * (g * h)) = rightConjugate H t := by
  intro X Y _hX_nonempty hXV hYV g hY
  classical
  let Ysub : Subgroup G := Subgroup.closure Y
  by_cases hYsub_bot : Ysub = ⊥
  · refine ⟨g⁻¹, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hyY
      have hySub : y ∈ Ysub := Subgroup.subset_closure hyY
      have hy_one : y = 1 := by
        simpa [Ysub, hYsub_bot] using hySub
      simp [hy_one]
    · simpa [rightConjugate] using (Subgroup.conjBy_one H)
    · simp [rightConjugate]
  · have hYsub_ne : Ysub ≠ ⊥ := hYsub_bot
    have hYsub_le_V : Ysub ≤ V := by
      exact (Subgroup.closure_le (K := V)).2 hYV
    obtain ⟨α, hHα⟩ := hsec.section2.hA.A1.point_stabilizer
    let β : Ω := t⁻¹ • α
    have ht_inv : t⁻¹ = t := by
      have htt : t * t = 1 := by
        simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
      calc
        t⁻¹ = t⁻¹ * 1 := by simp
        _ = t⁻¹ * (t * t) := by rw [htt]
        _ = t := by simp
    have fixes_alpha_of_mem_V : ∀ x : G, x ∈ V → x • α = α := by
      intro x hxV
      have hxVD : x ∈ peterfalviV D t := by
        simpa [hsec.section2.V_eq] using hxV
      have hxH : x ∈ H := hsec.section2.hA.A1.D_le_H hxVD.1
      simpa [hHα, MulAction.mem_stabilizer_iff] using hxH
    have fixes_beta_of_mem_V : ∀ x : G, x ∈ V → x • β = β := by
      intro x hxV
      have hxVD : x ∈ peterfalviV D t := by
        simpa [hsec.section2.V_eq] using hxV
      have hcomm_xt : x * t = t * x :=
        ((Subgroup.mem_centralizer_iff.mp hxVD.2) t (by simp)).symm
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
        _ = β := by rw [fixes_alpha_of_mem_V x hxV]
    have hfix_alpha : α ∈ fixedPointsOfSubgroup G Ω Ysub := by
      intro y hy
      exact fixes_alpha_of_mem_V y (hYsub_le_V hy)
    have hfix_beta : β ∈ fixedPointsOfSubgroup G Ω Ysub := by
      intro y hy
      exact fixes_beta_of_mem_V y (hYsub_le_V hy)
    have hfix_ginv_of_X_fixed :
        ∀ ω : Ω, (∀ x : G, x ∈ X → x • ω = ω) →
          g⁻¹ • ω ∈ fixedPointsOfSubgroup G Ω Ysub := by
      intro ω hω
      apply lemma_2_fixed_of_closure
      intro y hyY
      have hyY' : y ∈ rightConjugateSet X g := by
        simpa [hY] using hyY
      rcases hyY' with ⟨x, hxX, hyx⟩
      rw [hyx]
      calc
        rightConjugateElem x g • (g⁻¹ • ω) = g⁻¹ • (x • ω) := by
          simp [rightConjugateElem, mul_assoc, smul_smul]
        _ = g⁻¹ • ω := by rw [hω x hxX]
    have hfix_galpha : g⁻¹ • α ∈ fixedPointsOfSubgroup G Ω Ysub :=
      hfix_ginv_of_X_fixed α fun x hxX => fixes_alpha_of_mem_V x (hXV hxX)
    have hfix_gbeta : g⁻¹ • β ∈ fixedPointsOfSubgroup G Ω Ysub :=
      hfix_ginv_of_X_fixed β fun x hxX => fixes_beta_of_mem_V x (hXV hxX)
    have hαβ : α ≠ β := by
      intro hαβ
      apply hsec.section2.hA.A1.t_not_mem_H
      rw [hHα]
      change t • α = α
      have hfix_inv : t⁻¹ • α = α := by
        simpa [β] using hαβ.symm
      calc
        t • α = t • (t⁻¹ • α) := by rw [hfix_inv]
        _ = (t * t⁻¹) • α := by rw [smul_smul]
        _ = α := by simp
    have hgαβ : g⁻¹ • α ≠ g⁻¹ • β := by
      intro h
      apply hαβ
      have h' := congrArg (fun z : Ω => g • z) h
      simpa [smul_smul] using h'
    obtain ⟨h, hCsub, hα, hβ⟩ :=
      proposition_1_a_pair_transitive_on_fixed_points
        H D Q K V W Q0 S Q1 Ysub t s hsec hYsub_ne hYsub_le_V
        α β (g⁻¹ • α) (g⁻¹ • β)
        hfix_alpha hfix_beta hfix_galpha hfix_gbeta hαβ hgαβ
    have hCY : h ∈ Subgroup.centralizer Y := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyY
      exact (Subgroup.mem_centralizer_iff.mp hCsub) y (Subgroup.subset_closure hyY)
    have hghH : rightConjugate H (g * h) = H := by
      rw [hHα, rightConjugate_stabilizer]
      have hpre : (g * h)⁻¹ • α = α := by
        have hback := congrArg (fun z : Ω => h⁻¹ • z) hα
        have hmap : h⁻¹ • (g⁻¹ • α) = α := by
          simpa [smul_smul] using hback.symm
        simpa [mul_inv_rev, smul_smul] using hmap
      rw [hpre]
    have htghHt : rightConjugate H (t * (g * h)) = rightConjugate H t := by
      rw [hHα, rightConjugate_stabilizer,
        rightConjugate_stabilizer]
      have hpre : (t * (g * h))⁻¹ • α = t⁻¹ • α := by
        have hback := congrArg (fun z : Ω => h⁻¹ • z) hβ
        have hmap : h⁻¹ • (g⁻¹ • β) = β := by
          simpa [smul_smul] using hback.symm
        simpa [β, mul_inv_rev, smul_smul, mul_assoc] using hmap
      rw [hpre]
    exact ⟨h, hCY, hghH, htghHt⟩

private theorem lemma_2_D_conjugator_of_double_transitive_centralizer_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ X Y : Set G, (∃ x : G, x ∈ X) →
      X ⊆ (V : Set G) → Y ⊆ (V : Set G) →
      ∀ g : G, Y = rightConjugateSet X g →
        ∃ h : G, h ∈ Subgroup.centralizer Y ∧ g * h ∈ D := by
  intro X Y hX_nonempty hXV hYV g hY
  rcases
    lemma_2_double_transitive_centralizer_adjustment_obligation
      H D Q K V W Q0 S Q1 t s hsec X Y hX_nonempty hXV hYV g hY
    with ⟨h, hC, hghH, htghHt⟩
  exact
    ⟨h, hC,
      lemma_2_mem_D_of_adjusted_stabilizers
        H D Q K V W Q0 S Q1 t s (g * h) hsec hghH htghHt⟩

private theorem lemma_2_D_conjugator_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ X Y : Set G, (∃ x : G, x ∈ X) →
      X ⊆ (V : Set G) → Y ⊆ (V : Set G) →
      (∃ g : G, Y = rightConjugateSet X g) →
        ∃ d : D, Y = rightConjugateSet X (d : G) := by
  intro X Y hX_nonempty hXV hYV hconj
  rcases hconj with ⟨g, hY⟩
  rcases
    lemma_2_D_conjugator_of_double_transitive_centralizer_obligation
      H D Q K V W Q0 S Q1 t s hsec X Y hX_nonempty hXV hYV g hY
    with ⟨h, hC, hghD⟩
  exact
    ⟨⟨g * h, hghD⟩,
      lemma_2_same_conjugate_after_centralizer_adjustment hY hC⟩

private theorem lemma_2_D_conjugator_projects_to_V_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ X Y : Set G, (∃ x : G, x ∈ X) →
      X ⊆ (V : Set G) → Y ⊆ (V : Set G) →
      (∃ d : D, Y = rightConjugateSet X (d : G)) →
        ∃ v : V, Y = rightConjugateSet X (v : G) := by
  intro X Y _hX_nonempty hXV hYV hDconj
  rcases hDconj with ⟨d, hYd⟩
  rcases
    lemma_2_D_mem_decompose_VK H D Q K V W Q0 S Q1 t s (d : G) hsec d.property
    with ⟨v, k, hvV, hkK, hd_eq⟩
  have hpoint :
      ∀ x : G, x ∈ X →
        rightConjugateElem x (d : G) = rightConjugateElem x v := by
    intro x hx
    have hxvV : rightConjugateElem x v ∈ V := by
      exact V.mul_mem (V.mul_mem (V.inv_mem hvV) (hXV hx)) hvV
    have hxdY : rightConjugateElem x (d : G) ∈ Y := by
      rw [hYd]
      exact ⟨x, hx, rfl⟩
    have hxdV : rightConjugateElem x (d : G) ∈ V := hYV hxdY
    have hcomp :
        rightConjugateElem x (d : G) =
          rightConjugateElem (rightConjugateElem x v) k := by
      rw [hd_eq]
      simp [rightConjugateElem, mul_assoc]
    have hconjV : rightConjugateElem (rightConjugateElem x v) k ∈ V := by
      simpa [← hcomp] using hxdV
    have hfix :
        rightConjugateElem (rightConjugateElem x v) k =
          rightConjugateElem x v :=
      lemma_2_rightConjugateElem_eq_self_of_K_mem_of_mem_V
        H D Q K V W Q0 S Q1 t s (rightConjugateElem x v) k hsec
        hxvV hkK hconjV
    exact hcomp.trans hfix
  refine ⟨⟨v, hvV⟩, ?_⟩
  rw [hYd]
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, hyx⟩
    exact ⟨x, hx, by rw [hyx, hpoint x hx]⟩
  · intro hy
    rcases hy with ⟨x, hx, hyx⟩
    exact ⟨x, hx, by rw [hyx, ← hpoint x hx]⟩

public theorem lemma_2
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ X Y : Set G, X ⊆ (V : Set G) → Y ⊆ (V : Set G) →
      (∃ g : G, Y = rightConjugateSet X g) →
        ∃ v : V, Y = rightConjugateSet X (v : G) := by
  intro X Y hXV hYV hconj
  by_cases hX_nonempty : ∃ x : G, x ∈ X
  · have hD :
        ∃ d : D, Y = rightConjugateSet X (d : G) :=
      lemma_2_D_conjugator_obligation H D Q K V W Q0 S Q1 t s hsec
        X Y hX_nonempty hXV hYV hconj
    exact
      lemma_2_D_conjugator_projects_to_V_obligation
        H D Q K V W Q0 S Q1 t s hsec X Y hX_nonempty hXV hYV hD
  · have hX_empty : X = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (hX_nonempty ⟨x, hx⟩)
      · intro hx
        cases hx
    rcases hconj with ⟨g, hY⟩
    refine ⟨⟨1, V.one_mem⟩, ?_⟩
    have hY_empty : Y = ∅ := by
      rw [hY, hX_empty, lemma_2_rightConjugateSet_empty]
    have htarget_empty : rightConjugateSet X (1 : G) = ∅ := by
      rw [hX_empty, lemma_2_rightConjugateSet_empty]
    rw [hY_empty, htarget_empty]

end PFchapter1section3
end CFSG.BenderSuzuki
