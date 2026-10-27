module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_c

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section3

open PFchapter1section1 PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 3, Lemma 3
-/

private theorem lemma_3_exists_involution_of_even_card
    {G : Type*} [Group G] [Finite G] (L : Subgroup G)
    (hL_even : Even (Nat.card L)) :
    ∃ u : G, u ∈ L ∧ IsInvolution u := by
  classical
  have hL_even_card : Even (Nat.card L) := by
    simpa [Nat.card, Nat.card_coe_set_eq] using hL_even
  have htwo_dvd_card : 2 ∣ Nat.card L := even_iff_two_dvd.mp hL_even_card
  obtain ⟨u, hu_order⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 htwo_dvd_card
  refine ⟨u, u.property, ?_⟩
  constructor
  · intro hu_one
    have horder_one : orderOf u = 1 := by
      have : u = 1 := by
        ext
        exact hu_one
      simp [this]
    omega
  · have hpow : u ^ 2 = 1 := by
      simpa [hu_order] using pow_orderOf_eq_one u
    exact congrArg Subtype.val hpow

private theorem lemma_3_rightConjugateElem_mul
    {G : Type*} [Group G] (x y g : G) :
    rightConjugateElem (x * y) g =
      rightConjugateElem x g * rightConjugateElem y g := by
  simp [rightConjugateElem, mul_assoc]

private theorem lemma_3_rightConjugateElem_right_inv
    {G : Type*} [Group G] (x g : G) :
    rightConjugateElem (rightConjugateElem x g) g⁻¹ = x := by
  simp [rightConjugateElem, mul_assoc]

private theorem lemma_3_rightConjugateElem_eq_one_iff
    {G : Type*} [Group G] (x g : G) :
    rightConjugateElem x g = 1 ↔ x = 1 := by
  constructor
  · intro h
    calc
      x = g * rightConjugateElem x g * g⁻¹ := by
        simp [rightConjugateElem, mul_assoc]
      _ = 1 := by simp [h]
  · intro h
    simp [rightConjugateElem, h]

private theorem lemma_3_sq_ne_one_of_rightConjugateElem_eq
    {G : Type*} [Group G] {x z g : G}
    (hx2 : x ^ 2 ≠ 1) (hxg : rightConjugateElem x g = z) :
    z ^ 2 ≠ 1 := by
  intro hz
  apply hx2
  have hconj_sq : rightConjugateElem (x ^ 2) g = z ^ 2 := by
    calc
      rightConjugateElem (x ^ 2) g = rightConjugateElem (x * x) g := by
        rw [pow_two]
      _ = rightConjugateElem x g * rightConjugateElem x g :=
        lemma_3_rightConjugateElem_mul x x g
      _ = z * z := by rw [hxg]
      _ = z ^ 2 := by rw [pow_two]
  have hx2_conj_one : rightConjugateElem (x ^ 2) g = 1 := by
    rw [hconj_sq, hz]
  exact (lemma_3_rightConjugateElem_eq_one_iff (x ^ 2) g).mp hx2_conj_one

private theorem lemma_3_rightConjugateElem_mem_centralizer_singleton
    {G : Type*} [Group G] {x y z g : G}
    (hyC : y ∈ Subgroup.centralizer ({x} : Set G))
    (hxg : rightConjugateElem x g = z) :
    rightConjugateElem y g ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  subst a
  rw [← hxg]
  have hcomm_yx : y * x = x * y :=
    Subgroup.mem_centralizer_singleton_iff.mp hyC
  have hcomm : x * y = y * x := hcomm_yx.symm
  calc
    rightConjugateElem x g * rightConjugateElem y g =
        rightConjugateElem (x * y) g := by
      rw [lemma_3_rightConjugateElem_mul]
    _ = rightConjugateElem (y * x) g := by rw [hcomm]
    _ = rightConjugateElem y g * rightConjugateElem x g :=
      lemma_3_rightConjugateElem_mul y x g


private theorem lemma_3_mem_rightConjugate_Q0_of_mem_rightConjugate_H
    {G : Type*} [Group G] {H Q0 : Subgroup G} {q t : G}
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hqH : q ∈ rightConjugate H t) (hqI : IsInvolution q) :
    q ∈ rightConjugate Q0 t := by
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hqH ⊢
  rcases hqH with ⟨h, hhH, hhq⟩
  refine ⟨h, ?_, hhq⟩
  have hhq' : rightConjugateElem h t = q := by
    simpa [rightConjugateElem, MulAut.conj_apply] using hhq
  have hhI : IsInvolution h := by
    have hconjI : IsInvolution (rightConjugateElem q t⁻¹) :=
      isInvolution_rightConjugateElem hqI
    have hback : rightConjugateElem q t⁻¹ = h := by
      rw [← hhq']
      exact lemma_3_rightConjugateElem_right_inv h t
    simpa [hback] using hconjI
  exact (hQ0_def h).mpr (Or.inr ⟨hhH, hhI⟩)

private theorem lemma_3_sq_eq_one_of_mem_rightConjugate_Q0
    {G : Type*} [Group G] {H Q0 : Subgroup G} {q t : G}
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hqQ0 : q ∈ rightConjugate Q0 t) :
    q ^ 2 = 1 := by
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hqQ0
  rcases hqQ0 with ⟨a, haQ0, haq⟩
  have haq' : rightConjugateElem a t = q := by
    simpa [rightConjugateElem, MulAut.conj_apply] using haq
  rcases (hQ0_def a).mp haQ0 with ha1 | haI
  · have hq1 : q = 1 := by
      rw [← haq']
      simp [rightConjugateElem, ha1]
    simp [hq1]
  · have hqI : IsInvolution q := by
      rw [← haq']
      exact isInvolution_rightConjugateElem haI.2
    exact hqI.sq_eq_one

private theorem lemma_3_sq_eq_one_of_left_endpoint_centralizes
    {G : Type*} [Group G] {q t : G}
    (hq2 : q ^ 2 = 1) (ht2 : t ^ 2 = 1)
    (hqC : q ∈ Subgroup.centralizer ({q * t} : Set G)) :
    (q * t) ^ 2 = 1 := by
  have hqmul : q * q = 1 := by
    simpa [pow_two] using hq2
  have hcomm : q * (q * t) = (q * t) * q :=
    Subgroup.mem_centralizer_singleton_iff.mp hqC
  have hqtq : q * t * q = t := by
    calc
      q * t * q = (q * t) * q := by rw [mul_assoc]
      _ = q * (q * t) := hcomm.symm
      _ = (q * q) * t := by rw [mul_assoc]
      _ = 1 * t := by rw [hqmul]
      _ = t := by rw [one_mul]
  calc
    (q * t) ^ 2 = q * t * q * t := by
      simp [pow_two, mul_assoc]
    _ = (q * t * q) * t := rfl
    _ = t * t := by rw [hqtq]
    _ = 1 := by simpa [pow_two] using ht2

private theorem lemma_3_sq_eq_one_of_right_endpoint_centralizes
    {G : Type*} [Group G] {q t : G}
    (hq2 : q ^ 2 = 1) (ht2 : t ^ 2 = 1)
    (htC : t ∈ Subgroup.centralizer ({q * t} : Set G)) :
    (q * t) ^ 2 = 1 := by
  have htmul : t * t = 1 := by
    simpa [pow_two] using ht2
  have hcomm : t * (q * t) = (q * t) * t :=
    Subgroup.mem_centralizer_singleton_iff.mp htC
  have htqt : t * q * t = q := by
    calc
      t * q * t = t * (q * t) := by rw [mul_assoc]
      _ = (q * t) * t := hcomm
      _ = q * (t * t) := by rw [mul_assoc]
      _ = q * 1 := by rw [htmul]
      _ = q := by rw [mul_one]
  calc
    (q * t) ^ 2 = q * t * q * t := by
      simp [pow_two, mul_assoc]
    _ = q * (t * q * t) := by group
    _ = q * q := by rw [htqt]
    _ = 1 := by simpa [pow_two] using hq2

private theorem lemma_3_involution_fix_t_to_rightConjugate_H_obligation
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
    ∀ u : G, IsInvolution u → (u * t) ^ 2 ≠ 1 →
      ∃ (q g : G), q ∈ rightConjugate H t ∧
        rightConjugateElem t g = t ∧ rightConjugateElem u g = q := by
  intro u hu hut2
  have hcontained :
      ∀ z : G, IsInvolution z →
        ∃ a : G, z ∈ rightConjugate H a := by
    intro z hz
    obtain ⟨a, ha⟩ :=
      proposition_2_b H D Q t hsec.section2.hA.A1
        s z hsec.s_involution hz
    refine ⟨a, ?_⟩
    rw [ha]
    rw [rightConjugate, rightConjugateElem, Subgroup.conjBy,
      Subgroup.mem_map]
    exact ⟨s, hsec.s_mem_H, by simp⟩
  obtain ⟨a, hua⟩ := hcontained u hu
  obtain ⟨b, htb⟩ :=
    hcontained t hsec.section2.hA.A1.involution_t
  have hcontaining_distinct :
      rightConjugate H a ≠ rightConjugate H b := by
    intro heq
    have hta : t ∈ rightConjugate H a := by
      rw [heq]
      exact htb
    have hback_mem :
        ∀ z : G, z ∈ rightConjugate H a →
          rightConjugateElem z a⁻¹ ∈ H := by
      intro z hz
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hz
      rcases hz with ⟨z₀, hz₀H, hz₀z⟩
      have hz₀z' : rightConjugateElem z₀ a = z := by
        simpa [rightConjugateElem, MulAut.conj_apply] using hz₀z
      rw [← hz₀z',
        lemma_3_rightConjugateElem_right_inv z₀ a]
      exact hz₀H
    let u₀ : G := rightConjugateElem u a⁻¹
    let t₀ : G := rightConjugateElem t a⁻¹
    have hu₀H : u₀ ∈ H := hback_mem u hua
    have ht₀H : t₀ ∈ H := hback_mem t hta
    have hu₀I : IsInvolution u₀ := by
      dsimp [u₀]
      exact isInvolution_rightConjugateElem hu
    have ht₀I : IsInvolution t₀ := by
      dsimp [t₀]
      exact
        isInvolution_rightConjugateElem
          hsec.section2.hA.A1.involution_t
    have hu₀Q0 : u₀ ∈ Q0 :=
      (hsec.section2.Q0_def u₀).mpr (Or.inr ⟨hu₀H, hu₀I⟩)
    have ht₀Q0 : t₀ ∈ Q0 :=
      (hsec.section2.Q0_def t₀).mpr (Or.inr ⟨ht₀H, ht₀I⟩)
    have hprodQ0 : u₀ * t₀ ∈ Q0 := Q0.mul_mem hu₀Q0 ht₀Q0
    have hprod_sq : (u₀ * t₀) ^ 2 = 1 := by
      have hsq :=
        (_root_.CFSG.BenderSuzuki.PFchapter1section2.proposition_1_c
          H D Q K V W Q0 S Q1 t hsec.section2).2.2
          ⟨u₀ * t₀, hprodQ0⟩
      exact congrArg Subtype.val hsq
    have hprod_conj :
        rightConjugateElem (u * t) a⁻¹ = u₀ * t₀ := by
      exact lemma_3_rightConjugateElem_mul u t a⁻¹
    exact
      (lemma_3_sq_ne_one_of_rightConjugateElem_eq hut2 hprod_conj)
        hprod_sq
  obtain ⟨r, hrQ, hsr⟩ := hsec.s_conjugate
  let d : G := t * r⁻¹ * t
  have ht_target : t ∈ rightConjugate H d := by
    have hst : rightConjugateElem s d = t := by
      have htt : t * t = 1 := by
        simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
      dsimp [d, rightConjugateElem]
      rw [mul_inv_rev, mul_inv_rev, inv_inv,
        hsec.section2.hA.A1.involution_t.inv_eq_self]
      calc
        t * (r * t) * s * (t * r⁻¹ * t) =
            t * r * (t * s * t) * r⁻¹ * t := by group
        _ = t * r * (r⁻¹ * t * r) * r⁻¹ * t := by rw [hsr]
        _ = t := by simp [mul_assoc, htt]
    rw [← hst]
    rw [rightConjugate, rightConjugateElem, Subgroup.conjBy,
      Subgroup.mem_map]
    exact ⟨s, hsec.s_mem_H, by simp⟩
  have ht_not_mem_Ht : t ∉ rightConjugate H t := by
    intro htHt
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at htHt
    rcases htHt with ⟨a₀, ha₀H, ha₀t⟩
    have ha₀t' : rightConjugateElem a₀ t = t := by
      simpa [rightConjugateElem, MulAut.conj_apply] using ha₀t
    apply hsec.section2.hA.A1.t_not_mem_H
    have ha₀_eq : a₀ = t := by
      calc
        a₀ = rightConjugateElem (rightConjugateElem a₀ t) t⁻¹ :=
          (lemma_3_rightConjugateElem_right_inv a₀ t).symm
        _ = rightConjugateElem t t⁻¹ := by rw [ha₀t']
        _ = t := by
          have htt : t * t = 1 := by
            simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
          simp [rightConjugateElem,
            hsec.section2.hA.A1.involution_t.inv_eq_self, htt]
    simpa [ha₀_eq] using ha₀H
  have htarget_distinct :
      rightConjugate H t ≠ rightConjugate H d := by
    intro heq
    exact ht_not_mem_Ht (heq ▸ ht_target)
  have htriple_transitive :
      ∀ a₁ b₁ a₂ b₂ z₁ z₂ : G,
        rightConjugate H a₁ ≠ rightConjugate H b₁ →
        rightConjugate H a₂ ≠ rightConjugate H b₂ →
        z₁ ∈ rightConjugate H b₁ → IsInvolution z₁ →
        z₂ ∈ rightConjugate H b₂ → IsInvolution z₂ →
        ∀ x : G, x ∈ rightConjugate H a₁ →
          ∃ g : G, rightConjugateElem x g ∈ rightConjugate H a₂ ∧
            rightConjugateElem z₁ g = z₂ := by
    classical
    obtain ⟨base, hHbase⟩ :=
      hsec.section2.hA.A1.point_stabilizer
    subst H
    intro a₁ b₁ a₂ b₂ z₁ z₂ hsource_ne htarget_ne
      hz₁ hz₁I hz₂ hz₂I x hx
    let source₁ : Ω := a₁⁻¹ • base
    let source₂ : Ω := b₁⁻¹ • base
    let target₁ : Ω := a₂⁻¹ • base
    let target₂ : Ω := b₂⁻¹ • base
    have hsource_points : source₁ ≠ source₂ := by
      intro hpoints
      apply hsource_ne
      rw [rightConjugate_stabilizer, rightConjugate_stabilizer]
      simpa [source₁, source₂] using
        congrArg (MulAction.stabilizer G) hpoints
    have htarget_points : target₁ ≠ target₂ := by
      intro hpoints
      apply htarget_ne
      rw [rightConjugate_stabilizer, rightConjugate_stabilizer]
      simpa [target₁, target₂] using
        congrArg (MulAction.stabilizer G) hpoints
    obtain ⟨k, hk₁, hk₂⟩ :=
      (MulAction.is_two_pretransitive_iff.mp
        hsec.section2.hA.A1.two_transitive)
        hsource_points htarget_points
    have hk₁_inv : k⁻¹ • target₁ = source₁ := by
      calc
        k⁻¹ • target₁ = k⁻¹ • (k • source₁) := by rw [hk₁]
        _ = source₁ := by simp [smul_smul]
    have hk₂_inv : k⁻¹ • target₂ = source₂ := by
      calc
        k⁻¹ • target₂ = k⁻¹ • (k • source₂) := by rw [hk₂]
        _ = source₂ := by simp [smul_smul]
    let x₀ : G := rightConjugateElem x k⁻¹
    let z₀ : G := rightConjugateElem z₁ k⁻¹
    have hx₀ : x₀ ∈ MulAction.stabilizer G target₁ := by
      have hxfix : x • source₁ = source₁ := by
        have hx' : x ∈ MulAction.stabilizer G source₁ := by
          simpa [source₁, rightConjugate_stabilizer] using hx
        exact MulAction.mem_stabilizer_iff.mp hx'
      rw [MulAction.mem_stabilizer_iff]
      dsimp [x₀]
      calc
        rightConjugateElem x k⁻¹ • target₁ =
            k • (x • (k⁻¹ • target₁)) := by
              simp [rightConjugateElem, mul_smul]
        _ = k • (x • source₁) := by rw [hk₁_inv]
        _ = k • source₁ := by rw [hxfix]
        _ = target₁ := hk₁
    have hz₀ : z₀ ∈ MulAction.stabilizer G target₂ := by
      have hz₁fix : z₁ • source₂ = source₂ := by
        have hz₁' : z₁ ∈ MulAction.stabilizer G source₂ := by
          simpa [source₂, rightConjugate_stabilizer] using hz₁
        exact MulAction.mem_stabilizer_iff.mp hz₁'
      rw [MulAction.mem_stabilizer_iff]
      dsimp [z₀]
      calc
        rightConjugateElem z₁ k⁻¹ • target₂ =
            k • (z₁ • (k⁻¹ • target₂)) := by
              simp [rightConjugateElem, mul_smul]
        _ = k • (z₁ • source₂) := by rw [hk₂_inv]
        _ = k • source₂ := by rw [hz₁fix]
        _ = target₂ := hk₂
    have hz₀I : IsInvolution z₀ := by
      dsimp [z₀]
      exact isInvolution_rightConjugateElem hz₁I
    let beta : Ω := t⁻¹ • base
    have hbase_beta : base ≠ beta := by
      intro heq
      apply hsec.section2.hA.A1.t_not_mem_H
      change t • base = base
      have htinv : t⁻¹ = t :=
        hsec.section2.hA.A1.involution_t.inv_eq_self
      simpa [beta, htinv] using heq.symm
    obtain ⟨c, hcbase, hcbeta⟩ :=
      (MulAction.is_two_pretransitive_iff.mp
        hsec.section2.hA.A1.two_transitive)
        hbase_beta htarget_points.symm
    have hcbase_inv : c⁻¹ • target₂ = base := by
      calc
        c⁻¹ • target₂ = c⁻¹ • (c • base) := by rw [hcbase]
        _ = base := by simp [smul_smul]
    have hcbeta_inv : c⁻¹ • target₁ = beta := by
      calc
        c⁻¹ • target₁ = c⁻¹ • (c • beta) := by rw [hcbeta]
        _ = beta := by simp [smul_smul]
    let z₀' : G := rightConjugateElem z₀ c
    let z₂' : G := rightConjugateElem z₂ c
    have hz₀'H : z₀' ∈ MulAction.stabilizer G base := by
      have hz₀fix : z₀ • target₂ = target₂ :=
        MulAction.mem_stabilizer_iff.mp hz₀
      rw [MulAction.mem_stabilizer_iff]
      dsimp [z₀']
      calc
        rightConjugateElem z₀ c • base =
            c⁻¹ • (z₀ • (c • base)) := by
              simp [rightConjugateElem, mul_smul]
        _ = c⁻¹ • (z₀ • target₂) := by rw [hcbase]
        _ = c⁻¹ • target₂ := by rw [hz₀fix]
        _ = base := hcbase_inv
    have hz₂'H : z₂' ∈ MulAction.stabilizer G base := by
      have hz₂fix : z₂ • target₂ = target₂ := by
        have hz₂' : z₂ ∈ MulAction.stabilizer G target₂ := by
          simpa [target₂, rightConjugate_stabilizer] using hz₂
        exact MulAction.mem_stabilizer_iff.mp hz₂'
      rw [MulAction.mem_stabilizer_iff]
      dsimp [z₂']
      calc
        rightConjugateElem z₂ c • base =
            c⁻¹ • (z₂ • (c • base)) := by
              simp [rightConjugateElem, mul_smul]
        _ = c⁻¹ • (z₂ • target₂) := by rw [hcbase]
        _ = c⁻¹ • target₂ := by rw [hz₂fix]
        _ = base := hcbase_inv
    have hz₀'I : IsInvolution z₀' := by
      dsimp [z₀']
      exact isInvolution_rightConjugateElem hz₀I
    have hz₂'I : IsInvolution z₂' := by
      dsimp [z₂']
      exact isInvolution_rightConjugateElem hz₂I
    obtain ⟨m, hmK, hmz⟩ :=
      ((proposition_3 (MulAction.stabilizer G base) D Q t
        hsec.section2.hA.A1).2 z₀' hz₀'H hz₀'I z₂').mp
        ⟨hz₂'H, hz₂'I⟩
    have hm_pair :
        m ∈ MulAction.stabilizer G base ⊓
          MulAction.stabilizer G beta := by
      have hmD : m ∈ D := hmK.1
      rw [hsec.section2.hA.A1.D_eq] at hmD
      refine ⟨hmD.1, ?_⟩
      simpa [beta, rightConjugate_stabilizer] using hmD.2
    let h : G := c * m * c⁻¹
    have hh_target₁ : h ∈ MulAction.stabilizer G target₁ := by
      have hmfix : m • beta = beta :=
        MulAction.mem_stabilizer_iff.mp hm_pair.2
      rw [MulAction.mem_stabilizer_iff]
      dsimp [h]
      calc
        (c * m * c⁻¹) • target₁ =
            c • (m • (c⁻¹ • target₁)) := by simp [mul_smul]
        _ = c • (m • beta) := by rw [hcbeta_inv]
        _ = c • beta := by rw [hmfix]
        _ = target₁ := hcbeta
    have hz_adjust : rightConjugateElem z₀ h = z₂ := by
      dsimp [h]
      calc
        rightConjugateElem z₀ (c * m * c⁻¹) =
            rightConjugateElem
              (rightConjugateElem (rightConjugateElem z₀ c) m) c⁻¹ := by
                simp [rightConjugateElem, mul_assoc]
        _ = rightConjugateElem (rightConjugateElem z₀' m) c⁻¹ := rfl
        _ = rightConjugateElem z₂' c⁻¹ := by rw [hmz]
        _ = z₂ := by
          dsimp [z₂']
          exact lemma_3_rightConjugateElem_right_inv z₂ c
    have hx_adjust :
        rightConjugateElem x₀ h ∈ MulAction.stabilizer G target₁ := by
      simpa [rightConjugateElem] using
        (MulAction.stabilizer G target₁).mul_mem
          ((MulAction.stabilizer G target₁).mul_mem
            ((MulAction.stabilizer G target₁).inv_mem hh_target₁) hx₀)
          hh_target₁
    refine ⟨k⁻¹ * h, ?_, ?_⟩
    · simpa [x₀, source₁, target₁, rightConjugate_stabilizer,
        rightConjugateElem_comp] using hx_adjust
    · calc
        rightConjugateElem z₁ (k⁻¹ * h) =
            rightConjugateElem (rightConjugateElem z₁ k⁻¹) h :=
              (rightConjugateElem_comp z₁ k⁻¹ h).symm
        _ = rightConjugateElem z₀ h := rfl
        _ = z₂ := hz_adjust
  obtain ⟨g, hugH, htg⟩ :=
    htriple_transitive a b t d t t
      hcontaining_distinct htarget_distinct htb
      hsec.section2.hA.A1.involution_t ht_target
      hsec.section2.hA.A1.involution_t u hua
  exact ⟨rightConjugateElem u g, g, hugH, htg, rfl⟩

private theorem lemma_3_involution_fix_t_to_standard_obligation
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
    ∀ u : G, IsInvolution u → (u * t) ^ 2 ≠ 1 →
      ∃ (q g : G), q ∈ rightConjugate Q0 t ∧
        rightConjugateElem t g = t ∧ rightConjugateElem u g = q := by
  intro u hu hu_ne_t
  obtain ⟨q, g, hqH, htg, hug⟩ :=
    lemma_3_involution_fix_t_to_rightConjugate_H_obligation
      H D Q K V W Q0 S Q1 t s hsec u hu hu_ne_t
  have hqI : IsInvolution q := by
    rw [← hug]
    exact isInvolution_rightConjugateElem hu
  exact
    ⟨q, g,
      lemma_3_mem_rightConjugate_Q0_of_mem_rightConjugate_H
        hsec.section2.Q0_def hqH hqI,
      htg, hug⟩

private theorem lemma_3_distinct_involution_standard_pair_obligation
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
    ∀ u v : G, IsInvolution u → IsInvolution v → (u * v) ^ 2 ≠ 1 →
      ∃ (q g : G), q ∈ rightConjugate Q0 t ∧
        rightConjugateElem u g = q ∧ rightConjugateElem v g = t := by
  intro u v hu hv huv
  obtain ⟨g0, hvg0⟩ :=
    proposition_2_b H D Q t hsec.section2.hA.A1 v t hv hsec.section2.hA.A1.involution_t
  let u0 : G := rightConjugateElem u g0
  have hu0 : IsInvolution u0 := by
    dsimp [u0]
    exact isInvolution_rightConjugateElem hu
  have hprod_conj :
      rightConjugateElem (u * v) g0 = u0 * t := by
    calc
      rightConjugateElem (u * v) g0 =
          rightConjugateElem u g0 * rightConjugateElem v g0 :=
        lemma_3_rightConjugateElem_mul u v g0
      _ = u0 * t := by
        dsimp [u0]
        rw [hvg0]
  have hu0t2 : (u0 * t) ^ 2 ≠ 1 :=
    lemma_3_sq_ne_one_of_rightConjugateElem_eq huv hprod_conj
  obtain ⟨q, g1, hq, htg1, hu0g1⟩ :=
    lemma_3_involution_fix_t_to_standard_obligation
      H D Q K V W Q0 S Q1 t s hsec u0 hu0 hu0t2
  refine ⟨q, g0 * g1, hq, ?_, ?_⟩
  · calc
      rightConjugateElem u (g0 * g1) = rightConjugateElem u0 g1 := by
        dsimp [u0]
        rw [rightConjugateElem_comp]
      _ = q := hu0g1
  · calc
      rightConjugateElem v (g0 * g1) = rightConjugateElem (rightConjugateElem v g0) g1 := by
        rw [rightConjugateElem_comp]
      _ = rightConjugateElem t g1 := by rw [hvg0]
      _ = t := htg1

private theorem lemma_3_distinct_involution_product_conjugate_obligation
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
    ∀ u v : G, IsInvolution u → IsInvolution v → (u * v) ^ 2 ≠ 1 →
      ∃ (q g : G), q ∈ rightConjugate Q0 t ∧ rightConjugateElem (u * v) g = q * t := by
  intro u v hu hv huv
  obtain ⟨q, g, hq, hu_eq, hv_eq⟩ :=
    lemma_3_distinct_involution_standard_pair_obligation
      H D Q K V W Q0 S Q1 t s hsec u v hu hv huv
  refine ⟨q, g, hq, ?_⟩
  calc
    rightConjugateElem (u * v) g =
        rightConjugateElem u g * rightConjugateElem v g :=
      lemma_3_rightConjugateElem_mul u v g
    _ = q * t := by rw [hu_eq, hv_eq]

private theorem lemma_3_strongly_real_conjugate_obligation
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
    ∀ x : G, IsStronglyReal x → x ^ 2 ≠ 1 →
      ∃ (u g : G), u ∈ rightConjugate Q0 t ∧ rightConjugateElem x g = u * t := by
  intro x hxstrong hx2
  rcases hxstrong with ⟨u, v, hu, hv, rfl⟩
  exact
    lemma_3_distinct_involution_product_conjugate_obligation
      H D Q K V W Q0 S Q1 t s hsec u v hu hv hx2

private theorem lemma_3_strongly_real_conjugate_Q0_sharp
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
    ∀ x : G, IsStronglyReal x → x ^ 2 ≠ 1 →
      ∃ (u g : G), u ∈ Q0 ∧ u ≠ 1 ∧ rightConjugateElem x g = u * t := by
  intro x hxstrong hx2
  obtain ⟨q, g, hqQ0t, hxg⟩ :=
    lemma_3_strongly_real_conjugate_obligation
      H D Q K V W Q0 S Q1 t s hsec x hxstrong hx2
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hqQ0t
  rcases hqQ0t with ⟨u, huQ0, hqu⟩
  have hqu' : rightConjugateElem u t = q := by
    simpa [rightConjugateElem, MulAut.conj_apply] using hqu
  have htinv : t⁻¹ = t :=
    hsec.section2.hA.A1.involution_t.inv_eq_self
  have hq_back : rightConjugateElem q t = u := by
    rw [← hqu']
    simpa [htinv] using lemma_3_rightConjugateElem_right_inv u t
  have ht2 : t * t = 1 := by
    simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
  have ht_back : rightConjugateElem t t = t := by
    simp [rightConjugateElem, htinv, ht2]
  have hxgt : rightConjugateElem x (g * t) = u * t := by
    calc
      rightConjugateElem x (g * t) = rightConjugateElem (rightConjugateElem x g) t := by
        rw [rightConjugateElem_comp]
      _ = rightConjugateElem (q * t) t := by rw [hxg]
      _ = rightConjugateElem q t * rightConjugateElem t t :=
        lemma_3_rightConjugateElem_mul q t t
      _ = u * t := by rw [hq_back, ht_back]
  refine ⟨u, g * t, huQ0, ?_, hxgt⟩
  intro hu_one
  have hut_ne : (u * t) ^ 2 ≠ 1 :=
    lemma_3_sq_ne_one_of_rightConjugateElem_eq hx2 hxgt
  exact hut_ne (by simp [hu_one, hsec.section2.hA.A1.involution_t.sq_eq_one])

private theorem lemma_3_standard_product_endpoint_centralizer_obligation
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
    ∀ q : G, q ∈ rightConjugate Q0 t → (q * t) ^ 2 ≠ 1 →
      ∀ y : G, IsInvolution y →
        y ∈ Subgroup.centralizer ({q * t} : Set G) →
          q ∈ Subgroup.centralizer ({q * t} : Set G) ∨
            t ∈ Subgroup.centralizer ({q * t} : Set G) := by
  intro q hqQ0 hqt2 y hyI hyC
  have hsource_endpoint :
      ∀ u : G, u ∈ Q0 → u ≠ 1 → (u * t) ^ 2 ≠ 1 →
        ∀ z : G, IsInvolution z →
          z ∈ Subgroup.centralizer ({u * t} : Set G) →
            u ∈ Subgroup.centralizer ({u * t} : Set G) ∨
              t ∈ Subgroup.centralizer ({u * t} : Set G) := by
    intro u huQ0 hu_ne hut2 z hzI hzC
    have hu_data : u ∈ H ∧ IsInvolution u := by
      rcases (hsec.section2.Q0_def u).mp huQ0 with hu_one | hu_data
      · exact (hu_ne hu_one).elim
      · exact hu_data
    let N : Subgroup G :=
      Subgroup.normalizer (Subgroup.zpowers (u * t) : Set G)
    have hnormalizer_of_inverts :
        ∀ a : G, a * (u * t) * a⁻¹ = (u * t)⁻¹ → a ∈ N := by
      intro a hax
      have hconj_zpow :
          ∀ n : ℤ, a * (u * t) ^ n * a⁻¹ = (u * t) ^ (-n) := by
        intro n
        have hsem : SemiconjBy a (u * t) (u * t)⁻¹ := by
          rw [SemiconjBy]
          calc
            a * (u * t) =
                (a * (u * t) * a⁻¹) * a := by group
            _ = (u * t)⁻¹ * a := by rw [hax]
        have hp := hsem.zpow_right n
        calc
          a * (u * t) ^ n * a⁻¹ = ((u * t)⁻¹) ^ n := by
            rw [hp]
            simp [mul_assoc]
          _ = (u * t) ^ (-n) := inv_zpow' (u * t) n
      have hax_inv :
          a⁻¹ * (u * t) * (a⁻¹)⁻¹ = (u * t)⁻¹ := by
        have hi := congrArg Inv.inv hax
        have hi' : a * (u * t)⁻¹ * a⁻¹ = u * t := by
          simpa [mul_assoc] using hi
        calc
          a⁻¹ * (u * t) * (a⁻¹)⁻¹ =
              a⁻¹ * (u * t) * a := by rw [inv_inv]
          _ = a⁻¹ * (a * (u * t)⁻¹ * a⁻¹) * a := by rw [hi']
          _ = (u * t)⁻¹ := by group
      have hconj_inv_zpow :
          ∀ n : ℤ, a⁻¹ * (u * t) ^ n * a = (u * t) ^ (-n) := by
        intro n
        have hsem : SemiconjBy a⁻¹ (u * t) (u * t)⁻¹ := by
          rw [SemiconjBy]
          calc
            a⁻¹ * (u * t) =
                (a⁻¹ * (u * t) * (a⁻¹)⁻¹) * a⁻¹ := by group
            _ = (u * t)⁻¹ * a⁻¹ := by rw [hax_inv]
        have hp := hsem.zpow_right n
        calc
          a⁻¹ * (u * t) ^ n * a = ((u * t)⁻¹) ^ n := by
            rw [hp]
            simp [mul_assoc]
          _ = (u * t) ^ (-n) := inv_zpow' (u * t) n
      dsimp [N]
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
        rw [Subgroup.mem_zpowers_iff]
        exact ⟨-n, (hconj_zpow n).symm⟩
      · intro hy
        rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, hn⟩
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨-n, ?_⟩
        calc
          (u * t) ^ (-n) =
              a⁻¹ * (u * t) ^ n * a :=
            (hconj_inv_zpow n).symm
          _ = y := by rw [hn]; group
    have huN : u ∈ N := by
      apply hnormalizer_of_inverts u
      have huu : u * u = 1 := by
        simpa [pow_two] using hu_data.2.sq_eq_one
      have htt : t * t = 1 := by
        simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
      calc
        u * (u * t) * u⁻¹ = (u * u) * t * u := by
          rw [hu_data.2.inv_eq_self]
          group
        _ = t * u := by rw [huu]; simp
        _ = (u * t)⁻¹ := by
          simp [mul_inv_rev, hu_data.2.inv_eq_self,
            hsec.section2.hA.A1.involution_t.inv_eq_self]
    have htN : t ∈ N := by
      apply hnormalizer_of_inverts t
      have htt : t * t = 1 := by
        simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
      calc
        t * (u * t) * t⁻¹ = t * u * (t * t) := by
          rw [hsec.section2.hA.A1.involution_t.inv_eq_self]
          group
        _ = t * u := by rw [htt]; simp
        _ = (u * t)⁻¹ := by
          simp [mul_inv_rev, hu_data.2.inv_eq_self,
            hsec.section2.hA.A1.involution_t.inv_eq_self]
    have hzN : z ∈ N := by
      apply centralizer_le_normalizer (Subgroup.zpowers (u * t))
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rcases Subgroup.mem_zpowers_iff.mp hw with ⟨n, rfl⟩
      have hcomm : Commute z (u * t) :=
        Subgroup.mem_centralizer_singleton_iff.mp hzC
      exact (hcomm.zpow_right n).eq.symm
    have hcentralizer_conj :
        ∀ c w : G, c ∈ N →
          w ∈ Subgroup.centralizer ({u * t} : Set G) →
            rightConjugateElem w c ∈
              Subgroup.centralizer ({u * t} : Set G) := by
      intro c w hcN hwC
      have hx_mem : u * t ∈ Subgroup.zpowers (u * t) :=
        Subgroup.mem_zpowers (u * t)
      have hcx :
          c * (u * t) * c⁻¹ ∈ Subgroup.zpowers (u * t) := by
        exact
          (Subgroup.mem_normalizer_iff.mp
            (show c ∈ Subgroup.normalizer
              (Subgroup.zpowers (u * t) : Set G) by simpa [N] using hcN)
            (u * t)).1 hx_mem
      rcases Subgroup.mem_zpowers_iff.mp hcx with ⟨n, hn⟩
      have hwcomm : Commute w (u * t) :=
        Subgroup.mem_centralizer_singleton_iff.mp hwC
      have hwpow : w * (u * t) ^ n = (u * t) ^ n * w :=
        (hwcomm.zpow_right n).eq
      rw [Subgroup.mem_centralizer_singleton_iff]
      dsimp [rightConjugateElem]
      calc
        (c⁻¹ * w * c) * (u * t) =
            c⁻¹ * (w * (c * (u * t) * c⁻¹)) * c := by group
        _ = c⁻¹ * (w * (u * t) ^ n) * c := by rw [← hn]
        _ = c⁻¹ * ((u * t) ^ n * w) * c := by rw [hwpow]
        _ = c⁻¹ * (c * (u * t) * c⁻¹ * w) * c := by rw [hn]
        _ = (u * t) * (c⁻¹ * w * c) := by group
    have hodd_product_same_centralizer :
        ∀ a b : G, IsInvolution a → IsInvolution b → a ≠ b →
          Odd (orderOf (a * b)) → a ∈ N → b ∈ N →
          (a ∈ Subgroup.centralizer ({u * t} : Set G) ↔
            b ∈ Subgroup.centralizer ({u * t} : Set G)) := by
      intro a b ha hb hab hodd haN hbN
      have hconjugator :
          ∃ c : G, c ∈ N ∧ IsInvolution c ∧
            rightConjugateElem a c = b := by
        rcases hodd with ⟨m, hm⟩
        let r₀ : G := a * b
        let k : ℕ := m + 1
        have ha_inv : a⁻¹ = a := ha.inv_eq_self
        have hb_inv : b⁻¹ = b := hb.inv_eq_self
        have haa : a * a = 1 := by
          simpa [pow_two] using ha.sq_eq_one
        have hsem : SemiconjBy a r₀ r₀⁻¹ := by
          change a * (a * b) = (a * b)⁻¹ * a
          rw [mul_inv_rev, ha_inv, hb_inv, ← mul_assoc, haa, one_mul,
            mul_assoc, haa, mul_one]
        have hark : a * r₀ ^ k = (r₀ ^ k)⁻¹ * a := by
          have h := hsem.pow_right k
          simpa [inv_pow] using h.eq
        have hpow_order : r₀ ^ (2 * m + 1) = 1 := by
          have h := pow_orderOf_eq_one r₀
          simpa [r₀, hm] using h
        have htwo_k : 2 * k = (2 * m + 1) + 1 := by
          dsimp [k]
          omega
        have hpow_two_k : r₀ ^ (2 * k) = r₀ := by
          rw [htwo_k, pow_succ, hpow_order, one_mul]
        let c : G := a * r₀ ^ k
        have hc_sq : c ^ 2 = 1 := by
          change (a * r₀ ^ k) ^ 2 = 1
          rw [pow_two]
          calc
            (a * r₀ ^ k) * (a * r₀ ^ k) =
                ((r₀ ^ k)⁻¹ * a) * (a * r₀ ^ k) := by rw [hark]
            _ = 1 := by
              rw [mul_assoc, ← mul_assoc a a (r₀ ^ k), haa, one_mul,
                inv_mul_cancel]
        have hc_conj : rightConjugateElem a c = b := by
          change (a * r₀ ^ k)⁻¹ * a * (a * r₀ ^ k) = b
          calc
            (a * r₀ ^ k)⁻¹ * a * (a * r₀ ^ k) =
                (r₀ ^ k)⁻¹ * a * a * (a * r₀ ^ k) := by
                  simp [mul_assoc, ha_inv]
            _ = (r₀ ^ k)⁻¹ * a * r₀ ^ k := by
                  simp [mul_assoc, haa]
            _ = (a * r₀ ^ k) * r₀ ^ k := by rw [← hark]
            _ = a * r₀ ^ (2 * k) := by
                  rw [mul_assoc, ← pow_add, show k + k = 2 * k by omega]
            _ = a * r₀ := by rw [hpow_two_k]
            _ = b := by
                  dsimp [r₀]
                  rw [← mul_assoc, haa, one_mul]
        have hc_ne : c ≠ 1 := by
          intro hc
          have hb_eq_a : b = a := by
            rw [← hc_conj, hc]
            simp [rightConjugateElem]
          exact hab hb_eq_a.symm
        have hcN : c ∈ N := by
          exact N.mul_mem haN (N.pow_mem (N.mul_mem haN hbN) k)
        exact ⟨c, hcN, ⟨hc_ne, hc_sq⟩, hc_conj⟩
      obtain ⟨c, hcN, hcI, hc⟩ := hconjugator
      constructor
      · intro haC
        have hbC := hcentralizer_conj c a hcN haC
        simpa [hc] using hbC
      · intro hbC
        have hc_invN : c⁻¹ ∈ N := N.inv_mem hcN
        have haC := hcentralizer_conj c⁻¹ b hc_invN hbC
        have hback : rightConjugateElem b c⁻¹ = a := by
          rw [← hc]
          exact lemma_3_rightConjugateElem_right_inv a c
        simpa [hback] using haC
    by_cases hzH : z ∈ H
    · right
      have hzt_ne : z ≠ t := by
        intro h
        exact hsec.section2.hA.A1.t_not_mem_H (h ▸ hzH)
      have hodd :
          Odd (orderOf (z * t)) :=
        proposition_2_a H D Q t hsec.section2.hA.A1
          z t hzH hzI hsec.section2.hA.A1.involution_t
          hsec.section2.hA.A1.t_not_mem_H
      exact
        (hodd_product_same_centralizer z t hzI
          hsec.section2.hA.A1.involution_t hzt_ne hodd hzN htN).mp hzC
    · left
      have huz_ne : u ≠ z := by
        intro h
        exact hzH (h ▸ hu_data.1)
      have hodd :
          Odd (orderOf (u * z)) :=
        proposition_2_a H D Q t hsec.section2.hA.A1
          u z hu_data.1 hu_data.2 hzI hzH
      exact
        (hodd_product_same_centralizer u z hu_data.2 hzI
          huz_ne hodd huN hzN).mpr hzC
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hqQ0
  rcases hqQ0 with ⟨u, huQ0, hqu⟩
  have hqu' : rightConjugateElem u t = q := by
    simpa [rightConjugateElem, MulAut.conj_apply] using hqu
  have htinv : t⁻¹ = t :=
    hsec.section2.hA.A1.involution_t.inv_eq_self
  have hq_back : rightConjugateElem q t = u := by
    rw [← hqu']
    simpa [htinv] using lemma_3_rightConjugateElem_right_inv u t
  have ht2 : t * t = 1 := by
    simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
  have ht_back : rightConjugateElem t t = t := by
    simp [rightConjugateElem, htinv, ht2]
  have hprod :
      rightConjugateElem (q * t) t = u * t := by
    calc
      rightConjugateElem (q * t) t =
          rightConjugateElem q t * rightConjugateElem t t :=
        lemma_3_rightConjugateElem_mul q t t
      _ = u * t := by rw [hq_back, ht_back]
  have hut2 : (u * t) ^ 2 ≠ 1 :=
    lemma_3_sq_ne_one_of_rightConjugateElem_eq hqt2 hprod
  have hu_ne : u ≠ 1 := by
    intro hu
    apply hut2
    simp [hu, hsec.section2.hA.A1.involution_t.sq_eq_one]
  let y' : G := rightConjugateElem y t
  have hy'I : IsInvolution y' :=
    isInvolution_rightConjugateElem hyI
  have hy'C : y' ∈ Subgroup.centralizer ({u * t} : Set G) :=
    lemma_3_rightConjugateElem_mem_centralizer_singleton hyC hprod
  have hprod_back :
      rightConjugateElem (u * t) t⁻¹ = q * t := by
    rw [← hprod]
    exact lemma_3_rightConjugateElem_right_inv (q * t) t
  rcases hsource_endpoint u huQ0 hu_ne hut2 y' hy'I hy'C with huC | htC
  · have hqC : q ∈ Subgroup.centralizer ({q * t} : Set G) := by
      have htransport :=
        lemma_3_rightConjugateElem_mem_centralizer_singleton
          huC hprod_back
      simpa [htinv, hqu'] using htransport
    exact Or.inl hqC
  · have htC' : t ∈ Subgroup.centralizer ({q * t} : Set G) := by
      have htransport :=
        lemma_3_rightConjugateElem_mem_centralizer_singleton
          htC hprod_back
      simpa [htinv, ht_back] using htransport
    exact Or.inr htC'

private theorem lemma_3_standard_product_no_centralizing_involution_obligation
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
    ∀ q : G, q ∈ rightConjugate Q0 t → (q * t) ^ 2 ≠ 1 →
      ∀ y : G, IsInvolution y →
        y ∈ Subgroup.centralizer ({q * t} : Set G) → False := by
  intro q hqQ0 hqt2 y hyI hyC
  have hq2 : q ^ 2 = 1 :=
    lemma_3_sq_eq_one_of_mem_rightConjugate_Q0 hsec.section2.Q0_def hqQ0
  have ht2 : t ^ 2 = 1 :=
    hsec.section2.hA.A1.involution_t.sq_eq_one
  rcases
    lemma_3_standard_product_endpoint_centralizer_obligation
      H D Q K V W Q0 S Q1 t s hsec q hqQ0 hqt2 y hyI hyC with
    hqC | htC
  · exact hqt2 (lemma_3_sq_eq_one_of_left_endpoint_centralizes hq2 ht2 hqC)
  · exact hqt2 (lemma_3_sq_eq_one_of_right_endpoint_centralizes hq2 ht2 htC)

private theorem lemma_3_no_centralizing_involution_obligation
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
    ∀ x : G, IsStronglyReal x → x ^ 2 ≠ 1 →
      ∀ y : G, IsInvolution y →
        y ∈ Subgroup.centralizer ({x} : Set G) → False := by
  intro x hxstrong hx2 y hyI hyC
  obtain ⟨q, g, hq, hxg⟩ :=
    lemma_3_strongly_real_conjugate_obligation
      H D Q K V W Q0 S Q1 t s hsec x hxstrong hx2
  let y' : G := rightConjugateElem y g
  have hy'I : IsInvolution y' :=
    isInvolution_rightConjugateElem hyI
  have hy'C : y' ∈ Subgroup.centralizer ({q * t} : Set G) :=
    lemma_3_rightConjugateElem_mem_centralizer_singleton hyC hxg
  have hqt2 : (q * t) ^ 2 ≠ 1 :=
    lemma_3_sq_ne_one_of_rightConjugateElem_eq hx2 hxg
  exact
    lemma_3_standard_product_no_centralizing_involution_obligation
      H D Q K V W Q0 S Q1 t s hsec q hq hqt2 y' hy'I hy'C

private theorem lemma_3_centralizer_odd_of_no_involutions
    {G : Type*} [Group G] [Finite G] {x : G}
    (hno :
      ∀ y : G, IsInvolution y →
        y ∈ Subgroup.centralizer ({x} : Set G) → False) :
    Odd (Nat.card (Subgroup.centralizer ({x} : Set G))) := by
  classical
  by_contra hodd
  have heven :
      Even (Nat.card (Subgroup.centralizer ({x} : Set G))) :=
    Nat.not_odd_iff_even.mp hodd
  obtain ⟨y, hyC, hyInv⟩ :=
    lemma_3_exists_involution_of_even_card
      (Subgroup.centralizer ({x} : Set G)) heven
  exact hno y hyInv hyC

private theorem lemma_3_centralizer_odd_obligation
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
    ∀ x : G, IsStronglyReal x → x ^ 2 ≠ 1 →
      Odd (Nat.card (Subgroup.centralizer ({x} : Set G))) := by
  intro x hxstrong hx2
  exact
    lemma_3_centralizer_odd_of_no_involutions
      (lemma_3_no_centralizing_involution_obligation
        H D Q K V W Q0 S Q1 t s hsec x hxstrong hx2)

public theorem lemma_3
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
    ∀ x : G, IsStronglyReal x → x ^ 2 ≠ 1 →
      (∃ (u g : G), u ∈ Q0 ∧ u ≠ 1 ∧ rightConjugateElem x g = u * t) ∧
        Odd (Nat.card (Subgroup.centralizer ({x} : Set G))) := by
  intro x hxstrong hx2
  exact
    ⟨lemma_3_strongly_real_conjugate_Q0_sharp
        H D Q K V W Q0 S Q1 t s hsec x hxstrong hx2,
      lemma_3_centralizer_odd_obligation
        H D Q K V W Q0 S Q1 t s hsec x hxstrong hx2⟩

end PFchapter1section3
end CFSG.BenderSuzuki
