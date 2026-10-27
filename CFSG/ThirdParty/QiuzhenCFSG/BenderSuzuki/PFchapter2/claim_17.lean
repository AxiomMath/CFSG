module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.theorem_14_4_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.TBS.TBS
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.Semidirect
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_5

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixIII
open PFchapter1section3
open scoped Pointwise

attribute [local instance] commutatorElement

/-!
# Peterfalvi, Part II, Chapter II, Claim (17), conclusion
-/

private theorem claim_17_B2_excludes_normal_index_p
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
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
    (hN : ∃ N : Subgroup G, N.Normal ∧ Nat.card (G ⧸ N) = p) :
    False := by
  rcases hN with ⟨N, hNnormal, hNindex⟩
  exact hch.B2 N hNnormal hNindex

private theorem chapter2_claim17_stronglyReal_rightConjugateElem
    {G : Type*} [Group G] {x : G} (g : G) (hx : IsStronglyReal x) :
    IsStronglyReal (rightConjugateElem x g) := by
  rcases hx with ⟨u, v, hu, hv, huv⟩
  refine ⟨rightConjugateElem u g, rightConjugateElem v g,
    isInvolution_rightConjugateElem hu, isInvolution_rightConjugateElem hv, ?_⟩
  calc
    rightConjugateElem x g = rightConjugateElem (u * v) g := by rw [huv]
    _ = rightConjugateElem u g * rightConjugateElem v g := by
      simp [rightConjugateElem, mul_assoc]
private theorem chapter2_claim17_strongly_real_of_inverted_by_involution
    {G : Type*} [Group G] {x s : G}
    (hs : IsInvolution s) (hxinv : rightConjugateElem x s = x⁻¹)
    (hx2 : x ^ 2 ≠ 1) :
    IsStronglyReal x := by
  have hs_inv : s⁻¹ = s := by
    have hs_mul : s * s = 1 := by
      simpa [pow_two] using hs.sq_eq_one
    calc
      s⁻¹ = s⁻¹ * 1 := by simp
      _ = s⁻¹ * (s * s) := by rw [hs_mul]
      _ = s := by simp
  have hs_mul : s * s = 1 := by
    simpa [pow_two] using hs.sq_eq_one
  have hconj : s * x * s = x⁻¹ := by
    simpa [rightConjugateElem, hs_inv, mul_assoc] using hxinv
  have hxs_sq : (x * s) ^ 2 = 1 := by
    calc
      (x * s) ^ 2 = x * (s * x * s) := by
        simp [pow_two, mul_assoc]
      _ = 1 := by
        rw [hconj]
        simp
  have hxs_ne : x * s ≠ 1 := by
    intro hxs
    have hx_eq_s : x = s := by
      calc
        x = x * 1 := by simp
        _ = x * (s * s) := by rw [hs_mul]
        _ = (x * s) * s := by simp [mul_assoc]
        _ = s := by rw [hxs]; simp
    exact hx2 (by simpa [hx_eq_s] using hs.sq_eq_one)
  refine ⟨x * s, s, ⟨hxs_ne, hxs_sq⟩, hs, ?_⟩
  simp [hs_mul, mul_assoc]

private theorem chapter2_claim17_Z1_stronglyReal
    {G : Type*} [Group G] (Z1 : Subgroup G) (s t : G)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hst3 : orderOf (s * t) = 3)
    (hs : IsInvolution s) (ht : IsInvolution t) :
    ∀ z : G, z ∈ Z1 → z ≠ 1 → IsStronglyReal z := by
  intro z hzZ1 hzne
  have hzpow : z ∈ Subgroup.zpowers (s * t) := by simpa [hZ1] using hzZ1
  have hzinv : rightConjugateElem z s = z⁻¹ := by
    rw [Subgroup.mem_zpowers_iff] at hzpow
    rcases hzpow with ⟨n, rfl⟩
    have hss : s * s = 1 := by simpa [pow_two] using hs.sq_eq_one
    have hgen : (MulAut.conj s⁻¹) (s * t) = (s * t)⁻¹ := by
      simp only [MulAut.conj_apply, hs.inv_eq_self, mul_inv_rev, ht.inv_eq_self]
      calc
        s * (s * t) * s = (s * s) * t * s := by simp [mul_assoc]
        _ = t * s := by rw [hss]; simp
    have hmap :
        (MulAut.conj s⁻¹) ((s * t) ^ n) = ((s * t) ^ n)⁻¹ := by
      rw [map_zpow, hgen]
      exact inv_zpow (s * t) n
    simpa [rightConjugateElem, MulAut.conj_apply] using hmap
  apply chapter2_claim17_strongly_real_of_inverted_by_involution hs hzinv
  intro hz2
  have hdvd2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
  have hdvd3 : orderOf z ∣ 3 := by
    rw [← hst3]
    exact orderOf_dvd_of_mem_zpowers hzpow
  have hdvd1 : orderOf z ∣ 1 := by
    simpa using Nat.dvd_gcd hdvd2 hdvd3
  exact hzne (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1))


private theorem chapter2_claim17_natCard_rightConjugate
    {G : Type*} [Group G] (X : Subgroup G) (g : G) :
    Nat.card (rightConjugate X g) = Nat.card X := by
  rw [rightConjugate, Subgroup.conjBy]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective X
      (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm.toEquiv

private theorem chapter2_claim17_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type*} [Group G] (F H : Subgroup G)
    (hnormal : H ≤ Subgroup.normalizer (F : Set G)) (hdisjoint : Disjoint F H) :
    Nat.card (F ⊔ H : Subgroup G) = Nat.card F * Nat.card H := by
  let toB : F × H → ↥(F ⊔ H) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have htoB_injective : Function.Injective toB := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have htoB_surjective : Function.Surjective toB := by
    intro b
    have hb : (b : G) ∈ (F : Set G) * (H : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left F H hnormal]
      exact b.property
    rcases hb with ⟨f, hf, h, hh, hfh⟩
    refine ⟨(⟨f, hf⟩, ⟨h, hh⟩), ?_⟩
    exact Subtype.ext hfh
  calc
    Nat.card (F ⊔ H : Subgroup G) = Nat.card (F × H) :=
      Nat.card_congr (Equiv.ofBijective toB ⟨htoB_injective, htoB_surjective⟩).symm
    _ = Nat.card F * Nat.card H := Nat.card_prod F H

private theorem chapter2_claim17_rightConjugate_rightConjugate
    {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    rightConjugate (rightConjugate H a) b = rightConjugate H (a * b) := by
  ext x
  constructor
  · intro hx
    change x ∈ (rightConjugate H a).map (MulAut.conj b⁻¹).toMonoidHom at hx
    rcases hx with ⟨y, hy, rfl⟩
    change y ∈ H.map (MulAut.conj a⁻¹).toMonoidHom at hy
    rcases hy with ⟨z, hz, rfl⟩
    change (MulAut.conj b⁻¹) ((MulAut.conj a⁻¹) z) ∈
      H.map (MulAut.conj (a * b)⁻¹).toMonoidHom
    refine ⟨z, hz, ?_⟩
    simp [mul_assoc]
  · intro hx
    change x ∈ H.map (MulAut.conj (a * b)⁻¹).toMonoidHom at hx
    rcases hx with ⟨z, hz, rfl⟩
    change (MulAut.conj (a * b)⁻¹) z ∈
      (rightConjugate H a).map (MulAut.conj b⁻¹).toMonoidHom
    refine ⟨(MulAut.conj a⁻¹) z, ?_, ?_⟩
    · change (MulAut.conj a⁻¹) z ∈ H.map (MulAut.conj a⁻¹).toMonoidHom
      exact ⟨z, hz, rfl⟩
    · simp [mul_assoc]

private theorem chapter2_claim17_rightConjugate_one
    {G : Type*} [Group G] (H : Subgroup G) :
    rightConjugate H 1 = H := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hy
  · intro hx
    exact ⟨x, hx, by simp⟩

private theorem chapter2_claim17_mem_normalizer_of_conjBy_eq
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
    have hxconj : g * x * g⁻¹ ∈ H.conjBy g := by
      simpa [h] using hx
    rw [Subgroup.conjBy, Subgroup.mem_map] at hxconj
    rcases hxconj with ⟨y, hy, hyx⟩
    have : y = x := by
      apply (MulAut.conj g).injective
      simpa [MulAut.conj_apply] using hyx
    simpa [this] using hy

private theorem chapter2_claim17_mem_normalizer_of_rightConjugate_eq_self
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : rightConjugate H g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  have hgInv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) := by
    apply chapter2_claim17_mem_normalizer_of_conjBy_eq
    simpa [rightConjugate] using h
  simpa using (Subgroup.normalizer (H : Set G)).inv_mem hgInv

private theorem chapter2_claim17_rightConjugate_eq_self_of_mem_normalizer
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    rightConjugate H g = H := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    have hg_inv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).inv_mem hg
    exact (Subgroup.mem_normalizer_iff.mp hg_inv y).1 hy
  · intro hx
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hg x).1 hx
    · calc
        (MulAut.conj g⁻¹) (g * x * g⁻¹) =
            g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ := rfl
        _ = x := by group

private theorem chapter2_claim17_disjoint_of_card_three_of_not_le
    {G : Type*} [Group G] [Finite G] (A B : Subgroup G)
    (hAcard : Nat.card A = 3) (hnot : ¬ A ≤ B) :
    Disjoint A B := by
  rw [disjoint_iff_inf_le]
  let K : Subgroup A := (A ⊓ B).subgroupOf A
  haveI : Fact (Nat.card A).Prime := ⟨by simpa [hAcard] using Nat.prime_three⟩
  rcases K.eq_bot_or_eq_top_of_prime_card with hK | hK
  · intro x hx
    have hxK : (⟨x, hx.1⟩ : A) ∈ K := by
      exact hx
    rw [hK] at hxK
    simpa using hxK
  · exfalso
    apply hnot
    intro x hxA
    have hxK : (⟨x, hxA⟩ : A) ∈ K := by
      rw [hK]
      trivial
    exact hxK.2


private theorem chapter2_claim17_zpowers_stronglyReal_of_generator
    {G : Type*} [Group G] {x : G}
    (hx : IsStronglyReal x) (hxorder : orderOf x = 3) :
    ∀ z : G, z ∈ Subgroup.zpowers x → z ≠ 1 → IsStronglyReal z := by
  rcases hx with ⟨u, v, hu, hv, hxuv⟩
  have hu_inv : u⁻¹ = u := hu.inv_eq_self
  have huu : u * u = 1 := by
    simpa [pow_two] using hu.sq_eq_one
  have hconj_x : rightConjugateElem x u = x⁻¹ := by
    rw [hxuv]
    calc
      rightConjugateElem (u * v) u = u * (u * v) * u := by
        simp [rightConjugateElem, hu_inv]
      _ = v * u := by rw [← mul_assoc, huu]; simp
      _ = (u * v)⁻¹ := by simp [hu_inv, hv.inv_eq_self]
  intro z hz hzne
  rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
  have hzinv : rightConjugateElem (x ^ n) u = (x ^ n)⁻¹ := by
    have hmap :
        (MulAut.conj u⁻¹) (x ^ n) = (x ^ n)⁻¹ := by
      rw [map_zpow, show (MulAut.conj u⁻¹) x = x⁻¹ by
        simpa [rightConjugateElem, MulAut.conj_apply] using hconj_x]
      exact inv_zpow x n
    simpa [rightConjugateElem, MulAut.conj_apply] using hmap
  apply chapter2_claim17_strongly_real_of_inverted_by_involution hu hzinv
  intro hz2
  have hdvd2 : orderOf (x ^ n) ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
  have hdvd3 : orderOf (x ^ n) ∣ 3 := by
    rw [← hxorder]
    exact orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers x n)
  have hdvd1 : orderOf (x ^ n) ∣ 1 := by
    simpa using Nat.dvd_gcd hdvd2 hdvd3
  exact hzne (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1))

private theorem chapter2_claim17_unique_stronglyReal_three_subgroup_rightConjugate
    {G : Type*} [Group G] [Finite G] (Q Z1 : Subgroup G) (g : G)
    (huniq :
      ∀ X : Subgroup G,
        X ≤ Q → Nat.card X = 3 →
          (∀ x : G, x ∈ X → x ≠ 1 → IsStronglyReal x) → X = Z1) :
    ∀ X : Subgroup G,
      X ≤ rightConjugate Q g → Nat.card X = 3 →
        (∀ x : G, x ∈ X → x ≠ 1 → IsStronglyReal x) →
          X = rightConjugate Z1 g := by
  intro X hX hXcard hXstrong
  let X0 : Subgroup G := rightConjugate X g⁻¹
  have hX0_le : X0 ≤ Q := by
    change rightConjugate X g⁻¹ ≤ Q
    have hmap :
        rightConjugate X g⁻¹ ≤ rightConjugate (rightConjugate Q g) g⁻¹ := by
      change X.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom ≤
        (rightConjugate Q g).map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
      exact Subgroup.map_mono hX
    calc
      rightConjugate X g⁻¹ ≤ rightConjugate (rightConjugate Q g) g⁻¹ := hmap
      _ = rightConjugate Q (g * g⁻¹) :=
        chapter2_claim17_rightConjugate_rightConjugate Q g g⁻¹
      _ = rightConjugate Q 1 := by
        congr 1
        simp
      _ = Q := chapter2_claim17_rightConjugate_one Q
  have hX0card : Nat.card X0 = 3 := by
    change Nat.card (rightConjugate X g⁻¹) = 3
    rw [chapter2_claim17_natCard_rightConjugate, hXcard]
  have hX0strong :
      ∀ x : G, x ∈ X0 → x ≠ 1 → IsStronglyReal x := by
    intro x hx hne
    change x ∈ X.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom at hx
    rcases hx with ⟨y, hy, rfl⟩
    have hyne : y ≠ 1 := by
      intro hy1
      apply hne
      simp [hy1]
    simpa [rightConjugateElem, MulAut.conj_apply] using
      (chapter2_claim17_stronglyReal_rightConjugateElem g⁻¹
        (hXstrong y hy hyne))
  have hX0eq : X0 = Z1 := huniq X0 hX0_le hX0card hX0strong
  have hconj := congrArg (fun Y : Subgroup G => rightConjugate Y g) hX0eq
  have hback : rightConjugate (rightConjugate X g⁻¹) g = X := by
    calc
      rightConjugate (rightConjugate X g⁻¹) g =
          rightConjugate X (g⁻¹ * g) :=
        chapter2_claim17_rightConjugate_rightConjugate X g⁻¹ g
      _ = rightConjugate X 1 := by
        congr 1
        simp
      _ = X := chapter2_claim17_rightConjugate_one X
  exact hback.symm.trans hconj

private theorem chapter2_claim17_centralizer_le_normalizer
    {G : Type*} [Group G] (A : Subgroup G) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hxy : y * g = g * y := (Subgroup.mem_centralizer_iff.mp hg) y hy
    have hconj : g * y * g⁻¹ = y := by
      calc
        g * y * g⁻¹ = (g * y) * g⁻¹ := by simp [mul_assoc]
        _ = (y * g) * g⁻¹ := by rw [hxy.symm]
        _ = y := by simp [mul_assoc]
    simpa [hconj] using hy
  · intro hy
    have hginv : g⁻¹ ∈ Subgroup.centralizer (A : Set G) :=
      (Subgroup.inv_mem_iff (H := Subgroup.centralizer (A : Set G))).2 hg
    have hyback : g⁻¹ * (g * y * g⁻¹) * g ∈ A := by
      have hyc : g * y * g⁻¹ ∈ A := hy
      have hxy : (g * y * g⁻¹) * g⁻¹ = g⁻¹ * (g * y * g⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hginv) (g * y * g⁻¹) hyc
      have hconj : g⁻¹ * (g * y * g⁻¹) * g = g * y * g⁻¹ := by
        calc
          g⁻¹ * (g * y * g⁻¹) * g =
              (g⁻¹ * (g * y * g⁻¹)) * g := by simp [mul_assoc]
          _ = ((g * y * g⁻¹) * g⁻¹) * g := by rw [hxy]
          _ = g * y * g⁻¹ := by simp [mul_assoc]
      simpa [hconj] using hyc
    simpa [mul_assoc] using hyback

private theorem chapter2_claim17_normal_of_index_eq_prime_of_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hGp : IsPGroup p G) (A : Subgroup G) (hindex : A.index = p) :
    A.Normal := by
  rcases hGp.exists_card_eq with ⟨n, hGcard⟩
  have hn_ne : n ≠ 0 := by
    intro hn
    have hcard_one : Nat.card G = 1 := by simpa [hn] using hGcard
    haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hcard_one).1
    have hAtop : A = ⊤ := by
      apply le_antisymm le_top
      intro x hx
      have hxone : x = 1 := Subsingleton.elim x 1
      simp [hxone]
    have hp_one : p = 1 := by simpa [hAtop] using hindex.symm
    exact (Fact.out : Nat.Prime p).ne_one hp_one
  apply Subgroup.normal_of_index_eq_minFac_card
  rw [hindex, hGcard]
  exact ((Fact.out : Nat.Prime p).pow_minFac hn_ne).symm

private theorem chapter2_claim17_not_stronglyReal_of_mem_peterfalviV_order_three
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s x : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
      K ≤ D ∧
      (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
      V = peterfalviV D t ∧ W ≤ V ∧
      W = peterfalviW V (K : Set G) ∧ Q0 ≤ Q ∧
      (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
      S ≤ Q ∧ Q1 ≤ Q ∧
      (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
      Odd (Nat.card Q1) ∧ Disjoint S Q1 ∧
      (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
      S ⊔ Q1 = Q) ∧
      s ∈ H ∧ IsInvolution s ∧
      ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hxV : x ∈ V) (hxne : x ≠ 1) (hx3 : x ^ 3 = 1) :
    ¬ IsStronglyReal x := by
  intro hxstrong
  have hx2 : x ^ 2 ≠ 1 := by
    intro hx2
    have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have hdvd3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have hdvd1 : orderOf x ∣ 1 := by
      simpa using Nat.dvd_gcd hdvd2 hdvd3
    exact hxne (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1))
  have hodd := (lemma_3 H D Q K V W Q0 S Q1 t s hsec x hxstrong hx2).2
  have htC : t ∈ Subgroup.centralizer ({x} : Set G) := by
    have hxCt : x ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [hsec.1.2.2.2.1] at hxV
      exact hxV.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hxCt).symm
  let tC : Subgroup.centralizer ({x} : Set G) := ⟨t, htC⟩
  have htC_order : orderOf tC = 2 := by
    have ht_order : orderOf t = 2 :=
      orderOf_eq_prime hsec.1.1.A1.involution_t.sq_eq_one
        hsec.1.1.A1.involution_t.ne_one
    simpa [tC] using (Subgroup.orderOf_coe tC).symm.trans ht_order
  have htwo_dvd : 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    rw [← htC_order]
    exact orderOf_dvd_natCard tC
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr htwo_dvd)


private theorem chapter2_claim17_commutative
    {G : Type*} [Group G] (P Sigma Z1 LV : Subgroup G)
    (hPcard : Nat.card P = 3)
    (hP_le_LV : P ≤ LV)
    (hcenter : LV ⊓ Subgroup.centralizer (LV : Set G) = Z1 ⊔ Sigma) :
    IsMulCommutative (Z1 ⊔ P ⊔ Sigma : Subgroup G) := by
  let A : Subgroup G := Z1 ⊔ Sigma
  have hA_le_LV : A ≤ LV := by
    change Z1 ⊔ Sigma ≤ LV
    rw [← hcenter]
    exact inf_le_left
  have hA_le_CLV : A ≤ Subgroup.centralizer (LV : Set G) := by
    change Z1 ⊔ Sigma ≤ Subgroup.centralizer (LV : Set G)
    rw [← hcenter]
    exact inf_le_right
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : IsMulCommutative P :=
    (isCyclic_of_prime_card hPcard).isMulCommutative
  have hA_le_CA : A ≤ Subgroup.centralizer (A : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_iff.mp (hA_le_CLV ha) b (hA_le_LV hb)
  have hA_le_CP : A ≤ Subgroup.centralizer (P : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_iff.mp (hA_le_CLV ha) b (hP_le_LV hb)
  have hP_le_CA : P ≤ Subgroup.centralizer (A : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hA_le_CP ha) p hp).symm
  have hP_le_CP : P ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hA_le_Csup :
      A ≤ Subgroup.centralizer ((A ⊔ P : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_sup_of_le_centralizers hA_le_CA hA_le_CP
  have hP_le_Csup :
      P ≤ Subgroup.centralizer ((A ⊔ P : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_sup_of_le_centralizers hP_le_CA hP_le_CP
  rw [show Z1 ⊔ P ⊔ Sigma = A ⊔ P by
    simp only [A]
    ac_rfl]
  exact Subgroup.le_centralizer_iff_isMulCommutative.mp
    (sup_le hA_le_Csup hP_le_Csup)

private theorem chapter2_claim17_weakly_closed_Z1PSigma
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L : Subgroup G)
    (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
      K ≤ D ∧
      (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
      V = peterfalviV D t ∧ W ≤ V ∧
      W = peterfalviW V (K : Set G) ∧ Q0 ≤ Q ∧
      (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
      S ≤ Q ∧ Q1 ≤ Q ∧
      (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
      Odd (Nat.card Q1) ∧ Disjoint S Q1 ∧
      (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
      S ⊔ Q1 = Q) ∧
      s ∈ H ∧ IsInvolution s ∧
      ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
      HypothesisB1 G V P p ∧ HypothesisB2 G p))
    (h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
      Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
      (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
        Z1 ⊔ P ∧
      R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
      R ⊔ Sigma ≤ R1 ∧ R2 = Subgroup.centralizer (Z1 : Set G) ∧ R1 ≤ R2)
    (h15 : L ≤ R1 ∧ (Nat.card L = 9 ∧ IsCyclic L) ∧
      (∀ x : G, x ∈ L → rightConjugateElem x s = x⁻¹) ∧
      V ≤ Subgroup.normalizer (L : Set G) ∧
      W ≤ Subgroup.centralizer (L : Set G) ∧
      ¬ P ≤ Subgroup.centralizer (L : Set G) ∧
      L ⊔ V ≤ R2 ∧ Nat.card R2 = 3 * Nat.card ((L ⊔ V : Subgroup G)) ∧
      (L ⊔ V) ⊓ Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) =
        Z1 ⊔ Sigma ∧
      ∀ x : G, x ∈ L ⊔ V → (x ^ 3 = 1 ↔ x ∈ Z1 ⊔ Sigma ⊔ P))
    (h16 : Z1 ⊔ P ⊔ Sigma ≤ R1 ∧
      (∀ x y : G, x ∈ Z1 ⊔ P ⊔ Sigma → y ∈ R1 →
        x * y * x⁻¹ * y⁻¹ ∈ R1 ⊓ Subgroup.centralizer (R1 : Set G)) ∧
      (∀ X : Subgroup G, X ≤ Z1 ⊔ P ⊔ Sigma → Nat.card X = 3 →
        (∀ x : G, x ∈ X → x ≠ 1 → IsStronglyReal x) → X = Z1) ∧
      Subgroup.normalizer ((Z1 ⊔ P ⊔ Sigma : Subgroup G) : Set G) =
        Subgroup.normalizer (Z1 : Set G) ∧
      Subgroup.normalizer (Z1 : Set G) =
        R2 ⊔ Subgroup.closure ({s} : Set G))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hp3 : p = 3)
    (hSigmaCard : Nat.card Sigma = 3)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hst3 : orderOf (s * t) = 3)
    (hR2p : IsPGroup 3 R2)
    (hcenterR2 : R2 ⊓ Subgroup.centralizer (R2 : Set G) = Z1) :
    External.WeaklyClosedIn R2 (Z1 ⊔ P ⊔ Sigma) := by
  classical
  let A : Subgroup G := Z1 ⊔ P ⊔ Sigma
  let B0 : Subgroup G := P ⊔ Sigma
  let LV : Subgroup G := L ⊔ V
  have hPcard : Nat.card P = 3 := by
    simpa [hp3] using hch.B1.P_card
  have hZ1card : Nat.card Z1 = 3 := by
    rw [hZ1, Nat.card_zpowers, hst3]
  have hZstrong := chapter2_claim17_Z1_stronglyReal Z1 s t hZ1 hst3
    hch.section3.2.2.1 hch.section3.section2.hA.A1.involution_t
  have hSigma_le_V : Sigma ≤ V := by
    rw [hSigma]
    exact inf_le_left.trans hch.section3.section2.W_le_V
  have hB0_le_V : B0 ≤ V := sup_le hch.B1.P_le_V hSigma_le_V
  have hB0_le_LV : B0 ≤ LV := hB0_le_V.trans le_sup_right
  have hZS_le_LV : Z1 ⊔ Sigma ≤ LV := by
    dsimp [LV]
    rw [← h15.2.2.2.2.2.2.2.2.1]
    exact inf_le_left
  have hZS_le_CLV : Z1 ⊔ Sigma ≤ Subgroup.centralizer (LV : Set G) := by
    dsimp [LV]
    rw [← h15.2.2.2.2.2.2.2.2.1]
    exact inf_le_right
  have hA_le_LV : A ≤ LV := by
    rw [show A = (Z1 ⊔ Sigma) ⊔ P by dsimp [A]; ac_rfl]
    exact sup_le hZS_le_LV (hch.B1.P_le_V.trans le_sup_right)
  have hA_le_R2 : A ≤ R2 := h16.1.trans h14.2.2.2.2.2.2.2.2
  have hP_not_le_Sigma : ¬ P ≤ Sigma := by
    intro hP_le
    apply h15.2.2.2.2.2.1
    exact hP_le.trans ((by rw [hSigma]; exact inf_le_left : Sigma ≤ W).trans
      h15.2.2.2.2.1)
  have hPdisjSigma : Disjoint P Sigma :=
    chapter2_claim17_disjoint_of_card_three_of_not_le P Sigma hPcard hP_not_le_Sigma
  have hSigma_le_CP : Sigma ≤ Subgroup.centralizer (P : Set G) := by
    rw [hSigma]
    exact inf_le_right
  have hB0card : Nat.card B0 = 9 := by
    dsimp [B0]
    rw [chapter2_claim17_natCard_sup_eq_mul_of_disjoint_of_le_normalizer P Sigma
      (hSigma_le_CP.trans (chapter2_claim17_centralizer_le_normalizer P))
      hPdisjSigma, hPcard, hSigmaCard]
  have hB0_le_A : B0 ≤ A := by
    dsimp [A, B0]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hB0pow : ∀ b : G, b ∈ B0 → b ^ 3 = 1 := by
    intro b hb
    apply (h15.2.2.2.2.2.2.2.2.2 b (hB0_le_LV hb)).mpr
    rw [show Z1 ⊔ Sigma ⊔ P = A by dsimp [A]; ac_rfl]
    exact hB0_le_A hb
  have hZ1disjB0 : Disjoint Z1 B0 := by
    rw [disjoint_iff_inf_le]
    intro z hz
    by_contra hzne
    exact
      (chapter2_claim17_not_stronglyReal_of_mem_peterfalviV_order_three
        H D Q K V W Q0 S Q1 t s z hch.section3
        (hB0_le_V hz.2) hzne (hB0pow z hz.2))
      (hZstrong z hz.1 hzne)
  have hB0_le_CZ1 : B0 ≤ Subgroup.centralizer (Z1 : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzCenter : z ∈ LV ⊓ Subgroup.centralizer (LV : Set G) := by
      rw [h15.2.2.2.2.2.2.2.2.1]
      exact Subgroup.mem_sup_left hz
    exact ((Subgroup.mem_centralizer_iff.mp hzCenter.2) b (hB0_le_LV hb)).symm
  have hAcard : Nat.card A = 27 := by
    have hZA : Z1 ⊔ B0 = A := by
      dsimp [A, B0]
      ac_rfl
    rw [← hZA,
      chapter2_claim17_natCard_sup_eq_mul_of_disjoint_of_le_normalizer Z1 B0
        (hB0_le_CZ1.trans (chapter2_claim17_centralizer_le_normalizer Z1))
        hZ1disjB0,
      hZ1card, hB0card]
  have hApow : ∀ a : G, a ∈ A → a ^ 3 = 1 := by
    intro a ha
    apply (h15.2.2.2.2.2.2.2.2.2 a (hA_le_LV ha)).mpr
    rw [show Z1 ⊔ Sigma ⊔ P = A by dsimp [A]; ac_rfl]
    exact ha
  have hAcomm : IsMulCommutative A := by
    simpa [A, LV] using
      chapter2_claim17_commutative P Sigma Z1 LV hPcard
        (hch.B1.P_le_V.trans le_sup_right)
        h15.2.2.2.2.2.2.2.2.1
  letI : IsMulCommutative A := hAcomm
  change A ≤ R2 ∧
    ∀ g : G, rightConjugate A g ≤ R2 → rightConjugate A g = A
  refine ⟨hA_le_R2, ?_⟩
  intro g hg_le
  let Ag : Subgroup G := rightConjugate A g
  let X : Subgroup G := rightConjugate Z1 g
  have hX_le_Ag : X ≤ Ag := by
    dsimp [X, Ag, rightConjugate]
    exact Subgroup.map_mono (by
      dsimp [A]
      exact le_sup_left.trans le_sup_left)
  have hX_le_R2 : X ≤ R2 := hX_le_Ag.trans hg_le
  have hXcard : Nat.card X = 3 := by
    dsimp [X]
    rw [chapter2_claim17_natCard_rightConjugate, hZ1card]
  have hXstrong : ∀ x : G, x ∈ X → x ≠ 1 → IsStronglyReal x := by
    intro x hx hxne
    change x ∈ rightConjugate Z1 g at hx
    rcases hx with ⟨z, hz, rfl⟩
    have hzne : z ≠ 1 := by
      intro hz1
      subst z
      simp at hxne
    simpa [rightConjugateElem, MulAut.conj_apply] using
      (chapter2_claim17_stronglyReal_rightConjugateElem g (hZstrong z hz hzne))
  have hAgcard : Nat.card Ag = 27 := by
    dsimp [Ag]
    rw [chapter2_claim17_natCard_rightConjugate, hAcard]
  have hAgpow : ∀ a : G, a ∈ Ag → a ^ 3 = 1 := by
    intro a ha
    change a ∈ rightConjugate A g at ha
    rcases ha with ⟨b, hb, rfl⟩
    calc
      (MulAut.conj g⁻¹ b) ^ 3 = MulAut.conj g⁻¹ (b ^ 3) := by
        simpa using (map_pow (MulAut.conj g⁻¹) b 3).symm
      _ = 1 := by rw [hApow b hb]; simp
  by_cases hX_le_LV : X ≤ LV
  · have hX_le_A : X ≤ A := by
      intro x hx
      have hxpow : x ^ 3 = 1 := hAgpow x (hX_le_Ag hx)
      have hxmem := (h15.2.2.2.2.2.2.2.2.2 x (hX_le_LV hx)).mp hxpow
      rw [show Z1 ⊔ Sigma ⊔ P = A by dsimp [A]; ac_rfl] at hxmem
      exact hxmem
    have hXeq : X = Z1 := h16.2.2.1 X (by simpa [A] using hX_le_A) hXcard hXstrong
    have hgZ1 : g ∈ Subgroup.normalizer (Z1 : Set G) :=
      chapter2_claim17_mem_normalizer_of_rightConjugate_eq_self
        (by simpa [X] using hXeq)
    have hgA : g ∈ Subgroup.normalizer (A : Set G) := by
      rw [h16.2.2.2.1]
      exact hgZ1
    simpa [Ag] using
      (chapter2_claim17_rightConjugate_eq_self_of_mem_normalizer hgA)
  · have hXdisjLV : Disjoint X LV :=
      chapter2_claim17_disjoint_of_card_three_of_not_le X LV hXcard hX_le_LV
    have hLV_le_R2 : LV ≤ R2 := h15.2.2.2.2.2.2.1
    have hLVindex : (LV.subgroupOf R2).index = 3 := by
      have hmul := (LV.subgroupOf R2).index_mul_card
      rw [natCard_subgroupOf_eq LV R2 hLV_le_R2,
        h15.2.2.2.2.2.2.2.1] at hmul
      exact Nat.mul_right_cancel (Nat.card_pos (α := LV)) hmul
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hLVnormal : (LV.subgroupOf R2).Normal :=
      chapter2_claim17_normal_of_index_eq_prime_of_isPGroup hR2p
        (LV.subgroupOf R2) hLVindex
    have hR2_norm_LV : R2 ≤ Subgroup.normalizer (LV : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLV_le_R2).mp hLVnormal
    have hLVXcard : Nat.card (LV ⊔ X : Subgroup G) = Nat.card LV * 3 := by
      rw [chapter2_claim17_natCard_sup_eq_mul_of_disjoint_of_le_normalizer LV X
        (hX_le_R2.trans hR2_norm_LV) hXdisjLV.symm, hXcard]
    have hLVXeq : LV ⊔ X = R2 := by
      apply Subgroup.eq_of_le_of_card_ge (sup_le hLV_le_R2 hX_le_R2)
      rw [hLVXcard, h15.2.2.2.2.2.2.2.1]
      simp [LV, Nat.mul_comm]
    let LV2 : Subgroup R2 := LV.subgroupOf R2
    let Ag2 : Subgroup R2 := Ag.subgroupOf R2
    letI : LV2.Normal := by simpa [LV2] using hLVnormal
    let q : R2 →* R2 ⧸ LV2 := QuotientGroup.mk' LV2
    have hquotcard : Nat.card (R2 ⧸ LV2) = 3 := by
      change LV2.index = 3
      simpa [LV2] using hLVindex
    obtain ⟨z, hzX, hzLV⟩ := Set.not_subset.mp hX_le_LV
    have hzAg : z ∈ Ag := hX_le_Ag hzX
    let zR2 : R2 := ⟨z, hX_le_R2 hzX⟩
    have hzImg : q zR2 ∈ Ag2.map q := by
      exact ⟨zR2, hzAg, rfl⟩
    have hzqne : q zR2 ≠ 1 := by
      intro hzq
      apply hzLV
      exact (QuotientGroup.eq_one_iff (N := LV2) (x := zR2)).mp hzq
    have hImg_ne : Ag2.map q ≠ ⊥ := by
      intro hbot
      have hzbot : q zR2 ∈ (⊥ : Subgroup (R2 ⧸ LV2)) := by
        rw [← hbot]
        exact hzImg
      exact hzqne (by simpa using hzbot)
    have hImg_top : Ag2.map q = ⊤ := by
      haveI : Fact (Nat.card (R2 ⧸ LV2)).Prime := ⟨by
        rw [hquotcard]
        exact Nat.prime_three⟩
      rcases (Ag2.map q).eq_bot_or_eq_top_of_prime_card with hbot | htop
      · exact (hImg_ne hbot).elim
      · exact htop
    have hImgcard : Nat.card (Ag2.map q) = 3 := by
      rw [hImg_top]
      simpa using hquotcard
    have hrel : LV2.relIndex Ag2 = 3 := by
      calc
        LV2.relIndex Ag2 = q.ker.relIndex Ag2 := by
          rw [QuotientGroup.ker_mk']
        _ = Nat.card (Ag2.map q) := Subgroup.relIndex_ker Ag2 q
        _ = 3 := hImgcard
    let Ksub : Subgroup Ag2 := LV2.subgroupOf Ag2
    have hKindex : Ksub.index = 3 := by
      simpa [Ksub, Subgroup.relIndex] using hrel
    have hAg2card : Nat.card Ag2 = 27 := by
      simpa [Ag2] using
        (natCard_subgroupOf_eq Ag R2 hg_le).trans hAgcard
    have hKcard : Nat.card Ksub = 9 := by
      have hmul := Ksub.card_mul_index
      rw [hKindex, hAg2card] at hmul
      omega
    let B : Subgroup G := Ag ⊓ LV
    let e : Ksub ≃ B :=
      { toFun := fun k => ⟨(k : G), ⟨k.1.property, k.property⟩⟩
        invFun := fun b =>
          ⟨⟨⟨(b : G), hg_le b.property.1⟩, b.property.1⟩, b.property.2⟩
        left_inv := by intro k; rfl
        right_inv := by intro b; rfl }
    have hBcard : Nat.card B = 9 :=
      (Nat.card_congr e).symm.trans hKcard
    have hB_le_Ag : B ≤ Ag := inf_le_left
    have hB_le_LV : B ≤ LV := inf_le_right
    have hB_le_A : B ≤ A := by
      intro b hb
      have hbmem := (h15.2.2.2.2.2.2.2.2.2 b (hB_le_LV hb)).mp
        (hAgpow b (hB_le_Ag hb))
      rw [show Z1 ⊔ Sigma ⊔ P = A by dsimp [A]; ac_rfl] at hbmem
      exact hbmem
    have hBnotStrong :
        ∀ b : G, b ∈ B → b ≠ 1 → ¬ IsStronglyReal b := by
      intro b hb hbne hbstrong
      let Y : Subgroup G := Subgroup.zpowers b
      have hborder : orderOf b = 3 :=
        orderOf_eq_prime (hAgpow b (hB_le_Ag hb)) hbne
      have hYcard : Nat.card Y = 3 := by
        dsimp [Y]
        rw [Nat.card_zpowers, hborder]
      have hY_le_B : Y ≤ B := Subgroup.zpowers_le.mpr hb
      have hYstrong :
          ∀ y : G, y ∈ Y → y ≠ 1 → IsStronglyReal y :=
        chapter2_claim17_zpowers_stronglyReal_of_generator hbstrong hborder
      have hYeqZ1 : Y = Z1 :=
        h16.2.2.1 Y (hY_le_B.trans hB_le_A) hYcard hYstrong
      have hYeqX : Y = X :=
        chapter2_claim17_unique_stronglyReal_three_subgroup_rightConjugate
          A Z1 g h16.2.2.1 Y (hY_le_B.trans hB_le_Ag) hYcard hYstrong
      have hXeqZ1 : X = Z1 := hYeqX.symm.trans hYeqZ1
      apply hX_le_LV
      rw [hXeqZ1]
      exact le_sup_left.trans hZS_le_LV
    have hBdisjZ1 : Disjoint B Z1 := by
      rw [disjoint_iff_inf_le]
      intro z hz
      by_contra hzne
      exact (hBnotStrong z hz.1 hzne) (hZstrong z hz.2 hzne)
    have hB_le_CZ1 : B ≤ Subgroup.centralizer (Z1 : Set G) := by
      intro b hb
      have hbA := hB_le_A hb
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := A)).comm
          ⟨z, (by
            dsimp [A]
            exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hz))⟩
          ⟨b, hbA⟩)
    have hZBcard : Nat.card (Z1 ⊔ B : Subgroup G) = 27 := by
      rw [chapter2_claim17_natCard_sup_eq_mul_of_disjoint_of_le_normalizer Z1 B
        (hB_le_CZ1.trans (chapter2_claim17_centralizer_le_normalizer Z1))
        hBdisjZ1.symm, hZ1card, hBcard]
    have hZB_eq_A : Z1 ⊔ B = A := by
      apply Subgroup.eq_of_le_of_card_ge
        (sup_le (by dsimp [A]; exact le_sup_left.trans le_sup_left) hB_le_A)
      rw [hZBcard, hAcard]
    haveI : IsMulCommutative Ag := by
      change IsMulCommutative
        (A.map (MulAut.conj g⁻¹).toMonoidHom)
      infer_instance
    have hAg_le_CAg : Ag ≤ Subgroup.centralizer (Ag : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
    have hX_le_CB : X ≤ Subgroup.centralizer (B : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp
        (hAg_le_CAg (hX_le_Ag hx))) b (hB_le_Ag hb)
    have hX_le_CZ1 : X ≤ Subgroup.centralizer (Z1 : Set G) := by
      rw [← h14.2.2.2.2.2.2.2.1]
      exact hX_le_R2
    have hX_le_CA : X ≤ Subgroup.centralizer (A : Set G) := by
      rw [← hZB_eq_A]
      exact Subgroup.le_centralizer_sup_of_le_centralizers hX_le_CZ1 hX_le_CB
    have hZS_le_A : Z1 ⊔ Sigma ≤ A := by
      dsimp [A]
      exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
    have hZS_le_CX : Z1 ⊔ Sigma ≤ Subgroup.centralizer (X : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact ((Subgroup.mem_centralizer_iff.mp (hX_le_CA hx)) z
        (hZS_le_A hz)).symm
    have hZS_le_CR2 : Z1 ⊔ Sigma ≤ Subgroup.centralizer (R2 : Set G) := by
      rw [← hLVXeq]
      exact Subgroup.le_centralizer_sup_of_le_centralizers hZS_le_CLV hZS_le_CX
    have hZS_le_ZR2 :
        Z1 ⊔ Sigma ≤ R2 ⊓ Subgroup.centralizer (R2 : Set G) :=
      fun z hz => ⟨hLV_le_R2 (hZS_le_LV hz), hZS_le_CR2 hz⟩
    have hSigma_le_Z1 : Sigma ≤ Z1 := by
      rw [hcenterR2] at hZS_le_ZR2
      exact le_sup_right.trans hZS_le_ZR2
    have hSigma_bot : Sigma = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro z hz
      have hzinf : z ∈ Z1 ⊓ B0 := by
        exact ⟨hSigma_le_Z1 hz,
          (by dsimp [B0]; exact Subgroup.mem_sup_right hz)⟩
      have hdisj : Z1 ⊓ B0 ≤ ⊥ := by
        rwa [← disjoint_iff_inf_le]
      exact hdisj hzinf
    have hSigma_one : Nat.card Sigma = 1 := by
      rw [hSigma_bot]
      simp
    omega

private theorem chapter2_claim17_commutator_le_zpowers_of_center_sup_two_generators
    {G : Type*} [Group G] (x y : G)
    (hcomm : _root_.commutator G ≤ Subgroup.center G)
    (hgen : Subgroup.center G ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤) :
    _root_.commutator G ≤ Subgroup.zpowers ⁅x, y⁆ := by
  classical
  let C : Subgroup G := Subgroup.zpowers ⁅x, y⁆
  let U : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers y
  have hUclosure : U = Subgroup.closure ({x, y} : Set G) := by
    dsimp [U]
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union]
    congr 1
  have hCcenter : C ≤ Subgroup.center G := by
    apply Subgroup.zpowers_le.mpr
    exact hcomm (Subgroup.commutator_mem_commutator
      (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G)) trivial trivial)
  have hUU : ∀ u : G, u ∈ U → ∀ v : G, v ∈ U → ⁅u, v⁆ ∈ C := by
    intro u hu
    rw [hUclosure] at hu
    refine Subgroup.closure_induction (p := fun u _ =>
      ∀ v : G, v ∈ U → ⁅u, v⁆ ∈ C) ?_ ?_ ?_ ?_ hu
    · intro u hu v hv
      rw [hUclosure] at hv
      refine Subgroup.closure_induction (p := fun v _ => ⁅u, v⁆ ∈ C)
        ?_ ?_ ?_ ?_ hv
      · intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
        rcases hu with hu | hu <;> rcases hv with hv | hv
        · subst u; subst v
          simpa [C] using C.one_mem
        · subst u; subst v
          exact Subgroup.mem_zpowers ⁅x, y⁆
        · subst u; subst v
          simpa [C, commutatorElement_inv x y] using
            (C.inv_mem (Subgroup.mem_zpowers ⁅x, y⁆))
        · subst u; subst v
          simpa [C] using C.one_mem
      · simpa [C] using C.one_mem
      · intro a b _ _ ha hb
        rw [TBSBaer.commutator_mul_right_of_commutator_le_center hcomm]
        exact C.mul_mem ha hb
      · intro a _ ha
        have hprod : ⁅u, a⁆ * ⁅u, a⁻¹⁆ = 1 := by
          rw [← TBSBaer.commutator_mul_right_of_commutator_le_center hcomm]
          simp
        rw [eq_inv_of_mul_eq_one_right hprod]
        exact C.inv_mem ha
    · intro v hv
      simpa [C] using C.one_mem
    · intro a b _ _ ha hb v hv
      rw [TBSBaer.commutator_mul_left_of_commutator_le_center hcomm]
      exact C.mul_mem (ha v hv) (hb v hv)
    · intro a _ ha v hv
      have hprod : ⁅a, v⁆ * ⁅a⁻¹, v⁆ = 1 := by
        rw [← TBSBaer.commutator_mul_left_of_commutator_le_center hcomm]
        simp
      rw [eq_inv_of_mul_eq_one_right hprod]
      exact C.inv_mem (ha v hv)
  rw [commutator_eq_closure, Subgroup.closure_le]
  intro c hc
  rcases hc with ⟨a, b, rfl⟩
  have haTop : a ∈ Subgroup.center G ⊔ U := by
    rw [show Subgroup.center G ⊔ U = ⊤ by simpa [U, sup_assoc] using hgen]
    trivial
  have hbTop : b ∈ Subgroup.center G ⊔ U := by
    rw [show Subgroup.center G ⊔ U = ⊤ by simpa [U, sup_assoc] using hgen]
    trivial
  rcases (Subgroup.mem_sup_of_normal_left (s := Subgroup.center G) (t := U)).mp haTop with
    ⟨za, hza, ua, hua, hzaa⟩
  rcases (Subgroup.mem_sup_of_normal_left (s := Subgroup.center G) (t := U)).mp hbTop with
    ⟨zb, hzb, ub, hub, hzbb⟩
  rw [← hzaa, ← hzbb,
    TBSBaer.commutator_mul_left_of_commutator_le_center hcomm,
    TBSBaer.commutator_mul_right_of_commutator_le_center hcomm,
    TBSBaer.commutator_mul_right_of_commutator_le_center hcomm,
    TBSBaer.commutator_eq_one_of_left_mem_center hza,
    TBSBaer.commutator_eq_one_of_left_mem_center hza,
    TBSBaer.commutator_eq_one_of_right_mem_center hzb]
  simpa using hUU ua hua ub hub


private theorem chapter2_claim17_commutator_pow_left_of_commutator_le_center
    {G : Type*} [Group G]
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y : G) :
    ∀ n : ℕ, ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, TBSBaer.commutator_mul_left_of_commutator_le_center hcomm,
        ih, pow_succ]

private theorem chapter2_claim17_card_sup_eq_mul_of_disjoint_of_commutative
    {G : Type*} [Group G] [Finite G] [IsMulCommutative G]
    (A B : Subgroup G) (hdisj : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have hinj : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisj
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective toSup := by
    intro z
    have hz : (z : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B]
      · exact z.property
      · letI : A.Normal := inferInstance
        rw [Subgroup.normalizer_eq_top]
        exact le_top
    rcases hz with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinj, hsurj⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

private theorem chapter2_claim17_commutator_card_le_three_of_center_index_le_nine
    {G : Type*} [Group G] [Finite G]
    (hGp : IsPGroup 3 G) (hindex : (Subgroup.center G).index ≤ 9) :
    Nat.card (_root_.commutator G) ≤ 3 := by
  classical
  let Z : Subgroup G := Subgroup.center G
  letI : Z.Normal := by dsimp [Z]; infer_instance
  let q : G →* G ⧸ Z := QuotientGroup.mk' Z
  have hVp : IsPGroup 3 (G ⧸ Z) := hGp.to_quotient Z
  obtain ⟨n, hn⟩ := hVp.exists_card_eq
  have hnle : n ≤ 2 := by
    by_contra hnot
    have hn3 : 3 ≤ n := by omega
    have h27 : 27 ≤ 3 ^ n := by
      calc
        27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have : 3 ^ n ≤ 9 := by
      change Z.index ≤ 9 at hindex
      rwa [Subgroup.index_eq_card Z, hn] at hindex
    omega
  interval_cases n
  · have hVcard : Nat.card (G ⧸ Z) = 1 := by simpa using hn
    haveI : Subsingleton (G ⧸ Z) := (Nat.card_eq_one_iff_unique.mp hVcard).1
    haveI : IsCyclic (G ⧸ Z) := isCyclic_of_subsingleton
    haveI hmul : IsMulCommutative G :=
      MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center q (by simp [q, Z])
    have hbot : _root_.commutator G = ⊥ := by
      rw [commutator_eq_closure]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro c ⟨a, b, rfl⟩
        simpa [commutatorElement_eq_one_iff_mul_comm, hmul.is_comm.comm a b]
      · exact bot_le
    simp [hbot]
  · have hVcard : Nat.card (G ⧸ Z) = 3 := by simpa using hn
    haveI : IsCyclic (G ⧸ Z) := isCyclic_of_prime_card hVcard
    haveI hmul : IsMulCommutative G :=
      MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center q (by simp [q, Z])
    have hbot : _root_.commutator G = ⊥ := by
      rw [commutator_eq_closure]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro c ⟨a, b, rfl⟩
        simpa [commutatorElement_eq_one_iff_mul_comm, hmul.is_comm.comm a b]
      · exact bot_le
    simp [hbot]
  · have hVcard : Nat.card (G ⧸ Z) = 9 := by simpa using hn
    by_cases hVcyc : IsCyclic (G ⧸ Z)
    · letI : IsCyclic (G ⧸ Z) := hVcyc
      haveI hmul : IsMulCommutative G :=
        MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center q (by simp [q, Z])
      have hbot : _root_.commutator G = ⊥ := by
        rw [commutator_eq_closure]
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro c ⟨a, b, rfl⟩
          simpa [commutatorElement_eq_one_iff_mul_comm, hmul.is_comm.comm a b]
        · exact bot_le
      simp [hbot]
    · have hVcomm : IsMulCommutative (G ⧸ Z) :=
        IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
          (by simpa using hVcard)
      letI : IsMulCommutative (G ⧸ Z) := hVcomm
      have hVexp : Monoid.exponent (G ⧸ Z) = 3 :=
        (not_isCyclic_iff_exponent_eq_prime Nat.prime_three
          (by simpa using hVcard)).mp hVcyc
      letI : IsElementaryAbelian 3 (G ⧸ Z) :=
        { toIsMulCommutative := hVcomm
          exponent_dvd_p := by rw [hVexp] }
      haveI : Nontrivial (G ⧸ Z) :=
        Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨xb, hxb⟩ := exists_ne (1 : G ⧸ Z)
      let X : Subgroup (G ⧸ Z) := Subgroup.zpowers xb
      have hxb3 : xb ^ 3 = 1 := by
        rw [← hVexp]
        exact Monoid.pow_exponent_eq_one xb
      have hxbOrder : orderOf xb = 3 := orderOf_eq_prime hxb3 hxb
      have hXcard : Nat.card X = 3 := by
        dsimp [X]
        rw [Nat.card_zpowers, hxbOrder]
      obtain ⟨Y, hXY⟩ := IsElementaryAbelian.exists_isCompl 3 (G ⧸ Z) X
      have hYcard : Nat.card Y = 3 := by
        have hsupCard := chapter2_claim17_card_sup_eq_mul_of_disjoint_of_commutative X Y hXY.disjoint
        rw [hXY.sup_eq_top] at hsupCard
        have htopCard : Nat.card (⊤ : Subgroup (G ⧸ Z)) = 9 := by
          simpa using hVcard
        rw [htopCard, hXcard] at hsupCard
        omega
      have hYcyc : IsCyclic Y := isCyclic_of_prime_card hYcard
      obtain ⟨yb, hyb⟩ := IsCyclic.exists_generator (α := Y)
      have hYgen : Subgroup.zpowers (yb : G ⧸ Z) = Y := by
        apply le_antisymm
        · exact Subgroup.zpowers_le.mpr yb.property
        · intro z hz
          have hzY : (⟨z, hz⟩ : Y) ∈ Subgroup.zpowers yb := hyb ⟨z, hz⟩
          rcases hzY with ⟨n, hnz⟩
          exact ⟨n, congrArg Subtype.val hnz⟩
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z xb
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Z (yb : G ⧸ Z)
      let H0 : Subgroup G := Z ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers y
      have hmapH0 : H0.map q = ⊤ := by
        calc
          H0.map q = Z.map q ⊔ (Subgroup.zpowers x).map q ⊔
              (Subgroup.zpowers y).map q := by
                simp [H0, Subgroup.map_sup]
          _ = ⊥ ⊔ X ⊔ Y := by
                rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, hx, hy]
                simp [q, Z, X, hYgen]
          _ = ⊤ := by simpa using hXY.sup_eq_top
      have hgen : H0 = ⊤ := by
        apply top_unique
        intro g _
        have hqg : q g ∈ H0.map q := by rw [hmapH0]; trivial
        rcases hqg with ⟨h, hh, hEq⟩
        have hdiv : g * h⁻¹ ∈ Z := by
          have := (QuotientGroup.eq_iff_div_mem (N := Z) (x := g) (y := h)).mp hEq.symm
          simpa [div_eq_mul_inv] using this
        have hdivH : g * h⁻¹ ∈ H0 := by
          exact (show Z ≤ H0 by
            dsimp [H0]
            exact le_sup_left.trans le_sup_left) hdiv
        have hgh : (g * h⁻¹) * h ∈ H0 := H0.mul_mem hdivH hh
        simpa [mul_assoc] using hgh
      have hcomm : _root_.commutator G ≤ Subgroup.center G := by
        change _root_.commutator G ≤ Z
        haveI : IsMulCommutative (G ⧸ Z) := hVcomm
        exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Z)).mp
          inferInstance
      have hcomm_le : _root_.commutator G ≤ Subgroup.zpowers ⁅x, y⁆ :=
        chapter2_claim17_commutator_le_zpowers_of_center_sup_two_generators x y hcomm (by
          simpa [H0, Z] using hgen)
      have hx3Z : x ^ 3 ∈ Subgroup.center G := by
        change x ^ 3 ∈ Z
        apply (QuotientGroup.eq_one_iff (N := Z) (x := x ^ 3)).mp
        calc
          q (x ^ 3) = (q x) ^ 3 := map_pow q x 3
          _ = xb ^ 3 := by rw [hx]
          _ = 1 := hxb3
      have hc3 : ⁅x, y⁆ ^ 3 = 1 := by
        rw [← chapter2_claim17_commutator_pow_left_of_commutator_le_center hcomm]
        exact TBSBaer.commutator_eq_one_of_left_mem_center hx3Z
      calc
        Nat.card (_root_.commutator G) ≤ Nat.card (Subgroup.zpowers ⁅x, y⁆) :=
          Subgroup.card_le_of_le hcomm_le
        _ = orderOf ⁅x, y⁆ := Nat.card_zpowers ⁅x, y⁆
        _ ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc3)


private theorem chapter2_claim17_internalSemidirect_mul_unique
    {G : Type*} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K)
    {h₁ h₂ k₁ k₂ : G}
    (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H)
    (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (hmul : h₁ * k₁ = h₂ * k₂) :
    h₁ = h₂ ∧ k₁ = k₂ := by
  have hleft_eq_right : h₂⁻¹ * h₁ = k₂ * k₁⁻¹ := by
    calc
      h₂⁻¹ * h₁ = h₂⁻¹ * (h₁ * k₁) * k₁⁻¹ := by simp [mul_assoc]
      _ = h₂⁻¹ * (h₂ * k₂) * k₁⁻¹ := by rw [hmul]
      _ = k₂ * k₁⁻¹ := by simp
  have hmemH : h₂⁻¹ * h₁ ∈ H := H.mul_mem (H.inv_mem hh₂) hh₁
  have hmemK : h₂⁻¹ * h₁ ∈ K := by
    rw [hleft_eq_right]
    exact K.mul_mem hk₂ (K.inv_mem hk₁)
  have hbot : h₂⁻¹ * h₁ ∈ (⊥ : Subgroup G) := by
    have hinf : h₂⁻¹ * h₁ ∈ H ⊓ K := ⟨hmemH, hmemK⟩
    rw [h.inf_eq_bot] at hinf
    exact hinf
  have hh_eq_one : h₂⁻¹ * h₁ = 1 := by simpa using hbot
  have hh : h₁ = h₂ := by
    calc
      h₁ = h₂ * (h₂⁻¹ * h₁) := by simp
      _ = h₂ := by simp [hh_eq_one]
  have hk : k₁ = k₂ := by
    have hmul' := congrArg (fun z : G => h₂⁻¹ * z) hmul
    simpa [hh, mul_assoc] using hmul'
  exact ⟨hh, hk⟩

private theorem chapter2_claim17_internalSemidirect_top
    {G : Type*} [Group G] (H V : Subgroup G)
    (hV_norm_H : V ≤ Subgroup.normalizer (H : Set G))
    (hdisj : Disjoint H V) :
    Section2.IsInternalSemidirectProduct
      (⊤ : Subgroup ↥(H ⊔ V : Subgroup G))
      (H.subgroupOf (H ⊔ V)) (V.subgroupOf (H ⊔ V)) := by
  refine
    { left_le := ?_
      right_le := ?_
      right_normalizes_left := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro x _hx
    exact Subgroup.mem_top x
  · intro x _hx
    exact Subgroup.mem_top x
  · intro k hk h hh
    change (((k : ↥(H ⊔ V : Subgroup G)) : G) *
        ((h : ↥(H ⊔ V : Subgroup G)) : G) *
        ((k : ↥(H ⊔ V : Subgroup G)) : G)⁻¹) ∈ H
    have hkV : ((k : ↥(H ⊔ V : Subgroup G)) : G) ∈ V := by
      simpa [Subgroup.mem_subgroupOf] using hk
    have hhH : ((h : ↥(H ⊔ V : Subgroup G)) : G) ∈ H := by
      simpa [Subgroup.mem_subgroupOf] using hh
    exact (Subgroup.mem_normalizer_iff.mp (hV_norm_H hkV)
      ((h : ↥(H ⊔ V : Subgroup G)) : G)).1 hhH
  · apply le_antisymm
    · intro x hx
      have hxH : ((x : ↥(H ⊔ V : Subgroup G)) : G) ∈ H := by
        simpa [Subgroup.mem_subgroupOf] using hx.1
      have hxV : ((x : ↥(H ⊔ V : Subgroup G)) : G) ∈ V := by
        simpa [Subgroup.mem_subgroupOf] using hx.2
      have hxBot : ((x : ↥(H ⊔ V : Subgroup G)) : G) ∈ (⊥ : Subgroup G) :=
        hdisj.le_bot ⟨hxH, hxV⟩
      ext
      simpa using hxBot
    · exact bot_le
  · intro c _hc
    have hmulset := Subgroup.coe_mul_of_right_le_normalizer_left H V hV_norm_H
    have hcProd :
        ((c : ↥(H ⊔ V : Subgroup G)) : G) ∈ (H : Set G) * (V : Set G) := by
      rw [← hmulset]
      exact c.property
    rcases hcProd with ⟨h0, hh0, v0, hv0, hprod⟩
    let hC : ↥(H ⊔ V : Subgroup G) :=
      ⟨h0, (le_sup_left : H ≤ H ⊔ V) hh0⟩
    let vC : ↥(H ⊔ V : Subgroup G) :=
      ⟨v0, (le_sup_right : V ≤ H ⊔ V) hv0⟩
    refine ⟨hC, ?_, vC, ?_, ?_⟩
    · change (hC : G) ∈ H
      exact hh0
    · change (vC : G) ∈ V
      exact hv0
    · apply Subtype.ext
      exact hprod.symm

private noncomputable def chapter2_claim17_internalLeft
    {L : Type*} [Group L] {H K : Subgroup L}
    (h : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H K)
    (x : L) : H := by
  classical
  let hs := h.mul_surjective x (Subgroup.mem_top x)
  exact ⟨Classical.choose hs, (Classical.choose_spec hs).1⟩

private noncomputable def chapter2_claim17_internalRight
    {L : Type*} [Group L] {H K : Subgroup L}
    (h : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H K)
    (x : L) : K := by
  classical
  let hs := h.mul_surjective x (Subgroup.mem_top x)
  let hk := (Classical.choose_spec hs).2
  exact ⟨Classical.choose hk, (Classical.choose_spec hk).1⟩

private theorem chapter2_claim17_internalLeft_mul_right
    {L : Type*} [Group L] {H K : Subgroup L}
    (h : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H K)
    (x : L) :
    (chapter2_claim17_internalLeft h x : L) *
        (chapter2_claim17_internalRight h x : L) = x := by
  classical
  dsimp [chapter2_claim17_internalLeft, chapter2_claim17_internalRight]
  let hs := h.mul_surjective x (Subgroup.mem_top x)
  let hk := (Classical.choose_spec hs).2
  exact (Classical.choose_spec hk).2.symm

private theorem chapter2_claim17_internalLeft_of_mul
    {L : Type*} [Group L] {H K : Subgroup L}
    (h : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H K)
    (h0 : H) (k0 : K) :
    chapter2_claim17_internalLeft h ((h0 : L) * (k0 : L)) = h0 := by
  apply Subtype.ext
  have hdec := chapter2_claim17_internalLeft_mul_right h ((h0 : L) * (k0 : L))
  exact
    (chapter2_claim17_internalSemidirect_mul_unique h
      (chapter2_claim17_internalLeft h ((h0 : L) * (k0 : L))).2 h0.2
      (chapter2_claim17_internalRight h ((h0 : L) * (k0 : L))).2 k0.2 hdec).1

private noncomputable def chapter2_claim17_internalInvariantCharacter
    {L A : Type*} [Group L] [Group A] {H K : Subgroup L}
    (h : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H K)
    (χ : H →* A)
    (hinv : ∀ k : K, ∀ h0 : H,
      χ ⟨Section2.conjBy (k : L) (h0 : L),
          h.right_normalizes_left (k : L) k.2 (h0 : L) h0.2⟩ = χ h0) :
    L →* A where
  toFun x := χ (chapter2_claim17_internalLeft h x)
  map_one' := by
    have hleft := chapter2_claim17_internalLeft_of_mul h (1 : H) (1 : K)
    simpa using congrArg χ hleft
  map_mul' := by
    intro x y
    let lx := chapter2_claim17_internalLeft h x
    let rx := chapter2_claim17_internalRight h x
    let ly := chapter2_claim17_internalLeft h y
    let ry := chapter2_claim17_internalRight h y
    have hdec_x : (lx : L) * (rx : L) = x := chapter2_claim17_internalLeft_mul_right h x
    have hdec_y : (ly : L) * (ry : L) = y := chapter2_claim17_internalLeft_mul_right h y
    have hconj_mem : Section2.conjBy (rx : L) (ly : L) ∈ H :=
      h.right_normalizes_left (rx : L) rx.2 (ly : L) ly.2
    have hleft_mem : (lx : L) * Section2.conjBy (rx : L) (ly : L) ∈ H :=
      H.mul_mem lx.2 hconj_mem
    have hright_mem : (rx : L) * (ry : L) ∈ K := K.mul_mem rx.2 ry.2
    have hprod :
        ((lx : L) * Section2.conjBy (rx : L) (ly : L)) *
            ((rx : L) * (ry : L)) = x * y := by
      calc
        ((lx : L) * Section2.conjBy (rx : L) (ly : L)) *
            ((rx : L) * (ry : L)) =
            ((lx : L) * (rx : L)) * ((ly : L) * (ry : L)) := by
              simp [Section2.conjBy, mul_assoc]
        _ = x * y := by rw [hdec_x, hdec_y]
    have hdec_xy := chapter2_claim17_internalLeft_mul_right h (x * y)
    have hleft_eq :
        chapter2_claim17_internalLeft h (x * y) =
          ⟨(lx : L) * Section2.conjBy (rx : L) (ly : L), hleft_mem⟩ := by
      apply Subtype.ext
      exact
        (chapter2_claim17_internalSemidirect_mul_unique h
          (chapter2_claim17_internalLeft h (x * y)).2 hleft_mem
          (chapter2_claim17_internalRight h (x * y)).2 hright_mem
          (by simpa [hprod] using hdec_xy)).1
    let cly : H := ⟨Section2.conjBy (rx : L) (ly : L), hconj_mem⟩
    calc
      χ (chapter2_claim17_internalLeft h (x * y)) =
          χ ⟨(lx : L) * Section2.conjBy (rx : L) (ly : L), hleft_mem⟩ := by rw [hleft_eq]
      _ = χ (lx * cly) := rfl
      _ = χ lx * χ cly := by rw [map_mul]
      _ = χ lx * χ ly := by rw [hinv rx ly]

private theorem chapter2_claim17_internalInvariantCharacter_apply_left
    {L A : Type*} [Group L] [Group A] {H K : Subgroup L}
    (h : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H K)
    (χ : H →* A)
    (hinv : ∀ k : K, ∀ h0 : H,
      χ ⟨Section2.conjBy (k : L) (h0 : L),
          h.right_normalizes_left (k : L) k.2 (h0 : L) h0.2⟩ = χ h0)
    (h0 : H) :
    chapter2_claim17_internalInvariantCharacter h χ hinv (h0 : L) = χ h0 := by
  change χ (chapter2_claim17_internalLeft h (h0 : L)) = χ h0
  have hleft := chapter2_claim17_internalLeft_of_mul h h0 (1 : K)
  simpa using congrArg χ hleft

private theorem chapter2_claim17_local_index_of_invariant_character
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    (H V : Subgroup G)
    (hV_norm_H : V ≤ Subgroup.normalizer (H : Set G))
    (hdisj : Disjoint H V)
    (χ : H →* A) (hχ : Function.Surjective χ)
    (hinv : ∀ v : V, ∀ h : H,
      χ ⟨Section2.conjBy (v : G) (h : G),
          (Subgroup.mem_normalizer_iff.mp (hV_norm_H v.2) (h : G)).1 h.2⟩ = χ h) :
    ∃ M : Subgroup (H ⊔ V : Subgroup G),
      M.Normal ∧ Nat.card ((H ⊔ V : Subgroup G) ⧸ M) = Nat.card A := by
  classical
  let L : Type _ := ↥(H ⊔ V : Subgroup G)
  let HL : Subgroup L := H.subgroupOf (H ⊔ V)
  let VL : Subgroup L := V.subgroupOf (H ⊔ V)
  let hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) HL VL :=
    chapter2_claim17_internalSemidirect_top H V hV_norm_H hdisj
  let χL : HL →* A :=
    χ.comp
      { toFun := fun h => ⟨((h : L) : G), h.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
  have hinvL : ∀ v : VL, ∀ h : HL,
      χL ⟨Section2.conjBy (v : L) (h : L),
          hsemi.right_normalizes_left (v : L) v.2 (h : L) h.2⟩ = χL h := by
    intro v h
    exact hinv ⟨((v : L) : G), v.2⟩ ⟨((h : L) : G), h.2⟩
  let ψ : L →* A := chapter2_claim17_internalInvariantCharacter hsemi χL hinvL
  have hψ : Function.Surjective ψ := by
    intro a
    obtain ⟨h, rfl⟩ := hχ a
    let hL : HL := ⟨⟨(h : G), (le_sup_left : H ≤ H ⊔ V) h.2⟩, h.2⟩
    refine ⟨(hL : L), ?_⟩
    simpa [ψ, χL, hL] using
      chapter2_claim17_internalInvariantCharacter_apply_left hsemi χL hinvL hL
  refine ⟨ψ.ker, inferInstance, ?_⟩
  exact
    (Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv).trans rfl


private theorem chapter2_claim17_mem_normalizer_centralizer_of_mem_normalizer
    {G : Type*} [Group G] (A : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro a ha
    have ha_back : g⁻¹ * a * g ∈ A := by
      apply (hg (g⁻¹ * a * g)).mpr
      simpa [mul_assoc] using ha
    calc
      a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [hx _ ha_back]
      _ = (g * x * g⁻¹) * a := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro a ha
    have hga : g * a * g⁻¹ ∈ A := (hg a).mp ha
    have hcomm := hx (g * a * g⁻¹) hga
    have h := congrArg (fun z : G => g⁻¹ * z * g) hcomm
    simpa [mul_assoc] using h

private theorem chapter2_claim17_fixed_subgroup_of_inverted_semidirect
    {G : Type*} [Group G] [Finite G]
    (T B : Subgroup G) (s : G) (hs : IsInvolution s)
    (hB_norm_T : B ≤ Subgroup.normalizer (T : Set G))
    (hdisj : Disjoint T B) (hTp : IsPGroup 3 T)
    (hinvT : ∀ x : G, x ∈ T → rightConjugateElem x s = x⁻¹)
    (hcentB : B ≤ Subgroup.centralizer ({s} : Set G)) :
    (T ⊔ B) ⊓ Subgroup.centralizer ({s} : Set G) = B := by
  classical
  apply le_antisymm
  · intro x hx
    let TB : Subgroup G := T ⊔ B
    let T0 : Subgroup TB := T.subgroupOf TB
    let B0 : Subgroup TB := B.subgroupOf TB
    let hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup TB) T0 B0 :=
      chapter2_claim17_internalSemidirect_top T B hB_norm_T hdisj
    let xTB : TB := ⟨x, hx.1⟩
    let l : T0 := chapter2_claim17_internalLeft hsemi xTB
    let r : B0 := chapter2_claim17_internalRight hsemi xTB
    have hlT : ((l : TB) : G) ∈ T := by
      change (l : TB) ∈ T.subgroupOf TB
      exact l.2
    have hrB : ((r : TB) : G) ∈ B := by
      change (r : TB) ∈ B.subgroupOf TB
      exact r.2
    have hdecTB := chapter2_claim17_internalLeft_mul_right hsemi xTB
    have hdec : ((l : TB) : G) * ((r : TB) : G) = x :=
      congrArg Subtype.val hdecTB
    have hxcomm : x * s = s * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hxfix : s * x * s⁻¹ = x := by
      calc
        s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [hxcomm.symm]
        _ = x := by simp [mul_assoc]
    have hlInv : s * ((l : TB) : G) * s⁻¹ = ((l : TB) : G)⁻¹ := by
      simpa [rightConjugateElem, hs.inv_eq_self] using
        (hinvT ((l : TB) : G) hlT)
    have hrFix : s * ((r : TB) : G) * s⁻¹ = ((r : TB) : G) := by
      have hrs : ((r : TB) : G) * s = s * ((r : TB) : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hcentB hrB)
      calc
        s * ((r : TB) : G) * s⁻¹ = (((r : TB) : G) * s) * s⁻¹ := by rw [hrs.symm]
        _ = ((r : TB) : G) := by simp [mul_assoc]
    have hconjDec :
        s * x * s⁻¹ = ((l : TB) : G)⁻¹ * ((r : TB) : G) := by
      rw [← hdec]
      calc
        s * (((l : TB) : G) * ((r : TB) : G)) * s⁻¹ =
            (s * ((l : TB) : G) * s⁻¹) *
              (s * ((r : TB) : G) * s⁻¹) := by group
        _ = ((l : TB) : G)⁻¹ * ((r : TB) : G) := by rw [hlInv, hrFix]
    have hlEqInv : ((l : TB) : G)⁻¹ = ((l : TB) : G) := by
      apply mul_right_cancel (b := ((r : TB) : G))
      calc
        ((l : TB) : G)⁻¹ * ((r : TB) : G) = s * x * s⁻¹ := hconjDec.symm
        _ = x := hxfix
        _ = ((l : TB) : G) * ((r : TB) : G) := hdec.symm
    have hlsqG : ((l : TB) : G) ^ 2 = 1 := by
      calc
        ((l : TB) : G) ^ 2 = ((l : TB) : G)⁻¹ * ((l : TB) : G) := by
          rw [pow_two, hlEqInv]
        _ = 1 := by simp
    let lT : T := ⟨((l : TB) : G), hlT⟩
    have hlsqT : lT ^ 2 = 1 := by
      apply Subtype.ext
      exact hlsqG
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hTp) lT
    have hd2 : orderOf lT ∣ 2 := orderOf_dvd_of_pow_eq_one hlsqT
    have hd3 : orderOf lT ∣ 3 ^ n := by rw [hn]
    have hgcd : Nat.gcd 2 (3 ^ n) = 1 :=
      (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 2 3)).gcd_eq_one
    have hd1 : orderOf lT ∣ 1 := by
      rw [← hgcd]
      exact Nat.dvd_gcd hd2 hd3
    have hlTone : lT = 1 :=
      orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)
    have hlGone : ((l : TB) : G) = 1 := congrArg Subtype.val hlTone
    have hxEq : x = ((r : TB) : G) := by
      calc
        x = ((l : TB) : G) * ((r : TB) : G) := hdec.symm
        _ = ((r : TB) : G) := by rw [hlGone, one_mul]
    rw [hxEq]
    exact hrB
  · intro b hb
    exact ⟨(le_sup_right : B ≤ T ⊔ B) hb, hcentB hb⟩

private theorem chapter2_claim17_hallWielandt_data
    {G : Type*} [Group G] [Finite G]
    (p : ℕ) (R2 Q H17 : Subgroup G)
    (hp3 : p = 3)
    (hR2s : ∃ R2s : Sylow 3 G, (R2s : Subgroup G) = R2)
    (hH : H17 = Subgroup.normalizer (Q : Set G))
    (hweak : External.WeaklyClosedIn R2 Q)
    (hcomm : IsMulCommutative Q) :
    (External.hallPResidual p H17).map H17.subtype =
        H17 ⊓ External.hallPResidual p G ∧
      letI : (External.hallPResidual p G).Normal :=
        External.hallPResidual_normal p G
      letI : (External.hallPResidual p H17).Normal :=
        External.hallPResidual_normal p H17
      Nonempty ((G ⧸ External.hallPResidual p G) ≃*
        (H17 ⧸ External.hallPResidual p H17)) := by
  subst p
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R2s, hR2s_eq⟩ := hR2s
  have hweak' :
      External.WeaklyClosedIn (R2s : Subgroup G) Q := by
    simpa [hR2s_eq] using hweak
  have hcondition :
      (∀ u z : G, u ∈ (R2s : Subgroup G) → z ∈ Q →
        External.engelSymbol 3 u z = 1) ∨
      (∀ u z : G, u ∈ Q → z ∈ Q →
        External.engelSymbol (3 - 1) u z = 1) ∨
      Q.subgroupOf (R2s : Subgroup G) ≤
        Subgroup.upperCentralSeries (R2s : Subgroup G) (3 - 1) := by
    right
    left
    intro u z hu hz
    have huz : Commute u z :=
      congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := Q)).comm ⟨u, hu⟩ ⟨z, hz⟩)
    change u⁻¹ * z⁻¹ * u * z = 1
    calc
      u⁻¹ * z⁻¹ * u * z = u⁻¹ * (z⁻¹ * u) * z := by simp [mul_assoc]
      _ = u⁻¹ * (u * z⁻¹) * z := by rw [huz.inv_right.eq.symm]
      _ = 1 := by simp
  exact External.hallWielandt_residual_intersection
    3 R2s Q H17 hH hweak' hcondition

private theorem chapter2_claim17_global_index_from_local_hall_data
    {G H A : Type*} [Group G] [Finite G] [Group H] [Group A]
    (p : ℕ) (K : Subgroup G) [K.Normal] (L : Subgroup H) [L.Normal]
    (hquot : Nonempty ((G ⧸ K) ≃* (H ⧸ L)))
    (phi : (H ⧸ L) →* A) (hphi : Function.Surjective phi)
    (hcard : Nat.card A = p) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card (G ⧸ N) = p := by
  classical
  let e : (G ⧸ K) ≃* (H ⧸ L) := Classical.choice hquot
  let psi : G →* A :=
    phi.comp (e.toMonoidHom.comp (QuotientGroup.mk' K))
  have hpsi : Function.Surjective psi :=
    hphi.comp (e.surjective.comp (QuotientGroup.mk'_surjective K))
  refine ⟨psi.ker, inferInstance, ?_⟩
  exact
    (Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective psi hpsi).toEquiv).trans hcard

private theorem chapter2_claim17_hallPResidual_le_of_quotient_card_eq
    {H : Type*} [Group H] (p : ℕ) (M : Subgroup H) [M.Normal]
    (hcard : Nat.card (H ⧸ M) = p) :
    External.hallPResidual p H ≤ M := by
  change Subgroup.closure {x : H | Nat.Coprime p (orderOf x)} ≤ M
  rw [Subgroup.closure_le]
  intro x hx
  change Nat.Coprime p (orderOf x) at hx
  let q : H →* H ⧸ M := QuotientGroup.mk' M
  have hq_dvd_p : orderOf (q x) ∣ p := by
    rw [← hcard]
    exact orderOf_dvd_natCard (q x)
  have hq_dvd_x : orderOf (q x) ∣ orderOf x :=
    orderOf_map_dvd q x
  have hq_dvd_one : orderOf (q x) ∣ 1 := by
    rw [← hx.gcd_eq_one]
    exact Nat.dvd_gcd hq_dvd_p hq_dvd_x
  have hq_order : orderOf (q x) = 1 := Nat.dvd_one.mp hq_dvd_one
  exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hq_order)


private theorem chapter2_claim17_sylow_card_from_factorization
    {G : Type*} [Group G] [Finite G] (S : Sylow 3 G)
    (k u : ℕ) (hk : Nat.card G = 3 ^ k * u) (hu : ¬ 3 ∣ u) :
    Nat.card (S : Subgroup G) = 3 ^ k := by
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    exact hu (dvd_zero 3)
  rw [Sylow.card_eq_multiplicity S, hk,
    Nat.factorization_mul (pow_ne_zero k (by norm_num)) hu0,
    Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_three]
  have hufac : u.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hu
  rw [hufac]
  simp

private theorem chapter2_claim17_closure_involution_card
    {G : Type*} [Group G] (s : G) (hs : IsInvolution s) :
    Nat.card (Subgroup.closure ({s} : Set G)) = 2 := by
  rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers,
    orderOf_eq_prime hs.sq_eq_one hs.ne_one]

private theorem chapter2_claim17_mem_closure_involution_eq_one_or_eq
    {G : Type*} [Group G] [Finite G] (s : G) (hs : IsInvolution s) :
    ∀ x : Subgroup.closure ({s} : Set G), (x : G) = 1 ∨ (x : G) = s := by
  intro x
  by_cases hx1 : (x : G) = 1
  · exact Or.inl hx1
  right
  by_contra hxs
  let C : Subgroup G := Subgroup.closure ({s} : Set G)
  let sC : C := ⟨s, Subgroup.subset_closure (Set.mem_singleton s)⟩
  let f : Fin 3 → C := fun i => match i with
    | 0 => 1
    | 1 => ⟨(x : G), x.2⟩
    | 2 => sC
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, sC, Subtype.ext_iff, hx1, hxs, hs.ne_one, eq_comm] at hij ⊢
  have hle := Nat.card_le_card_of_injective f hf
  have hCcard := chapter2_claim17_closure_involution_card s hs
  simpa [Nat.card_fin, C, hCcard] using hle

private theorem chapter2_claim17_R1_card
    {G : Type*} [Group G] [Finite G]
    (RS R1 : Subgroup G) (s : G)
    (hRScard : Nat.card RS = 81)
    (hs : IsInvolution s)
    (phi : Subgroup.normalizer (RS : Set G) →* Equiv.Perm (Fin 3))
    (hphi : Function.Surjective phi)
    (hker : MonoidHom.ker phi =
      RS.subgroupOf (Subgroup.normalizer (RS : Set G)))
    (hN : Subgroup.normalizer (RS : Set G) =
      R1 ⊔ Subgroup.closure ({s} : Set G))
    (hdisj : Disjoint R1 (Subgroup.closure ({s} : Set G)))
    (hN_le_NR1 : Subgroup.normalizer (RS : Set G) ≤
      Subgroup.normalizer (R1 : Set G)) :
    Nat.card R1 = 243 := by
  let N : Subgroup G := Subgroup.normalizer (RS : Set G)
  let C : Subgroup G := Subgroup.closure ({s} : Set G)
  have hCcard : Nat.card C = 2 := by
    simpa [C] using chapter2_claim17_closure_involution_card s hs
  have hrange : phi.range = ⊤ := MonoidHom.range_eq_top.mpr hphi
  have hkerCard : Nat.card phi.ker = 81 := by
    rw [hker]
    exact (natCard_subgroupOf_eq RS N (by
      dsimp [N]
      exact Subgroup.le_normalizer)).trans hRScard
  have hrangeCard : Nat.card phi.range = 6 := by
    rw [hrange]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hNcard : Nat.card N = 486 := by
    calc
      Nat.card N = Nat.card (N ⧸ phi.ker) * Nat.card phi.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup phi.ker
      _ = Nat.card phi.range * Nat.card phi.ker := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange phi).toEquiv]
      _ = 486 := by rw [hrangeCard, hkerCard]
  have hC_norm_R1 : C ≤ Subgroup.normalizer (R1 : Set G) := by
    change Subgroup.closure ({s} : Set G) ≤ Subgroup.normalizer (R1 : Set G)
    calc
      Subgroup.closure ({s} : Set G) ≤ R1 ⊔ Subgroup.closure ({s} : Set G) := le_sup_right
      _ = Subgroup.normalizer (RS : Set G) := hN.symm
      _ ≤ Subgroup.normalizer (R1 : Set G) := hN_le_NR1
  have hsupCard : Nat.card (R1 ⊔ C : Subgroup G) = Nat.card R1 * 2 := by
    rw [chapter2_claim17_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
      R1 C hC_norm_R1 hdisj, hCcard]
  rw [← hN] at hsupCard
  change Nat.card N = Nat.card R1 * 2 at hsupCard
  rw [hNcard] at hsupCard
  omega

private theorem chapter2_claim17_perm_fin_three_cube_of_pow_243
    (a : Equiv.Perm (Fin 3)) (ha : a ^ 243 = 1) : a ^ 3 = 1 := by
  have hd6 : orderOf a ∣ 6 := by
    have := orderOf_dvd_natCard a
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at this ⊢
    exact this
  have hd243 : orderOf a ∣ 243 := orderOf_dvd_of_pow_eq_one ha
  have hd3 : orderOf a ∣ 3 := by
    have := Nat.dvd_gcd hd6 hd243
    norm_num at this ⊢
    exact this
  exact orderOf_dvd_iff_pow_eq_one.mp hd3

private theorem chapter2_claim17_perm_fin_three_eq_one_of_cube_commute_involution
    (a b : Equiv.Perm (Fin 3))
    (ha : a ^ 3 = 1) (hb : b ^ 2 = 1) (hbne : b ≠ 1)
    (hab : a * b = b * a) : a = 1 := by
  by_contra hane
  let A : Subgroup (Equiv.Perm (Fin 3)) := Subgroup.zpowers a
  let B : Subgroup (Equiv.Perm (Fin 3)) := Subgroup.zpowers b
  have haord : orderOf a = 3 := orderOf_eq_prime ha hane
  have hbord : orderOf b = 2 := orderOf_eq_prime hb hbne
  have hAcard : Nat.card A = 3 := by dsimp [A]; rw [Nat.card_zpowers, haord]
  have hBcard : Nat.card B = 2 := by dsimp [B]; rw [Nat.card_zpowers, hbord]
  have hdisj : Disjoint A B := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hAcard, hBcard]
    norm_num
  have habComm : Commute a b := hab
  have hB_le_CA : B ≤ Subgroup.centralizer (A : Set (Equiv.Perm (Fin 3))) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hz with ⟨n, rfl⟩
    rcases hw with ⟨m, rfl⟩
    exact (habComm.zpow_zpow m n).eq
  have hA_le_CB : A ≤ Subgroup.centralizer (B : Set (Equiv.Perm (Fin 3))) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hz with ⟨m, rfl⟩
    rcases hw with ⟨n, rfl⟩
    exact (habComm.zpow_zpow m n).symm.eq
  have hB_le_NA : B ≤ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 3))) :=
    hB_le_CA.trans (chapter2_claim17_centralizer_le_normalizer A)
  have hsupCard : Nat.card (A ⊔ B : Subgroup (Equiv.Perm (Fin 3))) = 6 := by
    rw [chapter2_claim17_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
      A B hB_le_NA hdisj, hAcard, hBcard]
  have htopCard : Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 3))) = 6 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hsupTop : A ⊔ B = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [hsupCard, htopCard]
  have hA_le_CA : A ≤ Subgroup.centralizer (A : Set (Equiv.Perm (Fin 3))) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hB_le_CB : B ≤ Subgroup.centralizer (B : Set (Equiv.Perm (Fin 3))) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hsup_le_Csup : A ⊔ B ≤
      Subgroup.centralizer ((A ⊔ B : Subgroup (Equiv.Perm (Fin 3))) : Set _) := by
    apply sup_le
    · exact Subgroup.le_centralizer_sup_of_le_centralizers hA_le_CA hA_le_CB
    · exact Subgroup.le_centralizer_sup_of_le_centralizers hB_le_CA hB_le_CB
  have hcommAmb : ∀ x y : Equiv.Perm (Fin 3), x * y = y * x := by
    intro x y
    have hx : x ∈ A ⊔ B := by rw [hsupTop]; trivial
    have hy : y ∈ A ⊔ B := by rw [hsupTop]; trivial
    exact (Subgroup.mem_centralizer_iff.mp (hsup_le_Csup hx) y hy).symm
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have hne : (τ * σ) 0 ≠ (σ * τ) 0 := by decide
  exact hne (congrArg (fun f : Equiv.Perm (Fin 3) => f 0) (hcommAmb τ σ))

private theorem chapter2_claim17_normal_index_from_hallWielandt_cases_source_interface
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R T R1 R2 L : Subgroup G) (t s : G) (p : ℕ)
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
    (h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
          Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
            (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              Z1 ⊔ P ∧
              R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                R ⊔ Sigma ≤ R1 ∧
                  R2 = Subgroup.centralizer (Z1 : Set G) ∧
                    R1 ≤ R2)
    (h15 : L ≤ R1 ∧
      (Nat.card L = 9 ∧ IsCyclic L) ∧
        (∀ x : G, x ∈ L → rightConjugateElem x s = x⁻¹) ∧
          V ≤ Subgroup.normalizer (L : Set G) ∧
            W ≤ Subgroup.centralizer (L : Set G) ∧
              ¬ P ≤ Subgroup.centralizer (L : Set G) ∧
                L ⊔ V ≤ R2 ∧
                  Nat.card R2 = 3 * Nat.card ((L ⊔ V : Subgroup G)) ∧
                  (L ⊔ V) ⊓ Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) =
                    Z1 ⊔ Sigma ∧
                    ∀ x : G, x ∈ L ⊔ V →
                      (x ^ 3 = 1 ↔ x ∈ Z1 ⊔ Sigma ⊔ P))
    (h16 : Z1 ⊔ P ⊔ Sigma ≤ R1 ∧
      (∀ x y : G, x ∈ Z1 ⊔ P ⊔ Sigma → y ∈ R1 →
        x * y * x⁻¹ * y⁻¹ ∈
          R1 ⊓ Subgroup.centralizer (R1 : Set G)) ∧
      (∀ X : Subgroup G,
        X ≤ Z1 ⊔ P ⊔ Sigma →
          Nat.card X = 3 →
            (∀ x : G, x ∈ X → x ≠ 1 → IsStronglyReal x) →
              X = Z1) ∧
        Subgroup.normalizer ((Z1 ⊔ P ⊔ Sigma : Subgroup G) : Set G) =
          Subgroup.normalizer (Z1 : Set G) ∧
          Subgroup.normalizer (Z1 : Set G) = R2 ⊔ Subgroup.closure ({s} : Set G))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hp3 : p = 3)
    (hSigmaCard : Nat.card Sigma = 3)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hst3 : orderOf (s * t) = 3)
    (hR2p : IsPGroup 3 R2)
    (hR2s : ∃ R2s : Sylow 3 G, (R2s : Subgroup G) = R2)
    (hRT : R = T ⊔ P)
    (hTdisjP : Disjoint T P)
    (hTleCP : T ≤ Subgroup.centralizer (P : Set G))
    (hSigmaNormT : Sigma ≤ Subgroup.normalizer (T : Set G))
    (hTinverted : ∀ x : G, x ∈ T → rightConjugateElem x s = x⁻¹)
    (hRdisjSigma : Disjoint R Sigma)
    (hRScard : Nat.card (R ⊔ Sigma : Subgroup G) = 81)
    (hWdisjP : Disjoint W P)
    (hWcases : Nat.card W = 3 ∨ Nat.card W = 9)
    (hfactor : ∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
      Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u)
    (hR1p : IsPGroup 3 R1)
    (hphiPack : ∃ phi : (Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G)) →*
        Equiv.Perm (Fin 3),
      Function.Surjective phi ∧
        MonoidHom.ker phi =
          (R ⊔ Sigma).subgroupOf
            (Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G)))
    (hNRS : Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) =
      R1 ⊔ Subgroup.closure ({s} : Set G))
    (hdisjR1C : Disjoint R1 (Subgroup.closure ({s} : Set G)))
    (hNleNR1 : Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ≤
      Subgroup.normalizer (R1 : Set G))
    (hcenterR1 : R1 ⊓ Subgroup.centralizer (R1 : Set G) = Z1)
    (hindex : (R1.subgroupOf R2).index = 1 ∨
      (R1.subgroupOf R2).index = 3)
    (hmap :
      let H17 : Subgroup G := R2 ⊔ Subgroup.closure ({s} : Set G)
      (External.hallPResidual p H17).map H17.subtype = H17 ⊓ External.hallPResidual p G)
    (hquot :
      let H17 : Subgroup G := R2 ⊔ Subgroup.closure ({s} : Set G)
      letI : (External.hallPResidual p G).Normal := External.hallPResidual_normal p G
      letI : (External.hallPResidual p H17).Normal := External.hallPResidual_normal p H17
      Nonempty ((G ⧸ External.hallPResidual p G) ≃*
        (↥H17 ⧸ External.hallPResidual p H17))) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card (G ⧸ N) = p := by
  let H17 : Subgroup G := R2 ⊔ Subgroup.closure ({s} : Set G)
  have hlocal_index :
      ∃ M : Subgroup H17, M.Normal ∧ Nat.card (H17 ⧸ M) = p := by
    classical
    subst p
    let C : Subgroup G := Subgroup.closure ({s} : Set G)
    let RS : Subgroup G := R ⊔ Sigma
    let B0 : Subgroup G := P ⊔ Sigma
    have hsI : IsInvolution s := hch.section3.s_involution
    have hCcard : Nat.card C = 2 := by
      calc
        Nat.card C = Nat.card (Subgroup.closure ({s} : Set G)) := by simp [C]
        _ = 2 := chapter2_claim17_closure_involution_card s hsI
    have hCp : IsPGroup 2 C := IsPGroup.of_card (n := 1) (by rw [hCcard]; norm_num)
    rcases hphiPack with ⟨phi, hphiSurj, hphiKer⟩
    have hR1card : Nat.card R1 = 243 :=
      chapter2_claim17_R1_card RS R1 s (by simpa [RS] using hRScard) hsI phi
        hphiSurj (by simpa [RS] using hphiKer) (by simpa [RS] using hNRS)
        hdisjR1C (by simpa [RS] using hNleNR1)
    obtain ⟨R2Sylow, hR2Sylow⟩ := hR2s
    obtain ⟨k, u, hku, hGcard, hu⟩ := hfactor
    have hR2card : Nat.card R2 = 3 ^ 4 * Nat.card W := by
      calc
        Nat.card R2 = Nat.card (R2Sylow : Subgroup G) := by rw [hR2Sylow]
        _ = 3 ^ k := chapter2_claim17_sylow_card_from_factorization R2Sylow k u
          (by rw [← hku]; exact hGcard) hu
        _ = 3 ^ 4 * Nat.card W := hku.symm
    have hSigma_le_W : Sigma ≤ W := by rw [hSigma]; exact inf_le_left
    have hSigma_le_V : Sigma ≤ V := hSigma_le_W.trans hch.section3.section2.W_le_V
    have hPcard : Nat.card P = 3 := by simpa using hch.B1.P_card
    have hP_not_le_Sigma : ¬ P ≤ Sigma := by
      intro hle
      have hPbot : P ≤ (⊥ : Subgroup G) := by
        intro x hx
        exact hWdisjP.le_bot ⟨hSigma_le_W (hle hx), hx⟩
      have hPeq : P = ⊥ := le_antisymm hPbot bot_le
      rw [hPeq] at hPcard
      norm_num at hPcard
    have hPdisjSigma : Disjoint P Sigma :=
      chapter2_claim17_disjoint_of_card_three_of_not_le P Sigma hPcard hP_not_le_Sigma
    have hSigma_le_CP : Sigma ≤ Subgroup.centralizer (P : Set G) := by
      rw [hSigma]
      exact inf_le_right
    have hB0card : Nat.card B0 = 9 := by
      dsimp [B0]
      rw [chapter2_claim17_natCard_sup_eq_mul_of_disjoint_of_le_normalizer P Sigma
        (hSigma_le_CP.trans (chapter2_claim17_centralizer_le_normalizer P))
        hPdisjSigma, hPcard, hSigmaCard]
    have hB0_le_V : B0 ≤ V := sup_le hch.B1.P_le_V hSigma_le_V
    have hV_eq : V = D ⊓ Subgroup.centralizer ({s} : Set G) := by
      calc
        V = peterfalviV D t := hch.section3.section2.V_eq
        _ = D ⊓ Subgroup.centralizer ({s} : Set G) :=
          (proposition_5 H D Q t s hch.section3.section2.hA.A1
            hch.section3.s_mem_H hsI hch.section3.s_conjugate).1
    have hsC_V : s ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hvCs : v ∈ Subgroup.centralizer ({s} : Set G) := by
        rw [hV_eq] at hv
        exact hv.2
      exact Subgroup.mem_centralizer_singleton_iff.mp hvCs
    have hC_norm_R1 : C ≤ Subgroup.normalizer (R1 : Set G) := by
      change Subgroup.closure ({s} : Set G) ≤ Subgroup.normalizer (R1 : Set G)
      calc
        Subgroup.closure ({s} : Set G) ≤ R1 ⊔ Subgroup.closure ({s} : Set G) := le_sup_right
        _ = Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) := hNRS.symm
        _ ≤ Subgroup.normalizer (R1 : Set G) := hNleNR1
    rcases hWcases with hW3 | hW9
    · have hR2card3 : Nat.card R2 = 243 := by
        rw [hR2card, hW3]
        norm_num
      have hR1eqR2 : R1 = R2 :=
        Subgroup.eq_of_le_of_card_ge h14.2.2.2.2.2.2.2.2 (by rw [hR1card, hR2card3])
      have hZ1card : Nat.card Z1 = 3 := by
        rw [hZ1, Nat.card_zpowers, hst3]
      have hZstrong := chapter2_claim17_Z1_stronglyReal Z1 s t hZ1 hst3
        hsI hch.section3.section2.hA.A1.involution_t
      have hB0_le_LV : B0 ≤ L ⊔ V := hB0_le_V.trans le_sup_right
      have hB0_le_A : B0 ≤ Z1 ⊔ P ⊔ Sigma := by
        dsimp [B0]
        exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
      have hB0pow : ∀ b : G, b ∈ B0 → b ^ 3 = 1 := by
        intro b hb
        apply (h15.2.2.2.2.2.2.2.2.2 b (hB0_le_LV hb)).mpr
        rw [show Z1 ⊔ Sigma ⊔ P = Z1 ⊔ P ⊔ Sigma by ac_rfl]
        exact hB0_le_A hb
      have hZ1disjB0 : Disjoint Z1 B0 := by
        rw [disjoint_iff_inf_le]
        intro z hz
        by_contra hzne
        exact
          (chapter2_claim17_not_stronglyReal_of_mem_peterfalviV_order_three
            H D Q K V W Q0 S Q1 t s z hch.section3
            (hB0_le_V hz.2) hzne (hB0pow z hz.2))
          (hZstrong z hz.1 hzne)
      have hZ1_le_R1 : Z1 ≤ R1 :=
        (le_sup_left.trans le_sup_left).trans h16.1
      let Zsub : Subgroup R1 := Z1.subgroupOf R1
      have hZsub_center : Zsub ≤ Subgroup.center R1 := by
        intro z hz
        rw [Subgroup.mem_center_iff]
        intro r
        apply Subtype.ext
        have hzCenter : (z : G) ∈ R1 ⊓ Subgroup.centralizer (R1 : Set G) := by
          rw [hcenterR1]
          exact hz
        exact (Subgroup.mem_centralizer_iff.mp hzCenter.2) (r : G) r.2
      letI : Zsub.Normal :=
        ⟨fun a ha b => by
          have hcent := hZsub_center ha
          simpa [mul_assoc, Subgroup.mem_center_iff.mp hcent b, hcent] using ha⟩
      let qZ : R1 →* R1 ⧸ Zsub := QuotientGroup.mk' Zsub
      let Bsub : Subgroup R1 := B0.subgroupOf R1
      have hB0_le_R1 : B0 ≤ R1 := hB0_le_A.trans h16.1
      have hBsubCard : Nat.card Bsub = 9 := by
        exact (natCard_subgroupOf_eq B0 R1 hB0_le_R1).trans hB0card
      let fB : Bsub →* R1 ⧸ Zsub := qZ.comp Bsub.subtype
      have hfB_inj : Function.Injective fB := by
        intro x y hxy
        apply Subtype.ext
        have hdivZ : (x : R1) / (y : R1) ∈ Zsub :=
          (QuotientGroup.eq_iff_div_mem (N := Zsub)).mp hxy
        have hdivB : ((x : R1) / (y : R1) : R1) ∈ Bsub := Bsub.div_mem x.2 y.2
        have hdivAmb : (((x : R1) / (y : R1) : R1) : G) ∈ Z1 ⊓ B0 :=
          ⟨hdivZ, hdivB⟩
        have hdivOne : (((x : R1) / (y : R1) : R1) : G) = 1 := by
          have := hZ1disjB0.le_bot hdivAmb
          simpa using this
        apply Subtype.ext
        simpa [div_eq_one] using hdivOne
      let Bbar : Subgroup (R1 ⧸ Zsub) := fB.range
      have hBbarCard : Nat.card Bbar = 9 := by
        calc
          Nat.card Bbar = Nat.card Bsub := by
            simpa [Bbar, fB, MonoidHom.range_eq_map] using
              Subgroup.card_map_of_injective (K := (⊤ : Subgroup Bsub))
                (f := fB) hfB_inj
          _ = 9 := hBsubCard
      have hBbar_le_center : Bbar ≤ Subgroup.center (R1 ⧸ Zsub) := by
        rintro _ ⟨b, -, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro rbar
        obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective Zsub rbar
        symm
        change qZ (b : R1) * qZ r = qZ r * qZ (b : R1)
        rw [← commutatorElement_eq_one_iff_mul_comm,
          ← map_commutatorElement]
        apply (QuotientGroup.eq_one_iff (N := Zsub)
          (x := ⁅(b : R1), r⁆)).2
        have hbA : (b : G) ∈ Z1 ⊔ P ⊔ Sigma := hB0_le_A b.2
        have hcommMem := h16.2.1 (b : G) (r : G) hbA r.2
        rw [hcenterR1] at hcommMem
        exact hcommMem
      have hZsubCard : Nat.card Zsub = 3 :=
        (natCard_subgroupOf_eq Z1 R1 hZ1_le_R1).trans hZ1card
      have hQcard : Nat.card (R1 ⧸ Zsub) = 81 := by
        have hmul := Zsub.index_mul_card
        rw [Subgroup.index_eq_card Zsub, hZsubCard, hR1card] at hmul
        omega
      have hcenterCardGe : 9 ≤ Nat.card (Subgroup.center (R1 ⧸ Zsub)) := by
        rw [← hBbarCard]
        exact Subgroup.card_le_of_le hBbar_le_center
      have hcenterIndexLe : (Subgroup.center (R1 ⧸ Zsub)).index ≤ 9 := by
        have hmul := (Subgroup.center (R1 ⧸ Zsub)).index_mul_card
        rw [hQcard] at hmul
        have hle := Nat.mul_le_mul_left
          (Subgroup.center (R1 ⧸ Zsub)).index hcenterCardGe
        rw [hmul] at hle
        omega
      have hQp : IsPGroup 3 (R1 ⧸ Zsub) := hR1p.to_quotient Zsub
      have hDqCard : Nat.card (derivedSubgroup (R1 ⧸ Zsub)) ≤ 3 := by
        have htemp := chapter2_claim17_commutator_card_le_three_of_center_index_le_nine
          hQp hcenterIndexLe
        have h_eq : derivedSubgroup (R1 ⧸ Zsub) = commutator (R1 ⧸ Zsub) := by
          dsimp [derivedSubgroup]
        simpa [h_eq] using htemp
      have hqZtop : (⊤ : Subgroup R1).map qZ = ⊤ :=
        Subgroup.map_top_of_surjective qZ (QuotientGroup.mk'_surjective Zsub)
      have hmapDerived : (derivedSubgroup R1).map qZ =
          derivedSubgroup (R1 ⧸ Zsub) := by
        have h_eq1 : derivedSubgroup R1 = commutator R1 := by
          dsimp [derivedSubgroup]
        have h_eq2 : derivedSubgroup (R1 ⧸ Zsub) = commutator (R1 ⧸ Zsub) := by
          dsimp [derivedSubgroup]
        have h_comm_map : (commutator R1).map qZ = commutator (R1 ⧸ Zsub) := by
          calc
            Subgroup.map qZ (commutator R1) = Subgroup.map qZ (⁅(⊤ : Subgroup R1), (⊤ : Subgroup R1)⁆) := rfl
            _ = ⁅Subgroup.map qZ (⊤ : Subgroup R1), Subgroup.map qZ (⊤ : Subgroup R1)⁆ := by
              rw [Subgroup.map_commutator]
            _ = ⁅⊤, ⊤⁆ := by rw [hqZtop]
            _ = commutator (R1 ⧸ Zsub) := rfl
        calc
          (derivedSubgroup R1).map qZ = (commutator R1).map qZ := by rw [h_eq1]
          _ = commutator (R1 ⧸ Zsub) := h_comm_map
          _ = derivedSubgroup (R1 ⧸ Zsub) := by rw [h_eq2]
      have hB0notDerived : ¬ Bsub ≤ derivedSubgroup R1 := by
        intro hle
        have hmapLe : Bbar ≤ (derivedSubgroup R1).map qZ := by
          rintro _ ⟨b, -, rfl⟩
          exact ⟨b, hle b.2, rfl⟩
        have hcardLe : 9 ≤ Nat.card (derivedSubgroup (R1 ⧸ Zsub)) := by
          rw [← hBbarCard, ← hmapDerived]
          exact Subgroup.card_le_of_le hmapLe
        omega
      obtain ⟨b, hbB, hbD⟩ := Set.not_subset.mp hB0notDerived
      let D1 : Subgroup R1 := derivedSubgroup R1
      letI : D1.Normal := by dsimp [D1]; infer_instance
      letI : D1.Characteristic := by dsimp [D1]; infer_instance
      let qD : R1 →* R1 ⧸ D1 := QuotientGroup.mk' D1
      let bAb : R1 ⧸ D1 := qD b
      have hbAbNe : bAb ≠ 1 := by
        intro hb1
        apply hbD
        exact (QuotientGroup.eq_one_iff (N := D1) (x := b)).mp hb1
      have hsC : s ∈ C := by
        dsimp [C]
        exact Subgroup.subset_closure (Set.mem_singleton s)
      let sNorm : Subgroup.normalizer (R1 : Set G) := ⟨s, hC_norm_R1 hsC⟩
      let phiR : MulAut R1 := R1.normalizerMonoidHom sNorm
      have hphiR2 : Function.Involutive phiR := by
        intro r
        apply Subtype.ext
        simp [phiR, sNorm, hsI.inv_eq_self, mul_assoc]
        have hs2 : s * s = 1 := by simpa [pow_two] using hsI.sq_eq_one
        rw [hs2, mul_one, ← mul_assoc, hs2, one_mul]
      have hDinv : ∀ r : R1, r ∈ D1 ↔ phiR r ∈ D1 := by
        exact External.hkt_characteristic_subgroup_invariant phiR D1
      let phiAb : MulAut (R1 ⧸ D1) :=
        External.invariantQuotientAut phiR D1 hDinv
      have hphiAb2 : Function.Involutive phiAb := by
        intro x
        obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective D1 x
        simp only [phiAb, External.invariantQuotientAut_mk']
        rw [hphiR2 r]
      have hsb : s * (b : G) = (b : G) * s := by
        exact ((Subgroup.mem_centralizer_iff.mp hsC_V) (b : G) (hB0_le_V hbB)).symm
      have hphiRb : phiR b = b := by
        apply Subtype.ext
        simp [phiR, sNorm, hsI.inv_eq_self, hsb, mul_assoc]
        simpa [pow_two] using hsI.sq_eq_one
      have hphiAbB : phiAb bAb = bAb := by
        change phiAb (qD b) = qD b
        rw [External.invariantQuotientAut_mk', hphiRb]
      have hAbcomm : IsMulCommutative (R1 ⧸ D1) :=
        (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := D1)).mpr
          (by exact le_rfl)
      letI : IsMulCommutative (R1 ⧸ D1) := hAbcomm
      letI : CommGroup (R1 ⧸ D1) := IsMulCommutative.instCommGroup
      have hAbp : IsPGroup 3 (R1 ⧸ D1) := hR1p.to_quotient D1
      let plus : (R1 ⧸ D1) →* (R1 ⧸ D1) :=
        phiAb.toMonoidHom * MonoidHom.id (R1 ⧸ D1)
      have hplusInv (x : R1 ⧸ D1) : plus (phiAb x) = plus x := by
        change phiAb (phiAb x) * phiAb x = phiAb x * x
        rw [hphiAb2 x]
        exact mul_comm _ _
      have hplusB : plus bAb = bAb ^ 2 := by
        change phiAb bAb * bAb = bAb ^ 2
        rw [hphiAbB]
        simp [pow_two]
      have hplusBne : plus bAb ≠ 1 := by
        intro hplus1
        have hb2 : bAb ^ 2 = 1 := by rw [← hplusB]; exact hplus1
        have hd2 : orderOf bAb ∣ 2 := orderOf_dvd_of_pow_eq_one hb2
        obtain ⟨n, hAbcard⟩ := hAbp.exists_card_eq
        have hd3 : orderOf bAb ∣ 3 ^ n := by
          rw [← hAbcard]
          exact orderOf_dvd_natCard bAb
        have hgcd : Nat.gcd 2 (3 ^ n) = 1 :=
          (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 2 3)).gcd_eq_one
        have hd1 : orderOf bAb ∣ 1 := by
          rw [← hgcd]
          exact Nat.dvd_gcd hd2 hd3
        exact hbAbNe (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1))
      let Kplus : Subgroup (R1 ⧸ D1) := plus.range
      let kb : Kplus := ⟨plus bAb, ⟨bAb, rfl⟩⟩
      have hkbne : kb ≠ 1 := by
        intro h
        apply hplusBne
        exact congrArg Subtype.val h
      letI : Nontrivial Kplus := nontrivial_of_ne kb 1 hkbne
      have hKp : IsPGroup 3 Kplus := hAbp.to_subgroup Kplus
      letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      letI : Fact (IsPGroup 3 Kplus) := ⟨hKp⟩
      obtain ⟨n, hKcard⟩ := hKp.exists_card_eq
      have hn0 : n ≠ 0 := by
        intro hn
        subst n
        have hcard1 : Nat.card Kplus = 1 := by simpa using hKcard
        have hsub : Subsingleton Kplus := (Nat.card_eq_one_iff_unique.mp hcard1).1
        exact hkbne (Subsingleton.elim kb 1)
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hpowLe : 3 ^ m ≤ Nat.card Kplus := by
        rw [hKcard]
        exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m)
      obtain ⟨Mplus, hMplusCard⟩ :=
        Sylow.exists_subgroup_card_pow_prime_of_le_card
          (G := Kplus) (p := 3) (n := m) (hp := Nat.prime_three) hKp hpowLe
      letI : Mplus.Normal := by infer_instance
      have htargetCard : Nat.card (Kplus ⧸ Mplus) = 3 := by
        have hmul := Mplus.index_mul_card
        rw [Subgroup.index_eq_card Mplus, hMplusCard, hKcard, pow_succ] at hmul
        apply Nat.mul_right_cancel (show 0 < 3 ^ m by positivity)
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
      let plusR : (R1 ⧸ D1) →* Kplus := plus.rangeRestrict
      have hplusR : Function.Surjective plusR := by
        intro y
        rcases y.2 with ⟨x, hx⟩
        exact ⟨x, Subtype.ext hx⟩
      let chi : (R1 ⧸ D1) →* (Kplus ⧸ Mplus) :=
        (QuotientGroup.mk' Mplus).comp plusR
      have hchi : Function.Surjective chi :=
        (QuotientGroup.mk'_surjective Mplus).comp hplusR
      have hchiInv (x : R1 ⧸ D1) : chi (phiAb x) = chi x := by
        change QuotientGroup.mk' Mplus (plusR (phiAb x)) =
          QuotientGroup.mk' Mplus (plusR x)
        apply congrArg (QuotientGroup.mk' Mplus)
        exact Subtype.ext (hplusInv x)
      let psi : R1 →* (Kplus ⧸ Mplus) := chi.comp qD
      have hpsi : Function.Surjective psi :=
        hchi.comp (QuotientGroup.mk'_surjective D1)
      have hpsiPhi (r : R1) : psi (phiR r) = psi r := by
        change chi (qD (phiR r)) = chi (qD r)
        rw [show qD (phiR r) = phiAb (qD r) by
          exact (External.invariantQuotientAut_mk' phiR D1 hDinv r).symm]
        exact hchiInv (qD r)
      have hpsiS (r : R1) :
          psi ⟨s * (r : G) * s⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hC_norm_R1 hsC) (r : G)).1 r.2⟩ = psi r := by
        have hphiR_apply : (phiR r : G) = s * (r : G) * s⁻¹ := by
          calc
            (phiR r : G) = ((R1.normalizerMonoidHom sNorm) r : G) := rfl
            _ = (sNorm : G) * (r : G) * (sNorm : G)⁻¹ :=
              Subgroup.normalizerMonoidHom_apply_apply_coe R1 sNorm r
            _ = s * (r : G) * s⁻¹ := by simp [sNorm]
        have hphiR_subtype : phiR r = ⟨s * (r : G) * s⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hC_norm_R1 hsC) (r : G)).1 r.2⟩ :=
          Subtype.ext hphiR_apply
        simpa [hphiR_subtype] using hpsiPhi r
      have hpsiC : ∀ v : C, ∀ r : R1,
          psi ⟨Section2.conjBy (v : G) (r : G),
            (Subgroup.mem_normalizer_iff.mp (hC_norm_R1 v.2) (r : G)).1 r.2⟩ = psi r := by
        intro v r
        rcases chapter2_claim17_mem_closure_involution_eq_one_or_eq s hsI
          ⟨(v : G), by simpa [C] using v.2⟩ with hv | hv
        · have hvG : (v : G) = 1 := hv
          apply congrArg psi
          apply Subtype.ext
          simp [Section2.conjBy, hvG]
        · have hvG : (v : G) = s := hv
          have h_goal := hpsiS r
          simp [Section2.conjBy, hvG] at h_goal ⊢
          exact h_goal
      have hloc := chapter2_claim17_local_index_of_invariant_character
        R1 C hC_norm_R1 hdisjR1C psi hpsi hpsiC
      change ∃ M : Subgroup ↥(R2 ⊔ C), M.Normal ∧ Nat.card (↥(R2 ⊔ C) ⧸ M) = 3
      rw [← hR1eqR2]
      simpa [C, htargetCard] using hloc
    · have hR2card9 : Nat.card R2 = 729 := by
        rw [hR2card, hW9]
        norm_num
      have hR1_le_R2 : R1 ≤ R2 := h14.2.2.2.2.2.2.2.2
      have hindex3 : (R1.subgroupOf R2).index = 3 := by
        exact hindex.resolve_left (by
          intro hindex1
          have hmul := (R1.subgroupOf R2).index_mul_card
          rw [hindex1, natCard_subgroupOf_eq R1 R2 hR1_le_R2,
            hR1card, hR2card9] at hmul
          omega)
      letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hR1normal : (R1.subgroupOf R2).Normal :=
        chapter2_claim17_normal_of_index_eq_prime_of_isPGroup hR2p
          (R1.subgroupOf R2) hindex3
      have hP_le_CT : P ≤ Subgroup.centralizer (T : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact ((Subgroup.mem_centralizer_iff.mp (hTleCP hy)) x hx).symm
      have hB0_norm_T : B0 ≤ Subgroup.normalizer (T : Set G) := by
        apply sup_le
        · exact hP_le_CT.trans (chapter2_claim17_centralizer_le_normalizer T)
        · exact hSigmaNormT
      have hT_le_R : T ≤ R := by rw [hRT]; exact le_sup_left
      have hP_le_R : P ≤ R := by rw [hRT]; exact le_sup_right
      have hSigma_norm_P : Sigma ≤ Subgroup.normalizer (P : Set G) :=
        hSigma_le_CP.trans (chapter2_claim17_centralizer_le_normalizer P)
      have hTdisjB0 : Disjoint T B0 := by
        apply disjoint_iff.mpr
        apply le_antisymm
        · intro x hx
          have hmulset := Subgroup.coe_mul_of_right_le_normalizer_left
            P Sigma hSigma_norm_P
          have hxProd : x ∈ (P : Set G) * (Sigma : Set G) := by
            rw [← hmulset]
            exact hx.2
          rcases hxProd with ⟨p0, hp0, z0, hz0, hprod⟩
          change p0 * z0 = x at hprod
          have hzR : z0 ∈ R := by
            have htmp := R.mul_mem (R.inv_mem (hP_le_R hp0)) (hT_le_R hx.1)
            have hzEq : z0 = p0⁻¹ * x := by
              rw [← hprod]
              simp
            rw [hzEq]
            exact htmp
          have hzBot : z0 ∈ (⊥ : Subgroup G) :=
            hRdisjSigma.le_bot ⟨hzR, hz0⟩
          have hzOne : z0 = 1 := by simpa using hzBot
          have hxP : x ∈ P := by
            have hxEq : x = p0 := by rw [← hprod, hzOne, mul_one]
            rw [hxEq]
            exact hp0
          exact hTdisjP.le_bot ⟨hx.1, hxP⟩
        · exact bot_le
      have hT_le_R1 : T ≤ R1 :=
        hT_le_R.trans (le_sup_left.trans h14.2.2.2.2.2.2.1)
      have hTp : IsPGroup 3 T := by
        have hsub := hR1p.to_subgroup (T.subgroupOf R1)
        exact hsub.of_equiv (Subgroup.subgroupOfEquivOfLe hT_le_R1)
      have hB0_cent_s : B0 ≤ Subgroup.centralizer ({s} : Set G) := by
        intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hsC_V) b (hB0_le_V hb)
      have hTB_eq_RS : T ⊔ B0 = RS := by
        dsimp [B0, RS]
        rw [hRT]
        ac_rfl
      have hRSfixed :
          RS ⊓ Subgroup.centralizer ({s} : Set G) = B0 := by
        rw [← hTB_eq_RS]
        exact chapter2_claim17_fixed_subgroup_of_inverted_semidirect
          T B0 s hsI hB0_norm_T hTdisjB0 hTp hTinverted hB0_cent_s
      have hsNRS : s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) :=
        h14.2.2.1
      have hsC : s ∈ C := by
        dsimp [C]
        exact Subgroup.subset_closure (Set.mem_singleton s)
      have hR1fixed_le_RS :
          R1 ⊓ Subgroup.centralizer ({s} : Set G) ≤ RS := by
        intro r hr
        let rN : Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) :=
          ⟨r, h14.2.2.2.2.2.1 hr.1⟩
        let sN : Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) :=
          ⟨s, hsNRS⟩
        let rR1 : R1 := ⟨r, hr.1⟩
        have hrpowR1 : rR1 ^ 243 = 1 := by
          rw [← hR1card]
          exact pow_card_eq_one'
        have hrpowN : rN ^ 243 = 1 := by
          apply Subtype.ext
          change r ^ 243 = 1
          exact congrArg Subtype.val hrpowR1
        have hphiRpow : phi rN ^ 243 = 1 := by
          rw [← map_pow, hrpowN, map_one]
        have hphiR3 : phi rN ^ 3 = 1 :=
          chapter2_claim17_perm_fin_three_cube_of_pow_243 (phi rN) hphiRpow
        have hsNpow : sN ^ 2 = 1 := by
          apply Subtype.ext
          change s ^ 2 = 1
          exact hsI.sq_eq_one
        have hphiS2 : phi sN ^ 2 = 1 := by
          rw [← map_pow, hsNpow, map_one]
        have hphiSne : phi sN ≠ 1 := by
          intro hsphi
          have hsKer : sN ∈ MonoidHom.ker phi := hsphi
          rw [hphiKer] at hsKer
          change s ∈ R ⊔ Sigma at hsKer
          have hsR1 : s ∈ R1 := h14.2.2.2.2.2.2.1 hsKer
          have hsBot : s ∈ (⊥ : Subgroup G) :=
            hdisjR1C.le_bot ⟨hsR1, hsC⟩
          exact hsI.ne_one (by simpa using hsBot)
        have hrs : r * s = s * r :=
          Subgroup.mem_centralizer_singleton_iff.mp hr.2
        have hrsN : rN * sN = sN * rN := by
          apply Subtype.ext
          exact hrs
        have hphiComm : phi rN * phi sN = phi sN * phi rN := by
          simpa only [map_mul] using congrArg phi hrsN
        have hphiRone : phi rN = 1 :=
          chapter2_claim17_perm_fin_three_eq_one_of_cube_commute_involution
            (phi rN) (phi sN) hphiR3 hphiS2 hphiSne hphiComm
        have hrKer : rN ∈ MonoidHom.ker phi := hphiRone
        rw [hphiKer] at hrKer
        change r ∈ R ⊔ Sigma at hrKer
        simpa [RS] using hrKer
      have hB0_le_R1 : B0 ≤ R1 := by
        apply (show B0 ≤ Z1 ⊔ P ⊔ Sigma by
          apply sup_le
          · exact (le_sup_right : P ≤ Z1 ⊔ P).trans le_sup_left
          · exact le_sup_right).trans h16.1
      have hR1fixed :
          R1 ⊓ Subgroup.centralizer ({s} : Set G) = B0 := by
        apply le_antisymm
        · intro r hr
          have hrRS : r ∈ RS := hR1fixed_le_RS hr
          have hrInf : r ∈ RS ⊓ Subgroup.centralizer ({s} : Set G) := ⟨hrRS, hr.2⟩
          rw [hRSfixed] at hrInf
          exact hrInf
        · intro b hb
          exact ⟨hB0_le_R1 hb, hB0_cent_s hb⟩
      have hW_cent_s : W ≤ Subgroup.centralizer ({s} : Set G) := by
        intro w hw
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hsC_V) w
          (hch.section3.section2.W_le_V hw)
      have hW_not_le_R1 : ¬ W ≤ R1 := by
        intro hWle
        have hWleB0 : W ≤ B0 := by
          intro w hw
          have hwfix : w ∈ R1 ⊓ Subgroup.centralizer ({s} : Set G) :=
            ⟨hWle hw, hW_cent_s hw⟩
          rw [hR1fixed] at hwfix
          exact hwfix
        have hWeq : W = B0 := by
          apply Subgroup.eq_of_le_of_card_ge hWleB0
          rw [hW9, hB0card]
        have hP_le_W : P ≤ W := by
          rw [hWeq]
          exact le_sup_left
        have hPbot : P ≤ (⊥ : Subgroup G) := by
          intro x hx
          exact hWdisjP.le_bot ⟨hP_le_W hx, hx⟩
        have hPeq : P = ⊥ := le_antisymm hPbot bot_le
        rw [hPeq] at hPcard
        norm_num at hPcard
      have hW_le_R2 : W ≤ R2 :=
        hch.section3.section2.W_le_V.trans
          (le_sup_right.trans h15.2.2.2.2.2.2.1)
      let R1sub : Subgroup R2 := R1.subgroupOf R2
      let Wsub : Subgroup R2 := W.subgroupOf R2
      letI : R1sub.Normal := by simpa [R1sub] using hR1normal
      let qR : R2 →* R2 ⧸ R1sub := QuotientGroup.mk' R1sub
      have hQcard : Nat.card (R2 ⧸ R1sub) = 3 := by
        change R1sub.index = 3
        simpa [R1sub] using hindex3
      obtain ⟨w0, hw0W, hw0R1⟩ := Set.not_subset.mp hW_not_le_R1
      let w0R2 : R2 := ⟨w0, hW_le_R2 hw0W⟩
      have hqw0ne : qR w0R2 ≠ 1 := by
        intro hq
        apply hw0R1
        have hwmem : w0R2 ∈ R1sub :=
          (QuotientGroup.eq_one_iff (N := R1sub) (x := w0R2)).mp hq
        exact hwmem
      have hQprime : Nat.Prime (Nat.card (R2 ⧸ R1sub)) := by
        rw [hQcard]
        exact Nat.prime_three
      have hzpowTop : Subgroup.zpowers (qR w0R2) = ⊤ :=
        zpowers_eq_top_of_prime_card_of_ne_one hQprime hqw0ne
      have hqw0mem : qR w0R2 ∈ Wsub.map qR := by
        refine ⟨w0R2, ?_, rfl⟩
        exact hw0W
      have hWmapTop : Wsub.map qR = ⊤ := by
        apply top_unique
        rw [← hzpowTop]
        exact Subgroup.zpowers_le.2 hqw0mem
      have hR2eq : R1 ⊔ W = R2 := by
        apply le_antisymm (sup_le hR1_le_R2 hW_le_R2)
        intro x hx
        let xR2 : R2 := ⟨x, hx⟩
        have hxmap : qR xR2 ∈ Wsub.map qR := by
          rw [hWmapTop]
          trivial
        rcases hxmap with ⟨w, hwWsub, hqw⟩
        have hdiv : xR2 / w ∈ R1sub :=
          (QuotientGroup.eq_iff_div_mem).mp hqw.symm
        have hdivG0 : ((xR2 / w : R2) : G) ∈ R1 := hdiv
        have hdivG : x * (w : G)⁻¹ ∈ R1 := by
          simpa [xR2, div_eq_mul_inv] using hdivG0
        have hwG : (w : G) ∈ W := hwWsub
        have hprod : (x * (w : G)⁻¹) * (w : G) ∈ R1 ⊔ W :=
          (R1 ⊔ W).mul_mem
            ((le_sup_left : R1 ≤ R1 ⊔ W) hdivG)
            ((le_sup_right : W ≤ R1 ⊔ W) hwG)
        simpa [mul_assoc] using hprod
      have hC_norm_R2 : C ≤ Subgroup.normalizer (R2 : Set G) := by
        intro v hv
        rw [h14.2.2.2.2.2.2.2.1]
        apply chapter2_claim17_mem_normalizer_centralizer_of_mem_normalizer Z1
        have hvNZ1 : (v : G) ∈ Subgroup.normalizer (Z1 : Set G) := by
          rw [h16.2.2.2.2]
          exact (le_sup_right : C ≤ R2 ⊔ C) hv
        exact hvNZ1
      have hdisjR2C : Disjoint R2 C := by
        apply Subgroup.disjoint_of_coprime_natCard
        rw [hR2card9, hCcard]
        norm_num
      let sNorm2 : Subgroup.normalizer (R2 : Set G) := ⟨s, hC_norm_R2 hsC⟩
      let phiR2 : MulAut R2 := R2.normalizerMonoidHom sNorm2
      have hphiR2_apply (r : R2) : (phiR2 r : G) = s * (r : G) * s⁻¹ := by
        calc
          (phiR2 r : G) = ((R2.normalizerMonoidHom sNorm2) r : G) := rfl
          _ = (sNorm2 : G) * (r : G) * (sNorm2 : G)⁻¹ :=
            Subgroup.normalizerMonoidHom_apply_apply_coe R2 sNorm2 r
          _ = s * (r : G) * s⁻¹ := by simp [sNorm2]
      have hR1inv : ∀ r : R2, r ∈ R1sub ↔ phiR2 r ∈ R1sub := by
        intro r
        have hnorm := Subgroup.mem_normalizer_iff.mp (hC_norm_R1 hsC) (r : G)
        simpa [R1sub, hphiR2_apply r, Subgroup.mem_subgroupOf] using hnorm
      let phiQ : MulAut (R2 ⧸ R1sub) :=
        External.invariantQuotientAut phiR2 R1sub hR1inv
      have hphiQfixed : ∀ x : R2 ⧸ R1sub, phiQ x = x := by
        intro x
        have hxmap : x ∈ Wsub.map qR := by
          rw [hWmapTop]
          trivial
        rcases hxmap with ⟨w, hwWsub, rfl⟩
        have hsw : s * (w : G) = (w : G) * s := by
          exact ((Subgroup.mem_centralizer_iff.mp hsC_V) (w : G)
            (hch.section3.section2.W_le_V hwWsub)).symm
        have hphiW : phiR2 w = w := by
          apply Subtype.ext
          simp [phiR2, sNorm2, hsI.inv_eq_self, hsw, mul_assoc]
          simpa [pow_two] using hsI.sq_eq_one
        change External.invariantQuotientAut phiR2 R1sub hR1inv
            (QuotientGroup.mk' R1sub w) = QuotientGroup.mk' R1sub w
        rw [External.invariantQuotientAut_mk', hphiW]
      have hqS (r : R2) : qR (phiR2 r) = qR r := by
        calc
          qR (phiR2 r) = phiQ (qR r) :=
            (External.invariantQuotientAut_mk' phiR2 R1sub hR1inv r).symm
          _ = qR r := hphiQfixed (qR r)
      have hqC : ∀ v : C, ∀ r : R2,
          qR ⟨Section2.conjBy (v : G) (r : G),
            (Subgroup.mem_normalizer_iff.mp (hC_norm_R2 v.2) (r : G)).1 r.2⟩ = qR r := by
        intro v r
        rcases chapter2_claim17_mem_closure_involution_eq_one_or_eq s hsI
          ⟨(v : G), by simpa [C] using v.2⟩ with hv | hv
        · have hvG : (v : G) = 1 := hv
          apply congrArg qR
          apply Subtype.ext
          simp [Section2.conjBy, hvG]
        · have hvG : (v : G) = s := hv
          have hphiR2_subtype : phiR2 r = ⟨s * (r : G) * s⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hC_norm_R2 hsC) (r : G)).1 r.2⟩ :=
            Subtype.ext (hphiR2_apply r)
          have h_goal := hqS r
          simp [Section2.conjBy, hvG, hphiR2_subtype] at h_goal ⊢
          exact h_goal
      have hloc := chapter2_claim17_local_index_of_invariant_character
        R2 C hC_norm_R2 hdisjR2C qR
          (QuotientGroup.mk'_surjective R1sub) hqC
      simpa [H17, C, hQcard] using hloc
  obtain ⟨M, hM_normal, hM_index⟩ := hlocal_index
  letI : (External.hallPResidual p G).Normal :=
    External.hallPResidual_normal p G
  letI : (External.hallPResidual p H17).Normal :=
    External.hallPResidual_normal p H17
  letI : M.Normal := hM_normal
  have hres_le : External.hallPResidual p H17 ≤ M :=
    chapter2_claim17_hallPResidual_le_of_quotient_card_eq p M hM_index
  have hres_le' :
      External.hallPResidual p H17 ≤ M.comap (MonoidHom.id H17) := by
    simpa [Subgroup.comap_id] using hres_le
  let phi : (H17 ⧸ External.hallPResidual p H17) →* (H17 ⧸ M) :=
    QuotientGroup.map (External.hallPResidual p H17) M
      (MonoidHom.id H17) hres_le'
  have hphi : Function.Surjective phi := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M y
    exact ⟨QuotientGroup.mk' (External.hallPResidual p H17) x, rfl⟩
  exact
    chapter2_claim17_global_index_from_local_hall_data
      p (External.hallPResidual p G) (External.hallPResidual p H17)
      hquot phi hphi hM_index

public theorem claim_17
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R T R1 R2 L : Subgroup G) (t s : G) (p : ℕ)
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
    (h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
          Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
            (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              Z1 ⊔ P ∧
              R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                R ⊔ Sigma ≤ R1 ∧
                  R2 = Subgroup.centralizer (Z1 : Set G) ∧
                    R1 ≤ R2)
    (h15 : L ≤ R1 ∧
      (Nat.card L = 9 ∧ IsCyclic L) ∧
        (∀ x : G, x ∈ L → rightConjugateElem x s = x⁻¹) ∧
          V ≤ Subgroup.normalizer (L : Set G) ∧
            W ≤ Subgroup.centralizer (L : Set G) ∧
              ¬ P ≤ Subgroup.centralizer (L : Set G) ∧
                L ⊔ V ≤ R2 ∧
                  Nat.card R2 = 3 * Nat.card ((L ⊔ V : Subgroup G)) ∧
                  (L ⊔ V) ⊓ Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) =
                    Z1 ⊔ Sigma ∧
                    ∀ x : G, x ∈ L ⊔ V →
                      (x ^ 3 = 1 ↔ x ∈ Z1 ⊔ Sigma ⊔ P))
    (h16 : Z1 ⊔ P ⊔ Sigma ≤ R1 ∧
      (∀ x y : G, x ∈ Z1 ⊔ P ⊔ Sigma → y ∈ R1 →
        x * y * x⁻¹ * y⁻¹ ∈
          R1 ⊓ Subgroup.centralizer (R1 : Set G)) ∧
      (∀ X : Subgroup G,
        X ≤ Z1 ⊔ P ⊔ Sigma →
          Nat.card X = 3 →
            (∀ x : G, x ∈ X → x ≠ 1 → IsStronglyReal x) →
              X = Z1) ∧
        Subgroup.normalizer ((Z1 ⊔ P ⊔ Sigma : Subgroup G) : Set G) =
          Subgroup.normalizer (Z1 : Set G) ∧
          Subgroup.normalizer (Z1 : Set G) = R2 ⊔ Subgroup.closure ({s} : Set G))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hp3 : p = 3)
    (hSigmaCard : Nat.card Sigma = 3)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hst3 : orderOf (s * t) = 3)
    (hR2p : IsPGroup 3 R2)
    (hcenterR2 : R2 ⊓ Subgroup.centralizer (R2 : Set G) = Z1)
    (hR2s : ∃ R2s : Sylow 3 G, (R2s : Subgroup G) = R2)
    (hRT : R = T ⊔ P)
    (hTdisjP : Disjoint T P)
    (hTleCP : T ≤ Subgroup.centralizer (P : Set G))
    (hSigmaNormT : Sigma ≤ Subgroup.normalizer (T : Set G))
    (hTinverted : ∀ x : G, x ∈ T → rightConjugateElem x s = x⁻¹)
    (hRdisjSigma : Disjoint R Sigma)
    (hRScard : Nat.card (R ⊔ Sigma : Subgroup G) = 81)
    (hWdisjP : Disjoint W P)
    (hWcases : Nat.card W = 3 ∨ Nat.card W = 9)
    (hfactor : ∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
      Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u)
    (hR1p : IsPGroup 3 R1)
    (hphiPack : ∃ phi : (Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G)) →*
        Equiv.Perm (Fin 3),
      Function.Surjective phi ∧
        MonoidHom.ker phi =
          (R ⊔ Sigma).subgroupOf
            (Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G)))
    (hNRS : Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) =
      R1 ⊔ Subgroup.closure ({s} : Set G))
    (hdisjR1C : Disjoint R1 (Subgroup.closure ({s} : Set G)))
    (hNleNR1 : Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ≤
      Subgroup.normalizer (R1 : Set G))
    (hcenterR1 : R1 ⊓ Subgroup.centralizer (R1 : Set G) = Z1)
    (hindex : (R1.subgroupOf R2).index = 1 ∨
      (R1.subgroupOf R2).index = 3) :
    False := by
  have hweak :
      External.WeaklyClosedIn R2 (Z1 ⊔ P ⊔ Sigma) :=
    chapter2_claim17_weakly_closed_Z1PSigma
      H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L t s p hch h14 h15 h16
      hSigma hp3 hSigmaCard hZ1 hst3 hR2p hcenterR2
  have hcomm :
      IsMulCommutative (Z1 ⊔ P ⊔ Sigma : Subgroup G) :=
    chapter2_claim17_commutative P Sigma Z1 (L ⊔ V)
      (by simpa [hp3] using hch.B1.P_card)
      (hch.B1.P_le_V.trans le_sup_right)
      h15.2.2.2.2.2.2.2.2.1
  let H17 : Subgroup G := R2 ⊔ Subgroup.closure ({s} : Set G)
  have hH17 :
      H17 = Subgroup.normalizer ((Z1 ⊔ P ⊔ Sigma : Subgroup G) : Set G) := by
    change R2 ⊔ Subgroup.closure ({s} : Set G) =
      Subgroup.normalizer ((Z1 ⊔ P ⊔ Sigma : Subgroup G) : Set G)
    exact (h16.2.2.2.1.trans h16.2.2.2.2).symm
  have hhall :=
    chapter2_claim17_hallWielandt_data p R2 (Z1 ⊔ P ⊔ Sigma) H17
      hp3 hR2s hH17 hweak hcomm
  have hmap :
      let H17 : Subgroup G := R2 ⊔ Subgroup.closure ({s} : Set G)
      (External.hallPResidual p H17).map H17.subtype =
        H17 ⊓ External.hallPResidual p G := by
    simpa [H17] using hhall.1
  have hquot :
      let H17 : Subgroup G := R2 ⊔ Subgroup.closure ({s} : Set G)
      letI : (External.hallPResidual p G).Normal := External.hallPResidual_normal p G
      letI : (External.hallPResidual p H17).Normal := External.hallPResidual_normal p H17
      Nonempty ((G ⧸ External.hallPResidual p G) ≃*
        (↥H17 ⧸ External.hallPResidual p H17)) := by
    simpa [H17] using (hhall.2)
  exact
    claim_17_B2_excludes_normal_index_p H D Q K V W Q0 S Q1 P t s p hch
      (chapter2_claim17_normal_index_from_hallWielandt_cases_source_interface
        H D Q K V W Q0 S Q1 P Sigma Z1 R T R1 R2 L t s p hch h14 h15 h16
        hSigma hp3 hSigmaCard hZ1 hst3 hR2p hR2s
        hRT hTdisjP hTleCP hSigmaNormT hTinverted hRdisjSigma hRScard
        hWdisjP hWcases hfactor hR1p hphiPack hNRS hdisjR1C hNleNR1 hcenterR1 hindex
        hmap hquot)

end PFchapter2
end CFSG.BenderSuzuki
