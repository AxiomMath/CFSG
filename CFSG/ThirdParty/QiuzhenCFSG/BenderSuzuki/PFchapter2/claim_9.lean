module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.AppendixIInput
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_2_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_4

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixIII
open PFchapter1section3

/-!
# Peterfalvi, Part II, Chapter II, Claim (9)
-/

private theorem chapter2_K_inf_V_eq_bot
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
      K ≤ D ∧
      (∀ x : G, x ∈ K ↔ x ∈ D ∧
        _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
      W ≤ V ∧
      W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
      Q0 ≤ Q ∧
      (∀ x : G, x ∈ Q0 ↔ x = 1 ∨
        (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
      S ≤ Q ∧ Q1 ≤ Q ∧
      (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
      Odd (Nat.card Q1) ∧ Disjoint S Q1 ∧
      (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
      S ⊔ Q1 = Q)) :
    K ⊓ V = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxK : x ∈ K := hx.1
  have hxV : x ∈ V := hx.2
  have ht_inv : t⁻¹ = t := hsec.hA.A1.involution_t.inv_eq_self
  have ht_sq : t * t = 1 := by
    simpa [pow_two] using hsec.hA.A1.involution_t.sq_eq_one
  have hxInv : t * x * t = x⁻¹ := by
    have hx := ((hsec.K_def x).mp hxK).2
    simpa [rightConjugateElem, ht_inv] using hx
  have hxComm : x * t = t * x := by
    rw [hsec.V_eq] at hxV
    exact Subgroup.mem_centralizer_singleton_iff.mp hxV.2
  have hxFix : t * x * t = x := by
    rw [← hxComm, mul_assoc, ht_sq, mul_one]
  have hxSelfInv : x = x⁻¹ := hxFix.symm.trans hxInv
  have hxSq : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := by rw [pow_two]
      _ = x * x⁻¹ := congrArg (fun z : G => x * z) hxSelfInv
      _ = 1 := mul_inv_cancel x
  by_contra hxOne
  let xD : D := ⟨x, hsec.K_le_D hxK⟩
  have hxDsq : xD ^ 2 = 1 := by
    apply Subtype.ext
    exact hxSq
  have hxDne : xD ≠ 1 := by
    intro h
    apply hxOne
    exact congrArg Subtype.val h
  have horder : orderOf xD = 2 :=
    orderOf_eq_prime_iff.mpr ⟨hxDsq, hxDne⟩
  have htwoDvd : 2 ∣ Nat.card D := by
    rw [← horder]
    exact orderOf_dvd_natCard xD
  exact (Nat.not_even_iff_odd.mpr hsec.hA.A1.D_odd)
    (even_iff_two_dvd.mpr htwoDvd)

private theorem chapter2_K_sup_V_eq_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
      K ≤ D ∧
      (∀ x : G, x ∈ K ↔ x ∈ D ∧
        _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
      W ≤ V ∧
      W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
      Q0 ≤ Q ∧
      (∀ x : G, x ∈ Q0 ↔ x = 1 ∨
        (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
      S ≤ Q ∧ Q1 ≤ Q ∧
      (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
      Odd (Nat.card Q1) ∧ Disjoint S Q1 ∧
      (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
      S ⊔ Q1 = Q)) :
    K ⊔ V = D := by
  apply le_antisymm
  · refine sup_le hsec.K_le_D ?_
    rw [hsec.V_eq]
    exact inf_le_left
  · intro d hd
    have htNorm : t ∈ Subgroup.normalizer (D : Set G) :=
      proposition_5_involution_t_mem_normalizer_D H D Q t hsec.hA.A1
    rcases (lemma_a t D hsec.hA.A1.involution_t hsec.hA.A1.D_odd htNorm).1.2.2 hd with
      ⟨⟨v, z⟩, _hvz, hprod⟩
    have hvV : (v : G) ∈ V := by
      rw [hsec.V_eq]
      exact v.property
    have hzK : (z : G) ∈ K := (hsec.K_def (z : G)).mpr z.property
    rw [← hprod]
    exact (K ⊔ V).mul_mem (Subgroup.mem_sup_right hvV)
      (Subgroup.mem_sup_left hzK)
private lemma chapter2_claim9_conjugate_mem_sup_of_normalizes
    {G : Type*} [Group G] {A B : Subgroup G} {x y : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G))
    (hy : y ∈ A ⊔ B) :
    x * y * x⁻¹ ∈ A ⊔ B := by
  rw [Subgroup.sup_eq_closure] at hy ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
  · intro z hz
    rcases hz with hzA | hzB
    · exact
        Subgroup.subset_closure
          (Or.inl ((Subgroup.mem_normalizer_iff.mp hA z).1 hzA))
    · exact
        Subgroup.subset_closure
          (Or.inr ((Subgroup.mem_normalizer_iff.mp hB z).1 hzB))
  · simp
  · intro a b _ha _hb hca hcb
    simpa [mul_assoc] using
      (Subgroup.closure ((A : Set G) ∪ (B : Set G))).mul_mem hca hcb
  · intro a _ha hca
    simpa [mul_assoc] using
      (Subgroup.closure ((A : Set G) ∪ (B : Set G))).inv_mem hca

private lemma chapter2_claim9_mem_normalizer_sup_of_normalizes
    {G : Type*} [Group G] {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact chapter2_claim9_conjugate_mem_sup_of_normalizes hA hB
  · intro hy
    have hAinv : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem hA
    have hBinv : x⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
      (Subgroup.normalizer (B : Set G)).inv_mem hB
    have h := chapter2_claim9_conjugate_mem_sup_of_normalizes
      (A := A) (B := B) (x := x⁻¹) (y := x * y * x⁻¹)
      hAinv hBinv hy
    simpa [mul_assoc] using h

private lemma chapter2_claim9_le_normalizer_sup_of_normalizes
    {G : Type*} [Group G] {A B X : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro x hx
  exact chapter2_claim9_mem_normalizer_sup_of_normalizes (hA hx) (hB hx)

private theorem chapter2_claim9_hom_eq_one_of_prime_target
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    (p : ℕ) (hp : Nat.Prime p) (hcardA : Nat.card A = p)
    (hB2 : HypothesisB2 G p) (f : G →* A) :
    f = 1 := by
  have hprimeA : Nat.Prime (Nat.card A) := hcardA.symm ▸ hp
  letI : Fact (Nat.card A).Prime := ⟨hprimeA⟩
  rcases f.range.eq_bot_or_eq_top_of_prime_card with hrange | hrange
  · exact MonoidHom.range_eq_bot_iff.mp hrange
  · have hquot : Nat.card (G ⧸ f.ker) = p := by
      calc
        Nat.card (G ⧸ f.ker) = f.ker.index := Subgroup.index_eq_card f.ker
        _ = Nat.card f.range := Subgroup.index_ker f
        _ = Nat.card A := by simp [hrange]
        _ = p := hcardA
    exact (hB2 f.ker inferInstance hquot).elim

private noncomputable def chapter2_claim9_rightTranslateLeftTransversal
    {G : Type*} [Group G] {H : Subgroup G}
    (T : H.LeftTransversal) (h : H) : H.LeftTransversal :=
  let f : G ⧸ H → G := fun q =>
    (T.2.leftQuotientEquiv q : G) * (h : G)
  ⟨Set.range f, Subgroup.isComplement_range_left fun q => by
    change (QuotientGroup.mk
      ((T.2.leftQuotientEquiv q : G) * (h : G)) : G ⧸ H) = q
    rw [QuotientGroup.mk_mul_of_mem _ h.2]
    exact T.2.quotientGroupMk_leftQuotientEquiv q⟩

private theorem chapter2_claim9_rightTranslateLeftTransversal_apply
    {G : Type*} [Group G] {H : Subgroup G}
    (T : H.LeftTransversal) (h : H) (q : G ⧸ H) :
    ((chapter2_claim9_rightTranslateLeftTransversal T h).2.leftQuotientEquiv q : G) =
      (T.2.leftQuotientEquiv q : G) * (h : G) := by
  let f : G ⧸ H → G := fun q =>
    (T.2.leftQuotientEquiv q : G) * (h : G)
  have hf : ∀ q, (f q : G ⧸ H) = q := by
    intro q
    change (QuotientGroup.mk
      ((T.2.leftQuotientEquiv q : G) * (h : G)) : G ⧸ H) = q
    rw [QuotientGroup.mk_mul_of_mem _ h.2]
    exact T.2.quotientGroupMk_leftQuotientEquiv q
  change
    ((Subgroup.isComplement_range_left hf).leftQuotientEquiv q : G) = f q
  exact Subgroup.IsComplement.leftQuotientEquiv_apply hf q

private theorem chapter2_claim9_leftQuotientEquiv_mk_of_mem
    {G : Type*} [Group G] {H : Subgroup G}
    (T : H.LeftTransversal) {x : G} (hx : x ∈ (T : Set G)) :
    (T.2.leftQuotientEquiv (QuotientGroup.mk x) : G) = x := by
  have hinj := (Subgroup.isComplement_subgroup_right_iff_bijective.mp T.2).1
  have heq :
      T.2.leftQuotientEquiv (QuotientGroup.mk x) =
        (⟨x, hx⟩ : (T : Set G)) := by
    apply hinj
    simpa using T.2.quotientGroupMk_leftQuotientEquiv (QuotientGroup.mk x)
  exact congrArg Subtype.val heq

private theorem chapter2_claim9_mem_rightTranslateLeftTransversal_iff
    {G : Type*} [Group G] {H : Subgroup G}
    (T : H.LeftTransversal) (h : H) (y : G) :
    y ∈ (chapter2_claim9_rightTranslateLeftTransversal T h : Set G) ↔
      ∃ r : G, r ∈ (T : Set G) ∧ y = r * (h : G) := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(T.2.leftQuotientEquiv q : G),
      (T.2.leftQuotientEquiv q).property, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    refine ⟨QuotientGroup.mk r, ?_⟩
    change (T.2.leftQuotientEquiv (QuotientGroup.mk r) : G) * (h : G) =
      r * (h : G)
    rw [chapter2_claim9_leftQuotientEquiv_mk_of_mem T hr]

private noncomputable def chapter2_claim9_sourceLeftTransversal
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : PFchapter1section1.HypothesisA1 G Ω H D Q t) :
    H.LeftTransversal := by
  classical
  let R : Set G := {x : G | x = 1 ∨ ∃ q : Q, x = (q : G) * t}
  refine ⟨R, Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr ?_⟩
  intro g
  have htinv : t⁻¹ = t := hA1.involution_t.inv_eq_self
  have htsq : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  by_cases hgH : g ∈ H
  · let r0 : R := ⟨1, Or.inl rfl⟩
    refine ⟨r0, by simpa [r0], ?_⟩
    intro r hr
    apply Subtype.ext
    rcases r.property with hr1 | ⟨q, hrq⟩
    · exact hr1
    · have hrH : (r : G) ∈ H := by
        have hm := H.mul_mem hgH (H.inv_mem hr)
        convert hm using 1 ;
          group
      have htH : t ∈ H := by
        have hm := H.mul_mem (H.inv_mem (hA1.Q_le_H q.property)) hrH
        simpa [hrq, mul_assoc] using hm
      exact (hA1.t_not_mem_H htH).elim
  · have hginv : g⁻¹ ∉ H := by
      intro h
      exact hgH (by simpa using H.inv_mem h)
    rcases PFchapter1section1.proposition_4_a H D Q t hA1 g⁻¹ hginv with
      ⟨⟨h0, q0⟩, hdec, huniq⟩
    let r0 : R := ⟨(q0 : G)⁻¹ * t,
      Or.inr ⟨q0⁻¹, by simp⟩⟩
    have hgform : g = (q0 : G)⁻¹ * t * (h0 : G)⁻¹ := by
      have hinv := congrArg Inv.inv hdec
      simpa [htinv, mul_assoc] using hinv
    have hr0 : (r0 : G)⁻¹ * g ∈ H := by
      have heq : (r0 : G)⁻¹ * g = (h0 : G)⁻¹ := by
        simp [r0, hgform, htinv, mul_assoc]
        rw [← mul_assoc, htsq, one_mul]
      rw [heq]
      exact H.inv_mem h0.property
    refine ⟨r0, hr0, ?_⟩
    intro r hr
    apply Subtype.ext
    rcases r.property with hr1 | ⟨q, hrq⟩
    · have : g ∈ H := by simpa [hr1] using hr
      exact (hgH this).elim
    · let cH : H := ⟨(r : G)⁻¹ * g, hr⟩
      let p' : H × Q := ⟨cH⁻¹, q⁻¹⟩
      have hp' : g⁻¹ = (p'.1 : G) * t * (p'.2 : G) := by
        change g⁻¹ = (((r : G)⁻¹ * g)⁻¹) * t * (q : G)⁻¹
        calc
          g⁻¹ = g⁻¹ * ((q : G) * t) * t * (q : G)⁻¹ := by
            simp [htsq, mul_assoc]
          _ = g⁻¹ * (r : G) * t * (q : G)⁻¹ := by rw [hrq]
          _ = (((r : G)⁻¹ * g)⁻¹) * t * (q : G)⁻¹ := by group
      have heq : p' = (h0, q0) := huniq p' hp'
      have hq : q⁻¹ = q0 := congrArg Prod.snd heq
      have hqG : (q : G) = (q0 : G)⁻¹ := by
        have hv := congrArg (fun z : Q => (z : G)) hq
        have hinv := congrArg Inv.inv hv
        simpa using hinv
      simp [r0, hrq, hqG]

private theorem chapter2_claim9_smul_sourceLeftTransversal_eq_rightTranslate
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q P V : Subgroup G) (t x : G)
    (hA1 : PFchapter1section1.HypothesisA1 G Ω H D Q t)
    (hxH : x ∈ H) (hVeq : V = PFchapter1section1.peterfalviV D t)
    (hPleV : P ≤ V) (hxP : x ∈ P) :
    let T := chapter2_claim9_sourceLeftTransversal H D Q t hA1
    let xH : H := ⟨x, hxH⟩
    x • T = chapter2_claim9_rightTranslateLeftTransversal T xH := by
  classical
  let T := chapter2_claim9_sourceLeftTransversal H D Q t hA1
  have hxV : x ∈ V := hPleV hxP
  let xH : H := ⟨x, hxH⟩
  have hxt : x * t = t * x := by
    rw [hVeq] at hxV
    exact Subgroup.mem_centralizer_singleton_iff.mp hxV.2
  have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA1.Q_le_H).mp hA1.Q_normal_in_H
  have hxNormQ : x ∈ Subgroup.normalizer (Q : Set G) := hHnormQ hxH
  apply Subtype.ext
  ext y
  constructor
  · intro hy
    rcases Set.mem_smul_set.mp hy with ⟨r, hr, rfl⟩
    change r = 1 ∨ ∃ q : Q, r = (q : G) * t at hr
    apply (chapter2_claim9_mem_rightTranslateLeftTransversal_iff T xH _).2
    rcases hr with hr1 | ⟨q, hrq⟩
    · subst r
      refine ⟨1, ?_, by simp [xH]⟩
      change (1 : G) = 1 ∨ ∃ q : Q, (1 : G) = (q : G) * t
      exact Or.inl rfl
    · let q' : Q := ⟨x * (q : G) * x⁻¹,
        (Subgroup.mem_normalizer_iff.mp hxNormQ (q : G)).1 q.property⟩
      refine ⟨(q' : G) * t, ?_, ?_⟩
      · change (q' : G) * t = 1 ∨ ∃ q : Q, (q' : G) * t = (q : G) * t
        exact Or.inr ⟨q', rfl⟩
      · rw [hrq]
        calc
          x * ((q : G) * t) = (x * (q : G) * x⁻¹) * (x * t) := by group
          _ = (x * (q : G) * x⁻¹) * (t * x) := by rw [hxt]
          _ = ((q' : G) * t) * (xH : G) := by simp [q', xH, mul_assoc]
  · intro hy
    rcases (chapter2_claim9_mem_rightTranslateLeftTransversal_iff T xH _).1 hy with
      ⟨r, hr, rfl⟩
    change r = 1 ∨ ∃ q : Q, r = (q : G) * t at hr
    apply Set.mem_smul_set.mpr
    rcases hr with hr1 | ⟨q, hrq⟩
    · subst r
      refine ⟨1, ?_, by simp [xH]⟩
      change (1 : G) = 1 ∨ ∃ q : Q, (1 : G) = (q : G) * t
      exact Or.inl rfl
    · have hxInvNormQ : x⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
        (Subgroup.normalizer (Q : Set G)).inv_mem hxNormQ
      let q' : Q := ⟨x⁻¹ * (q : G) * x,
        by simpa using
          (Subgroup.mem_normalizer_iff.mp hxInvNormQ (q : G)).1 q.property⟩
      refine ⟨(q' : G) * t, ?_, ?_⟩
      · change (q' : G) * t = 1 ∨ ∃ q : Q, (q' : G) * t = (q : G) * t
        exact Or.inr ⟨q', rfl⟩
      · rw [hrq]
        calc
          x * ((q' : G) * t) = (q : G) * (x * t) := by simp [q', mul_assoc]
          _ = (q : G) * (t * x) := by rw [hxt]
          _ = ((q : G) * t) * (xH : G) := by simp [xH, mul_assoc]

private theorem chapter2_claim9_diff_rightTranslate
    {G A : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    [CommGroup A] (φ : H →* A) (S T : H.LeftTransversal) (h : H) :
    Subgroup.leftTransversals.diff φ S
        (chapter2_claim9_rightTranslateLeftTransversal T h) =
      Subgroup.leftTransversals.diff φ S T * (φ h) ^ H.index := by
  classical
  letI := H.fintypeQuotientOfFiniteIndex
  rw [Subgroup.leftTransversals.diff, Subgroup.leftTransversals.diff,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card,
    ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [← φ.map_mul]
  apply congrArg φ
  apply Subtype.ext
  change
    (S.2.leftQuotientEquiv q : G)⁻¹ *
        ((chapter2_claim9_rightTranslateLeftTransversal T h).2.leftQuotientEquiv q : G) =
      ((S.2.leftQuotientEquiv q : G)⁻¹ * (T.2.leftQuotientEquiv q : G)) * (h : G)
  rw [chapter2_claim9_rightTranslateLeftTransversal_apply]
  simp [mul_assoc]

private theorem chapter2_claim9_normal_complement
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
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p)) :
    let N : Subgroup G := Q ⊔ K ⊔ W
    ∃ hN : (N.subgroupOf H).Normal,
      letI : (N.subgroupOf H).Normal := hN
      (N.subgroupOf H).IsComplement' (P.subgroupOf H) := by
  classical
  let hsec := hch.section3.section2
  let hA1 := hsec.hA.A1
  let N : Subgroup G := Q ⊔ K ⊔ W
  let KW : Subgroup G := K ⊔ W
  have hVleD : V ≤ D :=
    PFchapter1section2.proposition_3_V_le_D H D Q K V W Q0 S Q1 t hsec
  have hWleD : W ≤ D := hsec.W_le_V.trans hVleD
  have hPleD : P ≤ D := hch.B1.P_le_V.trans hVleD
  have hKnormalD : (K.subgroupOf D).Normal :=
    (PFchapter1section2.proposition_2 H D Q K V W Q0 S Q1 t hsec).2
  have hWnormalD : (W.subgroupOf D).Normal :=
    PFchapter1section2.peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_normal_D
      H D Q K V W t hA1 hsec.K_def hsec.V_eq hsec.W_le_V hsec.W_eq hVleD
  have hDnormK : D ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsec.K_le_D).mp hKnormalD
  have hDnormW : D ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWleD).mp hWnormalD
  have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA1.Q_le_H).mp hA1.Q_normal_in_H
  have hDnormQ : D ≤ Subgroup.normalizer (Q : Set G) :=
    hA1.D_le_H.trans hHnormQ
  have hDnormQK : D ≤ Subgroup.normalizer ((Q ⊔ K : Subgroup G) : Set G) :=
    chapter2_claim9_le_normalizer_sup_of_normalizes hDnormQ hDnormK
  have hDnormN : D ≤ Subgroup.normalizer (N : Set G) := by
    simpa [N] using
      chapter2_claim9_le_normalizer_sup_of_normalizes hDnormQK hDnormW
  have hQleN : Q ≤ N := le_sup_left.trans le_sup_left
  have hQnormN : Q ≤ Subgroup.normalizer (N : Set G) :=
    hQleN.trans Subgroup.le_normalizer
  have hHnormN : H ≤ Subgroup.normalizer (N : Set G) := by
    rw [← hA1.Q_sup_D]
    exact sup_le hQnormN hDnormN
  have hNleH : N ≤ H := by
    exact sup_le
      (sup_le hA1.Q_le_H (hsec.K_le_D.trans hA1.D_le_H))
      (hWleD.trans hA1.D_le_H)
  have hNnormalH : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNleH).mpr hHnormN
  have hKinfV : K ⊓ V = ⊥ :=
    chapter2_K_inf_V_eq_bot H D Q K V W Q0 S Q1 t hsec
  rcases (claim_1 H D Q K V W Q0 S Q1 P t s p hch).1 with
    ⟨_hWleV, _hPleV, _hWnormV, hWdisjP, hWsupP⟩
  have hKWleD : KW ≤ D := sup_le hsec.K_le_D hWleD
  have hKWdisjP : Disjoint KW P := by
    let KKW : Subgroup KW := K.subgroupOf KW
    let WKW : Subgroup KW := W.subgroupOf KW
    have hKleKW : K ≤ KW := le_sup_left
    have hWleKW : W ≤ KW := le_sup_right
    haveI : KKW.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKleKW).mpr
        (hKWleD.trans hDnormK)
    rw [Subgroup.disjoint_def]
    intro x hxKW hxP
    let xKW : KW := ⟨x, hxKW⟩
    have hxSup : xKW ∈ KKW ⊔ WKW := by
      rw [← Subgroup.subgroupOf_sup hKleKW hWleKW]
      simp [KW, xKW]
    rcases Subgroup.mem_sup_of_normal_left.mp hxSup with
      ⟨kKW, hkK, wKW, hwW, hkw⟩
    have hkKG : (kKW : G) ∈ K := by
      simpa [KKW, Subgroup.mem_subgroupOf] using hkK
    have hwWG : (wKW : G) ∈ W := by
      simpa [WKW, Subgroup.mem_subgroupOf] using hwW
    have hkwG : (kKW : G) * (wKW : G) = x := by
      simpa [xKW] using congrArg Subtype.val hkw
    have hkV : (kKW : G) ∈ V := by
      have hk_eq : (kKW : G) = x * (wKW : G)⁻¹ := by
        rw [← hkwG]
        simp [mul_assoc]
      rw [hk_eq]
      exact V.mul_mem (hch.B1.P_le_V hxP) (V.inv_mem (hsec.W_le_V hwWG))
    have hkOne : (kKW : G) = 1 := by
      have hkInf : (kKW : G) ∈ K ⊓ V := ⟨hkKG, hkV⟩
      rw [hKinfV] at hkInf
      simpa using hkInf
    rw [hkOne, one_mul] at hkwG
    have hxW : x ∈ W := hkwG ▸ hwWG
    exact (Subgroup.disjoint_def.mp hWdisjP) hxW hxP
  have hPleH : P ≤ H := hPleD.trans hA1.D_le_H
  let NH : Subgroup H := N.subgroupOf H
  let PH : Subgroup H := P.subgroupOf H
  let QH : Subgroup H := Q.subgroupOf H
  let KWH : Subgroup H := KW.subgroupOf H
  have hKWleH : KW ≤ H := hKWleD.trans hA1.D_le_H
  haveI : QH.Normal := by
    simpa [QH] using hA1.Q_normal_in_H
  have hNH_eq : NH = QH ⊔ KWH := by
    change N.subgroupOf H = Q.subgroupOf H ⊔ KW.subgroupOf H
    rw [← Subgroup.subgroupOf_sup hA1.Q_le_H hKWleH]
    simp [N, KW, sup_assoc]
  have hdisjH : Disjoint NH PH := by
    rw [Subgroup.disjoint_def]
    intro x hxN hxP
    have hxSup : x ∈ QH ⊔ KWH := by
      rw [← hNH_eq]
      exact hxN
    rcases Subgroup.mem_sup_of_normal_left.mp hxSup with
      ⟨qH, hqQ, kwH, hkwKW, hqkw⟩
    have hxPG : (x : G) ∈ P := by
      simpa [PH, Subgroup.mem_subgroupOf] using hxP
    have hkwKWG : (kwH : G) ∈ KW := by
      simpa [KWH, Subgroup.mem_subgroupOf] using hkwKW
    have hqQG : (qH : G) ∈ Q := by
      simpa [QH, Subgroup.mem_subgroupOf] using hqQ
    have hqkwG : (qH : G) * (kwH : G) = (x : G) :=
      congrArg Subtype.val hqkw
    have hqD : (qH : G) ∈ D := by
      have hq_eq : (qH : G) = (x : G) * (kwH : G)⁻¹ := by
        rw [← hqkwG]
        simp [mul_assoc]
      rw [hq_eq]
      exact D.mul_mem (hPleD hxPG) (D.inv_mem (hKWleD hkwKWG))
    have hqOne : (qH : G) = 1 :=
      (Subgroup.disjoint_def.mp hA1.Q_disjoint_D) hqQG hqD
    rw [hqOne, one_mul] at hqkwG
    have hxKW : (x : G) ∈ KW := hqkwG ▸ hkwKWG
    have hxOne : (x : G) = 1 :=
      (Subgroup.disjoint_def.mp hKWdisjP) hxKW hxPG
    exact Subtype.ext hxOne
  have hNsupP : N ⊔ P = H := by
    calc
      N ⊔ P = Q ⊔ (K ⊔ (W ⊔ P)) := by
        simp only [N]
        ac_rfl
      _ = Q ⊔ (K ⊔ V) := by rw [hWsupP]
      _ = Q ⊔ D := by rw [chapter2_K_sup_V_eq_D H D Q K V W Q0 S Q1 t hsec]
      _ = H := hA1.Q_sup_D
  have hsupH : NH ⊔ PH = ⊤ := by
    change N.subgroupOf H ⊔ P.subgroupOf H = ⊤
    rw [← Subgroup.subgroupOf_sup hNleH hPleH, hNsupP]
    exact Subgroup.subgroupOf_self H
  refine ⟨hNnormalH, ?_⟩
  letI : NH.Normal := hNnormalH
  exact isComplement'_of_disjoint_sup_eq_top_of_normal NH PH hdisjH hsupH

/-- The exact transfer conclusion printed in Claim (9), proved from the source transversal
`{1} ∪ {q * t | q ∈ Q}` and Hypothesis B2. -/
public theorem chapter2_transfer_p_dvd_Q_card_succ
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
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p)) :
    p ∣ Nat.card Q + 1 := by
  classical
  let hsec := hch.section3.section2
  let hA1 := hsec.hA.A1
  let N : Subgroup G := Q ⊔ K ⊔ W
  rcases chapter2_claim9_normal_complement
      H D Q K V W Q0 S Q1 P t s p hch with ⟨hN, hcomp⟩
  let NH : Subgroup H := N.subgroupOf H
  letI : NH.Normal := hN
  have hVleD : V ≤ D :=
    PFchapter1section2.proposition_3_V_le_D H D Q K V W Q0 S Q1 t hsec
  have hPleH : P ≤ H :=
    hch.B1.P_le_V.trans (hVleD.trans hA1.D_le_H)
  let PH : Subgroup H := P.subgroupOf H
  have hPHcard : Nat.card PH = p := by
    rw [show Nat.card PH = Nat.card P by
      simpa [PH] using natCard_subgroupOf_eq P H hPleH]
    exact hch.B1.P_card
  letI : Fact p.Prime := ⟨hch.B1.p_prime⟩
  haveI : IsCyclic PH := isCyclic_of_prime_card hPHcard
  letI : CommGroup PH := IsCyclic.commGroup
  let proj : H →* PH :=
    hcomp.symm.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' NH)
  let τ : G →* PH := MonoidHom.transfer proj
  have hτone : τ = 1 :=
    chapter2_claim9_hom_eq_one_of_prime_target
      p hch.B1.p_prime hPHcard hch.B2 τ
  haveI : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial, hch.B1.P_card]
    exact hch.B1.p_prime.one_lt
  obtain ⟨u, hu⟩ : ∃ u : P, u ≠ 1 := exists_ne 1
  let uH : H := ⟨(u : G), hPleH u.property⟩
  let uPH : PH := ⟨uH, u.property⟩
  have huPHne : uPH ≠ 1 := by
    intro h
    apply hu
    apply Subtype.ext
    have hv := congrArg (fun z : PH => (((z : H) : G))) h
    simpa [uPH, uH] using hv
  have huPHpow : uPH ^ p = 1 := by
    simpa [hPHcard] using (pow_card_eq_one' (x := uPH))
  have huPHorder : orderOf uPH = p :=
    orderOf_eq_prime_iff.mpr ⟨huPHpow, huPHne⟩
  have hproj_u : proj uH = uPH := by
    simpa [proj, uH, uPH] using
      (quotientMulEquiv_mk_apply_of_isComplement' hcomp.symm uPH)
  let T : H.LeftTransversal := chapter2_claim9_sourceLeftTransversal H D Q t hA1
  have hsmul :
      (u : G) • T = chapter2_claim9_rightTranslateLeftTransversal T uH := by
    simpa [T, uH] using
      (chapter2_claim9_smul_sourceLeftTransversal_eq_rightTranslate
        H D Q P V t (u : G) hA1 (hPleH u.property) hsec.V_eq
          hch.B1.P_le_V u.property)
  have hτpow : τ (u : G) = uPH ^ H.index := by
    calc
      τ (u : G) = Subgroup.leftTransversals.diff proj T ((u : G) • T) :=
        MonoidHom.transfer_def proj T (u : G)
      _ = Subgroup.leftTransversals.diff proj T
          (chapter2_claim9_rightTranslateLeftTransversal T uH) := by rw [hsmul]
      _ = Subgroup.leftTransversals.diff proj T T * (proj uH) ^ H.index :=
        chapter2_claim9_diff_rightTranslate proj T T uH
      _ = uPH ^ H.index := by rw [Subgroup.leftTransversals.diff_self, hproj_u, one_mul]
  have huIndex : uPH ^ H.index = 1 := by
    have h := DFunLike.congr_fun hτone (u : G)
    rw [hτpow] at h
    simpa using h
  have hpIndex : p ∣ H.index := by
    rw [← huPHorder]
    exact orderOf_dvd_of_pow_eq_one huIndex
  haveI : MulAction.IsMultiplyPretransitive G Ω 2 := hA1.two_transitive
  haveI : MulAction.IsPretransitive G Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨alpha, hHpoint⟩ := hA1.point_stabilizer
  have hHindex : H.index = Nat.card Ω := by
    rw [hHpoint]
    exact MulAction.index_stabilizer_of_transitive (G := G) (x := alpha)
  have hOmega : Nat.card Ω = Nat.card Q + 1 :=
    hypothesisA1_card_space_eq_card_Q_add_one_of_hypothesis H D Q t hA1
  rwa [hHindex, hOmega] at hpIndex

/- Claim (9): transfer computation proving `p` divides the near-field order. -/
private theorem chapter2_claim9_p_dvd_field_order
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p ell : ℕ)
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
    (_hell : orderOf (s * t) = ell) :
    p ∣ Nat.card (nearFieldStar Q P) + 1 := by
  letI : Fact (Nat.Prime p) := ⟨hch.B1.p_prime⟩
  have hQcard :
      Nat.card Q = Nat.card (nearFieldStar Q P) ^ p := by
    simpa [nearFieldStar] using
      claim_4 H D Q K V W Q0 S Q1 P t s p hch
  have hpQ : p ∣ Nat.card Q + 1 :=
    chapter2_transfer_p_dvd_Q_card_succ
      H D Q K V W Q0 S Q1 P t s p hch
  have hcast :
      ((Nat.card (nearFieldStar Q P) + 1 : ℕ) : ZMod p) = 0 := by
    calc
      ((Nat.card (nearFieldStar Q P) + 1 : ℕ) : ZMod p) =
          (Nat.card (nearFieldStar Q P) : ZMod p) ^ p + 1 := by
            simp [ZMod.pow_card]
      _ = ((Nat.card (nearFieldStar Q P) ^ p + 1 : ℕ) : ZMod p) := by
            simp
      _ = ((Nat.card Q + 1 : ℕ) : ZMod p) := by rw [hQcard]
      _ = 0 := (ZMod.natCast_eq_zero_iff (Nat.card Q + 1) p).2 hpQ
  exact
    (ZMod.natCast_eq_zero_iff (Nat.card (nearFieldStar Q P) + 1) p).1 hcast

/- Claim (9): `ell = orderOf (s*t)` is the near-field characteristic prime. -/
private theorem chapter2_claim9_characteristic_prime
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p ell : ℕ)
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
    (hell : orderOf (s * t) = ell) :
    Nat.Prime ell := by
  have h2b := claim_2_b H D Q K V W Q0 S Q1 P t s p hch
  dsimp only at h2b
  rcases h2b with
    ⟨_hNcore, _hnormal, _quotientAction, _hsmul, _hAbar,
      F, hF, hFfinite, hFnontrivial, _unitEquiv, _hPO, hcharacteristic⟩
  letI : PFAppendixII.RightNearField F := hF
  letI : Finite F := hFfinite
  letI : Nontrivial F := hFnontrivial
  have hprime :
      Nat.Prime (addOrderOf (1 : F)) :=
    PFAppendixII.rightNearField_addOrderOf_one_prime
  rw [hcharacteristic, hell] at hprime
  exact hprime

/- Claim (9): the near-field order is a positive power of its characteristic. -/
private theorem chapter2_claim9_field_order_prime_power
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p ell : ℕ)
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
    (hell : orderOf (s * t) = ell) :
    ∃ a : ℕ, 0 < a ∧ Nat.card (nearFieldStar Q P) + 1 = ell ^ a := by
  have h2b := claim_2_b H D Q K V W Q0 S Q1 P t s p hch
  dsimp only at h2b
  rcases h2b with
    ⟨_hNcore, _hnormal, _quotientAction, _hsmul, _hAbar,
      F, hF, hFfinite, hFnontrivial, unitEquiv, _hPO, hcharacteristic⟩
  letI : PFAppendixII.RightNearField F := hF
  letI : Finite F := hFfinite
  letI : Nontrivial F := hFnontrivial
  obtain ⟨a, hFcard⟩ :=
    PFAppendixII.rightNearField_natCard_eq_addOrderOf_one_pow (F := F)
  have hFgt : 1 < Nat.card F := by
    letI : Fintype F := Fintype.ofFinite F
    simpa [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F)
  have ha_ne : a ≠ 0 := by
    intro ha
    subst a
    simp at hFcard
    omega
  have hUnitsCard :
      Nat.card (nearFieldStar Q P) = Nat.card Fˣ := by
    simpa [nearFieldStar] using Nat.card_congr unitEquiv.toEquiv
  refine ⟨a, Nat.pos_of_ne_zero ha_ne, ?_⟩
  calc
    Nat.card (nearFieldStar Q P) + 1 = Nat.card Fˣ + 1 := by rw [hUnitsCard]
    _ = Nat.card F := (Nat.card_eq_card_units_add_one F).symm
    _ = addOrderOf (1 : F) ^ a := hFcard
    _ = ell ^ a := by rw [hcharacteristic, hell]

public theorem claim_9
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p ℓ : ℕ)
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
    (hell : orderOf (s * t) = ℓ) :
    p = ℓ := by
  have hell_prime : Nat.Prime ℓ :=
    chapter2_claim9_characteristic_prime H D Q K V W Q0 S Q1 P t s p ℓ hch hell
  rcases chapter2_claim9_field_order_prime_power
      H D Q K V W Q0 S Q1 P t s p ℓ hch hell with
    ⟨a, _ha_pos, hStarComm_order⟩
  have hp_dvd : p ∣ ℓ ^ a := by
    simpa [hStarComm_order] using
      chapter2_claim9_p_dvd_field_order H D Q K V W Q0 S Q1 P t s p ℓ hch hell
  have hp_eq_ℓ : p = ℓ :=
    Nat.prime_eq_prime_of_dvd_pow hch.B1.p_prime hell_prime hp_dvd
  exact hp_eq_ℓ

end PFchapter2
end CFSG.BenderSuzuki


