module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.LinearAlgebra.Projectivization.Action
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.theorem_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter3section1.theorem_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter3section1.proposition
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.AppendixIInput
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter3section2.proposition
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter3section3.proposition
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section3.corollary_1_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section4.case_v_ne_w

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki

open PFchapter1section1 PFchapter1section2 PFchapter1section3 PFAppendixIII MatrixGroups
open scoped LinearAlgebra.Projectivization

universe u v

/-!
# Peterfalvi, Part II, Suzuki theorem
-/

private theorem endpoint_D_le_K_sup_V
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : HypothesisA G Omega H D Q t ∧
      K ≤ D ∧
        (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
          V = peterfalviV D t ∧
            W ≤ V ∧
              W = peterfalviW V (K : Set G) ∧
                Q0 ≤ Q ∧
                  (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
                    S ≤ Q ∧
                      Q1 ≤ Q ∧
                        (∃ P : Sylow 2 Q,
                          S = (P : Subgroup Q).map Q.subtype) ∧
                          Odd (Nat.card Q1) ∧
                            Disjoint S Q1 ∧
                              (∀ a : G, a ∈ S → ∀ b : G, b ∈ Q1 →
                                a * b = b * a) ∧
                                S ⊔ Q1 = Q) :
    D ≤ K ⊔ V := by
  classical
  have hconjD : ∀ d : G, d ∈ D → rightConjugateElem d t ∈ D := by
    intro d hd
    have htinv : t⁻¹ = t := hsec.hA.A1.involution_t.inv_eq_self
    have htt : t * t = 1 := by
      simpa [pow_two] using hsec.hA.A1.involution_t.sq_eq_one
    have hd' : d ∈ H ⊓ rightConjugate H t := by
      simpa [hsec.hA.A1.D_eq] using hd
    rw [hsec.hA.A1.D_eq]
    refine ⟨?_, ?_⟩
    · rcases hd'.2 with ⟨h, hhH, hhd⟩
      have tht : t * h * t = d := by
        simpa [MulAut.conj, htinv, mul_assoc] using hhd
      have hconj_eq : rightConjugateElem d t = h := by
        calc
          rightConjugateElem d t = t * d * t := by
            simp [rightConjugateElem, htinv]
          _ = t * (t * h * t) * t := by rw [← tht]
          _ = (t * t) * h * (t * t) := by simp [mul_assoc]
          _ = h := by simp [htt]
      simpa [hconj_eq] using hhH
    · refine ⟨d, hd'.1, ?_⟩
      simp [rightConjugateElem]
  have htNormD : t ∈ Subgroup.normalizer (D : Set G) := by
    have htinv : t⁻¹ = t := hsec.hA.A1.involution_t.inv_eq_self
    have htt : t * t = 1 := by
      simpa [pow_two] using hsec.hA.A1.involution_t.sq_eq_one
    rw [Subgroup.mem_normalizer_iff'']
    intro d
    constructor
    · intro hd
      simpa [rightConjugateElem, htinv] using hconjD d hd
    · intro hd
      have hmem := hconjD (t⁻¹ * d * t) hd
      have htd : t * (t * d) = d := by
        calc
          t * (t * d) = (t * t) * d := by simp [mul_assoc]
          _ = d := by rw [htt]; simp
      have hmem' : t * (t * d) ∈ D := by
        simpa [rightConjugateElem, htinv, htt, mul_assoc] using hmem
      simpa [htd] using hmem'
  have hdecomp :=
    (PFchapter1section1.lemma_a t D hsec.hA.A1.involution_t
      hsec.hA.A1.D_odd htNormD).1
  intro d hdD
  obtain ⟨p, _hp, hp_eq⟩ := hdecomp.surjOn hdD
  rcases p with ⟨v, k⟩
  have hvV : (v : G) ∈ V := by
    rw [hsec.V_eq]
    exact v.property
  have hkK : (k : G) ∈ K := (hsec.K_def (k : G)).2 k.property
  rw [← hp_eq]
  exact (K ⊔ V).mul_mem (Subgroup.mem_sup_right hvV) (Subgroup.mem_sup_left hkK)

private theorem endpoint_eq_one_of_sq_eq_one_of_odd_card
    {X : Type*} [Group X] [Finite X] (hXodd : Odd (Nat.card X))
    (x : X) (hx : x ^ 2 = 1) : x = 1 := by
  have hord_dvd_two : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have hcop : Nat.Coprime 2 (Nat.card X) := hXodd.coprime_two_left
  have hord_dvd_one : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hord_dvd_two (orderOf_dvd_natCard x)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord_dvd_one)

private theorem exists_canonical_maps
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Omega H D Q t) :
    ∃ f g h : G → G,
      (∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1) ∧
        (∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1) ∧
          (∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D) ∧
            (∀ x : G, x ∈ Q → x ≠ 1 →
              t * x * t = g x * h x * t * f x) := by
  classical
  have htinv : t⁻¹ = t := hA1.involution_t.inv_eq_self
  have htt : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  have hdecomp : ∀ y : G, y ∈ H →
      ∃ q : Q, ∃ d : D, (q : G) * (d : G) = y := by
    intro y hy
    let QH : Subgroup H := Q.subgroupOf H
    let DH : Subgroup H := D.subgroupOf H
    haveI : QH.Normal := by
      simpa [QH] using hA1.Q_normal_in_H
    have hsupH : QH ⊔ DH = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (A := Q) (A' := D) (B := H)
          hA1.Q_le_H hA1.D_le_H]
      rw [hA1.Q_sup_D, Subgroup.subgroupOf_self]
    have hySup : (⟨y, hy⟩ : H) ∈ QH ⊔ DH := by
      rw [hsupH]
      trivial
    rcases (Subgroup.mem_sup_of_normal_left
        (s := QH) (t := DH) (x := (⟨y, hy⟩ : H))).mp hySup with
      ⟨q, hq, d, hd, hqd⟩
    refine ⟨⟨q, ?_⟩, ⟨d, ?_⟩, ?_⟩
    · simpa [QH, Subgroup.mem_subgroupOf] using hq
    · simpa [DH, Subgroup.mem_subgroupOf] using hd
    · simpa using congrArg Subtype.val hqd
  have hcanonical : ∀ x : G, x ∈ Q → x ≠ 1 →
      ∃ gx dx fx : G,
        gx ∈ Q ∧ gx ≠ 1 ∧ dx ∈ D ∧ fx ∈ Q ∧ fx ≠ 1 ∧
          t * x * t = gx * dx * t * fx := by
    intro x hxQ hxne
    have hyRight : t * x * t ∈ rightConjugate H t := by
      have hmem := PFchapter4section1.rightConjugateElem_mem_rightConjugate
        (t := t) (hA1.Q_le_H hxQ)
      simpa [rightConjugateElem, htinv] using hmem
    have hyNotH : t * x * t ∉ H := by
      intro hyH
      have hyD : t * x * t ∈ D := by
        rw [hA1.D_eq]
        exact ⟨hyH, hyRight⟩
      have hxD' := PFchapter4section1.rightConjugateElem_mem_D
        htinv hA1.D_eq hyD
      have hxD : x ∈ D := by
        have hback : rightConjugateElem (t * x * t) t = x := by
          calc
            rightConjugateElem (t * x * t) t = t * (t * x * t) * t := by
              simp [rightConjugateElem, htinv]
            _ = (t * t) * x * (t * t) := by group
            _ = x := by rw [htt]; simp
        simpa [hback] using hxD'
      exact hxne <| (Subgroup.disjoint_def.mp hA1.Q_disjoint_D) hxQ hxD
    obtain ⟨p, hp, _hp_unique⟩ :=
      PFchapter1section1.proposition_4_a H D Q t hA1 (t * x * t) hyNotH
    obtain ⟨gx, dx, hgdx⟩ := hdecomp p.1 p.1.property
    have heq : t * x * t = (gx : G) * (dx : G) * t * (p.2 : G) := by
      calc
        t * x * t = (p.1 : G) * t * (p.2 : G) := hp
        _ = ((gx : G) * (dx : G)) * t * (p.2 : G) := by rw [hgdx]
        _ = (gx : G) * (dx : G) * t * (p.2 : G) := by rfl
    have hfxne : (p.2 : G) ≠ 1 := by
      intro hfx
      have htxeq : t * x = (gx : G) * (dx : G) := by
        have hmul := congrArg (fun z : G => z * t) heq
        simpa [hfx, htt, mul_assoc] using hmul
      apply hA1.t_not_mem_H
      have hteq : t = (t * x) * x⁻¹ := by group
      rw [hteq, htxeq]
      exact H.mul_mem
        (H.mul_mem (hA1.Q_le_H gx.property) (hA1.D_le_H dx.property))
        (H.inv_mem (hA1.Q_le_H hxQ))
    have hgxne : (gx : G) ≠ 1 := by
      intro hgx
      have hxteq : x * t = t * (dx : G) * t * (p.2 : G) := by
        calc
          x * t = t * (t * x * t) := by
            calc
              x * t = (t * t) * x * t := by rw [htt]; simp
              _ = t * (t * x * t) := by group
          _ = t * ((gx : G) * (dx : G) * t * (p.2 : G)) := by rw [heq]
          _ = t * (dx : G) * t * (p.2 : G) := by rw [hgx]; simp only [one_mul]; group
      have htdtD : t * (dx : G) * t ∈ D := by
        have hmem := PFchapter4section1.rightConjugateElem_mem_D
          htinv hA1.D_eq dx.property
        simpa [rightConjugateElem, htinv] using hmem
      apply hA1.t_not_mem_H
      have hteq : t = x⁻¹ * (x * t) := by group
      have hxtH : x * t ∈ H := by
        rw [hxteq]
        exact H.mul_mem (hA1.D_le_H htdtD) (hA1.Q_le_H p.2.property)
      rw [hteq]
      exact H.mul_mem (H.inv_mem (hA1.Q_le_H hxQ)) hxtH
    exact ⟨gx, dx, p.2, gx.property, hgxne, dx.property,
      p.2.property, hfxne, heq⟩
  have hall : ∀ x : G, ∃ fx gx dx : G,
      (x ∈ Q → x ≠ 1 → fx ∈ Q ∧ fx ≠ 1) ∧
        (x ∈ Q → x ≠ 1 → gx ∈ Q ∧ gx ≠ 1) ∧
          (x ∈ Q → x ≠ 1 → dx ∈ D) ∧
            (x ∈ Q → x ≠ 1 → t * x * t = gx * dx * t * fx) := by
    intro x
    by_cases hxQ : x ∈ Q
    · by_cases hxne : x ≠ 1
      · obtain ⟨gx, dx, fx, hgxQ, hgxne, hdxD, hfxQ, hfxne, heq⟩ :=
          hcanonical x hxQ hxne
        exact ⟨fx, gx, dx,
          fun _ _ => ⟨hfxQ, hfxne⟩,
          fun _ _ => ⟨hgxQ, hgxne⟩,
          fun _ _ => hdxD,
          fun _ _ => heq⟩
      · exact ⟨1, 1, 1,
          fun _ hx => (hxne hx).elim,
          fun _ hx => (hxne hx).elim,
          fun _ hx => (hxne hx).elim,
          fun _ hx => (hxne hx).elim⟩
    · exact ⟨1, 1, 1,
        fun hx _ => (hxQ hx).elim,
        fun hx _ => (hxQ hx).elim,
        fun hx _ => (hxQ hx).elim,
        fun hx _ => (hxQ hx).elim⟩
  choose f g h hf hg hh heq using hall
  exact ⟨f, g, h, hf, hg, hh, heq⟩

private theorem endpoint_normal_proper_of_carrier
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q K V W Q0 S Q1 L : Subgroup G) (t : G)
    (hsec : HypothesisA G Omega H D Q t ∧
      K ≤ D ∧
        (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
          V = peterfalviV D t ∧
            W ≤ V ∧
              W = peterfalviW V (K : Set G) ∧
                Q0 ≤ Q ∧
                  (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
                    S ≤ Q ∧
                      Q1 ≤ Q ∧
                        (∃ P : Sylow 2 Q,
                          S = (P : Subgroup Q).map Q.subtype) ∧
                          Odd (Nat.card Q1) ∧
                            Disjoint S Q1 ∧
                              (∀ a : G, a ∈ S → ∀ b : G, b ∈ Q1 →
                                a * b = b * a) ∧
                                S ⊔ Q1 = Q)
    (hSQ : S = Q) (hVne : V ≠ ⊥)
    (hLcarrier : (L : Set G) =
      {x | ∃ a ∈ S, ∃ b ∈ K, x = a * b} ∪
        {x | ∃ s₁ ∈ S, ∃ k ∈ K, ∃ s₂ ∈ S, x = s₁ * k * t * s₂}) :
    L.Normal ∧ L ≠ ⊥ ∧ L ≠ ⊤ := by
  classical
  have hS_le_L : S ≤ L := by
    intro a ha
    change a ∈ (L : Set G)
    rw [hLcarrier]
    left
    exact ⟨a, ha, 1, K.one_mem, by simp⟩
  have hK_le_L : K ≤ L := by
    intro b hb
    change b ∈ (L : Set G)
    rw [hLcarrier]
    left
    exact ⟨1, S.one_mem, b, hb, by simp⟩
  have htL : t ∈ L := by
    change t ∈ (L : Set G)
    rw [hLcarrier]
    right
    exact ⟨1, S.one_mem, 1, K.one_mem, 1, S.one_mem, by simp⟩
  have hD_le_KV : D ≤ K ⊔ V :=
    endpoint_D_le_K_sup_V H D Q K V W Q0 S Q1 t hsec
  have hQ_le_L : Q ≤ L := by
    rw [← hSQ]
    exact hS_le_L
  have hH_le_LV : H ≤ L ⊔ V := by
    rw [← hsec.hA.A1.Q_sup_D]
    refine sup_le (hQ_le_L.trans le_sup_left) ?_
    exact hD_le_KV.trans <| sup_le (hK_le_L.trans le_sup_left) le_sup_right
  have hLV_top : L ⊔ V = ⊤ := by
    apply top_unique
    intro x _hx
    by_cases hxH : x ∈ H
    · exact hH_le_LV hxH
    · obtain ⟨p, hp, _hp_unique⟩ :=
        PFchapter1section1.proposition_4_a H D Q t hsec.hA.A1 x hxH
      rw [hp]
      exact (L ⊔ V).mul_mem
        ((L ⊔ V).mul_mem (hH_le_LV p.1.property) (Subgroup.mem_sup_left htL))
        (hH_le_LV (hsec.hA.A1.Q_le_H p.2.property))
  have hV_le_D : V ≤ D := by
    intro v hv
    have hv' : v ∈ peterfalviV D t := by
      rw [← hsec.V_eq]
      exact hv
    exact hv'.1
  have hD_le_normalizer_K : D ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsec.K_le_D).mp
      (PFchapter1section2.proposition_2 H D Q K V W Q0 S Q1 t hsec).2
  have hH_le_normalizer_Q : H ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsec.hA.A1.Q_le_H).mp
      hsec.hA.A1.Q_normal_in_H
  have hV_le_normalizer_S : V ≤ Subgroup.normalizer (S : Set G) := by
    intro v hv
    rw [hSQ]
    exact hH_le_normalizer_Q (hsec.hA.A1.D_le_H (hV_le_D hv))
  have hconj_mem_L : ∀ v : G, v ∈ V → ∀ x : G, x ∈ L → v * x * v⁻¹ ∈ L := by
    intro v hv x hx
    have hvPet : v ∈ peterfalviV D t := by
      rw [← hsec.V_eq]
      exact hv
    have hvt : Commute v t :=
      Subgroup.mem_centralizer_singleton_iff.mp hvPet.2
    have htfix : v * t * v⁻¹ = t := by
      calc
        v * t * v⁻¹ = t * v * v⁻¹ := by rw [hvt.eq]
        _ = t := by simp
    have hx' : x ∈ (L : Set G) := hx
    rw [hLcarrier] at hx'
    change v * x * v⁻¹ ∈ (L : Set G)
    rw [hLcarrier]
    rcases hx' with ⟨a, ha, b, hb, rfl⟩ | ⟨s₁, hs₁, k, hk, s₂, hs₂, rfl⟩
    · left
      refine ⟨v * a * v⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hV_le_normalizer_S hv) a).mp ha,
        v * b * v⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hD_le_normalizer_K (hV_le_D hv)) b).mp hb,
        ?_⟩
      group
    · right
      refine ⟨v * s₁ * v⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hV_le_normalizer_S hv) s₁).mp hs₁,
        v * k * v⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hD_le_normalizer_K (hV_le_D hv)) k).mp hk,
        v * s₂ * v⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hV_le_normalizer_S hv) s₂).mp hs₂,
        ?_⟩
      calc
        v * (s₁ * k * t * s₂) * v⁻¹ =
            (v * s₁ * v⁻¹) * (v * k * v⁻¹) *
              (v * t * v⁻¹) * (v * s₂ * v⁻¹) := by group
        _ = (v * s₁ * v⁻¹) * (v * k * v⁻¹) * t *
              (v * s₂ * v⁻¹) := by rw [htfix]
  have hV_le_normalizer_L : V ≤ Subgroup.normalizer (L : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconj_mem_L v hv x
    · intro hx
      have hback := hconj_mem_L v⁻¹ (V.inv_mem hv) (v * x * v⁻¹) hx
      simpa [mul_assoc] using hback
  have hLnormal : L.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hLV_top]
    exact sup_le L.le_normalizer hV_le_normalizer_L
  have hLne_bot : L ≠ ⊥ := by
    intro hLbot
    have : t = 1 := by
      rw [hLbot] at htL
      exact Subgroup.mem_bot.mp htL
    exact hsec.hA.A1.involution_t.ne_one this
  obtain ⟨v, hvne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hv_not_L : (v : G) ∉ L := by
    intro hvL
    have hvL' : (v : G) ∈ (L : Set G) := hvL
    rw [hLcarrier] at hvL'
    rcases hvL' with ⟨a, ha, b, hb, hvab⟩ | ⟨s₁, hs₁, k, hk, s₂, hs₂, hvskts⟩
    · have haD : a ∈ D := by
        have haeq : a = (v : G) * b⁻¹ := by
          rw [hvab]
          group
        rw [haeq]
        exact D.mul_mem (hV_le_D v.property) (D.inv_mem (hsec.K_le_D hb))
      have haone : a = 1 :=
        (Subgroup.disjoint_def.mp hsec.hA.A1.Q_disjoint_D)
          (by simpa [← hSQ] using ha) haD
      have hvb : (v : G) = b := by simpa [haone] using hvab
      have hvPet : (v : G) ∈ peterfalviV D t := by
        rw [← hsec.V_eq]
        exact v.property
      have hvfixed : rightConjugateElem (v : G) t = (v : G) := by
        have hvt : Commute (v : G) t :=
          Subgroup.mem_centralizer_singleton_iff.mp hvPet.2
        calc
          rightConjugateElem (v : G) t = t⁻¹ * ((v : G) * t) := by
            simp [rightConjugateElem, mul_assoc]
          _ = t⁻¹ * (t * (v : G)) := by rw [hvt.eq]
          _ = (v : G) := by simp
      have hbfix : rightConjugateElem b t = b := by simpa [hvb] using hvfixed
      have hbanti : rightConjugateElem b t = b⁻¹ := (hsec.K_def b).mp hb |>.2
      have hbinv : b = b⁻¹ := hbfix.symm.trans hbanti
      have hbsq : b ^ 2 = 1 := by
        calc
          b ^ 2 = b * b := by rw [pow_two]
          _ = b⁻¹ * b := congrArg (fun x => x * b) hbinv
          _ = 1 := by simp
      let bD : D := ⟨b, hsec.K_le_D hb⟩
      have hbDsq : bD ^ 2 = 1 := by
        apply Subtype.ext
        simpa [bD] using hbsq
      have hbDOne : bD = 1 :=
        endpoint_eq_one_of_sq_eq_one_of_odd_card hsec.hA.A1.D_odd bD hbDsq
      have hbOne : b = 1 := by simpa [bD] using congrArg Subtype.val hbDOne
      apply hvne
      apply Subtype.ext
      simp [hvb, hbOne]
    · apply hsec.hA.A1.t_not_mem_H
      have hteq : t = k⁻¹ * s₁⁻¹ * (v : G) * s₂⁻¹ := by
        rw [hvskts]
        group
      rw [hteq]
      exact H.mul_mem
        (H.mul_mem
          (H.mul_mem
            (H.inv_mem (hsec.hA.A1.D_le_H (hsec.K_le_D hk)))
            (H.inv_mem (hsec.hA.A1.Q_le_H (by simpa [← hSQ] using hs₁))))
          (hsec.hA.A1.D_le_H (hV_le_D v.property)))
        (H.inv_mem (hsec.hA.A1.Q_le_H (by simpa [← hSQ] using hs₂)))
  have hLne_top : L ≠ ⊤ := by
    intro hLtop
    apply hv_not_L
    rw [hLtop]
    trivial
  exact ⟨hLnormal, hLne_bot, hLne_top⟩

public theorem suzuki
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA : HypothesisA G Ω H D Q t) :
    ∃ (L : Subgroup G) (_ : L.Normal) (q : ℕ),
  Odd (Nat.card (G ⧸ L)) ∧ (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
    ((∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ k)
          (eL : L ≃* PSL2BinaryMatrixGroup k)
          (rho : PSL2BinaryMatrixGroup k →*
            Equiv.Perm (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)))
          (eΩ : Ω ≃ ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)),
        (∀ A : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField k),
          ∀ z : ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k),
            rho (QuotientGroup.mk'
              (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
                (BinaryGaloisField k))) A) z =
              Matrix.SpecialLinearGroup.toLin' A • z) ∧
        ∀ l : L, ∀ ω : Ω,
          eΩ ((l : G) • ω) = rho (eL l) (eΩ ω)) ∨
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
        ∃ (eL : L ≃* SuzukiMatrixGroup k)
            (rho : SuzukiMatrixGroup k →* Equiv.Perm {z // z ∈ O})
            (eΩ : Ω ≃ {z // z ∈ O}),
          (∀ g : SuzukiMatrixGroup k, ∀ z : {z // z ∈ O},
            ((rho g z : {z // z ∈ O}) : ℙ K (Fin 4 → K)) =
              (Matrix.GeneralLinearGroup.toLin
                (g : GL (Fin 4) K)).toLinearEquiv •
                  (z : ℙ K (Fin 4 → K))) ∧
          ∀ l : L, ∀ ω : Ω,
            eΩ ((l : G) • ω) = rho (eL l) (eΩ ω)) ∨
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
        ∃ (eL : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
            (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm X)
            (eΩ : Ω ≃ X),
          (∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : X,
            ∀ M : J.specialSubgroup,
              Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) E) =
                  (g : Matrix.ProjGenLinGroup (Fin 3) E) →
                ((rho g z : X) : P) =
                  (Matrix.GeneralLinearGroup.toLin
                    (M : GL (Fin 3) E)).toLinearEquiv • (z : P)) ∧
          ∀ l : L, ∀ ω : Ω,
            eΩ ((l : G) • ω) = rho (eL l) (eΩ ω))) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (L : Type u) [Group L] [Finite L],
      ∀ (OmegaL : Type v) [MulAction L OmegaL] [Finite OmegaL]
        (HL DL QL : Subgroup L) (tL : L),
        Nat.card L = n →
          HypothesisA L OmegaL HL DL QL tL →
            suzukiConclusion.{u, v} L OmegaL
  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n ih L _ _ OmegaL _ _ HL DL QL tL hcard hAL
    obtain ⟨Q0, hQ0_le, hQ0_def, hQ0_comm, hQ0_sq⟩ :=
      proposition_1_c_exists_Q0 HL DL QL tL hAL
    obtain ⟨S, Q1, hS_le, hQ1_le, hS_sylow, hQ1_odd, hdisjoint, hcomm,
        hdecomp⟩ :=
      proposition_1_c_exists_S_Q1 HL DL QL tL hAL
    obtain ⟨K, V, W, hK_le, hK_def, hV_eq, hW_le, hW_eq, _hK_cyclic,
        _hK_normal⟩ :=
      proposition_2_exists_K HL DL QL Q0 tL hAL hQ0_def hQ0_comm hQ0_sq
    obtain ⟨s, hsH, hsI, hs_structure, _hsQ0, _hV_stab, _hVfix⟩ :=
      _root_.CFSG.BenderSuzuki.PFchapter1section2.peterfalvi_chapter1_section2_proposition_3_distinguished_involution
        HL DL QL V Q0 tL hAL.A1 hV_eq hQ0_def
    have hsec :=
      show ((HypothesisA L OmegaL HL DL QL tL ∧
        K ≤ DL ∧
          (∀ x : L, x ∈ K ↔ x ∈ DL ∧ rightConjugateElem x tL = x⁻¹) ∧
            V = peterfalviV DL tL ∧
              W ≤ V ∧
                W = peterfalviW V (K : Set L) ∧
                  Q0 ≤ QL ∧
                    (∀ x : L, x ∈ Q0 ↔ x = 1 ∨ (x ∈ HL ∧ IsInvolution x)) ∧
                      S ≤ QL ∧
                        Q1 ≤ QL ∧
                          (∃ T : Sylow 2 QL,
                            S = (T : Subgroup QL).map QL.subtype) ∧
                            Odd (Nat.card Q1) ∧
                              Disjoint S Q1 ∧
                                (∀ a : L, a ∈ S → ∀ b : L, b ∈ Q1 →
                                  a * b = b * a) ∧
                                  S ⊔ Q1 = QL) ∧
        s ∈ HL ∧ IsInvolution s ∧
          ∃ r : L, r ∈ QL ∧ tL * s * tL = r⁻¹ * tL * r) from
        ⟨⟨hAL, hK_le, hK_def, hV_eq, hW_le, hW_eq, hQ0_le, hQ0_def,
          hS_le, hQ1_le, hS_sylow, hQ1_odd, hdisjoint, hcomm, hdecomp⟩,
          hsH, hsI, hs_structure⟩
    have hind :
        ∀ (M : Type u) [Group M] [Finite M],
          ∀ (OmegaM : Type v) [MulAction M OmegaM] [Finite OmegaM]
            (HM DM QM : Subgroup M) (tM : M),
            Nat.card M < Nat.card L →
              HypothesisA M OmegaM HM DM QM tM →
                suzukiConclusion.{u, v} M OmegaM := by
      intro M _ _ OmegaM _ _ HM DM QM tM hlt hAM
      have hlt' : Nat.card M < n := by
        rw [← hcard]
        exact hlt
      exact ih (Nat.card M) hlt' M OmegaM HM DM QM tM rfl hAM
    by_cases hV : V = ⊥
    · rcases BenderSuzuki.PFchapter3section1.case_v_eq_bot
          HL DL QL V tL hAL hsec.section2.V_eq hV with
        ⟨q, hq, hq_gt, hmodel⟩
      refine ⟨⊤, inferInstance, q, ?_, hq, hq_gt, ?_⟩
      · simp
      · rcases hmodel with hpsl | hsuzuki
        · exact Or.inl hpsl
        · exact Or.inr (Or.inl hsuzuki)
    by_cases hbad : ∃ (R : Subgroup L) (p : ℕ),
        R ≤ V ∧ Nat.Prime p ∧ Nat.card R = p ∧
          ¬ TwoRankAtLeastTwo (Subgroup.centralizer (R : Set L))
    · rcases hbad with ⟨R, p, hR_le, hp, hRcard, hRrank⟩
      have hB1 : BenderSuzuki.PFchapter2.HypothesisB1 L V R p := by
        refine
          { p_prime := hp
            P_le_V := hR_le
            P_card := hRcard
            centralizer_has_involution := ?_
            centralizer_has_two_rank_one := hRrank }
        exact ⟨tL,
          t_mem_centralizer_of_le_peterfalviV DL V R tL hR_le hsec.section2.V_eq,
          hsec.section2.hA.A1.involution_t⟩
      simpa only [suzukiConclusion] using
        BenderSuzuki.PFchapter2.theorem_b HL DL QL K V W Q0 S Q1 R
          tL s p hsec hind hB1
    · have hC1 : BenderSuzuki.PFchapter3section1.HypothesisC1 L V := by
        refine
          { V_ne_bot := hV
            centralizers_two_rank := ?_ }
        intro R hR ⟨p, hp, hRcard⟩
        by_contra hRrank
        exact hbad ⟨R, p, hR, hp, hRcard, hRrank⟩
      have hQ_two : IsPGroup 2 QL := by
        simpa only [suzukiConclusion] using
          BenderSuzuki.PFchapter3section1.theorem_c.{u, v}
            HL DL QL K V W Q0 S Q1 tL s ⟨hsec, hC1⟩ hind
      have hSQ : S = QL := by
        obtain ⟨T, hS_eq⟩ := hsec.section2.S_sylow_in_Q
        have hT_top : (T : Subgroup QL) = ⊤ :=
          (T.is_maximal' (hQ_two.to_subgroup ⊤) le_top).symm
        rw [hS_eq, hT_top]
        ext q
        constructor
        · rintro ⟨q, _hq, rfl⟩
          exact q.property
        · intro hq
          exact ⟨⟨q, hq⟩, trivial, rfl⟩
      rcases BenderSuzuki.PFchapter3section1.proposition.{u, v}
          HL DL QL K V W Q0 S Q1 tL s ⟨hsec, hC1⟩ hind hSQ with
        hab | hrest
      · let G0 : Subgroup L := psl2GeneratedSubgroup Q0 K tL
        have hlemma := BenderSuzuki.PFchapter1section3.lemma_4
          HL DL QL K V W Q0 S Q1 tL s hsec hind hab.2 hV
        have hG0carrier : (G0 : Set L) =
            {x | ∃ a ∈ S, ∃ b ∈ K, x = a * b} ∪
              {x | ∃ s₁ ∈ S, ∃ k ∈ K, ∃ s₂ ∈ S,
                x = s₁ * k * tL * s₂} := by
          rw [show (G0 : Set L) =
              (psl2GeneratedSubgroup Q0 K tL : Set L) from rfl,
            hlemma.1]
          ext x
          simp only [q0KUnionQ0KtQ0, Set.mem_setOf_eq, Set.mem_union]
          constructor
          · rintro (⟨q, k, hq, hk, hx⟩ | ⟨q, k, q', hq, hk, hq', hx⟩)
            · left
              exact ⟨q, by simpa [hab.1] using hq, k, hk, hx⟩
            · right
              exact ⟨q, by simpa [hab.1] using hq, k, hk,
                q', by simpa [hab.1] using hq', hx⟩
          · rintro (⟨a, ha, b, hb, hx⟩ | ⟨s₁, hs₁, k, hk, s₂, hs₂, hx⟩)
            · left
              exact ⟨a, b, by simpa [hab.1] using ha, hb, hx⟩
            · right
              exact ⟨s₁, k, s₂, by simpa [hab.1] using hs₁, hk,
                by simpa [hab.1] using hs₂, hx⟩
        have hG0 := endpoint_normal_proper_of_carrier
          HL DL QL K V W Q0 S Q1 G0 tL hsec.section2 hSQ hV hG0carrier
        simpa only [suzukiConclusion] using
          BenderSuzuki.PFchapter1section3.proposition_2
            HL DL QL K V W Q0 S Q1 tL s hsec hind ⟨G0, hG0⟩
      · rcases hrest with htypeA | htypeB
        · obtain ⟨G0, hG0carrier⟩ :=
            BenderSuzuki.PFchapter3section2.proposition
              HL DL QL K V W Q0 S Q1 tL s
                ⟨hsec, hC1, htypeA⟩ hSQ
          have hG0 := endpoint_normal_proper_of_carrier
            HL DL QL K V W Q0 S Q1 G0 tL hsec.section2 hSQ hV hG0carrier
          simpa only [suzukiConclusion] using
            BenderSuzuki.PFchapter1section3.proposition_2
              HL DL QL K V W Q0 S Q1 tL s hsec hind ⟨G0, hG0⟩
        · have hC2 : BenderSuzuki.PFchapter3section3.HypothesisC2
              L S W tL s :=
            { S_type_B := htypeB.1
              st_order_three := htypeB.2.1
              W_ne_bot := htypeB.2.2 }
          obtain ⟨f, g, h, hf, hg, hh, hcanonical⟩ :=
            exists_canonical_maps HL DL QL tL hsec.section2.hA.A1
          have hC3 : BenderSuzuki.PFchapter3section3.TypeBChapter3Data
                L K Q0 S W s :=
            BenderSuzuki.PFchapter3section3.proposition.{u, v}
              HL DL QL K V W Q0 S Q1 tL s hsec hC1 hC2 hind hSQ
          by_cases hVW : V = W
          · rcases BenderSuzuki.PFchapter4section3.corollary_1_b.{u, v}
                HL DL QL K V W Q0 S Q1 tL s f g h hsec hC1 hC2 hC3
                  hQ_two hf hg hh hcanonical hVW with
              ⟨N, hN, q, _hN_eq, hodd, hq, hq_gt, hunitary⟩
            exact ⟨N, hN, q, hodd, hq, hq_gt, Or.inr (Or.inr hunitary)⟩
          · simpa only [suzukiConclusion] using
              BenderSuzuki.PFchapter4section4.case_v_ne_w
                HL DL QL K V W Q0 S Q1 tL s f g h hsec hC1 hC2 hC3 hind
                  hQ_two hf hg hh hcanonical hVW
  have hmain : P (Nat.card G) := Nat.strong_induction_on (Nat.card G) hP
  exact hmain G Ω H D Q t rfl hA

end CFSG.BenderSuzuki
