module

public import CFSG.Quasithin.EmptyFaithful.SzF53B2Nat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace SzF53B2

section Amalg

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace B2Setup

theorem exists_conj_V (h : B2Setup H M S) :
    ∃ x' ∈ H, conjSub x' (VZ S M) ≤ conjClosure (VZ S M) H ∧
      ¬ conjSub x' (VZ S M) ≤ pCoreOf 2 M ∧ ⁅VZ S M, conjSub x' (VZ S M)⁆ ≠ ⊥ := by
  obtain ⟨x', hx'H, hx'Qb, hx'M, hnt, hle, hquad⟩ :=
    F112W.exists_conj_of_critDist_eq_two h.amalgamHypV h.V_ne_bot h.crit
  have hVc : VZ S M ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    (h.V_le_center).trans inf_le_right
  refine ⟨x', hx'H, ?_, ?_, hnt⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact mem_conjClosure hx'H hv
  · intro hle'
    apply hnt
    rw [eq_bot_iff]
    refine (Subgroup.commutator_mono le_rfl hle').trans ?_
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hVc).le

theorem sup_eq_S_of (h : B2Setup H M S) {W : Subgroup G} (hWS : W ≤ S) (hWQ : ¬ W ≤ pCoreOf 2 M) :
    pCoreOf 2 M ⊔ W = S := by
  have hQaS : pCoreOf 2 M ≤ S := isSylowTwoOf_pCoreOf_le h.sylow_M
  have hQS2 := h.relIndex_facts.2.1
  have hle2 : pCoreOf 2 M ⊔ W ≤ S := sup_le hQaS hWS
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 M) (pCoreOf 2 M ⊔ W) S le_sup_left hle2
  rw [hQS2] at hmul
  have hne : (pCoreOf 2 M).relIndex (pCoreOf 2 M ⊔ W) ≠ 1 := by
    intro h1'
    exact hWQ (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1'))
  have hdvd : (pCoreOf 2 M).relIndex (pCoreOf 2 M ⊔ W) ∣ 2 := ⟨_, hmul.symm⟩
  have h2' : (pCoreOf 2 M).relIndex (pCoreOf 2 M ⊔ W) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left hne
  rw [h2'] at hmul
  have : (pCoreOf 2 M ⊔ W).relIndex S = 1 := by omega
  exact le_antisymm hle2 (Subgroup.relIndex_eq_one.mp this)

theorem Vb_le_Qb (h : B2Setup H M S) : conjClosure (VZ S M) H ≤ pCoreOf 2 H :=
  F112W.conjClosure_le_pCoreOf_G₂ h.V_le_Qb

theorem sup_eq_S (h : B2Setup H M S) : pCoreOf 2 M ⊔ conjClosure (VZ S M) H = S := by
  obtain ⟨x', hx'H, hV'Vb, hV'Q, -⟩ := h.exists_conj_V
  exact h.sup_eq_S_of ((h.Vb_le_Qb).trans (isSylowTwoOf_pCoreOf_le h.sylow_H))
    (fun hle => hV'Q (hV'Vb.trans hle))

theorem sup_conj_S (h : B2Setup H M S) {x : G} (hx : x ∈ M) (hxS : x ∉ S) :
    S ⊔ conjSub x S = M := by
  have hSM := h.sylow_M.1
  have hxM : conjSub x S ≤ M := by
    have := conjSub_mono x hSM
    rwa [F7.conjSub_eq_of_mem hx] at this
  have hnot : ¬ conjSub x S ≤ S := by
    intro hle
    have heq : conjSub x S = S :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
    exact hxS (h.normalizer_S x hx heq)
  have hle2 : S ⊔ conjSub x S ≤ M := sup_le hSM hxM
  have hmul := Subgroup.relIndex_mul_relIndex S (S ⊔ conjSub x S) M le_sup_left hle2
  rw [h.relIndex_facts.2.2] at hmul
  have hne : S.relIndex (S ⊔ conjSub x S) ≠ 1 := fun h1 =>
    hnot (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1))
  have hdvd : S.relIndex (S ⊔ conjSub x S) ∣ 3 := ⟨_, hmul.symm⟩
  have h3 : S.relIndex (S ⊔ conjSub x S) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne
  rw [h3] at hmul
  have : (S ⊔ conjSub x S).relIndex M = 1 := by omega
  exact le_antisymm hle2 (Subgroup.relIndex_eq_one.mp this)

theorem eq_sup_vBeta (h : B2Setup H M S) {x : G} (hx : x ∈ M) (hxS : x ∉ S) :
    M = pCoreOf 2 M ⊔ conjClosure (VZ S M) H ⊔ conjSub x (conjClosure (VZ S M) H) := by
  have hxQa : conjSub x (pCoreOf 2 M) = pCoreOf 2 M :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 M hx)
  have h1 : conjSub x S = pCoreOf 2 M ⊔ conjSub x (conjClosure (VZ S M) H) := by
    have := congrArg (conjSub x) h.sup_eq_S.symm
    rw [this, conjSub_sup, hxQa]
  calc M = S ⊔ conjSub x S := (h.sup_conj_S hx hxS).symm
    _ = (pCoreOf 2 M ⊔ conjClosure (VZ S M) H) ⊔
          (pCoreOf 2 M ⊔ conjSub x (conjClosure (VZ S M) H)) := by
        rw [h1]
        exact congrArg (fun T => T ⊔ _) h.sup_eq_S.symm
    _ = pCoreOf 2 M ⊔ conjClosure (VZ S M) H ⊔ conjSub x (conjClosure (VZ S M) H) := by
        rw [sup_sup_sup_comm, sup_idem, ← sup_assoc]

theorem le_or_ge_V (h : B2Setup H M S) {x : G} (hx : x ∈ M) (hxS : x ∉ S) {Y : Subgroup G}
    (hY : IsElemAbelian 2 Y) (hYQ : Y ≤ pCoreOf 2 M)
    (hYn : pCoreOf 2 M ≤ Subgroup.normalizer (Y : Set G))
    (hb : ⁅conjClosure (VZ S M) H, Y⁆ ≤ VZ S M)
    (hl : ⁅conjSub x (conjClosure (VZ S M) H), Y⁆ ≤ VZ S M) :
    VZ S M ≤ Y ∨ Y ≤ VZ S M := by
  have hyp := h.amalgamHypV
  have hMV : M ≤ Subgroup.normalizer (VZ S M : Set G) := hyp.normalizes
  have hQM : pCoreOf 2 M ≤ M := pCoreOf_le 2 M
  have hVc : VZ S M ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    (h.V_le_center).trans inf_le_right
  have hSM := h.sylow_M.1
  have hVcY : VZ S M ≤ Subgroup.centralizer (Y : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr (fun y hy =>
      Subgroup.mem_centralizer_iff.mp (hVc hv) y (hYQ hy))
  have hVnY : VZ S M ≤ Subgroup.normalizer (Y : Set G) :=
    hVcY.trans (Subgroup.centralizer_le_normalizer _)
  set N : Subgroup G := Y ⊔ VZ S M with hN
  have hYN : Y ≤ N := le_sup_left
  have hVN : VZ S M ≤ N := le_sup_right
  have key : ∀ X : Subgroup G, X ≤ M → ⁅X, Y⁆ ≤ VZ S M →
      X ≤ Subgroup.normalizer (N : Set G) := by
    intro X hXM hXY
    have hconj : ∀ g ∈ X, conjSub g N ≤ N := by
      intro g hg
      rw [hN, conjSub_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        have hc : ⁅g, a⁆ ∈ VZ S M := hXY (Subgroup.commutator_mem_commutator hg ha)
        show g * a * g⁻¹ ∈ N
        have e : g * a * g⁻¹ = ⁅g, a⁆ * a := by rw [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem (hVN hc) (hYN ha)
      · exact ((F7.conjSub_eq_of_mem_normalizer (hMV (hXM hg))).le).trans hVN
    exact fun g hg => F7.mem_normalizer_of_conj_le (hconj g hg) (hconj g⁻¹ (X.inv_mem hg))
  have hVbM : conjClosure (VZ S M) H ≤ M :=
    (h.Vb_le_Qb.trans (isSylowTwoOf_pCoreOf_le h.sylow_H)).trans hSM
  have hVlM : conjSub x (conjClosure (VZ S M) H) ≤ M := by
    have := conjSub_mono x hVbM
    rwa [F7.conjSub_eq_of_mem hx] at this
  have hNb := key _ hVbM hb
  have hNl := key _ hVlM hl
  have hNQ : pCoreOf 2 M ≤ Subgroup.normalizer (N : Set G) :=
    F1.le_normalizer_sup hYn (hQM.trans hMV)
  have hMN : M ≤ Subgroup.normalizer (N : Set G) :=
    (h.eq_sup_vBeta hx hxS).le.trans (sup_le (sup_le hNQ hNb) hNl)
  have hKn : M ≤ Subgroup.normalizer ((⁅pCoreOf 2 M, N⁆ : Subgroup G) : Set G) := by
    intro g hg
    apply CosetGeom.mem_normalizer_of_conjSub_eq
    rw [← conjSub_commutator, F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 M hg),
      F7.conjSub_eq_of_mem_normalizer (hMN hg)]
  have hKY : ⁅pCoreOf 2 M, N⁆ ≤ Y := by
    rw [Subgroup.commutator_le]
    intro q hq n hn
    obtain ⟨a, ha, b, hb', rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hVnY).mp hn
    have hqb : q * b = b * q := Subgroup.mem_centralizer_iff.mp (hVc hb') q hq
    have hqa : q * a * q⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hYn hq) a).mp ha
    have hb2 : b * q⁻¹ * b⁻¹ = q⁻¹ := by
      have : q⁻¹ * b = b * q⁻¹ := by
        calc q⁻¹ * b = q⁻¹ * (b * q) * q⁻¹ := by group
          _ = q⁻¹ * (q * b) * q⁻¹ := by rw [hqb]
          _ = b * q⁻¹ := by group
      rw [← this]; group
    have e : ⁅q, a * b⁆ = (q * a * q⁻¹) * a⁻¹ := by
      rw [commutatorElement_def]
      have : q * (a * b) * q⁻¹ * (a * b)⁻¹ = q * a * (b * q⁻¹ * b⁻¹) * a⁻¹ := by group
      rw [this, hb2]
    rw [e]
    exact Y.mul_mem hqa (Y.inv_mem ha)
  have hKQ : ⁅pCoreOf 2 M, N⁆ ≤ pCoreOf 2 M := by
    rw [Subgroup.commutator_le]
    intro q hq n hn
    have hnM : n ∈ M := (sup_le (hYQ.trans hQM) (h.V_le_M)) hn
    have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M hnM) q⁻¹).mp
      ((pCoreOf 2 M).inv_mem hq)
    have e : ⁅q, n⁆ = q * (n * q⁻¹ * n⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (pCoreOf 2 M).mul_mem hq h1
  by_cases hK : ⁅pCoreOf 2 M, N⁆ = ⊥
  · right
    have hQY : pCoreOf 2 M ≤ Subgroup.centralizer (Y : Set G) := by
      have : ⁅pCoreOf 2 M, Y⁆ = ⊥ :=
        le_bot_iff.mp (hK ▸ Subgroup.commutator_mono le_rfl hYN)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp this
    have hYC : Y ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) := Subgroup.le_centralizer_iff.mpr hQY
    intro y hy
    rw [← h.omegaOneCenter_Qa]
    exact Subgroup.subset_closure ⟨⟨hYQ hy, hYC hy⟩, F7.isElemAbelian_pow_eq_one hY hy⟩
  · left
    exact (h.V_le_of_normal hKn hKQ hK).trans hKY

end B2Setup

end Amalg

end SzF53B2

end CFSG.Quasithin
