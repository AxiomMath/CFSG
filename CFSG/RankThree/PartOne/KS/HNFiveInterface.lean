module

public import CFSG.RankThree.PartOne.KS.HNFiveForms
public import CFSG.RankThree.CentralExtension.PrimeToPKernel

public section

namespace CFSG.RankThree.PartOne.KS.HNFive

open Subgroup CFSG.Monster.B.Pinned CFSG.RankThree.CentralExtension
open scoped Matrix

@[expose] def FiveLocalInterface (G : Type*) [Group G] : Prop :=
  ∃ (H Q : Subgroup G) (hQH : Q ≤ H) (_ : (Q.subgroupOf H).Normal)
    (_ : Module (ZMod 5) (Additive (Abelianization Q)))
    (R : Subgroup (H ⧸ Q.subgroupOf H)) (_ : R.Normal),
    (∃ P : Sylow 5 G, (P : Subgroup G) ≤ H) ∧ (∀ q ∈ Q, q ^ 5 = 1) ∧
    center Q = commutator Q ∧ Nat.card (center Q) = 5 ∧
    (∀ P : Sylow 5 (H ⧸ Q.subgroupOf H), IsCyclic P) ∧ (Nat.card R).Coprime 5 ∧
    (∀ h : H, (h : H ⧸ Q.subgroupOf H) ∈ R → ∀ z ∈ center Q, conjOnNormal hQH h z = z) ∧
    (∃ h : H, (h : H ⧸ Q.subgroupOf H) ∈ R ∧
      ∀ q : Q, Abelianization.of (conjOnNormal hQH h q) = (Abelianization.of q)⁻¹) ∧
    Module.finrank (ZMod 5) (conjInvariantAltForms 5 hQH R) = 1

theorem finrank_span_single_eq_one {V : Type*} [AddCommGroup V] [Module (ZMod 5) V] (v : V)
    (hv : v ≠ 0) : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) {v}) = 1 := by
  have hinv : ∀ c : ZMod 5, c ≠ 0 → ∃ d : ZMod 5, d * c = 1 := by decide
  have hinj : Function.Injective (LinearMap.toSpanSingleton (ZMod 5) V v) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra hne
    obtain ⟨d, hd⟩ := hinv c hne
    apply hv
    have h1 : c • v = 0 := hc
    calc v = (d * c) • v := by rw [hd, one_smul]
      _ = d • (c • v) := mul_smul d c v
      _ = 0 := by rw [h1, smul_zero]
  have e := LinearEquiv.ofInjective (LinearMap.toSpanSingleton (ZMod 5) V v) hinj
  rw [LinearMap.span_singleton_eq_range]
  rw [← LinearEquiv.finrank_eq e]
  have : Nontrivial (ZMod 5) := ⟨⟨0, 1, by decide⟩⟩
  exact Module.finrank_self (ZMod 5)

variable {G : Type*} [Group G]

namespace Rel

variable {k : ℕ} {q : Fin 4 → G} {z x : G} {r : Fin k → G} {M : Matrix (Fin 4) (Fin 4) (ZMod 5)}
  {XU : GL (Fin 4) (ZMod 5)} {cx : Fin 4 → ℕ} {BU : Fin k → GL (Fin 4) (ZMod 5)}
  {cr : Fin k → Fin 4 → ℕ} (hR : Rel q z x r M XU cx BU cr)
include hR

theorem pow_five (g : QG q) : g ^ 5 = 1 :=
  Subtype.ext (by simpa using hR.pow_five_of_mem g.2)

@[expose, instance_reducible] noncomputable def vModule :
    Module (ZMod 5) (Additive (Abelianization (QG q))) :=
  AddCommGroup.zmodModule fun v => by
    obtain ⟨u, rfl⟩ := ab_surjective v
    rw [ab, ← ofMul_pow, ← map_pow, hR.pow_five u, map_one, ofMul_one]

section Finite

variable [Finite G] [((QG q).subgroupOf (HG q x r)).Normal]
  [Module (ZMod 5) (Additive (Abelianization (QG q)))]

theorem formOf_invariant_iff (F : Matrix (Fin 4) (Fin 4) (ZMod 5)) (g : HG q x r) :
    (∀ u u' : QG q, hR.formOf F (ab (conjOnNormal Q_le_H g u)) (ab (conjOnNormal Q_le_H g u')) =
        hR.formOf F (ab u) (ab u')) ↔
      CommData.actMat 5 q z M (g : G)⁻¹ * F * (CommData.actMat 5 q z M (g : G)⁻¹)ᵀ = F := by
  set B : Matrix (Fin 4) (Fin 4) (ZMod 5) := (CommData.actMat 5 q z M (g : G)⁻¹)ᵀ with hB
  have key : ∀ c c' : Fin 4 → ZMod 5,
      (B *ᵥ c) ⬝ᵥ (F *ᵥ (B *ᵥ c')) = c ⬝ᵥ ((Bᵀ * F * B) *ᵥ c') := by
    intro c c'
    simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hBT : Bᵀ = CommData.actMat 5 q z M (g : G)⁻¹ := by rw [hB, Matrix.transpose_transpose]
  have hconj : ∀ u : QG q, cAb hR.commData (ab (conjOnNormal Q_le_H g u)) =
      B *ᵥ cAb hR.commData (ab u) := fun u =>
    hR.cAb_conj g.2 u _ (conjOnNormal_apply Q_le_H g u)
  rw [← hBT]
  constructor
  · intro h
    apply mat_eq_of_forms
    intro c c'
    obtain ⟨v, hv⟩ := cAb_surjective hR.commData c
    obtain ⟨v', hv'⟩ := cAb_surjective hR.commData c'
    obtain ⟨u, rfl⟩ := ab_surjective v
    obtain ⟨u', rfl⟩ := ab_surjective v'
    have := h u u'
    rw [hR.formOf_apply, hR.formOf_apply, hconj, hconj, hv, hv', key] at this
    exact this
  · intro h u u'
    rw [hR.formOf_apply, hR.formOf_apply, hconj, hconj, key, h]

omit [Finite G] in
theorem commForm_invariant (g : HG q x r) (u u' : QG q) :
    hR.commForm (ab (conjOnNormal Q_le_H g u)) (ab (conjOnNormal Q_le_H g u')) =
      hR.commForm (ab u) (ab u') := by
  rw [hR.commForm_ab, hR.commForm_ab]
  have e1 : ((conjOnNormal Q_le_H g u : QG q) : G) = g * u * (g : G)⁻¹ :=
    conjOnNormal_apply Q_le_H g u
  have e2 : ((conjOnNormal Q_le_H g u' : QG q) : G) = g * u' * (g : G)⁻¹ :=
    conjOnNormal_apply Q_le_H g u'
  rw [e1, e2]
  have h1 : bcomm ((g : G) * u * (g : G)⁻¹) ((g : G) * u' * (g : G)⁻¹) =
      g * bcomm (u : G) u' * (g : G)⁻¹ := by
    have := bcomm_conj' (g : G)⁻¹ u u'
    simpa using this
  rw [h1]
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hR.bcomm_mem_zpowers u.2 u'.2)
  have hc : Commute (g : G) (bcomm (u : G) u') := by
    rw [← hn]
    exact (hR.H_commute_z g.2).zpow_right n
  rw [hc.eq, mul_inv_cancel_right]

omit [Finite G] [((QG q).subgroupOf (HG q x r)).Normal] in
theorem commForm_alt (v : Additive (Abelianization (QG q))) : hR.commForm v v = 0 := by
  obtain ⟨u, rfl⟩ := ab_surjective v
  rw [hR.commForm_ab, show bcomm (u : G) u = 1 from bcomm_eq_one_iff.2 rfl, lg_one hR.orderOf_z]

omit [Finite G] [((QG q).subgroupOf (HG q x r)).Normal] in
theorem commForm_ne_zero : hR.commForm ≠ 0 := by
  intro h
  have h1 := hR.commForm_ab ⟨q 0, q_mem 0⟩ ⟨q 1, q_mem 1⟩
  rw [h, LinearMap.zero_apply, LinearMap.zero_apply] at h1
  have h2 : lg 5 z (bcomm (q 0) (q 1)) = 1 := by
    rw [hR.z_eq]
    have := lg_pow (p := 5) hR.orderOf_z 1
    rwa [pow_one, Nat.cast_one] at this
  have h3 : (0 : ZMod 5) = 1 := h1.trans h2
  exact absurd h3 (by decide)

theorem conjInvariantAltForms_eq (T : Subgroup (GL (Fin 4) (ZMod 5))) (hB : ∀ j, BU j ∈ T)
    (hforms : ∀ F : Matrix (Fin 4) (Fin 4) (ZMod 5), Fᵀ = -F → (∀ i, F i i = 0) →
      (∀ j, (BU j : Matrix (Fin 4) (Fin 4) (ZMod 5)) * F *
        (BU j : Matrix (Fin 4) (Fin 4) (ZMod 5))ᵀ = F) → ∃ c : ZMod 5, F = c • M) :
    conjInvariantAltForms 5 Q_le_H (hR.R T) = Submodule.span (ZMod 5) {hR.commForm} := by
  apply le_antisymm
  · intro β hβ
    obtain ⟨halt, hinv⟩ := mem_conjInvariantAltForms.1 hβ
    have hβF := hR.eq_formOf_gram β
    set F := gram β with hFdef
    have hFalt := (hR.formOf_alt_iff F).1 (fun v => by rw [← hβF]; exact halt v)
    have hFinv : ∀ j, (BU j : Matrix (Fin 4) (Fin 4) (ZMod 5)) * F *
        (BU j : Matrix (Fin 4) (Fin 4) (ZMod 5))ᵀ = F := by
      intro j
      set g : HG q x r := ⟨(r j)⁻¹, inv_mem (r_mem_H j)⟩ with hg
      have hgR : (g : HG q x r ⧸ (QG q).subgroupOf (HG q x r)) ∈ hR.R T := by
        rw [R, mem_comap, hR.rho_mk]
        have : hR.AU g = (BU j)⁻¹ := by
          rw [hg, show (⟨(r j)⁻¹, inv_mem (r_mem_H j)⟩ : HG q x r) =
            (⟨r j, r_mem_H j⟩ : HG q x r)⁻¹ from rfl, map_inv, hR.AU_r]
        rw [this]
        exact inv_mem (hB j)
      have hi := (hR.formOf_invariant_iff F g).1 (fun u u' => by
        rw [← hβF]
        exact hinv g hgR u u')
      have e : ((g : HG q x r) : G)⁻¹ = r j := by rw [hg]; exact inv_inv _
      rw [e, hR.actMat_r j] at hi
      exact hi
    obtain ⟨c, hc⟩ := hforms F hFalt.1 hFalt.2 hFinv
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [hβF, hc, hR.formOf_smul]
    rfl
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine mem_conjInvariantAltForms.2 ⟨hR.commForm_alt, fun g _ u u' => ?_⟩
    exact hR.commForm_invariant g u u'

theorem finrank_conjInvariant (T : Subgroup (GL (Fin 4) (ZMod 5))) (hB : ∀ j, BU j ∈ T)
    (hforms : ∀ F : Matrix (Fin 4) (Fin 4) (ZMod 5), Fᵀ = -F → (∀ i, F i i = 0) →
      (∀ j, (BU j : Matrix (Fin 4) (Fin 4) (ZMod 5)) * F *
        (BU j : Matrix (Fin 4) (Fin 4) (ZMod 5))ᵀ = F) → ∃ c : ZMod 5, F = c • M) :
    Module.finrank (ZMod 5) (conjInvariantAltForms 5 Q_le_H (hR.R T)) = 1 := by
  rw [hR.conjInvariantAltForms_eq T hB hforms]
  exact finrank_span_single_eq_one hR.commForm hR.commForm_ne_zero

omit [Module (ZMod 5) (Additive (Abelianization (QG q)))] in
theorem sigma_conj_ab (T : Subgroup (GL (Fin 4) (ZMod 5))) (hB : ∀ j, BU j ∈ T) {s : Fin k}
    (hs : BU s = -1) :
    ∃ g : HG q x r, (g : HG q x r ⧸ (QG q).subgroupOf (HG q x r)) ∈ hR.R T ∧
      ∀ u : QG q, Abelianization.of (conjOnNormal Q_le_H g u) = (Abelianization.of u)⁻¹ := by
  refine ⟨⟨r s, r_mem_H s⟩, ?_, fun u => ?_⟩
  · rw [R, mem_comap, hR.rho_mk, hR.AU_r]
    exact hB s
  · have hinv : CommData.actMat 5 q z M (r s)⁻¹ = -1 := by
      have h1 : hR.AU (⟨r s, r_mem_H s⟩ : HG q x r)⁻¹ = -1 := by
        rw [map_inv, hR.AU_r, hs]
        exact inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_one])
      have h2 := congrArg Units.val h1
      rw [Units.val_neg, Units.val_one] at h2
      exact h2
    have h1 := hR.cAb_conj (g := (⟨r s, r_mem_H s⟩ : HG q x r)) (⟨r s, r_mem_H s⟩ : HG q x r).2
      u _ (conjOnNormal_apply Q_le_H (⟨r s, r_mem_H s⟩ : HG q x r) u)
    have hv : ∀ v : Fin 4 → ZMod 5, (CommData.actMat 5 q z M (r s)⁻¹)ᵀ *ᵥ v = -v := by
      intro v
      rw [hinv]
      simp [Matrix.neg_mulVec]
    rw [show ((⟨r s, r_mem_H s⟩ : HG q x r) : G)⁻¹ = (r s)⁻¹ from rfl, hv] at h1
    have h2 := hR.cAb_injective (h1.trans (map_neg (cAb hR.commData) (ab u)).symm)
    exact congrArg Additive.toMul h2

end Finite

theorem interface [Finite G] (T : Subgroup (GL (Fin 4) (ZMod 5))) (hX : XU ≠ 1)
    (hT : IsPGroup 2 T) (hB : ∀ j, BU j ∈ T)
    (hXn : XU ∈ normalizer (T : Set (GL (Fin 4) (ZMod 5)))) (hs : ∃ s, BU s = -1)
    (hforms : ∀ F : Matrix (Fin 4) (Fin 4) (ZMod 5), Fᵀ = -F → (∀ i, F i i = 0) →
      (∀ j, (BU j : Matrix (Fin 4) (Fin 4) (ZMod 5)) * F *
        (BU j : Matrix (Fin 4) (Fin 4) (ZMod 5))ᵀ = F) → ∃ c : ZMod 5, F = c • M)
    (h5 : (Nat.card G).factorization 5 = 6) : FiveLocalInterface G := by
  have hN : ((QG q).subgroupOf (HG q x r)).Normal := hR.Q_normal_H
  have hRn : (hR.R T).Normal := hR.R_normal T hXn hB
  let _ : Module (ZMod 5) (Additive (Abelianization (QG q))) := hR.vModule
  obtain ⟨S, hS⟩ := hR.P_sylow hX h5
  obtain ⟨s, hs⟩ := hs
  refine ⟨HG q x r, QG q, Q_le_H, hN, hR.vModule, hR.R T, hRn, ⟨S, hS ▸ P_le_H⟩,
    fun g hg => hR.pow_five_of_mem hg, hR.center_Q_eq_commutator, hR.card_center_Q,
    fun P => hR.sylow_HL_cyclic h5 P, hR.coprime_R T hT hX h5, ?_,
    hR.sigma_conj_ab T hB hs, hR.finrank_conjInvariant T hB hforms⟩
  intro g _ y hy
  apply Subtype.ext
  rw [conjOnNormal_apply]
  have hy' : (y : G) ∈ zpowers z := by
    have := fact5
    rw [hR.commData.center_eq, mem_subgroupOf] at hy
    exact hy
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hy'
  have hc : Commute (g : G) (y : G) := by
    rw [← hn]
    exact (hR.H_commute_z g.2).zpow_right n
  rw [hc.eq, mul_inv_cancel_right]

end Rel

end CFSG.RankThree.PartOne.KS.HNFive
