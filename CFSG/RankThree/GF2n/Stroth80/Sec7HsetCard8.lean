module

public import CFSG.RankThree.GF2n.Stroth80.Sec7LBElation

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_Hset_card8 [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (h4 : OmegaPlusNat hc t 4) {K : Type} [Field K] [Finite K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
    (hS : IsTensorSetup hc n M₀ ρ b) (ψ : M₀.E →ₗ[K] M₀.E)
    (hψ : ∀ e, ψ e = (ρ (QuotientGroup.mk (⟨t, hc.LB_le_M hs.toSec5.mem⟩ : ↥M))).toAdd e - e)
    (hrange : ∀ e, e ∈ LinearMap.range ψ ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) :
    Nat.card (sec7Hset M₀ (Vt M (LB M Q B) B Z t) B) = Nat.card K ^ 7 ∧
      Nat.card (hc.VtSub hS.model t) = Nat.card K ^ 8 := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hS.card.trans he)
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hZK : Nat.card Z = Nat.card K := hS.card.symm
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  have hLZ : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hZQB
  have hreg := hS.model.reg
  have hUcard : Nat.card (hc.VtSub hS.model t) = Nat.card K ^ 8 := by
    have hV9 := card_Vt_orthogonal hc (t := t) (m := 4) (by norm_num) (Or.inl h4)
    have hcV := Tim79.QuadModel.card_eq M₀ hVQ hZV'
    have hcimg : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) =
        Nat.card (hc.VtSub hS.model t) := rfl
    rw [hV9, hcimg] at hcV
    have h2 := Nat.eq_of_mul_eq_mul_left Nat.card_pos hcV
    rw [← h2, hZK]
  have hfU : Module.finrank K (hc.VtSub hS.model t) = 8 := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := hc.VtSub hS.model t)
    rw [hUcard] at h
    exact (Nat.pow_right_injective hK2 h).symm
  refine ⟨?_, hUcard⟩
  have hcard35 := stroth_3_5 h34 hc hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen
  obtain ⟨T, bT, hT, hfT, -, hb0, hB, hact, -⟩ :=
    sec7_LB_elation hc hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hcard35.2.2.1
      hcard35.2.2.2 hS.model
  have htbar : (QuotientGroup.mk (⟨t, htM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.mpr (hc.LB_le_H0 ht), rfl⟩
  let Tl : M₀.E ≃ₗ[K] M₀.E :=
    AddEquiv.toLinearEquiv (ρ (QuotientGroup.mk (⟨t, htM⟩ : ↥M))).toAdd (hS.lin _ htbar)
  have hTl : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = Tl (M₀.π x) := fun x hx => hS.conj ⟨t, htM⟩ x hx
  have hiso : ∀ e e', M₀.B (Tl e) (Tl e') = M₀.B e e' := hS.iso _ htbar
  have hψTl : ∀ e, ψ e = Tl e - e := hψ
  obtain ⟨-, hTc, hflag, hfixiff⟩ := hact t ht Tl hTl
  obtain ⟨e', he'T, he'ne⟩ : ∃ e' ∈ T, Tl e' ≠ e' := by
    by_contra hcon
    push Not at hcon
    exact hs.toSec5.notQ (hfixiff.mp hcon)
  obtain ⟨c, hc'⟩ := hTc e' he'T
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc'
    exact he'ne (sub_eq_zero.mp hc')
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : M₀.E, M₀.B e₀ bT ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hb0
    exact M₀.nondeg _ fun f => by rw [Tim79.QuadModel.B_comm, hcon f, neg_zero]
  have hUiso : ∀ u ∈ hc.VtSub hS.model t, ∀ u' ∈ hc.VtSub hS.model t, M₀.B u u' = 0 := by
    intro u hu u' hu'
    obtain ⟨v, hvV, hvQ, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hu)
    obtain ⟨v', hvV', hvQ', rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hu')
    have hvW : v ∈ Wt Q (Vt M (LB M Q B) B Z t) := sec7_V_le_W h310chi hc hs hvV
    exact (M₀.comm_iff_B hreg hvQ hvQ').mp (Subgroup.mem_centralizer_iff.mp hvW.2 v' hvV').symm
  have hTiso : ∀ u ∈ T, ∀ v ∈ T, M₀.B u v = 0 := by
    intro u hu v hv
    obtain ⟨x, hxX, hxQ, rfl⟩ := M₀.mem_img.mp ((hT u).mp hu)
    obtain ⟨y, hyX, hyQ, rfl⟩ := M₀.mem_img.mp ((hT v).mp hv)
    have hc1 := hc.inf_QB_elemAbelian.1.is_comm
    have h1 : x * y = y * x := congrArg Subtype.val (hc1.comm ⟨x, hxX⟩ ⟨y, hyX⟩)
    exact (M₀.comm_iff_B hreg hxQ hyQ).mp h1
  have hadj : ∀ e e', M₀.B (ψ e) e' = M₀.B e (ψ e') := by
    intro e e'
    have h1 := hiso e e'
    have h2 : Tl e = e + ψ e := by rw [hψTl]; abel
    have h2' : Tl e' = e' + ψ e' := by rw [hψTl]; abel
    have hU1 : ψ e ∈ hc.VtSub hS.model t :=
      (hc.mem_VtSub hS.model t).mpr ((hrange _).mp ⟨e, rfl⟩)
    have hU2 : ψ e' ∈ hc.VtSub hS.model t :=
      (hc.mem_VtSub hS.model t).mpr ((hrange _).mp ⟨e', rfl⟩)
    have h0 := hUiso _ hU1 _ hU2
    rw [h2, h2'] at h1
    simp only [map_add, LinearMap.add_apply] at h1
    rw [h0, add_zero] at h1
    have h3 : M₀.B e (ψ e') + M₀.B (ψ e) e' = 0 := by linear_combination h1
    exact (eq_neg_of_add_eq_zero_right h3).trans (CharTwo.neg_eq _)
  have hHmem : ∀ e, e ∈ sec7Hset M₀ (Vt M (LB M Q B) B Z t) B ↔
      e ∈ hc.VtSub hS.model t ⊓ T := by
    intro e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    have hsupeq : (Vt M (LB M Q B) B Z t ⊓ QB B) ⊔ Z = Vt M (LB M Q B) B Z t ⊓ QB B :=
      sup_eq_left.mpr (le_inf hZV' hZQB)
    show M₀.π x ∈ M₀.img ((Vt M (LB M Q B) B Z t ⊓ QB B) ⊔ Z) ↔ _
    rw [hsupeq, Tim79.QuadModel.mem_img_iff M₀ (le_inf hZV' hZQB) hxQ, Submodule.mem_inf,
      hc.mem_VtSub hS.model t, hT, Tim79.QuadModel.mem_img_iff M₀ hZV' hxQ,
      Tim79.QuadModel.mem_img_iff M₀ hLZ hxQ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hxQ, h2⟩
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
  have hHcard : Nat.card (sec7Hset M₀ (Vt M (LB M Q B) B Z t) B) =
      Nat.card ↥(hc.VtSub hS.model t ⊓ T) :=
    Nat.card_congr (Equiv.subtypeEquivRight hHmem)
  rw [hHcard, Module.natCard_eq_pow_finrank (K := K) (V := ↥(hc.VtSub hS.model t ⊓ T))]
  congr 1
  have hnotsub : ¬ ∀ e ∈ hc.VtSub hS.model t, e ∈ T := by
    intro hsub
    have hψe₀ : ψ e₀ ∈ hc.VtSub hS.model t :=
      (hc.mem_VtSub hS.model t).mpr ((hrange _).mp ⟨e₀, rfl⟩)
    have h1 := hTiso _ (hsub _ hψe₀) _ he'T
    rw [hadj] at h1
    have h2 : M₀.B e₀ (ψ e') = c * M₀.B e₀ bT := by
      rw [hψTl, hc', map_smul, smul_eq_mul]
    rw [h2] at h1
    exact mul_ne_zero hc0 he₀ h1
  have hle7 : Module.finrank K ↥(hc.VtSub hS.model t ⊓ T) ≤ 7 := by
    have hlt : hc.VtSub hS.model t ⊓ T < hc.VtSub hS.model t := by
      refine lt_of_le_of_ne inf_le_left fun h => hnotsub fun e he => ?_
      have : e ∈ hc.VtSub hS.model t ⊓ T := by rw [h]; exact he
      exact this.2
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  let Fb : M₀.E →ₗ[K] K := M₀.B.flip bT
  have hFb : ∀ e, Fb e = M₀.B e bT := fun e => rfl
  let Hp : Submodule K M₀.E := LinearMap.ker Fb
  have hmapHp : Submodule.map ψ Hp ≤ hc.VtSub hS.model t ⊓ T := by
    rintro _ ⟨h, hh, rfl⟩
    have hh' : M₀.B h bT = 0 := hh
    refine ⟨(hc.mem_VtSub hS.model t).mpr ((hrange _).mp ⟨h, rfl⟩), ?_⟩
    rw [hψTl]
    exact hflag h hh'
  have hcover : Nat.card ↥(LinearMap.range ψ) ≤
      Nat.card ↥(Submodule.map ψ Hp) * Nat.card K := by
    let F : ↥(Submodule.map ψ Hp) × K → ↥(LinearMap.range ψ) := fun p =>
      ⟨(p.1 : M₀.E) + p.2 • ψ e₀, (LinearMap.range ψ).add_mem
        (LinearMap.map_le_range p.1.2) ((LinearMap.range ψ).smul_mem _ ⟨e₀, rfl⟩)⟩
    have hFs : Function.Surjective F := by
      rintro ⟨y, e, rfl⟩
      have hβ : Fb e₀ ≠ 0 := he₀
      set cc : K := Fb e / Fb e₀ with hcc
      have hhp : e - cc • e₀ ∈ Hp := by
        show Fb (e - cc • e₀) = 0
        rw [map_sub, map_smul, smul_eq_mul, hcc, div_mul_cancel₀ _ hβ, sub_self]
      refine ⟨(⟨ψ (e - cc • e₀), ⟨_, hhp, rfl⟩⟩, cc), ?_⟩
      apply Subtype.ext
      show ψ (e - cc • e₀) + cc • ψ e₀ = ψ e
      rw [map_sub, map_smul]
      abel
    have h1 := Nat.card_le_card_of_surjective F hFs
    rwa [Nat.card_prod] at h1
  have hrcard : Nat.card ↥(LinearMap.range ψ) = Nat.card K ^ 8 := by
    rw [← hUcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun e =>
      (hrange e).trans (hc.mem_VtSub hS.model t).symm)
  have hmcard : Nat.card ↥(Submodule.map ψ Hp) ≤ Nat.card ↥(hc.VtSub hS.model t ⊓ T) :=
    Nat.card_le_card_of_injective (Submodule.inclusion hmapHp)
      (Submodule.inclusion_injective hmapHp)
  have h7 : Nat.card K ^ 7 ≤ Nat.card ↥(Submodule.map ψ Hp) := by
    rw [hrcard] at hcover
    have h8 : Nat.card K ^ 7 * Nat.card K ≤ Nat.card ↥(Submodule.map ψ Hp) * Nat.card K := by
      rw [← pow_succ]
      exact hcover
    exact Nat.le_of_mul_le_mul_right h8 Nat.card_pos
  have h7' : Nat.card K ^ 7 ≤ Nat.card K ^ Module.finrank K ↥(hc.VtSub hS.model t ⊓ T) := by
    rw [← Module.natCard_eq_pow_finrank (K := K) (V := ↥(hc.VtSub hS.model t ⊓ T))]
    exact h7.trans hmcard
  have hge7 : 7 ≤ Module.finrank K ↥(hc.VtSub hS.model t ⊓ T) :=
    (Nat.pow_le_pow_iff_right (by omega)).mp h7'
  omega

end CFSG.RankThree.GF2n.Stroth80
