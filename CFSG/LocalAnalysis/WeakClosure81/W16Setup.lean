module

public import CFSG.LocalAnalysis.WeakClosure81.W15Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Thm152 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ ⦃M V₀ V : Subgroup G⦄ (hyp : Hyp15 M V₀ V),
    1 < mBar M V₀ V hyp.h6.elemAbelian → (mSub V₀ : ℕ∞) < rMV M V

structure Cex16 (M V₀ V U S : Subgroup G) : Prop where
  hyp : Hyp15 M V₀ V
  mbar : 1 < mBar M V₀ V hyp.h6.elemAbelian
  le : U ≤ V
  not_le : ¬ centralizer (U : Set G) ≤ M
  mquot : (E3.mQuot V U : ℕ∞) = rMV M V
  small : rMV M V < ((mBar M V₀ V hyp.h6.elemAbelian + mSub V₀ : ℕ) : ℕ∞)
  sylow : IsSylowIn 2 S (M ⊓ centralizer (U : Set G))

theorem exists_cex16 {M V₀ V : Subgroup G} (hyp : Hyp15 M V₀ V)
    (hm : 1 < mBar M V₀ V hyp.h6.elemAbelian)
    (hr : rMV M V < ((mBar M V₀ V hyp.h6.elemAbelian + mSub V₀ : ℕ) : ℕ∞)) :
    ∃ U S : Subgroup G, Cex16 M V₀ V U S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  have hne : ∃ U : Subgroup G, U ≤ V ∧ ¬ centralizer (U : Set G) ≤ M := by
    by_contra hcon
    have htop : rMV M V = ⊤ := by
      unfold rMV
      exact iInf_eq_top.2 fun U => iInf_eq_top.2 fun hU => absurd ⟨U, hU.1, hU.2⟩ hcon
    rw [htop] at hr
    exact absurd hr (not_lt.2 le_top)
  let P : ℕ → Prop := fun n =>
    ∃ U : Subgroup G, U ≤ V ∧ ¬ centralizer (U : Set G) ≤ M ∧ E3.mQuot V U = n
  have hP : ∃ n, P n := by
    obtain ⟨U, h1, h2⟩ := hne
    exact ⟨_, U, h1, h2, rfl⟩
  obtain ⟨U, hUV, hUC, hUn⟩ := Nat.find_spec hP
  have hmin : ∀ U' : Subgroup G, U' ≤ V → ¬ centralizer (U' : Set G) ≤ M →
      E3.mQuot V U ≤ E3.mQuot V U' := by
    intro U' h1 h2
    rw [hUn]
    exact Nat.find_min' hP ⟨U', h1, h2, rfl⟩
  have hmq : (E3.mQuot V U : ℕ∞) = rMV M V := by
    apply le_antisymm
    · refine le_iInf₂ fun U' hU' => ?_
      exact_mod_cast hmin U' hU'.1 hU'.2
    · exact rMV_le_mQuot M V U hUV hUC
  obtain ⟨S, hS, -⟩ := exists_isSylowIn_ge 2
    (bot_le : (⊥ : Subgroup G) ≤ M ⊓ centralizer (U : Set G)) IsPGroup.of_bot
  exact ⟨U, S, ⟨hyp, hm, hUV, hUC, hmq, hr, hS⟩⟩

theorem mBar_le_mQuot {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V) :
    mBar M V₀ V hV ≤ E3.mQuot V V₀ := by
  have hc : Nat.card V = Nat.card V₀ * Nat.card (Vtil V₀ V hV) := card_Vtil_eq V₀ V hV hV₀
  have hrel : V₀.relIndex V * Nat.card V₀ = Nat.card V := by
    simpa [inf_eq_left.2 hV₀] using Subgroup.relIndex_mul_card (H := V₀) (K := V)
  have hidx : V₀.relIndex V = Nat.card (Vtil V₀ V hV) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card V₀)
    rw [hrel, hc, mul_comm]
  calc mBar M V₀ V hV = E3.mParam (Mbar M V₀ V hV) := rfl
    _ ≤ rk (Vtil V₀ V hV) := E3.mParam_le_rk _
    _ = E3.mQuot V V₀ := by rw [rk, E3.mQuot, hidx]

theorem exists_mul_of_mem_sup {U V₀ V : Subgroup G} (hU : U ≤ V) (hV₀ : V₀ ≤ V)
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) {y : G} (hy : y ∈ U ⊔ V₀) :
    ∃ u ∈ U, ∃ w ∈ V₀, u * w = y := by
  have hc : ∀ u ∈ U, ∀ w ∈ V₀, u * w * u⁻¹ = w := fun u hu w hw => by
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm u (hU hu) w (hV₀ hw)
  have hnorm : U ≤ normalizer (V₀ : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rwa [hc u hu w hw]
    · intro hw
      have h2 : u⁻¹ * (u * w * u⁻¹) * u⁻¹⁻¹ = u * w * u⁻¹ := hc u⁻¹ (U.inv_mem hu) _ hw
      have h3 : u⁻¹ * (u * w * u⁻¹) * u⁻¹⁻¹ = w := by group
      rw [h3] at h2
      rw [h2]
      exact hw
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right U V₀ hnorm] at hy
  exact hy

private theorem card_sup_eq_mul {U V₀ V : Subgroup G} (hU : U ≤ V) (hV₀ : V₀ ≤ V)
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hinf : U ⊓ V₀ = ⊥) :
    Nat.card ↥(U ⊔ V₀) = Nat.card U * Nat.card V₀ := by
  have hmem : ∀ y ∈ U ⊔ V₀, ∃ u ∈ U, ∃ w ∈ V₀, u * w = y := fun y hy =>
    exists_mul_of_mem_sup hU hV₀ hcomm hy
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : U × V₀ => (⟨p.1.1 * p.2.1, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩ :
      ↥(U ⊔ V₀))) ⟨?_, ?_⟩)
  · rintro ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ ⟨⟨u', hu'⟩, ⟨w', hw'⟩⟩ h
    have h' : u * w = u' * w' := congrArg Subtype.val h
    have h1 : u'⁻¹ * u = w' * w⁻¹ := by
      calc u'⁻¹ * u = u'⁻¹ * (u * w) * w⁻¹ := by group
        _ = u'⁻¹ * (u' * w') * w⁻¹ := by rw [h']
        _ = w' * w⁻¹ := by group
    have h2 : u'⁻¹ * u ∈ U ⊓ V₀ :=
      ⟨U.mul_mem (U.inv_mem hu') hu, h1 ▸ V₀.mul_mem hw' (V₀.inv_mem hw)⟩
    rw [hinf, Subgroup.mem_bot] at h2
    have hu1 : u = u' := (inv_mul_eq_one.1 h2).symm
    subst hu1
    have hw1 : w = w' := mul_left_cancel h'
    subst hw1
    rfl
  · rintro ⟨y, hy⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := hmem y hy
    exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), rfl⟩

namespace Cex16

variable {M V₀ V U S : Subgroup G}

theorem inf_eq_bot (h : Cex16 M V₀ V U S) : U ⊓ V₀ = ⊥ := by
  by_contra hne
  obtain ⟨⟨w, hwU, hwV⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  apply h.not_le
  intro g hg
  have hgc : g ∈ centralizer ({w} : Set G) :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hwU)) hg
  exact h.hyp.centralizer_le hwV (fun h1 => hw1 (Subtype.ext h1)) hgc

theorem exists_mul_of_mem_sup (h : Cex16 M V₀ V U S) {y : G} (hy : y ∈ U ⊔ V₀) :
    ∃ u ∈ U, ∃ w ∈ V₀, u * w = y :=
  CFSG.LocalAnalysis.WeakClosure81.exists_mul_of_mem_sup h.le h.hyp.h6.le
    (fun x hx y hy => B2F.isElemAbelian_comm h.hyp.h6.elemAbelian hx hy) hy

theorem V_le_S (h : Cex16 M V₀ V U S) : V ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := h.hyp
  have hVc : V ≤ centralizer (U : Set G) := fun v hv => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (B2F.isElemAbelian_comm hH.h6.elemAbelian hv (h.le hw)).symm
  have hVK : V ≤ M ⊓ centralizer (U : Set G) := le_inf hH.le_M hVc
  have hVnorm : (V.subgroupOf (M ⊓ centralizer (U : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVK]
    exact inf_le_left.trans (hH.h6.normalizer_eq ▸ le_rfl)
  exact h.sylow.le_of_normal hVK hVnorm hH.isPGroup

theorem V₀_le_S (h : Cex16 M V₀ V U S) : V₀ ≤ S := h.hyp.h6.le.trans h.V_le_S

theorem S_le_M (h : Cex16 M V₀ V U S) : S ≤ M := h.sylow.le.trans inf_le_left

theorem S_le_centralizer (h : Cex16 M V₀ V U S) : S ≤ centralizer (U : Set G) :=
  h.sylow.le.trans inf_le_right

theorem mQuot_sup (h : Cex16 M V₀ V U S) : E3.mQuot (U ⊔ V₀) U = mSub V₀ := by
  have hH := h.hyp
  have hX2 : IsPGroup 2 ↥(U ⊔ V₀) := hH.isPGroup.to_le (sup_le h.le hH.h6.le)
  have h1 := E3.card_eq_two_pow_mul hX2 (le_sup_left : U ≤ U ⊔ V₀)
  have h2 : Nat.card ↥(U ⊔ V₀) = Nat.card U * Nat.card V₀ :=
    card_sup_eq_mul h.le hH.h6.le (fun x hx y hy => B2F.isElemAbelian_comm hH.h6.elemAbelian hx hy)
      h.inf_eq_bot
  have h0 : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub (hH.isPGroup.to_le hH.h6.le)
  have hpos : 0 < Nat.card U := Nat.card_pos
  rw [h2, h0, mul_comm (Nat.card U)] at h1
  exact Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_right hpos h1).symm

theorem mQuot_eq_add (h : Cex16 M V₀ V U S) :
    E3.mQuot V U = E3.mQuot V (U ⊔ V₀) + mSub V₀ := by
  have hH := h.hyp
  rw [E3.mQuot_add (le_sup_left : U ≤ U ⊔ V₀) (sup_le h.le hH.h6.le), h.mQuot_sup, add_comm]

theorem rMV_eq (h : Cex16 M V₀ V U S) :
    rMV M V = ((E3.mQuot V (U ⊔ V₀) + mSub V₀ : ℕ) : ℕ∞) := by
  rw [← h.mquot, h.mQuot_eq_add]

theorem n_lt_mBar (h : Cex16 M V₀ V U S) :
    E3.mQuot V (U ⊔ V₀) < mBar M V₀ V h.hyp.h6.elemAbelian := by
  have h1 := h.small
  rw [h.rMV_eq] at h1
  have h2 : E3.mQuot V (U ⊔ V₀) + mSub V₀ < mBar M V₀ V h.hyp.h6.elemAbelian + mSub V₀ := by
    exact_mod_cast h1
  omega

theorem one_le_n (h152 : Thm152 G) (h : Cex16 M V₀ V U S) : 1 ≤ E3.mQuot V (U ⊔ V₀) := by
  have h1 := h152 h.hyp h.mbar
  rw [h.rMV_eq] at h1
  have h2 : mSub V₀ < E3.mQuot V (U ⊔ V₀) + mSub V₀ := by exact_mod_cast h1
  omega

theorem ne_bot (h : Cex16 M V₀ V U S) : U ≠ ⊥ := by
  intro hU
  have h1 := h.n_lt_mBar
  have h2 : E3.mQuot V (U ⊔ V₀) = E3.mQuot V V₀ := by rw [hU, bot_sup_eq]
  exact absurd (mBar_le_mQuot h.hyp.h6.elemAbelian h.hyp.h6.le) (_root_.not_le.2 (h2 ▸ h1))

theorem sup_ne_top (h152 : Thm152 G) (h : Cex16 M V₀ V U S) : U ⊔ V₀ ≠ V := by
  intro hUV
  have h1 := h.one_le_n h152
  rw [hUV, E3.mQuot_self] at h1
  omega

end Cex16

end CFSG.LocalAnalysis.WeakClosure81
