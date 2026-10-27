module

public import CFSG.LocalAnalysis.WeakClosure81.W15Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_cex15 {M V₀ V : Subgroup G} (hyp : Hyp15 M V₀ V)
    (hm : 1 < mBar M V₀ V hyp.h6.elemAbelian) (hr : rMV M V ≤ (mSub V₀ : ℕ∞)) :
    ∃ U S : Subgroup G, Cex15 M V₀ V U S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  have hne : ∃ U : Subgroup G, U ≤ V ∧ ¬ centralizer (U : Set G) ≤ M := by
    by_contra hcon
    have htop : rMV M V = ⊤ := by
      unfold rMV
      exact iInf_eq_top.2 fun U => iInf_eq_top.2 fun hU => absurd ⟨U, hU.1, hU.2⟩ hcon
    rw [htop] at hr
    exact absurd (top_le_iff.1 hr) (ENat.coe_ne_top _)
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

private theorem toQuot_injective {V₀ V U : Subgroup G} (hV₀V : V₀ ≤ V) (hinf : U ⊓ V₀ = ⊥) :
    Function.Injective
      fun x : V₀ => (QuotientGroup.mk (⟨x.1, hV₀V x.2⟩ : V) : V ⧸ U.subgroupOf V) := by
  intro x y hxy
  have hxy' : ((⟨x.1, hV₀V x.2⟩ : V) : V ⧸ U.subgroupOf V) =
      ((⟨y.1, hV₀V y.2⟩ : V) : V ⧸ U.subgroupOf V) := hxy
  have hmem' := QuotientGroup.eq.1 hxy'
  have hmem : x.1⁻¹ * y.1 ∈ U := hmem'
  have hmem₀ : x.1⁻¹ * y.1 ∈ V₀ := V₀.mul_mem (V₀.inv_mem x.2) y.2
  have h1 : x.1⁻¹ * y.1 ∈ U ⊓ V₀ := Subgroup.mem_inf.2 ⟨hmem, hmem₀⟩
  rw [hinf, Subgroup.mem_bot] at h1
  exact Subtype.ext (inv_mul_eq_one.1 h1)

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem inf_eq_bot (h : Cex15 M V₀ V U S) : U ⊓ V₀ = ⊥ := by
  by_contra hne
  obtain ⟨⟨w, hwU, hwV⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  apply h.not_le
  intro g hg
  have hgc : g ∈ centralizer ({w} : Set G) :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hwU)) hg
  exact h.hyp.centralizer_le hwV (fun h1 => hw1 (Subtype.ext h1)) hgc

theorem mQuot_eq (h : Cex15 M V₀ V U S) : E3.mQuot V U = mSub V₀ := by
  have hH := h.hyp
  have hinj := toQuot_injective hH.h6.le h.inf_eq_bot
  have hcard : Nat.card V₀ ≤ Nat.card (V ⧸ U.subgroupOf V) :=
    Nat.card_le_card_of_injective _ hinj
  have hrel : Nat.card (V ⧸ U.subgroupOf V) = 2 ^ E3.mQuot V U :=
    E3.relIndex_eq_two_pow hH.isPGroup U
  have h0 : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub (hH.isPGroup.to_le hH.h6.le)
  have hle1 : mSub V₀ ≤ E3.mQuot V U := by
    rw [h0, hrel] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  have hle2 : E3.mQuot V U ≤ mSub V₀ := by
    have := h.mquot.le.trans h.small
    exact_mod_cast this
  exact le_antisymm hle2 hle1

theorem decomp (h : Cex15 M V₀ V U S) {v : G} (hv : v ∈ V) :
    ∃ w ∈ V₀, ∃ u ∈ U, v = w * u := by
  have hH := h.hyp
  have hinj := toQuot_injective hH.h6.le h.inf_eq_bot
  have hrel : Nat.card (V ⧸ U.subgroupOf V) = 2 ^ E3.mQuot V U :=
    E3.relIndex_eq_two_pow hH.isPGroup U
  have h0 : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub (hH.isPGroup.to_le hH.h6.le)
  have hbij := hinj.bijective_of_nat_card_le (le_of_eq (by rw [hrel, h0, h.mQuot_eq]))
  obtain ⟨x, hx⟩ := hbij.2 (QuotientGroup.mk (⟨v, hv⟩ : V))
  have hx' : ((⟨x.1, hH.h6.le x.2⟩ : V) : V ⧸ U.subgroupOf V) =
      ((⟨v, hv⟩ : V) : V ⧸ U.subgroupOf V) := hx
  have hu' := QuotientGroup.eq.1 hx'
  have hu : x.1⁻¹ * v ∈ U := hu'
  exact ⟨x.1, x.2, x.1⁻¹ * v, hu, by group⟩

theorem sup_eq (h : Cex15 M V₀ V U S) : U ⊔ V₀ = V := by
  refine le_antisymm (sup_le h.le h.hyp.h6.le) fun v hv => ?_
  obtain ⟨w, hw, u, hu, rfl⟩ := h.decomp hv
  exact (U ⊔ V₀).mul_mem (Subgroup.mem_sup_right hw) (Subgroup.mem_sup_left hu)

theorem ne_bot (h : Cex15 M V₀ V U S) : U ≠ ⊥ := by
  intro hU
  have h1 := h.sup_eq
  rw [hU, bot_sup_eq] at h1
  exact h.hyp.h6.ne_top h.hyp.ne_bot h1

theorem V_le_S (h : Cex15 M V₀ V U S) : V ≤ S := by
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

theorem centralizer_le_cTilde (h : Cex15 M V₀ V U S) :
    M ⊓ centralizer (U : Set G) ≤ F11.CTilde M V₀ V := by
  intro x hx
  have hH := h.hyp
  have hxN : x ∈ normalizer (V₀ : Set G) := hH.h6.le_normalizer₀ hx.1
  refine FourteenTwo.mem_cTilde_iff_comm.2 ⟨hx.1, hxN, fun v hv => ?_⟩
  obtain ⟨w, hw, u, hu, rfl⟩ := h.decomp hv
  have hxu : x * u * x⁻¹ = u := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 hx.2 u hu).symm
  have hxw : x * w * x⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hxN w).1 hw
  have e : x * (w * u) * x⁻¹ * (w * u)⁻¹ = (x * w * x⁻¹) * w⁻¹ := by
    calc x * (w * u) * x⁻¹ * (w * u)⁻¹
        = (x * w * x⁻¹) * (x * u * x⁻¹) * u⁻¹ * w⁻¹ := by group
      _ = (x * w * x⁻¹) * w⁻¹ := by rw [hxu]; group
  rw [e]
  exact V₀.mul_mem hxw (V₀.inv_mem hw)

theorem one_lt_mSub (h : Cex15 M V₀ V U S) : 1 < mSub V₀ := by
  by_contra hle
  have hle' : mSub V₀ ≤ 1 := not_lt.1 hle
  have hH := h.hyp
  have hcard : Nat.card V₀ = 2 := by
    have h1 : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub (hH.isPGroup.to_le hH.h6.le)
    have h2 : 1 < Nat.card V₀ := (Subgroup.one_lt_card_iff_ne_bot V₀).2 hH.ne_bot
    have h3 : mSub V₀ = 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle' with h0 | h0
      · rw [h0] at h1; omega
      · exact h0
    rw [h1, h3]; rfl
  have h14 := FourteenTwo.fourteen_three_rMV hH.h6.elemAbelian hH.h6.le hcard
    hH.h6.normalizer_eq.symm.le hH.normalizer₀.symm (hH.h6.conjGenerated hH.ne_bot) hH.s14c
    hH.exists_cTilde_not_le
  have h3 : rMV M V ≤ 1 := h.small.trans (by exact_mod_cast hle')
  exact absurd h14 (not_lt.2 h3)

end Cex15

end CFSG.LocalAnalysis.WeakClosure81
