module

public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenMod
public import CFSG.LocalAnalysis.WeakClosure81.FourteenSeven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_barSub_eq_relIndex {M V₀ V B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G)) (hBM : B ≤ M) :
    Nat.card (barSub V₀ V hV B) = (B ⊓ F11.CTilde M V₀ V).relIndex B := by
  have hB : B ≤ stabTil V₀ V := hBM.trans (le_stabTil hM hM₀)
  let f : B →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hB)
  have hrange : f.range = barSub V₀ V hV B := by
    unfold barSub
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : f.ker = (B ⊓ F11.CTilde M V₀ V).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_cTilde_iff hV hM]
    constructor
    · intro h1
      exact ⟨b.2, hBM b.2, hB b.2, h1⟩
    · rintro ⟨_, _, _, h1⟩
      exact h1
  rw [← hrange, ← Subgroup.index_ker, hker]
  rfl

theorem imgTil_sup_V₀ {V₀ V N : Subgroup G} (hV : IsElemAbelian 2 V) (hN : N ≤ V)
    (hV₀ : V₀ ≤ V) : imgTil V₀ V hV (N ⊔ V₀) = imgTil V₀ V hV N := by
  have h1 : intSub V hV (N ⊔ V₀) = intSub V hV N ⊔ intSub V hV V₀ :=
    Subgroup.subgroupOf_sup hN hV₀
  have h2 : (intSub V hV V₀).map (mkTil V₀ V hV) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    exact (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 hx
  unfold imgTil
  rw [h1, Subgroup.map_sup, h2, sup_bot_eq]

theorem card_barSub_mul_index_eq {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g)
    (hgen : GenHyp M V g) :
    Nat.card (barSub V₀ V h.elemAbelian (BOf M V g)) *
        (imgTil V₀ V h.elemAbelian (UOf M V g)).index =
      (imgTil V₀ V h.elemAbelian (NOf M V g)).index := by
  have hV := h.elemAbelian
  have hM : M ≤ normalizer (V : Set G) := h.normalizer_eq.symm.le
  have h1 := card_barSub_eq_relIndex (B := BOf M V g) hV hM h.le_normalizer₀ inf_le_right
  have h2 := six_four_five h hgen
  have hNV : NOf M V g ≤ V := inf_le_left.trans inf_le_left
  have hUidx : (imgTil V₀ V hV (UOf M V g)).index = (UOf M V g).relIndex V := by
    rw [← card_quotient_imgTil hV (V₀_le_UOf h hgen)]
    rfl
  have hNidx : (imgTil V₀ V hV (NOf M V g)).index =
      (V ⊓ Subgroup.centralizer (BOf M V g : Set G)).relIndex V := by
    rw [six_four_four_centralizer_V h, ← imgTil_sup_V₀ hV hNV h.le,
      ← card_quotient_imgTil hV (le_sup_right : V₀ ≤ NOf M V g ⊔ V₀)]
    rfl
  rw [hUidx, hNidx, h1]
  exact h2

theorem imgTil_NOf_le_fixV_barSub {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g) :
    imgTil V₀ V h.elemAbelian (NOf M V g) ≤
      fixV (barSub V₀ V h.elemAbelian (BOf M V g)) := by
  have hV := h.elemAbelian
  intro q hq
  obtain ⟨x, hxN, rfl⟩ := (mem_imgTil V₀ V hV _ q).1 hq
  rw [mem_fixV]
  intro φ hφ
  obtain ⟨d, hdB, rfl⟩ := (mem_barSub V₀ V hV (BOf M V g) φ).1 hφ
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
  have hCB : x.val ∈ V ⊓ Subgroup.centralizer (BOf M V g : Set G) := by
    rw [six_four_four_centralizer_V h]
    exact Subgroup.mem_sup_left hxN
  have hcomm : (d : G) * x.val = x.val * (d : G) :=
    Subgroup.mem_centralizer_iff.1 hCB.2 (d : G) hdB
  rw [show (d : G) * x.val * (d : G)⁻¹ * x.val⁻¹ = 1 by rw [hcomm]; group]
  exact V₀.one_mem

private theorem fixV_barSub_BOf_eq_imgTil_NOf {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) :
    fixV (barSub V₀ V h.elemAbelian (BOf M V g)) = imgTil V₀ V h.elemAbelian (NOf M V g) := by
  have hNV : NOf M V g ≤ V := inf_le_left.trans inf_le_left
  have h1 := imgTil_preTil V₀ V h.elemAbelian (fixV (barSub V₀ V h.elemAbelian (BOf M V g)))
  rw [preTil_fixV_barSub_BOf h hgen, imgTil_sup_V₀ h.elemAbelian hNV h.le] at h1
  exact h1.symm

theorem fixV_zpowers_le_imgTil_UOf {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) {b : MulAut (Vtil V₀ V h.elemAbelian)}
    (hb : b ∈ barSub V₀ V h.elemAbelian (BOf M V g)) (hb1 : b ≠ 1) :
    fixV (Subgroup.zpowers b) ≤ imgTil V₀ V h.elemAbelian (UOf M V g) := by
  have hV := h.elemAbelian
  have hM : M ≤ normalizer (V : Set G) := h.normalizer_eq.symm.le
  obtain ⟨⟨β, hβs⟩, hβB, rfl⟩ := (mem_barSub V₀ V hV (BOf M V g) b).1 hb
  have hβC : β ∉ F11.CTilde M V₀ V := fun hc => by
    obtain ⟨-, hs, h1⟩ := (mem_cTilde_iff hV hM).1 hc
    exact hb1 h1
  intro w hw
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV w
  have hDB : Subgroup.zpowers β ≤ BOf M V g := Subgroup.zpowers_le.2 hβB
  have hDC : ¬ Subgroup.zpowers β ≤ F11.CTilde M V₀ V := fun hle =>
    hβC (hle (Subgroup.mem_zpowers β))
  have h43 := six_four_three_of_gen h hgen hDB hDC
  have hcomm : ∀ d ∈ Subgroup.zpowers β, ⁅x.val, d⁆ ∈ V₀ := by
    intro d hd
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    have hds : β ^ i ∈ stabTil V₀ V := (stabTil V₀ V).zpow_mem hβs i
    have hmem : actTil V₀ V hV ⟨β ^ i, hds⟩ ∈ Subgroup.zpowers (actTil V₀ V hV ⟨β, hβs⟩) := by
      have : (⟨β ^ i, hds⟩ : stabTil V₀ V) = ⟨β, hβs⟩ ^ i := Subtype.ext (by simp)
      rw [this, map_zpow]
      exact Subgroup.zpow_mem_zpowers _ i
    have hfix : actTil V₀ V hV ⟨β ^ i, hds⟩ (mkTil V₀ V hV x) = mkTil V₀ V hV x :=
      (mem_fixV.1 hw) _ hmem
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix
    have hdv : ⁅β ^ i, x.val⁆ ∈ V₀ := hfix
    rw [show ⁅x.val, β ^ i⁆ = ⁅β ^ i, x.val⁆⁻¹ from (commutatorElement_inv (β ^ i) x.val).symm]
    exact V₀.inv_mem hdv
  have hxU : x.val ∈ UOf M V g := h43.1 (h43.2 x.val x.val_mem hcomm)
  exact (mem_imgTil V₀ V hV _ _).2 ⟨x, hxU, rfl⟩

theorem apply_mul_inv_mem_imgTil_NOf {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) {b : MulAut (Vtil V₀ V h.elemAbelian)}
    (hb : b ∈ barSub V₀ V h.elemAbelian (BOf M V g)) (hb1 : b ≠ 1)
    {u : Vtil V₀ V h.elemAbelian} (hu : u ∈ imgTil V₀ V h.elemAbelian (UOf M V g)) :
    b u * u⁻¹ ∈ imgTil V₀ V h.elemAbelian (NOf M V g) := by
  have hV := h.elemAbelian
  have hM : M ≤ normalizer (V : Set G) := h.normalizer_eq.symm.le
  obtain ⟨⟨β, hβs⟩, hβB, rfl⟩ := (mem_barSub V₀ V hV (BOf M V g) b).1 hb
  have hβC : β ∉ F11.CTilde M V₀ V := fun hc => by
    obtain ⟨-, hs, h1⟩ := (mem_cTilde_iff hV hM).1 hc
    exact hb1 h1
  have key := (mem_imgTil_UOf_iff h hgen hβB hβC hβs u).1 hu
  rw [fixV_barSub_BOf_eq_imgTil_NOf h hgen] at key
  have := (imgTil V₀ V hV (NOf M V g)).inv_mem key
  rwa [mul_inv_rev, inv_inv] at this

theorem mem_imgTil_UOf_of_apply_mul_inv_mem {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) {b : MulAut (Vtil V₀ V h.elemAbelian)}
    (hb : b ∈ barSub V₀ V h.elemAbelian (BOf M V g)) (hb1 : b ≠ 1)
    {w : Vtil V₀ V h.elemAbelian} (hw : b w * w⁻¹ ∈ imgTil V₀ V h.elemAbelian (NOf M V g)) :
    w ∈ imgTil V₀ V h.elemAbelian (UOf M V g) := by
  have hV := h.elemAbelian
  have hM : M ≤ normalizer (V : Set G) := h.normalizer_eq.symm.le
  obtain ⟨⟨β, hβs⟩, hβB, rfl⟩ := (mem_barSub V₀ V hV (BOf M V g) b).1 hb
  have hβC : β ∉ F11.CTilde M V₀ V := fun hc => by
    obtain ⟨-, hs, h1⟩ := (mem_cTilde_iff hV hM).1 hc
    exact hb1 h1
  rw [← fixV_barSub_BOf_eq_imgTil_NOf h hgen] at hw
  have := (fixV (barSub V₀ V hV (BOf M V g))).inv_mem hw
  rw [mul_inv_rev, inv_inv] at this
  exact (mem_imgTil_UOf_iff h hgen hβB hβC hβs w).2 this

theorem rkIdx_imgTil_UOf_le {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g)
    (hgen : GenHyp M V g) : rkIdx (imgTil V₀ V h.elemAbelian (UOf M V g)) ≤ n := by
  rw [← mQuot_UOf_eq_rkIdx h hgen]
  exact mQuot_UOf_le h

end CFSG.LocalAnalysis.WeakClosure81
