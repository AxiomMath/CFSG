module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_9
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_10
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_4

namespace CFSG
end CFSG
open CFSG

/-!
# Scratch formalization for Peterfalvi Section 4, items (4.5)–(4.10)

This file is the active PF section-4 continuation for items `(4.5)`--`(4.10)`.
It used to live under `Scratch/`; the live PF work is now kept here so local
helpers for the remaining PF section-5 bridges stay next to the theorem shells.

The current goal is to:

1. fix the book-facing statements for PF `(4.5)` through `(4.10)`,
2. keep the interfaces Lean-elaborating, and
3. expose top-down theorem shells so later proof work can fill helpers in
   place rather than redesigning the statements again.

For `(4.8)` and `(4.10)` the displayed formulas were checked directly against
`PF.pdf` page images rendered into `Scratch/`.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section4Scratch

universe u v

open Section1 Section2 Section3 Section4
open _root_.CFSG.Section4Scratch

private theorem conjugateIn_symm_pf45
    {G : Type*} [Group G] {a b : G}
    (h : Section2.conjugateIn a b) :
    Section2.conjugateIn b a := by
  rcases h with ⟨x, hx⟩
  refine ⟨x⁻¹, ?_⟩
  have hx' := congrArg (fun t : G => x⁻¹ * t * x) hx
  simpa [Section2.conjBy, mul_assoc] using hx'.symm

private theorem exists_ne_one_mem_of_natCard_ne_one_pf45
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (hH : Nat.card H ≠ 1) :
    ∃ x, x ∈ H ∧ x ≠ 1 := by
  by_contra hcontra
  have hforall : ∀ x : H, x = 1 := by
    intro x
    by_contra hx
    have hx' : (x : G) ≠ 1 := by
      intro hx1
      apply hx
      apply Subtype.ext
      exact hx1
    exact hcontra ⟨x, x.2, hx'⟩
  have hsubsingleton : Subsingleton H := by
    refine ⟨?_⟩
    intro x y
    rw [hforall x, hforall y]
  have hcard : Nat.card H = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨1, fun x => hforall x⟩
  exact hH hcard

private theorem internalSemidirectProduct_mul_unique_pf45
    {G : Type u} [Group G] {C H K : Subgroup G}
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
    have hinf : h₂⁻¹ * h₁ ∈ H ⊓ K := Subgroup.mem_inf.mpr ⟨hmemH, hmemK⟩
    simpa [h.inf_eq_bot] using hinf
  have hh_eq_one : h₂⁻¹ * h₁ = 1 := by simpa using hbot
  have hh : h₁ = h₂ := by
    calc
      h₁ = h₂ * (h₂⁻¹ * h₁) := by simp
      _ = h₂ := by simp [hh_eq_one]
  have hk : k₁ = k₂ := by
    have hmul' := congrArg (fun z : G => h₂⁻¹ * z) hmul
    simpa [hh, mul_assoc] using hmul'
  exact ⟨hh, hk⟩

private theorem internalSemidirectProduct_card_mul_pf45
    {G : Type u} [Group G] [Finite G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) :
    Nat.card C = Nat.card H * Nat.card K := by
  classical
  let f : H × K → C := fun p =>
    ⟨(p.1 : G) * (p.2 : G),
      C.mul_mem (h.left_le p.1.2) (h.right_le p.2.2)⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
    apply Prod.ext
    · apply Subtype.ext
      exact (internalSemidirectProduct_mul_unique_pf45 h h₁.2 h₂.2 k₁.2 k₂.2
        (Subtype.ext_iff.mp heq)).1
    · apply Subtype.ext
      exact (internalSemidirectProduct_mul_unique_pf45 h h₁.2 h₂.2 k₁.2 k₂.2
        (Subtype.ext_iff.mp heq)).2
  have hf_surj : Function.Surjective f := by
    intro c
    rcases h.mul_surjective (c : G) c.2 with ⟨h₀, hh₀, k₀, hk₀, hc⟩
    refine ⟨(⟨h₀, hh₀⟩, ⟨k₀, hk₀⟩), ?_⟩
    apply Subtype.ext
    exact hc.symm
  have hcard_equiv : Nat.card (H × K) = Nat.card C :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  have hprod : Nat.card (H × K) = Nat.card H * Nat.card K := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_prod H K
  rw [← hcard_equiv, hprod]

private theorem w2_le_K_of_hypothesis_4_2_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W) :
    W2 ≤ K := by
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, hcard1, _hcyc2, _hcard2,
      hcent, _hW1, _hW2, _hW, _hodd⟩
  rcases exists_ne_one_mem_of_natCard_ne_one_pf45 W1 hcard1 with ⟨x, hxW1, hx1⟩
  have hcentx : Section2.centralizerIn K x = W2 := by
    exact hcent ⟨x, hxW1⟩ (by
      intro hxsub
      exact hx1 (Subtype.ext_iff.mp hxsub))
  intro z hz
  have hz' : z ∈ Section2.centralizerIn K x := by
    simpa [hcentx] using hz
  exact (Subgroup.mem_inf.mp hz').1

private theorem normal_K_of_hypothesis_4_2_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W) :
    K.Normal := by
  rcases h42 with ⟨hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, _hW, _hodd⟩
  refine ⟨?_⟩
  intro k hk x
  rcases hsemi.mul_surjective x (by trivial) with ⟨h, hh, w, hw, rfl⟩
  have hwk : Section2.conjBy w k ∈ K :=
    hsemi.right_normalizes_left w hw k hk
  show Section2.conjBy (h * w) k ∈ K
  simpa [Section2.conjBy, mul_assoc] using
    K.mul_mem (K.mul_mem hh hwk) (K.inv_mem hh)

private theorem natCard_quotient_K_eq_natCard_W1_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (hKnorm : K.Normal)
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W) :
    Nat.card (L ⧸ K) = Nat.card W1 := by
  let : K.Normal := hKnorm
  rcases h42 with ⟨hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, _hW, _hodd⟩
  let q : W1 →* (L ⧸ K) := (QuotientGroup.mk' K).comp W1.subtype
  have hq_surj : Function.Surjective q := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K x
    rcases hsemi.mul_surjective g (by trivial) with ⟨k, hk, w, hw, hkw⟩
    refine ⟨⟨w, hw⟩, ?_⟩
    change QuotientGroup.mk' K w = QuotientGroup.mk' K g
    rw [hkw]
    have hk_one : QuotientGroup.mk' K k = 1 :=
      (QuotientGroup.eq_one_iff (N := K) (x := k)).2 hk
    calc
      QuotientGroup.mk' K w = 1 * QuotientGroup.mk' K w := by simp
      _ = QuotientGroup.mk' K k * QuotientGroup.mk' K w := by rw [hk_one]
      _ = QuotientGroup.mk' K (k * w) := by simp
  have hq_inj : Function.Injective q := by
    intro x y hxy
    apply Subtype.ext
    have hxy_one : q (x * y⁻¹) = 1 := by
      calc
        q (x * y⁻¹) = q x * (q y)⁻¹ := by simp [q]
        _ = 1 := by simp [hxy]
    have hmemK : ((x : L) * (y : L)⁻¹) ∈ K := by
      exact (QuotientGroup.eq_one_iff (N := K) (x := ((x : L) * (y : L)⁻¹))).1
        (by simpa [q] using hxy_one)
    have hmemW1 : ((x : L) * (y : L)⁻¹) ∈ W1 :=
      W1.mul_mem x.2 (W1.inv_mem y.2)
    have hbot : ((x : L) * (y : L)⁻¹) ∈ (⊥ : Subgroup L) := by
      have hinf : ((x : L) * (y : L)⁻¹) ∈ K ⊓ W1 :=
        Subgroup.mem_inf.mpr ⟨hmemK, hmemW1⟩
      simpa [hsemi.inf_eq_bot] using hinf
    have hxy_inv : (x : L) * (y : L)⁻¹ = 1 := by
      simpa using hbot
    calc
      (x : L) = ((x : L) * (y : L)⁻¹) * y := by simp [mul_assoc]
      _ = y := by simp [hxy_inv]
  exact (Nat.card_congr (Equiv.ofBijective q ⟨hq_inj, hq_surj⟩)).symm

private theorem isCyclic_quotient_K_of_hypothesis_4_2_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (hKnorm : K.Normal)
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W) :
    IsCyclic (L ⧸ K) := by
  let : K.Normal := hKnorm
  rcases h42 with ⟨hsemi, _hHall, hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, _hW, _hodd⟩
  let q : W1 →* (L ⧸ K) := (QuotientGroup.mk' K).comp W1.subtype
  have hq_surj : Function.Surjective q := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K x
    rcases hsemi.mul_surjective g (by trivial) with ⟨k, hk, w, hw, hkw⟩
    refine ⟨⟨w, hw⟩, ?_⟩
    change QuotientGroup.mk' K w = QuotientGroup.mk' K g
    rw [hkw]
    have hk_one : QuotientGroup.mk' K k = 1 :=
      (QuotientGroup.eq_one_iff (N := K) k).2 hk
    calc
      QuotientGroup.mk' K w = 1 * QuotientGroup.mk' K w := by simp
      _ = QuotientGroup.mk' K k * QuotientGroup.mk' K w := by rw [hk_one]
      _ = QuotientGroup.mk' K (k * w) := by simp
  let : IsCyclic W1 := hcyc1
  exact isCyclic_of_surjective q hq_surj

private theorem mem_W2_of_mem_K_and_mem_W_of_hypothesis_4_2_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    {x : L} (hxK : x ∈ K) (hxW : x ∈ W) :
    x ∈ W2 := by
  have hW2leK : W2 ≤ K := w2_le_K_of_hypothesis_4_2_pf45 h42
  rcases h42 with ⟨hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, hW2, hDirect, _hodd⟩
  rcases hDirect.mul_surjective x hxW with ⟨w1, hw1, w2, hw2, hw12⟩
  have hw2K : (w2 : L) ∈ K := hW2leK hw2
  have hw1K : (w1 : L) ∈ K := by
    have hw1eq : (w1 : L) = x * (w2 : L)⁻¹ := by
      calc
        (w1 : L) = (w1 : L) * ((w2 : L) * (w2 : L)⁻¹) := by simp
        _ = ((w1 : L) * (w2 : L)) * (w2 : L)⁻¹ := by simp [mul_assoc]
        _ = x * (w2 : L)⁻¹ := by rw [hw12]
    rw [hw1eq]
    exact K.mul_mem hxK (K.inv_mem hw2K)
  have hw1bot : (w1 : L) ∈ (⊥ : Subgroup L) := by
    have hinf : (w1 : L) ∈ K ⊓ W1 := Subgroup.mem_inf.mpr ⟨hw1K, hw1⟩
    simpa [hsemi.inf_eq_bot] using hinf
  have hw1one : (w1 : L) = 1 := by
    simpa using hw1bot
  have hxeq : x = (w2 : L) := by
    calc
      x = (w1 : L) * (w2 : L) := hw12
      _ = (w2 : L) := by simp [hw1one]
  simpa [hxeq] using hw2

private theorem dadeSupport_trivial_eq_conjugateSet_pf45
    {G : Type*} [Group G] (A : Set G) :
    Section2.dadeSupport A (fun _ : G => ⊥) = Section2.conjugateSet A := by
  ext g
  constructor
  · intro hg
    rcases hg with ⟨a, ha, k, hk, hconj⟩
    have hk1 : k = 1 := by simpa using hk
    subst hk1
    have hconj' : Section2.conjugateIn g a := by
      simpa using hconj
    exact ⟨a, ha, conjugateIn_symm_pf45 hconj'⟩
  · intro hg
    rcases hg with ⟨a, ha, hconj⟩
    have hconj' : Section2.conjugateIn g a := conjugateIn_symm_pf45 hconj
    exact ⟨a, ha, 1, by simp, by simpa using hconj'⟩

private theorem omega_eq_baseRow_of_mem_W2_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → ClassFunction W}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) {x : W} (hx : (x : L) ∈ W2) :
    ω i j x = ω i0 j x := by
  have hleft : ω i j0 x = 1 := by
    have hker := hω.left_kernel i ⟨x, hx⟩
    simpa [hω.degree_one i j0] using hker
  calc
    ω i j x = ω i j0 x * ω i0 j x := hω.product i j x
    _ = ω i0 j x := by simp [hleft]

private theorem omegaRowDifference_CFOn_wMinusW2_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → ClassFunction W}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) :
    Section2.CFOn W ((W : Set L) \ (W2 : Set L)) (ω i j - ω i0 j) := by
  constructor
  · intro x g
    simp [hω.is_class i j x g, hω.is_class i0 j x g]
  · intro x hx
    have hxW2 : (x : L) ∈ W2 := by
      by_contra hxnot
      exact hx ⟨x.2, hxnot⟩
    have hEq : ω i j x = ω i0 j x :=
      omega_eq_baseRow_of_mem_W2_pf45 hω i j hxW2
    simp [Pi.sub_apply, hEq]


private theorem not_mem_conjugateSet_wMinusW2_of_mem_K_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    (k : K) :
    (k : L) ∉ Section2.conjugateSet ((W : Set L) \ (W2 : Set L)) := by
  have hKnorm : K.Normal := normal_K_of_hypothesis_4_2_pf45 h42
  intro hkconj
  rcases hkconj with ⟨a, ha, hconj⟩
  rcases hconj with ⟨x, hx⟩
  have haK : a ∈ K := by
    have hkconj' : Section2.conjBy x a ∈ K := by
      simp [hx]
    have := Subgroup.Normal.conj_mem hKnorm (Section2.conjBy x a) hkconj' x⁻¹
    simpa [Section2.conjBy, mul_assoc] using this
  have haW2 : a ∈ W2 :=
    mem_W2_of_mem_K_and_mem_W_of_hypothesis_4_2_pf45 h42 haK ha.1
  exact ha.2 haW2

private theorem natCard_W1_coprime_natCard_K_of_hypothesis_4_2_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W) :
    Nat.Coprime (Nat.card W1) (Nat.card K) := by
  rcases h42 with ⟨hsemi, hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, _hW, _hodd⟩
  rcases hHall with ⟨π, hHall⟩
  have hcard_top : Nat.card (⊤ : Subgroup L) = Nat.card K * Nat.card W1 := by
    simpa using internalSemidirectProduct_card_mul_pf45 hsemi
  have hindex_eq : W1.index = Nat.card K := by
    have hmul1 : W1.index * Nat.card W1 = Nat.card L := Subgroup.index_mul_card (H := W1)
    have hmul2 : Nat.card K * Nat.card W1 = Nat.card L := by
      simpa using hcard_top.symm
    exact Nat.mul_right_cancel (Nat.card_pos (α := W1)) (hmul1.trans hmul2.symm)
  simpa [hindex_eq] using IsHallSubgroup.card_coprime_index (π := π) (H := W1) hHall

private theorem conjugateSet_mono_pf45
    {G : Type*} [Group G] {S T : Set G}
    (hST : S ⊆ T) :
    Section2.conjugateSet S ⊆ Section2.conjugateSet T := by
  intro g hg
  rcases hg with ⟨s, hs, hconj⟩
  exact ⟨s, hST hs, hconj⟩

private theorem subgroupCosetByElement_W2_subset_wMinusW2_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    {w : L} (hwW1 : w ∈ W1) (hw1 : w ≠ 1) :
    Section2.subgroupCosetByElement W2 w ⊆ ((W : Set L) \ (W2 : Set L)) := by
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, hW1, hW2, hW, _hodd⟩
  intro y hy
  rcases hy with ⟨z, hzW2, rfl⟩
  refine ⟨W.mul_mem (hW2 hzW2) (hW1 hwW1), ?_⟩
  intro hzwW2
  have hwW2 : w ∈ W2 := by
    have hwW2' : z⁻¹ * (z * w) ∈ W2 := W2.mul_mem (W2.inv_mem hzW2) hzwW2
    simpa [mul_assoc] using hwW2'
  have hbot : w ∈ (⊥ : Subgroup L) := by
    have hinf : w ∈ W1 ⊓ W2 := Subgroup.mem_inf.mpr ⟨hwW1, hwW2⟩
    simpa [hW.inf_eq_bot] using hinf
  exact hw1 (by simpa using hbot)

private theorem exists_conjugateSet_subgroupCosetByElement_W2_of_not_mem_K_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    {x : L} (hxK : x ∉ K) :
    ∃ w : L, w ∈ W1 ∧ w ≠ 1 ∧
      x ∈ Section2.conjugateSet (Section2.subgroupCosetByElement W2 w) := by
  have h42' := h42
  rcases h42 with ⟨hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      hcent, _hW1, _hW2, _hW, _hodd⟩
  have hKnorm : K.Normal := normal_K_of_hypothesis_4_2_pf45 h42'
  let : K.Normal := hKnorm
  have hcopW1K := natCard_W1_coprime_natCard_K_of_hypothesis_4_2_pf45 h42'
  rcases hsemi.mul_surjective x (by trivial) with ⟨k, hkK, w, hwW1, rfl⟩
  have hw1 : w ≠ 1 := by
    intro hw
    apply hxK
    simpa [hw] using hkK
  have hcopwK : Nat.Coprime (orderOf w) (Nat.card K) := by
    exact Nat.Coprime.of_dvd_left (Subgroup.orderOf_dvd_natCard W1 hwW1) hcopW1K
  have hnormSet : Section2.normalizesSet (K : Set L) w := by
    intro g
    constructor
    · intro hg
      have hg' : w⁻¹ * (w * g * w⁻¹) * w ∈ K := by
        simpa [mul_assoc] using
          (show K.Normal from inferInstance).conj_mem (w * g * w⁻¹) hg w⁻¹
      simpa [Section2.conjBy, mul_assoc] using hg'
    · intro hg
      simpa [Section2.conjBy] using
        (show K.Normal from inferInstance).conj_mem g hg w
  rcases Section2.proposition_2_1 w K hnormSet hcopwK with
    ⟨reps, _hcard, _hreps, _hdisj, hcover⟩
  have hxCoset : k * w ∈ Section2.subgroupCosetByElement K w := by
    exact ⟨k, hkK, rfl⟩
  have hxPieceSet :
      k * w ∈ {z | ∃ r ∈ reps, z ∈ Section2.conjugateCosetPiece K w r} := by
    simpa [hcover] using hxCoset
  rcases hxPieceSet with ⟨r, hr, hxpiece⟩
  have hxConjW2 :
      k * w ∈ Section2.conjugateSet (Section2.subgroupCosetByElement W2 w) := by
    have hcentw : Section2.centralizerIn K w = W2 := by
      exact hcent ⟨w, hwW1⟩ (by
        intro hwsub
        exact hw1 (Subtype.ext_iff.mp hwsub))
    have hxConjCent :
        k * w ∈ Section2.conjugateSet
          (Section2.subgroupCosetByElement (Section2.centralizerIn K w) w) := by
      rcases hxpiece with ⟨s, hs, hsx⟩
      refine ⟨s, hs, ?_⟩
      exact ⟨r, hsx.symm⟩
    simpa [hcentw] using hxConjCent
  exact ⟨w, hwW1, hw1, hxConjW2⟩

private theorem mem_conjugateSet_wMinusW2_of_not_mem_K_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    {x : L} (hxK : x ∉ K) :
    x ∈ Section2.conjugateSet ((W : Set L) \ (W2 : Set L)) := by
  rcases exists_conjugateSet_subgroupCosetByElement_W2_of_not_mem_K_pf45
      h42 hxK with ⟨w, hwW1, hw1, hx⟩
  exact conjugateSet_mono_pf45
    (subgroupCosetByElement_W2_subset_wMinusW2_pf45 h42 hwW1 hw1) hx

public theorem mem_K_of_not_mem_conjugateSet_wMinusW2_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    {x : L}
    (hx : x ∉ Section2.conjugateSet ((W : Set L) \ (W2 : Set L))) :
    x ∈ K := by
  by_contra hxK
  exact hx (mem_conjugateSet_wMinusW2_of_not_mem_K_pf45 h42 hxK)

/- When the subgroup `H` in Hypothesis `(4.6)` is all of `K`, the set `A`
contains every nonidentity element of `K`; the conjugate `W \\ W₂` part then
covers the remaining nonidentity elements of `L`. -/
public theorem puncturedSet_subset_a0Set_of_hypothesis_4_6_self
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {A : Set L}
    (h46 : hypothesis_4_6_statement K W1 W2 W K A) :
    puncturedSet ⊆ a0Set W2 W A := by
  intro x hx1
  change x ≠ 1 at hx1
  rcases h46 with ⟨h42, _hKnorm, _hW2K, _hKK, hcentA, _hAinK⟩
  by_cases hxK : x ∈ K
  · left
    apply hcentA
    refine Set.mem_iUnion.mpr ?_
    let xK : K := ⟨x, hxK⟩
    let xKne : {h : K // (h : L) ≠ 1} := ⟨xK, hx1⟩
    refine ⟨xKne, ?_⟩
    constructor
    · refine Subgroup.mem_inf.mpr ⟨hxK, ?_⟩
      rw [Section2.elementCentralizer, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      change x * x = x * x
      rfl
    · simpa using hx1
  · right
    exact mem_conjugateSet_wMinusW2_of_not_mem_K_pf45 h42 hxK

private theorem sign_ne_zero_pf45 {z : ℂ} (hz : Section1.IsSign z) : z ≠ 0 := by
  rcases hz with h | h <;> simp [h]

private theorem sign_mul_self_eq_one_pf45
    {z : ℂ} (hz : Section1.IsSign z) :
    z * z = 1 := by
  rcases hz with h | h <;> simp [h]

private theorem sign_star_eq_self_pf45
    {z : ℂ} (hz : Section1.IsSign z) :
    star z = z := by
  rcases hz with h | h <;> simp [h]


private theorem mem_subgroup_iff_conj_mem_pf45
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (x g : G) :
    x * g * x⁻¹ ∈ H ↔ g ∈ H := by
  constructor
  · intro hx
    have hx' : x⁻¹ * (x * g * x⁻¹) * x ∈ H := by
      simpa [mul_assoc] using (show H.Normal from inferInstance).conj_mem (x * g * x⁻¹) hx x⁻¹
    simpa [mul_assoc] using hx'
  · intro hg
    simpa using (show H.Normal from inferInstance).conj_mem g hg x

private theorem complex_norm_eq_one_of_pow_eq_one_pf45
    {z : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hz : z ^ n = 1) :
    ‖z‖ = 1 := by
  have hpow : ‖z‖ ^ n = (1 : ℝ) := by
    simpa [hz] using (norm_pow z n).symm
  have habs_pow : |(‖z‖ : ℝ) ^ n| = 1 := by
    rw [hpow, abs_one]
  have habs : |(‖z‖ : ℝ)| = 1 :=
    (abs_pow_eq_one (‖z‖ : ℝ) hn).mp habs_pow
  simpa [abs_of_nonneg (norm_nonneg z)] using habs

private theorem complex_eq_one_of_pow_eq_one_of_one_le_re_pf45
    {z : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hz : z ^ n = 1) (hre : 1 ≤ z.re) :
    z = 1 := by
  have hnorm : ‖z‖ = 1 := complex_norm_eq_one_of_pow_eq_one_pf45 hn hz
  have hre_le : z.re ≤ 1 := by
    simpa [hnorm] using Complex.re_le_norm z
  have hre_eq : z.re = 1 := le_antisymm hre_le hre
  have hnormSq : z.re * z.re + z.im * z.im = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply, hnorm] at h
    norm_num at h
    exact h
  have him_sq : z.im * z.im = 0 := by
    nlinarith
  have him : z.im = 0 := mul_self_eq_zero.mp him_sq
  exact Complex.ext (by simp [hre_eq]) (by simp [him])

private theorem eigenspace_finrank_pos_pf45
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (μ : f.Eigenvalues) :
    0 < Module.finrank ℂ (f.eigenspace (μ : ℂ)) := by
  have hμ : f.HasEigenvalue (μ : ℂ) :=
    Module.End.hasEigenvalue_of_hasGenEigenvalue μ.property
  rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨⟨v, ?_⟩, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    exact hv.apply_eq_smul
  · intro hzero
    have hvzero : v = 0 := by
      simpa using congrArg Subtype.val hzero
    exact hv.2 hvzero

private theorem finite_order_eq_one_of_trace_eq_finrank_pf45
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hpow : f ^ n = 1)
    (htrace : LinearMap.trace ℂ V f = (Module.finrank ℂ V : ℂ)) :
    f = 1 := by
  classical
  let m : f.Eigenvalues → ℝ :=
    fun μ => (Module.finrank ℂ (f.eigenspace (μ : ℂ)) : ℝ)
  have htrace_one :
      LinearMap.trace ℂ V f =
        ∑ μ : f.Eigenvalues, (μ : ℂ) * (m μ : ℂ) := by
    simpa [m] using
      (trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 1) hn hpow)
  have htrace_zero :
      (Module.finrank ℂ V : ℂ) =
        ∑ μ : f.Eigenvalues, (m μ : ℂ) := by
    have h0 :=
      trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 0) hn hpow
    simpa [m, LinearMap.trace_id] using h0
  have hsum_complex :
      ∑ μ : f.Eigenvalues, (μ : ℂ) * (m μ : ℂ) =
        ∑ μ : f.Eigenvalues, (1 : ℂ) * (m μ : ℂ) := by
    rw [← htrace_one, htrace, htrace_zero]
    simp
  have hsum_real :
      ∑ μ : f.Eigenvalues, (μ : ℂ).re * m μ =
        ∑ μ : f.Eigenvalues, (1 : ℝ) * m μ := by
    have h := congrArg Complex.re hsum_complex
    simpa [Complex.re_sum, Complex.re_mul_ofReal] using h
  have hle :
      ∀ μ ∈ (Finset.univ : Finset f.Eigenvalues),
        (μ : ℂ).re * m μ ≤ (1 : ℝ) * m μ := by
    intro μ hμ
    have hμpow : (μ : ℂ) ^ n = 1 :=
      eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
    have hnorm : ‖(μ : ℂ)‖ = 1 :=
      complex_norm_eq_one_of_pow_eq_one_pf45 hn hμpow
    have hre_le : (μ : ℂ).re ≤ 1 := by
      simpa [hnorm] using Complex.re_le_norm (μ : ℂ)
    exact mul_le_mul_of_nonneg_right hre_le (by positivity : 0 ≤ m μ)
  have heq_each :
      ∀ μ : f.Eigenvalues, (μ : ℂ).re * m μ = (1 : ℝ) * m μ := by
    intro μ
    exact (Finset.sum_eq_sum_iff_of_le hle).mp (by simpa using hsum_real) μ
      (Finset.mem_univ μ)
  have heigen_eq_one : ∀ μ : f.Eigenvalues, (μ : ℂ) = 1 := by
    intro μ
    have hpos_nat : 0 < Module.finrank ℂ (f.eigenspace (μ : ℂ)) :=
      eigenspace_finrank_pos_pf45 μ
    have hpos : 0 < m μ := by
      dsimp [m]
      exact_mod_cast hpos_nat
    have hre_eq : (μ : ℂ).re = 1 := by
      have h := heq_each μ
      nlinarith
    have hμpow : (μ : ℂ) ^ n = 1 :=
      eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
    exact complex_eq_one_of_pow_eq_one_of_one_le_re_pf45 hn hμpow (by linarith)
  have htop :
      f.eigenspace (1 : ℂ) = ⊤ := by
    have hsemi : f.IsSemisimple := end_isSemisimple_of_pow_eq_one f hn hpow
    have hiSup := eigenspace_iSup_eq_top_over_eigenvalues (f := f) hsemi
    apply top_unique
    rw [← hiSup]
    refine iSup_le ?_
    intro μ
    simp [heigen_eq_one μ]
  ext v
  have hv : v ∈ f.eigenspace (1 : ℂ) := by
    rw [htop]
    exact Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hv
  simpa using hv

private theorem subgroupInKernel'_of_eq_pf45
    {G : Type*} [Group G]
    {A : Subgroup G}
    {phi psi : ClassFunction G}
    (hEq : phi = psi)
    (hpsi : Section1.subgroupInKernel' psi A) :
    Section1.subgroupInKernel' phi A := by
  simpa [hEq] using hpsi

private theorem subgroupInKernel'_conjugateCharacter_iff_pf45
    {G : Type*} [Group G]
    {A : Subgroup G}
    {phi : ClassFunction G} :
    Section1.subgroupInKernel' (Section1.conjugateCharacter phi) A ↔
      Section1.subgroupInKernel' phi A := by
  constructor <;> intro h a
  · have ha := h a
    have ha' := congrArg star ha
    simpa [Section1.conjugateCharacter, Section1.degree] using ha'
  · have ha := h a
    simpa [Section1.conjugateCharacter, Section1.degree] using congrArg star ha

private theorem subgroupRestriction_conjugateCharacter_pf45
    {G : Type*} [Group G]
    (H : Subgroup G)
    (phi : ClassFunction G) :
    Section1.conjugateCharacter (Section1.subgroupRestriction H phi) =
      Section1.subgroupRestriction H (Section1.conjugateCharacter phi) := by
  rfl

private def dualCoannihilatorSubrepresentation_pf45
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V)
    (S : Subrepresentation rho.dual) : Subrepresentation rho where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule := by
    intro g v hv
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    have hS : rho.dual g⁻¹ f ∈ S.toSubmodule :=
      S.apply_mem_toSubmodule g⁻¹ hf
    have hvzero := hv (rho.dual g⁻¹ f) hS
    simpa only [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply,
      LinearMap.comp_apply] using hvzero

private theorem dualCoannihilatorSubrepresentation_eq_top_of_eq_bot_pf45
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V) :
    dualCoannihilatorSubrepresentation_pf45 rho (⊥ : Subrepresentation rho.dual) = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  change (⊥ : Submodule ℂ (Module.Dual ℂ V)).dualCoannihilator =
    (⊤ : Submodule ℂ V)
  simp

private theorem dualCoannihilatorSubrepresentation_eq_bot_of_eq_top_pf45
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V) :
    dualCoannihilatorSubrepresentation_pf45 rho (⊤ : Subrepresentation rho.dual) = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  change (⊤ : Submodule ℂ (Module.Dual ℂ V)).dualCoannihilator =
    (⊥ : Submodule ℂ V)
  simp

private theorem representation_dual_irreducible_of_pf45
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible ρ.dual := by
  let : Representation.IsIrreducible ρ := hρ
  refine
    { exists_pair_ne := ?_
      eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro hbotTop
    have hcong :=
      congrArg (dualCoannihilatorSubrepresentation_pf45 ρ) hbotTop
    have htop : (⊤ : Subrepresentation ρ) = ⊥ := by
      rw [dualCoannihilatorSubrepresentation_eq_top_of_eq_bot_pf45 ρ,
        dualCoannihilatorSubrepresentation_eq_bot_of_eq_top_pf45 ρ] at hcong
      exact hcong
    exact IsSimpleOrder.bot_ne_top (α := Subrepresentation ρ) htop.symm
  · intro S
    have hN := eq_bot_or_eq_top (dualCoannihilatorSubrepresentation_pf45 ρ S)
    rcases hN with hNbot | hNtop
    · right
      apply Subrepresentation.toSubmodule_injective
      have hdual :
          S.toSubmodule.dualCoannihilator.dualAnnihilator = S.toSubmodule :=
        Subspace.dualCoannihilator_dualAnnihilator_eq
      have hNsub : S.toSubmodule.dualCoannihilator = ⊥ := by
        have htmp := congrArg Subrepresentation.toSubmodule hNbot
        change S.toSubmodule.dualCoannihilator = (⊥ : Submodule ℂ V) at htmp
        exact htmp
      rw [hNsub] at hdual
      change S.toSubmodule = (⊤ : Submodule ℂ (Module.Dual ℂ V))
      simpa only [Submodule.dualAnnihilator_bot] using hdual.symm
    · left
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm ?_ bot_le
      intro f hf
      rw [Submodule.mem_bot]
      ext v
      have hNsub : S.toSubmodule.dualCoannihilator = ⊤ := by
        have htmp := congrArg Subrepresentation.toSubmodule hNtop
        change S.toSubmodule.dualCoannihilator = (⊤ : Submodule ℂ V) at htmp
        exact htmp
      have hv : v ∈ S.toSubmodule.dualCoannihilator := by
        rw [hNsub]
        exact Submodule.mem_top
      exact (Submodule.mem_dualCoannihilator v).mp hv f hf

private theorem conjugateCharacter_representationCharacter_eq_dual_pf45
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Section1.conjugateCharacter ρ.character = ρ.dual.character := by
  funext g
  calc
    Section1.conjugateCharacter ρ.character g =
        star (ρ.character g) := by
          simp [Section1.conjugateCharacter]
    _ = ρ.character g⁻¹ := by
          exact (Section1.representation_character_inv_eq_star_character ρ g).symm
    _ = ρ.dual.character g := by
          rw [Representation.char_dual]

private noncomputable def standardizeRepresentation_pf45
    {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := b.equivFun
  refine
    { toFun := fun g => e.conj (ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

private theorem standardizeRepresentation_character_pf45
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (standardizeRepresentation_pf45 ρ).character g = ρ.character g := by
  dsimp [standardizeRepresentation_pf45, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := Fin (Module.finrank ℂ V) → ℂ) (ρ g)
    (Module.Basis.equivFun (Module.finBasis ℂ V))

private theorem standardizeRepresentation_irreducible_pf45
    {G : Type u} {V : Type v} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible (standardizeRepresentation_pf45 ρ) := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := b.equivFun
  let eRep : Theory.Representation.RepEquiv ρ (standardizeRepresentation_pf45 ρ) := by
    refine
      { toLinearEquiv := e
        isIntertwining' := ?_ }
    intro g
    ext v i
    have h := congrArg (fun w => w i)
      (LinearMap.toMatrix_mulVec_repr (v₁ := b) (v₂ := b) (f := ρ g) v)
    simp [standardizeRepresentation_pf45, e, b, b.equivFun_apply]
  exact (Theory.Representation.RepEquiv.irreducible_euqiv eRep).1 hρ

private theorem isIrreducibleCharacterOnGroup_conjugateCharacter_pf45
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsIrreducibleCharacterOnGroup (Section1.conjugateCharacter χ) := by
  rcases hχ with ⟨n, ρ, hρirr, hχchar⟩
  refine ⟨Module.finrank ℂ (Module.Dual ℂ (Fin n → ℂ)),
    standardizeRepresentation_pf45 (G := G)
      (V := Module.Dual ℂ (Fin n → ℂ))
      (ρ := (ρ.dual : Representation ℂ G (Module.Dual ℂ (Fin n → ℂ)))), ?_, ?_⟩
  · exact standardizeRepresentation_irreducible_pf45 (G := G)
      (V := Module.Dual ℂ (Fin n → ℂ))
      (ρ := (ρ.dual : Representation ℂ G (Module.Dual ℂ (Fin n → ℂ))))
      (representation_dual_irreducible_of_pf45 ρ hρirr)
  · rw [hχchar, conjugateCharacter_representationCharacter_eq_dual_pf45]
    ext g
    symm
    exact standardizeRepresentation_character_pf45 (G := G)
      (V := Module.Dual ℂ (Fin n → ℂ))
      (ρ := (ρ.dual : Representation ℂ G (Module.Dual ℂ (Fin n → ℂ)))) g

private theorem degree_eq_nat_of_isIrreducibleCharacterOnGroup_pf45
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ n : ℕ, Section1.degree χ = (n : ℂ) := by
  rcases hχ with ⟨n, ρ, _hρirr, hχchar⟩
  refine ⟨n, ?_⟩
  rw [hχchar]
  simpa using Section1.degree_representation_character ρ

private theorem positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf45
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ n : ℕ, 0 < n ∧ Section1.degree χ = (n : ℂ) := by
  rcases hχ with ⟨n, ρ, hρirr, hχchar⟩
  refine ⟨n, ?_, ?_⟩
  · by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hdeg : Section1.degree χ = 0 := by
      simp [hχchar, Section1.degree_representation_character ρ, hn0]
    exact Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup χ
      ⟨n, ρ, hρirr, hχchar⟩ hdeg
  · rw [hχchar]
    simpa using Section1.degree_representation_character ρ


private theorem supportedOn_diff_of_supportedOn_withOne_and_equal_degree_pf45
    {G : Type u} [Group G]
    (A : Set G)
    {φ ψ : ClassFunction G}
    (hφ : Section1.supportedOn φ (withOne A))
    (hψ : Section1.supportedOn ψ (withOne A))
    (hdeg : Section1.degree φ = Section1.degree ψ) :
    Section1.supportedOn (φ - ψ) A := by
  rw [Section1.supportedOn_iff]
  intro x hxA
  by_cases hx1 : x = 1
  · have hEqVal : φ x = ψ x := by
      simpa [Section1.degree, hx1] using hdeg
    simp [Pi.sub_apply, hEqVal]
  · rw [Section1.supportedOn_iff] at hφ hψ
    have hxNotWithOne : x ∉ withOne A := by
      simp [withOne, hxA, hx1]
    have hφ0 : φ x = 0 := hφ x hxNotWithOne
    have hψ0 : ψ x = 0 := hψ x hxNotWithOne
    simp [Pi.sub_apply, hφ0, hψ0]

private theorem degree_conjugateOnNormal_pf45
    {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (g : G) :
    Section1.degree (Section1.conjugateOnNormal H theta g) = Section1.degree theta := by
  unfold Section1.degree Section1.conjugateOnNormal
  exact congrArg theta (Subtype.ext (by simp))

private theorem conjugateOnNormal_one_pf45
    {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) :
    Section1.conjugateOnNormal H theta 1 = theta := by
  funext h
  simp [Section1.conjugateOnNormal]

private theorem conjugateOnNormal_mul_pf45
    {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (a b : G) :
    Section1.conjugateOnNormal H theta (a * b) =
      Section1.conjugateOnNormal H (Section1.conjugateOnNormal H theta a) b := by
  funext h
  simp [Section1.conjugateOnNormal, mul_assoc]

private theorem conjugateOnNormal_subgroupRestriction_eq_of_isClassFunction_pf45
    {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal]
    (phi : ClassFunction G)
    (hphi : Section1.IsClassFunction phi)
    (g : G) :
    Section1.conjugateOnNormal H (Section1.subgroupRestriction H phi) g =
      Section1.subgroupRestriction H phi := by
  funext h
  change phi (g * (h : G) * g⁻¹) = phi (h : G)
  simpa [Section1.subgroupRestriction, Section1.conjugateOnNormal] using hphi g (h : G)

private theorem subgroupInRepresentationKernel_of_subgroupInKernel_pf45
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G)
    (hA : Section1.subgroupInKernel ρ A) :
    Section1.subgroupInRepresentationKernel ρ A := by
  let : Representation.IsTrivial (ρ.comp A.subtype) :=
    (Section1.subgroupInKernel_iff ρ A).mp hA
  intro a
  change (ρ.comp A.subtype) a = LinearMap.id
  simpa only [Module.End.one_eq_id] using Representation.isTrivial_def (ρ.comp A.subtype) a


private theorem subgroupInKernel'_subgroupRestriction_iff_pf45
    {G : Type*} [Group G]
    (H A : Subgroup G) (hAH : A ≤ H)
    (phi : ClassFunction G) :
    Section1.subgroupInKernel' (Section1.subgroupRestriction H phi) (A.subgroupOf H) ↔
      Section1.subgroupInKernel' phi A := by
  constructor
  · intro h a
    have haH : a.1 ∈ H := hAH a.2
    have hs : (⟨a.1, haH⟩ : H) ∈ A.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      simp [a.2]
    have h' := h ⟨⟨a.1, haH⟩, hs⟩
    simp [Section1.subgroupRestriction, Section1.degree] at h' ⊢
    exact h'
  · intro h a
    simpa [Section1.subgroupRestriction, Section1.degree] using h ⟨a.1, a.2⟩

private theorem subgroupInKernel'_character_of_subgroupInRepresentationKernel_pf45
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G)
    (hV : Section1.subgroupInRepresentationKernel ρ A) :
    Section1.subgroupInKernel' ρ.character A := by
  intro a
  rw [Section1.degree]
  change LinearMap.trace ℂ V (ρ (a : G)) = LinearMap.trace ℂ V (ρ (1 : G))
  rw [hV a]
  simp

private theorem subgroupInRepresentationKernel_of_subgroupInKernel'_character_pf45
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G)
    (hV : Section1.subgroupInKernel' ρ.character A) :
    Section1.subgroupInRepresentationKernel ρ A := by
  intro a
  have hn : orderOf (a : G) ≠ 0 := Nat.ne_of_gt (orderOf_pos (a : G))
  have hpow : (ρ (a : G)) ^ orderOf (a : G) = 1 := by
    rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
  have htrace : LinearMap.trace ℂ V (ρ (a : G)) = (Module.finrank ℂ V : ℂ) := by
    have hchar := hV a
    rw [Section1.degree] at hchar
    change ρ.character (a : G) = ρ.character (1 : G) at hchar
    simpa [Representation.character] using hchar
  exact
    finite_order_eq_one_of_trace_eq_finrank_pf45 (ρ (a : G)) hn hpow htrace

private theorem subgroupInKernel'_character_iff_subgroupInRepresentationKernel_pf45
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G) :
    Section1.subgroupInKernel' ρ.character A ↔
      Section1.subgroupInRepresentationKernel ρ A := by
  constructor
  · exact subgroupInRepresentationKernel_of_subgroupInKernel'_character_pf45 ρ A
  · exact subgroupInKernel'_character_of_subgroupInRepresentationKernel_pf45 ρ A

private theorem representation_character_eq_of_div_mem_kernel_pf45
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G)
    (hker : Section1.subgroupInRepresentationKernel ρ A)
    {x y : G} (hxy : x / y ∈ A) :
    ρ.character x = ρ.character y := by
  let a : A := ⟨x / y, hxy⟩
  have hx : x = (a : G) * y := by
    simp [a, div_eq_mul_inv, mul_assoc]
  have hρ : ρ x = ρ y := by
    rw [hx, map_mul, hker a]
    simp
  simp [Representation.character, hρ]

private theorem representation_character_mul_left_eq_of_mem_kernel_pf45
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G)
    (hker : Section1.subgroupInRepresentationKernel ρ A)
    {a g : G} (ha : a ∈ A) :
    ρ.character (a * g) = ρ.character g := by
  exact representation_character_eq_of_div_mem_kernel_pf45 ρ A hker (by
    simpa [div_eq_mul_inv, mul_assoc] using ha)

private theorem inducedClassFunction_eq_zero_of_not_mem_pf45
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) {g : G} (hg : g ∉ H) :
    Section1.inducedClassFunction H theta g = 0 := by
  classical
  unfold Section1.inducedClassFunction
  have hsum :
      ∑ x : G,
          (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0) =
        0 := by
    refine Finset.sum_eq_zero ?_
    intro x _hx
    have hxfalse : ¬ x * g * x⁻¹ ∈ H := by
      rw [mem_subgroup_iff_conj_mem_pf45 H x g]
      exact hg
    simp [hxfalse]
  rw [hsum]
  simp

private theorem subgroupInKernel'_conjugateOnNormal_pf45
    {G : Type*} [Group G]
    (H A : Subgroup G) [H.Normal] [A.Normal] (hAH : A ≤ H)
    (theta : ClassFunction H)
    (hker : Section1.subgroupInKernel' theta (A.subgroupOf H)) (x : G) :
    Section1.subgroupInKernel' (Section1.conjugateOnNormal H theta x) (A.subgroupOf H) := by
  intro a
  have haA : (((a : A.subgroupOf H) : H) : G) ∈ A := by
    exact Subgroup.mem_subgroupOf.mp a.2
  have hxaA : x * (((a : A.subgroupOf H) : H) : G) * x⁻¹ ∈ A := by
    simpa using (show A.Normal from inferInstance).conj_mem (((a : A.subgroupOf H) : H) : G) haA x
  have hxaH : x * (((a : A.subgroupOf H) : H) : G) * x⁻¹ ∈ H := hAH hxaA
  have hker' :
      theta ⟨x * (((a : A.subgroupOf H) : H) : G) * x⁻¹, hxaH⟩ =
        Section1.degree theta := by
    exact hker ⟨⟨x * (((a : A.subgroupOf H) : H) : G) * x⁻¹, hxaH⟩, by
      exact Subgroup.mem_subgroupOf.mpr hxaA⟩
  rw [degree_conjugateOnNormal_pf45 H theta x]
  simpa [Section1.conjugateOnNormal] using hker'

private theorem conjugateOrbit_exists_fiber_pf45
    {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (i : Section1.conjugateOrbitIndex H theta) :
    ∃ x : G, Section1.conjugateOrbitFiber H theta x = i := by
  refine Quotient.inductionOn i ?_
  intro x
  exact ⟨x, rfl⟩

private theorem conjugateOrbitRepresentation_irreducible_pf45
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (ρ : Representation ℂ H V) (hρ : Representation.IsIrreducible ρ) :
    ∀ i : Section1.conjugateOrbitIndex H ρ.character,
      Representation.IsIrreducible (Section1.conjugateOrbitRepresentation H ρ i) := by
  let : Representation.IsIrreducible ρ := hρ
  intro i
  exact Section1.irreducible_conjugateRepresentation H ρ (Quotient.out i)

private theorem subgroupInKernel'_characterInflationByHom_mk'_pf45
    {L : Type u} [Group L] {K : Subgroup L} [K.Normal]
    (chi : (L ⧸ K) →* ℂˣ) :
    Section1.subgroupInKernel'
      (Section1.characterInflationByHom (QuotientGroup.mk' K) chi) K := by
  intro k
  have hkq : QuotientGroup.mk' K (k : L) = 1 :=
    (QuotientGroup.eq_one_iff (N := K) (x := (k : L))).2 k.2
  have hdeg :
      Section1.degree
        (Section1.characterInflationByHom (QuotientGroup.mk' K) chi) = 1 := by
    simp [Section1.degree, Section1.characterInflationByHom]
  simp [Section1.characterInflationByHom, hkq, hdeg]

private theorem characterInflationByHom_mk'_injective_pf45
    {L : Type u} [Group L] {K : Subgroup L} [K.Normal] :
    Function.Injective
      (fun chi : (L ⧸ K) →* ℂˣ =>
        Section1.characterInflationByHom (QuotientGroup.mk' K) chi) := by
  intro chi eta hEq
  ext q
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective K q
  have hval := congrFun hEq g
  simpa [Section1.characterInflationByHom, hg] using hval

private theorem twistBy_characterInflationByHom_mk'_isIrreducibleCharacterOnGroup_pf45
    {L : Type u} [Group L] [Finite L] {K : Subgroup L} [K.Normal]
    (chi : (L ⧸ K) →* ℂˣ)
    {ψ : Section1.ClassFunction L}
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.characterInflationByHom (QuotientGroup.mk' K) chi * ψ) := by
  let lambda : L →* ℂˣ := chi.comp (QuotientGroup.mk' K)
  rcases hψ with ⟨n, ρ, hρirr, hρchar⟩
  refine ⟨n, Section1.representationTwistByCharacter lambda ρ, ?_, ?_⟩
  · exact Section1.irreducible_twistByCharacter lambda ρ hρirr
  · rw [hρchar]
    calc
      Section1.characterInflationByHom (QuotientGroup.mk' K) chi * ρ.character =
          (fun g : L => (lambda g : ℂ)) * ρ.character := by
            ext g
            rfl
      _ = (Section1.representationTwistByCharacter lambda ρ).character :=
        (Section1.representationTwistByCharacter_character lambda ρ).symm

private theorem characterInflationByHom_mk'_isIrreducibleCharacterOnGroup_pf45
    {L : Type u} [Group L] [Finite L] {K : Subgroup L} [K.Normal]
    (chi : (L ⧸ K) →* ℂˣ) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.characterInflationByHom (QuotientGroup.mk' K) chi) := by
  rcases
      twistBy_characterInflationByHom_mk'_isIrreducibleCharacterOnGroup_pf45
        (L := L) (K := K) chi
        (ψ := Section1.principalCharacter L)
        (Section3.principalCharacter_isIrreducibleCharacterOnGroup (G := L)) with
    ⟨n, ρ, hρirr, hρchar⟩
  refine ⟨n, ρ, hρirr, ?_⟩
  calc
    Section1.characterInflationByHom (QuotientGroup.mk' K) chi =
        Section1.characterInflationByHom (QuotientGroup.mk' K) chi *
          Section1.principalCharacter L := by
            ext g
            simp [Section1.characterInflationByHom, Section1.principalCharacter]
    _ = ρ.character := hρchar

private theorem exists_baseRow_equiv_of_hypothesis_4_2_pf45
    {L : Type u} [Group L] [Finite L]
    {K : Subgroup L} [K.Normal]
    (W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : Section4.theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (hC : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω) :
    ∃ e : ((L ⧸ K) →* ℂˣ) ≃ I,
      ∀ chi : (L ⧸ K) →* ℂˣ,
        Section1.characterInflationByHom (QuotientGroup.mk' K) chi = piChar (e chi) j0 := by
  classical
  let Q := L ⧸ K
  have hQcyc : IsCyclic Q := by
    simpa [Q] using
      isCyclic_quotient_K_of_hypothesis_4_2_pf45
        (K := K) (W1 := W1) (W2 := W2) (W := W) inferInstance h42
  let : CommGroup Q := by
    simpa [Q] using hQcyc.commGroup
  have hExpNeZero : NeZero (Monoid.exponent Q) :=
    Monoid.neZero_exponent_of_finite (G := Q)
  have hRoots : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) := by
    let : NeZero (Monoid.exponent Q) := hExpNeZero
    exact Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
  let inflated : (Q →* ℂˣ) → ClassFunction L :=
    fun chi => Section1.characterInflationByHom (QuotientGroup.mk' K) chi
  have h44 := Section4.proposition_4_4
    K W1 W2 W I J i0 j0 ω σ piChar deltaSign h42 hω hB hC
  let f : (Q →* ℂˣ) → I := fun chi =>
    Classical.choose <|
      ((h44.1 (inflated chi)
          (characterInflationByHom_mk'_isIrreducibleCharacterOnGroup_pf45
            (L := L) (K := K) chi)).1
        (subgroupInKernel'_characterInflationByHom_mk'_pf45
          (L := L) (K := K) chi))
  have hf_spec :
      ∀ chi : Q →* ℂˣ,
        inflated chi = piChar (f chi) j0 := by
    intro chi
    exact Classical.choose_spec <|
      ((h44.1 (inflated chi)
          (characterInflationByHom_mk'_isIrreducibleCharacterOnGroup_pf45
            (L := L) (K := K) chi)).1
        (subgroupInKernel'_characterInflationByHom_mk'_pf45
          (L := L) (K := K) chi))
  have hf_inj : Function.Injective f := by
    intro chi eta hfeq
    exact characterInflationByHom_mk'_injective_pf45 (L := L) (K := K) <|
      calc
        inflated chi = piChar (f chi) j0 := hf_spec chi
        _ = piChar (f eta) j0 := by rw [hfeq]
        _ = inflated eta := (hf_spec eta).symm
  let : Finite (Q →* ℂˣ) := Finite.of_injective f hf_inj
  let : Fintype (Q →* ℂˣ) := Fintype.ofFinite (Q →* ℂˣ)
  have hcard_quot : Nat.card ((L ⧸ K) →* ℂˣ) = Nat.card (L ⧸ K) := by
    let : CommGroup (L ⧸ K) := by
      simpa using hQcyc.commGroup
    let : HasEnoughRootsOfUnity ℂ (Monoid.exponent (L ⧸ K)) := hRoots
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (L ⧸ K) ℂ
  have hcard_chars_nat : Nat.card (Q →* ℂˣ) = Nat.card I := by
    calc
      Nat.card (Q →* ℂˣ) = Nat.card Q := by simpa [Q] using hcard_quot
      _ = Nat.card W1 := by
            simpa using
              natCard_quotient_K_eq_natCard_W1_pf45
                (K := K) (W1 := W1) (W2 := W2) (W := W) inferInstance h42
      _ = Fintype.card I := hω.card_left.symm
      _ = Nat.card I := by simp
  have hcard_chars : Fintype.card (Q →* ℂˣ) = Fintype.card I := by
    rw [← Nat.card_eq_fintype_card (α := Q →* ℂˣ),
      ← Nat.card_eq_fintype_card (α := I)]
    exact hcard_chars_nat
  have hbij : Function.Bijective f := by
    exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcard_chars⟩
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  intro chi
  exact hf_spec chi

private theorem baseRow_twist_eq_row_pf45
    {L : Type u} [Group L] [Finite L]
    {K : Subgroup L} [K.Normal]
    (W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : Section4.theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (hC : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    {e : ((L ⧸ K) →* ℂˣ) ≃ I}
    (he : ∀ chi : (L ⧸ K) →* ℂˣ,
      Section1.characterInflationByHom (QuotientGroup.mk' K) chi = piChar (e chi) j0) :
    ∀ chi : (L ⧸ K) →* ℂˣ, ∀ j : J,
      Section1.characterInflationByHom (QuotientGroup.mk' K) chi * piChar i0 j =
        piChar (e chi) j := by
  classical
  rcases Section4.proposition_4_4_base
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σ) (piChar := piChar) (deltaSign := deltaSign)
      (hω := hω) (hB := hB) with
    ⟨hdelta0, _h00⟩
  rcases hB with ⟨hσmap, hsign, hirr, _hdistinct, _hind, _hSigma⟩
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    (Section4.theorem_4_3_a K W1 W2 W h42).2
  rcases Section3.proposition_3_9_a_uniqueness
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h31 hω with
    ⟨χpf, _horth, _hvirt, _hsigned, _h00, _hInd, huniq⟩
  intro chi j
  let twist : ClassFunction L :=
    Section1.characterInflationByHom (QuotientGroup.mk' K) chi * piChar i0 j
  have htwistIrr : Section1.IsIrreducibleCharacterOnGroup twist := by
    exact
      twistBy_characterInflationByHom_mk'_isIrreducibleCharacterOnGroup_pf45
        (L := L) (K := K) chi (hirr i0 j)
  have htwistV :
      ∀ x : L, ∀ hx : x ∈ Section3.cyclicTISet W1 W2 W,
        (deltaSign j • twist) x =
          ω (e chi) j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
    intro x hx
    have hxWm : x ∈ ((W : Set L) \ (W2 : Set L)) := by
      exact ⟨Section3.cyclicTISet_subset W1 W2 W hx,
        Section3.cyclicTISet_not_mem_right W1 W2 W hx⟩
    have hbaseVal := congrFun (he chi) x
    have hrow0 := hC.1 (e chi) j0 x hxWm
    have hcol0 := hC.1 i0 j x hxWm
    change deltaSign j *
        (Section1.characterInflationByHom (QuotientGroup.mk' K) chi x *
          piChar i0 j x) =
      ω (e chi) j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩
    calc
      deltaSign j *
          (Section1.characterInflationByHom (QuotientGroup.mk' K) chi x *
            piChar i0 j x) =
          deltaSign j * (piChar (e chi) j0 x * piChar i0 j x) := by
            rw [hbaseVal]
      _ = deltaSign j *
            (ω (e chi) j0 ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ *
              piChar i0 j x) := by
            rw [hrow0]
            simp [hdelta0]
      _ = deltaSign j *
            (ω (e chi) j0 ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ *
              (deltaSign j *
                ω i0 j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩)) := by
            rw [hcol0]
      _ = (deltaSign j * deltaSign j) *
            (ω (e chi) j0 ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ *
              ω i0 j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩) := by
            ring
      _ = ω (e chi) j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
            rw [sign_mul_self_eq_one_pf45 (hsign j)]
            simp [hω.product (e chi) j
              ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩]
  have htwistEq :
      deltaSign j • twist = Section3.sigmaOfPF35 ω χpf (ω (e chi) j) := by
    exact huniq (hω.irreducible (e chi) j)
      ⟨deltaSign j, hsign j, twist, htwistIrr, rfl⟩ htwistV
  have hrowV :
      ∀ x : L, ∀ hx : x ∈ Section3.cyclicTISet W1 W2 W,
        (deltaSign j • piChar (e chi) j) x =
          ω (e chi) j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
    intro x hx
    have hxWm : x ∈ ((W : Set L) \ (W2 : Set L)) := by
      exact ⟨Section3.cyclicTISet_subset W1 W2 W hx,
        Section3.cyclicTISet_not_mem_right W1 W2 W hx⟩
    have hval := hC.1 (e chi) j x hxWm
    change deltaSign j * piChar (e chi) j x =
      ω (e chi) j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩
    calc
      deltaSign j * piChar (e chi) j x =
          deltaSign j *
            (deltaSign j *
              ω (e chi) j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩) := by
                rw [hval]
      _ = (deltaSign j * deltaSign j) *
            ω (e chi) j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
            ring
      _ = ω (e chi) j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
            rw [sign_mul_self_eq_one_pf45 (hsign j)]
            simp
  have hrowEq :
      deltaSign j • piChar (e chi) j = Section3.sigmaOfPF35 ω χpf (ω (e chi) j) := by
    exact huniq (hω.irreducible (e chi) j)
      ⟨deltaSign j, hsign j, piChar (e chi) j, hirr (e chi) j, rfl⟩ hrowV
  have hscaled :
      deltaSign j • twist = deltaSign j • piChar (e chi) j := by
    calc
      deltaSign j • twist = Section3.sigmaOfPF35 ω χpf (ω (e chi) j) := htwistEq
      _ = deltaSign j • piChar (e chi) j := hrowEq.symm
  ext x
  have hval := congrFun hscaled x
  have hδ0 : deltaSign j ≠ 0 := sign_ne_zero_pf45 (hsign j)
  have hsub : deltaSign j * (twist x - piChar (e chi) j x) = 0 := by
    rw [mul_sub]
    simpa [Pi.smul_apply] using sub_eq_zero.mpr hval
  have hxEq : twist x = piChar (e chi) j x := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left hδ0)
  simpa [twist] using hxEq

private theorem induced_restriction_eq_regular_inflated_sum_pf45
    {L : Type u} [Group L] [Finite L]
    {K : Subgroup L} [K.Normal]
    (hquot_comm : Std.Commutative (fun x y : L ⧸ K => x * y))
    [DecidableEq (L ⧸ K)]
    [Finite ((L ⧸ K) →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (L ⧸ K))]
    (psi : ClassFunction L)
    (hpsi : Section1.IsClassFunction psi) :
    Section1.inducedCF K (Section1.subgroupRestriction K psi) =
      Section1.familySum
        (fun chi : (L ⧸ K) →* ℂˣ =>
          Section1.characterInflationByHom (QuotientGroup.mk' K) chi * psi) := by
  classical
  let : CommGroup (L ⧸ K) :=
    { (inferInstance : Group (L ⧸ K)) with
      mul_comm := fun x y => hquot_comm.comm x y }
  let : DecidablePred (fun t : L => t ∈ K) := Classical.decPred _
  have hcardK_ne : (Nat.card K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := K)).ne'
  have hindex_card : (Subgroup.index K : ℂ) * Nat.card K = Nat.card L := by
    exact_mod_cast K.index_mul_card
  have hcoef : (Nat.card K : ℂ)⁻¹ * (Nat.card L : ℂ) =
      (Subgroup.index K : ℂ) := by
    have hindex_card' :
        (Nat.card L : ℂ) = (Subgroup.index K : ℂ) * Nat.card K := by
      simpa [mul_comm] using hindex_card.symm
    rw [hindex_card']
    field_simp [hcardK_ne]
  have hker :
      ∀ t : L, QuotientGroup.mk' K t = 1 ↔ t ∈ K := by
    intro t
    change (((t : L) : L ⧸ K) = 1) ↔ t ∈ K
    exact QuotientGroup.eq_one_iff (N := K) t
  ext t
  by_cases htK : t ∈ K
  · have hsum :
        (∑ x : L,
          if hx : x * t * x⁻¹ ∈ K then
            Section1.subgroupRestriction K psi ⟨x * t * x⁻¹, hx⟩
          else 0) =
        (Nat.card L : ℂ) * psi t := by
      calc
        (∑ x : L,
          if hx : x * t * x⁻¹ ∈ K then
            Section1.subgroupRestriction K psi ⟨x * t * x⁻¹, hx⟩
          else 0) = ∑ _x : L, psi t := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            have hxmem : x * t * x⁻¹ ∈ K := (show K.Normal from inferInstance).conj_mem t htK x
            have hclass : psi (x * t * x⁻¹) = psi t := hpsi x t
            simp [Section1.subgroupRestriction, hxmem, hclass]
        _ = (Nat.card L : ℂ) * psi t := by
            simp [Finset.card_univ]
    calc
      Section1.inducedCF K (Section1.subgroupRestriction K psi) t =
          (Nat.card K : ℂ)⁻¹ *
            ∑ x : L,
              if hx : x * t * x⁻¹ ∈ K then
                Section1.subgroupRestriction K psi ⟨x * t * x⁻¹, hx⟩
              else 0 := by
                unfold Section1.inducedCF Section1.inducedClassFunction
                rfl
      _ = ((Nat.card K : ℂ)⁻¹ * (Nat.card L : ℂ)) * psi t := by
            rw [hsum]
            ring
      _ = (Subgroup.index K : ℂ) * psi t := by
            rw [hcoef]
      _ =
          (∑ chi : (L ⧸ K) →* ℂˣ,
            Section1.characterInflationByHom (QuotientGroup.mk' K) chi t) * psi t := by
              have hregular :
                  ∑ chi : (L ⧸ K) →* ℂˣ,
                    Section1.characterInflationByHom (QuotientGroup.mk' K) chi t =
                      (Subgroup.index K : ℂ) := by
                exact Section1.characterInflationByHom_regular_sum_mem
                  (Q := L ⧸ K) (S := K) (pi := QuotientGroup.mk' K) hker rfl t htK
              rw [← hregular]
      _ = Section1.familySum
            (fun chi : (L ⧸ K) →* ℂˣ =>
              Section1.characterInflationByHom (QuotientGroup.mk' K) chi * psi) t := by
            simp [Section1.familySum, Finset.sum_mul]
  · have hsum :
        (∑ x : L,
          if hx : x * t * x⁻¹ ∈ K then
            Section1.subgroupRestriction K psi ⟨x * t * x⁻¹, hx⟩
          else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x _hx
      have hxnot : ¬ x * t * x⁻¹ ∈ K := by
        intro hxmem
        apply htK
        have hback : x⁻¹ * (x * t * x⁻¹) * x ∈ K := by
          simpa [mul_assoc] using
            (show K.Normal from inferInstance).conj_mem (x * t * x⁻¹) hxmem x⁻¹
        simpa [mul_assoc] using hback
      simp [hxnot]
    calc
      Section1.inducedCF K (Section1.subgroupRestriction K psi) t =
          (Nat.card K : ℂ)⁻¹ *
            ∑ x : L,
              if hx : x * t * x⁻¹ ∈ K then
                Section1.subgroupRestriction K psi ⟨x * t * x⁻¹, hx⟩
              else 0 := by
                unfold Section1.inducedCF Section1.inducedClassFunction
                rfl
      _ = 0 := by
            rw [hsum]
            simp
      _ =
          (∑ chi : (L ⧸ K) →* ℂˣ,
            Section1.characterInflationByHom (QuotientGroup.mk' K) chi t) * psi t := by
              have hregular :
                  ∑ chi : (L ⧸ K) →* ℂˣ,
                    Section1.characterInflationByHom (QuotientGroup.mk' K) chi t = 0 := by
                exact Section1.characterInflationByHom_regular_sum_not_mem
                  (Q := L ⧸ K) (S := K) (pi := QuotientGroup.mk' K) hker rfl t htK
              rw [hregular]
              simp
      _ = Section1.familySum
            (fun chi : (L ⧸ K) →* ℂˣ =>
              Section1.characterInflationByHom (QuotientGroup.mk' K) chi * psi) t := by
            simp [Section1.familySum, Finset.sum_mul]

private theorem isClassFunction_of_irreducibleCharacterOnGroup_pf45
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨n, ρ, _hρirr, rfl⟩
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x

private theorem scalarProduct_irreducible_self_pf45
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨n, ρ, hρirr, rfl⟩
  exact Section1.scalarProduct_representation_char_self ρ hρirr

private theorem scalarProduct_irreducible_ne_pf45
    {G : Type*} [Group G] [Finite G]
    {φ ψ : Section1.ClassFunction G}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hne : φ ≠ ψ) :
    Section1.scalarProduct G φ ψ = 0 := by
  rcases hφ with ⟨nφ, ρφ, hρφ, hφchar⟩
  rcases hψ with ⟨nψ, ρψ, hρψ, hψchar⟩
  exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
    φ ψ ρφ ρψ hφchar hψchar hρφ hρψ hne

private theorem subgroupRestriction_fixed_column_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : Section4.theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω) :
    ∀ i j, Section1.subgroupRestriction K (piChar i j) =
      Section1.subgroupRestriction K (piChar i0 j) := by
  rcases hB with ⟨_hσmap, hsign, _hirr, _hdistinct, hind, _hSigma⟩
  intro i j
  ext k
  let A : Set L := (W : Set L) \ (W2 : Set L)
  have hA : Section2.IsTISubsetWithNormalizer A W :=
    (Section4.theorem_4_3_a K W1 W2 W h42).1
  have hHyp2 : Section2.Hypothesis2 A W (fun _ : L => ⊥) :=
    (Section2.proposition_2_3 A W hA.1).1 hA
  have hAL : ∀ a ∈ A, a ∈ W := hHyp2.subset_L
  have hCF : Section2.CFOn W A (ω i j - ω i0 j) :=
    omegaRowDifference_CFOn_wMinusW2_pf45 hω i j
  have hIndEq :=
    Section3.inducedCF_eq_dadeTransform_trivial A W hHyp2 hAL (ω i j - ω i0 j) hCF
  have hDadeZero :=
    (Section2.definition_2_5 A W (fun _ : L => ⊥) hHyp2 hAL (ω i j - ω i0 j) hCF).2
  have hknot :
      (k : L) ∉ Section2.dadeSupport A (fun _ : L => ⊥) := by
    rw [dadeSupport_trivial_eq_conjugateSet_pf45]
    exact not_mem_conjugateSet_wMinusW2_of_mem_K_pf45 h42 k
  have hind_zero : Section1.inducedCF W (ω i j - ω i0 j) k = 0 := by
    rw [hIndEq]
    exact hDadeZero k hknot
  have hFormula := congrFun (hind i j) (k : L)
  rw [hind_zero] at hFormula
  have hFormula' : deltaSign j * (piChar i j k - piChar i0 j k) = 0 := by
    simpa [Pi.smul_apply, Pi.sub_apply] using hFormula.symm
  have hδ0 : deltaSign j ≠ 0 := sign_ne_zero_pf45 (hsign j)
  have hEqVal : piChar i j k = piChar i0 j k := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hFormula').resolve_left hδ0)
  simpa [Section1.subgroupRestriction] using hEqVal

private theorem irreducible_fixed_column_of_induced_eq_piColumn_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : Section4.theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (hInd :
      ∀ j, Section1.inducedCF K (Section1.subgroupRestriction K (piChar i0 j)) =
        piColumn piChar j) :
    ∀ j, Section1.IsIrreducibleCharacterOnGroup
      (Section1.subgroupRestriction K (piChar i0 j)) := by
  classical
  rcases hB with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigma⟩
  intro j
  rcases hirr i0 j with ⟨n, ρ, hρirr, hρchar⟩
  let ρK : Representation ℂ K (Fin n → ℂ) := ρ.comp K.subtype
  have hresChar :
      Section1.subgroupRestriction K (piChar i0 j) = ρK.character := by
    ext k
    simp [ρK, Section1.subgroupRestriction, hρchar, Representation.character]
  have hchiClass : Section1.IsClassFunction (piChar i0 j) :=
    isClassFunction_of_irreducibleCharacterOnGroup_pf45 (hirr i0 j)
  have horthCol :
      ∀ p q : I,
        Section1.scalarProduct L (piChar p j) (piChar q j) =
          if p = q then 1 else 0 := by
    intro p q
    by_cases hpq : p = q
    · subst hpq
      simpa using scalarProduct_irreducible_self_pf45 (hirr p j)
    · simpa [hpq] using
        scalarProduct_irreducible_ne_pf45 (hirr p j) (hirr q j)
          (hdistinct (p, j) (q, j) (by
            intro hEq
            apply hpq
            exact congrArg Prod.fst hEq))
  have hcolInner :
      Section1.scalarProduct L (piColumn piChar j) (piChar i0 j) = 1 := by
    unfold piColumn
    have hsum : ((∑ i : I, piChar i j : ClassFunction L)) = fun g => ∑ i : I, piChar i j g := by
      ext g
      simp
    rw [hsum, Section1.scalarProduct_fintype_sum_left]
    calc
      ∑ i : I, Section1.scalarProduct L (piChar i j) (piChar i0 j) =
          ∑ i : I, if i = i0 then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            exact horthCol i i0
      _ = 1 := by
            simp
  have hself :
      Section1.scalarProduct K
          (Section1.subgroupRestriction K (piChar i0 j))
          (Section1.subgroupRestriction K (piChar i0 j)) = 1 := by
    calc
      Section1.scalarProduct K
          (Section1.subgroupRestriction K (piChar i0 j))
          (Section1.subgroupRestriction K (piChar i0 j)) =
          Section1.scalarProduct L
            (Section1.inducedCF K (Section1.subgroupRestriction K (piChar i0 j)))
            (piChar i0 j) := by
              symm
              exact Section1.scalarProduct_inducedCF_left K
                (Section1.subgroupRestriction K (piChar i0 j)) (piChar i0 j) hchiClass
      _ = Section1.scalarProduct L (piColumn piChar j) (piChar i0 j) := by
            rw [hInd j]
      _ = 1 := hcolInner
  have hρKirr : Representation.IsIrreducible ρK := by
    apply (Theory.Character.irreducible_iff_character_norm_one (ρ := ρK)).2
    have hρKclass : Section1.IsClassFunction ρK.character := by
      intro x g
      simpa [mul_assoc] using Representation.char_conj (ρ := ρK) g x
    have htoeq :
        Section1.toConjClassFunction ρK.character hρKclass =
          Theory.Character.characterClassFunction ρK := by
      apply Section1.toConjClassFunction_eq_of_apply
      intro g
      rfl
    rw [← htoeq, Section1.classFunctionInner_toConjClassFunction]
    rw [hresChar] at hself
    exact hself
  exact ⟨n, ρK, hρKirr, hresChar⟩

public theorem hypothesis_3_1_of_hypothesis_4_6_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    (h46 : hypothesis_4_6_statement K W1 W2 W H A) :
    Section3.hypothesis_3_1_statement W1 W2 W :=
  (Section4.theorem_4_3_a K W1 W2 W h46.1).2

private theorem not_two_eq_int_mul_of_three_le_pf45
    {m : Int} {n : Nat}
    (hn : 3 ≤ n) :
    ¬ (2 : Int) = m * (n : Int) := by
  intro hEq
  have hdivInt : (n : Int) ∣ (2 : Int) := by
    refine ⟨m, ?_⟩
    simpa [mul_comm] using hEq
  have hdiv : n ∣ 2 := Int.natCast_dvd_natCast.mp hdivInt
  have hle : n ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  linarith

public theorem deltaSign_eq_of_equal_degree_pf45
    {L : Type u} [Group L] [Finite L]
    (W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hsign : ∀ j, Section1.IsSign (deltaSign j))
    (h43d : Section4.theorem_4_3_d_statement W1 I J piChar deltaSign)
    {i : I} {j k : J}
    (hdeg : Section1.degree (piChar i j) = Section1.degree (piChar i k)) :
    deltaSign j = deltaSign k := by
  have hcard : 3 ≤ Nat.card W1 :=
    Section3.natCard_left_ge_three_of_hypothesis_3_1
      (W1 := W1) (W2 := W2) (W := W) h31
  have hcard' : 3 ≤ Fintype.card W1 := by
    rw [Nat.card_eq_fintype_card] at hcard
    exact hcard
  rcases h43d i j with ⟨a, ha⟩
  rcases h43d i k with ⟨b, hb⟩
  rcases hsign j with hj | hj <;> rcases hsign k with hk | hk
  · simp [hj, hk]
  · exfalso
    have hEq :
        (1 : ℂ) + ((a : ℂ) * (Nat.card W1 : ℂ)) =
          (-1 : ℂ) + ((b : ℂ) * (Nat.card W1 : ℂ)) := by
      calc
        (1 : ℂ) + ((a : ℂ) * (Nat.card W1 : ℂ))
            = Section1.degree (piChar i j) := by simpa [hj] using ha.symm
        _ = Section1.degree (piChar i k) := hdeg
        _ = (-1 : ℂ) + ((b : ℂ) * (Nat.card W1 : ℂ)) := by simpa [hk] using hb
    have hEqRe := congrArg Complex.re hEq
    simp at hEqRe
    have hEqInt' :
        (1 : Int) + a * (Fintype.card W1 : Int) = -1 + b * (Fintype.card W1 : Int) := by
      exact_mod_cast hEqRe
    have hEqInt : (((b : Int) - a) * (Fintype.card W1 : Int) : Int) = 2 := by
      nlinarith
    exact not_two_eq_int_mul_of_three_le_pf45 hcard' hEqInt.symm
  · exfalso
    have hEq :
        (-1 : ℂ) + ((a : ℂ) * (Nat.card W1 : ℂ)) =
          (1 : ℂ) + ((b : ℂ) * (Nat.card W1 : ℂ)) := by
      calc
        (-1 : ℂ) + ((a : ℂ) * (Nat.card W1 : ℂ))
            = Section1.degree (piChar i j) := by simpa [hj] using ha.symm
        _ = Section1.degree (piChar i k) := hdeg
        _ = (1 : ℂ) + ((b : ℂ) * (Nat.card W1 : ℂ)) := by simpa [hk] using hb
    have hEqRe := congrArg Complex.re hEq
    simp at hEqRe
    have hEqInt' :
        (-1 : Int) + a * (Fintype.card W1 : Int) = 1 + b * (Fintype.card W1 : Int) := by
      exact_mod_cast hEqRe
    have hEqInt : (((a : Int) - b) * (Fintype.card W1 : Int) : Int) = 2 := by
      nlinarith
    exact not_two_eq_int_mul_of_three_le_pf45 hcard' hEqInt.symm
  · simp [hj, hk]

private theorem irreducible_eq_principal_of_both_kernels_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    {ψ : ClassFunction W}
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hker1 : Section1.subgroupInKernel' ψ (W1.subgroupOf W))
    (hker2 : Section1.subgroupInKernel' ψ (W2.subgroupOf W))
    (hdeg : Section1.degree ψ = 1) :
    ψ = Section1.principalCharacter W := by
  rcases h31 with ⟨_hW1, _hW2, hDirect, _hcycW, _hodd, _hcard1, _hcard2, _hTI⟩
  rcases hψ with ⟨n, ρ, hρirr, hchar⟩
  have hkerRep1 :
      Section1.subgroupInRepresentationKernel ρ (W1.subgroupOf W) :=
      (subgroupInKernel'_character_iff_subgroupInRepresentationKernel_pf45
        ρ (W1.subgroupOf W)).mp (subgroupInKernel'_of_eq_pf45 hchar.symm hker1)
  have hkerRep2 :
      Section1.subgroupInRepresentationKernel ρ (W2.subgroupOf W) :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel_pf45
      ρ (W2.subgroupOf W)).mp (subgroupInKernel'_of_eq_pf45 hchar.symm hker2)
  ext x
  rcases hDirect.mul_surjective (x : L) x.2 with ⟨a, ha, b, hb, hmul⟩
  let aW : W := ⟨a, hDirect.left_le ha⟩
  let bW : W := ⟨b, hDirect.right_le hb⟩
  have hxmul : x = aW * bW := by
    apply Subtype.ext
    simpa [aW, bW] using hmul
  have hρa : ρ aW = 1 := hkerRep1 ⟨aW, ha⟩
  have hρb : ρ bW = 1 := hkerRep2 ⟨bW, hb⟩
  have hρx : ρ x = 1 := by
    rw [hxmul, map_mul, hρa, hρb]
    simp
  have hpsi_one : ψ 1 = 1 := by
    simpa [Section1.degree] using hdeg
  have hpsi_x : ψ x = 1 := by
    calc
      ψ x = ρ.character x := by rw [hchar]
      _ = ρ.character 1 := by simp [Representation.character, hρx]
      _ = ψ 1 := by rw [hchar]
      _ = 1 := hpsi_one
  simpa [Section1.principalCharacter] using hpsi_x

private theorem omega_column_eq_base_of_right_kernel_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → ClassFunction W}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I} {j : J}
    (hker : Section1.subgroupInKernel' (ω i j) (W2.subgroupOf W)) :
    j = j0 := by
  have hkerBase : Section1.subgroupInKernel' (ω i0 j) (W2.subgroupOf W) := by
    intro x
    have hij : ω i j x = 1 := by
      simpa [hω.degree_one i j] using hker x
    have hij0 : ω i j0 x = 1 := by
      simpa [hω.degree_one i j0] using hω.left_kernel i x
    have hprod := hω.product i j x
    rw [hij, hij0] at hprod
    have hbase : ω i0 j x = 1 := by
      simpa using hprod.symm
    simpa [hω.degree_one i0 j] using hbase
  have hprincipal : ω i0 j = Section1.principalCharacter W :=
    irreducible_eq_principal_of_both_kernels_pf45
      (W1 := W1) (W2 := W2) (W := W) h31
      (hω.irreducible i0 j) (hω.right_kernel j) hkerBase (hω.degree_one i0 j)
  have heq : ω i0 j = ω i0 j0 := by
    rw [hprincipal, hω.principal]
  exact (hω.pairwise_eq (i := i0) (i' := i0) (j := j) (j' := j0) heq).2

private theorem omega_row_eq_base_of_left_kernel_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → ClassFunction W}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I} {j : J}
    (hker : Section1.subgroupInKernel' (ω i j) (W1.subgroupOf W)) :
    i = i0 := by
  simpa using
    omega_column_eq_base_of_right_kernel_pf45
      (W1 := W2) (W2 := W1) (W := W)
      (I := J) (J := I) (i0 := j0) (j0 := i0)
      (ω := fun j i => ω i j)
      (Section3.hypothesis_3_1_statement_swap h31)
      (Section3.notation_3_3_statement_swap hω) hker

private theorem conjugate_omega_baseRow_eq_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → ClassFunction W}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (j : J) :
    ∃ j', Section1.conjugateCharacter (ω i0 j) = ω i0 j' := by
  have hbarIrr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.conjugateCharacter (ω i0 j)) :=
    isIrreducibleCharacterOnGroup_conjugateCharacter_pf45 (hω.irreducible i0 j)
  rcases hω.all_irreducibles (Section1.conjugateCharacter (ω i0 j)) hbarIrr with
    ⟨i, j', hEq⟩
  have hbarKer :
      Section1.subgroupInKernel' (Section1.conjugateCharacter (ω i0 j))
        (W1.subgroupOf W) :=
    (subgroupInKernel'_conjugateCharacter_iff_pf45).2 (hω.right_kernel j)
  have hi : i = i0 :=
    omega_row_eq_base_of_left_kernel_pf45
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      h31 hω (subgroupInKernel'_of_eq_pf45 hEq.symm hbarKer)
  refine ⟨j', ?_⟩
  simpa [hi] using hEq

private theorem conjugate_omega_baseRow_ne_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → ClassFunction W}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {j : J} (hj0 : j ≠ j0) :
    ∃ j', Section1.conjugateCharacter (ω i0 j) = ω i0 j' ∧ j' ≠ j := by
  rcases conjugate_omega_baseRow_eq_pf45
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) h31 hω j with
    ⟨j', hbar⟩
  have hbar_ne : Section1.conjugateCharacter (ω i0 j) ≠ ω i0 j := by
    intro hfix
    have hne_principal : ω i0 j ≠ Section1.principalCharacter W := by
      intro hEq
      exact hj0 ((hω.pairwise_eq (i := i0) (i' := i0) (j := j) (j' := j0)
        (by simpa [hω.principal] using hEq)).2)
    rcases h31 with ⟨_hW1, _hW2, _hDirect, _hcycW, hoddW, _hcard1, _hcard2, _hTI⟩
    rcases hω.irreducible i0 j with ⟨n, ρ, hρirr, hρchar⟩
    have hneChar : ρ.character ≠ Section1.principalCharacter W := by
      simpa [hρchar] using hne_principal
    exact Section1.proposition_1_1 hoddW ρ hρirr hneChar
      (by simpa [hρchar] using hfix.symm)
  refine ⟨j', hbar, ?_⟩
  intro hj'eq
  apply hbar_ne
  simpa [hj'eq] using hbar

private theorem not_subgroupInKernel'_xChar_of_ne_base_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    {j : J}
    (hj0 : j ≠ j0) :
    ¬ Section1.subgroupInKernel' (xChar j) (H.subgroupOf K) := by
  intro hker
  rcases h46 with ⟨h42, hHnorm, hW2H, hHK, _hcentA, _hAinK⟩
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    (Section4.theorem_4_3_a K W1 W2 W h42).2
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, hcard1, _hcyc2, _hcard2,
      hcent, hW1, hW2, hDirect, _hodd⟩
  rcases h45a with ⟨hres, _hirrX, _hindX⟩
  rcases h43b with ⟨_hσmap, hsign, hirrPi, _hdistinct, _hind, _hSigma⟩
  obtain ⟨x, hxW1, hx1⟩ := exists_ne_one_mem_of_natCard_ne_one_pf45 W1 hcard1
  have hxWnot : x ∉ W2 := by
    intro hxW2
    have hbot : x ∈ (⊥ : Subgroup L) := by
      have hinf : x ∈ W1 ⊓ W2 := Subgroup.mem_inf.mpr ⟨hxW1, hxW2⟩
      simpa [hDirect.inf_eq_bot] using hinf
    exact hx1 (by simpa using hbot)
  have hxWm : x ∈ ((W : Set L) \ (W2 : Set L)) := ⟨hW1 hxW1, hxWnot⟩
  have hresKer :
      Section1.subgroupInKernel' (Section1.subgroupRestriction K (piChar i0 j))
        (H.subgroupOf K) := by
    rw [hres i0 j]
    exact hker
  have hkerPi : Section1.subgroupInKernel' (piChar i0 j) H :=
    (subgroupInKernel'_subgroupRestriction_iff_pf45 K H hHK (piChar i0 j)).mp hresKer
  rcases hirrPi i0 j with ⟨nPi, rhoPi, hRhoPiIrr, hRhoPiChar⟩
  have hkerRepPi : Section1.subgroupInRepresentationKernel rhoPi H :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel_pf45
      rhoPi H).mp (subgroupInKernel'_of_eq_pf45 hRhoPiChar.symm hkerPi)
  rcases hω.irreducible i0 j with ⟨nOmega, rhoOmega, hRhoOmegaIrr, hRhoOmegaChar⟩
  have hkerRepOmega :
      Section1.subgroupInRepresentationKernel rhoOmega (W1.subgroupOf W) :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel_pf45
      rhoOmega (W1.subgroupOf W)).mp
        (subgroupInKernel'_of_eq_pf45 hRhoOmegaChar.symm (hω.right_kernel j))
  have hkerW2 : Section1.subgroupInKernel' (ω i0 j) (W2.subgroupOf W) := by
    let xW : W := ⟨x, hW1 hxW1⟩
    let xW1 : W1.subgroupOf W := ⟨xW, hxW1⟩
    intro y
    have hyW2 : ((y : W) : L) ∈ W2 := Subgroup.mem_subgroupOf.mp y.2
    have hyH : ((y : W) : L) ∈ H := hW2H hyW2
    have hyCent : ((y : W) : L) ∈ Section2.centralizerIn K x := by
      have hcentx : Section2.centralizerIn K x = W2 := hcent ⟨x, hxW1⟩ (by
        intro hxsub
        exact hx1 (Subtype.ext_iff.mp hxsub))
      simpa [hcentx] using hyW2
    have hyComm : x * ((y : W) : L) = ((y : W) : L) * x := by
      have hyElemCent : ((y : W) : L) ∈ Section2.elementCentralizer x :=
        (Subgroup.mem_inf.mp hyCent).2
      exact (Subgroup.mem_centralizer_iff.mp hyElemCent) x (by simp)
    have hxyWm : x * ((y : W) : L) ∈ ((W : Set L) \ (W2 : Set L)) := by
      refine ⟨W.mul_mem (hW1 hxW1) y.1.2, ?_⟩
      intro hxyW2
      have hxW2' : x ∈ W2 := by
        have hxEq : x = (x * ((y : W) : L)) * ((y : W) : L)⁻¹ := by
          simp [mul_assoc]
        exact hxEq ▸ W2.mul_mem hxyW2 (W2.inv_mem hyW2)
      exact hxWnot hxW2'
    have hPiEq :
        piChar i0 j (x * ((y : W) : L)) = piChar i0 j x := by
      calc
        piChar i0 j (x * ((y : W) : L)) = piChar i0 j (((y : W) : L) * x) := by
          rw [hyComm]
        _ = rhoPi.character (((y : W) : L) * x) := by rw [hRhoPiChar]
        _ = rhoPi.character x :=
            representation_character_mul_left_eq_of_mem_kernel_pf45
              rhoPi H hkerRepPi hyH
        _ = piChar i0 j x := by rw [hRhoPiChar]
    have hDeltaEq :
        deltaSign j * ω i0 j ⟨x * ((y : W) : L), hxyWm.1⟩ =
          deltaSign j * ω i0 j ⟨x, hxWm.1⟩ := by
      simpa [h43c.1 i0 j (x * ((y : W) : L)) hxyWm, h43c.1 i0 j x hxWm] using hPiEq
    have hOmegaEq :
        ω i0 j ⟨x * ((y : W) : L), hxyWm.1⟩ = ω i0 j ⟨x, hxWm.1⟩ := by
      exact mul_left_cancel₀ (sign_ne_zero_pf45 (hsign j)) hDeltaEq
    have hOmegaX : ω i0 j ⟨x, hW1 hxW1⟩ = 1 := by
      have hkerX := hω.right_kernel j ⟨⟨x, hW1 hxW1⟩, hxW1⟩
      simpa [hω.degree_one i0 j] using hkerX
    have hOmegaXY : ω i0 j ⟨x * ((y : W) : L), hxyWm.1⟩ = 1 := by
      simpa using hOmegaEq.trans hOmegaX
    have hOmegaY :
        ω i0 j ((xW1 : W) * (y : W)) = ω i0 j (y : W) := by
      calc
        ω i0 j ((xW1 : W) * (y : W))
            = rhoOmega.character ((xW1 : W) * (y : W)) := by
                rw [hRhoOmegaChar]
        _ = rhoOmega.character (y : W) :=
              representation_character_mul_left_eq_of_mem_kernel_pf45
                rhoOmega (W1.subgroupOf W) hkerRepOmega xW1.2
        _ = ω i0 j (y : W) := by rw [hRhoOmegaChar]
    have hOmegaY' : ω i0 j (y : W) = 1 := by
      have hxySubtype :
          ((xW1 : W) * (y : W)) =
            ⟨x * ((y : W) : L), hxyWm.1⟩ := by
        apply Subtype.ext
        rfl
      rw [hxySubtype] at hOmegaY
      exact hOmegaY.symm.trans hOmegaXY
    simpa [hω.degree_one i0 j] using hOmegaY'
  exact hj0 (omega_column_eq_base_of_right_kernel_pf45
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0) h31 hω hkerW2)

private theorem centralizer_intersection_eq_bot_of_not_mem_A_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    {x : K}
    (hxA : (x : L) ∉ A)
    (hx1 : x ≠ 1) :
    H.subgroupOf K ⊓ Subgroup.centralizer ({x} : Set K) = ⊥ := by
  rcases h46 with ⟨_h42, _hHnorm, _hW2H, _hHK, hcentA, _hAinK⟩
  apply le_antisymm
  · intro a ha
    rcases Subgroup.mem_inf.mp ha with ⟨haH, haCent⟩
    by_cases ha1 : (a : K) = 1
    · simpa [Subgroup.mem_bot] using ha1
    · let hne : {h : H // (h : L) ≠ 1} :=
        ⟨⟨(a : K), Subgroup.mem_subgroupOf.mp haH⟩, by
          intro haL
          exact ha1 (Subtype.ext haL)⟩
      have hxCent : (x : L) ∈ Section2.centralizerIn K ((hne : H) : L) := by
        refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro z hz
        have hzEq : z = ((hne : H) : L) := by
          simpa using hz
        subst hzEq
        have hcommK : (a : K) * x = x * (a : K) := by
          simpa using ((Subgroup.mem_centralizer_iff.mp haCent) x (by simp)).symm
        simpa [hne] using congrArg (fun z : K => (z : L)) hcommK
      have hxUnion :
          (x : L) ∈
            ⋃ h : {h : H // (h : L) ≠ 1},
              (((Section2.centralizerIn K ((h : H) : L)) : Set L) \ {1}) := by
        rw [Set.mem_iUnion]
        refine ⟨hne, ?_⟩
        simp [hxCent, hx1]
      have hxA' : (x : L) ∈ A := hcentA hxUnion
      exact (hxA hxA').elim
  · exact bot_le

private theorem not_subgroupInKernel'_conjugateOrbitConj_of_not_pf45
    {L : Type u} [Group L] [Finite L]
    (K H : Subgroup L) [K.Normal] [H.Normal]
    (hHK : H ≤ K)
    {X : ClassFunction K}
    (hXker : ¬ Section1.subgroupInKernel' X (H.subgroupOf K))
    (o : Section1.conjugateOrbitIndex K X) :
    ¬ Section1.subgroupInKernel' (Section1.conjugateOrbitConj K X o) (H.subgroupOf K) := by
  intro hkerConj
  rcases conjugateOrbit_exists_fiber_pf45 K X o with ⟨g, hg⟩
  have hkerConj' :
      Section1.subgroupInKernel' (Section1.conjugateOnNormal K X g) (H.subgroupOf K) := by
    rw [← hg] at hkerConj
    change Section1.subgroupInKernel'
      (Section1.conjugateOnNormal K X g) (H.subgroupOf K) at hkerConj
    exact hkerConj
  have hkerBase :
      Section1.subgroupInKernel'
        (Section1.conjugateOnNormal K (Section1.conjugateOnNormal K X g) g⁻¹)
        (H.subgroupOf K) :=
    subgroupInKernel'_conjugateOnNormal_pf45 K H hHK
      (Section1.conjugateOnNormal K X g) hkerConj' g⁻¹
  have hkerX : Section1.subgroupInKernel' X (H.subgroupOf K) := by
    have hEq :
        Section1.conjugateOnNormal K (Section1.conjugateOnNormal K X g) g⁻¹ = X := by
      calc
        Section1.conjugateOnNormal K (Section1.conjugateOnNormal K X g) g⁻¹
            = Section1.conjugateOnNormal K X (g * g⁻¹) := by
                symm
                exact conjugateOnNormal_mul_pf45 K X g g⁻¹
        _ = Section1.conjugateOnNormal K X 1 := by simp
        _ = X := conjugateOnNormal_one_pf45 K X
    simpa [hEq] using hkerBase
  exact hXker hkerX

private theorem supportedOn_irreducible_of_not_subgroupInKernel_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    {X : ClassFunction K}
    (hX : Section1.IsIrreducibleCharacterOnGroup X)
    (hXker : ¬ Section1.subgroupInKernel' X (H.subgroupOf K)) :
    Section1.supportedOn X (withOne (subgroupPullbackSet K A)) := by
  have h46' := h46
  rcases h46 with ⟨h42, hHnorm, _hW2H, _hHK, _hcentA, _hAinK⟩
  have hKnorm : K.Normal := normal_K_of_hypothesis_4_2_pf45 h42
  let : K.Normal := hKnorm
  let : (H.subgroupOf K).Normal := Section1.subgroupOf_normal_of_normal H K
  rcases hX with ⟨n, rho, hRhoIrr, rfl⟩
  have hkerRep :
      ¬ Section1.subgroupInRepresentationKernel rho (H.subgroupOf K) := by
    intro hrep
    apply hXker
    exact
      (subgroupInKernel'_character_iff_subgroupInRepresentationKernel_pf45
        rho (H.subgroupOf K)).mpr hrep
  have hkerPrime :
      ¬ Section1.subgroupInKernel rho (H.subgroupOf K) := by
    intro hprime
    exact hkerRep (subgroupInRepresentationKernel_of_subgroupInKernel_pf45
      rho (H.subgroupOf K) hprime)
  rw [Section1.supportedOn_iff]
  intro x hx
  have hxA : (x : L) ∉ A := by
    intro hxA
    exact hx (Or.inl hxA)
  have hx1 : x ≠ 1 := by
    intro hx1
    exact hx (Or.inr hx1)
  let : Representation.IsIrreducible rho := hRhoIrr
  exact Section1.proposition_1_2 rho hkerPrime
    (centralizer_intersection_eq_bot_of_not_mem_A_pf45 K W1 W2 W H A h46' hxA hx1)

private theorem supportedOn_induced_irreducible_of_not_subgroupInKernel_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    {X : ClassFunction K}
    (hX : Section1.IsIrreducibleCharacterOnGroup X)
    (hXker : ¬ Section1.subgroupInKernel' X (H.subgroupOf K)) :
    Section1.supportedOn (Section1.inducedCF K X) (withOne A) := by
  have h46' := h46
  rcases h46 with ⟨h42, hHnorm, _hW2H, hHK, _hcentA, _hAinK⟩
  have hKnorm : K.Normal := normal_K_of_hypothesis_4_2_pf45 h42
  let : K.Normal := hKnorm
  let : H.Normal := hHnorm
  let : (H.subgroupOf K).Normal := Section1.subgroupOf_normal_of_normal H K
  rcases hX with ⟨n, rho, hRhoIrr, rfl⟩
  have hSuppX :
      Section1.supportedOn rho.character (withOne (subgroupPullbackSet K A)) :=
    supportedOn_irreducible_of_not_subgroupInKernel_pf45
      K W1 W2 W H A h46' ⟨n, rho, hRhoIrr, rfl⟩ hXker
  rw [Section1.supportedOn_iff]
  intro g hg
  by_cases hgK : g ∈ K
  · let gK : K := ⟨g, hgK⟩
    have hgK' : gK ∉ withOne (subgroupPullbackSet K A) := by
      intro hgK'
      rcases hgK' with hgKA | hgK1
      · exact hg (Or.inl hgKA)
      · exact hg (Or.inr (Subtype.ext_iff.mp hgK1))
    have hres :
        Section1.subgroupRestriction K (Section1.inducedCF K rho.character) =
          fun h =>
            (K.relIndex (Section1.inertiaSubgroup K rho.character) : ℂ) *
              ∑ o : Section1.conjugateOrbitIndex K rho.character,
                Section1.conjugateOrbitConj K rho.character o h := by
      exact Section1.proposition_1_5_a_orbit_relIndex_canonical K rho
    have horbitZero :
        ∀ o : Section1.conjugateOrbitIndex K rho.character,
          Section1.conjugateOrbitConj K rho.character o gK = 0 := by
      intro o
      have hOrbitIrr :
          Section1.IsIrreducibleCharacterOnGroup
            (Section1.conjugateOrbitConj K rho.character o) := by
        refine ⟨n, Section1.conjugateOrbitRepresentation K rho o, ?_, ?_⟩
        · exact conjugateOrbitRepresentation_irreducible_pf45 K rho hRhoIrr o
        · exact Section1.conjugateOrbitConj_representationCharacter K rho o
      have hOrbitKer :
          ¬ Section1.subgroupInKernel'
            (Section1.conjugateOrbitConj K rho.character o) (H.subgroupOf K) :=
        not_subgroupInKernel'_conjugateOrbitConj_of_not_pf45
          K H hHK hXker o
      have hSuppOrbit :
          Section1.supportedOn
            (Section1.conjugateOrbitConj K rho.character o)
            (withOne (subgroupPullbackSet K A)) :=
        supportedOn_irreducible_of_not_subgroupInKernel_pf45
          K W1 W2 W H A h46' hOrbitIrr hOrbitKer
      exact (Section1.supportedOn_iff.mp hSuppOrbit) gK hgK'
    have hval0 :
        Section1.subgroupRestriction K (Section1.inducedCF K rho.character) gK = 0 := by
      rw [hres]
      simp [horbitZero]
    simpa [Section1.subgroupRestriction] using hval0
  · simpa using inducedClassFunction_eq_zero_of_not_mem_pf45 K rho.character hgK

private theorem theorem_4_7_nonbase_column_data_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h47 : theorem_4_7_statement K H A)
    (j : J) (hj0 : j ≠ j0) :
    ¬ Section1.subgroupInKernel' (xChar j) (H.subgroupOf K) ∧
      Section1.supportedOn (xChar j) (withOne (subgroupPullbackSet K A)) ∧
        Section1.supportedOn (piColumn piChar j) (withOne A) := by
  have h45a' := h45a
  rcases h45a with ⟨_hres, hirrX, hindX⟩
  have hkerj :
      ¬ Section1.subgroupInKernel' (xChar j) (H.subgroupOf K) :=
    not_subgroupInKernel'_xChar_of_ne_base_pf45
      K W1 W2 W H A i0 j0 ω σ piChar xChar deltaSign h46 h45a' hω h43b h43c hj0
  have hsuppj :
      Section1.supportedOn (xChar j) (withOne (subgroupPullbackSet K A)) :=
    (h47 (xChar j) (hirrX j) hkerj).1
  have hsuppIndj :
      Section1.supportedOn (Section1.inducedCF K (xChar j)) (withOne A) :=
    (h47 (xChar j) (hirrX j) hkerj).2
  refine ⟨hkerj, hsuppj, ?_⟩
  simpa [hindX j] using hsuppIndj

private theorem supportedOn_diff_a0_of_equal_degree_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h47 : theorem_4_7_statement K H A)
    {i : I} {j k : J}
    (hj0 : j ≠ j0) (hk0 : k ≠ j0)
    (hdeg : Section1.degree (piChar i j) = Section1.degree (piChar i k)) :
    Section1.supportedOn (piChar i j - piChar i k) (a0Set W2 W A) := by
  rw [Section1.supportedOn_iff]
  intro x hx
  have hxA : x ∉ A := by
    intro hxA
    exact hx (Or.inl hxA)
  have hxConj : x ∉ Section2.conjugateSet ((W : Set L) \ (W2 : Set L)) := by
    intro hxConj
    exact hx (Or.inr hxConj)
  have h46' := h46
  rcases h46 with ⟨h42, _hHnorm, _hW2H, _hHK, _hcentA, _hAinK⟩
  have hxK : x ∈ K := mem_K_of_not_mem_conjugateSet_wMinusW2_pf45 h42 hxConj
  let xK : K := ⟨x, hxK⟩
  by_cases hx1 : x = 1
  · have hEqVal : piChar i j x = piChar i k x := by
      simpa [Section1.degree, hx1] using hdeg
    simp [Pi.sub_apply, hEqVal]
  · have h45a' := h45a
    rcases h45a with ⟨hres, _hirrX, _hindX⟩
    rcases theorem_4_7_nonbase_column_data_pf45
        K W1 W2 W H A i0 j0 ω σ piChar xChar deltaSign
        h46' h45a' hω h43b h43c h47 j hj0 with ⟨_hkerj, hsuppj, _hsuppColj⟩
    rcases theorem_4_7_nonbase_column_data_pf45
        K W1 W2 W H A i0 j0 ω σ piChar xChar deltaSign
        h46' h45a' hω h43b h43c h47 k hk0 with ⟨_hkerk, hsuppk, _hsuppColk⟩
    have hxKnot :
        xK ∉ withOne (subgroupPullbackSet K A) := by
      intro hxKmem
      rcases hxKmem with hxKA | hxK1
      · exact hxA hxKA
      · exact hx1 (Subtype.ext_iff.mp hxK1)
    rw [Section1.supportedOn_iff] at hsuppj hsuppk
    have hvalj : xChar j xK = 0 := hsuppj xK hxKnot
    have hvalk : xChar k xK = 0 := hsuppk xK hxKnot
    have hresj := congrFun (hres i j) xK
    have hresk := congrFun (hres i k) xK
    have hEqj : piChar i j x = 0 := by
      simpa [Section1.subgroupRestriction] using hresj.trans hvalj
    have hEqk : piChar i k x = 0 := by
      simpa [Section1.subgroupRestriction] using hresk.trans hvalk
    simp [Pi.sub_apply, hEqj, hEqk]


public theorem supportedOn_diff_primeDadeA0_of_equal_degree_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h43d : Section4.theorem_4_3_d_statement W1 I J piChar deltaSign)
    (h47 : theorem_4_7_statement K H A)
    {i : I} {j k : J}
    (hj0 : j ≠ j0) (hk0 : k ≠ j0)
    (hdeg : Section1.degree (piChar i j) = Section1.degree (piChar i k)) :
    Section1.supportedOn (piChar i j - piChar i k)
      (primeDadeA0Set W1 W2 W A) := by
  rw [Section1.supportedOn_iff]
  intro x hx
  have hxA : x ∉ A := by
    intro hxA
    exact hx (Or.inl hxA)
  have hxCyclic : x ∉ Section2.conjugateSet (Section3.cyclicTISet W1 W2 W) := by
    intro hxCyclic
    exact hx (Or.inr hxCyclic)
  have h46' := h46
  rcases h46 with ⟨h42, _hHnorm, _hW2H, _hHK, _hcentA, _hAinK⟩
  by_cases hxK : x ∈ K
  · let xK : K := ⟨x, hxK⟩
    by_cases hx1 : x = 1
    · have hEqVal : piChar i j x = piChar i k x := by
        simpa [Section1.degree, hx1] using hdeg
      simp [Pi.sub_apply, hEqVal]
    · have h45a' := h45a
      rcases h45a with ⟨hres, _hirrX, _hindX⟩
      rcases theorem_4_7_nonbase_column_data_pf45
          K W1 W2 W H A i0 j0 ω σ piChar xChar deltaSign
          h46' h45a' hω h43b h43c h47 j hj0 with
        ⟨_hkerj, hsuppj, _hsuppColj⟩
      rcases theorem_4_7_nonbase_column_data_pf45
          K W1 W2 W H A i0 j0 ω σ piChar xChar deltaSign
          h46' h45a' hω h43b h43c h47 k hk0 with
        ⟨_hkerk, hsuppk, _hsuppColk⟩
      have hxKnot : xK ∉ withOne (subgroupPullbackSet K A) := by
        intro hxKmem
        rcases hxKmem with hxKA | hxK1
        · exact hxA hxKA
        · exact hx1 (Subtype.ext_iff.mp hxK1)
      rw [Section1.supportedOn_iff] at hsuppj hsuppk
      have hvalj : xChar j xK = 0 := hsuppj xK hxKnot
      have hvalk : xChar k xK = 0 := hsuppk xK hxKnot
      have hresj := congrFun (hres i j) xK
      have hresk := congrFun (hres i k) xK
      have hEqj : piChar i j x = 0 := by
        simpa [Section1.subgroupRestriction] using hresj.trans hvalj
      have hEqk : piChar i k x = 0 := by
        simpa [Section1.subgroupRestriction] using hresk.trans hvalk
      simp [Pi.sub_apply, hEqj, hEqk]
  · rcases exists_conjugateSet_subgroupCosetByElement_W2_of_not_mem_K_pf45
        h42 hxK with ⟨w, hwW1, hw1, hxConj⟩
    rcases hxConj with ⟨yw, hywCoset, hconj⟩
    rcases hywCoset with ⟨y, hyW2, rfl⟩
    rcases h42 with
      ⟨_hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
        _hcent, hW1W, hW2W, hDirect, _hodd⟩
    have hy1 : y = 1 := by
      by_contra hy1
      apply hxCyclic
      refine ⟨y * w, ?_, hconj⟩
      apply (Section3.cyclicTISet_mem_iff W1 W2 W).2
      have hywW : y * w ∈ W := W.mul_mem (hW2W hyW2) (hW1W hwW1)
      have hywNotW2 : y * w ∉ W2 :=
        (subgroupCosetByElement_W2_subset_wMinusW2_pf45 h46'.1 hwW1 hw1
          ⟨y, hyW2, rfl⟩).2
      have hywNotW1 : y * w ∉ W1 := by
        intro hywW1
        have hyW1 : y ∈ W1 := by
          have hmem : (y * w) * w⁻¹ ∈ W1 :=
            W1.mul_mem hywW1 (W1.inv_mem hwW1)
          simpa [mul_assoc] using hmem
        have hyBot : y ∈ (⊥ : Subgroup L) := by
          have hyInf : y ∈ W1 ⊓ W2 := Subgroup.mem_inf.mpr ⟨hyW1, hyW2⟩
          simpa [hDirect.inf_eq_bot] using hyInf
        exact hy1 (by simpa using hyBot)
      exact ⟨hywW, hywNotW1, hywNotW2⟩
    subst y
    simp only [one_mul] at hconj
    rcases hconj with ⟨g, hg⟩
    have h43b' := h43b
    rcases h43b with ⟨_hσmap, hsign, hirr, _hdistinct, _hind, _hSigma⟩
    have hsignjk : deltaSign j = deltaSign k :=
      deltaSign_eq_of_equal_degree_pf45 W1 W2 W piChar deltaSign
        (hypothesis_3_1_of_hypothesis_4_6_pf45 h46') hsign h43d hdeg
    have hwW : w ∈ W := hW1W hwW1
    have hwW2 : w ∉ W2 := by
      intro hwW2
      have hwBot : w ∈ (⊥ : Subgroup L) := by
        have hwInf : w ∈ W1 ⊓ W2 := Subgroup.mem_inf.mpr ⟨hwW1, hwW2⟩
        simpa [hDirect.inf_eq_bot] using hwInf
      exact hw1 (by simpa using hwBot)
    have hwDiff : w ∈ ((W : Set L) \ (W2 : Set L)) := ⟨hwW, hwW2⟩
    let wW : W := ⟨w, hwW⟩
    have hωj : ω i0 j wW = 1 := by
      have hker := hω.right_kernel j ⟨wW, hwW1⟩
      simpa [hω.degree_one i0 j] using hker
    have hωk : ω i0 k wW = 1 := by
      have hker := hω.right_kernel k ⟨wW, hwW1⟩
      simpa [hω.degree_one i0 k] using hker
    have hωeq : ω i j wW = ω i k wW := by
      rw [hω.product i j wW, hω.product i k wW, hωj, hωk]
    have hclassj : Section1.IsClassFunction (piChar i j) :=
      isClassFunction_of_irreducibleCharacterOnGroup_pf45 (hirr i j)
    have hclassk : Section1.IsClassFunction (piChar i k) :=
      isClassFunction_of_irreducibleCharacterOnGroup_pf45 (hirr i k)
    have hvalj : piChar i j x = deltaSign j * ω i j wW := by
      calc
        piChar i j x = piChar i j w := by rw [← hg]; exact hclassj g w
        _ = deltaSign j * ω i j wW := h43c.1 i j w hwDiff
    have hvalk : piChar i k x = deltaSign k * ω i k wW := by
      calc
        piChar i k x = piChar i k w := by rw [← hg]; exact hclassk g w
        _ = deltaSign k * ω i k wW := h43c.1 i k w hwDiff
    rw [Pi.sub_apply, hvalj, hvalk, hsignjk, hωeq, sub_self]


public theorem primeDadeA0Set_subset_a0Set
    {L : Type u} [Group L]
    (W1 W2 W : Subgroup L) (A : Set L) :
    primeDadeA0Set W1 W2 W A ⊆ a0Set W2 W A := by
  intro x hx
  rcases hx with hxA | hxV
  · exact Or.inl hxA
  · refine Or.inr ?_
    rcases hxV with ⟨v, hv, hconj⟩
    exact ⟨v, ⟨hv.1, fun hvW2 => hv.2 (Or.inr hvW2)⟩, hconj⟩

/-- A class function supported on the broad Section 4 carrier is supported on
the exact prime-Dade carrier once it vanishes on the missing `W1` conjugacy
classes. -/
public theorem supportedOn_primeDadeA0Set_of_supportedOn_a0Set_of_vanishesOn_W1
    {L : Type u} [Group L]
    (W1 W2 W : Subgroup L) (A : Set L)
    {f : ClassFunction L}
    (hfClass : Section1.IsClassFunction f)
    (hfA0 : Section1.supportedOn f (a0Set W2 W A))
    (hfW1 : ∀ x : L, x ∈ W1 → f x = 0) :
    Section1.supportedOn f (primeDadeA0Set W1 W2 W A) := by
  rw [Section1.supportedOn_iff] at hfA0 ⊢
  intro x hxPrime
  by_cases hxA0 : x ∈ a0Set W2 W A
  · rcases hxA0 with hxA | hxConj
    · exact False.elim (hxPrime (Or.inl hxA))
    · rcases hxConj with ⟨w, hw, g, hg⟩
      have hwW1 : w ∈ W1 := by
        by_contra hwNotW1
        apply hxPrime
        refine Or.inr ⟨w, ?_, g, hg⟩
        exact (Section3.cyclicTISet_mem_iff W1 W2 W).2
          ⟨hw.1, hwNotW1, hw.2⟩
      calc
        f x = f w := by rw [← hg]; exact hfClass g w
        _ = 0 := hfW1 w hwW1
  · exact hfA0 x hxA0

private theorem supportedOn_smul_pf45
    {G : Type*} [Group G]
    {A : Set G} {f : ClassFunction G} {z : ℂ}
    (hf : Section1.supportedOn f A) :
    Section1.supportedOn (z • f) A := by
  rw [Section1.supportedOn_iff] at hf ⊢
  intro x hx
  simp [Pi.smul_apply, hf x hx]

private theorem theorem_4_10_formula_pf45
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    {W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (W1 W2 : Subgroup L)
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σL : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (hτσ : tau_agrees_on_cyclicTI_induced_statement W1 W2 W σ τ) :
    theorem_4_10_statement i0 j0 ω σ piChar deltaSign τ := by
  have h43b' := h43b
  intro i j
  rcases h43b with ⟨_hσmapL, _hsign, _hirr, _hdistinct, hind, _hSigmaL⟩
  have hδ0 : deltaSign j0 = 1 :=
    (Section4.proposition_4_4_base
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σL) (piChar := piChar) (deltaSign := deltaSign)
      hω h43b').1
  let α : ClassFunction W := Section3.alphaIJ W i0 j0 ω i j
  have hα : Section2.CFOn W (Section3.cyclicTISet W1 W2 W) α :=
    Section3.alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i j
  have hbeta :
      deltaSign j • piChar i j - deltaSign j • piChar i0 j - piChar i j0 + piChar i0 j0 =
        Section1.inducedCF W α := by
    calc
      deltaSign j • piChar i j - deltaSign j • piChar i0 j - piChar i j0 + piChar i0 j0
          = deltaSign j • (piChar i j - piChar i0 j) -
              deltaSign j0 • (piChar i j0 - piChar i0 j0) := by
                simp [hδ0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = Section1.inducedCF W (ω i j - ω i0 j) -
            Section1.inducedCF W (ω i j0 - ω i0 j0) := by
              rw [hind i j, hind i j0]
      _ = Section1.inducedCFLinear W
            ((ω i j - ω i0 j) - (ω i j0 - ω i0 j0)) := by
              rw [LinearMap.map_sub, Section1.inducedCFLinear_apply,
                Section1.inducedCFLinear_apply]
      _ = Section1.inducedCF W α := by
            rw [Section1.inducedCFLinear_apply]
            simp [α, Section3.alphaIJ, hω.principal, sub_eq_add_neg,
              add_assoc, add_left_comm, add_comm]
  calc
    τ (deltaSign j • piChar i j - deltaSign j • piChar i0 j - piChar i j0 + piChar i0 j0)
        = τ (Section1.inducedCF W α) := by rw [hbeta]
    _ = σ α := hτσ α hα
    _ = (σ (ω i j) - σ (ω i0 j)) - (σ (ω i j0) - σ (ω i0 j0)) := by
          simp [α, Section3.alphaIJ, hω.principal, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm]

/-! ## Top-down theorem shells -/

public theorem theorem_4_5_a
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : Section4.theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (hC : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω) :
    ∃ xChar : J → ClassFunction K, theorem_4_5_a_statement K piChar xChar := by
  classical
  have hKnorm : K.Normal := normal_K_of_hypothesis_4_2_pf45 h42
  let : K.Normal := hKnorm
  obtain ⟨e, he⟩ :=
    exists_baseRow_equiv_of_hypothesis_4_2_pf45
      (K := K) (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σ) (piChar := piChar) (deltaSign := deltaSign)
      h42 hω hB hC
  let Q := L ⧸ K
  have hQcyc : IsCyclic Q := by
    simpa [Q] using
      isCyclic_quotient_K_of_hypothesis_4_2_pf45
        (K := K) (W1 := W1) (W2 := W2) (W := W) hKnorm h42
  let : DecidableEq Q := Classical.decEq Q
  let : CommGroup Q := by
    simpa [Q] using hQcyc.commGroup
  let : Finite (Q →* ℂˣ) := Finite.of_equiv I e.symm
  let : Fintype (Q →* ℂˣ) := Fintype.ofFinite (Q →* ℂˣ)
  have hExpNeZero : NeZero (Monoid.exponent Q) :=
    Monoid.neZero_exponent_of_finite (G := Q)
  let : NeZero (Monoid.exponent Q) := hExpNeZero
  let : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) :=
    Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
  have hB' := hB
  rcases hB with ⟨_hσmap, _hsign, hirr, _hdistinct, _hind, _hSigma⟩
  have htwist :
      ∀ chi : Q →* ℂˣ, ∀ j : J,
        Section1.characterInflationByHom (QuotientGroup.mk' K) chi * piChar i0 j =
          piChar (e chi) j := by
    exact
      baseRow_twist_eq_row_pf45
        (K := K) (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (ω := ω) (σ := σ) (piChar := piChar) (deltaSign := deltaSign)
        h42 hω hB' hC he
  have hInd :
      ∀ j, Section1.inducedCF K (Section1.subgroupRestriction K (piChar i0 j)) =
        piColumn piChar j := by
    intro j
    have hquot_comm : Std.Commutative (fun x y : Q => x * y) := by
      let : CommGroup Q := IsCyclic.commGroup
      infer_instance
    have hclass : Section1.IsClassFunction (piChar i0 j) :=
      isClassFunction_of_irreducibleCharacterOnGroup_pf45 (hirr i0 j)
    calc
      Section1.inducedCF K (Section1.subgroupRestriction K (piChar i0 j)) =
          Section1.familySum
            (fun chi : Q →* ℂˣ =>
              Section1.characterInflationByHom (QuotientGroup.mk' K) chi *
                piChar i0 j) := by
            simpa [Q] using
              induced_restriction_eq_regular_inflated_sum_pf45
                (L := L) (K := K) hquot_comm (psi := piChar i0 j) hclass
      _ = Section1.familySum (fun chi : Q →* ℂˣ => piChar (e chi) j) := by
            congr
            funext chi
            exact htwist chi j
      _ = piColumn piChar j := by
            ext g
            simpa [Section1.familySum, piColumn] using
              Fintype.sum_equiv e
                (fun chi : Q →* ℂˣ => piChar (e chi) j g)
                (fun i : I => piChar i j g)
                (by intro chi; rfl)
  refine ⟨fun j => Section1.subgroupRestriction K (piChar i0 j), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact subgroupRestriction_fixed_column_pf45
      K W1 W2 W i0 j0 ω σ piChar deltaSign h42 hω hB' i j
  · exact irreducible_fixed_column_of_induced_eq_piColumn_pf45
      K W1 W2 W i0 j0 ω σ piChar deltaSign hω hB' hInd
  · exact hInd

private theorem exists_irreducible_constituent_of_subgroupRestriction_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {ψ : ClassFunction L}
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ) :
    ∃ X : ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup X ∧
        Section1.scalarProduct K X (Section1.subgroupRestriction K ψ) ≠ 0 := by
  rcases hψ with ⟨n, ρ, hρirr, hρchar⟩
  let ρK : Representation ℂ K (Fin n → ℂ) := ρ.comp K.subtype
  let : Nontrivial (Fin n → ℂ) := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨φ, hφirr⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρK
  let : Nontrivial φ.toSubmodule := Subrepresentation.irreducible_module_nontrivial φ.toRepresentation
  let incl : Theory.Representation.RepMap φ.toRepresentation ρK := by
    refine Theory.Representation.RepMap.mk φ.toSubmodule.subtype ?_
    intro k
    ext v
    rfl
  have hincl_ne : incl ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := exists_ne (0 : φ.toSubmodule)
    have hval : incl v = 0 := by
      simpa using congrArg (fun f : Theory.Representation.RepMap φ.toRepresentation ρK => f v) hzero
    have hsub : v = 0 := by
      apply Subtype.ext
      simpa [incl] using hval
    exact hv hsub
  have hinner_res :
      Section1.scalarProduct K ρK.character φ.toRepresentation.character ≠ 0 := by
    have hfinpos :
        0 < Module.finrank ℂ (Representation.IntertwiningMap φ.toRepresentation ρK) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨incl, hincl_ne⟩
    rw [Section1.scalarProduct_representation_char_eq_finrank]
    exact_mod_cast (Nat.ne_of_gt hfinpos)
  have hresChar :
      Section1.subgroupRestriction K ψ = ρK.character := by
    ext k
    simp [ρK, Section1.subgroupRestriction, hρchar, Representation.character]
  refine ⟨φ.toRepresentation.character, ?_, ?_⟩
  · refine ⟨Module.finrank ℂ φ.toSubmodule,
      standardizeRepresentation_pf45 φ.toRepresentation, ?_, ?_⟩
    · exact standardizeRepresentation_irreducible_pf45 φ.toRepresentation hφirr
    · ext k
      symm
      exact standardizeRepresentation_character_pf45 φ.toRepresentation k
  · have hinner_res' :
        Section1.scalarProduct K (Section1.subgroupRestriction K ψ)
          φ.toRepresentation.character ≠ 0 := by
      simpa [hresChar] using hinner_res
    exact
      (Section1.scalarProduct_ne_zero_swap
        φ.toRepresentation.character (Section1.subgroupRestriction K ψ)).2 hinner_res'

private theorem irreducible_mem_range_of_piColumn_inner_ne_zero_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I)
    (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    {ψ : ClassFunction L}
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    {j : J}
    (hinner : Section1.scalarProduct L (piColumn piChar j) ψ ≠ 0) :
    ψ ∈ Set.range (fun p : I × J => piChar p.1 p.2) := by
  rcases h43b with ⟨_hσmap, _hsign, hirr, _hdistinct, _hind, _hSigma⟩
  by_contra hnot
  have hzero : Section1.scalarProduct L (piColumn piChar j) ψ = 0 := by
    unfold piColumn
    have hsum :
        ((∑ i : I, piChar i j : ClassFunction L)) = fun g => ∑ i : I, piChar i j g := by
      ext g
      simp
    rw [hsum, Section1.scalarProduct_fintype_sum_left]
    refine Finset.sum_eq_zero ?_
    intro i _hi
    have hneq : piChar i j ≠ ψ := by
      intro hEq
      refine hnot ⟨(i, j), ?_⟩
      simpa using hEq
    exact scalarProduct_irreducible_ne_pf45 (hirr i j) hψ hneq
  exact hinner hzero

private theorem theorem_4_5_b_exhaustion_of_first_part_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    {W1 W2 W : Subgroup L}
    (i0 : I)
    (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (deltaSign : J → ℂ)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (hfirst :
      ∀ X : ClassFunction K,
        Section1.IsIrreducibleCharacterOnGroup X →
          X ∉ Set.range xChar →
            Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K X)) :
    ∀ ψ : ClassFunction L,
      Section1.IsIrreducibleCharacterOnGroup ψ →
        ψ ∈ Set.range (fun p : I × J => piChar p.1 p.2) ∨
          ∃ X : ClassFunction K,
            Section1.IsIrreducibleCharacterOnGroup X ∧
              X ∉ Set.range xChar ∧
                ψ = Section1.inducedCF K X := by
  rcases h45a with ⟨_hres, hirrX, hindX⟩
  intro ψ hψ
  obtain ⟨X, hXirr, hXinner⟩ :=
    exists_irreducible_constituent_of_subgroupRestriction_pf45 K hψ
  by_cases hXmem : X ∈ Set.range xChar
  · rcases hXmem with ⟨j, rfl⟩
    left
    have hψclass : Section1.IsClassFunction ψ :=
      isClassFunction_of_irreducibleCharacterOnGroup_pf45 hψ
    have hcolInner :
        Section1.scalarProduct L (Section1.inducedCF K (xChar j)) ψ ≠ 0 := by
      rw [Section1.scalarProduct_inducedCF_left K (xChar j) ψ hψclass]
      exact hXinner
    have hpiInner : Section1.scalarProduct L (piColumn piChar j) ψ ≠ 0 := by
      simpa [hindX j] using hcolInner
    exact irreducible_mem_range_of_piColumn_inner_ne_zero_pf45
      i0 j0 ω σ piChar deltaSign hω h43b hψ hpiInner
  · right
    refine ⟨X, hXirr, hXmem, ?_⟩
    have hψclass : Section1.IsClassFunction ψ :=
      isClassFunction_of_irreducibleCharacterOnGroup_pf45 hψ
    have hindInner :
        Section1.scalarProduct L (Section1.inducedCF K X) ψ ≠ 0 := by
      rw [Section1.scalarProduct_inducedCF_left K X ψ hψclass]
      exact hXinner
    have hIndIrr :
        Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K X) :=
      hfirst X hXirr hXmem
    have hEq : Section1.inducedCF K X = ψ := by
      by_contra hne
      exact hindInner (scalarProduct_irreducible_ne_pf45 hIndIrr hψ hne)
    exact hEq.symm

private theorem xChar_fixed_by_conjugateOnNormal_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L) [K.Normal]
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I)
    (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (xChar : J → ClassFunction K)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : Section4.theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h45a : theorem_4_5_a_statement K piChar xChar) :
    ∀ j g, Section1.conjugateOnNormal K (xChar j) g = xChar j := by
  rcases h45a with ⟨hres, _hirrX, _hindX⟩
  rcases hB with ⟨_hσmap, _hsign, hirr, _hdistinct, _hind, _hSigma⟩
  intro j g
  have hclass : Section1.IsClassFunction (piChar i0 j) :=
    isClassFunction_of_irreducibleCharacterOnGroup_pf45 (hirr i0 j)
  calc
    Section1.conjugateOnNormal K (xChar j) g =
        Section1.conjugateOnNormal K
          (Section1.subgroupRestriction K (piChar i0 j)) g := by
            rw [hres i0 j]
    _ = Section1.subgroupRestriction K (piChar i0 j) :=
      conjugateOnNormal_subgroupRestriction_eq_of_isClassFunction_pf45
        K (piChar i0 j) hclass g
    _ = xChar j := hres i0 j

private theorem irreducible_fixed_mem_range_of_card_bound_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal]
    {J : Type*} [Fintype J]
    (xChar : J → ClassFunction K)
    {g : L}
    (hfixedFinite :
      ({X : ClassFunction K |
        Section1.IsIrreducibleCharacterOnGroup X ∧
          Section1.conjugateOnNormal K X g = X} : Set (ClassFunction K)).Finite)
    (hfixedX_le :
      Nat.card {X : ClassFunction K |
        Section1.IsIrreducibleCharacterOnGroup X ∧
          Section1.conjugateOnNormal K X g = X} ≤ Nat.card (Set.range xChar))
    (hfixed_range :
      Set.range xChar ⊆
        {X : ClassFunction K |
          Section1.IsIrreducibleCharacterOnGroup X ∧
            Section1.conjugateOnNormal K X g = X})
    {X : ClassFunction K}
    (hX : Section1.IsIrreducibleCharacterOnGroup X)
    (hfix : Section1.conjugateOnNormal K X g = X) :
    X ∈ Set.range xChar := by
  classical
  let fixedSet : Set (ClassFunction K) :=
    {X : ClassFunction K |
      Section1.IsIrreducibleCharacterOnGroup X ∧
        Section1.conjugateOnNormal K X g = X}
  have hrange_card :
      Nat.card fixedSet ≤ Nat.card (Set.range xChar) := hfixedX_le
  have hfixed_eq : fixedSet = Set.range xChar := by
    refine (Set.Finite.eq_of_subset_of_card_le (s := Set.range xChar)
      (t := fixedSet) ?_ ?_ ?_).symm
    · simpa [fixedSet] using hfixedFinite
    · exact hfixed_range
    · exact hrange_card
  have hXfixed : X ∈ fixedSet := ⟨hX, hfix⟩
  simpa [hfixed_eq] using hXfixed

private theorem ofConjClassFunction_toConjClassFunction_pf45
    {G : Type*} [Group G]
    (φ : ClassFunction G) (hφ : Section1.IsClassFunction φ) :
    Section1.ofConjClassFunction (Section1.toConjClassFunction φ hφ) = φ := by
  ext g
  rfl

private theorem toConjClassFunction_isIrreducibleCharacter_of_onGroup_pf45
    {G : Type u} [Group G] [Finite G]
    {φ : ClassFunction G}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ) :
    Theory.Character.IsIrreducibleConjCharacter
      (Section1.toConjClassFunction φ
        (isClassFunction_of_irreducibleCharacterOnGroup_pf45 hφ)) := by
  classical
  rcases hφ with ⟨n, ρ, hρirr, rfl⟩
  constructor
  · refine ⟨n, ρ, ?_⟩
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    rfl
  · have hnorm :=
      (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
    have hρclass : Section1.IsClassFunction ρ.character := by
      intro x g
      simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
    have htoeq :
        Section1.toConjClassFunction ρ.character hρclass =
          Theory.Character.characterClassFunction ρ := by
      apply Section1.toConjClassFunction_eq_of_apply
      intro g
      rfl
    calc
      Section1.scalarProduct G ρ.character ρ.character =
          Theory.Character.classFunctionInner
            (Section1.toConjClassFunction ρ.character hρclass)
            (Section1.toConjClassFunction ρ.character hρclass) :=
        (Section1.classFunctionInner_toConjClassFunction
          ρ.character ρ.character hρclass hρclass).symm
      _ = Theory.Character.classFunctionInner
          (Theory.Character.characterClassFunction ρ)
          (Theory.Character.characterClassFunction ρ) := by rw [htoeq]
      _ = 1 := hnorm

private theorem ofConjClassFunction_isIrreducibleCharacterOnGroup_pf45
    {G : Type u} [Group G] [Finite G]
    {χ : Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsIrreducibleConjCharacter χ) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.ofConjClassFunction χ) := by
  classical
  rcases hχ with ⟨⟨n, ρ, hχeq⟩, hnorm⟩
  refine ⟨n, ρ, ?_, ?_⟩
  · exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).2
      (by simpa [hχeq] using hnorm)
  · simpa [hχeq] using
      (Section1.ofConjClassFunction_characterClassFunction ρ)

private theorem irreducibleCharacterOnGroup_set_finite_pf45
    {G : Type u} [Group G] [Finite G] :
    ({φ : ClassFunction G | Section1.IsIrreducibleCharacterOnGroup φ} :
      Set (ClassFunction G)).Finite := by
  classical
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, χ, hχ, _b, _hb⟩
  let : Fintype ι := hι
  let χold : ι → ClassFunction G := fun i => Section1.ofConjClassFunction (χ i)
  refine (Set.finite_range χold).subset ?_
  intro φ hφ
  rcases hχ.2.1
      (Section1.toConjClassFunction φ
        (isClassFunction_of_irreducibleCharacterOnGroup_pf45 hφ))
      (toConjClassFunction_isIrreducibleCharacter_of_onGroup_pf45 hφ) with
    ⟨i, hi⟩
  refine ⟨i, ?_⟩
  dsimp [χold]
  rw [hi]
  exact ofConjClassFunction_toConjClassFunction_pf45 φ
    (isClassFunction_of_irreducibleCharacterOnGroup_pf45 hφ)


private theorem isIrreducibleCharacterOnGroup_conjugateOnNormal_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal]
    {X : ClassFunction K}
    (hX : Section1.IsIrreducibleCharacterOnGroup X) (g : L) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.conjugateOnNormal K X g) := by
  rcases hX with ⟨n, ρ, hρirr, rfl⟩
  refine ⟨n, Section1.conjugateRepresentation K ρ g, ?_, ?_⟩
  · let : Representation.IsIrreducible ρ := hρirr
    exact Section1.irreducible_conjugateRepresentation K ρ g
  · exact (Section1.representationCharacter_conjugateRepresentation K ρ g).symm


private theorem trace_linearEquiv_eq_ncard_fixedPoints_of_permutes_basis_pf45
    {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module ℂ M]
    (b : Module.Basis ι ℂ M)
    (σ : Equiv.Perm ι)
    (T : M ≃ₗ[ℂ] M)
    (hT : ∀ i, T (b i) = b (σ i)) :
    LinearMap.trace ℂ M T.toLinearMap =
      ((Function.fixedPoints σ).ncard : ℂ) := by
  classical
  have hmatrix :
      LinearMap.toMatrix b b T.toLinearMap = (σ⁻¹).permMatrix ℂ := by
    ext i j
    by_cases h : σ j = i
    · have hsymm : σ⁻¹ i = j := by
        rw [← h]
        simp
      simp [LinearMap.toMatrix_apply, hT, h, hsymm]
    · have hsymm : σ⁻¹ i ≠ j := by
        intro hsymm
        apply h
        rw [← hsymm]
        simp
      have hsymm' : (Equiv.symm σ) i ≠ j := by
        exact hsymm
      rw [LinearMap.toMatrix_apply]
      have hentry :
          (b.repr ((T : M →ₗ[ℂ] M) (b j))) i = (b.repr (b (σ j))) i := by
        simpa using congrArg (fun v => (b.repr v) i) (hT j)
      rw [hentry]
      simp [h, hsymm']
  calc
    LinearMap.trace ℂ M T.toLinearMap =
        Matrix.trace (LinearMap.toMatrix b b T.toLinearMap) := by
          rw [LinearMap.trace_eq_matrix_trace ℂ b T.toLinearMap]
    _ = Matrix.trace ((σ⁻¹).permMatrix ℂ) := by
          rw [hmatrix]
    _ = ((Function.fixedPoints (σ⁻¹ : Equiv.Perm ι)).ncard : ℂ) := by
          exact Matrix.trace_permutation (R := ℂ) (σ := σ⁻¹)
    _ = ((Function.fixedPoints σ).ncard : ℂ) := by
          congr 1
          congr 1
          ext i
          constructor
          · intro hi
            change σ⁻¹ i = i at hi
            calc
              σ i = σ (σ⁻¹ i) := by rw [hi]
              _ = i := by simp
          · intro hi
            change σ i = i at hi
            apply σ.injective
            simp [hi]

private noncomputable def normalSubgroupConjMulEquiv_pf45
    {L : Type u} [Group L]
    (K : Subgroup L) [K.Normal] (g : L) : K ≃* K where
  toFun x :=
    ⟨g * (x : L) * g⁻¹,
      Subgroup.Normal.conj_mem (inferInstance : K.Normal) (x : L) x.2 g⟩
  invFun x :=
    ⟨g⁻¹ * (x : L) * g, by
      simpa using
        ((inferInstance : K.Normal).conj_mem (x : L) x.2 g⁻¹)⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_assoc]

private noncomputable def conjClassesConjPerm_pf45
    {L : Type u} [Group L]
    (K : Subgroup L) [K.Normal] (g : L) :
    Equiv.Perm (ConjClasses K) where
  toFun := ConjClasses.map (normalSubgroupConjMulEquiv_pf45 K g).toMonoidHom
  invFun := ConjClasses.map (normalSubgroupConjMulEquiv_pf45 K g⁻¹).toMonoidHom
  left_inv c := by
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    apply ConjClasses.mk_eq_mk_iff_isConj.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp [normalSubgroupConjMulEquiv_pf45, mul_assoc]
  right_inv c := by
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    apply ConjClasses.mk_eq_mk_iff_isConj.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp [normalSubgroupConjMulEquiv_pf45, mul_assoc]

private theorem conjClassesConjPerm_mk_pf45
    {L : Type u} [Group L]
    (K : Subgroup L) [K.Normal] (g : L) (x : K) :
    conjClassesConjPerm_pf45 K g (ConjClasses.mk x) =
      ConjClasses.mk ((normalSubgroupConjMulEquiv_pf45 K g) x) := rfl

private theorem conjClassesConjPerm_symm_inv_mk_pf45
    {L : Type u} [Group L]
    (K : Subgroup L) [K.Normal] (g : L) (x : K) :
    (conjClassesConjPerm_pf45 K g⁻¹).symm (ConjClasses.mk x) =
      ConjClasses.mk ((normalSubgroupConjMulEquiv_pf45 K g) x) := by
  apply (conjClassesConjPerm_pf45 K g⁻¹).injective
  rw [Equiv.apply_symm_apply, conjClassesConjPerm_mk_pf45]
  apply ConjClasses.mk_eq_mk_iff_isConj.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simp [normalSubgroupConjMulEquiv_pf45, mul_assoc]

private noncomputable def classFunctionConjLinearEquiv_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L) :
    (ConjClasses K → ℂ) ≃ₗ[ℂ] (ConjClasses K → ℂ) where
  toFun φ := fun c => φ ((conjClassesConjPerm_pf45 K g).symm c)
  invFun φ := fun c => φ ((conjClassesConjPerm_pf45 K g) c)
  left_inv φ := by
    ext c
    simp
  right_inv φ := by
    ext c
    simp
  map_add' φ ψ := by
    ext c
    simp
  map_smul' a φ := by
    ext c
    simp

private theorem classFunctionConjLinearEquiv_basisFun_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L)
    (c : ConjClasses K) :
    classFunctionConjLinearEquiv_pf45 K g
        ((Pi.basisFun ℂ (ConjClasses K)) c) =
      (Pi.basisFun ℂ (ConjClasses K))
        ((conjClassesConjPerm_pf45 K g) c) := by
  classical
  ext d
  by_cases hsymm : (conjClassesConjPerm_pf45 K g).symm d = c
  · have hdc : d = (conjClassesConjPerm_pf45 K g) c := by
      rw [← hsymm]
      simp
    rw [hdc]
    have hinv :
        (conjClassesConjPerm_pf45 K g).symm
          ((conjClassesConjPerm_pf45 K g) c) = c := by
      simp
    change
      ((Pi.basisFun ℂ (ConjClasses K)) c)
          ((conjClassesConjPerm_pf45 K g).symm
            ((conjClassesConjPerm_pf45 K g) c)) =
        ((Pi.basisFun ℂ (ConjClasses K))
          ((conjClassesConjPerm_pf45 K g) c))
            ((conjClassesConjPerm_pf45 K g) c)
    simp [hinv]
  · have hdc : d ≠ (conjClassesConjPerm_pf45 K g) c := by
      intro hdc
      apply hsymm
      rw [hdc]
      simp
    simp [classFunctionConjLinearEquiv_pf45, hsymm, hdc]

private theorem classFunctionConjLinearEquiv_toConjClassFunction_conjugateOnNormal_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] {X : ClassFunction K}
    (hXirr : Section1.IsIrreducibleCharacterOnGroup X) (g : L) :
    classFunctionConjLinearEquiv_pf45 K g⁻¹
        (Section1.toConjClassFunction X
          (isClassFunction_of_irreducibleCharacterOnGroup_pf45 hXirr)) =
      Section1.toConjClassFunction (Section1.conjugateOnNormal K X g)
        (isClassFunction_of_irreducibleCharacterOnGroup_pf45
          (isIrreducibleCharacterOnGroup_conjugateOnNormal_pf45 K hXirr g)) := by
  ext c
  rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
  change
    Section1.toConjClassFunction X
        (isClassFunction_of_irreducibleCharacterOnGroup_pf45 hXirr)
        ((conjClassesConjPerm_pf45 K g⁻¹).symm (ConjClasses.mk x)) =
      Section1.toConjClassFunction (Section1.conjugateOnNormal K X g)
        (isClassFunction_of_irreducibleCharacterOnGroup_pf45
          (isIrreducibleCharacterOnGroup_conjugateOnNormal_pf45 K hXirr g))
        (ConjClasses.mk x)
  rw [conjClassesConjPerm_symm_inv_mk_pf45]
  change
    X ((normalSubgroupConjMulEquiv_pf45 K g) x) =
      X ⟨g * (x : L) * g⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : K.Normal) (x : L) x.2 g⟩
  rfl

private theorem classFunctionConjLinearEquiv_isIrreducibleCharacter_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L)
    {χ : Theory.Character.ConjClassFunction K}
    (hχ : Theory.Character.IsIrreducibleConjCharacter χ) :
    Theory.Character.IsIrreducibleConjCharacter
      (classFunctionConjLinearEquiv_pf45 K g χ) := by
  classical
  let X : ClassFunction K := Section1.ofConjClassFunction χ
  have hXirr : Section1.IsIrreducibleCharacterOnGroup X :=
    ofConjClassFunction_isIrreducibleCharacterOnGroup_pf45 hχ
  have hto :
      Section1.toConjClassFunction X
        (isClassFunction_of_irreducibleCharacterOnGroup_pf45 hXirr) = χ := by
    simpa [X] using Section1.toConjClassFunction_ofConjClassFunction χ
  have hconj :
      classFunctionConjLinearEquiv_pf45 K g χ =
        Section1.toConjClassFunction (Section1.conjugateOnNormal K X g⁻¹)
          (isClassFunction_of_irreducibleCharacterOnGroup_pf45
            (isIrreducibleCharacterOnGroup_conjugateOnNormal_pf45 K hXirr g⁻¹)) := by
    calc
      classFunctionConjLinearEquiv_pf45 K g χ =
          classFunctionConjLinearEquiv_pf45 K (g⁻¹)⁻¹
            (Section1.toConjClassFunction X
              (isClassFunction_of_irreducibleCharacterOnGroup_pf45 hXirr)) := by
            simp [hto]
      _ =
          Section1.toConjClassFunction (Section1.conjugateOnNormal K X g⁻¹)
            (isClassFunction_of_irreducibleCharacterOnGroup_pf45
              (isIrreducibleCharacterOnGroup_conjugateOnNormal_pf45 K hXirr g⁻¹)) := by
            exact
              classFunctionConjLinearEquiv_toConjClassFunction_conjugateOnNormal_pf45
                (K := K) (X := X) hXirr (g := g⁻¹)
  rw [hconj]
  exact toConjClassFunction_isIrreducibleCharacter_of_onGroup_pf45
    (isIrreducibleCharacterOnGroup_conjugateOnNormal_pf45 K hXirr g⁻¹)

private theorem classFunctionConjLinearEquiv_symm_apply_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L)
    (χ : Theory.Character.ConjClassFunction K) :
    (classFunctionConjLinearEquiv_pf45 K g).symm χ =
      classFunctionConjLinearEquiv_pf45 K g⁻¹ χ := by
  ext c
  rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
  simp [classFunctionConjLinearEquiv_pf45, conjClassesConjPerm_mk_pf45,
    conjClassesConjPerm_symm_inv_mk_pf45]

private noncomputable def irreducibleConjClassFunctionPerm_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L) :
    Equiv.Perm
      {χ : Theory.Character.ConjClassFunction K //
        Theory.Character.IsIrreducibleConjCharacter χ} where
  toFun χ :=
    ⟨classFunctionConjLinearEquiv_pf45 K g χ.1,
      classFunctionConjLinearEquiv_isIrreducibleCharacter_pf45 K g χ.2⟩
  invFun χ :=
    ⟨classFunctionConjLinearEquiv_pf45 K g⁻¹ χ.1,
      classFunctionConjLinearEquiv_isIrreducibleCharacter_pf45 K g⁻¹ χ.2⟩
  left_inv χ := by
    apply Subtype.ext
    change classFunctionConjLinearEquiv_pf45 K g⁻¹
        (classFunctionConjLinearEquiv_pf45 K g χ.1) = χ.1
    rw [← classFunctionConjLinearEquiv_symm_apply_pf45 K g]
    simp
  right_inv χ := by
    apply Subtype.ext
    change classFunctionConjLinearEquiv_pf45 K g
        (classFunctionConjLinearEquiv_pf45 K g⁻¹ χ.1) = χ.1
    rw [← classFunctionConjLinearEquiv_symm_apply_pf45 K g]
    simp

private theorem trace_classFunctionConjLinearEquiv_eq_fixed_irreducibles_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L) :
    LinearMap.trace ℂ (ConjClasses K → ℂ)
        (classFunctionConjLinearEquiv_pf45 K g).toLinearMap =
      ((Function.fixedPoints
          (irreducibleConjClassFunctionPerm_pf45 K g)).ncard : ℂ) := by
  classical
  rcases Theory.Character.irreducible_characters_form_basis (G := K) with
    ⟨ι, hι, χ, hχ, b, hb⟩
  let : Fintype ι := hι
  let f :
      ι →
        {χ : Theory.Character.ConjClassFunction K //
          Theory.Character.IsIrreducibleConjCharacter χ} :=
    fun i => ⟨χ i, hχ.1 i⟩
  have hf_bij : Function.Bijective f := by
    constructor
    · intro i j hij
      apply hχ.2.2
      exact congrArg Subtype.val hij
    · intro ψ
      rcases hχ.2.1 ψ.1 ψ.2 with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hi
  let e :
      ι ≃
        {χ : Theory.Character.ConjClassFunction K //
          Theory.Character.IsIrreducibleConjCharacter χ} :=
    Equiv.ofBijective f hf_bij
  let : Fintype
      {χ : Theory.Character.ConjClassFunction K //
        Theory.Character.IsIrreducibleConjCharacter χ} :=
    Fintype.ofEquiv ι e
  let bIrr :
      Module.Basis
        {χ : Theory.Character.ConjClassFunction K //
          Theory.Character.IsIrreducibleConjCharacter χ}
        ℂ (Theory.Character.ConjClassFunction K) :=
    b.reindex e
  have hbIrr :
      ∀ ψ :
        {χ : Theory.Character.ConjClassFunction K //
          Theory.Character.IsIrreducibleConjCharacter χ},
        bIrr ψ = ψ.1 := by
    intro ψ
    dsimp [bIrr]
    rw [Module.Basis.reindex_apply, hb]
    have h := congrArg Subtype.val (Equiv.apply_symm_apply e ψ)
    dsimp [e, f] at h
    exact h
  exact
    trace_linearEquiv_eq_ncard_fixedPoints_of_permutes_basis_pf45
      bIrr (irreducibleConjClassFunctionPerm_pf45 K g)
      (classFunctionConjLinearEquiv_pf45 K g)
      (by
        intro ψ
        rw [hbIrr, hbIrr]
        rfl)

private theorem trace_classFunctionConjLinearEquiv_eq_fixed_conjClasses_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L) :
    LinearMap.trace ℂ (ConjClasses K → ℂ)
        (classFunctionConjLinearEquiv_pf45 K g).toLinearMap =
      ((Function.fixedPoints (conjClassesConjPerm_pf45 K g)).ncard : ℂ) := by
  classical
  exact
    trace_linearEquiv_eq_ncard_fixedPoints_of_permutes_basis_pf45
      (Pi.basisFun ℂ (ConjClasses K)) (conjClassesConjPerm_pf45 K g)
      (classFunctionConjLinearEquiv_pf45 K g)
      (classFunctionConjLinearEquiv_basisFun_pf45 K g)

private theorem fixedPoints_perm_inv_ncard_pf45
    {α : Type*} (σ : Equiv.Perm α) :
    (Function.fixedPoints (σ⁻¹ : Equiv.Perm α)).ncard =
      (Function.fixedPoints σ).ncard := by
  classical
  congr 1
  ext x
  constructor
  · intro hx
    rw [Function.mem_fixedPoints_iff] at hx ⊢
    calc
      σ x = σ (σ⁻¹ x) := by rw [hx]
      _ = x := by simp
  · intro hx
    rw [Function.mem_fixedPoints_iff] at hx ⊢
    calc
      σ⁻¹ x = σ⁻¹ (σ x) := by rw [hx]
      _ = x := by simp

private theorem fixed_irreducible_natCard_eq_fixed_conjClassFunctions_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L) :
    Nat.card {X : ClassFunction K |
        Section1.IsIrreducibleCharacterOnGroup X ∧
          Section1.conjugateOnNormal K X g = X} =
      Nat.card
        (Function.fixedPoints (irreducibleConjClassFunctionPerm_pf45 K g⁻¹)) := by
  classical
  refine Nat.card_congr ?_
  refine
    { toFun := fun X =>
        ⟨⟨Section1.toConjClassFunction X.1
              (isClassFunction_of_irreducibleCharacterOnGroup_pf45 X.property.1),
            toConjClassFunction_isIrreducibleCharacter_of_onGroup_pf45 X.property.1⟩,
          ?_⟩
      invFun := fun ψ =>
        ⟨Section1.ofConjClassFunction ψ.1.1, ⟨
          ofConjClassFunction_isIrreducibleCharacterOnGroup_pf45 ψ.1.2,
          ?_⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Subtype.ext
    have hXirr : Section1.IsIrreducibleCharacterOnGroup X.1 := X.property.1
    have hXfix : Section1.conjugateOnNormal K X.1 g = X.1 := X.property.2
    change
      classFunctionConjLinearEquiv_pf45 K g⁻¹
          (Section1.toConjClassFunction X.1
            (isClassFunction_of_irreducibleCharacterOnGroup_pf45 hXirr)) =
        Section1.toConjClassFunction X.1
          (isClassFunction_of_irreducibleCharacterOnGroup_pf45 hXirr)
    rw [classFunctionConjLinearEquiv_toConjClassFunction_conjugateOnNormal_pf45
      (K := K) (X := X.1) (hXirr := hXirr) (g := g)]
    ext c
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    change (Section1.conjugateOnNormal K X.1 g) x = X.1 x
    rw [hXfix]
  · have hψfix := congrArg Subtype.val ψ.2
    change
      classFunctionConjLinearEquiv_pf45 K g⁻¹ ψ.1.1 = ψ.1.1 at hψfix
    let X : ClassFunction K := Section1.ofConjClassFunction ψ.1.1
    have hXirr :
        Section1.IsIrreducibleCharacterOnGroup X :=
      ofConjClassFunction_isIrreducibleCharacterOnGroup_pf45 ψ.1.2
    have htoX :
        Section1.toConjClassFunction X
            (isClassFunction_of_irreducibleCharacterOnGroup_pf45 hXirr) =
          ψ.1.1 := by
      simpa [X] using Section1.toConjClassFunction_ofConjClassFunction ψ.1.1
    have htoConj :
        Section1.toConjClassFunction (Section1.conjugateOnNormal K X g)
            (isClassFunction_of_irreducibleCharacterOnGroup_pf45
              (isIrreducibleCharacterOnGroup_conjugateOnNormal_pf45 K hXirr g)) =
          Section1.toConjClassFunction X
            (isClassFunction_of_irreducibleCharacterOnGroup_pf45 hXirr) := by
      calc
        Section1.toConjClassFunction (Section1.conjugateOnNormal K X g)
            (isClassFunction_of_irreducibleCharacterOnGroup_pf45
              (isIrreducibleCharacterOnGroup_conjugateOnNormal_pf45 K hXirr g)) =
            classFunctionConjLinearEquiv_pf45 K g⁻¹
              (Section1.toConjClassFunction X
                (isClassFunction_of_irreducibleCharacterOnGroup_pf45 hXirr)) := by
              exact
                (classFunctionConjLinearEquiv_toConjClassFunction_conjugateOnNormal_pf45
                  (K := K) (X := X) hXirr (g := g)).symm
        _ = classFunctionConjLinearEquiv_pf45 K g⁻¹ ψ.1.1 := by
              rw [htoX]
        _ = ψ.1.1 := hψfix
        _ = Section1.toConjClassFunction X
              (isClassFunction_of_irreducibleCharacterOnGroup_pf45 hXirr) := htoX.symm
    ext x
    have happ := congrFun htoConj (ConjClasses.mk x)
    simpa [Section1.toConjClassFunction_apply] using happ
  · intro X
    apply Subtype.ext
    exact ofConjClassFunction_toConjClassFunction_pf45 X.1
      (isClassFunction_of_irreducibleCharacterOnGroup_pf45 X.2.1)
  · intro ψ
    apply Subtype.ext
    apply Subtype.ext
    simpa using Section1.toConjClassFunction_ofConjClassFunction ψ.1.1

private theorem natCard_set_eq_ncard_pf45
    {α : Type*} [Finite α] (s : Set α) :
    Nat.card s = s.ncard := by
  classical
  simpa using (Set.ncard_coe (s := s))

private theorem fixed_irreducible_natCard_eq_fixed_conjClasses_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L) :
    Nat.card {X : ClassFunction K |
        Section1.IsIrreducibleCharacterOnGroup X ∧
          Section1.conjugateOnNormal K X g = X} =
      Nat.card (Function.fixedPoints (conjClassesConjPerm_pf45 K g)) := by
  classical
  rcases Theory.Character.irreducible_characters_form_basis (G := K) with
    ⟨ι, hι, χ, hχ, _b, _hb⟩
  let : Fintype ι := hι
  let f :
      ι →
        {χ : Theory.Character.ConjClassFunction K //
          Theory.Character.IsIrreducibleConjCharacter χ} :=
    fun i => ⟨χ i, hχ.1 i⟩
  have hf_bij : Function.Bijective f := by
    constructor
    · intro i j hij
      apply hχ.2.2
      exact congrArg Subtype.val hij
    · intro ψ
      rcases hχ.2.1 ψ.1 ψ.2 with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hi
  let e :
      ι ≃
        {χ : Theory.Character.ConjClassFunction K //
          Theory.Character.IsIrreducibleConjCharacter χ} :=
    Equiv.ofBijective f hf_bij
  let : Fintype
      {χ : Theory.Character.ConjClassFunction K //
        Theory.Character.IsIrreducibleConjCharacter χ} :=
    Fintype.ofEquiv ι e
  have htrace_irred :=
    trace_classFunctionConjLinearEquiv_eq_fixed_irreducibles_pf45 K g⁻¹
  have htrace_conj :=
    trace_classFunctionConjLinearEquiv_eq_fixed_conjClasses_pf45 K g⁻¹
  have hfix_conj_inv :
      (Function.fixedPoints (conjClassesConjPerm_pf45 K g⁻¹)).ncard =
        (Function.fixedPoints (conjClassesConjPerm_pf45 K g)).ncard := by
    have hperm :
        conjClassesConjPerm_pf45 K g⁻¹ = (conjClassesConjPerm_pf45 K g)⁻¹ := by
      apply Equiv.ext
      intro c
      rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
      rw [conjClassesConjPerm_mk_pf45]
      symm
      simpa using (conjClassesConjPerm_symm_inv_mk_pf45 K g⁻¹ x)
    rw [hperm]
    exact fixedPoints_perm_inv_ncard_pf45 (conjClassesConjPerm_pf45 K g)
  have hcast :
      ((Nat.card {X : ClassFunction K |
          Section1.IsIrreducibleCharacterOnGroup X ∧
            Section1.conjugateOnNormal K X g = X}) : ℂ) =
        ((Nat.card (Function.fixedPoints (conjClassesConjPerm_pf45 K g))) : ℂ) := by
    let : Finite
        {χ : Theory.Character.ConjClassFunction K //
          Theory.Character.IsIrreducibleConjCharacter χ} :=
      Finite.of_fintype
        {χ : Theory.Character.ConjClassFunction K //
          Theory.Character.IsIrreducibleConjCharacter χ}
    calc
      ((Nat.card {X : ClassFunction K |
          Section1.IsIrreducibleCharacterOnGroup X ∧
            Section1.conjugateOnNormal K X g = X}) : ℂ) =
          ((Nat.card
            (Function.fixedPoints
              (irreducibleConjClassFunctionPerm_pf45 K g⁻¹))) : ℂ) := by
            rw [fixed_irreducible_natCard_eq_fixed_conjClassFunctions_pf45 K g]
      _ = ((Function.fixedPoints
              (irreducibleConjClassFunctionPerm_pf45 K g⁻¹)).ncard : ℂ) := by
            rw [natCard_set_eq_ncard_pf45]
      _ = LinearMap.trace ℂ (ConjClasses K → ℂ)
            (classFunctionConjLinearEquiv_pf45 K g⁻¹).toLinearMap := by
            exact htrace_irred.symm
      _ = ((Function.fixedPoints (conjClassesConjPerm_pf45 K g⁻¹)).ncard : ℂ) :=
            htrace_conj
      _ = ((Function.fixedPoints (conjClassesConjPerm_pf45 K g)).ncard : ℂ) := by
            rw [hfix_conj_inv]
      _ = ((Nat.card (Function.fixedPoints (conjClassesConjPerm_pf45 K g))) : ℂ) := by
            rw [natCard_set_eq_ncard_pf45]
  exact_mod_cast hcast


private theorem mem_fixedPoints_conjClassesConjPerm_mk_iff_pf45
    {L : Type u} [Group L]
    (K : Subgroup L) [K.Normal] (g : L) (x : K) :
    ConjClasses.mk x ∈ Function.fixedPoints (conjClassesConjPerm_pf45 K g) ↔
      IsConj ((normalSubgroupConjMulEquiv_pf45 K g) x) x := by
  rw [Function.mem_fixedPoints_iff, conjClassesConjPerm_mk_pf45,
    ConjClasses.mk_eq_mk_iff_isConj]

private theorem fixed_conjClass_exists_conjugator_pf45
    {L : Type u} [Group L]
    (K : Subgroup L) [K.Normal] (g : L)
    {c : ConjClasses K}
    (hc : c ∈ Function.fixedPoints (conjClassesConjPerm_pf45 K g)) :
    ∃ x : K, ConjClasses.mk x = c ∧
      ∃ y : K, y * ((normalSubgroupConjMulEquiv_pf45 K g) x) * y⁻¹ = x := by
  rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
  have hx :
      IsConj ((normalSubgroupConjMulEquiv_pf45 K g) x) x :=
    (mem_fixedPoints_conjClassesConjPerm_mk_iff_pf45 K g x).1 hc
  rcases isConj_iff.mp hx with ⟨y, hy⟩
  exact ⟨x, rfl, y, hy⟩

private theorem fixed_conjClasses_card_le_centralizerIn_of_representatives_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L)
    (hrep :
      ∀ c : ConjClasses K,
        c ∈ Function.fixedPoints (conjClassesConjPerm_pf45 K g) →
          ∃ x : K, ConjClasses.mk x = c ∧ (x : L) ∈ Section2.centralizerIn K g) :
    Nat.card (Function.fixedPoints (conjClassesConjPerm_pf45 K g)) ≤
      Nat.card (Section2.centralizerIn K g) := by
  classical
  choose rep hrep_mk hrep_cent using hrep
  let f : Function.fixedPoints (conjClassesConjPerm_pf45 K g) →
      Section2.centralizerIn K g :=
    fun c => ⟨(rep c c.property : L), hrep_cent c c.property⟩
  have hf_inj : Function.Injective f := by
    intro c d hcd
    apply Subtype.ext
    calc
      (c : ConjClasses K) = ConjClasses.mk (rep c c.property) := by
        exact (hrep_mk c c.property).symm
      _ = ConjClasses.mk (rep d d.property) := by
        have hrep_eq : rep c c.property = rep d d.property := by
          apply Subtype.ext
          exact congrArg (fun z : Section2.centralizerIn K g => (z : L)) hcd
        exact congrArg ConjClasses.mk hrep_eq
       _ = (d : ConjClasses K) := hrep_mk d d.property
  exact Nat.card_le_card_of_injective f hf_inj

private theorem mem_elementCentralizer_commute_pf45
    {L : Type u} [Group L] {g c : L}
    (hc : c ∈ Section2.elementCentralizer g) :
    g * c = c * g := by
  unfold Section2.elementCentralizer at hc
  rw [Subgroup.mem_centralizer_iff] at hc
  exact hc g (by simp)

private theorem normalizesSet_subgroup_of_normal_pf45
    {L : Type u} [Group L]
    (K : Subgroup L) [K.Normal] (g : L) :
    Section2.normalizesSet (K : Set L) g := by
  intro x
  constructor
  · intro hx
    have hx' : g⁻¹ * (g * x * g⁻¹) * g ∈ K := by
      simpa [mul_assoc] using
        (show K.Normal from inferInstance).conj_mem (g * x * g⁻¹) hx g⁻¹
    simpa [Section2.conjBy, mul_assoc] using hx'
  · intro hx
    simpa [Section2.conjBy] using
      (show K.Normal from inferInstance).conj_mem x hx g

private theorem exists_multiple_card_pow_eq_self_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) (g : L)
    (hcop : Nat.Coprime (orderOf g) (Nat.card K)) :
    ∃ n : ℕ, Nat.card K ∣ n ∧ g ^ n = g := by
  rcases exists_pow_eq_self_of_coprime (x := g) (n := Nat.card K) hcop.symm with
    ⟨m, hm⟩
  refine ⟨Nat.card K * m, ⟨m, rfl⟩, ?_⟩
  simpa [pow_mul] using hm

private theorem fixed_conjClass_exists_centralizing_rep_of_coprime_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L)
    (hcop : Nat.Coprime (orderOf g) (Nat.card K))
    {c : ConjClasses K}
    (hc : c ∈ Function.fixedPoints (conjClassesConjPerm_pf45 K g)) :
    ∃ x : K, ConjClasses.mk x = c ∧ (x : L) ∈ Section2.centralizerIn K g := by
  rcases fixed_conjClass_exists_conjugator_pf45 K g hc with ⟨x, hxc, y, hy⟩
  have hyL : (y : L) * (g * (x : L) * g⁻¹) * (y : L)⁻¹ = (x : L) := by
    simpa [normalSubgroupConjMulEquiv_pf45, mul_assoc] using
      congrArg (fun z : K => (z : L)) hy
  have hygx_conj : ((y : L) * g) * (x : L) * (((y : L) * g)⁻¹) = (x : L) := by
    simpa [mul_assoc] using hyL
  have hygx_comm : ((y : L) * g) * (x : L) = (x : L) * ((y : L) * g) := by
    calc
      ((y : L) * g) * (x : L) =
          ((((y : L) * g) * (x : L) * (((y : L) * g)⁻¹)) * ((y : L) * g)) := by
            simp [mul_assoc]
      _ = (x : L) * ((y : L) * g) := by rw [hygx_conj]
  rcases Section2.proposition_2_1 g K
      (normalizesSet_subgroup_of_normal_pf45 K g) hcop with
    ⟨reps, _hcard, hreps, _hdisj, hcover⟩
  have hygCoset : (y : L) * g ∈ Section2.subgroupCosetByElement K g := by
    exact ⟨(y : L), y.2, rfl⟩
  have hygPiece :
      (y : L) * g ∈ {z | ∃ r ∈ reps, z ∈ Section2.conjugateCosetPiece K g r} := by
    simpa [hcover] using hygCoset
  rcases hygPiece with ⟨r, hr, hpiece⟩
  have hrK : r ∈ K := hreps r hr
  rcases hpiece with ⟨s, hs, hsEq⟩
  rcases hs with ⟨u, huCent, rfl⟩
  have hugEq : u * g = r⁻¹ * ((y : L) * g) * r := by
    simpa [Section2.conjBy, mul_assoc] using
      congrArg (fun t : L => r⁻¹ * t * r) hsEq.symm
  let xr : K := ⟨r⁻¹ * (x : L) * r, by
    simpa [mul_assoc] using
      (show K.Normal from inferInstance).conj_mem (x : L) x.2 r⁻¹⟩
  have hxr_mk : ConjClasses.mk xr = c := by
    calc
      ConjClasses.mk xr = ConjClasses.mk x := by
        apply ConjClasses.mk_eq_mk_iff_isConj.2
        rw [isConj_iff]
        refine ⟨⟨r, hrK⟩, ?_⟩
        apply Subtype.ext
        simp [xr, mul_assoc]
      _ = c := hxc
  have hxr_comm_ug : Commute (xr : L) (u * g) := by
    change (xr : L) * (u * g) = (u * g) * (xr : L)
    calc
      (xr : L) * (u * g)
          = (r⁻¹ * (x : L) * r) * (r⁻¹ * ((y : L) * g) * r) := by
              rw [hugEq]
      _ = r⁻¹ * ((x : L) * ((y : L) * g)) * r := by simp [mul_assoc]
      _ = r⁻¹ * (((y : L) * g) * (x : L)) * r := by rw [hygx_comm]
      _ = (r⁻¹ * ((y : L) * g) * r) * (r⁻¹ * (x : L) * r) := by simp [mul_assoc]
      _ = (u * g) * (xr : L) := by rw [← hugEq]
  rcases exists_multiple_card_pow_eq_self_pf45 K g hcop with ⟨n, hnK, hgn⟩
  have huK : u ∈ K := (Subgroup.mem_inf.mp huCent).1
  have huPow : u ^ n = 1 := by
    rcases hnK with ⟨m, rfl⟩
    have hu_sub : (⟨u, huK⟩ : K) ^ Nat.card K = 1 := pow_card_eq_one'
    have hu_card : u ^ Nat.card K = 1 := by
      exact Subtype.ext_iff.mp hu_sub
    rw [pow_mul, hu_card, one_pow]
  have huComm : Commute u g := by
    exact (mem_elementCentralizer_commute_pf45 ((Subgroup.mem_inf.mp huCent).2)).symm
  have hugPow : (u * g) ^ n = g := by
    calc
      (u * g) ^ n = u ^ n * g ^ n := huComm.mul_pow n
      _ = 1 * g := by rw [huPow, hgn]
      _ = g := by simp
  have hxr_comm_g : Commute (xr : L) g := by
    simpa [hugPow] using hxr_comm_ug.pow_right n
  refine ⟨xr, hxr_mk, ?_⟩
  refine Subgroup.mem_inf.mpr ⟨xr.2, ?_⟩
  unfold Section2.elementCentralizer
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  exact hxr_comm_g.symm.eq

private theorem fixed_irreducible_card_le_centralizerIn_source_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L) [K.Normal]
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    {g : L} (hgW1 : g ∈ W1) (_hg1 : g ≠ 1) :
    Nat.card {X : ClassFunction K |
        Section1.IsIrreducibleCharacterOnGroup X ∧
          Section1.conjugateOnNormal K X g = X} ≤
      Nat.card (Section2.centralizerIn K g) := by
  rw [fixed_irreducible_natCard_eq_fixed_conjClasses_pf45 K g]
  apply fixed_conjClasses_card_le_centralizerIn_of_representatives_pf45
  intro c hc
  have hcopW1K : Nat.Coprime (Nat.card W1) (Nat.card K) :=
    natCard_W1_coprime_natCard_K_of_hypothesis_4_2_pf45 h42
  have hcopgK : Nat.Coprime (orderOf g) (Nat.card K) :=
    Nat.Coprime.of_dvd_left (Subgroup.orderOf_dvd_natCard W1 hgW1) hcopW1K
  exact fixed_conjClass_exists_centralizing_rep_of_coprime_pf45 K g hcopgK hc

public theorem fixed_irreducible_card_le_centralizerIn_of_coprime_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L)
    (hcop : Nat.Coprime (orderOf g) (Nat.card K)) :
    Nat.card {X : ClassFunction K |
        Section1.IsIrreducibleCharacterOnGroup X ∧
          Section1.conjugateOnNormal K X g = X} ≤
      Nat.card (Section2.centralizerIn K g) := by
  rw [fixed_irreducible_natCard_eq_fixed_conjClasses_pf45 K g]
  apply fixed_conjClasses_card_le_centralizerIn_of_representatives_pf45
  intro c hc
  exact fixed_conjClass_exists_centralizing_rep_of_coprime_pf45 K g hcop hc

public theorem fixed_irreducible_subsingleton_of_card_le_one_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L)
    (hle :
      Nat.card {X : ClassFunction K |
          Section1.IsIrreducibleCharacterOnGroup X ∧
            Section1.conjugateOnNormal K X g = X} ≤ 1) :
    Subsingleton {X : ClassFunction K |
        Section1.IsIrreducibleCharacterOnGroup X ∧
          Section1.conjugateOnNormal K X g = X} := by
  have hfinite :
      ({X : ClassFunction K |
          Section1.IsIrreducibleCharacterOnGroup X ∧
            Section1.conjugateOnNormal K X g = X} :
        Set (ClassFunction K)).Finite :=
    (irreducibleCharacterOnGroup_set_finite_pf45 (G := K)).subset (by
      intro X hX
      exact hX.1)
  let : Finite {X : ClassFunction K |
      Section1.IsIrreducibleCharacterOnGroup X ∧
        Section1.conjugateOnNormal K X g = X} := hfinite
  exact (Finite.card_le_one_iff_subsingleton
    (α := {X : ClassFunction K |
      Section1.IsIrreducibleCharacterOnGroup X ∧
        Section1.conjugateOnNormal K X g = X})).1 hle

private theorem centralizerIn_K_eq_W2_of_hypothesis_4_2_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    {g : L} (hgW1 : g ∈ W1) (hg1 : g ≠ 1) :
    Section2.centralizerIn K g = W2 := by
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      hcent, _hW1, _hW2, _hDirect, _hodd⟩
  exact hcent ⟨g, hgW1⟩ (by
    intro hgsub
    exact hg1 (Subtype.ext_iff.mp hgsub))

private theorem fixed_irreducible_card_le_natCard_W2_source_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L) [K.Normal]
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    {g : L} (hgW1 : g ∈ W1) (hg1 : g ≠ 1) :
    Nat.card {X : ClassFunction K |
        Section1.IsIrreducibleCharacterOnGroup X ∧
          Section1.conjugateOnNormal K X g = X} ≤
      Nat.card W2 := by
  have hcentg : Section2.centralizerIn K g = W2 :=
    centralizerIn_K_eq_W2_of_hypothesis_4_2_pf45 K W1 W2 W h42 hgW1 hg1
  simpa [hcentg] using
    fixed_irreducible_card_le_centralizerIn_source_pf45
      K W1 W2 W h42 hgW1 hg1

private theorem fixed_irreducible_card_le_natCard_W2_of_W1_fixed_core_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L) [K.Normal]
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (_i0 : I) (_j0 : J)
    (_ω : I → J → ClassFunction W)
    (_σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (_piChar : I → J → ClassFunction L)
    (_deltaSign : J → ℂ)
    (_xChar : J → ClassFunction K)
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    {g : L} (hgW1 : g ∈ W1) (hg1 : g ≠ 1) :
    Nat.card {X : ClassFunction K |
        Section1.IsIrreducibleCharacterOnGroup X ∧
          Section1.conjugateOnNormal K X g = X} ≤ Nat.card W2 := by
  have hcentg : Section2.centralizerIn K g = W2 :=
    centralizerIn_K_eq_W2_of_hypothesis_4_2_pf45 K W1 W2 W h42 hgW1 hg1
  simpa [hcentg] using
    fixed_irreducible_card_le_natCard_W2_source_pf45
      K W1 W2 W h42 hgW1 hg1

public theorem xChar_injective_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    {W1 W2 W : Subgroup L}
    (i0 : I)
    (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (deltaSign : J → ℂ)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω) :
    Function.Injective xChar := by
  rcases h45a with ⟨hres, hirrX, hindX⟩
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigma⟩
  intro j k hEq
  by_contra hjk
  have hsumj :
      (piColumn piChar j : ClassFunction L) = fun g => ∑ i : I, piChar i j g := by
    ext g
    simp [piColumn]
  have hsumk :
      (piColumn piChar k : ClassFunction L) = fun g => ∑ i : I, piChar i k g := by
    ext g
    simp [piColumn]
  have hzero :
      Section1.scalarProduct L (piColumn piChar j) (piColumn piChar k) = 0 := by
    rw [hsumj, Section1.scalarProduct_fintype_sum_left]
    refine Finset.sum_eq_zero ?_
    intro i _hi
    have hinner_i :
        Section1.scalarProduct L (piChar i j) (piColumn piChar k) = 0 := by
      rw [hsumk, Section1.scalarProduct_fintype_sum_right]
      refine Finset.sum_eq_zero ?_
      intro p _hp
      have hneq : piChar i j ≠ piChar p k := by
        refine hdistinct (i, j) (p, k) ?_
        intro hpair
        exact hjk (congrArg Prod.snd hpair)
      exact scalarProduct_irreducible_ne_pf45 (hirr i j) (hirr p k) hneq
    exact hinner_i
  have hpiClass : Section1.IsClassFunction (piColumn piChar k) := by
    intro x g
    rw [hsumk]
    refine Finset.sum_congr rfl ?_
    intro c _hc
    exact isClassFunction_of_irreducibleCharacterOnGroup_pf45 (hirr c k) x g
  have hresCol :
      Section1.subgroupRestriction K (piColumn piChar k) =
        (Fintype.card I : ℂ) • xChar k := by
    ext t
    calc
      Section1.subgroupRestriction K (piColumn piChar k) t = ∑ i : I, piChar i k t := by
        simp [hsumk, Section1.subgroupRestriction]
      _ = ∑ _i : I, xChar k t := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simpa [Section1.subgroupRestriction] using congrFun (hres i k) t
      _ = (Fintype.card I : ℂ) * xChar k t := by
        simp [Finset.sum_const]
      _ = ((Fintype.card I : ℂ) • xChar k) t := by
        simp
  have hcardI_ne : (Fintype.card I : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i0⟩).ne'
  have hnonzero :
      Section1.scalarProduct L (piColumn piChar j) (piColumn piChar k) ≠ 0 := by
    rw [← hindX j]
    rw [Section1.scalarProduct_inducedCF_left K (xChar j) (piColumn piChar k) hpiClass]
    rw [hresCol, hEq, Section1.scalarProduct_smul_right]
    have hself : Section1.scalarProduct K (xChar j) (xChar j) = 1 :=
      scalarProduct_irreducible_self_pf45 (hirrX j)
    have hselfk : Section1.scalarProduct K (xChar k) (xChar k) = 1 := by
      simpa [hEq] using hself
    rw [hselfk]
    simp [hcardI_ne]
  exact hnonzero hzero

public theorem natCard_range_xChar_eq_natCard_W2_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    {W1 W2 W : Subgroup L}
    (i0 : I)
    (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (deltaSign : J → ℂ)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω) :
    Nat.card (Set.range xChar) = Nat.card W2 := by
  have hInj :
      Function.Injective xChar :=
    xChar_injective_pf45 K piChar xChar h45a i0 j0 ω σ deltaSign hω h43b
  calc
    Nat.card (Set.range xChar) = Nat.card J := by
      exact Nat.card_congr (Equiv.ofInjective xChar hInj).symm
    _ = Nat.card W2 := by
      rw [Nat.card_eq_fintype_card, hω.card_right]

private theorem fixed_irreducible_card_le_range_xChar_of_W1_fixed_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L) [K.Normal]
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (xChar : J → ClassFunction K)
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    {g : L} (hgW1 : g ∈ W1) (hg1 : g ≠ 1) :
    Nat.card {X : ClassFunction K |
        Section1.IsIrreducibleCharacterOnGroup X ∧
          Section1.conjugateOnNormal K X g = X} ≤ Nat.card (Set.range xChar) := by
  have hfixed_le_W2 :
      Nat.card {X : ClassFunction K |
          Section1.IsIrreducibleCharacterOnGroup X ∧
            Section1.conjugateOnNormal K X g = X} ≤ Nat.card W2 :=
    fixed_irreducible_card_le_natCard_W2_of_W1_fixed_core_pf45
      K W1 W2 W i0 j0 ω σ piChar deltaSign xChar h42
      hgW1 hg1
  have hrange :
      Nat.card (Set.range xChar) = Nat.card W2 :=
    natCard_range_xChar_eq_natCard_W2_pf45
      K piChar xChar h45a i0 j0 ω σ deltaSign hω hB
  rw [hrange]
  exact hfixed_le_W2

private theorem inertiaSubgroup_eq_of_no_nontrivial_W1_fixed_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L) [K.Normal]
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    {X : ClassFunction K}
    (hXclass : Section1.IsClassFunction X)
    (hnoFix :
      ∀ g : L, g ∈ W1 → g ≠ 1 →
        Section1.conjugateOnNormal K X g ≠ X) :
    Section1.inertiaSubgroup K X = K := by
  rcases h42 with ⟨hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, _hDirect, _hodd⟩
  have hKleI :
      K ≤ Section1.inertiaSubgroup K X := by
    intro x hx
    change Section1.conjugateOnNormal K X x = X
    funext h
    have hclass := hXclass ⟨x, hx⟩ h
    change X ⟨x * (h : L) * x⁻¹, _⟩ = X h at hclass
    exact hclass
  apply le_antisymm
  · intro g hgI
    rcases hsemi.mul_surjective g (by trivial) with ⟨k, hkK, w, hwW1, hkw⟩
    have hkI : k ∈ Section1.inertiaSubgroup K X := hKleI hkK
    have hwI : w ∈ Section1.inertiaSubgroup K X := by
      have :
          k⁻¹ * g ∈ Section1.inertiaSubgroup K X :=
        (Section1.inertiaSubgroup K X).mul_mem
          ((Section1.inertiaSubgroup K X).inv_mem hkI) hgI
      simpa [hkw, mul_assoc] using this
    have hw1 : w = 1 := by
      by_contra hwne
      have hfixw : Section1.conjugateOnNormal K X w = X := by
        simpa [Section1.inertiaSubgroup] using hwI
      exact hnoFix w hwW1 hwne hfixw
    have hgk : g = k := by
      calc
        g = k * w := hkw
        _ = k := by simp [hw1]
    simpa [hgk] using hkK
  · exact hKleI

private theorem fixed_irreducible_mem_range_xChar_of_W1_fixed_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L) [K.Normal]
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (xChar : J → ClassFunction K)
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    {X : ClassFunction K}
    (hX : Section1.IsIrreducibleCharacterOnGroup X)
    {g : L} (hgW1 : g ∈ W1) (hg1 : g ≠ 1)
    (hfix : Section1.conjugateOnNormal K X g = X) :
    X ∈ Set.range xChar := by
  classical
  have hfixed_range :
      Set.range xChar ⊆
        {Y : ClassFunction K |
          Section1.IsIrreducibleCharacterOnGroup Y ∧
            Section1.conjugateOnNormal K Y g = Y} := by
    intro Y hY
    rcases hY with ⟨j, rfl⟩
    exact ⟨h45a.2.1 j,
      xChar_fixed_by_conjugateOnNormal_pf45
        K W1 W2 W i0 j0 ω σ piChar deltaSign xChar hω hB h45a j g⟩
  have hfixedFinite :
      ({Y : ClassFunction K |
        Section1.IsIrreducibleCharacterOnGroup Y ∧
          Section1.conjugateOnNormal K Y g = Y} : Set (ClassFunction K)).Finite := by
    exact (irreducibleCharacterOnGroup_set_finite_pf45 (G := K)).subset (by
      intro Y hY
      exact hY.1)
  have hfixedCard :=
    fixed_irreducible_card_le_range_xChar_of_W1_fixed_pf45
      K W1 W2 W i0 j0 ω σ piChar deltaSign xChar h42 hω hB h45a
      hgW1 hg1
  exact
    irreducible_fixed_mem_range_of_card_bound_pf45 K xChar
      hfixedFinite hfixedCard hfixed_range hX hfix

private theorem induced_irreducible_of_not_mem_range_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (xChar : J → ClassFunction K)
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (_hC : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (X : ClassFunction K)
    (hX : Section1.IsIrreducibleCharacterOnGroup X)
    (hXnot : X ∉ Set.range xChar) :
    Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K X) := by
  have hKnorm : K.Normal := normal_K_of_hypothesis_4_2_pf45 h42
  let : K.Normal := hKnorm
  rcases hX with ⟨n, ρ, hρirr, rfl⟩
  have hXclass : Section1.IsClassFunction ρ.character :=
    isClassFunction_of_irreducibleCharacterOnGroup_pf45 ⟨n, ρ, hρirr, rfl⟩
  have hnoFix :
      ∀ g : L, g ∈ W1 → g ≠ 1 →
        Section1.conjugateOnNormal K ρ.character g ≠ ρ.character := by
    intro g hgW1 hg1 hfix
    exact hXnot
      (fixed_irreducible_mem_range_xChar_of_W1_fixed_pf45
        K W1 W2 W i0 j0 ω σ piChar deltaSign xChar
        h42 hω hB h45a ⟨n, ρ, hρirr, rfl⟩ hgW1 hg1 hfix)
  have hIeq :
      Section1.inertiaSubgroup K ρ.character = K :=
    inertiaSubgroup_eq_of_no_nontrivial_W1_fixed_pf45
      K W1 W2 W h42 hXclass hnoFix
  have hnorm :
      Section1.scalarProduct L (Section1.inducedCF K ρ.character)
        (Section1.inducedCF K ρ.character) = 1 := by
    exact
      Section1.proposition_1_5_b_norm_one_rep_orbit_relIndex_canonical
        K ρ hρirr (by simp [hIeq])
  have : FiniteDimensional ℂ (Representation.IndV K.subtype ρ) :=
    Theory.Representation.finiteDimensional_ind K ρ
  have hIndIrr :
      Representation.IsIrreducible (Representation.ind K.subtype ρ) := by
    apply (Theory.Character.irreducible_iff_character_norm_one
      (ρ := Representation.ind K.subtype ρ)).2
    have hIndClass : Section1.IsClassFunction (Representation.ind K.subtype ρ).character := by
      intro x g
      simpa [mul_assoc] using
        Representation.char_conj (ρ := Representation.ind K.subtype ρ) g x
    have htoeq :
        Section1.toConjClassFunction (Representation.ind K.subtype ρ).character hIndClass =
          Theory.Character.characterClassFunction (Representation.ind K.subtype ρ) := by
      apply Section1.toConjClassFunction_eq_of_apply
      intro g
      rfl
    rw [← htoeq, Section1.classFunctionInner_toConjClassFunction,
      ← Section1.inducedCF_eq_representation_character K ρ]
    exact hnorm
  refine ⟨Module.finrank ℂ (Representation.IndV K.subtype ρ),
    standardizeRepresentation_pf45 (Representation.ind K.subtype ρ), ?_, ?_⟩
  · exact standardizeRepresentation_irreducible_pf45
      (Representation.ind K.subtype ρ) hIndIrr
  · calc
      Section1.inducedCF K ρ.character =
          (Representation.ind K.subtype ρ).character := by
            exact Section1.inducedCF_eq_representation_character K ρ
      _ = (standardizeRepresentation_pf45 (Representation.ind K.subtype ρ)).character := by
            ext g
            symm
            exact standardizeRepresentation_character_pf45
              (Representation.ind K.subtype ρ) g

public theorem theorem_4_5_b
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (xChar : J → ClassFunction K)
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (hC : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h45a : theorem_4_5_a_statement K piChar xChar) :
theorem_4_5_b_statement K piChar xChar := by
  have hKnorm : K.Normal := normal_K_of_hypothesis_4_2_pf45 h42
  let : K.Normal := hKnorm
  have h45a' := h45a
  have hB' := hB
  rcases h45a with ⟨hres, hirrX, hindX⟩
  rcases hB with ⟨_hσmap, _hsign, hirr, _hdistinct, _hind, _hSigma⟩
  refine ⟨?_, ?_⟩
  · intro X hX hXnot
    refine ⟨induced_irreducible_of_not_mem_range_pf45
      K W1 W2 W i0 j0 ω σ piChar deltaSign xChar h42 hω hB' hC h45a' X hX hXnot, ?_⟩
    intro hmem
    rcases hmem with ⟨⟨i, j⟩, hEq⟩
    have hpiClass : Section1.IsClassFunction (piChar i j) :=
      isClassFunction_of_irreducibleCharacterOnGroup_pf45 (hirr i j)
    have hzero :
        Section1.scalarProduct L (Section1.inducedCF K X) (piChar i j) = 0 := by
      rw [Section1.scalarProduct_inducedCF_left K X (piChar i j) hpiClass, hres i j]
      have hneqX : X ≠ xChar j := by
        intro hEqX
        exact hXnot ⟨j, hEqX.symm⟩
      exact scalarProduct_irreducible_ne_pf45 hX (hirrX j) hneqX
    have hone :
        Section1.scalarProduct L (Section1.inducedCF K X) (piChar i j) = 1 := by
      simpa [hEq] using
        scalarProduct_irreducible_self_pf45
          (induced_irreducible_of_not_mem_range_pf45
            K W1 W2 W i0 j0 ω σ piChar deltaSign xChar h42 hω hB' hC h45a' X hX hXnot)
    simp [hone] at hzero
  · intro ψ hψ
    exact theorem_4_5_b_exhaustion_of_first_part_pf45
      K piChar xChar h45a' i0 j0 ω σ deltaSign hω hB'
      (fun X hX hXnot =>
        induced_irreducible_of_not_mem_range_pf45
          K W1 W2 W i0 j0 ω σ piChar deltaSign xChar h42 hω hB' hC h45a' X hX hXnot)
      ψ hψ

public theorem theorem_4_5
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : Section4.theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (hC : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω) :
    theorem_4_5_statement K piChar := by
  rcases theorem_4_5_a K W1 W2 W i0 j0 ω σ piChar deltaSign h42 hω hB hC with
    ⟨xChar, h45a⟩
  refine ⟨xChar, h45a, ?_⟩
  exact theorem_4_5_b
    K W1 W2 W i0 j0 ω σ piChar deltaSign xChar h42 hω hB hC h45a

public theorem theorem_4_7
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A) :
    theorem_4_7_statement K H A := by
  intro X hX hXker
  refine ⟨?_, ?_⟩
  · exact supportedOn_irreducible_of_not_subgroupInKernel_pf45
      K W1 W2 W H A h46 hX hXker
  · exact supportedOn_induced_irreducible_of_not_subgroupInKernel_pf45
      K W1 W2 W H A h46 hX hXker

public theorem theorem_4_7_nonbase_column
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h47 : theorem_4_7_statement K H A) :
    theorem_4_7_nonbase_column_statement K H A j0 piChar xChar := by
  intro j hj0
  exact theorem_4_7_nonbase_column_data_pf45
    K W1 W2 W H A i0 j0 ω σ piChar xChar deltaSign
    h46 h45a hω h43b h43c h47 j hj0

public theorem theorem_4_7_full
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω) :
    theorem_4_7_full_statement K H A j0 piChar xChar := by
  have h47 : theorem_4_7_statement K H A :=
    theorem_4_7 K W1 W2 W H A h46
  exact ⟨h47,
    theorem_4_7_nonbase_column
      K W1 W2 W H A i0 j0 ω σ piChar xChar deltaSign
      h46 h45a hω h43b h43c h47⟩

private theorem sigma_sub_eq_signed_baseRow_sub_pf45
    {L : Type u} [Group L] [Finite L]
    (W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σL : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h43d : Section4.theorem_4_3_d_statement W1 I J piChar deltaSign)
    {j k : J}
    (hdeg : Section1.degree (piChar i0 j) = Section1.degree (piChar i0 k)) :
    σL (ω i0 j - ω i0 k) =
      deltaSign j • (piChar i0 j - piChar i0 k) := by
  rcases h43b with ⟨_hσmapL, hsign, _hirr, _hdistinct, _hind, hSigmaL⟩
  have hsignjk : deltaSign j = deltaSign k :=
    deltaSign_eq_of_equal_degree_pf45
      W1 W2 W piChar deltaSign h31 hsign h43d hdeg
  calc
    σL (ω i0 j - ω i0 k) = σL (ω i0 j) - σL (ω i0 k) := by
      rw [LinearMap.map_sub]
    _ = deltaSign j • piChar i0 j - deltaSign k • piChar i0 k := by
      rw [hSigmaL i0 j, hSigmaL i0 k]
    _ = deltaSign j • (piChar i0 j - piChar i0 k) := by
      rw [hsignjk]
      simp [smul_sub]

private theorem baseRow_sub_eq_signed_sigma_sub_pf45
    {L : Type u} [Group L] [Finite L]
    (W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σL : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h43d : Section4.theorem_4_3_d_statement W1 I J piChar deltaSign)
    {j k : J}
    (hdeg : Section1.degree (piChar i0 j) = Section1.degree (piChar i0 k)) :
    piChar i0 j - piChar i0 k =
      deltaSign j • σL (ω i0 j - ω i0 k) := by
  have h43b' := h43b
  rcases h43b with ⟨_hσmapL, hsign, _hirr, _hdistinct, _hind, _hSigmaL⟩
  calc
    piChar i0 j - piChar i0 k =
        (deltaSign j * deltaSign j) • (piChar i0 j - piChar i0 k) := by
          rw [sign_mul_self_eq_one_pf45 (hsign j)]
          simp
    _ = deltaSign j •
          (deltaSign j • (piChar i0 j - piChar i0 k)) := by
            rw [smul_smul]
    _ = deltaSign j • σL (ω i0 j - ω i0 k) := by
          rw [sigma_sub_eq_signed_baseRow_sub_pf45
            W1 W2 W i0 j0 ω σL piChar deltaSign h31 hω h43b' h43d hdeg]

private theorem sigmaL_baseRow_sub_eq_baseRowDiff_on_wMinusW2_pf45
    {L : Type u} [Group L] [Finite L]
    (W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σL : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h43d : Section4.theorem_4_3_d_statement W1 I J piChar deltaSign)
    {j k : J}
    (hdeg : Section1.degree (piChar i0 j) = Section1.degree (piChar i0 k)) :
    ∀ x, ∀ hx : x ∈ ((W : Set L) \ (W2 : Set L)),
      σL (ω i0 j - ω i0 k) x = (ω i0 j - ω i0 k) ⟨x, hx.1⟩ := by
  have h43b' := h43b
  rcases h43b with ⟨_hσmapL, hsign, _hirr, _hdistinct, _hind, _hSigmaL⟩
  have hsignjk : deltaSign j = deltaSign k :=
    deltaSign_eq_of_equal_degree_pf45
      W1 W2 W piChar deltaSign h31 hsign h43d hdeg
  have hbaseSigma :
      σL (ω i0 j - ω i0 k) =
        deltaSign j • (piChar i0 j - piChar i0 k) :=
    sigma_sub_eq_signed_baseRow_sub_pf45
      W1 W2 W i0 j0 ω σL piChar deltaSign h31 hω h43b' h43d hdeg
  intro x hx
  have hbaseX := congrFun hbaseSigma x
  have hpiX :
      (piChar i0 j - piChar i0 k) x =
        deltaSign j * ((ω i0 j - ω i0 k) ⟨x, hx.1⟩) := by
    rw [Pi.sub_apply, h43c.1 i0 j x hx, h43c.1 i0 k x hx, hsignjk]
    simp [Pi.sub_apply, mul_sub]
  calc
    σL (ω i0 j - ω i0 k) x =
        deltaSign j * ((piChar i0 j - piChar i0 k) x) := by
          simpa [Pi.smul_apply] using hbaseX
    _ = deltaSign j * (deltaSign j * ((ω i0 j - ω i0 k) ⟨x, hx.1⟩)) := by
          rw [hpiX]
    _ = (ω i0 j - ω i0 k) ⟨x, hx.1⟩ := by
          rw [← mul_assoc, sign_mul_self_eq_one_pf45 (hsign j)]
          simp

private theorem tau_sigmaL_baseRow_sub_eq_sigma_sub_pf45
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σL : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h43d : Section4.theorem_4_3_d_statement W1 I J piChar deltaSign)
    (hτA0 : tau_agrees_on_a0_extension_statement W2 W A σ τ)
    (h47 : theorem_4_7_statement K H A)
    {j k : J}
    (hj0 : j ≠ j0) (hk0 : k ≠ j0)
    (hdeg : Section1.degree (piChar i0 j) = Section1.degree (piChar i0 k)) :
    τ (σL (ω i0 j - ω i0 k)) =
      σ (ω i0 j) - σ (ω i0 k) := by
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    hypothesis_3_1_of_hypothesis_4_6_pf45 h46
  have h43b' := h43b
  have hbaseSupport :
      Section1.supportedOn
        (piChar i0 j - piChar i0 k) (a0Set W2 W A) :=
    supportedOn_diff_a0_of_equal_degree_pf45
      K W1 W2 W H A i0 j0 ω σL piChar xChar deltaSign
      h46 h45a hω h43b h43c h47 hj0 hk0 hdeg
  have hbaseSigma :
      σL (ω i0 j - ω i0 k) =
        deltaSign j • (piChar i0 j - piChar i0 k) :=
    sigma_sub_eq_signed_baseRow_sub_pf45
      W1 W2 W i0 j0 ω σL piChar deltaSign h31 hω h43b' h43d hdeg
  have hsigmaLSupport :
      Section1.supportedOn
        (σL (ω i0 j - ω i0 k)) (a0Set W2 W A) := by
    rw [hbaseSigma]
    exact supportedOn_smul_pf45 hbaseSupport
  have hagreeOnV :
      ∀ x, ∀ hx : x ∈ ((W : Set L) \ (W2 : Set L)),
        σL (ω i0 j - ω i0 k) x =
          (ω i0 j - ω i0 k) ⟨x, hx.1⟩ :=
    sigmaL_baseRow_sub_eq_baseRowDiff_on_wMinusW2_pf45
      W1 W2 W i0 j0 ω σL piChar deltaSign h31 hω h43b' h43c h43d hdeg
  simpa [Pi.sub_apply] using
    hτA0 (σL (ω i0 j - ω i0 k)) (ω i0 j - ω i0 k) hsigmaLSupport hagreeOnV

private theorem tau_sub_eq_signed_sigma_sub_baseRow_of_equal_degree_pf45
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σL : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h43d : Section4.theorem_4_3_d_statement W1 I J piChar deltaSign)
    (hτA0 : tau_agrees_on_a0_extension_statement W2 W A σ τ)
    (h47 : theorem_4_7_statement K H A)
    {j k : J}
    (hj0 : j ≠ j0) (hk0 : k ≠ j0)
    (hdeg : Section1.degree (piChar i0 j) = Section1.degree (piChar i0 k)) :
    τ (piChar i0 j - piChar i0 k) =
      deltaSign j • (σ (ω i0 j) - σ (ω i0 k)) := by
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    hypothesis_3_1_of_hypothesis_4_6_pf45 h46
  have h43b' := h43b
  rcases h43b with ⟨hσmapL, hsign, _hirr, _hdistinct, _hind, _hSigmaL⟩
  have hsignjk : deltaSign j = deltaSign k :=
    deltaSign_eq_of_equal_degree_pf45
      W1 W2 W piChar deltaSign h31 hsign h43d hdeg
  have hbaseSigma :
      piChar i0 j - piChar i0 k =
        deltaSign j • σL (ω i0 j - ω i0 k) :=
    baseRow_sub_eq_signed_sigma_sub_pf45
      W1 W2 W i0 j0 ω σL piChar deltaSign h31 hω h43b' h43d hdeg
  calc
    τ (piChar i0 j - piChar i0 k) =
        τ (deltaSign j • σL (ω i0 j - ω i0 k)) := by
          rw [hbaseSigma]
    _ = deltaSign j • τ (σL (ω i0 j - ω i0 k)) := by
          rw [LinearMap.map_smul]
    _ = deltaSign j • (σ (ω i0 j) - σ (ω i0 k)) := by
          rw [tau_sigmaL_baseRow_sub_eq_sigma_sub_pf45
            K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ
            h46 h45a hω h43b' h43c h43d hτA0 h47 hj0 hk0 hdeg]

private theorem tau_sub_eq_signed_sigma_sub_of_equal_degree_pf45
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σL : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h43d : Section4.theorem_4_3_d_statement W1 I J piChar deltaSign)
    (hτσ : tau_agrees_on_cyclicTI_induced_statement W1 W2 W σ τ)
    (hτA0 : tau_agrees_on_a0_extension_statement W2 W A σ τ)
    (h47 : theorem_4_7_statement K H A)
    {i : I} {j k : J}
    (hj0 : j ≠ j0) (hk0 : k ≠ j0)
    (hdeg : Section1.degree (piChar i j) = Section1.degree (piChar i k)) :
    τ (piChar i j - piChar i k) =
      deltaSign j • (σ (ω i j) - σ (ω i k)) := by
  have h45a' := h45a
  have h43b' := h43b
  rcases h45a with ⟨hres, _hirrX, _hindX⟩
  rcases h43b with ⟨_hσmap, hsign, _hirr, _hdistinct, _hind, _hSigma⟩
  have hsignjk : deltaSign j = deltaSign k :=
    deltaSign_eq_of_equal_degree_pf45 W1 W2 W piChar deltaSign
      (hypothesis_3_1_of_hypothesis_4_6_pf45 h46) hsign h43d hdeg
  have hdegX : Section1.degree (xChar j) = Section1.degree (xChar k) := by
    have hresij := congrFun (hres i j) 1
    have hresik := congrFun (hres i k) 1
    calc
      Section1.degree (xChar j) = Section1.degree (piChar i j) := by
        simpa [Section1.degree, Section1.subgroupRestriction] using hresij.symm
      _ = Section1.degree (piChar i k) := hdeg
      _ = Section1.degree (xChar k) := by
        simpa [Section1.degree, Section1.subgroupRestriction] using hresik
  have hdegBase : Section1.degree (piChar i0 j) = Section1.degree (piChar i0 k) := by
    have hres0j := congrFun (hres i0 j) 1
    have hres0k := congrFun (hres i0 k) 1
    calc
      Section1.degree (piChar i0 j) = Section1.degree (xChar j) := by
        simpa [Section1.degree, Section1.subgroupRestriction] using hres0j
      _ = Section1.degree (xChar k) := hdegX
      _ = Section1.degree (piChar i0 k) := by
        simpa [Section1.degree, Section1.subgroupRestriction] using hres0k.symm
  have hbase :=
    tau_sub_eq_signed_sigma_sub_baseRow_of_equal_degree_pf45
      K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ
      h46 h45a' hω h43b' h43c h43d hτA0 h47 hj0 hk0 hdegBase
  have h10 := theorem_4_10_formula_pf45
    W1 W2 i0 j0 ω σL σ piChar deltaSign τ hω h43b' hτσ
  have hsub := congrArg₂ HSub.hSub (h10 i j) (h10 i k)
  have hrect :
      τ (deltaSign j • ((piChar i j - piChar i k) - (piChar i0 j - piChar i0 k))) =
        (σ (ω i j) - σ (ω i k)) - (σ (ω i0 j) - σ (ω i0 k)) := by
    have hsub' :
        τ ((deltaSign j • piChar i j - deltaSign j • piChar i0 j - piChar i j0 + piChar i0 j0) -
            (deltaSign k • piChar i k - deltaSign k • piChar i0 k - piChar i j0 + piChar i0 j0)) =
          ((σ (ω i j) - σ (ω i0 j)) - (σ (ω i j0) - σ (ω i0 j0))) -
            ((σ (ω i k) - σ (ω i0 k)) - (σ (ω i j0) - σ (ω i0 j0))) := by
      simpa [LinearMap.map_sub] using hsub
    ext g
    have hsubg := congrFun hsub' g
    rw [← hsignjk] at hsubg
    simp [Pi.smul_apply, sub_eq_add_neg] at hsubg ⊢
    ring_nf at hsubg ⊢
    exact hsubg
  have hdiff :
      τ ((piChar i j - piChar i k) - (piChar i0 j - piChar i0 k)) =
        deltaSign j • ((σ (ω i j) - σ (ω i k)) - (σ (ω i0 j) - σ (ω i0 k))) := by
    have hrect' := hrect
    rw [LinearMap.map_smul] at hrect'
    calc
      τ ((piChar i j - piChar i k) - (piChar i0 j - piChar i0 k)) =
          (deltaSign j * deltaSign j) •
            τ ((piChar i j - piChar i k) - (piChar i0 j - piChar i0 k)) := by
              rw [sign_mul_self_eq_one_pf45 (hsign j)]
              simp
      _ = deltaSign j • (deltaSign j •
            τ ((piChar i j - piChar i k) - (piChar i0 j - piChar i0 k))) := by
              rw [smul_smul]
      _ = deltaSign j • ((σ (ω i j) - σ (ω i k)) - (σ (ω i0 j) - σ (ω i0 k))) := by
            rw [hrect']
  have hdiff' :
      τ (piChar i j - piChar i k) - τ (piChar i0 j - piChar i0 k) =
        deltaSign j • (σ (ω i j) - σ (ω i k)) -
          deltaSign j • (σ (ω i0 j) - σ (ω i0 k)) := by
    simpa [LinearMap.map_sub, smul_sub] using hdiff
  calc
    τ (piChar i j - piChar i k) =
        (τ (piChar i j - piChar i k) - τ (piChar i0 j - piChar i0 k)) +
          τ (piChar i0 j - piChar i0 k) := by
            ext g
            simp [sub_eq_add_neg]
            ring_nf
    _ =
        (deltaSign j • (σ (ω i j) - σ (ω i k)) -
            deltaSign j • (σ (ω i0 j) - σ (ω i0 k))) +
          τ (piChar i0 j - piChar i0 k) := by
            rw [hdiff']
    _ = deltaSign j • (σ (ω i j) - σ (ω i k)) := by
          rw [hbase]
          ext g
          simp [Pi.smul_apply, sub_eq_add_neg]
          ring_nf

public theorem theorem_4_8
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σL : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h43d : Section4.theorem_4_3_d_statement W1 I J piChar deltaSign)
    (hτσ : tau_agrees_on_cyclicTI_induced_statement W1 W2 W σ τ)
    (hτA0 : tau_agrees_on_a0_extension_statement W2 W A σ τ)
    (h47 : theorem_4_7_statement K H A) :
    theorem_4_8_statement W2 W A j0 ω σ piChar deltaSign τ := by
  have h43b' := h43b
  rcases h43b with ⟨_hσmap, hsign, _hirr, _hdistinct, _hind, _hSigma⟩
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    hypothesis_3_1_of_hypothesis_4_6_pf45 h46
  intro i j k hj0 hk0 hdeg
  refine ⟨?_, ?_, ?_⟩
  · exact supportedOn_diff_a0_of_equal_degree_pf45
      K W1 W2 W H A i0 j0 ω σL piChar xChar deltaSign
      h46 h45a hω h43b' h43c h47 hj0 hk0 hdeg
  · exact deltaSign_eq_of_equal_degree_pf45
      W1 W2 W piChar deltaSign h31 hsign h43d hdeg
  · exact tau_sub_eq_signed_sigma_sub_of_equal_degree_pf45
      K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ
      h46 h45a hω h43b' h43c h43d hτσ hτA0 h47 hj0 hk0 hdeg

private theorem supportedOn_evalCoeff_of_supportedOn_pf45
    {G : Type u} [Group G]
    {J : Type*} [Fintype J]
    (mu : J → ClassFunction G) (A : Set G)
    (hmu : ∀ j, Section1.supportedOn (mu j) A) :
    ∀ v : Section1.CoeffVector J, Section1.supportedOn (Section1.evalCoeff mu v) A := by
  intro v
  rw [Section1.supportedOn_iff]
  intro x hx
  have hmu0 : ∀ j, mu j x = 0 := by
    intro j
    exact (Section1.supportedOn_iff.mp (hmu j)) x hx
  simp [Section1.evalCoeff, hmu0]

private theorem supportedOn_punctured_iff_supportedOn_of_supportedOn_withOne_pf45
    {L : Type u} [Group L]
    (A : Set L)
    (hA : A ⊆ puncturedSet)
    {f : ClassFunction L}
    (hf : Section1.supportedOn f (withOne A)) :
    Section1.supportedOn f puncturedSet ↔ Section1.supportedOn f A := by
  constructor
  · intro hpunct
    rw [Section1.supportedOn_iff] at hpunct hf ⊢
    intro x hxA
    by_cases hx1 : x = 1
    · exact hpunct x (by simp [puncturedSet, hx1])
    · exact hf x (by simp [withOne, hxA, hx1])
  · intro hAon
    rw [Section1.supportedOn_iff] at hAon ⊢
    intro x hxPunct
    have hxNotA : x ∉ A := by
      intro hxA
      exact hxPunct (hA hxA)
    exact hAon x hxNotA

private theorem conjugate_piChar_baseRow_eq_of_conjugate_omega_pf45
    {L : Type u} [Group L] [Finite L]
    (W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    {j j' : J}
    (hbarOmega : Section1.conjugateCharacter (ω i0 j) = ω i0 j') :
    Section1.conjugateCharacter (piChar i0 j) = piChar i0 j' := by
  rcases h43b with ⟨_hσmap, hsign, hirr, _hdistinct, _hind, _hSigma⟩
  rcases Section3.proposition_3_9_a_uniqueness
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h31 hω with
    ⟨χpf, _horth, _hvirt, _hsigned, _h00, _hInd, huniq⟩
  have hbarIrr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.conjugateCharacter (piChar i0 j)) :=
    isIrreducibleCharacterOnGroup_conjugateCharacter_pf45 (hirr i0 j)
  have hbarV :
      ∀ x : L, ∀ hx : x ∈ Section3.cyclicTISet W1 W2 W,
        (deltaSign j • Section1.conjugateCharacter (piChar i0 j)) x =
          ω i0 j' ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
    intro x hx
    have hxWm : x ∈ ((W : Set L) \ (W2 : Set L)) := by
      exact ⟨Section3.cyclicTISet_subset W1 W2 W hx,
        Section3.cyclicTISet_not_mem_right W1 W2 W hx⟩
    have hval := h43c.1 i0 j x hxWm
    have hbarVal := congrFun hbarOmega ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩
    have hδstar : star (deltaSign j) = deltaSign j := by
      rcases hsign j with hδ | hδ <;> simp [hδ]
    have hstarEq :
        star (piChar i0 j x) =
          deltaSign j *
            star (ω i0 j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩) := by
      simpa [hδstar, mul_comm] using congrArg star hval
    change
      deltaSign j * star (piChar i0 j x) =
        ω i0 j' ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩
    calc
      deltaSign j * star (piChar i0 j x) =
          deltaSign j *
            (deltaSign j *
              star (ω i0 j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩)) := by
                rw [hstarEq]
      _ = (deltaSign j * deltaSign j) *
            star (ω i0 j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩) := by
              ring
      _ = star (ω i0 j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩) := by
            rw [sign_mul_self_eq_one_pf45 (hsign j)]
            simp
      _ = ω i0 j' ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
            simpa [Section1.conjugateCharacter] using hbarVal
  have hbarEq :
      deltaSign j • Section1.conjugateCharacter (piChar i0 j) =
        Section3.sigmaOfPF35 ω χpf (ω i0 j') := by
    exact huniq (hω.irreducible i0 j')
      ⟨deltaSign j, hsign j, Section1.conjugateCharacter (piChar i0 j), hbarIrr, rfl⟩
      hbarV
  have hrowV :
      ∀ x : L, ∀ hx : x ∈ Section3.cyclicTISet W1 W2 W,
        (deltaSign j' • piChar i0 j') x =
          ω i0 j' ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
    intro x hx
    have hxWm : x ∈ ((W : Set L) \ (W2 : Set L)) := by
      exact ⟨Section3.cyclicTISet_subset W1 W2 W hx,
        Section3.cyclicTISet_not_mem_right W1 W2 W hx⟩
    have hval := h43c.1 i0 j' x hxWm
    change deltaSign j' * piChar i0 j' x =
      ω i0 j' ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩
    calc
      deltaSign j' * piChar i0 j' x =
          deltaSign j' *
            (deltaSign j' *
              ω i0 j' ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩) := by
                rw [hval]
      _ = (deltaSign j' * deltaSign j') *
            ω i0 j' ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
              ring
      _ = ω i0 j' ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
            rw [sign_mul_self_eq_one_pf45 (hsign j')]
            simp
  have hrowEq :
      deltaSign j' • piChar i0 j' =
        Section3.sigmaOfPF35 ω χpf (ω i0 j') := by
    exact huniq (hω.irreducible i0 j')
      ⟨deltaSign j', hsign j', piChar i0 j', hirr i0 j', rfl⟩ hrowV
  have hscaled :
      deltaSign j • Section1.conjugateCharacter (piChar i0 j) =
        deltaSign j' • piChar i0 j' := by
    calc
      deltaSign j • Section1.conjugateCharacter (piChar i0 j) =
          Section3.sigmaOfPF35 ω χpf (ω i0 j') := hbarEq
      _ = deltaSign j' • piChar i0 j' := hrowEq.symm
  rcases hirr i0 j with ⟨n, ρ, hρirr, hρchar⟩
  rcases hirr i0 j' with ⟨m, ρ', hρ'irr, hρ'char⟩
  have hnDeg : Section1.degree (piChar i0 j) = (n : ℂ) := by
    rw [hρchar]
    simpa using Section1.degree_representation_character ρ
  have hmDeg : Section1.degree (piChar i0 j') = (m : ℂ) := by
    rw [hρ'char]
    simpa using Section1.degree_representation_character ρ'
  have hnormj : Section1.scalarProduct L (piChar i0 j) (piChar i0 j) = 1 := by
    simpa using scalarProduct_irreducible_self_pf45 (hirr i0 j)
  have hnormj' : Section1.scalarProduct L (piChar i0 j') (piChar i0 j') = 1 := by
    simpa using scalarProduct_irreducible_self_pf45 (hirr i0 j')
  have hnPos : 0 < n := by
    by_contra hnNotPos
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnNotPos
    subst hn0
    have hzeroChar : ρ.character = (0 : ClassFunction L) := by
      ext g
      have hρg0 : ρ g = 0 := by
        ext v i
        exact Fin.elim0 i
      simp [Representation.character, hρg0]
    have hzero : piChar i0 j = 0 := by
      simpa [hρchar] using hzeroChar
    rw [hzero] at hnormj
    simp [Section1.scalarProduct] at hnormj
  have hmPos : 0 < m := by
    by_contra hmNotPos
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hmNotPos
    subst hm0
    have hzeroChar : ρ'.character = (0 : ClassFunction L) := by
      ext g
      have hρg0 : ρ' g = 0 := by
        ext v i
        exact Fin.elim0 i
      simp [Representation.character, hρg0]
    have hzero : piChar i0 j' = 0 := by
      simpa [hρ'char] using hzeroChar
    rw [hzero] at hnormj'
    simp [Section1.scalarProduct] at hnormj'
  have hnVal : piChar i0 j 1 = (n : ℂ) := by
    simpa [Section1.degree] using hnDeg
  have hmVal : piChar i0 j' 1 = (m : ℂ) := by
    simpa [Section1.degree] using hmDeg
  rcases hsign j with hj | hj <;> rcases hsign j' with hj' | hj'
  · simpa [hj, hj'] using hscaled
  · exfalso
    have hAt1 := congrFun hscaled 1
    have hEq : (n : ℂ) = (-m : ℂ) := by
      calc
        (n : ℂ) = star (piChar i0 j 1) := by rw [hnVal]; simp
        _ = -piChar i0 j' 1 := by
              simpa [Pi.smul_apply, Section1.conjugateCharacter, hj, hj'] using hAt1
        _ = (-m : ℂ) := by rw [hmVal]
    have hEqRe := congrArg Complex.re hEq
    simp at hEqRe
    nlinarith
  · exfalso
    have hAt1 := congrFun hscaled 1
    have hEq : (-n : ℂ) = (m : ℂ) := by
      calc
        (-n : ℂ) = -star (piChar i0 j 1) := by rw [hnVal]; simp
        _ = piChar i0 j' 1 := by
              simpa [Pi.smul_apply, Section1.conjugateCharacter, hj, hj'] using hAt1
        _ = (m : ℂ) := by rw [hmVal]
    have hEqRe := congrArg Complex.re hEq
    simp at hEqRe
    nlinarith
  · simpa [hj, hj'] using hscaled


private theorem baseRow_linearCharacter_left_eq_one_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → ClassFunction W}
    (hIP : Section2.IsInternalDirectProduct W W1 W2)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {j : J}
    (lin : W →* ℂˣ)
    (hlin : ω i0 j = fun w : W => (lin w : ℂ))
    (x : W1) :
    lin ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
      (MonoidHom.inl W1 W2 x)) = 1 := by
  apply Units.ext
  have hmem :
      (Section3.internalDirectProductMulEquiv hIP).toMonoidHom
          (MonoidHom.inl W1 W2 x) ∈ W1.subgroupOf W := by
    change
      (((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
          (MonoidHom.inl W1 W2 x) : W) : L) ∈ W1
    have hEq :
        (((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
            (MonoidHom.inl W1 W2 x) : W) : L) = x := by
      simpa using congrArg Subtype.val
        (Section3.internalDirectProductMulEquiv_apply_inl hIP x)
    rw [hEq]
    exact x.property
  have hker := hω.right_kernel j
    ⟨(Section3.internalDirectProductMulEquiv hIP).toMonoidHom
      (MonoidHom.inl W1 W2 x), hmem⟩
  have hval :
      ω i0 j ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
        (MonoidHom.inl W1 W2 x)) = 1 := by
    rw [hω.degree_one i0 j] at hker
    exact hker
  simpa [hlin] using hval

private theorem baseRow_linearCharacter_eq_rightComponent_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → ClassFunction W}
    (hIP : Section2.IsInternalDirectProduct W W1 W2)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {j : J}
    (lin : W →* ℂˣ)
    (hlin : ω i0 j = fun w : W => (lin w : ℂ))
    (w : W) :
    lin w =
      lin ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
        (MonoidHom.inr W1 W2
          (((Section3.internalDirectProductMulEquiv hIP).symm w).2))) := by
  let e : W1 × W2 ≃* W := Section3.internalDirectProductMulEquiv hIP
  let p : W1 × W2 := e.symm w
  have hp : MonoidHom.inl W1 W2 p.1 * MonoidHom.inr W1 W2 p.2 = p := by
    ext <;> simp [MonoidHom.inl_apply, MonoidHom.inr_apply]
  have hw :
      e.toMonoidHom (MonoidHom.inl W1 W2 p.1) *
          e.toMonoidHom (MonoidHom.inr W1 W2 p.2) = w := by
    calc
      e.toMonoidHom (MonoidHom.inl W1 W2 p.1) *
          e.toMonoidHom (MonoidHom.inr W1 W2 p.2) =
          e.toMonoidHom (MonoidHom.inl W1 W2 p.1 *
            MonoidHom.inr W1 W2 p.2) := by
            rw [map_mul]
      _ = e.toMonoidHom p := by rw [hp]
      _ = w := by
            change e p = w
            simp [p, e]
  have hleft :
      lin (e.toMonoidHom (MonoidHom.inl W1 W2 p.1)) = 1 :=
    baseRow_linearCharacter_left_eq_one_pf45 hIP hω lin hlin p.1
  calc
    lin w = lin (e.toMonoidHom (MonoidHom.inl W1 W2 p.1) *
        e.toMonoidHom (MonoidHom.inr W1 W2 p.2)) := by rw [hw]
    _ = lin (e.toMonoidHom (MonoidHom.inl W1 W2 p.1)) *
        lin (e.toMonoidHom (MonoidHom.inr W1 W2 p.2)) := by rw [map_mul]
    _ = lin (e.toMonoidHom (MonoidHom.inr W1 W2 p.2)) := by rw [hleft, one_mul]
    _ = lin ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
        (MonoidHom.inr W1 W2
          (((Section3.internalDirectProductMulEquiv hIP).symm w).2))) := rfl

private theorem baseRow_rightCharacter_ne_one_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → ClassFunction W}
    (hIP : Section2.IsInternalDirectProduct W W1 W2)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {j : J}
    (hj : j ≠ j0)
    (lin : W →* ℂˣ)
    (hlin : ω i0 j = fun w : W => (lin w : ℂ)) :
    lin.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inr W1 W2)) ≠ 1 := by
  intro hres
  have hrow_principal : ω i0 j = Section1.principalCharacter W := by
    ext w
    have hright :
        lin ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
          (MonoidHom.inr W1 W2
            (((Section3.internalDirectProductMulEquiv hIP).symm w).2))) = 1 := by
      have happ := congrArg
        (fun f : W2 →* ℂˣ =>
          f (((Section3.internalDirectProductMulEquiv hIP).symm w).2)) hres
      simpa using happ
    calc
      ω i0 j w = (lin w : ℂ) := by rw [hlin]
      _ =
          (lin ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
            (MonoidHom.inr W1 W2
              (((Section3.internalDirectProductMulEquiv hIP).symm w).2))) : ℂ) := by
            rw [baseRow_linearCharacter_eq_rightComponent_pf45 hIP hω lin hlin w]
      _ = 1 := by
            exact congrArg (fun z : ℂˣ => (z : ℂ)) hright
      _ = Section1.principalCharacter W w := rfl
  have hbase : ω i0 j = ω i0 j0 := by
    rw [hrow_principal, hω.principal]
  exact hj (hω.pairwise_eq (i := i0) (i' := i0) (j := j) (j' := j0) hbase).2

private theorem baseRow_exactCharacterValueOrder_of_rightCharacter_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → ClassFunction W}
    {q : ℕ}
    (hIP : Section2.IsInternalDirectProduct W W1 W2)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {j : J}
    (lin : W →* ℂˣ)
    (hlin : ω i0 j = fun w : W => (lin w : ℂ))
    (horder : orderOf
      (lin.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
        (MonoidHom.inr W1 W2))) = q)
    (hqpos : 0 < q) :
    Section3.exactCharacterValueOrder (ω i0 j) q := by
  let rightHom : W2 →* ℂˣ :=
    lin.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inr W1 W2))
  have hright_order : orderOf rightHom = q := horder
  constructor
  · constructor
    · exact hqpos
    · intro w
      have hright :
          lin w =
            rightHom (((Section3.internalDirectProductMulEquiv hIP).symm w).2) := by
        simpa [rightHom] using
          baseRow_linearCharacter_eq_rightComponent_pf45 hIP hω lin hlin w
      have hpowRight : rightHom ^ q = 1 := by
        rw [← hright_order]
        exact pow_orderOf_eq_one rightHom
      have hval := congrArg
        (fun f : W2 →* ℂˣ => f (((Section3.internalDirectProductMulEquiv hIP).symm w).2))
        hpowRight
      calc
        (ω i0 j w) ^ q = ((lin w : ℂ)) ^ q := by rw [hlin]
        _ = ((rightHom (((Section3.internalDirectProductMulEquiv hIP).symm w).2) : ℂ)) ^ q := by
              rw [hright]
        _ = 1 := by
              simpa [MonoidHom.pow_apply, Units.val_pow_eq_pow_val] using
                congrArg (fun z : ℂˣ => (z : ℂ)) hval
  · intro b hb
    have hpowRight : rightHom ^ b = 1 := by
      ext y
      have hval := hb.2
        ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
          (MonoidHom.inr W1 W2 y))
      simpa [rightHom, hlin, Units.val_pow_eq_pow_val] using hval
    rw [← hright_order]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpowRight

private theorem baseRow_classFunctionValueZPow_of_rightCharacter_zpow_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → ClassFunction W}
    (hIP : Section2.IsInternalDirectProduct W W1 W2)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {jbase jtarget : J}
    {k : ℤ}
    (base target : W →* ℂˣ)
    (hbase : ω i0 jbase = fun w : W => (base w : ℂ))
    (htarget : ω i0 jtarget = fun w : W => (target w : ℂ))
    (hres :
      target.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
        (MonoidHom.inr W1 W2)) =
        (base.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
          (MonoidHom.inr W1 W2))) ^ k) :
    Section3.classFunctionValueZPow (ω i0 jbase) (ω i0 jtarget) k := by
  let rightBase : W2 →* ℂˣ :=
    base.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inr W1 W2))
  let rightTarget : W2 →* ℂˣ :=
    target.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inr W1 W2))
  have hres' : rightTarget = rightBase ^ k := by
    simpa [rightBase, rightTarget] using hres
  intro w
  have hbase_right :
      base w = rightBase (((Section3.internalDirectProductMulEquiv hIP).symm w).2) := by
    simpa [rightBase] using
      baseRow_linearCharacter_eq_rightComponent_pf45 hIP hω base hbase w
  have htarget_right :
      target w = rightTarget (((Section3.internalDirectProductMulEquiv hIP).symm w).2) := by
    simpa [rightTarget] using
      baseRow_linearCharacter_eq_rightComponent_pf45 hIP hω target htarget w
  have htarget_pow :
      target w = base w ^ k := by
    calc
      target w = rightTarget (((Section3.internalDirectProductMulEquiv hIP).symm w).2) :=
        htarget_right
      _ = (rightBase ^ k) (((Section3.internalDirectProductMulEquiv hIP).symm w).2) := by
        rw [hres']
      _ = rightBase (((Section3.internalDirectProductMulEquiv hIP).symm w).2) ^ k := by
        simp [MonoidHom.zpow_apply]
      _ = base w ^ k := by rw [hbase_right]
  calc
    ω i0 jtarget w = (target w : ℂ) := by rw [htarget]
    _ = ((base w ^ k : ℂˣ) : ℂ) := by rw [htarget_pow]
    _ = ((base w : ℂ) ^ k) := by rw [Units.val_zpow_eq_zpow_val]
    _ = (ω i0 jbase w) ^ k := by rw [hbase]

private theorem baseRow_omega_power_of_prime_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → ClassFunction W}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hW2prime : Nat.Prime (Nat.card W2))
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {j k : J}
    (hj : j ≠ j0) (hk : k ≠ j0) :
    ∃ n : ℤ,
      Section3.exactCharacterValueOrder (ω i0 k) (Nat.card W2) ∧
        IsCoprime n (Nat.card W2 : ℤ) ∧
          Section3.classFunctionValueZPow (ω i0 k) (ω i0 j) n := by
  classical
  rcases h31 with ⟨_hW1le, hW2le, hIP, _hcycW, _hodd, _hcard1, _hcard2, _hTI⟩
  have hcycW2 : IsCyclic W2 := Subgroup.isCyclic_of_le hW2le
  let : CommGroup W2 := IsCyclic.commGroup
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent W2) :=
    Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent W2)
  let : Fintype (W2 →* ℂˣ) := by
    let e := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity W2 ℂ).some
    exact Fintype.ofEquiv W2 e.toEquiv.symm
  have hcardLin : Nat.card (W2 →* ℂˣ) = Nat.card W2 :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity W2 ℂ
  rcases Section1.exists_linearCharacter_of_irreducible_degree_one
      (hω.irreducible i0 k) (hω.degree_one i0 k) with
    ⟨baseLin, hbaseLin⟩
  rcases Section1.exists_linearCharacter_of_irreducible_degree_one
      (hω.irreducible i0 j) (hω.degree_one i0 j) with
    ⟨targetLin, htargetLin⟩
  let rightBase : W2 →* ℂˣ :=
    baseLin.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inr W1 W2))
  let rightTarget : W2 →* ℂˣ :=
    targetLin.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inr W1 W2))
  have hbase_ne : rightBase ≠ 1 := by
    exact baseRow_rightCharacter_ne_one_pf45 hIP hω hk baseLin hbaseLin
  have htarget_ne : rightTarget ≠ 1 := by
    exact baseRow_rightCharacter_ne_one_pf45 hIP hω hj targetLin htargetLin
  have : Fact (Nat.card W2).Prime := ⟨hW2prime⟩
  have hrightBase_gen : ∀ χ : W2 →* ℂˣ, χ ∈ Subgroup.zpowers rightBase := by
    intro χ
    exact mem_zpowers_of_prime_card (G := W2 →* ℂˣ)
      (p := Nat.card W2) hcardLin hbase_ne
  have hrightBase_order : orderOf rightBase = Nat.card W2 := by
    calc
      orderOf rightBase = Nat.card (W2 →* ℂˣ) :=
        orderOf_eq_card_of_forall_mem_zpowers hrightBase_gen
      _ = Nat.card W2 := hcardLin
  have htarget_mem : rightTarget ∈ Subgroup.zpowers rightBase :=
    hrightBase_gen rightTarget
  rcases Subgroup.mem_zpowers_iff.mp htarget_mem with ⟨n, hnpow⟩
  have hbase_mem_target : rightBase ∈ Subgroup.zpowers rightTarget :=
    mem_zpowers_of_prime_card (G := W2 →* ℂˣ)
      (p := Nat.card W2) hcardLin htarget_ne
  have hbase_mem_power : rightBase ∈ Subgroup.zpowers (rightBase ^ n) := by
    simpa [hnpow] using hbase_mem_target
  have hn_gcd : n.gcd (orderOf rightBase : ℤ) = 1 :=
    mem_zpowers_zpow_iff.mp hbase_mem_power
  have hn_coprime_order : IsCoprime n (orderOf rightBase : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact hn_gcd
  have hn_coprime : IsCoprime n (Nat.card W2 : ℤ) := by
    simpa [hrightBase_order] using hn_coprime_order
  have horder :
      Section3.exactCharacterValueOrder (ω i0 k) (Nat.card W2) :=
    baseRow_exactCharacterValueOrder_of_rightCharacter_pf45 hIP hω
      baseLin hbaseLin hrightBase_order hW2prime.pos
  have hpow :
      Section3.classFunctionValueZPow (ω i0 k) (ω i0 j) n :=
    baseRow_classFunctionValueZPow_of_rightCharacter_zpow_pf45 hIP hω
      baseLin targetLin hbaseLin htargetLin (by
        simpa [rightBase, rightTarget] using hnpow.symm)
  exact ⟨n, horder, hn_coprime, hpow⟩

/-- The base-column counterpart of `baseRow_omega_power_of_prime_pf45`,
obtained by swapping the two cyclic direct factors in PF `(3.3)`. -/
public theorem baseColumn_omega_power_of_prime_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J → ClassFunction W}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hW1prime : Nat.Prime (Nat.card W1))
    (homega : Section3.notation_3_3_statement W1 W2 W I J i0 j0 omega)
    {i k : I}
    (hi : i ≠ i0) (hk : k ≠ i0) :
    ∃ n : ℤ,
      Section3.exactCharacterValueOrder (omega k j0) (Nat.card W1) ∧
        IsCoprime n (Nat.card W1 : ℤ) ∧
          Section3.classFunctionValueZPow (omega k j0) (omega i j0) n := by
  simpa using
    (baseRow_omega_power_of_prime_pf45
      (W1 := W2) (W2 := W1) (W := W)
      (I := J) (J := I) (i0 := j0) (j0 := i0)
      (ω := fun j i => omega i j)
      (Section3.hypothesis_3_1_statement_swap h31) hW1prime
      (Section3.notation_3_3_statement_swap homega) hi hk)

private theorem baseRowGaloisConjugate_pf45
    {L : Type u} [Group L] [Finite L]
    (W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hW2prime : Nat.Prime (Nat.card W2))
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω) :
    ∀ j k, j ≠ j0 → k ≠ j0 →
      ∃ γ : Gal(ℂ/ℚ),
        deltaSign j • piChar i0 j =
          Section3.classFunctionGaloisConjugate γ
            (deltaSign k • piChar i0 k) := by
  classical
  rcases h43b with ⟨hσmap, _hsign, _hirr, _hdistinct, _hind, hSigma⟩
  rcases Section3.pf35_data_of_theorem_3_2_map_statement hω σ hσmap with
    ⟨χ, horth, hsigned, h00, hInd, hσeq⟩
  have hσ_eq : σ = Section3.sigmaOfPF35 ω χ :=
    Section3.sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h31 hω hσeq
  have hroot : ∀ {c b e : ℕ}, e.Coprime (c * b) →
      ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e := by
    intro c b e he
    exact Section1.complex_galois_aut_pow_on_roots he
  have hB :
      Section3.proposition_3_9_statement_b_complex_galois
        (Section3.sigmaOfPF35 ω χ) :=
    Section3.proposition_3_9_b_of_rootAction_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h31 hω horth hsigned h00 hInd hroot
  intro j k hj hk
  rcases baseRow_omega_power_of_prime_pf45 h31 hW2prime hω hj hk with
    ⟨n, horder, hncoprime, hpow_row⟩
  rcases hB (ω' := ω i0 k) (a := Nat.card W2) (k := n)
      (hω.irreducible i0 k) horder hncoprime with
    ⟨ωn, _hωn_irred, hpow, γ, _hγ, hσγ, _hpoint⟩
  have hωn_eq : ωn = ω i0 j := by
    ext w
    rw [hpow w, hpow_row w]
  refine ⟨γ, ?_⟩
  calc
    deltaSign j • piChar i0 j = σ (ω i0 j) := (hSigma i0 j).symm
    _ = σ ωn := by rw [hωn_eq]
    _ = Section3.sigmaOfPF35 ω χ ωn := by rw [hσ_eq]
    _ = Section3.classFunctionGaloisConjugate γ
          (Section3.sigmaOfPF35 ω χ (ω i0 k)) := hσγ
    _ = Section3.classFunctionGaloisConjugate γ (σ (ω i0 k)) := by rw [← hσ_eq]
    _ = Section3.classFunctionGaloisConjugate γ (deltaSign k • piChar i0 k) := by
          rw [hSigma i0 k]


public theorem baseRowGaloisConjugate_of_hypothesis_4_6_supported_statement
    {G : Type v} [Group G] [Finite G]
    (L : Subgroup G) [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → ClassFunction W}
    {σL : ClassFunction W →ₗ[ℂ] ClassFunction L}
    {σ : ClassFunction W →ₗ[ℂ] ClassFunction G}
    {piChar : I → J → ClassFunction L}
    {xChar : J → ClassFunction K}
    {deltaSign : J → ℂ}
    {τ : ClassFunction L →ₗ[ℂ] ClassFunction G}
    {H_A : G → Subgroup G}
    (_hSupported :
      hypothesis_4_6_supported_statement L K W1 W2 W H A i0 j0 ω σL σ
        piChar xChar deltaSign τ H_A)
    (_hW2prime : Nat.Prime (Nat.card W2)) :
    ∀ j k, j ≠ j0 → k ≠ j0 →
      ∃ γ : Gal(ℂ/ℚ),
        deltaSign j • piChar i0 j =
          Section3.classFunctionGaloisConjugate γ (deltaSign k • piChar i0 k) := by
  rcases _hSupported with
    ⟨h46, _hW2K, _h31img, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hRest⟩
  rcases hRest with
    ⟨hω, h43b, _h43c, _h43d, _h45a, _h45b, _hτσ, _hτA0,
      _hτiso, _hτpunct, _hτvirt, _hPF39⟩
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    hypothesis_3_1_of_hypothesis_4_6_pf45 h46
  exact baseRowGaloisConjugate_pf45 W1 W2 W i0 j0 ω σL piChar
    deltaSign h31 _hW2prime hω h43b


/-- The PF `(4.9.a)` zero-row conjugation step, retaining the cyclic-TI
`ω` conjugation witness as well as its selected `Π`-character consequence. -/
public theorem theorem_4_9_a_baseRow_omega_piChar_conjugate
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    {j : J} (hj : j ≠ j0) :
    ∃ j' : J, j' ≠ j0 ∧ j' ≠ j ∧
      Section1.conjugateCharacter (ω i0 j) = ω i0 j' ∧
        Section1.conjugateCharacter (piChar i0 j) = piChar i0 j' := by
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    hypothesis_3_1_of_hypothesis_4_6_pf45 h46
  rcases conjugate_omega_baseRow_ne_pf45
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) h31 hω hj with
    ⟨j', hbarOmega, hj'ne⟩
  have hj'0 : j' ≠ j0 := by
    intro hj'0
    have hbar0 :
        Section1.conjugateCharacter (ω i0 j) = Section1.principalCharacter W := by
      simpa [hj'0, hω.principal] using hbarOmega
    have hprincipal : ω i0 j = Section1.principalCharacter W := by
      ext x
      have hx := congrFun hbar0 x
      simpa [Section1.conjugateCharacter, Section1.principalCharacter] using congrArg star hx
    exact hj ((hω.pairwise_eq (i := i0) (i' := i0) (j := j) (j' := j0)
      (by simpa [hω.principal] using hprincipal)).2)
  refine ⟨j', hj'0, hj'ne, hbarOmega, ?_⟩
  exact conjugate_piChar_baseRow_eq_of_conjugate_omega_pf45
    (W1 := W1) (W2 := W2) (W := W) (i0 := i0) (j0 := j0)
    (ω := ω) (σ := σ) (piChar := piChar) (deltaSign := deltaSign)
    h31 hω h43b h43c hbarOmega

private theorem conjugateCharacter_inducedCF_pf45
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) :
    Section1.conjugateCharacter (Section1.inducedCF H theta) =
      Section1.inducedCF H (Section1.conjugateCharacter theta) := by
  classical
  funext g
  unfold Section1.conjugateCharacter Section1.inducedCF Section1.inducedClassFunction
  calc
    star ((Nat.card H : ℂ)⁻¹ *
        ∑ x : G, (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0))
        =
      (Nat.card H : ℂ)⁻¹ *
        star (∑ x : G, (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0)) := by
          simp
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ x : G, star (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0) := by
          rw [star_sum]
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ x : G,
          (if hx : x * g * x⁻¹ ∈ H then
            (Section1.conjugateCharacter theta) ⟨x * g * x⁻¹, hx⟩
          else 0) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro x _hx
            by_cases hmem : x * g * x⁻¹ ∈ H
            · simp [hmem]
              rfl
            · simp [hmem]

private theorem conjugate_piColumn_eq_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal]
    {I J : Type*} [Fintype I] [Fintype J]
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    {i0 : I} {j j' : J}
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hbarBase : Section1.conjugateCharacter (piChar i0 j) = piChar i0 j') :
    Section1.conjugateCharacter (piColumn piChar j) = piColumn piChar j' := by
  rcases h45a with ⟨hres, _hirrX, hindX⟩
  calc
    Section1.conjugateCharacter (piColumn piChar j)
        = Section1.conjugateCharacter
            (Section1.inducedCF K (Section1.subgroupRestriction K (piChar i0 j))) := by
              rw [hres i0 j, hindX j]
    _ = Section1.inducedCF K
          (Section1.conjugateCharacter (Section1.subgroupRestriction K (piChar i0 j))) := by
            rw [conjugateCharacter_inducedCF_pf45 K]
    _ = Section1.inducedCF K
          (Section1.subgroupRestriction K (Section1.conjugateCharacter (piChar i0 j))) := by
            rw [subgroupRestriction_conjugateCharacter_pf45]
    _ = Section1.inducedCF K (Section1.subgroupRestriction K (piChar i0 j')) := by
            rw [hbarBase]
    _ = piColumn piChar j' := by
          rw [hres i0 j', hindX j']

private theorem degree_piColumn_eq_nat_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (j : J) :
    ∃ n : ℕ, Section1.degree (piColumn piChar j) = (n : ℂ) := by
  rcases h45a with ⟨_hres, hirrX, hindX⟩
  rcases degree_eq_nat_of_isIrreducibleCharacterOnGroup_pf45 (hirrX j) with ⟨m, hm⟩
  refine ⟨Subgroup.index K * m, ?_⟩
  calc
    Section1.degree (piColumn piChar j)
        = Section1.degree (Section1.inducedCF K (xChar j)) := by rw [← hindX j]
    _ = (Subgroup.index K : ℂ) * Section1.degree (xChar j) := by
          simpa using Section1.degree_inducedClassFunction K (xChar j)
    _ = ((Subgroup.index K * m : Nat) : ℂ) := by
          rw [hm, Nat.cast_mul]

private theorem positive_degree_piColumn_eq_nat_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (j : J) :
    ∃ n : ℕ, 0 < n ∧ Section1.degree (piColumn piChar j) = (n : ℂ) := by
  rcases h45a with ⟨_hres, hirrX, hindX⟩
  rcases positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf45 (hirrX j) with
    ⟨m, hmpos, hm⟩
  have hidxpos : 0 < Subgroup.index K := Nat.pos_of_ne_zero <|
    Subgroup.index_ne_zero_of_finite (G := L) (H := K)
  refine ⟨Subgroup.index K * m, Nat.mul_pos hidxpos hmpos, ?_⟩
  calc
    Section1.degree (piColumn piChar j)
        = Section1.degree (Section1.inducedCF K (xChar j)) := by rw [← hindX j]
    _ = (Subgroup.index K : ℂ) * Section1.degree (xChar j) := by
          simpa using Section1.degree_inducedClassFunction K (xChar j)
    _ = ((Subgroup.index K * m : Nat) : ℂ) := by
          rw [hm, Nat.cast_mul]

private theorem degree_entry_eq_of_equal_degree_column_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    {i : I} {j k : J}
    (hdegCol : Section1.degree (piColumn piChar j) = Section1.degree (piColumn piChar k)) :
    Section1.degree (piChar i j) = Section1.degree (piChar i k) := by
  rcases h45a with ⟨hres, _hirrX, hindX⟩
  have hidxC : (Subgroup.index K : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (G := L) (H := K)
  have hdegX :
      Section1.degree (xChar j) = Section1.degree (xChar k) := by
    have hmul :
        (Subgroup.index K : ℂ) * Section1.degree (xChar j) =
          (Subgroup.index K : ℂ) * Section1.degree (xChar k) := by
      calc
        (Subgroup.index K : ℂ) * Section1.degree (xChar j)
            = Section1.degree (piColumn piChar j) := by
                rw [← hindX j]
                simpa using (Section1.degree_inducedClassFunction K (xChar j)).symm
        _ = Section1.degree (piColumn piChar k) := hdegCol
        _ = (Subgroup.index K : ℂ) * Section1.degree (xChar k) := by
              rw [← hindX k]
              simpa using Section1.degree_inducedClassFunction K (xChar k)
    exact mul_left_cancel₀ hidxC hmul
  have hresj := congrFun (hres i j) 1
  have hresk := congrFun (hres i k) 1
  calc
    Section1.degree (piChar i j) = Section1.degree (xChar j) := by
      simpa [Section1.degree, Section1.subgroupRestriction] using hresj
    _ = Section1.degree (xChar k) := hdegX
    _ = Section1.degree (piChar i k) := by
      simpa [Section1.degree, Section1.subgroupRestriction] using hresk.symm

private theorem scalarProduct_piColumn_entry_eq_ite_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I)
    (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (j k : J) :
    Section1.scalarProduct L (piColumn piChar j) (piChar i0 k) =
      if j = k then 1 else 0 := by
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigma⟩
  unfold piColumn
  have hsum :
      ((∑ i : I, piChar i j : ClassFunction L)) = fun g => ∑ i : I, piChar i j g := by
    ext g
    simp
  rw [hsum]
  rw [Section1.scalarProduct_fintype_sum_left]
  by_cases hjk : j = k
  · subst k
    calc
      ∑ i : I, Section1.scalarProduct L (piChar i j) (piChar i0 j) =
          ∑ i : I, if i = i0 then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            by_cases hii : i = i0
            · subst i
              simpa using scalarProduct_irreducible_self_pf45 (hirr i0 j)
            · simpa [hii] using
                scalarProduct_irreducible_ne_pf45 (hirr i j) (hirr i0 j)
                  (hdistinct (i, j) (i0, j) (by
                    intro hEq
                    exact hii (congrArg Prod.fst hEq)))
      _ = if j = j then 1 else 0 := by
            simp
  · calc
      ∑ i : I, Section1.scalarProduct L (piChar i j) (piChar i0 k) =
          ∑ i : I, (0 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simpa using
              scalarProduct_irreducible_ne_pf45 (hirr i j) (hirr i0 k)
                (hdistinct (i, j) (i0, k) (by
                  intro hEq
                  exact hjk (congrArg Prod.snd hEq)))
      _ = if j = k then 1 else 0 := by
            simp [hjk]

private theorem scalarProduct_piColumn_eq_card_ite_pf45
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I)
    (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (j k : J) :
    Section1.scalarProduct L (piColumn piChar j) (piColumn piChar k) =
      if j = k then (Fintype.card I : ℂ) else 0 := by
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigma⟩
  unfold piColumn
  have hsumj :
      ((∑ i : I, piChar i j : ClassFunction L)) = fun g => ∑ i : I, piChar i j g := by
    ext g
    simp
  have hsumk :
      ((∑ i : I, piChar i k : ClassFunction L)) = fun g => ∑ i : I, piChar i k g := by
    ext g
    simp
  rw [hsumj, Section1.scalarProduct_fintype_sum_left]
  by_cases hjk : j = k
  · subst k
    calc
      ∑ i : I, Section1.scalarProduct L (piChar i j) (∑ p : I, piChar p j) =
          ∑ i : I, Section1.scalarProduct L (piChar i j) (fun g => ∑ p : I, piChar p j g) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hsumj]
      _ =
          ∑ i : I, ∑ p : I, Section1.scalarProduct L (piChar i j) (piChar p j) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Section1.scalarProduct_fintype_sum_right]
      _ =
          ∑ i : I, ∑ p : I, if i = p then (1 : ℂ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            refine Finset.sum_congr rfl ?_
            intro p _hp
            by_cases hip : i = p
            · subst p
              simpa using scalarProduct_irreducible_self_pf45 (hirr i j)
            · simpa [hip] using
                scalarProduct_irreducible_ne_pf45 (hirr i j) (hirr p j)
                  (hdistinct (i, j) (p, j) (by
                    intro hEq
                    exact hip (congrArg Prod.fst hEq)))
      _ = if j = j then (Fintype.card I : ℂ) else 0 := by
            simp
  · calc
      ∑ i : I, Section1.scalarProduct L (piChar i j) (∑ p : I, piChar p k) =
          ∑ i : I, Section1.scalarProduct L (piChar i j) (fun g => ∑ p : I, piChar p k g) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hsumk]
      _ =
          ∑ i : I, ∑ p : I, Section1.scalarProduct L (piChar i j) (piChar p k) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Section1.scalarProduct_fintype_sum_right]
      _ =
          ∑ i : I, ∑ p : I, (0 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            refine Finset.sum_congr rfl ?_
            intro p _hp
            simpa using
              scalarProduct_irreducible_ne_pf45 (hirr i j) (hirr p k)
                (hdistinct (i, j) (p, k) (by
                  intro hEq
                  exact hjk (congrArg Prod.snd hEq)))
      _ = if j = k then (Fintype.card I : ℂ) else 0 := by
            simp [hjk]

private theorem scalarProduct_omegaColumnSigma_eq_card_ite_pf45
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I)
    (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (deltaSign : J → ℂ)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hσiso : ∀ α β, Section1.scalarProduct G (σ α) (σ β) =
      Section1.scalarProduct W α β)
    (hsign : ∀ j, Section1.IsSign (deltaSign j))
    (k j l : J) :
    Section1.scalarProduct G (deltaSign k • omegaColumnSigma σ ω j)
      (deltaSign k • omegaColumnSigma σ ω l) =
      if j = l then (Fintype.card I : ℂ) else 0 := by
  have hbase :
      Section1.scalarProduct G (omegaColumnSigma σ ω j) (omegaColumnSigma σ ω l) =
        if j = l then (Fintype.card I : ℂ) else 0 := by
    unfold omegaColumnSigma
    have hsumj :
        ((∑ i : I, σ (ω i j) : ClassFunction G)) =
          fun g => ∑ i : I, σ (ω i j) g := by
      ext g
      simp
    have hsuml :
        ((∑ i : I, σ (ω i l) : ClassFunction G)) =
          fun g => ∑ i : I, σ (ω i l) g := by
      ext g
      simp
    rw [hsumj, Section1.scalarProduct_fintype_sum_left]
    by_cases hjl : j = l
    · subst l
      calc
        ∑ i : I, Section1.scalarProduct G (σ (ω i j)) (∑ p : I, σ (ω p j)) =
            ∑ i : I, Section1.scalarProduct G (σ (ω i j)) (fun g => ∑ p : I, σ (ω p j) g) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [hsumj]
        _ =
            ∑ i : I, ∑ p : I, Section1.scalarProduct G (σ (ω i j)) (σ (ω p j)) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [Section1.scalarProduct_fintype_sum_right]
        _ =
            ∑ i : I, ∑ p : I, if i = p then (1 : ℂ) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              refine Finset.sum_congr rfl ?_
              intro p _hp
              by_cases hip : i = p
              · subst p
                calc
                  Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) =
                      Section1.scalarProduct W (ω i j) (ω i j) := hσiso _ _
                  _ = 1 := scalarProduct_irreducible_self_pf45 (hω.irreducible i j)
                  _ = if i = i then (1 : ℂ) else 0 := by simp
              · have hneq : ω i j ≠ ω p j := by
                  intro hEq
                  exact hip ((hω.pairwise_eq (i := i) (i' := p) (j := j) (j' := j) hEq).1)
                calc
                  Section1.scalarProduct G (σ (ω i j)) (σ (ω p j)) =
                      Section1.scalarProduct W (ω i j) (ω p j) := hσiso _ _
                  _ = 0 := by
                      simpa using scalarProduct_irreducible_ne_pf45
                        (hω.irreducible i j) (hω.irreducible p j) hneq
                  _ = if i = p then (1 : ℂ) else 0 := by simp [hip]
        _ = if j = j then (Fintype.card I : ℂ) else 0 := by
              simp
    · calc
        ∑ i : I, Section1.scalarProduct G (σ (ω i j)) (∑ p : I, σ (ω p l)) =
            ∑ i : I, Section1.scalarProduct G (σ (ω i j)) (fun g => ∑ p : I, σ (ω p l) g) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [hsuml]
        _ =
            ∑ i : I, ∑ p : I, Section1.scalarProduct G (σ (ω i j)) (σ (ω p l)) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [Section1.scalarProduct_fintype_sum_right]
        _ =
            ∑ i : I, ∑ p : I, (0 : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              refine Finset.sum_congr rfl ?_
              intro p _hp
              have hneq : ω i j ≠ ω p l := by
                intro hEq
                exact hjl ((hω.pairwise_eq
                  (i := i) (i' := p) (j := j) (j' := l) hEq).2)
              calc
                Section1.scalarProduct G (σ (ω i j)) (σ (ω p l)) =
                    Section1.scalarProduct W (ω i j) (ω p l) := hσiso _ _
                _ = 0 := by
                    simpa using scalarProduct_irreducible_ne_pf45
                      (hω.irreducible i j) (hω.irreducible p l) hneq
                _ = (0 : ℂ) := rfl
        _ = if j = l then (Fintype.card I : ℂ) else 0 := by
              simp [hjl]
  have hδstar : star (deltaSign k) = deltaSign k := sign_star_eq_self_pf45 (hsign k)
  calc
    Section1.scalarProduct G (deltaSign k • omegaColumnSigma σ ω j)
        (deltaSign k • omegaColumnSigma σ ω l) =
          deltaSign k * (star (deltaSign k) *
            Section1.scalarProduct G (omegaColumnSigma σ ω j) (omegaColumnSigma σ ω l)) := by
              rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
    _ = Section1.scalarProduct G (omegaColumnSigma σ ω j) (omegaColumnSigma σ ω l) := by
          calc
            deltaSign k * (star (deltaSign k) *
                Section1.scalarProduct G (omegaColumnSigma σ ω j) (omegaColumnSigma σ ω l)) =
                (deltaSign k * deltaSign k) *
                  Section1.scalarProduct G (omegaColumnSigma σ ω j) (omegaColumnSigma σ ω l) := by
                    rw [hδstar]
                    ring
            _ = Section1.scalarProduct G (omegaColumnSigma σ ω j) (omegaColumnSigma σ ω l) := by
                  rw [sign_mul_self_eq_one_pf45 (hsign k)]
                  simp
    _ = if j = l then (Fintype.card I : ℂ) else 0 := hbase

private theorem scalarProduct_evalCoeff_eq_of_gram_eq
    {G : Type u} [Group G] [Finite G]
    {H : Type v} [Group H] [Finite H]
    {J : Type*} [Fintype J]
    (mu : J → ClassFunction G)
    (nu : J → ClassFunction H)
    (hgram : ∀ j k, Section1.scalarProduct G (mu j) (mu k) =
      Section1.scalarProduct H (nu j) (nu k))
    (v w : Section1.CoeffVector J) :
    Section1.scalarProduct G (Section1.evalCoeff mu v) (Section1.evalCoeff mu w) =
      Section1.scalarProduct H (Section1.evalCoeff nu v) (Section1.evalCoeff nu w) := by
  have hleftG :
      (∑ j : J, (v j : ℂ) • mu j) = fun g : G => ∑ j : J, ((v j : ℂ) • mu j) g := by
    ext g
    simp
  have hrightG :
      (∑ j : J, (w j : ℂ) • mu j) = fun g : G => ∑ j : J, ((w j : ℂ) • mu j) g := by
    ext g
    simp
  have hleftH :
      (∑ j : J, (v j : ℂ) • nu j) = fun h : H => ∑ j : J, ((v j : ℂ) • nu j) h := by
    ext h
    simp
  have hrightH :
      (∑ j : J, (w j : ℂ) • nu j) = fun h : H => ∑ j : J, ((w j : ℂ) • nu j) h := by
    ext h
    simp
  calc
    Section1.scalarProduct G (Section1.evalCoeff mu v) (Section1.evalCoeff mu w) =
        ∑ j : J, ∑ k : J,
          (v j : ℂ) * (star (w k : ℂ) * Section1.scalarProduct G (mu j) (mu k)) := by
            simp only [Section1.evalCoeff]
            rw [hleftG, hrightG, Section1.scalarProduct_fintype_sum_left]
            simp_rw [Section1.scalarProduct_smul_left]
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [Section1.scalarProduct_fintype_sum_right]
            simp_rw [Section1.scalarProduct_smul_right]
            rw [Finset.mul_sum]
    _ = ∑ j : J, ∑ k : J,
          (v j : ℂ) * (star (w k : ℂ) * Section1.scalarProduct H (nu j) (nu k)) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            refine Finset.sum_congr rfl ?_
            intro k _hk
            rw [hgram j k]
    _ = Section1.scalarProduct H (Section1.evalCoeff nu v) (Section1.evalCoeff nu w) := by
          symm
          simp only [Section1.evalCoeff]
          rw [hleftH, hrightH, Section1.scalarProduct_fintype_sum_left]
          simp_rw [Section1.scalarProduct_smul_left]
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [Section1.scalarProduct_fintype_sum_right]
          simp_rw [Section1.scalarProduct_smul_right]
          rw [Finset.mul_sum]

private theorem coeff_sum_complex_zero_of_supportedOn_punctured_equalDegree_evalCoeff_pf45
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (j0 k : J)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (v : Section1.CoeffVector (equalDegreeColumnIndex piChar j0 k))
    (hv : Section1.supportedOn
      (Section1.evalCoeff
        (fun t : equalDegreeColumnIndex piChar j0 k => piColumn piChar t.1) v)
      puncturedSet) :
    ∑ t : equalDegreeColumnIndex piChar j0 k, (v t : ℂ) = 0 := by
  let T := equalDegreeColumnIndex piChar j0 k
  have hdeg0 :
      Section1.degree
        (Section1.evalCoeff (fun t : T => piColumn piChar t.1) v) = 0 := by
    exact (Section1.supportedOn_iff.mp hv) 1 (by simp [puncturedSet])
  rcases positive_degree_piColumn_eq_nat_pf45 K piChar xChar h45a k with ⟨n, hnpos, hkdeg⟩
  have hcommon : ∀ t : T, Section1.degree (piColumn piChar t.1) = (n : ℂ) := by
    intro t
    calc
      Section1.degree (piColumn piChar t.1) = Section1.degree (piColumn piChar k) := t.2.2
      _ = (n : ℂ) := hkdeg
  have hdegEval :
      Section1.degree (Section1.evalCoeff (fun t : T => piColumn piChar t.1) v) =
        (∑ t : T, (v t : ℂ)) * (n : ℂ) := by
    calc
      Section1.degree (Section1.evalCoeff (fun t : T => piColumn piChar t.1) v) =
          ∑ t : T, (v t : ℂ) * Section1.degree (piColumn piChar t.1) := by
            simp [Section1.degree, Section1.evalCoeff, Pi.smul_apply]
      _ = ∑ t : T, (v t : ℂ) * (n : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            rw [hcommon t]
      _ = (∑ t : T, (v t : ℂ)) * (n : ℂ) := by
            rw [Finset.sum_mul]
  have hmul0 : (∑ t : T, (v t : ℂ)) * (n : ℂ) = 0 := by
    simpa [hdegEval] using hdeg0
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hnpos
  exact (mul_eq_zero.mp hmul0).resolve_right hnC

private theorem evalCoeff_eq_evalCoeff_sub_base_of_coeff_sum_zero_pf45
    {G : Type u} [Group G]
    {J : Type*} [Fintype J]
    (mu : J → ClassFunction G)
    (j0 : J)
    (v : Section1.CoeffVector J)
    (hsum : ∑ j : J, (v j : ℂ) = 0) :
    Section1.evalCoeff mu v =
      Section1.evalCoeff (fun j => mu j - mu j0) v := by
  ext g
  have hzero : ∑ j : J, (v j : ℂ) * mu j0 g = 0 := by
    calc
      ∑ j : J, (v j : ℂ) * mu j0 g = (∑ j : J, (v j : ℂ)) * mu j0 g := by
        rw [Finset.sum_mul]
      _ = 0 := by simp [hsum]
  calc
    Section1.evalCoeff mu v g = ∑ j : J, (v j : ℂ) * mu j g := by
      simp [Section1.evalCoeff, Pi.smul_apply, mul_comm]
    _ = ∑ j : J, (v j : ℂ) * mu j g - 0 := by
          ring
    _ = ∑ j : J, (v j : ℂ) * mu j g - ∑ j : J, (v j : ℂ) * mu j0 g := by
          rw [hzero]
    _ = ∑ j : J, ((v j : ℂ) * mu j g - (v j : ℂ) * mu j0 g) := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ j : J, (v j : ℂ) * (mu j g - mu j0 g) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring
    _ = Section1.evalCoeff (fun j => mu j - mu j0) v g := by
          simp [Section1.evalCoeff, Pi.smul_apply, mul_comm]

private theorem tau_piColumn_sub_eq_signed_omegaColumnSigma_sub_pf45
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (K W2 W : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (i0 : I)
    (j0 k : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (h48 : theorem_4_8_statement (W2 := W2) (W := W) (j0 := j0)
      (ω := ω) A σ piChar deltaSign τ)
    (hk0 : k ≠ j0)
    {j : J}
    (hj : j ∈ equalDegreeColumnSet piChar j0 k) :
    τ (piColumn piChar j - piColumn piChar k) =
      deltaSign k • (omegaColumnSigma σ ω j - omegaColumnSigma σ ω k) := by
  have hdeg0 :
      Section1.degree (piChar i0 j) = Section1.degree (piChar i0 k) :=
    degree_entry_eq_of_equal_degree_column_pf45 K piChar xChar h45a hj.2
  have hsignjk : deltaSign j = deltaSign k :=
    (h48 i0 j k hj.1 hk0 hdeg0).2.1
  have hsumDiff :
      piColumn piChar j - piColumn piChar k =
        ∑ i : I, (piChar i j - piChar i k) := by
    ext g
    simp [piColumn, sub_eq_add_neg, Finset.sum_add_distrib,
      add_comm]
  calc
    τ (piColumn piChar j - piColumn piChar k)
        = ∑ i : I, τ (piChar i j - piChar i k) := by
            rw [hsumDiff, map_sum]
    _ = ∑ i : I, deltaSign k • (σ (ω i j) - σ (ω i k)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          have hdegik :
              Section1.degree (piChar i j) = Section1.degree (piChar i k) :=
            degree_entry_eq_of_equal_degree_column_pf45 K piChar xChar h45a hj.2
          calc
            τ (piChar i j - piChar i k)
                = deltaSign j • (σ (ω i j) - σ (ω i k)) :=
                    (h48 i j k hj.1 hk0 hdegik).2.2
            _ = deltaSign k • (σ (ω i j) - σ (ω i k)) := by rw [hsignjk]
    _ = deltaSign k • (omegaColumnSigma σ ω j - omegaColumnSigma σ ω k) := by
          calc
            ∑ i : I, deltaSign k • (σ (ω i j) - σ (ω i k)) =
                ∑ i : I, (deltaSign k • σ (ω i j) - deltaSign k • σ (ω i k)) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _hi
                  rw [smul_sub]
            _ = (∑ i : I, deltaSign k • σ (ω i j)) - ∑ i : I, deltaSign k • σ (ω i k) := by
                  rw [Finset.sum_sub_distrib]
            _ = deltaSign k • omegaColumnSigma σ ω j - deltaSign k • omegaColumnSigma σ ω k := by
                  unfold omegaColumnSigma
                  rw [Finset.smul_sum, Finset.smul_sum]
            _ = deltaSign k • (omegaColumnSigma σ ω j - omegaColumnSigma σ ω k) := by
                  rw [smul_sub]

/-- Internal witness package used to prove the lattice equality in `(4.9)(a)`:
conjugate equal-degree columns pair nontrivially, and one signed basis
difference is supported on `A`.  These are proof ingredients, not part of the
numbered book statement itself. -/
private theorem theorem_4_9_a_core_pf45
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    [DecidableEq I]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (k : J)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h47 : theorem_4_7_statement K H A) :
    k ≠ j0 →
      (∀ j, j ∈ equalDegreeColumnSet piChar j0 k →
        ∃ j', j' ∈ equalDegreeColumnSet piChar j0 k ∧
          Section1.conjugateCharacter (piColumn piChar j) = piColumn piChar j' ∧
            piColumn piChar j' ≠ piColumn piChar j) ∧
      (∃ v : Section1.CoeffVector (equalDegreeColumnIndex piChar j0 k), v ≠ 0 ∧
        Section1.supportedOn
          (Section1.evalCoeff
            (fun t : equalDegreeColumnIndex piChar j0 k => piColumn piChar t.1) v) A) := by
  have h42 : Section4.hypothesis_4_2_statement K W1 W2 W := h46.1
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    hypothesis_3_1_of_hypothesis_4_6_pf45 h46
  have hKnorm : K.Normal := normal_K_of_hypothesis_4_2_pf45 h42
  let : K.Normal := hKnorm
  have hconj :
      ∀ j, j ∈ equalDegreeColumnSet piChar j0 k →
        ∃ j', j' ∈ equalDegreeColumnSet piChar j0 k ∧
          Section1.conjugateCharacter (piColumn piChar j) = piColumn piChar j' ∧
            piColumn piChar j' ≠ piColumn piChar j := by
    intro j hj
    have hj0 : j ≠ j0 := hj.1
    rcases conjugate_omega_baseRow_ne_pf45
        (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (ω := ω) h31 hω hj0 with
      ⟨j', hbarOmega, hj'ne⟩
    have hj'0 : j' ≠ j0 := by
      intro hj'0
      have hbar0 :
          Section1.conjugateCharacter (ω i0 j) = Section1.principalCharacter W := by
        simpa [hj'0, hω.principal] using hbarOmega
      have hprincipal : ω i0 j = Section1.principalCharacter W := by
        ext x
        have hx := congrFun hbar0 x
        simpa [Section1.conjugateCharacter, Section1.principalCharacter] using congrArg star hx
      exact hj0 ((hω.pairwise_eq (i := i0) (i' := i0) (j := j) (j' := j0)
        (by simpa [hω.principal] using hprincipal)).2)
    have hbarBase :
        Section1.conjugateCharacter (piChar i0 j) = piChar i0 j' :=
      conjugate_piChar_baseRow_eq_of_conjugate_omega_pf45
        (W1 := W1) (W2 := W2) (W := W)
        (i0 := i0) (j0 := j0) (ω := ω) (σ := σ)
        (piChar := piChar) (deltaSign := deltaSign)
        h31 hω h43b h43c hbarOmega
    have hbarCol :
        Section1.conjugateCharacter (piColumn piChar j) = piColumn piChar j' :=
      conjugate_piColumn_eq_pf45 K piChar xChar h45a hbarBase
    have hj'deg :
        Section1.degree (piColumn piChar j') = Section1.degree (piColumn piChar j) := by
      rcases degree_piColumn_eq_nat_pf45 K piChar xChar h45a j with ⟨n, hn⟩
      have hn1 : piColumn piChar j 1 = (n : ℂ) := by
        simpa [Section1.degree] using hn
      have hdegBar :
          Section1.degree (Section1.conjugateCharacter (piColumn piChar j)) =
            Section1.degree (piColumn piChar j) := by
        calc
          Section1.degree (Section1.conjugateCharacter (piColumn piChar j)) =
              star (piColumn piChar j 1) := by
                rfl
          _ = star (n : ℂ) := by rw [hn1]
          _ = (n : ℂ) := by simp
          _ = Section1.degree (piColumn piChar j) := by simpa [Section1.degree] using hn.symm
      simpa [hbarCol] using hdegBar
    have hj'mem : j' ∈ equalDegreeColumnSet piChar j0 k := by
      exact ⟨hj'0, hj'deg.trans hj.2⟩
    have hneqCol : piColumn piChar j' ≠ piColumn piChar j := by
      intro hEq
      have hleft :
          Section1.scalarProduct L (piColumn piChar j') (piChar i0 j) = 0 := by
        have hinner := scalarProduct_piColumn_entry_eq_ite_pf45
          (W1 := W1) (W2 := W2) (W := W)
          (i0 := i0) (j0 := j0) (ω := ω) (σ := σ)
          (piChar := piChar) (deltaSign := deltaSign)
          (hω := hω) (j := j') (k := j)
          (h43b := h43b)
        simpa [hj'ne] using hinner
      have hright :
          Section1.scalarProduct L (piColumn piChar j) (piChar i0 j) = 1 := by
        simpa using scalarProduct_piColumn_entry_eq_ite_pf45
          (W1 := W1) (W2 := W2) (W := W)
          (i0 := i0) (j0 := j0) (ω := ω) (σ := σ)
          (piChar := piChar) (deltaSign := deltaSign)
          (hω := hω) (j := j) (k := j)
          (h43b := h43b)
      have hEqInner :
          Section1.scalarProduct L (piColumn piChar j') (piChar i0 j) =
            Section1.scalarProduct L (piColumn piChar j) (piChar i0 j) := by
        simp [hEq]
      rw [hright] at hEqInner
      have : (0 : ℂ) = 1 := hleft.symm.trans hEqInner
      exact zero_ne_one this
    exact ⟨j', hj'mem, hbarCol, hneqCol⟩
  intro hk0
  have hkmem : k ∈ equalDegreeColumnSet piChar j0 k := by
    exact ⟨hk0, rfl⟩
  rcases hconj k hkmem with ⟨j', hj'mem, _hbarCol, hneqCol⟩
  let : DecidableEq (equalDegreeColumnIndex piChar j0 k) := Classical.decEq _
  let tk : equalDegreeColumnIndex piChar j0 k := ⟨k, hkmem⟩
  let tj' : equalDegreeColumnIndex piChar j0 k := ⟨j', hj'mem⟩
  refine ⟨hconj, ?_⟩
  refine ⟨Section1.signedBasisDifference 1 tj' tk, ?_, ?_⟩
  · intro hv0
    have hknej' : k ≠ j' := by
      intro hEq
      apply hneqCol
      simp [hEq]
    have hval :=
      congrArg (fun v : Section1.CoeffVector (equalDegreeColumnIndex piChar j0 k) => v tk) hv0
    have htkneq : tk ≠ tj' := by
      intro hEq
      exact hknej' (congrArg Subtype.val hEq)
    have htk : Section1.basisVector tk tk = (1 : Int) := by
      simp [Section1.basisVector]
    have htj : Section1.basisVector tj' tk = (0 : Int) := by
      simp [Section1.basisVector, htkneq]
    have hzero : (0 : Int) = 1 := by
      simpa [Section1.signedBasisDifference, htk, htj] using hval.symm
    exact (by norm_num : (0 : Int) ≠ 1) hzero
  · have hkSupp : Section1.supportedOn (piColumn piChar k) (withOne A) :=
      (theorem_4_7_nonbase_column_data_pf45
        K W1 W2 W H A i0 j0 ω σ piChar xChar deltaSign
        h46 h45a hω h43b h43c h47 k hk0).2.2
    have hj'Supp : Section1.supportedOn (piColumn piChar j') (withOne A) :=
      (theorem_4_7_nonbase_column_data_pf45
        K W1 W2 W H A i0 j0 ω σ piChar xChar deltaSign
        h46 h45a hω h43b h43c h47 j' hj'mem.1).2.2
    have hdegEq :
        Section1.degree (piColumn piChar k) = Section1.degree (piColumn piChar j') :=
      hj'mem.2.symm
    have hdiff :
        Section1.supportedOn (piColumn piChar k - piColumn piChar j') A :=
      supportedOn_diff_of_supportedOn_withOne_and_equal_degree_pf45
        A hkSupp hj'Supp hdegEq
    simpa [tk, tj'] using
      (show Section1.supportedOn
        (Section1.evalCoeff
          (fun t : equalDegreeColumnIndex piChar j0 k => piColumn piChar t.1)
          (Section1.signedBasisDifference 1 tj' tk)) A from by
        rw [Section1.evalCoeff_signedBasisDifference]
        simpa [Section1.signIntToComplex] using hdiff)

public theorem theorem_4_9_a
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I)
    (j0 k : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (h46 : hypothesis_4_6_statement K W1 W2 W H A)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h47 : theorem_4_7_statement K H A) :
    theorem_4_9_a_statement A j0 k piChar := by
  intro hk0
  have h46' := h46
  have hcore :=
    theorem_4_9_a_core_pf45
      K W1 W2 W H A i0 j0 ω σ k piChar xChar deltaSign
      h46' h45a hω h43b h43c h47 hk0
  rcases h46 with ⟨_h42, _hHnorm, _hW2H, _hHK, _hcentA, hAinK⟩
  have hA_punct : A ⊆ puncturedSet := by
    intro x hxA
    exact (hAinK hxA).2
  refine ⟨hcore.1, hcore.2, ?_⟩
  intro v
  have hcols :
      ∀ t : equalDegreeColumnIndex piChar j0 k,
        Section1.supportedOn (piColumn piChar t.1) (withOne A) := by
    intro t
    exact (theorem_4_7_nonbase_column_data_pf45
      K W1 W2 W H A i0 j0 ω σ piChar xChar deltaSign
      h46' h45a hω h43b h43c h47 t.1 t.2.1).2.2
  have hvWithOne :
      Section1.supportedOn
        (Section1.evalCoeff
          (fun t : equalDegreeColumnIndex piChar j0 k => piColumn piChar t.1) v)
        (withOne A) := by
    exact supportedOn_evalCoeff_of_supportedOn_pf45
      (fun t : equalDegreeColumnIndex piChar j0 k => piColumn piChar t.1)
      (withOne A) hcols v
  exact supportedOn_punctured_iff_supportedOn_of_supportedOn_withOne_pf45
    A hA_punct hvWithOne

private theorem isVirtualCharacter_zero_pf45
    {G : Type u} [Group G] [Finite G] :
    Theory.Character.IsVirtualCharacter (0 : ClassFunction G) := by
  simpa using
    (Section3.isVirtualCharacter_sub
      (G := G)
      (χ := Section1.principalCharacter G)
      (ψ := Section1.principalCharacter G)
      Section3.isVirtualCharacter_principalCharacter
      Section3.isVirtualCharacter_principalCharacter)

private theorem isVirtualCharacter_finset_sum_pf45
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} (s : Finset ι)
    (Φ : ι → ClassFunction G)
    (hΦ : ∀ i ∈ s, Theory.Character.IsVirtualCharacter (Φ i)) :
    Theory.Character.IsVirtualCharacter (s.sum Φ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (isVirtualCharacter_zero_pf45 (G := G))
  | @insert a s ha ih =>
      have ha' : Theory.Character.IsVirtualCharacter (Φ a) :=
        hΦ a (Finset.mem_insert_self a s)
      have hs' : Theory.Character.IsVirtualCharacter (s.sum Φ) := by
        exact ih (by
          intro i hi
          exact hΦ i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using Section3.isVirtualCharacter_add ha' hs'

private theorem isVirtualCharacter_fintype_sum_pf45
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Fintype ι]
    (Φ : ι → ClassFunction G)
    (hΦ : ∀ i, Theory.Character.IsVirtualCharacter (Φ i)) :
    Theory.Character.IsVirtualCharacter (∑ i, Φ i) := by
  classical
  exact isVirtualCharacter_finset_sum_pf45
    (G := G) (s := Finset.univ) Φ (by
      intro i _hi
      exact hΦ i)

private theorem isVirtualCharacter_intCast_smul_pf45
    {G : Type u} [Group G]
    (n : ℤ) {χ : ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter ((n : ℂ) • χ) := by
  classical
  rcases hχ with ⟨r, m, d, ρ, rfl⟩
  refine ⟨r, fun i => n * m i, d, ρ, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

private theorem isVirtualCharacter_sign_smul_pf45
    {G : Type u} [Group G]
    {ε : ℂ} {χ : ClassFunction G}
    (hε : Section1.IsSign ε)
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (ε • χ) := by
  rcases hε with rfl | rfl
  · simpa using hχ
  · simpa using Section3.isVirtualCharacter_neg hχ

private theorem omegaColumnSigma_isVirtualCharacter_pf45
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (hσvirt : ∀ α : ClassFunction W, Theory.Character.IsVirtualCharacter α →
      Theory.Character.IsVirtualCharacter (σ α))
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (j : J) :
    Theory.Character.IsVirtualCharacter (omegaColumnSigma σ ω j) := by
  unfold omegaColumnSigma
  exact isVirtualCharacter_fintype_sum_pf45
    (fun i => σ (ω i j))
    (by
      intro i
      exact hσvirt (ω i j)
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
          (hω.irreducible i j)))

private theorem evalCoeff_isVirtualCharacter_pf45
    {G : Type u} [Group G] [Finite G]
    {J : Type*} [Fintype J]
    (mu : J → ClassFunction G)
    (v : Section1.CoeffVector J)
    (hmu : ∀ j, Theory.Character.IsVirtualCharacter (mu j)) :
    Theory.Character.IsVirtualCharacter (Section1.evalCoeff mu v) := by
  unfold Section1.evalCoeff
  exact isVirtualCharacter_fintype_sum_pf45
    (fun j => ((v j : ℂ) • mu j))
    (by
      intro j
      exact isVirtualCharacter_intCast_smul_pf45 (v j) (hmu j))

public theorem theorem_4_9_b_lands_in_zIrr
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (_K W1 W2 W : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    [DecidableEq I]
    (i0 : I)
    (j0 k : J)
    (ω : I → J → ClassFunction W)
    (σL : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (hσvirt : ∀ α : ClassFunction W, Theory.Character.IsVirtualCharacter α →
      Theory.Character.IsVirtualCharacter (σ α))
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω) :
    theorem_4_9_b_lands_in_zIrr_statement j0 k W ω σ piChar deltaSign := by
  intro _hk0 v
  rcases h43b with ⟨_hsigmaL, hsign, _hirr, _hdistinct, _hind, _hSigmaL⟩
  exact evalCoeff_isVirtualCharacter_pf45
    (fun t : equalDegreeColumnIndex piChar j0 k =>
      deltaSign k • omegaColumnSigma σ ω t.1) v
    (by
      intro t
      exact isVirtualCharacter_sign_smul_pf45 (hsign k)
        (omegaColumnSigma_isVirtualCharacter_pf45
          (W1 := W1) (W2 := W2) (W := W) (i0 := i0) (j0 := j0)
          ω σ hσvirt hω t.1))

public theorem theorem_4_9_b
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (K W1 W2 W : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    [DecidableEq I]
    (i0 : I)
    (j0 k : J)
    (ω : I → J → ClassFunction W)
    (σL : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G)
    (hσiso : ∀ α β, Section1.scalarProduct G (σ α) (σ β) =
      Section1.scalarProduct W α β)
    (h45a : theorem_4_5_a_statement K piChar xChar)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h49a : theorem_4_9_a_statement A j0 k piChar)
    (h48 : theorem_4_8_statement (W2 := W2) (W := W) A j0 ω σ piChar deltaSign τ) :
    theorem_4_9_b_statement A j0 k W ω σ piChar deltaSign τ := by
  intro hk0
  have hAiff := h49a hk0
  rcases h43b with ⟨hsigmaL, hsign, hirr, hdistinct, _hind, _hSigmaL⟩
  let T := equalDegreeColumnIndex piChar j0 k
  refine ⟨?_, ?_⟩
  · intro v w
    let muG : T → ClassFunction G := fun t => deltaSign k • omegaColumnSigma σ ω t.1
    let muL : T → ClassFunction L := fun t => piColumn piChar t.1
    exact scalarProduct_evalCoeff_eq_of_gram_eq muG muL
      (by
        intro t u
        dsimp [muG, muL]
        calc
          Section1.scalarProduct G
              (deltaSign k • omegaColumnSigma σ ω t.1)
              (deltaSign k • omegaColumnSigma σ ω u.1) =
              if t.1 = u.1 then (Fintype.card I : ℂ) else 0 := by
                exact scalarProduct_omegaColumnSigma_eq_card_ite_pf45
                  i0 j0 ω σ deltaSign hω hσiso hsign k t.1 u.1
          _ = Section1.scalarProduct L (piColumn piChar t.1) (piColumn piChar u.1) := by
                symm
                exact scalarProduct_piColumn_eq_card_ite_pf45
                  i0 j0 ω σL piChar deltaSign hω
                  ⟨hsigmaL, hsign, hirr, hdistinct, _hind, _hSigmaL⟩ t.1 u.1)
      v w
  · intro v hvA
    let tk : T := ⟨k, ⟨hk0, rfl⟩⟩
    let muL : T → ClassFunction L := fun t => piColumn piChar t.1
    let muG : T → ClassFunction G := fun t => deltaSign k • omegaColumnSigma σ ω t.1
    have hvPunct :
        Section1.supportedOn (Section1.evalCoeff muL v) puncturedSet := (hAiff.2.2 v).2 hvA
    have hsum0 : ∑ t : T, (v t : ℂ) = 0 :=
      coeff_sum_complex_zero_of_supportedOn_punctured_equalDegree_evalCoeff_pf45
        K j0 k piChar xChar h45a v hvPunct
    have hEvalL :
        Section1.evalCoeff muL v =
          Section1.evalCoeff (fun t => muL t - muL tk) v :=
      evalCoeff_eq_evalCoeff_sub_base_of_coeff_sum_zero_pf45 muL tk v hsum0
    have hEvalG :
        Section1.evalCoeff muG v =
          Section1.evalCoeff (fun t => muG t - muG tk) v :=
      evalCoeff_eq_evalCoeff_sub_base_of_coeff_sum_zero_pf45 muG tk v hsum0
    calc
      τ (Section1.evalCoeff muL v)
          = τ (Section1.evalCoeff (fun t => muL t - muL tk) v) := by rw [hEvalL]
      _ = Section1.evalCoeff (fun t => τ (muL t - muL tk)) v := by
            unfold Section1.evalCoeff
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro t _ht
            simp
      _ = Section1.evalCoeff
            (fun t => deltaSign k • (omegaColumnSigma σ ω t.1 - omegaColumnSigma σ ω k)) v := by
            apply congrArg (fun f => Section1.evalCoeff f v)
            funext t
            dsimp [muL, tk]
            exact tau_piColumn_sub_eq_signed_omegaColumnSigma_sub_pf45
              K W2 W A i0 j0 k ω σ piChar xChar deltaSign τ h45a h48 hk0 t.2
      _ = Section1.evalCoeff (fun t => muG t - muG tk) v := by
            refine congrArg (fun f => Section1.evalCoeff f v) ?_
            funext t
            dsimp [muG, tk]
            simp [smul_sub]
      _ = Section1.evalCoeff muG v := hEvalG.symm


public theorem theorem_4_10
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    {W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (W1 W2 : Subgroup L)
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σL : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (hτσ : tau_agrees_on_cyclicTI_induced_statement W1 W2 W σ τ) :
    theorem_4_10_statement i0 j0 ω σ piChar deltaSign τ := by
  exact theorem_4_10_formula_pf45
    W1 W2 i0 j0 ω σL σ piChar deltaSign τ hω h43b hτσ

end CFSG.Section4Scratch
