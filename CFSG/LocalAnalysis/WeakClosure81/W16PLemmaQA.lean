module

public import CFSG.LocalAnalysis.WeakClosure81.W16Setup
public import CFSG.RankThree.GF2n.Tim77.InvolAutD
import CFSG.CGT.Timmesfeld75.Sec3TwelveRho

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure CfgLemmaQ (M V₀ V : Subgroup G) (h : G) (C : Subgroup G) : Prop where
  hyp : Hyp15 M V₀ V
  not_isPGroup : ¬ IsPGroup 2 ↥(V₀ ⊔ conjSubgroup V₀ h)
  inf_ne_bot : V₀ ⊓ conjSubgroup M h ≠ ⊥
  le : C ≤ V
  le_sup : V ≤ C ⊔ V₀
  le_conj : C ≤ conjSubgroup M h
  le_centralizer : C ≤ centralizer ((conjSubgroup V₀ h ⊓ M : Subgroup G) : Set G)

namespace CfgLemmaQ

variable {M V₀ V C : Subgroup G} {h : G}

theorem prop24Setup (q : CfgLemmaQ M V₀ V h C) :
    CFSG.RankThree.GF2n.Tim77.Prop24Setup V₀ (conjSubgroup V₀ h) (nVSub V₀ h) (bSub V₀ h)
      (nVSub V₀ h ⊔ bSub V₀ h) := by
  have hnV : nVSub V₀ h = V₀ ⊓ conjSubgroup M h := by
    rw [nVSub, ← conjSubgroup_normalizer V₀ h, q.hyp.normalizer₀]
  refine CFSG.LocalAnalysis.WeakClosure81.prop24Setup (V := V₀) (g := h)
    q.hyp.elemAbelian₀ q.hyp.isTI ?_ ?_
  · rw [hnV]
    exact q.inf_ne_bot
  · intro hEq
    apply q.not_isPGroup
    have hN : V₀ ≤ Subgroup.normalizer (conjSubgroup V₀ h : Set G) :=
      (le_of_eq hEq.symm).trans inf_le_right
    have hV₀p : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup q.hyp.elemAbelian₀
    have hAbp : IsPGroup 2 (conjSubgroup V₀ h) := E3.isPGroup_conjSubgroup hV₀p h
    exact IsPGroup.to_sup_of_normal_right' hV₀p hAbp hN

private theorem mQuot_le_mSub_of_le {V U : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ≤ V) :
    E3.mQuot V U ≤ mSub V := by
  have h1 : Nat.card V = 2 ^ E3.mQuot V U * Nat.card U := E3.card_eq_two_pow_mul hV hUV
  have h2 : Nat.card V = 2 ^ mSub V := card_eq_two_pow_mSub hV
  have h3 : 2 ^ E3.mQuot V U ≤ 2 ^ mSub V := by
    rw [h2] at h1
    calc 2 ^ E3.mQuot V U = 2 ^ E3.mQuot V U * 1 := (mul_one _).symm
      _ ≤ 2 ^ E3.mQuot V U * Nat.card U := Nat.mul_le_mul_left _ Nat.card_pos
      _ = 2 ^ mSub V := h1.symm
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3

theorem false_of_le (h152 : Thm152 G) (q : CfgLemmaQ M V₀ V h C)
    (hm : 1 < mBar M V₀ V q.hyp.h6.elemAbelian)
    (hV : V ≤ V₀ ⊔ (V ⊓ centralizer ((V₀ ⊔ conjSubgroup V₀ h : Subgroup G) : Set G))) :
    False := by
  let X : Subgroup G := V₀ ⊔ conjSubgroup V₀ h
  let U' : Subgroup G := V ⊓ centralizer (X : Set G)
  have hV' : V ≤ V₀ ⊔ U' := hV
  have hVeq : V = V₀ ⊔ U' :=
    le_antisymm hV' (sup_le q.hyp.h6.le inf_le_left)
  have hU'V : U' ≤ V := inf_le_left
  have hXc : X ≤ Subgroup.centralizer (U' : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2) x hx).symm
  have hXnotM : ¬ X ≤ M := by
    intro hXM
    apply q.not_isPGroup
    have hAbM : conjSubgroup V₀ h ≤ M := le_sup_right.trans hXM
    have hN : conjSubgroup V₀ h ≤ Subgroup.normalizer (V₀ : Set G) := by
      rwa [← q.hyp.normalizer₀] at hAbM
    have hV₀p : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup q.hyp.elemAbelian₀
    have hAbp : IsPGroup 2 (conjSubgroup V₀ h) := E3.isPGroup_conjSubgroup hV₀p h
    exact IsPGroup.to_sup_of_normal_left' hV₀p hAbp hN
  have hU'C : ¬ Subgroup.centralizer (U' : Set G) ≤ M := fun h => hXnotM (hXc.trans h)
  have hV₀N : V₀ ≤ Subgroup.normalizer (U' : Set G) :=
    ((le_sup_left : V₀ ≤ X).trans hXc).trans (Subgroup.centralizer_le_normalizer _)
  have hrel : U'.relIndex (V₀ ⊔ U') = U'.relIndex V₀ :=
    B2F.relIndex_sup_eq_of_le_normalizer' hV₀N
  have hV₀p : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup q.hyp.elemAbelian₀
  have hbound : E3.mQuot V U' ≤ mSub V₀ := by
    have h1 : E3.mQuot V U' = E3.mQuot V₀ U' := by
      rw [hVeq]
      exact congrArg (padicValNat 2) hrel
    have h2 : E3.mQuot V₀ U' = E3.mQuot V₀ (V₀ ⊓ U') := by
      rw [inf_comm V₀ U']
      exact congrArg (padicValNat 2)
        (Subgroup.inf_relIndex_right (H := U') (K := V₀)).symm
    have h3 : E3.mQuot V₀ (V₀ ⊓ U') ≤ mSub V₀ :=
      mQuot_le_mSub_of_le hV₀p inf_le_left
    rw [h1, h2]
    exact h3
  have hr : rMV M V ≤ (mSub V₀ : ℕ∞) :=
    (rMV_le_mQuot M V U' hU'V hU'C).trans (by exact_mod_cast hbound)
  exact (not_lt.2 hr) (h152 q.hyp hm)

section Certified


theorem exists_mul_commutator_mem (q : CfgLemmaQ M V₀ V h C) {c : G} (hc : c ∈ C) :
    ∃ a ∈ V₀, a * c ∈ centralizer ((nVSub V₀ h ⊔ bSub V₀ h : Subgroup G) : Set G) ∧
      ∀ x ∈ V₀ ⊔ conjSubgroup V₀ h, x * (a * c) * x⁻¹ * (a * c)⁻¹ ∈ nVSub V₀ h ⊔ bSub V₀ h := by
  let A : Subgroup G := V₀
  let Ab : Subgroup G := conjSubgroup V₀ h
  let L : Subgroup G := nVSub V₀ h
  let Lb : Subgroup G := bSub V₀ h
  let Mm : Subgroup G := L ⊔ Lb
  have S : CFSG.RankThree.GF2n.Tim77.Prop24Setup A Ab L Lb Mm := q.prop24Setup
  obtain ⟨k, hkX, hkLb⟩ := CFSG.RankThree.GF2n.Tim77.sec34_exists_k S
  have hcV : c ∈ V := q.le hc
  have hcc : c * c = 1 := by
    rw [← sq]
    exact q.hyp.h6.elemAbelian.2 c hcV
  have hcA : c ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact B2F.isElemAbelian_comm q.hyp.h6.elemAbelian (q.hyp.h6.le ha) hcV
  have hLbeq : Lb = conjSubgroup V₀ h ⊓ M := by
    rw [show Lb = bSub V₀ h from rfl, bSub, q.hyp.normalizer₀]
  have hcLb : c ∈ Subgroup.centralizer (Lb : Set G) := by
    rw [hLbeq]
    exact q.le_centralizer hc
  have hcL : c ∈ Subgroup.centralizer (L : Set G) :=
    (Subgroup.centralizer_le S.L_le) hcA
  have hcMm : c ∈ Subgroup.centralizer (Mm : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hm
    have hlc : l * c = c * l := (Subgroup.mem_centralizer_iff.mp hcL l hl)
    have hlbc : lb * c = c * lb := (Subgroup.mem_centralizer_iff.mp hcLb lb hlb)
    calc (l * lb) * c = l * (lb * c) := by group
      _ = l * (c * lb) := by rw [hlbc]
      _ = (l * c) * lb := by group
      _ = (c * l) * lb := by rw [hlc]
      _ = c * (l * lb) := by group
  have hcN_Mm : c ∈ Subgroup.normalizer (Mm : Set G) :=
    Subgroup.centralizer_le_normalizer _ hcMm
  have hAbN : c ∈ Subgroup.normalizer (Ab : Set G) := by
    have hcConj : c ∈ conjSubgroup M h := q.le_conj hc
    have h' : conjSubgroup M h = Subgroup.normalizer (Ab : Set G) := by
      rw [← q.hyp.normalizer₀]
      exact conjSubgroup_normalizer V₀ h
    rwa [h'] at hcConj
  have hA_conj : A.map (MulAut.conj c).toMonoidHom = A :=
    CFSG.CGT.Timmesfeld75.mem_normalizer_iff_conjSubgroup_eq.mp
      (Subgroup.centralizer_le_normalizer _ hcA)
  have hAb_conj : Ab.map (MulAut.conj c).toMonoidHom = Ab :=
    CFSG.CGT.Timmesfeld75.mem_normalizer_iff_conjSubgroup_eq.mp hAbN
  have hX_T75 : CFSG.CGT.Timmesfeld75.conjSubgroup c (A ⊔ Ab) = A ⊔ Ab := by
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup, Subgroup.map_sup, hA_conj, hAb_conj]
  have hrel : 2 < L.relIndex A ∨ L.relIndex A = 2 := by
    have h0 : L.relIndex A ≠ 0 := E3.relIndex_ne_zero' A L
    have h1 : L.relIndex A ≠ 1 := by
      intro hone
      exact S.ne (le_antisymm S.L_le (Subgroup.relIndex_eq_one.1 hone))
    omega
  obtain ⟨a, ha, hinner⟩ : ∃ a ∈ A, ∀ x ∈ A ⊔ Ab,
      (a * c)⁻¹ * x⁻¹ * (a * c) * x ∈ Mm := by
    rcases hrel with hlt | heq
    · refine CFSG.RankThree.GF2n.Tim77.prop24Inner_holds G A Ab L Lb Mm S hlt c hX_T75 hcA ?_
      intro x _
      rw [hcc, inv_one, one_mul, mul_one, inv_mul_cancel]
      exact Mm.one_mem
    · exact CFSG.RankThree.GF2n.Tim77.prop24InnerD_holds G A Ab L Lb Mm S heq c hX_T75 hcA
  have hgN : a * c ∈ Subgroup.normalizer (Mm : Set G) :=
    Subgroup.mul_mem _ (S.A_le_normalizer_M ha) hcN_Mm
  have hconj : ∀ x ∈ A ⊔ Ab, x * (a * c) * x⁻¹ * (a * c)⁻¹ ∈ Mm := by
    intro x hx
    have hx' : x⁻¹ ∈ A ⊔ Ab := (A ⊔ Ab).inv_mem hx
    have hmem : (a * c)⁻¹ * x * (a * c) * x⁻¹ ∈ Mm := by
      simpa using hinner x⁻¹ hx'
    have hthis := (Subgroup.mem_normalizer_iff.mp hgN _).mp hmem
    have e : (a * c) * ((a * c)⁻¹ * x * (a * c) * x⁻¹) * (a * c)⁻¹ =
        x * (a * c) * x⁻¹ * (a * c)⁻¹ := by group
    rwa [e] at hthis
  have hXN : A ⊔ Ab ≤ Subgroup.normalizer (Mm : Set G) :=
    sup_le S.A_le_normalizer_M S.Ab_le_normalizer_M
  have hlτ : ∀ l ∈ L, (a * c) * l = l * (a * c) := by
    intro l hl
    have hla : a * l = l * a := S.comm_A ha (S.L_le hl)
    have hlc : c * l = l * c := (Subgroup.mem_centralizer_iff.mp hcA l (S.L_le hl)).symm
    rw [mul_assoc, hlc, ← mul_assoc, hla, mul_assoc]
  have hτC : a * c ∈ Subgroup.centralizer (Mm : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hm
    have hlbτ : (a * c) * lb = lb * (a * c) := by
      have hXM : ∀ x ∈ A ⊔ Ab, ∀ m ∈ Mm, x * m * x⁻¹ ∈ Mm :=
        fun x hx m hm => (Subgroup.mem_normalizer_iff.mp (hXN hx) m).mp hm
      have hb : ∀ x ∈ A ⊔ Ab, x⁻¹ * ((a * c) * x * (a * c)⁻¹) ∈ Mm := by
        intro x hx
        have h := hconj x⁻¹ ((A ⊔ Ab).inv_mem hx)
        rwa [inv_inv, show ((x⁻¹ * (a * c)) * x) * (a * c)⁻¹ =
          x⁻¹ * ((a * c) * x * (a * c)⁻¹) by group] at h
      have hlbmem : lb ∈ CFSG.CGT.Timmesfeld75.conjSubgroup k L := by
        rw [← hkLb]
        exact hlb
      have hl'mem : k⁻¹ * lb * k ∈ L :=
        (CFSG.CGT.Timmesfeld75.mem_conjSubgroup).mp hlbmem
      have hl'cent : k⁻¹ * lb * k ∈
          Mm ⊓ Subgroup.centralizer ({(a * c)} : Set G) :=
        ⟨S.L_le_M hl'mem,
          Subgroup.mem_centralizer_singleton_iff.2 (hlτ _ hl'mem).symm⟩
      have hres := CFSG.CGT.Timmesfeld75.inf_centralizer_conj_mem
        S.isElemAbelian_M hXM hb hkX hl'cent
      have hthis : lb * (a * c) = (a * c) * lb := by
        have hcomm := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.mp hres).2
        rwa [show k * (k⁻¹ * lb * k) * k⁻¹ = lb by group] at hcomm
      exact hthis.symm
    calc (l * lb) * (a * c) = l * (lb * (a * c)) := by group
      _ = l * ((a * c) * lb) := by rw [← hlbτ]
      _ = l * (a * c) * lb := by group
      _ = (a * c) * l * lb := by rw [← hlτ l hl]
      _ = (a * c) * (l * lb) := by group
  exact ⟨a, ha, hτC, hconj⟩

end Certified

end CfgLemmaQ

end CFSG.LocalAnalysis.WeakClosure81

end
