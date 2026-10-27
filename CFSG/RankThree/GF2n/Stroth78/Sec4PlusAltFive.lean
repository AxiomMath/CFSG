module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusEight
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusAltNumerics
public import CFSG.LargeExtraspecial.A2ModPLPairing

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusEightU33
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.LargeExtraspecial.A2Mod
  (A2Action IsPointMaps commSpaceOf commSpace_le_commSpaceOf transvectionSet)

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem false_of_w_eq_five_of_isPointMaps
    (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hZ : Nat.card ↥(ZQ z) = 4)
    (e : ↥(Xsub S a) ≃* alternatingGroup (Fin 8))
    {Ψ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* ↥(Xsub S a)}
    {P Pd : (Fin 4 → ZMod 2) →ₗ[ZMod 2] Additive (QbarOf S)} (hΨ : Function.Surjective Ψ)
    (hA : A2Action (transvectionSet 4 (ZMod 2)) (qS S) ((rhoX S a).comp Ψ))
    (hP : IsPointMaps ((rhoX S a).comp Ψ) (qS S) P Pd) (hw5 : w = 5) : False := by
  classical
  letI := modAbF S
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  obtain ⟨-, hLi, hIle, hLb, hD2⟩ := card_Lbar_numerics_of_mulEquiv_alt8 S h h217 h34 hZ e
  subst hw5
  set C : Subgroup (Hbar z) := Subgroup.centralizer (Xsub S a : Set (Hbar z)) with hCdef
  have hIle' : Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) ≤ 32 := by simpa using hIle
  have hLi' : Nat.card ↥(Lbar S a) * Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) = 1024 := by
    rw [hLi]
    norm_num
  have hLge : 32 ≤ Nat.card ↥(Lbar S a) := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card ↥(Lbar S a) * Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) ≤
        Nat.card ↥(Lbar S a) * 32 := Nat.mul_le_mul_left _ hIle'
    omega
  have hLC : 2 ≤ Nat.card ↥(Lbar S a ⊓ C) := by
    by_contra hlt
    push Not at hlt
    omega
  have hne : Lbar S a ⊓ C ≠ ⊥ := by
    intro hbot
    rw [hbot] at hLC
    simp at hLC
  obtain ⟨⟨r, hrLC⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hr1' : r ≠ 1 := fun h1 => hr1 (Subtype.ext h1)
  have hrL : r ∈ Lbar S a := (Subgroup.mem_inf.mp hrLC).1
  have hrC : r ∈ C := (Subgroup.mem_inf.mp hrLC).2
  have hrr : r * r = 1 := by
    rw [← pow_two]
    exact sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj hrL
  set t : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S) := rhoLin S r with ht
  have hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup (qS S) := (rhoBar S r).2
  have htt : t * t = 1 := by
    rw [ht, ← rhoLin_mul, hrr]
    exact LinearEquiv.ext fun v => by simp [rhoLin]
  have ht1 : t ≠ 1 := by
    intro h1
    apply hr1'
    apply rhoLin_injective S
    rw [← ht, h1]
    exact (LinearEquiv.ext fun v => by simp [rhoLin]).symm
  set W : Submodule (ZMod 2) (Additive (QbarOf S)) :=
    LinearMap.range P ⊔ LinearMap.range Pd with hW
  have hdim : finrank (ZMod 2) (Additive (QbarOf S)) = 10 := by
    rw [finrank_QbarOf_eq_two_mul S h.card_F]
  have hdim16 : finrank (ZMod 2) (Additive (QbarOf S)) < 16 := by omega
  have hc : ∀ g, t * ((rhoX S a).comp Ψ) g = ((rhoX S a).comp Ψ) g * t := by
    intro g
    rw [MonoidHom.comp_apply, rhoX_apply, ht]
    have hcomm : ((Ψ g : ↥(Xsub S a)) : Hbar z) * r = r * ((Ψ g : ↥(Xsub S a)) : Hbar z) :=
      Subgroup.mem_centralizer_iff.mp hrC _ (Ψ g).2
    show rhoLin S r * rhoLin S ↑(Ψ g) = rhoLin S ↑(Ψ g) * rhoLin S r
    rw [← rhoLin_mul, ← rhoLin_mul, hcomm]
  have hfix := hP.apply_eq_self_of_commute hc
  obtain ⟨⟨α, hαR⟩, hα1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα1' : α ≠ 1 := fun h1 => hα1 (Subtype.ext h1)
  have hαX : α ∈ Xsub S a := h.Rbar_le_Xsub hαR
  have hãW : aVec S h.mem_Q ∈ W := by
    have hmem := aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
      h.centerIn_Qa_not_le_Q hαR hα1'
    have h1 : aVec S h.mem_Q ∈ commSpaceOf (rhoX S a) ⊤ := by
      refine commSpace_le_commSpaceOf (rhoX S a) (Subgroup.mem_top (⟨α, hαX⟩ : ↥(Xsub S a))) ?_
      rw [rhoX_apply]
      exact hmem
    rw [← MonoidHom.range_eq_top.mpr hΨ, CFSG.LargeExtraspecial.A2Mod.commSpaceOf_range,
      hP.commSpaceOf_top] at h1
    exact h1
  set Wo : Submodule (ZMod 2) (Additive (QbarOf S)) :=
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (qS S)) W with hWo
  have hnd : (QuadraticMap.polarBilin (qS S)).Nondegenerate := hA.nondegenerate
  have hsup : W ⊔ Wo = ⊤ := hP.sup_orthogonal_eq_top hA hdim16
  have hWo_dim : finrank (ZMod 2) ↥Wo = 2 := by
    rw [hWo, LinearMap.BilinForm.finrank_orthogonal hnd, hW, hP.finrank_range_sup, hdim]
  have hcomm_le : commSpace t ≤ Wo := by
    intro x hx
    obtain ⟨y, rfl⟩ := mem_commSpace.mp hx
    rw [hWo, LinearMap.BilinForm.mem_orthogonal_iff]
    intro x' hx'
    show QuadraticMap.polar (qS S) x' (t y - y) = 0
    have h1 : QuadraticMap.polar (qS S) x' (t y) = QuadraticMap.polar (qS S) (t x') (t y) := by
      rw [hfix x' hx']
    rw [QuadraticMap.polar_sub_right, h1,
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO, sub_self]
  have hI0 : ∀ v ∈ QaInterImage S (Q z ⊓ QaOf a), qS S v = 0 := by
    intro v hv
    obtain ⟨y, hyB, hyv⟩ := (mem_QaInterImage_iff S).mp hv
    have hv' : v = Additive.ofMul (mkQbar S y) := (congrArg Additive.ofMul hyv).symm
    rw [hv']
    exact (q_eq_zero_iff S y).mpr (sq_eq_one_of_mem_QaOf_inf_Q S h
      (by rw [inf_comm]; exact hyB))
  have hzero : ∀ x ∈ commSpace t, qS S x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := mem_commSpace.mp hx
    obtain ⟨xW, hxW, u, hu, hyu⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top : y ∈ W ⊔ Wo)
    have htxW := hfix xW hxW
    have heq : t y - y = t u - u := by
      rw [← hyu, map_add, htxW]
      abel
    rw [heq]
    have hu' : u ∈ QaInterImage S (Q z ⊓ Subgroup.centralizer ({a} : Set G)) := by
      rw [QaInterImage_CQ_eq_orthogonal S h.mem_Q]
      exact LinearMap.BilinForm.orthogonal_le
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hãW)) hu
    exact hI0 _ (commutator_Lbar_CQ_le S r hrL u hu')
  have hev := even_finrank_commSpace_of_forall_eq_zero hnd hO htt hzero
  have hne0 : commSpace t ≠ ⊥ := fun h0 =>
    ht1 (CFSG.LargeExtraspecial.A2Mod.commSpace_eq_bot_iff.mp h0)
  have hpos : 0 < finrank (ZMod 2) ↥(commSpace t) := by
    rcases Nat.eq_zero_or_pos (finrank (ZMod 2) ↥(commSpace t)) with h0 | h0
    · exact absurd (Submodule.finrank_eq_zero.mp h0) hne0
    · exact h0
  have hle2 : finrank (ZMod 2) ↥(commSpace t) ≤ 2 :=
    (Submodule.finrank_mono hcomm_le).trans hWo_dim.le
  have heq2 : finrank (ZMod 2) ↥(commSpace t) = 2 := by
    obtain ⟨k, hk⟩ := hev
    omega
  have hCW : commSpace t = Wo :=
    Submodule.eq_of_le_of_finrank_eq hcomm_le (by rw [heq2, hWo_dim])
  have hWo_ne : Wo ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hWo_dim
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWo_ne
  have hrad : ∀ y, QuadraticMap.polar (qS S) u y = 0 := by
    intro y
    obtain ⟨xW, hxW, u', hu', rfl⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top : y ∈ W ⊔ Wo)
    rw [QuadraticMap.polar_add_right]
    have h1 : QuadraticMap.polar (qS S) u xW = 0 := by
      rw [QuadraticMap.polar_comm]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hu) xW hxW
    have h2 : QuadraticMap.polar (qS S) u u' = 0 := by
      rw [← hCW] at hu hu'
      exact polar_commSpace_eq_zero hO htt hu hu'
    rw [h1, h2, add_zero]
  exact hu0 (hnd.1 u (fun y => hrad y))

end CFSG.RankThree.GF2n.Stroth78
