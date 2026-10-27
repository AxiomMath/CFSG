module

public import CFSG.RankThree.GF2n.Stroth78.Sec1One

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFixedSq
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusZQFour
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusPerfect
import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeLift
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.ClassicalGroups.Alternating.BinaryPointFix
import CFSG.LinearAlgebra.F2PlaneMaps

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module CFSG.ClassicalGroups.Symplectic
open CFSG.ClassicalGroups.Alternating CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}


theorem not_lieModel_psp_of_card_ZQ_eq_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hZ : Nat.card ↥(ZQ z) = 4) {m : ℕ} (hm : 4 ≤ m) :
    ¬ CFSG.Blueprint.LieModel ↥(Xsub S a) .PSp m 2 1 := by
  intro hX
  classical
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  obtain ⟨Q₁, Q₂, φ, π, -, hQ₂, hQ₁, hsurj, hker, hπ, -⟩ :=
    exists_naturalSeries_psp S h h217 h34 hm hX
  have hD := rootClass_Xsub S h h217 h34
  have hA := a2Action_Xsub S a
  have hZX := rhoZ_eq_self_of_mem_Xsub_of_card_ZQ_eq_four S h h217 h34 hZ
  have hR2 := card_Rbar_eq_two_of_card_ZQ_eq_four S h hZ
  have hodd3 : ∀ n : ℕ, n ∣ 3 → Odd n := fun n hn => by
    rcases (Nat.dvd_prime Nat.prime_three).mp hn with rfl | rfl <;> decide
  obtain ⟨⟨α, hαR⟩, hα1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα1 : α ≠ 1 := fun h1 => hα1' (Subtype.ext h1)
  set α' : ↥(Xsub S a) := ⟨α, h.Rbar_le_Xsub hαR⟩ with hα'
  have hαD : α' ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) :=
    Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hαR hα1)
  set aT := aVec S h.mem_Q with haT
  have haL : aT ∈ commSpace (rhoX S a α') := (mem_A2set_and_aVec_mem_of_mem_Rbar h hαR hα1).2
  have hcQ : ∀ (x : ↥(Xsub S a)) {v}, v ∈ commSpace (rhoX S a x) → v ∈ Q₂ := fun x _ hv =>
    hQ₂ (CFSG.LargeExtraspecial.A2Mod.commSpace_le_commSpaceOf (rhoX S a) (Subgroup.mem_top x) hv)
  have haQ₂ : aT ∈ Q₂ := hcQ α' haL
  have hcommα : ∀ y : ↥(Xsub S a), Odd (orderOf y) → rhoX S a y aT = aT →
      y * α' = α' * y := by
    intro y hy hfix
    have hYX : Subgroup.closure {(y : Hbar z)} ≤ Xsub S a :=
      (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr y.2)
    have hYfix : ∀ t ∈ Subgroup.closure {(y : Hbar z)}, rhoLin S t aT = aT := by
      intro t ht
      induction ht using Subgroup.closure_induction with
      | mem t ht =>
        rw [Set.mem_singleton_iff.mp ht]
        exact hfix
      | one => rw [rhoLin, map_one]; rfl
      | mul t s _ _ ht hs => rw [rhoLin_mul, LinearEquiv.mul_apply, hs, ht]
      | inv t _ ht =>
        rw [rhoLin_inv]
        calc (rhoLin S t)⁻¹ aT = (rhoLin S t)⁻¹ (rhoLin S t aT) := by rw [ht]
          _ = aT := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    have hyC := mem_CHbar_of_odd_orderOf S h.mem_Q hYfix (fun t ht => hZX t (hYX ht))
      (Subgroup.subset_closure rfl) (by rwa [Subgroup.orderOf_coe])
    exact Subtype.ext (commute_of_mem_CHbar_of_card_Rbar_eq_two S a hR2 hαR hα1 hyC)
  have hv₀ : π aT ≠ 0 := by
    intro h0
    have hQ1 : aT ∈ Q₁ := by
      rw [← hker]
      exact ⟨haQ₂, h0⟩
    have hle := le_CHbar_of_perfect S h.mem_Q (commutator_Xsub_eq_of_threeFourPlus S h h217 h34)
      (fun y hy => hQ₁ ⟨y, hy⟩ aT hQ1) hZX
    have hcen : α' ∈ Subgroup.center ↥(Xsub S a) := Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (commute_of_mem_CHbar_of_card_Rbar_eq_two S a hR2 hαR hα1 (hle g.2))
    rw [hD.2.2.1, Subgroup.mem_bot] at hcen
    exact hα1 (congrArg Subtype.val hcen)
  have haT0 : aT ≠ 0 := fun h0 => hv₀ (by rw [h0, map_zero])
  set B := spForm m (ZMod 2) with hB_def
  have hBa : B.IsAlt := spForm_isAlt
  have hBn : B.Nondegenerate := spForm_nondegenerate
  set ψ : ↥(Xsub S a) ≃* Gsp B := φ.trans spEquiv with hψ_def
  have hψπ : ∀ x, ∀ v ∈ Q₂, π (rhoX S a x v) =
      ((ψ x : LinearMap.GeneralLinearGroup (ZMod 2) (Fin m ⊕ Fin m → ZMod 2)) :
        (Fin m ⊕ Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)) (π v) := by
    intro x v hv
    rw [hπ x v hv]
    rfl
  have hC : ∀ g ∈ bilinIsometryGroup B, g ^ 3 = 1 →
      (g : (Fin m ⊕ Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)) (π aT) = π aT →
      ∀ ℓ ∈ commSpace (rhoX S a α'),
        (g : (Fin m ⊕ Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)) (π ℓ) = π ℓ := by
    intro g hg hg3 hgv ℓ hℓ
    set y := ψ.symm ⟨g, hg⟩ with hy_def
    have hψy : ψ y = ⟨g, hg⟩ := ψ.apply_symm_apply _
    have hy3 : y ^ 3 = 1 := ψ.injective (by rw [map_pow, hψy, map_one]; exact Subtype.ext hg3)
    have hyfix : rhoX S a y aT = aT := by
      set q := rhoX S a y aT - aT with hq_def
      have hq : q ∈ Q₁ := by
        rw [← hker]
        refine ⟨hcQ y (sub_mem_commSpace _ aT), ?_⟩
        show π (rhoX S a y aT - aT) = 0
        rw [map_sub, hψπ y aT haQ₂, hψy, sub_eq_zero]
        exact hgv
      have hfq : rhoX S a y q = q := hQ₁ y q hq
      have e1 : rhoX S a y aT = aT + q := by
        rw [hq_def]
        abel
      have h2 : rhoX S a (y ^ 2) aT = aT := by
        rw [pow_two, map_mul, LinearEquiv.mul_apply, e1, map_add, hfq, e1, add_assoc,
          ZModModule.add_self, add_zero]
      have h3 : rhoX S a (y ^ 3) aT = aT := by
        rw [hy3, map_one]
        rfl
      rwa [pow_succ', map_mul, LinearEquiv.mul_apply, h2] at h3
    have hcomm := hcommα y (hodd3 _ (orderOf_dvd_of_pow_eq_one hy3)) hyfix
    have hpres : ∀ v ∈ commSpace (rhoX S a α'), rhoX S a y v ∈ commSpace (rhoX S a α') := by
      intro v hv
      obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
      refine mem_commSpace.mpr ⟨rhoX S a y u, ?_⟩
      have hc : rhoX S a α' (rhoX S a y u) = rhoX S a y (rhoX S a α' u) := by
        rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, hcomm]
      rw [map_sub, hc]
    have hρodd : Odd (orderOf (rhoX S a y)) := by
      rw [orderOf_injective _ hA.2.1 y]
      exact hodd3 _ (orderOf_dvd_of_pow_eq_one hy3)
    have hfixL := CFSG.LinearAlgebra.apply_eq_self_of_odd_of_apply_eq (hA.isTypeA hαD).2.2.2.1
      hpres hρodd haL haT0 hyfix ℓ hℓ
    have := hψπ y ℓ (hcQ α' hℓ)
    rw [hfixL, hψy] at this
    exact this.symm
  have hτ : (ψ α' : LinearMap.GeneralLinearGroup (ZMod 2) (Fin m ⊕ Fin m → ZMod 2)) =
      binarySymplecticTransvection B hBa (π aT) := by
    refine BinaryPointFix.eq_transvection_of_forall_fix hBa hBn
      (by rw [finrank_spSpace]; omega) (ψ α').2 ?_ ?_ hv₀ ?_
    · rw [sq, ← Subgroup.coe_mul, ← map_mul, hD.mul_self hαD, map_one, Subgroup.coe_one]
    · intro h1
      apply hα1
      have : α' = 1 := ψ.injective (by rw [map_one]; exact Subtype.ext h1)
      exact congrArg Subtype.val this
    · intro g hg hg3 hgv x
      have hx : x ∈ Q₂.map π := by
        rw [hsurj]
        trivial
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
      have hAx : ((ψ α' : LinearMap.GeneralLinearGroup (ZMod 2) (Fin m ⊕ Fin m → ZMod 2)) :
          (Fin m ⊕ Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)) (π v) - π v =
          π (rhoX S a α' v - v) := by
        rw [map_sub, hψπ α' v hv]
      rw [hAx]
      exact hC g hg hg3 hgv _ (sub_mem_commSpace _ v)
  have hDτ : ∀ d ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)), ∃ b,
      (ψ d : LinearMap.GeneralLinearGroup (ZMod 2) (Fin m ⊕ Fin m → ZMod 2)) =
        binarySymplecticTransvection B hBa b := by
    intro d hd
    obtain ⟨d₀, -, hcl⟩ := hD.1.2.1
    obtain ⟨c, hc⟩ := isConj_iff.mp (((hcl α').mp hαD).symm.trans ((hcl d).mp hd))
    refine ⟨((ψ c : LinearMap.GeneralLinearGroup (ZMod 2) (Fin m ⊕ Fin m → ZMod 2)) :
      (Fin m ⊕ Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)) (π aT), ?_⟩
    rw [← hc, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hτ]
    exact BinarySymplecticTransvection.conj hBa (ψ c).2 (π aT)
  obtain ⟨d, hd, e, he, h4⟩ := hD.2.1
  obtain ⟨b₁, hb₁⟩ := hDτ d hd
  obtain ⟨b₂, hb₂⟩ := hDτ e he
  have h4' : orderOf (ψ (d * e) : LinearMap.GeneralLinearGroup (ZMod 2) (Fin m ⊕ Fin m → ZMod 2)) =
      4 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, h4]
  rw [map_mul, Subgroup.coe_mul, hb₁, hb₂] at h4'
  exact BinaryPointFix.orderOf_mul_ne_four hBa hBn b₁ b₂ h4'

end CFSG.RankThree.GF2n.Stroth78
