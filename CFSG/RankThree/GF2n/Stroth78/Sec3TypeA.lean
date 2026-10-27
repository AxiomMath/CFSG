module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Fifteen
import CFSG.LargeExtraspecial.OrthoF2Pairs57
import CFSG.LargeExtraspecial.S3bTenGeom

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem rhoBar_coe_eq_conjQbar (S : Setting z E F) (x : ↥(H z)) :
    (rhoBar S (QuotientGroup.mk x) :
      Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) = conjQbar S x := by
  rw [rhoBar_apply_mk, rho_apply_mk]

theorem conjQbar_eq_one_of_mem_Q (S : Setting z E F) {y : G} (hyH : y ∈ H z)
    (hyQ : y ∈ Q z) : conjQbar S ⟨y, hyH⟩ = 1 := by
  have hmem : (⟨y, hyH⟩ : ↥(H z)) ∈ (rho S).ker := by
    rw [rho_ker S]
    exact Subgroup.mem_subgroupOf.mpr hyQ
  have h1 : rho S ⟨y, hyH⟩ = 1 := MonoidHom.mem_ker.mp hmem
  simpa [rho_apply_mk] using congrArg Subtype.val h1

theorem conjQbar_zpow_eq_one_or_eq (S : Setting z E F) {x : G} (hxH : x ∈ H z)
    (hx2 : x ^ 2 ∈ Q z) (k : ℤ) :
    conjQbar S ⟨x ^ k, Subgroup.zpow_mem (H z) hxH k⟩ = 1 ∨
      conjQbar S ⟨x ^ k, Subgroup.zpow_mem (H z) hxH k⟩ = conjQbar S ⟨x, hxH⟩ := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    have hQ : x ^ (2 * m) ∈ Q z := by
      rw [zpow_mul]
      have h2 : x ^ (2 : ℤ) = x ^ 2 := zpow_natCast x 2
      rw [h2]
      exact zpow_mem hx2 m
    exact conjQbar_eq_one_of_mem_Q S (Subgroup.zpow_mem (H z) hxH _) hQ
  · right
    have hQ : x ^ (2 * m) ∈ Q z := by
      rw [zpow_mul]
      have h2 : x ^ (2 : ℤ) = x ^ 2 := zpow_natCast x 2
      rw [h2]
      exact zpow_mem hx2 m
    have hsplit : (⟨x ^ (2 * m + 1), Subgroup.zpow_mem (H z) hxH _⟩ : ↥(H z)) =
        ⟨x ^ (2 * m), Subgroup.zpow_mem (H z) hxH _⟩ * ⟨x, hxH⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
      rw [zpow_add, zpow_one]
    rw [hsplit, conjQbar_mul, conjQbar_eq_one_of_mem_Q S (Subgroup.zpow_mem (H z) hxH _) hQ,
      one_mul]

theorem conjQbar_eq_one_or_eq_of_mem_zpowers (S : Setting z E F) {x y : G} (hxH : x ∈ H z)
    (hx2 : x ^ 2 ∈ Q z) (hyH : y ∈ H z) (hy : y ∈ Subgroup.zpowers x) :
    conjQbar S ⟨y, hyH⟩ = 1 ∨ conjQbar S ⟨y, hyH⟩ = conjQbar S ⟨x, hxH⟩ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hsub : (⟨x ^ k, hyH⟩ : ↥(H z)) = ⟨x ^ k, Subgroup.zpow_mem (H z) hxH k⟩ :=
    Subtype.ext rfl
  rw [hsub]
  exact conjQbar_zpow_eq_one_or_eq S hxH hx2 k

theorem mem_commSpace_of_commutator_zpowers (S : Setting z E F) {x q y : G} (hxH : x ∈ H z)
    (hx2 : x ^ 2 ∈ Q z) (hq : q ∈ Q z) (hyH : y ∈ H z) (hy : y ∈ Subgroup.zpowers x) :
    Additive.ofMul (mkQbar S ⟨⁅q, y⁆, commutator_mem_Q_of_mem_H hyH hq⟩) ∈
      commSpace (conjQbar S ⟨x, hxH⟩) := by
  have h := additive_commutator_eq_sub S hyH hq
  rcases conjQbar_eq_one_or_eq_of_mem_zpowers S hxH hx2 hyH hy with h1 | h1
  · rw [h, h1]
    simp
  · rw [h, h1]
    exact sub_mem_commSpace (conjQbar S ⟨x, hxH⟩) _

theorem commSpace_le_QaInterImage_commutator_zpowers (S : Setting z E F) {x : G}
    (hxH : x ∈ H z) :
    commSpace (conjQbar S ⟨x, hxH⟩) ≤ QaInterImage S ⁅Q z, Subgroup.zpowers x⁆ := by
  intro v hv
  obtain ⟨q, rfl⟩ := (mem_commSpace_conjQbar_iff S hxH).mp hv
  exact (mem_QaInterImage_iff S).mpr
    ⟨⟨⁅(q : G), x⁆, commutator_mem_Q_of_mem_H hxH q.2⟩,
      Subgroup.commutator_mem_commutator q.2 (Subgroup.mem_zpowers x), rfl⟩

theorem mkQbar_mem_commSpace_of_mem_commutator_zpowers (S : Setting z E F) {x : G}
    (hxH : x ∈ H z) (hx2 : x ^ 2 ∈ Q z) {a : G}
    (ha : a ∈ ⁅Q z, Subgroup.zpowers x⁆) (haQ : a ∈ Q z) :
    Additive.ofMul (mkQbar S ⟨a, haQ⟩) ∈ commSpace (conjQbar S ⟨x, hxH⟩) := by
  let A : Subgroup G := ⁅Q z, Subgroup.zpowers x⁆
  have hA : A ≤ Q z := by
    rw [Subgroup.commutator_le]
    intro q hq y hy
    exact commutator_mem_Q_of_mem_H (Subgroup.zpowers_le.mpr hxH hy) hq
  have hset : A = Subgroup.closure
      {g : G | ∃ q ∈ Q z, ∃ y ∈ Subgroup.zpowers x, ⁅q, y⁆ = g} :=
    Subgroup.commutator_def _ _
  have hclass : ∀ a ∈ A, ∀ haQ : a ∈ Q z,
      Additive.ofMul (mkQbar S ⟨a, haQ⟩) ∈ commSpace (conjQbar S ⟨x, hxH⟩) := by
    intro a ha
    rw [hset] at ha
    induction ha using Subgroup.closure_induction with
    | mem g hg =>
        intro hgQ
        obtain ⟨q, hq, y, hy, rfl⟩ := hg
        have hyH : y ∈ H z := Subgroup.zpowers_le.mpr hxH hy
        simpa using mem_commSpace_of_commutator_zpowers S hxH hx2 hq hyH hy
    | one =>
        intro h1Q
        have hsub : (⟨1, h1Q⟩ : ↥(Q z)) = 1 := Subtype.ext rfl
        rw [hsub, map_one]
        exact Submodule.zero_mem _
    | mul u v hu hv ihu ihv =>
        intro huvQ
        have huQ : u ∈ Q z := hA hu
        have hvQ : v ∈ Q z := hA hv
        have hsub : (⟨u * v, huvQ⟩ : ↥(Q z)) = ⟨u, huQ⟩ * ⟨v, hvQ⟩ :=
          Subtype.ext rfl
        rw [hsub, map_mul]
        exact Submodule.add_mem _ (ihu huQ) (ihv hvQ)
    | inv u hu ihu =>
        intro huQ
        have huQ' : u ∈ Q z := hA hu
        have hsub : (⟨u⁻¹, huQ⟩ : ↥(Q z)) = ⟨u, huQ'⟩⁻¹ := Subtype.ext rfl
        rw [hsub, map_inv]
        exact Submodule.neg_mem _ (ihu huQ')
  exact hclass a ha haQ

theorem QaInterImage_commutator_zpowers_le_commSpace_of_sq_mem_Q (S : Setting z E F) {x : G}
    (hxH : x ∈ H z) (hx2 : x ^ 2 ∈ Q z) :
    QaInterImage S ⁅Q z, Subgroup.zpowers x⁆ ≤ commSpace (conjQbar S ⟨x, hxH⟩) := by
  intro v hv
  obtain ⟨q, hqA, hqv⟩ := (mem_QaInterImage_iff S).mp hv
  have hv' : Additive.ofMul (mkQbar S q) = v := by
    simpa using congrArg Additive.ofMul hqv
  rw [← hv']
  exact mkQbar_mem_commSpace_of_mem_commutator_zpowers S hxH hx2 hqA q.2

theorem QaInterImage_commutator_zpowers_eq_commSpace_of_sq_mem_Q (S : Setting z E F) {x : G}
    (hxH : x ∈ H z) (hx2 : x ^ 2 ∈ Q z) :
    QaInterImage S ⁅Q z, Subgroup.zpowers x⁆ = commSpace (conjQbar S ⟨x, hxH⟩) :=
  le_antisymm
    (QaInterImage_commutator_zpowers_le_commSpace_of_sq_mem_Q S hxH hx2)
    (commSpace_le_QaInterImage_commutator_zpowers S hxH)

theorem isElemAbelian_commutator_zpowers_of_q_eq_zero (S : Setting z E F) {x : G}
    (hxH : x ∈ H z) (hx2 : x ^ 2 ∈ Q z)
    (hq0 : ∀ v ∈ commSpace (conjQbar S ⟨x, hxH⟩), qS S v = 0) :
    IsElemAbelian 2 ⁅Q z, Subgroup.zpowers x⁆ := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  rw [Subgroup.commutator_def]
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · rintro _ ⟨q₁, hq₁, y₁, hy₁, rfl⟩ _ ⟨q₂, hq₂, y₂, hy₂, rfl⟩
    have hy₁H : y₁ ∈ H z := Subgroup.zpowers_le.mpr hxH hy₁
    have hy₂H : y₂ ∈ H z := Subgroup.zpowers_le.mpr hxH hy₂
    have h₁ := mem_commSpace_of_commutator_zpowers S hxH hx2 hq₁ hy₁H hy₁
    have h₂ := mem_commSpace_of_commutator_zpowers S hxH hx2 hq₂ hy₂H hy₂
    have hp := CFSG.LargeExtraspecial.polar_eq_zero_of_forall_eq_zero
      (q := qS S) hq0 h₁ h₂
    exact (polar_q_eq_zero_iff S ⟨⁅q₁, y₁⁆, commutator_mem_Q_of_mem_H hy₁H hq₁⟩
      ⟨⁅q₂, y₂⁆, commutator_mem_Q_of_mem_H hy₂H hq₂⟩).mp hp
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    have hyH : y ∈ H z := Subgroup.zpowers_le.mpr hxH hy
    have h := mem_commSpace_of_commutator_zpowers S hxH hx2 hq hyH hy
    have h0 : CFSG.RankThree.GF2n.Stroth78.q S
        (QuotientGroup.mk ⟨⁅q, y⁆, commutator_mem_Q_of_mem_H hyH hq⟩) = 0 := hq0 _ h
    exact (CFSG.RankThree.GF2n.Stroth78.q_eq_zero_iff S
      ⟨⁅q, y⁆, commutator_mem_Q_of_mem_H hyH hq⟩).mp h0

theorem conjQbar_mul_self_eq_one_of_sq_mem_Q (S : Setting z E F) {x : G} (hxH : x ∈ H z)
    (hx2 : x ^ 2 ∈ Q z) :
    conjQbar S ⟨x, hxH⟩ * conjQbar S ⟨x, hxH⟩ = 1 := by
  have hmk : (QuotientGroup.mk ⟨x, hxH⟩ : Hbar z) * QuotientGroup.mk ⟨x, hxH⟩ = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa [pow_two] using hx2)
  have h1 : rhoBar S (QuotientGroup.mk ⟨x, hxH⟩) *
      rhoBar S (QuotientGroup.mk ⟨x, hxH⟩) = 1 := by
    rw [← map_mul, hmk, map_one]
  rw [← rhoBar_coe_eq_conjQbar S ⟨x, hxH⟩]
  exact congrArg Subtype.val h1

theorem sq_mem_Q_of_conjQbar_mul_self_eq_one (S : Setting z E F) {x : G} (hxH : x ∈ H z)
    (hσ2 : conjQbar S ⟨x, hxH⟩ * conjQbar S ⟨x, hxH⟩ = 1) : x ^ 2 ∈ Q z := by
  have hρ : (rhoBar S (QuotientGroup.mk ⟨x, hxH⟩) :
      Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) = conjQbar S ⟨x, hxH⟩ :=
    rhoBar_coe_eq_conjQbar S ⟨x, hxH⟩
  have h2 : rhoBar S (QuotientGroup.mk ⟨x, hxH⟩ * QuotientGroup.mk ⟨x, hxH⟩) = 1 := by
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul]
    simpa [hρ] using hσ2
  rw [← map_one (rhoBar S)] at h2
  have hmk : (QuotientGroup.mk ⟨x, hxH⟩ : Hbar z) * QuotientGroup.mk ⟨x, hxH⟩ = 1 :=
    rhoBar_injective S h2
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at hmk
  simpa [pow_two] using Subgroup.mem_subgroupOf.mp hmk

theorem finrank_commSpace_eq_two_of_natCard_eq_four (S : Setting z E F) {x : G} (hxH : x ∈ H z)
    (h : Nat.card (commSpace (conjQbar S ⟨x, hxH⟩)) = 4) :
    finrank (ZMod 2) (commSpace (conjQbar S ⟨x, hxH⟩)) = 2 := by
  haveI : Module.Finite (ZMod 2) (commSpace (conjQbar S ⟨x, hxH⟩)) :=
    Module.Finite.of_finite
  have h1 : Nat.card (commSpace (conjQbar S ⟨x, hxH⟩)) =
      2 ^ finrank (ZMod 2) (commSpace (conjQbar S ⟨x, hxH⟩)) := by
    simpa using Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := commSpace (conjQbar S ⟨x, hxH⟩))
  have h2 : 2 ^ (2 : ℕ) =
      2 ^ finrank (ZMod 2) (commSpace (conjQbar S ⟨x, hxH⟩)) := by
    rw [← h1, h]
    norm_num
  exact (Nat.pow_right_injective (le_refl 2) h2).symm

theorem natCard_commSpace_eq_four_of_finrank_eq_two (S : Setting z E F) {x : G}
    (hxH : x ∈ H z) (h : finrank (ZMod 2) (commSpace (conjQbar S ⟨x, hxH⟩)) = 2) :
    Nat.card (commSpace (conjQbar S ⟨x, hxH⟩)) = 4 := by
  haveI : Module.Finite (ZMod 2) (commSpace (conjQbar S ⟨x, hxH⟩)) :=
    Module.Finite.of_finite
  have h1 : Nat.card (commSpace (conjQbar S ⟨x, hxH⟩)) =
      2 ^ finrank (ZMod 2) (commSpace (conjQbar S ⟨x, hxH⟩)) := by
    simpa using Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := commSpace (conjQbar S ⟨x, hxH⟩))
  rw [h] at h1
  simpa using h1

theorem isTypeA_rhoBar_of_isA2Hbar (S : Setting z E F) {α : Hbar z} (hα : IsA2Hbar S α) :
    CFSG.LargeExtraspecial.IsTypeA (qS S)
      (rhoBar S α : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) 2 := by
  obtain ⟨x, hxα, hxH, hxQ, hx2Q, hxcard, hxab⟩ := hα
  subst hxα
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  have hρ : (rhoBar S (QuotientGroup.mk x) :
      Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) = conjQbar S ⟨x, hxH⟩ :=
    rhoBar_coe_eq_conjQbar S ⟨x, hxH⟩
  have hσ2 : conjQbar S ⟨x, hxH⟩ * conjQbar S ⟨x, hxH⟩ = 1 :=
    conjQbar_mul_self_eq_one_of_sq_mem_Q S hxH hx2Q
  have hA : ⁅Q z, Subgroup.zpowers (x : G)⁆ ≤ Q z := by
    rw [Subgroup.commutator_le]
    intro q hq y hy
    exact commutator_mem_Q_of_mem_H (Subgroup.zpowers_le.mpr hxH hy) hq
  have hcardA : Nat.card (QaInterImage S ⁅Q z, Subgroup.zpowers (x : G)⁆) = 4 := by
    have h := card_sup_ZQ_eq_card_QaInterImage_mul S ⁅Q z, Subgroup.zpowers (x : G)⁆ hA
    rw [hxcard] at h
    exact Nat.mul_right_cancel (Nat.card_pos (α := ZQ z)) h.symm
  have hcardC : Nat.card (commSpace (conjQbar S ⟨x, hxH⟩)) = 4 := by
    rw [← QaInterImage_commutator_zpowers_eq_commSpace_of_sq_mem_Q S hxH hx2Q, hcardA]
  have hfin : finrank (ZMod 2) (commSpace (conjQbar S ⟨x, hxH⟩)) = 2 :=
    finrank_commSpace_eq_two_of_natCard_eq_four S hxH hcardC
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (rhoBar S (QuotientGroup.mk x)).2
  · intro h
    apply hxQ
    have h1 : rhoBar S (QuotientGroup.mk x) = 1 := Subtype.ext h
    have h2 : (QuotientGroup.mk x : Hbar z) = 1 := by
      apply rhoBar_injective S
      rw [h1, map_one]
    rw [QuotientGroup.eq_one_iff] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  · rw [hρ]
    exact hσ2
  · rw [hρ]
    exact hfin
  · intro v hv
    rw [hρ] at hv
    rw [← QaInterImage_commutator_zpowers_eq_commSpace_of_sq_mem_Q S hxH hx2Q] at hv
    obtain ⟨q, hqA, hqv⟩ := (mem_QaInterImage_iff S).mp hv
    have hv' : v = Additive.ofMul (mkQbar S q) := by
      simpa using (congrArg Additive.ofMul hqv).symm
    rw [hv']
    exact (CFSG.RankThree.GF2n.Stroth78.q_eq_zero_iff S q).mpr
      (hxab.2 (q : G) hqA)

theorem isA2Hbar_of_isTypeA_rhoBar (S : Setting z E F) {α : Hbar z}
    (hα : CFSG.LargeExtraspecial.IsTypeA (qS S)
      (rhoBar S α : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) 2) :
    IsA2Hbar S α := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective α
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  have hρ : (rhoBar S (QuotientGroup.mk x) :
      Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) = conjQbar S ⟨x, x.2⟩ :=
    rhoBar_coe_eq_conjQbar S x
  have hσ2 : conjQbar S ⟨x, x.2⟩ * conjQbar S ⟨x, x.2⟩ = 1 := by
    rw [← hρ]
    exact hα.2.2.1
  have hne : conjQbar S ⟨x, x.2⟩ ≠ 1 := by
    intro h
    apply hα.2.1
    rw [hρ, h]
  have hxQ : (x : G) ∉ Q z :=
    fun hxq => hne (conjQbar_eq_one_of_mem_Q S x.2 hxq)
  have hx2Q : (x : G) ^ 2 ∈ Q z :=
    sq_mem_Q_of_conjQbar_mul_self_eq_one S x.2 hσ2
  have hA : ⁅Q z, Subgroup.zpowers (x : G)⁆ ≤ Q z := by
    rw [Subgroup.commutator_le]
    intro q hq y hy
    exact commutator_mem_Q_of_mem_H (Subgroup.zpowers_le.mpr x.2 hy) hq
  have hfin : finrank (ZMod 2) (commSpace (conjQbar S ⟨x, x.2⟩)) = 2 := by
    rw [← hρ]
    exact hα.2.2.2.1
  have hcardC : Nat.card (commSpace (conjQbar S ⟨x, x.2⟩)) = 4 :=
    natCard_commSpace_eq_four_of_finrank_eq_two S x.2 hfin
  have hcardI : Nat.card (QaInterImage S ⁅Q z, Subgroup.zpowers (x : G)⁆) = 4 := by
    rw [QaInterImage_commutator_zpowers_eq_commSpace_of_sq_mem_Q S x.2 hx2Q, hcardC]
  have hcard : Nat.card ↥(⁅Q z, Subgroup.zpowers (x : G)⁆ ⊔ ZQ z) = 4 * Nat.card (ZQ z) := by
    rw [card_sup_ZQ_eq_card_QaInterImage_mul S _ hA, hcardI]
  have hq0 : ∀ v ∈ commSpace (conjQbar S ⟨x, x.2⟩), qS S v = 0 := by
    intro v hv
    rw [← hρ] at hv
    exact hα.2.2.2.2 v hv
  have hAea : IsElemAbelian 2 ⁅Q z, Subgroup.zpowers (x : G)⁆ :=
    isElemAbelian_commutator_zpowers_of_q_eq_zero S x.2 hx2Q hq0
  exact ⟨x, rfl, x.2, hxQ, hx2Q, hcard, hAea⟩

theorem isA2Hbar_iff (S : Setting z E F) {α : Hbar z} :
    IsA2Hbar S α ↔ CFSG.LargeExtraspecial.IsTypeA (qS S)
      (rhoBar S α : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) 2 :=
  ⟨isTypeA_rhoBar_of_isA2Hbar S, isA2Hbar_of_isTypeA_rhoBar S⟩

theorem orderOf_rhoBar (S : Setting z E F) (α : Hbar z) :
    orderOf (rhoBar S α : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) =
      orderOf α := by
  rw [Subgroup.orderOf_coe (rhoBar S α)]
  exact orderOf_injective (rhoBar S) (rhoBar_injective S) α

theorem orderOf_mul_of_isA2Hbar (S : Setting z E F) {α β : Hbar z}
    (hα : IsA2Hbar S α) (hβ : IsA2Hbar S β) :
    orderOf (α * β) ∈ ({1, 2, 3, 4} : Finset ℕ) ∧
      (orderOf (α * β) = 4 → IsA2Hbar S ((α * β) ^ 2)) := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  haveI : Finite (Additive (QbarOf S)) := inferInstance
  have hα' := isTypeA_rhoBar_of_isA2Hbar S hα
  have hβ' := isTypeA_rhoBar_of_isA2Hbar S hβ
  have h := CFSG.LargeExtraspecial.aschbacher_3_7 (q_nondegenerate S) hα' hβ'
  have hord : orderOf ((rhoBar S α :
      Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) *
      (rhoBar S β : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) =
      orderOf (α * β) := by
    rw [← Subgroup.coe_mul, ← map_mul, orderOf_rhoBar]
  rw [hord] at h
  refine ⟨h.1, fun h4 => ?_⟩
  have htype := h.2 h4
  have hsq : ((rhoBar S α :
      Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) *
      (rhoBar S β : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) ^ 2 =
      (rhoBar S ((α * β) ^ 2) :
        Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) := by
    rw [← Subgroup.coe_mul, ← map_mul, ← Subgroup.coe_pow, ← map_pow]
  rw [hsq] at htype
  exact (isA2Hbar_iff S).mpr htype

@[expose] def A2set (S : Setting z E F) : Set (Hbar z) := {α | IsA2Hbar S α}

theorem conj_mem_A2set (S : Setting z E F) (g : Hbar z) {α : Hbar z}
    (hα : α ∈ A2set S) : g * α * g⁻¹ ∈ A2set S := by
  have ht := (isA2Hbar_iff S).mp hα
  have hconj : (rhoBar S (g * α * g⁻¹) :
      Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) =
      (rhoBar S g : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) *
        (rhoBar S α : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) *
        (rhoBar S g : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))⁻¹ := by
    have h : rhoBar S (g * α * g⁻¹) = rhoBar S g * rhoBar S α * (rhoBar S g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    exact congrArg Subtype.val h
  refine (isA2Hbar_iff S).mpr ?_
  rw [hconj]
  exact CFSG.LargeExtraspecial.isTypeA_conj ht (rhoBar S g).2

theorem orderOf_eq_two_of_mem_A2set (S : Setting z E F) {α : Hbar z}
    (hα : α ∈ A2set S) : orderOf α = 2 := by
  have ht := (isA2Hbar_iff S).mp hα
  rw [← orderOf_rhoBar S α]
  exact orderOf_eq_prime (by rw [pow_two]; exact ht.2.2.1) ht.2.1

theorem A2set_isRootInvolutionSet (S : Setting z E F) :
    CFSG.Timmesfeld.IsRootInvolutionSet (A2set S) := by
  refine ⟨fun d hd => orderOf_eq_two_of_mem_A2set S hd, ?_, ?_⟩
  · intro d hd e he
    have h := (orderOf_mul_of_isA2Hbar S hd he).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h
    · rw [h]; exact Or.inr (Or.inr odd_one)
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr (Or.inr ⟨1, by norm_num⟩)
    · rw [h]; exact Or.inr (Or.inl rfl)
  · intro d hd e he h
    exact (orderOf_mul_of_isA2Hbar S hd he).2 h

theorem orderOf_mul_le_four_of_mem_A2set (S : Setting z E F) {α β : Hbar z}
    (hα : α ∈ A2set S) (hβ : β ∈ A2set S) : orderOf (α * β) ≤ 4 := by
  have h := (orderOf_mul_of_isA2Hbar S hα hβ).1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  omega

theorem Tset_subset_A2set (S : Setting z E F) (a : G) : Tset S a ⊆ A2set S := by
  intro α hα
  exact hα.2.2

theorem Eset_subset_A2set (S : Setting z E F) (a : G) : Eset S a ⊆ A2set S := by
  rintro α ⟨h, β, hβ, rfl⟩
  exact conj_mem_A2set S h (Tset_subset_A2set S a hβ)

end CFSG.RankThree.GF2n.Stroth78
