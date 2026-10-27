module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LocalAnalysis

open Subgroup
open scoped Pointwise commutatorElement

theorem odd_center_two_factor_diagonal_normalizer_generation {H : Type*} [Group H] [Finite H]
    {t : H} (ht : orderOf t = 2) {A : Subgroup H} [Group.IsPerfect A]
    (hC : Odd (Nat.card (center A))) (hsimple : IsSimpleGroup (A ⧸ center A))
    (heven : Even (Nat.card (A ⧸ center A)))
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) {U : Subgroup H} (hUA : U ≤ A)
    (hU : ∃ T : Sylow 2 A, (T : Subgroup A) = U.subgroupOf A) :
    let δ : H → H := fun a => a * (t⁻¹ * a * t)
    let At := A.map (MulAut.conj t⁻¹).toMonoidHom
    let Ut := U.map (MulAut.conj t⁻¹).toMonoidHom
    let P := U ⊔ Ut
    let δU := closure (δ '' (U : Set H))
    let Q := δU ⊔ zpowers t
    (P : Set H) = (U : Set H) * (Ut : Set H) ∧ (δU : Set H) = δ '' (U : Set H) ∧
      (Q : Set H) = (δU : Set H) * (zpowers t : Set H) ∧
      ((A ⊔ At : Subgroup H) : Set H) = (A : Set H) * (At : Set H) ∧
      closure (δ '' (A : Set H) ∪ (P ⊓ normalizer (Q : Set H) : Subgroup H)) = A ⊔ At := by
  intro δ At Ut P δU Q
  classical
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hconj : ∀ a, (MulAut.conj t⁻¹).toMonoidHom a = t⁻¹ * a * t := fun a => by
    simp
  have hAAt : ∀ a ∈ A, ∀ b ∈ At, b * a = a * b := fun a ha b hb =>
    mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm ha) b hb
  have hconjA : ∀ a ∈ A, t⁻¹ * a * t ∈ At := fun a ha => ⟨a, ha, hconj a⟩
  have hδmul : ∀ a ∈ A, ∀ b ∈ A, δ (a * b) = δ a * δ b := by
    intro a ha b hb
    have h := hAAt b hb (t⁻¹ * a * t) (hconjA a ha)
    calc a * b * (t⁻¹ * (a * b) * t) = a * (b * (t⁻¹ * a * t)) * (t⁻¹ * b * t) := by group
      _ = a * ((t⁻¹ * a * t) * b) * (t⁻¹ * b * t) := by rw [← h]
      _ = a * (t⁻¹ * a * t) * (b * (t⁻¹ * b * t)) := by group
  let δhom : A →* H :=
    { toFun := fun a => δ a
      map_one' := by simp [δ]
      map_mul' := fun a b => hδmul a a.2 b b.2 }
  have himage : ∀ K : Subgroup H, K ≤ A → δ '' (K : Set H) = ((K.subgroupOf A).map δhom : Set H) :=
    fun K hK => by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, hK hk⟩, hk, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
  have hδU : (δU : Set H) = δ '' (U : Set H) := by
    show ((closure (δ '' (U : Set H)) : Subgroup H) : Set H) = δ '' (U : Set H)
    rw [himage U hUA, closure_eq]
  have htδ : ∀ u ∈ A, t * δ u * t⁻¹ = δ u := fun u hu => by
    have h := hAAt u hu (t⁻¹ * u * t) (hconjA u hu)
    simp only [δ]
    rw [htinv] at h ⊢
    calc t * (u * (t * u * t)) * t = t * u * t * u * (t * t) := by group
      _ = (t * u * t) * u := by rw [ht2, mul_one]
      _ = u * (t * u * t) := h
  have htC : t ∈ centralizer (δU : Set H) := by
    rw [mem_centralizer_iff]
    intro x hx
    rw [hδU] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have h := htδ u (hUA hu)
    calc δ u * t = t * δ u * t⁻¹ * t := by rw [h]
      _ = t * δ u := by group
  have hUtA : Ut ≤ At := map_mono hUA
  have hUtC : Ut ≤ centralizer (U : Set H) := fun b hb => mem_centralizer_iff.mpr fun u hu =>
    (hAAt u (hUA hu) b (hUtA hb)).symm
  have hAtC : At ≤ centralizer (A : Set H) := fun b hb => mem_centralizer_iff.mpr fun a ha =>
    (hAAt a ha b hb).symm
  have hP : (P : Set H) = (U : Set H) * (Ut : Set H) :=
    coe_mul_of_right_le_normalizer_left U Ut (hUtC.trans (centralizer_le_normalizer _))
  have hQ : (Q : Set H) = (δU : Set H) * (zpowers t : Set H) :=
    coe_mul_of_right_le_normalizer_left δU (zpowers t)
      (zpowers_le.mpr (centralizer_le_normalizer _ htC))
  have hAAt' : ((A ⊔ At : Subgroup H) : Set H) = (A : Set H) * (At : Set H) :=
    coe_mul_of_right_le_normalizer_left A At (hAtC.trans (centralizer_le_normalizer _))
  refine ⟨hP, hδU, hQ, hAAt', ?_⟩
  obtain ⟨T, hT⟩ := hU
  have hAcard : Nat.card A = Nat.card (A ⧸ center A) * Nat.card (center A) :=
    card_eq_card_quotient_mul_card_subgroup (center A)
  have hAeven : 2 ∣ Nat.card A := by
    rw [hAcard]
    exact (even_iff_two_dvd.mp heven).mul_right _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTcard : 2 ∣ Nat.card T := by
    rw [Sylow.card_eq_multiplicity]
    exact dvd_pow_self 2 (Nat.Prime.factorization_pos_of_dvd Nat.prime_two
      Nat.card_pos.ne' hAeven).ne'
  have eU : U.subgroupOf A ≃* U := subgroupOfEquivOfLe hUA
  have hU2 : IsPGroup 2 U := by
    have h1 : IsPGroup 2 (U.subgroupOf A) := hT ▸ T.isPGroup'
    exact h1.of_equiv eU
  have hUcard : 2 ∣ Nat.card U := by
    rw [← Nat.card_congr eU.toEquiv, ← hT]
    exact hTcard
  have : Nontrivial U := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Nat.le_of_dvd Nat.card_pos hUcard
    omega
  have hZU : Nontrivial (center U) := hU2.center_nontrivial
  obtain ⟨n, hn, hZcard⟩ := (hU2.to_subgroup (center U)).nontrivial_iff_card.mp hZU
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := center U) 2
    (by rw [hZcard]; exact dvd_pow_self 2 hn.ne')
  set z : H := ((w : U) : H) with hz
  have hzU : z ∈ U := (w : U).2
  have hzA : z ∈ A := hUA hzU
  have hzo : orderOf z = 2 := by
    rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hzz : z * z = 1 := by rw [← sq, ← hzo, pow_orderOf_eq_one]
  have hzUc : ∀ u ∈ U, u * z = z * u := fun u hu =>
    congrArg Subtype.val (mem_center_iff.mp w.2 ⟨u, hu⟩)
  have hzC : (⟨z, hzA⟩ : A) ∉ center A := by
    intro h
    have h1 : orderOf (⟨⟨z, hzA⟩, h⟩ : center A) ∣ Nat.card (center A) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hzo] at h1
    obtain ⟨k, hk⟩ := hC
    omega
  have hzδ : ∀ u ∈ U, z * δ u * z⁻¹ = δ u := fun u hu => by
    have h1 := hzUc u hu
    have h2 := hAAt z hzA (t⁻¹ * u * t) (hconjA u (hUA hu))
    show z * (u * (t⁻¹ * u * t)) * z⁻¹ = u * (t⁻¹ * u * t)
    calc z * (u * (t⁻¹ * u * t)) * z⁻¹ = (z * u) * (t⁻¹ * u * t) * z⁻¹ := by group
      _ = (u * z) * (t⁻¹ * u * t) * z⁻¹ := by rw [h1]
      _ = u * (z * (t⁻¹ * u * t)) * z⁻¹ := by group
      _ = u * ((t⁻¹ * u * t) * z) * z⁻¹ := by rw [h2]
      _ = u * (t⁻¹ * u * t) := by group
  have hzt : z * t * z⁻¹ = δ z * t := by
    show z * t * z⁻¹ = z * (t⁻¹ * z * t) * t
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    rw [hzinv, htinv]
    calc z * t * z = z * t * z * (t * t) := by rw [ht2, mul_one]
      _ = z * (t * z * t) * t := by group
  have hzQ : ∀ x ∈ Q, z * x * z⁻¹ ∈ Q := by
    have hle : Q ≤ Q.comap (MulAut.conj z).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [closure_le]
        rintro _ ⟨u, hu, rfl⟩
        show (MulAut.conj z).toMonoidHom (δ u) ∈ Q
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hzδ u hu]
        exact mem_sup_left (subset_closure ⟨u, hu, rfl⟩)
      · rw [zpowers_le]
        show (MulAut.conj z).toMonoidHom t ∈ Q
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hzt]
        exact mul_mem (mem_sup_left (subset_closure ⟨z, hzU, rfl⟩))
          (mem_sup_right (mem_zpowers t))
    intro x hx
    have h := hle hx
    rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    exact h
  have hzN : z ∈ normalizer (Q : Set H) := by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hzQ x hx, fun hx => ?_⟩
    have h := hzQ _ hx
    have e : z * (z * x * z⁻¹) * z⁻¹ = x := by
      calc z * (z * x * z⁻¹) * z⁻¹ = (z * z) * x * (z * z)⁻¹ := by group
        _ = x := by rw [hzz, inv_one, one_mul, mul_one]
    rwa [e] at h
  set K := closure (δ '' (A : Set H) ∪ (P ⊓ normalizer (Q : Set H) : Subgroup H)) with hK
  have hzK : z ∈ K := subset_closure (Or.inr ⟨mem_sup_left hzU, hzN⟩)
  have hδK : ∀ a ∈ A, δ a ∈ K := fun a ha => subset_closure (Or.inl ⟨a, ha, rfl⟩)
  have hconjK : ∀ a ∈ A, a * z * a⁻¹ ∈ K := fun a ha => by
    have h1 : δ a * z * (δ a)⁻¹ = a * z * a⁻¹ := by
      have h2 := hAAt z hzA (t⁻¹ * a * t) (hconjA a ha)
      show a * (t⁻¹ * a * t) * z * (a * (t⁻¹ * a * t))⁻¹ = a * z * a⁻¹
      calc a * (t⁻¹ * a * t) * z * (a * (t⁻¹ * a * t))⁻¹ =
          a * ((t⁻¹ * a * t) * z) * (t⁻¹ * a * t)⁻¹ * a⁻¹ := by group
        _ = a * (z * (t⁻¹ * a * t)) * (t⁻¹ * a * t)⁻¹ * a⁻¹ := by rw [h2]
        _ = a * z * a⁻¹ := by group
    rw [← h1]
    exact mul_mem (mul_mem (hδK a ha) hzK) (inv_mem (hδK a ha))
  let X : Subgroup A := normalClosure {(⟨z, hzA⟩ : A)}
  have hXK : X.map A.subtype ≤ K := by
    rw [map_le_iff_le_comap]
    refine closure_le _ |>.mpr fun c hc => ?_
    obtain ⟨b, hb, hbc⟩ := Group.mem_conjugatesOfSet_iff.mp hc
    rw [Set.mem_singleton_iff] at hb
    subst hb
    obtain ⟨g, rfl⟩ := isConj_iff.mp hbc
    show ((g : H) * z * (g : H)⁻¹) ∈ K
    exact hconjK g g.2
  have hXtop : X = ⊤ := by
    have hXn : X.Normal := normalClosure_normal
    have hmap : (X.map (QuotientGroup.mk' (center A))).Normal :=
      hXn.map _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X.map (QuotientGroup.mk' (center A))) with
      h | h
    · exfalso
      have h1 : QuotientGroup.mk' (center A) ⟨z, hzA⟩ ∈ X.map (QuotientGroup.mk' (center A)) :=
        mem_map_of_mem _ (subset_normalClosure rfl)
      rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact hzC h1
    · have hsup : X ⊔ center A = ⊤ := by
        have h1 := congrArg (Subgroup.comap (QuotientGroup.mk' (center A))) h
        rwa [comap_map_eq, QuotientGroup.ker_mk', comap_top] at h1
      have hle : ⁅(⊤ : Subgroup A), ⊤⁆ ≤ X := by
        rw [← hsup, commutator_le]
        intro g hg h hh
        rw [← SetLike.mem_coe, mul_normal X (center A)] at hg hh
        obtain ⟨x, hx, c, hc, rfl⟩ := hg
        obtain ⟨y, hy, d, hd, rfl⟩ := hh
        rw [SetLike.mem_coe, mem_center_iff] at hc hd
        have e : ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
          rw [commutatorElement_def, commutatorElement_def]
          calc x * c * (y * d) * (x * c)⁻¹ * (y * d)⁻¹
              = x * (c * (y * d)) * c⁻¹ * x⁻¹ * (y * d)⁻¹ := by group
            _ = x * ((y * d) * c) * c⁻¹ * x⁻¹ * (y * d)⁻¹ := by rw [← hc (y * d)]
            _ = x * y * (d * x⁻¹) * d⁻¹ * y⁻¹ := by group
            _ = x * y * (x⁻¹ * d) * d⁻¹ * y⁻¹ := by rw [← hd x⁻¹]
            _ = x * y * x⁻¹ * y⁻¹ := by group
        rw [e, commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
      have htop : commutator A = ⊤ := Group.IsPerfect.commutator_eq_top
      rw [_root_.commutator_def] at htop
      exact eq_top_iff.mpr (htop ▸ hle)
  have hAK : A ≤ K := fun a ha => hXK ⟨⟨a, ha⟩, hXtop ▸ mem_top _, rfl⟩
  have hAtK : At ≤ K := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hconj]
    have e : t⁻¹ * a * t = a⁻¹ * δ a := by
      show t⁻¹ * a * t = a⁻¹ * (a * (t⁻¹ * a * t))
      group
    rw [e]
    exact mul_mem (inv_mem (hAK ha)) (hδK a ha)
  refine le_antisymm ?_ (sup_le hAK hAtK)
  rw [closure_le]
  rintro x (⟨a, ha, rfl⟩ | ⟨hx, -⟩)
  · exact mul_mem (mem_sup_left ha) (mem_sup_right (hconjA a ha))
  · exact sup_le_sup hUA hUtA hx

end CFSG.LocalAnalysis
