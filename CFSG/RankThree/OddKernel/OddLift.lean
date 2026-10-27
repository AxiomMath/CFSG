module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.OddKernel

open Subgroup

variable {G : Type*} [Group G]

theorem inf_eq_bot_of_odd [Finite G] {A N : Subgroup G} (hA : IsPGroup 2 A)
    (hN : Odd (Nat.card N)) :
    A ⊓ N = ⊥ := by
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hN)

theorem injective_restrict_of_odd [Finite G] {H : Type*} [Group H] (π : G →* H)
    (hker : Odd (Nat.card π.ker)) {A : Subgroup G} (hA : IsPGroup 2 A) :
    Function.Injective (π.comp A.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have h2 : (x : G) ∈ A ⊓ π.ker := ⟨x.2, hx⟩
  rw [inf_eq_bot_of_odd hA hker, mem_bot] at h2
  exact mem_bot.mpr (Subtype.ext h2)

theorem exists_two_subgroup_map_eq [Finite G] {H : Type*} [Group H] (π : G →* H)
    (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker)) (E : Subgroup H)
    (hE : IsPGroup 2 E) :
    ∃ A : Subgroup G, IsPGroup 2 A ∧ A.map π = E ∧ Function.Injective (π.comp A.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := E.comap π with hK
  set f : K →* E := (π.comp K.subtype).codRestrict E (fun x => x.2) with hf
  have hfs : Function.Surjective f := by
    intro e
    obtain ⟨g, hg⟩ := hπ (e : H)
    exact ⟨⟨g, show π g ∈ E by rw [hg]; exact e.2⟩, Subtype.ext hg⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 K) := inferInstance
  set S' : Sylow 2 E := S.mapSurjective hfs
  have hS'top : (S' : Subgroup E) = ⊤ :=
    (S'.3 (hE.of_equiv Subgroup.topEquiv.symm) le_top).symm
  set A := (S : Subgroup K).map K.subtype with hA
  have hA2 : IsPGroup 2 A := S.2.map K.subtype
  refine ⟨A, hA2, ?_, injective_restrict_of_odd π hker hA2⟩
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    exact x.2
  · intro e he
    have : (⟨e, he⟩ : E) ∈ (S' : Subgroup E) := hS'top ▸ mem_top _
    rw [Sylow.coe_mapSurjective] at this
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨(x : G), ⟨x, hx, rfl⟩, congrArg Subtype.val hxe⟩

theorem orderOf_mk_eq_two [Finite G] (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) {t : G}
    (ht : orderOf t = 2) : orderOf (t : G ⧸ N) = 2 := by
  have h2 : (t : G ⧸ N) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, ← ht, pow_orderOf_eq_one, QuotientGroup.mk_one]
  refine orderOf_eq_prime h2 fun h1 => ?_
  rw [QuotientGroup.eq_one_iff] at h1
  have hdvd : orderOf t ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N h1
  rw [ht] at hdvd
  exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr hdvd)

theorem isConj_of_mk_eq [Finite G] (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) {t t' : G}
    (ht : orderOf t = 2) (ht' : orderOf t' = 2) (h : (t : G ⧸ N) = t') :
    ∃ m ∈ N, m * t * m⁻¹ = t' := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq, ← ht, pow_orderOf_eq_one])
  have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right (by rw [← sq, ← ht', pow_orderOf_eq_one])
  set n := t' * t⁻¹ with hn
  have hnN : n ∈ N := by
    rw [← QuotientGroup.eq_one_iff, hn, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h,
      mul_inv_cancel]
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hinv : MulAut.conj t n = n⁻¹ := by
    rw [MulAut.conj_apply, hn, htinv, mul_inv_rev, htinv, ht'inv]
    calc t * (t' * t) * t = t * t' * (t * t) := by group
      _ = t * t' := by rw [ht2, mul_one]
  have hodd : Odd (orderOf n) := Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N hnN)
  obtain ⟨k, hk⟩ := hodd
  set m := n ^ (k + 1) with hm
  have hm2 : m * m = n := by
    rw [hm, ← pow_add, show k + 1 + (k + 1) = orderOf n + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hminv : MulAut.conj t m⁻¹ = m := by
    rw [map_inv, hm, map_pow, hinv, inv_pow, inv_inv]
  rw [MulAut.conj_apply] at hminv
  have htm : t * m⁻¹ = m * t := by
    calc t * m⁻¹ = t * m⁻¹ * t⁻¹ * t := by group
      _ = m * t := by rw [hminv]
  refine ⟨m, pow_mem hnN _, ?_⟩
  calc m * t * m⁻¹ = m * (t * m⁻¹) := by group
    _ = m * m * t := by rw [htm]; group
    _ = t' := by rw [hm2, hn, inv_mul_cancel_right]

theorem isConj_of_isConj_quotient [Finite G] (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N))
    (hconj : ∀ s s' : G ⧸ N, orderOf s = 2 → orderOf s' = 2 → IsConj s s') {t t' : G}
    (ht : orderOf t = 2) (ht' : orderOf t' = 2) : IsConj t t' := by
  obtain ⟨c, hc⟩ :=
    isConj_iff.1 (hconj _ _ (orderOf_mk_eq_two N hN ht) (orderOf_mk_eq_two N hN ht'))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  have ht'' : orderOf (g * t * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  obtain ⟨m, -, hm⟩ := isConj_of_mk_eq N hN ht'' ht' (by rw [← hc]; rfl)
  exact isConj_iff.2 ⟨m * g, by rw [← hm]; group⟩

end CFSG.RankThree.OddKernel
