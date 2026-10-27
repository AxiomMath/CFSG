module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.QuasithinUnique

theorem card_eq_pow_of_isSylowTwoOf_top {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) {a m : ℕ} (hG : Nat.card G = 2 ^ a * m) (hm : ¬ 2 ∣ m) :
    Nat.card T = 2 ^ a := by
  have hp := K1.isSylowTwoOf_top_iff.1 hT
  let P : Sylow 2 G := hp.1.toSylow hp.2
  have h := P.card_eq_multiplicity
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero 2)
  rw [hG, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero] at h
  exact h

theorem isSylowTwoOf_map_equiv {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    {T : Subgroup G} (hT : IsSylowTwoOf T ⊤) : IsSylowTwoOf (T.map φ.toMonoidHom) ⊤ := by
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.1 hT
  refine K1.isSylowTwoOf_top_iff.2 ⟨hp.map φ.toMonoidHom, ?_⟩
  rw [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective]
  exact hi

theorem exists_central_involution {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hTp : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    ∃ z ∈ T, z ≠ 1 ∧ z * z = 1 ∧ ∀ t ∈ T, z * t = t * z := by
  have hnt : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hT1
  have hZn : Nontrivial (Subgroup.center T) := hTp.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center T) :=
    hTp.of_injective (Subgroup.center T).subtype Subtype.val_injective
  obtain ⟨e, he⟩ := IsPGroup.iff_card.1 hZp
  have he0 : e ≠ 0 := by
    rintro rfl
    have : Nat.card (Subgroup.center T) = 1 := by rw [he, pow_zero]
    exact (Finite.one_lt_card_iff_nontrivial.2 hZn).ne' this
  have hdvd : 2 ∣ Nat.card (Subgroup.center T) := by
    rw [he]
    exact dvd_pow_self 2 he0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2 hdvd
  set z : G := (((y : Subgroup.center T) : T) : G) with hz
  have hord : orderOf z = 2 := by
    rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  refine ⟨z, ((y : Subgroup.center T) : T).2, ?_, ?_, fun t ht => ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  · rw [← sq]
    exact hord ▸ pow_orderOf_eq_one z
  · have := Subgroup.mem_center_iff.1 y.2 ⟨t, ht⟩
    exact (congrArg Subtype.val this).symm

theorem eq_bot_of_normal_odd {G : Type*} [Group G] (hO : CFSG.oddCore G = ⊥)
    (N : Subgroup G) (hN : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ :=
  le_bot_iff.1 (hO ▸ le_sSup ⟨hN, hodd⟩)

theorem exists_sylow_center_of_equiv {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    {Q : Subgroup G} {zG : G} (hQ : IsSylowTwoOf Q ⊤)
    (hz : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = zG) :
    ∃ (T : Subgroup H) (z : H), IsSylowTwoOf T ⊤ ∧ IsPGroup 2 T ∧
      ∀ c ∈ T, (∀ t ∈ T, c * t = t * c) → c = 1 ∨ c = z := by
  have hT := isSylowTwoOf_map_equiv φ hQ
  refine ⟨Q.map φ.toMonoidHom, φ zG, hT, (K1.isSylowTwoOf_top_iff.1 hT).1, ?_⟩
  rintro _ ⟨q, hq, rfl⟩ hc
  have hqc : ∀ q' ∈ Q, q * q' = q' * q := fun q' hq' =>
    φ.injective (by simpa using hc (φ q') ⟨q', hq', rfl⟩)
  rcases hz q hq hqc with h | h
  · exact Or.inl (by simp [h])
  · exact Or.inr (by simp [h])

end CFSG.Quasithin.ModH
