module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312NB
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312D
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312NA

public section

namespace CFSG.Quasithin.H13.L3312.NQ

open CFSG.Open CFSG.QuasithinUnique

theorem Type3312R.two_dvd_card {W : Type} [Group W] (h : Type3312R W) : 2 ∣ Nat.card W := by
  rcases h.card with ⟨n, hn, hc⟩ | hc | hc
  · rw [hc]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  · rw [hc]; norm_num
  · rw [hc]; norm_num

theorem odd_normal_eq_bot {Y : Type} [Group Y] [Finite Y] (h : Type3312R (Y ⧸ CFSG.pCore 2 Y))
    (N : Subgroup Y) [N.Normal] (hN : Odd (Nat.card N)) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.pCore 2 Y).Normal := CFSG.pCore_normal
  have hs : IsSimpleGroup (Y ⧸ CFSG.pCore 2 Y) := Type3312R.isSimpleGroup h
  set π := QuotientGroup.mk' (CFSG.pCore 2 Y) with hπ
  have hM : (N.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with hbot | htop
  · have hle : N ≤ CFSG.pCore 2 Y := by
      intro x hx
      have : π x ∈ N.map π := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have h2 : IsPGroup 2 N := CFSG.pCore_isPGroup.to_le hle
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hk] at hN
      exact (Nat.not_even_iff_odd.mpr hN) ((Nat.even_pow' hk0).mpr even_two)
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  · exfalso
    have h1 : Nat.card (Y ⧸ CFSG.pCore 2 Y) ∣ Nat.card N := by
      have := Subgroup.card_map_dvd (f := π) N
      rwa [htop, Subgroup.card_top] at this
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hN h1))
      (even_iff_two_dvd.mpr (Type3312R.two_dvd_card h))

variable {Q : Type} [Group Q] [Finite Q]

theorem inf_oddCore_eq_bot {B : Subgroup Q} (h : Type3312R (ModO2 B)) :
    B ⊓ CFSG.oddCore Q = ⊥ := by
  have hN : ((CFSG.oddCore Q).subgroupOf B).Normal := Subgroup.Normal.subgroupOf inferInstance B
  have hodd : Odd (Nat.card ((CFSG.oddCore Q).subgroupOf B)) := by
    have h1 : Nat.card ((CFSG.oddCore Q).subgroupOf B) ∣ Nat.card (CFSG.oddCore Q) := by
      rw [← Subgroup.card_map_of_injective B.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact Odd.of_dvd_nat odd_card_oddCore h1
  have hbot := odd_normal_eq_bot h _ hodd
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx.1⟩ : ↥B) ∈ (CFSG.oddCore Q).subgroupOf B := Subgroup.mem_subgroupOf.mpr hx.2
  rw [hbot, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

noncomputable def equivQuotOfCompl {B O : Subgroup Q} [O.Normal] (hBO : B ⊓ O = ⊥)
    (hBsup : B ⊔ O = ⊤) : ↥B ≃* Q ⧸ O :=
  MulEquiv.ofBijective ((QuotientGroup.mk' O).comp B.subtype) ⟨by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : (x : Q) ∈ O := by
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      exact hx
    have : (x : Q) ∈ B ⊓ O := ⟨x.2, hxO⟩
    rw [hBO, Subgroup.mem_bot] at this
    exact Subtype.ext this, by
    intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
    have hq : q ∈ ((B ⊔ O : Subgroup Q) : Set Q) := by rw [hBsup]; trivial
    rw [Subgroup.mul_normal] at hq
    obtain ⟨b, hb, o, ho, rfl⟩ := hq
    refine ⟨⟨b, hb⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    simpa using ho⟩

omit [Finite Q] in
theorem commutator_eq_top_of_equiv' {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : commutator Y = ⊤) : commutator X = ⊤ := by
  have h1 := Subgroup.map_commutator (⊤ : Subgroup Y) ⊤ e.symm.toMonoidHom
  rw [Subgroup.map_top_of_surjective _ e.symm.surjective] at h1
  rw [commutator_def, ← h1, ← commutator_def, hY,
    Subgroup.map_top_of_surjective _ e.symm.surjective]

theorem sl2_data {B : Subgroup Q} {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (e : ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
    ⁅B, B⁆ = B ∧ ∃ z ∈ B, z * z = 1 ∧ z ≠ 1 ∧ ∀ t ∈ B, t * t = 1 → t = 1 ∨ t = z := by
  have hp2 : p ≠ 2 := by omega
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    apply CFSG.LinearGroups.special_linear_dimension_two_perfect
    have : 4 ≤ (Finset.univ : Finset (ZMod p)).card := by
      rw [Finset.card_univ, ZMod.card]
      omega
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq this
    exact ⟨s, hs⟩
  have hBperf : ⁅B, B⁆ = B := by
    rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
    exact commutator_eq_top_of_equiv' e (Group.isPerfect_def.mp hperf)
  refine ⟨hBperf, ?_⟩
  have h2B : 2 ∣ Nat.card ↥B := by
    rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      Nat.card_zmod]
    have hodd : Odd p := hp.out.odd_of_ne_two hp2
    have : Even (p ^ 2 - 1) := by
      obtain ⟨k, hk⟩ := hodd
      refine ⟨2 * k * k + 2 * k, ?_⟩
      rw [hk]
      ring_nf
      omega
    exact Dvd.dvd.mul_left (even_iff_two_dvd.mp this) _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2B
  have hz2 : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  refine ⟨z, z.2, congrArg Subtype.val hz2, fun h => hz1 (Subtype.ext h), ?_⟩
  intro t ht htt
  by_cases h1 : (⟨t, ht⟩ : ↥B) = 1
  · left
    exact congrArg Subtype.val h1
  · right
    have htt' : (⟨t, ht⟩ : ↥B) * ⟨t, ht⟩ = 1 := Subtype.ext htt
    have he1 : e ⟨t, ht⟩ * e ⟨t, ht⟩ = 1 := by rw [← map_mul, htt', map_one]
    have he2 : e z * e z = 1 := by rw [← map_mul, hz2, map_one]
    have := sl2_involution_eq hp2 he1 he2 (fun h => h1 (e.injective (h.trans (map_one e).symm)))
      (fun h => hz1 (e.injective (h.trans (map_one e).symm)))
    exact congrArg Subtype.val (e.injective this)

end CFSG.Quasithin.H13.L3312.NQ
