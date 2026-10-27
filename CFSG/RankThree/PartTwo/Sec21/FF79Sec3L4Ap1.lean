module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Lift2
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem pp_eq_of_mk_eq (N : Subgroup X) [N.Normal] (hN : Nat.Coprime 3 (Nat.card N))
    {T : Subgroup X} (hT : IsPGroup 3 T) {x y : X} (hx : x ∈ T) (hy : y ∈ T)
    (h : (QuotientGroup.mk x : X ⧸ N) = QuotientGroup.mk y) : x = y := by
  have hmem : x⁻¹ * y ∈ N := QuotientGroup.eq.mp h
  have := eq_one_of_pgroup_of_coprime hT hN (T.mul_mem (T.inv_mem hx) hy) hmem
  exact inv_mul_eq_one.mp this

theorem pp_mapEquiv (N : Subgroup X) [N.Normal] (hN : Nat.Coprime 3 (Nat.card N))
    {T : Subgroup X} (hT : IsPGroup 3 T) :
    Nonempty (↥T ≃* ↥(T.map (QuotientGroup.mk' N))) := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).subgroupMap T) := by
    intro x y hxy
    apply Subtype.ext
    exact pp_eq_of_mk_eq N hN hT x.2 y.2 (congrArg Subtype.val hxy)
  exact ⟨MulEquiv.ofBijective _ ⟨hinj, (QuotientGroup.mk' N).subgroupMap_surjective T⟩⟩

theorem pp_card_map (N : Subgroup X) [N.Normal] (hN : Nat.Coprime 3 (Nat.card N))
    {T : Subgroup X} (hT : IsPGroup 3 T) :
    Nat.card (T.map (QuotientGroup.mk' N)) = Nat.card T := by
  obtain ⟨e⟩ := pp_mapEquiv N hN hT
  exact (Nat.card_congr e.toEquiv).symm

theorem pp_isSylowOf_map (N : Subgroup X) [N.Normal] (hN : Nat.Coprime 3 (Nat.card N))
    {S : Subgroup X} (hS : IsSylowOf 3 S ⊤) :
    IsSylowOf 3 (S.map (QuotientGroup.mk' N)) ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine L41.isSylowOf_of_card_p le_top ?_
  rw [pp_card_map N hN hS.2.1, L41.isSylowOf_card_p hS]
  have h1 : Nat.card (⊤ : Subgroup X) = Nat.card (X ⧸ N) * Nat.card N := by
    rw [Subgroup.card_top]; exact Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have h2 : Nat.card (⊤ : Subgroup (X ⧸ N)) = Nat.card (X ⧸ N) := Subgroup.card_top
  have h3 : (Nat.card N).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN)
  rw [h1, h2, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, h3,
    add_zero]

theorem pp_orderOf_mk (N : Subgroup X) [N.Normal] (hN : Nat.Coprime 3 (Nat.card N)) {x : X}
    (hx : IsPGroup 3 (Subgroup.zpowers x)) : orderOf (QuotientGroup.mk x : X ⧸ N) = orderOf x := by
  refine Nat.dvd_antisymm (orderOf_map_dvd (QuotientGroup.mk' N) x) ?_
  refine orderOf_dvd_iff_pow_eq_one.mpr ?_
  have h1 : (QuotientGroup.mk (x ^ orderOf (QuotientGroup.mk x : X ⧸ N)) : X ⧸ N) = 1 := by
    rw [QuotientGroup.mk_pow]; exact pow_orderOf_eq_one _
  have h2 : x ^ orderOf (QuotientGroup.mk x : X ⧸ N) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
  exact eq_one_of_pgroup_of_coprime hx hN (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _) h2

end Abstract

section ElemAb

theorem isElementaryAbelian_iff {Y : Type*} [Group Y] (p : ℕ) (T : Subgroup Y) :
    IsElementaryAbelian p T ↔ (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧ ∀ x ∈ T, x ^ p = 1 := by
  constructor
  · intro h
    exact ⟨fun x hx y hy => setLike_mul_comm hx hy,
      fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩
  · rintro ⟨hc, hp⟩
    refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · exact IsMulCommutative.of_setLike_mul_comm fun _ h₁ _ h₂ => hc _ h₁ _ h₂
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => ?_
      apply Subtype.ext
      simpa using hp x x.2

end ElemAb

section A5

variable {Y : Type} [Group Y]

theorem a5_inf_eq_bot (K R : Subgroup Y) [R.Normal]
    (hK : Nonempty (↥K ≃* alternatingGroup (Fin 5))) (hKR : ¬ K ≤ R) :
    ∀ x ∈ K, x ∈ R → x = 1 := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  obtain ⟨e⟩ := hK
  haveI : IsSimpleGroup ↥K := e.isSimpleGroup
  intro x hxK hxR
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf K) with h | h
  · have : (⟨x, hxK⟩ : ↥K) ∈ R.subgroupOf K := hxR
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exact absurd (Subgroup.subgroupOf_eq_top.mp h) hKR

theorem a5_card_dvd (K : Subgroup Y) (hK : Nonempty (↥K ≃* alternatingGroup (Fin 5))) :
    Nat.card K = 60 := by
  obtain ⟨e⟩ := hK
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

end A5

end CFSG.RankThree.PartTwo.Sec21.FF79
