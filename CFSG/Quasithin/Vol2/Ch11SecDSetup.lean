module

public import CFSG.Quasithin.Vol2.Ch11SecABasic
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem inf_L_le_TL (T L : Subgroup G) : T ⊓ L ≤ TL T L :=
  inf_le_inf_left T le_sup_left

theorem TL_inf_L (T L : Subgroup G) : TL T L ⊓ L = T ⊓ L :=
  le_antisymm (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (inf_L_le_TL T L) inf_le_right)

theorem mem_normalizer_inf {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  simp only [Subgroup.mem_inf]
  rw [hA y, hB y]

variable [Finite G]

theorem exists_hall_of_normal_sylow {K P : Subgroup G} (hP : QuasithinUnique.IsSylowTwoOf P K)
    (hN : K ≤ Subgroup.normalizer (P : Set G)) :
    ∃ D : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf D K := by
  have : (P.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hP.1).mpr hN
  have hcardP : Nat.card (P.subgroupOf K) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv
  obtain ⟨e, he⟩ := hP.2.1.exists_card_eq
  have hidx : ¬ 2 ∣ (P.subgroupOf K).index := hP.2.2
  have hcop : Nat.Coprime (Nat.card (P.subgroupOf K)) (P.subgroupOf K).index := by
    rw [hcardP, he]
    exact Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx)
  obtain ⟨D', hD'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hmul : Nat.card (P.subgroupOf K) * Nat.card D' = Nat.card K := hD'.card_mul_card
  have hmul' : (P.subgroupOf K).index * Nat.card (P.subgroupOf K) = Nat.card K :=
    Subgroup.index_mul_card _
  have hDcard : Nat.card D' = (P.subgroupOf K).index := by
    have hpos : 0 < Nat.card (P.subgroupOf K) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hmul, ← hmul', mul_comm]
  have hDindex : D'.index = 2 ^ e := by
    have h1 : D'.index * Nat.card D' = Nat.card K := Subgroup.index_mul_card _
    have hpos : 0 < Nat.card D' := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← hmul, hcardP, he]
  refine ⟨D'.map K.subtype, Subgroup.map_subtype_le D', ?_, ⟨e, ?_⟩⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hDcard]
    exact Nat.odd_iff.mpr (by omega)
  · change ((D'.map K.subtype).comap K.subtype).index = 2 ^ e
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective, hDindex]

variable {T L I : Subgroup G} {n : ℕ}

theorem isSylowTwoOf_inf_L (h : Hyp11 G T L I n) :
    QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
  A4.isSylowTwoOf_inf_normal (SecA.isSylowTwoOf_M h) Subgroup.le_normalizer le_rfl

theorem exists_isCartanX (h : Hyp11 G T L I n) : ∃ X : Subgroup G, IsCartanX T L X := by
  have hTLN : T ⊓ L ≤ L ⊓ Subgroup.normalizer (TL T L : Set G) :=
    le_inf inf_le_right fun x hx => Subgroup.le_normalizer (inf_L_le_TL T L hx)
  have hsyl : QuasithinUnique.IsSylowTwoOf (T ⊓ L) (L ⊓ Subgroup.normalizer (TL T L : Set G)) :=
    A4.isSylowTwoOf_mono (isSylowTwoOf_inf_L h) hTLN inf_le_left
  have hnorm : L ⊓ Subgroup.normalizer (TL T L : Set G) ≤
      Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    intro x hx
    rw [← TL_inf_L T L]
    exact mem_normalizer_inf hx.2 (Subgroup.le_normalizer hx.1)
  exact exists_hall_of_normal_sylow hsyl hnorm

end CFSG.Quasithin.Vol2.Ch11.SecD
