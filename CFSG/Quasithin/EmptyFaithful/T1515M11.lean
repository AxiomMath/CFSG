module

public import CFSG.Quasithin.EmptyFaithful.T1515Der2
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def PSUThreeThreeOrder : Prop :=
  ∀ (X : Type) [Group X], IsPSU 3 3 1 X → Nat.card X = 6048

@[expose] def ThreeD4TwoOrder : Prop :=
  ∀ (X : Type) [Group X], Is3D4 2 1 X → Nat.card X = 211341312

section Orders

theorem card_eq_of_isSporadic1522 {X : Type} [Group X] {s : TauCeti.SporadicName} {n : ℕ}
    (hn : Nat.card (NativeSporadic.Carrier s) = n) (h : IsSporadic s X) : Nat.card X = n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, hn]

theorem not_isSporadic_quotient1522 {L : Type} [Group L] (N : Subgroup L) [N.Normal]
    (hL : Nat.card L = 7920) {s : TauCeti.SporadicName} {n : ℕ}
    (hn : Nat.card (NativeSporadic.Carrier s) = n) (hlt : 7920 < n) : ¬ IsSporadic s (L ⧸ N) := by
  intro h
  have h1 : Nat.card (L ⧸ N) = n := card_eq_of_isSporadic1522 hn h
  have h2 : Nat.card (L ⧸ N) ∣ Nat.card L := N.index_dvd_card
  rw [h1, hL] at h2
  exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)

theorem card_nativeM23_1522
    : Nat.card NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans CFSG.M23.M23Group.card_M23

theorem card_statedSL_two1522 (n : ℕ) [NeZero n] (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) : Nat.card (StatedSL n K) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL n K).toEquiv,
    Matrix.card_SL_field, hq]
  simp

theorem statedScalars_subgroupOf_eq_bot1522 (n : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  have hunits : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have : Subsingleton Kˣ := Finite.card_le_one_iff_subsingleton.mp hunits.le
  have hsc : StatedScalars (Fin n) K = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
    obtain ⟨u, rfl⟩ := hg
    rw [Subsingleton.elim u 1, map_one]
  rw [hsc]
  exact Subgroup.bot_subgroupOf _

theorem card_of_isPSL_two1522 (n : ℕ) [NeZero n] {X : Type} [Group X] (h : IsPSL n 2 1 X) :
    Nat.card X = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  rw [Nat.card_congr e.toEquiv, ← card_statedSL_two1522 n K hK2]
  have hbot := statedScalars_subgroupOf_eq_bot1522 n K hK2
  show Nat.card (↥(StatedSL n K) ⧸ (StatedScalars (Fin n) K).subgroupOf
    (StatedSL n K)) = _
  rw [← Subgroup.index, hbot, Subgroup.index_bot]

theorem twentyfive_dvd_card_of_isTits1522
    {X : Type} [Group X] (h : IsTits X) :
    25 ∣ Nat.card X := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model h
  obtain ⟨x, y, -, -, -, -, hcard, -⟩ := CFSG.SectionRank.Tits_sylow5_square_witness (K := K) hK
  have h1 := Subgroup.card_subgroup_dvd_card (Subgroup.closure ({x, y} : Set _))
  rw [hcard] at h1
  rw [Nat.card_congr e.toEquiv]
  simpa using h1

end Orders

theorem m11TypesDisjoint1522_of_orders
    (hU : PSUThreeThreeOrder) (hD : ThreeD4TwoOrder) :
    M11TypesDisjoint1522 := by
  intro G _ _ L hL
  have h7920 : Nat.card ↥L = 7920 :=
    card_eq_of_isSporadic1522 (s := .M11) CFSG.Sporadic.Mathieu.card_M11 hL
  have hquo : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ∣ 7920 := by
    rw [← h7920]
    exact (CFSG.pCore 2 ↥L).index_dvd_card
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro ⟨-, α, hα, -⟩
    have h1 := Subgroup.card_dvd_of_surjective hα
    rw [h7920, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    revert h1
    decide
  ·
    rintro (⟨-, α, hα, -⟩ | ⟨-, α, hα, hker, -⟩ | ⟨-, hpsu, -⟩)
    · have h1 := Subgroup.card_dvd_of_surjective hα
      have h168 : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 := by
        rw [card_statedSL_two1522 3 (ZMod 2) (by simp)]
        decide
      rw [h7920, h168] at h1
      revert h1
      decide
    · have h1 := Subgroup.card_ker_mul_card_of_surjective hα
      have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin]
        decide
      rw [h7920, hA6] at h1
      have hp : IsPGroup 2 α.ker := hker ▸ CFSG.pCore_isPGroup
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      rw [hk] at h1
      have h22 : 2 ^ k = 22 := by omega
      rcases Nat.lt_or_ge k 5 with hk5 | hk5
      · interval_cases k <;> simp at h22
      · have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk5
        omega
    · have h1 := hU _ hpsu
      rw [h1] at hquo
      revert hquo
      decide
  ·
    rintro ⟨-, hpsl | hpsl⟩
    · have h1 := card_of_isPSL_two1522 4 hpsl
      rw [h1] at hquo
      revert hquo
      simp [Fin.prod_univ_four]
    · have h1 := card_of_isPSL_two1522 5 hpsl
      rw [h1] at hquo
      revert hquo
      simp [Fin.prod_univ_five]
  ·
    rintro (hpsu | htits | hd4)
    · have h1 := hU _ hpsu
      omega
    · have h1 := twentyfive_dvd_card_of_isTits1522 htits
      rw [h7920] at h1
      revert h1
      decide
    · have h1 := hD _ hd4
      omega
  ·
    rintro (h | h | h | h | h | h)
    · exact not_isSporadic_quotient1522 (Subgroup.center ↥L) h7920
        (s := .J2) (CFSG.Sporadic.J2.card_J2) (by norm_num) h
    · exact not_isSporadic_quotient1522 (Subgroup.center ↥L) h7920
        (s := .He) (CFSG.Sporadic.He.card_He) (by norm_num) h
    · exact not_isSporadic_quotient1522 (Subgroup.center ↥L) h7920
        (s := .M12) (CFSG.Sporadic.Mathieu.card_M12) (by norm_num) h
    · exact not_isSporadic_quotient1522 (Subgroup.center ↥L) h7920
        (s := .M22) (CFSG.Sporadic.Mathieu.card_M22) (by norm_num) h
    · exact not_isSporadic_quotient1522 (Subgroup.center ↥L) h7920 (s := .M23) card_nativeM23_1522
        (by norm_num) h
    · exact not_isSporadic_quotient1522 (Subgroup.center ↥L) h7920
        (s := .M24) (CFSG.Sporadic.Mathieu.card_M24) (by norm_num) h
  ·
    rintro (hpsl | hpsl)
    · have h1 := card_of_isPSL_two1522 4 hpsl
      rw [h7920] at h1
      revert h1
      simp [Fin.prod_univ_four]
    · have h1 := card_of_isPSL_two1522 5 hpsl
      rw [h7920] at h1
      revert h1
      simp [Fin.prod_univ_five]

end CFSG.Quasithin
