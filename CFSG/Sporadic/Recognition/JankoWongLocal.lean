module

public import CFSG.Sporadic.Recognition.JankoWongLemma13b

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Subgroup CFSG.GH74 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem Setup.local_structure
    (S : Setup G) :
    27 ∣ Nat.card G ∧ 3 ^ 6 ∣ Nat.card G ∧
      ∃ s : G, orderOf s = 3 ∧ ∃ Nn : Subgroup G,
        Nn = (CFSG.oddCore ↥(normalizer ((zpowers s : Subgroup G) : Set G))).map
          (normalizer ((zpowers s : Subgroup G) : Set G)).subtype ∧
        s ∈ Nn ∧ Nat.card Nn = 81 ∧ (∀ y ∈ Nn, ∀ w ∈ Nn, y * w = w * y) ∧
        (∀ y ∈ Nn, y ^ 3 = 1) ∧ (∀ g : G, (∀ y ∈ Nn, y * g = g * y) → g ∈ Nn) := by
  obtain ⟨c⟩ := S.exists_ctx
  exact ⟨S.twentySeven_dvd_card, S.three_pow_six_dvd_card, c.s, c.orderOf_s, c.OG, rfl,
    c.zpowers_le_OG (mem_zpowers c.s), c.card_OG_eq_81, c.OG_comm, c.OG_pow_three,
    c.centralizer_OG_le⟩

theorem Setup.local_structure_centralizers
    (S : Setup G) :
    ∃ (s : G) (P Nn : Subgroup G), orderOf s = 3 ∧ s ∈ P ∧ Nat.card P = 9 ∧
      P ≤ centralizer ({S.z} : Set G) ∧ P ≤ Nn ∧
      Nn = (CFSG.oddCore ↥(normalizer ((zpowers s : Subgroup G) : Set G))).map
        (normalizer ((zpowers s : Subgroup G) : Set G)).subtype ∧
      Nat.card Nn = 81 ∧
      (Nat.card (centralizer ({s} : Set G)) = 324 ∨ Nat.card (centralizer ({s} : Set G)) = 972) ∧
      centralizer (P : Set G) = Nn ⊔ zpowers S.z ∧ Nat.card (centralizer (P : Set G)) = 162 ∧
      (∀ g ∈ normalizer (P : Set G), ∀ y ∈ Nn, g * y * g⁻¹ ∈ Nn) := by
  obtain ⟨c⟩ := S.exists_ctx
  refine ⟨c.s, c.PG, c.OG, c.orderOf_s, c.s_mem_PG, c.card_PG, ?_, c.PG_le_OG c.card_OG_eq_81,
    rfl, c.card_OG_eq_81, ?_, c.CP_eq, c.card_CP, fun g hg => c.OG_normalized_of_normalizes_PG hg⟩
  · rintro _ ⟨p, -, rfl⟩
    exact p.2
  rcases c.card_Cg_cases with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem nonempty_setup_of_doubleCover (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {z : G} (hz : orderOf z = 2) (hH : IsDoubleCoverOfAlt ↥(centralizer ({z} : Set G)) 8) :
    Nonempty (Setup G) := by
  have hz1 : z ≠ 1 := fun e => by
    rw [e, orderOf_one] at hz; exact absurd hz (by norm_num)
  obtain ⟨ρ, hρ⟩ := isCover8_of_isDoubleCoverOfAlt hH (zIn_mem_center z)
    (fun e => hz1 (congrArg Subtype.val e))
  exact ⟨⟨z, ρ, hz, hρ, hs, hnab⟩⟩

theorem local_structure_of_doubleCover
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {z : G} (hz : orderOf z = 2) (hH : IsDoubleCoverOfAlt ↥(centralizer ({z} : Set G)) 8) :
    27 ∣ Nat.card G ∧ 3 ^ 6 ∣ Nat.card G ∧
      ∃ s : G, orderOf s = 3 ∧ ∃ Nn : Subgroup G,
        Nn = (CFSG.oddCore ↥(normalizer ((zpowers s : Subgroup G) : Set G))).map
          (normalizer ((zpowers s : Subgroup G) : Set G)).subtype ∧
        s ∈ Nn ∧ Nat.card Nn = 81 ∧ (∀ y ∈ Nn, ∀ w ∈ Nn, y * w = w * y) ∧
        (∀ y ∈ Nn, y ^ 3 = 1) ∧ (∀ g : G, (∀ y ∈ Nn, y * g = g * y) → g ∈ Nn) := by
  obtain ⟨S⟩ := nonempty_setup_of_doubleCover hs hnab hz hH
  exact S.local_structure

theorem local_structure_of_perfect_centralizer
    (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2)
    (hperf : Group.IsPerfect ↥(centralizer ({t} : Set G)))
    (hcen : Subgroup.center ↥(centralizer ({t} : Set G)) = zpowers (zIn t))
    (hquot : Nonempty (↥(centralizer ({t} : Set G)) ⧸ zpowers (zIn t) ≃*
      alternatingGroup (Fin 8))) :
    27 ∣ Nat.card G ∧ 3 ^ 6 ∣ Nat.card G ∧
      ∃ s : G, orderOf s = 3 ∧ ∃ Nn : Subgroup G,
        Nn = (CFSG.oddCore ↥(normalizer ((zpowers s : Subgroup G) : Set G))).map
          (normalizer ((zpowers s : Subgroup G) : Set G)).subtype ∧
        s ∈ Nn ∧ Nat.card Nn = 81 ∧ (∀ y ∈ Nn, ∀ w ∈ Nn, y * w = w * y) ∧
        (∀ y ∈ Nn, y ^ 3 = 1) ∧ (∀ g : G, (∀ y ∈ Nn, y * g = g * y) → g ∈ Nn) :=
  local_structure_of_doubleCover hs hnab ht
    (isDoubleCoverOfAlt_of_perfect_centralizer ht hperf hcen hquot)

end CFSG.Sporadic.Recognition.JankoWong
