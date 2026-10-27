module

public import CFSG.Sporadic.Recognition.JankoWongLemma17c
public import CFSG.Sporadic.Recognition.JankoWongLemma17b

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

theorem card_sup_mul_card_inf_ge {G : Type*} [Group G] [Finite G] (A B : Subgroup G) :
    Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by
  have e1 : A.relIndex B * Nat.card ↥(A ⊓ B) = Nat.card B := by
    rw [Subgroup.relIndex_mul_card]
  have e2 : A.relIndex (A ⊔ B) * Nat.card A = Nat.card ↥(A ⊔ B) := by
    have := Subgroup.relIndex_mul_card A (A ⊔ B)
    rwa [inf_eq_left.mpr le_sup_left] at this
  have hne0 : A.relIndex (A ⊔ B) ≠ 0 := by
    intro h
    rw [h] at e2
    have : 0 < Nat.card ↥(A ⊔ B) := Nat.card_pos
    omega
  have hle : A.relIndex B ≤ A.relIndex (A ⊔ B) := Subgroup.relIndex_le_of_le_right le_sup_right hne0
  calc Nat.card A * Nat.card B = Nat.card A * (A.relIndex B * Nat.card ↥(A ⊓ B)) := by rw [e1]
    _ ≤ Nat.card A * (A.relIndex (A ⊔ B) * Nat.card ↥(A ⊓ B)) := by gcongr
    _ = Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by rw [← e2]; ring

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

theorem PG_inf_MG_le : c.PG ⊓ c.MG ≤ zpowers (c.a : G) := by
  intro y hy
  obtain ⟨hyP, hyM⟩ := hy
  obtain ⟨hyK, hyq⟩ := c.mem_MG_iff.mp hyM
  obtain ⟨p, -, rfl⟩ := hyP
  have hz : ((p : S.H) : G) * S.z = S.z * ((p : S.H) : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp p.2
  have hmem : (⟨(p : G), hyK⟩ : ↥c.Kg) ∈ CFSG.oddCore ↥c.Kg ⊓ centralizer ({c.zK} : Set ↥c.Kg) :=
    ⟨hyq, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hz)⟩
  rw [c.bsStructure.2.2.1] at hmem
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
  have := congrArg Subtype.val hj
  simpa [Ctx.aK] using this

theorem card_MG_inf_OG_eq
    : Nat.card ↥(c.MG ⊓ c.OG) = 27 := by
  have h27 := c.card_MG_inf_OG
  have hdvd : Nat.card ↥(c.MG ⊓ c.OG) ∣ 81 := by
    rw [← c.card_OG_eq_81]; exact Subgroup.card_dvd_of_le inf_le_right
  have hne : c.MG ⊓ c.OG ≠ c.OG := by
    intro h
    have hPN : c.PG ≤ c.OG := fun x hx => c.PG_le_OG c.card_OG_eq_81 hx
    have hle : c.PG ≤ c.PG ⊓ c.MG := fun x hx => by
      have hxMO : x ∈ c.MG ⊓ c.OG := by rw [h]; exact hPN hx
      exact ⟨hx, hxMO.1⟩
    have h1 := Subgroup.card_le_of_le (hle.trans c.PG_inf_MG_le)
    rw [Nat.card_zpowers, orderOf_aG, c.card_PG] at h1
    omega
  have hlt : Nat.card ↥(c.MG ⊓ c.OG) < 81 := by
    refine lt_of_le_of_ne (Nat.le_of_dvd (by norm_num) hdvd) (fun h => hne ?_)
    exact Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, c.card_OG_eq_81])
  have hdvd' : Nat.card ↥(c.MG ⊓ c.OG) ∣ 3 ^ 4 := by
    rw [show (3 : ℕ) ^ 4 = 81 by norm_num]; exact hdvd
  obtain ⟨j, hj, hj3⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd'
  rw [hj3] at h27 hlt ⊢
  interval_cases j <;> omega

variable {c}

theorem IsW.MG_sup_OG
    {W : Subgroup G} (hW : c.IsW W) : c.MG ⊔ c.OG = W := by
  have hle : c.MG ⊔ c.OG ≤ W := sup_le (c.MG_le_W hW) hW.OG_le
  have h := card_sup_mul_card_inf_ge c.MG c.OG
  rw [c.card_MG, (c.isPGroup_three_oddCore hW).2, c.card_OG_eq_81, c.card_MG_inf_OG_eq] at h
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hW.card]
  omega

variable (c)

theorem lemma17
    : ∃ W : Subgroup G, IsPGroup 3 W ∧ Nat.card W = 3 ^ 6 ∧ (Nat.card G).factorization 3 = 6 ∧
      c.OG ≤ W ∧ W ≤ c.NG ∧ (∀ w ∈ W, w * (c.a : G) = (c.a : G) * w) ∧
      (∀ y : G, (y ∈ W ∧ ∀ w ∈ W, w * y = y * w) ↔ y ∈ zpowers (c.a : G)) ∧
      normalizer (W : Set G) = c.NG ⊓ normalizer ((zpowers (c.a : G) : Subgroup G) : Set G) ∧
      Nat.card ↥(normalizer (W : Set G)) = 2 ^ 3 * 3 ^ 6 ∧
      IsExtraspecialThree c.MG (c.a : G) ∧ c.MG ≤ W ∧ Nat.card ↥c.Kg = 29160 ∧
      Nat.card ↥(c.MG ⊓ c.OG) = 27 ∧ c.MG ⊔ c.OG = W := by
  obtain ⟨W, hW⟩ := c.exists_isW
  refine ⟨W, hW.isPGroup, hW.card, hW.factorization_three_card, hW.OG_le, hW.le_NG, hW.comm_a,
    fun y => ?_, hW.normalizer_eq, by rw [hW.card_normalizer]; norm_num,
    c.isExtraspecialThree_MG hW, c.MG_le_W hW, ?_, c.card_MG_inf_OG_eq, hW.MG_sup_OG⟩
  · rw [← hW.centerW_eq_zpowers_a, mem_centerW]
  · rw [c.card_Kg_eq, (c.isPGroup_three_oddCore hW).2]; norm_num

end Ctx

theorem factorization_three_card_eq (S : Setup G)
    : (Nat.card G).factorization 3 = 6 := by
  obtain ⟨c⟩ := S.exists_ctx
  obtain ⟨W, hW⟩ := c.exists_isW
  exact hW.factorization_three_card

end Setup

end CFSG.Sporadic.Recognition.JankoWong
