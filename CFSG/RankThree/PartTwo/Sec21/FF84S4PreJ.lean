module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreSC
public import CFSG.RankThree.PartTwo.Sec21.FF84S3B

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem U_le_B (h : FF84Sec4 b L B K b₁ b₂) :
    Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G) ≤ B := (Subgroup.closure_le _).2 (by
  intro z hz
  rcases hz with rfl | hz
  · exact bb₁sq_mem h
  · rw [Set.mem_singleton_iff.1 hz]; exact mem_b₂ h)

theorem card_U (h : FF84Sec4 b L B K b₁ b₂) :
    Nat.card (Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G)) = 9 := by
  have h1 := Subgroup.relIndex_mul_card (Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G)) B
  rw [inf_of_le_left (U_le_B h), relIndex_U h, card_B h] at h1
  omega

theorem orderOf_bb₁sq (h : FF84Sec4 b L B K b₁ b₂) : orderOf (b * b₁ ^ 2) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (bb₁sq_cube h) (bb₁sq_ne_one h)

theorem orderOf_b₂ (h : FF84Sec4 b L B K b₁ b₂) : orderOf b₂ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (pow3_of_mem h (mem_b₂ h)) (b₂_ne_one h)

theorem bb₁sq_mem_E (h : FF84Sec4 b L B K b₁ b₂) :
    b * b₁ ^ 2 ∈ Subgroup.closure ({b, b₁} : Set G) :=
  mul_mem (Subgroup.subset_closure (by simp)) (pow_mem (Subgroup.subset_closure (by simp)) 2)

theorem P₁_inf_P₂ (h : FF84Sec4 b L B K b₁ b₂) :
    Subgroup.zpowers (b * b₁ ^ 2) ⊓ Subgroup.zpowers b₂ = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.zpowers (b * b₁ ^ 2) ⊓ Subgroup.zpowers b₂ with hCdef
  have hC : C ≤ Subgroup.zpowers b₂ := inf_le_right
  have hc2 : Nat.card (Subgroup.zpowers b₂) = 3 := by rw [Nat.card_zpowers, orderOf_b₂ h]
  have hcard : Nat.card C ∣ 3 := hc2 ▸ Subgroup.card_dvd_of_le hC
  rcases (Nat.dvd_prime Nat.prime_three).1 hcard with h1 | h3
  · exact Subgroup.card_eq_one.1 h1
  · exfalso
    have heq : C = Subgroup.zpowers b₂ :=
      Subgroup.eq_of_le_of_card_ge hC (by rw [h3, hc2])
    have hb : b₂ ∈ C := heq ▸ Subgroup.mem_zpowers b₂
    exact b₂_notin_E h ((Subgroup.zpowers_le.2 (bb₁sq_mem_E h)) hb.1)

theorem zpowers_sup_eq (x y : G) :
    Subgroup.zpowers x ⊔ Subgroup.zpowers y = Subgroup.closure ({x, y} : Set G) := by
  apply le_antisymm
  · exact sup_le (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))
      (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))
  · refine (Subgroup.closure_le _).2 ?_
    rintro z (rfl | hz)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rw [Set.mem_singleton_iff.1 hz]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem S41_J (h23 : FF84_2_3) (h : FF84Sec4 b L B K b₁ b₂) {D₀ : Subgroup G}
    (hDD : D₀ ≤ Cen (b * b₁)) (hne : D₀ ≠ ⊤)
    (hsyl : IsSylowOf 3 (Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G)) D₀) :
    ∃ J₁ J₂ : Subgroup G, J₁ ≤ D₀ ∧ J₂ ≤ D₀ ∧ (∀ g ∈ D₀, ∀ x ∈ J₁, g * x * g⁻¹ ∈ J₁) ∧
      (∀ g ∈ D₀, ∀ x ∈ J₂, g * x * g⁻¹ ∈ J₂) ∧ Subgroup.zpowers (b * b₁ ^ 2) ≤ J₁ ∧
      Subgroup.zpowers b₂ ≤ J₂ ∧ J₁ ⊓ J₂ ≤ Opp 3 D₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U := Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G) with hU
  set P₁ := Subgroup.zpowers (b * b₁ ^ 2) with hP₁
  set P₂ := Subgroup.zpowers b₂ with hP₂
  have hUD : U ≤ D₀ := hsyl.1
  have hsup : P₁ ⊔ P₂ = U := zpowers_sup_eq _ _
  have hP₁U : P₁ ≤ U := hsup ▸ le_sup_left
  have hP₂U : P₂ ≤ U := hsup ▸ le_sup_right
  have hKG := S3.B_kgroup h.hyp.iii D₀ hne
  have hmain := h23 ↥D₀ hKG (U.subgroupOf D₀) (P₁.subgroupOf D₀) (P₂.subgroupOf D₀)
    ⟨le_top, hsyl.2.1.comap_subtype, by
      rw [Subgroup.relIndex_top_right]
      exact hsyl.2.2⟩
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUD).toEquiv]; exact card_U h)
    (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hP₁U.trans hUD)).toEquiv, hP₁,
        Nat.card_zpowers, orderOf_bb₁sq h])
    (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hP₂U.trans hUD)).toEquiv, hP₂,
        Nat.card_zpowers, orderOf_b₂ h])
    (by rw [← Subgroup.subgroupOf_sup (hP₁U.trans hUD) (hP₂U.trans hUD), hsup])
    (by
      have e : P₁.subgroupOf D₀ ⊓ P₂.subgroupOf D₀ = (P₁ ⊓ P₂).subgroupOf D₀ :=
        (Subgroup.comap_inf _ _ _).symm
      rw [e, P₁_inf_P₂ h, Subgroup.bot_subgroupOf])
    ⟨fun x hx => hP₁U hx, fun a ha g hg => by
      have := sc_P₁ h (a := (a : G)) (g := (g : G)) ha (hDD g.2) (U_le_B h hg)
      show ((g⁻¹ * a * g : ↥D₀) : G) ∈ P₁; simpa using this⟩
    ⟨fun x hx => hP₂U hx, fun a ha g hg => by
      have := sc_P₂ h (a := (a : G)) (g := (g : G)) ha (hDD g.2) (U_le_B h hg)
      show ((g⁻¹ * a * g : ↥D₀) : G) ∈ P₂; simpa using this⟩
  refine ⟨(Subgroup.normalClosure ((P₁.subgroupOf D₀ : Subgroup ↥D₀) : Set ↥D₀)).map D₀.subtype,
    (Subgroup.normalClosure ((P₂.subgroupOf D₀ : Subgroup ↥D₀) : Set ↥D₀)).map D₀.subtype,
    Subgroup.map_subtype_le _, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹,
      (Subgroup.normalClosure_normal).conj_mem x hx ⟨g, hg⟩, by simp⟩
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹,
      (Subgroup.normalClosure_normal).conj_mem x hx ⟨g, hg⟩, by simp⟩
  · intro x hx
    exact ⟨⟨x, hUD (hP₁U hx)⟩, Subgroup.subset_normalClosure hx, rfl⟩
  · intro x hx
    exact ⟨⟨x, hUD (hP₂U hx)⟩, Subgroup.subset_normalClosure hx, rfl⟩
  · rintro x ⟨⟨j₁, hj₁, rfl⟩, ⟨j₂, hj₂, hj⟩⟩
    have : j₂ = j₁ := Subtype.ext hj
    subst this
    exact ⟨j₂, hmain ⟨hj₁, hj₂⟩, rfl⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
