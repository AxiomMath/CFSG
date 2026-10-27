module

public import CFSG.RankThree.PartTwo.Sec21.FF84S48
public import CFSG.RankThree.PartTwo.Sec21.FF84S4BIndex

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

namespace S48Ctx

variable (c : S48Ctx b L B K b₁ b₂) {U : Subgroup G} (hU : U ∈ PiStar (Cen b) B 2)

include c hU

theorem U_le_S : U ≤ Op 2 (Nor U) :=
  op2_of_normal Subgroup.le_normalizer (normal_subgroupOf_of le_rfl Subgroup.le_normalizer) hU.2.1

theorem B_le_nor_S : B ≤ Nor (Op 2 (Nor U)) := hU.2.2.1.trans (le_nor_op2 _)

theorem B_nor_inf_cen {x : G} (hx : x ∈ B) {Y : Subgroup G} (hBY : B ≤ Nor Y) :
    B ≤ Nor (Y ⊓ Cen x) := by
  intro g hg
  refine nor_inf (hBY hg) (Subgroup.le_normalizer ?_)
  exact Subgroup.mem_centralizer_singleton_iff.2 (c.hBcomm g hg x hx)

theorem U_ne_bot : U ≠ ⊥ := by
  intro h
  have := c.piU_card hU
  rw [h] at this
  simp at this

theorem S48_CSb : Op 2 (Nor U) ⊓ Cen b = U :=
  hU.2.2.2 _ (le_inf (U_le_S c hU) hU.1) inf_le_right ((op2_isPGroup _).to_le inf_le_left)
    (B_nor_inf_cen c hU (mem_b c.sec) (B_le_nor_S c hU))

theorem S48_charTwo : Nor U ⊓ CenS (Op 2 (Nor U)) ≤ Op 2 (Nor U) :=
  B_charTwo c.sec.hyp.char2 hU.2.1 (U_ne_bot c hU)

theorem S48_index4 : 4 ≤ (Op 2 (Nor U) ⊓ Cen b).relIndex (Op 2 (Nor U)) := by
  refine B_coprime_index_four (op2_isPGroup _) c.ord_b (B_le_nor_S c hU (mem_b c.sec)) ?_
  intro hle
  have hbS : b ∈ Op 2 (Nor U) := by
    apply S48_charTwo c hU
    refine ⟨hU.2.2.1 (mem_b c.sec), Subgroup.mem_centralizer_iff.2 ?_⟩
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hs)
  obtain ⟨k, hk⟩ := (op2_isPGroup (Nor U)) ⟨b, hbS⟩
  have hbk : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 : 3 ∣ 2 ^ k := by
    have := orderOf_dvd_of_pow_eq_one hbk
    rwa [c.ord_b] at this
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem X_cen {X : Subgroup G} (hX : IsPGroup 2 X) (hBX : B ≤ Nor X)
    (hSX : Op 2 (Nor U) ≤ X) : X ⊓ Cen b = U :=
  hU.2.2.2 _ (le_inf ((U_le_S c hU).trans hSX) hU.1) inf_le_right (hX.to_le inf_le_left)
    (B_nor_inf_cen c hU (mem_b c.sec) hBX)

theorem S48_elemab : IsElemAb 2 6 (Op 2 (Nor U)) ∧ Op 2 (Nor U) ∈ PiStar ⊤ B 2 := by
  set S := Op 2 (Nor U) with hSdef
  have hSp : IsPGroup 2 S := op2_isPGroup _
  have hBS : B ≤ Nor S := B_le_nor_S c hU
  obtain ⟨X, hX, hSX⟩ := exists_piStar_ge (X := (⊤ : Subgroup G)) (A := B) le_top hSp hBS
  have hXp : IsPGroup 2 X := hX.2.1
  have hBX : B ≤ Nor X := hX.2.2.1
  obtain ⟨n, d⟩ := c.core_ex hU hXp hBX (X_cen c hU hXp hBX hSX) (Or.inl rfl)
  obtain ⟨hEAX, -, hX4, hW16⟩ := d.core
  have hXle : Nat.card X ≤ 64 := by omega
  have hrel := Subgroup.relIndex_mul_card (H := S ⊓ Cen b) (K := S)
  have e : (S ⊓ Cen b) ⊓ S = U := by
    rw [S48_CSb c hU]; exact inf_eq_left.2 (U_le_S c hU)
  rw [e, c.piU_card hU] at hrel
  have h4 : 4 ≤ (S ⊓ Cen b).relIndex S := S48_index4 c hU
  have hS64 : 64 ≤ Nat.card S := by omega
  have hSXcard : Nat.card S ≤ Nat.card X := Subgroup.card_le_of_le hSX
  have hSXeq : S = X := Subgroup.eq_of_le_of_card_ge hSX (by omega)
  refine ⟨EA2.isElemAb (hEAX.mono hSX) (by
    have : Nat.card S = 64 := by omega
    rw [this]; norm_num), ?_⟩
  rw [hSXeq]
  exact hX

theorem S_card_W {cc : G} (hcc : cc = b₁ ∨ cc = b₂) :
    EA2 (Op 2 (Nor U) ⊓ Cen cc) ∧ Nat.card ↥(Op 2 (Nor U) ⊓ Cen cc) = 16 := by
  obtain ⟨hEA6, hSPi⟩ := S48_elemab c hU
  obtain ⟨n, d⟩ := c.core_ex hU (op2_isPGroup _) (B_le_nor_S c hU) (S48_CSb c hU) hcc
  obtain ⟨-, -, hX4, -⟩ := d.core
  refine ⟨d.hW.1, ?_⟩
  rw [hEA6.2] at hX4
  omega

theorem S48_b2 : Nat.card ↥(Op 2 (Nor U) ⊓ Cen b₂) = 16 ∧ Nat.card ↥(Op 2 (Nor U) ⊓ Cen b₁) = 16 ∧
    Op 2 (Nor U) ⊓ CenS B = ⊥ := by
  refine ⟨(S_card_W c hU (Or.inr rfl)).2, (S_card_W c hU (Or.inl rfl)).2, ?_⟩
  rw [eq_bot_iff]
  rintro x ⟨hxS, hxB⟩
  have hxB := Subgroup.mem_centralizer_iff.1 hxB
  have hxb : x ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.2 (hxB b (mem_b c.sec)).symm
  have hxU : x ∈ U := by rw [← S48_CSb c hU]; exact ⟨hxS, hxb⟩
  have hx12 : x ∈ Cen (b₁ * b₂) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h1 := hxB b₁ (mem_b₁ c.sec)
    have h2 := hxB b₂ (mem_b₂ c.sec)
    calc x * (b₁ * b₂) = b₁ * x * b₂ := by rw [← mul_assoc, ← h1]
      _ = b₁ * (b₂ * x) := by rw [mul_assoc, ← h2]
      _ = b₁ * b₂ * x := by rw [mul_assoc]
  have : x ∈ U ⊓ Cen (b₁ * b₂) := ⟨hxU, hx12⟩
  rw [(c.piU hU).2.2.2] at this
  exact this

end S48Ctx

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
