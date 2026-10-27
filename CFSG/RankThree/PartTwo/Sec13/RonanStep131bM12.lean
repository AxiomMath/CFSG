module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bPlan

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

structure InvData {G : Type} [Group G] (E : Subgroup G) (b c : G) (Y : Subgroup G) (t : G)
    (EY : Subgroup G) : Prop where
  mem_Y : t ∈ Y
  comm_b : t * b = b * t
  mem_normalizer : t ∈ Subgroup.normalizer (E : Set G)
  le_E : EY ≤ E
  card_EY : Nat.card EY = 9
  mem_c : c ∈ EY
  not_mem_b : b ∉ EY
  inv : ∀ x ∈ EY, t * x * t⁻¹ = x⁻¹

@[expose] def YCfgMemA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y → a ∈ A

@[expose] def M12Inverting : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      (haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1;
        Nonempty (Y ⧸ solvableRadical Y ≃* CFSG.Blueprint.NativeSporadic.M12)) →
      ∃ (t : G) (EY : Subgroup G), InvData E b c Y t EY

@[expose] def M12NormLComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y → a ∈ A →
      ∀ t : G, t ∈ Subgroup.normalizer (E : Set G) → t * b = b * t →
        t ∈ Subgroup.normalizer (L : Set G) →
        ∀ x ∈ E, t * x * t⁻¹ * x⁻¹ ∈ Subgroup.zpowers c

@[expose] def M12MovesL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y → a ∈ A →
      (haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1;
        Nonempty (Y ⧸ solvableRadical Y ≃* CFSG.Blueprint.NativeSporadic.M12)) →
      ∀ (t : G) (EY : Subgroup G), InvData E b c Y t EY →
        t ∉ Subgroup.normalizer (L : Set G) → False

theorem false_of_inv_data {G : Type} [Group G] [Finite G] {E : Subgroup G} {b c t : G}
    {Y EY : Subgroup G} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hc : c ∈ E) (hc1 : c ≠ 1)
    (hd : InvData E b c Y t EY)
    (hcomm : ∀ x ∈ E, t * x * t⁻¹ * x⁻¹ ∈ Subgroup.zpowers c) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : c ^ 3 = 1 := hEe.2 c hc
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hle : EY ≤ Subgroup.zpowers c := by
    intro x hx
    have h1 := hcomm x (hd.le_E hx)
    rw [show t * x * t⁻¹ * x⁻¹ = x⁻¹ * x⁻¹ by rw [hd.inv x hx]] at h1
    have hx3 : x ^ 3 = 1 := hEe.2 x (hd.le_E hx)
    have hinv : x⁻¹ = x * x := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hx3)
    have hxx : x⁻¹ * x⁻¹ = x := by
      calc x⁻¹ * x⁻¹ = x⁻¹ * (x * x) := by rw [← hinv]
        _ = x := inv_mul_cancel_left x x
    rw [hxx] at h1
    exact h1
  have hcard : Nat.card EY ≤ Nat.card (Subgroup.zpowers c) := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hord, hd.card_EY] at hcard
  exact absurd hcard (by norm_num)

theorem pieceM12_of_residual (h0 : YCfgMemA) (h1 : M12Inverting) (h2 : M12NormLComm)
    (h3 : M12MovesL) : PieceM12 := by
  intro G _ _ A c L E F a b R Y hY hM
  obtain ⟨t, EY, hd⟩ := h1 G A c L E F a b R Y hY hM
  have haA : a ∈ A := h0 G A c L E F a b R Y hY
  by_cases htL : t ∈ Subgroup.normalizer (L : Set G)
  · exact false_of_inv_data hY.hCfg.hEe hY.hcE hY.hCfg.hD.ne_one hd
      (h2 G A c L E F a b R Y hY haA t hd.mem_normalizer hd.comm_b htL)
  · exact h3 G A c L E F a b R Y hY haA hM t EY hd htL

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
