module

public import CFSG.Quasithin.EmptyFaithful.SBd8Rk2Abs
public import CFSG.Quasithin.Background.GoldschmidtS146RLatG2
public import CFSG.LieType.Chevalley.ExactG2FiniteOrder

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.SteinbergBS

namespace SBd8

section G2Arith

theorem g2Std_nine_dvd {q n : ℕ} (hq : q = 2 ^ n) :
    3 ∣ (q - 1) ^ 2 * q ^ 6 → 9 ∣ (q - 1) ^ 2 * q ^ 6 := by
  intro h
  have h3 : Nat.Prime 3 := Nat.prime_three
  rcases (Nat.Prime.dvd_mul h3).1 h with h1 | h1
  · obtain ⟨k, hk⟩ := h3.dvd_of_dvd_pow h1
    exact Dvd.dvd.mul_right ⟨k ^ 2, by rw [hk]; ring⟩ _
  · exfalso
    have h2 : 3 ∣ q := h3.dvd_of_dvd_pow h1
    rw [hq] at h2
    have h4 := h3.dvd_of_dvd_pow h2
    omega

theorem g2Std_card_ne {q : ℕ} (hq : 4 ≤ q) :
    (q - 1) ^ 2 * q ^ 6 ≠ q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := by
  intro h1
  have h6 : 0 < q ^ 6 := by positivity
  have h2 : (q ^ 6 - 1) * (q ^ 2 - 1) = (q - 1) ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left h6
    calc q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) = q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := by ring
      _ = (q - 1) ^ 2 * q ^ 6 := h1.symm
      _ = q ^ 6 * (q - 1) ^ 2 := by ring
  have hq2 : q < q ^ 2 := by nlinarith
  have hq26 : q ^ 2 ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have ha : q - 1 < q ^ 6 - 1 := by omega
  have hb : q - 1 < q ^ 2 - 1 := by omega
  have := Nat.mul_lt_mul'' ha hb
  rw [h2, sq] at this
  omega

end G2Arith

section G2Std


variable {F : Type} [Field F]

theorem g2Std_solvable_overgroup_le_normalizer [Finite F] (hF4 : 4 ≤ Nat.card F)
    (Y : Subgroup ↥(adjointGroup Tag.G2 F))
    (hUY : (posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) ≤ Y)
    (hY : Group.IsSolvable ↥Y) :
    Y ≤ Subgroup.normalizer
      (((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) :
        Subgroup ↥(adjointGroup Tag.G2 F)) : Set ↥(adjointGroup Tag.G2 F)) := by
  have : Finite (ModGL Tag.G2 F) := finite_modGL
  have hUC : posUnipotent Tag.G2 F ≤ adjointGroup Tag.G2 F := posUnipotent_le_adjointGroup
  have hMC : Y.map (adjointGroup Tag.G2 F).subtype ≤ adjointGroup Tag.G2 F := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hUM : posUnipotent Tag.G2 F ≤ Y.map (adjointGroup Tag.G2 F).subtype := by
    intro u hu
    exact ⟨⟨u, hUC hu⟩, hUY (by rwa [Subgroup.mem_subgroupOf]), rfl⟩
  have hMs : Group.IsSolvable ↥(Y.map (adjointGroup Tag.G2 F).subtype) :=
    Group.isSolvable_of_surjective
      (f := ((adjointGroup Tag.G2 F).subtype.subgroupMap Y))
      (MonoidHom.subgroupMap_surjective _ Y)
  have hB := solvable_ordinary_posUnipotent_overgroups_le_borelGroup Tag.G2 F hF4 hMC hUM hMs
  intro y hy
  have hyB : (y : ModGL Tag.G2 F) ∈ borelGroup Tag.G2 F := hB ⟨y, hy, rfl⟩
  have hyN : (y : ModGL Tag.G2 F) ∈
      Subgroup.normalizer (posUnipotent Tag.G2 F : Set (ModGL Tag.G2 F)) := by
    rw [← (borel_self_normalizers Tag.G2 F).1] at hyB
    exact hyB.2
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key := Subgroup.mem_normalizer_iff.mp hyN (h : ModGL Tag.G2 F)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact key

theorem g2Std_normalizer_eq :
    Subgroup.normalizer
      (((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) :
        Subgroup ↥(adjointGroup Tag.G2 F)) : Set ↥(adjointGroup Tag.G2 F)) =
      (borelGroup Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) := by
  have hUC : posUnipotent Tag.G2 F ≤ adjointGroup Tag.G2 F := posUnipotent_le_adjointGroup
  ext x
  rw [mem_normalizer_subgroupOf_iff hUC x, Subgroup.mem_subgroupOf,
    ← (borel_self_normalizers Tag.G2 F).1, Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem g2Std_card_normalizer [Finite F] :
    Nat.card ↥(Subgroup.normalizer
      (((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) :
        Subgroup ↥(adjointGroup Tag.G2 F)) : Set ↥(adjointGroup Tag.G2 F))) =
      (Nat.card F - 1) ^ 2 * Nat.card F ^ 6 := by
  rw [g2Std_normalizer_eq, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (borelGroup_le_adjointGroup' (τ := Tag.G2) (K := F))).toEquiv,
    card_borelGroup, CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2, card_posUnipotent,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2]

theorem g2Std_normalizer_ne_top [Finite F] (hF4 : 4 ≤ Nat.card F) :
    Subgroup.normalizer
      (((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) :
        Subgroup ↥(adjointGroup Tag.G2 F)) : Set ↥(adjointGroup Tag.G2 F)) ≠ ⊤ := by
  intro h
  have h1 := g2Std_card_normalizer (F := F)
  rw [h, Subgroup.card_top] at h1
  obtain ⟨-, hC, -⟩ := exact_G2_finite_order F (rfl : Nat.card F = Nat.card F)
  rw [hC] at h1
  exact g2Std_card_ne hF4 h1.symm

theorem g2Std_isSylowTwoOf [Finite F] [CharP F 2] :
    IsSylowTwoOf ((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F)) ⊤ := by
  have : Finite (ModGL Tag.G2 F) := finite_modGL
  exact isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
    (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := F) 2).1)

theorem famG2_std [Finite ↥(adjointGroup Tag.G2 F)] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) {A : Subgroup (MulAut ↥(adjointGroup Tag.G2 F))}
    {K : Subgroup ↥(adjointGroup Tag.G2 F)}
    (d : OvgData ↥(adjointGroup Tag.G2 F) A
      ((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F)) K) : False := by
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine rank2_false d (GoldS146R.latShape_adjointGroup_G2 hn hF)
    (fun Y hUY hY => g2Std_solvable_overgroup_le_normalizer hF4 Y hUY hY)
    (g2Std_normalizer_ne_top hF4) ?_
  rw [g2Std_card_normalizer]
  exact g2Std_nine_dvd hF

end G2Std

end SBd8

end CFSG.Quasithin
