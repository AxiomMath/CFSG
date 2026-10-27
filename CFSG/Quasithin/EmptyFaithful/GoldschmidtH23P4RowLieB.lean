module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowLieA
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6Six

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252.A6

theorem card_Sa_a6 : Nat.card Sa = 24 := by
  obtain ⟨-, hs, -, -, hsn, -, -, -, -, -⟩ := sizes_ok
  rw [card_of_list R6.enc_inj Sa saL hsn mem_Sa (fun r hr => (sound_Sa r hr).imp fun x hx => hx.2)]
  exact hs

theorem card_Sb_a6 : Nat.card Sb = 24 := by
  obtain ⟨-, -, hs, -, -, hsn, -, -, -, -⟩ := sizes_ok
  rw [card_of_list R6.enc_inj Sb sbL hsn mem_Sb (fun r hr => (sound_Sb r hr).imp fun x hx => hx.2)]
  exact hs

theorem card_D0_subgroupOf : Nat.card (D0.subgroupOf A6s) = 8 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe D0_le_A6).toEquiv).trans card_D0

theorem isSylowTwoOf_D0_a6 : IsSylowTwoOf (D0.subgroupOf A6s) ⊤ := by
  have hmul := Subgroup.card_mul_index (D0.subgroupOf A6s)
  rw [card_D0_subgroupOf] at hmul
  have hA : Nat.card ↥A6s = 360 := card_A6
  have hi : (D0.subgroupOf A6s).index = 45 := by omega
  rw [isSylowTwoOf_top_iff, hi]
  exact ⟨IsPGroup.of_card (n := 3) (by rw [card_D0_subgroupOf]; norm_num), by norm_num⟩

theorem card_overgroup_a6 (U : Subgroup ↥A6s) (hU : D0.subgroupOf A6s ≤ U) :
    Nat.card U ∈ [8, 24, 360] := by
  have hinj : Function.Injective A6s.subtype := A6s.subtype_injective
  have hD : D0 ≤ U.map A6s.subtype := fun d hd =>
    ⟨⟨d, D0_le_A6 hd⟩, hU (by rwa [Subgroup.mem_subgroupOf]), rfl⟩
  have hA : U.map A6s.subtype ≤ A6s := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hcard : Nat.card U = Nat.card (U.map A6s.subtype) :=
    (Subgroup.card_map_of_injective hinj).symm
  rw [hcard]
  rcases six_overgroups _ hD hA with h | h | h | h <;> rw [h]
  · simp [card_D0]
  · simp [card_Sa_a6]
  · simp [card_Sb_a6]
  · rw [card_A6]
    simp

theorem noFiveIndex_alternating_six : NoFiveIndex (alternatingGroup (Fin 6)) :=
  NoFiveIndex.of_card_overgroups isSylowTwoOf_D0_a6 card_D0_subgroupOf (by norm_num) [8, 24, 360]
    card_overgroup_a6 (by decide) (by decide)

theorem rowOK_alternating_six : RowOK (alternatingGroup (Fin 6)) where
  center := alternatingGroup.center_eq_bot (by simp)
  out := CFSG.Quasithin.H23Out.out5Pow_alternating (by norm_num)
  idx := noFiveIndex_alternating_six

end CFSG.Quasithin.H23P4
