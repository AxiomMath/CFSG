module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup

public section

open Subgroup

namespace CFSG.Quasithin.A94.He42

theorem card_two_sub_le_four_422 {Y : Type} [Group Y] [Finite Y] (V : Subgroup Y)
    (hV : Nat.card ↥V = 4) (hcent : ∀ v ∈ V, v ≠ 1 → ∀ c : Y, c * v = v * c → c ∈ V)
    (W : Subgroup Y) (hW : IsPGroup 2 W) : Nat.card ↥W ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp : IsPGroup 2 V := IsPGroup.of_card (p := 2) (n := 2) (by rw [hV]; norm_num)
  obtain ⟨P, hVP⟩ := hVp.exists_le_sylow
  have hVne1 : ∃ v ∈ V, v ≠ 1 := by
    haveI : Nontrivial ↥V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV]; norm_num)
    obtain ⟨v, hv⟩ := exists_ne (1 : ↥V)
    exact ⟨v.1, v.2, fun h => hv (Subtype.ext h)⟩
  have hPV : P.toSubgroup = V := by
    by_contra hne
    have hlt : V < P.toSubgroup := lt_of_le_of_ne hVP (fun h => hne h.symm)
    have hQ : IsPGroup 2 P.toSubgroup := P.isPGroup'
    haveI : Group.IsNilpotent ↥P.toSubgroup := hQ.isNilpotent
    have hVtop : V.subgroupOf P.toSubgroup < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
      exact hlt.2
    obtain ⟨q, hqn, hqV⟩ := SetLike.exists_of_lt
      (normalizerCondition_of_isNilpotent (G := ↥P.toSubgroup) _ hVtop)
    have hqN : (q : Y) ∈ normalizer (V : Set Y) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hVP] at hqn
      exact Subgroup.mem_subgroupOf.mp hqn
    have hqQ : (q : Y) ∈ P.toSubgroup := q.2
    have hqV' : (q : Y) ∉ V := fun h => hqV (Subgroup.mem_subgroupOf.mpr h)
    set P₀ : Subgroup Y := normalizer (V : Set Y) ⊓ P.toSubgroup with hP₀
    have hVP₀ : V ≤ P₀ := le_inf (le_normalizer) hVP
    have hqP₀ : (q : Y) ∈ P₀ := Subgroup.mem_inf.mpr ⟨hqN, hqQ⟩
    have hP₀N : P₀ ≤ normalizer (V : Set Y) := inf_le_left
    have hP₀Q : IsPGroup 2 P₀ := hQ.to_le inf_le_right
    haveI : Group.IsNilpotent ↥P₀ := hP₀Q.isNilpotent
    haveI hnormal : (V.subgroupOf P₀).Normal :=
      (normal_subgroupOf_iff_le_normalizer hVP₀).mpr hP₀N
    have hVbot : V.subgroupOf P₀ ≠ ⊥ := by
      intro h
      obtain ⟨v, hvV, hv1⟩ := hVne1
      have hmem : (⟨v, hVP₀ hvV⟩ : ↥P₀) ∈ V.subgroupOf P₀ := Subgroup.mem_subgroupOf.mpr hvV
      rw [h, Subgroup.mem_bot] at hmem
      exact hv1 (congrArg Subtype.val hmem)
    have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hVbot
    obtain ⟨x, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨hxV', hxc⟩ := Subgroup.mem_inf.mp x.2
    have hxV : ((x : ↥P₀) : Y) ∈ V := Subgroup.mem_subgroupOf.mp hxV'
    have hx1 : ((x : ↥P₀) : Y) ≠ 1 := fun h => hx1' (Subtype.ext (Subtype.ext h))
    have hcomm : ∀ c ∈ P₀, c * ((x : ↥P₀) : Y) = ((x : ↥P₀) : Y) * c := by
      intro c hc
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨c, hc⟩)
    exact hqV' (hcent ((x : ↥P₀) : Y) hxV hx1 (q : Y) (hcomm _ hqP₀))
  obtain ⟨Q, hWQ⟩ := hW.exists_le_sylow
  have hcardQ : Nat.card ↥Q.toSubgroup = Nat.card ↥P.toSubgroup := by
    rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity P]
  have hcardP : Nat.card ↥P.toSubgroup = 4 := by rw [hPV, hV]
  calc Nat.card ↥W ≤ Nat.card ↥Q.toSubgroup := Subgroup.card_le_of_le hWQ
    _ = 4 := by rw [hcardQ, hcardP]

end CFSG.Quasithin.A94.He42
