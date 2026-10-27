module

public import CFSG.Quasithin.Background.E3Gen
public import CFSG.LocalAnalysis.WeakClosure81.W19Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mBarGT_card_le {M V₀ V : Subgroup G} {n : ℕ} (h : MBarGT M V₀ V n) :
    2 ^ (n + 1) ≤ Nat.card V := by
  classical
  by_cases hex : ∃ m ∈ M, ¬ CentralizesMod V₀ V m ∧ CentralizesMod V₀ V (m * m)
  · obtain ⟨m, hm, h1, h2⟩ := hex
    have h3 := h.1 m hm h1 h2
    have hpos : 0 < Nat.card (centMod V₀ V m) := by
      haveI : Nonempty (centMod V₀ V m) := ⟨⟨1, V.one_mem, by simp⟩⟩
      exact Nat.card_pos
    calc 2 ^ (n + 1) ≤ 2 ^ (n + 1) * Nat.card (centMod V₀ V m) :=
          Nat.le_mul_of_pos_right _ hpos
      _ ≤ Nat.card V := h3
  · push Not at hex
    have h3 := h.2 (fun m hm h2 => by_contra fun h1 => hex m hm h1 h2)
    calc 2 ^ (n + 1) ≤ 2 ^ (n + 1) * Nat.card V₀ := Nat.le_mul_of_pos_right _ Nat.card_pos
      _ ≤ Nat.card V := h3

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem isPGroup_V (c : MinCex193 D V₀ V p X) : IsPGroup 2 V :=
  B2F.isPGroup_of_isElemAbelian c.setting.isElemAbelian

theorem V₀_le_V (c : MinCex193 D V₀ V p X) : V₀ ≤ V := c.setting.pair.le

theorem V_le_M (c : MinCex193 D V₀ V p X) : V ≤ D.M := c.setting.pair.le_M

theorem V_le_T (c : MinCex193 D V₀ V p X) : V ≤ D.T :=
  (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 c.V_le_M c.setting.pair.le_normalizer
    c.isPGroup_V).trans
    (E1.pCoreOf_two_le_of_isSylowIn (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM))

theorem V_le_H (c : MinCex193 D V₀ V p X) : V ≤ X ⊔ D.T := c.V_le_T.trans le_sup_right

theorem V_le_pCoreOf (c : MinCex193 D V₀ V p X) : V ≤ pCoreOf 2 (X ⊔ D.T) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 c.V_le_H
    (c.hyp.le_M.trans c.setting.pair.le_normalizer) c.isPGroup_V

theorem three_le_rk (c : MinCex193 D V₀ V p X) : 3 ≤ rk ↥V := by
  have h1 := mBarGT_card_le c.mbar
  rw [card_eq_two_pow_of_isPGroup c.isPGroup_V] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

theorem V_le_wClos (c : MinCex193 D V₀ V p X) : V ≤ E3.wClos V 1 D.T :=
  E3.le_wClos_of_mQuot_le_self c.setting.isElemAbelian c.V_le_T le_rfl
    (by rw [E3.mQuot_self]; exact Nat.zero_le _) (by have := c.three_le_rk; omega)

theorem isPGroup_wClos (c : MinCex193 D V₀ V p X) : IsPGroup 2 (E3.wClos V 1 D.T) :=
  D.sylowM.isPGroup.to_le (E3.wClos_le 1 D.T)

theorem inf_Z193_ne_bot (c : MinCex193 D V₀ V p X) : V₀ ⊓ Z193 D V ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := E3.wClos V 1 D.T with hW
  have hWT : W ≤ D.T := E3.wClos_le 1 D.T
  have hV₀W : V₀ ≤ W := c.V₀_le_V.trans c.V_le_wClos
  haveI hnil : Group.IsNilpotent ↥W := c.isPGroup_wClos.isNilpotent
  haveI hnorm : (V₀.subgroupOf W).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hgM : (g : G) ∈ D.M := D.sylowM.le (hWT g.2)
    have := (Subgroup.mem_normalizer_iff.1 (c.setting.pair.le_normalizer₀ hgM) (x : G)).1 hx
    simpa using this
  have hne : V₀.subgroupOf W ≠ ⊥ := by
    intro hbot
    apply c.ne_bot
    rw [← Subgroup.map_subgroupOf_eq_of_le hV₀W, hbot, Subgroup.map_bot]
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have haV : ((a.1 : ↥W) : G) ∈ V₀ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 a.2).1
  have haZ : (a.1 : ↥W) ∈ Subgroup.center ↥W := (Subgroup.mem_inf.1 a.2).2
  have hsq : ((a.1 : ↥W) : G) ^ 2 = 1 := c.setting.pair.elemAbelian₀.2 _ haV
  have hZ : ((a.1 : ↥W) : G) ∈ Z193 D V := by
    unfold Z193 omegaOneCenterOf omegaOneOf
    refine Subgroup.subset_closure ⟨⟨(a.1 : ↥W).2, Subgroup.mem_centralizer_iff.2 ?_⟩, hsq⟩
    intro w hw
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 haZ ⟨w, hw⟩)
  intro hbot
  have hmem : ((a.1 : ↥W) : G) ∈ V₀ ⊓ Z193 D V := Subgroup.mem_inf.2 ⟨haV, hZ⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact ha (Subtype.ext (Subtype.ext hmem))

theorem Z193_le_cClos (_c : MinCex193 D V₀ V p X) : Z193 D V ≤ E3.cClos V 1 D.T := by
  unfold Z193 omegaOneCenterOf omegaOneOf E3.cClos
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨⟨hxW, hxC⟩, -⟩
  exact ⟨E3.wClos_le 1 D.T hxW, hxC⟩

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81
