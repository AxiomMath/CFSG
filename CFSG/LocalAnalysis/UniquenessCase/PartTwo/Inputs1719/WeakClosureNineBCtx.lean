module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNCtx

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGW

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW

variable {G : Type} [Group G] [Finite G]

structure Ctx15 (V T N L₁ L₂ : Subgroup G) {X : Type} [Group X] [Finite X] (π : ↥N →* X) :
    Prop where
  hyp : Hyp9 V T
  TN : T ≤ N
  NM : N ≤ normalizer (V : Set G)
  L1N : L₁ ≤ N
  L2N : L₂ ≤ N
  star : Star915 V N L₁ L₂
  surj : Function.Surjective π
  ker : ∀ x : ↥N, π x = 1 ↔ (x : G) ∈ pCoreOf 2 N
  facts : NineFifteenBarFacts X (barSub π L₁) (barSub π L₂) (barSub π T)

omit [Finite G] in
theorem mem_sup_of_mem_barSub {N L : Subgroup G} {X : Type} [Group X] {π : ↥N →* X}
    (hker : ∀ x : ↥N, π x = 1 ↔ (x : G) ∈ pCoreOf 2 N) {x : ↥N} (hx : π x ∈ barSub π L) :
    (x : G) ∈ L ⊔ pCoreOf 2 N := by
  obtain ⟨l, hl, hlx⟩ := hx
  have hq : ((l⁻¹ * x : ↥N) : G) ∈ pCoreOf 2 N :=
    (hker _).1 (by rw [map_mul, map_inv, hlx, inv_mul_cancel])
  have e : (x : G) = (l : G) * ((l⁻¹ * x : ↥N) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hq)

namespace Ctx15

variable {V T N L₁ L₂ : Subgroup G} {X : Type} [Group X] [Finite X] {π : ↥N →* X}
variable (c : Ctx15 V T N L₁ L₂ π)
include c

omit [Finite G] in
theorem elem : IsElemAbelian 2 V := c.hyp.hyp7.1

omit [Finite G] in
theorem ti : IsTI V := c.hyp.hyp7.2.2

omit [Finite G] in
theorem isPGroup_V : IsPGroup 2 V := c.elem.isPGroup

theorem card_V : 8 ≤ Nat.card V := by
  rw [card_eq_two_pow_of_isPGroup c.isPGroup_V]
  calc 8 = 2 ^ 3 := rfl
    _ ≤ 2 ^ rk ↥V := Nat.pow_le_pow_right (by norm_num) c.hyp.rk_gt

theorem V_ne_bot : V ≠ ⊥ := by
  intro h
  have h1 := c.card_V
  rw [h, Subgroup.card_bot] at h1
  omega

omit [Finite G] in
theorem T_le_M : T ≤ normalizer (V : Set G) := c.TN.trans c.NM

omit [Finite G] in
theorem isPGroup_T : IsPGroup 2 T := c.hyp.sylow.isPGroup

theorem V_le_T : V ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : V ≤ pCoreOf 2 (normalizer (V : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      c.isPGroup_V
  exact h1.trans (CFSG.Quasithin.AppendixH.H14.pCoreOf_le_of_sylow c.hyp.sylow.1
    c.hyp.sylow.2.1 c.hyp.sylow.2.2)

omit [Finite G] in
theorem T_sylow_N : IsSylowIn 2 T N := by
  refine ⟨c.TN, c.isPGroup_T, fun hdvd => c.hyp.sylow.2.2 ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex T N _ c.TN c.NM]
  exact dvd_mul_of_dvd_left hdvd _

theorem Q_le_T : pCoreOf 2 N ≤ T :=
  CFSG.Quasithin.AppendixH.H14.pCoreOf_le_of_sylow c.TN c.isPGroup_T c.T_sylow_N.2.2

theorem liftSub_barSub_T : liftSub π (barSub π T) = T :=
  liftSub_barSub c.ker c.Q_le_T c.TN

omit [Finite G] in
theorem one_lt_rk : 1 < rk ↥V := by have := c.hyp.rk_gt; omega

theorem conj_le_wClos_one {g : G} {Y : Subgroup G} (hg : conjSubgroup V g ≤ Y) :
    conjSubgroup V g ≤ E3.wClos V 1 Y :=
  E3.le_wClos_of_mQuot_le c.elem g hg le_rfl (by rw [E3.mQuot_self]; omega) c.one_lt_rk

theorem card_conj (g : G) : 8 ≤ Nat.card (conjSubgroup V g) := by
  rw [E3.card_conjSubgroup V g]
  exact c.card_V

theorem conj_ne_bot (g : G) : conjSubgroup V g ≠ ⊥ := by
  intro hb
  have h1 := c.card_conj g
  rw [hb, Subgroup.card_bot] at h1
  omega

omit [Finite G] in
theorem not_orderOf_three {g : G} (hgM : conjSubgroup V g ≤ normalizer (V : Set G))
    (hgV : conjSubgroup V g ≠ V) {x : G} (hxN : x ∈ N)
    (hx : x ∈ normalizer (conjSubgroup V g : Set G))
    (hgood : x ∈ L₁ ⊔ pCoreOf 2 N ∨ x ∈ L₂ ⊔ pCoreOf 2 N) : orderOf x ≠ 3 :=
  c.star g (fun hg => hgV (conjSubgroup_eq_iff_mem_normalizer.2 hg)) hgM x ⟨hxN, hx⟩ hgood

theorem exists_good_of_mem_barSub {D : Subgroup G} {y : X} (hy : y ∈ barSub π D)
    (hg : IsGood915 (barSub π L₁) (barSub π L₂) y) :
    ∃ x ∈ D, x ∈ N ∧ orderOf x = 3 ∧ (x ∈ L₁ ⊔ pCoreOf 2 N ∨ x ∈ L₂ ⊔ pCoreOf 2 N) := by
  obtain ⟨n, hnD, rfl⟩ := hy
  obtain ⟨h3, hL⟩ := hg
  have hdvd : 3 ∣ orderOf n := h3 ▸ orderOf_map_dvd π n
  have hpos : orderOf n ≠ 0 := (orderOf_pos n).ne'
  refine ⟨((n ^ (orderOf n / 3) : ↥N) : G), ?_, (n ^ (orderOf n / 3)).2, ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact D.pow_mem hnD _
  · rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div hpos hdvd
  · have hπ : π (n ^ (orderOf n / 3)) = (π n) ^ (orderOf n / 3) := map_pow _ _ _
    rcases hL with h | h
    · left
      exact mem_sup_of_mem_barSub c.ker (hπ ▸ Subgroup.pow_mem _ h _)
    · right
      exact mem_sup_of_mem_barSub c.ker (hπ ▸ Subgroup.pow_mem _ h _)

theorem false_of_good {D : Subgroup G} {y : X} (hy : y ∈ barSub π D)
    (hg : IsGood915 (barSub π L₁) (barSub π L₂) y) {g : G}
    (hgM : conjSubgroup V g ≤ normalizer (V : Set G)) (hgV : conjSubgroup V g ≠ V)
    (hD : D ≤ normalizer (conjSubgroup V g : Set G)) : False := by
  obtain ⟨x, hxD, hxN, hx3, hgood⟩ := c.exists_good_of_mem_barSub hy hg
  exact c.not_orderOf_three hgM hgV hxN (hD hxD) hgood hx3

theorem false_of_good_commute {D : Subgroup G} {y : X} (hy : y ∈ barSub π D)
    (hg : IsGood915 (barSub π L₁) (barSub π L₂) y) {g : G}
    (hgM : conjSubgroup V g ≤ normalizer (V : Set G)) (hgV : conjSubgroup V g ≠ V) {b : G}
    (hb : b ∈ conjSubgroup V g) (hb1 : b ≠ 1) (hD : ∀ x ∈ D, x * b = b * x) : False :=
  c.false_of_good hy hg hgM hgV fun x hx =>
    centralizer_le_normalizer_conj c.ti g hb hb1
      (Subgroup.mem_centralizer_singleton_iff.2 (hD x hx))

theorem exists_witness (h1 : ¬ normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G)) :
    ∃ U u, Witness V T U u := by
  obtain ⟨h, hh1, hhM⟩ := Set.not_subset.1 h1
  set W1 := E3.wClos V 1 T with hW1
  set W0 := E3.wClos V 0 T with hW0
  have hVW1 : V ≤ W1 := by
    have := c.conj_le_wClos_one (g := 1) (Y := T)
      (by rw [CFSG.Quasithin.conjSubgroup_one]; exact c.V_le_T)
    rwa [CFSG.Quasithin.conjSubgroup_one] at this
  have hW1conj : conjSubgroup W1 h = W1 := conjSubgroup_eq_iff_mem_normalizer.2 hh1
  have hUW1 : conjSubgroup V h ≤ W1 := by
    have := E3.conjSubgroup_mono_left h hVW1
    rwa [hW1conj] at this
  have hUT : conjSubgroup V h ≤ T := hUW1.trans (E3.wClos_le 1 T)
  have hUV : conjSubgroup V h ≠ V := fun heq => hhM (conjSubgroup_eq_iff_mem_normalizer.1 heq)
  obtain ⟨v, hvV, hv1, hvT⟩ := RonanE628.exists_central_of_normalized c.isPGroup_T c.V_le_T
    c.V_ne_bot c.T_le_M
  have huU : h⁻¹ * v * h ∈ conjSubgroup V h := by
    rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using hvV
  have hu1 : h⁻¹ * v * h ≠ 1 := by
    intro h0
    apply hv1
    have := congrArg (fun z => h * z * h⁻¹) h0
    simpa [mul_assoc] using this
  have huC : h⁻¹ * v * h ∈ centralizer (W1 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : h * w * h⁻¹ ∈ W1 := (Subgroup.mem_normalizer_iff.1 hh1 w).1 hw
    have hc := hvT _ (E3.wClos_le 1 T hw')
    calc w * (h⁻¹ * v * h) = h⁻¹ * ((h * w * h⁻¹) * v) * h := by group
      _ = h⁻¹ * (v * (h * w * h⁻¹)) * h := by rw [hc]
      _ = h⁻¹ * v * h * w := by group
  have hh0 : h ∈ normalizer (W0 : Set G) :=
    normalizer_wClos_one_le c.elem (by have := c.card_V; omega) hh1
  have hW0U : W0 ≤ normalizer (conjSubgroup V h : Set G) := by
    have h2 : conjSubgroup W0 h = W0 := conjSubgroup_eq_iff_mem_normalizer.2 hh0
    have h3 : conjSubgroup W0 h ≤ conjSubgroup (normalizer (V : Set G)) h :=
      E3.conjSubgroup_mono_left h ((E3.wClos_le 0 T).trans c.T_le_M)
    rwa [h2, conjSubgroup_normalizer] at h3
  have hUC0 : conjSubgroup V h ≤ centralizer (W0 : Set G) := by
    rw [Subgroup.le_centralizer_iff, hW0, wClos_zero_eq_iSup c.elem]
    refine iSup₂_le fun g hg => ?_
    exact conj_le_centralizer_of_le_normalizer c.elem c.ti c.V_ne_bot
      ((conjSubgroup_le_wClos_zero hg).trans hW0U)
  exact ⟨conjSubgroup V h, h⁻¹ * v * h, ⟨⟨h, rfl⟩, hUT, hUV, huU, hu1, huC, hUC0⟩⟩

theorem exists_conj_not_le (h2 : ¬ N ≤ normalizer (E3.wClos V 0 T : Set G)) :
    ∃ g : G, conjSubgroup V g ≤ T ∧ ¬ conjSubgroup V g ≤ pCoreOf 2 N := by
  by_contra hcon'
  have hcon : ∀ g : G, conjSubgroup V g ≤ T → conjSubgroup V g ≤ pCoreOf 2 N :=
    fun g hg => by_contra fun hn => hcon' ⟨g, hg, hn⟩
  apply h2
  have heq : E3.wClos V 0 T = E3.wClos V 0 (pCoreOf 2 N) := by
    rw [wClos_zero_eq_iSup c.elem, wClos_zero_eq_iSup c.elem]
    apply le_antisymm
    · exact iSup₂_le fun g hg => le_iSup₂_of_le g (hcon g hg) le_rfl
    · exact iSup₂_le fun g hg => le_iSup₂_of_le g (hg.trans c.Q_le_T) le_rfl
  rw [heq]
  exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N).trans
    (E3.normalizer_le_normalizer_wClos _)

theorem cClos_le_liftSub {g : G} (hAT : conjSubgroup V g ≤ T) {Kb : Subgroup X}
    (hcore : coreIn (barSub π T ⊓ centralizer (barSub π (conjSubgroup V g) : Set X))
      (barSub π T) ≤ Kb) :
    E3.cClos V 1 T ≤ liftSub π Kb := by
  set A := conjSubgroup V g
  have hC1TT : E3.cClos V 1 T ≤ T := inf_le_left
  have hTC1T : T ≤ normalizer (E3.cClos V 1 T : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_cClos T)
  have hAW1 : A ≤ E3.wClos V 1 T := c.conj_le_wClos_one hAT
  have hC1A : E3.cClos V 1 T ≤ centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.1 hx.2) a (hAW1 ha)
  have hC1Tb : barSub π (E3.cClos V 1 T) ≤
      coreIn (barSub π T ⊓ centralizer (barSub π A : Set X)) (barSub π T) :=
    le_coreIn (barSub_mono hC1TT) (barSub_le_normalizer hTC1T)
      (le_inf (barSub_mono hC1TT) (barSub_le_centralizer hC1A))
  exact (barSub_le_iff (hC1TT.trans c.TN)).1 (hC1Tb.trans hcore)

end Ctx15

end CFSG.LocalAnalysis.WeakClosure81.NGW
