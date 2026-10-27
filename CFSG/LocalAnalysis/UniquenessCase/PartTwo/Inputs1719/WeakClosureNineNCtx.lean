module

public import CFSG.LocalAnalysis.WeakClosure81.W18Weak
public import CFSG.LocalAnalysis.WeakClosure81.EightFour
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.RonanE628RLocal
public import CFSG.Quasithin.AppendixH.H14.H142Group
public import CFSG.CGT.Timmesfeld75.NodeAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNLift

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFW

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ne_bot_of_irred {S Y : Subgroup G} (h : IrredOnFrattiniQuot S Y) : Y ≠ ⊥ := by
  rintro rfl
  exact not_lt_bot h.1

theorem exists_orderOf_three_twoResidual {K S Y : Subgroup G} (h : TwoPTwoIrred K S Y 3) :
    ∃ y ∈ twoResidual K, orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy, hy3⟩ := exists_orderOf_eq_of_isPGroup h.sylowP.isPGroup (ne_bot_of_irred h.irred)
  exact ⟨y, CFSG.Quasithin.F6.mem_twoResidual_of_odd (h.sylowP.le hy) (by rw [hy3]; decide), hy3⟩

theorem le_twoResidual_of_isPGroup {K Y : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hY : IsPGroup p Y) (hYK : Y ≤ K) : Y ≤ twoResidual K := by
  intro y hy
  refine CFSG.Quasithin.F6.mem_twoResidual_of_odd (hYK hy) ?_
  obtain ⟨k, hk⟩ := hY.exists_orderOf_dvd_pow ⟨y, hy⟩
  rw [Subgroup.orderOf_mk] at hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hk
  rw [hj]
  exact (hp.odd_of_ne_two hp2).pow

theorem conj_le_centralizer_of_le_normalizer {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : IsTI V) (hVne : V ≠ ⊥) {a b : G}
    (hle : conjSubgroup V a ≤ normalizer (conjSubgroup V b : Set G)) :
    conjSubgroup V a ≤ centralizer (conjSubgroup V b : Set G) := by
  have hne : conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G) ≠ ⊥ := by
    rw [inf_eq_left.2 hle]
    intro h
    apply hVne
    have := congrArg (fun H => conjSubgroup H a⁻¹) h
    simpa only [E3.conjSubgroup_conj_inv, E3.conjSubgroup_bot] using this
  rcases two_conj_eq_or_comm hV hTI ⟨a, rfl⟩ ⟨b, rfl⟩ hne with hc | ⟨y, hy, heq⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hc x hx z hz).symm
  · have hyN : y ∈ normalizer (conjSubgroup V b : Set G) :=
      (sup_le hle Subgroup.le_normalizer) hy
    have hab : conjSubgroup V a = conjSubgroup V b := by
      have h1 : conjSubgroup (conjSubgroup V b) y⁻¹ = conjSubgroup V b :=
        conjSubgroup_eq_iff_mem_normalizer.2 (inv_mem hyN)
      rw [← h1, heq, E3.conjSubgroup_conj_inv]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [← hab] at hz
    exact (commute_of_isElemAbelian (isElemAbelian_conjSubgroup' hV a) hz hx).eq

structure Ctx (V T N : Subgroup G) {X : Type} [Group X] [Finite X] (π : ↥N →* X)
    (Lb : Subgroup X) : Prop where
  hyp : Hyp9 V T
  TN : T ≤ N
  NM : N ≤ normalizer (V : Set G)
  star : Star914 V N
  surj : Function.Surjective π
  ker : ∀ x : ↥N, π x = 1 ↔ (x : G) ∈ pCoreOf 2 N
  facts : NineFourteenBarFacts X Lb (barSub π T)

structure Witness (V T U : Subgroup G) (u : G) : Prop where
  conj : IsGConj V U
  le_T : U ≤ T
  ne : U ≠ V
  mem : u ∈ U
  ne_one : u ≠ 1
  cent_W1 : u ∈ centralizer (E3.wClos V 1 T : Set G)
  cent_W0 : U ≤ centralizer (E3.wClos V 0 T : Set G)

namespace Ctx

variable {V T N : Subgroup G} {X : Type} [Group X] [Finite X] {π : ↥N →* X} {Lb : Subgroup X}
variable (c : Ctx V T N π Lb)
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

theorem V_le_Q : V ≤ pCoreOf 2 N :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (c.V_le_T.trans c.TN) c.NM c.isPGroup_V

theorem liftSub_barSub_T : liftSub π (barSub π T) = T :=
  liftSub_barSub c.ker c.Q_le_T c.TN

omit [Finite G] in
theorem one_lt_rk : 1 < rk ↥V := by have := c.hyp.rk_gt; omega

theorem conj_le_wClos_one {g : G} {Y : Subgroup G} (hg : conjSubgroup V g ≤ Y) :
    conjSubgroup V g ≤ E3.wClos V 1 Y :=
  E3.le_wClos_of_mQuot_le c.elem g hg le_rfl (by rw [E3.mQuot_self]; omega) c.one_lt_rk

omit [Finite G] in
theorem not_orderOf_three {g : G} (hgM : conjSubgroup V g ≤ normalizer (V : Set G))
    (hgV : conjSubgroup V g ≠ V) {x : G} (hxN : x ∈ N)
    (hx : x ∈ normalizer (conjSubgroup V g : Set G)) : orderOf x ≠ 3 :=
  c.star g (fun hg => hgV (conjSubgroup_eq_iff_mem_normalizer.2 hg)) hgM x ⟨hxN, hx⟩

theorem not_orderOf_three_of_commute {g : G} (hgM : conjSubgroup V g ≤ normalizer (V : Set G))
    (hgV : conjSubgroup V g ≠ V) {b : G} (hb : b ∈ conjSubgroup V g) (hb1 : b ≠ 1) {x : G}
    (hxN : x ∈ N) (hxb : x * b = b * x) : orderOf x ≠ 3 :=
  c.not_orderOf_three hgM hgV hxN
    (centralizer_le_normalizer_conj c.ti g hb hb1 (Subgroup.mem_centralizer_singleton_iff.2 hxb))

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

theorem exists_orderOf_three_of_normal {D : Subgroup G} (hND : N ≤ normalizer (D : Set G))
    {a : ↥N} (haD : (a : G) ∈ D) (ha : orderOf (π a) = 2) : ∃ x ∈ D, orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnorm : (barSub π D).Normal := barSub_normal c.surj hND
  have hL : Lb ≤ barSub π D := c.facts.le_of_normal _ hnorm ⟨π a, mem_barSub_of_mem' haD, ha⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 c.facts.three_dvd
  exact exists_orderOf_eq_of_barSub (hL z.2) (by rw [Subgroup.orderOf_coe]; exact hz)

theorem exists_orderOf_three_of_maximal
    (hmax : ∀ H : Subgroup X, barSub π T ≤ H → H = barSub π T ∨ H = ⊤)
    {K S Y : Subgroup G} {p : ℕ} (h : TwoPTwoIrred K S Y p) (hKN : K ≤ N) {D : Subgroup G}
    (hTD : T ≤ normalizer (D : Set G)) (hKD : twoResidual K ≤ D) :
    ∃ x ∈ D, orderOf x = 3 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYne : Y ≠ ⊥ := ne_bot_of_irred h.irred
  have hYp : IsPGroup p Y := h.sylowP.isPGroup
  have hYK : Y ≤ K := h.sylowP.le
  have hYN : Y ≤ N := hYK.trans hKN
  have hYD : Y ≤ D := (le_twoResidual_of_isPGroup h.prime h.odd hYp hYK).trans hKD
  set Db := barSub π D with hDb
  set Tb := barSub π T with hTb
  have hsup : Db ⊔ Tb = ⊤ := by
    rcases hmax (Db ⊔ Tb) le_sup_right with h1 | h1
    · exfalso
      have hYb : barSub π Y ≤ Tb := (barSub_mono hYD).trans (h1 ▸ le_sup_left)
      have h2 : IsPGroup 2 (barSub π Y) := c.facts.sylow.isPGroup.to_le hYb
      have hbot : barSub π Y = ⊥ :=
        disjoint_self.1 (IsPGroup.disjoint_of_ne p 2 h.odd _ _ (isPGroup_barSub hYp) h2)
      have hYQ : Y ≤ pCoreOf 2 N := (barSub_eq_bot_iff c.ker hYN).1 hbot
      exact hYne (disjoint_self.1 (IsPGroup.disjoint_of_ne p 2 h.odd Y Y hYp
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le hYQ)))
    · exact h1
  have hnorm : Db.Normal := by
    have h1 : Db ⊔ Tb ≤ normalizer (Db : Set X) :=
      sup_le Subgroup.le_normalizer (barSub_le_normalizer hTD)
    rw [hsup, top_le_iff] at h1
    exact Subgroup.normalizer_eq_top_iff.1 h1
  have h2q : IsPGroup 2 (X ⧸ Db) := by
    refine IsPGroup.of_surjective c.facts.sylow.isPGroup ((QuotientGroup.mk' Db).comp Tb.subtype)
      ?_
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Db w
    have hx : x ∈ Db ⊔ Tb := hsup ▸ Subgroup.mem_top x
    obtain ⟨d, hd, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    refine ⟨⟨t, ht⟩, ?_⟩
    show QuotientGroup.mk' Db t = QuotientGroup.mk' Db (d * t)
    have hd1 : QuotientGroup.mk' Db d = 1 := (QuotientGroup.eq_one_iff d).2 hd
    rw [map_mul, hd1, one_mul]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 c.facts.three_dvd
  have hz' : orderOf (z : X) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
  have hzD : (z : X) ∈ Db := by
    obtain ⟨k, hk⟩ := h2q (QuotientGroup.mk' Db (z : X))
    have h3 : (QuotientGroup.mk' Db (z : X)) ^ 3 = 1 := by
      rw [← map_pow, ← hz', pow_orderOf_eq_one, map_one]
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have h1 : QuotientGroup.mk' Db (z : X) = 1 := (pow_eq_one_iff_of_coprime hcop).1 ⟨hk, h3⟩
    exact (QuotientGroup.eq_one_iff _).1 h1
  exact exists_orderOf_eq_of_barSub hzD hz'

end Ctx

end CFSG.LocalAnalysis.WeakClosure81.NFW
