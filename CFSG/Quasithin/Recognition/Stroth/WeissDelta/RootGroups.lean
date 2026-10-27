module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Quasithin.Recognition.Stroth.RootGroupRegular
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma5_2
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Quasithin.GPath

@[expose] def castLength {V : Type} {Γ : SimpleGraph V} {m n : ℕ} (h : m = n) (p : GPath Γ m) :
    GPath Γ n where
  toFun := p.toFun
  adj i hi := p.adj i (by omega)
  tail i hi := by
    have h1 : p.toFun i = p.toFun m := p.tail i (by omega)
    exact h1.trans (congrArg p.toFun h)

@[simp] theorem castLength_apply {V : Type} {Γ : SimpleGraph V} {m n : ℕ} (h : m = n)
    (p : GPath Γ m) (i : ℕ) : castLength h p i = p i := rfl

theorem castLength_noBack {V : Type} {Γ : SimpleGraph V} {m n : ℕ} (h : m = n)
    {p : GPath Γ m} (hp : p.NoBack) : (castLength h p).NoBack := by
  intro i hi
  exact hp i (by omega)

theorem stabPath_take_le {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V]
    {n m m' : ℕ} {p : GPath Γ n} (hmm : m' ≤ m) (hm : m ≤ n) (hm' : m' ≤ n) :
    GPath.stabPath (H := H) (p.take m hm) ≤
      GPath.stabPath (H := H) (p.take m' hm') := by
  intro g hg
  rw [mem_stabPath_iff] at hg ⊢
  intro i hi
  have h := hg i (by omega)
  rw [take_apply_of_le p m hm (i := i) (by omega)] at h
  rw [take_apply_of_le p m' hm' (i := i) hi]
  exact h

theorem take_self {V : Type} {Γ : SimpleGraph V} {n : ℕ} (p : GPath Γ n) :
    p.take n le_rfl = p := by
  apply ext'
  intro i hi
  rw [take_apply_of_le p n le_rfl (i := i) hi]

end CFSG.Quasithin.GPath

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

universe u

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V]
  [GraphAction H Γ]

theorem smul_path_eq_self_of_mem_pathRootGroup {n : ℕ} (hn : 3 ≤ n) {p : GPath Γ n} {g : H}
    (hg : g ∈ pathRootGroup H Γ p) :
    ∀ i, i ≤ n → g • p i = p i := by
  have hfix := mem_pathRootGroup.mp hg
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · have h : Γ.Adj (p 0) (p 1) := p.adj 0 (by omega)
    exact hfix 1 (by omega) (by omega) (p 0) h.symm
  · rcases (by omega : i = 1 ∨ 2 ≤ i) with rfl | hi2
    · have h : Γ.Adj (p 1) (p 2) := p.adj 1 (by omega)
      exact hfix 2 (by omega) (by omega) (p 1) h.symm
    · have h : Γ.Adj (p (i - 1)) (p i) := by
        have := p.adj (i - 1) (by omega)
        rwa [show i - 1 + 1 = i by omega] at this
      exact hfix (i - 1) (by omega) (by omega) (p i) h

@[instance_reducible, expose] def neighborAction (P : Subgroup H) (v w : V)
    (hv : ∀ g ∈ P, g • v = v) (hw : ∀ g ∈ P, g • w = w) :
    MulAction P {y : V // Γ.Adj v y ∧ y ≠ w} where
  smul g y := ⟨g.1 • y.1, by
    constructor
    · have h := (GraphAction.adj_smul (Γ := Γ) g.1 v y.1).mpr y.2.1
      rwa [hv g.1 g.2] at h
    · intro he
      have h' : g.1⁻¹ • (g.1 • y.1) = g.1⁻¹ • w := congrArg (g.1⁻¹ • ·) he
      rw [inv_smul_smul, hw g.1⁻¹ (Subgroup.inv_mem _ g.2)] at h'
      exact y.2.2 h'⟩
  one_smul y := Subtype.ext (one_smul H y.1)
  mul_smul g h y := Subtype.ext (mul_smul g.1 h.1 y.1)

theorem exists_fixed_neighbor_of_isPGroup_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup H} (hP : IsPGroup p P) {v w : V} (hv : ∀ g ∈ P, g • v = v)
    (hw : ∀ g ∈ P, g • w = w) {e : ℕ}
    (hcard : Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e) :
    ∃ y : V, Γ.Adj v y ∧ y ≠ w ∧ ∀ g ∈ P, g • y = y := by
  classical
  letI : MulAction P {y : V // Γ.Adj v y ∧ y ≠ w} := neighborAction P v w hv hw
  have hndvd : ¬ p ∣ Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} := by
    rw [hcard]
    intro hdvd
    apply hp2
    have hdvd2 : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow Fact.out hdvd
    have hp1 : p = 1 ∨ p = 2 := (Nat.dvd_prime Nat.prime_two).mp hdvd2
    rcases hp1 with h1 | h1
    · exact absurd h1 (Fact.out : p.Prime).ne_one
    · exact h1
  obtain ⟨y, hy⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card
    {y : V // Γ.Adj v y ∧ y ≠ w} hndvd
  refine ⟨y.1, y.2.1, y.2.2, fun g hg => ?_⟩
  have hfix := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hy ⟨g, hg⟩)
  change ((⟨g, hg⟩ : P) : H) • (y : V) = (y : V) at hfix
  simpa using hfix

theorem pathRootGroup_eq_one_of_fix_of_weissFree {n : ℕ} (hn : 3 ≤ n)
    (hW : WeissFree H Γ n) {p : GPath Γ n} (hp : p.NoBack) {g : H}
    (hg : g ∈ pathRootGroup H Γ p) {w : V} (hw : Γ.Adj (p n) w)
    (hw' : w ≠ p (n - 1)) (hgw : g • w = w) : g = 1 := by
  have hfixp := smul_path_eq_self_of_mem_pathRootGroup hn hg
  have hqnb : (p.shiftSnoc w hw).NoBack := hp.shiftSnoc hw hw'
  refine hW (p.shiftSnoc w hw) hqnb g ?_ ?_ ?_
  · intro i hi
    by_cases hin : i < n
    · rw [GPath.shiftSnoc_apply_lt _ _ _ hin]
      exact hfixp (i + 1) (by omega)
    · rw [show i = n by omega, GPath.shiftSnoc_last]
      exact hgw
  · intro y hy
    have h1 : (p.shiftSnoc w hw) 0 = p 1 := by
      rw [GPath.shiftSnoc_apply_lt _ _ _ (by omega)]
    rw [h1] at hy
    exact (mem_pathRootGroup.mp hg) 1 (by omega) (by omega) y hy
  · intro y hy
    have h1 : (p.shiftSnoc w hw) 1 = p 2 := by
      rw [GPath.shiftSnoc_apply_lt _ _ _ (by omega)]
    rw [h1] at hy
    exact (mem_pathRootGroup.mp hg) 2 (by omega) (by omega) y hy

theorem pathRootGroup_regular_of_weissFree {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n) {p : GPath Γ n}
    (hp : p.NoBack) {y y' : V} (hy : Γ.Adj (p n) y) (hy' : Γ.Adj (p n) y')
    (hne : y ≠ p (n - 1)) (hne' : y' ≠ p (n - 1)) :
    ∃! g : ↥(pathRootGroup H Γ p), (g : H) • y = y' := by
  obtain ⟨g, hgfix, hgy⟩ := hM p hp y y' hy hy' hne hne'
  have hg : g ∈ pathRootGroup H Γ p := mem_pathRootGroup.mpr hgfix
  refine ⟨⟨g, hg⟩, hgy, ?_⟩
  rintro ⟨g', hg'⟩ hgy'
  have hmem : g⁻¹ * g' ∈ pathRootGroup H Γ p :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hg'
  have hfix : (g⁻¹ * g') • y = y := by
    rw [mul_smul, hgy', ← hgy, inv_smul_smul]
  have hone : g⁻¹ * g' = 1 :=
    pathRootGroup_eq_one_of_fix_of_weissFree hn hW hp hmem hy hne hfix
  refine Subtype.ext ?_
  calc g' = g * (g⁻¹ * g') := by group
    _ = g := by rw [hone, mul_one]

theorem fixingSubgroup_inf_pathRootGroup_eq_bot {n : ℕ} (hn : 2 ≤ n)
    (hW : WeissFree H Γ n) {p : GPath Γ n} (hp : p.NoBack) :
    fixingSubgroup H (Γ.neighborSet (p 0)) ⊓ pathRootGroup H Γ p = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hg0, hgU⟩ := Subgroup.mem_inf.mp hg
  have hfix := mem_pathRootGroup.mp hgU
  refine hW p hp g ?_ ?_ ?_
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact hfix 1 (by omega) (by omega) (p 0) (p.adj 0 (by omega)).symm
    · rcases (by omega : i = 1 ∨ 2 ≤ i) with rfl | hi2
      · exact (mem_fixingSubgroup_iff H).mp hg0 (p 1) (p.adj 0 (by omega))
      · have h : Γ.Adj (p (i - 1)) (p i) := by
          have := p.adj (i - 1) (by omega)
          rwa [show i - 1 + 1 = i by omega] at this
        exact hfix (i - 1) (by omega) (by omega) (p i) h
  · exact (mem_fixingSubgroup_iff H).mp hg0
  · intro w hw
    exact hfix 1 (by omega) (by omega) w hw

private theorem smul_eq_self_of_mem_zpowers {g : H} {v : V} (hv : g • v = v) :
    ∀ h ∈ Subgroup.zpowers g, h • v = v := by
  intro h hh
  have hle : Subgroup.zpowers g ≤ fixingSubgroup H ({v} : Set V) :=
    Subgroup.zpowers_le.mpr ((mem_fixingSubgroup_iff H).mpr (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hv))
  exact (mem_fixingSubgroup_iff H).mp (hle hh) v (Set.mem_singleton v)

private theorem isPGroup_two_of_forall_odd_prime_order {G : Type*} [Group G] [Finite G]
    (h : ∀ (ℓ : ℕ), ℓ.Prime → Odd ℓ → ∀ g : G, orderOf g = ℓ → False) :
    IsPGroup 2 G := by
  rw [isPGroup_iff_orderOf_dvd_pow]
  intro g
  have hg0 : orderOf g ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite g)
  have huniq : ∀ {d : ℕ}, Nat.Prime d → d ∣ orderOf g → d = 2 := by
    intro d hd hdvd
    by_contra hd2
    exact h d hd (hd.odd_of_ne_two hd2) (g ^ (orderOf g / d))
      (orderOf_pow_orderOf_div hg0 hdvd)
  refine ⟨(orderOf g).primeFactorsList.length, ?_⟩
  conv_lhs => rw [Nat.eq_prime_pow_of_unique_prime_dvd hg0 (p := 2) huniq]

theorem exists_fixed_noBack_path_of_odd {ℓ : ℕ} [Fact ℓ.Prime] (hodd : Odd ℓ)
    {g : H} (hgord : orderOf g = ℓ)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    {s : ℕ} {p : GPath Γ s} (hs : 1 ≤ s) (hp : p.NoBack)
    (hfix : ∀ i, i ≤ s → g • p i = p i) :
    ∀ t : ℕ, s ≤ t → ∃ q : GPath Γ t, q.NoBack ∧
      (∀ i, i ≤ s → q i = p i) ∧ (∀ i, i ≤ t → g • q i = q i) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact ⟨p, hp, fun i _ => rfl, hfix⟩
  | succ t ht ih =>
      obtain ⟨q, hqnb, hqp, hqf⟩ := ih
      have ht1 : 1 ≤ t := le_trans hs ht
      have hvw : Γ.Adj (q t) (q (t - 1)) := by
        have h := q.adj (t - 1) (by omega)
        rw [show t - 1 + 1 = t by omega] at h
        exact h.symm
      have hqfix : g • q t = q t := hqf t le_rfl
      have hqfix' : g • q (t - 1) = q (t - 1) := hqf (t - 1) (by omega)
      have hP : IsPGroup ℓ (Subgroup.zpowers g) := by
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, hgord, pow_one]
      have hp2 : ℓ ≠ 2 := by
        rintro rfl
        norm_num [Nat.Prime] at hodd
      have hv : ∀ h ∈ Subgroup.zpowers g, h • q t = q t :=
        smul_eq_self_of_mem_zpowers hqfix
      have hw : ∀ h ∈ Subgroup.zpowers g, h • q (t - 1) = q (t - 1) :=
        smul_eq_self_of_mem_zpowers hqfix'
      obtain ⟨e, he⟩ := hval (q t) (q (t - 1)) hvw
      obtain ⟨y, hy, hyne, hyfix⟩ :=
        exists_fixed_neighbor_of_isPGroup_odd (p := ℓ) hp2 hP hv hw he
      have hq'nb : (q.snoc y hy).NoBack := by
        intro i hi
        by_cases h1 : i + 2 ≤ t
        · rw [GPath.snoc_of_le _ _ _ (by omega), GPath.snoc_of_le _ _ _ (by omega)]
          exact hqnb i h1
        · have hi2 : i + 2 = t + 1 := by omega
          rw [hi2, GPath.snoc_last, GPath.snoc_of_le _ _ _ (by omega)]
          rw [show i = t - 1 by omega]
          exact hyne.symm
      refine ⟨q.snoc y hy, hq'nb, ?_, ?_⟩
      · intro i hi
        rw [GPath.snoc_of_le _ _ _ (by omega)]
        exact hqp i hi
      · intro i hi
        by_cases hit : i ≤ t
        · rw [GPath.snoc_of_le _ _ _ hit]
          exact hqf i hit
        · rw [show i = t + 1 by omega, GPath.snoc_last]
          exact hyfix g (Subgroup.mem_zpowers g)

theorem edgeKernel_isPGroup_of_weissFree [Finite H] {n : ℕ} (hn : 1 ≤ n)
    (hW : WeissFree H Γ n)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    {x y : V} (hxy : Γ.Adj x y) :
    IsPGroup 2 ↥(edgeKernel (H := H) Γ x y) := by
  apply isPGroup_two_of_forall_odd_prime_order
  intro ℓ hℓ hodd u huord
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨hx, hy⟩ := mem_edgeKernel.mp u.2
  have hgx : (u : H) • x = x := hy x hxy.symm
  have hgy : (u : H) • y = y := hx y hxy
  have huord' : orderOf (u : H) = ℓ := (Subgroup.orderOf_coe u).trans huord
  let p : GPath Γ 1 := GPath.ofAdj hxy
  have hpnb : p.NoBack := by
    intro i hi
    omega
  have hpf : ∀ i, i ≤ 1 → (u : H) • p i = p i := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [show p 0 = x from GPath.ofAdj_zero hxy]
      exact hgx
    · rw [show p 1 = y from GPath.ofAdj_one hxy]
      exact hgy
  obtain ⟨q, hqnb, hqp, hqf⟩ :=
    exists_fixed_noBack_path_of_odd (p := p) (s := 1) hodd huord' hval le_rfl hpnb hpf n hn
  have hq0 : q 0 = x := by
    rw [hqp 0 (by omega), show p 0 = x from GPath.ofAdj_zero hxy]
  have hq1 : q 1 = y := by
    rw [hqp 1 (by omega), show p 1 = y from GPath.ofAdj_one hxy]
  have hone : (u : H) = 1 := by
    refine hW q hqnb (u : H) hqf ?_ ?_
    · intro w hw
      rw [hq0] at hw
      exact hx w hw
    · intro w hw
      rw [hq1] at hw
      exact hy w hw
  rw [show u = 1 from Subtype.ext hone, orderOf_one] at huord
  exact hℓ.ne_one huord.symm

theorem pathRootGroup_isPGroup [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hW : WeissFree H Γ n)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    {p : GPath Γ n} (hp : p.NoBack) :
    IsPGroup 2 ↥(pathRootGroup H Γ p) := by
  apply isPGroup_two_of_forall_odd_prime_order
  intro ℓ hℓ hodd u huord
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hgU : (u : H) ∈ pathRootGroup H Γ p := u.2
  have huord' : orderOf (u : H) = ℓ := (Subgroup.orderOf_coe u).trans huord
  have hfixvn : (u : H) • p n = p n :=
    smul_path_eq_self_of_mem_pathRootGroup hn hgU n le_rfl
  have hfixwn : (u : H) • p (n - 1) = p (n - 1) :=
    smul_path_eq_self_of_mem_pathRootGroup hn hgU (n - 1) (by omega)
  have hvw : Γ.Adj (p n) (p (n - 1)) := by
    have h := p.adj (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega] at h
    exact h.symm
  obtain ⟨e, he⟩ := hval (p n) (p (n - 1)) hvw
  have hP : IsPGroup ℓ (Subgroup.zpowers (u : H)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, huord', pow_one]
  have hp2 : ℓ ≠ 2 := by
    rintro rfl
    norm_num [Nat.Prime] at hodd
  have hv : ∀ h ∈ Subgroup.zpowers (u : H), h • p n = p n :=
    smul_eq_self_of_mem_zpowers hfixvn
  have hw : ∀ h ∈ Subgroup.zpowers (u : H), h • p (n - 1) = p (n - 1) :=
    smul_eq_self_of_mem_zpowers hfixwn
  obtain ⟨w, hwadj, hwne, hwfix⟩ :=
    exists_fixed_neighbor_of_isPGroup_odd (p := ℓ) hp2 hP hv hw he
  have hqnb : (p.shiftSnoc w hwadj).NoBack := hp.shiftSnoc hwadj hwne
  have hqf : ∀ i, i ≤ n → (u : H) • (p.shiftSnoc w hwadj) i = (p.shiftSnoc w hwadj) i := by
    intro i hi
    by_cases hin : i < n
    · rw [GPath.shiftSnoc_apply_lt _ _ _ hin]
      exact smul_path_eq_self_of_mem_pathRootGroup hn hgU (i + 1) (by omega)
    · rw [show i = n by omega, GPath.shiftSnoc_last]
      exact hwfix (u : H) (Subgroup.mem_zpowers _)
  have hone : (u : H) = 1 := by
    refine hW (p.shiftSnoc w hwadj) hqnb (u : H) hqf ?_ ?_
    · intro y hy
      have h1 : (p.shiftSnoc w hwadj) 0 = p 1 := by
        rw [GPath.shiftSnoc_apply_lt _ _ _ (by omega)]
      rw [h1] at hy
      exact (mem_pathRootGroup.mp hgU) 1 (by omega) (by omega) y hy
    · intro y hy
      have h1 : (p.shiftSnoc w hwadj) 1 = p 2 := by
        rw [GPath.shiftSnoc_apply_lt _ _ _ (by omega)]
      rw [h1] at hy
      exact (mem_pathRootGroup.mp hgU) 2 (by omega) (by omega) y hy
  rw [show u = 1 from Subtype.ext hone, orderOf_one] at huord
  exact hℓ.ne_one huord.symm

@[expose] def FixingNeighbourhoodFixesVertex (x : V) : Prop :=
  fixingSubgroup H (Γ.neighborSet x) ≤ MulAction.stabilizer H x

theorem fixingSubgroup_le_stabilizer_of_twinFree
    (htwin : ∀ x y : V, (∀ z : V, Γ.Adj x z ↔ Γ.Adj y z) → x = y) (x : V) :
    FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) x := by
  intro k hk
  rw [MulAction.mem_stabilizer_iff]
  apply htwin (k • x) x
  intro z
  constructor
  · intro hz
    have h1 : Γ.Adj x (k⁻¹ • z) := by
      have h := (GraphAction.adj_smul k⁻¹ (k • x) z).mpr hz
      rw [← mul_smul, inv_mul_cancel, one_smul] at h
      exact h
    have h2 : k • (k⁻¹ • z) = k⁻¹ • z :=
      (mem_fixingSubgroup_iff H).mp hk (k⁻¹ • z) h1
    rw [smul_inv_smul] at h2
    rw [h2]
    exact h1
  · intro hz
    have h1 : Γ.Adj (k • x) (k • z) := (GraphAction.adj_smul k x z).mpr hz
    have h2 : k • z = z := (mem_fixingSubgroup_iff H).mp hk z hz
    rwa [h2] at h1

private theorem noBack_snoc {m : ℕ} {p : GPath Γ m} (hp : p.NoBack) {u : V}
    (hu : Γ.Adj (p m) u) (hne : u ≠ p (m - 1)) : (p.snoc u hu).NoBack := by
  intro i hi
  by_cases h1 : i + 2 ≤ m
  · rw [GPath.snoc_of_le _ _ _ (by omega), GPath.snoc_of_le _ _ _ (by omega)]
    exact hp i h1
  · have hi2 : i + 2 = m + 1 := by omega
    rw [hi2, GPath.snoc_last, GPath.snoc_of_le _ _ _ (by omega)]
    rw [show i = m - 1 by omega]
    exact hne.symm

theorem exists_backward_noBack (hdeg : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {x z : V} (hxz : Γ.Adj x z) (k : ℕ) :
    ∃ p : GPath Γ k, p.NoBack ∧ p k = x ∧ (0 < k → p (k - 1) ≠ z) := by
  induction k with
  | zero => exact ⟨GPath.nil x, GPath.noBack_nil x, rfl, by omega⟩
  | succ k ih =>
      obtain ⟨p, hp, hpk, hpz⟩ := ih
      by_cases hk : k = 0
      · subst hk
        obtain ⟨y, hy, hyz⟩ := hdeg x z hxz
        refine ⟨GPath.cons y p (by rw [hpk]; exact hy.symm), ?_, ?_, ?_⟩
        · refine GPath.noBack_cons y p _ hp ?_
          rw [show p 1 = p 0 from p.tail 1 (by omega), hpk]
          exact hy.symm.ne
        · rw [GPath.cons_succ]
          exact hpk
        · intro _
          rw [show (0 : ℕ) + 1 - 1 = 0 by omega, GPath.cons_zero]
          exact hyz
      · have h0 : Γ.Adj (p 0) (p 1) := p.adj 0 (by omega)
        obtain ⟨y, hy, hyn⟩ := hdeg (p 0) (p 1) h0
        refine ⟨GPath.cons y p hy.symm, ?_, ?_, ?_⟩
        · exact GPath.noBack_cons y p _ hp hyn
        · rw [GPath.cons_succ]
          exact hpk
        · intro _
          rw [show k + 1 - 1 = k by omega]
          have hcs := GPath.cons_succ y p hy.symm (k - 1)
          rw [show k - 1 + 1 = k by omega] at hcs
          exact hcs.trans_ne (hpz (by omega))

private theorem exists_walk_of_path {m : ℕ} (p : GPath Γ m) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m) :
    ∃ w : Γ.Walk (p i) (p j), w.length = j - i := by
  revert hj
  induction j, hij using Nat.le_induction with
  | base => intro _; exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ j hij ih =>
      intro hj
      obtain ⟨w, hw⟩ := ih (by omega)
      refine ⟨w.concat (p.adj j (by omega)), ?_⟩
      rw [SimpleGraph.Walk.length_concat, hw]
      omega

theorem eq_one_of_fix_ball {n : ℕ} (hn : 3 ≤ n) (hW : WeissFree H Γ n)
    (hdeg : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w) {x : V} {g : H}
    (hx : ∃ y : V, Γ.Adj x y)
    (hg : ∀ w, Γ.dist x w ≤ n - 1 → g • w = w) : g = 1 := by
  obtain ⟨z1, hxz⟩ := hx
  obtain ⟨p, hpnb, hpx, hpz⟩ := exists_backward_noBack hdeg hxz (n - 2)
  have h1adj : Γ.Adj (p (n - 2)) z1 := by rw [hpx]; exact hxz
  let q1 : GPath Γ ((n - 2) + 1) := p.snoc z1 h1adj
  have hq1nb : q1.NoBack := by
    refine noBack_snoc hpnb h1adj ?_
    intro h
    exact hpz (by omega) h.symm
  obtain ⟨z2, hz2, hz2ne⟩ := hdeg z1 x hxz.symm
  have h2adj : Γ.Adj (q1 ((n - 2) + 1)) z2 := by
    rw [GPath.snoc_last]
    exact hz2
  let q2 : GPath Γ (((n - 2) + 1) + 1) := q1.snoc z2 h2adj
  have hq2nb : q2.NoBack := by
    refine noBack_snoc hq1nb h2adj ?_
    rw [show (n - 2) + 1 - 1 = n - 2 by omega,
      GPath.snoc_of_le _ _ _ (by omega), hpx]
    exact hz2ne
  let q : GPath Γ n :=
    { toFun := q2.toFun
      adj := fun i hi => q2.adj i (by omega)
      tail := fun i _ => by
        have h1 : q2.toFun i = q2.toFun (((n - 2) + 1) + 1) := q2.tail i (by omega)
        have h2 : q2.toFun (((n - 2) + 1) + 1) = q2.toFun n :=
          congrArg (fun j => q2.toFun j) (by omega)
        exact h1.trans h2 }
  have hqnb : q.NoBack := fun i hi => hq2nb i (by omega)
  have hq_p : ∀ i, i ≤ n - 2 → q i = p i := by
    intro i hi
    have h1 : q2 i = q1 i := GPath.snoc_of_le q1 z2 h2adj (by omega)
    have h2' : q1 i = p i := GPath.snoc_of_le p z1 h1adj (by omega)
    exact h1.trans h2'
  have hq_n1 : q (n - 1) = z1 := by
    have h1 : q2 (n - 1) = q1 (n - 1) := GPath.snoc_of_le q1 z2 h2adj (by omega)
    have h2' : q1 (n - 1) = z1 := by
      rw [show n - 1 = (n - 2) + 1 by omega]
      exact GPath.snoc_last p z1 h1adj
    exact h1.trans h2'
  have hq_n : q n = z2 := by
    have h1 : q2 n = q2 (((n - 2) + 1) + 1) :=
      congrArg (fun j => q2.toFun j) (by omega)
    exact h1.trans (GPath.snoc_last q1 z2 h2adj)
  have hfix : ∀ i, i ≤ n → g • q i = q i := by
    intro i hi
    rcases (by omega : i ≤ n - 2 ∨ i = n - 1 ∨ i = n) with hle | hmid | htop
    · rw [hq_p i hle]
      apply hg
      obtain ⟨w, hw⟩ := exists_walk_of_path p (i := i) (j := n - 2) hle le_rfl
      have hle' : Γ.dist (p i) x ≤ w.length := by
        rw [← hpx]
        exact SimpleGraph.dist_le w
      rw [hw] at hle'
      rw [SimpleGraph.dist_comm]
      omega
    · subst hmid
      rw [hq_n1]
      apply hg
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hxz]
      omega
    · subst htop
      rw [hq_n]
      apply hg
      have hle' : Γ.dist x z2 ≤ 2 := by
        have hw := SimpleGraph.dist_le
          (SimpleGraph.Walk.cons hxz (SimpleGraph.Walk.cons hz2 SimpleGraph.Walk.nil))
        simpa using hw
      omega
  refine hW q hqnb g hfix ?_ ?_
  · intro y hy
    have hy0 : q 0 = p 0 := hq_p 0 (by omega)
    rw [hy0] at hy
    apply hg
    obtain ⟨w, hw⟩ := exists_walk_of_path p (i := 0) (j := n - 2) (by omega) le_rfl
    have hylen : w.length = n - 2 := by rw [hw]; omega
    have hlen : (w.reverse.concat hy).length = n - 1 := by
      rw [SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse, hylen]
      omega
    calc Γ.dist x y = Γ.dist (p (n - 2)) y := by rw [hpx]
      _ ≤ (w.reverse.concat hy).length := SimpleGraph.dist_le _
      _ = n - 1 := hlen
  · intro y hy
    have hy1 : q 1 = p 1 := hq_p 1 (by omega)
    rw [hy1] at hy
    apply hg
    obtain ⟨w, hw⟩ := exists_walk_of_path p (i := 1) (j := n - 2) (by omega) le_rfl
    have hylen : w.length = n - 3 := by rw [hw]; omega
    have hlen : (w.reverse.concat hy).length = n - 2 := by
      rw [SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse, hylen]
      omega
    calc Γ.dist x y = Γ.dist (p (n - 2)) y := by rw [hpx]
      _ ≤ (w.reverse.concat hy).length := SimpleGraph.dist_le _
      _ = n - 2 := hlen
      _ ≤ n - 1 := by omega

theorem exists_smul_of_mem_stabPath_take {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {s : ℕ} {p : GPath Γ s} (hp : p.NoBack) {i : ℕ} (hi1 : 1 ≤ i) (his : i ≤ s)
    (hin : i ≤ n) {y y' : V} (hy : Γ.Adj (p i) y) (hy' : Γ.Adj (p i) y')
    (hyne : y ≠ p (i - 1)) (hy'ne : y' ≠ p (i - 1)) :
    ∃ g : H, g ∈ (p.take i his).stabPath ∧ g • y = y' := by
  have hsi : 1 ≤ s := le_trans hi1 his
  have h0 : Γ.Adj (p 0) (p 1) := p.adj 0 (by omega)
  by_cases hin' : i = n
  · subst i
    have hqnb : (p.take n his).NoBack := hp.take n his
    have hqn : (p.take n his) n = p n := GPath.take_apply_of_le _ _ _ le_rfl
    have hqn1 : (p.take n his) (n - 1) = p (n - 1) :=
      GPath.take_apply_of_le _ _ _ (by omega)
    obtain ⟨g, hgfix, hgy⟩ := hM (p.take n his) hqnb y y'
      (by rwa [hqn]) (by rwa [hqn]) (by rwa [hqn1]) (by rwa [hqn1])
    refine ⟨g, ?_, hgy⟩
    have hgU : g ∈ pathRootGroup H Γ (p.take n his) := mem_pathRootGroup.mpr hgfix
    have hfixq := smul_path_eq_self_of_mem_pathRootGroup hn hgU
    rw [GPath.mem_stabPath_iff]
    intro j hj
    simpa only [GPath.take_apply_of_le _ _ _ hj] using hfixq j hj
  · have hkpos : 0 < n - i := by omega
    obtain ⟨r, hrnb, hrk, hrprev⟩ :=
      exists_backward_noBack hne (x := p 0) (z := p 1) h0 (n - i)
    have hjoin : r (n - i) = (p.take i his) 0 := by
      rw [hrk, GPath.take_apply_of_le _ _ _ (Nat.zero_le i)]
    have hcross : r ((n - i) - 1) ≠ (p.take i his) 1 := by
      rw [GPath.take_apply_of_le _ _ _ hi1]
      exact hrprev hkpos
    have hq2nb : (GPath.append r (p.take i his) hjoin).NoBack :=
      GPath.noBack_append r (p.take i his) hjoin hrnb (hp.take i his) hkpos hi1 hcross
    let q := GPath.castLength (Nat.sub_add_cancel hin) (GPath.append r (p.take i his) hjoin)
    have hqnb : q.NoBack := GPath.castLength_noBack _ hq2nb
    have hqn : q n = p i := by
      have hcast : q n = (GPath.append r (p.take i his) hjoin) ((n - i) + i) :=
        congrArg (GPath.append r (p.take i his) hjoin).toFun (Nat.sub_add_cancel hin).symm
      rw [hcast, GPath.append_apply_right _ _ _ (by omega)]
      rw [show (n - i) + i - (n - i) = i by omega, GPath.take_apply_of_le _ _ _ le_rfl]
    have hqn1 : q (n - 1) = p (i - 1) := by
      have hcast : q (n - 1) = (GPath.append r (p.take i his) hjoin) ((n - i) + i - 1) :=
        congrArg (GPath.append r (p.take i his) hjoin).toFun
          (by omega : n - 1 = (n - i) + i - 1)
      rw [hcast, GPath.append_apply_right _ _ _ (by omega)]
      rw [show (n - i) + i - 1 - (n - i) = i - 1 by omega,
        GPath.take_apply_of_le _ _ _ (by omega)]
    obtain ⟨g, hgfix, hgy⟩ := hM q hqnb y y'
      (by rwa [hqn]) (by rwa [hqn]) (by rw [hqn1]; exact hyne)
      (by rw [hqn1]; exact hy'ne)
    refine ⟨g, ?_, hgy⟩
    have hgU : g ∈ pathRootGroup H Γ q := mem_pathRootGroup.mpr hgfix
    have hfixq := smul_path_eq_self_of_mem_pathRootGroup hn hgU
    rw [GPath.mem_stabPath_iff]
    intro j hj
    have hval : q ((n - i) + j) = (p.take i his) j := by
      have hcast : q ((n - i) + j) =
          (GPath.append r (p.take i his) hjoin) ((n - i) + j) := rfl
      rw [hcast, GPath.append_apply_right _ _ _ (by omega)]
      rw [show (n - i) + j - (n - i) = j by omega]
    have hval' : q ((n - i) + j) = p j := by
      rw [hval, GPath.take_apply_of_le _ _ _ hj]
    have h := hfixq ((n - i) + j) (by omega)
    rw [hval'] at h
    simpa only [GPath.take_apply_of_le _ _ _ hj] using h

end CFSG.Quasithin.Stroth.WeissDelta
