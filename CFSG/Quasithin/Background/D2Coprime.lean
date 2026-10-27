module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.Data.Int.Star
public import Mathlib.GroupTheory.GroupAction.CardCommute
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

section Coprime

variable [Finite V]

noncomputable def avgMap (P : Subgroup (MulAut V)) : V →* V :=
  haveI := Fintype.ofFinite P
  { toFun := fun v => ∏ g : P, (g : MulAut V) v
    map_one' := by simp
    map_mul' := fun a b => by simp [Finset.prod_mul_distrib] }

theorem avgMap_apply (P : Subgroup (MulAut V)) [Fintype P] (v : V) :
    avgMap P v = ∏ g : P, (g : MulAut V) v := by
  unfold avgMap
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  congr
  exact Subsingleton.elim _ _

theorem avgMap_mem_fixV (P : Subgroup (MulAut V)) (v : V) : avgMap P v ∈ fixV P := by
  have := Fintype.ofFinite P
  intro g hg
  rw [avgMap_apply, map_prod]
  have : ∀ h : P, g ((h : MulAut V) v) = ((⟨g, hg⟩ * h : P) : MulAut V) v := fun h => rfl
  simp only [this]
  exact Fintype.prod_equiv (Equiv.mulLeft (⟨g, hg⟩ : P)) _ _ fun h => rfl

theorem avgMap_smul (P : Subgroup (MulAut V)) {g : MulAut V} (hg : g ∈ P) (v : V) :
    avgMap P (g v) = avgMap P v := by
  have := Fintype.ofFinite P
  rw [avgMap_apply, avgMap_apply]
  have : ∀ h : P, (h : MulAut V) (g v) = ((h * ⟨g, hg⟩ : P) : MulAut V) v := fun h => rfl
  simp only [this]
  exact Fintype.prod_equiv (Equiv.mulRight (⟨g, hg⟩ : P)) _ _ fun h => rfl

theorem avgMap_of_mem_fixV {P : Subgroup (MulAut V)} (hP : Odd (Nat.card P))
    (hV : ∀ v : V, v ^ 2 = 1) {w : V} (hw : w ∈ fixV P) : avgMap P w = w := by
  have := Fintype.ofFinite P
  rw [avgMap_apply]
  have : ∀ h : P, (h : MulAut V) w = w := fun h => hw h h.2
  simp only [this, Finset.prod_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card]
  obtain ⟨k, hk⟩ := hP
  rw [hk, pow_succ, pow_mul, hV w, one_pow, one_mul]

theorem avgMap_commutator {P : Subgroup (MulAut V)} {c : V} (hc : c ∈ commV P) :
    avgMap P c = 1 := by
  refine Subgroup.closure_induction (p := fun c _ => avgMap P c = 1) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨g, hg, v, rfl⟩
    rw [map_mul, avgMap_smul P hg, map_inv, mul_inv_cancel]
  · exact map_one _
  · intro a b _ _ ha hb
    rw [map_mul, ha, hb, mul_one]
  · intro a _ ha
    rw [map_inv, ha, inv_one]

theorem mul_avgMap_mem_commV {P : Subgroup (MulAut V)} (hP : Odd (Nat.card P))
    (hV : ∀ v : V, v ^ 2 = 1) (v : V) : v * avgMap P v ∈ commV P := by
  have := Fintype.ofFinite P
  have h1 : v * avgMap P v = ∏ g : P, (v * (g : MulAut V) v) := by
    rw [avgMap_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := hP
    rw [hk, pow_succ, pow_mul, hV v, one_pow, one_mul]
  rw [h1]
  refine Subgroup.prod_mem _ fun g _ => ?_
  have : v * (g : MulAut V) v = (g : MulAut V) v * v⁻¹ := by
    have : v⁻¹ = v := by
      have := hV v
      rw [pow_two, mul_eq_one_iff_eq_inv] at this
      exact this.symm
    rw [this, mul_comm]
  rw [this]
  exact Subgroup.subset_closure ⟨g, g.2, v, rfl⟩

theorem coprime_decomp {P : Subgroup (MulAut V)} (hP : Odd (Nat.card P))
    (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} (hW : ∀ g ∈ P, ∀ w ∈ W, g w ∈ W) :
    commSub W P ⊔ (W ⊓ fixV P) = W ∧ commSub W P ⊓ (W ⊓ fixV P) = ⊥ := by
  have hcomm_le : commSub W P ≤ W := commSub_le_of_invariant hW
  have hbar : ∀ w ∈ W, avgMap P w ∈ W := by
    intro w hw
    have := Fintype.ofFinite P
    rw [avgMap_apply]
    exact Subgroup.prod_mem _ fun g _ => hW g g.2 w hw
  constructor
  · refine le_antisymm (sup_le hcomm_le inf_le_left) fun w hw => ?_
    have h1 : avgMap P w ∈ W ⊓ fixV P := ⟨hbar w hw, avgMap_mem_fixV P w⟩
    have h2 : w * avgMap P w ∈ commSub W P := by
      have := Fintype.ofFinite P
      have h1' : w * avgMap P w = ∏ g : P, (w * (g : MulAut V) w) := by
        rw [avgMap_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          ← Nat.card_eq_fintype_card]
        obtain ⟨k, hk⟩ := hP
        have hV' : w ^ 2 = 1 := hV w
        rw [hk, pow_succ, pow_mul, hV', one_pow, one_mul]
      rw [h1']
      refine Subgroup.prod_mem _ fun g _ => ?_
      have hinv : w⁻¹ = w := by
        have := hV w
        rw [pow_two, mul_eq_one_iff_eq_inv] at this
        exact this.symm
      have : w * (g : MulAut V) w = (g : MulAut V) w * w⁻¹ := by rw [hinv, mul_comm]
      rw [this]
      exact Subgroup.subset_closure ⟨g, g.2, w, hw, rfl⟩
    have hw' : w = (w * avgMap P w) * avgMap P w := by
      have := hV (avgMap P w)
      rw [mul_assoc, ← pow_two, this, mul_one]
    rw [hw']
    exact Subgroup.mul_mem_sup h2 h1
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun w ⟨hw1, hw2⟩ => ?_
    have h1 : avgMap P w = 1 := by
      refine Subgroup.closure_induction (p := fun c _ => avgMap P c = 1) ?_ ?_ ?_ ?_ hw1
      · rintro _ ⟨g, hg, v, -, rfl⟩
        rw [map_mul, avgMap_smul P hg, map_inv, mul_inv_cancel]
      · exact map_one _
      · intro a b _ _ ha hb
        rw [map_mul, ha, hb, mul_one]
      · intro a _ ha
        rw [map_inv, ha, inv_one]
    rw [← avgMap_of_mem_fixV hP hV hw2.2]
    exact h1

end Coprime


section Counting

theorem mem_fixV_zpowers_iff {g : MulAut V} {v : V} : v ∈ fixV (Subgroup.zpowers g) ↔ g v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

@[expose] def commHom (g : MulAut V) : V →* V where
  toFun v := g v * v⁻¹
  map_one' := by simp
  map_mul' a b := by rw [map_mul, mul_inv]; ac_rfl

theorem commHom_apply (g : MulAut V) (v : V) : commHom g v = g v * v⁻¹ := rfl

theorem ker_commHom (g : MulAut V) : (commHom g).ker = fixV (Subgroup.zpowers g) := by
  ext v
  rw [MonoidHom.mem_ker, commHom_apply, mul_inv_eq_one, mem_fixV_zpowers_iff]

theorem commSub_zpowers_eq_map [Finite V] {g : MulAut V} {W : Subgroup V}
    (hW : ∀ x ∈ Subgroup.zpowers g, ∀ w ∈ W, x w ∈ W) :
    commSub W (Subgroup.zpowers g) = W.map (commHom g) := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, g ^ n = x :=
      (Submonoid.mem_powers_iff x g).mp ((mem_powers_iff_mem_zpowers (x := g) (y := x)).mpr hx)
    clear hx
    induction n generalizing w with
    | zero => exact ⟨1, W.one_mem, by simp [commHom_apply]⟩
    | succ n ih =>
      have hmem : (g ^ n) w ∈ W := hW _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) n) w hw
      have : (g ^ (n + 1)) w * w⁻¹ = commHom g ((g ^ n) w) * ((g ^ n) w * w⁻¹) := by
        simp [commHom_apply, pow_succ', MulAut.mul_apply, mul_assoc]
      rw [this]
      exact Subgroup.mul_mem _ ⟨_, hmem, rfl⟩ (ih w hw)
  · rintro _ ⟨w, hw, rfl⟩
    exact Subgroup.subset_closure ⟨g, Subgroup.mem_zpowers g, w, hw, rfl⟩

theorem rk_map_add_rk_inf_ker [Finite V] {V' : Type*} [CommGroup V'] (f : V →* V')
    (W : Subgroup V) : rk (W.map f) + rk (W ⊓ f.ker : Subgroup V) = rk W := by
  have h1 : (f.domRestrict W).range = W.map f := MonoidHom.domRestrict_range W f
  have h2 : (f.domRestrict W).ker = f.ker.subgroupOf W := MonoidHom.ker_domRestrict W f
  have h3 := Subgroup.index_ker (f.domRestrict W)
  have h4 := Subgroup.card_mul_index (f.domRestrict W).ker
  have h5 : Nat.card ↥(f.ker.subgroupOf W) = Nat.card ↥(W ⊓ f.ker) := by
    have : f.ker.subgroupOf W = (W ⊓ f.ker).subgroupOf W := by
      ext x; simp [Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hfin : Finite (W.map f) := (Set.Finite.image f (Set.toFinite (W : Set V))).to_subtype
  rw [h1] at h3
  rw [h3, h2, h5] at h4
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', mul_comm, h4]

theorem commV_zpowers_eq_map [Finite V] (g : MulAut V) :
    commV (Subgroup.zpowers g) = (⊤ : Subgroup V).map (commHom g) := by
  rw [commV_eq_commSub, commSub_zpowers_eq_map]
  intro x _ w _
  exact Subgroup.mem_top _

theorem rk_commV_add_rk_fixV [Finite V] (g : MulAut V) :
    rk (commV (Subgroup.zpowers g)) + rk (fixV (Subgroup.zpowers g)) = rk V := by
  have := rk_map_add_rk_inf_ker (commHom g) ⊤
  rw [← commV_zpowers_eq_map, top_inf_eq, ker_commHom, rk_top] at this
  exact this

theorem rkIdx_fixV_zpowers [Finite V] (g : MulAut V) :
    rkIdx (fixV (Subgroup.zpowers g)) = rk (commV (Subgroup.zpowers g)) := by
  have := rk_add_rkIdx (fixV (Subgroup.zpowers g))
  have := rk_commV_add_rk_fixV g
  omega

theorem rk_commSub_add_rk_inf_fixV [Finite V] {g : MulAut V} {W : Subgroup V}
    (hW : ∀ x ∈ Subgroup.zpowers g, ∀ w ∈ W, x w ∈ W) :
    rk (commSub W (Subgroup.zpowers g)) + rk (W ⊓ fixV (Subgroup.zpowers g) : Subgroup V) =
      rk W := by
  have := rk_map_add_rk_inf_ker (commHom g) W
  rwa [← commSub_zpowers_eq_map hW, ker_commHom] at this

theorem rk_iSup_biSup_eq_sum [Finite V] {ι : Type*} (S : ι → Subgroup V) (hS : iSupIndep S)
    (s : Finset ι) : rk (⨆ i ∈ s, S i : Subgroup V) = ∑ i ∈ s, rk (S i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (⨆ i ∈ (∅ : Finset ι), S i : Subgroup V) = ⊥ :=
      iSup_eq_bot.mpr fun i => iSup_eq_bot.mpr fun hi => absurd hi (Finset.notMem_empty i)
    rw [h0, rk_bot, Finset.sum_empty]
  | insert j s hj ih =>
    rw [Finset.iSup_insert, Finset.sum_insert hj, ← ih]
    have hd : Disjoint (S j) (⨆ i ∈ (s : Set ι), S i) :=
      hS.disjoint_biSup (by simpa using hj)
    have hd' : Disjoint (S j) (⨆ i ∈ s, S i) := by simpa using hd
    have := rk_sup_add_rk_inf (S j) (⨆ i ∈ s, S i)
    rw [hd'.eq_bot, rk_bot] at this
    omega

theorem card_modEq_card_fixV [Finite V] {q : ℕ} [Fact q.Prime] {Y : Subgroup (MulAut V)}
    (hY : IsPGroup q Y) : Nat.card V ≡ Nat.card (fixV Y) [MOD q] := by
  have := hY.card_modEq_card_fixedPoints V
  refine this.trans ?_
  have heq : (MulAction.fixedPoints Y V) = (fixV Y : Set V) := by
    ext v
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, mem_fixV]
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
  rw [heq]
  exact Nat.ModEq.refl _

theorem card_dvd_card_of_free [Finite V] {G : Subgroup (MulAut V)} {Ω : Set V}
    (hΩ : ∀ g ∈ G, ∀ v ∈ Ω, g v ∈ Ω) (hfree : ∀ g ∈ G, ∀ v ∈ Ω, g v = v → g = 1) :
    Nat.card G ∣ Nat.card Ω := by
  classical
  let s : SubMulAction G V :=
    { carrier := Ω
      smul_mem' := fun g v hv => hΩ g g.2 v hv }
  have hfree' : ∀ (g : G) (ω : s), g • ω = ω → g = 1 := by
    intro g ω h
    have h1 : (g : MulAut V) (ω : V) = ω := congrArg Subtype.val h
    exact Subtype.ext (hfree g g.2 ω ω.2 h1)
  have : Fintype G := Fintype.ofFinite G
  have : Fintype s := Fintype.ofFinite s
  have : Fintype (MulAction.orbitRel.Quotient G s) := Fintype.ofFinite _
  have hst : ∀ ω : s, Fintype.card (MulAction.stabilizer G ω) = 1 := by
    intro ω
    rw [Fintype.card_eq_one_iff]
    refine ⟨1, fun ⟨g, hg⟩ => ?_⟩
    exact Subtype.ext (hfree' g ω (MulAction.mem_stabilizer_iff.mp hg))
  have key := MulAction.card_eq_sum_card_group_div_card_stabilizer G s
  simp only [hst, Nat.div_one, Finset.sum_const, Finset.card_univ, smul_eq_mul] at key
  have h2 : Nat.card ↥Ω = Fintype.card s := Nat.card_eq_fintype_card
  rw [h2, key, Nat.card_eq_fintype_card (α := G)]
  exact Dvd.intro_left _ rfl

theorem card_compl_fixV [Finite V] (H : Subgroup V) :
    Nat.card ((H : Set V)ᶜ : Set V) = Nat.card V - Nat.card H := by
  classical
  have h1 := Nat.card_congr (Equiv.Set.sumCompl (H : Set V))
  rw [Nat.card_sum] at h1
  have h2 : Nat.card (H : Set V) = Nat.card H := rfl
  omega

theorem sq_dvd_card_sub_card_fixV [Finite V] {q : ℕ} [Fact q.Prime] {y : MulAut V}
    (hy : orderOf y = q ^ 2) :
    q ^ 2 ∣ Nat.card V - Nat.card (fixV (Subgroup.zpowers (y ^ q))) := by
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  set F := fixV (Subgroup.zpowers (y ^ q)) with hF
  have hcomm : ∀ g ∈ Subgroup.zpowers y, g * y ^ q = y ^ q * g := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (Commute.pow_right (Commute.refl y) q) k).eq
  have hΩ : ∀ g ∈ Subgroup.zpowers y, ∀ v ∈ ((F : Set V)ᶜ : Set V),
      g v ∈ ((F : Set V)ᶜ : Set V) := by
    intro g hg v hv hgv
    apply hv
    have h1 : (y ^ q) (g v) = g v := mem_fixV_zpowers_iff.mp hgv
    have h2 : g ((y ^ q) v) = g v := by
      have hc := hcomm g hg
      calc g ((y ^ q) v) = (g * y ^ q) v := rfl
        _ = (y ^ q * g) v := by rw [hc]
        _ = (y ^ q) (g v) := rfl
        _ = g v := h1
    have h3 : (y ^ q) v = v := g.injective h2
    exact mem_fixV_zpowers_iff.mpr h3
  have hfree : ∀ g ∈ Subgroup.zpowers y, ∀ v ∈ ((F : Set V)ᶜ : Set V), g v = v → g = 1 := by
    intro g hg v hv hgv
    by_contra hg1
    apply hv
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff g y).mp
      ((mem_powers_iff_mem_zpowers (x := y) (y := g)).mpr hg)
    have hj : ¬ q ^ 2 ∣ j := fun h => hg1 ((orderOf_dvd_iff_pow_eq_one (x := y)).mp (hy ▸ h))
    have hlt : Nat.gcd j (q ^ 2) < q ^ 2 := by
      have hpos : 0 < q ^ 2 := by positivity
      refine lt_of_le_of_ne (Nat.le_of_dvd hpos (Nat.gcd_dvd_right _ _)) fun h => hj ?_
      rw [← h]
      exact Nat.gcd_dvd_left _ _
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd hlt
    have hstab : ∀ n : ℕ, (y ^ j) ^ n ∈ MulAction.stabilizer (MulAut V) v := fun n =>
      Subgroup.pow_mem _ (MulAction.mem_stabilizer_iff.mpr hgv) n
    have hfix : (y ^ (Nat.gcd j (q ^ 2))) v = v := by
      have : y ^ (Nat.gcd j (q ^ 2)) = (y ^ j) ^ m := by
        rw [← pow_mul, ← hm, ← hy, pow_mod_orderOf]
      rw [this]
      exact MulAction.mem_stabilizer_iff.mp (hstab m)
    obtain ⟨i, hi, hgcd⟩ := (Nat.dvd_prime_pow (Fact.out : q.Prime)).mp (Nat.gcd_dvd_right j (q ^ 2))
    have hstab' : ∀ n : ℕ, (y ^ (Nat.gcd j (q ^ 2))) ^ n ∈ MulAction.stabilizer (MulAut V) v :=
      fun n => Subgroup.pow_mem _ (MulAction.mem_stabilizer_iff.mpr hfix) n
    show v ∈ F
    rw [hF, mem_fixV_zpowers_iff]
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · interval_cases i
      ·
        have h1 : Nat.gcd j (q ^ 2) = 1 := by simpa using hgcd
        rw [h1, pow_one] at hfix
        have hs : y ∈ MulAction.stabilizer (MulAut V) v := hfix
        exact Subgroup.pow_mem _ hs q
      · have h1 : Nat.gcd j (q ^ 2) = q := by simpa using hgcd
        rw [h1] at hfix
        exact hfix
    · exfalso
      have : i = 2 := le_antisymm hi hi2
      subst this
      exact absurd hgcd (Nat.ne_of_lt hlt)
  have hdvd := card_dvd_card_of_free hΩ hfree
  rw [Nat.card_zpowers, hy, card_compl_fixV F] at hdvd
  exact hdvd


theorem card_eq_two_pow_rk [Finite V] (hV : ∀ v : V, v ^ 2 = 1) : Nat.card V = 2 ^ rk V :=
  card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)

theorem eq_one_of_fixV_eq_top {g : MulAut V} (h : fixV (Subgroup.zpowers g) = ⊤) : g = 1 := by
  ext v
  have : v ∈ fixV (Subgroup.zpowers g) := by rw [h]; exact Subgroup.mem_top v
  exact mem_fixV_zpowers_iff.mp this

theorem not_sq_dvd_orderOf [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {q : ℕ} [Fact q.Prime]
    (hq : q = 3 ∨ q = 5) (hrk : rk V ≤ 5) (y : MulAut V) : ¬ q ^ 2 ∣ orderOf y := by
  intro hdvd
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < orderOf y := orderOf_pos y
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  have hy' : orderOf (y ^ m) = q ^ 2 := by
    rw [orderOf_pow_of_dvd hm0 ⟨q ^ 2, by rw [hm]; ring⟩, hm]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  have hfix := sq_dvd_card_sub_card_fixV (q := q) hy'
  have hz : (y ^ m) ^ q ≠ 1 := by
    intro h
    have h1 : orderOf (y ^ m) ∣ q := orderOf_dvd_of_pow_eq_one h
    rw [hy'] at h1
    have h2 := Nat.le_of_dvd (by omega) h1
    nlinarith
  have hFlt : rk (fixV (Subgroup.zpowers ((y ^ m) ^ q))) < rk V := by
    by_contra hge
    rw [not_lt] at hge
    exact hz (eq_one_of_fixV_eq_top (eq_of_le_of_rk_le hV le_top (by rw [rk_top]; exact hge)))
  rw [card_eq_two_pow_rk hV, card_eq_two_pow hV] at hfix
  generalize rk (fixV (Subgroup.zpowers ((y ^ m) ^ q))) = e at hFlt hfix
  generalize rk V = d at hrk hFlt hfix
  rcases hq with rfl | rfl
  · have : ∀ d ≤ 5, ∀ e < d, ¬ 3 ^ 2 ∣ 2 ^ d - 2 ^ e := by decide
    exact this d hrk e hFlt hfix
  · have : ∀ d ≤ 5, ∀ e < d, ¬ 5 ^ 2 ∣ 2 ^ d - 2 ^ e := by decide
    exact this d hrk e hFlt hfix

theorem card_mulAut_eq [Finite V] (hV : ∀ v : V, v ^ 2 = 1) :
    Nat.card (MulAut V) = ∏ i : Fin (rk V), (2 ^ rk V - 2 ^ (i : ℕ)) := by
  unfold rk
  classical
  let _ : Module (ZMod 2) (Additive V) :=
    AddCommGroup.zmodModule (n := 2) (fun x => by
      have := hV (Additive.toMul x)
      show (2 : ℕ) • x = 0
      apply Additive.toMul.injective
      simpa [pow_two] using this)
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hcard : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_congr (Additive.toMul : Additive V ≃ V)] at this
    simpa using this
  have hrk : padicValNat 2 (Nat.card V) = Module.finrank (ZMod 2) (Additive V) := by
    rw [hcard, padicValNat.prime_pow]
  rw [hrk]
  set d := Module.finrank (ZMod 2) (Additive V) with hd
  have hb : Nonempty (Additive V ≃ₗ[ZMod 2] (Fin d → ZMod 2)) :=
    ⟨LinearEquiv.ofFinrankEq _ _ (by simp [hd])⟩
  obtain ⟨b⟩ := hb
  have e1 : MulAut V ≃ (Additive V ≃ₗ[ZMod 2] Additive V) :=
    { toFun := fun g => (MulEquiv.toAdditive g).toLinearEquiv (fun c x => by
        simpa using ZMod.map_smul (MulEquiv.toAdditive g).toAddMonoidHom c x)
      invFun := fun f => MulEquiv.toAdditive.symm f.toAddEquiv
      left_inv := fun g => by ext; rfl
      right_inv := fun f => by ext; rfl }
  have e2 : (Additive V ≃ₗ[ZMod 2] Additive V) ≃ ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) :=
    { toFun := fun f => b.symm.trans (f.trans b)
      invFun := fun g => b.trans (g.trans b.symm)
      left_inv := fun f => by ext; simp
      right_inv := fun g => by ext; simp }
  have e3 : ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) ≃ GL (Fin d) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin d → ZMod 2)).symm.toEquiv.trans
      (Matrix.GeneralLinearGroup.toLin (n := Fin d) (R := ZMod 2)).symm.toEquiv
  rw [Nat.card_congr (e1.trans (e2.trans e3)), Matrix.card_GL_field]
  simp


end Counting

end CFSG.Quasithin
