module

public import CFSG.Quasithin.Vol2.Ch10SecALift
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114Orders
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114FSU
public import CFSG.Quasithin.Vol2.Ch6Remark612
public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Timmesfeld.Orders
  CFSG.Timmesfeld.ClassicalOrders
open scoped IsMulCommutative

theorem L2_two_adic {n a b : ℕ} (hn : 1 ≤ n) (hb : Odd b)
    (h : 2 ^ n * ((2 ^ n) ^ 2 - 1) = 2 ^ a * b) : n = a ∧ (2 ^ n) ^ 2 - 1 = b := by
  have ha := eq_of_two_pow_mul_odd (odd_two_pow_pow_sub_one hn (by norm_num)) hb h
  subst ha
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem card_SL3_ne_L2_odd {F : Type} [Field F] [Finite F] {k n : ℕ} (hF : Nat.card F = 2 ^ k)
    (hn : 1 ≤ n) : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) ≠ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  intro he
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hF
      exact absurd hF (Finite.one_lt_card).ne'
    · exact h0
  rw [L34Orders.card_SL3, hF] at he
  have hodd : Odd (((2 ^ k) ^ 3 - 1) * ((2 ^ k) ^ 2 - 1)) :=
    (odd_two_pow_pow_sub_one hk (by norm_num)).mul (odd_two_pow_pow_sub_one hk (by norm_num))
  have he2 : 2 ^ n * ((2 ^ n) ^ 2 - 1) =
      2 ^ (k * 3) * (((2 ^ k) ^ 3 - 1) * ((2 ^ k) ^ 2 - 1)) := by
    rw [pow_mul]
    exact he.symm
  obtain ⟨hnk, he'⟩ := L2_two_adic hn hodd he2
  subst hnk
  rw [pow_mul] at he'
  set q := 2 ^ k with hq
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h3 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
  have h2 : q ^ 2 + 1 ≤ q ^ 3 := by nlinarith
  have hlt : (q ^ 3 - 1) * (q ^ 2 - 1) < (q ^ 3) ^ 2 - 1 := by
    have e : (q ^ 3) ^ 2 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
      have : 1 ≤ q ^ 3 := by omega
      zify [this, Nat.one_le_pow 2 (q ^ 3) (by omega)]
      ring
    rw [e]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  omega

theorem card_statedSp_ne_L2_odd {F : Type} [Field F] [Finite F] {k n : ℕ}
    (hF : Nat.card F = 2 ^ k) (hn : Odd n) :
    Nat.card (CFSG.Assembly.LowTwoRank.StatedSp 2 F) ≠ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  intro he
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hF
      exact absurd hF (Finite.one_lt_card).ne'
    · exact h0
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF,
    show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)] at he
  have hodd : Odd (((2 ^ k) ^ (2 * 1) - 1) * ((2 ^ k) ^ (2 * 2) - 1)) :=
    (odd_two_pow_pow_sub_one hk (by norm_num)).mul (odd_two_pow_pow_sub_one hk (by norm_num))
  have he2 : 2 ^ n * ((2 ^ n) ^ 2 - 1) =
      2 ^ (k * 2 ^ 2) * (((2 ^ k) ^ (2 * 1) - 1) * ((2 ^ k) ^ (2 * 2) - 1)) := by
    rw [pow_mul]
    exact he.symm
  have hn1 : 1 ≤ n := by obtain ⟨j, rfl⟩ := hn; omega
  obtain ⟨hnk, -⟩ := L2_two_adic hn1 hodd he2
  rw [hnk] at hn
  exact absurd hn (by rw [Nat.not_odd_iff_even]; exact ⟨2 * k, by ring⟩)

theorem L2_odd_ne_360 {n : ℕ} (hn : 1 ≤ n) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 360 := by
  intro he
  obtain ⟨rfl, h⟩ := L2_two_adic (a := 3) (b := 45) hn ⟨22, by norm_num⟩ (he.trans (by norm_num))
  norm_num at h

theorem L2_odd_ne_20160 {n : ℕ} (hn : Odd n) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 20160 := by
  intro he
  have hn1 : 1 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
  obtain ⟨rfl, -⟩ := L2_two_adic (a := 6) (b := 315) hn1 ⟨157, by norm_num⟩ (he.trans (by norm_num))
  exact absurd hn (by decide)

theorem L2_odd_ne_9999360 {n : ℕ} (hn : Odd n) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 9999360 := by
  intro he
  have hn1 : 1 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
  obtain ⟨rfl, -⟩ :=
    L2_two_adic (a := 10) (b := 9765) hn1 ⟨4882, by norm_num⟩ (he.trans (by norm_num))
  exact absurd hn (by decide)

theorem L2_odd_ne_2520 {n : ℕ} (hn : 1 ≤ n) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 2520 := by
  intro he
  obtain ⟨rfl, h⟩ := L2_two_adic (a := 3) (b := 315) hn ⟨157, by norm_num⟩ (he.trans (by norm_num))
  norm_num at h

section General

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_one_mem_centralizer {T X : Subgroup G} (hT : IsPGroup 2 T) (hXT : X ≤ T)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hX : X ≠ ⊥) :
    ∃ z ∈ X, z ≠ 1 ∧ z ∈ Subgroup.centralizer (T : Set G) := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (X.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTX
  have hne : X.subgroupOf T ≠ ⊥ := by
    intro h
    apply hX
    rw [← Subgroup.map_subgroupOf_eq_of_le hXT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨y, hy.1, fun h1 => hy1 (Subtype.ext (Subtype.ext h1)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)

theorem le_normalizer_centralizer_of_le {T L : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    T ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) := by
  intro t ht
  apply mem_normalizer_of_forall_conj_mem'
  intro c hc
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro l hl
  have hl' : t⁻¹ * l * t ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hTL (T.inv_mem ht)) l).mp hl
    simpa using this
  have hc' := hc _ hl'
  calc l * (t * c * t⁻¹) = t * ((t⁻¹ * l * t) * c) * t⁻¹ := by group
    _ = t * (c * (t⁻¹ * l * t)) * t⁻¹ := by rw [hc']
    _ = t * c * t⁻¹ * l := by group

end General

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_0_1

variable (h : Hyp5_0_1 G T M L n)
include h

theorem pCoreOf_le_centralizer_L {W : Subgroup G} (hW : W ≤ reducedAggregate (L ⊔ T)) :
    pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : IsSubnormal L (L ⊔ T) :=
    IsSubnormal.step le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr h.sup_le_normalizer)
      (IsSubnormal.refl _)
  exact (A4.pCoreOf_le_of_subnormal 2 hsub).trans
    ((reducedAggregate_props _).2.2.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hW)))

theorem card_autOn_L {W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hW : W ≤ reducedAggregate (L ⊔ T)) (hne : ¬ L ≤ Subgroup.centralizer (W : Set G)) :
    Nat.card ↥(autOn L W) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨e⟩ := nonempty_autOn_equiv_O2Q h.isSimple hLW (h.pCoreOf_le_centralizer_L hW) hne
  rw [Nat.card_congr e.toEquiv]
  exact h.card_quot

theorem inf_centralizer_eq_bot {W : Subgroup G} (hWR : W ≤ reducedAggregate (L ⊔ T))
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hZ : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    W ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hR2, -, hRO, -⟩ := CFSG.Quasithin.Vol2.Ch11.SecA.reducedAggregate_props (L ⊔ T)
  have hTS : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  have hWT : W ≤ T := hWR.trans (hRO.trans (pCoreOf_le_of_isSylowTwoOf hTS))
  by_contra hne
  have hTC := le_normalizer_centralizer_of_le h.T_le_normalizer
  have hTX : T ≤ Subgroup.normalizer
      ((W ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hTW ht) x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp (hTC ht) x).mp hx.2⟩
  obtain ⟨z, hzX, hz1, hzT⟩ :=
    exists_ne_one_mem_centralizer hTS.2.1 (inf_le_left.trans hWT) hTX hne
  have hzZ : z ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨hWT hzX.1, hzT⟩, hR2 z (hWR hzX.1)⟩
  have hmem : z ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := ⟨hzZ, hzX.2⟩
  rw [hZ, Subgroup.mem_bot] at hmem
  exact hz1 hmem

end Hyp5_0_1

omit [Finite G] in
theorem IsNatModCh5.ne_bot {L W : Subgroup G} {n : ℕ} (hW : IsNatModCh5 L W n) : W ≠ ⊥ := by
  obtain ⟨-, _, K, _, _, -, π, hπ⟩ := hW
  obtain ⟨β, hβs, -, -⟩ := Vol2.Ch10.SecA.exists_beta_of_realizesVia_nat hπ
  intro hb
  obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd ![1, 0])
  have hw1 : w = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall W).mp hb (w : G) w.2)
  rw [hw1, map_one] at hw
  have := congrFun (congrArg Multiplicative.toAdd hw) 0
  simp at this

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem exists_natural_of_odd (hIrr : IrrPlusBaseNonempty) (h323 : Stmt3_2_3)
    (h325 : Stmt3_2_5) (h3228 : Stmt3_2_2_eight) (h513 : Stmt5_1_3) (h5114 : Stmt5_1_14_first)
    (hn : Odd n) :
    ∃ V₀ : Subgroup G, IsCh5Module T L V₀ ∧ IsNatModCh5 L V₀ n ∧ V₀ ≤ T ∧
      T ≤ Subgroup.normalizer (V₀ : Set G) ∧ IsTISetUnder V₀ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  have hn1 : 1 ≤ n := by obtain ⟨j, rfl⟩ := hn; omega
  have hL0 : conjClosure L T = L := hh.conjClosure_eq
  have hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    (h5114 G T M L V H B D n h.hyp h.notation59 h.module h.l34).2.2
  obtain ⟨I, hI⟩ := hIrr G T L hh.simple hh.nonabelian hh.qtke hh.sylow hh.maximal hh.faithful
    hh.isQuasisimple hh.T_le_normalizer
  obtain ⟨-, -, h323I⟩ := h323 G T L hh.simple hh.nonabelian hh.qtke hh.sylow hh.maximal
    hh.faithful hh.isQuasisimple
  rw [hL0] at h323I
  obtain ⟨V₀, hV₀, -, hfsu⟩ := h323I I hI
  obtain ⟨hV₀R, hV₀ne, hLV₀, hV₀L, -, hV₀irr, -⟩ := hV₀
  have hne₀ : ¬ L ≤ Subgroup.centralizer (V₀ : Set G) := by
    intro hc
    apply hV₀ne
    rw [← hV₀L]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (Subgroup.le_centralizer_iff.mp hc)
  have hVR : conjClosure V₀ T ≤ reducedAggregate (L ⊔ T) :=
    Hyp5_1_14.conjClosure_le_reducedAggregate hV₀R
  have hLV : L ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) :=
    le_normalizer_conjClosure_of_le hh.T_le_normalizer hLV₀
  have hneV : ¬ L ≤ Subgroup.centralizer (conjClosure V₀ T : Set G) := fun hc =>
    hne₀ (hc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure V₀ T))))
  have hcardV := hh.card_autOn_L hLV hVR hneV
  obtain ⟨-, -, hcases⟩ := h325 G T L V₀ hfsu hL0.symm
  have hcase : V₀ = conjClosure V₀ T ∧ IsTISetUnder V₀ M := by
    rcases hcases with ⟨h1, h1'⟩ | ⟨h1, -, -, -, hTI⟩ | ⟨-, hlist, -⟩
    · refine ⟨h1, fun g hg hgV => absurd ?_ hgV⟩
      rw [h1, h1']
      exact le_normalizer_conjClosure _ _ (hh.normal hg)
    · exact ⟨h1, fun g hg hgV => hTI g (hh.normal hg) hgV⟩
    · exfalso
      rcases hlist with ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
        ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
      · exact card_SL3_ne_L2_odd hF hn1 ((Nat.card_congr e.toEquiv).symm.trans hcardV)
      · exact card_statedSp_ne_L2_odd hF hn ((Nat.card_congr e.toEquiv).symm.trans hcardV)
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [L34Orders.card_alt 6 (by norm_num)] at h1
        exact L2_odd_ne_360 hn1 (h1.symm.trans (by norm_num [Nat.factorial]))
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [L34Orders.card_SL4_two] at h1
        exact L2_odd_ne_20160 hn h1.symm
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [L34Orders.card_SL5_two] at h1
        exact L2_odd_ne_9999360 hn h1.symm
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [L34Orders.card_alt 7 (by norm_num)] at h1
        exact L2_odd_ne_2520 hn1 (h1.symm.trans (by norm_num [Nat.factorial]))
  obtain ⟨hVeq, hTI⟩ := hcase
  obtain ⟨hVLT, hred, -⟩ := h3228 G T L V₀ hfsu
  rw [hL0, ← hVeq] at hVLT hred
  have hmod : IsCh5Module T L V₀ := ⟨hVLT, hred, fun hb => hV₀ne (by rw [← hV₀L]; exact hb)⟩
  have hV₀T : V₀ ≤ T := by
    obtain ⟨-, -, hRO, -⟩ := CFSG.Quasithin.Vol2.Ch11.SecA.reducedAggregate_props (L ⊔ T)
    exact hV₀R.trans (hRO.trans (pCoreOf_le_of_isSylowTwoOf (hh.isSylowTwoOf le_sup_right)))
  have hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G) := by
    rw [hVeq]
    exact le_normalizer_conjClosure V₀ T
  have hCV : V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ := hh.inf_centralizer_eq_bot hV₀R hTV₀ hZL
  have hirr : ∀ J : Subgroup G, J ≤ V₀ → L ≤ Subgroup.normalizer (J : Set G) →
      J = ⊥ ∨ J = V₀ := by
    intro J hJ hLJ
    have := hV₀irr J (by rw [hCV]; exact bot_le) hJ hLJ
    rwa [hCV] at this
  refine ⟨V₀, hmod, ?_, hV₀T, hTV₀, hTI⟩
  rcases h513 G T M L V₀ n hh hmod with ⟨W₁, W₂, hW₁, hW₂, h12, h12s, hN1, hN2⟩ | ⟨rfl, -⟩ |
      hnat | ⟨m, hm, -⟩ | ⟨-, ⟨e⟩, -⟩
  ·
    exfalso
    have hW₁V : W₁ = V₀ := (hirr W₁ (h12s ▸ le_sup_left) hW₁).resolve_left hN1.ne_bot
    have hW₂V : W₂ = V₀ := (hirr W₂ (h12s ▸ le_sup_right) hW₂).resolve_left hN2.ne_bot
    rw [hW₁V, hW₂V, inf_idem] at h12
    exact hV₀ne h12
  · exact absurd hn (by decide)
  ·
    have hsub : (Subgroup.centralizer (L : Set G)).subgroupOf V₀ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (x : G) ∈ V₀ ⊓ Subgroup.centralizer (L : Set G) := ⟨x.2, hx⟩
      rw [hCV, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (Subtype.ext hx')
    rw [hV₀L] at hnat
    obtain ⟨hLV', hc, hb⟩ := hnat
    rw [hsub] at hb
    exact ⟨hLV', hc, hb⟩
  · exact absurd hn (by rw [hm, Nat.not_odd_iff_even]; exact even_two_mul m)
  ·
    exfalso
    have hcard₀ := hh.card_autOn_L hLV₀ hV₀R hne₀
    have : Finite ↥(autOn (L ⊔ T) V₀) := Finite.of_equiv _ e.toEquiv.symm
    have hle := Subgroup.card_le_of_le (A4.autOn_mono (V := V₀) (le_sup_left : L ≤ L ⊔ T))
    rw [hcard₀, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at hle
    have hn3 : 3 ≤ n := by
      obtain ⟨j, rfl⟩ := hn
      have := hh.two_le
      omega
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h63 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 h63
    norm_num [Nat.factorial] at hle
    omega

end Hyp5_1_14

end CFSG.Quasithin.H13
