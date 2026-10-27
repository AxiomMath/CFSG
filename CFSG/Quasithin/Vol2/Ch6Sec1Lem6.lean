module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem3
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.Quasithin.Vol2.Ch6NatFacts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem inf_omegaOneCenter_ne_bot_of_normal {T N : Subgroup G} (hT : IsPGroup 2 T)
    (hNT : N ≤ T) (hN : T ≤ Subgroup.normalizer (N : Set G)) (hN1 : N ≠ ⊥) :
    N ⊓ quasithinOmegaOneCenter T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  have hnorm : (N.subgroupOf T).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNT]
    exact hN
  have hne : N.subgroupOf T ≠ ⊥ := by
    intro h0
    apply hN1
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hNT hv⟩ : ↥T) ∈ N.subgroupOf T := hv
    rw [h0, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hK1 : N.subgroupOf T ⊓ Subgroup.center ↥T ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hK2 : IsPGroup 2 ↥(N.subgroupOf T ⊓ Subgroup.center ↥T) := hT.to_subgroup _
  obtain ⟨k, hk⟩ := hK2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hK1
    rw [pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(N.subgroupOf T ⊓ Subgroup.center ↥T)) 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxN : (((x : ↥T) : G)) ∈ N := (Subgroup.mem_inf.mp x.2).1
  have hxZ : (x : ↥T) ∈ Subgroup.center ↥T := (Subgroup.mem_inf.mp x.2).2
  have hxsq : ((x : ↥T) : G) ^ 2 = 1 := by
    have := congrArg (fun y : ↥(N.subgroupOf T ⊓ Subgroup.center ↥T) => ((y : ↥T) : G)) hx2
    simpa using this
  have hmem : ((x : ↥T) : G) ∈ quasithinOmegaOneCenter T := by
    refine Subgroup.subset_closure ⟨⟨(x : ↥T).2, ?_⟩, hxsq⟩
    show ((x : ↥T) : G) ∈ Subgroup.centralizer (T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := Subgroup.mem_center_iff.mp hxZ ⟨t, ht⟩
    exact congrArg Subtype.val this
  intro h0
  apply hx1
  have : ((x : ↥T) : G) ∈ (⊥ : Subgroup G) := h0 ▸ ⟨hxN, hmem⟩
  rw [Subgroup.mem_bot] at this
  exact Subtype.ext (Subtype.ext this)

variable {T M L V : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem IsNatQuotCh5.isNatModCh5 {W : Subgroup G} (h : IsNatQuotCh5 L W n)
    (hW : W ⊓ Subgroup.centralizer (L : Set G) = ⊥) : IsNatModCh5 L W n := by
  obtain ⟨hLW, hc, hB⟩ := h
  have hsub : (Subgroup.centralizer (L : Set G)).subgroupOf W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have : (x : G) ∈ W ⊓ Subgroup.centralizer (L : Set G) := ⟨x.2, hx⟩
    rw [hW, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  rw [hsub] at hB
  exact ⟨hLW, hc, hB⟩

namespace Hyp611

theorem omegaOneCenter_inf_centralizer_eq_bot (h331 : Stmt3_3_1) (h432 : Stmt4_3_2)
    (h615 : Stmt6_1_5) (h : Hyp611 G T M L V n) :
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hU := h.isUniqueM h432
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    (Subgroup.closure_le _).mpr fun z hz => hz.1.1
  have hY2 : IsPGroup 2 ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) :=
    h.sylow.1.to_le (inf_le_left.trans hZT)
  have hLTY : L ⊔ T ≤ Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    refine sup_le (fun l hl => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp hy.2 l hl).symm))
      fun t ht => ?_
    have h1 : t ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
      normalizer_le_normalizer_quasithinOmegaOneCenter T (Subgroup.le_normalizer ht)
    have h2 : t ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
      F7.normalizer_le_normalizer_centralizer L (h.T_le.trans h.normal ht)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp h1 y,
      Subgroup.mem_normalizer_iff.mp h2 y]
  have hNY := le_of_isUniqueM_of_le_twoLocal hU hLTY ⟨_, hne, hY2, rfl⟩
  have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M :=
    (Subgroup.centralizer_le (show ((quasithinOmegaOneCenter T ⊓
        Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) ⊆
        (quasithinOmegaOneCenter T : Set G) from inf_le_left)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNY)
  obtain ⟨-, hB⟩ := h331 G T h.simple h.nonabelian h.qtke h.sylow
  obtain ⟨⟨-, -, huniq⟩, -, ⟨H, hH⟩, -⟩ := hB L h.maximal h.toHyp5_0_1.isQuasisimple
  have hMeq := huniq M h.maxTwoLocal (sup_le h.L_le h.T_le)
  rw [← hMeq] at hH
  exact hH.2.1 ((h615 G T M L V n h H hH).trans hCZ)

theorem inf_centralizer_eq_bot (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h : Hyp611 G T M L V n) : T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  by_contra hne
  have hN : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro t ht
    have h2 : t ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
      F7.normalizer_le_normalizer_centralizer L (h.T_le.trans h.normal ht)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp
      (Subgroup.le_normalizer ht) y, Subgroup.mem_normalizer_iff.mp h2 y]
  apply inf_omegaOneCenter_ne_bot_of_normal h.sylow.1 inf_le_left hN hne
  rw [eq_bot_iff, ← h.omegaOneCenter_inf_centralizer_eq_bot h331 h432 h615]
  rintro x ⟨⟨-, hxC⟩, hxZ⟩
  exact ⟨hxZ, hxC⟩

theorem inf_centralizer_V_eq_bot (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h : Hyp611 G T M L V n) : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff, ← h.inf_centralizer_eq_bot h331 h432 h615]
  exact fun x hx => ⟨h.le_T hx.1, hx.2⟩

theorem isNatModCh5_commutator (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h614 : Stmt6_1_4)
    (h615 : Stmt6_1_5) (h : Hyp611 G T M L V n) : IsNatModCh5 L ⁅V, L⁆ n := by
  refine (h614 G T M L V n h).isNatModCh5 ?_
  rw [eq_bot_iff, ← h.inf_centralizer_V_eq_bot h331 h432 h615]
  exact fun x hx =>
    ⟨Subgroup.le_normalizer_iff_commutator_le_left.mp h.L_le_normalizer hx.1, hx.2⟩

theorem eq_commutator_of (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h615 : Stmt6_1_5) (h : Hyp611 G T M L V n) (hJ : ⁅L, thompsonJ T⁆ = L) : V = ⁅V, L⁆ := by
  have hVC := h.inf_centralizer_V_eq_bot h331 h432 h615
  rcases h512 G T M L V n h.toHyp5_0_1 h.module with ⟨hJV, -⟩ | ⟨-, h2⟩ | ⟨-, -, hsplit, -⟩
  ·
    exfalso
    apply h.module.2.2
    have hJO : thompsonJ T ≤ pCoreOf 2 (L ⊔ T) := by
      rw [← h.centralizer_eq]
      exact le_inf (GammaExtra.thompsonJ_le fun A hA => hA.1) (hJV.trans inf_le_right)
    have hLO : L ≤ pCoreOf 2 (L ⊔ T) := by
      have h1 : ⁅L, thompsonJ T⁆ ≤ pCoreOf 2 (L ⊔ T) :=
        (Subgroup.commutator_mono le_rfl hJO).trans
          (Subgroup.le_normalizer_iff_commutator_le_right.mp
            (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))))
      rwa [hJ] at h1
    have hLC : L ≤ Subgroup.centralizer (V : Set G) := by
      rw [← h.centralizer_eq] at hLO
      exact hLO.trans inf_le_right
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLC
  ·
    exact ((h2.isNatModCh5 hVC).commutator_eq).symm
  ·
    have h0 : V ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) = ⊥ := by
      rw [eq_bot_iff, ← hVC]
      exact fun x hx => ⟨hx.1, Subgroup.centralizer_le
        (show (L : Set G) ⊆ ((L ⊔ T : Subgroup G) : Set G) from (le_sup_left : L ≤ L ⊔ T))
        hx.2⟩
    have := hsplit.2
    rw [h0, sup_bot_eq] at this
    exact this.symm

theorem lemma_6_1_6_one_two (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h : Hyp611 G T M L V n) :
    (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
      T ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∧
    (IsNatModCh5 L ⁅V, L⁆ n ∧ (⁅L, thompsonJ T⁆ = L → V = ⁅V, L⁆)) :=
  ⟨⟨h.omegaOneCenter_inf_centralizer_eq_bot h331 h432 h615,
      h.inf_centralizer_eq_bot h331 h432 h615⟩,
    h.isNatModCh5_commutator h331 h432 h614 h615, h.eq_commutator_of h331 h432 h512 h615⟩

end Hyp611

end CFSG.Quasithin.H13
