module

public import CFSG.Quasithin.Background.ONanE68LieSwap
public import CFSG.Quasithin.Background.ONanE68LieSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinNonIso
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentU3
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
public import CFSG.Quasithin.Background.ONanE68Cases
public import CFSG.Quasithin.Background.ONanE68Elim
public import CFSG.Quasithin.Background.ONanE68S8

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68
  CFSG.QuasithinUnique.Vol2Native.L239

section Basic

variable {G : Type} [Group G]

noncomputable def qbarEquiv {L : Subgroup G} (h : Subgroup.center ↥L = ⊥) :
    Bar.Qbar L ≃* ↥L :=
  (mulEquivQuotientCenter h).symm

variable [Finite G] {T M V U L : Subgroup G}

omit [Finite G] in
theorem card_eq_mul_index_of_sylow {P : Subgroup G} (hP : IsSylowTwoOf P L) :
    Nat.card L = Nat.card P * (P.subgroupOf L).index := by
  rw [← Subgroup.card_mul_index (P.subgroupOf L)]
  exact congrArg (· * _) (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv)

omit [Finite G] in
theorem card_omegaCenter_le {S : Type} [Group S] [Finite S] (P : Subgroup S) :
    Nat.card (omegaCenter P) ≤ Nat.card P := Subgroup.card_le_of_le omegaCenter_le

theorem sqtkCharTwoLie_of_psl_two {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 2 n) : Ch1.SQTKCharTwoLie X :=
  Or.inl (Or.inl ⟨n, Or.inl ⟨hn, h⟩⟩)

theorem sqtkCharTwoLie_of_psl_three {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 n) : Ch1.SQTKCharTwoLie X :=
  Or.inl (Or.inl ⟨n, Or.inr (Or.inl ⟨hn, h⟩)⟩)

theorem sqtkCharTwoLie_of_psu_three {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 2 n) : Ch1.SQTKCharTwoLie X :=
  Or.inl (Or.inl ⟨n, Or.inr (Or.inr (Or.inl ⟨hn, h⟩))⟩)

theorem sqtkCharTwoLie_of_psp_two {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 n) : Ch1.SQTKCharTwoLie X :=
  Or.inl (Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hn, h⟩)))⟩)

theorem sqtkCharTwoLie_of_suzuki {X : Type} [Group X] {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (h : CFSG.Blueprint.SuzukiModel X 2 n) : Ch1.SQTKCharTwoLie X :=
  Or.inl (Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hn, h3, h⟩))))))⟩)

end Basic

section Dich

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem isSylowTwoOf_sylowBar (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L)) : IsSylowTwoOf (sylowBar T V L) ⊤ :=
  isSylowTwoOf_map_piBar (RankOneRecog.isSylowTwoOf_inf_of_subnormal (e6_5_one h hU) hL.1 hL.2.2)
    (center_le_sylow h hU hL hZ2)

theorem borel_dichotomy (hInn : Ch1.EvenLieAutInner) (hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L))
    (h121 : Id2519.Prop121Three) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) (hZ0L : Subgroup.center ↥L = ⊥)
    (hCh : CharTwo (borOf T V L))
    (hquot : ∀ a ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
      ∀ b ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
        a * b * a⁻¹ * b⁻¹ ∈ sylowBar T V L)
    (hord : ∀ c ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)), orderOf c = 3 →
      4 < (sylowBar T V L ⊓ Subgroup.centralizer ({c} : Set (Bar.Qbar L))).relIndex
        (sylowBar T V L) ∨
      (Nat.card (sylowBar T V L) = 4 ∧
        sylowBar T V L ⊓ Subgroup.centralizer ({c} : Set (Bar.Qbar L)) = ⊥)) :
    borOf T V L ≤ M ∨ (Nat.card (pgOf T V L) = 4 ∧
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2) := by
  classical
  by_cases hQN : T ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G)
  · rcases borel_le_M_or_small hInn hmod h hU hL hQN (isPGroup_two_of_center_eq_bot hZ0L) hCh
      hquot hord with hle | ⟨⟨c, hc, hc3, hcard, hbot⟩, hsmall⟩
    · exact Or.inl hle
    · exact Or.inr ⟨by rw [← card_sylowBar_of_center_eq_bot hZ0L]; exact hcard, hsmall⟩
  · obtain ⟨q₀, hq₀Q, hq₀N⟩ := IsConcreteLE.not_le_iff_exists.1 hQN
    have hQH := e6_5_one h hU
    have hq₀H : q₀ ∈ Subgroup.centralizer (U : Set G) := hQH.1 hq₀Q
    have hnotH : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) :=
      fun hh => hQN (hQH.1.trans hh)
    have := h.simple
    rcases h121 G h.simple h.nonabelian (qtkeCore_of_cat h.nonabelian h.qtke) _
        (pCoreOf_centralizer_ne_bot h hU) L (Vol2Native.mem_cComp_of_isComponentIn hL) with
      hN | ⟨hcard2, -⟩
    · exact absurd hN hnotH
    · have hne : CFSG.conjugate L q₀ ≠ L := fun heq =>
        hq₀N (BenderBranch.conjugate_eq_iff_mem_normalizer.1 heq)
      have hQ2 : ∀ q ∈ T ⊓ Subgroup.centralizer (V : Set G),
          CFSG.conjugate L q = L ∨ CFSG.conjugate L q = CFSG.conjugate L q₀ := by
        intro q hq
        let a : {L' : Subgroup G // ∃ x ∈ Subgroup.centralizer (U : Set G),
            L' = CFSG.conjugate L x} := ⟨L, 1, Subgroup.one_mem _,
          (BenderBranch.conjugate_one L).symm⟩
        let b : {L' : Subgroup G // ∃ x ∈ Subgroup.centralizer (U : Set G),
            L' = CFSG.conjugate L x} := ⟨CFSG.conjugate L q₀, q₀, hq₀H, rfl⟩
        let c : {L' : Subgroup G // ∃ x ∈ Subgroup.centralizer (U : Set G),
            L' = CFSG.conjugate L x} := ⟨CFSG.conjugate L q, q, hQH.1 hq, rfl⟩
        obtain ⟨y0, -, huniq⟩ := (Nat.card_eq_two_iff' a).1 hcard2
        by_cases hca : c = a
        · exact Or.inl (congrArg Subtype.val hca)
        · right
          have hba : b ≠ a := fun hh => hne (congrArg Subtype.val hh)
          exact congrArg Subtype.val ((huniq c hca).trans (huniq b hba).symm)
      exact borel_le_M_or_small_swap hInn hmod h hU hL hZ0L hq₀Q hne hQ2 hCh hquot hord

end Dich

section RankOne

open CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem out_of_rankOne (hF : E68LieFacts)
    (hInn : Ch1.EvenLieAutInner) (h121 : Id2519.Prop121Three)
    (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {n : ℕ}
    (hfam : (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 2 2 n) ∨
      (Odd n ∧ 3 ≤ n ∧ CFSG.Blueprint.SuzukiModel ↥L 2 n) ∨
      (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 2 n)) :
    E68Out hV T M U L := by
  classical
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hs : IsSimpleGroup ↥L := by
    rcases hfam with ⟨-, hm⟩ | ⟨-, -, hm⟩ | ⟨-, hm⟩
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 n hm).2
    · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 n hm).2
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 n hm).2
  have hZ0L : Subgroup.center ↥L = ⊥ := center_eq_bot_of_simple_quasisimple hq hs
  have hn : 2 ≤ n := by
    rcases hfam with ⟨h2, -⟩ | ⟨-, h3, -⟩ | ⟨h2, -⟩ <;> omega
  have hZ2 := isPGroup_two_of_center_eq_bot hZ0L
  have hZ := center_le_sylow h hU hL hZ2
  have hSyl : IsSylowTwoOf (pgOf T V L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal (e6_5_one h hU) hL.1 hL.2.2
  have hPg2 : IsPGroup 2 (pgOf T V L) := h.isPGroup_Q.to_le inf_le_left
  let e := qbarEquiv hZ0L
  have hSm : (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel (Bar.Qbar L) .PSL 2 2 n) ∨
      (Odd n ∧ 3 ≤ n ∧ CFSG.Blueprint.SuzukiModel (Bar.Qbar L) 2 n) ∨
      (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel (Bar.Qbar L) .PSU 3 2 n) := by
    rcases hfam with ⟨h2, hm⟩ | ⟨ho, h3, hm⟩ | ⟨h2, hm⟩
    · exact Or.inl ⟨h2, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm⟩
    · exact Or.inr (Or.inl ⟨ho, h3, CFSG.SectionRank.suzukiModel_of_mulEquiv e hm⟩)
    · exact Or.inr (Or.inr ⟨h2, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm⟩)
  have hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L) := by
    rcases hSm with ⟨h2, hm⟩ | ⟨ho, h3, hm⟩ | ⟨h2, hm⟩
    · exact sqtkCharTwoLie_of_psl_two h2 hm
    · exact sqtkCharTwoLie_of_suzuki ho h3 hm
    · exact sqtkCharTwoLie_of_psu_three h2 hm
  have hdata := hF.rankOne (Bar.Qbar L) n hSm (sylowBar T V L) (isSylowTwoOf_sylowBar h hU hL hZ2)
  have hCh : CharTwo (borOf T V L) := charTwo_borOf_of_centralizer_le hZ hPg2 hdata.centralizer_le
  have hBM := borel_dichotomy hInn hmod h121 h hU hL hZ0L hCh hdata.quot_comm hdata.order_three
  have hcardP : Nat.card (sylowBar T V L) = Nat.card (pgOf T V L) :=
    card_sylowBar_of_center_eq_bot hZ0L
  have hmodel : (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 n) ∨
      (Odd n ∧ 3 ≤ n ∧ CFSG.Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n) ∨
      (1 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 n) ∨
      (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 n) := by
    rcases hSm with hm | hm | hm
    · exact Or.inl hm
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr (Or.inr hm))
  have hexc : Nat.card (pgOf T V L) = 4 →
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2 → E68Case5 M V U L := by
    intro h4 hsmall
    have hle : 2 ^ n ≤ 4 := by
      rw [← h4, ← hcardP, ← hdata.card_root]
      exact card_omegaCenter_le _
    rcases hfam with ⟨-, hm⟩ | ⟨-, h3, -⟩ | ⟨-, hm⟩
    · have hn2 : n = 2 := by
        by_contra hne
        have : 3 ≤ n := by omega
        have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this
        omega
      subst hn2
      have hmem : (CFSG.Assembly.LowTwoRank.StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by
        decide
      have h5 := statedClassicalModel_psl_two_five_of_alternating_five ↥L
        (PSL2_four_alternating_five_model ↥L (Or.inl ⟨hmem, hm⟩))
      exact case5_of_relIndex_le_two h hU hL
        (Or.inl ⟨5, ⟨by norm_num, Or.inl ⟨1, by norm_num⟩⟩, h5⟩) hsmall
    · exfalso
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
      omega
    · exfalso
      have hn2 : n = 2 := by
        by_contra hne
        have : 3 ≤ n := by omega
        have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this
        omega
      subst hn2
      have hc := Id2519.card_of_statedPSU_three_four hm
      have hidx := card_eq_mul_index_of_sylow hSyl
      rw [hc, h4] at hidx
      have hodd := hSyl.2.2
      omega
  rcases case_of_rankOne hInn hmod hV h hU hL hZ0L hn hdata hBM hmodel hexc with h1 | h5
  · exact Or.inl h1
  · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))

theorem out_of_psl25 (hF : E68LieFacts)
    (hInn : Ch1.EvenLieAutInner) (h121 : Id2519.Prop121Three)
    (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 2 5 1) : E68Out hV T M U L :=
  out_of_rankOne hF hInn h121 hV h hU hL (n := 2) (Or.inl ⟨le_rfl, hF.psl25 ↥L hm⟩)

end RankOne

section RankTwo

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem le_normalizer_of_nonIso
    (h121 : Id2519.Prop121Three) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {n : ℕ}
    (hn : 2 ≤ n)
    (hmq : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 n ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSp 2 2 n) :
    T ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  (e6_5_one h hU).1.trans (le_normalizer_of_not_is121List h121 h hU hL
    (Fin257.nonIso257 ↥L n hn hmq).2.2.2.1)

theorem out_of_lin3
    (hF : E68LieFacts) (hInn : Ch1.EvenLieAutInner)
    (h121 : Id2519.Prop121Three) (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {n : ℕ}
    (hn : 2 ≤ n) (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 3 2 n) :
    E68Out hV T M U L := by
  classical
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hs : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 n hm).2
  have hZ0L : Subgroup.center ↥L = ⊥ := center_eq_bot_of_simple_quasisimple hq hs
  have hZ2 := isPGroup_two_of_center_eq_bot hZ0L
  have hSyl : IsSylowTwoOf (pgOf T V L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal (e6_5_one h hU) hL.1 hL.2.2
  have : Group.IsPerfect ↥L := hq.1
  have hpc : CFSG.pCore 2 ↥L = ⊥ := le_bot_iff.mp ((pCore_two_le_center hq.2.1).trans hZ0L.le)
  have hSm : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Bar.Qbar L) .PSL 3 2 n :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv (qbarEquiv hZ0L) hm
  have hmq : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 n :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv (mulEquivQuotientPCore hpc).symm hm
  have hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L) := sqtkCharTwoLie_of_psl_three (by omega) hSm
  have hQN := le_normalizer_of_nonIso h121 h hU hL hn (Or.inl hmq)
  have hrk : IsRankTwoEvenType L := Or.inl ⟨n, by omega, hm⟩
  have hCh := (rankTwoBorelFacts G L (pgOf T V L) hq hrk hSyl).1
  have hdata := hF.lin3 (Bar.Qbar L) n hn hSm (sylowBar T V L) (isSylowTwoOf_sylowBar h hU hL hZ2)
  have hBX := borel_le_M_of_strict hInn hmod h hU hL hQN hZ2 hCh hdata.quot_comm hdata.order_three
  exact Or.inl (case_of_lin3 hInn hmod hV h hU hL hZ2 hn hdata hBX hSm)

theorem out_of_cover
    (hF : E68LieFacts) (hInn : Ch1.EvenLieAutInner)
    (h121 : Id2519.Prop121Three) (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hc : Subgroup.center ↥L = CFSG.pCore 2 ↥L ∧ Subgroup.center ↥L ≠ ⊥ ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 2) :
    E68Out hV T M U L := by
  classical
  obtain ⟨hcp, -, hm⟩ := hc
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hZ2 : IsPGroup 2 (Subgroup.center ↥L) := by
    have : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
    rwa [← hcp] at this
  have hSyl : IsSylowTwoOf (pgOf T V L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal (e6_5_one h hU) hL.1 hL.2.2
  have hSm : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Bar.Qbar L) .PSL 3 2 2 :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hcp) hm
  have hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L) := sqtkCharTwoLie_of_psl_three (by omega) hSm
  have hQN := le_normalizer_of_nonIso h121 h hU hL (n := 2) le_rfl (Or.inl hm)
  have hrk : IsRankTwoEvenType L := Or.inr (Or.inr (Or.inr hm))
  have hCh := (rankTwoBorelFacts G L (pgOf T V L) hq hrk hSyl).1
  have hdata := hF.lin3 (Bar.Qbar L) 2 le_rfl hSm (sylowBar T V L)
    (isSylowTwoOf_sylowBar h hU hL hZ2)
  have hBX := borel_le_M_of_strict hInn hmod h hU hL hQN hZ2 hCh hdata.quot_comm hdata.order_three
  exact Or.inl (case_of_lin3 hInn hmod hV h hU hL hZ2 le_rfl hdata hBX hSm)

theorem out_of_sp4
    (hF : E68LieFacts) (hInn : Ch1.EvenLieAutInner)
    (h121 : Id2519.Prop121Three) (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {n : ℕ}
    (hn : 2 ≤ n) (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 2 2 n) :
    E68Out hV T M U L := by
  classical
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hs : IsSimpleGroup ↥L :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 2 n hm
  have hZ0L : Subgroup.center ↥L = ⊥ := center_eq_bot_of_simple_quasisimple hq hs
  have hZ2 := isPGroup_two_of_center_eq_bot hZ0L
  have hSyl : IsSylowTwoOf (pgOf T V L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal (e6_5_one h hU) hL.1 hL.2.2
  have : Group.IsPerfect ↥L := hq.1
  have hpc : CFSG.pCore 2 ↥L = ⊥ := le_bot_iff.mp ((pCore_two_le_center hq.2.1).trans hZ0L.le)
  have hSm : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Bar.Qbar L) .PSp 2 2 n :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv (qbarEquiv hZ0L) hm
  have hmq : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSp 2 2 n :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv (mulEquivQuotientPCore hpc).symm hm
  have hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L) := sqtkCharTwoLie_of_psp_two hn hSm
  have hQN := le_normalizer_of_nonIso h121 h hU hL hn (Or.inr hmq)
  have hrk : IsRankTwoEvenType L := Or.inr (Or.inl ⟨n, hn, hm⟩)
  obtain ⟨hCh, P₁, P₂, -, -, -, -, -, hsup, honly, -, -⟩ :=
    rankTwoBorelFacts G L (pgOf T V L) hq hrk hSyl
  have hdata := hF.sp4 (Bar.Qbar L) n hn hSm (sylowBar T V L) (isSylowTwoOf_sylowBar h hU hL hZ2)
  have hBX := borel_le_M_of_strict hInn hmod h hU hL hQN hZ2 hCh hdata.quot_comm hdata.order_three
  exact Or.inr (Or.inl (case_of_sp4 hInn hmod hV h hU hL hZ0L hn hdata hBX hsup honly hm))

end RankTwo

end E68Proof

end E6

end CFSG.Quasithin
