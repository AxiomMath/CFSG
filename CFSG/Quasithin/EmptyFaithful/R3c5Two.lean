module

public import CFSG.Quasithin.EmptyFaithful.R3c2List
public import CFSG.Quasithin.EmptyFaithful.R3c5Pgl
public import CFSG.Quasithin.EmptyFaithful.R3c5Sign
public import CFSG.Quasithin.EmptyFaithful.R3c5Gen
public import CFSG.Quasithin.EmptyFaithful.R3c5Out
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04

public section

namespace CFSG.Quasithin.R3c5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def RankTwoListCatalogue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G),
    Lemma115Cases L z → CFSG.IsQuasisimple ↥L → centerOf L = pCoreOf 2 L →
      (¬ ∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)) → CFSG.Open.pRank 3 L = 2 →
      ∀ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) →
        IsPSLEps3q s q (↥L ⧸ Subgroup.center ↥L) →
          ∃ n : ℕ, q = 2 ^ n ∧ IsPSLEps3 s 2 n (↥L ⧸ Subgroup.center ↥L)

@[expose] def RankTwoSign : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (A : Type) [Group A] [Finite A] (P Y Q : Subgroup A),
    IsPGLEps3 false (2 ^ n) ↥P → IsSylowTwoOf Q P → Y ≤ P →
      Q ≤ Subgroup.normalizer (Y : Set A) → IsPGroup 3 (OTwoQuot Y) →
        2 ≤ CFSG.Open.pRank 3 Y → False

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem OTwoQuot_pow_three_of_struct (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) :
    ∀ z : OTwoQuot Yp, z ^ 3 = 1 := by
  rcases c.facts11.struct_Yp with ⟨⟨e⟩⟩ | ⟨-, -, hexp⟩
  · intro z
    apply e.injective
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    funext i
    have h1 : ∀ a : ZMod 3, 3 • a = 0 := by decide
    simpa [toAdd_pow] using h1 (Multiplicative.toAdd (e z) i)
  · exact hexp

theorem isPSLEps3q_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {s : Bool} {q : ℕ}
    (h : IsPSLEps3q s q Y) : IsPSLEps3q s q X := by
  obtain ⟨p, n, hp, hn, hq, hY⟩ := h
  refine ⟨p, n, hp, hn, hq, ?_⟩
  cases s
  · obtain ⟨hadm, K, hK, hKf, hcard, ⟨e'⟩⟩ := hY
    exact ⟨hadm, K, hK, hKf, hcard, ⟨e.trans e'⟩⟩
  · obtain ⟨hadm, K, hK, hKf, hcard, ⟨e'⟩⟩ := hY
    exact ⟨hadm, K, hK, hKf, hcard, ⟨e.trans e'⟩⟩

theorem even_of_two_pow_modEq_one {n : ℕ} (h : Int.ModEq 3 ((2 ^ n : ℕ) : ℤ) 1) : Even n := by
  by_contra hodd
  have h1 := R3c.two_pow_mod_three_of_odd (Nat.not_even_iff_odd.mp hodd)
  have h2 : ((2 ^ n : ℕ) : ℤ) % 3 = 1 := by simpa [Int.ModEq] using h
  omega

theorem two_le_of_isPSU_three_two {n : ℕ} {X : Type} [Group X] (h : IsPSU 3 2 n X) : 2 ≤ n := by
  obtain ⟨⟨-, hn, -, hne⟩, -⟩ := h
  by_contra hlt
  have : n = 1 := by omega
  subst this
  exact hne (by simp)

omit [Finite G] in
theorem transport_decomposition {I L Y : Subgroup G} (hYI : Y ≤ I) {y' : ↥I}
    (hdec : Y.subgroupOf I = oTwoUpper (Y.subgroupOf I ⊓ L.subgroupOf I) ⊔ Subgroup.zpowers y' ⊔
      pCoreOf 2 (Y.subgroupOf I)) :
    Y = oTwoUpper (Y ⊓ L) ⊔ Subgroup.zpowers (y' : G) ⊔ pCoreOf 2 Y := by
  have h := congrArg (Subgroup.map I.subtype) hdec
  have hinf : Y.subgroupOf I ⊓ L.subgroupOf I = (Y ⊓ L).subgroupOf I :=
    (Subgroup.comap_inf _ _ _).symm
  rw [Subgroup.map_subgroupOf_eq_of_le hYI, Subgroup.map_sup, Subgroup.map_sup, hinf,
    map_oTwoUpper_subgroupOf (inf_le_left.trans hYI), map_pCoreOf_subgroupOf hYI,
    MonoidHom.map_zpowers] at h
  exact h

theorem input15337RankTwo_of_named (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h36 : A36ForSQTK)
    (hF : A318Facts) (hE : CFSG.Quasithin.Vol2.Ch11.SecA.FactA318Excl) (hlist : Lemma115_3_List)
    (hA : R3c2.Input15333Two) (kCat : RankTwoListCatalogue)
    (kSign : RankTwoSign) : Input15337RankTwo := by
  classical
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL0 hr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hq := hh.hyp.qtfe
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hYI : Yp ≤ I := le_sup_left.trans c.inH.1.1
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hSQ : SQTKGroup ↥I :=
    sqtkGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian c.inH.1.2
  have hSQ' := SQTKHyp.of_sqtkGroup ↥I hSQ
  have hQ : CFSG.IsQuasisimple ↥L := c.c33.quasisimple
  have hZ : IsPGroup 2 ↥(Subgroup.center ↥L) := R3c3.isPGroup_two_center c.c33.center_eq
  have h3L : 3 ∣ Nat.card ↥L := R3c2.three_dvd_card_of_one_le_pRank L (by omega)
  have hI3 : CFSG.Open.pRank 3 I ≤ 2 :=
    pRank_le_two_of_pCoreOf_ne_bot hq.qtke c.inH.1.2 Nat.prime_three (by norm_num)
  have hLc' : L.subgroupOf I ∈ cComp (⊤ : Subgroup ↥I) := subgroupOf_mem_cComp hLc
  let eL : ↥(L.subgroupOf I) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLI
  have hQ' : CFSG.IsQuasisimple ↥(L.subgroupOf I) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hQ
  have hZ' : IsPGroup 2 ↥(Subgroup.center ↥(L.subgroupOf I)) :=
    hZ.of_equiv (Subgroup.centerCongr eL).symm
  have hr' : 1 < CFSG.Open.pRank 3 (L.subgroupOf I) := by
    rw [R3c2.pRank_three_subgroupOf hLI]
    omega
  have h3L' : 3 ∣ Nat.card ↥(L.subgroupOf I) := by
    rw [Nat.card_congr eL.toEquiv]
    exact h3L
  have hYo' : oTwoUpper (Yp.subgroupOf I) = Yp.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_oTwoUpper_subgroupOf hYI, c.hyp.oTwoUpper_eq, Subgroup.map_subgroupOf_eq_of_le hYI]
  have hYe' : ∀ z : OTwoQuot (Yp.subgroupOf I), z ^ 3 = 1 :=
    OTwoQuot_pow_three_subgroupOf hYI (OTwoQuot_pow_three_of_struct c)
  have hrY' : 2 ≤ CFSG.Open.pRank 3 (Yp.subgroupOf I) := by
    rw [R3c2.pRank_three_subgroupOf hYI, c.rank]
  have hSY : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := S153D.Sgp153_le_normalizer_Yp hh
  have hSY' : (Sgp153 T V₁).subgroupOf I ≤ Subgroup.normalizer ((Yp.subgroupOf I : Subgroup ↥I) : Set ↥I) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := (Subgroup.mem_normalizer_iff.mp (hSY hs) (y : G))
    simpa [Subgroup.mem_subgroupOf] using this
  have hSyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    S153D.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hLc) c.facts11.sylow
  have hSyl' : IsSylowTwoOf ((Sgp153 T V₁).subgroupOf I ⊓ L.subgroupOf I) (L.subgroupOf I) := by
    have := isSylowTwoOf_subgroupOf (I := I) hLI hSyl
    rwa [show (Sgp153 T V₁ ⊓ L).subgroupOf I = (Sgp153 T V₁).subgroupOf I ⊓ L.subgroupOf I from
      Subgroup.comap_inf _ _ _] at this
  have hLn : (L.subgroupOf I).Normal :=
    A318.normal_of_pRank_gt_one hSQ (h38 _ hSQ') hLc' Nat.prime_three (by norm_num) hr'
  have : (L.subgroupOf I).Normal := hLn
  rcases rankTwo_H hF hE.2 pglIndex_holds hSQ (h36 _ hSQ') (h38 _ hSQ') hLc' hQ' hZ' hr' hYo' hYe' with
    hYL | ⟨s, q, hqmod, hSq, hPGL, hXP, hcard, y', hy'Y, hy'ord, hy'L, hdec⟩
  · left
    have := Subgroup.map_mono (f := I.subtype) hYL
    rwa [Subgroup.map_subgroupOf_eq_of_le hYI, Subgroup.map_subgroupOf_eq_of_le hLI] at this
  · right
    obtain ⟨p, e, hp, he, hqp, hX'⟩ := hSq
    have hSq0 : IsPSLEps3q s q ↥(starImage 3 (L.subgroupOf I)) := ⟨p, e, hp, he, hqp, hX'⟩
    have hXs : IsSimpleGroup ↥(starImage 3 (L.subgroupOf I)) := (isPSLEps3_finite_simple hX').2
    obtain ⟨eX⟩ := nonempty_starImage_equiv_quotCenter hQ' h3L' hXs
    let eQ : (↥(L.subgroupOf I) ⧸ Subgroup.center ↥(L.subgroupOf I)) ≃*
        (↥L ⧸ Subgroup.center ↥L) :=
      QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)
    have hSq' : IsPSLEps3q s q (↥L ⧸ Subgroup.center ↥L) :=
      isPSLEps3q_of_mulEquiv (eX.trans eQ).symm hSq0
    obtain ⟨z, hz⟩ := hA G T Mc M V₁ V₂ Yp I t c.toCtxComp
    have hcomp : IsComponentIn L I :=
      Id2519.isComponentIn_of_mem_cComp c.c33.mem c.c33.quasisimple
    have hsimple : IsSimpleGroup G := hq.simple
    have hcore : QTKECore G := qtkeCore_of_cat hq.nonabelian hq.qtke
    have hcases : Lemma115Cases L z :=
      (Lemma115_3_List.component_cases hlist hsimple hq.nonabelian hcore hz hcomp).2.2.2
    obtain ⟨n, hqn, hLn⟩ := kCat G L z hcases hQ c.c33.center_eq c.c34.not_Sz hr s q hqmod hSq'
    cases s
    ·
      exfalso
      have hn2 : 2 ≤ n := two_le_of_isPSU_three_two hLn
      obtain ⟨hSyl2, hnorm, hYP, hY3, hYr⟩ := sign_hyps hYo' hYe' hrY' hSY' hSyl' hXP hcard
      subst hqn
      exact kSign n hn2 (PStar 3 ↥I) _ _ _ hPGL hSyl2 hYP hnorm hY3 hYr
    · have hn_even : Even n := by
        subst hqn
        exact even_of_two_pow_modEq_one (by simpa using hqmod)
      have hyL : (y' : G) ∉ L := hy'L
      refine ⟨Or.inl ⟨n, hn_even, hLn⟩,
        S153D.YL153_ne_bot h37 h38 hh c.inH c.rank hLc c.c34.rank, (y' : G), hy'Y, ?_, ?_, ?_⟩
      · rw [Subgroup.orderOf_coe]
        exact hy'ord
      · exact not_mem_sup_centralizer hLI hZ (by omega) hI3 y'.2
          (by rw [Subgroup.orderOf_coe]; exact hy'ord) hyL
      · exact transport_decomposition hYI hdec

end CFSG.Quasithin.R3c5
