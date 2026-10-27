module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8Set
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Comp
public import CFSG.Quasithin.Background.E6EightStmt
public import CFSG.Quasithin.EmptyFaithful.T1515eA
public import CFSG.Quasithin.Background.C1PackS15205F
public import CFSG.Quasithin.EmptyFaithful.R3c2Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Families
public import CFSG.Quasithin.EmptyFaithful.S146xB2Cmp
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique S1248

@[expose] def L32ListFact1248 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (z : Y), CFSG.IsQuasisimple ↥K →
    CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSL 3 2 1 →
      IsPGroup 2 (Subgroup.center ↥K) →
    Lemma115Cases K z → Subgroup.center ↥K = ⊥

@[expose] def L33ExclusionFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 3 1 →
    A318Exclusion X

@[expose] def HatA67Fact1248 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → Nat.card (Subgroup.center X) = 3 →
    (Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 7))) →
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) ∧ ∀ (s : Bool) (q : ℕ), ¬ IsPSLEps3q s q X ∧
      ¬ IsSLEps3 s q X

@[expose] def L2pThreeFact1248 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), Ch1.IsFermatOrMersennePrime p →
    CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p 1 → 3 ∣ Nat.card X ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1

namespace S1248

variable {G : Type} [Group G] [Finite G] {T L V U : Subgroup G} {z : G}

theorem mem_cComp_normalizer_of_isComponentIn {W K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer (W : Set G))) :
    K ∈ cComp (Subgroup.normalizer (W : Set G)) := by
  have hKc : K ∈ cComp (Subgroup.centralizer (W : Set G)) := Sec1216Lv.cComp_of_isComponentIn hK
  have hCN : Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hCnorm : ((Subgroup.centralizer (W : Set G)).subgroupOf
      (Subgroup.normalizer (W : Set G))).Normal := by
    refine ⟨fun c hc n => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro w hw
    have hw' : (n : G)⁻¹ * w * n ∈ W := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ n.2) w).1 hw
      simpa using this
    have h1 := hc _ hw'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc w * ((n : G) * c * (n : G)⁻¹)
        = (n : G) * (((n : G)⁻¹ * w * n) * c) * (n : G)⁻¹ := by group
      _ = (n : G) * (c * ((n : G)⁻¹ * w * n)) * (n : G)⁻¹ := by rw [h1]
      _ = (n : G) * c * (n : G)⁻¹ * w := by group
  refine ⟨ne_bot_of_mem_cComp hKc, perfect_of_mem_cComp hKc,
    A3.subnormal_trans (subnormal_of_mem_cComp hKc) (A3.subnormal_of_normal hCN hCnorm), ?_⟩
  intro K' hK'K hK'ne hK'perf hK'sub
  exact hKc.2.2.2 K' hK'K hK'ne hK'perf
    (A3.subnormal_of_le_of_le hK'sub (hK'K.le.trans (le_of_mem_cComp hKc)) hCN)

omit [Finite G] in
theorem pCoreOf_normalizer_ne_bot {W : Subgroup G} (hW : IsPGroup 2 W) (hW1 : W ≠ ⊥) :
    pCoreOf 2 (Subgroup.normalizer (W : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  apply hW1
  have hle : W ≤ pCoreOf 2 (Subgroup.normalizer (W : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hW
  rw [h] at hle
  exact le_bot_iff.1 hle

theorem false_of_three_le {W K X : Subgroup G} (hKW : K ≤ Subgroup.centralizer (W : Set G))
    (hXN : X ≤ Subgroup.normalizer (W : Set G)) (hX3 : Nat.card X = 3)
    (hXW : X ⊓ Subgroup.centralizer (W : Set G) = ⊥)
    (hK : K = oPrimeResidualOf 3 (Subgroup.normalizer (W : Set G)) ∨
      K = thetaOf (Subgroup.normalizer (W : Set G))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 (by rw [hX3])
  have hx3 : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hxK : (x : G) ∈ K := by
    rcases hK with h | h
    · rw [h]
      exact Subgroup.subset_closure ⟨hXN x.2, 1, by rw [hx3, pow_one]⟩
    · rw [h]
      exact Subgroup.subset_closure ⟨hXN x.2, hx3⟩
  have h1 : (x : G) ∈ X ⊓ Subgroup.centralizer (W : Set G) := ⟨x.2, hKW hxK⟩
  rw [hXW, Subgroup.mem_bot] at h1
  rw [h1, orderOf_one] at hx3
  norm_num at hx3

open CFSG.Quasithin.Vol2.Ch11.SecA (quotPCore_subgroupOf_equiv pRank_subgroupOf_eq
  map_oPrimeResidualOf_top)

theorem false_of_exclusion (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {W K X : Subgroup G} (hSQ : SQTKGroup ↥(Subgroup.normalizer (W : Set G)))
    (hKc : K ∈ cComp (Subgroup.normalizer (W : Set G))) (hKW : K ≤ Subgroup.centralizer (W : Set G))
    (hKq : CFSG.IsQuasisimple ↥K) (hKs : IsSimpleGroup ↥K) {S : Type} [Group S] [Finite S]
    (e₁ : ↥K ≃* S) (hS : A318Exclusion S)
    (hXN : X ≤ Subgroup.normalizer (W : Set G)) (hX3 : Nat.card X = 3)
    (hXW : X ⊓ Subgroup.centralizer (W : Set G) = ⊥) : False := by
  have h3 : 3 ∣ Nat.card ↥K := by
    rw [Nat.card_congr e₁.toEquiv]
    exact hS.three_dvd_card
  obtain ⟨e₀⟩ := quotPCore_equiv_of_simple hKs h3
  have hQ : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hKq
  exact false_of_three_le hKW hXN hX3 hXW
    (Or.inl (eq_oPrimeResidualOf_three_of_exclusion hF318 h36 h38 hSQ hKc hQ (e₀.trans e₁) hS))

omit [Finite G] in
theorem orderOf_ne_three_of_mem_pPrimeCore {H : Type} [Group H] [Finite H] {h : H}
    (hh : h ∈ CFSG.pPrimeCore 3 H) : orderOf h ≠ 3 := by
  intro h3
  have hd : orderOf (⟨h, hh⟩ : ↥(CFSG.pPrimeCore 3 H)) ∣ Nat.card ↥(CFSG.pPrimeCore 3 H) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, h3] at hd
  have := (CFSG.pPrimeCore_coprime_card (p := 3) (G := H))
  exact absurd (Nat.Coprime.eq_one_of_dvd this hd) (by norm_num)

theorem nonempty_starImage_equiv {H K : Subgroup G} (hKH : K ≤ H) (hKq : CFSG.IsQuasisimple ↥K)
    (hZ3 : Nat.card (Subgroup.center ↥K) = 3) :
    Nonempty (↥(starImage 3 (K.subgroupOf H)) ≃* ↥K) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e : ↥(K.subgroupOf H) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH with he
  set f : ↥H →* PStar 3 ↥H := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) with hf
  set g : ↥K →* PStar 3 ↥H := (f.comp (K.subgroupOf H).subtype).comp e.symm.toMonoidHom with hg
  have hker3 : ∀ k ∈ g.ker, orderOf k ≠ 3 := by
    intro k hk h3
    have h1 : ((e.symm k : ↥(K.subgroupOf H)) : ↥H) ∈ CFSG.pPrimeCore 3 ↥H := by
      have := MonoidHom.mem_ker.1 hk
      rw [hg] at this
      exact (QuotientGroup.eq_one_iff _).1 this
    apply orderOf_ne_three_of_mem_pPrimeCore h1
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, h3]
  have hz : ∃ c ∈ Subgroup.center ↥K, orderOf c = 3 := by
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥K)) 3 (by rw [hZ3])
    exact ⟨c, c.2, by rw [Subgroup.orderOf_coe, hc]⟩
  have hinj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq (MonoidHom.normal_ker g) with h | h
    · exfalso
      obtain ⟨c, -, hc⟩ := hz
      exact hker3 c (h ▸ Subgroup.mem_top c) hc
    · refine eq_bot_iff.2 fun k hk => ?_
      by_contra hk1
      have hd : orderOf k ∣ 3 := hZ3 ▸ Subgroup.orderOf_dvd_natCard _ (h hk)
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
      · exact hk1 (orderOf_eq_one_iff.1 h1)
      · exact hker3 k hk h3
  have hrange : g.range = starImage 3 (K.subgroupOf H) := by
    rw [hg, MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.symm.surjective, Subgroup.map_top,
      MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm⟩

theorem false_of_hat (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {W K X : Subgroup G} (hSQ : SQTKGroup ↥(Subgroup.normalizer (W : Set G)))
    (hKc : K ∈ cComp (Subgroup.normalizer (W : Set G))) (hKW : K ≤ Subgroup.centralizer (W : Set G))
    (hKq : CFSG.IsQuasisimple ↥K) (hZ3 : Nat.card (Subgroup.center ↥K) = 3)
    (hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K))
    (hnPSL : ∀ s q, ¬ IsPSLEps3q s q ↥K) (hnSL : ∀ s q, ¬ IsSLEps3 s q ↥K)
    (hXN : X ≤ Subgroup.normalizer (W : Set G)) (hX3 : Nat.card X = 3)
    (hXW : X ⊓ Subgroup.centralizer (W : Set G) = ⊥) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (W : Set G) with hHdef
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hSQQ := SQTKHyp.of_sqtkGroup ↥H hSQ
  have hLc := subgroupOf_mem_cComp hKc
  have hO2 : CFSG.pCore 2 ↥K = ⊥ := by
    have hP := CFSG.pCore_isPGroup (p := 2) (G := ↥K)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
    have h3K : 3 ∣ Nat.card ↥K := hZ3 ▸ Subgroup.card_subgroup_dvd_card _
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq (CFSG.pCore_normal (p := 2)) with h | h
    · exfalso
      rw [h, Subgroup.card_top] at hn
      rw [hn] at h3K
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3K)
      omega
    · have hd : Nat.card (CFSG.pCore 2 ↥K) ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le h
      rw [hn] at hd
      have hn0 : n = 0 := by
        by_contra hne
        have h2 : 2 ∣ 3 := (dvd_pow_self 2 hne).trans hd
        norm_num at h2
      rw [hn0, pow_zero] at hn
      exact Subgroup.card_eq_one.1 hn
  have eK : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot
  have hQK : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hKq
  obtain ⟨e₀⟩ := quotPCore_subgroupOf_equiv (L := K) hKH
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hQK
  have hr' : 1 < CFSG.Open.pRank 3 (K.subgroupOf H) := by
    rw [pRank_subgroupOf_eq hKH Nat.prime_three (by norm_num),
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eK]
    omega
  have hconc := a318 hF318 hSQ (h36 _ hSQQ) (h38 _ hSQQ) hLc hQ' Nat.prime_three (by norm_num) hr'
  obtain ⟨eS⟩ := nonempty_starImage_equiv hKH hKq hZ3
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, -, h3 | h3⟩
  · have hK : K = oPrimeResidualOf 3 H := by
      rw [← map_oPrimeResidualOf_top, ← h1, Subgroup.map_subgroupOf_eq_of_le hKH]
    exact false_of_three_le hKW hXN hX3 hXW (Or.inl hK)
  · obtain ⟨s, q, -, ⟨p, f, hp, hf, hq, hpsl⟩, -⟩ := h2
    exact hnPSL s q ⟨p, f, hp, hf, hq, IsPSLEps3.of_mulEquiv eS hpsl⟩
  · have hK : K = thetaOf H := by
      rw [← R3c2.map_thetaOf_top, ← h3, Subgroup.map_subgroupOf_eq_of_le hKH]
    exact false_of_three_le hKW hXN hX3 hXW (Or.inr hK)
  · obtain ⟨s, q, x, hsl, -⟩ := h3
    exact hnSL s q (IsSLEps3.of_mulEquiv eS hsl)

omit [Finite G] in
theorem isSimpleGroup_of_center_eq_bot {K : Subgroup G} (hKq : CFSG.IsQuasisimple ↥K)
    (hZ : Subgroup.center ↥K = ⊥) : IsSimpleGroup ↥K := by
  have := hKq.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem Facts.comp_type_core
    (hF : Facts G T L V U z) (hinv : InvolFact1248) (h68 : E6.E68Stmt)
    (hlist : Lemma115_3_List) (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hKF : KnownFacts15122Types) (hKG1 : L32ListFact1248) (hKG2 : L33ExclusionFact)
    (hKG3 : HatA67Fact1248) {W : Subgroup G} (hW : W = U ∨ (W ≤ U ∧ W.relIndex U = 2))
    {X : Subgroup G} (hXN : X ≤ Subgroup.normalizer (W : Set G)) (hX3 : Nat.card X = 3)
    (hXW : X ⊓ Subgroup.centralizer (W : Set G) = ⊥) {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer (W : Set G))) :
    IsSimpleGroup ↥K ∧ ∃ p : ℕ, Ch1.IsFermatOrMersennePrime p ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 2 p 1 := by
  classical
  have hyp := hF.setting.cx.hyp
  have := hyp.simple
  have hΓ := hF.mem_gamma hinv hW
  have hV : CFSG.Open.IsElemAbelian 2 V := hF.cx.isElemAbelian
  have hV2 : IsPGroup 2 V := hyp.sylow.1.to_le hF.cx.le_T
  have hWV : W ≤ V := hΓ.1
  obtain ⟨-, hcase⟩ := h68 G T (Subgroup.normalizer (L : Set G)) V W K hV hF.e61 hΓ hK
  have hKMV : K ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.centralizer (V : Set G) := by
    intro k hk
    have : k ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (W : Set G) :=
      ⟨hk.2, hK.1 hk.1⟩
    rw [hF.inf_centralizer_eq hinv hW] at this
    exact this.2
  have hautI : Nat.card (autI hV (K ⊓ Subgroup.normalizer (L : Set G))) = 1 := by
    have h0 : autOn (K ⊓ Subgroup.normalizer (L : Set G)) V = ⊥ :=
      C1Pack5.autOn_eq_bot_of_le_centralizer hKMV
    have h1 : Nat.card (autI hV (K ⊓ Subgroup.normalizer (L : Set G))) =
        Nat.card (autOn (K ⊓ Subgroup.normalizer (L : Set G)) V) := rfl
    rw [h1, h0, Subgroup.card_bot]
  have hmW : E3.mQuot V W ≤ 2 := by
    have h1 := E3.relIndex_eq_two_pow hV2 W
    have h2 : W.relIndex V ≤ 4 := by
      rcases hW with rfl | ⟨h, h2⟩
      · rw [hF.setting.hyper]; norm_num
      · rw [← Subgroup.relIndex_mul_relIndex W U V h hF.setting.le, h2, hF.setting.hyper]
    rw [h1] at h2
    by_contra hlt
    push Not at hlt
    have : 2 ^ 3 ≤ 2 ^ E3.mQuot V W := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  have hSQ : SQTKGroup ↥(Subgroup.normalizer (W : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian
      (pCoreOf_normalizer_ne_bot (hV2.to_le hWV) hΓ.2.1)
  have hKc := mem_cComp_normalizer_of_isComponentIn hK
  have hKq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hKW : K ≤ Subgroup.centralizer (W : Set G) := hK.1
  have h115 := hF.lemma115Hyp hinv hW
  have hcases := (Lemma115_3_List.component_cases hlist hyp.simple hyp.nonabelian
    (qtkeCore_of_cat hyp.nonabelian hyp.qtke) h115 hK).2.2.2
  have hexcl : ∀ {S : Type} [Group S] [Finite S], (↥K ≃* S) → A318Exclusion S → False :=
    fun e hS => by
      have := hS.simple
      exact false_of_exclusion hF318 h36 h38 hSQ hKc hKW hKq e.isSimpleGroup e hS hXN hX3 hXW
  rcases hcase with ⟨n, hmod, hZ, -, -, hcard, -, -, -⟩ | ⟨n, hn1, hmod, hmq, -, hab⟩ |
      ⟨hpsl4, -⟩ | ⟨hmod4, -⟩ | ⟨hmod5, -⟩
  ·
    rw [hautI] at hcard
    have hn : n = 1 := by
      have h2 : 2 ^ n = 2 := by omega
      exact Nat.pow_right_injective (le_refl 2) (show 2 ^ n = 2 ^ 1 by rw [h2, pow_one])
    subst hn
    have hpsl : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ Subgroup.center ↥K)
        .PSL 3 2 1 := by
      rcases hmod with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · omega
      · omega
      · exact h
      · omega
    have hZ1 := hKG1 G K z hKq hpsl hZ hcases
    have hs := isSimpleGroup_of_center_eq_bot hKq hZ1
    have eK : ↥K ≃* (↥K ⧸ Subgroup.center ↥K) :=
      ((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot).symm
    have h32 : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 3 2 1 :=
      IsPSL.of_mulEquiv eK.symm hpsl
    refine ⟨hs, 7, ⟨by norm_num, Or.inr ⟨3, by norm_num, by norm_num⟩⟩,
      Vol2Native.statedClassicalModel_psl_two_seven_of_three_two h32⟩
  ·
    have hn : n = 1 := by
      rcases hab with ⟨-, ⟨h2n, -⟩ | ⟨h1, -⟩⟩ | ⟨-, -, -, -, hcyc⟩
      · omega
      · exact h1
      · by_contra hne
        have := (hcyc (by omega)).2
        rw [hautI] at this
        have h2 : 2 ^ n = 2 := by omega
        exact hne (Nat.pow_right_injective (le_refl 2) (show 2 ^ n = 2 ^ 1 by rw [h2, pow_one]))
    subst hn
    rcases hmod with ⟨h, -⟩ | ⟨-, he⟩
    · omega
    · obtain ⟨e⟩ := he
      exact (hexcl e hKF.alt6).elim
  ·
    exact (hexcl (MulEquiv.refl ↥K) (hKF.l42 ↥K hpsl4)).elim
  ·
    rcases hmod4 with he | ⟨hZ3, h6⟩ | ⟨hZ3, h7⟩
    · obtain ⟨e⟩ := he
      exact (hexcl e hKF.alt7).elim
    · obtain ⟨hr, hn⟩ := hKG3 ↥K hKq hZ3 (Or.inl h6)
      exact (false_of_hat hF318 h36 h38 hSQ hKc hKW hKq hZ3 hr (fun s q => (hn s q).1)
        (fun s q => (hn s q).2) hXN hX3 hXW).elim
    · obtain ⟨hr, hn⟩ := hKG3 ↥K hKq hZ3 (Or.inr h7)
      exact (false_of_hat hF318 h36 h38 hSQ hKc hKW hKq hZ3 hr (fun s q => (hn s q).1)
        (fun s q => (hn s q).2) hXN hX3 hXW).elim
  ·
    rcases hmod5 with ⟨p, hp, hpsl⟩ | h33 | he
    · have hLie : LieModel ↥K .PSL 2 p 1 := Or.inl ⟨by decide, hpsl⟩
      exact ⟨CFSG.Timmesfeld.isSimpleGroup_of_lieModel hLie, p, hp, hpsl⟩
    · exact (hexcl (MulEquiv.refl ↥K) (hKG2 ↥K h33)).elim
    · exact (hexcl (MulEquiv.refl ↥K) (hKF.m11 ↥K he)).elim

theorem Facts.comp_basic (hF : Facts G T L V U z) (hinv : InvolFact1248) {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer (U : Set G))) :
    ¬ K ≤ Subgroup.normalizer (L : Set G) ∧ V ⊓ Subgroup.centralizer (K : Set G) = U := by
  have h115 := hF.lemma115Hyp hinv (Or.inl rfl)
  have hKM : ¬ K ≤ Subgroup.normalizer (L : Set G) := (h115.component_action hK).2.2.1
  refine ⟨hKM, ?_⟩
  set W := V ⊓ Subgroup.centralizer (K : Set G) with hW
  have hUW : U ≤ W := fun u hu => ⟨hF.setting.le hu, Subgroup.mem_centralizer_iff.2 fun k hk =>
    (Subgroup.mem_centralizer_iff.1 (hK.1 hk) u hu).symm⟩
  have hWV : W ≤ V := inf_le_left
  have hWne : W ≠ V := by
    intro h
    apply hKM
    rw [← hF.normalizer_V_eq]
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.le_centralizer_iff, ← h]
    exact inf_le_right
  have hmul := Subgroup.relIndex_mul_relIndex U W V hUW hWV
  rw [hF.setting.hyper] at hmul
  have hWV2 : W.relIndex V ≠ 1 := fun h1 => hWne (le_antisymm hWV (Subgroup.relIndex_eq_one.1 h1))
  have hUW1 : U.relIndex W = 1 := by
    have h0 : W.relIndex V ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases Nat.lt_or_ge (W.relIndex V) 2 with h | h
    · omega
    · nlinarith [Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite : U.relIndex W ≠ 0)]
  exact (le_antisymm (Subgroup.relIndex_eq_one.1 hUW1) hUW)

theorem exists_orderOf_three_mem_centralizer {C Y : Subgroup G}
    (hYC : Y ≤ Subgroup.normalizer (C : Set G)) (hY : IsPGroup 3 Y) (h3 : 3 ∣ Nat.card C) :
    ∃ w ∈ C ⊓ Subgroup.centralizer (Y : Set G), orderOf w = 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : ↥Y →* MulAut ↥C := C.normalizerMonoidHom.comp (Subgroup.inclusion hYC)
  let _ : MulAction ↥Y ↥C := MulAction.compHom ↥C φ
  have hmod := IsPGroup.card_modEq_card_fixedPoints (α := ↥C) hY
  have hφ : ∀ (y : ↥Y) (c : ↥C), ((y • c : ↥C) : G) = y * c * (y : G)⁻¹ := fun _ _ => rfl
  have hF : Nat.card (MulAction.fixedPoints ↥Y ↥C) =
      Nat.card ↥(C ⊓ Subgroup.centralizer (Y : Set G)) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨(c.1 : G), c.1.2, Subgroup.mem_centralizer_iff.2 fun y hy => by
          have h1 := congrArg Subtype.val (c.2 ⟨y, hy⟩)
          rw [hφ] at h1
          calc y * (c.1 : G) = y * c.1 * y⁻¹ * y := by group
            _ = c.1 * y := by rw [h1]⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, fun y => by
          apply Subtype.ext
          rw [hφ]
          have h1 := Subgroup.mem_centralizer_iff.1 v.2.2 y y.2
          show (y : G) * v.1 * (y : G)⁻¹ = v.1
          rw [h1]
          group⟩
        left_inv := fun c => by ext; rfl
        right_inv := fun v => by ext; rfl }
  have h3F : 3 ∣ Nat.card ↥(C ⊓ Subgroup.centralizer (Y : Set G)) := by
    rw [← hF]
    exact (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 h3)))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(C ⊓ Subgroup.centralizer (Y : Set G)))
    3 h3F
  exact ⟨w, w.2, by rw [Subgroup.orderOf_coe, hw]⟩

theorem false_of_Y (hev : CFSG.Open.evenRank G ≤ 2) {U Y K : Subgroup G} (hU2 : IsPGroup 2 U)
    (hU1 : U ≠ ⊥) (hYN : Y ≤ Subgroup.normalizer (U : Set G)) (hY27 : Nat.card Y = 27)
    (hY3 : ∀ y ∈ Y, y ^ 3 = 1) (hYU : Y ⊓ Subgroup.centralizer (U : Set G) = ⊥)
    (hKC : K ≤ Subgroup.centralizer (U : Set G)) (hK3 : 3 ∣ Nat.card K) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (U : Set G) with hC
  have hYC : Y ≤ Subgroup.normalizer (C : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have hyU := Subgroup.mem_normalizer_iff.1 (hYN hy)
    constructor
    · intro hc
      rw [hC, Subgroup.mem_centralizer_iff] at hc ⊢
      intro u hu
      have hu' : y⁻¹ * u * y ∈ U := by
        have := (hyU (y⁻¹ * u * y)).2 (by simpa [mul_assoc] using hu)
        exact this
      have h1 := hc _ hu'
      calc u * (y * c * y⁻¹) = y * ((y⁻¹ * u * y) * c) * y⁻¹ := by group
        _ = y * (c * (y⁻¹ * u * y)) * y⁻¹ := by rw [h1]
        _ = y * c * y⁻¹ * u := by group
    · intro hc
      rw [hC, Subgroup.mem_centralizer_iff] at hc ⊢
      intro u hu
      have hu' : y * u * y⁻¹ ∈ U := (hyU u).1 hu
      have h1 := hc _ hu'
      calc u * c = y⁻¹ * ((y * u * y⁻¹) * (y * c * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * c * y⁻¹) * (y * u * y⁻¹)) * y := by rw [h1]
        _ = c * u := by group
  have hY : IsPGroup 3 Y := IsPGroup.of_card (n := 3) (by rw [hY27]; norm_num)
  have h3C : 3 ∣ Nat.card C := hK3.trans (Subgroup.card_dvd_of_le hKC)
  obtain ⟨w, ⟨hwC, hwY⟩, hw3⟩ := exists_orderOf_three_mem_centralizer hYC hY h3C
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Y) 3 (n := 2)
    (by rw [hY27]; norm_num)
  set E : Subgroup G := E₀.map Y.subtype with hE
  have hE9 : Nat.card E = 3 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective Y.subtype_injective, hE₀]
  have hEY : E ≤ Y := Subgroup.map_subtype_le E₀
  have hEab : IsElemAbelian 3 E := by
    exact ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hE9, fun x hx => hY3 x (hEY hx)⟩
  set Q : Subgroup G := Subgroup.zpowers w with hQ
  have hQ3 : Nat.card Q = 3 ^ 1 := by rw [hQ, Nat.card_zpowers, hw3, pow_one]
  have hQab : IsElemAbelian 3 Q := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hw3, pow_orderOf_eq_one,
        one_zpow]
  have hcomm : ∀ x ∈ E, ∀ y ∈ Q, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h1 : x * w = w * x := Subgroup.mem_centralizer_iff.1 hwY x (hEY hx)
    exact ((Commute.zpow_right h1 m)).eq
  have hEQ : E ⊓ Q = ⊥ := by
    refine le_bot_iff.1 ?_
    calc E ⊓ Q ≤ Y ⊓ C := inf_le_inf hEY (Subgroup.zpowers_le.2 hwC)
      _ = ⊥ := hYU
  have hEH : E ≤ Subgroup.normalizer (U : Set G) := hEY.trans hYN
  have hQH : Q ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.zpowers_le.2 hwC).trans (Subgroup.centralizer_le_normalizer _)
  have h1 := le_pRank_of_commute_of_inf_eq_bot' Nat.prime_three hEab hQab hcomm hEQ hE9 hQ3 hEH hQH
  have h2 := A1b.pRank_le_evenRank Nat.prime_three (by norm_num)
    (⟨U, hU1, hU2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (U : Set G)))
  omega

end S1248

open S1248

theorem comp1248Type_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (hpre : Pre1242) (hinv : InvolFact1248) (hX : HypX1248) (h68 : E6.E68Stmt)
    (hlist : Lemma115_3_List) (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hKF : KnownFacts15122Types) (hKG1 : L32ListFact1248) (hKG2 : L33ExclusionFact)
    (hKG3 : HatA67Fact1248) (hKG4 : L2pThreeFact1248) : Comp1248Type := by
  intro G _ _ T L V U hS K hK
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hF⟩ := S1248.exists_facts h331 h1222 h323 h3228 hpre hS
  have hyp := hS.cx.hyp
  have hev : CFSG.Open.evenRank G ≤ 2 := hyp.qtke.2.2
  have hΓ := hF.mem_gamma hinv (Or.inl rfl)
  have hU2 : IsPGroup 2 U := (hyp.sylow.1.to_le hF.cx.le_T).to_le hS.le
  obtain ⟨X, hXN, hX3, hXW⟩ : ∃ X : Subgroup G, X ≤ Subgroup.normalizer (U : Set G) ∧
      Nat.card X = 3 ∧ X ⊓ Subgroup.centralizer (U : Set G) = ⊥ := by
    rcases hX G T L V U hS with ⟨X, hXle, hX3, hXU, -⟩ | ⟨Y, hYle, hY27, -, hYU⟩
    · refine ⟨X, hXle.trans inf_le_right, hX3, ?_⟩
      have hd : Nat.card ↥(X ⊓ Subgroup.centralizer (U : Set G)) ∣ 3 :=
        hX3 ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
      · exact Subgroup.card_eq_one.1 h1
      · exfalso
        apply hXU
        have heq : X ⊓ Subgroup.centralizer (U : Set G) = X :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hX3])
        rw [← heq]
        exact inf_le_right
    · obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 (by rw [hY27]; norm_num)
      refine ⟨Subgroup.zpowers (y : G), (Subgroup.zpowers_le.2 y.2).trans
        (hYle.trans inf_le_right), by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy], ?_⟩
      refine le_bot_iff.1 ?_
      calc Subgroup.zpowers (y : G) ⊓ Subgroup.centralizer (U : Set G) ≤
          Y ⊓ Subgroup.centralizer (U : Set G) := inf_le_inf_right _ (Subgroup.zpowers_le.2 y.2)
        _ = ⊥ := hYU
  obtain ⟨hKs, hKp⟩ := hF.comp_type_core hinv h68 hlist hF318 h36 h38 hKF hKG1 hKG2 hKG3
    (Or.inl rfl) hXN hX3 hXW hK
  obtain ⟨hKM, hCV⟩ := hF.comp_basic hinv hK
  refine ⟨?_, hKs, hKp, hKM, hCV⟩
  rintro ⟨Y, hYle, hY27, hY3, hYU⟩
  obtain ⟨p, hp, hpsl⟩ := hKp
  exact false_of_Y hev hU2 hΓ.2.1 (hYle.trans inf_le_right) hY27 hY3 hYU hK.1
    (hKG4 ↥K p hp hpsl).1

end CFSG.Quasithin.H13
