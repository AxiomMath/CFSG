module

public import CFSG.Quasithin.Vol2.Ch11SecOE6G
public import CFSG.Quasithin.Vol2.Ch11SecQ9bXi
public import CFSG.Quasithin.Vol2.Ch1Sec3Thm137
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.Quasithin.Vol2.Ch12Sec6Final
public import CFSG.Quasithin.Vol2.Ch12Sec6L23a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace S126L30

theorem isCyclic_of_mulAut_of_not_sq_dvd {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (hout : Nat.Coprime p (Nat.card (Outer X)))
    (hsq : ¬ p ^ 2 ∣ Nat.card (X ⧸ Subgroup.center X)) {U : Subgroup (MulAut X)}
    (hU : IsPGroup p U) : IsCyclic ↥U := by
  have hUI : U ≤ inner X := by
    intro u hu
    obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
    have h1 : orderOf (QuotientGroup.mk u : Outer X) ∣ Nat.card (Outer X) :=
      orderOf_dvd_natCard _
    have h2 : orderOf (QuotientGroup.mk u : Outer X) ∣ p ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow, show u ^ p ^ k = 1 from congrArg Subtype.val hk,
        QuotientGroup.mk_one]
    have h3 : orderOf (QuotientGroup.mk u : Outer X) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hout) h2 h1
    exact (QuotientGroup.eq_one_iff u).mp (orderOf_eq_one_iff.mp h3)
  have hdvd : Nat.card U ∣ Nat.card (X ⧸ Subgroup.center X) := by
    rw [← Nat.card_congr (Vol2.Ch11.OE6.innerEquiv X).toEquiv]
    exact Subgroup.card_dvd_of_le hUI
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  have hk1 : k ≤ 1 := by
    by_contra h
    exact hsq ((pow_dvd_pow p (by omega)).trans (hk ▸ hdvd))
  interval_cases k
  · rw [pow_zero] at hk
    have : Subsingleton ↥U := (Nat.card_eq_one_iff_unique.mp hk).1
    infer_instance
  · rw [pow_one] at hk
    exact isCyclic_of_prime_card hk

theorem not_sq_dvd_20160 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ^ 2 ∣ 20160 := by
  intro hp2
  have hpd : p ∣ 2 ^ 6 * (3 ^ 2 * (5 * 7)) :=
    (by norm_num : (20160 : ℕ) = 2 ^ 6 * (3 ^ 2 * (5 * 7))) ▸
      (dvd_pow_self p two_ne_zero).trans hp2
  have hp57 : p = 5 ∨ p = 7 := by
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h1 | h1
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
      omega
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h2)
      omega
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3)
  rcases hp57 with rfl | rfl <;> norm_num at hp2

theorem isCyclic_mulAut_of_alt8 {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    (φ : Q →* ↥(alternatingGroup (Fin 8))) (hφ : Function.Surjective φ) {p : ℕ}
    [hp : Fact p.Prime] (hp5 : 5 ≤ p) {U : Subgroup (MulAut Q)} (hU : IsPGroup p U) :
    IsCyclic ↥U := by
  have : Group.IsPerfect Q := hQ.1
  have hker : φ.ker = Subgroup.center Q := by
    apply le_antisymm
    · rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ φ.normal_ker with h | h
      · exfalso
        obtain ⟨q, hq⟩ := hφ ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
          rw [Equiv.Perm.mem_alternatingGroup]
          decide⟩
        have h1 : q ∈ φ.ker := h ▸ Subgroup.mem_top q
        rw [MonoidHom.mem_ker, hq] at h1
        have h2 := congrArg (fun s : ↥(alternatingGroup (Fin 8)) => (s : Equiv.Perm (Fin 8)) 0) h1
        exact absurd h2 (by decide)
      · exact h
    · intro z hz
      rw [MonoidHom.mem_ker]
      have hc : φ z ∈ Subgroup.center ↥(alternatingGroup (Fin 8)) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨x, rfl⟩ := hφ y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
      rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num), Subgroup.mem_bot] at hc
      exact hc
  let e : Q ⧸ Subgroup.center Q ≃* ↥(alternatingGroup (Fin 8)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have hout : Nat.card (Outer Q) ∣ 2 :=
    (Subgroup.card_dvd_of_injective _
      (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_comp_injective Q e)).trans
      (SteinbergCB.isSolvable_outer_alternatingGroup (n := 8) (Or.inr (by norm_num))).2
  have hcop : Nat.Coprime p (Nat.card (Outer Q)) :=
    Nat.Coprime.coprime_dvd_right hout
      ((Nat.coprime_primes hp.out Nat.prime_two).2 (by omega))
  have hcard : Nat.card (Q ⧸ Subgroup.center Q) = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  exact isCyclic_of_mulAut_of_not_sq_dvd hcop (hcard ▸ not_sq_dvd_20160 hp.out hp5) hU

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_isCyclic {T H K Y : Subgroup G} (S : Vol2.Ch11.OE6.Setting G T H K Y)
    (hcyc : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ U : Subgroup (MulAut (↥K ⧸ CFSG.pCore 2 ↥K)),
      IsPGroup p U → IsCyclic ↥U) :
    K ≤ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨p, hp, hp5, hpY, P, hSyl⟩ := S.exists_prime
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hPp, hexp, hc2, -, hNP, hirr⟩ := S.bar_data hp2 hpY hSyl
  have := S.normal_bar
  obtain ⟨e⟩ := Vol2.Ch11.SecA.C11P9B.modO2Image_equiv S.KH S.normal_subgroupOf
  have hle := Vol2.Ch11.OE6.le_centralizer_of_isCyclic hPp hexp hc2 hNP hirr
    (Vol2.Ch11.OE6.isCyclic_of_mulEquiv e.symm (hcyc p hp hp5)
      (hPp.map (MulAut.conjNormal : (↥H ⧸ CFSG.pCore 2 ↥H) →* MulAut ↥(modO2Image H K))))
  exact S.le_normalizer_of_le_centralizer hp2 hpY hSyl hle

theorem exists_prime_fitting (h36 : Vol2Native.A36CoreForSQTKCat) (hloc : LocalSQTK G)
    {H K : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hK : K ∈ cComp H)
    (hnq : ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ Nat.card (CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  obtain ⟨e⟩ := modO2_mulEquiv hK
  have hcore := Vol2Native.lemma_1_2_1_four_core hloc h36 hH hK
  have hFe : Nat.card (CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K)) =
      Nat.card (CFSG.fittingSubgroup ↥(modO2Image H K)) := by
    rw [← CFSG.Walter.map_fittingSubgroup_of_mulEquiv' e,
      Subgroup.card_map_of_injective e.injective]
  rw [hFe]
  rcases hcore.1 with hc | ⟨p₀, hp₀, hp₀3, -, hel, -⟩ | ⟨-, -, h5, h4⟩
  · exact absurd (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hc.1) hnq
  · have hp₀4 : p₀ ≠ 4 := by
      rintro rfl
      norm_num at hp₀
    refine ⟨p₀, hp₀, by omega, ?_⟩
    have : Fact p₀.Prime := ⟨hp₀⟩
    obtain ⟨eF⟩ := hel
    have hcard : Nat.card (CFSG.fittingSubgroup ↥(modO2Image H K)) = p₀ ^ 2 := by
      rw [Nat.card_congr eF.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [hcard]
    exact dvd_pow_self p₀ two_ne_zero
  · have hne : Nat.card (CFSG.fittingSubgroup ↥(modO2Image H K)) ≠ 1 := by
      intro h1
      have hbot : CFSG.fittingSubgroup ↥(modO2Image H K) = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      obtain ⟨e5⟩ := h5
      exact hnq (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
        (A313.IsSL2.isQuasisimple Nat.prime_five le_rfl
          ⟨(QuotientGroup.quotientBot.symm.trans
            (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e5⟩))
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    refine ⟨p, hp, ?_, hpd⟩
    have hp4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    have := hp.two_le
    rcases (h4 p hp hpd).1 with h | h | h <;> omega

variable {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
theorem mem_cComp_normalizer {T L : Subgroup G} (hL : quasithinIsLocal T L) :
    L ∈ cComp (Subgroup.normalizer (L : Set G)) := by
  obtain ⟨-, hc, -, -⟩ := hL
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  refine ⟨hc.1, hc.2.1, A3.subnormal_of_normal hLN
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hLN).2 le_rfl), ?_⟩
  intro J hJL hJ1 hJp hJN
  exact hc.2.2.2 J hJL hJ1 hJp
    (A3.subnormal_trans (A3.subnormal_of_le_of_le hJN hJL.le hLN) hc.2.2.1)

omit [IsMulCommutative ↥V] in
theorem isCyclic_mulAut_L (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ U : Subgroup (MulAut (↥L ⧸ CFSG.pCore 2 ↥L)),
      IsPGroup p U → IsCyclic ↥U := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_reduced hyp.normalizes hVT hred
  obtain ⟨φ, hφ, hker⟩ := hH.alt8
  have hNK : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [hker, Subgroup.mem_subgroupOf]
    apply hO2
    exact ⟨x, hx, rfl⟩
  intro p hp hp5 U hU
  have : Fact p.Prime := ⟨hp⟩
  exact isCyclic_mulAut_of_alt8 hyp.quasisimple (QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hNK)
    (QuotientGroup.lift_surjective_of_surjective _ φ hφ hNK) hp5 hU

theorem isQuasisimple_of_mem_cComp (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h1229 : Lemma12_6_29) (h36 : Vol2Native.A36CoreForSQTKCat) (h133 : Vol2.Ch11.Tmp1_3_3)
    (F : Frame126 T L V) (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {H₁ K : Subgroup G} (hH₁ : InHz T L F.V1 H₁) (hK : K ∈ cComp H₁)
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G)) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
  by_contra hnq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  have : IsSimpleGroup G := hyp.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  obtain ⟨⟨hLTH, hO2⟩, -, -⟩ := hH₁
  have hTH : T ≤ H₁ := le_sup_right.trans hLTH
  have hTs : IsSylowTwoOf T H₁ := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH
  obtain ⟨p, hp, hp5, hpF⟩ := exists_prime_fitting h36 hloc hO2 hK hnq
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hXi : IsXi T (Vol2.Ch11.xiP K p) :=
    h133 G T K p hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
      (isLocal_of_mem_cComp_of_sylow hTs hO2 hK) hnq hp hp2 hpF
  have hX5 : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card (Vol2.Ch11.xiP K p) → 5 ≤ q :=
    fun q hq hq2 hqX => by
      rw [Vol2.Ch11.OE6.eq_of_dvd_card_xiP K hp hq hq2 hqX]
      exact hp5
  have hXs : Group.IsSolvable ↥(Vol2.Ch11.xiP K p) := by
    apply CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    have hsub : (Nat.card ↥(Vol2.Ch11.xiP K p)).primeFactors ⊆ {2, p} := by
      intro q hq
      obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.1 hq
      by_cases hq2 : q = 2
      · simp [hq2]
      · simp [Vol2.Ch11.OE6.eq_of_dvd_card_xiP K hp hqp hq2 hqd]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hTs' : Group.IsSolvable ↥T := by
    have := hyp.sylow.1.isNilpotent
    infer_instance
  have hXTs : Group.IsSolvable ↥(Vol2.Ch11.xiP K p ⊔ T) :=
    CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer hXi.2.1 hXs hTs'
  have hXM : Vol2.Ch11.xiP K p ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    h1229 G T L V F hH hZ _ ⟨le_sup_right, hXi.2.2.1⟩ (Or.inr hXTs)
  obtain ⟨⟨hMmax, -, huniq⟩, -, -⟩ := S126L23a.stmt331 h331 hH
  have S : Vol2.Ch11.OE6.Setting G T (Subgroup.normalizer (L : Set G)) L (Vol2.Ch11.xiP K p) :=
    ⟨hloc, hyp.sylow, CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal hMmax.1, hXM,
      mem_cComp_normalizer hyp.maximal.1, le_rfl, hXi, hX5⟩
  have hLX := le_normalizer_of_isCyclic S (isCyclic_mulAut_L h1222 hH)
  have hO2X : pCoreOf 2 (Vol2.Ch11.xiP K p) ≠ ⊥ :=
    Thm137.pCoreOf_ne_bot_of_isXi hyp.qtke.2.1 hyp.sylow hXi
  have hNW : Subgroup.normalizer (Vol2.Ch11.xiP K p : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (Vol2.Ch11.xiP K p) : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 _
  obtain ⟨M', hM', hle⟩ := CFSG.Quasithin.exists_maxTwoLocal_ge
    (⟨pCoreOf 2 (Vol2.Ch11.xiP K p), hO2X, pCoreOf_isPGroup 2 _, rfl⟩ : IsTwoLocal _)
  have hLT : L ⊔ T ≤ M' := (sup_le hLX hXi.2.1).trans (hNW.trans hle)
  have hKX : K ≤ Subgroup.normalizer (Vol2.Ch11.xiP K p : Set G) :=
    Subgroup.le_normalizer.trans (Vol2.Ch11.SecA.C11P9B.normalizer_le_normalizer_xiP p)
  exact hKM (hKX.trans (hNW.trans (hle.trans (huniq M' hM' hLT).le)))

end S126L30

end CFSG.Quasithin.H13
