module

public import CFSG.Quasithin.Background.C1PackClassG
public import CFSG.Quasithin.Background.C1PackSolvP
public import CFSG.Quasithin.Background.C1PackA4
public import CFSG.Quasithin.Background.C1PackC126B
public import CFSG.Quasithin.Background.C1PackSubnormal

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_involution_not_mem_centralizer {S V : Subgroup G}
    (h : ¬ thompsonJ S ≤ Subgroup.centralizer (V : Set G)) :
    ∃ a ∈ thompsonJ S, a ^ 2 = 1 ∧ a ∉ Subgroup.centralizer (V : Set G) := by
  by_contra hcon
  apply h
  refine iSup₂_le fun A hA a ha => ?_
  by_contra hna
  exact hcon ⟨a, le_thompsonJ hA ha, hA.2.1.2 a ha, hna⟩

omit [Finite G] in
theorem isAltType_three_of_isBlock2_of_solvable {P K : Subgroup G} (hK : IsBlock2 P K)
    (hsolv : Group.IsSolvable ↥P) : IsAltType K 3 := by
  have h3 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 := by
    rcases hK.1.2.2.2.1 with hq | h3
    · exfalso
      have hKs : Group.IsSolvable ↥K :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hK.2.1)
      have hQs : Group.IsSolvable (↥K ⧸ CFSG.pCore 2 ↥K) :=
        Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K))
      have : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K) := CFSG.LocalCores.isQuasisimple_nontrivial hq
      have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hq.1
      exact Group.IsPerfect.not_isSolvable (↥K ⧸ CFSG.pCore 2 ↥K) hQs
    · exact h3
  exact isAltType_three_of_card_three hK.1 h3

theorem isSubnormal_twoResidual_lift {U T M P : Subgroup G} (h : MinParabolic U T M)
    (hsolv : Group.IsSolvable ↥U) (hSyl : IsSylowTwoOf (baum T) (twoResidual U ⊔ baum T))
    (hSP : baum T ≤ P) (hPY : P ≤ twoResidual U ⊔ baum T) :
    ((twoResidual P).subgroupOf U).IsSubnormal := by
  have hT := h.isSylow
  have hST : baum T ≤ T := inf_le_left
  have hSU : baum T ≤ U := hST.trans hT.1
  have hKUle : twoResidual U ≤ U := twoResidual_le U
  have hUN : U ≤ Subgroup.normalizer (twoResidual U : Set G) := le_normalizer_twoResidual U
  have hY : twoResidual U ⊔ baum T ≤ U := sup_le hKUle hSU
  have hPU : P ≤ U := hPY.trans hY
  have hKle : twoResidual P ≤ twoResidual U := by
    have hNn : P ≤ Subgroup.normalizer ((P ⊓ twoResidual U : Subgroup G) : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hUN (hPU hg)⟩
    have h2 : ∀ y ∈ P, ∃ k : ℕ, y ^ 2 ^ k ∈ P ⊓ twoResidual U := by
      intro y hy
      obtain ⟨k, hk⟩ := isTwoQuotient_of_sup_eq (hT.2.1.to_le hST) (hY.trans hUN)
        (sup_comm _ _) y (hPY hy)
      exact ⟨k, P.pow_mem hy _, hk⟩
    exact (twoResidual_le_of_isTwoQuotient inf_le_left hNn h2).trans inf_le_right
  have hQ₀S : pCoreOf 2 (twoResidual U) ≤ baum T := by
    have hQY : pCoreOf 2 (twoResidual U) ≤ twoResidual U ⊔ baum T :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left
    have hYN : twoResidual U ⊔ baum T ≤
        Subgroup.normalizer (pCoreOf 2 (twoResidual U) : Set G) :=
      hY.trans (hUN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQY hYN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans (pCoreOf_two_le_of_isSylowTwoOf hSyl)
  have hQ₀N : pCoreOf 2 (twoResidual U) ≤ Subgroup.normalizer (twoResidual P : Set G) :=
    (hQ₀S.trans hSP).trans (le_normalizer_twoResidual P)
  have hsub1 : ((twoResidual P).subgroupOf (pCoreOf 2 (twoResidual U) ⊔ twoResidual P)).IsSubnormal :=
    (Subgroup.normal_subgroupOf_sup_of_le_normalizer hQ₀N).isSubnormal
  obtain ⟨p, hp, hp2, hpow⟩ := h.exists_prime_pow_mem_pCoreOf hsolv
  have : Fact p.Prime := ⟨hp⟩
  have hKUOU : twoResidual U ⊓ pCoreOf 2 U ≤ pCoreOf 2 (twoResidual U) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 U (hKUle hg)⟩)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 U).to_le inf_le_right)
  have hQ₀n : ((pCoreOf 2 (twoResidual U)).subgroupOf (twoResidual U)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).2
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hpq : ∀ g ∈ twoResidual U, ∃ a : ℕ, g ^ p ^ a ∈ pCoreOf 2 (twoResidual U) := by
    intro g hg
    obtain ⟨a, ha⟩ := hpow g hg
    exact ⟨a, hKUOU ⟨(twoResidual U).pow_mem hg _, ha⟩⟩
  have hsub2 : ((pCoreOf 2 (twoResidual U) ⊔ twoResidual P).subgroupOf (twoResidual U)).IsSubnormal :=
    isSubnormal_subgroupOf_of_pGroup_quotient hQ₀n le_sup_left hpq
  have hKUn : ((twoResidual U).subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKUle).2 hUN
  have hAle : pCoreOf 2 (twoResidual U) ⊔ twoResidual P ≤ twoResidual U :=
    sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hKle
  have hstep1 : ((twoResidual P).subgroupOf (twoResidual U)).IsSubnormal :=
    isSubnormal_subgroupOf_trans' le_sup_right hAle hsub1 hsub2
  exact isSubnormal_subgroupOf_trans' hKle hKUle hstep1 hKUn.isSubnormal

theorem c126_case_B {C₁ C₂ H T M : Subgroup G} (h1Z : C₁ ≤ omegaOneCenterOf T) (h2B : C₂ ≤ baum T)
    (h2char : (C₂.subgroupOf (baum T)).Characteristic) (hmin : MinParabolic H T M)
    (hF : CharTwo H) (hJ : thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G)) :
    C₁ ≤ centerOf H ∨ H ≤ Subgroup.normalizer (C₂ : Set G) := by
  have hT : IsSylowTwoOf T H := hmin.isSylow
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  by_cases hHV : H ≤ Subgroup.centralizer (VZ T H : Set G)
  · left
    have hC1V : C₁ ≤ VZ T H := h1Z.trans (le_conjClosure _ H)
    refine le_inf ((h1Z.trans ?_).trans hT.1) ?_
    · exact (Subgroup.closure_le T).mpr fun x hx => hx.1.1
    · intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.mem_centralizer_iff.mp (hHV hh) c (hC1V hc)).symm
  · right
    have hredV : IsTwoReducedIn H (conjClosure (quasithinOmegaOneCenter T) H) := hred
    have htfae := MinParabolic.tfae_thompsonJ hmin hredV hHV
    have h1 : ⁅VZ T H, thompsonJ T⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hJ
    have h3 : baum T = baum (pCoreOf 2 H) := (htfae.out 1 3).1 h1
    have hHN : H ≤ Subgroup.normalizer (baum T : Set G) := by
      rw [h3]
      exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans
        (normalizer_le_normalizer_baum _)
    exact hHN.trans (normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char)

theorem exists_a3Block_of_not_le {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    {X T U M' : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X) (hT : IsSylowTwoOf T X)
    (hsolv : perfectCore X ≤ Subgroup.centralizer (VZ T X : Set G)) (hU : U ∈ uFamHat X T)
    (hM' : (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔
      (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ≤ M')
    (hTM' : T ≤ M') (hUM' : ¬ U ≤ M') :
    ∃ K : Subgroup G, IsChi0Block U K ∧ IsAltType K 3 ∧ ⁅K, thompsonJ T⁆ = K ∧
      U = T ⊔ conjClosure K T ∧ ¬ K ≤ M' := by
  have hUX : U ≤ X := hU.1.1
  have hTU : T < U := hU.1.2.1
  have hTSyl : IsSylowTwoOf T U := C1GN.isSylowTwoOf_of_le hT hTU.le hUX
  have hFU : CharTwo U := C1GN.charTwo_of_le hX hT hTU.le hUX
  have hSQU : IsSQTKTC U := C1GN.IsSQTKTC.mono hUX hSQ
  have hUmin : IsMinParabolicOf U U := ⟨T, hTSyl, ⟨le_rfl, hTU, hU.1.2.2⟩, hU.2⟩
  obtain ⟨M, hM⟩ : ∃ M, IsUniqueMaxOver U T M := maxOver_ncard_eq_one_iff.1 hU.1.2.2
  have hmin : MinParabolic U T M := minParabolic_iff.2 ⟨hUmin, hTSyl, hM⟩
  have hT0 : T ≠ ⊥ := minParabolic_ne_bot hmin
  obtain ⟨-, h1Z, -, -, h2B, h2char, -⟩ := hC.pair T hT.2.1 hT0
  have hPM'_of : ∀ P : Subgroup G, P ≤ U →
      (C₁ T ≤ centerOf P ∨ P ≤ Subgroup.normalizer (C₂ T : Set G)) → P ≤ M' := by
    intro P hPU h
    rcases h with h1 | h2
    · have hPC : P ≤ X ⊓ Subgroup.centralizer (C₁ T : Set G) :=
        le_inf (hPU.trans hUX) fun u hu => Subgroup.mem_centralizer_iff.2 fun c hc =>
          (Subgroup.mem_centralizer_iff.1 (h1 hc).2 u hu).symm
      exact (hPC.trans le_sup_left).trans hM'
    · exact ((le_inf (hPU.trans hUX) h2).trans le_sup_right).trans hM'
  obtain ⟨-, -, hredU⟩ := conjClosure_isTwoReducedIn_of_charTwo hTSyl hFU (le_refl _)
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (VZ T U : Set G)
  · exact absurd (hPM'_of U le_rfl (c126_case_B h1Z h2B h2char hmin hFU hJ)) hUM'
  have hUV : ¬ U ≤ Subgroup.centralizer (VZ T U : Set G) := fun hle =>
    hJ ((B6.thompsonJ_le T).trans (hTSyl.1.trans hle))
  have hperf : perfectCore U ≤ Subgroup.centralizer (VZ T U : Set G) :=
    (perfectCore_mono hUX).trans
      (hsolv.trans (Subgroup.centralizer_le (conjClosure_mono le_rfl hUX)))
  have hsolvU : Group.IsSolvable ↥U := isSolvable_of_perfectCore_le hmin hredU hUV hperf
  obtain ⟨P, hSP, hPY, hPM, hPT, hMinP, hFP, hJP, hSyl⟩ :=
    exists_minimal_parabolic_over_baum hmin hFU hsolvU (pRank_le_two_of_isSQTKTC hSQU) hJ
  have hPU : P ≤ U := hPT ▸ le_sup_left
  have hSQP : IsSQTKTC P := C1GN.IsSQTKTC.mono hPU hSQU
  have hsolvP : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPU)
  have hbb : baum (baum T) = baum T := C1GN.baum_baum T
  have hCls : InClassG P (baum T) := inClassG_of_solvable_minParabolic hMinP hFP hsolvP
    (pRank_le_two_of_isSQTKTC hSQP) hJP hbb
  have hPnotM' : ¬ P ≤ M' := fun hPM'' => hUM' (hPT ▸ sup_le hPM'' hTM')
  rcases hC.dichotomy hT.2.1 hT0 hCls with h1 | h2 | h3
  · exact absurd (hPM'_of P hPU (Or.inl h1)) hPnotM'
  · exact absurd (hPM'_of P hPU (Or.inr h2)) hPnotM'
  have hKblock : IsBlock2 P (twoResidual P) := h3.1
  have hKalt : IsAltType (twoResidual P) 3 := isAltType_three_of_isBlock2_of_solvable hKblock hsolvP
  have hKP : twoResidual P ≤ P := twoResidual_le P
  have hKU : twoResidual P ≤ U := hKP.trans hPU
  have hKblockU : IsBlock2 U (twoResidual P) :=
    ⟨hKblock.1, hKU, isSubnormal_twoResidual_lift hmin hsolvU hSyl hSP hPY⟩
  have hJT : thompsonJ T ≤ P := (B6.thompsonJ_le_baum T).trans hSP
  have hKJ : ⁅twoResidual P, thompsonJ T⁆ = twoResidual P := by
    obtain ⟨-, hVel, hredP⟩ := conjClosure_isTwoReducedIn_of_charTwo hMinP.isSylow hFP (le_refl _)
    obtain ⟨L, hL, hnat⟩ :=
      exists_single_block hVel hMinP hsolvP (pRank_le_two_of_isSQTKTC hSQP) hredP hJP hbb
    obtain ⟨-, hKf, hcomm⟩ := isNatL2Section_fstarPre hVel hredP.2.1 hL hnat
    have hJS : thompsonJ (baum T) = thompsonJ T :=
      B6.thompsonJ_eq_of_le (B6.thompsonJ_le_baum T) inf_le_left
    have hPV : ¬ P ≤ Subgroup.centralizer (VZ (baum T) P : Set G) := fun hle =>
      hJP ((B6.thompsonJ_le _).trans (hMinP.isSylow.1.trans hle))
    have hKC : ¬ twoResidual P ≤ Subgroup.centralizer (VZ (baum T) P : Set G) :=
      MinParabolic.not_twoResidual_le_centralizer hredP hPV
    obtain ⟨a, haJ, ha2, haC⟩ := exists_involution_not_mem_centralizer hJP
    rw [hJS] at haJ
    have hNC := hcomm (twoResidual P) (thompsonJ T) hKf hJT hKC ⟨a, haJ, ha2, haC⟩
    have hQK : pCoreOf 2 (twoResidual P) ≤ Subgroup.centralizer (VZ (baum T) P : Set G) :=
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKP)
        ((le_normalizer_twoResidual P).trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans
        (MinParabolic.pCoreOf_le_centralizer hredP)
    have hNC' : ¬ ⁅twoResidual P, thompsonJ T⁆ ≤ pCoreOf 2 (twoResidual P) := fun hle =>
      hNC (hle.trans hQK)
    have hJN : thompsonJ T ≤ Subgroup.normalizer (twoResidual P : Set G) :=
      hJT.trans (le_normalizer_twoResidual P)
    have hNL : ⁅twoResidual P, thompsonJ T⁆ ≤ twoResidual P :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hJN
    have hLN : twoResidual P ≤ Subgroup.normalizer
        ((⁅twoResidual P, thompsonJ T⁆ : Subgroup G) : Set G) :=
      A3.le_normalizer_commutator_left _ _
    have hq : IsAltQuotient (twoResidual P) (pCoreOf 2 (twoResidual P)) 3 := by
      obtain ⟨α, hαs, hαk, -⟩ := hKalt
      exact ⟨α, hαs, by rw [hαk, pCoreOf_subgroupOf_self]⟩
    exact C1GN.isShort2_eq_of_isAltQuotient hKblock.1 (by decide) le_rfl hq hNL hLN hNC'
  have hUeq : U = T ⊔ conjClosure (twoResidual P) T := by
    apply le_antisymm
    · calc U = P ⊔ T := hPT.symm
        _ = (baum T ⊔ twoResidual P) ⊔ T := by rw [sup_twoResidual_eq hMinP.isSylow]
        _ ≤ T ⊔ conjClosure (twoResidual P) T :=
          sup_le (sup_le (inf_le_left.trans le_sup_left)
            ((le_conjClosure _ T).trans le_sup_right)) le_sup_left
    · refine sup_le hTU.le (conjClosure_le fun t ht z hz => ?_)
      exact U.mul_mem (U.mul_mem (hTU.le ht) (hKU hz)) (U.inv_mem (hTU.le ht))
  have hKM' : ¬ twoResidual P ≤ M' := by
    intro hKM
    apply hPnotM'
    calc P = baum T ⊔ twoResidual P := (sup_twoResidual_eq hMinP.isSylow).symm
      _ ≤ M' := sup_le (inf_le_left.trans hTM') hKM
  exact ⟨twoResidual P, ⟨hKblockU, Or.inr (Or.inl hKalt)⟩, hKalt, hKJ, hUeq, hKM'⟩

end CFSG.Quasithin.C1Pack
