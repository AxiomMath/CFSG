module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_7_c

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section12_CA_msigma_primeOrder_of_tau2_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    Nat.card (subgroupCentralizerIn A (section10Msigma M)) = p.val := by
  classical
  obtain ⟨A₀, hA₀, hCA₀⟩ :=
    section12_exists_primeOrder_centralizer_ne_bot_of_tau2_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA
  have hCA_eq_A₀ :
      subgroupCentralizerIn A (section10Msigma M) = A₀ :=
    section12_CA_msigma_eq_fixed_primeOrder_of_tau2_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (A₀ := A₀) (p := p)
      hM hE hp hA hA₀ hCA₀ hSylow
  simpa [hCA_eq_A₀] using hA₀.2

public theorem CFSG.section12_sigma_compl_fitting_core_isPGroup_of_tau2_singleton_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    IsPGroup p.val
      (piCoreIn (section10SigmaPrimes M)ᶜ (section8FittingSubgroup M)) := by
  classical
  let F : Subgroup G := section8FittingSubgroup M
  let Z : Subgroup G := piCoreIn (section10SigmaPrimes M)ᶜ F
  have hZπ : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) Z := by
    intro q hqZ
    have hZleF : Z ≤ F := by
      simpa [Z, F] using
        piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ F
    have hqF : q ∈ subgroupPrimeSet F :=
      hqZ.trans (Subgroup.card_dvd_of_le hZleF)
    have hZσcompl :
        IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ Z := by
      simpa [Z, F] using
        piCoreIn_isPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ F
    have hq_not_sigma : q ∉ section10SigmaPrimes M :=
      hZσcompl q hqZ
    let Rq : Subgroup G :=
      piCoreIn ({q} : Set Nat.Primes) (section8CenterInFitting M)
    have hqZFit : q ∈ subgroupPrimeSet (section8CenterInFitting M) := by
      simpa [F] using
        (by
          rw [section8CenterInFitting_primeSet_eq_fitting M]
          exact hqF)
    have hZFit_comm : IsMulCommutative (section8CenterInFitting M) := by
      simpa using section8CenterInFitting_isMulCommutative M
    letI : IsMulCommutative (section8CenterInFitting M) := hZFit_comm
    have hRq_ne : Rq ≠ ⊥ := by
      simpa [Rq] using
        section8_piCoreIn_singleton_ne_bot_of_mem_subgroupPrimeSet_of_isMulCommutative
          (G := G) (H := section8CenterInFitting M) hqZFit
    have hRq_le_M : Rq ≤ M :=
      (piCoreIn_le (G := G) ({q} : Set Nat.Primes) (section8CenterInFitting M)).trans
        (section8CenterInFitting_le_maximal M)
    have hRq_p : IsPGroup q.val Rq := by
      simpa [Rq] using
        section8_piCoreIn_singleton_centerInFitting_isPGroup (G := G) M q
    have hM8 : M ∈ section8MaximalSubgroups G := by
      simpa [section8MaximalSubgroups, section9MaximalSubgroups] using hM
    have hnorm_Rq_eq_M :
        Subgroup.normalizer (Rq : Set G) = M := by
      simpa [Rq, F] using
        section8_normalizer_piCoreIn_singleton_centerInFitting_eq
          (G := G) (M := M) hM8 hqF
    have hMstar :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Rq : Set G)) := by
      refine ⟨hM, ?_⟩
      intro x hx
      rwa [hnorm_Rq_eq_M] at hx
    have hq_sigma_or_tau2 :
        q ∈ section10SigmaPrimes M ∪ section12Tau2Primes M :=
      lemma_12_2_a (G := G) (M := M) (Mstar := M) (X := Rq) (p := q)
        hM hRq_p hRq_ne hRq_le_M hMstar
    rcases hq_sigma_or_tau2 with hqσ | hqτ2
    · exact False.elim (hq_not_sigma hqσ)
    · have hτ2_single : section12Tau2Primes M = {p} :=
        theorem_12_7_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hM hE hp hA hSylow
      have hq_single : q ∈ ({p} : Set Nat.Primes) := by
        simpa [hτ2_single] using hqτ2
      simpa using hq_single
  simpa [Z] using
    section8_isPGroup_of_isPiSubgroup_singleton (G := G) hZπ

public theorem CFSG.section12_CA_msigma_ne_omegaOneCenter_of_tau2_pre
    {M E E₁₂ E₁ E₂ E₃ A P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (_hPnonab : ¬ IsMulCommutative P)
    (hPnotM : ¬ P ≤ M)
    (hCcard : Nat.card (subgroupCentralizerIn A (section10Msigma M)) = p.val) :
    subgroupCentralizerIn A (section10Msigma M) ≠ section10OmegaOneCenter p P := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  have hCprime : C ∈ section10PrimeOrderSubgroupsIn p A := by
    exact ⟨inf_le_left, by simpa [C] using hCcard⟩
  have hσ_le_centC : section10Msigma M ≤ Subgroup.centralizer (C : Set G) := by
    simpa [C] using section12_subgroupCentralizerIn_commute_pre A (section10Msigma M)
  have hCσ_ne_bot : subgroupCentralizerIn (section10Msigma M) C ≠ ⊥ := by
    intro hbot
    have hσ_le_bot : section10Msigma M ≤ ⊥ := by
      intro s hs
      have hsC : s ∈ subgroupCentralizerIn (section10Msigma M) C := ⟨hs, hσ_le_centC hs⟩
      simpa [hbot] using hsC
    exact (theorem_10_2_e (G := G) hM) (le_bot_iff.mp hσ_le_bot)
  intro hCeq
  have hP_le_centC : P ≤ Subgroup.centralizer (C : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcΩ : c ∈ section10OmegaOneCenter p P := by
      simpa [C, hCeq] using hc
    exact (Subgroup.mem_centralizer_iff.mp
      (section12_omegaOneCenter_centralizes_pre (G := G) (p := p) P hcΩ) x hx).symm
  have hCentC_le_M :
      Subgroup.centralizer (C : Set G) ≤ M :=
    section12_centralizer_le_M_of_msigma_fixed_primeOrder_tau2_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (X := C) (p := p)
      hM hE hp hA hCprime hCσ_ne_bot
  exact hPnotM (hP_le_centC.trans hCentC_le_M)

public theorem CFSG.section12_lemma_10_13_factor_msigma_centralizer_eq_bot_pre
    {M E E₁₂ E₁ E₂ E₃ A P Y : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G)
    (hPp : IsPGroup p.val P)
    (hYleCP : Y ≤ subgroupCentralizerIn P A)
    (hdisj : Disjoint (subgroupCentralizerIn A (section10Msigma M)) Y) :
    subgroupCentralizerIn Y (section10Msigma M) = ⊥ := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  apply le_bot_iff.mp
  intro y hy
  by_contra hyne_bot
  have hyne : y ≠ 1 := by
    intro hy1
    exact hyne_bot (by simp [hy1])
  obtain ⟨q, z, hz_zpowy, hzY, hzne, hXqY⟩ :=
    section12_exists_primeOrder_zpowers_in_pre (B := Y) hy.1 hyne
  let X : Subgroup G := Subgroup.zpowers z
  have hXqY' : X ∈ section10PrimeOrderSubgroupsIn q Y := by
    simpa [X] using hXqY
  rcases (show X ≤ Y ∧ Nat.card X = q.val from hXqY') with ⟨hX_le_Y, hXcard_q⟩
  have hY_le_P : Y ≤ P := hYleCP.trans inf_le_left
  have hq_eq_p : q = p := by
    have hPπ : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) P :=
      section8_isPiSubgroup_singleton_of_isPGroup (G := G) hPp
    have hqP : q.val ∣ Nat.card P :=
      (by rw [hXcard_q] : q.val ∣ Nat.card X).trans
        (Subgroup.card_dvd_of_le (hX_le_Y.trans hY_le_P))
    have hq_single : q ∈ ({p} : Set Nat.Primes) := hPπ q hqP
    simpa using hq_single
  have hX_E : X ∈ section10PrimeOrderSubgroupsIn p E := by
    have hCentA_le_E : Subgroup.centralizer (A : Set G) ≤ E := by
      have h6 :=
        corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hM hE hp hA
      simpa [h6.2.1] using h6.1
    have hY_le_centA : Y ≤ Subgroup.centralizer (A : Set G) :=
      hYleCP.trans inf_le_right
    exact ⟨hX_le_Y.trans (hY_le_centA.trans hCentA_le_E), by simpa [hq_eq_p] using hXcard_q⟩
  have hX_ne_C : X ≠ C := by
    intro hXC
    have hX_ne_bot : X ≠ ⊥ := section12_primeOrder_ne_bot hX_E
    have hX_le_CinfY : X ≤ C ⊓ Y := by
      intro x hx
      exact ⟨by simpa [C, ← hXC] using hx, hX_le_Y hx⟩
    have hXbot : X = ⊥ := le_bot_iff.mp (by
      rw [← hdisj.eq_bot]
      exact hX_le_CinfY)
    exact hX_ne_bot hXbot
  have hCX_bot : subgroupCentralizerIn (section10Msigma M) X = ⊥ :=
    (theorem_12_7_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow X hX_E (by simpa [C] using hX_ne_C)).1
  have hσ_le_CX : section10Msigma M ≤ subgroupCentralizerIn (section10Msigma M) X := by
    intro s hs
    refine ⟨hs, ?_⟩
    change s ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hxX
    rcases Subgroup.mem_zpowers_iff.mp (by simpa [X] using hxX) with ⟨n, rfl⟩
    have hy_cent_σ : y ∈ Subgroup.centralizer (section10Msigma M : Set G) := hy.2
    have hcomm : Commute y s := by
      exact (Subgroup.mem_centralizer_iff.mp hy_cent_σ s hs).symm
    have hz_comm : Commute z s := by
      have hz_pow : z ∈ Subgroup.zpowers y := hz_zpowy
      rcases Subgroup.mem_zpowers_iff.mp hz_pow with ⟨m, rfl⟩
      exact hcomm.zpow_left m
    exact (hz_comm.zpow_left n).eq
  have hσ_bot : section10Msigma M = ⊥ := le_bot_iff.mp (by
    intro s hs
    simpa [hCX_bot] using hσ_le_CX hs)
  exact (theorem_10_2_e (G := G) hM) hσ_bot

public theorem CFSG.section12_sigma_compl_fitting_core_le_CA_msigma_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G)
    (hCcard : Nat.card (subgroupCentralizerIn A (section10Msigma M)) = p.val) :
    piCoreIn (section10SigmaPrimes M)ᶜ (section8FittingSubgroup M) ≤
      subgroupCentralizerIn A (section10Msigma M) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  let F : Subgroup G := section8FittingSubgroup M
  let S : Subgroup G := section10Msigma M
  let Z : Subgroup G := piCoreIn (section10SigmaPrimes M)ᶜ F
  let C : Subgroup G := subgroupCentralizerIn A S
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hZp : IsPGroup p.val Z := by
    simpa [Z, F] using
      section12_sigma_compl_fitting_core_isPGroup_of_tau2_singleton_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA hSylow
  have hAp : IsPGroup p.val A := by
    have hElem := (section12_rankTwo_elementary hA).2
    haveI : IsElementaryAbelian p.val A := hElem
    exact IsElementaryAbelian.isPGroup p.val A
  have hZ_le_F : Z ≤ F := by
    simpa [Z, F] using
      piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ F
  have hZ_le_M : Z ≤ M :=
    hZ_le_F.trans (section8FittingSubgroup_le M)
  have hZ_cent_S : Z ≤ Subgroup.centralizer (S : Set G) := by
    simpa [Z, F, S] using
      section10_sigma_compl_fitting_core_le_centralizer_msigma (G := G) hM
  have hA_norm_Z : A ≤ Subgroup.normalizer (Z : Set G) := by
    exact (section12_rankTwo_le hA_M).trans (by
      simpa [Z, F] using
        section10_le_normalizer_sigma_compl_fitting_core (G := G) M)
  have hJoin_p : IsPGroup p.val (A ⊔ Z : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hAp hZp hA_norm_Z
  obtain ⟨P, hJoin_le_P⟩ :=
    IsPGroup.exists_le_sylow (G := G) (p := p.val) hJoin_p
  have hA_le_P : A ≤ (P : Subgroup G) :=
    le_sup_left.trans hJoin_le_P
  have hZ_le_P : Z ≤ (P : Subgroup G) :=
    le_sup_right.trans hJoin_le_P
  have hPnonab : ¬ IsMulCommutative (P : Subgroup G) := by
    obtain ⟨Pnonab, _hA_le_Pnonab, hPnonab_noncomm⟩ :=
      section12_exists_nonabelian_sylow_containing_rankTwo_pre
        (G := G) (E := E) (A := A) (p := p) hA hSylow
    intro hPcomm
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Pnonab
    have hconj_comm : IsMulCommutative ((g • P : Sylow p.val G) : Subgroup G) := by
      letI : IsMulCommutative (P : Subgroup G) := hPcomm
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.map_isMulCommutative
        (f := (MulAut.conj g).toMonoidHom) (H := (P : Subgroup G))
    have hPnonab_comm : IsMulCommutative (Pnonab : Subgroup G) := by
      rw [← hg]
      exact hconj_comm
    exact hPnonab_noncomm hPnonab_comm
  have hPnotM : ¬ (P : Subgroup G) ≤ M :=
    section12_global_sylow_not_le_M_of_nonabelian_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hPnonab
  have hZ_cent_A : Z ≤ Subgroup.centralizer (A : Set G) := by
    have hPM_comm : IsMulCommutative ((P : Subgroup G) ⊓ M : Subgroup G) :=
      section12_sylow_inf_M_isMulCommutative_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA P
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hzPM : z ∈ (P : Subgroup G) ⊓ M := ⟨hZ_le_P hz, hZ_le_M hz⟩
    have haPM : a ∈ (P : Subgroup G) ⊓ M :=
      ⟨hA_le_P ha, (section12_rankTwo_le hA_M) ha⟩
    exact (setLike_mul_comm
      (s := (P : Subgroup G) ⊓ M) hzPM haPM).symm
  have hAmaxG : A ∈ maximalElementaryAbelianSubgroups p.val G :=
    (lemma_12_1_g (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA_M).1
  have hA10 : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G := by
    simpa [section10RankTwoMaximalElementaryAbelianSubgroups] using
      (⟨section12_rankTwo_elementary hA, hAmaxG⟩ :
        A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G ∧
          A ∈ maximalElementaryAbelianSubgroups p.val G)
  have hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G) := by
    exact (section12_rankTwo_prime_mem hA).trans
      (Subgroup.card_dvd_of_le (show E ≤ (⊤ : Subgroup G) from le_top))
  have hCprime : C ∈ section10PrimeOrderSubgroupsIn p A := by
    exact ⟨inf_le_left, by simpa [C, S] using hCcard⟩
  have hCneOmega : C ≠ section10OmegaOneCenter p (P : Subgroup G) := by
    simpa [C, S] using
      section12_CA_msigma_ne_omegaOneCenter_of_tau2_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (P := (P : Subgroup G)) (p := p)
        hM hE hp hA hPnonab hPnotM hCcard
  obtain ⟨Y, _hΩY, hYcyc, hCdisjY, hCPeq⟩ :=
    lemma_10_13_b (G := G) (p := p) (A := A) (P := (P : Subgroup G))
      (A₀ := C) hpG hA10 P.isPGroup' hPnonab hA_le_P hCprime hCneOmega
  have hY_le_CP : Y ≤ subgroupCentralizerIn (P : Subgroup G) A := by
    rw [hCPeq]
    exact le_sup_right
  have hY_cent_S_bot : subgroupCentralizerIn Y S = ⊥ := by
    simpa [S, C] using
      section12_lemma_10_13_factor_msigma_centralizer_eq_bot_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (P := (P : Subgroup G))
        (Y := Y) (p := p) hM hE hp hA hSylow P.isPGroup'
        hY_le_CP (by simpa [C, S] using hCdisjY)
  have hC_norm_Y : C ≤ Subgroup.normalizer (Y : Set G) := by
    have hY_le_centA : Y ≤ Subgroup.centralizer (A : Set G) :=
      hY_le_CP.trans inf_le_right
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hcomm : c * y = y * c :=
        Subgroup.mem_centralizer_iff.mp (hY_le_centA hy) c (hc.1)
      have hconj : c * y * c⁻¹ = y := by
        calc
          c * y * c⁻¹ = y * c * c⁻¹ := by rw [hcomm]
          _ = y := by simp [mul_assoc]
      simpa [hconj] using hy
    · intro hy
      let y' : G := c * y * c⁻¹
      have hy'Y : y' ∈ Y := by simpa [y'] using hy
      have hcomm' : c * y' = y' * c :=
        Subgroup.mem_centralizer_iff.mp (hY_le_centA hy'Y) c (hc.1)
      have hy_eq : y = y' := by
        calc
          y = c⁻¹ * y' * c := by simp [y', mul_assoc]
          _ = y' := by
            have h := congrArg (fun t : G => c⁻¹ * t) hcomm'.symm
            simpa [mul_assoc] using h
      simpa [hy_eq] using hy'Y
  intro x hxZ
  have hxCP : x ∈ subgroupCentralizerIn (P : Subgroup G) A :=
    ⟨hZ_le_P hxZ, hZ_cent_A hxZ⟩
  have hxSup : x ∈ C ⊔ Y := by
    simpa [hCPeq] using hxCP
  let D : Subgroup G := C ⊔ Y
  let CD : Subgroup D := C.subgroupOf D
  let YD : Subgroup D := Y.subgroupOf D
  haveI : YD.Normal := by
    simpa [D, YD] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := C) (N := Y) hC_norm_Y)
  let xD : D := ⟨x, by simpa [D] using hxSup⟩
  have hCD_YD_top : CD ⊔ YD = ⊤ := by
    calc
      CD ⊔ YD = D.subgroupOf D := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := C) (A' := Y) (B := D)
          (by simp [D])
          (by simp [D])
      _ = ⊤ := by simp
  have hxTop : xD ∈ CD ⊔ YD := by
    simp [hCD_YD_top]
  rcases (Subgroup.mem_sup_of_normal_right
      (s := CD) (t := YD) (x := xD)).1 hxTop with
    ⟨cD, hcD, yD, hyD, hmul⟩
  let c : G := cD
  let y : G := yD
  have hcC : c ∈ C := by
    simpa [c, CD, Subgroup.mem_subgroupOf] using hcD
  have hyY : y ∈ Y := by
    simpa [y, YD, Subgroup.mem_subgroupOf] using hyD
  have hx_eq_cy : x = c * y := by
    have hval := congrArg (fun z : D => (z : G)) hmul
    simpa [xD, c, y] using hval.symm
  have hy_cent_S : y ∈ Subgroup.centralizer (S : Set G) := by
    have hy_eq : y = c⁻¹ * x := by
      calc
        y = c⁻¹ * (c * y) := by simp
        _ = c⁻¹ * x := by rw [← hx_eq_cy]
    have hc_cent_S : c ∈ Subgroup.centralizer (S : Set G) := hcC.2
    have hx_cent_S : x ∈ Subgroup.centralizer (S : Set G) := hZ_cent_S hxZ
    rw [hy_eq]
    exact (Subgroup.centralizer (S : Set G)).mul_mem
      ((Subgroup.centralizer (S : Set G)).inv_mem hc_cent_S) hx_cent_S
  have hySub : y ∈ subgroupCentralizerIn Y S := ⟨hyY, hy_cent_S⟩
  have hy_one : y = 1 := by
    have hybot : y ∈ (⊥ : Subgroup G) := by
      simpa [hY_cent_S_bot] using hySub
    simpa using hybot
  have hx_eq_c : x = c := by
    simpa [hy_one] using hx_eq_cy
  simpa [C, S, hx_eq_c] using hcC

public theorem CFSG.section12_fitting_eq_msigma_sup_CA_msigma_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G)
    (hCcard : Nat.card (subgroupCentralizerIn A (section10Msigma M)) = p.val) :
    section8FittingSubgroup M =
      section10Msigma M ⊔ subgroupCentralizerIn A (section10Msigma M) := by
  classical
  let F : Subgroup G := section8FittingSubgroup M
  let S : Subgroup G := section10Msigma M
  let C : Subgroup G := subgroupCentralizerIn A S
  let Z : Subgroup G := piCoreIn (section10SigmaPrimes M)ᶜ F
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hσF : S ≤ F :=
    section12_msigma_le_fitting_of_tau2_pre hM hp hA_M
  have hC_le_F : C ≤ F := by
    simpa [C, F] using
      section12_subgroupCentralizerIn_le_fitting_of_card_prime_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hE (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA).1
        hCcard
  have hZ_le_C : Z ≤ C := by
    simpa [Z, F, S, C] using
      section12_sigma_compl_fitting_core_le_CA_msigma_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA hSylow hCcard
  have hFeq :
      F = S ⊔ C := by
    apply le_antisymm
    · exact (section10_fitting_le_msigma_sup_sigma_compl_fitting_core (G := G) M).trans
        (sup_le_sup_left hZ_le_C S)
    · refine sup_le hσF ?_
      exact hC_le_F
  simpa [F, S, C] using hFeq

public theorem CFSG.section12_internalDirectProduct_msigma_CA_msigma_of_card_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G)
    (hCcard : Nat.card (subgroupCentralizerIn A (section10Msigma M)) = p.val) :
    section12InternalDirectProduct (section10Msigma M)
      (subgroupCentralizerIn A (section10Msigma M)) (section8FittingSubgroup M) := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hσF : section10Msigma M ≤ section8FittingSubgroup M :=
    section12_msigma_le_fitting_of_tau2_pre hM hp hA_M
  have hAnorm : section10NormalIn A E :=
    (corollary_12_6_a hM hE hp hA).1
  have hCF : C ≤ section8FittingSubgroup M := by
    simpa [C] using
      section12_subgroupCentralizerIn_le_fitting_of_card_prime_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hE hAnorm hCcard
  have hCE : C ≤ E := by
    intro x hx
    exact (section12_rankTwo_le hA) hx.1
  have hdisj : Disjoint (section10Msigma M) C := by
    rw [Subgroup.disjoint_def]
    intro x hxσ hxC
    exact Subgroup.disjoint_def.mp hE.1.2.2.2 hxσ (hCE hxC)
  have hcomm : section10Msigma M ≤ Subgroup.centralizer (C : Set G) := by
    simpa [C] using section12_subgroupCentralizerIn_commute_pre A (section10Msigma M)
  have hFeq :
      section8FittingSubgroup M = section10Msigma M ⊔ C := by
    simpa [C] using
      section12_fitting_eq_msigma_sup_CA_msigma_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA hSylow hCcard
  exact ⟨hσF, hCF, hFeq, hdisj, hcomm⟩

/-- Maschke complement for an invariant subgroup of an elementary abelian group,
specialized to the subgroup/action conventions used in Section 12. -/
public theorem CFSG.section12_exists_isCompl_isInvariant_of_elementaryAbelian_coprime_pre
    {V A : Type*} [Group V] [Finite V] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p V] [Group A] [Finite A] [MulDistribMulAction A V]
    (hcop : Nat.Coprime p (Nat.card A)) (B : Subgroup V) [IsInvariant A V B] :
    ∃ C : Subgroup V, IsCompl B C ∧ IsInvariant A V C := by
  classical
  letI : CommGroup V := IsMulCommutative.instCommGroup
  letI : AddCommGroup (Additive V) := Additive.addCommGroup
  let ρ : Representation (ZMod p) A (Additive V) :=
    Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := p)
  let instAdd : AddCommGroup ρ.asModule := Representation.instAddCommGroupAsModule ρ
  letI : AddCommGroup ρ.asModule := instAdd
  let instMod : Module (MonoidAlgebra (ZMod p) A) ρ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  letI : Module (MonoidAlgebra (ZMod p) A) ρ.asModule := instMod
  let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hBinv : η B ∈ ρ.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    have hxB : Additive.toMul x ∈ B := by simpa [η] using hx
    simpa [ρ, η] using
      (IsInvariant.invariant (A := A) (G := V) (H := B) a (Additive.toMul x)).1 hxB
  let Bpack : ρ.invtSubmodule := ⟨η B, hBinv⟩
  haveI : Fintype A := Fintype.ofFinite A
  haveI : NeZero (Fintype.card A : ZMod p) := by
    constructor
    intro hzero
    have hdiv : p ∣ Fintype.card A :=
      (ZMod.natCast_eq_zero_iff (Fintype.card A) p).1 hzero
    have hnot : ¬ p ∣ Fintype.card A := by
      exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd).1
        (by simpa [Nat.card_eq_fintype_card] using hcop)
    exact hnot hdiv
  let Bmod : @Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule _
      instAdd.toAddCommMonoid instMod :=
    ρ.mapSubmodule Bpack
  obtain ⟨Cmod, hBCmod⟩ := @MonoidAlgebra.Submodule.exists_isCompl'
    (ZMod p) inferInstance A inferInstance inferInstance ρ.asModule instAdd instMod inferInstance Bmod
  let Cpack : ρ.invtSubmodule := ρ.mapSubmodule.symm Cmod
  let C : Subgroup V := η.symm (Cpack : Submodule (ZMod p) (Additive V))
  have hCinv : IsInvariant A V C := by
    refine ⟨?_⟩
    intro a v
    constructor
    · intro hv
      have hvC : Additive.ofMul v ∈ (Cpack : Submodule (ZMod p) (Additive V)) := by
        simpa [C, η] using hv
      have hmem := (Representation.mem_invtSubmodule (ρ := ρ)).1 Cpack.2 a
      have hsmul :=
        (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ρ a)).1 hmem
          (Additive.ofMul v) hvC
      simpa [ρ, C, η] using hsmul
    · intro hv
      have hvC : Additive.ofMul (a • v) ∈ (Cpack : Submodule (ZMod p) (Additive V)) := by
        simpa [C, η] using hv
      have hmem := (Representation.mem_invtSubmodule (ρ := ρ)).1 Cpack.2 a⁻¹
      have hsmul :=
        (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ρ a⁻¹)).1 hmem
          (Additive.ofMul (a • v)) hvC
      simpa [ρ, C, η, inv_smul_smul] using hsmul
  refine ⟨C, ?_, hCinv⟩
  have hcompl_sub : IsCompl (η B) (η C) := by
    have hcompl_pack : IsCompl Bpack Cpack := by
      exact (ρ.mapSubmodule.isCompl_iff).2 (by simpa [Bmod, Cpack] using hBCmod)
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl_pack ⊢
    constructor
    · simpa [Bpack, Cpack, C] using congrArg Subtype.val hcompl_pack.1
    · simpa [Bpack, Cpack, C] using congrArg Subtype.val hcompl_pack.2
  exact (OrderIso.isCompl_iff (f := η) (x := B) (y := C)).2 hcompl_sub

public theorem CFSG.section12_E2_isPGroup_of_tau2_singleton_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    IsPGroup p.val E₂ := by
  classical
  have hτ2_single : section12Tau2Primes M = {p} :=
    theorem_12_7_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  have hE2HallIn :
      section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
    section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
  rcases hE2HallIn with ⟨hE2E, hHallE2⟩
  apply section12_isPGroup_of_isPiSubgroup_singleton
  intro q hqdiv
  have hqdiv_sub : q.val ∣ Nat.card (E₂.subgroupOf E) := by
    simpa [natCard_subgroupOf_eq _ _ hE2E] using hqdiv
  have hqτ2 : q ∈ section12Tau2Primes M :=
    hHallE2.p_in_pi_of_p_dvd_card q hqdiv_sub
  have hq_single : q ∈ ({p} : Set Nat.Primes) := by
    simpa [hτ2_single] using hqτ2
  simpa using hq_single

public theorem CFSG.section12_rankTwo_tau2_le_E2
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    A ≤ E₂ := by
  classical
  have hAnorm : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).1
  haveI : (A.subgroupOf E).Normal := hAnorm.2
  have hE2HallIn :
      section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
    section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
  rcases hE2HallIn with ⟨hE2E, hHallE2⟩
  have hAp : IsPGroup p.val (A.subgroupOf E) :=
    section12_rankTwo_subgroupOf_isPGroup hA
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hp' : (⟨p.val, Fact.out⟩ : Nat.Primes) ∈ section12Tau2Primes M := by
    rw [show (⟨p.val, Fact.out⟩ : Nat.Primes) = p by exact Subtype.ext rfl]
    exact hp
  have hA_le_E2sub : A.subgroupOf E ≤ E₂.subgroupOf E :=
    section12_normal_pSubgroup_le_of_isHallSubgroup_of_prime_mem
      (R := E) (π := section12Tau2Primes M) (H := E₂.subgroupOf E)
      (N := A.subgroupOf E) (p := p.val) hAp hHallE2 hp'
  intro x hx
  have hxE : x ∈ E := section12_rankTwo_le hA hx
  let xE : E := ⟨x, hxE⟩
  have hxSub : xE ∈ A.subgroupOf E := by
    simpa [xE, Subgroup.mem_subgroupOf] using hx
  exact hA_le_E2sub hxSub

public theorem CFSG.section12_CA_msigma_le_E2_of_tau2_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    subgroupCentralizerIn A (section10Msigma M) ≤ E₂ :=
  inf_le_left.trans (section12_rankTwo_tau2_le_E2 hM hE hp hA)

public theorem CFSG.section12_E2_commutative_of_tau2_nonabelian_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    IsMulCommutative E₂ := by
  classical
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hE2_p : IsPGroup p.val E₂ :=
    section12_E2_isPGroup_of_tau2_singleton_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  have hE2HallIn :
      section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
    section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
  rcases hE2HallIn with ⟨hE2E, _hHallE2⟩
  let E₂sub : Subgroup M := E₂.subgroupOf M
  have hE2_le_M : E₂ ≤ M := hE2E.trans hE.1.2.1
  have hE2sub_p : IsPGroup p.val E₂sub :=
    hE2_p.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := E₂) (K := M) hE2_le_M).symm
  obtain ⟨T, hE2sub_le_T⟩ :=
    IsPGroup.exists_le_sylow (G := M) (p := p.val) hE2sub_p
  have hTcomm : IsMulCommutative (T : Subgroup M) :=
    (theorem_12_5_b hM hp hA_M).1 T
  have hTamb_comm : IsMulCommutative (section10AmbientSylowSubgroup M T) := by
    exact section11_isMulCommutative_ambient_of_sylow hTcomm
  have hE2_amb_le_T : E₂ ≤ section10AmbientSylowSubgroup M T := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hE2_le_M hx⟩,
        hE2sub_le_T (by simpa [E₂sub, Subgroup.mem_subgroupOf] using hx), rfl⟩
  refine ⟨⟨fun x y => ?_⟩⟩
  exact Subtype.ext <|
    setLike_mul_comm
      (s := section10AmbientSylowSubgroup M T)
      (hE2_amb_le_T x.property) (hE2_amb_le_T y.property)

public theorem CFSG.section12_E2_le_centralizer_rankTwo_tau2_of_theorem_12_7_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    E₂ ≤ Subgroup.centralizer (A : Set G) := by
  classical
  have hA_le_E2 : A ≤ E₂ :=
    section12_rankTwo_tau2_le_E2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA
  have hE2comm : IsMulCommutative E₂ :=
    section12_E2_commutative_of_tau2_nonabelian_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA hSylow
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (setLike_mul_comm
    (s := E₂) hx (hA_le_E2 ha)).symm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_E_le_normalizer_CA_msigma_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hAnorm : section10NormalIn A E) :
    E ≤ Subgroup.normalizer
      (subgroupCentralizerIn A (section10Msigma M) : Set G) := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  have hE_norm_A : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAnorm.1).mp hAnorm.2
  have hE_norm_σ : E ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hE.1.2.1.trans section12_le_normalizer_msigma
  intro e he
  have he_norm_A : e ∈ Subgroup.normalizer (A : Set G) := hE_norm_A he
  have he_norm_σ : e ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    hE_norm_σ he
  have he_inv_norm_A : e⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normalizer (A : Set G)).inv_mem he_norm_A
  have he_inv_norm_σ : e⁻¹ ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    (Subgroup.normalizer (section10Msigma M : Set G)).inv_mem he_norm_σ
  have hconj_mem :
      ∀ {x : G}, x ∈ C → e * x * e⁻¹ ∈ C := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp he_norm_A x).1 hx.1
    · change e * x * e⁻¹ ∈ Subgroup.centralizer (section10Msigma M : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyσ
      have hy_conj : e⁻¹ * y * e ∈ section10Msigma M := by
        simpa using (Subgroup.mem_normalizer_iff.mp he_inv_norm_σ y).1 hyσ
      have hcomm :
          (e⁻¹ * y * e) * x = x * (e⁻¹ * y * e) :=
        Subgroup.mem_centralizer_iff.mp hx.2 (e⁻¹ * y * e) hy_conj
      calc
        y * (e * x * e⁻¹) = e * ((e⁻¹ * y * e) * x) * e⁻¹ := by group
        _ = e * (x * (e⁻¹ * y * e)) * e⁻¹ := by rw [hcomm]
        _ = (e * x * e⁻¹) * y := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hconj_mem hx
  · intro hx
    have hx' : e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹ ∈ C := by
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp he_inv_norm_A (e * x * e⁻¹)).1 hx.1
      · change e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹ ∈
          Subgroup.centralizer (section10Msigma M : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hyσ
        have hy_conj : e * y * e⁻¹ ∈ section10Msigma M :=
          (Subgroup.mem_normalizer_iff.mp he_norm_σ y).1 hyσ
        have hcomm :
            (e * y * e⁻¹) * (e * x * e⁻¹) =
              (e * x * e⁻¹) * (e * y * e⁻¹) :=
          Subgroup.mem_centralizer_iff.mp hx.2 (e * y * e⁻¹) hy_conj
        calc
          y * (e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹) =
              e⁻¹ * ((e * y * e⁻¹) * (e * x * e⁻¹)) * e := by group
          _ = e⁻¹ * ((e * x * e⁻¹) * (e * y * e⁻¹)) * e := by rw [hcomm]
          _ = (e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹) * y := by group
    simpa [C, mul_assoc] using hx'

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_CA_msigma_normalIn_E_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hAnorm : section10NormalIn A E) :
    section10NormalIn (subgroupCentralizerIn A (section10Msigma M)) E := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  have hCE : C ≤ E := inf_le_left.trans hAnorm.1
  refine ⟨hCE, ?_⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hCE).2
    (by simpa [C] using section12_E_le_normalizer_CA_msigma_pre (G := G) hE hAnorm)

public theorem CFSG.section12_E1_le_normalizer_E2_pre
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    E₁ ≤ Subgroup.normalizer (E₂ : Set G) := by
  classical
  have h12 := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
    (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE
  have hE1_le_E12 : E₁ ≤ E₁₂ := hE.2.2.1.1
  have hE12_norm_E2 : E₁₂ ≤ Subgroup.normalizer (E₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h12.2.2.2.1).1 h12.2.2.2.2
  exact hE1_le_E12.trans hE12_norm_E2

/-- Theorem 12.7(b). -/
public theorem CFSG.theorem_12_7_b
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    Nat.card (subgroupCentralizerIn A (section10Msigma M)) = p.val ∧
      section12InternalDirectProduct (section10Msigma M)
        (subgroupCentralizerIn A (section10Msigma M)) (section8FittingSubgroup M) := by
  classical
  have hCcard :=
    section12_CA_msigma_primeOrder_of_tau2_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  exact ⟨hCcard,
    section12_internalDirectProduct_msigma_CA_msigma_of_card_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow hCcard⟩




end Section12
