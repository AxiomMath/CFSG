module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.corollary_13_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 13 4 from BG Section 13 -/

section Section13

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
public theorem CFSG.section13_sigma_of_mem_centralizer_msigma
    {M P : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hqX : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) P)) :
    q ∈ section10SigmaPrimes M := by
  have hX_le_msigma :
      subgroupCentralizerIn (section10Msigma M) P ≤ section10Msigma M :=
    inf_le_left
  have hqMsigma : q ∈ subgroupPrimeSet (section10Msigma M) :=
    section8_subgroupPrimeSet_mono hX_le_msigma hqX
  exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card q hqMsigma

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_normalizer_le_normalizer_centralizer
    (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro p hp
    have hpn : n⁻¹ * p * n ∈ P := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (P : Set G)).inv_mem hn) p).1 hp
    have hcomm : (n⁻¹ * p * n) * c = c * (n⁻¹ * p * n) := hc _ hpn
    have hcomm' := congrArg (fun x : G => n * x * n⁻¹) hcomm
    simpa [mul_assoc] using hcomm'
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro p hp
    have hpn : n * p * n⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hn p).1 hp
    have hcomm :
        (n * p * n⁻¹) * (n * c * n⁻¹) =
          (n * c * n⁻¹) * (n * p * n⁻¹) :=
      hc _ hpn
    have hcomm' := congrArg (fun x : G => n⁻¹ * x * n) hcomm
    simpa [mul_assoc] using hcomm'

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_le_normalizer_map_of_isInvariant
    {A H : Subgroup G} {K : Subgroup H}
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) :
    haveI : Subgroup.Normalizes A H := ⟨hAH⟩
    IsInvariant (↥A) (↥H) K →
    A ≤ Subgroup.normalizer (K.map H.subtype : Set G) := by
  intro hKinv
  haveI : Subgroup.Normalizes A H := ⟨hAH⟩
  letI : IsInvariant (↥A) (↥H) K := hKinv
  refine subgroup_le_normalizer_of_conj_mem (K.map H.subtype) A ?_
  intro a x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  have hyInv : a • y ∈ K :=
    (IsInvariant.invariant (A := ↥A) (G := ↥H) (H := K) a y).1 hy
  exact Subgroup.mem_map.mpr ⟨a • y, hyInv, by
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]⟩

private theorem CFSG.section13_theorem_13_4_exists_pr_invariant_sylow
    {M E E₁₂ E₁ E₂ E₃ P R : Subgroup G} {p r q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hqX : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) P)) :
    ∃ hAX : Subgroup.Normalizes (P ⊔ R) (subgroupCentralizerIn (section10Msigma M) P),
    letI : Subgroup.Normalizes (P ⊔ R) (subgroupCentralizerIn (section10Msigma M) P) := hAX
    ∃ S : Sylow q.val (subgroupCentralizerIn (section10Msigma M) P),
      IsInvariant (↥(P ⊔ R)) (↥(subgroupCentralizerIn (section10Msigma M) P))
        (S : Subgroup (subgroupCentralizerIn (section10Msigma M) P)) := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let X : Subgroup G := subgroupCentralizerIn (section10Msigma M) P
  let A : Subgroup G := P ⊔ R
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPE, _hPcard⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR) with
    ⟨hR_le_CEP, _hRcard⟩
  have hR_le_E : R ≤ E := hR_le_CEP.trans inf_le_left
  have hR_le_centP : R ≤ Subgroup.centralizer (P : Set G) :=
    hR_le_CEP.trans inf_le_right
  have hA_le_E : A ≤ E := by
    dsimp [A]
    exact sup_le hPE hR_le_E
  have hE_le_M : E ≤ M := hE.1.2.1
  have hA_le_M : A ≤ M := hA_le_E.trans hE_le_M
  have hA_norm_msigma :
      A ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hA_le_M.trans section13_le_normalizer_msigma
  have hA_norm_P : A ≤ Subgroup.normalizer (P : Set G) := by
    dsimp [A]
    exact sup_le Subgroup.le_normalizer
      (hR_le_centP.trans (centralizer_le_normalizer P))
  have hA_norm_centP :
      A ≤ Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) :=
    hA_norm_P.trans (section13_normalizer_le_normalizer_centralizer (G := G) P)
  have hA_norm_X : A ≤ Subgroup.normalizer (X : Set G) := by
    simpa [X, subgroupCentralizerIn] using
      section13_le_normalizer_inf
        (G := G) (A := A) (H := section10Msigma M)
        (K := Subgroup.centralizer (P : Set G)) hA_norm_msigma hA_norm_centP
  have hX_le_msigma : X ≤ section10Msigma M := by
    dsimp [X, subgroupCentralizerIn]
    exact inf_le_left
  have hXπsub : IsPiSubgroup (G := G) (section10SigmaPrimes M) X := by
    intro s hsX
    exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card s
      (hsX.trans (Subgroup.card_dvd_of_le hX_le_msigma))
  have hXπ : IsPiGroup (section10SigmaPrimes M) X :=
    IsPiSubgroup.isPiGroup X hXπsub
  have hEπsub : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ E := by
    intro s hsE
    have hcard : Nat.card (E.subgroupOf M) = Nat.card E :=
      natCard_subgroupOf_eq E M hE_le_M
    have hsEsub : s.val ∣ Nat.card (E.subgroupOf M) := by
      simpa [hcard] using hsE
    exact (section12_msigma_complement_isHall_sigma_compl
      (G := G) hM hE.1).p_in_pi_of_p_dvd_card s hsEsub
  have hAπsub : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ A := by
    intro s hsA
    exact hEπsub s (hsA.trans (Subgroup.card_dvd_of_le hA_le_E))
  have hAπ : IsPiGroup (section10SigmaPrimes M)ᶜ A :=
    IsPiSubgroup.isPiGroup A hAπsub
  have hMsigma_le_M : section10Msigma M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hX_le_M : X ≤ M := hX_le_msigma.trans hMsigma_le_M
  have hX_ne_top : X ≠ ⊤ := by
    intro hXtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hXtop] using hX_le_M
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hXsolv : IsSolvable X :=
    IsMinCE.proper_subgroups_solvable X (lt_top_iff_ne_top.2 hX_ne_top)
  have hqσ : q ∈ section10SigmaPrimes M :=
    section13_sigma_of_mem_centralizer_msigma (G := G) hM hqX
  have hAX : Subgroup.Normalizes A X := ⟨hA_norm_X⟩
  refine ⟨by simpa [X, A] using hAX, ?_⟩
  letI : Subgroup.Normalizes A X := hAX
  have hq_eq : (⟨q.val, Fact.out⟩ : Nat.Primes) = q := by
    ext
    rfl
  simpa [X, A] using
    exists_invariant_sylow_of_pi_complement_action
      (G := X) (A := A) (π := section10SigmaPrimes M) (p := q.val)
      hXπ hAπ hXsolv (by rw [hq_eq]; exact hqσ)

private theorem CFSG.section13_theorem_13_4_centralizes_of_not_tau1_star
    {M E E₁₂ E₁ E₂ E₃ P R Mstar : Subgroup G} {p r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining
      (Subgroup.normalizer (P : Set G)))
    (hr_notτ1star : r ∉ section12Tau1Primes Mstar) :
    subgroupCentralizerIn (section10Msigma M) P ≤ Subgroup.centralizer (R : Set G) := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPE, hPcard⟩
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  have hE_le_M : E ≤ M := hE.1.2.1
  have hPM : P ≤ M := hPE.trans hE_le_M
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR) with
    ⟨hR_le_CEP, hRcard⟩
  have hRp : IsPGroup r.val R := by
    refine IsPGroup.of_card (p := r.val) (G := R) (n := 1) ?_
    simpa [pow_one] using hRcard
  have hR_le_E : R ≤ E := hR_le_CEP.trans inf_le_left
  have hR_le_centP : R ≤ Subgroup.centralizer (P : Set G) :=
    hR_le_CEP.trans inf_le_right
  have hR_le_Mstar : R ≤ Mstar := by
    intro x hx
    exact hMstar.2 ((centralizer_le_normalizer P) (hR_le_centP hx))
  have hR_le_inf : R ≤ E ⊓ Mstar := le_inf hR_le_E hR_le_Mstar
  have hRπc : IsPiSubgroup (G := G) (section12Tau1Primes Mstar)ᶜ R :=
    section13_isPiSubgroup_compl_of_isPGroup_not_mem hr_notτ1star hRp
  have hR_cent :
      R ≤ Subgroup.centralizer (section10Msigma M ⊓ Mstar : Set G) :=
    corollary_13_2_b (G := G) hM hE (Or.inl hpτ1)
      hPp hPne hPM hMstar R hR_le_inf hRπc
  have hInf_cent_R :
      section10Msigma M ⊓ Mstar ≤ Subgroup.centralizer (R : Set G) :=
    (Subgroup.le_centralizer_iff
      (H := R) (K := section10Msigma M ⊓ Mstar)).mp hR_cent
  intro x hx
  have hxMstar : x ∈ Mstar :=
    hMstar.2 ((centralizer_le_normalizer P) hx.2)
  exact hInf_cent_R ⟨hx.1, hxMstar⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_theorem_13_4_big_commutator_ne_of_sylow_commutator_ne
    {M E E₁₂ E₁ E₂ E₃ P R Mstar : Subgroup G} {p r q : Nat.Primes}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (_hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining
      (Subgroup.normalizer (P : Set G)))
    (S : Sylow q.val (subgroupCentralizerIn (section10Msigma M) P))
    (hcomm :
      ⁅(S : Subgroup (subgroupCentralizerIn (section10Msigma M) P)).map
          (subgroupCentralizerIn (section10Msigma M) P).subtype, R⁆ ≠ ⊥) :
    ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥ := by
  classical
  intro hbig
  apply hcomm
  apply le_bot_iff.mp
  rw [← hbig]
  have hS_le_inf :
      (S : Subgroup (subgroupCentralizerIn (section10Msigma M) P)).map
          (subgroupCentralizerIn (section10Msigma M) P).subtype ≤
        section10Msigma M ⊓ Mstar := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨s, _hs, rfl⟩
    have hsX : (s : G) ∈ subgroupCentralizerIn (section10Msigma M) P := s.property
    exact ⟨hsX.1, hMstar.2 ((centralizer_le_normalizer P) hsX.2)⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR) with
    ⟨hR_le_CEP, _hRcard⟩
  have hR_le_E : R ≤ E := hR_le_CEP.trans inf_le_left
  have hR_le_centP : R ≤ Subgroup.centralizer (P : Set G) :=
    hR_le_CEP.trans inf_le_right
  have hR_le_M : R ≤ M := hR_le_E.trans hE.1.2.1
  have hR_le_Mstar : R ≤ Mstar := by
    intro x hx
    exact hMstar.2 ((centralizer_le_normalizer P) (hR_le_centP hx))
  exact Subgroup.commutator_mono hS_le_inf (le_inf hR_le_M hR_le_Mstar)

private theorem CFSG.section13_theorem_13_4_p_mem_beta_star_of_sylow_commutator_ne
    {M E E₁₂ E₁ E₂ E₃ P R Mstar : Subgroup G} {p r q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining
      (Subgroup.normalizer (P : Set G)))
    (S : Sylow q.val (subgroupCentralizerIn (section10Msigma M) P))
    (hcomm :
      ⁅(S : Subgroup (subgroupCentralizerIn (section10Msigma M) P)).map
          (subgroupCentralizerIn (section10Msigma M) P).subtype, R⁆ ≠ ⊥) :
    p ∈ section10BetaPrimes Mstar := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPE, hPcard⟩
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  have hPM : P ≤ M := hPE.trans hE.1.2.1
  have hbig :
      ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥ :=
    section13_theorem_13_4_big_commutator_ne_of_sylow_commutator_ne
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (Mstar := Mstar)
      (p := p) (r := r) (q := q) hE hP hR hMstar S hcomm
  exact
    (corollary_13_2_c (G := G) hM hE (Or.inl hpτ1)
      hPp hPne hPM hMstar hbig).2 hpτ1

private theorem CFSG.section13_theorem_13_4_p_mem_beta_star_of_commutator_ne
    {M E E₁₂ E₁ E₂ E₃ P R Mstar Sg : Subgroup G} {p r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining
      (Subgroup.normalizer (P : Set G)))
    (hSg_le_X : Sg ≤ subgroupCentralizerIn (section10Msigma M) P)
    (hcomm : ⁅Sg, R⁆ ≠ ⊥) :
    p ∈ section10BetaPrimes Mstar := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPE, hPcard⟩
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  have hPM : P ≤ M := hPE.trans hE.1.2.1
  have hbig :
      ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥ := by
    intro hbig
    apply hcomm
    apply le_bot_iff.mp
    rw [← hbig]
    have hSg_le_Mstar : Sg ≤ Mstar := by
      intro x hx
      have hxX : x ∈ subgroupCentralizerIn (section10Msigma M) P := hSg_le_X hx
      exact hMstar.2 ((centralizer_le_normalizer P) (by
        simpa [subgroupCentralizerIn] using hxX.2))
    have hSg_le_inf : Sg ≤ section10Msigma M ⊓ Mstar := by
      intro x hx
      exact ⟨(hSg_le_X hx).1, hSg_le_Mstar hx⟩
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR) with
      ⟨hR_le_CEP, _hRcard⟩
    have hR_le_E : R ≤ E := hR_le_CEP.trans inf_le_left
    have hR_le_centP : R ≤ Subgroup.centralizer (P : Set G) :=
      hR_le_CEP.trans inf_le_right
    have hR_le_M : R ≤ M := hR_le_E.trans hE.1.2.1
    have hR_le_Mstar : R ≤ Mstar := by
      intro x hx
      exact hMstar.2 ((centralizer_le_normalizer P) (hR_le_centP hx))
    exact Subgroup.commutator_mono hSg_le_inf (le_inf hR_le_M hR_le_Mstar)
  exact
    (corollary_13_2_c (G := G) hM hE (Or.inl hpτ1)
      hPp hPne hPM hMstar hbig).2 hpτ1

private theorem CFSG.section13_theorem_13_4_noncentral_pgroup_not_alpha
    {M E E₁₂ E₁ E₂ E₃ P R Mstar Sg : Subgroup G} {p r q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hrE : r ∈ subgroupPrimeSet E)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hqX : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) P))
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining
      (Subgroup.normalizer (P : Set G)))
    (hrτ1star : r ∈ section12Tau1Primes Mstar)
    (hSg_le_X : Sg ≤ subgroupCentralizerIn (section10Msigma M) P)
    (hSgq : IsPGroup q.val Sg)
    (hR_norm_Sg : R ≤ Subgroup.normalizer (Sg : Set G))
    (hcomm : ⁅Sg, R⁆ ≠ ⊥) :
    q ∉ section10AlphaPrimes M := by
  classical
  let Q : Subgroup G := ⁅Sg, R⁆
  have hpβstar : p ∈ section10BetaPrimes Mstar :=
    section13_theorem_13_4_p_mem_beta_star_of_commutator_ne
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (Mstar := Mstar)
      (Sg := Sg) (p := p) (r := r)
      hM hE hpτ1 hP hR hMstar hSg_le_X hcomm
  have hQ_ne : Q ≠ ⊥ := by
    simpa [Q] using hcomm
  have hQ_le_Sg : Q ≤ Sg := by
    simpa [Q] using section13_commutator_le_left_of_le_normalizer hR_norm_Sg
  have hX_le_msigma :
      subgroupCentralizerIn (section10Msigma M) P ≤ section10Msigma M :=
    inf_le_left
  have hMsigma_le_M : section10Msigma M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hSg_le_M : Sg ≤ M := hSg_le_X.trans (hX_le_msigma.trans hMsigma_le_M)
  have hQ_le_M : Q ≤ M := hQ_le_Sg.trans hSg_le_M
  have hSg_le_Mstar : Sg ≤ Mstar := by
    intro x hx
    have hxX : x ∈ subgroupCentralizerIn (section10Msigma M) P := hSg_le_X hx
    exact hMstar.2 ((centralizer_le_normalizer P) (by
      simpa [subgroupCentralizerIn] using hxX.2))
  have hQ_le_Mstar : Q ≤ Mstar := hQ_le_Sg.trans hSg_le_Mstar
  have hQq : IsPGroup q.val Q :=
    section13_isPGroup_of_le_pSubgroup (G := G) hSgq hQ_le_Sg
  have hSR_norm_Q : Sg ⊔ R ≤ Subgroup.normalizer (Q : Set G) := by
    have hQ_norm_sup : (Q.subgroupOf (Sg ⊔ R : Subgroup G)).Normal := by
      simpa [Q] using commutator_normal_in_sup Sg R
    have hQ_le_sup : Q ≤ Sg ⊔ R := by
      simpa [Q] using commutator_le_sup Sg R
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := Q) (K := Sg ⊔ R) hQ_le_sup).mp hQ_norm_sup
  have hR_norm_Q : R ≤ Subgroup.normalizer (Q : Set G) :=
    le_sup_right.trans hSR_norm_Q
  have hqσ : q ∈ section10SigmaPrimes M :=
    section13_sigma_of_mem_centralizer_msigma (G := G) hM hqX
  have hqr : q ≠ r :=
    (section13_ne_of_sigma_and_mem_E (G := G) hM hE hrE hqσ).symm
  have hq_pPrime_r : q ∈ section10PPrimeSet r := by
    rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hqr
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hP_le_E, hPcard⟩
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  have hP_le_M : P ≤ M := hP_le_E.trans hE.1.2.1
  have hnotconj_star_M : section12NotConjugate Mstar M :=
    lemma_12_2_b (G := G) (M := M) (Mstar := Mstar) (X := P) (p := p)
      hM hPp hPne hP_le_M hMstar (Or.inr (Or.inl hpτ1))
  have hMstar_ne_M : Mstar ≠ M := by
    intro hEq
    exact hnotconj_star_M 1 (by simpa [hEq] using section8_conjBy_one (G := G) Mstar)
  have hSg_comm : IsMulCommutative Sg := by
    by_contra hnon
    exact
      (section13_not_unique_of_le_two_distinct_maximal
        (G := G) hM hMstar.1 hSg_le_M hSg_le_Mstar hMstar_ne_M)
        (theorem_12_13 (G := G) (P := Sg) (p := q) hSgq hnon)
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR) with
    ⟨hR_le_CEP, hRcard⟩
  have hRr : IsPGroup r.val R := by
    refine IsPGroup.of_card (p := r.val) (G := R) (n := 1) ?_
    simpa [pow_one] using hRcard
  have hRπ : IsPiSubgroup (G := G) ({r} : Set Nat.Primes) R :=
    section8_isPiSubgroup_singleton_of_isPGroup hRr
  have hSgπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Sg :=
    section8_isPiSubgroup_singleton_of_isPGroup hSgq
  have hdis_rq : Disjoint ({r} : Set Nat.Primes) ({q} : Set Nat.Primes) := by
    rw [Set.disjoint_left]
    intro s hsr hsq
    have hsr_eq : s = r := by simpa using hsr
    have hsq_eq : s = q := by simpa using hsq
    exact hqr (hsq_eq.symm.trans hsr_eq)
  have hcop_RSg : Nat.Coprime (Nat.card R) (Nat.card Sg) :=
    section13_coprime_card_of_isPiSubgroup_disjoint_primes
      (G := G) hRπ hSgπ hdis_rq
  have hCQ_bot : subgroupCentralizerIn Q R = ⊥ := by
    simpa [Q] using
      section13_commutator_centralizerIn_eq_bot_of_coprime
        (G := G) (K := Sg) (P := R) hR_norm_Sg hcop_RSg hSg_comm
  have hR_le_Mstar : R ≤ Mstar := by
    intro x hx
    exact hMstar.2 ((centralizer_le_normalizer P) ((hR_le_CEP hx).2))
  have hrMstar : r ∈ subgroupPrimeSet Mstar :=
    section8_subgroupPrimeSet_mono hR_le_Mstar (by
      rw [subgroupPrimeSet, hRcard]
      exact dvd_rfl)
  have hR_prime_Mstar : R ∈ section10PrimeOrderSubgroupsIn r Mstar := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hR_le_Mstar, hRcard⟩
  have hpαstar : p ∈ section10AlphaPrimes Mstar := hpβstar.1
  have hMstarα_ne : section10Malpha Mstar ≠ ⊥ := by
    intro hαbot
    have hHallα : IsHallSubgroup (section10AlphaPrimes Mstar) (section10Malpha Mstar) :=
      (theorem_10_2_a (G := G) hMstar.1).1
    have hpG : p.val ∣ Nat.card G :=
      hpαstar.1.trans (Subgroup.card_subgroup_dvd_card Mstar)
    have hindex_mul : (section10Malpha Mstar).index * Nat.card (section10Malpha Mstar) =
        Nat.card G :=
      Subgroup.index_mul_card (H := section10Malpha Mstar)
    have hp_prod : p.val ∣ (section10Malpha Mstar).index *
        Nat.card (section10Malpha Mstar) := by
      simpa [hindex_mul] using hpG
    rcases p.property.dvd_mul.mp hp_prod with hpidx | hpαcard
    · exact (hHallα.p_in_pi_of_p_dvd_index p hpidx) hpαstar
    have hp_dvd_α : p.val ∣ Nat.card (section10Malpha Mstar) := hpαcard
    rw [hαbot] at hp_dvd_α
    exact p.property.not_dvd_one (by simpa using hp_dvd_α)
  have hq_notαstar : q ∉ section10AlphaPrimes Mstar := by
    have hdis : Disjoint (section10AlphaPrimes Mstar) (section10SigmaPrimes M) :=
      (lemma_10_12_a (G := G) (M := Mstar) (H := M) hMstar.1 hM
        (section13_notConjugate_symm hnotconj_star_M)).2
    rw [Set.disjoint_left] at hdis
    intro hqαstar
    exact hdis hqαstar hqσ
  have hP_le_Mstar : P ≤ Mstar :=
    Subgroup.le_normalizer.trans hMstar.2
  have hPsub_p : IsPGroup p.val (P.subgroupOf Mstar) :=
    hPp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := P) (K := Mstar) hP_le_Mstar).symm
  have hPsub_le_beta :
      P.subgroupOf Mstar ≤ section10MbetaSubgroup Mstar :=
    section13_pSubgroup_le_normal_hall_of_prime_mem
      (R := Mstar) (π := section10BetaPrimes Mstar)
      (H := section10MbetaSubgroup Mstar) (A := P.subgroupOf Mstar)
      (p := p) (lemma_10_8_a (G := G) hMstar.1).2 hpβstar hPsub_p
  have hP_le_Mbeta_star : P ≤ section10Mbeta Mstar := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hP_le_Mstar hx⟩, by
        exact hPsub_le_beta (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hP_le_Malpha_star : P ≤ section10Malpha Mstar :=
    hP_le_Mbeta_star.trans (section13_mbeta_le_malpha (G := G) Mstar)
  have hP_le_Msigma_star : P ≤ section10Msigma Mstar :=
    hP_le_Malpha_star.trans (section13_malpha_le_msigma (G := G) hMstar.1)
  have hR_le_centP : R ≤ Subgroup.centralizer (P : Set G) :=
    hR_le_CEP.trans inf_le_right
  have hQ_le_centP : Q ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    exact (hSg_le_X (hQ_le_Sg hx)).2
  have hRQ_le_centP : R ⊔ Q ≤ Subgroup.centralizer (P : Set G) :=
    sup_le hR_le_centP hQ_le_centP
  have hP_le_cent_RQ : P ≤ Subgroup.centralizer ((R ⊔ Q : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff (H := R ⊔ Q) (K := P)).mp hRQ_le_centP
  have hP_le_Calpha_RQ :
      P ≤ subgroupCentralizerIn (section10Malpha Mstar) (R ⊔ Q) := by
    intro x hx
    exact ⟨hP_le_Malpha_star hx, hP_le_cent_RQ hx⟩
  have hUniqueStar :
      section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) = {Mstar} := by
    by_contra hnotUnique
    have h1218 :
        subgroupCentralizerIn (section10Malpha Mstar) R ≠ ⊥ ∧
          subgroupCentralizerIn (section10Malpha Mstar) (R ⊔ Q) = ⊥ :=
      lemma_12_18_a (G := G) (M := Mstar) (P := R) (Q := Q)
        (p := r) (q := q) hMstar.1 hrτ1star hR_prime_Mstar hq_pPrime_r
        hQ_le_Mstar hQ_ne hQq hR_norm_Q hCQ_bot hnotUnique
        hMstarα_ne hq_notαstar
    have hP_le_bot : P ≤ (⊥ : Subgroup G) := by
      intro x hx
      have hxC : x ∈ subgroupCentralizerIn (section10Malpha Mstar) (R ⊔ Q) :=
        hP_le_Calpha_RQ hx
      simpa [h1218.2] using hxC
    exact hPne (le_bot_iff.mp hP_le_bot)
  have hMstarQ :
      Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) := by
    rw [hUniqueStar]
    simp
  have hQ_le_inf : Q ≤ M ⊓ Mstar :=
    le_inf hQ_le_M hQ_le_Mstar
  have hQsub_p : IsPGroup q.val (Q.subgroupOf (M ⊓ Mstar : Subgroup G)) :=
    hQq.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := Q) (K := M ⊓ Mstar) hQ_le_inf).symm
  obtain ⟨T, hQsub_le_T⟩ :=
    IsPGroup.exists_le_sylow (G := (M ⊓ Mstar : Subgroup G)) (p := q.val) hQsub_p
  have hQ_le_Tamb : Q ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) T := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hQ_le_inf hx⟩, hQsub_le_T (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hqσstar : q ∈ section10SigmaPrimes Mstar := by
    by_contra hq_notσstar
    rcases proposition_12_15_e (G := G) (M := M) (Mstar := Mstar) (X := Q)
        (q := q) (S := T) hM hqσ hQ_le_M hQ_ne hQq hMstarQ
        hMstar_ne_M hQ_le_Tamb hq_notσstar with
      ⟨_hqτ2star, _hbeta_transfer, hcompl⟩
    rcases hcompl with ⟨_hσ_le_star, _hinf_le_star, _hstar_join, hdisj⟩
    have hP_le_bot : P ≤ (⊥ : Subgroup G) := by
      intro x hx
      have hxinf : x ∈ section10Msigma Mstar ⊓ (M ⊓ Mstar : Subgroup G) :=
        ⟨hP_le_Msigma_star hx, ⟨hP_le_M hx, hP_le_Mstar hx⟩⟩
      simpa [hdisj.eq_bot] using hxinf
    exact hPne (le_bot_iff.mp hP_le_bot)
  have hdis : Disjoint (section10AlphaPrimes M) (section10SigmaPrimes Mstar) :=
    (lemma_10_12_a (G := G) (M := M) (H := Mstar) hM hMstar.1
      hnotconj_star_M).2
  rw [Set.disjoint_left] at hdis
  intro hqα
  exact hdis hqα hqσstar

private theorem CFSG.section13_malpha_exists_pr_invariant_sylow
    {M E E₁₂ E₁ E₂ E₃ P R : Subgroup G} {p r q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hrτ1 : r ∈ section12Tau1Primes M)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hqX : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Malpha M) P)) :
    ∃ hAX : Subgroup.Normalizes (P ⊔ R) (subgroupCentralizerIn (section10Malpha M) P),
    letI : Subgroup.Normalizes (P ⊔ R) (subgroupCentralizerIn (section10Malpha M) P) := hAX
    ∃ S : Sylow q.val (subgroupCentralizerIn (section10Malpha M) P),
      IsInvariant (↥(P ⊔ R)) (↥(subgroupCentralizerIn (section10Malpha M) P))
        (S : Subgroup (subgroupCentralizerIn (section10Malpha M) P)) := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let X : Subgroup G := subgroupCentralizerIn (section10Malpha M) P
  let A : Subgroup G := P ⊔ R
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPE, hPcard⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR) with
    ⟨hR_le_CEP, hRcard⟩
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  have hRr : IsPGroup r.val R := by
    refine IsPGroup.of_card (p := r.val) (G := R) (n := 1) ?_
    simpa [pow_one] using hRcard
  have hP_notα : p ∉ section10AlphaPrimes M := by
    rcases (by simpa [section12Tau1Primes] using hpτ1) with
      ⟨hp_notσ, _hpD, _hrank⟩
    intro hpα
    exact hp_notσ (section13_sigmaPrimes_mem_of_alphaPrimes_mem (G := G) hM hpα)
  have hR_notα : r ∉ section10AlphaPrimes M := by
    rcases (by simpa [section12Tau1Primes] using hrτ1) with
      ⟨hr_notσ, _hrD, _hrank⟩
    intro hrα
    exact hr_notσ (section13_sigmaPrimes_mem_of_alphaPrimes_mem (G := G) hM hrα)
  have hPπc : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ P :=
    section13_isPiSubgroup_compl_of_isPGroup_not_mem hP_notα hPp
  have hRπc : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ R :=
    section13_isPiSubgroup_compl_of_isPGroup_not_mem hR_notα hRr
  have hR_le_E : R ≤ E := hR_le_CEP.trans inf_le_left
  have hR_le_centP : R ≤ Subgroup.centralizer (P : Set G) :=
    hR_le_CEP.trans inf_le_right
  have hP_le_centR : P ≤ Subgroup.centralizer (R : Set G) :=
    (Subgroup.le_centralizer_iff (H := R) (K := P)).mp hR_le_centP
  have hP_norm_R : P ≤ Subgroup.normalizer (R : Set G) :=
    hP_le_centR.trans (centralizer_le_normalizer R)
  have hA_le_E : A ≤ E := by
    dsimp [A]
    exact sup_le hPE hR_le_E
  have hA_le_M : A ≤ M := hA_le_E.trans hE.1.2.1
  have hA_norm_malpha :
      A ≤ Subgroup.normalizer (section10Malpha M : Set G) :=
    hA_le_M.trans (section13_le_normalizer_malpha (G := G))
  have hA_norm_P : A ≤ Subgroup.normalizer (P : Set G) := by
    dsimp [A]
    exact sup_le Subgroup.le_normalizer
      (hR_le_centP.trans (centralizer_le_normalizer P))
  have hA_norm_centP :
      A ≤ Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) :=
    hA_norm_P.trans (section13_normalizer_le_normalizer_centralizer (G := G) P)
  have hA_norm_X : A ≤ Subgroup.normalizer (X : Set G) := by
    simpa [X, subgroupCentralizerIn] using
      section13_le_normalizer_inf
        (G := G) (A := A) (H := section10Malpha M)
        (K := Subgroup.centralizer (P : Set G)) hA_norm_malpha hA_norm_centP
  have hX_le_malpha : X ≤ section10Malpha M := by
    dsimp [X, subgroupCentralizerIn]
    exact inf_le_left
  have hXπsub : IsPiSubgroup (G := G) (section10AlphaPrimes M) X := by
    intro s hsX
    exact ((theorem_10_2_a (G := G) hM).1).p_in_pi_of_p_dvd_card s
      (hsX.trans (Subgroup.card_dvd_of_le hX_le_malpha))
  have hXπ : IsPiGroup (section10AlphaPrimes M) X :=
    IsPiSubgroup.isPiGroup X hXπsub
  have hAπsub : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ A := by
    simpa [A] using
      section13_isPiSubgroup_sup_of_le_normalizer
        (G := G) (π := (section10AlphaPrimes M)ᶜ) (H := P) (K := R)
        hPπc hRπc hP_norm_R
  have hAπ : IsPiGroup (section10AlphaPrimes M)ᶜ A :=
    IsPiSubgroup.isPiGroup A hAπsub
  have hMalpha_le_M : section10Malpha M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hX_le_M : X ≤ M := hX_le_malpha.trans hMalpha_le_M
  have hX_ne_top : X ≠ ⊤ := by
    intro hXtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hXtop] using hX_le_M
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hXsolv : IsSolvable X :=
    IsMinCE.proper_subgroups_solvable X (lt_top_iff_ne_top.2 hX_ne_top)
  have hqα : q ∈ section10AlphaPrimes M := hXπsub q hqX
  have hAX : Subgroup.Normalizes A X := ⟨hA_norm_X⟩
  refine ⟨by simpa [X, A] using hAX, ?_⟩
  letI : Subgroup.Normalizes A X := hAX
  have hq_eq : (⟨q.val, Fact.out⟩ : Nat.Primes) = q := by
    ext
    rfl
  simpa [X, A] using
    exists_invariant_sylow_of_pi_complement_action
      (G := X) (A := A) (π := section10AlphaPrimes M) (p := q.val)
      hXπ hAπ hXsolv (by rw [hq_eq]; exact hqα)

private theorem CFSG.section13_malpha_pr_invariant_sylow_centralizes
    {M E E₁₂ E₁ E₂ E₃ P R Mstar : Subgroup G} {p r q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hrE : r ∈ subgroupPrimeSet E)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hqXσ : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) P))
    (hqα : q ∈ section10AlphaPrimes M)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining
      (Subgroup.normalizer (P : Set G)))
    (hrτ1star : r ∈ section12Tau1Primes Mstar)
    [Subgroup.Normalizes (P ⊔ R) (subgroupCentralizerIn (section10Malpha M) P)]
    (S : Sylow q.val (subgroupCentralizerIn (section10Malpha M) P))
    (hSinv : IsInvariant (↥(P ⊔ R))
      (↥(subgroupCentralizerIn (section10Malpha M) P))
      (S : Subgroup (subgroupCentralizerIn (section10Malpha M) P))) :
    (S : Subgroup (subgroupCentralizerIn (section10Malpha M) P)).map
        (subgroupCentralizerIn (section10Malpha M) P).subtype ≤
          Subgroup.centralizer (R : Set G) := by
  classical
  let Xα : Subgroup G := subgroupCentralizerIn (section10Malpha M) P
  let Sg : Subgroup G := (S : Subgroup Xα).map Xα.subtype
  by_cases hcomm : ⁅Sg, R⁆ = ⊥
  · simpa [Sg, Xα] using
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Sg) (H₂ := R)).mp
        hcomm
  · exfalso
    have hPR_norm_Xα : P ⊔ R ≤ Subgroup.normalizer (Xα : Set G) :=
      Subgroup.Normalizes.le_normalizer
    have hPR_norm_Sg : P ⊔ R ≤ Subgroup.normalizer (Sg : Set G) := by
      simpa [Sg, Xα] using
        section13_le_normalizer_map_of_isInvariant
          (G := G) (A := P ⊔ R) (H := Xα) (K := (S : Subgroup Xα))
          hPR_norm_Xα (by simpa [Xα] using hSinv)
    have hR_norm_Sg : R ≤ Subgroup.normalizer (Sg : Set G) :=
      le_sup_right.trans hPR_norm_Sg
    have hSgq : IsPGroup q.val Sg := by
      change IsPGroup q.val ((S : Subgroup Xα).map Xα.subtype)
      exact IsPGroup.map (p := q.val) (H := (S : Subgroup Xα))
        S.isPGroup' Xα.subtype
    have hXα_le_Xσ :
        Xα ≤ subgroupCentralizerIn (section10Msigma M) P := by
      intro x hx
      exact ⟨section13_malpha_le_msigma (G := G) hM hx.1, hx.2⟩
    have hSg_le_Xσ : Sg ≤ subgroupCentralizerIn (section10Msigma M) P := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨s, _hs, rfl⟩
      exact hXα_le_Xσ s.property
    have hq_notα : q ∉ section10AlphaPrimes M :=
      section13_theorem_13_4_noncentral_pgroup_not_alpha
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (P := P) (R := R)
        (Mstar := Mstar) (Sg := Sg) (p := p) (r := r) (q := q)
        hM hE hpτ1 hP hrE hR hqXσ hMstar hrτ1star
        hSg_le_Xσ hSgq hR_norm_Sg (by simpa [Sg] using hcomm)
    exact hq_notα hqα

private theorem CFSG.section13_malpha_centralizer_le_of_tau1_prime_order_pair
    {M E E₁₂ E₁ E₂ E₃ P R : Subgroup G} {p r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hrτ1 : r ∈ section12Tau1Primes M)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P)) :
    subgroupCentralizerIn (section10Malpha M) P ≤
      subgroupCentralizerIn (section10Malpha M) R := by
  classical
  let Xα : Subgroup G := subgroupCentralizerIn (section10Malpha M) P
  have hXα_le_Xσ : Xα ≤ subgroupCentralizerIn (section10Msigma M) P := by
    intro x hx
    exact ⟨section13_malpha_le_msigma (G := G) hM hx.1, hx.2⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPE, hPcard⟩
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  have hPM : P ≤ M := hPE.trans hE.1.2.1
  have hnormP_ne_top :
      Subgroup.normalizer (P : Set G) ≠ ⊤ :=
    section13_normalizer_ne_top_of_ne_bot_le_maximal hM hPM hPne
  rcases section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) hnormP_ne_top with
    ⟨Mstar, hMstar⟩
  have hrE : r ∈ subgroupPrimeSet E := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR) with
      ⟨hR_le_CEP, hRcard⟩
    exact section8_subgroupPrimeSet_mono (hR_le_CEP.trans inf_le_left) (by
      rw [subgroupPrimeSet, hRcard]
      exact dvd_rfl)
  have hcent : Xα ≤ Subgroup.centralizer (R : Set G) := by
    apply section13_le_centralizer_of_exists_sylow_images
    intro q hqXα
    have hqXσ : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) P) :=
      section8_subgroupPrimeSet_mono hXα_le_Xσ hqXα
    by_cases hrτ1star : r ∈ section12Tau1Primes Mstar
    · have hqα : q ∈ section10AlphaPrimes M :=
        ((theorem_10_2_a (G := G) hM).1).p_in_pi_of_p_dvd_card q
          (hqXα.trans (Subgroup.card_dvd_of_le (by
            dsimp [Xα, subgroupCentralizerIn]
            exact inf_le_left)))
      rcases section13_malpha_exists_pr_invariant_sylow
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) (P := P) (R := R)
          (p := p) (r := r) (q := q) hM hE hpτ1 hP hrτ1 hR hqXα with
        ⟨hAX, S, hSinv⟩
      letI : Subgroup.Normalizes (P ⊔ R) Xα := by
        simpa [Xα] using hAX
      refine ⟨S, ?_⟩
      simpa [Xα] using
        section13_malpha_pr_invariant_sylow_centralizes
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (Mstar := Mstar)
          (p := p) (r := r) (q := q)
          hM hE hpτ1 hP hrE hR hqXσ hqα hMstar hrτ1star S hSinv
    · have hcentσ :
          subgroupCentralizerIn (section10Msigma M) P ≤
            Subgroup.centralizer (R : Set G) :=
        section13_theorem_13_4_centralizes_of_not_tau1_star
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (Mstar := Mstar)
          (p := p) (r := r) hM hE hpτ1 hP hR hMstar hrτ1star
      let S : Sylow q.val Xα := default
      refine ⟨S, ?_⟩
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨s, _hs, rfl⟩
      exact hcentσ (hXα_le_Xσ s.property)
  intro x hx
  exact ⟨hx.1, hcent hx⟩

private theorem CFSG.section13_theorem_13_4_pr_invariant_sylow_noncentral_absurd
    {M E E₁₂ E₁ E₂ E₃ P R Mstar : Subgroup G} {p r q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hrE : r ∈ subgroupPrimeSet E)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hqX : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) P))
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining
      (Subgroup.normalizer (P : Set G)))
    (hrτ1star : r ∈ section12Tau1Primes Mstar)
    [Subgroup.Normalizes (P ⊔ R) (subgroupCentralizerIn (section10Msigma M) P)]
    (S : Sylow q.val (subgroupCentralizerIn (section10Msigma M) P))
    (hSinv : IsInvariant (↥(P ⊔ R))
      (↥(subgroupCentralizerIn (section10Msigma M) P))
      (S : Subgroup (subgroupCentralizerIn (section10Msigma M) P)))
    (hcomm :
      ⁅(S : Subgroup (subgroupCentralizerIn (section10Msigma M) P)).map
          (subgroupCentralizerIn (section10Msigma M) P).subtype, R⁆ ≠ ⊥) :
    False := by
  classical
  let X : Subgroup G := subgroupCentralizerIn (section10Msigma M) P
  let Sg : Subgroup G := (S : Subgroup X).map X.subtype
  let Q : Subgroup G := ⁅Sg, R⁆
  have hpβstar : p ∈ section10BetaPrimes Mstar :=
    section13_theorem_13_4_p_mem_beta_star_of_sylow_commutator_ne
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (Mstar := Mstar)
      (p := p) (r := r) (q := q) hM hE hpτ1 hP hR hMstar S hcomm
  have hQ_ne : Q ≠ ⊥ := by
    simpa [Q, Sg, X] using hcomm
  have hPR_norm_X : P ⊔ R ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.Normalizes.le_normalizer
  have hPR_norm_Sg : P ⊔ R ≤ Subgroup.normalizer (Sg : Set G) := by
    simpa [Sg, X] using
      section13_le_normalizer_map_of_isInvariant
        (G := G) (A := P ⊔ R) (H := X) (K := (S : Subgroup X))
        hPR_norm_X (by simpa [X] using hSinv)
  have hR_norm_Sg : R ≤ Subgroup.normalizer (Sg : Set G) :=
    le_sup_right.trans hPR_norm_Sg
  have hQ_le_Sg : Q ≤ Sg := by
    simpa [Q] using section13_commutator_le_left_of_le_normalizer hR_norm_Sg
  have hSg_le_X : Sg ≤ X := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨s, _hs, rfl⟩
    exact s.property
  have hX_le_msigma : X ≤ section10Msigma M := by
    dsimp [X, subgroupCentralizerIn]
    exact inf_le_left
  have hMsigma_le_M : section10Msigma M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hSg_le_M : Sg ≤ M := hSg_le_X.trans (hX_le_msigma.trans hMsigma_le_M)
  have hQ_le_M : Q ≤ M := hQ_le_Sg.trans hSg_le_M
  have hSg_le_Mstar : Sg ≤ Mstar := by
    intro x hx
    have hxX : x ∈ X := hSg_le_X hx
    exact hMstar.2 ((centralizer_le_normalizer P) (by simpa [X, subgroupCentralizerIn] using hxX.2))
  have hQ_le_Mstar : Q ≤ Mstar := hQ_le_Sg.trans hSg_le_Mstar
  have hQq : IsPGroup q.val Q := by
    have hSgq : IsPGroup q.val Sg := by
      change IsPGroup q.val ((S : Subgroup X).map X.subtype)
      exact IsPGroup.map (p := q.val) (H := (S : Subgroup X))
        S.isPGroup' X.subtype
    exact section13_isPGroup_of_le_pSubgroup (G := G) hSgq hQ_le_Sg
  have hSR_norm_Q : Sg ⊔ R ≤ Subgroup.normalizer (Q : Set G) := by
    have hQ_norm_sup : (Q.subgroupOf (Sg ⊔ R : Subgroup G)).Normal := by
      simpa [Q] using commutator_normal_in_sup Sg R
    have hQ_le_sup : Q ≤ Sg ⊔ R := by
      simpa [Q] using commutator_le_sup Sg R
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := Q) (K := Sg ⊔ R) hQ_le_sup).mp hQ_norm_sup
  have hR_norm_Q : R ≤ Subgroup.normalizer (Q : Set G) :=
    le_sup_right.trans hSR_norm_Q
  have hqσ : q ∈ section10SigmaPrimes M :=
    section13_sigma_of_mem_centralizer_msigma (G := G) hM hqX
  have hqr : q ≠ r :=
    (section13_ne_of_sigma_and_mem_E (G := G) hM hE hrE hqσ).symm
  have hq_pPrime_r : q ∈ section10PPrimeSet r := by
    rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hqr
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hP_le_E, hPcard⟩
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  have hP_le_M : P ≤ M := hP_le_E.trans hE.1.2.1
  have hnotconj_star_M : section12NotConjugate Mstar M :=
    lemma_12_2_b (G := G) (M := M) (Mstar := Mstar) (X := P) (p := p)
      hM hPp hPne hP_le_M hMstar (Or.inr (Or.inl hpτ1))
  have hMstar_ne_M : Mstar ≠ M := by
    intro hEq
    exact hnotconj_star_M 1 (by simpa [hEq] using section8_conjBy_one (G := G) Mstar)
  have hSgq : IsPGroup q.val Sg := by
    change IsPGroup q.val ((S : Subgroup X).map X.subtype)
    exact IsPGroup.map (p := q.val) (H := (S : Subgroup X))
      S.isPGroup' X.subtype
  have hSg_comm : IsMulCommutative Sg := by
    by_contra hnon
    exact
      (section13_not_unique_of_le_two_distinct_maximal
        (G := G) hM hMstar.1 hSg_le_M hSg_le_Mstar hMstar_ne_M)
        (theorem_12_13 (G := G) (P := Sg) (p := q) hSgq hnon)
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR) with
    ⟨hR_le_CEP, hRcard⟩
  have hRr : IsPGroup r.val R := by
    refine IsPGroup.of_card (p := r.val) (G := R) (n := 1) ?_
    simpa [pow_one] using hRcard
  have hRπ : IsPiSubgroup (G := G) ({r} : Set Nat.Primes) R :=
    section8_isPiSubgroup_singleton_of_isPGroup hRr
  have hSgπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Sg :=
    section8_isPiSubgroup_singleton_of_isPGroup hSgq
  have hdis_rq : Disjoint ({r} : Set Nat.Primes) ({q} : Set Nat.Primes) := by
    rw [Set.disjoint_left]
    intro s hsr hsq
    have hsr_eq : s = r := by simpa using hsr
    have hsq_eq : s = q := by simpa using hsq
    exact hqr (hsq_eq.symm.trans hsr_eq)
  have hcop_RSg : Nat.Coprime (Nat.card R) (Nat.card Sg) :=
    section13_coprime_card_of_isPiSubgroup_disjoint_primes
      (G := G) hRπ hSgπ hdis_rq
  have hCQ_bot : subgroupCentralizerIn Q R = ⊥ := by
    simpa [Q] using
      section13_commutator_centralizerIn_eq_bot_of_coprime
        (G := G) (K := Sg) (P := R) hR_norm_Sg hcop_RSg hSg_comm
  have hR_le_Mstar : R ≤ Mstar := by
    intro x hx
    exact hMstar.2 ((centralizer_le_normalizer P) ((hR_le_CEP hx).2))
  have hrMstar : r ∈ subgroupPrimeSet Mstar :=
    section8_subgroupPrimeSet_mono hR_le_Mstar (by
      rw [subgroupPrimeSet, hRcard]
      exact dvd_rfl)
  have hR_prime_Mstar : R ∈ section10PrimeOrderSubgroupsIn r Mstar := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hR_le_Mstar, hRcard⟩
  have hpαstar : p ∈ section10AlphaPrimes Mstar := hpβstar.1
  have hMstarα_ne : section10Malpha Mstar ≠ ⊥ := by
    intro hαbot
    have hHallα : IsHallSubgroup (section10AlphaPrimes Mstar) (section10Malpha Mstar) :=
      (theorem_10_2_a (G := G) hMstar.1).1
    have hpG : p.val ∣ Nat.card G :=
      hpαstar.1.trans (Subgroup.card_subgroup_dvd_card Mstar)
    have hindex_mul : (section10Malpha Mstar).index * Nat.card (section10Malpha Mstar) =
        Nat.card G :=
      Subgroup.index_mul_card (H := section10Malpha Mstar)
    have hp_prod : p.val ∣ (section10Malpha Mstar).index *
        Nat.card (section10Malpha Mstar) := by
      simpa [hindex_mul] using hpG
    rcases p.property.dvd_mul.mp hp_prod with hpidx | hpαcard
    · exact (hHallα.p_in_pi_of_p_dvd_index p hpidx) hpαstar
    have hp_dvd_α : p.val ∣ Nat.card (section10Malpha Mstar) := hpαcard
    rw [hαbot] at hp_dvd_α
    exact p.property.not_dvd_one (by simpa using hp_dvd_α)
  have hq_notαstar : q ∉ section10AlphaPrimes Mstar := by
    have hdis : Disjoint (section10AlphaPrimes Mstar) (section10SigmaPrimes M) :=
      (lemma_10_12_a (G := G) (M := Mstar) (H := M) hMstar.1 hM
        (section13_notConjugate_symm hnotconj_star_M)).2
    rw [Set.disjoint_left] at hdis
    intro hqαstar
    exact hdis hqαstar hqσ
  have hP_le_Mstar : P ≤ Mstar :=
    Subgroup.le_normalizer.trans hMstar.2
  have hPsub_p : IsPGroup p.val (P.subgroupOf Mstar) :=
    hPp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := P) (K := Mstar) hP_le_Mstar).symm
  have hPsub_le_beta :
      P.subgroupOf Mstar ≤ section10MbetaSubgroup Mstar :=
    section13_pSubgroup_le_normal_hall_of_prime_mem
      (R := Mstar) (π := section10BetaPrimes Mstar)
      (H := section10MbetaSubgroup Mstar) (A := P.subgroupOf Mstar)
      (p := p) (lemma_10_8_a (G := G) hMstar.1).2 hpβstar hPsub_p
  have hP_le_Mbeta_star : P ≤ section10Mbeta Mstar := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hP_le_Mstar hx⟩, by
        exact hPsub_le_beta (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hP_le_Malpha_star : P ≤ section10Malpha Mstar :=
    hP_le_Mbeta_star.trans (section13_mbeta_le_malpha (G := G) Mstar)
  have hP_le_Msigma_star : P ≤ section10Msigma Mstar :=
    hP_le_Malpha_star.trans (section13_malpha_le_msigma (G := G) hMstar.1)
  have hR_le_centP : R ≤ Subgroup.centralizer (P : Set G) :=
    hR_le_CEP.trans inf_le_right
  have hQ_le_centP : Q ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    exact (hSg_le_X (hQ_le_Sg hx)).2
  have hRQ_le_centP : R ⊔ Q ≤ Subgroup.centralizer (P : Set G) :=
    sup_le hR_le_centP hQ_le_centP
  have hP_le_cent_RQ : P ≤ Subgroup.centralizer ((R ⊔ Q : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff (H := R ⊔ Q) (K := P)).mp hRQ_le_centP
  have hP_le_Calpha_RQ :
      P ≤ subgroupCentralizerIn (section10Malpha Mstar) (R ⊔ Q) := by
    intro x hx
    exact ⟨hP_le_Malpha_star hx, hP_le_cent_RQ hx⟩
  have hUniqueStar :
      section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) = {Mstar} := by
    by_contra hnotUnique
    have h1218 :
        subgroupCentralizerIn (section10Malpha Mstar) R ≠ ⊥ ∧
          subgroupCentralizerIn (section10Malpha Mstar) (R ⊔ Q) = ⊥ :=
      lemma_12_18_a (G := G) (M := Mstar) (P := R) (Q := Q)
        (p := r) (q := q) hMstar.1 hrτ1star hR_prime_Mstar hq_pPrime_r
        hQ_le_Mstar hQ_ne hQq hR_norm_Q hCQ_bot hnotUnique
        hMstarα_ne hq_notαstar
    have hP_le_bot : P ≤ (⊥ : Subgroup G) := by
      intro x hx
      have hxC : x ∈ subgroupCentralizerIn (section10Malpha Mstar) (R ⊔ Q) :=
        hP_le_Calpha_RQ hx
      simpa [h1218.2] using hxC
    exact hPne (le_bot_iff.mp hP_le_bot)
  have hMstarQ :
      Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) := by
    rw [hUniqueStar]
    simp
  have hQ_le_inf : Q ≤ M ⊓ Mstar :=
    le_inf hQ_le_M hQ_le_Mstar
  have hQsub_p : IsPGroup q.val (Q.subgroupOf (M ⊓ Mstar : Subgroup G)) :=
    hQq.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := Q) (K := M ⊓ Mstar) hQ_le_inf).symm
  obtain ⟨T, hQsub_le_T⟩ :=
    IsPGroup.exists_le_sylow (G := (M ⊓ Mstar : Subgroup G)) (p := q.val) hQsub_p
  have hQ_le_Tamb : Q ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) T := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hQ_le_inf hx⟩, hQsub_le_T (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hqσstar : q ∈ section10SigmaPrimes Mstar := by
    by_contra hq_notσstar
    rcases proposition_12_15_e (G := G) (M := M) (Mstar := Mstar) (X := Q)
        (q := q) (S := T) hM hqσ hQ_le_M hQ_ne hQq hMstarQ
        hMstar_ne_M hQ_le_Tamb hq_notσstar with
      ⟨_hqτ2star, _hbeta_transfer, hcompl⟩
    rcases hcompl with ⟨_hσ_le_star, _hinf_le_star, _hstar_join, hdisj⟩
    have hP_le_bot : P ≤ (⊥ : Subgroup G) := by
      intro x hx
      have hxinf : x ∈ section10Msigma Mstar ⊓ (M ⊓ Mstar : Subgroup G) :=
        ⟨hP_le_Msigma_star hx, ⟨hP_le_M hx, hP_le_Mstar hx⟩⟩
      simpa [hdisj.eq_bot] using hxinf
    exact hPne (le_bot_iff.mp hP_le_bot)
  have h1215d :
      Mstar = (M ⊓ Mstar) ⊔ section10Mbeta Mstar ∧
        section12Tau1Primes Mstar ⊆ section12Tau1Primes M ∪ section10AlphaPrimes M ∧
          section10Mbeta Mstar = section10Malpha Mstar ∧
            section10Mbeta Mstar ≠ ⊥ :=
    proposition_12_15_d (G := G) (M := M) (Mstar := Mstar) (X := Q)
      (q := q) (S := T) hM hqσ hQ_le_M hQ_ne hQq hMstarQ
      hMstar_ne_M hQ_le_Tamb hqσstar
  have hrτ1_or_α : r ∈ section12Tau1Primes M ∪ section10AlphaPrimes M :=
    h1215d.2.1 hrτ1star
  have hr_notα : r ∉ section10AlphaPrimes M := by
    intro hrα
    exact (section12_not_sigma_of_mem_complement (G := G) hM hE.1 hrE)
      (section13_sigmaPrimes_mem_of_alphaPrimes_mem (G := G) hM hrα)
  have hrτ1 : r ∈ section12Tau1Primes M := by
    rcases hrτ1_or_α with hrτ1 | hrα
    · exact hrτ1
    · exact False.elim (hr_notα hrα)
  have hq_notα : q ∉ section10AlphaPrimes M := by
    have hdis : Disjoint (section10AlphaPrimes M) (section10SigmaPrimes Mstar) :=
      (lemma_10_12_a (G := G) (M := M) (H := Mstar) hM hMstar.1
        hnotconj_star_M).2
    rw [Set.disjoint_left] at hdis
    intro hqα
    exact hdis hqα hqσstar
  have hR_prime_M : R ∈ section10PrimeOrderSubgroupsIn r M := by
    simpa [section10PrimeOrderSubgroupsIn] using
      ⟨(hR_le_CEP.trans inf_le_left).trans hE.1.2.1, hRcard⟩
  have hnotUniqueM :
      section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M} := by
    intro hEq
    have hM_mem : M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) := by
      rw [hEq]
      simp
    have hsingle : M ∈ ({Mstar} : Set (Subgroup G)) := by
      simpa [hUniqueStar] using hM_mem
    have hM_eq_star : M = Mstar := by simpa using hsingle
    exact hMstar_ne_M hM_eq_star.symm
  have hTamb_norm_M :
      Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) T : Subgroup G) : Set G) ≤
        M :=
    proposition_12_15_b (G := G) (M := M) (Mstar := Mstar) (X := Q)
      (q := q) (S := T) hM hqσ hQ_le_M hQ_ne hQq hMstarQ
      hMstar_ne_M hQ_le_Tamb
  have hSylowStar :
      section12SylowSubgroupIn q (section10AmbientSylowSubgroup (M ⊓ Mstar) T)
        Mstar :=
    proposition_12_15_c (G := G) (M := M) (Mstar := Mstar) (X := Q)
      (q := q) (S := T) hM hqσ hQ_le_M hQ_ne hQq hMstarQ
      hMstar_ne_M hQ_le_Tamb
  have hTamb_norm_Mstar :
      Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) T : Subgroup G) : Set G) ≤
        Mstar :=
    section13_normalizer_inf_sylow_le_right_of_sigma
      (G := G) (M := M) (Mstar := Mstar) (q := q) (S := T)
      hMstar.1 hqσstar hSylowStar
  rcases section13_global_sylow_of_inf_sylow_normalizer_le
      (G := G) (M := M) (Mstar := Mstar) (q := q) (S := T)
      hTamb_norm_M hTamb_norm_Mstar with
    ⟨Sglob, hSglob⟩
  have hSglob_norm_inf :
      Subgroup.normalizer ((Sglob : Subgroup G) : Set G) ≤ Mstar ⊓ M := by
    intro g hg
    have hg' :
        g ∈ Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) T : Subgroup G) : Set G) := by
      simpa [hSglob] using hg
    exact ⟨hTamb_norm_Mstar hg', hTamb_norm_M hg'⟩
  have h109b :
      Mstar ⊓ M ⊔ section10Mbeta M = M ∧
        section10AlphaPrimes M = section10BetaPrimes M :=
    corollary_10_9_b (G := G) (M := M) (H := Mstar)
      hM hMstar.1 hMstar_ne_M ⟨q, Sglob, hSglob_norm_inf⟩
  have hMα_ne : section10Malpha M ≠ ⊥ := by
    have hβ_ne : section10Mbeta M ≠ ⊥ :=
      section13_Mbeta_ne_bot_of_inf_sup_mbeta_eq
        (G := G) (M := Mstar) (Mstar := M)
        hMstar.1 hM hMstar_ne_M.symm h109b.1
    intro hαbot
    have hβ_eq_α : section10Mbeta M = section10Malpha M :=
      section13_Mbeta_eq_Malpha_of_alphaPrimes_eq_betaPrimes (G := G) h109b.2
    exact hβ_ne (by simpa [hβ_eq_α] using hαbot)
  have h1218M :
      subgroupCentralizerIn (section10Malpha M) R ≠ ⊥ ∧
        subgroupCentralizerIn (section10Malpha M) (R ⊔ Q) = ⊥ :=
    lemma_12_18_a (G := G) (M := M) (P := R) (Q := Q)
      (p := r) (q := q) hM hrτ1 hR_prime_M hq_pPrime_r
      hQ_le_M hQ_ne hQq hR_norm_Q hCQ_bot hnotUniqueM hMα_ne hq_notα
  have hSg_norm_CalphaP :
      Sg ≤ Subgroup.normalizer
        (subgroupCentralizerIn (section10Malpha M) P : Set G) :=
    section13_le_normalizer_subgroupCentralizerIn
      (G := G) (A := section10Malpha M) (P := P) (S := Sg)
      (hSg_le_M.trans (section13_le_normalizer_malpha (G := G)))
      (by
        intro x hx
        exact (hSg_le_X hx).2)
  have hCP_eq_CR :
      subgroupCentralizerIn (section10Malpha M) P =
        subgroupCentralizerIn (section10Malpha M) R := by
    have hCP_le_CR :
        subgroupCentralizerIn (section10Malpha M) P ≤
          subgroupCentralizerIn (section10Malpha M) R :=
      section13_malpha_centralizer_le_of_tau1_prime_order_pair
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (P := P) (R := R)
        (p := p) (r := r) hM hE hpτ1 hP hrτ1 hR
    have hR_prime_E : R ∈ section10PrimeOrderSubgroupsIn r E := by
      simpa [section10PrimeOrderSubgroupsIn] using
        ⟨hR_le_CEP.trans inf_le_left, hRcard⟩
    have hP_le_centR : P ≤ Subgroup.centralizer (R : Set G) :=
      (Subgroup.le_centralizer_iff (H := R) (K := P)).mp hR_le_centP
    have hP_prime_CER :
        P ∈ section10PrimeOrderSubgroupsIn p (subgroupCentralizerIn E R) := by
      simpa [section10PrimeOrderSubgroupsIn] using
        ⟨(by
          intro x hx
          exact ⟨hP_le_E hx, hP_le_centR hx⟩), hPcard⟩
    have hCR_le_CP :
        subgroupCentralizerIn (section10Malpha M) R ≤
          subgroupCentralizerIn (section10Malpha M) P :=
      section13_malpha_centralizer_le_of_tau1_prime_order_pair
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (P := R) (R := P)
        (p := r) (r := p) hM hE hrτ1 hR_prime_E hpτ1 hP_prime_CER
    exact le_antisymm hCP_le_CR hCR_le_CP
  have hCR_le_CRQ :
      subgroupCentralizerIn (section10Malpha M) R ≤
        subgroupCentralizerIn (section10Malpha M) (R ⊔ Q) := by
    simpa [Q] using
      section13_subgroupCentralizerIn_le_sup_of_equal_centralizers
        (G := G) (A := section10Malpha M) (P := P) (R := R) (S := Sg)
        hSg_norm_CalphaP hCP_eq_CR
  have hCR_bot : subgroupCentralizerIn (section10Malpha M) R = ⊥ :=
    le_bot_iff.mp (by
      rw [← h1218M.2]
      exact hCR_le_CRQ)
  exact h1218M.1 hCR_bot

private theorem CFSG.section13_theorem_13_4_pr_invariant_sylow_centralizes
    {M E E₁₂ E₁ E₂ E₃ P R Mstar : Subgroup G} {p r q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hrE : r ∈ subgroupPrimeSet E)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hqX : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) P))
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining
      (Subgroup.normalizer (P : Set G)))
    (hrτ1star : r ∈ section12Tau1Primes Mstar)
    [Subgroup.Normalizes (P ⊔ R) (subgroupCentralizerIn (section10Msigma M) P)]
    (S : Sylow q.val (subgroupCentralizerIn (section10Msigma M) P))
    (hSinv : IsInvariant (↥(P ⊔ R))
      (↥(subgroupCentralizerIn (section10Msigma M) P))
      (S : Subgroup (subgroupCentralizerIn (section10Msigma M) P))) :
    (S : Subgroup (subgroupCentralizerIn (section10Msigma M) P)).map
        (subgroupCentralizerIn (section10Msigma M) P).subtype ≤
          Subgroup.centralizer (R : Set G) := by
  classical
  let Sg : Subgroup G :=
    (S : Subgroup (subgroupCentralizerIn (section10Msigma M) P)).map
      (subgroupCentralizerIn (section10Msigma M) P).subtype
  by_cases hcomm : ⁅Sg, R⁆ = ⊥
  · simpa [Sg] using
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Sg) (H₂ := R)).mp
        hcomm
  · exact False.elim <|
      section13_theorem_13_4_pr_invariant_sylow_noncentral_absurd
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (Mstar := Mstar)
        (p := p) (r := r) (q := q)
        hM hE hpτ1 hP hrE hR hqX hMstar hrτ1star S hSinv
        (by simpa [Sg] using hcomm)

private theorem CFSG.section13_theorem_13_4_exists_centralized_sylow_tau1_star
    {M E E₁₂ E₁ E₂ E₃ P R Mstar : Subgroup G} {p r q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hrE : r ∈ subgroupPrimeSet E)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hqX : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) P))
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining
      (Subgroup.normalizer (P : Set G)))
    (hrτ1star : r ∈ section12Tau1Primes Mstar) :
    ∃ S : Sylow q.val (subgroupCentralizerIn (section10Msigma M) P),
      (S : Subgroup (subgroupCentralizerIn (section10Msigma M) P)).map
        (subgroupCentralizerIn (section10Msigma M) P).subtype ≤
          Subgroup.centralizer (R : Set G) := by
  classical
  rcases section13_theorem_13_4_exists_pr_invariant_sylow
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (R := R)
      (p := p) (r := r) (q := q) hM hE hP hR hqX with
    ⟨hAX, S, hSinv⟩
  letI : Subgroup.Normalizes (P ⊔ R) (subgroupCentralizerIn (section10Msigma M) P) := hAX
  refine ⟨S, ?_⟩
  exact
    section13_theorem_13_4_pr_invariant_sylow_centralizes
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (Mstar := Mstar)
      (p := p) (r := r) (q := q)
      hM hE hpτ1 hP hrE hR hqX hMstar hrτ1star S hSinv

/-- The hard Sylow step in Theorem 13.4.  The natural proof fixes, for each
prime divisor of `C_{M_σ}(P)`, a `PR`-invariant Sylow subgroup and derives a
contradiction from a nontrivial commutator with `R`; this bridge keeps only the
existence statement needed for the final cardinality lift. -/
private theorem CFSG.section13_theorem_13_4_exists_centralized_sylow
    {M E E₁₂ E₁ E₂ E₃ P R : Subgroup G} {p r q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hrE : r ∈ subgroupPrimeSet E)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hqX : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) P)) :
    ∃ S : Sylow q.val (subgroupCentralizerIn (section10Msigma M) P),
      (S : Subgroup (subgroupCentralizerIn (section10Msigma M) P)).map
        (subgroupCentralizerIn (section10Msigma M) P).subtype ≤
          Subgroup.centralizer (R : Set G) := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPE, hPcard⟩
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  have hPM : P ≤ M := hPE.trans hE.1.2.1
  have hnormP_ne_top :
      Subgroup.normalizer (P : Set G) ≠ ⊤ :=
    section13_normalizer_ne_top_of_ne_bot_le_maximal hM hPM hPne
  rcases section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) hnormP_ne_top with
    ⟨Mstar, hMstar⟩
  by_cases hrτ1star : r ∈ section12Tau1Primes Mstar
  · exact
      section13_theorem_13_4_exists_centralized_sylow_tau1_star
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (Mstar := Mstar)
        (p := p) (r := r) (q := q)
        hM hE hpτ1 hP hrE hR hqX hMstar hrτ1star
  · have hcent :
        subgroupCentralizerIn (section10Msigma M) P ≤ Subgroup.centralizer (R : Set G) :=
      section13_theorem_13_4_centralizes_of_not_tau1_star
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (Mstar := Mstar)
        (p := p) (r := r) hM hE hpτ1 hP hR hMstar hrτ1star
    let S : Sylow q.val (subgroupCentralizerIn (section10Msigma M) P) := default
    refine ⟨S, ?_⟩
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨s, _hs, rfl⟩
    exact hcent s.property

/-- Theorem 13.4: if `p ∈ τ₁(M)`, `P ∈ 𝓔_p^1(E)`, `r ∈ π(E)`, and
`R ∈ 𝓔_r^1(C_E(P))`, then `C_{M_σ}(P) ≤ C_{M_σ}(R)`. -/
public theorem CFSG.theorem_13_4
    {M E E₁₂ E₁ E₂ E₃ P R : Subgroup G} {p r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hrE : r ∈ subgroupPrimeSet E)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P)) :
    subgroupCentralizerIn (section10Msigma M) P ≤
      subgroupCentralizerIn (section10Msigma M) R := by
  classical
  have hcent :
      subgroupCentralizerIn (section10Msigma M) P ≤ Subgroup.centralizer (R : Set G) :=
    section13_le_centralizer_of_exists_sylow_images
      (G := G) (K := R) (X := subgroupCentralizerIn (section10Msigma M) P) (by
        intro q hqX
        exact section13_theorem_13_4_exists_centralized_sylow
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) (P := P) (R := R)
          (p := p) (r := r) (q := q)
          hM hE hpτ1 hP hrE hR hqX)
  intro x hx
  exact ⟨hx.1, hcent hx⟩

end Section13
