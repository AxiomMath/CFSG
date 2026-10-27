module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_7_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section12_CA_msigma_split_E2_cyclic_factor_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    ∃ Z : Subgroup G,
      Z ≤ E₂ ∧ IsCyclic Z ∧
        Disjoint (subgroupCentralizerIn A (section10Msigma M)) Z ∧
        E₂ = subgroupCentralizerIn A (section10Msigma M) ⊔ Z := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hE₂p : IsPGroup p.val E₂ :=
    section12_E2_isPGroup_of_tau2_singleton_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  obtain ⟨S, hE₂S⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hE₂p
  have hSnonab : ¬ IsMulCommutative (S : Subgroup G) := by
    intro hScomm
    rcases hSylow with ⟨Sbad, hSbad_noncomm⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Sbad
    have hconj_comm : IsMulCommutative ((g • S : Sylow p.val G) : Subgroup G) := by
      letI : IsMulCommutative (S : Subgroup G) := hScomm
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.map_isMulCommutative
        (f := (MulAut.conj g).toMonoidHom) (H := (S : Subgroup G))
    have hSbad_comm : IsMulCommutative (Sbad : Subgroup G) := by
      rw [← hg]
      exact hconj_comm
    exact hSbad_noncomm hSbad_comm
  have hA_le_E₂ : A ≤ E₂ :=
    section12_rankTwo_tau2_le_E2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA
  have hA_le_S : A ≤ (S : Subgroup G) := hA_le_E₂.trans hE₂S
  have hCcard : Nat.card C = p.val := by
    simpa [C] using (theorem_12_7_b
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow).1
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
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
    exact ⟨inf_le_left, by simpa [C] using hCcard⟩
  have hSnotM : ¬ (S : Subgroup G) ≤ M :=
    section12_global_sylow_not_le_M_of_nonabelian_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSnonab
  have hCneOmega : C ≠ section10OmegaOneCenter p (S : Subgroup G) := by
    simpa [C] using
      section12_CA_msigma_ne_omegaOneCenter_of_tau2_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (P := (S : Subgroup G)) (p := p)
        hM hE hp hA hSnonab hSnotM hCcard
  obtain ⟨Z, _hΩZ, hZcyc, hCdisjZ, hCS_eq⟩ :=
    lemma_10_13_b (G := G) (p := p) (A := A) (P := (S : Subgroup G))
      (A₀ := C) hpG hA10 S.isPGroup' hSnonab hA_le_S hCprime hCneOmega
  have hE₂_le_centA : E₂ ≤ Subgroup.centralizer (A : Set G) :=
    section12_E2_le_centralizer_rankTwo_tau2_of_theorem_12_7_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  have hE₂_le_CS : E₂ ≤ subgroupCentralizerIn (S : Subgroup G) A := by
    intro x hx
    exact ⟨hE₂S hx, hE₂_le_centA hx⟩
  have hCS_le_E : subgroupCentralizerIn (S : Subgroup G) A ≤ E := by
    have h6 :=
      corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
    exact inf_le_right.trans (by simpa [h6.2.1] using h6.1)
  have hCS_le_E₂ : subgroupCentralizerIn (S : Subgroup G) A ≤ E₂ := by
    let K : Subgroup E := (subgroupCentralizerIn (S : Subgroup G) A).subgroupOf E
    have hCS_p : IsPGroup p.val (subgroupCentralizerIn (S : Subgroup G) A) :=
      IsPGroup.to_le S.isPGroup' inf_le_left
    have hKp : IsPGroup p.val K :=
      hCS_p.of_equiv
        (Subgroup.subgroupOfEquivOfLe
          (H := subgroupCentralizerIn (S : Subgroup G) A) (K := E) hCS_le_E).symm
    have hE2HallIn :
        section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
      section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
    rcases hE2HallIn with ⟨hE2E, hHallE2E⟩
    let E₂sub : Subgroup E := E₂.subgroupOf E
    have hE₂sub_p : IsPGroup p.val E₂sub :=
      hE₂p.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := E₂) (K := E) hE2E).symm
    have hp_not_dvd_E₂sub_index : ¬ p.val ∣ E₂sub.index := by
      intro hpidx
      exact (hHallE2E.p_in_pi_of_p_dvd_index p hpidx) hp
    let P : Sylow p.val E := IsPGroup.toSylow (p := p.val) hE₂sub_p hp_not_dvd_E₂sub_index
    have hP_eq_E₂sub : (P : Subgroup E) = E₂sub := by
      simp [P, E₂sub, IsPGroup.toSylow_coe]
    have hP_le_K : (P : Subgroup E) ≤ K := by
      rw [hP_eq_E₂sub]
      intro x hx
      change (x : G) ∈ subgroupCentralizerIn (S : Subgroup G) A
      exact hE₂_le_CS (by simpa [E₂sub, Subgroup.mem_subgroupOf] using hx)
    have hK_eq_P : K = (P : Subgroup E) :=
      P.is_maximal' hKp hP_le_K
    intro x hx
    have hxE : x ∈ E := hCS_le_E hx
    let xE : E := ⟨x, hxE⟩
    have hxK : xE ∈ K := by
      simpa [K, xE, Subgroup.mem_subgroupOf] using hx
    have hxE₂sub : xE ∈ E₂sub := by
      simpa [hK_eq_P, hP_eq_E₂sub] using hxK
    simpa [E₂sub, xE, Subgroup.mem_subgroupOf] using hxE₂sub
  have hCS_eq_E₂ : subgroupCentralizerIn (S : Subgroup G) A = E₂ :=
    le_antisymm hCS_le_E₂ hE₂_le_CS
  refine ⟨Z, ?_, hZcyc, by simpa [C] using hCdisjZ, ?_⟩
  · exact le_sup_right.trans (by
      rw [← hCS_eq, hCS_eq_E₂])
  · calc
      E₂ = subgroupCentralizerIn (S : Subgroup G) A := hCS_eq_E₂.symm
      _ = C ⊔ Z := hCS_eq
      _ = subgroupCentralizerIn A (section10Msigma M) ⊔ Z := by simp [C]

public theorem CFSG.section12_CA_msigma_not_le_frattini_E2_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    ¬ (subgroupCentralizerIn A (section10Msigma M)).subgroupOf E₂ ≤ frattini E₂ := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  intro hCΦ
  obtain ⟨Z, hZE₂, _hZcyc, hdisj, hE₂eq⟩ :=
    section12_CA_msigma_split_E2_cyclic_factor_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  have hCE₂ : C ≤ E₂ := by
    simpa [C] using
      section12_CA_msigma_le_E2_of_tau2_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
  let C₂ : Subgroup E₂ := C.subgroupOf E₂
  let Z₂ : Subgroup E₂ := Z.subgroupOf E₂
  have hCZ_top : C₂ ⊔ Z₂ = ⊤ := by
    calc
      C₂ ⊔ Z₂ = (C ⊔ Z).subgroupOf E₂ := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := C) (A' := Z) (B := E₂) hCE₂ hZE₂
      _ = ⊤ := by
        apply Subgroup.subgroupOf_eq_top.2
        simpa [C] using le_of_eq hE₂eq
  have hZΦ_top : Z₂ ⊔ frattini E₂ = ⊤ := by
    apply le_antisymm le_top
    rw [← hCZ_top]
    exact sup_le
      (show C₂ ≤ Z₂ ⊔ frattini E₂ from
        (show C₂ ≤ frattini E₂ from by simpa [C₂, C] using hCΦ).trans le_sup_right)
      le_sup_left
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hE₂p : IsPGroup p.val E₂ :=
    section12_E2_isPGroup_of_tau2_singleton_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  haveI : Fact (IsPGroup p.val E₂) := ⟨hE₂p⟩
  have hZ₂top : Z₂ = ⊤ :=
    lemma_1_7_a (R := E₂) (p := p.val) (H := Z₂) hZΦ_top
  have hC_le_Z : C ≤ Z := by
    intro c hc
    have hcE₂ : c ∈ E₂ := hCE₂ hc
    let c₂ : E₂ := ⟨c, hcE₂⟩
    have hcZ₂ : c₂ ∈ Z₂ := by
      simp [hZ₂top]
    simpa [Z₂, c₂, Subgroup.mem_subgroupOf] using hcZ₂
  have hCbot : C = ⊥ := by
    apply le_bot_iff.mp
    intro c hc
    exact Subgroup.disjoint_def.mp hdisj hc (hC_le_Z hc)
  have hCcard := (theorem_12_7_b
    (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
    (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
    hM hE hp hA hSylow).1
  have hp_one : p.val = 1 := by
    simpa [C, hCbot] using hCcard.symm
  exact p.2.ne_one hp_one

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_coprime_card_E1_tau2_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (_hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (_hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    Nat.Coprime p.val (Nat.card E₁) := by
  classical
  rcases hE with ⟨_hcomp, _hE12, hE1, _hE2, _hE3⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  refine (p.property.coprime_iff_not_dvd).2 ?_
  intro hpdiv
  have hpdiv_sub : p.val ∣ Nat.card (E₁.subgroupOf E₁₂) := by
    simpa [natCard_subgroupOf_eq _ _ hE1E12] using hpdiv
  have hpτ1 : p ∈ section12Tau1Primes M :=
    hHallE1.p_in_pi_of_p_dvd_card p hpdiv_sub
  have h1 : primeRank p.val M = 1 := hpτ1.2.2
  have h2 : primeRank p.val M = 2 := hp.2
  omega

public theorem CFSG.section12_E1_invariant_CA_msigma_subgroupOf_E2_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    letI : Subgroup.Normalizes E₁ E₂ :=
      ⟨section12_E1_le_normalizer_E2_pre (G := G) (M := M) hM hE⟩
    IsInvariant E₁ E₂
      ((subgroupCentralizerIn A (section10Msigma M)).subgroupOf E₂) := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  letI : Subgroup.Normalizes E₁ E₂ :=
    ⟨section12_E1_le_normalizer_E2_pre (G := G) (M := M) hM hE⟩
  have hAnorm : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).1
  have hCnormE : section10NormalIn C E := by
    simpa [C] using
      section12_CA_msigma_normalIn_E_pre (G := G) (M := M) (E := E)
        (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A)
        hE hAnorm
  have hE_norm_C : E ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCnormE.1).1 hCnormE.2
  have hE₁E : E₁ ≤ E := hE.2.2.1.1.trans hE.2.1.1
  refine ⟨?_⟩
  intro a x
  have ha_norm_C : (a : G) ∈ Subgroup.normalizer (C : Set G) :=
    hE_norm_C (hE₁E a.property)
  simpa [C, Subgroup.mem_subgroupOf,
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
      (Subgroup.mem_normalizer_iff.mp ha_norm_C (x : G))

public theorem CFSG.section12_CA_msigma_complement_in_E2_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    ∃ P₀ : Subgroup G,
      P₀ ≤ E₂ ∧
        E₂ = subgroupCentralizerIn A (section10Msigma M) ⊔ P₀ ∧
        Disjoint (subgroupCentralizerIn A (section10Msigma M)) P₀ ∧
        E₁ ≤ Subgroup.normalizer (P₀ : Set G) := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  have hCE₂ : C ≤ E₂ := by
    simpa [C] using
      section12_CA_msigma_le_E2_of_tau2_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
  let C₂ : Subgroup E₂ := C.subgroupOf E₂
  let Φ : Subgroup E₂ := frattini E₂
  let q : E₂ →* E₂ ⧸ Φ := QuotientGroup.mk' Φ
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hE₂p : IsPGroup p.val E₂ :=
    section12_E2_isPGroup_of_tau2_singleton_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  haveI : Fact (IsPGroup p.val E₂) := ⟨hE₂p⟩
  letI : Subgroup.Normalizes E₁ E₂ :=
    ⟨section12_E1_le_normalizer_E2_pre (G := G) (M := M) hM hE⟩
  have hΦinv : IsInvariant E₁ E₂ Φ := by
    simpa [Φ] using isInvariant_of_characteristic (A := E₁) (G := E₂) (frattini E₂)
  letI : IsInvariant E₁ E₂ Φ := hΦinv
  haveI : Φ.Normal := by
    simpa [Φ] using (inferInstance : (frattini E₂).Normal)
  letI : MulDistribMulAction E₁ (E₂ ⧸ Φ) :=
    quotientMulDistribMulAction (A := E₁) (G := E₂) Φ hΦinv
  have hC₂inv : IsInvariant E₁ E₂ C₂ := by
    simpa [C₂, C] using
      section12_E1_invariant_CA_msigma_subgroupOf_E2_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
  letI : IsInvariant E₁ E₂ C₂ := hC₂inv
  let B : Subgroup (E₂ ⧸ Φ) := C₂.map q
  have hBinv : IsInvariant E₁ (E₂ ⧸ Φ) B := by
    simpa [B, q] using
      isInvariant_map_quotient
        (A := E₁) (G := E₂) (N := Φ) (H := C₂)
  letI : IsInvariant E₁ (E₂ ⧸ Φ) B := hBinv
  have hVelem : IsElementaryAbelian p.val (E₂ ⧸ Φ) := by
    simpa [Φ] using isElementaryAbelian_quotient_frattini (R := E₂) (p := p.val)
  letI : IsElementaryAbelian p.val (E₂ ⧸ Φ) := hVelem
  obtain ⟨Q, hBQ, hQinv⟩ :=
    section12_exists_isCompl_isInvariant_of_elementaryAbelian_coprime_pre
      (V := E₂ ⧸ Φ) (A := E₁) (p := p.val)
      (section12_coprime_card_E1_tau2_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA) B
  let P₀sub : Subgroup E₂ := Q.comap q
  letI : IsInvariant E₁ (E₂ ⧸ Φ) Q := hQinv
  have hqcompat : ∀ a : E₁, ∀ g : E₂, a • q g = q (a • g) := by
    intro a g
    simp [q, MulAction.Quotient.smul_mk]
  have hP₀subInv : IsInvariant E₁ E₂ P₀sub := by
    simpa [P₀sub, q] using
      isInvariant_comap_quotient
        (A := E₁) (G := E₂) (N := Φ) (H := Q) hqcompat
  let P₀ : Subgroup G := P₀sub.map E₂.subtype
  have hCcard : Nat.card C = p.val := by
    simpa [C] using (theorem_12_7_b
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow).1
  have hC₂card : Nat.card C₂ = p.val := by
    simpa [C₂, C, natCard_subgroupOf_eq _ _ hCE₂] using hCcard
  have hC₂_not_le_Φ : ¬ C₂ ≤ Φ := by
    simpa [C₂, C, Φ] using
      section12_CA_msigma_not_le_frattini_E2_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA hSylow
  have hC₂Φdisj : Disjoint C₂ Φ := by
    rw [Subgroup.disjoint_def]
    intro x hxC₂ hxΦ
    let D : Subgroup C₂ := Φ.subgroupOf C₂
    have hD_ne_top : D ≠ ⊤ := by
      intro hDtop
      have hC₂_le_Φ : C₂ ≤ Φ := by
        intro y hy
        let yC : C₂ := ⟨y, hy⟩
        have hyD : yC ∈ D := by simp [hDtop]
        simpa [D, yC, Subgroup.mem_subgroupOf] using hyD
      exact hC₂_not_le_Φ hC₂_le_Φ
    haveI : Fact (Nat.card C₂).Prime := ⟨by simpa [hC₂card] using p.2⟩
    have hD_bot : D = ⊥ := by
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card D with hD | hD
      · exact hD
      · exact False.elim (hD_ne_top hD)
    let xC : C₂ := ⟨x, hxC₂⟩
    have hxD : xC ∈ D := by
      simpa [D, xC, Subgroup.mem_subgroupOf] using hxΦ
    have hxC_bot : xC ∈ (⊥ : Subgroup C₂) := by simpa [hD_bot] using hxD
    exact Subtype.ext_iff.mp (by simpa using hxC_bot)
  have hΦ_le_P₀sub : Φ ≤ P₀sub := by
    intro x hx
    change q x ∈ Q
    have hxq : q x = 1 := by
      simpa [q, Φ] using (QuotientGroup.eq_one_iff (N := Φ) (x := x)).2 hx
    simp [hxq]
  have hC₂P₀sub_top : C₂ ⊔ P₀sub = ⊤ := by
    have hcomap :
        (Φ ⊔ C₂) ⊔ P₀sub = ⊤ := by
      have hsup_comap :
          B.comap q ⊔ Q.comap q = (B ⊔ Q).comap q := by
        simpa using
          (Subgroup.comap_sup_eq (f := q) (H := B) (K := Q)
            (QuotientGroup.mk'_surjective Φ))
      calc
        (Φ ⊔ C₂) ⊔ P₀sub = B.comap q ⊔ Q.comap q := by
          simp [B, P₀sub, q, QuotientGroup.comap_map_mk']
        _ = (B ⊔ Q).comap q := hsup_comap
        _ = ⊤ := by
          simp [hBQ.sup_eq_top]
    apply le_antisymm le_top
    rw [← hcomap]
    exact sup_le
      (sup_le (hΦ_le_P₀sub.trans le_sup_right) le_sup_left)
      le_sup_right
  have hC₂P₀sub_disj : Disjoint C₂ P₀sub := by
    rw [Subgroup.disjoint_def]
    intro x hxC₂ hxP₀
    have hxB : q x ∈ B := by
      exact Subgroup.mem_map.mpr ⟨x, hxC₂, rfl⟩
    have hxQ : q x ∈ Q := by
      simpa [P₀sub] using hxP₀
    have hxBQ : q x ∈ B ⊓ Q := ⟨hxB, hxQ⟩
    have hxq_one : q x = 1 := by
      have hxbot : q x ∈ (⊥ : Subgroup (E₂ ⧸ Φ)) := by
        simpa [hBQ.inf_eq_bot] using hxBQ
      simpa using hxbot
    have hxΦ : x ∈ Φ := by
      simpa [q] using (QuotientGroup.eq_one_iff (N := Φ) (x := x)).1 hxq_one
    exact Subgroup.disjoint_def.mp hC₂Φdisj hxC₂ hxΦ
  refine ⟨P₀, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  · calc
      E₂ = (⊤ : Subgroup E₂).map E₂.subtype := by
        ext x
        constructor
        · intro hx
          exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩
        · intro hx
          rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
          exact y.property
      _ = (C₂ ⊔ P₀sub).map E₂.subtype := by rw [hC₂P₀sub_top]
      _ = C₂.map E₂.subtype ⊔ P₀ := by simp [P₀, Subgroup.map_sup]
      _ = C ⊔ P₀ := by
        have hC₂map : C₂.map E₂.subtype = C := by
          simpa [C₂, C] using Subgroup.map_subgroupOf_eq_of_le hCE₂
        simp [hC₂map, C]
      _ = subgroupCentralizerIn A (section10Msigma M) ⊔ P₀ := by simp [C]
  · rw [Subgroup.disjoint_def]
    intro x hxC hxP₀
    have hxE₂ : x ∈ E₂ := hCE₂ hxC
    let x₂ : E₂ := ⟨x, hxE₂⟩
    have hxC₂ : x₂ ∈ C₂ := by
      simpa [C₂, C, x₂, Subgroup.mem_subgroupOf] using hxC
    have hxP₀sub : x₂ ∈ P₀sub := by
      rcases Subgroup.mem_map.mp hxP₀ with ⟨y, hyP₀sub, hyx⟩
      have hy_eq : y = x₂ := Subtype.ext hyx
      simpa [hy_eq] using hyP₀sub
    exact congrArg (fun y : E₂ => (y : G))
      (Subgroup.disjoint_def.mp hC₂P₀sub_disj hxC₂ hxP₀sub)
  · have hforward (a : E₁) {x : G} (hx : x ∈ P₀) :
        (a : G) * x * (a : G)⁻¹ ∈ P₀ := by
      rcases Subgroup.mem_map.mp hx with ⟨y, hyP₀sub, rfl⟩
      refine Subgroup.mem_map.mpr ⟨a • y, ?_, ?_⟩
      · exact (IsInvariant.invariant (A := E₁) (G := E₂) (H := P₀sub) a y).1 hyP₀sub
      · simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    intro e he
    let e₁ : E₁ := ⟨e, he⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hforward e₁
    · intro hx
      have hx' := hforward (e₁⁻¹) hx
      simpa [e₁, mul_assoc] using hx'

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_coprime_card_E1_E2_pre
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    Nat.Coprime (Nat.card E₁) (Nat.card E₂) := by
  classical
  rcases hE with ⟨_hcomp, _hE12, hE1, hE2, _hE3⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  rcases hE2 with ⟨hE2E12, hHallE2⟩
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqE1 hqE2
  let r : Nat.Primes := ⟨q, hqprime⟩
  have hr1 : r ∈ section12Tau1Primes M :=
    hHallE1.p_in_pi_of_p_dvd_card r
      (by simpa [natCard_subgroupOf_eq _ _ hE1E12, r] using hqE1)
  have hr2 : r ∈ section12Tau2Primes M :=
    hHallE2.p_in_pi_of_p_dvd_card r
      (by simpa [natCard_subgroupOf_eq _ _ hE2E12, r] using hqE2)
  have h1 : primeRank r.val M = 1 := hr1.2.2
  have h2 : primeRank r.val M = 2 := hr2.2
  omega

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_coprime_card_E12_E3_pre
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    Nat.Coprime (Nat.card E₁₂) (Nat.card E₃) := by
  classical
  rcases hE with ⟨_hcomp, hE12, _hE1, _hE2, hE3⟩
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE3 with ⟨hE3E, hHallE3⟩
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqE12 hqE3
  let r : Nat.Primes := ⟨q, hqprime⟩
  have hr12 : r ∈ section12Tau1Primes M ∪ section12Tau2Primes M :=
    hHallE12.p_in_pi_of_p_dvd_card r
      (by simpa [natCard_subgroupOf_eq _ _ hE12E, r] using hqE12)
  have hr3 : r ∈ section12Tau3Primes M :=
    hHallE3.p_in_pi_of_p_dvd_card r
      (by simpa [natCard_subgroupOf_eq _ _ hE3E, r] using hqE3)
  rcases hr12 with hr1 | hr2
  · exact hr1.2.1 hr3.2.1
  · have h2 : primeRank r.val M = 2 := hr2.2
    have h3 : primeRank r.val M = 1 := hr3.2.2
    omega

public theorem CFSG.section12_pack_complement_from_E2_pre
    {M E E₁₂ E₁ E₂ E₃ A P₀ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hP₀E₂ : P₀ ≤ E₂)
    (hE₂eq : E₂ = subgroupCentralizerIn A (section10Msigma M) ⊔ P₀)
    (hdisj : Disjoint (subgroupCentralizerIn A (section10Msigma M)) P₀)
    (hE₁normP₀ : E₁ ≤ Subgroup.normalizer (P₀ : Set G)) :
    ∃ E₀ : Subgroup G, section12ComplementIn E
      (subgroupCentralizerIn A (section10Msigma M)) E₀ := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  let D : Subgroup G := E₁ ⊔ P₀
  let E₀ : Subgroup G := D ⊔ E₃
  have h12 := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
    (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE
  have hE12E : E₁₂ ≤ E := hE.2.1.1
  have hE1E12 : E₁ ≤ E₁₂ := hE.2.2.1.1
  have hE2E12 : E₂ ≤ E₁₂ := hE.2.2.2.1.1
  have hE3E : E₃ ≤ E := hE.2.2.2.2.1
  have hCE2 : C ≤ E₂ := by
    simpa [C] using
      section12_CA_msigma_le_E2_of_tau2_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
  have hCE : C ≤ E := hCE2.trans (hE2E12.trans hE12E)
  have hP₀E12 : P₀ ≤ E₁₂ := hP₀E₂.trans hE2E12
  have hDE12 : D ≤ E₁₂ := by
    simpa [D] using sup_le hE1E12 hP₀E12
  have hDE : D ≤ E := hDE12.trans hE12E
  have hE₀E : E₀ ≤ E := by
    simpa [E₀] using sup_le hDE hE3E
  refine ⟨E₀, ?_⟩
  refine ⟨hCE, hE₀E, ?_, ?_⟩
  · calc
      E = E₁ ⊔ E₂ ⊔ E₃ := h12.1
      _ = E₁ ⊔ (C ⊔ P₀) ⊔ E₃ := by
        simpa [C] using congrArg (fun X : Subgroup G => E₁ ⊔ X ⊔ E₃) hE₂eq
      _ = C ⊔ E₀ := by
        simp [D, E₀, sup_left_comm, sup_comm]
  · rw [Subgroup.disjoint_def]
    intro x hxC hxE₀
    have hxE2 : x ∈ E₂ := hCE2 hxC
    have hxE12 : x ∈ E₁₂ := hE2E12 hxE2
    have hE3norm : section10NormalIn E₃ E :=
      (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2
    have hE_norm_E3 : E ≤ Subgroup.normalizer (E₃ : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hE3norm.1).1 hE3norm.2
    have hD_norm_E3 : D ≤ Subgroup.normalizer (E₃ : Set G) :=
      hDE.trans hE_norm_E3
    haveI : (E₃.subgroupOf E₀).Normal := by
      simpa [E₀] using
        (Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := D) (N := E₃) hD_norm_E3)
    let x₀ : E₀ := ⟨x, hxE₀⟩
    have hD_E₀ : D ≤ E₀ := by simp [E₀]
    have hE3_E₀ : E₃ ≤ E₀ := by simp [E₀]
    have hDE3_top : D.subgroupOf E₀ ⊔ E₃.subgroupOf E₀ = ⊤ := by
      calc
        D.subgroupOf E₀ ⊔ E₃.subgroupOf E₀ = (D ⊔ E₃).subgroupOf E₀ := by
          symm
          exact Subgroup.subgroupOf_sup
            (A := D) (A' := E₃) (B := E₀) hD_E₀ hE3_E₀
        _ = ⊤ := by simp [E₀]
    have hx₀top : x₀ ∈ D.subgroupOf E₀ ⊔ E₃.subgroupOf E₀ := by
      simp [hDE3_top]
    rcases (Subgroup.mem_sup_of_normal_right
        (s := D.subgroupOf E₀) (t := E₃.subgroupOf E₀) (x := x₀)).1 hx₀top with
      ⟨d₀, hd₀D, z₀, hz₀E3, hdz⟩
    let d : G := d₀
    let z : G := z₀
    have hdD : d ∈ D := by
      simpa [d, D, Subgroup.mem_subgroupOf] using hd₀D
    have hzE3 : z ∈ E₃ := by
      simpa [z, Subgroup.mem_subgroupOf] using hz₀E3
    have hdz_eq_x : d * z = x := by
      simpa [d, z, x₀] using congrArg (fun y : E₀ => (y : G)) hdz
    have hzE12 : z ∈ E₁₂ := by
      have hz_eq : z = d⁻¹ * x := by
        rw [← hdz_eq_x]
        simp
      rw [hz_eq]
      exact E₁₂.mul_mem (E₁₂.inv_mem (hDE12 hdD)) hxE12
    have hE12E3_disj : Disjoint E₁₂ E₃ :=
      Subgroup.disjoint_of_coprime_natCard
        (section12_coprime_card_E12_E3_pre (G := G) (M := M) (E := E)
          (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE)
    have hz_one : z = 1 := by
      have hzbot : z ∈ (⊥ : Subgroup G) := by
        exact Subgroup.disjoint_def.mp hE12E3_disj hzE12 hzE3
      simpa using hzbot
    have hx_eq_d : x = d := by
      rw [← hdz_eq_x, hz_one, mul_one]
    have hdE2 : d ∈ E₂ := by
      simpa [hx_eq_d] using hxE2
    haveI : (P₀.subgroupOf D).Normal := by
      simpa [D] using
        (Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := E₁) (N := P₀) hE₁normP₀)
    let dD : D := ⟨d, hdD⟩
    have hE1_D : E₁ ≤ D := by simp [D]
    have hP₀_D : P₀ ≤ D := by simp [D]
    have hE1P₀_top : E₁.subgroupOf D ⊔ P₀.subgroupOf D = ⊤ := by
      calc
        E₁.subgroupOf D ⊔ P₀.subgroupOf D = (E₁ ⊔ P₀).subgroupOf D := by
          symm
          exact Subgroup.subgroupOf_sup
            (A := E₁) (A' := P₀) (B := D) hE1_D hP₀_D
        _ = ⊤ := by simp [D]
    have hdDtop : dD ∈ E₁.subgroupOf D ⊔ P₀.subgroupOf D := by
      simp [hE1P₀_top]
    rcases (Subgroup.mem_sup_of_normal_right
        (s := E₁.subgroupOf D) (t := P₀.subgroupOf D) (x := dD)).1 hdDtop with
      ⟨eD, heE1, rD, hrP₀, her⟩
    let e : G := eD
    let r : G := rD
    have heE1' : e ∈ E₁ := by
      simpa [e, Subgroup.mem_subgroupOf] using heE1
    have hrP₀' : r ∈ P₀ := by
      simpa [r, Subgroup.mem_subgroupOf] using hrP₀
    have her_eq_d : e * r = d := by
      simpa [e, r, dD] using congrArg (fun y : D => (y : G)) her
    have heE2 : e ∈ E₂ := by
      have hrE2 : r ∈ E₂ := hP₀E₂ hrP₀'
      have he_eq : e = d * r⁻¹ := by
        rw [← her_eq_d]
        simp
      rw [he_eq]
      exact E₂.mul_mem hdE2 (E₂.inv_mem hrE2)
    have hE1E2_disj : Disjoint E₁ E₂ :=
      Subgroup.disjoint_of_coprime_natCard
        (section12_coprime_card_E1_E2_pre (G := G) (M := M) (E := E)
          (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE)
    have he_one : e = 1 := by
      have hebot : e ∈ (⊥ : Subgroup G) := by
        exact Subgroup.disjoint_def.mp hE1E2_disj heE1' heE2
      simpa using hebot
    have hd_eq_r : d = r := by
      rw [← her_eq_d, he_one, one_mul]
    have hxP₀ : x ∈ P₀ := by
      simpa [hx_eq_d, hd_eq_r] using hrP₀'
    exact Subgroup.disjoint_def.mp hdisj hxC hxP₀

/-- Theorem 12.7(d). -/
public theorem CFSG.theorem_12_7_d
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    ∃ E₀ : Subgroup G, section12ComplementIn E
      (subgroupCentralizerIn A (section10Msigma M)) E₀ := by
  obtain ⟨P₀, hP₀E₂, hE₂eq, hdisj, hE₁normP₀⟩ :=
    section12_CA_msigma_complement_in_E2_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  exact
    section12_pack_complement_from_E2_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (P₀ := P₀) (p := p)
      hM hE hp hA hP₀E₂ hE₂eq hdisj hE₁normP₀


end Section12
