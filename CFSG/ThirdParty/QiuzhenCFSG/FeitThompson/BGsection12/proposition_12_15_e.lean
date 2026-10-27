module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.proposition_12_15_d

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# proposition_12_15_e
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section12_prop1215e_tau2
    {M Mstar X : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hX : X ≤ M) (hXne : X ≠ ⊥) (hXq : IsPGroup q.val X)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)))
    (hqσstar : q ∉ section10SigmaPrimes Mstar) :
    q ∈ section12Tau2Primes Mstar := by
  rcases lemma_12_2_a (G := G) (M := M) (Mstar := Mstar) (X := X) (p := q)
      hM hXq hXne hX hMstar with hqσ | hqτ
  · exact False.elim (hqσstar hqσ)
  · exact hqτ

private theorem CFSG.section12_prop1215e_complement
    {M Mstar X : Subgroup G} {q : Nat.Primes}
    {S : Sylow q.val (M ⊓ Mstar : Subgroup G)}
    (hM : M ∈ section9MaximalSubgroups G)
    (hq : q ∈ section10SigmaPrimes M)
    (hX : X ≤ M) (hXne : X ≠ ⊥) (hXq : IsPGroup q.val X)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)))
    (hMstar_ne : Mstar ≠ M)
    (hXS : X ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) S)
    (hqτstar : q ∈ section12Tau2Primes Mstar) :
    section12ComplementIn Mstar (section10Msigma Mstar) (M ⊓ Mstar) := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  let Pamb : Subgroup G := section10AmbientSylowSubgroup (M ⊓ Mstar) S
  have hPamb_p : IsPGroup q.val Pamb := by
    change IsPGroup q.val
      ((S : Subgroup (M ⊓ Mstar : Subgroup G)).map (M ⊓ Mstar : Subgroup G).subtype)
    exact IsPGroup.map S.isPGroup' (M ⊓ Mstar : Subgroup G).subtype
  have hPamb_le_M : Pamb ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2.1
  have hSylowStar : section12SylowSubgroupIn q Pamb Mstar :=
    proposition_12_15_c (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q)
      (S := S) hM hq hX hXne hXq hMstar hMstar_ne hXS
  rcases hSylowStar with ⟨Pstar, hPstar⟩
  have hPamb_le_Mstar : Pamb ≤ Mstar := by
    intro x hx
    have hxPstar : x ∈ section10AmbientSylowSubgroup Mstar Pstar := by
      simpa [Pamb, hPstar] using hx
    exact (section12_ambient_sylow_le (M := Mstar) (p := q) Pstar) hxPstar
  have hPstar_noncyc : ¬ IsCyclic (Pstar : Subgroup Mstar) := by
    intro hcyc
    have hrank_le_one : primeRank q.val Mstar ≤ 1 :=
      section12_primeRank_le_one_of_cyclic_sylow (p := q.val) (R := Mstar) Pstar hcyc
    have hrank_eq_two : primeRank q.val Mstar = 2 := hqτstar.2
    omega
  have hPamb_noncyc : ¬ IsCyclic Pamb := by
    intro hcyc
    have hmap_cyc : IsCyclic (section10AmbientSylowSubgroup Mstar Pstar) := by
      rw [hPstar]
      exact hcyc
    let eP : (Pstar : Subgroup Mstar) ≃*
        section10AmbientSylowSubgroup Mstar Pstar :=
      Subgroup.equivMapOfInjective
        (f := Mstar.subtype) (Pstar : Subgroup Mstar) Mstar.subtype_injective
    exact hPstar_noncyc (eP.isCyclic.mpr hmap_cyc)
  obtain ⟨A, hA_Pamb⟩ :=
    section12_exists_rankTwo_in_noncyclic_pSubgroup
      (G := G) (P := Pamb) (p := q) hPamb_p hPamb_noncyc
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn q M :=
    section12_rankTwo_mono hA_Pamb hPamb_le_M
  have hA_Mstar : A ∈ section12RankTwoElementaryAbelianIn q Mstar :=
    section12_rankTwo_mono hA_Pamb hPamb_le_Mstar
  have hAq : IsPGroup q.val A := by
    have hAelem := (section12_rankTwo_elementary hA_Pamb).2
    have : IsElementaryAbelian q.val A := hAelem
    exact IsElementaryAbelian.isPGroup q.val A
  have hAnoncyc : ¬ IsCyclic A := by
    intro hcyc
    rcases section12_rankTwo_elementary hA_Pamb with ⟨hAcard, hAelem⟩
    have : IsElementaryAbelian q.val A := hAelem
    have hgen : 2 ≤ generatorRank A :=
      section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
        (p := q.val) hAcard
    have hle : generatorRank A ≤ 1 :=
      generatorRank_le_one_of_isCyclic (G := A) hcyc
    omega
  have hAπstar : IsPiSubgroup (G := G) (section10SigmaPrimes Mstar)ᶜ A := by
    intro r hrA
    have hr_eq_q : r = q := by
      simpa using
        (section8_isPiSubgroup_singleton_of_isPGroup (G := G) hAq r hrA)
    subst r
    simpa using hqτstar.1
  rcases section12_exists_EData_containing_sigma_compl_piSubgroup
      (G := G) (M := Mstar) (A := A) hMstar.1
      (section12_rankTwo_le hA_Mstar) hAπstar with
    ⟨Estar, Estar₁₂, Estar₁, Estar₂, Estar₃, hEstar, hA_le_Estar⟩
  have hA_Estar : A ∈ section12RankTwoElementaryAbelianIn q Estar :=
    ⟨hA_le_Estar, section12_rankTwo_elementary hA_Pamb⟩
  have hAnormEstar : section10NormalIn A Estar :=
    (corollary_12_6_a (G := G) (M := Mstar) (E := Estar) (E₁₂ := Estar₁₂)
      (E₁ := Estar₁) (E₂ := Estar₂) (E₃ := Estar₃) (A := A) (p := q)
      hMstar.1 hEstar hqτstar hA_Estar).1
  have hEstar_le_normA : Estar ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAnormEstar.1).1 hAnormEstar.2
  have hnormA_le_M : Subgroup.normalizer (A : Set G) ≤ M :=
    corollary_12_10_d (G := G) (M := M) (P := A) (p := q)
      hM hq hAq (section12_rankTwo_le hA_M) hAnoncyc
  have hEstar_le_M : Estar ≤ M := hEstar_le_normA.trans hnormA_le_M
  have hσstar_inf_M : section10Msigma Mstar ⊓ M = ⊥ :=
    theorem_12_5_e (G := G) (M := Mstar) (A := A) (p := q)
      hMstar.1 hqτstar hA_Mstar M ⟨hM, section12_rankTwo_le hA_M⟩
      hMstar_ne.symm
  exact
    section12_complementIn_inf_of_complementToMsigma_le_of_inf_bot
      (G := G) (M := M) (N := Mstar) (E := Estar)
      hEstar.1 hEstar_le_M hσstar_inf_M

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_notConjugate_symm
    {H K : Subgroup G} (hnot : section12NotConjugate H K) :
    section12NotConjugate K H := by
  intro g hKg
  have hH : H.conjBy g⁻¹ = K := by
    calc
      H.conjBy g⁻¹ = (K.conjBy g).conjBy g⁻¹ := by rw [hKg]
      _ = K := by
        ext x
        constructor
        · intro hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
          simpa [MulAut.conj_apply, mul_assoc] using hz
        · intro hx
          refine Subgroup.mem_map.mpr ?_
          refine ⟨g * x * g⁻¹, ?_, ?_⟩
          · exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
          · simp [mul_assoc]
  exact hnot g⁻¹ hH

private theorem CFSG.section12_not_betaG_of_tau2
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpτ2 : p ∈ section12Tau2Primes M) :
    p ∉ section12BetaPrimesOfGroup G := by
  rcases (by simpa [section12Tau2Primes] using hpτ2) with ⟨hpσ, hrank⟩
  exact by
    simpa [section12BetaPrimesOfGroup] using
      (lemma_10_4_c (G := G) hM hpσ hrank).1

private theorem CFSG.section12_not_beta_of_tau2
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpτ2 : p ∈ section12Tau2Primes M) :
    p ∉ section10BetaPrimes M := by
  intro hpβ
  have hpβG : p ∈ section12BetaPrimesOfGroup G := by
    simpa [section12BetaPrimesOfGroup, section10BetaPrimes] using hpβ.2
  exact section12_not_betaG_of_tau2 (G := G) hM hpτ2 hpβG

public theorem CFSG.section12_not_beta_of_sigma_notconj
    {M Mstar : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hqσ : q ∈ section10SigmaPrimes M) :
    q ∉ section10BetaPrimes Mstar := by
  intro hqβ
  have hdis : Disjoint (section10AlphaPrimes Mstar) (section10SigmaPrimes M) :=
    (lemma_10_12_a (G := G) (M := Mstar) (H := M) hMstar hM
      (section12_notConjugate_symm hnotconj)).2
  rw [Set.disjoint_left] at hdis
  exact hdis hqβ.1 hqσ

omit [IsMinCE G] in
public theorem CFSG.section12_not_beta_of_not_betaG
    {M : Subgroup G} {p : Nat.Primes}
    (hpβG : p ∉ section12BetaPrimesOfGroup G) :
    p ∉ section10BetaPrimes M := by
  intro hpβ
  exact hpβG (by simpa [section12BetaPrimesOfGroup, section10BetaPrimes] using hpβ.2)

private theorem CFSG.section12_prime_dvd_msigma_of_mem_sigma
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpσ : p ∈ section10SigmaPrimes M) :
    p.val ∣ Nat.card (section10Msigma M) := by
  classical
  have hpG : p.val ∣ Nat.card G :=
    hpσ.1.trans (Subgroup.card_subgroup_dvd_card M)
  by_contra hp_not
  have hmul : (section10Msigma M).index * Nat.card (section10Msigma M) = Nat.card G :=
    Subgroup.index_mul_card (H := section10Msigma M)
  have hp_prod : p.val ∣ (section10Msigma M).index * Nat.card (section10Msigma M) := by
    simpa [hmul] using hpG
  rcases p.property.dvd_or_dvd hp_prod with hp_idx | hp_card
  · exact ((theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_index p hp_idx) hpσ
  · exact hp_not hp_card

omit [IsMinCE G] in
private theorem CFSG.section12_ambient_sylow_ne_bot_of_mem_subgroupPrimeSet
    {M : Subgroup G} {p : Nat.Primes} (hpM : p ∈ subgroupPrimeSet M)
    (P : Sylow p.val M) :
    section10AmbientSylowSubgroup M P ≠ ⊥ := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have hP_ne : (P : Subgroup M) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := M) P hpM
  intro hbot
  have hmap_bot :
      (P : Subgroup M).map M.subtype = (⊥ : Subgroup G) := by
    simpa [section10AmbientSylowSubgroup] using hbot
  have hP_bot : (P : Subgroup M) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := (P : Subgroup M)) (f := M.subtype)
      M.subtype_injective).1 hmap_bot
  exact hP_ne hP_bot

private theorem CFSG.section12_ambient_msigma_sylow_ne_bot_of_mem_sigma
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpσ : p ∈ section10SigmaPrimes M)
    (P : Sylow p.val (section10Msigma M)) :
    section10AmbientSylowSubgroup (section10Msigma M) P ≠ ⊥ :=
  section12_ambient_sylow_ne_bot_of_mem_subgroupPrimeSet
    (G := G) (M := section10Msigma M) (p := p)
    (section12_prime_dvd_msigma_of_mem_sigma (G := G) hM hpσ) P

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_conjBy_le_centralizer_conjBy
    {B C : Subgroup G} (hC : C ≤ Subgroup.centralizer (B : Set G)) (g : G) :
    C.conjBy g ≤ Subgroup.centralizer (B.conjBy g : Set G) := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨c, hc, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases Subgroup.mem_map.mp hy with ⟨b, hb, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp (hC hc) b hb
  simpa [MulAut.conj_apply, mul_assoc] using congrArg (fun t : G => g * t * g⁻¹) hcomm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_le_centralizer_symm
    {A B : Subgroup G} (hA : A ≤ Subgroup.centralizer (B : Set G)) :
    B ≤ Subgroup.centralizer (A : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (hA ha) b hb).symm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_conjBy_ne_bot
    {H : Subgroup G} (hH : H ≠ ⊥) (g : G) :
    H.conjBy g ≠ ⊥ := by
  intro hbot
  have hmap_bot :
      H.map ((MulAut.conj g).toMonoidHom) = (⊥ : Subgroup G) := by
    simpa [Subgroup.conjBy] using hbot
  exact hH
    ((Subgroup.map_eq_bot_iff_of_injective
      (H := H) (f := (MulAut.conj g).toMonoidHom)
      (EquivLike.injective (MulAut.conj g))).1 hmap_bot)

private theorem CFSG.section12_prop1215e_beta_subset
    {M Mstar X : Subgroup G} {q : Nat.Primes}
    {S : Sylow q.val (M ⊓ Mstar : Subgroup G)}
    (hM : M ∈ section9MaximalSubgroups G)
    (hq : q ∈ section10SigmaPrimes M)
    (hX : X ≤ M) (hXne : X ≠ ⊥) (hXq : IsPGroup q.val X)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)))
    (hMstar_ne : Mstar ≠ M)
    (hXS : X ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) S)
    (hqτstar : q ∈ section12Tau2Primes Mstar) :
    (subgroupPrimeSet M ∩ section10SigmaPrimes Mstar) ⊆ section10BetaPrimes Mstar := by
  classical
  intro p hp
  rcases hp with ⟨hpM, hpσstar⟩
  by_contra hpβstar
  have : Fact p.val.Prime := ⟨p.property⟩
  have : Fact q.val.Prime := ⟨q.property⟩
  let Pamb : Subgroup G := section10AmbientSylowSubgroup (M ⊓ Mstar) S
  have hPamb_p : IsPGroup q.val Pamb := by
    change IsPGroup q.val
      ((S : Subgroup (M ⊓ Mstar : Subgroup G)).map (M ⊓ Mstar : Subgroup G).subtype)
    exact IsPGroup.map S.isPGroup' (M ⊓ Mstar : Subgroup G).subtype
  have hPamb_le_M : Pamb ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2.1
  have hSylowStar : section12SylowSubgroupIn q Pamb Mstar :=
    proposition_12_15_c (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q)
      (S := S) hM hq hX hXne hXq hMstar hMstar_ne hXS
  rcases hSylowStar with ⟨Qstar, hQstar_eq⟩
  have hPamb_le_Mstar : Pamb ≤ Mstar := by
    intro x hx
    have hxQstar : x ∈ section10AmbientSylowSubgroup Mstar Qstar := by
      simpa [Pamb, hQstar_eq] using hx
    exact (section12_ambient_sylow_le (M := Mstar) (p := q) Qstar) hxQstar
  have hQstar_noncyc : ¬ IsCyclic (Qstar : Subgroup Mstar) := by
    intro hcyc
    have hrank_le_one : primeRank q.val Mstar ≤ 1 :=
      section12_primeRank_le_one_of_cyclic_sylow (p := q.val) (R := Mstar) Qstar hcyc
    have hrank_eq_two : primeRank q.val Mstar = 2 := hqτstar.2
    omega
  have hPamb_noncyc : ¬ IsCyclic Pamb := by
    intro hcyc
    have hmap_cyc : IsCyclic (section10AmbientSylowSubgroup Mstar Qstar) := by
      rw [hQstar_eq]
      exact hcyc
    let eP : (Qstar : Subgroup Mstar) ≃*
        section10AmbientSylowSubgroup Mstar Qstar :=
      Subgroup.equivMapOfInjective
        (f := Mstar.subtype) (Qstar : Subgroup Mstar) Mstar.subtype_injective
    exact hQstar_noncyc (eP.isCyclic.mpr hmap_cyc)
  obtain ⟨A, hA_Pamb⟩ :=
    section12_exists_rankTwo_in_noncyclic_pSubgroup
      (G := G) (P := Pamb) (p := q) hPamb_p hPamb_noncyc
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn q M :=
    section12_rankTwo_mono hA_Pamb hPamb_le_M
  have hA_Mstar : A ∈ section12RankTwoElementaryAbelianIn q Mstar :=
    section12_rankTwo_mono hA_Pamb hPamb_le_Mstar
  have hAq : IsPGroup q.val A := by
    have hAelem := (section12_rankTwo_elementary hA_Pamb).2
    have : IsElementaryAbelian q.val A := hAelem
    exact IsElementaryAbelian.isPGroup q.val A
  have hAπstar : IsPiSubgroup (G := G) (section10SigmaPrimes Mstar)ᶜ A := by
    intro r hrA
    have hr_eq_q : r = q := by
      simpa using
        (section8_isPiSubgroup_singleton_of_isPGroup (G := G) hAq r hrA)
    subst r
    simpa using hqτstar.1
  rcases section12_exists_EData_containing_sigma_compl_piSubgroup
      (G := G) (M := Mstar) (A := A) hMstar.1
      (section12_rankTwo_le hA_Mstar) hAπstar with
    ⟨Estar, Estar₁₂, Estar₁, Estar₂, Estar₃, hEstar, hA_le_Estar⟩
  have hA_Estar : A ∈ section12RankTwoElementaryAbelianIn q Estar :=
    ⟨hA_le_Estar, section12_rankTwo_elementary hA_Pamb⟩
  rcases corollary_12_6_b
      (G := G) (M := Mstar) (E := Estar) (E₁₂ := Estar₁₂)
      (E₁ := Estar₁) (E₂ := Estar₂) (E₃ := Estar₃) (A := A) (p := q)
      hMstar.1 hEstar hqτstar hA_Estar with
    ⟨hCentA_le_norm, hnormA_eq_Estar, _hnotNorm⟩
  have hCentA_le_Estar : Subgroup.centralizer (A : Set G) ≤ Estar := by
    simpa [hnormA_eq_Estar] using hCentA_le_norm
  have hnotconj : section12NotConjugate Mstar M :=
    proposition_12_15_a (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q)
      (S := S) hM hq hX hXne hXq hMstar hMstar_ne hXS
  have hSigmaDisj : Disjoint (section10SigmaPrimes Mstar) (section10SigmaPrimes M) :=
    (corollary_12_6_f
      (G := G) (M := Mstar) (E := Estar) (E₁₂ := Estar₁₂)
      (E₁ := Estar₁) (E₂ := Estar₂) (E₃ := Estar₃) (A := A) (p := q)
      hMstar.1 hEstar hqτstar hA_Estar M hM
      (section12_notConjugate_symm hnotconj)).2
  have hp_notσM : p ∉ section10SigmaPrimes M := by
    rw [Set.disjoint_left] at hSigmaDisj
    exact hSigmaDisj hpσstar
  have hpq : p ≠ q := by
    intro hpq
    exact hqτstar.1 (by simpa [hpq] using hpσstar)
  have hqMstar : q ∈ subgroupPrimeSet Mstar :=
    section12_prime_dvd_card_of_primeRank_pos (R := Mstar) (by
      rw [hqτstar.2]
      norm_num)
  have hqβstar : q ∉ section10BetaPrimes Mstar :=
    section12_not_beta_of_tau2 (G := G) hMstar.1 hqτstar
  have hqβG : q ∉ section12BetaPrimesOfGroup G :=
    section12_not_betaG_of_tau2 (G := G) hMstar.1 hqτstar
  have hqβM : q ∉ section10BetaPrimes M :=
    section12_not_beta_of_not_betaG (G := G) (M := M) hqβG
  have hpβM : p ∉ section10BetaPrimes M := by
    intro hpβM
    exact hp_notσM (section12_sigmaPrimes_mem_of_alphaPrimes_mem hM hpβM.1)
  have hnot_p_lt_q : ¬ p.val < q.val := by
    intro hp_lt_q
    obtain ⟨Pσ, hPσ_cent_A⟩ :=
      corollary_10_9_a_1
        (G := G) (M := Mstar) (X := A) (p := p) (q := q)
        hMstar.1 hpσstar.1 hqMstar hpβstar hqβstar hpq
        (section12_rankTwo_le hA_Mstar) hAq (Or.inr hp_lt_q)
    let PG : Subgroup G := section10AmbientSylowSubgroup (section10Msigma Mstar) Pσ
    have hPG_le_Estar : PG ≤ Estar :=
      hPσ_cent_A.trans hCentA_le_Estar
    have hPG_le_sigma : PG ≤ section10Msigma Mstar :=
      section12_ambient_sylow_le (M := section10Msigma Mstar) (p := p) Pσ
    rcases hEstar.1 with ⟨_hσ_le_Mstar, _hE_le_Mstar, _hsup, hdisj⟩
    have hPG_bot : PG = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      exact Subgroup.disjoint_def.mp hdisj (hPG_le_sigma hx) (hPG_le_Estar hx)
    exact
      (section12_ambient_msigma_sylow_ne_bot_of_mem_sigma
        (G := G) hMstar.1 hpσstar Pσ) hPG_bot
  have hq_lt_p : q.val < p.val := by
    have hpq_val : p.val ≠ q.val := by
      intro hpq_val
      exact hpq (Subtype.ext hpq_val)
    omega
  have hnot_q_lt_p : ¬ q.val < p.val := by
    intro hq_lt_p
    let P : Sylow p.val M := Classical.choice (Sylow.nonempty (p := p.val) (G := M))
    let PG : Subgroup G := section10AmbientSylowSubgroup M P
    have hPGp : IsPGroup p.val PG := by
      change IsPGroup p.val ((P : Subgroup M).map M.subtype)
      exact IsPGroup.map (p := p.val) (H := (P : Subgroup M)) P.isPGroup' M.subtype
    obtain ⟨Qσ, hQσ_cent_PG⟩ :=
      corollary_10_9_a_1
        (G := G) (M := M) (X := PG) (p := q) (q := p)
        hM hq.1 hpM hqβM hpβM hpq.symm
        (section12_ambient_sylow_le (M := M) (p := p) P) hPGp (Or.inr hq_lt_p)
    let Qamb : Subgroup G := section10AmbientSylowSubgroup (section10Msigma M) Qσ
    have hA_le_Msigma : A ≤ section10Msigma M :=
      section12_rankTwo_le_msigma_of_sigma
        (G := G) (M := M) (A := A) (p := q) hM hq hA_M
    let Aσ : Subgroup (section10Msigma M) := A.subgroupOf (section10Msigma M)
    have hAσp : IsPGroup q.val Aσ :=
      hAq.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := A) (K := section10Msigma M)
          hA_le_Msigma).symm
    obtain ⟨QA, hAσ_le_QA⟩ :=
      IsPGroup.exists_le_sylow (G := section10Msigma M) (p := q.val) hAσp
    obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (section10Msigma M) Qσ QA
    have hQA_ambient_eq :
        section10AmbientSylowSubgroup (section10Msigma M) QA =
          Qamb.conjBy (m : G) := by
      rw [← hm]
      simpa [Qamb] using
        section12_ambientSylowSubgroup_smul_local
          (G := G) (M := section10Msigma M) (p := q) Qσ m
    have hA_le_Qconj : A ≤ Qamb.conjBy (m : G) := by
      intro a ha
      have haσ : (⟨a, hA_le_Msigma ha⟩ : section10Msigma M) ∈ Aσ := by
        simpa [Aσ, Subgroup.mem_subgroupOf] using ha
      have haQA : (⟨a, hA_le_Msigma ha⟩ : section10Msigma M) ∈ (QA : Subgroup (section10Msigma M)) :=
        hAσ_le_QA haσ
      have haAmb : a ∈ section10AmbientSylowSubgroup (section10Msigma M) QA :=
        Subgroup.mem_map.mpr ⟨⟨a, hA_le_Msigma ha⟩, haQA, rfl⟩
      simpa [hQA_ambient_eq] using haAmb
    have hQconj_le_cent_PGconj :
        Qamb.conjBy (m : G) ≤ Subgroup.centralizer (PG.conjBy (m : G) : Set G) :=
      section12_conjBy_le_centralizer_conjBy
        (G := G) (B := PG) (C := Qamb) hQσ_cent_PG (m : G)
    have hPGconj_le_cent_Qconj :
        PG.conjBy (m : G) ≤ Subgroup.centralizer (Qamb.conjBy (m : G) : Set G) :=
      section12_le_centralizer_symm hQconj_le_cent_PGconj
    have hPGconj_le_cent_A :
        PG.conjBy (m : G) ≤ Subgroup.centralizer (A : Set G) :=
      hPGconj_le_cent_Qconj.trans
        (Subgroup.centralizer_le
          (show (A : Set G) ⊆ (Qamb.conjBy (m : G) : Set G) from hA_le_Qconj))
    have hPGconj_le_Estar : PG.conjBy (m : G) ≤ Estar :=
      hPGconj_le_cent_A.trans hCentA_le_Estar
    have hPG_ne : PG ≠ ⊥ :=
      section12_ambient_sylow_ne_bot_of_mem_subgroupPrimeSet
        (G := G) (M := M) (p := p) hpM P
    have hPGconj_ne : PG.conjBy (m : G) ≠ ⊥ :=
      section12_conjBy_ne_bot (G := G) hPG_ne (m : G)
    have hPGconj_p : IsPGroup p.val (PG.conjBy (m : G)) := by
      change IsPGroup p.val (PG.map ((MulAut.conj (m : G)).toMonoidHom))
      exact IsPGroup.map (p := p.val) (H := PG) hPGp
        ((MulAut.conj (m : G)).toMonoidHom)
    have hpPGconj : p.val ∣ Nat.card (PG.conjBy (m : G)) := by
      rcases hPGconj_p.card_eq_or_dvd with hcard | hdiv
      · exact False.elim (hPGconj_ne ((Subgroup.card_eq_one (H := PG.conjBy (m : G))).1 hcard))
      · exact hdiv
    have hpEstar : p ∈ subgroupPrimeSet Estar :=
      hpPGconj.trans (Subgroup.card_dvd_of_le hPGconj_le_Estar)
    exact (section12_not_sigma_of_mem_complement hMstar.1 hEstar.1 hpEstar) hpσstar
  omega

/-- Proposition 12.15(e). -/
public theorem CFSG.proposition_12_15_e
    {M Mstar X : Subgroup G} {q : Nat.Primes}
    {S : Sylow q.val (M ⊓ Mstar : Subgroup G)}
    (hM : M ∈ section9MaximalSubgroups G)
    (hq : q ∈ section10SigmaPrimes M)
    (hX : X ≤ M) (hXne : X ≠ ⊥) (hXq : IsPGroup q.val X)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)))
    (hMstar_ne : Mstar ≠ M)
    (hXS : X ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) S)
    (hqσstar : q ∉ section10SigmaPrimes Mstar) :
    q ∈ section12Tau2Primes Mstar ∧
      (subgroupPrimeSet M ∩ section10SigmaPrimes Mstar) ⊆ section10BetaPrimes Mstar ∧
        section12ComplementIn Mstar (section10Msigma Mstar) (M ⊓ Mstar) := by
  classical
  have hqτstar : q ∈ section12Tau2Primes Mstar :=
    section12_prop1215e_tau2
      (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q)
      hM hX hXne hXq hMstar hqσstar
  have hcomp :
      section12ComplementIn Mstar (section10Msigma Mstar) (M ⊓ Mstar) :=
    section12_prop1215e_complement
      (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q) (S := S)
      hM hq hX hXne hXq hMstar hMstar_ne hXS hqτstar
  exact ⟨hqτstar,
    section12_prop1215e_beta_subset
      (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q) (S := S)
      hM hq hX hXne hXq hMstar hMstar_ne hXS hqτstar,
    hcomp⟩

end Section12
