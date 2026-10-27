module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection14.proposition_14_2

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Corollary 14 3 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- Corollary 14.3: centralizing a nonidentity `σ(M)'`-element in
`C_M(x)` gives the `κ(M)` or `τ₂(M)` alternative. -/
public theorem CFSG.corollary_14_3
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {x x' : G}
    (hx : x ∈ section10Msigma M) (hxne : x ≠ 1)
    (hx'ne : x' ≠ 1)
    (hx'cent : x' ∈ elementCentralizerIn M x)
    (hx'sigma' : section14IsPiElement (section10SigmaPrimes M)ᶜ x') :
    (section14ElementPrimeSupport x' ⊆ section14KappaPrimes M ∧
      Subgroup.centralizer ({x} : Set G) ≤ M) ∨
      (section14ElementPrimeSupport x' ⊆ section12Tau2Primes M ∧
        section14SigmaLength x' = 1 ∧
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x'} : Set G)) = {M}) := by
  have hx'M : x' ∈ M := hx'cent.1
  have hxcent' : x ∈ elementCentralizerIn (section10Msigma M) x' := by
    refine ⟨hx, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_singleton_iff.mp hx'cent.2).symm)
  have hcentne : elementCentralizerIn (section10Msigma M) x' ≠ ⊥ := by
    intro hbot
    have hxbot : x ∈ (⊥ : Subgroup G) := by simpa [hbot] using hxcent'
    exact hxne (Subgroup.mem_bot.mp hxbot)
  have hsuppM : section14ElementPrimeSupport x' ⊆ subgroupPrimeSet M :=
    section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hx'M)
  by_cases hτ2 : section14ElementPrimeSupport x' ⊆ section12Tau2Primes M
  · refine Or.inr ?_
    refine ⟨hτ2, ?_, ?_⟩
    · classical
      have sigma_mem_conjBy :
          ∀ {L : Subgroup G} {p : Nat.Primes},
            p ∈ section10SigmaPrimes L → ∀ a : G,
              p ∈ section10SigmaPrimes (L.conjBy a) := by
        intro L p hpσ a
        haveI : Fact p.val.Prime := ⟨p.property⟩
        rcases hpσ with ⟨hpL, P, hN⟩
        let PG : Subgroup G := section10AmbientSylowSubgroup L P
        let PGa : Subgroup G := PG.conjBy a
        have hPG_le_L : PG ≤ L := by
          intro y hy
          rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
          exact z.property
        have hPGa_le_La : PGa ≤ L.conjBy a := by
          intro y hy
          change y ∈ PG.conjBy a at hy
          rw [Subgroup.conjBy, Subgroup.mem_map] at hy
          rw [Subgroup.conjBy, Subgroup.mem_map]
          rcases hy with ⟨z, hz, rfl⟩
          exact ⟨z, hPG_le_L hz, rfl⟩
        have hPG_card : Nat.card PG = Nat.card (P : Subgroup L) := by
          simpa [PG, section10AmbientSylowSubgroup] using
            (Subgroup.card_map_of_injective
              (K := (P : Subgroup L)) (f := L.subtype) L.subtype_injective)
        let Psub : Subgroup (L.conjBy a) := PGa.subgroupOf (L.conjBy a)
        have hPsub_card :
            Nat.card Psub = p.val ^ (Nat.card (L.conjBy a)).factorization p.val := by
          calc
            Nat.card Psub = Nat.card PGa := by
              simpa [Psub] using natCard_subgroupOf_eq PGa (L.conjBy a) hPGa_le_La
            _ = Nat.card PG := by
              simpa [PGa] using section14_card_conjBy (G := G) PG a
            _ = Nat.card (P : Subgroup L) := by
              exact hPG_card
            _ = p.val ^ (Nat.card L).factorization p.val := Sylow.card_eq_multiplicity P
            _ = p.val ^ (Nat.card (L.conjBy a)).factorization p.val := by
              rw [section14_card_conjBy (G := G) L a]
        let P' : Sylow p.val (L.conjBy a) := Sylow.ofCard Psub hPsub_card
        have hP'_ambient : section10AmbientSylowSubgroup (L.conjBy a) P' = PGa := by
          calc
            section10AmbientSylowSubgroup (L.conjBy a) P' =
                (Psub.map (L.conjBy a).subtype : Subgroup G) := by
                  simp [section10AmbientSylowSubgroup, P']
            _ = PGa ⊓ L.conjBy a := Subgroup.subgroupOf_map_subtype PGa (L.conjBy a)
            _ = PGa := inf_eq_left.mpr hPGa_le_La
        refine ⟨?_, P', ?_⟩
        · change p.val ∣ Nat.card (L.conjBy a)
          rw [section14_card_conjBy (G := G) L a]
          exact hpL
        · intro n hn
          have hnPGa : n ∈ Subgroup.normalizer (PGa : Set G) := by
            simpa [hP'_ambient] using hn
          have hPG_fix : PG.conjBy (a⁻¹ * n * a) = PG := by
            have hn_eq : PGa.conjBy n = PGa :=
              section11_conjBy_eq_of_mem_normalizer (H := PGa) hnPGa
            calc
              PG.conjBy (a⁻¹ * n * a) =
                  (PG.conjBy (n * a)).conjBy a⁻¹ := by
                    simpa [mul_assoc] using
                      (section11_conjBy_conjBy (G := G) PG (n * a) a⁻¹).symm
              _ = ((PG.conjBy a).conjBy n).conjBy a⁻¹ := by
                    rw [(section11_conjBy_conjBy (G := G) PG a n).symm]
              _ = (PG.conjBy a).conjBy a⁻¹ := by
                    rw [show (PG.conjBy a).conjBy n = PG.conjBy a by
                      simpa [PGa] using hn_eq]
              _ = PG := section11_conjBy_inv (G := G) PG a
          have hconj :
              a⁻¹ * n * a ∈ Subgroup.normalizer (PG : Set G) :=
            section14_mem_normalizer_of_conjBy_eq (G := G) (H := PG) hPG_fix
          have hnL : a⁻¹ * n * a ∈ L := hN hconj
          rw [Subgroup.conjBy, Subgroup.mem_map]
          exact ⟨a⁻¹ * n * a, hnL, by simp [mul_assoc]⟩
      have hzpow_ne_bot : Subgroup.zpowers x' ≠ ⊥ :=
        (Subgroup.zpowers_ne_bot).2 hx'ne
      have hcard_ne_one : Nat.card (Subgroup.zpowers x') ≠ 1 := by
        intro hcard
        exact hzpow_ne_bot ((Subgroup.eq_bot_iff_card (H := Subgroup.zpowers x')).2 hcard)
      obtain ⟨p, hpprime, hpdiv⟩ := Nat.exists_prime_and_dvd hcard_ne_one
      let q : Nat.Primes := ⟨p, hpprime⟩
      have hqSupp : q ∈ section14ElementPrimeSupport x' := hpdiv
      have hqτ2 : q ∈ section12Tau2Primes M := hτ2 hqSupp
      letI : MulDistribMulAction Unit M := {
        smul := fun _ y => y
        one_smul := fun _ => rfl
        mul_smul := fun _ _ _ => rfl
        smul_mul := fun _ _ _ => rfl
        smul_one := fun _ => rfl }
      have hsolvM : IsSolvable M :=
        IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
      have hcop : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
      obtain ⟨Esub, hEHall, _hEInv⟩ :=
        exists_isHallSubgroup_isInvariant
          (G := M) (A := Unit) hsolvM hcop (section10SigmaPrimes M)ᶜ
      have hσHall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
        (theorem_10_2_b (G := G) hM).2
      have hcompSub : (section10MsigmaSubgroup M).IsComplement' Esub :=
        section11_isComplement_of_isHall_compl hσHall hEHall
      let E : Subgroup G := Esub.map M.subtype
      have hEcomp : section12ComplementToMsigma M E :=
        section14_complement_to_msigma_of_isComplement' hcompSub
      obtain ⟨E₁₂, E₁, E₂, E₃, hE⟩ :=
        section14_exists_EData_of_complement (G := G) (M := M) hM hEcomp
      obtain ⟨A, hA⟩ :=
        section12_exists_rankTwo_in_E_of_tau2
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hqτ2
      have hA_M : A ∈ section12RankTwoElementaryAbelianIn q M :=
        section12_rankTwo_of_EData hE hA
      have hA_le_M : A ≤ M := section12_rankTwo_le hA_M
      have hNormA_proper : Subgroup.normalizer (A : Set G) ≠ ⊤ := by
        intro hnorm_top
        have hA_normal : A.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
        letI : IsSimpleGroup G := IsMinCE.simple
        rcases (haveI := hA_normal; IsSimpleGroup.eq_bot_or_eq_top_of_normal A) with hAbot | hAtop
        · exact (section12_rankTwo_ne_bot hA) hAbot
        · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
            simpa [hAtop] using hA_le_M
          exact hM.1 (top_le_iff.mp htop_le_M)
      obtain ⟨Mstar, hMstar⟩ :=
        section9_exists_maximalSubgroupsContaining_of_ne_top
          (G := G) (H := Subgroup.normalizer (A : Set G)) hNormA_proper
      have hsupp_sigma_star :
          section14ElementPrimeSupport x' ⊆ section10SigmaPrimes Mstar := by
        intro r hr
        exact
          ((lemma_12_11_a
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
            (A := A) (Mstar := Mstar) (p := q)
            hM hE hqτ2 hA hMstar) (hτ2 hr)).1
      have hSigmaSupport_eq :
          section14SigmaSupport x' = {section10SigmaPrimes Mstar} := by
        ext π
        constructor
        · intro hπ
          rcases hπ with ⟨hπblock, hmeet⟩
          rcases hπblock with ⟨H, hH, rfl⟩
          rcases hmeet with ⟨r, hrSupp, hrHσ⟩
          have hrMstarσ : r ∈ section10SigmaPrimes Mstar := hsupp_sigma_star hrSupp
          by_cases hconj : section14ConjugateSubgroups H Mstar
          · rcases hconj with ⟨g, hHg⟩
            have hσeq : section10SigmaPrimes H = section10SigmaPrimes Mstar := by
              ext s
              constructor
              · intro hs
                have hsHg : s ∈ section10SigmaPrimes (Mstar.conjBy g) := by
                  simpa [hHg] using hs
                have hsBack :
                    s ∈ section10SigmaPrimes ((Mstar.conjBy g).conjBy g⁻¹) :=
                  sigma_mem_conjBy hsHg g⁻¹
                simpa [section11_conjBy_inv] using hsBack
              · intro hs
                have hsForw : s ∈ section10SigmaPrimes (Mstar.conjBy g) :=
                  sigma_mem_conjBy hs g
                simpa [hHg] using hsForw
            simp [hσeq]
          · have hHnot : section12NotConjugate H Mstar := by
              intro g hHg
              exact hconj ⟨g⁻¹, by
                simpa [section11_conjBy_inv] using congrArg (fun K => K.conjBy g⁻¹) hHg⟩
            have hdisj : Disjoint (section10SigmaPrimes Mstar) (section10SigmaPrimes H) :=
              theorem_13_9 (G := G) hMstar.1 hH hHnot
            exact False.elim ((Set.disjoint_left.mp hdisj) hrMstarσ hrHσ)
        · intro hπ
          rw [Set.mem_singleton_iff] at hπ
          subst hπ
          refine ⟨⟨Mstar, hMstar.1, rfl⟩, ?_⟩
          exact ⟨q, hqSupp, hsupp_sigma_star hqSupp⟩
      simp [section14SigmaLength, hSigmaSupport_eq]
    · classical
      letI : MulDistribMulAction Unit M := {
        smul := fun _ y => y
        one_smul := fun _ => rfl
        mul_smul := fun _ _ _ => rfl
        smul_mul := fun _ _ _ => rfl
        smul_one := fun _ => rfl }
      have hsolvM : IsSolvable M :=
        IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
      have hcop : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
      obtain ⟨Esub, hEHall, _hEInv⟩ :=
        exists_isHallSubgroup_isInvariant
          (G := M) (A := Unit) hsolvM hcop (section10SigmaPrimes M)ᶜ
      have hσHall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
        (theorem_10_2_b (G := G) hM).2
      have hcompSub : (section10MsigmaSubgroup M).IsComplement' Esub :=
        section11_isComplement_of_isHall_compl hσHall hEHall
      let E : Subgroup G := Esub.map M.subtype
      have hEcomp : section12ComplementToMsigma M E :=
        section14_complement_to_msigma_of_isComplement' hcompSub
      obtain ⟨E₁₂, E₁, E₂, E₃, hE⟩ :=
        section14_exists_EData_of_complement (G := G) (M := M) hM hEcomp
      simpa [section14ElementPrimeSupport] using
        corollary_12_10_e
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (x := x')
          hM hE hx'M hx'ne hτ2 hcentne
  · classical
    have hpWitness :
        ∃ p : Nat.Primes,
          p ∈ section14ElementPrimeSupport x' ∧ p ∉ section12Tau2Primes M := by
      by_contra hno
      apply hτ2
      intro q hqSupp
      by_contra hqnotτ2
      exact hno ⟨q, hqSupp, hqnotτ2⟩
    rcases hpWitness with ⟨p, hpSupp, hpnotτ2⟩
    have hpM : p ∈ subgroupPrimeSet M := hsuppM hpSupp
    have hpnotσ : p ∉ section10SigmaPrimes M := hx'sigma' hpSupp
    have hpτ13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M := by
      rcases section14_tau_split_of_not_sigma hM hpM hpnotσ with hpτ2 | hpτ13
      · exact False.elim (hpnotτ2 hpτ2)
      · exact hpτ13
    obtain ⟨X, hXzp⟩ :=
      section14_exists_primeOrderSubgroupIn_of_dvd_card
        (G := G) (A := Subgroup.zpowers x') (p := p) hpSupp
    rcases hXzp with ⟨hXle_zpow, hXcard⟩
    have hXM : X ≤ M :=
      hXle_zpow.trans (Subgroup.zpowers_le.2 hx'M)
    have hxcentX : x ∈ subgroupCentralizerIn (section10Msigma M) X := by
      refine ⟨hx, ?_⟩
      change x ∈ Subgroup.centralizer (X : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyX
      have hyz : y ∈ Subgroup.zpowers x' := hXle_zpow hyX
      rcases Subgroup.mem_zpowers_iff.mp hyz with ⟨n, rfl⟩
      have hcomm : Commute x x' :=
        Subgroup.mem_centralizer_singleton_iff.mp hxcent'.2
      exact (hcomm.symm.zpow_left n).eq
    have hCXne : subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ := by
      intro hbot
      have hxbot : x ∈ (⊥ : Subgroup G) := by simpa [hbot] using hxcentX
      exact hxne (Subgroup.mem_bot.mp hxbot)
    have hXprimeM : X ∈ section10PrimeOrderSubgroupsIn p M := by
      exact ⟨hXM, hXcard⟩
    have hpκ : p ∈ section14KappaPrimes M := by
      exact ⟨hpτ13, ⟨X, hXprimeM, hCXne⟩⟩
    have hMP : M ∈ section14MFamilyP G := ⟨hM, ⟨p, hpκ⟩⟩
    have hsolvM : IsSolvable M :=
      IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
    letI : MulDistribMulAction Unit M := {
      smul := fun _ y => y
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_mul := fun _ _ _ => rfl
      smul_one := fun _ => rfl }
    let Xsub : Subgroup M := X.subgroupOf M
    have hXsubπ :
        IsPiSubgroup (G := M) (section14KappaPrimes M) Xsub := by
      intro q hqXsub
      have hqdiv : q.val ∣ p.val := by
        have hcard : Nat.card Xsub = Nat.card X := section12_card_subgroupOf_eq hXM
        simpa [Xsub, hcard, hXcard] using hqXsub
      have hqeq : q = p :=
        Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hqdiv)
      simpa [hqeq] using hpκ
    have hXsubInv : IsInvariant Unit M Xsub := by
      refine ⟨?_⟩
      intro _ y
      simp [Xsub]
    have hcop : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
    obtain ⟨Ksub, hKsubHall, _hKsubInv, hXsubK⟩ :=
      exists_isHallSubgroup_isInvariant_of_isPiSubgroup
        (G := M) (A := Unit) hsolvM hcop (section14KappaPrimes M)
        Xsub hXsubπ hXsubInv
    let K : Subgroup G := Ksub.map M.subtype
    have hK : section12HallSubgroupIn (section14KappaPrimes M) K M :=
      section14_hallSubgroupIn_map_subtype hKsubHall
    have hXK : X ≤ K := by
      intro y hyX
      exact Subgroup.mem_map.mpr
        ⟨⟨y, hXM hyX⟩, hXsubK (show (⟨y, hXM hyX⟩ : M) ∈ Xsub from hyX), rfl⟩
    have hXprimeK : X ∈ section12PrimeOrderSubgroups K := by
      exact section14_primeOrderSubgroups_of_primeOrderSubgroupsIn
        (show X ∈ section10PrimeOrderSubgroupsIn p K from ⟨hXK, hXcard⟩)
    have hNXZ := proposition_14_2_b1
      (G := G) (M := M) (K := K) hMP hK X hXprimeK
    have hNXeqZ : subgroupNormalizerIn M (X : Set G) = section14Z M K :=
      hNXZ.1.trans hNXZ.2.1
    have hZdp : section14ZInternalDirectProduct M K := hNXZ.2.2
    have hx'centX : x' ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyX
      have hyz : y ∈ Subgroup.zpowers x' := hXle_zpow hyX
      rcases Subgroup.mem_zpowers_iff.mp hyz with ⟨n, rfl⟩
      exact (Commute.refl x').zpow_left n |>.eq
    have hx'Z : x' ∈ section14Z M K := by
      have hx'NX : x' ∈ subgroupNormalizerIn M (X : Set G) := by
        exact mem_subgroupNormalizerIn.mpr
          ⟨centralizer_le_normalizer X hx'centX, hx'M⟩
      simpa [hNXeqZ] using hx'NX
    have hKstar_normK : section14KStar M K ≤ Subgroup.normalizer (K : Set G) := by
      have hKstar_centK : section14KStar M K ≤ Subgroup.centralizer (K : Set G) := by
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact ((Subgroup.mem_centralizer_iff.mp (hZdp.2.2.2.2 hk)) y hy).symm
      exact hKstar_centK.trans (centralizer_le_normalizer K)
    have hcompZ :
        (K.subgroupOf (section14KStar M K ⊔ K)).IsComplement'
          ((section14KStar M K).subgroupOf (section14KStar M K ⊔ K)) := by
      simpa [inf_comm] using
        section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
          (G := G) (H := K) (R := section14KStar M K)
          hKstar_normK hZdp.2.2.2.1.eq_bot
    have hcardZ :
        Nat.card K * Nat.card (section14KStar M K) = Nat.card (section14Z M K) := by
      simpa [section14Z, sup_comm,
        natCard_subgroupOf_eq K (section14KStar M K ⊔ K) le_sup_right,
        natCard_subgroupOf_eq (section14KStar M K) (section14KStar M K ⊔ K) le_sup_left,
        Nat.mul_comm] using hcompZ.card_mul
    have hsuppκ : section14ElementPrimeSupport x' ⊆ section14KappaPrimes M := by
      intro r hrSupp
      have hrnotσ : r ∉ section10SigmaPrimes M := hx'sigma' hrSupp
      have hrZ : r ∈ subgroupPrimeSet (section14Z M K) :=
        section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hx'Z) hrSupp
      have hrprod : r.val ∣ Nat.card K * Nat.card (section14KStar M K) := by
        rw [hcardZ]
        exact hrZ
      rcases r.2.dvd_mul.mp hrprod with hrK | hrKstar
      · rcases hK with ⟨hKM, hHallK⟩
        exact hHallK.p_in_pi_of_p_dvd_card r
          (by simpa [section12_card_subgroupOf_eq hKM] using hrK)
      · have hrMsigma : r.val ∣ Nat.card (section10Msigma M) := by
          exact hrKstar.trans (Subgroup.card_dvd_of_le (inf_le_left : section14KStar M K ≤ section10Msigma M))
        have hrσ : r ∈ section10SigmaPrimes M :=
          ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card r hrMsigma
        exact False.elim (hrnotσ hrσ)
    obtain ⟨U, hU⟩ := proposition_14_2_a (G := G) (M := M) (K := K) hMP hK
    have hxKstar : x ∈ section14KStar M K := by
      have hCXeq :
          subgroupCentralizerIn (section10Msigma M) X = section14KStar M K :=
        section14_b1_centralizer_eq_kstar_of_prime_manner
          (M := M) (K := K) (X := X) hU.1 hXprimeK
      simpa [hCXeq] using hxcentX
    obtain ⟨q, z, hz_zpowx, hzKstar, hz_ne, hzprime⟩ :=
      section14_exists_primeOrder_zpowers_in
        (G := G) (B := section14KStar M K) hxKstar hxne
    have hzpow_le_xpow : Subgroup.zpowers z ≤ Subgroup.zpowers x :=
      Subgroup.zpowers_le.2 hz_zpowx
    have hzprimeKstar :
        Subgroup.zpowers z ∈ section12PrimeOrderSubgroups (section14KStar M K) :=
      section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hzprime
    have hzuniq :
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer (Subgroup.zpowers z : Set G)) = {M} :=
      (proposition_14_2_c (G := G) (M := M) (K := K) hMP hK).2
        (Subgroup.zpowers z) hzprimeKstar
    have hcentzM : Subgroup.centralizer (Subgroup.zpowers z : Set G) ≤ M := by
      have hMcentz :
          M ∈ section9MaximalSubgroupsContaining
            (Subgroup.centralizer (Subgroup.zpowers z : Set G)) := by
        rw [hzuniq]
        simp
      exact hMcentz.2
    have hcentx_le_centz :
        Subgroup.centralizer ({x} : Set G) ≤
          Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro y hy
      have hyx : y ∈ Subgroup.zpowers x := hzpow_le_xpow hy
      rcases Subgroup.mem_zpowers_iff.mp hyx with ⟨n, rfl⟩
      have hxg : Commute x g :=
        (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
      exact (hxg.zpow_left n).eq
    refine Or.inl ?_
    exact ⟨hsuppκ, hcentx_le_centz.trans hcentzM⟩

end Section14
