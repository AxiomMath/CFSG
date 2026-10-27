module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_17

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_18_a
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
private theorem CFSG.section12_isPiSubgroup_alpha_compl_of_isPGroup_not_mem
    {M X : Subgroup G} {p : Nat.Primes}
    (hpα : p ∉ section10AlphaPrimes M) (hXp : IsPGroup p.val X) :
    IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ X := by
  intro q hqX
  have hq_singleton : q ∈ ({p} : Set Nat.Primes) :=
    section8_isPiSubgroup_singleton_of_isPGroup hXp q hqX
  have hqp : q = p := by simpa using hq_singleton
  rw [Set.mem_compl_iff]
  intro hqα
  exact hpα (by simpa [hqp] using hqα)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_isPiSubgroup_sup_of_le_normalizer_alpha_local
    {π : Set Nat.Primes} {H K : Subgroup G}
    (hHπ : IsPiSubgroup (G := G) π H) (hKπ : IsPiSubgroup (G := G) π K)
    (hHnormK : H ≤ Subgroup.normalizer (K : Set G)) :
    IsPiSubgroup (G := G) π (H ⊔ K) := by
  classical
  let S : Subgroup G := H ⊔ K
  let Hs : Subgroup S := H.subgroupOf S
  let Ks : Subgroup S := K.subgroupOf S
  have hHsπ : IsPiSubgroup (G := S) π Hs := by
    intro q hq
    have hcard : Nat.card Hs = Nat.card H := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := H) (K := S)
          (by simp [S])).toEquiv
    exact hHπ q (by simpa [hcard] using hq)
  have hKsπ : IsPiSubgroup (G := S) π Ks := by
    intro q hq
    have hcard : Nat.card Ks = Nat.card K := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := K) (K := S)
          (by simp [S])).toEquiv
    exact hKπ q (by simpa [hcard] using hq)
  let _ : Ks.Normal := by
    simpa [S, Ks] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := H) (N := K) hHnormK)
  have hHsKs_top : Hs ⊔ Ks = ⊤ := by
    calc
      Hs ⊔ Ks = S.subgroupOf S := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := H) (A' := K) (B := S)
          (by simp [S])
          (by simp [S])
      _ = ⊤ := by simp
  have htopπ : IsPiSubgroup (G := S) π (⊤ : Subgroup S) := by
    rw [← hHsKs_top]
    exact section12_isPiSubgroup_sup_of_normal_right_local
      (G := S) (π := π) (H := Hs) (K := Ks) hHsπ hKsπ
  intro q hq
  exact htopπ q (by simpa using hq)

omit [IsMinCE G] in
private theorem CFSG.section12_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank
    {p : ℕ} {R : Type*} [Group R] [Finite R] (hrank : 3 ≤ primeRank p R) :
    ∃ A : Subgroup R, IsPGroup p A ∧ IsMulCommutative A ∧ 3 ≤ generatorRank A := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup p A ∧ IsMulCommutative A ∧
      n ≤ generatorRank A}
  have hrank' : 2 < sSup T := by
    exact lt_of_lt_of_le (by decide : 2 < 3) (by simpa [primeRank, T] using hrank)
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section8_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 2 < sSup T := by simp [hTempty]
    exact this hrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨A, hAp, hAcomm, htSup_le⟩
  exact ⟨A, hAp, hAcomm, Nat.succ_le_of_lt (lt_of_lt_of_le hrank' htSup_le)⟩

private theorem CFSG.section12_malpha_centralizer_rank_le_one_of_not_unique_normalizer
    {M X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hXle : X ≤ M) (hXne : X ≠ ⊥) (hXp : IsPGroup p.val X)
    (hpα : p ∉ section10AlphaPrimes M)
    (hnotUnique :
      section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {M}) :
    groupRank (subgroupCentralizerIn (section10Malpha M) X) ≤ 1 := by
  classical
  by_contra hle
  have hcentRank : 1 < groupRank (subgroupCentralizerIn (section10Malpha M) X) := by
    omega
  have hXπ : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ X :=
    section12_isPiSubgroup_alpha_compl_of_isPGroup_not_mem
      (G := G) (M := M) hpα hXp
  have hDunique : subgroupCentralizerIn M X ∈ section9UniqueSubgroups G :=
    lemma_10_3 (G := G) (M := M) (X := X) hM hXle hXπ hcentRank
  let D : Subgroup G := subgroupCentralizerIn M X
  have hDleM : D ≤ M := inf_le_left
  have hDuniq_eq : section9MaximalSubgroupsContaining D = {M} :=
    section12_unique_overgroups_eq_of_contains_maximal_local
      (G := G) (H := D) (M := M) hDunique hM hDleM
  have hDle_normX : D ≤ Subgroup.normalizer (X : Set G) :=
    (inf_le_right : D ≤ Subgroup.centralizer (X : Set G)).trans
      (centralizer_le_normalizer X)
  have hXne_top : X ≠ ⊤ := by
    intro hXtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hXtop] using hXle
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hnorm_proper : Subgroup.normalizer (X : Set G) ≠ ⊤ :=
    section12_normalizer_ne_top_of_ne_bot_ne_top (G := G) hXne hXne_top
  have hnorm_le_M : Subgroup.normalizer (X : Set G) ≤ M :=
    section12_le_unique_maximal_of_le
      (G := G) (Y := D) (X := Subgroup.normalizer (X : Set G)) (M := M)
      hDle_normX hnorm_proper hDuniq_eq
  have hsingle :
      section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) = {M} := by
    ext N
    constructor
    · intro hN
      have hN_D : N ∈ section9MaximalSubgroupsContaining D :=
        ⟨hN.1, hDle_normX.trans hN.2⟩
      have hN_eq : N = M := by
        have hsingleN : N ∈ ({M} : Set (Subgroup G)) := by
          simpa [hDuniq_eq] using hN_D
        simpa using hsingleN
      simp [hN_eq]
    · intro hN
      have hN_eq : N = M := by simpa using hN
      subst N
      exact ⟨hM, hnorm_le_M⟩
  exact hnotUnique hsingle

private theorem CFSG.section12_not_unique_normalizer_of_tau1_primeOrder
    {M P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M) :
    section9MaximalSubgroupsContaining (Subgroup.normalizer (P : Set G)) ≠ {M} := by
  classical
  intro hsingle
  rcases (by simpa [section12Tau1Primes] using hp) with
    ⟨hp_notσ, _hpD, hprank_one⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hPleM, _hPcard⟩
  have hPp : IsPGroup p.val P :=
    section12_primeOrderSubgroupsIn_isPGroup (G := G) (A := M) hP
  have hPne : P ≠ ⊥ := section12_primeOrder_ne_bot (G := G) hP
  have hMcont : M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (P : Set G)) := by
    simp [hsingle]
  have hpσ_or_tau2 :
      p ∈ section10SigmaPrimes M ∪ section12Tau2Primes M :=
    lemma_12_2_a (G := G) (M := M) (Mstar := M) (X := P) (p := p)
      hM hPp hPne hPleM hMcont
  rcases hpσ_or_tau2 with hpσ | hpτ2
  · exact hp_notσ hpσ
  · rcases (by simpa [section12Tau2Primes] using hpτ2) with
      ⟨_hp_notσ, hprank_two⟩
    rw [hprank_one] at hprank_two
    omega

private theorem CFSG.section12_malpha_centralizer_rank_le_one_of_tau1_primeOrder
    {M P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M) :
    groupRank (subgroupCentralizerIn (section10Malpha M) P) ≤ 1 := by
  classical
  rcases (by simpa [section12Tau1Primes] using hp) with
    ⟨hp_notσ, _hpD, _hprank_one⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hPleM, _hPcard⟩
  have hp_notα : p ∉ section10AlphaPrimes M := by
    intro hpα
    exact hp_notσ (section12_sigmaPrimes_mem_of_alphaPrimes_mem (G := G) hM hpα)
  have hPp : IsPGroup p.val P :=
    section12_primeOrderSubgroupsIn_isPGroup (G := G) (A := M) hP
  have hPne : P ≠ ⊥ := section12_primeOrder_ne_bot (G := G) hP
  exact
    section12_malpha_centralizer_rank_le_one_of_not_unique_normalizer
      (G := G) (M := M) (X := P) (p := p)
      hM hPleM hPne hPp hp_notα
      (section12_not_unique_normalizer_of_tau1_primeOrder
        (G := G) (M := M) (P := P) (p := p) hM hp hP)

private theorem CFSG.section12_exists_alpha_prime_of_malpha_ne_bot
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hMα : section10Malpha M ≠ ⊥) :
    ∃ r : Nat.Primes, r ∈ section10AlphaPrimes M := by
  classical
  have hcard_ne_one : Nat.card (section10Malpha M) ≠ 1 := by
    intro hcard
    exact hMα ((Subgroup.card_eq_one (H := section10Malpha M)).1 hcard)
  obtain ⟨r, hrprime, hrdiv⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let r' : Nat.Primes := ⟨r, hrprime⟩
  exact ⟨r', (theorem_10_2_a (G := G) hM).1.p_in_pi_of_p_dvd_card r' hrdiv⟩

private theorem CFSG.section12_malpha_sylow_groupRank_ge_three_of_mem_alpha
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {r : Nat.Primes}
    (hrα : r ∈ section10AlphaPrimes M)
    (R : Sylow r.val (section10Malpha M)) :
    3 ≤ groupRank (R : Subgroup (section10Malpha M)) := by
  classical
  let _ : Fact r.val.Prime := ⟨r.property⟩
  have hrrankM : 3 ≤ primeRank r.val M := Nat.succ_le_of_lt hrα.2
  obtain ⟨A, hAp, hAcomm, hAgen⟩ :=
    section12_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank
      (p := r.val) (R := M) hrrankM
  have hA_le_K : A ≤ section10MalphaSubgroup M := by
    exact section12_pSubgroup_le_normal_hall_of_prime_mem
      (R := M) (π := section10AlphaPrimes M) (H := section10MalphaSubgroup M)
      (A := A) (theorem_10_2_a (G := G) hM).2 hrα hAp
  let AG : Subgroup G := A.map M.subtype
  have hAG_le_malpha : AG ≤ section10Malpha M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, haA, rfl⟩
    exact Subgroup.mem_map.mpr ⟨a, hA_le_K haA, rfl⟩
  let Aα : Subgroup (section10Malpha M) := AG.subgroupOf (section10Malpha M)
  have hAGp : IsPGroup r.val AG := by
    simpa [AG] using IsPGroup.map (p := r.val) (H := A) hAp M.subtype
  have hAαp : IsPGroup r.val Aα := by
    exact hAGp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := AG) (K := section10Malpha M) hAG_le_malpha).symm
  have hAGcomm : IsMulCommutative AG := by
    let _ : IsMulCommutative A := hAcomm
    simpa [AG] using Subgroup.map_isMulCommutative (f := M.subtype) (H := A)
  have hAαcomm : IsMulCommutative Aα := by
    let _ : IsMulCommutative AG := hAGcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := AG) (K := section10Malpha M)
  have hAG_gen_eq : generatorRank AG = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr
      (Subgroup.equivMapOfInjective (f := M.subtype) A M.subtype_injective).symm
  have hAα_gen_eq : generatorRank Aα = generatorRank AG := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr
      (Subgroup.subgroupOfEquivOfLe (H := AG) (K := section10Malpha M) hAG_le_malpha)
  have hAαgen : 3 ≤ generatorRank Aα := by
    simpa [hAα_gen_eq, hAG_gen_eq] using hAgen
  have hprimeRank_malpha : 3 ≤ primeRank r.val (section10Malpha M) := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card (section10Malpha M), ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <|
        (section8_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
    · exact ⟨Aα, hAαp, hAαcomm, hAαgen⟩
  exact hprimeRank_malpha.trans
    (section10_primeRank_le_groupRank_sylow (G := section10Malpha M) R)

private theorem CFSG.section12_exists_alpha_invariant_sylow_malpha
    {M X : Subgroup G} [Subgroup.Normalizes X (section10Malpha M)]
    (hM : M ∈ section9MaximalSubgroups G)
    (hMα : section10Malpha M ≠ ⊥)
    (hXπ : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ X) :
    ∃ (r : Nat.Primes) (R : Sylow r.val (section10Malpha M)),
      r ∈ section10AlphaPrimes M ∧
        IsInvariant X (section10Malpha M) (R : Subgroup (section10Malpha M)) ∧
          3 ≤ groupRank (R : Subgroup (section10Malpha M)) := by
  classical
  obtain ⟨r, hrα⟩ := section12_exists_alpha_prime_of_malpha_ne_bot
    (G := G) (M := M) hM hMα
  let _ : Fact r.val.Prime := ⟨r.property⟩
  have hXπgroup : IsPiGroup (section10AlphaPrimes M)ᶜ X :=
    IsPiSubgroup.isPiGroup X hXπ
  have hMαπsub : IsPiSubgroup (G := G) (section10AlphaPrimes M) (section10Malpha M) :=
    (theorem_10_2_a (G := G) hM).1.p_in_pi_of_p_dvd_card
  have hMαπgroup : IsPiGroup (section10AlphaPrimes M) (section10Malpha M) :=
    IsPiSubgroup.isPiGroup (section10Malpha M) hMαπsub
  have hMαproper : section10Malpha M ≠ ⊤ := by
    intro htop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [htop] using (section10_malpha_le (G := G) (M := M))
    exact hM.1 (eq_top_iff.2 htop_le_M)
  have hMαsolv : Group.IsSolvable (section10Malpha M) :=
    IsMinCE.proper_subgroups_solvable
      (section10Malpha M) (lt_top_iff_ne_top.2 hMαproper)
  obtain ⟨R, hRinv⟩ :=
    exists_invariant_sylow_of_pi_complement_action
      (G := section10Malpha M) (A := X) (π := section10AlphaPrimes M)
      hMαπgroup hXπgroup hMαsolv hrα
  exact ⟨r, R, hrα, hRinv,
    section12_malpha_sylow_groupRank_ge_three_of_mem_alpha
      (G := G) (M := M) hM hrα R⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_centralizer_witness_image_isInvariant
    {M X : Subgroup G} [Subgroup.Normalizes X (section10Malpha M)]
    (A : Subgroup (subgroupCentralizerIn (section10Malpha M) X)) :
    let C : Subgroup G := subgroupCentralizerIn (section10Malpha M) X
    let ι : C →* section10Malpha M :=
      Subgroup.inclusion (show C ≤ section10Malpha M by exact inf_le_left)
    IsInvariant X (section10Malpha M) (A.map ι) := by
  let C : Subgroup G := subgroupCentralizerIn (section10Malpha M) X
  let ι : C →* section10Malpha M :=
    Subgroup.inclusion (show C ≤ section10Malpha M by exact inf_le_left)
  change IsInvariant X (section10Malpha M) (A.map ι)
  have hforward :
      ∀ x : X, ∀ y : section10Malpha M, y ∈ A.map ι → x • y ∈ A.map ι := by
    intro x y hy
    rcases Subgroup.mem_map.mp hy with ⟨a, haA, rfl⟩
    have hfixed : x • (ι a) = ι a := by
      apply Subtype.ext
      have hιa : ((ι a : section10Malpha M) : G) = ((a : C) : G) := rfl
      have hcomm :
          (x : G) * ((a : C) : G) = ((a : C) : G) * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp (a : C).property.2) (x : G) x.property
      calc
        ((x • (ι a) : section10Malpha M) : G) =
            (x : G) * ((ι a : section10Malpha M) : G) * (x : G)⁻¹ := by
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        _ = (x : G) * ((a : C) : G) * (x : G)⁻¹ := by rw [hιa]
        _ = ((a : C) : G) * (x : G) * (x : G)⁻¹ := by rw [hcomm]
        _ = ((ι a : section10Malpha M) : G) := by rw [hιa]; simp [mul_assoc]
    exact Subgroup.mem_map.mpr ⟨a, haA, hfixed.symm⟩
  refine ⟨?_⟩
  intro x y
  constructor
  · exact hforward x y
  · intro hy
    have hback := hforward x⁻¹ (x • y) hy
    simpa [← mul_smul] using hback

private theorem CFSG.section12_exists_alpha_invariant_sylow_malpha_containing_witness
    {M X : Subgroup G} [Subgroup.Normalizes X (section10Malpha M)]
    (hM : M ∈ section9MaximalSubgroups G)
    (hXπ : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ X)
    {r : Nat.Primes}
    (A : Subgroup (subgroupCentralizerIn (section10Malpha M) X))
    (hAp : IsPGroup r.val A) :
    ∃ R : Sylow r.val (section10Malpha M),
      IsInvariant X (section10Malpha M) (R : Subgroup (section10Malpha M)) ∧
        A.map (Subgroup.inclusion
          (show subgroupCentralizerIn (section10Malpha M) X ≤ section10Malpha M by
            exact inf_le_left)) ≤ (R : Subgroup (section10Malpha M)) := by
  classical
  let C : Subgroup G := subgroupCentralizerIn (section10Malpha M) X
  let ι : C →* section10Malpha M :=
    Subgroup.inclusion (show C ≤ section10Malpha M by exact inf_le_left)
  let Aα : Subgroup (section10Malpha M) := A.map ι
  let _ : Fact r.val.Prime := ⟨r.property⟩
  have hAαp : IsPGroup r.val Aα := by
    simpa [Aα] using IsPGroup.map (p := r.val) (H := A) hAp ι
  have hAαπ : IsPiSubgroup (G := section10Malpha M) ({r} : Set Nat.Primes) Aα :=
    section8_isPiSubgroup_singleton_of_isPGroup (G := section10Malpha M)
      (H := Aα) (q := r) hAαp
  have hAαinv : IsInvariant X (section10Malpha M) Aα := by
    simpa [Aα, C, ι] using
      section12_centralizer_witness_image_isInvariant (G := G) (M := M) (X := X) A
  have hMαproper : section10Malpha M ≠ ⊤ := by
    intro htop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [htop] using (section10_malpha_le (G := G) (M := M))
    exact hM.1 (eq_top_iff.2 htop_le_M)
  have hMαsolv : Group.IsSolvable (section10Malpha M) :=
    IsMinCE.proper_subgroups_solvable
      (section10Malpha M) (lt_top_iff_ne_top.2 hMαproper)
  have hXπgroup : IsPiGroup (section10AlphaPrimes M)ᶜ X :=
    IsPiSubgroup.isPiGroup X hXπ
  have hMαπsub : IsPiSubgroup (G := G) (section10AlphaPrimes M) (section10Malpha M) :=
    (theorem_10_2_a (G := G) hM).1.p_in_pi_of_p_dvd_card
  have hMαπgroup : IsPiGroup (section10AlphaPrimes M) (section10Malpha M) :=
    IsPiSubgroup.isPiGroup (section10Malpha M) hMαπsub
  have hcop_X_malpha : Nat.Coprime (Nat.card X) (Nat.card (section10Malpha M)) := by
    rw [IsPiGroup_iff] at hXπgroup hMαπgroup
    refine Nat.coprime_of_dvd ?_
    intro q hqprime hqX hqMα
    let q' : Nat.Primes := ⟨q, hqprime⟩
    exact (hXπgroup q' hqX) (hMαπgroup q' hqMα)
  obtain ⟨H, hHHall, hHinv, hAαH⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := section10Malpha M) (A := X) hMαsolv hcop_X_malpha
      ({r} : Set Nat.Primes) Aα hAαπ hAαinv
  have hHπ : IsPiSubgroup (G := section10Malpha M) ({r} : Set Nat.Primes) H :=
    hHHall.p_in_pi_of_p_dvd_card
  have hHp : IsPGroup r.val H :=
    section8_isPGroup_of_isPiSubgroup_singleton (G := section10Malpha M)
      (H := H) (q := r) hHπ
  have hr_not_dvd_index : ¬ r.val ∣ H.index := by
    intro hridx
    exact (hHHall.p_in_pi_of_p_dvd_index r hridx) (by simp)
  let R : Sylow r.val (section10Malpha M) := hHp.toSylow hr_not_dvd_index
  refine ⟨R, ?_, ?_⟩
  · simpa [R] using hHinv
  · simpa [R, Aα, C, ι] using hAαH

omit [IsMinCE G] in
private theorem CFSG.section12_lemma_12_18_a_sylow_not_le_centralizer_Q
    {M Q : Subgroup G} {r : Nat.Primes}
    (R : Sylow r.val (section10Malpha M))
    (hCQrank : groupRank (subgroupCentralizerIn (section10Malpha M) Q) ≤ 1)
    (hRrank : 3 ≤ groupRank (R : Subgroup (section10Malpha M))) :
    ¬ (R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype ≤
        Subgroup.centralizer (Q : Set G) := by
  classical
  intro hRcent
  let RG : Subgroup G :=
    (R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype
  have hRGleC : RG ≤ subgroupCentralizerIn (section10Malpha M) Q := by
    intro x hx
    have hxMα : x ∈ section10Malpha M := by
      rcases Subgroup.mem_map.mp hx with ⟨a, _haR, rfl⟩
      exact a.property
    exact ⟨hxMα, hRcent hx⟩
  let Rsub : Subgroup (subgroupCentralizerIn (section10Malpha M) Q) :=
    RG.subgroupOf (subgroupCentralizerIn (section10Malpha M) Q)
  let eRsub : Rsub ≃* RG :=
    Subgroup.subgroupOfEquivOfLe (H := RG)
      (K := subgroupCentralizerIn (section10Malpha M) Q) hRGleC
  have hRG_le_Crank : groupRank RG ≤ groupRank (subgroupCentralizerIn (section10Malpha M) Q) :=
    (groupRank_le_of_equiv eRsub).trans
      (section8_groupRank_le_of_subgroup Rsub)
  let eRG : (R : Subgroup (section10Malpha M)) ≃* RG :=
    Subgroup.equivMapOfInjective
      (f := (section10Malpha M).subtype) (R : Subgroup (section10Malpha M))
      (section10Malpha M).subtype_injective
  have hRrank_le_RG : groupRank (R : Subgroup (section10Malpha M)) ≤ groupRank RG :=
    groupRank_le_of_equiv eRG.symm
  have hRrank_le_one : groupRank (R : Subgroup (section10Malpha M)) ≤ 1 :=
    hRrank_le_RG.trans (hRG_le_Crank.trans hCQrank)
  omega

private theorem CFSG.section12_lemma_12_18_a_exists_critical_subgroup
    {M : Subgroup G} {r : Nat.Primes}
    (hrα : r ∈ section10AlphaPrimes M)
    (R : Sylow r.val (section10Malpha M))
    (hRrank : 3 ≤ groupRank (R : Subgroup (section10Malpha M))) :
    ∃ R1 : Subgroup (R : Subgroup (section10Malpha M)),
      R1.Characteristic ∧
        (⁅R1, ⊤⁆ ≤ centerIn (G := (R : Subgroup (section10Malpha M))) R1) ∧
        NilpotencyClassLe 2 (↥R1) ∧
        (Monoid.exponent (↥R1) = r.val) ∧
        IsPGroup r.val
          (↥(fixingSubgroup
            (M := MulAut (R : Subgroup (section10Malpha M)))
            (α := (R : Subgroup (section10Malpha M))) (R1 : Set (R : Subgroup (section10Malpha M))))) := by
  classical
  let _ : Fact r.val.Prime := ⟨r.property⟩
  have hr_dvd_G : r.val ∣ Nat.card G :=
    hrα.1.trans (Subgroup.card_subgroup_dvd_card M)
  have hrodd : r.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hr_dvd_G
  have hRp : IsPGroup r.val (R : Subgroup (section10Malpha M)) := R.isPGroup'
  let _ : Fact (IsPGroup r.val (R : Subgroup (section10Malpha M))) := ⟨hRp⟩
  have hR_nontrivial : Nontrivial (R : Subgroup (section10Malpha M)) := by
    refine not_subsingleton_iff_nontrivial.mp ?_
    intro hsub
    let _ : Subsingleton (R : Subgroup (section10Malpha M)) := hsub
    have hcyc : IsCyclic (R : Subgroup (section10Malpha M)) := inferInstance
    have hRank_le_one :
        groupRank (R : Subgroup (section10Malpha M)) ≤ 1 :=
      groupRank_le_one_of_isCyclic (R : Subgroup (section10Malpha M))
    exact (by decide : ¬ 3 ≤ (1 : ℕ)) (le_trans hRrank hRank_le_one)
  let _ : Nontrivial (R : Subgroup (section10Malpha M)) := hR_nontrivial
  simpa using
    theorem_1_13 (G := (R : Subgroup (section10Malpha M))) (p := r.val) hrodd

omit [IsMinCE G] in
private theorem CFSG.section12_action_trivial_of_coprime_range_le_fixing
    {A R : Type*} [Group A] [Finite A] [Group R] [Finite R]
    [MulDistribMulAction A R] {p : ℕ} [Fact p.Prime] {D : Subgroup R}
    (hcop : Nat.Coprime p (Nat.card A))
    (hfix : IsPGroup p
      (↥(fixingSubgroup (M := MulAut R) (α := R) (D : Set R))))
    (hRangeFix :
      (MulDistribMulAction.toMulAut A R).range ≤
        fixingSubgroup (M := MulAut R) (α := R) (D : Set R)) :
    ∀ a : A, ∀ x : R, a • x = x := by
  classical
  let φ : A →* MulAut R := MulDistribMulAction.toMulAut A R
  let F : Subgroup (MulAut R) := fixingSubgroup (M := MulAut R) (α := R) (D : Set R)
  let I : Subgroup (MulAut R) := φ.range
  have hIF : I ≤ F := by
    simpa [I, F, φ] using hRangeFix
  have hIcop : Nat.Coprime p (Nat.card I) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_range_dvd φ) hcop
  let IF : Subgroup F := I.subgroupOf F
  have hIFp : IsPGroup p IF := hfix.to_subgroup IF
  have hIFcard : Nat.card IF = Nat.card I := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := I) (K := F) hIF).toEquiv
  obtain ⟨n, hIcard_p⟩ := hIFp.exists_card_eq
  have hIcard_p' : Nat.card I = p ^ n := by
    simpa [hIFcard] using hIcard_p
  have hIcard_one : Nat.card I = 1 := by
    have hcop_pow : Nat.Coprime p (p ^ n) := by
      simpa [hIcard_p'] using hIcop
    have hnzero : n = 0 := by
      by_contra hn0
      have hpdvd : p ∣ p ^ n := dvd_pow_self p (Nat.pos_iff_ne_zero.mpr hn0).ne'
      exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcop_pow) hpdvd
    simp [hIcard_p', hnzero]
  have hIbot : I = ⊥ := (Subgroup.card_eq_one (H := I)).1 hIcard_one
  intro a x
  have hφmem : φ a ∈ I := ⟨a, rfl⟩
  have hφone : φ a = 1 := by
    have hbotmem : φ a ∈ (⊥ : Subgroup (MulAut R)) := by
      simpa [hIbot] using hφmem
    simpa using hbotmem
  have happly := congrArg (fun ψ : MulAut R => ψ x) hφone
  simpa [φ] using happly

omit [IsMinCE G] in
private theorem CFSG.section12_lemma_12_18_a_critical_not_le_centralizer_Q
    {M P Q : Subgroup G} {q r : Nat.Primes}
    [Subgroup.Normalizes (P ⊔ Q) (section10Malpha M)]
    (hQq : IsPGroup q.val Q)
    (hqα : q ∉ section10AlphaPrimes M)
    (hrα : r ∈ section10AlphaPrimes M)
    (R : Sylow r.val (section10Malpha M))
    (hRinv : IsInvariant (↥(P ⊔ Q)) (section10Malpha M)
      (R : Subgroup (section10Malpha M)))
    {R1 : Subgroup (R : Subgroup (section10Malpha M))}
    (hR1fix : IsPGroup r.val
      (↥(fixingSubgroup
        (M := MulAut (R : Subgroup (section10Malpha M)))
        (α := (R : Subgroup (section10Malpha M)))
        (R1 : Set (R : Subgroup (section10Malpha M))))))
    (hRnoncentral :
      ¬ (R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype ≤
        Subgroup.centralizer (Q : Set G)) :
    ¬ (R1.map (R : Subgroup (section10Malpha M)).subtype).map
        (section10Malpha M).subtype ≤ Subgroup.centralizer (Q : Set G) := by
  classical
  intro hR1cent
  have hqr : q ≠ r := by
    intro h
    subst h
    exact hqα hrα
  have hQcopR : Nat.Coprime r.val (Nat.card Q) := by
    exact (section8_coprime_prime_card_of_isPGroup_ne (G := G)
      (R := Q) (q := r) (r := q) (by simpa [eq_comm] using hqr) hQq)
  let _ : Fact r.val.Prime := ⟨r.property⟩
  let Rsub : Subgroup (section10Malpha M) := (R : Subgroup (section10Malpha M))
  let ιQ : Q →* (P ⊔ Q : Subgroup G) :=
    Subgroup.inclusion (show Q ≤ P ⊔ Q by exact le_sup_right)
  let _ : MulDistribMulAction (↥Q) Rsub :=
    MulDistribMulAction.compHom Rsub ιQ
  have hsmul_coe :
      ∀ q0 : Q, ∀ x : Rsub,
        (((q0 • x : Rsub) : section10Malpha M) : G) =
          (q0 : G) * (((x : Rsub) : section10Malpha M) : G) * (q0 : G)⁻¹ := by
    intro q0 x
    change ((((ιQ q0) • x : Rsub) : section10Malpha M) : G) =
      (q0 : G) * (((x : Rsub) : section10Malpha M) : G) * (q0 : G)⁻¹
    calc
      ((((ιQ q0) • x : Rsub) : section10Malpha M) : G)
          = (((ιQ q0) • (x : section10Malpha M) : section10Malpha M) : G) := rfl
      _ = ((ιQ q0 : ↥(P ⊔ Q)) : G) *
            (((x : Rsub) : section10Malpha M) : G) * ((ιQ q0 : ↥(P ⊔ Q)) : G)⁻¹ := by
            simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      _ = (q0 : G) * (((x : Rsub) : section10Malpha M) : G) * (q0 : G)⁻¹ := rfl
  have hRangeFix :
      (MulDistribMulAction.toMulAut (↥Q) Rsub).range ≤
        fixingSubgroup (M := MulAut Rsub) (α := Rsub) (R1 : Set Rsub) := by
    intro ψ hψ
    rcases hψ with ⟨q0, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro x hxR1
    apply Subtype.ext
    apply Subtype.ext
    have hxR1G :
        (((x : Rsub) : section10Malpha M) : G) ∈
          (R1.map Rsub.subtype).map (section10Malpha M).subtype := by
      exact Subgroup.mem_map.mpr
        ⟨(x : section10Malpha M), Subgroup.mem_map.mpr ⟨x, hxR1, rfl⟩, rfl⟩
    have hxcent :
        (((x : Rsub) : section10Malpha M) : G) ∈
          Subgroup.centralizer (Q : Set G) :=
      hR1cent hxR1G
    have hcomm :
        (q0 : G) * (((x : Rsub) : section10Malpha M) : G) =
          (((x : Rsub) : section10Malpha M) : G) * (q0 : G) := by
      simpa using
        (Subgroup.mem_centralizer_iff.mp hxcent (q0 : G) q0.property)
    calc
      (((MulDistribMulAction.toMulAut (↥Q) Rsub q0 x : Rsub) :
          section10Malpha M) : G)
          = (q0 : G) * (((x : Rsub) : section10Malpha M) : G) * (q0 : G)⁻¹ := by
            exact hsmul_coe q0 x
      _ = (((x : Rsub) : section10Malpha M) : G) := by
            rw [hcomm]
            simp [mul_assoc]
  have htriv :
      ∀ q0 : Q, ∀ x : Rsub, q0 • x = x :=
    section12_action_trivial_of_coprime_range_le_fixing
      (A := Q) (R := Rsub) (p := r.val) hQcopR hR1fix hRangeFix
  apply hRnoncentral
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨xR, hxR, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q0 hq0
  let qQ : Q := ⟨q0, hq0⟩
  let xRsub : Rsub := ⟨xR, hxR⟩
  have hfix := congrArg (fun y : Rsub => ((y : section10Malpha M) : G))
    (htriv qQ xRsub)
  have hconj :
      q0 * ((xRsub : section10Malpha M) : G) * q0⁻¹ =
        ((xRsub : section10Malpha M) : G) := by
    rw [← hsmul_coe qQ xRsub]
    exact hfix
  calc
    q0 * ((xRsub : section10Malpha M) : G)
        = (q0 * ((xRsub : section10Malpha M) : G) * q0⁻¹) * q0 := by
            simp [mul_assoc]
    _ = ((xRsub : section10Malpha M) : G) * q0 := by
            rw [hconj]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_le_normalizer_map_of_isInvariant
    {A H : Subgroup G} {K : Subgroup H}
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) :
    haveI : Subgroup.Normalizes A H := ⟨hAH⟩
    IsInvariant (↥A) (↥H) K →
    A ≤ Subgroup.normalizer (K.map H.subtype : Set G) := by
  intro hKinv
  let _ : Subgroup.Normalizes A H := ⟨hAH⟩
  let _ : IsInvariant (↥A) (↥H) K := hKinv
  refine subgroup_le_normalizer_of_conj_mem (K.map H.subtype) A ?_
  intro a x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  have hyInv : a • y ∈ K :=
    (IsInvariant.invariant (A := ↥A) (G := ↥H) (H := K) a y).1 hy
  exact Subgroup.mem_map.mpr ⟨a • y, hyInv, by
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]⟩

omit [IsMinCE G] in
private theorem CFSG.section12_lemma_12_18_a_critical_le_normalizer
    {M P Q : Subgroup G} {r : Nat.Primes}
    [Subgroup.Normalizes (P ⊔ Q) (section10Malpha M)]
    (R : Sylow r.val (section10Malpha M))
    (hRinv : IsInvariant (↥(P ⊔ Q)) (section10Malpha M)
      (R : Subgroup (section10Malpha M)))
    {R1 : Subgroup (R : Subgroup (section10Malpha M))}
    (hR1char : R1.Characteristic) :
    P ⊔ Q ≤ Subgroup.normalizer
      (((R1.map (R : Subgroup (section10Malpha M)).subtype).map
        (section10Malpha M).subtype : Subgroup G) : Set G) := by
  classical
  let Rsub : Subgroup (section10Malpha M) := (R : Subgroup (section10Malpha M))
  let RG : Subgroup G := Rsub.map (section10Malpha M).subtype
  let eR : Rsub ≃* RG :=
    Subgroup.equivMapOfInjective
      (f := (section10Malpha M).subtype) Rsub
      (section10Malpha M).subtype_injective
  let R1G : Subgroup RG := R1.map eR.toMonoidHom
  have hR1Gchar : R1G.Characteristic := by
    let _ : R1.Characteristic := hR1char
    simpa [R1G] using
      section8_characteristic_map_equiv (G := Rsub) (G' := RG) R1 eR
  have hPQ_norm_malpha :
      P ⊔ Q ≤ Subgroup.normalizer ((section10Malpha M : Subgroup G) : Set G) :=
    (inferInstance : Subgroup.Normalizes (P ⊔ Q) (section10Malpha M)).le_normalizer
  have hPQ_norm_RG : P ⊔ Q ≤ Subgroup.normalizer (RG : Set G) := by
    simpa [RG, Rsub] using
      section12_le_normalizer_map_of_isInvariant
        (G := G) (A := P ⊔ Q) (H := section10Malpha M) (K := Rsub)
        hPQ_norm_malpha (by simpa [Rsub] using hRinv)
  have hRG_norm_R1G :
      Subgroup.normalizer (RG : Set G) ≤
        Subgroup.normalizer ((R1G.map RG.subtype : Subgroup G) : Set G) := by
    let _ : R1G.Characteristic := hR1Gchar
    simpa using
      section8_normalizer_map_subtype_le_of_characteristic
        (G := G) (H := RG) (K := R1G)
  have hmap_eq :
      (R1G.map RG.subtype : Subgroup G) =
        (R1.map Rsub.subtype).map (section10Malpha M).subtype := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨(z : section10Malpha M),
          Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, rfl⟩
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨(eR z : RG),
          Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, rfl⟩
  simpa [hmap_eq, Rsub] using hPQ_norm_RG.trans hRG_norm_R1G

omit [IsMinCE G] in
private theorem CFSG.section12_lemma_12_18_a_not_nilpotent_sup_critical
    {M Q : Subgroup G} {q r : Nat.Primes}
    (hQq : IsPGroup q.val Q)
    (hqα : q ∉ section10AlphaPrimes M)
    (hrα : r ∈ section10AlphaPrimes M)
    (R : Sylow r.val (section10Malpha M))
    {R1 : Subgroup (R : Subgroup (section10Malpha M))}
    (hR1noncentral :
      ¬ (R1.map (R : Subgroup (section10Malpha M)).subtype).map
          (section10Malpha M).subtype ≤ Subgroup.centralizer (Q : Set G)) :
    ¬ Group.IsNilpotent
      ((R1.map (R : Subgroup (section10Malpha M)).subtype).map
          (section10Malpha M).subtype ⊔ Q : Subgroup G) := by
  classical
  intro hnil
  let Rsub : Subgroup (section10Malpha M) := (R : Subgroup (section10Malpha M))
  let D : Subgroup G := (R1.map Rsub.subtype).map (section10Malpha M).subtype
  have hqr : r ≠ q := by
    intro h
    subst h
    exact hqα hrα
  have hD_p : IsPGroup r.val D := by
    have hR1p : IsPGroup r.val R1 := R.isPGroup'.to_subgroup R1
    have hR1map_p : IsPGroup r.val (R1.map Rsub.subtype) :=
      IsPGroup.map (p := r.val) (H := R1) hR1p Rsub.subtype
    simpa [D, Rsub] using
      IsPGroup.map (p := r.val) (H := R1.map Rsub.subtype) hR1map_p
        (section10Malpha M).subtype
  have hDπ : IsPiSubgroup (G := G) ({r} : Set Nat.Primes) D :=
    section8_isPiSubgroup_singleton_of_isPGroup (G := G) (H := D) (q := r) hD_p
  have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
    section8_isPiSubgroup_singleton_of_isPGroup (G := G) (H := Q) (q := q) hQq
  have hπρ : Disjoint ({r} : Set Nat.Primes) ({q} : Set Nat.Primes) := by
    rw [Set.disjoint_left]
    intro s hs_r hs_q
    have hsr : s = r := by simpa using hs_r
    have hsq : s = q := by simpa using hs_q
    exact hqr (hsr.symm.trans hsq)
  have hDcentQ : D ≤ Subgroup.centralizer (Q : Set G) :=
    section10_isPiSubgroup_le_centralizer_of_nilpotent_disjoint
      (G := G) (π := ({r} : Set Nat.Primes)) (ρ := ({q} : Set Nat.Primes))
      (L := D ⊔ Q) (A := D) (B := Q)
      hπρ (by simpa [D] using hnil) le_sup_left le_sup_right hDπ hQπ
  exact hR1noncentral (by simpa [D, Rsub] using hDcentQ)

omit [IsMinCE G] in
private theorem CFSG.section12_isPiSubgroup_of_isPGroup_mem_current
    {π : Set Nat.Primes} {H : Subgroup G} {p : Nat.Primes}
    (hpπ : p ∈ π) (hHp : IsPGroup p.val H) :
    IsPiSubgroup (G := G) π H := by
  intro q hqH
  have hq_singleton : q ∈ ({p} : Set Nat.Primes) :=
    section8_isPiSubgroup_singleton_of_isPGroup (G := G) (H := H) (q := p) hHp q hqH
  have hqp : q = p := by simpa using hq_singleton
  simpa [hqp] using hpπ

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_coprime_card_of_isPiSubgroup_disjoint_primes_current
    {π ρ : Set Nat.Primes} {A B : Subgroup G}
    (hA : IsPiSubgroup (G := G) π A) (hB : IsPiSubgroup (G := G) ρ B)
    (hπρ : Disjoint π ρ) :
    Nat.Coprime (Nat.card A) (Nat.card B) := by
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqA hqB
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hqπ : q' ∈ π := hA q' hqA
  have hqρ : q' ∈ ρ := hB q' hqB
  exact (Set.disjoint_left.mp hπρ hqπ) hqρ

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_disjoint_of_isPiSubgroup_disjoint_primes_current
    {π ρ : Set Nat.Primes} {A B : Subgroup G}
    (hA : IsPiSubgroup (G := G) π A) (hB : IsPiSubgroup (G := G) ρ B)
    (hπρ : Disjoint π ρ) :
    Disjoint A B := by
  rw [Subgroup.disjoint_def]
  intro x hxA hxB
  have hcop : Nat.Coprime (Nat.card A) (Nat.card B) :=
    section12_coprime_card_of_isPiSubgroup_disjoint_primes_current
      (G := G) hA hB hπρ
  have hcop_order : Nat.Coprime (orderOf x) (Nat.card B) :=
    Nat.Coprime.of_dvd_left (Subgroup.orderOf_dvd_natCard A hxA) hcop
  have hx_order_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_order dvd_rfl
      (Subgroup.orderOf_dvd_natCard B hxB)
  exact orderOf_eq_one_iff.mp hx_order_one

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_le_normalizer_sup_current
    {R A B : Subgroup G}
    (hRA : R ≤ Subgroup.normalizer (A : Set G))
    (hRB : R ≤ Subgroup.normalizer (B : Set G)) :
    R ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  classical
  intro r hr
  have hforward :
      ∀ g ∈ R, ∀ x, x ∈ A ⊔ B → g * x * g⁻¹ ∈ A ⊔ B := by
    intro g hg x hx
    rw [Subgroup.sup_eq_closure] at hx ⊢
    refine
      Subgroup.closure_induction (p := fun y _hy => g * y * g⁻¹ ∈
        Subgroup.closure ((A : Set G) ∪ (B : Set G))) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with hyA | hyB
      · exact Subgroup.subset_closure
          (Or.inl ((Subgroup.mem_normalizer_iff.mp (hRA hg) y).1 hyA))
      · exact Subgroup.subset_closure
          (Or.inr ((Subgroup.mem_normalizer_iff.mp (hRB hg) y).1 hyB))
    · simp
    · intro y z _hy _hz hy hz
      simpa [mul_assoc] using
        (Subgroup.closure ((A : Set G) ∪ (B : Set G))).mul_mem hy hz
    · intro y _hy hy
      simpa [mul_assoc] using
        (Subgroup.closure ((A : Set G) ∪ (B : Set G))).inv_mem hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward r hr x
  · intro hx
    have hx' := hforward r⁻¹ (R.inv_mem hr) (r * x * r⁻¹) hx
    simpa [mul_assoc] using hx'

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_subgroupCentralizerIn_sup_eq_bot_of_normalized_factors_current
    {A B P : Subgroup G}
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hPnormB : P ≤ Subgroup.normalizer (B : Set G))
    (hAnormB : A ≤ Subgroup.normalizer (B : Set G))
    (hABdisj : Disjoint A B)
    (hAfix : subgroupCentralizerIn A P = ⊥)
    (hBfix : subgroupCentralizerIn B P = ⊥) :
    subgroupCentralizerIn (A ⊔ B : Subgroup G) P = ⊥ := by
  classical
  let S : Subgroup G := A ⊔ B
  let As : Subgroup S := A.subgroupOf S
  let Bs : Subgroup S := B.subgroupOf S
  let _ : Bs.Normal := by
    simpa [S, Bs] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := A) (N := B) hAnormB)
  have hAsBs_top : As ⊔ Bs = ⊤ := by
    calc
      As ⊔ Bs = S.subgroupOf S := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := A) (A' := B) (B := S)
          (by simp [S])
          (by simp [S])
      _ = ⊤ := by simp
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases hx with ⟨hxS, hxCentP⟩
  let xS : S := ⟨x, hxS⟩
  have hxTop : xS ∈ As ⊔ Bs := by simp [hAsBs_top]
  rcases (Subgroup.mem_sup_of_normal_right (s := As) (t := Bs) (x := xS)).1 hxTop with
    ⟨aS, haS, bS, hbS, habxS⟩
  let a : G := aS
  let b : G := bS
  have haA : a ∈ A := by
    simpa [a, As, Subgroup.mem_subgroupOf] using haS
  have hbB : b ∈ B := by
    simpa [b, Bs, Subgroup.mem_subgroupOf] using hbS
  have hx_eq : x = a * b := by
    have hval := congrArg (fun y : S => (y : G)) habxS
    simpa [a, b, xS] using hval.symm
  have hfactor_fixed :
      ∀ p0 : G, p0 ∈ P →
        p0 * a * p0⁻¹ = a ∧ p0 * b * p0⁻¹ = b := by
    intro p0 hp0
    let a' : G := p0 * a * p0⁻¹
    let b' : G := p0 * b * p0⁻¹
    have ha'A : a' ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hPnormA hp0) a).1 haA
    have hb'B : b' ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hPnormB hp0) b).1 hbB
    have hx_comm : p0 * x = x * p0 :=
      Subgroup.mem_centralizer_iff.mp hxCentP p0 hp0
    have hconj_x : p0 * x * p0⁻¹ = x := by
      calc
        p0 * x * p0⁻¹ = (x * p0) * p0⁻¹ := by rw [hx_comm]
        _ = x := by simp [mul_assoc]
    have hEq : a' * b' = a * b := by
      simpa [a', b', hx_eq, mul_assoc] using hconj_x
    have ha'_eq : a' = a * b * b'⁻¹ := by
      calc
        a' = (a' * b') * b'⁻¹ := by simp [mul_assoc]
        _ = (a * b) * b'⁻¹ := by rw [hEq]
        _ = a * b * b'⁻¹ := by simp [mul_assoc]
    have hcross : a⁻¹ * a' = b * b'⁻¹ := by
      calc
        a⁻¹ * a' = a⁻¹ * (a * b * b'⁻¹) := by rw [ha'_eq]
        _ = b * b'⁻¹ := by simp [mul_assoc]
    have hcrossA : a⁻¹ * a' ∈ A := A.mul_mem (A.inv_mem haA) ha'A
    have hcrossB : a⁻¹ * a' ∈ B := by
      rw [hcross]
      exact B.mul_mem hbB (B.inv_mem hb'B)
    have hcross1 : a⁻¹ * a' = 1 :=
      Subgroup.disjoint_def.mp hABdisj hcrossA hcrossB
    have ha_fixed : a' = a := by
      have h := congrArg (fun t : G => a * t) hcross1
      simpa [mul_assoc] using h
    have hb_fixed : b' = b := by
      have h := hEq
      rw [ha_fixed] at h
      have h' := congrArg (fun t : G => a⁻¹ * t) h
      simpa [mul_assoc] using h'
    exact ⟨by simpa [a'] using ha_fixed, by simpa [b'] using hb_fixed⟩
  have haCent : a ∈ subgroupCentralizerIn A P := by
    refine ⟨haA, ?_⟩
    change a ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro p0 hp0
    have hfix := (hfactor_fixed p0 hp0).1
    have hmul := congrArg (fun t : G => t * p0) hfix
    simpa [mul_assoc] using hmul
  have hbCent : b ∈ subgroupCentralizerIn B P := by
    refine ⟨hbB, ?_⟩
    change b ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro p0 hp0
    have hfix := (hfactor_fixed p0 hp0).2
    have hmul := congrArg (fun t : G => t * p0) hfix
    simpa [mul_assoc] using hmul
  have ha1 : a = 1 := by
    have : a ∈ (⊥ : Subgroup G) := by simpa [hAfix] using haCent
    exact Subgroup.mem_bot.mp this
  have hb1 : b = 1 := by
    have : b ∈ (⊥ : Subgroup G) := by simpa [hBfix] using hbCent
    exact Subgroup.mem_bot.mp this
  simp [hx_eq, ha1, hb1]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_subgroupCentralizerIn_sup_eq_right_of_normalized_factors_current
    {A B P : Subgroup G}
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hPnormB : P ≤ Subgroup.normalizer (B : Set G))
    (hAnormB : A ≤ Subgroup.normalizer (B : Set G))
    (hABdisj : Disjoint A B)
    (hAfix : subgroupCentralizerIn A P = ⊥) :
    subgroupCentralizerIn (A ⊔ B : Subgroup G) P = subgroupCentralizerIn B P := by
  classical
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨hxS, hxCentP⟩
    let S : Subgroup G := A ⊔ B
    let As : Subgroup S := A.subgroupOf S
    let Bs : Subgroup S := B.subgroupOf S
    let _ : Bs.Normal := by
      simpa [S, Bs] using
        (Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := A) (N := B) hAnormB)
    have hAsBs_top : As ⊔ Bs = ⊤ := by
      calc
        As ⊔ Bs = S.subgroupOf S := by
          symm
          exact Subgroup.subgroupOf_sup
            (A := A) (A' := B) (B := S)
            (by simp [S])
            (by simp [S])
        _ = ⊤ := by simp
    let xS : S := ⟨x, hxS⟩
    have hxTop : xS ∈ As ⊔ Bs := by simp [hAsBs_top]
    rcases (Subgroup.mem_sup_of_normal_right (s := As) (t := Bs) (x := xS)).1 hxTop with
      ⟨aS, haS, bS, hbS, habxS⟩
    let a : G := aS
    let b : G := bS
    have haA : a ∈ A := by
      simpa [a, As, Subgroup.mem_subgroupOf] using haS
    have hbB : b ∈ B := by
      simpa [b, Bs, Subgroup.mem_subgroupOf] using hbS
    have hx_eq : x = a * b := by
      have hval := congrArg (fun y : S => (y : G)) habxS
      simpa [a, b, xS] using hval.symm
    have hfactor_fixed :
        ∀ p0 : G, p0 ∈ P →
          p0 * a * p0⁻¹ = a ∧ p0 * b * p0⁻¹ = b := by
      intro p0 hp0
      let a' : G := p0 * a * p0⁻¹
      let b' : G := p0 * b * p0⁻¹
      have ha'A : a' ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hPnormA hp0) a).1 haA
      have hb'B : b' ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (hPnormB hp0) b).1 hbB
      have hx_comm : p0 * x = x * p0 :=
        Subgroup.mem_centralizer_iff.mp hxCentP p0 hp0
      have hconj_x : p0 * x * p0⁻¹ = x := by
        calc
          p0 * x * p0⁻¹ = (x * p0) * p0⁻¹ := by rw [hx_comm]
          _ = x := by simp [mul_assoc]
      have hEq : a' * b' = a * b := by
        simpa [a', b', hx_eq, mul_assoc] using hconj_x
      have ha'_eq : a' = a * b * b'⁻¹ := by
        calc
          a' = (a' * b') * b'⁻¹ := by simp [mul_assoc]
          _ = (a * b) * b'⁻¹ := by rw [hEq]
          _ = a * b * b'⁻¹ := by simp [mul_assoc]
      have hcross : a⁻¹ * a' = b * b'⁻¹ := by
        calc
          a⁻¹ * a' = a⁻¹ * (a * b * b'⁻¹) := by rw [ha'_eq]
          _ = b * b'⁻¹ := by simp [mul_assoc]
      have hcrossA : a⁻¹ * a' ∈ A := A.mul_mem (A.inv_mem haA) ha'A
      have hcrossB : a⁻¹ * a' ∈ B := by
        rw [hcross]
        exact B.mul_mem hbB (B.inv_mem hb'B)
      have hcross1 : a⁻¹ * a' = 1 :=
        Subgroup.disjoint_def.mp hABdisj hcrossA hcrossB
      have ha_fixed : a' = a := by
        have h := congrArg (fun t : G => a * t) hcross1
        simpa [mul_assoc] using h
      have hb_fixed : b' = b := by
        have h := hEq
        rw [ha_fixed] at h
        have h' := congrArg (fun t : G => a⁻¹ * t) h
        simpa [mul_assoc] using h'
      exact ⟨by simpa [a'] using ha_fixed, by simpa [b'] using hb_fixed⟩
    have haCent : a ∈ subgroupCentralizerIn A P := by
      refine ⟨haA, ?_⟩
      change a ∈ Subgroup.centralizer (P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro p0 hp0
      have hfix := (hfactor_fixed p0 hp0).1
      have hmul := congrArg (fun t : G => t * p0) hfix
      simpa [mul_assoc] using hmul
    have hbCent : b ∈ subgroupCentralizerIn B P := by
      refine ⟨hbB, ?_⟩
      change b ∈ Subgroup.centralizer (P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro p0 hp0
      have hfix := (hfactor_fixed p0 hp0).2
      have hmul := congrArg (fun t : G => t * p0) hfix
      simpa [mul_assoc] using hmul
    have ha1 : a = 1 := by
      have : a ∈ (⊥ : Subgroup G) := by simpa [hAfix] using haCent
      exact Subgroup.mem_bot.mp this
    have hx_eq_b : x = b := by
      simp [hx_eq, ha1]
    simpa [hx_eq_b] using hbCent
  · intro x hx
    exact ⟨Subgroup.mem_sup_right hx.1, hx.2⟩

private theorem CFSG.section12_lemma_12_18_a_centralizer_P_ne_bot_of_critical
    {M P Q : Subgroup G} {p q r : Nat.Primes}
    [Subgroup.Normalizes (P ⊔ Q) (section10Malpha M)]
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M)
    (hq : q ∈ section10PPrimeSet p)
    (hQle : Q ≤ M) (hQq : IsPGroup q.val Q)
    (hPinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hqα : q ∉ section10AlphaPrimes M)
    (hrα : r ∈ section10AlphaPrimes M)
    (R : Sylow r.val (section10Malpha M))
    (hRinv : IsInvariant (↥(P ⊔ Q)) (section10Malpha M)
      (R : Subgroup (section10Malpha M)))
    {R1 : Subgroup (R : Subgroup (section10Malpha M))}
    (hR1char : R1.Characteristic)
    (hR1noncentral :
      ¬ (R1.map (R : Subgroup (section10Malpha M)).subtype).map
          (section10Malpha M).subtype ≤ Subgroup.centralizer (Q : Set G)) :
    subgroupCentralizerIn (section10Malpha M) P ≠ ⊥ := by
  classical
  intro hCPbot
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hPleM, hPcard⟩
  rcases (by simpa [section12Tau1Primes] using hp) with
    ⟨hp_notσ, _hpD, _hprank_one⟩
  have hp_notα : p ∉ section10AlphaPrimes M := by
    intro hpα
    exact hp_notσ (section12_sigmaPrimes_mem_of_alphaPrimes_mem (G := G) hM hpα)
  let Rsub : Subgroup (section10Malpha M) := (R : Subgroup (section10Malpha M))
  let D : Subgroup G := (R1.map Rsub.subtype).map (section10Malpha M).subtype
  have hD_le_malpha : D ≤ section10Malpha M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hDleM : D ≤ M := hD_le_malpha.trans (section10_malpha_le (G := G))
  have hD_p : IsPGroup r.val D := by
    have hR1p : IsPGroup r.val R1 := R.isPGroup'.to_subgroup R1
    have hR1map_p : IsPGroup r.val (R1.map Rsub.subtype) :=
      IsPGroup.map (p := r.val) (H := R1) hR1p Rsub.subtype
    simpa [D, Rsub] using
      IsPGroup.map (p := r.val) (H := R1.map Rsub.subtype) hR1map_p
        (section10Malpha M).subtype
  have hPQnormD :
      P ⊔ Q ≤ Subgroup.normalizer (D : Set G) := by
    simpa [D, Rsub] using
      section12_lemma_12_18_a_critical_le_normalizer
        (G := G) (M := M) (P := P) (Q := Q) (r := r)
        R hRinv hR1char
  have hPnormD : P ≤ Subgroup.normalizer (D : Set G) :=
    le_sup_left.trans hPQnormD
  have hQnormD : Q ≤ Subgroup.normalizer (D : Set G) :=
    le_sup_right.trans hPQnormD
  have hDfix : subgroupCentralizerIn D P = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxCP : x ∈ subgroupCentralizerIn (section10Malpha M) P :=
      ⟨hD_le_malpha hx.1, hx.2⟩
    simpa [hCPbot] using hxCP
  have hqr : q ≠ r := by
    intro h
    subst h
    exact hqα hrα
  have hqr_val : q.val ≠ r.val := by
    intro hval
    exact hqr (Subtype.ext hval)
  let _ : Fact q.val.Prime := ⟨q.property⟩
  let _ : Fact r.val.Prime := ⟨r.property⟩
  have hQDdisj : Disjoint Q D :=
    IsPGroup.disjoint_of_ne q.val r.val hqr_val Q D hQq hD_p
  let K : Subgroup G := Q ⊔ D
  have hKfix : subgroupCentralizerIn K P = ⊥ := by
    simpa [K] using
      section12_subgroupCentralizerIn_sup_eq_bot_of_normalized_factors_current
        (G := G) (A := Q) (B := D) (P := P)
        hPinv hPnormD hQnormD hQDdisj hCQ hDfix
  have hPnormK : P ≤ Subgroup.normalizer (K : Set G) := by
    simpa [K] using
      section12_le_normalizer_sup_current
        (G := G) (R := P) (A := Q) (B := D) hPinv hPnormD
  have hQp' : IsPiSubgroup (G := G) (section10PPrimeSet p) Q :=
    section12_isPiSubgroup_of_isPGroup_mem_current (G := G) hq hQq
  have hrp' : r ∈ section10PPrimeSet p := by
    rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hrp
    exact hp_notα (by simpa [hrp] using hrα)
  have hDp' : IsPiSubgroup (G := G) (section10PPrimeSet p) D :=
    section12_isPiSubgroup_of_isPGroup_mem_current (G := G) hrp' hD_p
  have hKp' : IsPiSubgroup (G := G) (section10PPrimeSet p) K := by
    simpa [K] using
      section12_isPiSubgroup_sup_of_le_normalizer_alpha_local
        (G := G) (π := section10PPrimeSet p) (H := Q) (K := D)
        hQp' hDp' hQnormD
  have hPp : IsPGroup p.val P :=
    section12_primeOrderSubgroupsIn_isPGroup (G := G) (A := M) hP
  have hPπ : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) P :=
    section8_isPiSubgroup_singleton_of_isPGroup (G := G) (H := P) (q := p) hPp
  have hp'_disj_singleton : Disjoint (section10PPrimeSet p) ({p} : Set Nat.Primes) := by
    rw [Set.disjoint_left]
    intro s hs_p' hs_p
    have hs_not_p : s ∉ ({p} : Set Nat.Primes) := by
      simpa [section10PPrimeSet] using hs_p'
    exact hs_not_p hs_p
  have hK_P_disj : Disjoint K P :=
    section12_disjoint_of_isPiSubgroup_disjoint_primes_current
      (G := G) hKp' hPπ hp'_disj_singleton
  let T : Subgroup G := P ⊔ K
  have hKleM : K ≤ M := by
    exact sup_le hQle hDleM
  have hTleM : T ≤ M := by
    exact sup_le hPleM hKleM
  have hTne_top : T ≠ ⊤ := by
    intro hTtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      rw [← hTtop]
      exact hTleM
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hsolvT : Group.IsSolvable T :=
    IsMinCE.proper_subgroups_solvable T (lt_top_iff_ne_top.2 hTne_top)
  have hoddT : Odd (Nat.card T) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card T)
  have hKnormalT : (K.subgroupOf T).Normal := by
    simpa [T] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := P) (N := K) hPnormK)
  have hKsub_Psub_disj : Disjoint (K.subgroupOf T) (P.subgroupOf T) := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxP
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hK_P_disj hxK hxP
  have hKsubPsub_top : K.subgroupOf T ⊔ P.subgroupOf T = ⊤ := by
    calc
      K.subgroupOf T ⊔ P.subgroupOf T = P.subgroupOf T ⊔ K.subgroupOf T := by
        rw [sup_comm]
      _ = T.subgroupOf T := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := P) (A' := K) (B := T)
          (by simp [T])
          (by simp [T])
      _ = ⊤ := by simp
  have hcompT : (K.subgroupOf T).IsComplement' (P.subgroupOf T) := by
    let _ : (K.subgroupOf T).Normal := hKnormalT
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · exact hKsub_Psub_disj
    · rw [Set.eq_univ_iff_forall]
      intro y
      have hyTop : y ∈ K.subgroupOf T ⊔ P.subgroupOf T := by
        simp [hKsubPsub_top]
      rcases (Subgroup.mem_sup_of_normal_left
          (s := K.subgroupOf T) (t := P.subgroupOf T) (x := y)).1 hyTop with
        ⟨k, hk, p0, hp0, hkp⟩
      exact ⟨k, hk, p0, hp0, hkp⟩
  have hPsub_prime : Nat.Prime (Nat.card (P.subgroupOf T)) := by
    have hcard : Nat.card (P.subgroupOf T) = p.val := by
      rw [natCard_subgroupOf_eq P T (by simp [T]), hPcard]
    simpa [hcard] using p.property
  have hfixT : subgroupCentralizerIn (K.subgroupOf T) (P.subgroupOf T) = ⊥ := by
    rw [subgroupCentralizerIn_subgroupOf_eq T K P (by simp [T]), hKfix]
    simp
  have hnilKsub : Group.IsNilpotent (K.subgroupOf T) :=
    theorem_3_7 (G := T) (K.subgroupOf T) (P.subgroupOf T)
      hsolvT hoddT hKnormalT hcompT hPsub_prime hfixT
  have hnilK : Group.IsNilpotent K := by
    let e : K.subgroupOf T ≃* K :=
      Subgroup.subgroupOfEquivOfLe (H := K) (K := T) (by simp [T])
    let _ : Group.IsNilpotent (K.subgroupOf T) := hnilKsub
    exact Group.nilpotent_of_mulEquiv (G := K.subgroupOf T) (G' := K) e
  have hnotnil :
      ¬ Group.IsNilpotent (D ⊔ Q : Subgroup G) := by
    simpa [D, Rsub] using
      section12_lemma_12_18_a_not_nilpotent_sup_critical
        (G := G) (M := M) (Q := Q) (q := q) (r := r)
        hQq hqα hrα R hR1noncentral
  have hDQ_eq : D ⊔ Q = K := by
    simp [K, sup_comm]
  exact hnotnil (by rw [hDQ_eq]; exact hnilK)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_subgroupCentralizerIn_antitone_right_current
    {A S T : Subgroup G} (hST : S ≤ T) :
    subgroupCentralizerIn A T ≤ subgroupCentralizerIn A S := by
  intro x hx
  exact ⟨hx.1, (Subgroup.centralizer_le hST) hx.2⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_subgroupCentralizerIn_antitone_right_ne_bot_current
    {A S T : Subgroup G} (hST : S ≤ T)
    (hCT : subgroupCentralizerIn A T ≠ ⊥) :
    subgroupCentralizerIn A S ≠ ⊥ := by
  intro hCS
  apply hCT
  apply le_bot_iff.mp
  intro x hx
  have hxS : x ∈ subgroupCentralizerIn A S :=
    section12_subgroupCentralizerIn_antitone_right_current (G := G) hST hx
  simpa [hCS] using hxS

omit [IsMinCE G] in
private theorem CFSG.section12_subgroupCentralizerIn_rank_le_one_of_left_le_current
    {A B S : Subgroup G} (hAB : A ≤ B)
    (hRank : groupRank (subgroupCentralizerIn B S) ≤ 1) :
    groupRank (subgroupCentralizerIn A S) ≤ 1 := by
  have hle :
      subgroupCentralizerIn A S ≤ subgroupCentralizerIn B S := by
    intro x hx
    exact ⟨hAB hx.1, hx.2⟩
  let Csub : Subgroup (subgroupCentralizerIn B S) :=
    (subgroupCentralizerIn A S).subgroupOf (subgroupCentralizerIn B S)
  let eCsub : Csub ≃* subgroupCentralizerIn A S :=
    Subgroup.subgroupOfEquivOfLe
      (H := subgroupCentralizerIn A S) (K := subgroupCentralizerIn B S) hle
  exact
    ((groupRank_le_of_equiv eCsub).trans
      (section8_groupRank_le_of_subgroup Csub)).trans hRank

omit [IsMinCE G] in
private theorem CFSG.section12_primeRank_le_card_current
    {R : Type*} [Group R] [Finite R] (q : ℕ) :
    primeRank q R ≤ Nat.card R := by
  let S : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section8_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  by_cases hS : S.Nonempty
  · have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hS hSbdd
    rcases hsSup_mem with ⟨A, _hAq, _hAcomm, hsSup_le⟩
    rw [primeRank]
    exact hsSup_le.trans <|
      (section8_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have hSet :
        {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
          n ≤ generatorRank A} = ∅ := by
      simpa [S] using hSempty
    rw [primeRank, hSet]
    simp

omit [IsMinCE G] in
private theorem CFSG.section12_primeRank_le_groupRank_current
    {R : Type*} [Group R] [Finite R] {q : ℕ} (hq : Nat.Prime q) :
    primeRank q R ≤ groupRank R := by
  let S : Set ℕ := {n : ℕ | ∃ q' : ℕ, Nat.Prime q' ∧ n ≤ primeRank q' R}
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q', _hq', hnq'⟩
    exact hnq'.trans (section12_primeRank_le_card_current (R := R) q')
  have hmem : primeRank q R ∈ S := ⟨q, hq, le_rfl⟩
  simpa [groupRank, S] using le_csSup hSbdd hmem

omit [IsMinCE G] in
private theorem CFSG.section12_isCyclic_of_rank_le_one_pGroup_current
    {C : Subgroup G} {r : Nat.Primes}
    (hrodd : r.val ≠ 2) (hCp : IsPGroup r.val C)
    (hCrank : groupRank C ≤ 1) :
    IsCyclic C := by
  classical
  let _ : Fact r.val.Prime := ⟨r.property⟩
  by_contra hCcyc
  let _ : Fact (IsPGroup r.val C) := ⟨hCp⟩
  obtain ⟨A, _hAnorm, hAcard, hAelem⟩ :=
    lemma_4_5_a (R := C) (p := r.val) hrodd hCcyc
  let _ : IsElementaryAbelian r.val A := hAelem
  have hAp : IsPGroup r.val A := IsElementaryAbelian.isPGroup r.val A
  have hAcomm : IsMulCommutative A := inferInstance
  have hgen_A : 2 ≤ generatorRank A :=
    section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
      (p := r.val) hAcard
  have hprime_ge : 2 ≤ primeRank r.val C :=
    hgen_A.trans
      (section12_generatorRank_le_primeRank_of_subgroup
        (R := C) (q := r.val) (A := A) hAp hAcomm)
  have hgroup_ge : 2 ≤ groupRank C :=
    hprime_ge.trans (section12_primeRank_le_groupRank_current (R := C) r.property)
  omega

omit [IsMinCE G] in
private theorem CFSG.section12_natCard_eq_prime_of_rank_le_one_exponent_prime_current
    {C : Subgroup G} {r : Nat.Primes}
    (hrodd : r.val ≠ 2) (hCp : IsPGroup r.val C)
    (hCne : C ≠ ⊥) (hCrank : groupRank C ≤ 1)
    (hCpow : ∀ x : C, x ^ r.val = 1) :
    Nat.card C = r.val := by
  classical
  let _ : Fact r.val.Prime := ⟨r.property⟩
  let _ : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).2 hCne
  have hCcyc : IsCyclic C :=
    section12_isCyclic_of_rank_le_one_pGroup_current
      (G := G) (C := C) (r := r) hrodd hCp hCrank
  let _ : IsCyclic C := hCcyc
  have hExp : Monoid.exponent C = r.val :=
    (Monoid.exponent_eq_prime_iff (G := C) (p := r.val) r.property).2 (by
      intro x hx
      have horder_dvd : orderOf x ∣ r.val := orderOf_dvd_of_pow_eq_one (hCpow x)
      have horder_ne_one : orderOf x ≠ 1 := by
        intro horder
        exact hx (orderOf_eq_one_iff.mp horder)
      exact (r.property.eq_one_or_self_of_dvd (orderOf x) horder_dvd).resolve_left
        horder_ne_one)
  rw [← IsCyclic.exponent_eq_card (α := C), hExp]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_normalizer_le_normalizer_centralizer_current
    (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have ha' : n⁻¹ * a * n ∈ A :=
      (Subgroup.mem_normalizer_iff''.mp hn a).1 ha
    have hcomm : (n⁻¹ * a * n) * c = c * (n⁻¹ * a * n) := hc (n⁻¹ * a * n) ha'
    calc
      a * (n * c * n⁻¹) = n * ((n⁻¹ * a * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * a * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * c * n⁻¹) * a := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have ha' : n * a * n⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hn a).1 ha
    have hcomm :
        (n * a * n⁻¹) * (n * c * n⁻¹) =
          (n * c * n⁻¹) * (n * a * n⁻¹) :=
      hc (n * a * n⁻¹) ha'
    calc
      a * c = n⁻¹ * ((n * a * n⁻¹) * (n * c * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * c * n⁻¹) * (n * a * n⁻¹)) * n := by rw [hcomm]
      _ = c * a := by group

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_le_normalizer_subgroupCentralizerIn_of_normalizers_current
    {A P S : Subgroup G}
    (hS_norm_A : S ≤ Subgroup.normalizer (A : Set G))
    (hS_norm_P : S ≤ Subgroup.normalizer (P : Set G)) :
    S ≤ Subgroup.normalizer (subgroupCentralizerIn A P : Set G) := by
  have hS_norm_cent :
      S ≤ Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) :=
    hS_norm_P.trans (section12_normalizer_le_normalizer_centralizer_current (G := G) P)
  simpa [subgroupCentralizerIn] using
    Subgroup.le_normalizer_inf
      (G := G) (A := S) (H := A) (K := Subgroup.centralizer (P : Set G))
      hS_norm_A hS_norm_cent

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_sup_isNilpotent_of_commuting_nilpotent_current
    {A B : Subgroup G}
    (hAB : A ≤ Subgroup.centralizer (B : Set G))
    (hAnil : Group.IsNilpotent A) (hBnil : Group.IsNilpotent B) :
    Group.IsNilpotent (A ⊔ B : Subgroup G) := by
  classical
  let S : Subgroup G := A ⊔ B
  have hAnormB : A ≤ Subgroup.normalizer (B : Set G) :=
    hAB.trans (centralizer_le_normalizer B)
  let _ : (B.subgroupOf S).Normal := by
    simpa [S] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := A) (N := B) hAnormB)
  let f : A × B →* S := {
    toFun x := ⟨(x.1 : G) * (x.2 : G),
      S.mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' x y := by
      apply Subtype.ext
      change
        (((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G))) =
          (((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G)))
      have hcomm : (y.1 : G) * (x.2 : G) = (x.2 : G) * (y.1 : G) := by
        exact (Subgroup.mem_centralizer_iff.mp (hAB y.1.2) (x.2 : G) x.2.2).symm
      calc
        ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
            (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by
              group
        _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by rw [hcomm]
        _ = ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G)) := by
              group
  }
  have hf_surj : Function.Surjective f := by
    intro s
    have hAsBs_top : A.subgroupOf S ⊔ B.subgroupOf S = ⊤ := by
      calc
        A.subgroupOf S ⊔ B.subgroupOf S = S.subgroupOf S := by
          symm
          exact Subgroup.subgroupOf_sup
            (A := A) (A' := B) (B := S)
            (by simp [S])
            (by simp [S])
        _ = ⊤ := by simp
    have hs_mem : s ∈ A.subgroupOf S ⊔ B.subgroupOf S := by
      simp [hAsBs_top]
    rcases (Subgroup.mem_sup_of_normal_right
        (s := A.subgroupOf S) (t := B.subgroupOf S) (x := s)).1
        hs_mem with ⟨aS, haS, bS, hbS, hab⟩
    let a : A := ⟨(aS : G), by simpa [Subgroup.mem_subgroupOf] using haS⟩
    let b : B := ⟨(bS : G), by simpa [Subgroup.mem_subgroupOf] using hbS⟩
    refine ⟨(a, b), ?_⟩
    apply Subtype.ext
    have hval := congrArg (fun z : S => (z : G)) hab
    simpa [f, a, b, mul_assoc] using hval
  let _ : Group.IsNilpotent A := hAnil
  let _ : Group.IsNilpotent B := hBnil
  exact Group.nilpotent_of_surjective f hf_surj

private theorem CFSG.section12_lemma_12_18_a_critical_image_centralizer_P_ne_bot
    {M P Q D : Subgroup G} {p q r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M)
    (hq : q ∈ section10PPrimeSet p)
    (hQle : Q ≤ M) (hQq : IsPGroup q.val Q)
    (hPinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hqα : q ∉ section10AlphaPrimes M)
    (hrα : r ∈ section10AlphaPrimes M)
    (hDp : IsPGroup r.val D)
    (hD_le_malpha : D ≤ section10Malpha M)
    (hPnormD : P ≤ Subgroup.normalizer (D : Set G))
    (hQnormD : Q ≤ Subgroup.normalizer (D : Set G))
    (hDnotnil : ¬ Group.IsNilpotent (D ⊔ Q : Subgroup G)) :
    subgroupCentralizerIn D P ≠ ⊥ := by
  classical
  intro hDfix
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hPleM, hPcard⟩
  rcases (by simpa [section12Tau1Primes] using hp) with
    ⟨hp_notσ, _hpD, _hprank_one⟩
  have hp_notα : p ∉ section10AlphaPrimes M := by
    intro hpα
    exact hp_notσ (section12_sigmaPrimes_mem_of_alphaPrimes_mem (G := G) hM hpα)
  have hDleM : D ≤ M := hD_le_malpha.trans (section10_malpha_le (G := G))
  have hqr : q ≠ r := by
    intro h
    subst h
    exact hqα hrα
  have hqr_val : q.val ≠ r.val := by
    intro hval
    exact hqr (Subtype.ext hval)
  let _ : Fact q.val.Prime := ⟨q.property⟩
  let _ : Fact r.val.Prime := ⟨r.property⟩
  have hQDdisj : Disjoint Q D :=
    IsPGroup.disjoint_of_ne q.val r.val hqr_val Q D hQq hDp
  let K : Subgroup G := Q ⊔ D
  have hKfix : subgroupCentralizerIn K P = ⊥ := by
    simpa [K] using
      section12_subgroupCentralizerIn_sup_eq_bot_of_normalized_factors_current
        (G := G) (A := Q) (B := D) (P := P)
        hPinv hPnormD hQnormD hQDdisj hCQ hDfix
  have hPnormK : P ≤ Subgroup.normalizer (K : Set G) := by
    simpa [K] using
      section12_le_normalizer_sup_current
        (G := G) (R := P) (A := Q) (B := D) hPinv hPnormD
  have hQp' : IsPiSubgroup (G := G) (section10PPrimeSet p) Q :=
    section12_isPiSubgroup_of_isPGroup_mem_current (G := G) hq hQq
  have hrp' : r ∈ section10PPrimeSet p := by
    rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hrp
    exact hp_notα (by simpa [hrp] using hrα)
  have hDp' : IsPiSubgroup (G := G) (section10PPrimeSet p) D :=
    section12_isPiSubgroup_of_isPGroup_mem_current (G := G) hrp' hDp
  have hKp' : IsPiSubgroup (G := G) (section10PPrimeSet p) K := by
    simpa [K] using
      section12_isPiSubgroup_sup_of_le_normalizer_alpha_local
        (G := G) (π := section10PPrimeSet p) (H := Q) (K := D)
        hQp' hDp' hQnormD
  have hPp : IsPGroup p.val P :=
    section12_primeOrderSubgroupsIn_isPGroup (G := G) (A := M) hP
  have hPπ : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) P :=
    section8_isPiSubgroup_singleton_of_isPGroup (G := G) (H := P) (q := p) hPp
  have hp'_disj_singleton : Disjoint (section10PPrimeSet p) ({p} : Set Nat.Primes) := by
    rw [Set.disjoint_left]
    intro s hs_p' hs_p
    have hs_not_p : s ∉ ({p} : Set Nat.Primes) := by
      simpa [section10PPrimeSet] using hs_p'
    exact hs_not_p hs_p
  have hK_P_disj : Disjoint K P :=
    section12_disjoint_of_isPiSubgroup_disjoint_primes_current
      (G := G) hKp' hPπ hp'_disj_singleton
  let T : Subgroup G := P ⊔ K
  have hKleM : K ≤ M := by
    exact sup_le hQle hDleM
  have hTleM : T ≤ M := by
    exact sup_le hPleM hKleM
  have hTne_top : T ≠ ⊤ := by
    intro hTtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      rw [← hTtop]
      exact hTleM
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hsolvT : Group.IsSolvable T :=
    IsMinCE.proper_subgroups_solvable T (lt_top_iff_ne_top.2 hTne_top)
  have hoddT : Odd (Nat.card T) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card T)
  have hKnormalT : (K.subgroupOf T).Normal := by
    simpa [T] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := P) (N := K) hPnormK)
  have hKsub_Psub_disj : Disjoint (K.subgroupOf T) (P.subgroupOf T) := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxP
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hK_P_disj hxK hxP
  have hKsubPsub_top : K.subgroupOf T ⊔ P.subgroupOf T = ⊤ := by
    calc
      K.subgroupOf T ⊔ P.subgroupOf T = P.subgroupOf T ⊔ K.subgroupOf T := by
        rw [sup_comm]
      _ = T.subgroupOf T := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := P) (A' := K) (B := T)
          (by simp [T])
          (by simp [T])
      _ = ⊤ := by simp
  have hcompT : (K.subgroupOf T).IsComplement' (P.subgroupOf T) := by
    let _ : (K.subgroupOf T).Normal := hKnormalT
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · exact hKsub_Psub_disj
    · rw [Set.eq_univ_iff_forall]
      intro y
      have hyTop : y ∈ K.subgroupOf T ⊔ P.subgroupOf T := by
        simp [hKsubPsub_top]
      rcases (Subgroup.mem_sup_of_normal_left
          (s := K.subgroupOf T) (t := P.subgroupOf T) (x := y)).1 hyTop with
        ⟨k, hk, p0, hp0, hkp⟩
      exact ⟨k, hk, p0, hp0, hkp⟩
  have hPsub_prime : Nat.Prime (Nat.card (P.subgroupOf T)) := by
    have hcard : Nat.card (P.subgroupOf T) = p.val := by
      rw [natCard_subgroupOf_eq P T (by simp [T]), hPcard]
    simpa [hcard] using p.property
  have hfixT : subgroupCentralizerIn (K.subgroupOf T) (P.subgroupOf T) = ⊥ := by
    rw [subgroupCentralizerIn_subgroupOf_eq T K P (by simp [T]), hKfix]
    simp
  have hnilKsub : Group.IsNilpotent (K.subgroupOf T) :=
    theorem_3_7 (G := T) (K.subgroupOf T) (P.subgroupOf T)
      hsolvT hoddT hKnormalT hcompT hPsub_prime hfixT
  have hnilK : Group.IsNilpotent K := by
    let e : K.subgroupOf T ≃* K :=
      Subgroup.subgroupOfEquivOfLe (H := K) (K := T) (by simp [T])
    let _ : Group.IsNilpotent (K.subgroupOf T) := hnilKsub
    exact Group.nilpotent_of_mulEquiv (G := K.subgroupOf T) (G' := K) e
  have hDQ_eq : D ⊔ Q = K := by
    simp [K, sup_comm]
  exact hDnotnil (by rw [hDQ_eq]; exact hnilK)

private theorem CFSG.section12_lemma_12_18_a_rechosen_sylow_quotient_normalizer_core
    {M P Q D RG : Subgroup G} {p q r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M)
    (hq : q ∈ section10PPrimeSet p)
    (hQle : Q ≤ M) (_hQne : Q ≠ ⊥) (hQq : IsPGroup q.val Q)
    (hPinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (_hnotUnique : section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M})
    (hqα : q ∉ section10AlphaPrimes M)
    (_hCPne : subgroupCentralizerIn (section10Malpha M) P ≠ ⊥)
    (hrα : r ∈ section10AlphaPrimes M)
    (hDp : IsPGroup r.val D)
    (hDpow : ∀ x : D, x ^ r.val = 1)
    (hD_le_malpha : D ≤ section10Malpha M)
    (hPnormD : P ≤ Subgroup.normalizer (D : Set G))
    (hQnormD : Q ≤ Subgroup.normalizer (D : Set G))
    (hCDPrank : groupRank (subgroupCentralizerIn D P) ≤ 1)
    (hCDQrank : groupRank (subgroupCentralizerIn D Q) ≤ 1)
    (hD_le_RG : D ≤ RG)
    (hRGp : IsPGroup r.val RG)
    (hCRPQne : subgroupCentralizerIn RG (P ⊔ Q) ≠ ⊥)
    (hCRPrank : groupRank (subgroupCentralizerIn RG P) ≤ 1)
    (hCRQrank : groupRank (subgroupCentralizerIn RG Q) ≤ 1)
    (hDnotnil : ¬ Group.IsNilpotent (D ⊔ Q : Subgroup G)) :
    False := by
  have hCDPne : subgroupCentralizerIn D P ≠ ⊥ :=
    section12_lemma_12_18_a_critical_image_centralizer_P_ne_bot
      (G := G) (M := M) (P := P) (Q := Q) (D := D)
      (p := p) (q := q) (r := r)
      hM hp hP hq hQle hQq hPinv hCQ hqα hrα hDp
      hD_le_malpha hPnormD hQnormD hDnotnil
  have hCRPne : subgroupCentralizerIn RG P ≠ ⊥ :=
    section12_subgroupCentralizerIn_antitone_right_ne_bot_current
      (G := G) (A := RG) (S := P) (T := P ⊔ Q) le_sup_left hCRPQne
  have hCRQne : subgroupCentralizerIn RG Q ≠ ⊥ :=
    section12_subgroupCentralizerIn_antitone_right_ne_bot_current
      (G := G) (A := RG) (S := Q) (T := P ⊔ Q) le_sup_right hCRPQne
  have hrodd : r.val ≠ 2 := by
    have hr_dvd_G : r.val ∣ Nat.card G :=
      hrα.1.trans (Subgroup.card_subgroup_dvd_card M)
    exact Odd.ne_two_of_dvd_nat IsMinCE.odd_order hr_dvd_G
  have hCDPp : IsPGroup r.val (subgroupCentralizerIn D P) :=
    IsPGroup.to_le hDp inf_le_left
  have hCDPpow : ∀ x : subgroupCentralizerIn D P, x ^ r.val = 1 := by
    intro x
    apply Subtype.ext
    change ((x : subgroupCentralizerIn D P) : G) ^ r.val = 1
    have hpowD := hDpow ⟨(x : G), x.property.1⟩
    exact congrArg D.subtype hpowD
  have hCDPcard : Nat.card (subgroupCentralizerIn D P) = r.val :=
    section12_natCard_eq_prime_of_rank_le_one_exponent_prime_current
      (G := G) (C := subgroupCentralizerIn D P) (r := r)
      hrodd hCDPp hCDPne hCDPrank hCDPpow
  have hCRPp : IsPGroup r.val (subgroupCentralizerIn RG P) :=
    IsPGroup.to_le hRGp inf_le_left
  have hCRQp : IsPGroup r.val (subgroupCentralizerIn RG Q) :=
    IsPGroup.to_le hRGp inf_le_left
  have hCRPcyc : IsCyclic (subgroupCentralizerIn RG P) :=
    section12_isCyclic_of_rank_le_one_pGroup_current
      (G := G) (C := subgroupCentralizerIn RG P) (r := r)
      hrodd hCRPp hCRPrank
  have hCRQcyc : IsCyclic (subgroupCentralizerIn RG Q) :=
    section12_isCyclic_of_rank_le_one_pGroup_current
      (G := G) (C := subgroupCentralizerIn RG Q) (r := r)
      hrodd hCRQp hCRQrank
  have hCDP_le_CRP : subgroupCentralizerIn D P ≤ subgroupCentralizerIn RG P := by
    intro x hx
    exact ⟨hD_le_RG hx.1, hx.2⟩
  have hOmegaCRP_le_CDP :
      section12OmegaOneSubgroup r (subgroupCentralizerIn RG P) ≤
        subgroupCentralizerIn D P :=
    section12_omegaOneSubgroup_le_of_nontrivial_subgroup_of_cyclic_pSubgroup
      (G := G) (H := subgroupCentralizerIn RG P)
      (K := subgroupCentralizerIn D P) (p := r)
      hCRPp hCRPcyc hCRPne hCDP_le_CRP hCDPne
  have hOmegaCRP_card :
      Nat.card (section12OmegaOneSubgroup r (subgroupCentralizerIn RG P)) =
        r.val :=
    section12_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
      (G := G) (H := subgroupCentralizerIn RG P) (p := r)
      hCRPp hCRPcyc hCRPne
  have hOmegaCRQ_card :
      Nat.card (section12OmegaOneSubgroup r (subgroupCentralizerIn RG Q)) =
        r.val :=
    section12_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
      (G := G) (H := subgroupCentralizerIn RG Q) (p := r)
      hCRQp hCRQcyc hCRQne
  have hOmegaCRP_eq_CDP :
      section12OmegaOneSubgroup r (subgroupCentralizerIn RG P) =
        subgroupCentralizerIn D P :=
    Subgroup.eq_of_le_of_card_ge hOmegaCRP_le_CDP (by
      rw [hOmegaCRP_card, hCDPcard])
  have hCRPQ_le_CRP :
      subgroupCentralizerIn RG (P ⊔ Q) ≤ subgroupCentralizerIn RG P :=
    section12_subgroupCentralizerIn_antitone_right_current
      (G := G) (A := RG) (S := P) (T := P ⊔ Q) le_sup_left
  have hCRPQ_le_CRQ :
      subgroupCentralizerIn RG (P ⊔ Q) ≤ subgroupCentralizerIn RG Q :=
    section12_subgroupCentralizerIn_antitone_right_current
      (G := G) (A := RG) (S := Q) (T := P ⊔ Q) le_sup_right
  have hOmegaCRP_le_CRPQ :
      section12OmegaOneSubgroup r (subgroupCentralizerIn RG P) ≤
        subgroupCentralizerIn RG (P ⊔ Q) :=
    section12_omegaOneSubgroup_le_of_nontrivial_subgroup_of_cyclic_pSubgroup
      (G := G) (H := subgroupCentralizerIn RG P)
      (K := subgroupCentralizerIn RG (P ⊔ Q)) (p := r)
      hCRPp hCRPcyc hCRPne hCRPQ_le_CRP hCRPQne
  have hOmegaCRQ_le_CRPQ :
      section12OmegaOneSubgroup r (subgroupCentralizerIn RG Q) ≤
        subgroupCentralizerIn RG (P ⊔ Q) :=
    section12_omegaOneSubgroup_le_of_nontrivial_subgroup_of_cyclic_pSubgroup
      (G := G) (H := subgroupCentralizerIn RG Q)
      (K := subgroupCentralizerIn RG (P ⊔ Q)) (p := r)
      hCRQp hCRQcyc hCRQne hCRPQ_le_CRQ hCRPQne
  have hOmegaCRP_le_CRQ :
      section12OmegaOneSubgroup r (subgroupCentralizerIn RG P) ≤
        subgroupCentralizerIn RG Q :=
    hOmegaCRP_le_CRPQ.trans hCRPQ_le_CRQ
  have hOmegaCRQ_le_CRP :
      section12OmegaOneSubgroup r (subgroupCentralizerIn RG Q) ≤
        subgroupCentralizerIn RG P :=
    hOmegaCRQ_le_CRPQ.trans hCRPQ_le_CRP
  have hOmegaCRP_le_OmegaCRQ :
      section12OmegaOneSubgroup r (subgroupCentralizerIn RG P) ≤
        section12OmegaOneSubgroup r (subgroupCentralizerIn RG Q) :=
    section12_primeOrder_le_omegaOneSubgroup_of_le
      (G := G) (H := subgroupCentralizerIn RG Q)
      (X := section12OmegaOneSubgroup r (subgroupCentralizerIn RG P))
      (p := r) ⟨hOmegaCRP_le_CRQ, hOmegaCRP_card⟩
  have hOmegaCRQ_le_OmegaCRP :
      section12OmegaOneSubgroup r (subgroupCentralizerIn RG Q) ≤
        section12OmegaOneSubgroup r (subgroupCentralizerIn RG P) :=
    section12_primeOrder_le_omegaOneSubgroup_of_le
      (G := G) (H := subgroupCentralizerIn RG P)
      (X := section12OmegaOneSubgroup r (subgroupCentralizerIn RG Q))
      (p := r) ⟨hOmegaCRQ_le_CRP, hOmegaCRQ_card⟩
  have hOmegaCRP_eq_OmegaCRQ :
      section12OmegaOneSubgroup r (subgroupCentralizerIn RG P) =
        section12OmegaOneSubgroup r (subgroupCentralizerIn RG Q) :=
    le_antisymm hOmegaCRP_le_OmegaCRQ hOmegaCRQ_le_OmegaCRP
  have hCDP_le_CDQ : subgroupCentralizerIn D P ≤ subgroupCentralizerIn D Q := by
    intro x hx
    have hxOmegaP :
        x ∈ section12OmegaOneSubgroup r (subgroupCentralizerIn RG P) := by
      simpa [hOmegaCRP_eq_CDP] using hx
    have hxOmegaQ :
        x ∈ section12OmegaOneSubgroup r (subgroupCentralizerIn RG Q) := by
      rw [← hOmegaCRP_eq_OmegaCRQ]
      exact hxOmegaP
    have hxCRQ : x ∈ subgroupCentralizerIn RG Q := by
      rcases Subgroup.mem_map.mp hxOmegaQ with ⟨y, _hy, rfl⟩
      exact y.property
    exact ⟨hx.1, hxCRQ.2⟩
  have hCDQne : subgroupCentralizerIn D Q ≠ ⊥ := by
    intro hbot
    apply hCDPne
    apply le_bot_iff.mp
    intro x hx
    have hxQ : x ∈ subgroupCentralizerIn D Q := hCDP_le_CDQ hx
    simpa [hbot] using hxQ
  have hCDQp : IsPGroup r.val (subgroupCentralizerIn D Q) :=
    IsPGroup.to_le hDp inf_le_left
  have hCDQpow : ∀ x : subgroupCentralizerIn D Q, x ^ r.val = 1 := by
    intro x
    apply Subtype.ext
    change ((x : subgroupCentralizerIn D Q) : G) ^ r.val = 1
    have hpowD := hDpow ⟨(x : G), x.property.1⟩
    exact congrArg D.subtype hpowD
  have hCDQcard : Nat.card (subgroupCentralizerIn D Q) = r.val :=
    section12_natCard_eq_prime_of_rank_le_one_exponent_prime_current
      (G := G) (C := subgroupCentralizerIn D Q) (r := r)
      hrodd hCDQp hCDQne hCDQrank hCDQpow
  have hCDP_eq_CDQ : subgroupCentralizerIn D P = subgroupCentralizerIn D Q :=
    Subgroup.eq_of_le_of_card_ge hCDP_le_CDQ (by
      rw [hCDQcard, hCDPcard])
  let R0 : Subgroup G := subgroupCentralizerIn D Q
  let N : Subgroup G := subgroupNormalizerIn D (R0 : Set G)
  have hCDP_eq_R0 : subgroupCentralizerIn D P = R0 := by
    simpa [R0] using hCDP_eq_CDQ
  have hR0_le_D : R0 ≤ D := by
    intro x hx
    exact hx.1
  have hR0_ne : R0 ≠ ⊥ := by
    simpa [R0] using hCDQne
  have hR0_card : Nat.card R0 = r.val := by
    simpa [R0] using hCDQcard
  have hPnormR0 : P ≤ Subgroup.normalizer (R0 : Set G) := by
    simpa [R0] using
      section12_le_normalizer_subgroupCentralizerIn_of_normalizers_current
        (G := G) (A := D) (P := Q) (S := P) hPnormD hPinv
  have hQnormR0 : Q ≤ Subgroup.normalizer (R0 : Set G) := by
    simpa [R0] using
      section12_le_normalizer_subgroupCentralizerIn_of_normalizers_current
        (G := G) (A := D) (P := Q) (S := Q) hQnormD Subgroup.le_normalizer
  have hN_le_D : N ≤ D := by
    intro x hx
    exact (mem_subgroupNormalizerIn.mp hx).2
  have hNnormR0 : N ≤ Subgroup.normalizer (R0 : Set G) := by
    simpa [N] using subgroupNormalizerIn_le_normalizer D (R0 : Set G)
  have hR0_le_N : R0 ≤ N := by
    simpa [N] using le_subgroupNormalizerIn (U := D) (H := R0) hR0_le_D
  have hPnormN : P ≤ Subgroup.normalizer (N : Set G) := by
    have hPnorm_normR0 :
        P ≤ Subgroup.normalizer (Subgroup.normalizer (R0 : Set G) : Set G) :=
      hPnormR0.trans Subgroup.le_normalizer
    simpa [N, subgroupNormalizerIn] using
      Subgroup.le_normalizer_inf
        (G := G) (A := P) (H := Subgroup.normalizer (R0 : Set G)) (K := D)
        hPnorm_normR0 hPnormD
  have hQnormN : Q ≤ Subgroup.normalizer (N : Set G) := by
    have hQnorm_normR0 :
        Q ≤ Subgroup.normalizer (Subgroup.normalizer (R0 : Set G) : Set G) :=
      hQnormR0.trans Subgroup.le_normalizer
    simpa [N, subgroupNormalizerIn] using
      Subgroup.le_normalizer_inf
        (G := G) (A := Q) (H := Subgroup.normalizer (R0 : Set G)) (K := D)
        hQnorm_normR0 hQnormD
  have hPnormQN : P ≤ Subgroup.normalizer (Q ⊔ N : Subgroup G) := by
    exact section12_le_normalizer_sup_current
      (G := G) (R := P) (A := Q) (B := N) hPinv hPnormN
  have hQnormN' : Q ≤ Subgroup.normalizer (N : Set G) := hQnormN
  have hqr : q ≠ r := by
    intro h
    subst h
    exact hqα hrα
  have hqr_val : q.val ≠ r.val := by
    intro hval
    exact hqr (Subtype.ext hval)
  let _ : Fact q.val.Prime := ⟨q.property⟩
  let _ : Fact r.val.Prime := ⟨r.property⟩
  have hNp : IsPGroup r.val N :=
    IsPGroup.to_le hDp hN_le_D
  have hQNdisj : Disjoint Q N :=
    IsPGroup.disjoint_of_ne q.val r.val hqr_val Q N hQq hNp
  have hQNfix_eq_CN :
      subgroupCentralizerIn (Q ⊔ N : Subgroup G) P =
        subgroupCentralizerIn N P :=
    section12_subgroupCentralizerIn_sup_eq_right_of_normalized_factors_current
      (G := G) (A := Q) (B := N) (P := P)
      hPinv hPnormN hQnormN hQNdisj hCQ
  have hCN_le_R0 : subgroupCentralizerIn N P ≤ R0 := by
    intro x hx
    have hxCDP : x ∈ subgroupCentralizerIn D P :=
      ⟨hN_le_D hx.1, hx.2⟩
    simpa [hCDP_eq_R0] using hxCDP
  have hR0_le_CN : R0 ≤ subgroupCentralizerIn N P := by
    intro x hx
    have hxCDP : x ∈ subgroupCentralizerIn D P := by
      simpa [hCDP_eq_R0] using hx
    exact ⟨hR0_le_N hx, hxCDP.2⟩
  have hCN_eq_R0 : subgroupCentralizerIn N P = R0 :=
    le_antisymm hCN_le_R0 hR0_le_CN
  have hQNfix_eq_R0 : subgroupCentralizerIn (Q ⊔ N : Subgroup G) P = R0 := by
    rw [hQNfix_eq_CN, hCN_eq_R0]
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hPleM, hPcard⟩
  rcases (by simpa [section12Tau1Primes] using hp) with
    ⟨hp_notσ, _hpD, _hprank_one⟩
  have hp_notα : p ∉ section10AlphaPrimes M := by
    intro hpα
    exact hp_notσ (section12_sigmaPrimes_mem_of_alphaPrimes_mem (G := G) hM hpα)
  let K : Subgroup G := Q ⊔ N
  let T : Subgroup G := P ⊔ K
  have hK_eq : K = Q ⊔ N := rfl
  have hR0_le_K : R0 ≤ K := by
    exact hR0_le_N.trans le_sup_right
  have hK_le_malpha : K ≤ M := by
    exact sup_le hQle (hN_le_D.trans (hD_le_malpha.trans (section10_malpha_le (G := G))))
  have hTleM : T ≤ M := by
    exact sup_le hPleM hK_le_malpha
  have hTne_top : T ≠ ⊤ := by
    intro hTtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      rw [← hTtop]
      exact hTleM
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hsolvT : Group.IsSolvable T :=
    IsMinCE.proper_subgroups_solvable T (lt_top_iff_ne_top.2 hTne_top)
  have hoddT : Odd (Nat.card T) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card T)
  have hKnormR0 : K ≤ Subgroup.normalizer (R0 : Set G) := by
    exact sup_le hQnormR0 hNnormR0
  have hTnormR0 : T ≤ Subgroup.normalizer (R0 : Set G) := by
    exact sup_le hPnormR0 hKnormR0
  have hR0_le_T : R0 ≤ T := hR0_le_K.trans le_sup_right
  let L : Subgroup T := R0.subgroupOf T
  have hLnormalT : L.Normal := by
    simpa [L] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer hR0_le_T).2 hTnormR0
  have hKnormalT : (K.subgroupOf T).Normal := by
    simpa [K, T] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := P) (N := K) hPnormQN)
  have hQp' : IsPiSubgroup (G := G) (section10PPrimeSet p) Q :=
    section12_isPiSubgroup_of_isPGroup_mem_current (G := G) hq hQq
  have hrp' : r ∈ section10PPrimeSet p := by
    rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hrp
    exact hp_notα (by simpa [hrp] using hrα)
  have hNp' : IsPiSubgroup (G := G) (section10PPrimeSet p) N :=
    section12_isPiSubgroup_of_isPGroup_mem_current (G := G) hrp' hNp
  have hKp' : IsPiSubgroup (G := G) (section10PPrimeSet p) K := by
    simpa [K] using
      section12_isPiSubgroup_sup_of_le_normalizer_alpha_local
        (G := G) (π := section10PPrimeSet p) (H := Q) (K := N)
        hQp' hNp' hQnormN
  have hPp : IsPGroup p.val P :=
    section12_primeOrderSubgroupsIn_isPGroup (G := G) (A := M) hP
  have hPπ : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) P :=
    section8_isPiSubgroup_singleton_of_isPGroup (G := G) (H := P) (q := p) hPp
  have hp'_disj_singleton : Disjoint (section10PPrimeSet p) ({p} : Set Nat.Primes) := by
    rw [Set.disjoint_left]
    intro s hs_p' hs_p
    have hs_not_p : s ∉ ({p} : Set Nat.Primes) := by
      simpa [section10PPrimeSet] using hs_p'
    exact hs_not_p hs_p
  have hK_P_disj : Disjoint K P :=
    section12_disjoint_of_isPiSubgroup_disjoint_primes_current
      (G := G) hKp' hPπ hp'_disj_singleton
  have hKsub_Psub_disj : Disjoint (K.subgroupOf T) (P.subgroupOf T) := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxP
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hK_P_disj hxK hxP
  have hKsubPsub_top : K.subgroupOf T ⊔ P.subgroupOf T = ⊤ := by
    calc
      K.subgroupOf T ⊔ P.subgroupOf T = P.subgroupOf T ⊔ K.subgroupOf T := by
        rw [sup_comm]
      _ = T.subgroupOf T := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := P) (A' := K) (B := T)
          (by simp [T])
          (by simp [T])
      _ = ⊤ := by simp
  have hcompT : (K.subgroupOf T).IsComplement' (P.subgroupOf T) := by
    let _ : (K.subgroupOf T).Normal := hKnormalT
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · exact hKsub_Psub_disj
    · rw [Set.eq_univ_iff_forall]
      intro y
      have hyTop : y ∈ K.subgroupOf T ⊔ P.subgroupOf T := by
        simp [hKsubPsub_top]
      rcases (Subgroup.mem_sup_of_normal_left
          (s := K.subgroupOf T) (t := P.subgroupOf T) (x := y)).1 hyTop with
        ⟨k, hk, p0, hp0, hkp⟩
      exact ⟨k, hk, p0, hp0, hkp⟩
  have hPsub_prime : Nat.Prime (Nat.card (P.subgroupOf T)) := by
    have hcard : Nat.card (P.subgroupOf T) = p.val := by
      rw [natCard_subgroupOf_eq P T (by simp [T]), hPcard]
    simpa [hcard] using p.property
  have hL_le_Ksub : L ≤ K.subgroupOf T := by
    intro x hx
    exact hR0_le_K hx
  have hfix_sub :
      subgroupCentralizerIn (K.subgroupOf T) (P.subgroupOf T) = L := by
    rw [subgroupCentralizerIn_subgroupOf_eq T K P (by simp [T]), hQNfix_eq_R0]
  let qT : T →* T ⧸ L := QuotientGroup.mk' L
  have hcopKP : Nat.Coprime (Nat.card K) (Nat.card P) :=
    section12_coprime_card_of_isPiSubgroup_disjoint_primes_current
      (G := G) hKp' hPπ hp'_disj_singleton
  have hcopKsubPsub :
      Nat.Coprime (Nat.card (K.subgroupOf T)) (Nat.card (P.subgroupOf T)) := by
    rw [natCard_subgroupOf_eq K T (by simp [T]),
      natCard_subgroupOf_eq P T (by simp [T])]
    exact hcopKP
  have hcent_map :
      subgroupCentralizerIn ((K.subgroupOf T).map qT) ((P.subgroupOf T).map qT) =
        (subgroupCentralizerIn (K.subgroupOf T) (P.subgroupOf T)).map qT := by
    let _ : L.Normal := hLnormalT
    have hPsub_norm_Ksub : P.subgroupOf T ≤ Subgroup.normalizer (K.subgroupOf T) :=
      Subgroup.le_normalizer_of_normal (H := K.subgroupOf T)
    have hsolvKsub : Group.IsSolvable (K.subgroupOf T) := by
      let _ : Group.IsSolvable T := hsolvT
      infer_instance
    have hLinv : ∀ p0 : P.subgroupOf T, ∀ x ∈ L, (p0 : T) * x * (p0 : T)⁻¹ ∈ L := by
      intro p0 x hx
      exact (inferInstance : L.Normal).conj_mem x hx (p0 : T)
    exact
      subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
        (G := T) (H := K.subgroupOf T) (R := P.subgroupOf T) (X := L)
        hPsub_norm_Ksub hsolvKsub hcopKsubPsub hLinv
  have hfix_quot :
      subgroupCentralizerIn ((K.subgroupOf T).map qT) ((P.subgroupOf T).map qT) = ⊥ := by
    rw [hcent_map, hfix_sub]
    simp [qT]
  have hcomp_quot :
      ((K.subgroupOf T).map qT).IsComplement' ((P.subgroupOf T).map qT) := by
    let _ : L.Normal := hLnormalT
    exact
      isComplement'_map_mk'_of_le_isComplement'
        (K.subgroupOf T) (P.subgroupOf T) L hL_le_Ksub hcompT
  have hPmap_prime : Nat.Prime (Nat.card ((P.subgroupOf T).map qT)) := by
    let _ : L.Normal := hLnormalT
    have hcard :
        Nat.card ((P.subgroupOf T).map qT) = Nat.card (P.subgroupOf T) :=
      natCard_map_mk'_eq_of_le_isComplement'
        (K.subgroupOf T) (P.subgroupOf T) L hL_le_Ksub hcompT
    rw [hcard]
    exact hPsub_prime
  have hKmap_normal : ((K.subgroupOf T).map qT).Normal := by
    let _ : L.Normal := hLnormalT
    exact hKnormalT.map qT (QuotientGroup.mk'_surjective L)
  have hsolv_quot : Group.IsSolvable (T ⧸ L) := by
    let _ : Group.IsSolvable T := hsolvT
    infer_instance
  have hodd_quot : Odd (Nat.card (T ⧸ L)) := by
    let _ : L.Normal := hLnormalT
    exact theorem_3_7_quotient_odd_of_normal L hoddT
  have hnil_Kquot : Group.IsNilpotent ((K.subgroupOf T).map qT) := by
    exact theorem_3_7 (G := T ⧸ L)
      ((K.subgroupOf T).map qT) ((P.subgroupOf T).map qT)
      hsolv_quot hodd_quot hKmap_normal hcomp_quot hPmap_prime hfix_quot
  have hR0_lt_D : R0 < D := by
    refine ⟨hR0_le_D, ?_⟩
    intro hD_le_R0
    have hDcentQ : D ≤ Subgroup.centralizer (Q : Set G) := by
      intro x hx
      exact (hD_le_R0 hx).2
    have hnil_DQ : Group.IsNilpotent (D ⊔ Q : Subgroup G) :=
      section12_sup_isNilpotent_of_commuting_nilpotent_current
        (G := G) (A := D) (B := Q) hDcentQ hDp.isNilpotent hQq.isNilpotent
    exact hDnotnil hnil_DQ
  have hR0_lt_N : R0 < N := by
    rcases section12_exists_pSubgroup_gt_le_normalizer_of_lt_pgroup_local
        (G := G) (S := D) (X := R0) (p := r.val)
        hDp hR0_lt_D with
      ⟨Y, hR0_lt_Y, hY_le_D, hY_le_normR0, hYp⟩
    refine ⟨hR0_le_N, ?_⟩
    intro hN_le_R0
    have hY_le_N : Y ≤ N := by
      intro y hy
      exact mem_subgroupNormalizerIn.mpr ⟨hY_le_normR0 hy, hY_le_D hy⟩
    exact hR0_lt_Y.not_ge (hY_le_N.trans hN_le_R0)
  have hR0cyc : IsCyclic R0 := isCyclic_of_prime_card hR0_card
  have hNcentR0 : N ≤ Subgroup.centralizer (R0 : Set G) := by
    let _ : Subgroup.Normalizes N R0 := ⟨hNnormR0⟩
    have htriv : ActsTrivially (A := N) (G := R0) :=
      actsTrivially_of_isPGroup_on_cyclic_prime_order
        r.property hNp hR0cyc hR0_card
    have hcomm : ⁅N, R0⁆ = ⊥ :=
      commutator_eq_bot_of_actsTrivially_subgroup_conj
        (K := R0) (R := N) hNnormR0 htriv
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  have hQcentR0 : Q ≤ Subgroup.centralizer (R0 : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm
  have hKcentR0 : K ≤ Subgroup.centralizer (R0 : Set G) := by
    simpa [K] using sup_le hQcentR0 hNcentR0
  have hR0centK : R0 ≤ Subgroup.centralizer (K : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hKcentR0 hy) x hx).symm
  have hLsub_center :
      L.subgroupOf (K.subgroupOf T) ≤ Subgroup.center (K.subgroupOf T) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxR0 : (((x : K.subgroupOf T) : T) : G) ∈ R0 := by
      simpa [L, Subgroup.mem_subgroupOf] using hx
    have hyK : (((y : K.subgroupOf T) : T) : G) ∈ K := by
      exact y.property
    have hcomm :
        (((y : K.subgroupOf T) : T) : G) * (((x : K.subgroupOf T) : T) : G) =
          (((x : K.subgroupOf T) : T) : G) * (((y : K.subgroupOf T) : T) : G) :=
      Subgroup.mem_centralizer_iff.mp (hR0centK hxR0)
        (((y : K.subgroupOf T) : T) : G) hyK
    apply Subtype.ext
    exact hcomm
  have hnil_Ksub : Group.IsNilpotent (K.subgroupOf T) := by
    let Lsub : Subgroup (K.subgroupOf T) := L.subgroupOf (K.subgroupOf T)
    have hLsub_normal : Lsub.Normal := by
      simpa [Lsub] using
        Subgroup.Normal.subgroupOf
          (G := T) (H := L) (K := K.subgroupOf T) (hH := hLnormalT)
    have hnil_quot_sub : Group.IsNilpotent (K.subgroupOf T ⧸ Lsub) := by
      let _ : L.Normal := hLnormalT
      let e : (K.subgroupOf T ⧸ Lsub) ≃* (K.subgroupOf T).map qT := by
        simpa [Lsub, qT] using quotientSubgroupRangeEquiv (K.subgroupOf T) L
      let _ : Group.IsNilpotent ((K.subgroupOf T).map qT) := hnil_Kquot
      exact Group.nilpotent_of_mulEquiv
        (G := (K.subgroupOf T).map qT) (G' := K.subgroupOf T ⧸ Lsub) e.symm
    let _ : Lsub.Normal := hLsub_normal
    let qK : K.subgroupOf T →* K.subgroupOf T ⧸ Lsub := QuotientGroup.mk' Lsub
    have hker_center : qK.ker ≤ Subgroup.center (K.subgroupOf T) := by
      intro x hx
      have hxL : x ∈ Lsub := by
        simpa [qK, Lsub, QuotientGroup.eq_one_iff] using hx
      simpa [Lsub] using hLsub_center hxL
    let _ : Group.IsNilpotent (K.subgroupOf T ⧸ Lsub) := hnil_quot_sub
    exact Subgroup.isNilpotent_of_ker_le_center qK hker_center
  have hnilK : Group.IsNilpotent K := by
    let e : K.subgroupOf T ≃* K :=
      Subgroup.subgroupOfEquivOfLe (H := K) (K := T) (by simp [T])
    let _ : Group.IsNilpotent (K.subgroupOf T) := hnil_Ksub
    exact Group.nilpotent_of_mulEquiv (G := K.subgroupOf T) (G' := K) e
  have hNπ : IsPiSubgroup (G := G) ({r} : Set Nat.Primes) N :=
    section8_isPiSubgroup_singleton_of_isPGroup (G := G) (H := N) (q := r) hNp
  have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
    section8_isPiSubgroup_singleton_of_isPGroup (G := G) (H := Q) (q := q) hQq
  have hπρ : Disjoint ({r} : Set Nat.Primes) ({q} : Set Nat.Primes) := by
    rw [Set.disjoint_left]
    intro s hs_r hs_q
    have hsr : s = r := by simpa using hs_r
    have hsq : s = q := by simpa using hs_q
    exact hqr (hsq.symm.trans hsr)
  have hNcentQ : N ≤ Subgroup.centralizer (Q : Set G) :=
    section10_isPiSubgroup_le_centralizer_of_nilpotent_disjoint
      (G := G) (π := ({r} : Set Nat.Primes)) (ρ := ({q} : Set Nat.Primes))
      (L := K) (A := N) (B := Q) hπρ hnilK
      (by simp [K]) (by simp [K]) hNπ hQπ
  have hN_le_R0 : N ≤ R0 := by
    intro x hx
    exact ⟨hN_le_D hx, hNcentQ hx⟩
  have hN_eq_R0 : N = R0 := le_antisymm hN_le_R0 hR0_le_N
  exact hR0_lt_N.ne hN_eq_R0.symm

private theorem CFSG.section12_lemma_12_18_a_rechosen_sylow_quotient_core
    {M P Q : Subgroup G} {p q r : Nat.Primes}
    [Subgroup.Normalizes (P ⊔ Q) (section10Malpha M)]
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M)
    (hq : q ∈ section10PPrimeSet p)
    (hQle : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q.val Q)
    (hPinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hnotUnique : section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M})
    (hqα : q ∉ section10AlphaPrimes M)
    (hCPne : subgroupCentralizerIn (section10Malpha M) P ≠ ⊥)
    (hrα : r ∈ section10AlphaPrimes M)
    (R : Sylow r.val (section10Malpha M))
    (hRinv : IsInvariant (↥(P ⊔ Q)) (section10Malpha M)
      (R : Subgroup (section10Malpha M)))
    (hCRPQne :
      subgroupCentralizerIn
        ((R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype)
        (P ⊔ Q) ≠ ⊥)
    (_hCRPne :
      subgroupCentralizerIn
        ((R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype)
        P ≠ ⊥)
    (_hCRQne :
      subgroupCentralizerIn
        ((R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype)
        Q ≠ ⊥)
    (hCRPrank :
      groupRank
        (subgroupCentralizerIn
          ((R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype)
          P) ≤ 1)
    (hCRQrank :
      groupRank
        (subgroupCentralizerIn
          ((R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype)
          Q) ≤ 1)
    {R1 : Subgroup (R : Subgroup (section10Malpha M))}
    (hR1char : R1.Characteristic)
    (_hR1comm : ⁅R1, ⊤⁆ ≤
      centerIn (G := (R : Subgroup (section10Malpha M))) R1)
    (_hR1nil : NilpotencyClassLe 2 (↥R1))
    (hR1exp : Monoid.exponent (↥R1) = r.val)
    (_hR1fix : IsPGroup r.val
      (↥(fixingSubgroup
        (M := MulAut (R : Subgroup (section10Malpha M)))
        (α := (R : Subgroup (section10Malpha M)))
        (R1 : Set (R : Subgroup (section10Malpha M))))))
    (hR1noncentral :
      ¬ (R1.map (R : Subgroup (section10Malpha M)).subtype).map
          (section10Malpha M).subtype ≤ Subgroup.centralizer (Q : Set G)) :
    False := by
  classical
  let Rsub : Subgroup (section10Malpha M) := (R : Subgroup (section10Malpha M))
  let RG : Subgroup G := Rsub.map (section10Malpha M).subtype
  let D : Subgroup G := (R1.map Rsub.subtype).map (section10Malpha M).subtype
  have hD_le_RG : D ≤ RG := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
    exact Subgroup.mem_map.mpr ⟨z, z.property, rfl⟩
  have hD_le_malpha : D ≤ section10Malpha M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hD_p : IsPGroup r.val D := by
    have hR1p : IsPGroup r.val R1 := R.isPGroup'.to_subgroup R1
    have hR1map_p : IsPGroup r.val (R1.map Rsub.subtype) :=
      IsPGroup.map (p := r.val) (H := R1) hR1p Rsub.subtype
    simpa [D, Rsub] using
      IsPGroup.map (p := r.val) (H := R1.map Rsub.subtype) hR1map_p
        (section10Malpha M).subtype
  have hRG_p : IsPGroup r.val RG := by
    simpa [RG, Rsub] using
      IsPGroup.map (p := r.val) (H := Rsub) R.isPGroup'
        (section10Malpha M).subtype
  have hDpow : ∀ x : D, x ^ r.val = 1 := by
    intro x
    rcases x with ⟨x, hxD⟩
    rcases Subgroup.mem_map.mp hxD with ⟨xMα, hxR1map, hx_eq⟩
    rcases Subgroup.mem_map.mp hxR1map with ⟨xR, hxR1, hxMα_eq⟩
    let xR1 : R1 := ⟨xR, hxR1⟩
    have hpowR1 : xR1 ^ r.val = 1 := by
      have hdiv : Monoid.exponent (↥R1) ∣ r.val := by simp [hR1exp]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hdiv xR1
    have hx_toG :
        x = (section10Malpha M).subtype (Rsub.subtype (xR1 : Rsub)) := by
      calc
        x = (section10Malpha M).subtype xMα := hx_eq.symm
        _ = (section10Malpha M).subtype (Rsub.subtype xR) := by rw [hxMα_eq]
        _ = (section10Malpha M).subtype (Rsub.subtype (xR1 : Rsub)) := by
          rfl
    have hpowG :
        ((section10Malpha M).subtype (Rsub.subtype (xR1 : Rsub))) ^ r.val = 1 := by
      simpa using congrArg
        (fun y : R1 => (section10Malpha M).subtype (Rsub.subtype (y : Rsub)))
        hpowR1
    apply Subtype.ext
    change x ^ r.val = 1
    rw [hx_toG]
    exact hpowG
  have hPQnormD :
      P ⊔ Q ≤ Subgroup.normalizer (D : Set G) := by
    simpa [D, Rsub] using
      section12_lemma_12_18_a_critical_le_normalizer
        (G := G) (M := M) (P := P) (Q := Q) (r := r)
        R hRinv hR1char
  have hPnormD : P ≤ Subgroup.normalizer (D : Set G) :=
    le_sup_left.trans hPQnormD
  have hQnormD : Q ≤ Subgroup.normalizer (D : Set G) :=
    le_sup_right.trans hPQnormD
  have hDnotnil : ¬ Group.IsNilpotent (D ⊔ Q : Subgroup G) := by
    simpa [D, Rsub] using
      section12_lemma_12_18_a_not_nilpotent_sup_critical
        (G := G) (M := M) (Q := Q) (q := q) (r := r)
        hQq hqα hrα R hR1noncentral
  have hCDPrank : groupRank (subgroupCentralizerIn D P) ≤ 1 :=
    section12_subgroupCentralizerIn_rank_le_one_of_left_le_current
      (G := G) (A := D) (B := RG) (S := P) hD_le_RG
      (by simpa [RG, Rsub] using hCRPrank)
  have hCDQrank : groupRank (subgroupCentralizerIn D Q) ≤ 1 :=
    section12_subgroupCentralizerIn_rank_le_one_of_left_le_current
      (G := G) (A := D) (B := RG) (S := Q) hD_le_RG
      (by simpa [RG, Rsub] using hCRQrank)
  have hCRPQne_keep :
      subgroupCentralizerIn RG (P ⊔ Q) ≠ ⊥ := by
    simpa [RG, Rsub] using hCRPQne
  exact
    section12_lemma_12_18_a_rechosen_sylow_quotient_normalizer_core
      (G := G) (M := M) (P := P) (Q := Q) (D := D)
      (RG := RG)
      (p := p) (q := q) (r := r)
      hM hp hP hq hQle hQne hQq hPinv hCQ hnotUnique hqα hCPne
      hrα hD_p hDpow hD_le_malpha hPnormD hQnormD hCDPrank hCDQrank
      hD_le_RG hRG_p hCRPQne_keep
      (by simpa [RG, Rsub] using hCRPrank)
      (by simpa [RG, Rsub] using hCRQrank)
      hDnotnil

private theorem CFSG.section12_lemma_12_18_a_rechosen_sylow_endpoint_core
    {M P Q : Subgroup G} {p q r : Nat.Primes}
    [Subgroup.Normalizes (P ⊔ Q) (section10Malpha M)]
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M)
    (hq : q ∈ section10PPrimeSet p)
    (hQle : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q.val Q)
    (hPinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hnotUnique : section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M})
    (hqα : q ∉ section10AlphaPrimes M)
    (hCQrank : groupRank (subgroupCentralizerIn (section10Malpha M) Q) ≤ 1)
    (hCPrank : groupRank (subgroupCentralizerIn (section10Malpha M) P) ≤ 1)
    (hCPne : subgroupCentralizerIn (section10Malpha M) P ≠ ⊥)
    (hrα : r ∈ section10AlphaPrimes M)
    (R : Sylow r.val (section10Malpha M))
    (hRinv : IsInvariant (↥(P ⊔ Q)) (section10Malpha M)
      (R : Subgroup (section10Malpha M)))
    (hCRPQne :
      subgroupCentralizerIn
        ((R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype)
        (P ⊔ Q) ≠ ⊥)
    {R1 : Subgroup (R : Subgroup (section10Malpha M))}
    (hR1char : R1.Characteristic)
    (hR1comm : ⁅R1, ⊤⁆ ≤
      centerIn (G := (R : Subgroup (section10Malpha M))) R1)
    (hR1nil : NilpotencyClassLe 2 (↥R1))
    (hR1exp : Monoid.exponent (↥R1) = r.val)
    (hR1fix : IsPGroup r.val
      (↥(fixingSubgroup
        (M := MulAut (R : Subgroup (section10Malpha M)))
        (α := (R : Subgroup (section10Malpha M)))
        (R1 : Set (R : Subgroup (section10Malpha M))))))
    (hR1noncentral :
      ¬ (R1.map (R : Subgroup (section10Malpha M)).subtype).map
          (section10Malpha M).subtype ≤ Subgroup.centralizer (Q : Set G)) :
    False := by
  classical
  let RG : Subgroup G := (R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype
  have hCRPne : subgroupCentralizerIn RG P ≠ ⊥ :=
    section12_subgroupCentralizerIn_antitone_right_ne_bot_current
      (G := G) (A := RG) (S := P) (T := P ⊔ Q) le_sup_left (by simpa [RG] using hCRPQne)
  have hCRQne : subgroupCentralizerIn RG Q ≠ ⊥ :=
    section12_subgroupCentralizerIn_antitone_right_ne_bot_current
      (G := G) (A := RG) (S := Q) (T := P ⊔ Q) le_sup_right (by simpa [RG] using hCRPQne)
  have hRGleMα : RG ≤ section10Malpha M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hCRP_le_CP :
      subgroupCentralizerIn RG P ≤ subgroupCentralizerIn (section10Malpha M) P := by
    intro x hx
    exact ⟨hRGleMα hx.1, hx.2⟩
  have hCRQ_le_CQ :
      subgroupCentralizerIn RG Q ≤ subgroupCentralizerIn (section10Malpha M) Q := by
    intro x hx
    exact ⟨hRGleMα hx.1, hx.2⟩
  have hCRPrank : groupRank (subgroupCentralizerIn RG P) ≤ 1 := by
    let Csub : Subgroup (subgroupCentralizerIn (section10Malpha M) P) :=
      (subgroupCentralizerIn RG P).subgroupOf
        (subgroupCentralizerIn (section10Malpha M) P)
    let eCsub : Csub ≃* subgroupCentralizerIn RG P :=
      Subgroup.subgroupOfEquivOfLe
        (H := subgroupCentralizerIn RG P)
        (K := subgroupCentralizerIn (section10Malpha M) P) hCRP_le_CP
    exact
      ((groupRank_le_of_equiv eCsub).trans
        (section8_groupRank_le_of_subgroup Csub)).trans hCPrank
  have hCRQrank : groupRank (subgroupCentralizerIn RG Q) ≤ 1 := by
    let Csub : Subgroup (subgroupCentralizerIn (section10Malpha M) Q) :=
      (subgroupCentralizerIn RG Q).subgroupOf
        (subgroupCentralizerIn (section10Malpha M) Q)
    let eCsub : Csub ≃* subgroupCentralizerIn RG Q :=
      Subgroup.subgroupOfEquivOfLe
        (H := subgroupCentralizerIn RG Q)
        (K := subgroupCentralizerIn (section10Malpha M) Q) hCRQ_le_CQ
    exact
      ((groupRank_le_of_equiv eCsub).trans
        (section8_groupRank_le_of_subgroup Csub)).trans hCQrank
  exact
    section12_lemma_12_18_a_rechosen_sylow_quotient_core
      (G := G) (M := M) (P := P) (Q := Q) (p := p) (q := q) (r := r)
      hM hp hP hq hQle hQne hQq hPinv hCQ hnotUnique hqα hCPne
      hrα R hRinv hCRPQne
      (by simpa [RG] using hCRPne) (by simpa [RG] using hCRQne)
      (by simpa [RG] using hCRPrank) (by simpa [RG] using hCRQrank)
      hR1char hR1comm hR1nil hR1exp hR1fix hR1noncentral

private theorem CFSG.section12_lemma_12_18_a_join_centralizer_bot_of_rechosen_sylow
    {M P Q : Subgroup G} {p q r : Nat.Primes}
    [Subgroup.Normalizes (P ⊔ Q) (section10Malpha M)]
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M)
    (hq : q ∈ section10PPrimeSet p)
    (hQle : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q.val Q)
    (hPinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hnotUnique : section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M})
    (hqα : q ∉ section10AlphaPrimes M)
    (hCQrank : groupRank (subgroupCentralizerIn (section10Malpha M) Q) ≤ 1)
    (hCPrank : groupRank (subgroupCentralizerIn (section10Malpha M) P) ≤ 1)
    (hCPne : subgroupCentralizerIn (section10Malpha M) P ≠ ⊥)
    (hrα : r ∈ section10AlphaPrimes M)
    (R : Sylow r.val (section10Malpha M))
    (hRinv : IsInvariant (↥(P ⊔ Q)) (section10Malpha M)
      (R : Subgroup (section10Malpha M)))
    (hRrank : 3 ≤ groupRank (R : Subgroup (section10Malpha M)))
    (hCRPQne :
      subgroupCentralizerIn
        ((R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype)
        (P ⊔ Q) ≠ ⊥) :
    False := by
  classical
  have hRnoncentral :
      ¬ (R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype ≤
        Subgroup.centralizer (Q : Set G) :=
    section12_lemma_12_18_a_sylow_not_le_centralizer_Q
      (G := G) (M := M) (Q := Q) R hCQrank hRrank
  obtain ⟨R1, hR1char, hR1comm, hR1nil, hR1exp, hR1fix⟩ :=
    section12_lemma_12_18_a_exists_critical_subgroup
      (G := G) (M := M) (r := r) hrα R hRrank
  have hR1noncentral :
      ¬ (R1.map (R : Subgroup (section10Malpha M)).subtype).map
          (section10Malpha M).subtype ≤ Subgroup.centralizer (Q : Set G) :=
    section12_lemma_12_18_a_critical_not_le_centralizer_Q
      (G := G) (M := M) (P := P) (Q := Q) (q := q) (r := r)
      hQq hqα hrα R hRinv hR1fix hRnoncentral
  exact
    section12_lemma_12_18_a_rechosen_sylow_endpoint_core
      (G := G) (M := M) (P := P) (Q := Q) (p := p) (q := q) (r := r)
      hM hp hP hq hQle hQne hQq hPinv hCQ hnotUnique hqα
      hCQrank hCPrank hCPne hrα R hRinv hCRPQne
      hR1char hR1comm hR1nil hR1exp hR1fix hR1noncentral

private theorem CFSG.section12_lemma_12_18_a_join_centralizer_bot_core
    {M P Q : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M)
    (hq : q ∈ section10PPrimeSet p)
    (hQle : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q.val Q)
    (hPinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hnotUnique : section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M})
    (_hMα : section10Malpha M ≠ ⊥)
    (hqα : q ∉ section10AlphaPrimes M)
    (hCQrank : groupRank (subgroupCentralizerIn (section10Malpha M) Q) ≤ 1)
    (hCPrank : groupRank (subgroupCentralizerIn (section10Malpha M) P) ≤ 1)
    (hCPne : subgroupCentralizerIn (section10Malpha M) P ≠ ⊥) :
    subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥ := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPleM, _hPcard⟩
  rcases (by simpa [section12Tau1Primes] using hp) with
    ⟨hp_notσ, _hpD, _hprank_one⟩
  have hp_notα : p ∉ section10AlphaPrimes M := by
    intro hpα
    exact hp_notσ (section12_sigmaPrimes_mem_of_alphaPrimes_mem (G := G) hM hpα)
  have hPp : IsPGroup p.val P :=
    section12_primeOrderSubgroupsIn_isPGroup (G := G) (A := M) hP
  have hPπ : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ P :=
    section12_isPiSubgroup_alpha_compl_of_isPGroup_not_mem
      (G := G) (M := M) hp_notα hPp
  have hQπ : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ Q :=
    section12_isPiSubgroup_alpha_compl_of_isPGroup_not_mem
      (G := G) (M := M) hqα hQq
  have hPQπ : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ (P ⊔ Q) :=
    section12_isPiSubgroup_sup_of_le_normalizer_alpha_local
      (G := G) (π := (section10AlphaPrimes M)ᶜ)
      (H := P) (K := Q) hPπ hQπ hPinv
  have hPQleM : P ⊔ Q ≤ M := sup_le hPleM hQle
  have hPQnorm :
      P ⊔ Q ≤ Subgroup.normalizer (section10Malpha M : Set G) :=
    section10_le_normalizer_malpha_of_le (G := G) hPQleM
  let _ : Subgroup.Normalizes (P ⊔ Q) (section10Malpha M) := ⟨hPQnorm⟩
  let C : Subgroup G := subgroupCentralizerIn (section10Malpha M) (P ⊔ Q)
  change C = ⊥
  by_contra hCne
  have hcard_ne_one : Nat.card C ≠ 1 := by
    intro hcard
    exact hCne ((Subgroup.card_eq_one (H := C)).1 hcard)
  obtain ⟨r0, hr0prime, hr0divC⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let r : Nat.Primes := ⟨r0, hr0prime⟩
  let _ : Fact r.val.Prime := ⟨r.property⟩
  have hrα : r ∈ section10AlphaPrimes M := by
    have hr_dvd_malpha : r.val ∣ Nat.card (section10Malpha M) :=
      hr0divC.trans (Subgroup.card_dvd_of_le (show C ≤ section10Malpha M by
        exact inf_le_left))
    exact (theorem_10_2_a (G := G) hM).1.p_in_pi_of_p_dvd_card r hr_dvd_malpha
  obtain ⟨z, hz_order⟩ := exists_prime_orderOf_dvd_card' (G := C) r.val hr0divC
  let A : Subgroup C := Subgroup.zpowers z
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hr_one : r.val = 1 := by
      rw [← hz_order, hz1, orderOf_one]
    exact r.property.ne_one hr_one
  have hAcard : Nat.card A = r.val := by
    change Nat.card (Subgroup.zpowers z) = r.val
    rw [Nat.card_zpowers]
    exact hz_order
  have hAp : IsPGroup r.val A :=
    IsPGroup.of_card (p := r.val) (G := A) (n := 1) (by simp [hAcard])
  obtain ⟨R, hRinv, hA_le_R⟩ :=
    section12_exists_alpha_invariant_sylow_malpha_containing_witness
      (G := G) (M := M) (X := P ⊔ Q) (r := r) hM hPQπ A hAp
  have hRrank : 3 ≤ groupRank (R : Subgroup (section10Malpha M)) :=
    section12_malpha_sylow_groupRank_ge_three_of_mem_alpha
      (G := G) (M := M) hM hrα R
  have hCRPQne :
      subgroupCentralizerIn
        ((R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype)
        (P ⊔ Q) ≠ ⊥ := by
    intro hbot
    let ι : C →* section10Malpha M :=
      Subgroup.inclusion (show C ≤ section10Malpha M by exact inf_le_left)
    have hA_le_R' : A.map ι ≤ (R : Subgroup (section10Malpha M)) := by
      simpa [C, ι] using hA_le_R
    have hzAmap : ι z ∈ A.map ι :=
      Subgroup.mem_map_of_mem ι (Subgroup.mem_zpowers z)
    have hzR : ι z ∈ (R : Subgroup (section10Malpha M)) :=
      hA_le_R' hzAmap
    have hzRamb :
        ((z : C) : G) ∈
          ((R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype) :=
      Subgroup.mem_map.mpr ⟨ι z, hzR, rfl⟩
    have hzCent :
        ((z : C) : G) ∈ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) :=
      z.property.2
    have hzCR :
        ((z : C) : G) ∈
          subgroupCentralizerIn
            ((R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype)
            (P ⊔ Q) :=
      ⟨hzRamb, hzCent⟩
    have hzbot : ((z : C) : G) ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using hzCR
    have hz1 : ((z : C) : G) = 1 := Subgroup.mem_bot.mp hzbot
    exact hz_ne (Subtype.ext hz1)
  exact False.elim
    (section12_lemma_12_18_a_join_centralizer_bot_of_rechosen_sylow
      (G := G) (M := M) (P := P) (Q := Q) (p := p) (q := q) (r := r)
      hM hp hP hq hQle hQne hQq hPinv hCQ hnotUnique hqα
      hCQrank hCPrank hCPne hrα R hRinv hRrank hCRPQne)

private theorem CFSG.section12_lemma_12_18_a_critical_core
    {M P Q : Subgroup G} {p q r : Nat.Primes}
    [Subgroup.Normalizes (P ⊔ Q) (section10Malpha M)]
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M)
    (hq : q ∈ section10PPrimeSet p)
    (hQle : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q.val Q)
    (hPinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hnotUnique : section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M})
    (hMα : section10Malpha M ≠ ⊥)
    (hqα : q ∉ section10AlphaPrimes M)
    (hCQrank : groupRank (subgroupCentralizerIn (section10Malpha M) Q) ≤ 1)
    (hCPrank : groupRank (subgroupCentralizerIn (section10Malpha M) P) ≤ 1)
    (hrα : r ∈ section10AlphaPrimes M)
    (R : Sylow r.val (section10Malpha M))
    (hRinv : IsInvariant (↥(P ⊔ Q)) (section10Malpha M)
      (R : Subgroup (section10Malpha M)))
    (hRrank : 3 ≤ groupRank (R : Subgroup (section10Malpha M)))
    (hRnoncentral :
      ¬ (R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype ≤
        Subgroup.centralizer (Q : Set G)) :
    subgroupCentralizerIn (section10Malpha M) P ≠ ⊥ ∧
      subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥ := by
  classical
  obtain ⟨R1, hR1char, hR1comm, hR1nil, hR1exp, hR1fix⟩ :=
    section12_lemma_12_18_a_exists_critical_subgroup
      (G := G) (M := M) (r := r) hrα R hRrank
  have hR1noncentral :
      ¬ (R1.map (R : Subgroup (section10Malpha M)).subtype).map
          (section10Malpha M).subtype ≤ Subgroup.centralizer (Q : Set G) :=
    section12_lemma_12_18_a_critical_not_le_centralizer_Q
      (G := G) (M := M) (P := P) (Q := Q) (q := q) (r := r)
      hQq hqα hrα R hRinv hR1fix hRnoncentral
  have hCPne : subgroupCentralizerIn (section10Malpha M) P ≠ ⊥ :=
    section12_lemma_12_18_a_centralizer_P_ne_bot_of_critical
      (G := G) (M := M) (P := P) (Q := Q) (p := p) (q := q) (r := r)
      hM hp hP hq hQle hQq hPinv hCQ hqα hrα R hRinv hR1char hR1noncentral
  exact ⟨hCPne,
    section12_lemma_12_18_a_join_centralizer_bot_core
      (G := G) (M := M) (P := P) (Q := Q) (p := p) (q := q)
      hM hp hP hq hQle hQne hQq hPinv hCQ hnotUnique hMα hqα
      hCQrank hCPrank hCPne⟩

private theorem CFSG.section12_lemma_12_18_a_sylow_core
    {M P Q : Subgroup G} {p q r : Nat.Primes}
    [Subgroup.Normalizes (P ⊔ Q) (section10Malpha M)]
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M)
    (hq : q ∈ section10PPrimeSet p)
    (hQle : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q.val Q)
    (hPinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hnotUnique : section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M})
    (hMα : section10Malpha M ≠ ⊥)
    (hqα : q ∉ section10AlphaPrimes M)
    (hCQrank : groupRank (subgroupCentralizerIn (section10Malpha M) Q) ≤ 1)
    (hCPrank : groupRank (subgroupCentralizerIn (section10Malpha M) P) ≤ 1)
    (hrα : r ∈ section10AlphaPrimes M)
    (R : Sylow r.val (section10Malpha M))
    (hRinv : IsInvariant (↥(P ⊔ Q)) (section10Malpha M)
      (R : Subgroup (section10Malpha M)))
    (hRrank : 3 ≤ groupRank (R : Subgroup (section10Malpha M))) :
    subgroupCentralizerIn (section10Malpha M) P ≠ ⊥ ∧
      subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥ := by
  classical
  have hRnoncentral :
      ¬ (R : Subgroup (section10Malpha M)).map (section10Malpha M).subtype ≤
        Subgroup.centralizer (Q : Set G) :=
    section12_lemma_12_18_a_sylow_not_le_centralizer_Q
      (G := G) (M := M) (Q := Q) R hCQrank hRrank
  exact
    section12_lemma_12_18_a_critical_core
      (G := G) (M := M) (P := P) (Q := Q) (p := p) (q := q) (r := r)
      hM hp hP hq hQle hQne hQq hPinv hCQ hnotUnique hMα hqα
      hCQrank hCPrank hrα R hRinv hRrank hRnoncentral

private theorem CFSG.section12_lemma_12_18_a_fixed_point_core
    {M P Q : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M)
    (hq : q ∈ section10PPrimeSet p)
    (hQle : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q.val Q)
    (hPinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hnotUnique : section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M})
    (hMα : section10Malpha M ≠ ⊥)
    (hqα : q ∉ section10AlphaPrimes M)
    (hCQrank : groupRank (subgroupCentralizerIn (section10Malpha M) Q) ≤ 1)
    (hCPrank : groupRank (subgroupCentralizerIn (section10Malpha M) P) ≤ 1) :
    subgroupCentralizerIn (section10Malpha M) P ≠ ⊥ ∧
      subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥ := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPleM, _hPcard⟩
  rcases (by simpa [section12Tau1Primes] using hp) with
    ⟨hp_notσ, _hpD, _hprank_one⟩
  have hp_notα : p ∉ section10AlphaPrimes M := by
    intro hpα
    exact hp_notσ (section12_sigmaPrimes_mem_of_alphaPrimes_mem (G := G) hM hpα)
  have hPp : IsPGroup p.val P :=
    section12_primeOrderSubgroupsIn_isPGroup (G := G) (A := M) hP
  have hPπ : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ P :=
    section12_isPiSubgroup_alpha_compl_of_isPGroup_not_mem
      (G := G) (M := M) hp_notα hPp
  have hQπ : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ Q :=
    section12_isPiSubgroup_alpha_compl_of_isPGroup_not_mem
      (G := G) (M := M) hqα hQq
  have hPQπ : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ (P ⊔ Q) :=
    section12_isPiSubgroup_sup_of_le_normalizer_alpha_local
      (G := G) (π := (section10AlphaPrimes M)ᶜ)
      (H := P) (K := Q) hPπ hQπ hPinv
  have hPQleM : P ⊔ Q ≤ M := sup_le hPleM hQle
  have hPQnorm :
      P ⊔ Q ≤ Subgroup.normalizer (section10Malpha M : Set G) :=
    section10_le_normalizer_malpha_of_le (G := G) hPQleM
  let _ : Subgroup.Normalizes (P ⊔ Q) (section10Malpha M) := ⟨hPQnorm⟩
  obtain ⟨r, R, hrα, hRinv, hRrank⟩ :=
    section12_exists_alpha_invariant_sylow_malpha
      (G := G) (M := M) (X := P ⊔ Q) hM hMα hPQπ
  exact
    section12_lemma_12_18_a_sylow_core
      (G := G) (M := M) (P := P) (Q := Q) (p := p) (q := q) (r := r)
      hM hp hP hq hQle hQne hQq hPinv hCQ hnotUnique hMα hqα
      hCQrank hCPrank hrα R hRinv hRrank

/-- Lemma 12.18(a). -/
public theorem CFSG.lemma_12_18_a
    {M P Q : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M)
    (hq : q ∈ section10PPrimeSet p)
    (hQle : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q.val Q)
    (hPinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hnotUnique : section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M})
    (hMα : section10Malpha M ≠ ⊥)
    (hqα : q ∉ section10AlphaPrimes M) :
    subgroupCentralizerIn (section10Malpha M) P ≠ ⊥ ∧
      subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥ := by
  classical
  have hCQrank :
      groupRank (subgroupCentralizerIn (section10Malpha M) Q) ≤ 1 :=
    section12_malpha_centralizer_rank_le_one_of_not_unique_normalizer
      (G := G) (M := M) (X := Q) (p := q)
      hM hQle hQne hQq hqα hnotUnique
  have hCPrank :
      groupRank (subgroupCentralizerIn (section10Malpha M) P) ≤ 1 :=
    section12_malpha_centralizer_rank_le_one_of_tau1_primeOrder
      (G := G) (M := M) (P := P) (p := p) hM hp hP
  exact
    section12_lemma_12_18_a_fixed_point_core
      (G := G) (M := M) (P := P) (Q := Q) (p := p) (q := q)
      hM hp hP hq hQle hQne hQq hPinv hCQ hnotUnique hMα hqα hCQrank hCPrank

end Section12
