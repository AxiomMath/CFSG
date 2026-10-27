module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_3_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_centralizer_le_of_unique_normalizer_primeOrder_pre
    {M A A₀ : Subgroup G} {p : Nat.Primes}
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (huniq :
      section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) = {M}) :
    Subgroup.centralizer (A : Set G) ≤ M := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hA₀) with ⟨hA₀A, _hA₀card⟩
  have hMcont :
      M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) := by
    rw [huniq]
    simp
  have hCentA_le_CentA₀ :
      Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (A₀ : Set G) :=
    Subgroup.centralizer_le (show (A₀ : Set G) ⊆ (A : Set G) from hA₀A)
  exact hCentA_le_CentA₀.trans ((centralizer_le_normalizer A₀).trans hMcont.2)

omit [IsMinCE G] in
public theorem CFSG.section12_exists_maximalSubgroupsContaining_of_ne_top_pre
    {H : Subgroup G} (hHproper : H ≠ ⊤) :
    ∃ M : Subgroup G, M ∈ section9MaximalSubgroupsContaining H := by
  rcases eq_top_or_exists_le_coatom H with hHtop | ⟨M, hMcoatom, hHM⟩
  · exact False.elim (hHproper hHtop)
  · refine ⟨M, ?_⟩
    exact ⟨hMcoatom, hHM⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_unique_overgroups_eq_of_contains_maximal_pre
    {H M : Subgroup G} (hH : H ∈ section9UniqueSubgroups G)
    (hM : M ∈ section9MaximalSubgroups G) (hHM : H ≤ M) :
    section9MaximalSubgroupsContaining H = {M} := by
  classical
  rcases hH with ⟨_hHproper, N, hNuniq⟩
  have hMcont : M ∈ section9MaximalSubgroupsContaining H := ⟨hM, hHM⟩
  have hMN : M = N := by
    have hsingle : M ∈ ({N} : Set (Subgroup G)) := by
      simpa [hNuniq] using hMcont
    simpa using hsingle
  simpa [hMN] using hNuniq

omit [IsMinCE G] in
public theorem CFSG.section12_le_unique_maximal_of_le_pre
    {Y X M : Subgroup G} (hYX : Y ≤ X) (hXproper : X ≠ ⊤)
    (hMuniq : section9MaximalSubgroupsContaining Y = {M}) :
    X ≤ M := by
  classical
  rcases eq_top_or_exists_le_coatom X with hXtop | ⟨N, hNcoatom, hXN⟩
  · exact False.elim (hXproper hXtop)
  have hNmax : N ∈ section9MaximalSubgroups G := hNcoatom
  have hNcont : N ∈ section9MaximalSubgroupsContaining Y := ⟨hNmax, hYX.trans hXN⟩
  have hNM : N = M := by
    have hNsingle : N ∈ ({M} : Set (Subgroup G)) := by
      simpa [hMuniq] using hNcont
    simpa using hNsingle
  simpa [hNM] using hXN

omit [IsMinCE G] in
public theorem CFSG.section12_groupRank_at_least_two_of_generatorRank_subgroup_pre
    {q : ℕ} (hq : Nat.Prime q) {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A)
    (hAgen : 2 ≤ generatorRank A) :
    2 ≤ groupRank K := by
  let A' : Subgroup K := A.subgroupOf K
  have hA'p : IsPGroup q A' :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK).symm
  have hA'comm : IsMulCommutative A' := by
    let : IsMulCommutative A := hAcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := K)
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK)
  have hqrankK : 2 ≤ primeRank q K := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card K, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <|
        (section8_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
    · exact ⟨A', hA'p, hA'comm, by simpa [hgen_eq] using hAgen⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨r, _hr, hnr⟩
    exact hnr.trans (section12_primeRank_le_card (R := K) r)
  · exact ⟨q, hq, hqrankK⟩

omit [IsMinCE G] in
public theorem CFSG.section12_generatorRank_le_groupRank_of_subgroup_pre
    {q : ℕ} (hq : Nat.Prime q) {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A) :
    generatorRank A ≤ groupRank K := by
  let A' : Subgroup K := A.subgroupOf K
  have hA'p : IsPGroup q A' :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK).symm
  have hA'comm : IsMulCommutative A' := by
    let : IsMulCommutative A := hAcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := K)
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK)
  have hqrankK : generatorRank A ≤ primeRank q K := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card K, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <|
        (section8_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
    · exact ⟨A', hA'p, hA'comm, by simp [hgen_eq]⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨r, _hr, hnr⟩
    exact hnr.trans (section12_primeRank_le_card (R := K) r)
  · exact ⟨q, hq, hqrankK⟩

omit [IsMinCE G] in
public theorem CFSG.section12_groupRank_at_least_two_of_rankTwo_pre
    {H A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p H) :
    2 ≤ groupRank A := by
  have : Fact p.val.Prime := ⟨p.2⟩
  rcases section12_rankTwo_elementary hA with ⟨hcard, hElem⟩
  have : IsElementaryAbelian p.val A := hElem
  have hgen : 2 ≤ generatorRank A :=
    section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
      (p := p.val) hcard
  have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
  have hAcomm : IsMulCommutative A := inferInstance
  exact section12_groupRank_at_least_two_of_generatorRank_subgroup_pre
    (G := G) (q := p.val) p.2 (A := A) (K := A) le_rfl hAp hAcomm hgen

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_generatorRank_at_least_three_of_elementaryAbelian_card_gt_p_sq_pre
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hgt : p ^ 2 < Nat.card A) :
    3 ≤ generatorRank A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by
          simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  have hnot_le_two : ¬ Group.rank A ≤ 2 := by
    intro hle_two
    have hcard_le : Nat.card A ≤ p ^ Group.rank A :=
      Nat.le_of_dvd (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _) hcard_dvd
    have hpow_le : p ^ Group.rank A ≤ p ^ 2 :=
      Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hle_two
    exact (not_lt_of_ge (hcard_le.trans hpow_le)) hgt
  have hle_rank : 3 ≤ Group.rank A := by omega
  simpa [generatorRank_eq_group_rank] using hle_rank

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_primeOrder_ne_bot
    {A X : Subgroup G} {p : Nat.Primes}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A) :
    X ≠ ⊥ := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨_hXA, hXcard⟩
  intro hbot
  have hcard_bot : Nat.card X = 1 := (Subgroup.card_eq_one (H := X)).2 hbot
  have hp_eq_one : p.val = 1 := by
    rw [← hXcard, hcard_bot]
  exact (ne_of_gt p.2.one_lt) hp_eq_one

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_ne_bot
    {H A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p H) :
    A ≠ ⊥ := by
  rcases section12_rankTwo_elementary hA with ⟨hcard, _hElem⟩
  intro hbot
  have hcard_bot : Nat.card A = 1 := (Subgroup.card_eq_one (H := A)).2 hbot
  have hp_sq_eq_one : p.val ^ 2 = 1 := by
    rw [← hcard, hcard_bot]
  have hp_le_sq : p.val ≤ p.val ^ 2 :=
    le_self_pow p.2.one_lt.le (by decide : 2 ≠ 0)
  exact (ne_of_gt (p.2.one_lt.trans_le hp_le_sq)) hp_sq_eq_one

public theorem CFSG.section12_primeOrder_ne_top_pre
    {A X : Subgroup G} {p : Nat.Primes}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A) :
    X ≠ ⊤ := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨_hXA, hXcard⟩
  intro htop
  have hGcard : Nat.card G = p.val := by
    simpa [htop] using hXcard
  have : Fact p.val.Prime := ⟨p.2⟩
  have : IsCyclic G := by
    exact isCyclic_of_prime_card (α := G) (p := p.val) hGcard
  have hsolv : Group.IsSolvable G := by infer_instance
  exact IsMinCE.not_solvable (G := G) hsolv

public theorem CFSG.section12_normalizer_ne_top_of_ne_bot_ne_top_pre
    {Q : Subgroup G} (hQ_ne_bot : Q ≠ ⊥) (hQ_ne_top : Q ≠ ⊤) :
    Subgroup.normalizer (Q : Set G) ≠ ⊤ := by
  intro hNtop
  have hQnormal : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  let : IsSimpleGroup G := IsMinCE.simple
  rcases hQnormal.eq_bot_or_eq_top with hQbot | hQtop
  · exact hQ_ne_bot hQbot
  · exact hQ_ne_top hQtop

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_le_normalizer_of_primeOrder_pre
    {A X : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A) :
    A ≤ Subgroup.normalizer (X : Set G) := by
  classical
  rcases hA with ⟨_hAcard, hAelem⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXA, _hXcard⟩
  have hAcomm : IsMulCommutative A := hAelem.toIsMulCommutative
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hxA : x ∈ A := hXA hx
    have hcomm : a * x = x * a :=
      setLike_mul_comm (s := A) ha hxA
    have hconj : a * x * a⁻¹ = x := by
      calc
        a * x * a⁻¹ = x * a * a⁻¹ := by rw [hcomm]
        _ = x := by simp [mul_assoc]
    simpa [hconj] using hx
  · intro hx
    have hyA : a * x * a⁻¹ ∈ A := hXA hx
    have hainv : a⁻¹ ∈ A := A.inv_mem ha
    have hcomm : a⁻¹ * (a * x * a⁻¹) = (a * x * a⁻¹) * a⁻¹ :=
      setLike_mul_comm (s := A) hainv hyA
    have hpre : a⁻¹ * (a * x * a⁻¹) * a = a * x * a⁻¹ := by
      calc
        a⁻¹ * (a * x * a⁻¹) * a = (a * x * a⁻¹) * a⁻¹ * a := by rw [hcomm]
        _ = a * x * a⁻¹ := by simp [mul_assoc]
    have hx_eq : x = a * x * a⁻¹ := by
      calc
        x = a⁻¹ * (a * x * a⁻¹) * a := by simp [mul_assoc]
        _ = a * x * a⁻¹ := hpre
    simpa [← hx_eq] using hx

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_le_centralizer_of_primeOrder_pre
    {A X : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A) :
    A ≤ Subgroup.centralizer (X : Set G) := by
  rcases hA with ⟨_hAcard, hAelem⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXA, _hXcard⟩
  have hAcomm : IsMulCommutative A := hAelem.toIsMulCommutative
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact setLike_mul_comm (s := A) (hXA hx) ha

public theorem CFSG.section12_exists_alternate_normalizer_overgroup_pre
    {M A X : Subgroup G} {p : Nat.Primes}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A)
    (hnotUnique :
      section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {M}) :
    ∃ Mstar : Subgroup G,
      Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ∧
        Mstar ≠ M := by
  classical
  have hNproper : Subgroup.normalizer (X : Set G) ≠ ⊤ :=
    section12_normalizer_ne_top_of_ne_bot_ne_top_pre
      (section12_primeOrder_ne_bot hX) (section12_primeOrder_ne_top_pre hX)
  obtain ⟨N, hN⟩ :=
    section12_exists_maximalSubgroupsContaining_of_ne_top_pre (G := G) hNproper
  by_contra hnone
  have hforall :
      ∀ L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) → L = M := by
    intro L hL
    by_contra hLM
    exact hnone ⟨L, hL, hLM⟩
  apply hnotUnique
  ext L
  constructor
  · intro hL
    have hLM : L = M := hforall L hL
    simp [hLM]
  · intro hL
    have hLM : L = M := by simpa using hL
    subst L
    have hNM : N = M := hforall N hN
    simpa [hNM] using hN

public theorem CFSG.section12_rank_centralizerIn_primeOrder_le_two_pre
    {M A X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A)
    (hnotUnique :
      section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {M}) :
    groupRank (subgroupCentralizerIn M X) ≤ 2 := by
  classical
  let C : Subgroup G := subgroupCentralizerIn M X
  by_contra hle
  have hleC : ¬ groupRank C ≤ 2 := by simpa [C] using hle
  have hC_rank3 : 3 ≤ groupRank C := by omega
  have hC_le_M : C ≤ M := by
    intro x hx
    exact hx.1
  have hCproper : C ≠ ⊤ := by
    intro hCtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [C, hCtop] using hC_le_M
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hAelem : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G :=
    section12_rankTwo_elementary hA
  rcases hAelem with ⟨hAcard, hAelem'⟩
  have : Fact p.val.Prime := ⟨p.2⟩
  have : IsElementaryAbelian p.val A := hAelem'
  have hA_le_C : A ≤ C := by
    intro a ha
    refine ⟨section12_rankTwo_le hA ha, ?_⟩
    exact section12_rankTwo_le_centralizer_of_primeOrder_pre
      (p := p) ⟨hAcard, hAelem'⟩ hX ha
  have hAgen : 2 ≤ generatorRank A :=
    section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
      (p := p.val) hAcard
  have hC_rank2 : 2 ≤ groupRank C :=
    section12_groupRank_at_least_two_of_generatorRank_subgroup_pre
      (G := G) (q := p.val) p.2 (A := A) (K := C) hA_le_C
      (IsElementaryAbelian.isPGroup p.val A) inferInstance hAgen
  have hCunique : C ∈ section9UniqueSubgroups G :=
    theorem_9_6 (G := G) (K := C) hCproper hC_rank2 (Or.inl hC_rank3)
  have hCuniqM : section9MaximalSubgroupsContaining C = {M} :=
    section12_unique_overgroups_eq_of_contains_maximal_pre hCunique hM hC_le_M
  have hC_le_normX : C ≤ Subgroup.normalizer (X : Set G) := by
    exact (show C ≤ Subgroup.centralizer (X : Set G) from fun x hx => hx.2).trans
      (centralizer_le_normalizer X)
  have hNproper : Subgroup.normalizer (X : Set G) ≠ ⊤ :=
    section12_normalizer_ne_top_of_ne_bot_ne_top_pre
      (section12_primeOrder_ne_bot hX) (section12_primeOrder_ne_top_pre hX)
  have hNormX_le_M : Subgroup.normalizer (X : Set G) ≤ M :=
    section12_le_unique_maximal_of_le_pre hC_le_normX hNproper hCuniqM
  have hNormX_single :
      section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) = {M} := by
    ext L
    constructor
    · intro hL
      have hCL : C ≤ L := hC_le_normX.trans hL.2
      have hLmem : L ∈ section9MaximalSubgroupsContaining C := ⟨hL.1, hCL⟩
      have hLM : L = M := by
        have hsingle : L ∈ ({M} : Set (Subgroup G)) := by
          simpa [hCuniqM] using hLmem
        simpa using hsingle
      simp [hLM]
    · intro hL
      have hLM : L = M := by simpa using hL
      subst L
      exact ⟨hM, hNormX_le_M⟩
  exact hnotUnique hNormX_single

omit [IsMinCE G] in
public theorem CFSG.section12_exists_primeOrderSubgroupIn_rankTwo_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    ∃ X : Subgroup G, X ∈ section10PrimeOrderSubgroupsIn p A := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  rcases section12_rankTwo_elementary hA with ⟨hAcard, _hAelem⟩
  have hp_dvd_A : p.val ∣ Nat.card A := by
    rw [hAcard]
    exact dvd_pow_self p.val (by decide : 2 ≠ 0)
  obtain ⟨a, ha_order⟩ := exists_prime_orderOf_dvd_card' (G := A) p.val hp_dvd_A
  let X : Subgroup G := Subgroup.zpowers (a : G)
  have hX_le_A : X ≤ A := by
    dsimp [X]
    exact Subgroup.zpowers_le.2 a.2
  have hX_card : Nat.card X = p.val := by
    dsimp [X]
    rw [Nat.card_zpowers]
    simpa [Subgroup.orderOf_coe] using ha_order
  exact ⟨X, by simpa [section10PrimeOrderSubgroupsIn] using ⟨hX_le_A, hX_card⟩⟩

public theorem CFSG.section12_rank_centralizerIn_rankTwo_le_two_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hnotUnique :
      ∀ X : Subgroup G, X ∈ section10PrimeOrderSubgroupsIn p A →
        section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {M}) :
    groupRank (subgroupCentralizerIn M A) ≤ 2 := by
  classical
  obtain ⟨X, hX⟩ := section12_exists_primeOrderSubgroupIn_rankTwo_pre (G := G) hA
  have hCA_le_CX : subgroupCentralizerIn M A ≤ subgroupCentralizerIn M X := by
    intro g hg
    rcases (by simpa [subgroupCentralizerIn] using hg) with ⟨hgM, hgC⟩
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXA, _hXcard⟩
    refine ⟨hgM, ?_⟩
    exact (Subgroup.centralizer_le (show (X : Set G) ⊆ (A : Set G) from hXA)) hgC
  let Csub : Subgroup (subgroupCentralizerIn M X) :=
    (subgroupCentralizerIn M A).subgroupOf (subgroupCentralizerIn M X)
  have hCsub_eqv : Csub ≃* subgroupCentralizerIn M A :=
    Subgroup.subgroupOfEquivOfLe hCA_le_CX
  have hC_rank_le_sub : groupRank (subgroupCentralizerIn M A) ≤ groupRank Csub :=
    section12_groupRank_le_of_equiv hCsub_eqv
  exact hC_rank_le_sub.trans
    ((section8_groupRank_le_of_subgroup Csub).trans
      (section12_rank_centralizerIn_primeOrder_le_two_pre hM hA hX (hnotUnique X hX)))

public theorem CFSG.section12_primeRank_le_groupRank_of_normal_hall_pre
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    {H : Subgroup R} [H.Normal] (hHall : IsHallSubgroup π H)
    {p : Nat.Primes} (hpπ : p ∈ π) :
    primeRank p.val R ≤ groupRank H := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := p.val) (G := R), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨B, hBp, hBcomm, hnB⟩
    have hB_le_H : B ≤ H :=
      section12_pSubgroup_le_normal_hall_of_prime_mem hHall hpπ hBp
    exact hnB.trans <|
      section12_generatorRank_le_groupRank_of_subgroup_pre
        (G := R) (q := p.val) p.2 hB_le_H hBp hBcomm


public theorem CFSG.section12_primeRank_le_primeRank_of_normal_hall_ambient_pre
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {p : Nat.Primes} (hpσ : p ∈ section10SigmaPrimes M) :
    primeRank p.val M ≤ primeRank p.val (section10Msigma M) := by
  classical
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := p.val) (G := M), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨B, hBp, hBcomm, hnB⟩
    have hB_le_sigmaSub : B ≤ section10MsigmaSubgroup M :=
      section12_pSubgroup_le_normal_hall_of_prime_mem
        (H := section10MsigmaSubgroup M) (A := B)
        (theorem_10_2_b (M := M) hM).2 hpσ hBp
    let Bamb : Subgroup G := B.map M.subtype
    have hBamb_le_sigma : Bamb ≤ section10Msigma M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨b, hbB, rfl⟩
      exact Subgroup.mem_map.mpr ⟨b, hB_le_sigmaSub hbB, rfl⟩
    let Bσ : Subgroup (section10Msigma M) := Bamb.subgroupOf (section10Msigma M)
    have hBσ_p : IsPGroup p.val Bσ := by
      let eBamb : B ≃* Bamb :=
        Subgroup.equivMapOfInjective (f := M.subtype) B M.subtype_injective
      let eBσ : Bσ ≃* Bamb := Subgroup.subgroupOfEquivOfLe hBamb_le_sigma
      exact hBp.of_equiv (eBamb.trans eBσ.symm)
    have hBσ_comm : IsMulCommutative Bσ := by
      let : IsMulCommutative B := hBcomm
      let eBamb : B ≃* Bamb :=
        Subgroup.equivMapOfInjective (f := M.subtype) B M.subtype_injective
      let eBσ : Bσ ≃* Bamb := Subgroup.subgroupOfEquivOfLe hBamb_le_sigma
      let e : B ≃* Bσ := eBamb.trans eBσ.symm
      exact
        { is_comm := ⟨fun x y => by
            have hcomm :
                e.symm x * e.symm y = e.symm y * e.symm x :=
              (IsMulCommutative.is_comm (M := B)).comm (e.symm x) (e.symm y)
            simpa using congrArg e hcomm⟩ }
    have hgen_le : generatorRank B ≤ generatorRank Bσ := by
      let eBamb : B ≃* Bamb :=
        Subgroup.equivMapOfInjective (f := M.subtype) B M.subtype_injective
      let eBσ : Bσ ≃* Bamb := Subgroup.subgroupOfEquivOfLe hBamb_le_sigma
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      exact (Group.rank_congr (eBamb.trans eBσ.symm)).le
    have hmem :
        generatorRank B ∈
          {m : ℕ | ∃ A : Subgroup (section10Msigma M),
            IsPGroup p.val A ∧ IsMulCommutative A ∧ m ≤ generatorRank A} :=
      ⟨Bσ, hBσ_p, hBσ_comm, hgen_le⟩
    exact hnB.trans <| by
      refine le_csSup ?_ hmem
      refine ⟨Nat.card (section10Msigma M), ?_⟩
      intro m hm
      rcases hm with ⟨A, _hAp, _hAcomm, hmA⟩
      exact hmA.trans <|
        (section8_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)

omit [IsMinCE G] in
public theorem CFSG.section12_primeRank_le_groupRank_sylow_pre
    {p : Nat.Primes} (S : Sylow p.val G) :
    primeRank p.val G ≤ groupRank (S : Subgroup G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := p.val) (G := G), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, hAp, hAcomm, hnA⟩
    obtain ⟨Q, hAQ⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hAp
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
    let Aconj : Subgroup G := A.map (MulAut.conj g).toMonoidHom
    have hAconj_le_S : Aconj ≤ (S : Subgroup G) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨a, haA, rfl⟩
      have haQ : a ∈ (Q : Subgroup G) := hAQ haA
      have hmem : (MulAut.conj g) a ∈ ((g • Q : Sylow p.val G) : Subgroup G) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) (Q : Subgroup G) haQ
      simpa [hg] using hmem
    have hAconj_p : IsPGroup p.val Aconj := by
      exact hAp.of_equiv
        (Subgroup.equivMapOfInjective (f := (MulAut.conj g).toMonoidHom) A
          (EquivLike.injective (MulAut.conj g)))
    have hAconj_comm : IsMulCommutative Aconj := by
      let : IsMulCommutative A := hAcomm
      simpa [Aconj] using
        (Subgroup.map_isMulCommutative (f := (MulAut.conj g).toMonoidHom) (H := A))
    have hgen_eq : generatorRank A = generatorRank Aconj := by
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      exact Group.rank_congr
        (Subgroup.equivMapOfInjective (f := (MulAut.conj g).toMonoidHom) A
          (EquivLike.injective (MulAut.conj g)))
    exact hnA.trans <| by
      rw [hgen_eq]
      exact section12_generatorRank_le_groupRank_of_subgroup_pre
        (G := G) (q := p.val) p.property hAconj_le_S hAconj_p hAconj_comm

public theorem CFSG.section12_primeRank_le_groupRank_msigma_sylow_ambient_pre
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {p : Nat.Primes} (hpσ : p ∈ section10SigmaPrimes M)
    (P : Sylow p.val (section10Msigma M)) :
    primeRank p.val M ≤
      groupRank (section10AmbientSylowSubgroup (section10Msigma M) P) := by
  classical
  have h1 : primeRank p.val M ≤ primeRank p.val (section10Msigma M) :=
    section12_primeRank_le_primeRank_of_normal_hall_ambient_pre hM hpσ
  have h2 : primeRank p.val (section10Msigma M) ≤ groupRank (P : Subgroup (section10Msigma M)) :=
    section12_primeRank_le_groupRank_sylow_pre (G := section10Msigma M) P
  let e : (P : Subgroup (section10Msigma M)) ≃*
      section10AmbientSylowSubgroup (section10Msigma M) P :=
    Subgroup.equivMapOfInjective (f := (section10Msigma M).subtype)
      (P : Subgroup (section10Msigma M)) (section10Msigma M).subtype_injective
  have h3 :
      groupRank (P : Subgroup (section10Msigma M)) ≤
        groupRank (section10AmbientSylowSubgroup (section10Msigma M) P) :=
    section12_groupRank_le_of_equiv e.symm
  exact h1.trans (h2.trans h3)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_isElementaryAbelian_sup_of_le_centralizer_pre
    {p : ℕ} [Fact p.Prime] {E C : Subgroup G}
    [IsElementaryAbelian p E] [IsElementaryAbelian p C]
    (hCE : C ≤ Subgroup.centralizer (E : Set G)) :
    IsElementaryAbelian p ↥(E ⊔ C : Subgroup G) := by
  classical
  let s : Set G := (E : Set G) ∪ (C : Set G)
  have hcomm_s : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    rcases hx with hxE | hxC
    · rcases hy with hyE | hyC
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := E)).comm ⟨x, hxE⟩ ⟨y, hyE⟩)
      · exact (Subgroup.mem_centralizer_iff.mp (hCE hyC)) x hxE
    · rcases hy with hyE | hyC
      · exact ((Subgroup.mem_centralizer_iff.mp (hCE hxC)) y hyE).symm
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := C)).comm ⟨x, hxC⟩ ⟨y, hyC⟩)
  have hsup : E ⊔ C = Subgroup.closure s := by
    simpa [s] using (Subgroup.sup_eq_closure E C)
  refine
    { toIsMulCommutative := by
        rw [hsup]
        exact Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm_s x hx y hy
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  have hxcl : (x : G) ∈ Subgroup.closure s := by
    simpa [hsup] using x.property
  exact
    Subgroup.closure_induction (k := s)
      (p := fun z _hz => z ^ p = 1) (x := (x : G)) (by
        intro y hy
        rcases hy with hyE | hyC
        · have hypow : (⟨y, hyE⟩ : E) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p E) ⟨y, hyE⟩
          simpa using congrArg Subtype.val hypow
        · have hypow : (⟨y, hyC⟩ : C) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p C) ⟨y, hyC⟩
          simpa using congrArg Subtype.val hypow) (by simp) (by
        intro y z hy hz hypow hzpow
        have hyz_comm : Commute y z := by
          have hclosure_comm : IsMulCommutative ↥(Subgroup.closure s) :=
            Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm_s x hx y hy
          show y * z = z * y
          simpa using congrArg Subtype.val
            (hclosure_comm.is_comm.comm
              (⟨y, hy⟩ : Subgroup.closure s) (⟨z, hz⟩ : Subgroup.closure s))
        calc
          (y * z) ^ p = y ^ p * z ^ p := by simpa using hyz_comm.mul_pow p
          _ = 1 := by simp [hypow, hzpow]) (by
        intro y _hy hypow
        simpa [inv_pow] using congrArg Inv.inv hypow) hxcl

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_omega1_isElementaryAbelian_of_commutative
    {p : ℕ} [Fact p.Prime] (R : Type*) [Group R] [IsMulCommutative R] :
    IsElementaryAbelian p (omega₁ (G := R) (p := p)) := by
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  exact
    Subgroup.closure_induction (k := {y : R | y ^ (p ^ 1) = 1})
      (p := fun z _hz => z ^ p = 1) (x := x) (by
        intro y hy
        simpa [pow_one] using hy) (by simp) (by
        intro y z _ _ hy hz
        have hyz : Commute y z :=
          (commute_iff_eq y z).2
            ((IsMulCommutative.is_comm (M := R)).comm y z)
        calc
          (y * z) ^ p = y ^ p * z ^ p := hyz.mul_pow p
          _ = 1 := by simp [hy, hz]) (by
        intro y _ hy
        simp [hy]) x.property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_omega1Z_isElementaryAbelian_pre
    {p : ℕ} [Fact p.Prime] (R : Type*) [Group R] :
    IsElementaryAbelian p (Ω₁Z p R) := by
  change IsElementaryAbelian p
    ((omega₁ (G := Subgroup.center R) (p := p)).map
      (Subgroup.center R).subtype)
  let Ωc : Subgroup (Subgroup.center R) := omega₁ (G := Subgroup.center R) (p := p)
  have hΩcelem : IsElementaryAbelian p Ωc := by
    let : IsMulCommutative (Subgroup.center R) := inferInstance
    simpa [Ωc] using section12_omega1_isElementaryAbelian_of_commutative
      (p := p) (Subgroup.center R)
  let : IsElementaryAbelian p Ωc := hΩcelem
  exact section12_isElementaryAbelian_map
    (p := p) (A := Ωc) (Subgroup.center R).subtype

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_omegaOneCenter_isElementaryAbelian_pre
    {p : Nat.Primes} (P : Subgroup G) :
    IsElementaryAbelian p.val (section10OmegaOneCenter p P) := by
  change IsElementaryAbelian p.val ((Ω₁Z p.val P).map P.subtype)
  have : Fact p.val.Prime := ⟨p.2⟩
  have hZelem : IsElementaryAbelian p.val (Ω₁Z p.val P) :=
    section12_omega1Z_isElementaryAbelian_pre (p := p.val) P
  let : IsElementaryAbelian p.val (Ω₁Z p.val P) := hZelem
  exact section12_isElementaryAbelian_map
    (p := p.val) (A := Ω₁Z p.val P) P.subtype

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_omegaOneCenter_le_pre
    {p : Nat.Primes} (P : Subgroup G) :
    section10OmegaOneCenter p P ≤ P := by
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨y, _hy, rfl⟩
  exact y.property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_omegaOneCenter_centralizes_pre
    {p : Nat.Primes} (P : Subgroup G) :
    section10OmegaOneCenter p P ≤ Subgroup.centralizer (P : Set G) := by
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
  rcases Subgroup.mem_map.mp hy with ⟨c, _hc, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hxP
  simpa using congrArg Subtype.val ((Subgroup.mem_center_iff.mp c.property) ⟨x, hxP⟩)

omit [IsMinCE G] in
public theorem CFSG.section12_omegaOneCenter_ne_bot_of_nontrivial_pgroup_pre
    {p : Nat.Primes} {P : Subgroup G} (hPp : IsPGroup p.val P) (hPne : P ≠ ⊥) :
    section10OmegaOneCenter p P ≠ ⊥ := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  have hP_nontrivial : Nontrivial P := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    let : Subsingleton P := hsub
    apply hPne
    ext x
    constructor
    · intro hx
      have hx1 : (⟨x, hx⟩ : P) = 1 := Subsingleton.elim _ _
      simpa using congrArg Subtype.val hx1
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact P.one_mem
  have hcenter_nontrivial : Nontrivial (Subgroup.center P) := hPp.center_nontrivial
  have hcenter_p : IsPGroup p.val (Subgroup.center P) :=
    hPp.to_subgroup (Subgroup.center P)
  have hpdvd_center : p.val ∣ Nat.card (Subgroup.center P) := by
    rcases (IsPGroup.nontrivial_iff_card (p := p.val) (G := Subgroup.center P)
        (hG := hcenter_p)).1 hcenter_nontrivial with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self p.val (Nat.pos_iff_ne_zero.mp hn)
  have hZne : Ω₁Z p.val P ≠ ⊥ := by
    simpa [Ω₁Z] using
      omega₁_map_subtype_ne_bot (M := Subgroup.center P) (p := p.val) hpdvd_center
  intro hmap_bot
  apply hZne
  ext z
  constructor
  · intro hz
    have hzmap : ((z : P) : G) ∈ section10OmegaOneCenter p P :=
      Subgroup.mem_map_of_mem P.subtype hz
    have hzG_one : ((z : P) : G) = 1 := by
      simpa [hmap_bot] using hzmap
    have hz_one : z = 1 := Subtype.ext hzG_one
    simp [hz_one]
  · intro hz
    rw [Subgroup.mem_bot] at hz
    rw [hz]
    exact (Ω₁Z p.val P).one_mem

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_omega1Z_characteristic_pre
    (p : ℕ) (R : Type*) [Group R] :
    (Ω₁Z p R).Characteristic := by
  classical
  rw [Subgroup.characteristic_iff_map_le]
  intro φ x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hyΩZ, rfl⟩
  rcases Subgroup.mem_map.mp hyΩZ with ⟨z, hzΩ, rfl⟩
  have hcenter_map :
      ∀ (ψ : R ≃* R) (z : Subgroup.center R),
        ψ (z : R) ∈ Subgroup.center R := by
    intro ψ z
    rw [Subgroup.mem_center_iff]
    intro r
    have hzcomm := Subgroup.mem_center_iff.mp z.property (ψ.symm r)
    calc
      r * ψ (z : R) = ψ (ψ.symm r) * ψ (z : R) := by simp
      _ = ψ (ψ.symm r * (z : R)) := by simp
      _ = ψ ((z : R) * ψ.symm r) := by rw [hzcomm]
      _ = ψ (z : R) * r := by simp
  let φc : Subgroup.center R ≃* Subgroup.center R :=
    { toFun := fun z => ⟨φ (z : R), hcenter_map φ z⟩
      invFun := fun z => ⟨φ.symm (z : R), hcenter_map φ.symm z⟩
      left_inv := fun z => Subtype.ext (by simp)
      right_inv := fun z => Subtype.ext (by simp)
      map_mul' := fun z w => Subtype.ext (by simp) }
  have hΩchar : (omega₁ (G := Subgroup.center R) (p := p)).Characteristic :=
    omega₁_characteristic (G := Subgroup.center R) (p := p)
  have hφcz :
      φc z ∈ omega₁ (G := Subgroup.center R) (p := p) := by
    exact (Subgroup.characteristic_iff_map_le.mp hΩchar φc)
      (Subgroup.mem_map_of_mem φc.toMonoidHom hzΩ)
  exact Subgroup.mem_map.mpr ⟨φc z, hφcz, rfl⟩

omit [IsMinCE G] in
public theorem CFSG.section12_omegaOneCenter_le_rankTwo_of_rank_centralizer_pre
    {M A P : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hPM : P ≤ M) (hAP : A ≤ P)
    (hRankCMA : groupRank (subgroupCentralizerIn M A) ≤ 2) :
    section10OmegaOneCenter p P ≤ A := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  let Z : Subgroup G := section10OmegaOneCenter p P
  have hAelem_pack : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G :=
    section12_rankTwo_elementary hA
  rcases hAelem_pack with ⟨hAcard, hAelem⟩
  have : IsElementaryAbelian p.val A := hAelem
  have hZelem : IsElementaryAbelian p.val Z := by
    simpa [Z] using section12_omegaOneCenter_isElementaryAbelian_pre (p := p) P
  let : IsElementaryAbelian p.val Z := hZelem
  have hZ_cent_A : Z ≤ Subgroup.centralizer (A : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp
      (section12_omegaOneCenter_centralizes_pre (p := p) P hz)) a (hAP ha)
  have hA_cent_A : A ≤ Subgroup.centralizer (A : Set G) := by
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2
      (inferInstance : IsMulCommutative A)
  have hZ_le_M : Z ≤ M := (section12_omegaOneCenter_le_pre (p := p) P).trans hPM
  have hAZ_le_CMA : A ⊔ Z ≤ subgroupCentralizerIn M A := by
    refine sup_le ?_ ?_
    · intro a ha
      exact ⟨section12_rankTwo_le hA ha, hA_cent_A ha⟩
    · intro z hz
      exact ⟨hZ_le_M hz, hZ_cent_A hz⟩
  by_contra hZ_not_le_A
  have hA_lt_AZ : A < A ⊔ Z := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro hEq
    apply hZ_not_le_A
    intro z hz
    have hzsup : z ∈ A ⊔ Z := Subgroup.mem_sup_right hz
    simpa [← hEq] using hzsup
  have hcard_gt : p.val ^ 2 < Nat.card (A ⊔ Z : Subgroup G) := by
    simpa [hAcard] using natCard_lt_of_subgroup_lt hA_lt_AZ
  have hAZelem : IsElementaryAbelian p.val (A ⊔ Z : Subgroup G) :=
    section12_isElementaryAbelian_sup_of_le_centralizer_pre (p := p.val)
      (E := A) (C := Z) hZ_cent_A
  let : IsElementaryAbelian p.val (A ⊔ Z : Subgroup G) := hAZelem
  have hAZgen : 3 ≤ generatorRank (A ⊔ Z : Subgroup G) :=
    section12_generatorRank_at_least_three_of_elementaryAbelian_card_gt_p_sq_pre
      (p := p.val) hcard_gt
  have hAZp : IsPGroup p.val (A ⊔ Z : Subgroup G) :=
    IsElementaryAbelian.isPGroup p.val (A ⊔ Z : Subgroup G)
  have hAZcomm : IsMulCommutative (A ⊔ Z : Subgroup G) := inferInstance
  have hRank_ge_three : 3 ≤ groupRank (subgroupCentralizerIn M A) :=
    groupRank_at_least_three_of_generatorRank_subgroup
      (q := p.val) p.2 hAZ_le_CMA hAZp hAZcomm hAZgen
  omega

public theorem CFSG.section12_exists_msigma_sylow_with_rankTwo_omega_le_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∈ section10SigmaPrimes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hnotUnique :
      ∀ X : Subgroup G, X ∈ section10PrimeOrderSubgroupsIn p A →
        section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {M}) :
    ∃ P : Sylow p.val (section10Msigma M),
      A ≤ section10AmbientSylowSubgroup (section10Msigma M) P ∧
        section10AmbientSylowSubgroup (section10Msigma M) P ≤ M ∧
          section10OmegaOneCenter p
            (section10AmbientSylowSubgroup (section10Msigma M) P) ≤ A := by
  classical
  let σ : Subgroup G := section10Msigma M
  have hAσ : A ≤ σ :=
    section12_rankTwo_le_msigma_of_sigma hM hpσ hA
  have hAsub_p : IsPGroup p.val (A.subgroupOf σ) := by
    have hAp : IsPGroup p.val A := by
      rcases section12_rankTwo_elementary hA with ⟨_hcard, hElem⟩
      have : IsElementaryAbelian p.val A := hElem
      exact IsElementaryAbelian.isPGroup p.val A
    exact hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAσ).symm
  obtain ⟨P, hA_le_P⟩ := IsPGroup.exists_le_sylow
    (G := σ) (p := p.val) hAsub_p
  let Pamb : Subgroup G := section10AmbientSylowSubgroup σ P
  have hA_le_Pamb : A ≤ Pamb := by
    intro x hxA
    have hxsub : (⟨x, hAσ hxA⟩ : σ) ∈ A.subgroupOf σ := by
      simpa [Subgroup.mem_subgroupOf] using hxA
    exact Subgroup.mem_map.mpr ⟨⟨x, hAσ hxA⟩, hA_le_P hxsub, rfl⟩
  have hPamb_le_σ : Pamb ≤ σ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hσM : σ ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hPambM : Pamb ≤ M := hPamb_le_σ.trans hσM
  have hRankCMA : groupRank (subgroupCentralizerIn M A) ≤ 2 :=
    section12_rank_centralizerIn_rankTwo_le_two_pre hM hA hnotUnique
  have hZleA : section10OmegaOneCenter p Pamb ≤ A :=
    section12_omegaOneCenter_le_rankTwo_of_rank_centralizer_pre
      (M := M) (A := A) (P := Pamb) (p := p) hA hPambM hA_le_Pamb hRankCMA
  exact ⟨P, hA_le_Pamb, hPambM, hZleA⟩

omit [IsMinCE G] in
public theorem CFSG.section12_rankTwo_not_isCyclic_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    ¬ IsCyclic A := by
  have : Fact p.val.Prime := ⟨p.2⟩
  rcases section12_rankTwo_elementary hA with ⟨hcard, hElem⟩
  have : IsElementaryAbelian p.val A := hElem
  exact section12_not_isCyclic_of_two_le_generatorRank
    (section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
      (p := p.val) hcard)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_zpowers_mem_primeOrderSubgroupsIn_of_rankTwo_pre
    {M A : Subgroup G} {p : Nat.Primes} (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (a : A) (ha : a ≠ 1) :
    Subgroup.zpowers (a : G) ∈ section10PrimeOrderSubgroupsIn p A := by
  have : Fact p.val.Prime := ⟨p.2⟩
  rcases section12_rankTwo_elementary hA with ⟨_hcard, hElem⟩
  have : IsElementaryAbelian p.val A := hElem
  have hapow : a ^ p.val = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p.val A) a
  have ha_order : orderOf a = p.val := orderOf_eq_prime hapow ha
  have hz_le_A : Subgroup.zpowers (a : G) ≤ A := Subgroup.zpowers_le.2 a.2
  have hz_card : Nat.card (Subgroup.zpowers (a : G)) = p.val := by
    rw [Nat.card_zpowers]
    simpa [Subgroup.orderOf_coe] using ha_order
  exact (by
    simpa [section10PrimeOrderSubgroupsIn] using
      (And.intro hz_le_A hz_card))

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_coprime_card_of_pPrime_pre
    {M A K : Subgroup G} {p : Nat.Primes}
    (_hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hKp' : IsPiSubgroup (G := G) (section10PPrimeSet p) K) :
    Nat.Coprime p.val (Nat.card K) := by
  refine Nat.coprime_of_dvd ?_
  intro q hqPrime hqp hqK
  have hq_eq_p : q = p.val := by
    exact ((p.2.dvd_iff_eq hqPrime.ne_one).1 hqp).symm
  let q' : Nat.Primes := ⟨q, hqPrime⟩
  have hq'_not_p : q' ∉ ({p} : Set Nat.Primes) := by
    simpa [section10PPrimeSet] using hKp' q' hqK
  have hq'_eq_p : q' = p := Subtype.ext hq_eq_p
  exact hq'_not_p (by simp [hq'_eq_p])

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_centralizer_singleton_le_centralizer_zpowers_pre
    (a : G) :
    Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
  have hcomm : Commute a x :=
    (Subgroup.mem_centralizer_singleton_iff.mp hx).symm
  simpa using (hcomm.zpow_left n).eq

omit [IsMinCE G] in
public theorem CFSG.section12_prop116_subgroup_le_centralizer_pre
    {M A K : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hAKnorm : A ≤ Subgroup.normalizer (K : Set G))
    (hKp' : IsPiSubgroup (G := G) (section10PPrimeSet p) K)
    (hcentral :
      ∀ X : Subgroup G, X ∈ section10PrimeOrderSubgroupsIn p A →
        ∃ Mstar : Subgroup G,
          Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ∧
            Mstar ≠ M ∧ A ≤ Subgroup.centralizer (K ⊓ Mstar : Set G)) :
    K ≤ Subgroup.centralizer (A : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  rcases section12_rankTwo_elementary hA with ⟨_hAcard, hAelem⟩
  have : IsElementaryAbelian p.val A := hAelem
  have : IsMulCommutative A := hAelem.toIsMulCommutative
  let : CommGroup A := IsMulCommutative.instCommGroup
  have : Fact (IsPGroup p.val A) := ⟨IsElementaryAbelian.isPGroup p.val A⟩
  have : Subgroup.Normalizes A K := ⟨hAKnorm⟩
  have hKcop : Nat.Coprime p.val (Nat.card K) :=
    section12_rankTwo_coprime_card_of_pPrime_pre (G := G) hA hKp'
  have hAnoncyc : ¬ IsCyclic A := section12_rankTwo_not_isCyclic_pre hA
  have hfix_top :
      (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥K) =
        ⊤ := by
    simpa using
      proposition_1_16_a (G := ↥K) (A := A) p.val hKcop hAnoncyc
  have hfixed_map_le :
      ∀ a : A, ∀ ha_ne : a ≠ 1,
        (fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥K).map K.subtype ≤
          Subgroup.centralizer (A : Set G) := by
    intro a ha_ne
    let X : Subgroup G := Subgroup.zpowers (a : G)
    have hX : X ∈ section10PrimeOrderSubgroupsIn p A := by
      simpa [X] using section12_zpowers_mem_primeOrderSubgroupsIn_of_rankTwo_pre hA a ha_ne
    obtain ⟨Mstar, hMstar, _hMstar_ne, hAcent⟩ := hcentral X hX
    have hfix_eq :
        fixedPointSubgroup (↥(Subgroup.zpowers a)) (↥K) =
          (elementCentralizerIn K (a : G)).subgroupOf K := by
      simpa using fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn
        K A hAKnorm a
    have hfix_map :
        (fixedPointSubgroup (↥(Subgroup.zpowers a)) (↥K)).map K.subtype =
          elementCentralizerIn K (a : G) := by
      calc
        (fixedPointSubgroup (↥(Subgroup.zpowers a)) (↥K)).map K.subtype =
            ((elementCentralizerIn K (a : G)).subgroupOf K).map K.subtype := by
              rw [hfix_eq]
        _ = elementCentralizerIn K (a : G) ⊓ K := by
              rw [Subgroup.subgroupOf_map_subtype]
        _ = elementCentralizerIn K (a : G) := inf_eq_left.2 inf_le_left
    rw [hfix_map]
    intro x hx
    rcases (by simpa [elementCentralizerIn] using hx) with ⟨hxK, hxCentA⟩
    have hxCentX : x ∈ Subgroup.centralizer (X : Set G) := by
      simpa [X] using
        section12_centralizer_singleton_le_centralizer_zpowers_pre (G := G) (a := (a : G)) hxCentA
    have hxMstar : x ∈ Mstar :=
      hMstar.2 ((centralizer_le_normalizer X) hxCentX)
    have hxKMstar : x ∈ K ⊓ Mstar := ⟨hxK, hxMstar⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hyA
    exact ((Subgroup.mem_centralizer_iff.mp (hAcent hyA)) x hxKMstar).symm
  have htop_map_K : (⊤ : Subgroup K).map K.subtype = K := by
    simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := K))
  calc
    K = (⊤ : Subgroup K).map K.subtype := htop_map_K.symm
    _ =
        (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥K).map
          K.subtype := by
          simp [hfix_top]
    _ ≤ Subgroup.centralizer (A : Set G) := by
          rw [Subgroup.map_iSup]
          refine iSup_le ?_
          intro a
          rw [Subgroup.map_iSup]
          refine iSup_le ?_
          intro ha_ne
          exact hfixed_map_le a ha_ne

public theorem CFSG.section12_msigma_le_centralizer_of_not_sigma_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∉ section10SigmaPrimes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hnotUnique :
      ∀ X : Subgroup G, X ∈ section10PrimeOrderSubgroupsIn p A →
        section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {M}) :
    section10Msigma M ≤ Subgroup.centralizer (A : Set G) := by
  classical
  refine section12_prop116_subgroup_le_centralizer_pre
    (M := M) (A := A) (K := section10Msigma M) (p := p) hA ?_ ?_ ?_
  · exact (section12_rankTwo_le hA).trans (by simpa using section12_le_normalizer_msigma (M := M))
  · exact section12_isPiSubgroup_pPrime_of_le_msigma_pre hM hpσ le_rfl
  · intro X hX
    obtain ⟨Mstar, hMstar, hMstar_ne⟩ :=
      section12_exists_alternate_normalizer_overgroup_pre
        (G := G) (M := M) (A := A) (X := X) hX (hnotUnique X hX)
    have hA_le_Mstar : A ≤ Mstar := by
      have hA_le_normX : A ≤ Subgroup.normalizer (X : Set G) :=
        section12_rankTwo_le_normalizer_of_primeOrder_pre (section12_rankTwo_elementary hA) hX
      exact hA_le_normX.trans hMstar.2
    have hAinf : A ∈ section12RankTwoElementaryAbelianIn p (M ⊓ Mstar) :=
      ⟨le_inf (section12_rankTwo_le hA) hA_le_Mstar, section12_rankTwo_elementary hA⟩
    exact ⟨Mstar, hMstar, hMstar_ne,
      lemma_12_3_a (G := G) (M := M) (Mstar := Mstar) (A := A) (A₀ := X)
        (p := p) hM hMstar.1 hMstar_ne hAinf hX hMstar.2 hpσ⟩

public theorem CFSG.section12_malpha_le_centralizer_of_sigma_not_alpha_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∈ section10SigmaPrimes M)
    (hpα : p ∉ section10AlphaPrimes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hnotUnique :
      ∀ X : Subgroup G, X ∈ section10PrimeOrderSubgroupsIn p A →
        section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {M}) :
    section10Malpha M ≤ Subgroup.centralizer (A : Set G) := by
  classical
  refine section12_prop116_subgroup_le_centralizer_pre
    (M := M) (A := A) (K := section10Malpha M) (p := p) hA ?_ ?_ ?_
  · exact (section12_rankTwo_le hA).trans (by simpa using section12_le_normalizer_malpha_pre (M := M))
  · exact section12_isPiSubgroup_pPrime_of_le_malpha_pre hM hpα le_rfl
  · intro X hX
    obtain ⟨Mstar, hMstar, hMstar_ne⟩ :=
      section12_exists_alternate_normalizer_overgroup_pre
        (G := G) (M := M) (A := A) (X := X) hX (hnotUnique X hX)
    have hA_le_Mstar : A ≤ Mstar := by
      have hA_le_normX : A ≤ Subgroup.normalizer (X : Set G) :=
        section12_rankTwo_le_normalizer_of_primeOrder_pre (section12_rankTwo_elementary hA) hX
      exact hA_le_normX.trans hMstar.2
    have hAinf : A ∈ section12RankTwoElementaryAbelianIn p (M ⊓ Mstar) :=
      ⟨le_inf (section12_rankTwo_le hA) hA_le_Mstar, section12_rankTwo_elementary hA⟩
    exact ⟨Mstar, hMstar, hMstar_ne,
      lemma_12_3_b (G := G) (M := M) (Mstar := Mstar) (A := A) (A₀ := X)
        (p := p) hM hMstar.1 hMstar_ne hAinf hX hMstar.2 hpσ hpα⟩

public theorem CFSG.section12_malpha_eq_bot_of_sigma_not_alpha_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∈ section10SigmaPrimes M)
    (hpα : p ∉ section10AlphaPrimes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hnotUnique :
      ∀ X : Subgroup G, X ∈ section10PrimeOrderSubgroupsIn p A →
        section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {M}) :
    section10Malpha M = ⊥ := by
  classical
  have hMalpha_le_centA :
      section10Malpha M ≤ Subgroup.centralizer (A : Set G) :=
    section12_malpha_le_centralizer_of_sigma_not_alpha_pre hM hpσ hpα hA hnotUnique
  have hMalpha_le_M : section10Malpha M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hMalpha_le_CMA : section10Malpha M ≤ subgroupCentralizerIn M A := by
    intro x hx
    exact ⟨hMalpha_le_M hx, hMalpha_le_centA hx⟩
  have hRankCMA : groupRank (subgroupCentralizerIn M A) ≤ 2 :=
    section12_rank_centralizerIn_rankTwo_le_two_pre hM hA hnotUnique
  let MalphaInC : Subgroup (subgroupCentralizerIn M A) :=
    (section10Malpha M).subgroupOf (subgroupCentralizerIn M A)
  let eC : MalphaInC ≃* section10Malpha M :=
    Subgroup.subgroupOfEquivOfLe hMalpha_le_CMA
  have hRankMalpha : groupRank (section10Malpha M) ≤ 2 :=
    (section12_groupRank_le_of_equiv eC).trans
      ((section8_groupRank_le_of_subgroup MalphaInC).trans hRankCMA)
  by_contra hMalpha_ne_bot
  have hcard_ne_one : Nat.card (section10Malpha M) ≠ 1 := by
    intro hcard
    exact hMalpha_ne_bot ((Subgroup.card_eq_one (H := section10Malpha M)).1 hcard)
  obtain ⟨q, hqPrime, hqdiv⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let q' : Nat.Primes := ⟨q, hqPrime⟩
  have hqα_mem : q' ∈ section10AlphaPrimes M :=
    (theorem_10_2_a (M := M) hM).1.p_in_pi_of_p_dvd_card q' hqdiv
  have hqRankGt : 2 < primeRank q'.val M := by
    rcases (by simpa [section10AlphaPrimes] using hqα_mem) with ⟨_hqM, hqRankGt⟩
    exact hqRankGt
  have hqRank_le_sub :
      primeRank q'.val M ≤ groupRank (section10MalphaSubgroup M) :=
    section12_primeRank_le_groupRank_of_normal_hall_pre
      (R := M) (H := section10MalphaSubgroup M)
      (theorem_10_2_a (M := M) hM).2 hqα_mem
  let e : section10MalphaSubgroup M ≃* section10Malpha M :=
    Subgroup.equivMapOfInjective (f := M.subtype)
      (section10MalphaSubgroup M) M.subtype_injective
  have hRankSub_le :
      groupRank (section10MalphaSubgroup M) ≤ groupRank (section10Malpha M) :=
    section12_groupRank_le_of_equiv e.symm
  have hqRank_le_two : primeRank q'.val M ≤ 2 :=
    hqRank_le_sub.trans (hRankSub_le.trans hRankMalpha)
  omega

public theorem CFSG.section12_msigma_nilpotent_of_malpha_eq_bot_pre
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hαbot : section10Malpha M = ⊥) :
    Group.IsNilpotent (section10Msigma M) := by
  classical
  have hαsub_bot : section10MalphaSubgroup M = ⊥ := by
    have hmap_bot : (section10MalphaSubgroup M).map M.subtype = (⊥ : Subgroup G) := by
      simpa [section10Malpha] using hαbot
    exact Subgroup.map_injective M.subtype_injective (by simpa using hmap_bot)
  rcases (theorem_10_2_d (M := M) hM).2 with ⟨hαD, hαDnorm, hDquot_nil⟩
  have : ((section10MalphaSubgroup M).subgroupOf (derivedSubgroup M)).Normal := by
    simpa using hαDnorm
  have hαsubD_bot :
      (section10MalphaSubgroup M).subgroupOf (derivedSubgroup M) = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxα : (x : M) ∈ section10MalphaSubgroup M := by
        exact Subgroup.mem_subgroupOf.mp hx
      have hxbot : (x : M) ∈ (⊥ : Subgroup M) := by
        simpa [hαsub_bot] using hxα
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxbot))
    · intro hx
      have hxone : x = 1 := Subgroup.mem_bot.mp hx
      rw [hxone]
      exact Subgroup.one_mem _
  have hD_nil : Group.IsNilpotent (derivedSubgroup M) := by
    let e :
        derivedSubgroup M ⧸ (section10MalphaSubgroup M).subgroupOf (derivedSubgroup M) ≃*
          derivedSubgroup M :=
      (QuotientGroup.quotientMulEquivOfEq hαsubD_bot).trans
        (QuotientGroup.quotientBot (G := derivedSubgroup M))
    exact Group.nilpotent_of_mulEquiv
      (G := derivedSubgroup M ⧸ (section10MalphaSubgroup M).subgroupOf (derivedSubgroup M))
      (G' := derivedSubgroup M) e
  have hσD : section10MsigmaSubgroup M ≤ derivedSubgroup M :=
    (theorem_10_2_c (M := M) hM).2
  have hσsub_nil :
      Group.IsNilpotent ((section10MsigmaSubgroup M).subgroupOf (derivedSubgroup M)) := by
    have : Group.IsNilpotent (derivedSubgroup M) := hD_nil
    infer_instance
  let eσD : (section10MsigmaSubgroup M).subgroupOf (derivedSubgroup M) ≃*
      section10MsigmaSubgroup M :=
    Subgroup.subgroupOfEquivOfLe hσD
  have hσlocal_nil : Group.IsNilpotent (section10MsigmaSubgroup M) :=
    Group.nilpotent_of_mulEquiv
      (G := (section10MsigmaSubgroup M).subgroupOf (derivedSubgroup M))
      (G' := section10MsigmaSubgroup M) eσD
  let eσ : section10MsigmaSubgroup M ≃* section10Msigma M :=
    Subgroup.equivMapOfInjective (f := M.subtype)
      (section10MsigmaSubgroup M) M.subtype_injective
  exact Group.nilpotent_of_mulEquiv
    (G := section10MsigmaSubgroup M) (G' := section10Msigma M) eσ

public theorem CFSG.section12_not_alpha_in_prop_12_4_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∈ section10SigmaPrimes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hnotUnique :
      ∀ X : Subgroup G, X ∈ section10PrimeOrderSubgroupsIn p A →
        section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {M}) :
    p ∉ section10AlphaPrimes M := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  by_contra hpα
  rcases (by simpa [section10AlphaPrimes] using hpα) with ⟨_hpM, hRankGt⟩
  obtain ⟨P, hA_le_P, hP_le_M, hZ_le_A⟩ :=
    section12_exists_msigma_sylow_with_rankTwo_omega_le_pre
      (M := M) (A := A) (p := p) hM hpσ hA hnotUnique
  let Pamb : Subgroup G := section10AmbientSylowSubgroup (section10Msigma M) P
  let Z : Subgroup G := section10OmegaOneCenter p Pamb
  have hZ_ne : Z ≠ ⊥ := by
    have hPamb_p : IsPGroup p.val Pamb := by
      exact P.isPGroup'.of_equiv
        (Subgroup.equivMapOfInjective (f := (section10Msigma M).subtype)
          (P : Subgroup (section10Msigma M)) (section10Msigma M).subtype_injective)
    have hPamb_ne : Pamb ≠ ⊥ := by
      intro hbot
      have hA_bot : A = ⊥ := by
        exact le_bot_iff.mp (hA_le_P.trans (by simpa [Pamb] using le_of_eq hbot))
      rcases section12_rankTwo_elementary hA with ⟨hAcard, _hAelem⟩
      have hcard_bot : Nat.card A = 1 := (Subgroup.card_eq_one (H := A)).2 hA_bot
      have hp2_ne_one : p.val ^ 2 ≠ 1 := by
        have hp_le_sq : p.val ≤ p.val ^ 2 := by
          exact le_self_pow p.2.one_lt.le (by decide : 2 ≠ 0)
        exact ne_of_gt (p.2.one_lt.trans_le hp_le_sq)
      exact hp2_ne_one (by simpa [hAcard] using hcard_bot)
    simpa [Z] using
      section12_omegaOneCenter_ne_bot_of_nontrivial_pgroup_pre
        (p := p) (P := Pamb) hPamb_p hPamb_ne
  have hZp : IsPGroup p.val Z := by
    have hZelem : IsElementaryAbelian p.val Z := by
      simpa [Z] using section12_omegaOneCenter_isElementaryAbelian_pre (p := p) Pamb
    exact IsElementaryAbelian.isPGroup p.val Z
  have hcard_ne_one : Nat.card Z ≠ 1 := by
    intro hcard
    exact hZ_ne ((Subgroup.card_eq_one (H := Z)).1 hcard)
  obtain ⟨z, hz_order⟩ := exists_prime_orderOf_dvd_card' (G := Z) p.val (by
    rcases hZp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    cases n with
    | zero =>
        have hcard_one : Nat.card Z = 1 := by simp [hn]
        exact False.elim (hcard_ne_one hcard_one)
    | succ n =>
        exact dvd_pow_self p.val (Nat.succ_ne_zero n))
  let X : Subgroup G := Subgroup.zpowers (z : G)
  have hX_le_Z : X ≤ Z := by
    dsimp [X]
    exact Subgroup.zpowers_le.2 z.2
  have hX_A : X ∈ section10PrimeOrderSubgroupsIn p A := by
    have hX_le_A : X ≤ A := hX_le_Z.trans (by simpa [Z] using hZ_le_A)
    have hX_card : Nat.card X = p.val := by
      dsimp [X]
      rw [Nat.card_zpowers]
      simpa [Subgroup.orderOf_coe] using hz_order
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hX_le_A, hX_card⟩
  have hP_le_CMX : Pamb ≤ subgroupCentralizerIn M X := by
    intro y hyP
    refine ⟨hP_le_M hyP, ?_⟩
    change y ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hxX
    have hxZ : x ∈ Z := hX_le_Z hxX
    exact ((Subgroup.mem_centralizer_iff.mp
      (section12_omegaOneCenter_centralizes_pre (p := p) Pamb hxZ)) y hyP).symm
  let PInC : Subgroup (subgroupCentralizerIn M X) :=
    Pamb.subgroupOf (subgroupCentralizerIn M X)
  let eC : PInC ≃* Pamb := Subgroup.subgroupOfEquivOfLe hP_le_CMX
  have hRankP_le_CMX : groupRank Pamb ≤ groupRank (subgroupCentralizerIn M X) :=
    (section12_groupRank_le_of_equiv eC).trans
      (section8_groupRank_le_of_subgroup PInC)
  have hRankP_le_two : groupRank Pamb ≤ 2 :=
    hRankP_le_CMX.trans
      (section12_rank_centralizerIn_primeOrder_le_two_pre hM hA hX_A (hnotUnique X hX_A))
  have hRankM_le_P : primeRank p.val M ≤ groupRank Pamb :=
    section12_primeRank_le_groupRank_msigma_sylow_ambient_pre hM hpσ P
  have hRankM_le_two : primeRank p.val M ≤ 2 := hRankM_le_P.trans hRankP_le_two
  omega

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_isPiSubgroup_sigma_compl_of_not_sigma_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hpσ : p ∉ section10SigmaPrimes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ A := by
  intro q hqA
  rcases section12_rankTwo_elementary hA with ⟨hAcard, _hAelem⟩
  have hq_dvd_p2 : q.val ∣ p.val ^ 2 := by
    simpa [hAcard] using hqA
  have hq_dvd_p : q.val ∣ p.val := q.2.dvd_of_dvd_pow hq_dvd_p2
  have hq_eq_p : q = p :=
    Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hq_dvd_p)
  rw [Set.mem_compl_iff]
  simpa [hq_eq_p] using hpσ

public theorem CFSG.section12_not_not_sigma_in_prop_12_4_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hnotUnique :
      ∀ X : Subgroup G, X ∈ section10PrimeOrderSubgroupsIn p A →
        section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {M}) :
    p ∈ section10SigmaPrimes M := by
  classical
  by_contra hpσ
  have hMsigma_le_centA :
      section10Msigma M ≤ Subgroup.centralizer (A : Set G) :=
    section12_msigma_le_centralizer_of_not_sigma_pre hM hpσ hA hnotUnique
  have hAσcompl : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ A :=
    section12_rankTwo_isPiSubgroup_sigma_compl_of_not_sigma_pre hpσ hA
  have hCent_eq : subgroupCentralizerIn A (section10Msigma M) = A := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hxA
      refine ⟨hxA, ?_⟩
      change x ∈ Subgroup.centralizer (section10Msigma M : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyσ
      exact (Subgroup.mem_centralizer_iff.mp (hMsigma_le_centA hyσ) x hxA).symm
  have hRank_le_one : groupRank A ≤ 1 := by
    rw [← hCent_eq]
    exact proposition_10_11_b (G := G) (M := M) (K := A)
      hM (section12_rankTwo_le hA) hAσcompl
  have hRank_ge_two : 2 ≤ groupRank A :=
    section12_groupRank_at_least_two_of_rankTwo_pre hA
  omega

public theorem CFSG.section12_prop_12_4_hard_branch_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hnotUnique :
      ∀ X : Subgroup G, X ∈ section10PrimeOrderSubgroupsIn p A →
        section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {M}) :
    Subgroup.centralizer (A : Set G) ≤ M := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  have hpσ : p ∈ section10SigmaPrimes M :=
    section12_not_not_sigma_in_prop_12_4_pre hM hA hnotUnique
  have hpα : p ∉ section10AlphaPrimes M :=
    section12_not_alpha_in_prop_12_4_pre hM hpσ hA hnotUnique
  have hαbot : section10Malpha M = ⊥ :=
    section12_malpha_eq_bot_of_sigma_not_alpha_pre hM hpσ hpα hA hnotUnique
  have hnil : Group.IsNilpotent (section10Msigma M) :=
    section12_msigma_nilpotent_of_malpha_eq_bot_pre hM hαbot
  obtain ⟨P, _hA_le_P, hP_le_M, hZ_le_A⟩ :=
    section12_exists_msigma_sylow_with_rankTwo_omega_le_pre
      (M := M) (A := A) (p := p) hM hpσ hA hnotUnique
  let Pamb : Subgroup G := section10AmbientSylowSubgroup (section10Msigma M) P
  let Z : Subgroup G := section10OmegaOneCenter p Pamb
  have hPamb_p : IsPGroup p.val Pamb := by
    exact P.isPGroup'.of_equiv
      (Subgroup.equivMapOfInjective (f := (section10Msigma M).subtype)
        (P : Subgroup (section10Msigma M)) (section10Msigma M).subtype_injective)
  have hPamb_ne : Pamb ≠ ⊥ := by
    intro hbot
    have hA_bot : A = ⊥ := by
      exact le_bot_iff.mp (_hA_le_P.trans (by simpa [Pamb] using le_of_eq hbot))
    rcases section12_rankTwo_elementary hA with ⟨hAcard, _hAelem⟩
    have hcard_bot : Nat.card A = 1 := (Subgroup.card_eq_one (H := A)).2 hA_bot
    have hp2_ne_one : p.val ^ 2 ≠ 1 := by
      have hp_le_sq : p.val ≤ p.val ^ 2 :=
        le_self_pow p.2.one_lt.le (by decide : 2 ≠ 0)
      exact ne_of_gt (p.2.one_lt.trans_le hp_le_sq)
    exact hp2_ne_one (by simpa [hAcard] using hcard_bot)
  have hZ_ne : Z ≠ ⊥ := by
    simpa [Z] using
      section12_omegaOneCenter_ne_bot_of_nontrivial_pgroup_pre
        (p := p) (P := Pamb) hPamb_p hPamb_ne
  have hPnormal_σ : (P : Subgroup (section10Msigma M)).Normal :=
    Group.IsNilpotent.sylow_normal hnil p.val P
  have hPchar_σ : (P : Subgroup (section10Msigma M)).Characteristic :=
    Sylow.characteristic_of_normal P hPnormal_σ
  have hσsub_norm : ((section10Msigma M).subgroupOf M).Normal := by
    simpa [section12Msigma_subgroupOf_eq] using
      section10MsigmaSubgroup_normal (M := M)
  have hM_le_normσ : M ≤ Subgroup.normalizer (section10Msigma M : Set G) := by
    let : ((section10Msigma M).subgroupOf M).Normal := hσsub_norm
    exact Subgroup.le_normalizer_of_normal_subgroupOf (by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property)
  have hnormσ_le_normP :
      Subgroup.normalizer (section10Msigma M : Set G) ≤
        Subgroup.normalizer (Pamb : Set G) := by
    simpa [Pamb, section10AmbientSylowSubgroup] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := section10Msigma M)
        (K := (P : Subgroup (section10Msigma M))))
  have hPamb_normM : M ≤ Subgroup.normalizer (Pamb : Set G) :=
    hM_le_normσ.trans hnormσ_le_normP
  have hZchar_Pamb : (Ω₁Z p.val Pamb).Characteristic :=
    section12_omega1Z_characteristic_pre p.val Pamb
  have hnormP_le_normZ :
      Subgroup.normalizer (Pamb : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
    simpa [Z, section10OmegaOneCenter] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := Pamb) (K := Ω₁Z p.val Pamb))
  have hM_le_normZ : M ≤ Subgroup.normalizer (Z : Set G) :=
    hPamb_normM.trans hnormP_le_normZ
  have hZ_le_A' : Z ≤ A := by
    simpa [Z] using hZ_le_A
  have hZ_le_M : Z ≤ M := hZ_le_A'.trans (section12_rankTwo_le hA)
  have hZnormM : (Z.subgroupOf M).Normal := by
    exact Subgroup.normal_subgroupOf_of_le_normalizer hM_le_normZ
  have hM8 : M ∈ section8MaximalSubgroups G :=
    by simpa [section8MaximalSubgroups, section9MaximalSubgroups] using hM
  have hNormZ : Subgroup.normalizer (Z : Set G) = M :=
    section8_normalizer_eq_of_nontrivial_normal_in_maximal hM8 hZ_le_M hZ_ne hZnormM
  exact (Subgroup.centralizer_le (show (Z : Set G) ⊆ (A : Set G) from by
      simpa [Z] using hZ_le_A)).trans
    ((centralizer_le_normalizer Z).trans (by rw [hNormZ]))

/-- Proposition 12.4(a). -/
public theorem CFSG.proposition_12_4_a
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    Subgroup.centralizer (A : Set G) ≤ M := by
  classical
  by_cases hExists :
      ∃ A₀ : Subgroup G, A₀ ∈ section10PrimeOrderSubgroupsIn p A ∧
        section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) = {M}
  · rcases hExists with ⟨A₀, hA₀, huniq⟩
    exact section12_centralizer_le_of_unique_normalizer_primeOrder_pre hA₀ huniq
  · have hnotUnique :
        ∀ A₀ : Subgroup G, A₀ ∈ section10PrimeOrderSubgroupsIn p A →
          section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) ≠ {M} := by
      intro A₀ hA₀ huniq
      exact hExists ⟨A₀, hA₀, huniq⟩
    exact section12_prop_12_4_hard_branch_pre hM hA hnotUnique


end Section12
