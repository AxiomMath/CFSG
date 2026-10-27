module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_16_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_17
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section12_lemma_12_17_coprime_action
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    subgroupCentralizerIn (section10Msigma M) E ≤ ambientDerivedSubgroup (section10Msigma M) ∧
      ⁅section10Msigma M, E⁆ = section10Msigma M := by
  classical
  let Hloc : Subgroup M := section10MsigmaSubgroup M
  let Kloc : Subgroup M := E.subgroupOf M
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  let : Group.IsSolvable M := hMsolv
  have hHnorm : Hloc.Normal := by
    dsimp [Hloc]
    infer_instance
  let : Hloc.Normal := hHnorm
  have hHall : IsHallSubgroup (section10SigmaPrimes M) Hloc := by
    simpa [Hloc] using (theorem_10_2_b (G := G) hM).2
  have hcomp' : Kloc.IsComplement' Hloc := by
    simpa [Hloc, Kloc] using
      section12_complement_to_msigma_isComplement' (G := G) (M := M) (E := E) hE.1
  have hCompl : IsCompl Hloc Kloc := by
    simpa using hcomp'.symm.isCompl
  have hld : Hloc ≤ derivedSubgroup M := by
    simpa [Hloc] using (theorem_10_2_c (G := G) hM).2
  have hHloc_map : Hloc.map M.subtype = section10Msigma M := by
    simpa [Hloc, section12Msigma_subgroupOf_eq (G := G) (M := M)] using
      (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := section10Msigma M)
        (K := M) (section12_Msigma_le (G := G) M))
  have hKloc_map : Kloc.map M.subtype = E := by
    simpa [Kloc] using
      (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := E) (K := M) hE.1.2.1)
  have hcent_local : subgroupCentralizerIn Hloc Kloc ≤ ⁅Hloc, Hloc⁆ :=
    lemma_6_3_a_2 (G := M) (H := Hloc) (K := Kloc)
      ⟨section10SigmaPrimes M, hHall⟩ hCompl hld
  have hcomm_local : Hloc = ⁅Hloc, Kloc⁆ :=
    lemma_6_3_a_1 (G := M) (H := Hloc) (K := Kloc)
      ⟨section10SigmaPrimes M, hHall⟩ hCompl hld
  have hHH_comm_map :
      (⁅Hloc, Hloc⁆).map M.subtype =
        ambientDerivedSubgroup (section10Msigma M) := by
    calc
      (⁅Hloc, Hloc⁆).map M.subtype =
          ⁅Hloc.map M.subtype, Hloc.map M.subtype⁆ := by
            simpa using
              (Subgroup.map_commutator (H₁ := Hloc) (H₂ := Hloc) M.subtype)
      _ = ⁅section10Msigma M, section10Msigma M⁆ := by rw [hHloc_map]
      _ = ambientDerivedSubgroup (section10Msigma M) := by
            rw [section12_ambientDerivedSubgroup_eq_commutator]
  have hHK_comm_map :
      (⁅Hloc, Kloc⁆).map M.subtype = ⁅section10Msigma M, E⁆ := by
    calc
      (⁅Hloc, Kloc⁆).map M.subtype =
          ⁅Hloc.map M.subtype, Kloc.map M.subtype⁆ := by
            simpa using
              (Subgroup.map_commutator (H₁ := Hloc) (H₂ := Kloc) M.subtype)
      _ = ⁅section10Msigma M, E⁆ := by rw [hHloc_map, hKloc_map]
  constructor
  · intro x hx
    have hxσ : x ∈ section10Msigma M := hx.1
    have hxCentE : x ∈ Subgroup.centralizer (E : Set G) := hx.2
    have hxM : x ∈ M := section12_Msigma_le (G := G) M hxσ
    let xM : M := ⟨x, hxM⟩
    have hxHloc : xM ∈ Hloc := by
      have hxSub : xM ∈ (section10Msigma M).subgroupOf M := by
        simpa [xM, Subgroup.mem_subgroupOf] using hxσ
      simpa [Hloc, section12Msigma_subgroupOf_eq (G := G) (M := M)] using hxSub
    have hxCentLoc : xM ∈ Subgroup.centralizer (Kloc : Set M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyKloc
      apply Subtype.ext
      have hyE : (y : G) ∈ E := by
        simpa [Kloc, Subgroup.mem_subgroupOf] using hyKloc
      have hcomm : (y : G) * x = x * (y : G) :=
        (Subgroup.mem_centralizer_iff.mp hxCentE) (y : G) hyE
      simpa [xM] using hcomm
    have hxCentral : xM ∈ subgroupCentralizerIn Hloc Kloc := ⟨hxHloc, hxCentLoc⟩
    have hxComm : xM ∈ ⁅Hloc, Hloc⁆ := hcent_local hxCentral
    have hxMap : x ∈ (⁅Hloc, Hloc⁆).map M.subtype :=
      Subgroup.mem_map.mpr ⟨xM, hxComm, rfl⟩
    simpa [hHH_comm_map] using hxMap
  · have hmap_eq :
        Hloc.map M.subtype = (⁅Hloc, Kloc⁆).map M.subtype :=
      congrArg (fun L : Subgroup M => L.map M.subtype) hcomm_local
    have hEq : section10Msigma M = ⁅section10Msigma M, E⁆ := by
      simpa [hHloc_map, hHK_comm_map] using hmap_eq
    exact hEq.symm

private theorem CFSG.section12_lemma_12_17_not_centralizer_le
    {M X : Subgroup G} {p : Nat.Primes} {g : G}
    (hM : M ∈ section9MaximalSubgroups G) (hg : g ∉ M)
    (hXI : X ≤ section10Msigma M ⊓ M.conjBy g)
    (hXne : X ≠ ⊥) (hXp : IsPGroup p.val X) :
    ¬ Subgroup.centralizer (X : Set G) ≤ M := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have hXσ : X ≤ section10Msigma M := hXI.trans inf_le_left
  have hXM : X ≤ M := hXσ.trans (section12_Msigma_le (G := G) M)
  have hXMg : X ≤ M.conjBy g := hXI.trans inf_le_right
  have hpσ : p ∈ section10SigmaPrimes M := by
    have hXsub_ne : X.subgroupOf (section10Msigma M) ≠ ⊥ := by
      intro hbot
      exact hXne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hXσ)
    have hXsub_p : IsPGroup p.val (X.subgroupOf (section10Msigma M)) :=
      hXp.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := X) (K := section10Msigma M) hXσ).symm
    have hpMsigma : p ∈ subgroupPrimeSet (section10Msigma M) :=
      section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
        (A := section10Msigma M) (B := X.subgroupOf (section10Msigma M))
        hXsub_p hXsub_ne
    exact (theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_card p hpMsigma
  have hXginvM : X.conjBy g⁻¹ ≤ M := by
    have hmap : X.conjBy g⁻¹ ≤ (M.conjBy g).conjBy g⁻¹ :=
      Subgroup.map_mono hXMg
    simpa [section11_conjBy_inv] using hmap
  intro hCXM
  rcases theorem_10_1_a
      (G := G) (M := M) (X := X) (p := p)
      hM hpσ hXne hXp hXM hXginvM with
    ⟨m, c, hginv⟩
  have hcM : (c : G) ∈ M := hCXM c.property
  have hginvM : g⁻¹ ∈ M := by
    rw [hginv]
    exact M.mul_mem m.property hcM
  exact hg (by simpa using M.inv_mem hginvM)

private theorem CFSG.section12_lemma_12_17_prime_order_exclusions
    {M X : Subgroup G} {p : Nat.Primes} {g : G}
    (hM : M ∈ section9MaximalSubgroups G) (hg : g ∉ M)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p (section10Msigma M ⊓ M.conjBy g)) :
    p ∉ section10BetaPrimes M ∧
      ¬ X ≤ ambientDerivedSubgroup (section10Msigma M) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with
    ⟨hXI, hXcard⟩
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hcard_bot : Nat.card X = 1 := (Subgroup.card_eq_one (H := X)).2 hbot
    have hp_one : p.val = 1 := by simpa [hXcard] using hcard_bot
    exact p.property.ne_one hp_one
  have hXp : IsPGroup p.val X := by
    refine IsPGroup.of_card (p := p.val) (G := X) (n := 1) ?_
    simpa [pow_one] using hXcard
  have hXI_inf : X ≤ section10Msigma M ⊓ M.conjBy g := by
    intro x hx
    exact ⟨hXI.1 hx, hXI.2 hx⟩
  have hXσ : X ≤ section10Msigma M := hXI.1
  have hXM : X ∈ section10PrimeOrderSubgroupsIn p M :=
    ⟨hXσ.trans (section12_Msigma_le (G := G) M), hXcard⟩
  have hpMsigma : p ∈ subgroupPrimeSet (section10Msigma M) := by
    have hpX : p ∈ subgroupPrimeSet X := by
      change p.val ∣ Nat.card X
      rw [hXcard]
    exact section8_subgroupPrimeSet_mono hXσ hpX
  have hpσ : p ∈ section10SigmaPrimes M :=
    (theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_card p hpMsigma
  have hnotC :
      ¬ Subgroup.centralizer (X : Set G) ≤ M :=
    section12_lemma_12_17_not_centralizer_le
      (G := G) (M := M) (X := X) (p := p) (g := g)
      hM hg hXI_inf hXne hXp
  let P : Sylow p.val (section10Msigma M) :=
    Classical.choice (Sylow.nonempty (p := p.val) (G := section10Msigma M))
  constructor
  · intro hpβ
    have hsingle :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} :=
      (corollary_12_14
        (G := G) (M := M) (X := X) (p := p) P
        hM hpσ hXM (Or.inl hpβ)).1
    have hMcont :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
      rw [hsingle]
      simp
    exact hnotC hMcont.2
  · intro hXder
    have hsingle :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} :=
      (corollary_12_14
        (G := G) (M := M) (X := X) (p := p) P
        hM hpσ hXM (Or.inr hXder)).1
    have hMcont :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
      rw [hsingle]
      simp
    exact hnotC hMcont.2

private theorem CFSG.section12_lemma_12_17_primeRank_le_one
    {M : Subgroup G} {p : Nat.Primes} {g : G}
    (hM : M ∈ section9MaximalSubgroups G) (hg : g ∉ M) :
    primeRank p.val ↥(section10Msigma M ⊓ M.conjBy g) ≤ 1 := by
  classical
  by_contra hnot
  have hrank : 2 ≤ primeRank p.val ↥(section10Msigma M ⊓ M.conjBy g) := by
    omega
  obtain ⟨A, hA⟩ :=
    section12_exists_rankTwo_in_subgroup_of_two_le_primeRank
      (G := G) (N := section10Msigma M ⊓ M.conjBy g) (p := p) hrank
  have hA_le_I : A ≤ section10Msigma M ⊓ M.conjBy g :=
    section12_rankTwo_le hA
  have hAne : A ≠ ⊥ := section12_rankTwo_ne_bot hA
  have hAp : IsPGroup p.val A := by
    rcases section12_rankTwo_elementary hA with ⟨_hcard, hElem⟩
    have : IsElementaryAbelian p.val A := hElem
    exact IsElementaryAbelian.isPGroup p.val A
  have hAnoncyc : ¬ IsCyclic A :=
    section12_rankTwo_noncyclic (G := G) (H := section10Msigma M ⊓ M.conjBy g) hA
  have hAσ : A ≤ section10Msigma M := hA_le_I.trans inf_le_left
  have hAM : A ≤ M := hAσ.trans (section12_Msigma_le (G := G) M)
  have hpσ : p ∈ section10SigmaPrimes M := by
    have hpI : p ∈ subgroupPrimeSet (section10Msigma M ⊓ M.conjBy g) :=
      section12_rankTwo_prime_mem hA
    have hpMsigma : p ∈ subgroupPrimeSet (section10Msigma M) :=
      section8_subgroupPrimeSet_mono inf_le_left hpI
    exact (theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_card p hpMsigma
  have hnotC :
      ¬ Subgroup.centralizer (A : Set G) ≤ M :=
    section12_lemma_12_17_not_centralizer_le
      (G := G) (M := M) (X := A) (p := p) (g := g)
      hM hg hA_le_I hAne hAp
  have hnorm_le : Subgroup.normalizer (A : Set G) ≤ M :=
    corollary_12_10_d (G := G) (M := M) (P := A) (p := p)
      hM hpσ hAp hAM hAnoncyc
  exact hnotC ((centralizer_le_normalizer A).trans hnorm_le)

private theorem CFSG.section12_lemma_12_17_beta_compl
    {M : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G) (hg : g ∉ M) :
    IsPiSubgroup (section10BetaPrimes M)ᶜ (section10Msigma M ⊓ M.conjBy g) := by
  classical
  intro p hpI
  obtain ⟨z, _hzI, _hzne, hZp⟩ :=
    section12_exists_primeOrder_zpowers_of_prime_dvd_card
      (G := G) (B := section10Msigma M ⊓ M.conjBy g) (q := p) hpI
  have hp_not_beta :
      p ∉ section10BetaPrimes M :=
    (section12_lemma_12_17_prime_order_exclusions
      (G := G) (M := M) (X := Subgroup.zpowers z) (p := p) (g := g)
      hM hg hZp).1
  simpa [Set.mem_compl_iff] using hp_not_beta

private theorem CFSG.section12_lemma_12_17_disjoint_derived
    {M : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G) (hg : g ∉ M) :
    Disjoint (section10Msigma M ⊓ M.conjBy g)
      (ambientDerivedSubgroup (section10Msigma M)) := by
  classical
  let I : Subgroup G := section10Msigma M ⊓ M.conjBy g
  let D : Subgroup G := ambientDerivedSubgroup (section10Msigma M)
  rw [Subgroup.disjoint_def]
  intro x hxI hxD
  by_contra hxne
  let J : Subgroup G := I ⊓ D
  have hJne : J ≠ ⊥ := by
    intro hJbot
    have hxJ : x ∈ J := ⟨hxI, hxD⟩
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [J, hJbot] using hxJ
    exact hxne (by simpa using hxbot)
  have hJcard_ne_one : Nat.card J ≠ 1 := by
    intro hcard
    exact hJne ((Subgroup.card_eq_one (H := J)).mp hcard)
  obtain ⟨q0, hq0prime, hq0dvd⟩ := Nat.exists_prime_and_dvd hJcard_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  obtain ⟨z, _hzJ, _hzne, hZq⟩ :=
    section12_exists_primeOrder_zpowers_of_prime_dvd_card
      (G := G) (B := J) (q := q) hq0dvd
  have hZ_I :
      Subgroup.zpowers z ∈ section10PrimeOrderSubgroupsIn q I := by
    rcases (show Subgroup.zpowers z ≤ J ∧
        Nat.card (Subgroup.zpowers z) = q.val from hZq) with
      ⟨hZJ, hZcard⟩
    exact ⟨hZJ.trans inf_le_left, hZcard⟩
  have hZ_D : Subgroup.zpowers z ≤ D := by
    rcases (show Subgroup.zpowers z ≤ J ∧
        Nat.card (Subgroup.zpowers z) = q.val from hZq) with
      ⟨hZJ, _hZcard⟩
    exact hZJ.trans inf_le_right
  have hnotZ_D :
      ¬ Subgroup.zpowers z ≤ D :=
    (section12_lemma_12_17_prime_order_exclusions
      (G := G) (M := M) (X := Subgroup.zpowers z) (p := q) (g := g)
      hM hg (by simpa [I] using hZ_I)).2
  exact hnotZ_D hZ_D

private theorem CFSG.section12_lemma_12_17_inf_cyclic
    {M : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G) (hg : g ∉ M) :
    IsCyclic ↥(section10Msigma M ⊓ M.conjBy g) := by
  classical
  let I : Subgroup G := section10Msigma M ⊓ M.conjBy g
  let D : Subgroup G := ambientDerivedSubgroup (section10Msigma M)
  have hdisj : Disjoint I D :=
    section12_lemma_12_17_disjoint_derived (G := G) (M := M) (g := g) hM hg
  have hInf_bot : I ⊓ D = ⊥ := hdisj.eq_bot
  have hcomm_le_I : ⁅I, I⁆ ≤ I := Subgroup.commutator_le_self I
  have hcomm_le_D : ⁅I, I⁆ ≤ D := by
    dsimp [I, D]
    rw [section12_ambientDerivedSubgroup_eq_commutator]
    exact Subgroup.commutator_mono inf_le_left inf_le_left
  have hcomm_bot : ⁅I, I⁆ = ⊥ := by
    have hcomm_le_inf : ⁅I, I⁆ ≤ I ⊓ D := le_inf hcomm_le_I hcomm_le_D
    have hcomm_le_bot : ⁅I, I⁆ ≤ ⊥ := by
      simpa [hInf_bot] using hcomm_le_inf
    exact le_bot_iff.mp hcomm_le_bot
  have hIcomm : IsMulCommutative I := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm_bot
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have hyc : (y : G) ∈ Subgroup.centralizer (I : Set G) := hcomm_bot y.property
    have hxy : (x : G) * y = y * x := by
      simpa [Subgroup.mem_centralizer_iff] using hyc x x.property
    exact hxy
  have hIZ : IsZGroup I := by
    refine ⟨fun q hq Q => ?_⟩
    let p : Nat.Primes := ⟨q, hq⟩
    have : Fact p.val.Prime := ⟨p.2⟩
    by_cases hdiv : p.val ∣ Nat.card I
    · have hpodd : p.val ≠ 2 :=
        Odd.ne_two_of_dvd_nat IsMinCE.odd_order
          (hdiv.trans (Subgroup.card_subgroup_dvd_card I))
      have hrank : primeRank p.val I ≤ 1 :=
        by simpa [I] using
          section12_lemma_12_17_primeRank_le_one
            (G := G) (M := M) (p := p) (g := g) hM hg
      exact section12_sylow_cyclic_of_primeRank_le_one
        (G := G) (E := I) (p := p) hpodd hrank Q
    · have hQbot : (Q : Subgroup I) = ⊥ := by
        by_contra hQne
        have : Nontrivial (Q : Subgroup I) :=
          (Subgroup.nontrivial_iff_ne_bot (H := (Q : Subgroup I))).2 hQne
        have hpQ : p.val ∣ Nat.card (Q : Subgroup I) :=
          section12_prime_dvd_card_of_nontrivial_pSubgroup
            (p := p) (B := (Q : Subgroup I)) Q.isPGroup' inferInstance
        exact hdiv (hpQ.trans (Subgroup.card_subgroup_dvd_card (Q : Subgroup I)))
      have : Subsingleton (Q : Subgroup I) := by
        rw [hQbot]
        infer_instance
      exact isCyclic_of_subsingleton (α := (Q : Subgroup I))
  let : IsZGroup I := hIZ
  let : IsMulCommutative I := hIcomm
  let : CommGroup I := IsMulCommutative.instCommGroup
  exact inferInstance

/-- Lemma 12.17. -/
public theorem CFSG.lemma_12_17
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    subgroupCentralizerIn (section10Msigma M) E ≤ ambientDerivedSubgroup (section10Msigma M) ∧
      ⁅section10Msigma M, E⁆ = section10Msigma M ∧
        ∀ g : G, g ∉ M →
          IsCyclic ↥(section10Msigma M ⊓ M.conjBy g) ∧
            IsPiSubgroup (section10BetaPrimes M)ᶜ (section10Msigma M ⊓ M.conjBy g) ∧
              Disjoint (section10Msigma M ⊓ M.conjBy g)
                (ambientDerivedSubgroup (section10Msigma M)) := by
  classical
  rcases section12_lemma_12_17_coprime_action
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE with
    ⟨hcentral, hcomm⟩
  refine ⟨hcentral, hcomm, ?_⟩
  intro g hg
  exact ⟨
    section12_lemma_12_17_inf_cyclic (G := G) (M := M) (g := g) hM hg,
    section12_lemma_12_17_beta_compl (G := G) (M := M) (g := g) hM hg,
    section12_lemma_12_17_disjoint_derived (G := G) (M := M) (g := g) hM hg⟩

end Section12
