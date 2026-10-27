module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_6_f

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section12_exists_rankTwo_in_noncyclic_pSubgroup
    {P : Subgroup G} {p : Nat.Primes}
    (hPp : IsPGroup p.val P) (hPnoncyc : ¬ IsCyclic P) :
    ∃ A : Subgroup G, A ∈ section12RankTwoElementaryAbelianIn p P := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hp_dvd_P : p.val ∣ Nat.card P := by
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    cases n with
    | zero =>
        have hcard_one : Nat.card P = 1 := by
          simpa using hn
        exact False.elim <| hPnoncyc <| by
          letI : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hcard_one).1
          exact isCyclic_of_subsingleton (α := P)
    | succ n =>
        rw [hn]
        exact dvd_pow_self p.val (Nat.succ_ne_zero n)
  have hp_dvd_G : p.val ∣ Nat.card G :=
    hp_dvd_P.trans (Subgroup.card_subgroup_dvd_card P)
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  haveI : Fact (IsPGroup p.val P) := ⟨hPp⟩
  obtain ⟨A₀, _hA₀norm, hA₀card, hA₀elem⟩ :=
    lemma_4_5_a (R := P) (p := p.val) hpodd hPnoncyc
  haveI : IsElementaryAbelian p.val A₀ := hA₀elem
  let A : Subgroup G := A₀.map P.subtype
  have hA_le_P : A ≤ P := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, _ha, rfl⟩
    exact a.2
  have hAcard : Nat.card A = p.val ^ 2 := by
    have hcard : Nat.card A = Nat.card A₀ := by
      simpa [A] using
        Subgroup.card_map_of_injective (K := A₀) (f := P.subtype) P.subtype_injective
    rw [hcard, hA₀card]
  have hAelem : IsElementaryAbelian p.val A := by
    simpa [A] using
      section12_isElementaryAbelian_map (p := p.val) (A := A₀) P.subtype
  exact ⟨A, ⟨hA_le_P, hAcard, hAelem⟩⟩

public theorem CFSG.section12_inf_msigma_eq_bot_of_pSubgroup_not_sigma
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∉ section10SigmaPrimes M)
    (hAM : A ≤ M) (hAp : IsPGroup p.val A) :
    section10Msigma M ⊓ A = ⊥ := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hHall :
      IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
    (theorem_10_2_b (M := M) hM).2
  apply Subgroup.card_eq_one.mp
  apply section12_card_eq_one_of_no_prime_dvd
  intro q hqdiv
  let J : Subgroup G := section10Msigma M ⊓ A
  have hJM : J ≤ M := by
    intro x hx
    exact hAM hx.2
  let I : Subgroup M := J.subgroupOf M
  have hIcard : Nat.card I = Nat.card J :=
    natCard_subgroupOf_eq _ _ hJM
  have hqIdiv : q.val ∣ Nat.card I := by
    simpa [I, hIcard, J] using hqdiv
  have hI_sigma : IsPiSubgroup (G := M) (section10SigmaPrimes M) I := by
    refine IsPiSubgroup.of_le ?_ (fun r hr => hHall.p_in_pi_of_p_dvd_card r hr)
    intro x hx
    have hxσ : (x : G) ∈ section10Msigma M := by
      have hxJ : (x : G) ∈ J := by
        simpa [I, Subgroup.mem_subgroupOf] using hx
      exact hxJ.1
    change x ∈ section10MsigmaSubgroup M
    have hxσsub : x ∈ (section10Msigma M).subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hxσ
    simpa [section12Msigma_subgroupOf_eq] using hxσsub
  have hI_p : IsPGroup p.val I := by
    have hJp_sub : IsPGroup p.val (J.subgroupOf A) :=
      hAp.to_subgroup (J.subgroupOf A)
    let eJA : J.subgroupOf A ≃* J :=
      Subgroup.subgroupOfEquivOfLe (H := J) (K := A) inf_le_right
    have hJp : IsPGroup p.val J := hJp_sub.of_equiv eJA
    let e : I ≃* J :=
      Subgroup.subgroupOfEquivOfLe (H := J) (K := M) hJM
    exact hJp.of_equiv e.symm
  have hqσ : q ∈ section10SigmaPrimes M := hI_sigma q hqIdiv
  have hqeqp : q = p := by
    rcases hI_p.exists_card_eq with ⟨n, hn⟩
    have hq_dvd_p : q.val ∣ p.val := by
      exact q.2.dvd_of_dvd_pow (by simpa [I, hn] using hqIdiv)
    exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hq_dvd_p)
  exact hpσ (by simpa [hqeqp] using hqσ)

public theorem CFSG.section12_primeRank_E_ge_two_of_tau2
    {M E : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E)
    (hp : p ∈ section12Tau2Primes M) :
    2 ≤ primeRank p.val E := by
  classical
  rcases (by simpa [section12Tau2Primes] using hp) with ⟨hpσ, hprank⟩
  obtain ⟨A, hAp, hAcomm, hAgen⟩ :=
    section12_exists_pSubgroup_two_le_generatorRank_of_two_le_primeRank
      (R := M) (p := p.val) (by simp [hprank])
  have hAinf : section10Msigma M ⊓ (A.map M.subtype) = ⊥ := by
    have hAmap_p : IsPGroup p.val (A.map M.subtype) :=
      IsPGroup.map hAp M.subtype
    have hAmap_M : A.map M.subtype ≤ M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨a, _ha, rfl⟩
      exact a.property
    exact section12_inf_msigma_eq_bot_of_pSubgroup_not_sigma
      (G := G) (M := M) (A := A.map M.subtype) (p := p) hM hpσ hAmap_M hAmap_p
  have hAker_bot : (section10MsigmaSubgroup M).subgroupOf A = ⊥ := by
    apply le_bot_iff.mp
    intro a ha
    have haσ : ((a : M) : G) ∈ section10Msigma M := by
      have haσsub : (a : M) ∈ (section10Msigma M).subgroupOf M := by
        rw [section12Msigma_subgroupOf_eq]
        exact Subgroup.mem_subgroupOf.mp ha
      simpa [Subgroup.mem_subgroupOf] using haσsub
    have haA : ((a : M) : G) ∈ A.map M.subtype :=
      Subgroup.mem_map.mpr ⟨a, a.property, rfl⟩
    have habot : ((a : M) : G) ∈ (⊥ : Subgroup G) := by
      simpa [hAinf] using (show ((a : M) : G) ∈
        section10Msigma M ⊓ A.map M.subtype from ⟨haσ, haA⟩)
    apply Subtype.ext
    apply Subtype.ext
    simpa using habot
  let eA : A ≃* (A.map (QuotientGroup.mk' (section10MsigmaSubgroup M))) :=
    ((QuotientGroup.quotientMulEquivOfEq hAker_bot).trans
      (QuotientGroup.quotientBot (G := A))).symm.trans
        (quotientSubgroupRangeEquiv A (section10MsigmaSubgroup M))
  let eME : M ⧸ section10MsigmaSubgroup M ≃* E :=
    section12QuotientEquivComplement (M := M) (E := E) hcomp
  let Abar : Subgroup E :=
    (A.map (QuotientGroup.mk' (section10MsigmaSubgroup M))).map eME.toMonoidHom
  have hAbar_p : IsPGroup p.val Abar := by
    exact IsPGroup.map
      (IsPGroup.map hAp (QuotientGroup.mk' (section10MsigmaSubgroup M)))
      eME.toMonoidHom
  have hAbar_comm : IsMulCommutative Abar := by
    letI : IsMulCommutative A := hAcomm
    infer_instance
  have hgen_le_Abar : generatorRank A ≤ generatorRank Abar := by
    let eAbar : A ≃* Abar :=
      eA.trans
        (Subgroup.equivMapOfInjective
          (f := eME.toMonoidHom)
          (A.map (QuotientGroup.mk' (section10MsigmaSubgroup M)))
          eME.injective)
    exact section12_generatorRank_le_of_equiv (R := Abar) (S := A) eAbar.symm
  exact hAgen.trans
    (hgen_le_Abar.trans
      (section12_generatorRank_le_primeRank_of_subgroup
        (R := E) (q := p.val) (A := Abar) hAbar_p hAbar_comm))

public theorem CFSG.section12_exists_rankTwo_in_E_of_tau2
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hq : q ∈ section12Tau2Primes M) :
    ∃ B : Subgroup G, B ∈ section12RankTwoElementaryAbelianIn q E := by
  classical
  have hErank : 2 ≤ primeRank q.val E :=
    section12_primeRank_E_ge_two_of_tau2 hM hE.1 hq
  obtain ⟨A, hAp, hAcomm, hAgen⟩ :=
    section12_exists_pSubgroup_two_le_generatorRank_of_two_le_primeRank
      (R := E) (p := q.val) hErank
  have hAnoncyc : ¬ IsCyclic A :=
    section12_not_isCyclic_of_two_le_generatorRank hAgen
  let Aamb : Subgroup G := A.map E.subtype
  have hAamb_p : IsPGroup q.val Aamb := IsPGroup.map hAp E.subtype
  have hAamb_noncyc : ¬ IsCyclic Aamb := by
    intro hAamb_cyc
    let e : A ≃* Aamb :=
      Subgroup.equivMapOfInjective (f := E.subtype) A E.subtype_injective
    exact hAnoncyc (e.isCyclic.2 hAamb_cyc)
  obtain ⟨B, hB_Aamb⟩ :=
    section12_exists_rankTwo_in_noncyclic_pSubgroup
      (G := G) (P := Aamb) (p := q) hAamb_p hAamb_noncyc
  refine ⟨B, section12_rankTwo_mono hB_Aamb ?_⟩
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨a, _ha, rfl⟩
  exact a.property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_normal_rankTwo_centralizes_of_ne
    {E A B : Subgroup G} {p q : Nat.Primes}
    (hpq : p ≠ q)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hB : B ∈ section12RankTwoElementaryAbelianIn q E)
    (hAnorm : section10NormalIn A E) (hBnorm : section10NormalIn B E) :
    A ≤ Subgroup.centralizer (B : Set G) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  haveI : Fact q.val.Prime := ⟨q.2⟩
  have hAp : IsPGroup p.val (A.subgroupOf E) :=
    section12_rankTwo_subgroupOf_isPGroup hA
  have hBq : IsPGroup q.val (B.subgroupOf E) :=
    section12_rankTwo_subgroupOf_isPGroup hB
  have hdisj : Disjoint (A.subgroupOf E) (B.subgroupOf E) :=
    IsPGroup.disjoint_of_ne p.val q.val (by
      intro hpqval
      exact hpq (Subtype.ext hpqval)) (A.subgroupOf E) (B.subgroupOf E) hAp hBq
  haveI : (A.subgroupOf E).Normal := hAnorm.2
  haveI : (B.subgroupOf E).Normal := hBnorm.2
  have hcomm_le_inf : ⁅A.subgroupOf E, B.subgroupOf E⁆ ≤ A.subgroupOf E ⊓ B.subgroupOf E :=
    Subgroup.commutator_le_inf (H₁ := A.subgroupOf E) (H₂ := B.subgroupOf E)
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have haE : a ∈ E := section12_rankTwo_le hA ha
  have hbE : b ∈ E := section12_rankTwo_le hB hb
  let aE : E := ⟨a, haE⟩
  let bE : E := ⟨b, hbE⟩
  have haSub : aE ∈ A.subgroupOf E := by
    simpa [aE, Subgroup.mem_subgroupOf] using ha
  have hbSub : bE ∈ B.subgroupOf E := by
    simpa [bE, Subgroup.mem_subgroupOf] using hb
  have hcomm_mem : ⁅aE, bE⁆ ∈ ⁅A.subgroupOf E, B.subgroupOf E⁆ :=
    Subgroup.commutator_mem_commutator haSub hbSub
  have hcomm_inf : ⁅aE, bE⁆ ∈ A.subgroupOf E ⊓ B.subgroupOf E :=
    hcomm_le_inf hcomm_mem
  have hcomm_bot : ⁅aE, bE⁆ ∈ (⊥ : Subgroup E) := by
    simpa [hdisj.eq_bot] using hcomm_inf
  have hcomm_one : ⁅aE, bE⁆ = 1 := by
    simpa using hcomm_bot
  have hmul : aE * bE = bE * aE := by
    rwa [commutatorElement_eq_one_iff_mul_comm] at hcomm_one
  exact (congrArg (fun x : E => (x : G)) hmul).symm

public theorem CFSG.section12_sylow_contained_in_E_forces_abelian_sylow_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    {P : Sylow p.val G} (hP_le_E : (P : Subgroup G) ≤ E) :
    IsMulCommutative (P : Subgroup G) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hP_le_M : (P : Subgroup G) ≤ M := hP_le_E.trans hE.1.2.1
  let Psub : Subgroup M := (P : Subgroup G).subgroupOf M
  have hPsub_p : IsPGroup p.val Psub :=
    P.isPGroup'.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := (P : Subgroup G)) (K := M) hP_le_M).symm
  have hp_not_dvd_Psub_index : ¬ p.val ∣ Psub.index := by
    have hmap_eq : Psub.map M.subtype = (P : Subgroup G) := by
      simpa [Psub] using Subgroup.map_subgroupOf_eq_of_le hP_le_M
    have hidx : (P : Subgroup G).index = Psub.index * M.index := by
      rw [← hmap_eq]
      simpa [Psub] using Subgroup.index_map_subtype (K := Psub)
    intro hdiv
    exact P.not_dvd_index (by
      rw [hidx]
      exact dvd_mul_of_dvd_left hdiv _)
  let PM : Sylow p.val M := IsPGroup.toSylow (p := p.val) hPsub_p hp_not_dvd_Psub_index
  have hPM_eq_Psub : (PM : Subgroup M) = Psub := rfl
  have hPMcomm : IsMulCommutative (PM : Subgroup M) :=
    (theorem_12_5_b hM hp hA_M).1 PM
  refine ⟨⟨fun x y => ?_⟩⟩
  have hxsub : (⟨(x : G), hP_le_M x.property⟩ : M) ∈ (PM : Subgroup M) := by
    rw [hPM_eq_Psub]
    simp [Psub, Subgroup.mem_subgroupOf]
  have hysub : (⟨(y : G), hP_le_M y.property⟩ : M) ∈ (PM : Subgroup M) := by
    rw [hPM_eq_Psub]
    simp [Psub, Subgroup.mem_subgroupOf]
  apply Subtype.ext
  exact congrArg (fun z : M => (z : G)) <|
      setLike_mul_comm
        (s := (PM : Subgroup M)) hxsub hysub

omit [IsMinCE G] in
public theorem CFSG.section12_exists_mem_section7HStarFamily_of_mem_family_pre
    {H A R : Subgroup G} {π : Set Nat.Primes}
    (hR : R ∈ section7HFamily H A π) :
    ∃ Q ∈ section7HStarFamily H A π, R ≤ Q := by
  let s : Set (Subgroup G) := {Q | R ≤ Q ∧ Q ∈ section7HFamily H A π}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := ⟨R, le_rfl, hR⟩
  obtain ⟨Q, hQ, hQmax⟩ := hsfin.exists_maximal hsne
  refine ⟨Q, ?_, hQ.1⟩
  refine ⟨hQ.2, ?_⟩
  intro S hQS hS
  exact le_antisymm (hQmax ⟨hQ.1.trans hQS, hS⟩ hQS) hQS

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwoMaximal_subgroupOf_of_le_pre
    {p : Nat.Primes} {A S : Subgroup G} (hAS : A ≤ S)
    (hArankTwo : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G)
    (hAmax : A ∈ maximalElementaryAbelianSubgroups p.val G) :
    A.subgroupOf S ∈ section10RankTwoMaximalElementaryAbelianSubgroups p S := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases hArankTwo with ⟨hAcard, hAelem⟩
  rcases hAmax with ⟨_hAelem', hAmax'⟩
  haveI : IsElementaryAbelian p.val A := hAelem
  have hAsub_card : Nat.card (A.subgroupOf S) = p.val ^ 2 := by
    simpa [hAcard] using
      natCard_subgroupOf_eq A S hAS
  have hAsub_elem : IsElementaryAbelian p.val (A.subgroupOf S) := by
    refine
      { toIsMulCommutative := by
          exact
            { is_comm := ⟨fun x y =>
                Subtype.ext <| Subtype.ext <|
                  setLike_mul_comm (s := A)
                    (Subgroup.mem_subgroupOf.mp x.2) (Subgroup.mem_subgroupOf.mp y.2)⟩ }
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    apply Subtype.ext
    let xA : A := ⟨((x : A.subgroupOf S) : S), Subgroup.mem_subgroupOf.mp x.2⟩
    have hxpow : xA ^ p.val = 1 := by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p.val A) xA
    simpa [xA] using congrArg (fun y : A => ((y : A) : G)) hxpow
  have hAsub_max : A.subgroupOf S ∈ maximalElementaryAbelianSubgroups p.val S := by
    refine ⟨hAsub_elem, ?_⟩
    intro B hAB hBelem
    let Bmap : Subgroup G := B.map S.subtype
    have hA_le_Bmap : A ≤ Bmap := by
      intro a ha
      let aS : A.subgroupOf S := ⟨⟨a, hAS ha⟩, ha⟩
      exact Subgroup.mem_map.mpr ⟨aS, hAB aS.2, rfl⟩
    have hBmap_elem : IsElementaryAbelian p.val Bmap := by
      letI : IsElementaryAbelian p.val B := hBelem
      simpa [Bmap] using
        section12_isElementaryAbelian_map
          (R := S) (S := G) (p := p.val) (A := B) S.subtype
    have hEq : A = Bmap := hAmax' Bmap hA_le_Bmap hBmap_elem
    apply Subgroup.ext
    intro x
    constructor
    · intro hx
      have hxA : ((x : S) : G) ∈ A := hx
      rw [hEq] at hxA
      rcases Subgroup.mem_map.mp hxA with ⟨y, hyB, hyx⟩
      have : y = x := Subtype.ext hyx
      simpa [this] using hyB
    · intro hx
      have hxMap : ((x : S) : G) ∈ Bmap := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [← hEq] at hxMap
      exact hxMap
  exact ⟨⟨hAsub_card, hAsub_elem⟩, hAsub_max⟩

/-- Theorem 12.7(a). -/
public theorem CFSG.theorem_12_7_a
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    section12Tau2Primes M = {p} := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  ext q
  constructor
  · intro hq
    by_contra hq_ne_p
    obtain ⟨B, hB⟩ :=
      section12_exists_rankTwo_in_E_of_tau2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hE hq
    have hp_ne_q : p ≠ q := fun hpq => hq_ne_p hpq.symm
    have hAnorm : section10NormalIn A E :=
      (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA).1
    have hBnorm : section10NormalIn B E :=
      (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := B) (p := q)
        hM hE hq hB).1
    have hA_cent_B : A ≤ Subgroup.centralizer (B : Set G) :=
      section12_normal_rankTwo_centralizes_of_ne
        (G := G) (E := E) (A := A) (B := B) (p := p) (q := q)
        hp_ne_q hA hB hAnorm hBnorm
    have hB_le_centA : B ≤ Subgroup.centralizer (A : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact ((Subgroup.mem_centralizer_iff.mp (hA_cent_B ha)) b hb).symm
    have hqC : q ∈ subgroupPrimeSet (Subgroup.centralizer (A : Set G)) := by
      have hqB : q.val ∣ Nat.card B := by
        rcases section12_rankTwo_elementary hB with ⟨hBcard, _hBelem⟩
        rw [hBcard]
        exact dvd_pow_self q.val (by decide : 2 ≠ 0)
      exact hqB.trans (Subgroup.card_dvd_of_le hB_le_centA)
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
    have hBq : IsPGroup q.val B := by
      rcases section12_rankTwo_elementary hB with ⟨_hBcard, hBelem⟩
      haveI : IsElementaryAbelian q.val B := hBelem
      exact IsElementaryAbelian.isPGroup q.val B
    have hBfam : B ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
      refine ⟨le_top, ?_, ?_⟩
      · exact section12_isPiSubgroup_of_isPGroup_of_mem hBq (by simp)
      · exact hA_cent_B.trans (centralizer_le_normalizer B)
    obtain ⟨Q, hQstar, hB_le_Q⟩ :=
      section12_exists_mem_section7HStarFamily_of_mem_family_pre hBfam
    have hB_M : B ∈ section12RankTwoElementaryAbelianIn q M :=
      section12_rankTwo_of_EData hE hB
    have hBmaxG : B ∈ maximalElementaryAbelianSubgroups q.val G :=
      (lemma_12_1_g (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := B) (p := q)
        hM hE hq hB_M).1
    have hQshape :
        IsCyclic Q ∨
          ∃ B' : Subgroup Q, B' ∈ section10RankTwoMaximalElementaryAbelianSubgroups q Q := by
      right
      exact ⟨B.subgroupOf Q,
        section12_rankTwoMaximal_subgroupOf_of_le_pre
          (G := G) (p := q) (A := B) (S := Q) hB_le_Q
          (section12_rankTwo_elementary hB) hBmaxG⟩
    obtain ⟨P, _hA_le_P, hP_le_CQ⟩ :=
      proposition_10_10_c (G := G) (p := p) (q := q) hp_ne_q
        hA10 hQstar hqC hQshape
    have hCB_le_E : Subgroup.centralizer (B : Set G) ≤ E := by
      have h6B :=
        corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := B) (p := q)
          hM hE hq hB
      simpa [h6B.2.1] using h6B.1
    have hP_le_CB : (P : Subgroup G) ≤ Subgroup.centralizer (B : Set G) := by
      intro x hx
      exact Subgroup.centralizer_le (show (B : Set G) ⊆ (Q : Set G) from hB_le_Q)
        (hP_le_CQ hx)
    have hPcomm : IsMulCommutative (P : Subgroup G) :=
      section12_sylow_contained_in_E_forces_abelian_sylow_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA (hP_le_CB.trans hCB_le_E)
    rcases hSylow with ⟨Pbad, hPbad_noncomm⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Pbad
    have hPbad_comm : IsMulCommutative (Pbad : Subgroup G) := by
      have hconj_comm : IsMulCommutative ((g • P : Sylow p.val G) : Subgroup G) := by
        letI : IsMulCommutative (P : Subgroup G) := hPcomm
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.map_isMulCommutative
          (f := (MulAut.conj g).toMonoidHom) (H := (P : Subgroup G))
      rw [← hg]
      exact hconj_comm
    exact hPbad_noncomm hPbad_comm
  · intro hq
    simpa [Set.mem_singleton_iff.mp hq] using hp


end Section12
