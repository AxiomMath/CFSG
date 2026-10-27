module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_13

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement IsMulCommutative

/-!
# corollary_12_14
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_unique_overgroups_eq_of_contains_maximal_local
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

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_primeOrderSubgroupsIn_isPGroup
    {A X : Subgroup G} {p : Nat.Primes}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A) :
    IsPGroup p.val X := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with
    ⟨_hXA, hXcard⟩
  exact IsPGroup.of_card (p := p.val) (G := X) (n := 1)
    (by simp [hXcard])

omit [IsMinCE G] in
private theorem CFSG.section12_pSubgroup_le_centralizer_of_primeOrder_normalizes
    {U A X : Subgroup G} {p : Nat.Primes}
    (hUp : IsPGroup p.val U)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A)
    (hUnormX : U ≤ Subgroup.normalizer (X : Set G)) :
    U ≤ Subgroup.centralizer (X : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have : Subgroup.Normalizes U X := ⟨hUnormX⟩
  have hXcyc : IsCyclic X := isCyclic_of_prime_card hX.2
  have htriv : ActsTrivially (A := U) (G := X) :=
    actsTrivially_of_isPGroup_on_cyclic_prime_order p.property hUp hXcyc hX.2
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  let uU : U := ⟨u, hu⟩
  let xX : X := ⟨x, hx⟩
  have hfix := htriv uU xX
  have hconj : u * x * u⁻¹ = x := by
    simpa [uU, xX, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
      hUnormX] using congrArg Subtype.val hfix
  have h := congrArg (fun t : G => t * u) hconj
  simpa [mul_assoc] using h.symm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_exists_sylow_containing_pSubgroup
    {K X : Subgroup G} {p : Nat.Primes}
    (hXleK : X ≤ K) (hXp : IsPGroup p.val X) :
    ∃ S : Sylow p.val K, X ≤ section10AmbientSylowSubgroup K S := by
  classical
  have hXsubp : IsPGroup p.val (X.subgroupOf K) :=
    hXp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := X) (K := K) hXleK).symm
  rcases IsPGroup.exists_le_sylow hXsubp with ⟨S, hXS⟩
  refine ⟨S, ?_⟩
  intro x hx
  have hxXsub : (⟨x, hXleK hx⟩ : K) ∈ X.subgroupOf K := by
    simpa [Subgroup.mem_subgroupOf] using hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hXleK hx⟩, hXS hxXsub, rfl⟩

private theorem CFSG.section12_primeRank_le_primeRank_of_normal_hall_ambient_local
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

private theorem CFSG.section12_primeRank_le_groupRank_msigma_sylow_ambient_local
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {p : Nat.Primes} (hpσ : p ∈ section10SigmaPrimes M)
    (P : Sylow p.val (section10Msigma M)) :
    primeRank p.val M ≤
      groupRank (section10AmbientSylowSubgroup (section10Msigma M) P) := by
  classical
  have h1 : primeRank p.val M ≤ primeRank p.val (section10Msigma M) :=
    section12_primeRank_le_primeRank_of_normal_hall_ambient_local hM hpσ
  have h2 :
      primeRank p.val (section10Msigma M) ≤
        groupRank (P : Subgroup (section10Msigma M)) :=
    section10_primeRank_le_groupRank_sylow (G := section10Msigma M) P
  let e : (P : Subgroup (section10Msigma M)) ≃*
      section10AmbientSylowSubgroup (section10Msigma M) P :=
    Subgroup.equivMapOfInjective (f := (section10Msigma M).subtype)
      (P : Subgroup (section10Msigma M)) (section10Msigma M).subtype_injective
  have h3 :
    groupRank (P : Subgroup (section10Msigma M)) ≤
        groupRank (section10AmbientSylowSubgroup (section10Msigma M) P) :=
    groupRank_le_of_equiv e.symm
  exact h1.trans (h2.trans h3)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_ambientSylowSubgroup_smul_local
    {M : Subgroup G} {p : Nat.Primes}
    (P : Sylow p.val M) (m : M) :
    section10AmbientSylowSubgroup M (m • P) =
      (section10AmbientSylowSubgroup M P).conjBy (m : G) := by
  exact section10AmbientSylowSubgroup_smul P m

omit [IsMinCE G] in
private theorem CFSG.section12_conjBy_inv_local (H : Subgroup G) (g : G) :
    (H.conjBy g).conjBy g⁻¹ = H := by
  rw [section8_conjBy_conjBy]
  simpa using section8_conjBy_one H

omit [IsMinCE G] in
private theorem CFSG.section12_conjBy_inv'_local (H : Subgroup G) (g : G) :
    (H.conjBy g⁻¹).conjBy g = H := by
  simpa using section12_conjBy_inv_local (G := G) H g⁻¹

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_top_conjBy_local (g : G) :
    (⊤ : Subgroup G).conjBy g = ⊤ := by
  ext x
  constructor
  · intro _hx
    simp
  · intro _hx
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g⁻¹ * x * g, by simp, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_le_conjBy_inv_of_conjBy_le_local
    {H K : Subgroup G} {g : G} (hHK : H.conjBy g ≤ K) :
    H ≤ K.conjBy g⁻¹ := by
  intro x hx
  rw [Subgroup.conjBy, Subgroup.mem_map]
  refine ⟨g * x * g⁻¹, ?_, ?_⟩
  · apply hHK
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · simp [mul_assoc]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_maximal_conjBy_local
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) (g : G) :
    M.conjBy g ∈ section9MaximalSubgroups G := by
  have h_map : M.conjBy g = Subgroup.map ((MulAut.conj g : G ≃* G) : G →* G) M := rfl
  rw [h_map]
  exact ((MulAut.conj g : G ≃* G).mapSubgroup.isCoatom_iff M).mpr hM

omit [IsMinCE G] in
private theorem CFSG.section12_unique_conjBy_local
    {H : Subgroup G} (hH : H ∈ section9UniqueSubgroups G) (g : G) :
    H.conjBy g ∈ section9UniqueSubgroups G := by
  classical
  rcases hH with ⟨hHproper, M, hMuniq⟩
  have hMcont : M ∈ section9MaximalSubgroupsContaining H := by
    rw [hMuniq]
    simp
  refine ⟨?_, M.conjBy g, ?_⟩
  · intro htop
    have hHtop : H = ⊤ := by
      calc
        H = (H.conjBy g).conjBy g⁻¹ := (section12_conjBy_inv_local (G := G) H g).symm
        _ = (⊤ : Subgroup G).conjBy g⁻¹ := by rw [htop]
        _ = ⊤ := section12_top_conjBy_local (G := G) g⁻¹
    exact hHproper hHtop
  · ext N
    constructor
    · intro hN
      have hNinv_max : N.conjBy g⁻¹ ∈ section9MaximalSubgroups G :=
        section12_maximal_conjBy_local (G := G) hN.1 g⁻¹
      have hH_le_Ninv : H ≤ N.conjBy g⁻¹ :=
        section12_le_conjBy_inv_of_conjBy_le_local (G := G) hN.2
      have hNinv_cont : N.conjBy g⁻¹ ∈ section9MaximalSubgroupsContaining H :=
        ⟨hNinv_max, hH_le_Ninv⟩
      have hNinv_eq : N.conjBy g⁻¹ = M := by
        have hsingle : N.conjBy g⁻¹ ∈ ({M} : Set (Subgroup G)) := by
          simpa [hMuniq] using hNinv_cont
        simpa using hsingle
      have hN_eq : N = M.conjBy g := by
        calc
          N = (N.conjBy g⁻¹).conjBy g := (section12_conjBy_inv'_local (G := G) N g).symm
          _ = M.conjBy g := by rw [hNinv_eq]
      simp [hN_eq]
    · intro hN
      have hN_eq : N = M.conjBy g := by simpa using hN
      subst N
      refine ⟨section12_maximal_conjBy_local (G := G) hMcont.1 g, ?_⟩
      exact Subgroup.map_mono hMcont.2

omit [IsMinCE G] in
private theorem CFSG.section12_inf_eq_bot_of_pSubgroup_and_pPrime_card_local
    {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hHp : IsPGroup p H) (hKcop : Nat.Coprime p (Nat.card K)) :
    H ⊓ K = ⊥ := by
  rcases hHp.exists_card_eq with ⟨n, hn⟩
  have hcop : Nat.Coprime (Nat.card H) (Nat.card K) := by
    rw [hn]
    exact Nat.Coprime.pow_left n hKcop
  exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot

omit [IsMinCE G] in
private theorem CFSG.section12_sylow_map_quotient_pPrimeCore_eq_top_of_hasNormalPComplement_local
    {p : ℕ} [Fact p.Prime]
    (hcomp : HasNormalPComplement p G) (S : Sylow p G) :
    (S : Subgroup G).map (QuotientGroup.mk' (pPrimeCore p G)) = ⊤ := by
  classical
  let N : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Q := G ⧸ N
  have hQp : IsPGroup p Q :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p) (H := G) hcomp
  let Tmap : Sylow p Q := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have htop_p : IsPGroup p (⊤ : Subgroup Q) := by
    simpa using hQp.to_subgroup (⊤ : Subgroup Q)
  let Ttop : Sylow p Q :=
    IsPGroup.toSylow (G := Q) (p := p) htop_p (by
      simpa using (Fact.out : Nat.Prime p).not_dvd_one)
  have hTtop_normal : (Ttop : Subgroup Q).Normal := by
    have hTtop_eq : (Ttop : Subgroup Q) = ⊤ := by
      dsimp [Ttop]
    rw [hTtop_eq]
    infer_instance
  have : Unique (Sylow p Q) := Sylow.unique_of_normal Ttop hTtop_normal
  have hSylow_eq : Tmap = Ttop := Subsingleton.elim _ _
  change (Tmap : Subgroup Q) = ⊤
  simpa [Tmap, Ttop, IsPGroup.toSylow_coe, q, N, Q] using
    congrArg (fun P : Sylow p Q => (P : Subgroup Q)) hSylow_eq

omit [IsMinCE G] in
private noncomputable def CFSG.section12_quotientPPrimeCoreEquivSylowOfHasNormalPComplement_local
    {p : ℕ} [Fact p.Prime]
    (hcomp : HasNormalPComplement p G) (S : Sylow p G) :
    (G ⧸ pPrimeCore p G) ≃* (S : Subgroup G) := by
  classical
  let N : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hSmap_top : (S : Subgroup G).map q = ⊤ := by
    simpa [q, N] using
      section12_sylow_map_quotient_pPrimeCore_eq_top_of_hasNormalPComplement_local
        (G := G) (p := p) hcomp S
  let qS : (S : Subgroup G) →* (S : Subgroup G).map q :=
    q.subgroupMap (S : Subgroup G)
  have hqS_surj : Function.Surjective qS :=
    MonoidHom.subgroupMap_surjective q (S : Subgroup G)
  have hqS_range_top : qS.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    exact hqS_surj
  have hN_cop : Nat.Coprime p (Nat.card N) := by
    simpa [N] using pPrimeCore_coprime_card (p := p) (G := G)
  have hS_inf_N : (S : Subgroup G) ⊓ N = ⊥ :=
    section12_inf_eq_bot_of_pSubgroup_and_pPrime_card_local
      (G := G) (p := p) S.isPGroup' hN_cop
  have hqS_ker : qS.ker = ⊥ := by
    have hker : qS.ker = N.subgroupOf (S : Subgroup G) := by
      simpa [qS, q, N, QuotientGroup.ker_mk'] using
        (Subgroup.ker_subgroupMap (f := q) (H := (S : Subgroup G)))
    rw [hker, Subgroup.subgroupOf_eq_bot, disjoint_iff]
    simpa [inf_comm] using hS_inf_N
  let eKer : (S : Subgroup G) ⧸ qS.ker ≃* (S : Subgroup G) :=
    (QuotientGroup.quotientMulEquivOfEq hqS_ker).trans QuotientGroup.quotientBot
  let eImage : (S : Subgroup G) ⧸ qS.ker ≃* (S : Subgroup G).map q :=
    (QuotientGroup.quotientKerEquivRange qS).trans
      ((MulEquiv.subgroupCongr hqS_range_top).trans Subgroup.topEquiv)
  let eTop : (S : Subgroup G).map q ≃* G ⧸ N :=
    (MulEquiv.subgroupCongr hSmap_top).trans Subgroup.topEquiv
  exact eTop.symm.trans (eImage.symm.trans eKer)

omit [IsMinCE G] in
private theorem CFSG.section12_sylow_isComplement_pPrimeCore_of_hasNormalPComplement_local
    {p : ℕ} [Fact p.Prime]
    (hcomp : HasNormalPComplement p G) (S : Sylow p G) :
    (S : Subgroup G).IsComplement' (pPrimeCore p G) := by
  classical
  let N : Subgroup G := pPrimeCore p G
  let e : (G ⧸ N) ≃* (S : Subgroup G) :=
    section12_quotientPPrimeCoreEquivSylowOfHasNormalPComplement_local
      (G := G) (p := p) hcomp S
  have hcard_quot : Nat.card (G ⧸ N) = Nat.card (S : Subgroup G) :=
    Nat.card_congr e.toEquiv
  have hcard_mul : Nat.card (S : Subgroup G) * Nat.card N = Nat.card G := by
    calc
      Nat.card (S : Subgroup G) * Nat.card N =
          Nat.card (G ⧸ N) * Nat.card N := by rw [hcard_quot]
      _ = Nat.card G := (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := N)).symm
  have hcop : Nat.Coprime (Nat.card (S : Subgroup G)) (Nat.card N) := by
    rcases S.isPGroup'.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact Nat.Coprime.pow_left n (by
      simpa [N] using pPrimeCore_coprime_card (p := p) (G := G))
  simpa [N] using Subgroup.isComplement'_of_coprime hcard_mul hcop

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_quotient_mk_injective_on_complement_local
    {R : Type*} [Group R] {K N : Subgroup R} [N.Normal]
    (hcomp : K.IsComplement' N) {x y : K}
    (hxy : (QuotientGroup.mk' N (x : R) : R ⧸ N) = QuotientGroup.mk' N (y : R)) :
    x = y := by
  have hdiv : (x : R) * (y : R)⁻¹ ∈ N := by
    rw [← QuotientGroup.eq_one_iff (N := N)]
    simpa [map_mul, map_inv] using
      congrArg (fun q => q * (QuotientGroup.mk' N (y : R))⁻¹) hxy
  have hxyK : (x : R) * (y : R)⁻¹ ∈ K :=
    K.mul_mem x.property (K.inv_mem y.property)
  have htop : ((x : R) * (y : R)⁻¹ : R) = 1 :=
    Subgroup.disjoint_def.mp hcomp.disjoint hxyK hdiv
  exact Subtype.ext (mul_inv_eq_one.mp htop)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_quotient_equiv_complement_apply_local
    {R : Type*} [Group R] {K N : Subgroup R} [N.Normal]
    (hcomp : K.IsComplement' N) (x : K) :
    hcomp.QuotientMulEquiv (QuotientGroup.mk' N (x : R)) = x := by
  apply section12_quotient_mk_injective_on_complement_local hcomp
  rw [Subgroup.IsComplement'.QuotientMulEquiv_apply]
  exact Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv hcomp _

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_map_derived_quotient_local
    {R : Type*} [Group R] {N : Subgroup R} [N.Normal] :
    (derivedSubgroup R).map (QuotientGroup.mk' N) = derivedSubgroup (R ⧸ N) := by
  change (derivedSeries R 1).map (QuotientGroup.mk' N) = derivedSeries (R ⧸ N) 1
  exact map_derivedSeries_eq (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) 1

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_map_derived_mulEquiv_local
    {R S : Type*} [Group R] [Group S] (e : R ≃* S) :
    (derivedSubgroup R).map e.toMonoidHom = derivedSubgroup S := by
  change (derivedSeries R 1).map e.toMonoidHom = derivedSeries S 1
  exact map_derivedSeries_eq (f := e.toMonoidHom) e.surjective 1

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_complement_inf_derived_eq_local
    {R : Type*} [Group R] {K N : Subgroup R} [N.Normal]
    (hcomp : K.IsComplement' N) :
    K ⊓ derivedSubgroup R = (derivedSubgroup K).map K.subtype := by
  apply le_antisymm
  · intro x hx
    have hxK : x ∈ K := hx.1
    have hxder : x ∈ derivedSubgroup R := hx.2
    let q : R →* R ⧸ N := QuotientGroup.mk' N
    have hxq_der : q x ∈ derivedSubgroup (R ⧸ N) := by
      have hxmap : q x ∈ (derivedSubgroup R).map q := Subgroup.mem_map_of_mem q hxder
      change QuotientGroup.mk' N x ∈ derivedSubgroup (R ⧸ N)
      change QuotientGroup.mk' N x ∈ (derivedSubgroup R).map (QuotientGroup.mk' N) at hxmap
      rw [section12_map_derived_quotient_local (R := R) (N := N)] at hxmap
      exact hxmap
    let e : R ⧸ N ≃* K := hcomp.QuotientMulEquiv
    have hex_der : e (q x) ∈ derivedSubgroup K := by
      have hxmap : e (q x) ∈ (derivedSubgroup (R ⧸ N)).map e.toMonoidHom :=
        Subgroup.mem_map_of_mem e.toMonoidHom hxq_der
      change hcomp.QuotientMulEquiv ((QuotientGroup.mk' N) x) ∈ derivedSubgroup K
      change hcomp.QuotientMulEquiv ((QuotientGroup.mk' N) x) ∈
        (derivedSubgroup (R ⧸ N)).map hcomp.QuotientMulEquiv.toMonoidHom at hxmap
      rw [section12_map_derived_mulEquiv_local
          (R := R ⧸ N) (S := K) hcomp.QuotientMulEquiv] at hxmap
      exact hxmap
    have heqx : e (q x) = ⟨x, hxK⟩ :=
      section12_quotient_equiv_complement_apply_local hcomp ⟨x, hxK⟩
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    simpa [heqx] using hex_der
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    constructor
    · exact (y : K).property
    · exact (map_derivedSeries_le_derivedSeries K.subtype 1)
        (Subgroup.mem_map_of_mem K.subtype hy)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_subgroupCentralizerIn_subgroupOf_eq_local
    {P X : Subgroup G} (hXP : X ≤ P) :
    (subgroupCentralizerIn P X).subgroupOf P =
      Subgroup.centralizer ((X.subgroupOf P : Subgroup P) : Set P) := by
  ext y
  constructor
  · intro hy
    change ((y : P) : G) ∈ subgroupCentralizerIn P X at hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxX : ((x : P) : G) ∈ X := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hcommG :=
      Subgroup.mem_centralizer_iff.mp hy.2 ((x : P) : G) hxX
    exact Subtype.ext hcommG
  · intro hy
    change ((y : P) : G) ∈ subgroupCentralizerIn P X
    refine ⟨y.property, ?_⟩
    change ((y : P) : G) ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    let xP : P := ⟨x, hXP hx⟩
    have hxsub : xP ∈ X.subgroupOf P := by
      simpa [xP, Subgroup.mem_subgroupOf] using hx
    exact congrArg (fun z : P => (z : G))
      (Subgroup.mem_centralizer_iff.mp hy xP hxsub)

omit [Finite G] [IsMinCE G] in
private noncomputable def CFSG.section12_centralizerSubgroupOfEquivSubgroupCentralizerIn_local
    {P X : Subgroup G} (hXP : X ≤ P) :
    Subgroup.centralizer ((X.subgroupOf P : Subgroup P) : Set P) ≃*
      subgroupCentralizerIn P X :=
  (MulEquiv.subgroupCongr
      (section12_subgroupCentralizerIn_subgroupOf_eq_local (G := G) hXP).symm).trans
    (Subgroup.subgroupOfEquivOfLe (H := subgroupCentralizerIn P X) (K := P)
      (by
        intro x hx
        exact hx.1))

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_ambientDerivedSubgroup_eq_bot_of_isMulCommutative_local
    {P : Subgroup G} (hcomm : IsMulCommutative P) :
    ambientDerivedSubgroup P = ⊥ := by
  classical
  have : IsMulCommutative P := hcomm
  have htop_cent :
      (⊤ : Subgroup P) ≤ Subgroup.centralizer ((⊤ : Subgroup P) : Set P) := by
    intro x _hx
    rw [Subgroup.mem_centralizer_iff]
    intro y _hy
    exact (setLike_mul_comm
      (s := (⊤ : Subgroup P)) (by simp) (by simp)).symm
  have hcomm_bot : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).2 htop_cent
  have hder_bot : derivedSubgroup P = ⊥ := by
    simpa [derivedSubgroup, derivedSeries_one] using hcomm_bot
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hybot : y ∈ (⊥ : Subgroup P) := by
      rw [← hder_bot]
      exact hy
    have hy_one : y = 1 := Subgroup.mem_bot.mp hybot
    simpa using congrArg (fun z : P => (z : G)) hy_one
  · intro hx
    subst x
    exact Subgroup.one_mem _


omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_commutator_mul_mul_of_commute_local
    {R : Type*} [Group R] {q₁ q₂ y₁ y₂ : R}
    (hq₁y₂ : q₁ * y₂ = y₂ * q₁)
    (hy₁q₂ : y₁ * q₂ = q₂ * y₁)
    (hy₁y₂ : y₁ * y₂ = y₂ * y₁) :
    ⁅q₁ * y₁, q₂ * y₂⁆ = ⁅q₁, q₂⁆ := by
  have hc₁ : Commute q₁ y₂ := by exact hq₁y₂
  have hc₂ : Commute y₁ q₂ := by exact hy₁q₂
  have hc₃ : Commute y₁ y₂ := by exact hy₁y₂
  change
    q₁ * y₁ * (q₂ * y₂) * (q₁ * y₁)⁻¹ * (q₂ * y₂)⁻¹ =
      q₁ * q₂ * q₁⁻¹ * q₂⁻¹
  rw [mul_inv_rev, mul_inv_rev]
  calc
    q₁ * y₁ * (q₂ * y₂) * (y₁⁻¹ * q₁⁻¹) * (y₂⁻¹ * q₂⁻¹)
        = q₁ * y₁ * q₂ * y₂ * y₁⁻¹ * q₁⁻¹ * y₂⁻¹ * q₂⁻¹ := by
            simp [mul_assoc]
    _ 
        = q₁ * (y₁ * q₂) * y₂ * y₁⁻¹ * q₁⁻¹ * y₂⁻¹ * q₂⁻¹ := by
            simp [mul_assoc]
    _ = q₁ * (q₂ * y₁) * y₂ * y₁⁻¹ * q₁⁻¹ * y₂⁻¹ * q₂⁻¹ := by
            rw [hc₂.eq]
    _ = q₁ * q₂ * (y₁ * y₂) * y₁⁻¹ * q₁⁻¹ * y₂⁻¹ * q₂⁻¹ := by
            simp [mul_assoc]
    _ = q₁ * q₂ * (y₂ * y₁) * y₁⁻¹ * q₁⁻¹ * y₂⁻¹ * q₂⁻¹ := by
            rw [hc₃.eq]
    _ = q₁ * q₂ * y₂ * q₁⁻¹ * y₂⁻¹ * q₂⁻¹ := by
            simp [mul_assoc]
    _ = q₁ * q₂ * (y₂ * q₁⁻¹) * y₂⁻¹ * q₂⁻¹ := by
            simp [mul_assoc]
    _ = q₁ * q₂ * (q₁⁻¹ * y₂) * y₂⁻¹ * q₂⁻¹ := by
            rw [(hc₁.inv_left.symm).eq]
    _ = q₁ * q₂ * q₁⁻¹ * q₂⁻¹ := by
            simp [mul_assoc]


omit [IsMinCE G] in
private theorem CFSG.section12_derived_le_center_of_specialShape_type_local
    {R : Type*} [Group R] [Finite R] {p : Nat.Primes}
    (hshape : section10SpecialRankTwoSylowShape (H := R) p) :
    derivedSubgroup R ≤ Subgroup.center R := by
  classical
  rcases hshape with
    ⟨Q, Y, hQcard, hQnoncomm, hQexp, hYcyc, hcentral, _hΩeq⟩
  have : Fact p.val.Prime := ⟨p.property⟩
  have hQp : IsPGroup p.val Q := IsPGroup.of_card (n := 3) hQcard
  let : Fact (IsPGroup p.val Q) := ⟨hQp⟩
  have hQextra : IsExtraspecial p.val Q :=
    isExtraspecial_of_noncommutative_card_p3_exponent_p
      (K := Q) (p := p.val) hQcard hQexp hQnoncomm
  let : IsExtraspecial p.val Q := hQextra
  have hder_center :
      (derivedSubgroup Q).map Q.subtype =
        (Subgroup.center Q).map Q.subtype :=
    derivedSubgroup_map_subtype_eq_center_map_subtype_of_isExtraspecial
      (R := R) (p := p.val) Q
  have hder_le_centerQ : derivedSubgroup R ≤ (Subgroup.center Q).map Q.subtype := by
    rcases hcentral with ⟨_hQnorm, _hYnorm, hcommQY, hsupQY⟩
    have hQ_le_centY : Q ≤ Subgroup.centralizer (Y : Set R) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Q) (H₂ := Y)).1
        hcommQY
    have hYQ_bot : ⁅Y, Q⁆ = ⊥ := by
      simpa [Subgroup.commutator_comm] using hcommQY
    have hY_le_centQ : Y ≤ Subgroup.centralizer (Q : Set R) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Y) (H₂ := Q)).1
        hYQ_bot
    let : IsCyclic Y := hYcyc
    change ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ ≤ (Subgroup.center Q).map Q.subtype
    rw [Subgroup.commutator_le]
    intro a _ha b _hb
    have ha_sup : a ∈ Q ⊔ Y := by
      rw [hsupQY]
      exact Subgroup.mem_top a
    have hb_sup : b ∈ Q ⊔ Y := by
      rw [hsupQY]
      exact Subgroup.mem_top b
    rcases (Subgroup.mem_sup_of_normal_left (x := a) (s := Q) (t := Y)).1 ha_sup with
      ⟨q₁, hq₁, y₁, hy₁, hq₁y₁⟩
    rcases (Subgroup.mem_sup_of_normal_left (x := b) (s := Q) (t := Y)).1 hb_sup with
      ⟨q₂, hq₂, y₂, hy₂, hq₂y₂⟩
    have hq₁_y₂ : q₁ * y₂ = y₂ * q₁ :=
      (Subgroup.mem_centralizer_iff.mp (hQ_le_centY hq₁) y₂ hy₂).symm
    have hy₁_q₂ : y₁ * q₂ = q₂ * y₁ :=
      (Subgroup.mem_centralizer_iff.mp (hY_le_centQ hy₁) q₂ hq₂).symm
    have hy₁_y₂ : y₁ * y₂ = y₂ * y₁ := by
      exact congrArg (fun z : Y => (z : R))
        (mul_comm (⟨y₁, hy₁⟩ : Y) (⟨y₂, hy₂⟩ : Y))
    have hcomm_eq : ⁅a, b⁆ = ⁅q₁, q₂⁆ := by
      have hraw :=
        section12_commutator_mul_mul_of_commute_local
          (R := R) hq₁_y₂ hy₁_q₂ hy₁_y₂
      simpa [← hq₁y₁, ← hq₂y₂] using hraw
    have hqcomm_der :
        ⁅q₁, q₂⁆ ∈ (derivedSubgroup Q).map Q.subtype := by
      refine Subgroup.mem_map.mpr
        ⟨⁅(⟨q₁, hq₁⟩ : Q), (⟨q₂, hq₂⟩ : Q)⁆, ?_, ?_⟩
      · change ⁅(⟨q₁, hq₁⟩ : Q), (⟨q₂, hq₂⟩ : Q)⁆ ∈
          ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆
        exact Subgroup.commutator_mem_commutator (by simp) (by simp)
      · simp [commutatorElement_def]
    have hqcomm_center : ⁅q₁, q₂⁆ ∈ (Subgroup.center Q).map Q.subtype := by
      rw [← hder_center]
      exact hqcomm_der
    simpa [hcomm_eq] using hqcomm_center
  intro x hx
  have hxcenterQ : x ∈ (Subgroup.center Q).map Q.subtype := hder_le_centerQ hx
  rcases Subgroup.mem_map.mp hxcenterQ with ⟨z, hzcenter, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro w
  rcases hcentral with ⟨_hQnorm, _hYnorm, hcommQY, hsupQY⟩
  have hw_sup : w ∈ Q ⊔ Y := by
    rw [hsupQY]
    exact Subgroup.mem_top w
  rcases (Subgroup.mem_sup_of_normal_left (x := w) (s := Q) (t := Y)).1 hw_sup with
    ⟨q, hq, y, hy, hqy⟩
  have hzq_comm : (z : R) * q = q * (z : R) := by
    have hzq := congrArg (fun u : Q => (u : R))
      (Subgroup.mem_center_iff.mp hzcenter ⟨q, hq⟩)
    simpa using hzq.symm
  have hzy_comm : (z : R) * y = y * (z : R) := by
    have hQ_le_centY : Q ≤ Subgroup.centralizer (Y : Set R) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Q) (H₂ := Y)).1
        hcommQY
    exact (Subgroup.mem_centralizer_iff.mp (hQ_le_centY z.property) y hy).symm
  calc
    w * (z : R) = (q * y) * (z : R) := by rw [hqy]
    _ = q * (y * (z : R)) := by simp [mul_assoc]
    _ = q * ((z : R) * y) := by rw [← hzy_comm]
    _ = (q * (z : R)) * y := by simp [mul_assoc]
    _ = ((z : R) * q) * y := by rw [← hzq_comm]
    _ = (z : R) * (q * y) := by simp [mul_assoc]
    _ = (z : R) * w := by rw [hqy]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_derived_le_center_of_mulEquiv_local
    {R S : Type*} [Group R] [Group S] (e : R ≃* S)
    (hder : derivedSubgroup R ≤ Subgroup.center R) :
    derivedSubgroup S ≤ Subgroup.center S := by
  intro x hx
  have hxpre : e.symm x ∈ derivedSubgroup R := by
    have hxmap : e.symm x ∈ (derivedSubgroup S).map e.symm.toMonoidHom :=
      Subgroup.mem_map_of_mem e.symm.toMonoidHom hx
    rw [section12_map_derived_mulEquiv_local (R := S) (S := R) e.symm] at hxmap
    exact hxmap
  have hcenter_pre : e.symm x ∈ Subgroup.center R := hder hxpre
  rw [Subgroup.mem_center_iff]
  intro y
  have hcomm_pre := Subgroup.mem_center_iff.mp hcenter_pre (e.symm y)
  exact (by simpa using congrArg e hcomm_pre)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_ambientDerived_le_centralizer_of_derived_le_center_local
    {P : Subgroup G} (hder : derivedSubgroup P ≤ Subgroup.center P) :
    ambientDerivedSubgroup P ≤ Subgroup.centralizer (P : Set G) := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  have hycenter : y ∈ Subgroup.center P := hder hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact congrArg (fun t : P => (t : G))
    (Subgroup.mem_center_iff.mp hycenter ⟨z, hz⟩)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_hasNormalPComplement_msigma_ambient_local
    {M : Subgroup G} {p : ℕ}
    (hcomp : HasNormalPComplement p (section10MsigmaSubgroup M)) :
    HasNormalPComplement p (section10Msigma M) := by
  let e : section10MsigmaSubgroup M ≃* section10Msigma M :=
    Subgroup.equivMapOfInjective (f := M.subtype)
      (section10MsigmaSubgroup M) M.subtype_injective
  simpa [section10Msigma] using
    hasNormalPComplement_of_equiv p e hcomp

omit [IsMinCE G] in
private theorem CFSG.section12_sylow_le_normal_hall_of_mem_local
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} {S : Subgroup H}
    [S.Normal] (hSHall : IsHallSubgroup π S) {p : Nat.Primes} (hpπ : p ∈ π)
    (P : Sylow p.val H) :
    (P : Subgroup H) ≤ S := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let PS : Sylow p.val S := Classical.choice (Sylow.nonempty (p := p.val) (G := S))
  let Psub : Subgroup H := (PS : Subgroup S).map S.subtype
  have hPsub_p : IsPGroup p.val Psub := by
    exact IsPGroup.map (p := p.val) (H := (PS : Subgroup S)) PS.isPGroup' S.subtype
  have hp_not_S_index : ¬ p.val ∣ S.index := by
    intro hp_dvd
    exact (hSHall.p_in_pi_of_p_dvd_index p hp_dvd) hpπ
  have hp_not_Psub_index : ¬ p.val ∣ Psub.index := by
    intro hp_dvd
    have hidx : Psub.index = (PS : Subgroup S).index * S.index := by
      simpa [Psub] using (Subgroup.index_map_subtype (H := S) (K := (PS : Subgroup S)))
    have hp_prod : p.val ∣ (PS : Subgroup S).index * S.index := by
      simpa [hidx] using hp_dvd
    rcases p.property.dvd_or_dvd hp_prod with hp_PS | hp_S
    · exact PS.not_dvd_index hp_PS
    · exact hp_not_S_index hp_S
  let Q : Sylow p.val H := hPsub_p.toSylow hp_not_Psub_index
  have hQ_le_S : (Q : Subgroup H) ≤ S := by
    intro x hx
    have hxPsub : x ∈ Psub := by
      simpa [Q, IsPGroup.toSylow_coe] using hx
    rcases Subgroup.mem_map.mp hxPsub with ⟨y, _hy, rfl⟩
    exact y.property
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q P
  have hgQ_le_S : ((g • Q : Sylow p.val H) : Subgroup H) ≤ S := by
    intro x hx
    rw [Sylow.coe_subgroup_smul] at hx
    have hx' : g⁻¹ * x * g ∈ (Q : Subgroup H) := by
      simpa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        MulAut.conj_apply, mul_assoc] using hx
    have hxS' : g⁻¹ * x * g ∈ S := hQ_le_S hx'
    simpa [mul_assoc] using ((inferInstance : S.Normal).conj_mem (g⁻¹ * x * g) hxS' g)
  simpa [hg] using hgQ_le_S

omit [IsMinCE G] in
public theorem CFSG.section12_exists_pSubgroup_gt_le_normalizer_of_lt_pgroup_local
    {S X : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hSp : IsPGroup p S) (hXS : X < S) :
    ∃ Y : Subgroup G,
      X < Y ∧ Y ≤ S ∧ Y ≤ Subgroup.normalizer (X : Set G) ∧ IsPGroup p Y := by
  classical
  have hX_le_S : X ≤ S := hXS.le
  let XS : Subgroup S := X.subgroupOf S
  have hXS_lt_top : XS < ⊤ := by
    refine ⟨le_top, ?_⟩
    intro htop
    have hS_le_X : S ≤ X := by
      intro x hxS
      let xS : S := ⟨x, hxS⟩
      have hxXS : xS ∈ XS := htop (by simp)
      simpa [XS, Subgroup.mem_subgroupOf, xS] using hxXS
    exact hXS.ne (le_antisymm hX_le_S hS_le_X)
  have hnc : NormalizerCondition S := by
    let : Group.IsNilpotent S := IsPGroup.isNilpotent (p := p) (G := S) hSp
    exact Group.normalizerCondition_of_isNilpotent (G := S)
  let NS : Subgroup S := Subgroup.normalizer (XS : Set S)
  have hXS_lt_NS : XS < NS := by
    simpa [NS] using hnc XS hXS_lt_top
  let Y : Subgroup G := NS.map S.subtype
  have hX_le_Y : X ≤ Y := by
    intro x hx
    have hxS : x ∈ S := hX_le_S hx
    let xS : S := ⟨x, hxS⟩
    have hxXS : xS ∈ XS := by
      simpa [XS, Subgroup.mem_subgroupOf, xS] using hx
    have hxNS : xS ∈ NS := Subgroup.le_normalizer hxXS
    exact Subgroup.mem_map_of_mem S.subtype hxNS
  have hY_not_le_X : ¬ Y ≤ X := by
    intro hYX
    apply hXS_lt_NS.not_ge
    intro y hyNS
    have hyY : (y : G) ∈ Y := Subgroup.mem_map_of_mem S.subtype hyNS
    have hyX : (y : G) ∈ X := hYX hyY
    simpa [XS, Subgroup.mem_subgroupOf] using hyX
  have hY_le_S : Y ≤ S := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨yS, _hyNS, rfl⟩
    exact yS.property
  have hY_le_normX : Y ≤ Subgroup.normalizer (X : Set G) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨yS, hyNS, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hyNorm := Subgroup.mem_normalizer_iff.mp hyNS
    constructor
    · intro hzX
      have hzS : z ∈ S := hX_le_S hzX
      let zS : S := ⟨z, hzS⟩
      have hzXS : zS ∈ XS := by
        simpa [XS, Subgroup.mem_subgroupOf, zS] using hzX
      have hzImage : yS * zS * yS⁻¹ ∈ XS := (hyNorm zS).1 hzXS
      simpa [XS, Subgroup.mem_subgroupOf, zS, mul_assoc] using hzImage
    · intro hzConjX
      have hzConjS : (yS : G) * z * (yS : G)⁻¹ ∈ S := hX_le_S hzConjX
      have hzS : z ∈ S := by
        have hyS : (yS : G) ∈ S := yS.property
        have hyinvS : (yS : G)⁻¹ ∈ S := S.inv_mem hyS
        have hz' : (yS : G)⁻¹ * ((yS : G) * z * (yS : G)⁻¹) * (yS : G) ∈ S :=
          S.mul_mem (S.mul_mem hyinvS hzConjS) hyS
        simpa [mul_assoc] using hz'
      let zS : S := ⟨z, hzS⟩
      have hzConjXS : yS * zS * yS⁻¹ ∈ XS := by
        simpa [XS, Subgroup.mem_subgroupOf, zS, mul_assoc] using hzConjX
      have hzXS : zS ∈ XS := (hyNorm zS).2 hzConjXS
      simpa [XS, Subgroup.mem_subgroupOf, zS] using hzXS
  have hYp : IsPGroup p Y := by
    have hNSp : IsPGroup p NS := hSp.to_subgroup NS
    simpa [Y] using IsPGroup.map (p := p) (H := NS) hNSp S.subtype
  exact ⟨Y, ⟨hX_le_Y, hY_not_le_X⟩, hY_le_S, hY_le_normX, hYp⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_sylow_ambient_not_lt_pSubgroup_le_local
    {M Y : Subgroup G} {p : Nat.Primes} (P : Sylow p.val M)
    (hPGY : section10AmbientSylowSubgroup M P < Y)
    (hYM : Y ≤ M) (hYp : IsPGroup p.val Y) :
    False := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let YM : Subgroup M := Y.subgroupOf M
  have hYMp : IsPGroup p.val YM :=
    hYp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := Y) (K := M) hYM).symm
  have hP_le_YM : (P : Subgroup M) ≤ YM := by
    intro y hyP
    change (y : G) ∈ Y
    apply hPGY.le
    exact Subgroup.mem_map_of_mem M.subtype hyP
  have hYM_eq : YM = (P : Subgroup M) := P.is_maximal' hYMp hP_le_YM
  have hY_le_PG : Y ≤ section10AmbientSylowSubgroup M P := by
    intro y hyY
    have hyM : y ∈ M := hYM hyY
    let yM : M := ⟨y, hyM⟩
    have hyYM : yM ∈ YM := by
      simpa [YM, Subgroup.mem_subgroupOf, yM] using hyY
    have hyP : yM ∈ (P : Subgroup M) := by
      simpa [hYM_eq] using hyYM
    exact Subgroup.mem_map_of_mem M.subtype hyP
  exact hPGY.not_ge hY_le_PG

omit [IsMinCE G] in
private theorem CFSG.section12_sigma_ambient_sylow_eq_of_le_sylow_local
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∈ section10SigmaPrimes M) (P : Sylow p.val M)
    (S : Sylow p.val G)
    (hPGS : section10AmbientSylowSubgroup M P ≤ (S : Subgroup G)) :
    (S : Subgroup G) = section10AmbientSylowSubgroup M P := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  by_contra hne
  have hPG_lt_S : PG < (S : Subgroup G) := by
    refine ⟨by simpa [PG] using hPGS, ?_⟩
    intro hS_le_PG
    exact hne (le_antisymm hS_le_PG (by simpa [PG] using hPGS))
  rcases section12_exists_pSubgroup_gt_le_normalizer_of_lt_pgroup_local
      (G := G) (S := (S : Subgroup G)) (X := PG) (p := p.val)
      S.isPGroup' hPG_lt_S with
    ⟨Y, hPGY, _hYS, hYnorm, hYp⟩
  have hnorm_le_M :
      Subgroup.normalizer (PG : Set G) ≤ M := by
    intro g hg
    have hconj_eq : PG.conjBy g = PG := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.conjBy, Subgroup.mem_map] at hx
        rcases hx with ⟨y, hyPG, hyx⟩
        have hg_norm := Subgroup.mem_normalizer_iff.mp hg y
        have hy' : g * y * g⁻¹ ∈ PG := (hg_norm.1 hyPG)
        have hyx' : g * y * g⁻¹ = x := by
          simpa [MulAut.conj_apply] using hyx
        simpa [hyx'] using hy'
      · intro hx
        rw [Subgroup.conjBy, Subgroup.mem_map]
        refine ⟨g⁻¹ * x * g, ?_, ?_⟩
        · have hg_norm := Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)
          have hx' : g * (g⁻¹ * x * g) * g⁻¹ ∈ PG := by
            simpa [mul_assoc] using hx
          exact (hg_norm.2 hx')
        · simp [MulAut.conj_apply, mul_assoc]
    have hconj_le_M : PG.conjBy g ≤ M := by
      have hPG_le_M : PG ≤ M := by
        intro x hx
        change x ∈ section10AmbientSylowSubgroup M P at hx
        rw [section10AmbientSylowSubgroup, Subgroup.mem_map] at hx
        rcases hx with ⟨y, _hy, rfl⟩
        exact y.property
      simpa [hconj_eq, PG] using hPG_le_M
    exact theorem_10_1_d (G := G) hM hpσ P hconj_le_M
  have hYM : Y ≤ M := hYnorm.trans hnorm_le_M
  exact section12_sylow_ambient_not_lt_pSubgroup_le_local
    (G := G) P (by simpa [PG] using hPGY) hYM hYp

omit [IsMinCE G] in
private theorem CFSG.section12_le_ambientDerived_sylow_of_le_ambientDerived_of_hasNormalPComplement_local
    {K X : Subgroup G} {p : Nat.Primes} (S : Sylow p.val K)
    (hXleS : X ≤ section10AmbientSylowSubgroup K S)
    (hXder : X ≤ ambientDerivedSubgroup K)
    (hcomp : HasNormalPComplement p.val K) :
    X ≤ ambientDerivedSubgroup (section10AmbientSylowSubgroup K S) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let Pamb : Subgroup G := section10AmbientSylowSubgroup K S
  have hScomp : (S : Subgroup K).IsComplement' (pPrimeCore p.val K) :=
    section12_sylow_isComplement_pPrimeCore_of_hasNormalPComplement_local
      (G := K) (p := p.val) hcomp S
  have hInter :
      (S : Subgroup K) ⊓ derivedSubgroup K =
        (derivedSubgroup (S : Subgroup K)).map (S : Subgroup K).subtype :=
    section12_complement_inf_derived_eq_local
      (R := K) (K := (S : Subgroup K)) (N := pPrimeCore p.val K) hScomp
  intro x hx
  have hxPamb : x ∈ Pamb := hXleS hx
  have hxK : x ∈ K := by
    change x ∈ (S : Subgroup K).map K.subtype at hxPamb
    rcases Subgroup.mem_map.mp hxPamb with ⟨y, _hy, rfl⟩
    exact y.property
  let xK : K := ⟨x, hxK⟩
  have hxS : xK ∈ (S : Subgroup K) := by
    change x ∈ (S : Subgroup K).map K.subtype at hxPamb
    rcases Subgroup.mem_map.mp hxPamb with ⟨y, hy, hyx⟩
    have hy_eq : y = xK := by
      apply Subtype.ext
      simpa [xK] using hyx
    simpa [hy_eq] using hy
  have hxKder : xK ∈ derivedSubgroup K := by
    rcases Subgroup.mem_map.mp (hXder hx) with ⟨y, hy, hyx⟩
    have hy_eq : y = xK := by
      apply Subtype.ext
      simpa [xK] using hyx
    simpa [hy_eq] using hy
  have hxinf : xK ∈ ((S : Subgroup K) ⊓ derivedSubgroup K : Subgroup K) :=
    ⟨hxS, hxKder⟩
  have hxmap :
      xK ∈ (derivedSubgroup (S : Subgroup K)).map (S : Subgroup K).subtype := by
    rw [hInter] at hxinf
    exact hxinf
  rcases Subgroup.mem_map.mp hxmap with ⟨s, hsder, hsxK⟩
  let e : (S : Subgroup K) ≃* Pamb :=
    Subgroup.equivMapOfInjective (f := K.subtype) (S : Subgroup K) K.subtype_injective
  have hes_der : e s ∈ derivedSubgroup Pamb := by
    exact (map_derivedSeries_le_derivedSeries e.toMonoidHom 1)
      (Subgroup.mem_map_of_mem e.toMonoidHom hsder)
  refine Subgroup.mem_map.mpr ⟨e s, hes_der, ?_⟩
  have hsG : ((s : K) : G) = x := by
    have hsx : (s : K) = xK := hsxK
    simpa [xK] using congrArg (fun y : K => (y : G)) hsx
  change ((e s : Pamb) : G) = x
  change ((s : K) : G) = x
  exact hsG

private theorem CFSG.section12_corollary_12_14_derived_chosen_core
    {M X : Subgroup G} {p : Nat.Primes} (P : Sylow p.val (section10Msigma M))
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section10SigmaPrimes M)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p M)
    (hXleP : X ≤ section10AmbientSylowSubgroup (section10Msigma M) P)
    (hXder : X ≤ ambientDerivedSubgroup (section10Msigma M))
    (hcomp : HasNormalPComplement p.val (section10MsigmaSubgroup M)) :
    section10AmbientSylowSubgroup (section10Msigma M) P ∈ section9UniqueSubgroups G ∧
      section10AmbientSylowSubgroup (section10Msigma M) P ≤ M ∧
      (∃ U : Subgroup G,
        U ∈ section9UniqueSubgroups G ∧
          U ≤ Subgroup.centralizer (X : Set G) ∧
          U ≤ M) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let Pamb : Subgroup G := section10AmbientSylowSubgroup (section10Msigma M) P
  let C : Subgroup G := subgroupCentralizerIn Pamb X
  let Xsub : Subgroup Pamb := X.subgroupOf Pamb
  have hPamb_le_M : Pamb ≤ M := by
    intro x hx
    change x ∈ (P : Subgroup (section10Msigma M)).map (section10Msigma M).subtype at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    have hσM : section10Msigma M ≤ M := by
      simpa [section10Msigma] using Subgroup.map_subtype_le (section10MsigmaSubgroup M)
    exact hσM y.property
  have hPamb_p : IsPGroup p.val Pamb := by
    change IsPGroup p.val
      ((P : Subgroup (section10Msigma M)).map (section10Msigma M).subtype)
    exact IsPGroup.map P.isPGroup' (section10Msigma M).subtype
  have hPamb_proper : Pamb ≠ ⊤ :=
    IsMinCE.pSubgroup_ne_top (G := G) (p := p.val) hPamb_p
  have hcompAmb : HasNormalPComplement p.val (section10Msigma M) :=
    section12_hasNormalPComplement_msigma_ambient_local
      (G := G) (M := M) (p := p.val) hcomp
  have hXderP : X ≤ ambientDerivedSubgroup Pamb := by
    simpa [Pamb] using
      section12_le_ambientDerived_sylow_of_le_ambientDerived_of_hasNormalPComplement_local
        (G := G) (K := section10Msigma M) (X := X) (p := p) P
        hXleP hXder hcompAmb
  have hXne : X ≠ ⊥ := section12_primeOrder_ne_bot (G := G) hX
  have hPamb_nonab : ¬ IsMulCommutative Pamb := by
    intro hcomm
    have hder_bot : ambientDerivedSubgroup Pamb = ⊥ :=
      section12_ambientDerivedSubgroup_eq_bot_of_isMulCommutative_local
        (G := G) hcomm
    have hX_le_bot : X ≤ ⊥ := by
      intro x hx
      have hxder : x ∈ ambientDerivedSubgroup Pamb := hXderP hx
      simpa [hder_bot] using hxder
    exact hXne (le_antisymm hX_le_bot bot_le)
  have hPamb_unique : Pamb ∈ section9UniqueSubgroups G :=
    theorem_12_13 (G := G) (P := Pamb) (p := p) hPamb_p hPamb_nonab
  have hC_le_Pamb : C ≤ Pamb := by
    intro x hx
    have hx' : x ∈ Pamb ∧ x ∈ Subgroup.centralizer (X : Set G) := by
      simpa [C, subgroupCentralizerIn] using hx
    exact hx'.1
  have hC_le_CX : C ≤ Subgroup.centralizer (X : Set G) := by
    intro x hx
    have hx' : x ∈ Pamb ∧ x ∈ Subgroup.centralizer (X : Set G) := by
      simpa [C, subgroupCentralizerIn] using hx
    exact hx'.2
  have hC_le_M : C ≤ M := hC_le_Pamb.trans hPamb_le_M
  have hC_proper : C ≠ ⊤ := by
    intro hCtop
    have htop_le_Pamb : (⊤ : Subgroup G) ≤ Pamb := by
      intro x hx
      apply hC_le_Pamb
      rw [hCtop]
      exact hx
    exact hPamb_proper (top_le_iff.mp htop_le_Pamb)
  have hU :
      ∃ U : Subgroup G,
        U ∈ section9UniqueSubgroups G ∧
          U ≤ Subgroup.centralizer (X : Set G) ∧
          U ≤ M := by
    by_cases hCrank_le_two : groupRank C ≤ 2
    · have hXsub_card : Nat.card Xsub = p.val := by
        simpa [Xsub] using (natCard_subgroupOf_eq X Pamb hXleP).trans hX.2
      let Csub : Subgroup Pamb := Subgroup.centralizer (Xsub : Set Pamb)
      have hCsub_rank_le_two : groupRank Csub ≤ 2 := by
        let e : Csub ≃* C := by
          simpa [C, Csub, Xsub] using
            section12_centralizerSubgroupOfEquivSubgroupCentralizerIn_local
              (G := G) (P := Pamb) (X := X) hXleP
        exact (groupRank_le_of_equiv e.symm).trans hCrank_le_two
      have hpG_dvd : p.val ∣ Nat.card G :=
        hp.1.trans (Subgroup.card_subgroup_dvd_card M)
      have hpodd : p.val ≠ 2 :=
        Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG_dvd
      have hXsub_le_der : Xsub ≤ derivedSubgroup Pamb := by
        intro x hx
        have hxX : ((x : Pamb) : G) ∈ X := by
          simpa [Xsub, Subgroup.mem_subgroupOf] using hx
        rcases Subgroup.mem_map.mp (hXderP hxX) with ⟨d, hd, hdx⟩
        have hdx' : d = x := by
          apply Subtype.ext
          exact hdx
        simpa [hdx'] using hd
      have hPamb_rank_le_two : groupRank Pamb ≤ 2 := by
        by_contra hnot
        have hPamb_rank_ge_three : 3 ≤ groupRank Pamb := by omega
        have hnarrow : IsNarrowPGroup p.val Pamb :=
          (corollary_5_4 (p := p.val) hpodd (R := Pamb) hPamb_p
            hPamb_rank_ge_three).mpr ⟨Xsub, hXsub_card, hCsub_rank_le_two⟩
        have h53 :=
          theorem_5_3_d (p := p.val) hpodd (R := Pamb) hnarrow
            hPamb_rank_ge_three (S := Xsub) hXsub_card (hS := hCsub_rank_le_two)
        have hXsub_bot : Xsub = ⊥ := by
          apply le_antisymm
          · intro x hx
            have hxinf : x ∈ Xsub ⊓ derivedSubgroup Pamb :=
              ⟨hx, hXsub_le_der hx⟩
            have hxbot : x ∈ (⊥ : Subgroup Pamb) := by
              rw [← h53.2.1]
              exact hxinf
            exact hxbot
          · exact bot_le
        have hcard_bot : Nat.card Xsub = 1 := by
          rw [hXsub_bot]
          simp
        have hp_one : p.val = 1 := by
          rw [← hXsub_card]
          exact hcard_bot
        exact p.property.ne_one hp_one
      let PsubM : Subgroup M := Pamb.subgroupOf M
      have hPsubM_p : IsPGroup p.val PsubM :=
        hPamb_p.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := Pamb) (K := M) hPamb_le_M).symm
      obtain ⟨PM, hPsubM_le_PM⟩ :=
        IsPGroup.exists_le_sylow (G := M) (p := p.val) hPsubM_p
      let PMamb : Subgroup G := section10AmbientSylowSubgroup M PM
      have hPM_le_sigmaSub : (PM : Subgroup M) ≤ section10MsigmaSubgroup M :=
        section12_sylow_le_normal_hall_of_mem_local
          (H := M) (π := section10SigmaPrimes M)
          (S := section10MsigmaSubgroup M) (theorem_10_2_b (G := G) hM).2 hp PM
      have hPMamb_le_sigma : PMamb ≤ section10Msigma M := by
        intro x hx
        change x ∈ (PM : Subgroup M).map M.subtype at hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hyPM, rfl⟩
        exact Subgroup.mem_map.mpr ⟨y, hPM_le_sigmaSub hyPM, rfl⟩
      have hPamb_le_PMamb : Pamb ≤ PMamb := by
        intro x hx
        have hxM : x ∈ M := hPamb_le_M hx
        let xM : M := ⟨x, hxM⟩
        have hxPsubM : xM ∈ PsubM := by
          simpa [PsubM, Subgroup.mem_subgroupOf, xM] using hx
        exact Subgroup.mem_map.mpr ⟨xM, hPsubM_le_PM hxPsubM, rfl⟩
      have hPMamb_p : IsPGroup p.val PMamb := by
        change IsPGroup p.val ((PM : Subgroup M).map M.subtype)
        exact IsPGroup.map PM.isPGroup' M.subtype
      let PMambSub : Subgroup (section10Msigma M) := PMamb.subgroupOf (section10Msigma M)
      have hPMambSub_p : IsPGroup p.val PMambSub :=
        hPMamb_p.of_equiv
          (Subgroup.subgroupOfEquivOfLe
            (H := PMamb) (K := section10Msigma M) hPMamb_le_sigma).symm
      have hP_le_PMambSub : (P : Subgroup (section10Msigma M)) ≤ PMambSub := by
        intro y hy
        change ((y : section10Msigma M) : G) ∈ PMamb
        exact hPamb_le_PMamb (Subgroup.mem_map_of_mem (section10Msigma M).subtype hy)
      have hPMambSub_eq : PMambSub = (P : Subgroup (section10Msigma M)) :=
        P.is_maximal' hPMambSub_p hP_le_PMambSub
      have hPMamb_le_Pamb : PMamb ≤ Pamb := by
        intro x hx
        have hxS : x ∈ section10Msigma M := hPMamb_le_sigma hx
        let xS : section10Msigma M := ⟨x, hxS⟩
        have hxSub : xS ∈ PMambSub := by
          simpa [PMambSub, Subgroup.mem_subgroupOf, xS] using hx
        have hxP : xS ∈ (P : Subgroup (section10Msigma M)) := by
          simpa [hPMambSub_eq] using hxSub
        exact Subgroup.mem_map_of_mem (section10Msigma M).subtype hxP
      have hPMamb_eq : PMamb = Pamb := le_antisymm hPMamb_le_Pamb hPamb_le_PMamb
      obtain ⟨Sg, hPamb_le_Sg⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hPamb_p
      have hSg_eq_Pamb : (Sg : Subgroup G) = Pamb := by
        have hPMamb_le_Sg : PMamb ≤ (Sg : Subgroup G) := by
          simpa [hPMamb_eq] using hPamb_le_Sg
        have hSg_eq_PMamb :
            (Sg : Subgroup G) = section10AmbientSylowSubgroup M PM :=
          section12_sigma_ambient_sylow_eq_of_le_sylow_local
            (G := G) (M := M) (p := p) hM hp PM Sg hPMamb_le_Sg
        simpa [PMamb, hPMamb_eq] using hSg_eq_PMamb
      let eSgPamb : (Sg : Subgroup G) ≃* Pamb := MulEquiv.subgroupCongr hSg_eq_Pamb
      have hSg_rank_le_two : groupRank (Sg : Subgroup G) ≤ 2 :=
        (groupRank_le_of_equiv eSgPamb.symm).trans hPamb_rank_le_two
      have hderSg_le_center :
          derivedSubgroup (Sg : Subgroup G) ≤ Subgroup.center (Sg : Subgroup G) := by
        rcases corollary_10_7_b (G := G) Sg hSg_rank_le_two with hScomm | hshape
        · have : IsMulCommutative (Sg : Subgroup G) := hScomm
          intro x _hx
          rw [Subgroup.mem_center_iff]
          intro y
          exact (setLike_mul_comm
            (s := (⊤ : Subgroup (Sg : Subgroup G))) (by simp) (by simp)).symm
        · exact section12_derived_le_center_of_specialShape_type_local
            (p := p) hshape
      have hderPamb_le_center :
          derivedSubgroup Pamb ≤ Subgroup.center Pamb := by
        exact section12_derived_le_center_of_mulEquiv_local
          (R := (Sg : Subgroup G)) (S := Pamb) eSgPamb hderSg_le_center
      have hPamb_le_CX : Pamb ≤ Subgroup.centralizer (X : Set G) := by
        have hder_cent :
            ambientDerivedSubgroup Pamb ≤ Subgroup.centralizer (Pamb : Set G) :=
          section12_ambientDerived_le_centralizer_of_derived_le_center_local
            (G := G) (P := Pamb) hderPamb_le_center
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxcent : x ∈ Subgroup.centralizer (Pamb : Set G) :=
          hder_cent (hXderP hx)
        exact (Subgroup.mem_centralizer_iff.mp hxcent y hy).symm
      exact ⟨Pamb, hPamb_unique, hPamb_le_CX, hPamb_le_M⟩
    · have hCrank_ge_three : 3 ≤ groupRank C := by omega
      have hC_unique : C ∈ section9UniqueSubgroups G :=
        theorem_9_6 (G := G) (K := C) hC_proper (by omega)
          (Or.inl hCrank_ge_three)
      exact ⟨C, hC_unique, hC_le_CX, hC_le_M⟩
  exact ⟨by simpa [Pamb] using hPamb_unique, by simpa [Pamb] using hPamb_le_M, hU⟩

private theorem CFSG.section12_corollary_12_14_derived_core
    {M X : Subgroup G} {p : Nat.Primes} (P : Sylow p.val (section10Msigma M))
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section10SigmaPrimes M)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p M)
    (hXder : X ≤ ambientDerivedSubgroup (section10Msigma M))
    (hcomp : HasNormalPComplement p.val (section10MsigmaSubgroup M)) :
    section10AmbientSylowSubgroup (section10Msigma M) P ∈ section9UniqueSubgroups G ∧
      section10AmbientSylowSubgroup (section10Msigma M) P ≤ M ∧
      (∃ U : Subgroup G,
        U ∈ section9UniqueSubgroups G ∧
          U ≤ Subgroup.centralizer (X : Set G) ∧
          U ≤ M) := by
  classical
  let Pamb : Subgroup G := section10AmbientSylowSubgroup (section10Msigma M) P
  have hPamb_le_M : Pamb ≤ M := by
    intro x hx
    change x ∈ (P : Subgroup (section10Msigma M)).map (section10Msigma M).subtype at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    have hσM : section10Msigma M ≤ M := by
      simpa [section10Msigma] using Subgroup.map_subtype_le (section10MsigmaSubgroup M)
    exact hσM y.property
  have hXM : X ≤ M := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXM, _hXcard⟩
    exact hXM
  have hXp : IsPGroup p.val X :=
    section12_primeOrderSubgroupsIn_isPGroup (G := G) hX
  have hXsubM_p : IsPGroup p.val (X.subgroupOf M) :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := M) hXM).symm
  have hXsub_le_sigma :
      X.subgroupOf M ≤ section10MsigmaSubgroup M :=
    section12_pSubgroup_le_normal_hall_of_prime_mem
      (R := M) (π := section10SigmaPrimes M) (H := section10MsigmaSubgroup M)
      (A := X.subgroupOf M) (theorem_10_2_b (M := M) hM).2 hp hXsubM_p
  have hXle_sigma : X ≤ section10Msigma M := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hXM hx⟩, hXsub_le_sigma (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  obtain ⟨P₀, hXleP₀⟩ :=
    section12_exists_sylow_containing_pSubgroup
      (G := G) (K := section10Msigma M) (X := X) (p := p) hXle_sigma hXp
  rcases section12_corollary_12_14_derived_chosen_core
      (G := G) (M := M) (X := X) (p := p) P₀
      hM hp hX hXleP₀ hXder hcomp with
    ⟨hP₀_unique, _hP₀_le_M, hU⟩
  have : Fact p.val.Prime := ⟨p.property⟩
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (section10Msigma M) P₀ P
  have hPamb_conj :
      Pamb =
        (section10AmbientSylowSubgroup (section10Msigma M) P₀).conjBy (m : G) := by
    simpa [Pamb, hm] using
      section12_ambientSylowSubgroup_smul_local
        (G := G) (M := section10Msigma M) (p := p) P₀ m
  have hPamb_unique : Pamb ∈ section9UniqueSubgroups G := by
    rw [hPamb_conj]
    exact section12_unique_conjBy_local (G := G) hP₀_unique (m : G)
  exact ⟨hPamb_unique, hPamb_le_M, hU⟩

private theorem CFSG.section12_corollary_12_14_core
    {M X : Subgroup G} {p : Nat.Primes} (P : Sylow p.val (section10Msigma M))
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section10SigmaPrimes M)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p M)
    (hhyp : p ∈ section10BetaPrimes M ∨ X ≤ ambientDerivedSubgroup (section10Msigma M)) :
    section10AmbientSylowSubgroup (section10Msigma M) P ∈ section9UniqueSubgroups G ∧
      section10AmbientSylowSubgroup (section10Msigma M) P ≤ M ∧
      (∃ U : Subgroup G,
        U ∈ section9UniqueSubgroups G ∧
          U ≤ Subgroup.centralizer (X : Set G) ∧
          U ≤ M) := by
  classical
  let Pamb : Subgroup G := section10AmbientSylowSubgroup (section10Msigma M) P
  have hPamb_le_M : Pamb ≤ M := by
    intro x hx
    change x ∈ (P : Subgroup (section10Msigma M)).map (section10Msigma M).subtype at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    have hσM : section10Msigma M ≤ M := by
      simpa [section10Msigma] using Subgroup.map_subtype_le (section10MsigmaSubgroup M)
    exact hσM y.property
  have hPamb_p : IsPGroup p.val Pamb := by
    change IsPGroup p.val
      ((P : Subgroup (section10Msigma M)).map (section10Msigma M).subtype)
    exact IsPGroup.map P.isPGroup' (section10Msigma M).subtype
  have hbeta_core
      (hpβ : p ∈ section10BetaPrimes M) :
      section10AmbientSylowSubgroup (section10Msigma M) P ∈ section9UniqueSubgroups G ∧
        section10AmbientSylowSubgroup (section10Msigma M) P ≤ M ∧
        (∃ U : Subgroup G,
          U ∈ section9UniqueSubgroups G ∧
            U ≤ Subgroup.centralizer (X : Set G) ∧
            U ≤ M) := by
    have hpIdeal : section10IdealPrime p G := hpβ.2
    have hPrank_gt : 1 < groupRank Pamb := by
      have hα : 2 < primeRank p.val M := hpβ.1.2
      have hle :
          primeRank p.val M ≤ groupRank Pamb := by
        simpa [Pamb] using
          section12_primeRank_le_groupRank_msigma_sylow_ambient_local
            (G := G) (M := M) hM hp P
      exact lt_of_lt_of_le (by omega : 1 < primeRank p.val M) hle
    have hPamb_unique : Pamb ∈ section9UniqueSubgroups G :=
      proposition_10_14_b (G := G) hpIdeal hPamb_p hPrank_gt
    have hXM : X ≤ M := by
      rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXM, _hXcard⟩
      exact hXM
    have hXp : IsPGroup p.val X :=
      section12_primeOrderSubgroupsIn_isPGroup (G := G) hX
    obtain ⟨S, hX_le_S⟩ :=
      IsPGroup.exists_le_sylow (G := G) (p := p.val) hXp
    let U : Subgroup G := subgroupNormalizerIn (S : Subgroup G) (X : Set G)
    have hU_unique : U ∈ section9UniqueSubgroups G := by
      simpa [U] using
        proposition_10_14_c (G := G) hpIdeal S hX_le_S
    have hUp : IsPGroup p.val U := by
      exact S.isPGroup'.to_le (by
        intro u hu
        exact (mem_subgroupNormalizerIn.mp (by simpa [U] using hu)).2)
    have hU_le_CX : U ≤ Subgroup.centralizer (X : Set G) :=
      section12_pSubgroup_le_centralizer_of_primeOrder_normalizes
        (G := G) (U := U) (A := M) (X := X) (p := p) hUp hX (by
          intro u hu
          exact (mem_subgroupNormalizerIn.mp (by simpa [U] using hu)).1)
    have hXπβ : IsPiSubgroup (G := G) (section10BetaPrimes M) X := by
      intro q hqX
      have hXcard : Nat.card X = p.val := hX.2
      have hq_dvd_pow : q.val ∣ p.val ^ 1 := by
        simpa [hXcard] using hqX
      have hqp : q.val = p.val :=
        Nat.prime_eq_prime_of_dvd_pow q.property p.property hq_dvd_pow
      have hq_eq : q = p := Subtype.ext hqp
      simpa [hq_eq] using hpβ
    have hU_le_normX : U ≤ Subgroup.normalizer (X : Set G) := by
      intro u hu
      exact (mem_subgroupNormalizerIn.mp (by simpa [U] using hu)).1
    have hU_le_M : U ≤ M :=
      hU_le_normX.trans
        (proposition_10_14_d (G := G) hpIdeal S hM hXM
          (section12_primeOrder_ne_bot (G := G) hX) hXπβ)
    exact ⟨by simpa [Pamb] using hPamb_unique, by simpa [Pamb] using hPamb_le_M,
      ⟨U, hU_unique, hU_le_CX, hU_le_M⟩⟩
  rcases hhyp with hpβ | hXder
  · exact hbeta_core hpβ
  · have hpM : p ∈ subgroupPrimeSet M := hp.1
    by_cases hpβ : p ∈ section10BetaPrimes M
    · exact hbeta_core hpβ
    · exact section12_corollary_12_14_derived_core
        (G := G) (M := M) (X := X) (p := p) P hM hp hX hXder
        (lemma_10_8_c (G := G) hM hpM hpβ).2.1

/-- Corollary 12.14. -/
public theorem CFSG.corollary_12_14
    {M X : Subgroup G} {p : Nat.Primes} (P : Sylow p.val (section10Msigma M))
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section10SigmaPrimes M)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p M)
    (hhyp : p ∈ section10BetaPrimes M ∨ X ≤ ambientDerivedSubgroup (section10Msigma M)) :
    section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
      section9MaximalSubgroupsContaining
        (section10AmbientSylowSubgroup (section10Msigma M) P) = {M} := by
  classical
  let Pamb : Subgroup G := section10AmbientSylowSubgroup (section10Msigma M) P
  rcases section12_corollary_12_14_core (G := G) (M := M) (X := X) (p := p) P
      hM hp hX hhyp with
    ⟨hPamb_unique, hPamb_le_M, hU⟩
  have hPamb_single :
      section9MaximalSubgroupsContaining Pamb = {M} :=
    section12_unique_overgroups_eq_of_contains_maximal_local
      (G := G) (H := Pamb) (M := M) hPamb_unique hM hPamb_le_M
  rcases hU with ⟨U, hU_unique, hU_le_CX, _hU_le_M⟩
  have hCX_proper : Subgroup.centralizer (X : Set G) ≠ ⊤ := by
    intro hCXtop
    have htop_le_norm :
        (⊤ : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
      simpa [hCXtop] using (centralizer_le_normalizer X)
    exact section12_normalizer_ne_top_of_ne_bot_ne_top
      (section12_primeOrder_ne_bot hX) (section12_primeOrder_ne_top hX)
      (top_le_iff.mp htop_le_norm)
  have hU_single :
      section9MaximalSubgroupsContaining U = {M} :=
    section12_unique_overgroups_eq_of_contains_maximal_local
      (G := G) (H := U) (M := M) hU_unique hM _hU_le_M
  have hCX_le_M : Subgroup.centralizer (X : Set G) ≤ M :=
    section12_le_unique_maximal_of_le (G := G)
      (Y := U) (X := Subgroup.centralizer (X : Set G)) (M := M)
      hU_le_CX hCX_proper hU_single
  have hCX_unique : Subgroup.centralizer (X : Set G) ∈ section9UniqueSubgroups G :=
    section9_unique_of_le hU_le_CX hCX_proper hU_unique
  have hCX_single :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} :=
    section12_unique_overgroups_eq_of_contains_maximal_local
      (G := G) (H := Subgroup.centralizer (X : Set G)) (M := M)
      hCX_unique hM hCX_le_M
  exact ⟨hCX_single, by simpa [Pamb] using hPamb_single⟩

end Section12
