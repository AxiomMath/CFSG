module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourCentralizerTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourExceptionTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
import Mathlib.GroupTheory.SpecificGroups.KleinFour

namespace CFSG
end CFSG
open CFSG

/-!
# The large-field local endpoint for the split-four remark

Let `A ≤ PΓL₂(K)` contain the canonical `PSL₂(K)` layer, have dihedral
Sylow `2`-subgroups, and contain a Klein-four subgroup whose `C'` set is the
whole normalizer.  The field-automorphism image of `A` is odd
(`pGammaL2_field_projection_range_odd_of_dihedral`), so the projective-linear
kernel of `A` is a normal odd-index subgroup modeled by either `PSL₂(K)` or
`PGL₂(K)`.

If the kernel were the `PSL₂(K)` layer, the Klein four would lie inside it.
Lemma 2.1 applied to that layer then produces a normalizer element whose
square does not centralize the Klein four, contradicting the hypothesis that
`C'(Z)` is the full normalizer.  Therefore the kernel image is the full
`PGL₂(K)` layer, and since that image is a subgroup of `A`, the target
follows.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem normalizerContainsCPrime_iff_exists_local
    {G : Type u} [Group G] (Z : Subgroup G) :
    NormalizerContainsCPrime Z ↔
      ∃ n : G, n ∈ Subgroup.normalizer (Z : Set G) ∧
        n ^ 2 ∉ Subgroup.centralizer (Z : Set G) := by
  constructor
  · intro h
    rcases h with ⟨hsub, hnotsub⟩
    by_contra hnone
    apply hnotsub
    intro n hn
    have hc : n ^ 2 ∈ Subgroup.centralizer (Z : Set G) := by
      by_contra hsq
      exact hnone ⟨n, hn, hsq⟩
    exact ⟨hn, hc⟩
  · rintro ⟨n, hn, hsq⟩
    have hsub : cPrime Z ⊆ (Subgroup.normalizer (Z : Set G) : Set G) := by
      intro x hx
      exact hx.1
    have hnotsub : ¬ (Subgroup.normalizer (Z : Set G) : Set G) ⊆ cPrime Z := by
      intro hsub'
      exact hsq (hsub' hn).2
    exact ⟨hsub, hnotsub⟩

private theorem normal_index_two_of_normal_index_four
    {G : Type u} [Group G] [Finite G]
    (hN4 : ∃ N : Subgroup G, N.Normal ∧ N.index = 4) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  classical
  rcases hN4 with ⟨N4, hN4, hindex4⟩
  letI : N4.Normal := hN4
  letI : Fintype (G ⧸ N4) := N4.fintypeQuotientOfFiniteIndex
  have hcardQ : Nat.card (G ⧸ N4) = 4 := by
    rw [← N4.index_eq_card, hindex4]
  have h2dvd : 2 ∣ Fintype.card (G ⧸ N4) := by
    rw [← Nat.card_eq_fintype_card, hcardQ]
    norm_num
  obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card (G := G ⧸ N4) 2 h2dvd
  let H : Subgroup (G ⧸ N4) := Subgroup.zpowers x
  have hHcard : Nat.card H = 2 := by
    rw [Nat.card_zpowers, hx2]
  have hHindex : H.index = 2 := by
    have hprod := H.index_mul_card
    rw [hHcard, hcardQ] at hprod
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
      (by simpa [mul_comm] using hprod)
  have hHnormal : H.Normal := Subgroup.normal_of_index_eq_two hHindex
  let N : Subgroup G := H.comap (QuotientGroup.mk' N4)
  have hNnormal : N.Normal := hHnormal.comap (QuotientGroup.mk' N4)
  have hNindex : N.index = 2 := by
    rw [Subgroup.index_comap_of_surjective H (QuotientGroup.mk'_surjective N4)]
    exact hHindex
  exact ⟨N, hNnormal, hNindex⟩

private theorem twoGroup_le_normal_of_odd_index
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hNodd : Odd N.index)
    (Z : Subgroup G) (hZ : IsKleinFour Z) : Z ≤ N := by
  intro z hz
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hz2 : z ^ 2 = 1 := by
    simpa [pow_two] using congrArg Subtype.val
      (IsKleinFour.mul_self (⟨z, hz⟩ : Z))
  have hq2 : (q z) ^ 2 = 1 := by
    simpa [pow_two] using congrArg q hz2
  have hord_dvd : orderOf (q z) ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard (q z)
  have hqodd : Odd (orderOf (q z)) := Odd.of_dvd_nat hNodd hord_dvd
  have hord2 : orderOf (q z) ∣ 2 := orderOf_dvd_of_pow_eq_one hq2
  have hord1 : orderOf (q z) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact h
    · exfalso
      exact hqodd.not_two_dvd_nat (by rw [h])
  have hq1 : q z = 1 := orderOf_eq_one_iff.mp hord1
  exact (QuotientGroup.eq_one_iff (N := N) z).mp hq1

private theorem linearKernel_image_eq_psl_or_pgl
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (A : Subgroup (PGammaL2 K))
    (hPSL : pGammaL2PSLRange K ≤ A) :
    (pGammaL2LinearKernel K A).map A.subtype = pGammaL2PSLRange K ∨
      (pGammaL2LinearKernel K A).map A.subtype = pGammaL2PGLRange K := by
  let M : Subgroup (PGammaL2 K) :=
    (pGammaL2LinearKernel K A).map A.subtype
  have hHM : pGammaL2PSLRange K ≤ M := by
    intro x hx
    have hxA : x ∈ A := hPSL hx
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    exact (mem_pGammaL2LinearKernel_iff K A ⟨x, hxA⟩).mpr (by
      rcases hx with ⟨y, rfl⟩
      simp [pGammaL2FieldProjection])
  have hMP : M ≤ pGammaL2PGLRange K := by
    rintro _x ⟨a, ha, rfl⟩
    change (a : PGammaL2 K) ∈ pGammaL2PGLRange K
    rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom]
    simpa [pGammaL2FieldProjection] using
      (mem_pGammaL2LinearKernel_iff K A a).mp ha
  have hrel : (pGammaL2PSLRange K).relIndex (pGammaL2PGLRange K) = 2 :=
    pGammaL2_psl_range_relIndex_pgl_eq_two K hK
  have hmul := Subgroup.relIndex_mul_relIndex
    (pGammaL2PSLRange K) M (pGammaL2PGLRange K) hHM hMP
  rw [hrel] at hmul
  have hcase : (pGammaL2PSLRange K).relIndex M = 1 ∨
      M.relIndex (pGammaL2PGLRange K) = 1 := by
    have hdiv : (pGammaL2PSLRange K).relIndex M ∣ 2 :=
      ⟨M.relIndex (pGammaL2PGLRange K), hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hleft | hleft
    · exact Or.inl hleft
    · right
      rw [hleft] at hmul
      omega
  rcases hcase with hleft | hright
  · left
    apply le_antisymm
    · exact Subgroup.relIndex_eq_one.mp hleft
    · exact hHM
  · right
    apply le_antisymm
    · exact hMP
    · exact Subgroup.relIndex_eq_one.mp hright

private theorem normalizer_mem_of_normalizer_subgroupOf
    {G : Type u} [Group G] {M V : Subgroup G}
    (hVM : V ≤ M)
    {n : M} (hn : n ∈ Subgroup.normalizer
      ((V.subgroupOf M : Subgroup M) : Set M)) :
    (n : G) ∈ Subgroup.normalizer (V : Set G) := by
  have hn' : n ∈ (Subgroup.normalizer (V : Set G)).subgroupOf M := by
    rw [Subgroup.subgroupOf_normalizer_eq hVM]
    exact hn
  exact (Subgroup.mem_subgroupOf.mp hn')

private theorem normalizer_mem_of_map
    {G : Type u} [Group G] {A : Subgroup G} (Z : Subgroup A)
    {n : A}
    (hn : (n : G) ∈ Subgroup.normalizer
      ((Z.map A.subtype : Subgroup G) : Set G)) :
    n ∈ Subgroup.normalizer (Z : Set A) := by
  have hcomap :
      (Subgroup.normalizer (Z.map A.subtype : Set G)).comap A.subtype =
        Subgroup.normalizer (Z : Set A) := by
    rw [Subgroup.comap_normalizer_eq_of_le_range (f := A.subtype)
      (H := Z.map A.subtype)
      ((Subgroup.map_subtype_le Z).trans_eq A.range_subtype.symm)]
    congr 1
    ext a
    constructor
    · intro ha
      rcases Subgroup.mem_map.mp ha with ⟨z, hz, hzeq⟩
      have haeq : z = a := A.subtype_injective hzeq
      simpa [haeq] using hz
    · intro ha
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hn' : n ∈
      (Subgroup.normalizer (Z.map A.subtype : Set G)).comap A.subtype := hn
  rwa [hcomap] at hn'

private theorem not_centralizer_mem_of_not_centralizer_subgroupOf
    {G : Type u} [Group G] {M V : Subgroup G}
    {n : M}
    (hn : n ^ 2 ∉ Subgroup.centralizer
      ((V.subgroupOf M : Subgroup M) : Set M)) :
    (n : G) ^ 2 ∉ Subgroup.centralizer (V : Set G) := by
  intro hc
  apply hn
  rw [Subgroup.mem_centralizer_iff]
  intro xM hxM
  have hxV : (xM : G) ∈ V := (Subgroup.mem_subgroupOf.mp hxM)
  have hcomm := (Subgroup.mem_centralizer_iff.mp hc) (xM : G) hxV
  apply Subtype.ext
  change (xM : G) * (n : G) ^ 2 = (n : G) ^ 2 * (xM : G)
  exact hcomm

private theorem not_centralizer_mem_of_not_centralizer_map
    {G : Type u} [Group G] {A : Subgroup G} (Z : Subgroup A)
    {n : A}
    (hn : (n : G) ^ 2 ∉ Subgroup.centralizer
      ((Z.map A.subtype : Subgroup G) : Set G)) :
    n ^ 2 ∉ Subgroup.centralizer (Z : Set A) := by
  intro hc
  apply hn
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
  exact congrArg A.subtype
    ((Subgroup.mem_centralizer_iff.mp hc) z hz)

/-- In the canonical `PSL₂(K)` layer, every Klein-four subgroup has a
normalizer element whose square does not centralize it.  This is the
first branch of Gorenstein--Walter Lemma 2.1: the layer is simple for
`|K| > 3`, hence has no normal subgroup of index two or four. -/
private theorem pslLayer_kleinFour_normalizer_not_cPrime
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (ZP : Subgroup (↥(pGammaL2PSLRange K)))
    (hZP : IsKleinFour ZP) :
    ∃ n : ↥(pGammaL2PSLRange K),
      n ∈ Subgroup.normalizer (ZP : Set (↥(pGammaL2PSLRange K))) ∧
        n ^ 2 ∉ Subgroup.centralizer
          (ZP : Set (↥(pGammaL2PSLRange K))) := by
  let P := pGammaL2PSLRange K
  letI : Finite (↥P) :=
    Finite.of_surjective (pGammaL2PSLRangeEquiv K)
      (pGammaL2PSLRangeEquiv K).surjective
  have hPd : HasDihedralSylowTwo (↥P) :=
    pGammaL2PSLRange_hasDihedralSylowTwo K hK
  have hsimple : IsSimpleGroup (↥P) := by
    let e : PSL2 K ≃* (↥P) := pGammaL2PSLRangeEquiv K
    exact (MulEquiv.isSimpleGroup_congr e).mp
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := K) (by omega))
  have hno2 : ¬ ∃ N : Subgroup (↥P), N.Normal ∧ N.index = 2 := by
    rintro ⟨N, hNnormal, hNindex⟩
    rcases (haveI := hNnormal; hsimple.eq_bot_or_eq_top_of_normal N) with hbot | htop
    · rw [hbot, Subgroup.index_bot] at hNindex
      have hcard2 : Nat.card (↥P) = 2 := hNindex
      obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := ↥P)
      obtain ⟨m, hm, ⟨eS⟩⟩ := hPd S
      have hcardS : Nat.card (S : Subgroup (↥P)) = 2 * 2 ^ m := by
        exact (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
      have hSle : Nat.card (S : Subgroup (↥P)) ≤ Nat.card (↥P) :=
        Nat.card_le_card_of_injective _ (S : Subgroup (↥P)).subtype_injective
      rw [hcard2] at hSle
      have hSgt : 4 ≤ Nat.card (S : Subgroup (↥P)) := by
        rw [hcardS]
        have hpow : 2 ≤ 2 ^ m := by
          calc
            2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
        omega
      omega
    · rw [htop, Subgroup.index_top] at hNindex
      omega
  rcases gw_lemma_2_1 hPd with hfirst | hsecond | hthird
  · have hZp : IsPGroup 2 ZP := by
      apply IsPGroup.of_card (n := 2)
      rw [hZP.card_four]
      norm_num
    obtain ⟨S, hZPleS⟩ := IsPGroup.exists_le_sylow hZp
    rcases (normalizerContainsCPrime_iff_exists_local ZP).mp
      (hfirst.2.2 S ZP hZPleS hZP) with ⟨n, hn, hsq⟩
    exact ⟨n, hn, hsq⟩
  · exact False.elim (hno2 hsecond.1)
  · exfalso
    exact hno2 (normal_index_two_of_normal_index_four hthird.1)

/-- The large-field local endpoint: a dihedral-Sylow subgroup of `PΓL₂(K)`
containing the `PSL₂(K)` layer and a Klein four with `C'(Z) = N(Z)` must
contain the full `PGL₂(K)` layer. -/
public theorem pGammaL2_contains_pgl_of_selfCentralizing_four
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (A : Subgroup (PGammaL2 K))
    (hPSL : pGammaL2PSLRange K ≤ A)
    (hAd : HasDihedralSylowTwo A)
    (Z : Subgroup A) (hZ : IsKleinFour Z)
    (hN : cPrime Z = (Subgroup.normalizer (Z : Set A) : Set A)) :
    pGammaL2PGLRange K ≤ A := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  letI : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  letI : Finite (PGammaL2 K) :=
    Finite.of_injective (fun x : PGammaL2 K => (x.left, x.right)) (by
      intro x y hxy
      exact SemidirectProduct.ext
        (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  letI : Finite A := inferInstance
  have hodd : Odd (Nat.card
      (pGammaL2FieldProjection K A).range) :=
    pGammaL2_field_projection_range_odd_of_dihedral K hK hcard A hPSL hAd
  let L : Subgroup A := pGammaL2LinearKernel K A
  have hLindexOdd : Odd L.index :=
    pGammaL2LinearKernel_index_odd K A hodd
  haveI : L.Normal := pGammaL2LinearKernel_normal K A
  have hZleL : Z ≤ L :=
    twoGroup_le_normal_of_odd_index L hLindexOdd Z hZ
  rcases linearKernel_image_eq_psl_or_pgl hK A hPSL with hMpsl | hMpgl
  · -- The linear kernel image is the PSL₂ layer: contradiction.
    have hZlePSL : ∀ z : A, z ∈ Z →
        (z : PGammaL2 K) ∈ pGammaL2PSLRange K := by
      intro z hz
      have hzL : z ∈ L := hZleL hz
      have hzmap : (z : PGammaL2 K) ∈ L.map A.subtype :=
        Subgroup.mem_map.mpr ⟨z, hzL, rfl⟩
      rwa [hMpsl] at hzmap
    let Zmap : Subgroup (PGammaL2 K) := Z.map A.subtype
    have hZmapPSL : Zmap ≤ pGammaL2PSLRange K := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
      exact hZlePSL z hz
    let ZP : Subgroup (↥(pGammaL2PSLRange K)) :=
      Zmap.subgroupOf (pGammaL2PSLRange K)
    have hZmK : IsKleinFour Zmap :=
      isKleinFour_map_of_injective Z hZ A.subtype A.subtype_injective
    have hZPK : IsKleinFour ZP := isKleinFour_subgroupOf hZmapPSL hZmK
    obtain ⟨nP, hnPN, hnP2notC⟩ :=
      pslLayer_kleinFour_normalizer_not_cPrime hK hcard ZP hZPK
    let n : A := ⟨(nP : PGammaL2 K), hPSL nP.2⟩
    have hnN : n ∈ Subgroup.normalizer (Z : Set A) := by
      apply normalizer_mem_of_map Z
      exact normalizer_mem_of_normalizer_subgroupOf hZmapPSL hnPN
    have hn2notC : n ^ 2 ∉ Subgroup.centralizer (Z : Set A) := by
      apply not_centralizer_mem_of_not_centralizer_map Z
      exact not_centralizer_mem_of_not_centralizer_subgroupOf
        (G := PGammaL2 K) (M := pGammaL2PSLRange K) (V := Zmap)
        (n := nP) hnP2notC
    have hnC : n ∈ cPrime Z := by
      rw [hN]
      exact hnN
    exact False.elim (hn2notC hnC.2)
  · -- The linear kernel image is the PGL₂ layer, so that layer lies in A.
    intro x hx
    have hxA : x ∈ L.map A.subtype := by
      rwa [hMpgl]
    exact Subgroup.map_subtype_le L hxA

end CFSG.GorensteinWalter
