module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIX
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.BarOfInterTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenR
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.GapsNineteenR
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ComponentModO2Sup
public import CFSG.LocalAnalysis.UniquenessCase.UC6Grp
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7LemmaS
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmBasic
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7Mod
public import CFSG.RankThree.PartTwo.Sec18.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.ClassicalInvolution.Asc77.T3CII
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem oUpperTwo_sup_zpowers_eq {A : Subgroup G} {t : G} (hAodd : Odd (Nat.card A))
    (ht2 : ∃ k : ℕ, orderOf t = 2 ^ k) (htA : t ∈ normalizer (A : Set G)) :
    S17.oUpperTwo (A ⊔ zpowers t) = A := by
  obtain ⟨k, hk⟩ := ht2
  have hP2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers]; exact hk)
  have hPN : Subgroup.zpowers t ≤ normalizer (A : Set G) := Subgroup.zpowers_le.mpr htA
  apply le_antisymm
  · rw [S17.oUpperTwo_eq_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, hxodd⟩
    exact mem_of_odd_orderOf_of_mem_sup hP2 hPN hx hxodd
  · rw [S17.oUpperTwo_eq_closure]
    intro a ha
    exact Subgroup.subset_closure
      ⟨Subgroup.mem_sup_left ha, hAodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard A ha)⟩

theorem isComponentModO2_sup_pCoreOf_of_mem_calC_of_subgroup {N L : Subgroup G}
    (hL : L ∈ calC N) : F12.IsComponentModO2 N (L ⊔ pCoreOf 2 N) := by
  have hLN : L ≤ Subgroup.normalizer ((pCoreOf 2 N : Subgroup G) : Set G) :=
    (CFSG.Open.IsSubnormal.le hL.1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N)
  have hKN : L ⊔ pCoreOf 2 N ≤ Subgroup.normalizer ((pCoreOf 2 N : Subgroup G) : Set G) :=
    (sup_le (CFSG.Open.IsSubnormal.le hL.1) (CFSG.LieType.BorelTits.pCoreOf_le 2 N)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N)
  have hKsn : CFSG.Open.IsSubnormal (L ⊔ pCoreOf 2 N) N :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.sup_pCoreOf_isSubnormal hL.1
  have hpc : (pCoreOf 2 N).subgroupOf L = CFSG.pCore 2 ↥L := by
    have hEq : pCoreOf 2 L = pCoreOf 2 N ⊓ L := by
      refine le_antisymm (le_inf (CFSG.Quasithin.pCoreOf_le_pCoreOf_of_isSubnormal hL.1)
        (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) ?_
      have h2 : IsPGroup 2 ↥(pCoreOf 2 N ⊓ L) :=
        IsPGroup.to_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N) inf_le_left
      have hNL : L ≤ Subgroup.normalizer (((pCoreOf 2 N) ⊓ L : Subgroup G) : Set G) := by
        intro x hx
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨(CFSG.Open.IsSubnormal.le hL.1).trans
              (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N) hx,
            Subgroup.le_normalizer hx⟩
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hNL h2
    apply (Subgroup.map_subtype_inj (H := L)).mp
    rw [Subgroup.subgroupOf_map_subtype,
      show (CFSG.pCore 2 ↥L).map L.subtype = pCoreOf 2 L from rfl]
    exact hEq.symm
  have hbar : Nonempty (Bar2 (L ⊔ pCoreOf 2 N) ≃* Bar2 L) := by
    have hNL : ((pCoreOf 2 N).subgroupOf L).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hLN
    have hNK : ((pCoreOf 2 N).subgroupOf (L ⊔ pCoreOf 2 N)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hKN
    let e1 := QuotientGroup.quotientInfEquivProdNormalizerQuotient L (pCoreOf 2 N) hLN
    exact ⟨(QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.subgroupOf_pCoreOf_sup_eq_pCore_of_isSubnormal
          hL.1)).symm.trans
      (e1.symm.trans (QuotientGroup.quotientMulEquivOfEq hpc))⟩
  refine ⟨le_sup_right, sup_le (CFSG.Open.IsSubnormal.le hL.1)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 N), hKsn, ?_⟩
  have hAn : ((pCoreOf 2 N).subgroupOf (L ⊔ pCoreOf 2 N)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKN
  refine ⟨hAn, ?_⟩
  obtain ⟨e⟩ := hbar
  exact CFSG.Quasithin.Vol2.Ch10.SecC.C10KH.isQuasisimple_of_open
    (hL.2.2.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.subgroupOf_pCoreOf_sup_eq_pCore_of_isSubnormal
          hL.1)).trans e))

theorem oUpperTwo_le_sup_pCore_of_map_le {X Y : Type} [Group X] [Group Y]
    [Finite X] (ψ : X →* Y) (hker : IsPGroup 2 ψ.ker)
    {K N : Subgroup X} (hNK : N ≤ K)
    (h : S17.oUpperTwo (K.map ψ) ≤ N.map ψ ⊔ pCoreOf 2 (K.map ψ)) :
    S17.oUpperTwo K ≤ N ⊔ pCoreOf 2 K := by
  set ψK : ↥K →* ↥(K.map ψ) :=
    (ψ.comp K.subtype).codRestrict (K.map ψ) fun x => Subgroup.mem_map_of_mem ψ x.2 with hψKdef
  have hψKsurj : Function.Surjective ψK := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp (y.2 : (y : Y) ∈ K.map ψ)
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hkerK : IsPGroup 2 ψK.ker := by
    have hle : ψK.ker ≤ ψ.ker.comap K.subtype := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_comap, MonoidHom.mem_ker]
      have h1 := congrArg (fun y : ↥(K.map ψ) => (y : Y)) hx
      simpa [hψKdef] using h1
    exact (hker.comap_subtype (K := K)).to_le hle
  rw [S17.oUpperTwo_eq_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxK, hxodd⟩
  set xK : ↥K := ⟨x, hxK⟩ with hxKdef
  have hmemS : ψK xK ∈ (S17.oUpperTwo (K.map ψ)).subgroupOf (K.map ψ) := by
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.subset_closure ⟨(ψK xK).2, ?_⟩
    have h3 : orderOf (ψK xK) = orderOf (ψ x) := by
      rw [← Subgroup.orderOf_coe (ψK xK)]
      rfl
    rw [Subgroup.orderOf_coe, h3]
    exact hxodd.of_dvd_nat (orderOf_map_dvd ψ x)
  have hmem : ψ x ∈ N.map ψ ⊔ pCoreOf 2 (K.map ψ) := h hmemS
  have hmem' : ψK xK ∈ (N.map ψ).subgroupOf (K.map ψ) ⊔ CFSG.pCore 2 ↥(K.map ψ) := by
    have hpc : (pCoreOf 2 (K.map ψ)).subgroupOf (K.map ψ) =
        CFSG.pCore 2 ↥(K.map ψ) :=
      CFSG.openPCoreOf_subgroupOf 2 (K.map ψ)
    have hsup : (N.map ψ ⊔ pCoreOf 2 (K.map ψ)).subgroupOf (K.map ψ) =
        (N.map ψ).subgroupOf (K.map ψ) ⊔ (pCoreOf 2 (K.map ψ)).subgroupOf (K.map ψ) :=
      Subgroup.subgroupOf_sup (Subgroup.map_mono hNK)
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (K.map ψ))
    rw [← hpc, ← hsup, Subgroup.mem_subgroupOf]
    exact hmem
  rw [Subgroup.mem_sup_of_normal_right] at hmem'
  obtain ⟨n, hn, o, ho, hno⟩ := hmem'
  obtain ⟨c, hcN, hcn⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hn)
  have hcK : c ∈ K := hNK hcN
  set cK : ↥K := ⟨c, hcK⟩ with hcKdef
  have hcon : ψK cK = n := Subtype.ext hcn
  have hoψ : ψK (cK⁻¹ * xK) = o := by
    rw [map_mul, map_inv, hcon]
    rw [← hno]
    simp
  have hoP : cK⁻¹ * xK ∈ CFSG.pCore 2 ↥K := by
    rw [← CFSG.Quasithin.H13.L1297.comap_pCore_eq_of_isPGroup_ker ψK hψKsurj hkerK,
      Subgroup.mem_comap]
    exact hoψ ▸ ho
  have hxEq : x = c * (((cK⁻¹ * xK : ↥K) : X)) := by
    show x = c * (c⁻¹ * x)
    group
  have hPmem : (((cK⁻¹ * xK : ↥K) : X)) ∈ pCoreOf 2 K :=
    Subgroup.mem_map_of_mem K.subtype hoP
  rw [hxEq]
  exact (N ⊔ pCoreOf 2 K).mul_mem (Subgroup.mem_sup_left hcN)
    (Subgroup.mem_sup_right hPmem)

theorem oUpperTwo_le_of_le_sup_pCoreOf {K N : Subgroup G} (hNK : N ≤ K)
    (hNs : (N.subgroupOf K).Normal)
    (h : S17.oUpperTwo K ≤ N ⊔ pCoreOf 2 K) : S17.oUpperTwo K ≤ N := by
  have hKN : K ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hNs
  have hP : pCoreOf 2 K ≤ Subgroup.normalizer (N : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKN
  rw [S17.oUpperTwo_eq_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxK, hxodd⟩
  have hxS : x ∈ S17.oUpperTwo K := by
    rw [S17.oUpperTwo_eq_closure]
    exact Subgroup.subset_closure ⟨hxK, hxodd⟩
  exact mem_of_odd_orderOf_of_mem_sup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hP
    (h hxS) hxodd

theorem oUpperTwo_le_IOf_of_cases124 {M I A Dsub : Subgroup G}
    (hAM : A ≤ M) (h17 : A ≤ Subgroup.normalizer (Dsub : Set G))
    (hInorm : (I.subgroupOf M).Normal)
    (hcommnot : ¬ ⁅Opp 2 (Dsub ⊓ M), A⁆ ≤ pCoreOf 2 (Opp 2 (Dsub ⊓ M)))
    (hcomm : ⁅Opp 2 (Dsub ⊓ M), A⁆ ≤ I)
    (hshape : Shape19_16_124 (Bar2 Dsub) (barOfInter M Dsub))
    (hmin : K_19_18_minNormal) :
    S17.oUpperTwo (Opp 2 (Dsub ⊓ M)) ≤ I := by
  set K₀ : Subgroup G := Opp 2 (Dsub ⊓ M) with hK₀def
  have hK₀Ds : K₀ ≤ Dsub := by
    rw [hK₀def, Opp, CFSG.RankThree.PartOne.pElementSubgroup, Subgroup.closure_le]
    rintro x ⟨hx, -⟩
    exact hx.1
  have hK₀M : K₀ ≤ M := by
    rw [hK₀def, Opp, CFSG.RankThree.PartOne.pElementSubgroup, Subgroup.closure_le]
    rintro x ⟨hx, -⟩
    exact hx.2
  have hAnorm : A ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hK₀def]
    have hD : (Dsub ⊓ M).map (MulAut.conj a).toMonoidHom = Dsub ⊓ M := by
      rw [Subgroup.map_inf Dsub M (MulAut.conj a).toMonoidHom (MulAut.conj a).injective]
      have h2 : Dsub.map (MulAut.conj a).toMonoidHom = Dsub := by
        simpa using (Subgroup.mem_normalizer_iff_map_conj_eq).mp (h17 ha)
      have h3 : M.map (MulAut.conj a).toMonoidHom = M := by
        simpa using (Subgroup.mem_normalizer_iff_map_conj_eq).mp
          (Subgroup.le_normalizer (hAM ha))
      rw [h2, h3]
    have hmap := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map
      (p := 2) Nat.prime_two (MulAut.conj a).toMonoidHom (Dsub ⊓ M)
    rw [hD] at hmap
    change (CFSG.RankThree.PartOne.pElementSubgroup 2 (Dsub ⊓ M)).map
      (MulAut.conj a).toMonoidHom = CFSG.RankThree.PartOne.pElementSubgroup 2 (Dsub ⊓ M)
    exact hmap
  have hC₀le : ⁅K₀, A⁆ ≤ K₀ :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hAnorm
  set C₀ : Subgroup G := ⁅K₀, A⁆ with hC₀def
  have hC₀I : C₀ ≤ I := hcomm
  set NC : Subgroup ↥K₀ :=
    Subgroup.normalClosure ((C₀.subgroupOf K₀ : Subgroup ↥K₀) : Set ↥K₀) with hNCdef
  set N₀ : Subgroup G := NC.map K₀.subtype with hN₀def
  have hN₀K₀ : N₀ ≤ K₀ := Subgroup.map_subtype_le _
  have hC₀N₀ : C₀ ≤ N₀ := by
    have h1 : C₀.subgroupOf K₀ ≤ NC := Subgroup.le_normalClosure
    calc C₀ = (C₀.subgroupOf K₀).map K₀.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hC₀le).symm
      _ ≤ NC.map K₀.subtype := Subgroup.map_mono h1
  have hN₀norm : (N₀.subgroupOf K₀).Normal := by
    have h1 : N₀.subgroupOf K₀ = NC := by
      rw [hN₀def, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective K₀.subtype_injective]
    rw [h1]
    exact Subgroup.normalClosure_normal
  have hN₀I : N₀ ≤ I := by
    have : (I.subgroupOf M).Normal := hInorm
    have hIK : ((I ⊓ K₀).subgroupOf K₀).Normal := by
      have hEq : (I ⊓ K₀).subgroupOf K₀ = (I.subgroupOf M).comap (Subgroup.inclusion hK₀M) := by
        ext x
        simp [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.inclusion]
      rw [hEq]
      exact Subgroup.normal_comap (Subgroup.inclusion hK₀M)
    have hIKi : ((I ⊓ K₀).subgroupOf K₀).Normal := hIK
    have hle : C₀.subgroupOf K₀ ≤ (I ⊓ K₀).subgroupOf K₀ := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr
        ⟨hC₀I (Subgroup.mem_subgroupOf.mp hx), x.2⟩
    have h2 : NC ≤ (I ⊓ K₀).subgroupOf K₀ :=
      Subgroup.normalClosure_le_normal (N := (I ⊓ K₀).subgroupOf K₀) (fun x hx => hle hx)
    calc N₀ = NC.map K₀.subtype := by rw [hN₀def]
      _ ≤ ((I ⊓ K₀).subgroupOf K₀).map K₀.subtype := Subgroup.map_mono h2
      _ = I ⊓ K₀ := Subgroup.map_subgroupOf_eq_of_le inf_le_right
      _ ≤ I := inf_le_left
  set φ : ↥Dsub →* Bar2 Dsub := QuotientGroup.mk' (CFSG.pCore 2 ↥Dsub) with hφdef
  set Kbar : Subgroup (Bar2 Dsub) := Opp 2 (barOfInter M Dsub) with hKbardef
  have hKmap : (K₀.subgroupOf Dsub).map φ = Kbar := by
    rw [hK₀def, hKbardef, hφdef]
    exact map_opp_inter_eq_opp_barOfInter M Dsub
  have hψc0 : ∀ x : ↥K₀, φ (Subgroup.inclusion hK₀Ds x) ∈ Kbar := by
    intro x
    rw [← hKmap]
    exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr x.2)
  set ψc : ↥K₀ →* ↥Kbar :=
    (φ.comp (Subgroup.inclusion hK₀Ds)).codRestrict Kbar hψc0 with hψcdef
  have hψcsurj : Function.Surjective ψc := by
    intro y
    have hy : (y : Bar2 Dsub) ∈ (K₀.subgroupOf Dsub).map φ := by
      rw [hKmap]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext ?_⟩
    show φ (Subgroup.inclusion hK₀Ds ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩) = (y : Bar2 Dsub)
    have hincl : Subgroup.inclusion hK₀Ds ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩ = x := rfl
    rw [hincl, hxy]
  have hψcker : IsPGroup 2 ψc.ker := by
    have hker_eq : ψc.ker = (CFSG.pCore 2 ↥Dsub).comap (Subgroup.inclusion hK₀Ds) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap]
      have h1 : (ψc x = 1) ↔ (φ (Subgroup.inclusion hK₀Ds x) = 1) := by
        constructor
        · intro hh
          have h2 := congrArg (fun y : ↥Kbar => (y : Bar2 Dsub)) hh
          simpa [hψcdef] using h2
        · intro hh
          apply Subtype.ext
          simpa [hψcdef] using hh
      rw [h1]
      exact QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Dsub)
        (Subgroup.inclusion hK₀Ds x)
    rw [hker_eq]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥Dsub)).comap_of_injective
      (Subgroup.inclusion hK₀Ds) (Subgroup.inclusion_injective hK₀Ds)
  have hcomapψc : (CFSG.pCore 2 ↥Kbar).comap ψc = CFSG.pCore 2 ↥K₀ :=
    CFSG.Quasithin.H13.L1297.comap_pCore_eq_of_isPGroup_ker ψc hψcsurj hψcker
  set NT : Subgroup ↥K₀ := N₀.subgroupOf K₀ with hNTdef'
  have hNTnorm : NT.Normal := hN₀norm
  set Nbar : Subgroup (Bar2 Dsub) := (NT.map ψc).map Kbar.subtype with hNbardef
  have hNbarK : Nbar ≤ Kbar := Subgroup.map_subtype_le _
  have hNTmap : Nbar.subgroupOf Kbar = NT.map ψc := by
    rw [hNbardef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective Kbar.subtype_injective]
  have hNbarNorm : (Nbar.subgroupOf Kbar).Normal := by
    rw [hNTmap]
    exact hNTnorm.map ψc hψcsurj
  have hnotNbar : ¬ Nbar ≤ pCoreOf 2 Kbar := by
    intro hnp
    apply hcommnot
    intro c hc
    have hcN : c ∈ N₀ := hC₀N₀ hc
    have hcK₀ : c ∈ K₀ := hN₀K₀ hcN
    have hcNT : (⟨c, hcK₀⟩ : ↥K₀) ∈ NT := Subgroup.mem_subgroupOf.mpr hcN
    have h1 : NT.map ψc ≤ CFSG.pCore 2 ↥Kbar := by
      have h2 : Nbar.subgroupOf Kbar ≤ (pCoreOf 2 Kbar).subgroupOf Kbar := by
        intro x hx
        exact Subgroup.mem_subgroupOf.mpr (hnp (Subgroup.mem_subgroupOf.mp hx))
      rwa [hNTmap, CFSG.openPCoreOf_subgroupOf] at h2
    have h3 : ψc ⟨c, hcK₀⟩ ∈ CFSG.pCore 2 ↥Kbar := h1 (Subgroup.mem_map_of_mem ψc hcNT)
    have h4 : ⟨c, hcK₀⟩ ∈ (CFSG.pCore 2 ↥Kbar).comap ψc := Subgroup.mem_comap.mpr h3
    rw [hcomapψc] at h4
    exact Subgroup.mem_map_of_mem K₀.subtype h4
  have hfact0 := hmin (Bar2 Dsub) (barOfInter M Dsub) hshape Nbar hNbarK hNbarNorm hnotNbar
  have hfact : S17.oUpperTwo Kbar ≤ Nbar ⊔ pCoreOf 2 Kbar := by
    rw [← hKbardef] at hfact0
    exact hfact0
  set ψ₀ : ↥K₀ →* Bar2 Dsub := Kbar.subtype.comp ψc with hψ₀def
  have hψ₀ker : IsPGroup 2 ψ₀.ker := by
    have heq : ψ₀.ker = ψc.ker := by
      ext x
      simp [hψ₀def, MonoidHom.mem_ker]
    rw [heq]
    exact hψcker
  have hmapTop : (⊤ : Subgroup ↥K₀).map ψ₀ = Kbar := by
    rw [hψ₀def, ← Subgroup.map_map (⊤ : Subgroup ↥K₀) Kbar.subtype ψc,
      Subgroup.map_top_of_surjective ψc hψcsurj]
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hNT0 : NT.map ψ₀ = Nbar := by
    rw [hψ₀def, ← Subgroup.map_map NT Kbar.subtype ψc]
  have hT : S17.oUpperTwo ((⊤ : Subgroup ↥K₀).map ψ₀) ≤
      NT.map ψ₀ ⊔ pCoreOf 2 ((⊤ : Subgroup ↥K₀).map ψ₀) := by
    rw [hmapTop, hNT0]
    exact hfact
  have hmain := oUpperTwo_le_sup_pCore_of_map_le ψ₀ hψ₀ker (K := ⊤) (N := NT) le_top hT
  have htop : (⊤ : Subgroup ↥K₀).map K₀.subtype = K₀ := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hpcmap : (pCoreOf 2 (⊤ : Subgroup ↥K₀)).map K₀.subtype = pCoreOf 2 K₀ := by
    have h := CFSG.RankThree.PartTwo.Sec18.pCoreOf_map K₀.subtype K₀.subtype_injective 2
      (⊤ : Subgroup ↥K₀)
    rw [htop] at h
    exact h.symm
  have hmainG : S17.oUpperTwo K₀ ≤ N₀ ⊔ pCoreOf 2 K₀ := by
    have hstep : (S17.oUpperTwo (⊤ : Subgroup ↥K₀)).map K₀.subtype = S17.oUpperTwo K₀ := by
      have h1 := CFSG.AGLEmbedding.SUPair.map_oUpperTwo K₀.subtype (⊤ : Subgroup ↥K₀)
      rw [htop] at h1
      exact h1
    calc S17.oUpperTwo K₀ = (S17.oUpperTwo (⊤ : Subgroup ↥K₀)).map K₀.subtype := hstep.symm
      _ ≤ (NT ⊔ pCoreOf 2 (⊤ : Subgroup ↥K₀)).map K₀.subtype := Subgroup.map_mono hmain
      _ = N₀ ⊔ pCoreOf 2 K₀ := by
            rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hN₀K₀, hpcmap]
  exact (oUpperTwo_le_of_le_sup_pCoreOf hN₀K₀ hN₀norm hmainG).trans hN₀I

theorem nineteen_eighteen (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx)
    (h15 : R19_15At D V₀ V p L A t B r Y N Dsub H S h)
    (h17 : R19_17At D V₀ V p L A t B r Y N Dsub H S h)
    (hW1 : W7_9_1_4) (hW4 : W7_9_4c) (hmin : K_19_18_minNormal) (hgap : Gap19_18_5 D)
    (hcase3 : P19_16_3 D Dsub → False) :
    R19_18At D V₀ V p L A t B r Y N Dsub H S h := by
  have h17' : A ≤ Subgroup.normalizer (Dsub : Set G) := h17
  have hLcal : L ∈ calC D.M := S17.calLp_subset_calC D p h.ctx.hyp.hL
  have hIM : IOf D p L ≤ D.M := IOf_le_M D p hLcal.1.le
  have hInorm : ((IOf D p L).subgroupOf D.M).Normal := IOf_normal D p hLcal
  have hBI : B ≤ IOf D p L := by
    rw [h.ctx.hB]
    exact sup_le h.ctx.hA (Subgroup.zpowers_le.mpr h.ctx.htA)
  have hBM : B ≤ D.M := hBI.trans hIM
  have hoI : S17.oUpperTwo B ≤ IOf D p L := (S17.oUpperTwo_le B).trans hBI
  have heta : ∀ R : Subgroup G, R ≤ D.M → IsPGroup 2 R → B ≤ normalizer (R : Set G) →
      pCoreOf 2 (IOf D p L) ≤ R → calMOf (D.M ⊓ normalizer (R : Set G)) = {D.M} := by
    intro R hRM hR2 hBR hOR
    exact (h11 R ⟨hRM, hR2, hOR, hBR⟩).2
  have hYmem : Y ∈ muSet D B := h.hY.1
  have hYM : Y ≤ D.M := hYmem.1
  have hYN : Y ≤ N := h.hN.1.2
  have hNmax : IsMaxTwoLocalSubgroup N := h.hN.1.1
  have hNM : ¬ N ≤ D.M := by
    intro hle
    exact h.hN.2 (hNmax.2 D.M D.maxLocal.1 hle).symm
  have hNne : pCoreOf 2 N ≠ ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.pCoreOf_ne_bot_of_isTwoLocal hNmax.1
  have hmaxY : ∀ Z : Subgroup G, Z ≤ D.M → Z = B ⊔ pCoreOf 2 Z → pCoreOf 2 Z ≠ ⊥ →
      calMOf Z ≠ {D.M} → Y ≤ Z → Z = Y :=
    fun Z hZM hZ hZne hZcal hYZ => h.hY.2 Z ⟨hZM, hZ, hZne, hZcal⟩ hYZ
  have hO2NY : pCoreOf 2 N ≤ pCoreOf 2 Y :=
    hW1 G D.standing.simple D.standing.charTwo D.standing.kProper
      D.M (IOf D p L) B Y N D.maxLocal hIM hInorm hBM hoI heta hYM hYmem.2.1
      hYmem.2.2.1 hYmem.2.2.2 hmaxY hYN hNM hNne (pCoreOf 2 N)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 N) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
      (hYN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
  have hYH : Y ≤ H := by rw [h.hH]; exact le_sup_right
  have hHN : H ≤ N := by rw [h.hH]; exact sup_le h.hD.1.1.le hYN
  have hHM : ¬ H ≤ D.M := by
    intro hle
    exact h.hD.2 (le_trans le_sup_left (h.hH ▸ hle))
  have hO2Hne : pCoreOf 2 H ≠ ⊥ := by
    intro hbot
    apply hNne
    have hO2NH : pCoreOf 2 N ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (hO2NY.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYH))
        (hHN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    rw [hbot] at hO2NH
    exact le_bot_iff.mp hO2NH
  have hDsubH : Dsub ≤ H := by rw [h.hH]; exact le_sup_left
  have hDsubN : Dsub ≤ N := h.hD.1.1.le
  have hSubN : (Dsub.subgroupOf N).IsSubnormal :=
    (CFSG.Quasithin.isSubnormal_iff_subgroupOf hDsubN).mp h.hD.1.1
  have hSubH : (Dsub.subgroupOf H).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hHN hSubN
  have hDsubSubH : CFSG.Open.IsSubnormal Dsub H :=
    (CFSG.Quasithin.isSubnormal_iff_subgroupOf hDsubH).mpr hSubH
  have hO2norm : pCoreOf 2 H ≤ Subgroup.normalizer (Dsub : Set G) := by
    have : Group.IsNilpotent ↥(pCoreOf 2 H) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).isNilpotent
    have : Group.IsSolvable ↥(pCoreOf 2 H) := inferInstance
    exact CFSG.ClassicalInvolution.le_normalizer_of_isSubnormal_of_perfect_of_normal
      hDsubSubH h.hD.1.2.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      (Subgroup.normal_subgroupOf_of_le_normalizer
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hperfect : Dsub = CFSG.Quasithin.perfectCore (Dsub ⊔ pCoreOf 2 H) := by
    have hSolv : Group.IsSolvable ↥(pCoreOf 2 H) := by
      have : Group.IsNilpotent ↥(pCoreOf 2 H) :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).isNilpotent
      infer_instance
    have hmain := CFSG.StandardType.RCSTOm.perfectCore_eq_of_solvable
      (X := Dsub ⊔ pCoreOf 2 H) (Q := Dsub) (S := pCoreOf 2 H) (T := ⊥)
      (by rw [sup_bot_eq]) (by simpa using hO2norm) hSolv (by simpa using h.hD.1.2.1)
    rw [hmain, sup_bot_eq]
  have hcalCH : Dsub ∈ calC H := ⟨hDsubSubH, h.hD.1.2.1, h.hD.1.2.2⟩
  have hcomp : F12.IsComponentModO2 H (Dsub ⊔ pCoreOf 2 H) :=
    isComponentModO2_sup_pCoreOf_of_mem_calC_of_subgroup hcalCH
  have hnotblock : ¬ CFSG.RankThree.PartOne.IsBlockInX (Dsub.subgroupOf H) := by
    intro hb
    apply h15 (Dsub.subgroupOf N)
    have hb' : CFSG.CGT.PushingUp.IsBlockOfInX H Dsub :=
      (CFSG.CGT.PushingUpLit.isBlockInX_subgroupOf_iff hDsubH).mp hb
    exact (CFSG.CGT.PushingUpLit.isBlockInX_subgroupOf_iff hDsubN).mpr
      ⟨hDsubN, hSubN, hb'.2.2⟩
  have hnpos : 0 < S17.nOf L := by
    rcases h.ctx.h1910.2 with ⟨-, hnodd, -, -⟩ | ⟨-, -, h2n, -⟩ | ⟨-, h2n, -⟩
    · obtain ⟨m, hm⟩ := hnodd
      rw [hm]
      exact Nat.succ_pos _
    · omega
    · omega
  have hAodd : Odd (Nat.card A) := by
    have hcard := card_eq_of_isZModSq h.ctx.hAcard
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : S17.nOf L ≠ 0)
    have hodd : Odd (2 ^ (k + 1) - 1) :=
      Nat.Even.sub_odd (Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num)))
        ⟨2 ^ k, by rw [pow_succ]; ring⟩ odd_one
    rw [hcard, hk, Nat.succ_eq_add_one]
    exact hodd.mul hodd
  have htA : t ∈ normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      show t * a * t⁻¹ ∈ A
      rw [h.ctx.hinv a ha]
      exact A.inv_mem ha
    · intro a ha
      refine ⟨a⁻¹, A.inv_mem ha, ?_⟩
      show t * a⁻¹ * t⁻¹ = a
      rw [h.ctx.hinv a⁻¹ (A.inv_mem ha)]
      simp
  have hoB : S17.oUpperTwo B = A := by
    rw [h.ctx.hB]
    exact oUpperTwo_sup_zpowers_eq hAodd h.ctx.ht2 htA
  obtain ⟨hcommnot, hcomm⟩ := hW4 G D.standing.simple D.standing.charTwo D.standing.kProper
    D.M (IOf D p L) B Y Dsub H D.maxLocal hIM hInorm hBM hoI heta hYM hYmem.2.1
    hYmem.2.2.1 hYmem.2.2.2 hmaxY hYH hHM hO2Hne h.hH hperfect hcomp hnotblock
  rw [hoB, inf_comm] at hcommnot hcomm
  constructor
  · intro hc
    have hshape : Shape19_16_124 (Bar2 Dsub) (barOfInter D.M Dsub) := by
      rcases hc with h1 | h2 | h3 | h4
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨h2.1, (index_barOfInter (M := D.M) (L := Dsub) h.hO2).trans h2.2⟩)
      · exact absurd h3 hcase3
      · exact Or.inr (Or.inr h4)
    exact oUpperTwo_le_IOf_of_cases124 (M := D.M) (I := IOf D p L)
      (hAM := h.ctx.hA.trans hIM) (h17 := h17') hInorm hcommnot hcomm hshape hmin
  · intro h5
    obtain ⟨d, K, J, hfam, hcond⟩ := hgap V₀ V p L A t B r Y N Dsub H S h h17' h5
    obtain ⟨i, hi⟩ := hcond hcommnot
    exact ⟨d, K, J, hfam, i, hi.trans hcomm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
