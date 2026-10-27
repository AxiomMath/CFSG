module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4NM

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree
open CFSG.QuasithinUnique.Setup.X7 CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.ShultStronglyClosedTI.SuzukiLayerKernel
open CFSG.CGT.PushingUpLit.SolKNA
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem exists_mulEquiv_suzukiGroup_map_eq_suzukiU
    {H T : Subgroup G} {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hSz : Nonempty (oTwoQuot ↥H ≃* Sz a))
    (hT : IsSylowTwoOf T H) :
    ∃ e : oTwoQuot ↥H ≃* suzukiGroup a K,
      ((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom =
        suzukiU a K := by
  classical
  let e0 : oTwoQuot ↥H ≃* suzukiGroup a K :=
    (Classical.choice hSz).trans (suzukiGroupEquivSz a K hK).symm
  have hSylTop : IsSylowTwoOf (T.subgroupOf H) ⊤ :=
    CFSG.Quasithin.H13.NQCat.A314D.isSylowTwoOf_top_subgroupOf hT
  have hP0 : IsSylowTwoOf ((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hSylTop
      (QuotientGroup.mk' (pCore 2 ↥H)) (QuotientGroup.mk'_surjective _)
  have hP : IsSylowTwoOf (((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))).map
      e0.toMonoidHom) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hP0 e0.toMonoidHom e0.surjective
  have hU : IsSylowTwoOf (suzukiU a K) ⊤ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.suzukiU_isSylowTwoOf hK
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hP hU
  refine ⟨e0.trans (MulAut.conj g), ?_⟩
  have hmap : ((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))).map
        (e0.trans (MulAut.conj g)).toMonoidHom =
      (((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))).map e0.toMonoidHom).map
        (MulAut.conj g).toMonoidHom := by
    rw [show (e0.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp e0.toMonoidHom from rfl, ← Subgroup.map_map]
  rw [hmap, hg]
  rfl

theorem exists_mem_of_mem_suzukiZ0
    {H T C : Subgroup G} {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hCH : C ≤ H)
    (hC : ∀ x ∈ T, x * x ∈ pCoreOf 2 H → x ∈ C ⊔ pCoreOf 2 H)
    (e : oTwoQuot ↥H ≃* suzukiGroup a K)
    (he : ((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom =
      suzukiU a K) :
    ∀ z ∈ suzukiZ0 a K, ∃ c : ↥H, (c : G) ∈ C ∧ e (QuotientGroup.mk c) = z := by
  classical
  intro z hz
  have hzU : z ∈ suzukiU a K := suzukiZ0_le_suzukiU hz
  have hzS : z ∈ ((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom := by
    rw [he]
    exact hzU
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hzS
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
  have hsT : (s : G) ∈ T := Subgroup.mem_subgroupOf.mp hs
  have hyz' : e (QuotientGroup.mk' (pCore 2 ↥H) s) = z := hyz
  have hz2 : z * z = 1 := by
    have h := (mem_suzukiZ0_iff_sq_eq_one hK).mp hz
    simpa [pow_two] using h.2
  have hs2 : (s : G) * (s : G) ∈ pCoreOf 2 H := by
    have hqm : QuotientGroup.mk' (pCore 2 ↥H) (s * s) =
        QuotientGroup.mk' (pCore 2 ↥H) s * QuotientGroup.mk' (pCore 2 ↥H) s := map_mul _ s s
    have hsq : QuotientGroup.mk' (pCore 2 ↥H) (s * s) = 1 := by
      apply e.injective
      rw [hqm, map_mul, hyz', hz2, map_one]
    have hmem : s * s ∈ pCore 2 ↥H := (QuotientGroup.eq_one_iff (s * s)).mp hsq
    have hmemG : ((s * s : ↥H) : G) ∈ pCoreOf 2 H := (F1.mem_pCore_iff_coe (s * s)).mp hmem
    simpa using hmemG
  have hsmem : (s : G) ∈ C ⊔ pCoreOf 2 H := hC (s : G) hsT hs2
  have hsmem' : s ∈ (C ⊔ pCoreOf 2 H).subgroupOf H := Subgroup.mem_subgroupOf.mpr hsmem
  have hmapC : ((C ⊔ pCoreOf 2 H).subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H)) =
      (C.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H)) := by
    rw [Subgroup.subgroupOf_sup hCH (pCoreOf_le 2 H), Subgroup.map_sup]
    have hbot : ((pCoreOf 2 H).subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      change QuotientGroup.mk q = 1
      rw [QuotientGroup.eq_one_iff]
      exact (F1.mem_pCore_iff_coe q).mpr (Subgroup.mem_subgroupOf.mp hq)
    rw [hbot, sup_bot_eq]
  have hπs : QuotientGroup.mk' (pCore 2 ↥H) s ∈
      (C.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H)) := by
    rw [← hmapC]
    exact Subgroup.mem_map_of_mem _ hsmem'
  obtain ⟨c, hcC, hcπ⟩ := Subgroup.mem_map.mp hπs
  refine ⟨c, Subgroup.mem_subgroupOf.mp hcC, ?_⟩
  change e (QuotientGroup.mk' (pCore 2 ↥H) c) = z
  rw [hcπ]
  exact hyz'

variable [Finite G]

private theorem szv_sectionFacts {H U L N : Subgroup G}
    (hUQ : U ≤ pCoreOf 2 H) (hstep : IsChiefStep H U L N) :
    H ≤ Subgroup.normalizer (L : Set G) ∧
      H ≤ Subgroup.normalizer (N : Set G) ∧
      N ≤ Subgroup.normalizer (L : Set G) ∧
      IsElemAbelian 2 (Ch3z.chiefMod L N) ∧
      pCoreOf 2 H ≤ centralizerMod L H N := by
  have hUH : U ≤ H := hUQ.trans (pCoreOf_le 2 H)
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  have hU2 : IsPGroup 2 U := (pCoreOf_isPGroup 2 H).to_le hUQ
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) :=
    CFSG.Quasithin.isElemAbelian_chiefMod hstep hUH hU2
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hNQ : N ≤ pCoreOf 2 H := hstep.1.1.trans hUQ
  have hcommNQ : ⁅N, pCoreOf 2 H⁆ ≤ L :=
    F112W.commutator_le_of_isChiefStep (pCoreOf_isPGroup 2 H) (pCoreOf_le 2 H) hQn hstep hNQ
  have hO : pCoreOf 2 H ≤ centralizerMod L H N := by
    intro q hq
    refine ⟨pCoreOf_le 2 H hq, hHL (pCoreOf_le 2 H hq), fun n hn => ?_⟩
    have hmem : ⁅n, q⁆ ∈ L := hcommNQ (Subgroup.commutator_mem_commutator hn hq)
    have e : q * n * q⁻¹ * n⁻¹ = ⁅n, q⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact L.inv_mem hmem
  exact ⟨hHL, hHN, hNL, hE, hO⟩

private theorem szv_sectionRep_ne_one {H L N : Subgroup G} {a : ℕ}
    (hnc : ¬ IsCentralStep H L N)
    (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 H ≤ centralizerMod L H N)
    (e : oTwoQuot ↥H ≃* suzukiGroup a (GaloisField 2 (2 * a + 1))) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    ∃ g, sectionRep hHL hHN hNL hE hO e g ≠ 1 := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  unfold IsCentralStep at hnc
  push Not at hnc
  obtain ⟨y, hyH, n, hnN, hn⟩ := hnc
  refine ⟨e (QuotientGroup.mk ⟨y, hyH⟩), fun h1 => hn ?_⟩
  have hyn : y * n * y⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN hyH) n).mp hnN
  have h2 := LinearMap.congr_fun h1 (Additive.ofMul (Ch3z.chiefIota hNL ⟨n, hnN⟩))
  rw [sectionRep_chiefIota _ _ _ _ _ _ ⟨y, hyH⟩ ⟨n, hnN⟩ hyn, Module.End.one_apply] at h2
  have h3 : Ch3z.chiefIota hNL (⟨y * n * y⁻¹, hyn⟩ * (⟨n, hnN⟩ : ↥N)⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact Additive.ofMul.injective h2
  exact (Ch3z.chiefIota_eq_one_iff hNL _).1 h3

private theorem szv_sectionRep_isSzNatural
    {H T C U L N : Subgroup G} {a : ℕ} (ha : 1 ≤ a) (hCH : C ≤ H)
    (hC : ∀ x ∈ T, x * x ∈ pCoreOf 2 H → x ∈ C ⊔ pCoreOf 2 H)
    (hUH : U ≤ H) (hquad : ⁅⁅N, C⁆, C⁆ ≤ L)
    (hstep : IsChiefStep H U L N)
    (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 H ≤ centralizerMod L H N)
    (e : oTwoQuot ↥H ≃* suzukiGroup a (GaloisField 2 (2 * a + 1)))
    (he : ((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom =
      suzukiU a (GaloisField 2 (2 * a + 1)))
    (hnt : letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
      ∃ g, sectionRep hHL hHN hNL hE hO e g ≠ 1) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    IsSzNatural (sectionRep hHL hHN hNL hE hO e) := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  letI : Fintype K := Fintype.ofFinite K
  let ρ : Representation (ZMod 2) (suzukiGroup a K) (Additive (Ch3z.chiefMod L N)) :=
    sectionRep hHL hHN hNL hE hO e
  haveI : Fact ρ.IsIrreducible :=
    ⟨sectionRep_isIrreducible hstep hUH hHL hHN hNL hE hO e⟩
  have hZ0lift := exists_mem_of_mem_suzukiZ0 hK hCH hC e he
  have hZ0quad : ∀ z' ∈ suzukiZ0 a K, ∀ z ∈ suzukiZ0 a K,
      (ρ z' - 1) ∘ₗ (ρ z - 1) = 0 := by
    intro z' hz' z hz
    obtain ⟨s, hsC, hse⟩ := hZ0lift z' hz'
    obtain ⟨c, hcC, hce⟩ := hZ0lift z hz
    have hqc : ∀ n ∈ N, (c : G) * n * (c : G)⁻¹ * n⁻¹ ∈ ⁅N, C⁆ := by
      intro n hn
      have h1 : ⁅(c : G), n⁆ ∈ ⁅C, N⁆ :=
        Subgroup.commutator_mem_commutator hcC hn
      rwa [Subgroup.commutator_comm] at h1
    have hqs : ∀ y ∈ ⁅N, C⁆, (s : G) * y * (s : G)⁻¹ * y⁻¹ ∈ L := by
      intro y hy
      have h1 : ⁅(s : G), y⁆ ∈ ⁅C, ⁅N, C⁆⁆ :=
        Subgroup.commutator_mem_commutator hsC hy
      rw [Subgroup.commutator_comm] at h1
      exact hquad h1
    have h := sectionRep_comp_sub_one_eq_zero (Y := ⁅N, C⁆)
      hHL hHN hNL hE hO e c s hqc hqs
    simpa [ρ, hse, hce] using h
  have hquad' : CFSG.QuasithinUnique.Setup.X7.commSub ρ
        (CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K) (szZ a K)) ≤
      CFSG.QuasithinUnique.Setup.X7.fixedSub ρ
        (CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K) (szZ a K)) := by
    rw [conjSubgroup_weyl_szZ]
    exact CFSG.QuasithinUnique.Setup.X7.commSub_le_fixedSub hZ0quad
  exact isSzNatural_of_commSub_le_fixedSub hK ha ρ hnt (suzukiWElt a K) hquad'

theorem isSzNaturalSection_of_quadratic_of_sz
    {H T C U L N : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥H ≃* Sz a)) (hT : IsSylowTwoOf T H) (hCH : C ≤ H)
    (hC : ∀ x ∈ T, x * x ∈ pCoreOf 2 H → x ∈ C ⊔ pCoreOf 2 H)
    (hUQ : U ≤ pCoreOf 2 H) (hstep : IsChiefStep H U L N)
    (hquad : ⁅⁅N, C⁆, C⁆ ≤ L) (hnc : ¬ IsCentralStep H L N) :
    IsSzNaturalSection H N L a := by
  obtain ⟨hHL, hHN, hNL, hE, hO⟩ := szv_sectionFacts hUQ hstep
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨e, he⟩ := exists_mulEquiv_suzukiGroup_map_eq_suzukiU hK hSz hT
  have hnt := szv_sectionRep_ne_one hnc hHL hHN hNL hE hO e
  have hnat := szv_sectionRep_isSzNatural ha hCH hC (hUQ.trans (pCoreOf_le 2 H)) hquad hstep
    hHL hHN hNL hE hO e he hnt
  exact isSzNaturalSection_of_isSzNatural hHL hHN hNL hE hO e hnat

end CFSG.Quasithin.Stroth

end
