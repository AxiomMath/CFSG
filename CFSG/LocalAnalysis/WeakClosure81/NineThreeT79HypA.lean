module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79H0
public import CFSG.GroupTheory.StronglyClosedTI.OddCore
public import CFSG.GroupTheory.TIQuotientOdd
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nine3_fusionOddCore_eq_pPrimeCore (X : Type*) [Group X] :
    fusionOddCore X = CFSG.pPrimeCore 2 X := by
  unfold fusionOddCore CFSG.pPrimeCore
  congr 1
  ext K
  simp [Nat.coprime_two_left]

private theorem nine3_odd_card_fusionOddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  rw [nine3_fusionOddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem nine3_odd_card_fusionOddCoreOf (H : Subgroup G) : Odd (Nat.card (fusionOddCoreOf H)) := by
  rw [fusionOddCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
  exact nine3_odd_card_fusionOddCore ↥H

theorem nine3_fusionOddCore_le_center (h : Nine3T79Setup V T A K S X p g x) :
    fusionOddCore ↥(nineH0 V K g) ≤ Subgroup.center ↥(nineH0 V K g) := by
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hq' : (q : G) ∈ fusionOddCoreOf (nineH0 V K g) :=
    Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp
    (nine3_fusionOddCoreOf_le_centralizer h hq') (y : G) y.2
  simpa using hcomm

theorem nine3_dcal_inf_fusionOddCore_eq_bot (h : Nine3T79Setup V T A K S X p g x)
    {D : Subgroup G} (hD : D ∈ nine3Dcal V (nineH0 V K g)) :
    D ⊓ fusionOddCoreOf (nineH0 V K g) = ⊥ := by
  obtain ⟨k, hk, rfl⟩ := hD
  have hD2 : IsPGroup 2 (conjSubgroup V k) :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian
      (E3.isElemAbelian_conjSubgroup h.hc.core.hyp7.1 k)
  refine Subgroup.inf_eq_bot_of_coprime ?_
  obtain ⟨n, hn⟩ := hD2.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_left n
    (Nat.coprime_two_left.mpr (nine3_odd_card_fusionOddCoreOf (nineH0 V K g)))

private theorem nine3_map_conjSubgroup_hom {G' : Type*} [Group G'] (f : G →* G')
    (A : Subgroup G) (y : G) :
    conjSubgroup (A.map f) (f y) = (conjSubgroup A y).map f := by
  rw [CFSG.Quasithin.conjSubgroup, CFSG.Quasithin.conjSubgroup, Subgroup.map_map,
    Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply, map_mul]

theorem nine3_le_pCore_of_le_comap (h : Nine3T79Setup V T A K S X p g x) {D : Subgroup G}
    (hDH : D ≤ nineH0 V K g) (hD2 : IsPGroup 2 D)
    (hDle : D.subgroupOf (nineH0 V K g) ≤
      (CFSG.pCore 2 (nine3G1 V K g)).comap
        (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)))) :
    D ≤ pCoreOf 2 (nineH0 V K g) := by
  set H : Subgroup G := nineH0 V K g with hH
  set π : ↥H →* nine3G1 V K g := QuotientGroup.mk' (fusionOddCore ↥H) with hπ
  set M : Subgroup ↥H := (CFSG.pCore 2 (nine3G1 V K g)).comap π with hM
  have hMnormal : M.Normal := (CFSG.pCore_normal (p := 2)).comap π
  have hMnil : Group.IsNilpotent ↥M :=
    CFSG.GroupTheory.StronglyClosedTI.isNilpotent_comap_pCore
      (C := fusionOddCore ↥H) (nine3_fusionOddCore_le_center h)
  have hD'2 : IsPGroup 2 (D.subgroupOf H) := hD2.comap_of_injective H.subtype H.subtype_injective
  have hsub2 : IsPGroup 2 ((D.subgroupOf H).subgroupOf M) :=
    hD'2.comap_of_injective M.subtype M.subtype_injective
  obtain ⟨P, hP⟩ := hsub2.exists_le_sylow
  have hPmap : (P : Subgroup ↥M).map M.subtype ≤ CFSG.pCore 2 ↥H :=
    Sylow.map_le_pCore hMnormal hMnil 2 P
  have hD'sub : D.subgroupOf H ≤ CFSG.pCore 2 ↥H := by
    calc D.subgroupOf H = ((D.subgroupOf H).subgroupOf M).map M.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hDle).symm
      _ ≤ (P : Subgroup ↥M).map M.subtype := Subgroup.map_mono hP
      _ ≤ CFSG.pCore 2 ↥H := hPmap
  calc D = (D.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hDH).symm
    _ ≤ (CFSG.pCore 2 ↥H).map H.subtype := Subgroup.map_mono hD'sub
    _ = pCoreOf 2 H := rfl
    _ = pCoreOf 2 (nineH0 V K g) := rfl

private theorem nine3_subgroupOf_conjSubgroup {H A : Subgroup G} (hA : A ≤ H) {y : G}
    (hy : y ∈ H) :
    (conjSubgroup A y).subgroupOf H = conjSubgroup (A.subgroupOf H) ⟨y, hy⟩ := by
  ext z
  simp only [Subgroup.mem_subgroupOf, mem_conjSubgroup_iff, Subgroup.coe_mul, Subgroup.coe_inv]

theorem nine3_dcal_map_mem_omegaSet (h : Nine3T79Setup V T A K S X p g x)
    {D : Subgroup G} (hD : D ∈ nine3Dcal V (nineH0 V K g)) :
    (D.subgroupOf (nineH0 V K g)).map
        (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g))) ∈
      omegaSet (nine3BarV V K g) (⊤ : Subgroup (nine3G1 V K g)) (nine3BarE V K g) := by
  have hDkeep : D ∈ nine3Dcal V (nineH0 V K g) := hD
  have hDH : D ≤ nineH0 V K g := nine3_dcal_le_H0 h.hc hD
  have hD2 : IsPGroup 2 D := by
    obtain ⟨k, hk, rfl⟩ := hD
    exact CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian
      (E3.isElemAbelian_conjSubgroup h.hc.core.hyp7.1 k)
  obtain ⟨k, hk, hkD⟩ := hD
  rw [mem_omegaSet]
  refine ⟨QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)) ⟨k, hk⟩, ?_, ?_, ?_⟩
  ·
    rw [hkD, nine3_subgroupOf_conjSubgroup (nine3_V_le_H0 h.hc) hk]
    exact (nine3_map_conjSubgroup_hom (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)))
      (V.subgroupOf (nineH0 V K g)) ⟨k, hk⟩).symm
  ·
    obtain ⟨i, hi⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (nine3_dcal_inf_I0 h hDkeep).1
    have hiD : (i : G) ∈ D := i.2.1
    have hiI : (i : G) ∈ nineI0 V K g := i.2.2
    have hi1 : (i : G) ≠ 1 := fun hh => hi (Subtype.ext hh)
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)) ⟨(i : G), hDH hiD⟩, ?_⟩, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact Subgroup.mem_map.mpr
          ⟨⟨(i : G), hDH hiD⟩, Subgroup.mem_subgroupOf.mpr hiI, rfl⟩
      · exact Subgroup.mem_map.mpr
          ⟨⟨(i : G), hDH hiD⟩, Subgroup.mem_subgroupOf.mpr hiD, rfl⟩
    · intro hzero
      apply hi1
      have hq : (⟨(i : G), hDH hiD⟩ : ↥(nineH0 V K g)) ∈
          fusionOddCore ↥(nineH0 V K g) :=
        (QuotientGroup.eq_one_iff _).mp (Subtype.ext_iff.mp hzero)
      have hmem : (i : G) ∈ D ⊓ fusionOddCoreOf (nineH0 V K g) :=
        ⟨hiD, Subgroup.mem_map.mpr ⟨_, hq, rfl⟩⟩
      rw [nine3_dcal_inf_fusionOddCore_eq_bot h hDkeep, Subgroup.mem_bot] at hmem
      exact hmem
  ·
    intro hle
    rw [CFSG.Quasithin.B6.pCoreOf_top 2 (nine3G1 V K g)] at hle
    exact (nine3_dcal_not_le_pCore h hDkeep).1
      (nine3_le_pCore_of_le_comap h hDH hD2 (Subgroup.map_le_iff_le_comap.mp hle))

theorem nine3_iSup_dcal_map_le_kSub (h : Nine3T79Setup V T A K S X p g x) :
    (⊤ : Subgroup ↥(nineH0 V K g)) ≤
      (kSub (nine3BarV V K g) (⊤ : Subgroup (nine3G1 V K g)) (nine3BarE V K g)).comap
        (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g))) := by
  have hle : nineH0 V K g ≤
      ((kSub (nine3BarV V K g) (⊤ : Subgroup (nine3G1 V K g)) (nine3BarE V K g)).comap
        (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)))).map
        (nineH0 V K g).subtype := by
    refine (nine3_H0_eq_iSup_dcal h).le.trans ?_
    refine iSup₂_le fun D hD => ?_
    have hsub : D.subgroupOf (nineH0 V K g) ≤
        (kSub (nine3BarV V K g) (⊤ : Subgroup (nine3G1 V K g)) (nine3BarE V K g)).comap
          (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g))) :=
      Subgroup.map_le_iff_le_comap.mp (le_kSub (nine3_dcal_map_mem_omegaSet h hD))
    calc D = (D.subgroupOf (nineH0 V K g)).map (nineH0 V K g).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (nine3_dcal_le_H0 h.hc hD)).symm
      _ ≤ ((kSub (nine3BarV V K g) (⊤ : Subgroup (nine3G1 V K g)) (nine3BarE V K g)).comap
            (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)))).map
            (nineH0 V K g).subtype := Subgroup.map_mono hsub
  intro x _
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (hle x.2)
  rw [← Subtype.ext hzx]
  exact hz

theorem nine3_nineI0_le_H0 : nineI0 V K g ≤ nineH0 V K g := by
  have hIleH : nineI V K ≤ nineH V K :=
    iSup₂_le fun U hU => le_iSup₂_of_le U hU inf_le_left
  exact sup_le (hIleH.trans le_sup_left)
    ((E3.conjSubgroup_mono_left g hIleH).trans le_sup_right)

private theorem nine3_isTI_subgroupOf {A H : Subgroup G} (hAH : A ≤ H) (hTI : IsTI A) :
    IsTI (A.subgroupOf H) := by
  intro y
  have h := hTI (y : G)
  have hmap : ((A.subgroupOf H) ⊓
      CFSG.CGT.Timmesfeld75.conjSubgroup y (A.subgroupOf H)).map H.subtype =
      A ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup (y : G) A := by
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hAH,
      ← CFSG.GroupTheory.map_conjSubgroup H.subtype (A.subgroupOf H) y,
      Subgroup.map_subgroupOf_eq_of_le hAH]
    rfl
  rcases h with hbot | htop
  · left
    apply Subgroup.map_injective H.subtype_injective
    rw [hmap, hbot, Subgroup.map_bot]
  · right
    apply Subgroup.map_injective H.subtype_injective
    rw [hmap, htop, Subgroup.map_subgroupOf_eq_of_le hAH]

theorem nine3_card_barV (h : Nine3T79Setup V T A K S X p g x) :
    Nat.card (nine3BarV V K g) = Nat.card V := by
  have hinf : fusionOddCore ↥(nineH0 V K g) ⊓ V.subgroupOf (nineH0 V K g) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective
      (fusionOddCore ↥(nineH0 V K g) ⊓ V.subgroupOf (nineH0 V K g))
      (nineH0 V K g).subtype_injective).mp
    rw [Subgroup.map_inf _ _ _ (nineH0 V K g).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le (nine3_V_le_H0 h.hc), inf_comm]
    exact nine3_dcal_inf_fusionOddCore_eq_bot h
      ⟨1, (nineH0 V K g).one_mem, (CFSG.Quasithin.conjSubgroup_one V).symm⟩
  have hrel : (fusionOddCore ↥(nineH0 V K g)).relIndex (V.subgroupOf (nineH0 V K g)) =
      Nat.card (V.subgroupOf (nineH0 V K g)) := by
    have h := Subgroup.relIndex_mul_card (fusionOddCore ↥(nineH0 V K g))
      (V.subgroupOf (nineH0 V K g))
    rw [hinf, Subgroup.card_bot, mul_one] at h
    exact h
  change Nat.card ((V.subgroupOf (nineH0 V K g)).map
    (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)))) = Nat.card V
  rw [← Subgroup.relIndex_ker (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)))
      (K := V.subgroupOf (nineH0 V K g)), QuotientGroup.ker_mk', hrel]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (nine3_V_le_H0 h.hc)).toEquiv

theorem nine3_abelian_barE (h : Nine3T79Setup V T A K S X p g x) :
    IsMulCommutative (nine3BarE V K g) := by
  have hE : IsElemAbelian 2 ((nineI0 V K g).subgroupOf (nineH0 V K g)) :=
    IsElemAbelian.comap (h.hc.nineI0_isElemAbelian h.hI h.hN)
      (f := (nineH0 V K g).subtype) (nineH0 V K g).subtype_injective
  exact (hE.map (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)))).1

theorem nine3_normal_barE (h : Nine3T79Setup V T A K S X p g x) :
    (nine3BarE V K g).Normal := by
  have hInorm : ((nineI0 V K g).subgroupOf (nineH0 V K g)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer nine3_nineI0_le_H0).mpr h.hN
  exact hInorm.map _ (QuotientGroup.mk'_surjective _)

theorem nine3_isTI_barV (h : Nine3T79Setup V T A K S X p g x) :
    IsTI (nine3BarV V K g) := by
  have hVsub2 : IsPGroup 2 (V.subgroupOf (nineH0 V K g)) :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian
      (IsElemAbelian.comap h.hc.core.hyp7.1 (f := (nineH0 V K g).subtype)
        (nineH0 V K g).subtype_injective)
  have hVsubTI : IsTI (V.subgroupOf (nineH0 V K g)) :=
    nine3_isTI_subgroupOf (nine3_V_le_H0 h.hc) h.hc.core.hyp7.2.2
  have hZcenter := nine3_fusionOddCore_le_center h
  have hTZ : V.subgroupOf (nineH0 V K g) ≤
      Subgroup.centralizer (fusionOddCore ↥(nineH0 V K g) : Set ↥(nineH0 V K g)) := by
    intro v _
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_center_iff.mp (hZcenter hq) v).symm
  exact CFSG.GroupTheory.isTI_map_mk'_of_odd hVsub2 hVsubTI
    (nine3_odd_card_fusionOddCore ↥(nineH0 V K g)) hTZ

theorem nine3_iSub_le_pCoreOf_kSub_barV (h : Nine3T79Setup V T A K S X p g x) :
    iSub (nine3BarV V K g) (⊤ : Subgroup (nine3G1 V K g)) (nine3BarE V K g) ≤
      pCoreOf 2 (kSub (nine3BarV V K g) (⊤ : Subgroup (nine3G1 V K g)) (nine3BarE V K g)) := by
  refine iSup₂_le fun U hU => ?_
  exact (inf_le_inf_right _ (le_kSub hU)).trans
    (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 le_top)

theorem nine3_elemAbelian_barV (h : Nine3T79Setup V T A K S X p g x) :
    IsElemAbelian 2 (nine3BarV V K g) := by
  have hVsub : IsElemAbelian 2 (V.subgroupOf (nineH0 V K g)) :=
    IsElemAbelian.comap h.hc.core.hyp7.1 (f := (nineH0 V K g).subtype)
      (nineH0 V K g).subtype_injective
  exact hVsub.map (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)))

theorem nine3_fusionOddCoreOf_top_eq (X : Type*) [Group X] :
    fusionOddCoreOf (⊤ : Subgroup X) = fusionOddCore X := by
  rw [fusionOddCoreOf, ← CFSG.CGT.Timmesfeld75.fusionOddCore_map_mulEquiv
    (e := Subgroup.topEquiv (G := X))]
  rfl

theorem nine3_fusionOddCore_quotient_eq_bot (h : Nine3T79Setup V T A K S X p g x) :
    fusionOddCore (nine3G1 V K g) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2
      (Nat.card (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g))).ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mpr (nine3_odd_card_fusionOddCore ↥(nineH0 V K g))
  have hmap := CFSG.Semidihedral.Local.pPrimeCore_map_eq_of_coprime_ker 2
    (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)))
    (QuotientGroup.mk'_surjective _) hcop
  rw [← nine3_fusionOddCore_eq_pPrimeCore ↥(nineH0 V K g),
    ← nine3_fusionOddCore_eq_pPrimeCore (nine3G1 V K g)] at hmap
  rw [← hmap, QuotientGroup.map_mk'_self]

end CFSG.LocalAnalysis.WeakClosure81
