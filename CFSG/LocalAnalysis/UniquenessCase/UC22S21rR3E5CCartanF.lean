module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCartanE
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCartan
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CLink

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3e5c_card_barImage_beta {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    Nat.card ↥(barImage (conjClosure D.M L)
      (conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G))) =
      (2 ^ n) ^ 4 * (2 ^ n - 1) ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, heL, heK⟩ := uc22r3e5c_exists_bar2_mulEquiv_link hL hKC hKne hset hSz
  have hbar : (barImage (conjClosure D.M L) (conjClosure D.M L ⊓
      normalizer (D.T ⊓ conjClosure D.M L : Set G))).map e.toMonoidHom =
      (Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L))).prod
        (Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K))) :=
    uc22r3e5c_barImage_beta_eq_prod hL hKC hKne hset hSz heL heK
  have hULsyl : IsSylowTwoOf (barImage L (D.T ⊓ L)) ⊤ :=
    uc22r3e5c_isSylowTwoOf_barImage_inf_T hL
  have hUKsyl : IsSylowTwoOf (barImage K (D.T ⊓ K)) ⊤ :=
    uc22r3e5c_isSylowTwoOf_barImage_inf_T hKC
  let QL : Sylow 2 (Bar2 L) := hULsyl.2.1.toSylow (by
    rw [← Subgroup.relIndex_top_right (H := barImage L (D.T ⊓ L))]; exact hULsyl.2.2)
  let QK : Sylow 2 (Bar2 K) := hUKsyl.2.1.toSylow (by
    rw [← Subgroup.relIndex_top_right (H := barImage K (D.T ⊓ K))]; exact hUKsyl.2.2)
  have hQL : (QL : Subgroup (Bar2 L)) = barImage L (D.T ⊓ L) := IsPGroup.toSylow_coe _ _
  have hQK : (QK : Subgroup (Bar2 K)) = barImage K (D.T ⊓ K) := IsPGroup.toSylow_coe _ _
  have hKmem : K ∈ conjSetOf D.M L := by rw [hset]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hSzK : IsSz (Bar2 K) n := uc22r3e5c_isSz_of_mem_conjSetOf hKmem hSz
  have hcardL : Nat.card ↥(Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L))) =
      (2 ^ n) ^ 2 * (2 ^ n - 1) := by
    have h := CFSG.LieType.SuzukiSubgroups.card_normalizer_sylow_of_isSz
      (uc22r3e5c_quasithin_isSz_of_isSz hSz) QL
    rwa [hQL] at h
  have hcardK : Nat.card ↥(Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K))) =
      (2 ^ n) ^ 2 * (2 ^ n - 1) := by
    have h := CFSG.LieType.SuzukiSubgroups.card_normalizer_sylow_of_isSz
      (uc22r3e5c_quasithin_isSz_of_isSz hSzK) QK
    rwa [hQK] at h
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hbar,
    uc22r3e5c_card_prod, hcardL, hcardK]
  ring

private theorem uc22r3e5c_card_barImage_P {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    Nat.card ↥(barImage (conjClosure D.M L) (D.T ⊓ conjClosure D.M L)) = (2 ^ n) ^ 4 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, heL, heK⟩ := uc22r3e5c_exists_bar2_mulEquiv_link hL hKC hKne hset hSz
  have hKmem : K ∈ conjSetOf D.M L := by rw [hset]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hSzK : IsSz (Bar2 K) n := uc22r3e5c_isSz_of_mem_conjSetOf hKmem hSz
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
    uc22r3e5c_map_barImage_inf_eq_prod hL hKC hKne hset hSz heL heK,
    uc22r3e5c_card_prod, uc22r3e5c_card_barImage_inf_T hL hSz,
    uc22r3e5c_card_barImage_inf_T hKC hSzK]
  ring

theorem uc22r3e5c_card_beta {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    Nat.card ↥(conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G)) =
      Nat.card ↥(D.T ⊓ conjClosure D.M L) * (2 ^ n - 1) ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPX : D.T ⊓ conjClosure D.M L ≤ conjClosure D.M L := inf_le_right
  have hQleP : pCoreOf 2 (conjClosure D.M L) ≤ D.T ⊓ conjClosure D.M L :=
    uc22r3e5c_pCoreOf_le_of_sylow (uc22r3e5c_isSylowTwoOf_inf hL)
  have hQleBc : pCoreOf 2 (conjClosure D.M L) ≤
      conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G) :=
    le_inf (hQleP.trans hPX)
      (hQleP.trans (Subgroup.le_normalizer (H := D.T ⊓ conjClosure D.M L)))
  have hβ := uc22r3e5c_card_core_mul_card_barImage (X := conjClosure D.M L)
    (Y := conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G)) inf_le_left hQleBc
  have hP := uc22r3e5c_card_core_mul_card_barImage (X := conjClosure D.M L)
    (Y := D.T ⊓ conjClosure D.M L) hPX hQleP
  have hb := uc22r3e5c_card_barImage_beta hL hKC hKne hset hSz
  have hp := uc22r3e5c_card_barImage_P hL hKC hKne hset hSz
  rw [hb] at hβ
  rw [hp] at hP
  rw [← hβ, ← hP]
  ring

private theorem uc22r3e5c_isSolvable_normalizer_prod {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) {n : ℕ}
    (hSz : IsSz (Bar2 L) n) (hSzK : IsSz (Bar2 K) n) :
    Group.IsSolvable ↥((Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L))).prod
        (Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K)))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hULsyl : IsSylowTwoOf (barImage L (D.T ⊓ L)) ⊤ :=
    uc22r3e5c_isSylowTwoOf_barImage_inf_T hL
  have hUKsyl : IsSylowTwoOf (barImage K (D.T ⊓ K)) ⊤ :=
    uc22r3e5c_isSylowTwoOf_barImage_inf_T hKC
  let QL : Sylow 2 (Bar2 L) := hULsyl.2.1.toSylow (by
    rw [← Subgroup.relIndex_top_right (H := barImage L (D.T ⊓ L))]; exact hULsyl.2.2)
  let QK : Sylow 2 (Bar2 K) := hUKsyl.2.1.toSylow (by
    rw [← Subgroup.relIndex_top_right (H := barImage K (D.T ⊓ K))]; exact hUKsyl.2.2)
  have hQL : (QL : Subgroup (Bar2 L)) = barImage L (D.T ⊓ L) := IsPGroup.toSylow_coe _ _
  have hQK : (QK : Subgroup (Bar2 K)) = barImage K (D.T ⊓ K) := IsPGroup.toSylow_coe _ _
  haveI hLs : Group.IsSolvable ↥(Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L))) := by
    have h := uc22r3e5c_isSolvable_normalizer_sylow (uc22r3e5c_quasithin_isSz_of_isSz hSz) QL
    rwa [hQL] at h
  haveI hKs : Group.IsSolvable ↥(Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K))) := by
    have h := uc22r3e5c_isSolvable_normalizer_sylow (uc22r3e5c_quasithin_isSz_of_isSz hSzK) QK
    rwa [hQK] at h
  haveI : Group.IsSolvable (↥(Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L))) ×
      ↥(Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K)))) := inferInstance
  let ee := Subgroup.prodEquiv (Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L)))
    (Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K)))
  exact Group.isSolvable_of_isSolvable_injective (f := ee.toMonoidHom) ee.injective

private theorem uc22r3e5c_isSolvable_barImage_beta {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    Group.IsSolvable ↥(barImage (conjClosure D.M L) (conjClosure D.M L ⊓
      normalizer (D.T ⊓ conjClosure D.M L : Set G))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, heL, heK⟩ := uc22r3e5c_exists_bar2_mulEquiv_link hL hKC hKne hset hSz
  have hbar : (barImage (conjClosure D.M L) (conjClosure D.M L ⊓
      normalizer (D.T ⊓ conjClosure D.M L : Set G))).map e.toMonoidHom =
      (Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L))).prod
        (Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K))) :=
    uc22r3e5c_barImage_beta_eq_prod hL hKC hKne hset hSz heL heK
  have hKmem : K ∈ conjSetOf D.M L := by rw [hset]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hSzK : IsSz (Bar2 K) n := uc22r3e5c_isSz_of_mem_conjSetOf hKmem hSz
  haveI : Group.IsSolvable ↥((barImage (conjClosure D.M L) (conjClosure D.M L ⊓
      normalizer (D.T ⊓ conjClosure D.M L : Set G))).map e.toMonoidHom) := by
    rw [hbar]
    exact uc22r3e5c_isSolvable_normalizer_prod hL hKC hSz hSzK
  let ee := Subgroup.equivMapOfInjective (barImage (conjClosure D.M L)
    (conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G))) e.toMonoidHom
    e.injective
  exact Group.isSolvable_of_isSolvable_injective (f := ee.toMonoidHom) ee.injective

private noncomputable def uc22r3e5c_bar2Sub {X Bc : Subgroup G} (h : Bc ≤ X) :
    ↥(Bc.subgroupOf X) →* Bar2 X :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.subtype (Bc.subgroupOf X))

private theorem uc22r3e5c_bar2Sub_range {X Bc : Subgroup G} (h : Bc ≤ X) :
    (uc22r3e5c_bar2Sub h).range = barImage X Bc := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact Subgroup.mem_map.mpr ⟨y, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

private theorem uc22r3e5c_bar2Sub_ker {X Bc : Subgroup G} (h : Bc ≤ X) :
    (uc22r3e5c_bar2Sub h).ker = (CFSG.pCore 2 ↥X).subgroupOf (Bc.subgroupOf X) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥X) x

private theorem uc22r3e5c_isSolvable_pCore_subgroupOf {X Bc : Subgroup G}
    (hQle : CFSG.pCore 2 ↥X ≤ Bc.subgroupOf X) :
    Group.IsSolvable ↥((CFSG.pCore 2 ↥X).subgroupOf (Bc.subgroupOf X)) := by
  have h2 : IsPGroup 2 ↥((CFSG.pCore 2 ↥X).subgroupOf (Bc.subgroupOf X)) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQle).symm
  letI : Group.IsNilpotent ↥((CFSG.pCore 2 ↥X).subgroupOf (Bc.subgroupOf X)) :=
    IsPGroup.isNilpotent h2
  exact IsNilpotent.to_isSolvable

private theorem uc22r3e5c_isSolvable_quotient_bar2Sub {X Bc : Subgroup G} (h : Bc ≤ X)
    (hbs : Group.IsSolvable ↥(barImage X Bc)) :
    Group.IsSolvable (↥(Bc.subgroupOf X) ⧸ (uc22r3e5c_bar2Sub h).ker) := by
  have hfrange := uc22r3e5c_bar2Sub_range h
  haveI : Group.IsSolvable ↥(uc22r3e5c_bar2Sub h).range := by
    rw [hfrange]; exact hbs
  let ee := (QuotientGroup.quotientKerEquivRange (uc22r3e5c_bar2Sub h)).symm
  exact Group.isSolvable_of_surjective (f := ee.toMonoidHom) ee.surjective

theorem uc22r3e5c_isSolvable_beta {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    Group.IsSolvable ↥(conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQleP : pCoreOf 2 (conjClosure D.M L) ≤ D.T ⊓ conjClosure D.M L :=
    uc22r3e5c_pCoreOf_le_of_sylow (uc22r3e5c_isSylowTwoOf_inf hL)
  have hQleBc : pCoreOf 2 (conjClosure D.M L) ≤
      conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G) :=
    le_inf (hQleP.trans inf_le_right)
      (hQleP.trans (Subgroup.le_normalizer (H := D.T ⊓ conjClosure D.M L)))
  have hQleBc' : CFSG.pCore 2 ↥(conjClosure D.M L) ≤
      (conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G)).subgroupOf
        (conjClosure D.M L) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hQleBc ((CFSG.mem_openPCoreOf_iff (p := 2) (H := conjClosure D.M L) x).mpr hx)
  haveI : Group.IsSolvable ↥(uc22r3e5c_bar2Sub (inf_le_left :
      conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G) ≤
        conjClosure D.M L)).ker := by
    rw [uc22r3e5c_bar2Sub_ker]
    exact uc22r3e5c_isSolvable_pCore_subgroupOf hQleBc'
  haveI : Group.IsSolvable (↥((conjClosure D.M L ⊓ normalizer
      (D.T ⊓ conjClosure D.M L : Set G)).subgroupOf (conjClosure D.M L)) ⧸
      (uc22r3e5c_bar2Sub inf_le_left).ker) :=
    uc22r3e5c_isSolvable_quotient_bar2Sub inf_le_left
      (uc22r3e5c_isSolvable_barImage_beta hL hKC hKne hset hSz)
  haveI : Group.IsSolvable ↥((conjClosure D.M L ⊓ normalizer
      (D.T ⊓ conjClosure D.M L : Set G)).subgroupOf (conjClosure D.M L)) :=
    Group.isSolvable_of_subgroup_quotient (G := ↥((conjClosure D.M L ⊓ normalizer
      (D.T ⊓ conjClosure D.M L : Set G)).subgroupOf (conjClosure D.M L)))
      (uc22r3e5c_bar2Sub inf_le_left).ker
  let ee := (Subgroup.subgroupOfEquivOfLe (inf_le_left :
    conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G) ≤
      conjClosure D.M L)).symm
  exact Group.isSolvable_of_isSolvable_injective (f := ee.toMonoidHom) ee.injective

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
