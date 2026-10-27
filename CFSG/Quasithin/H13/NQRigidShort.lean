module

public import CFSG.Quasithin.H13.NQRigidShortCore
public import CFSG.Quasithin.H13.NQRigidInputs

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open CFSG.Quasithin
open scoped Pointwise

theorem stmtCPUShortBlock_holds :
    StmtCPUShortBlock := by
  intro H _ _ R hR2 hRpush K hK hF hKq hRK M hKM hRchar n hn F _ _ hFc ⟨e⟩
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := K ⊔ R with hB
  have hKB : K ≤ B := le_sup_left
  have hRB : R ≤ B := le_sup_right
  have hBK : B ≤ normalizer (K : Set H) := sup_le le_normalizer hRK
  have hKR : ((K ⊔ R : Subgroup H) : Set H) = (K : Set H) * (R : Set H) :=
    coe_mul_of_right_le_normalizer_left K R hRK
  set L := K.subgroupOf B with hL
  set S := R.subgroupOf B with hS
  have hLn : L.Normal := (normal_subgroupOf_iff_le_normalizer hKB).mpr hBK
  have hS2 : IsPGroup 2 S := hR2.comap_subtype
  have hBkr : ∀ x : ↥B, ∃ k ∈ L, ∃ r ∈ S, x = k * r := by
    intro x
    have hx : (x : H) ∈ ((K ⊔ R : Subgroup H) : Set H) := x.2
    rw [hKR] at hx
    obtain ⟨k, hk, r, hr, hkr⟩ := hx
    exact ⟨⟨k, hKB hk⟩, hk, ⟨r, hRB hr⟩, hr, Subtype.ext hkr.symm⟩
  have hKc : CFSG.IsCharacteristicP 2 ↥K :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥K 2).mpr hF
  let eL : ↥L ≃* ↥K := subgroupOfEquivOfLe hKB
  have hLc : CFSG.IsCharacteristicP 2 ↥L :=
    CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv eL.symm hKc
  have hBL : IsPGroup 2 (↥B ⧸ L) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, r, hr, rfl⟩ := hBkr x
    obtain ⟨n, hn⟩ := hS2 ⟨r, hr⟩
    refine ⟨n, ?_⟩
    have e2 : ((k : ↥B) : ↥B ⧸ L) = 1 := (QuotientGroup.eq_one_iff _).mpr hk
    have e3 : r ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    rw [QuotientGroup.mk_mul, e2, one_mul, ← QuotientGroup.mk_pow, e3, QuotientGroup.mk_one]
  have hchar : CFSG.IsCharacteristicP 2 ↥B :=
    CFSG.LocalAnalysis.characteristic_p_normal_p_extension hLc hBL
  have hSO : R = pCoreOf 2 (normalizer (R : Set H)) := by
    rw [pCoreOf]
    exact hRpush
  obtain ⟨-, -, -, hloc⟩ :=
    prime_radical_normalizers_localize_to_actual_Ccomponents Nat.prime_two hR2 hSO hK hKq
  rw [inf_eq_left.mpr hRK] at hloc
  have hpc : ∀ X : Subgroup ↥B, (pCoreOf 2 X).map B.subtype = pCoreOf 2 (X.map B.subtype) := by
    intro X
    rw [← NQBlock.map_inSubgroup_pCore]
    unfold inSubgroup pCoreOf
    try with_reducible rfl
  have hSmap : S.map B.subtype = R := by
    rw [hS, subgroupOf_map_subtype, inf_eq_left.mpr hRB]
  have hSO' : S = pCoreOf 2 (normalizer (S : Set ↥B)) := by
    apply map_injective B.subtype_injective
    rw [hpc, hSmap, hS, ← subgroupOf_normalizer_eq hRB, subgroupOf_map_subtype, inf_comm]
    exact hloc
  have hQS : CFSG.pCore 2 ↥B ≤ S :=
    NQTerm.le_of_isPGroup_of_le_normalizer hS2 hSO' CFSG.pCore_isPGroup (by
      rw [normalizer_eq_top_iff.mpr CFSG.pCore_normal]
      exact le_top)
  have hLQ : (CFSG.pCore 2 ↥B).subgroupOf L = CFSG.pCore 2 ↥L := by
    apply le_antisymm
    · refine SteinbergCC.le_pCore_of_normal_of_isPGroup ?_ CFSG.pCore_isPGroup.comap_subtype
      exact (CFSG.pCore_normal (p := 2) (G := ↥B)).subgroupOf L
    · intro x hx
      rw [mem_subgroupOf]
      exact CFSG.LyonsUnitaryFour.map_pCore_le_pCore_of_isSubnormal hLn.isSubnormal ⟨x, hx, rfl⟩
  let eKL : (↥L ⧸ (CFSG.pCore 2 ↥B).subgroupOf L) ≃* (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (QuotientGroup.quotientMulEquivOfEq hLQ).trans
      (QuotientGroup.congr _ _ eL (CFSG.LieType.SteinbergBR.pCore_map_equiv 2 eL))
  have hLq : CFSG.IsQuasisimple (↥L ⧸ (CFSG.pCore 2 ↥B).subgroupOf L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eKL.symm hKq
  have hLperf : Group.IsPerfect ↥L :=
    CFSG.QuasithinUnique.Setup.Lift.isPerfect_of_equiv eL.symm (Subgroup.isPerfect_iff.mpr hK.2.1)
  have hLM : ¬ L ≤ M.subgroupOf B := fun hle => hKM fun k hk =>
    mem_subgroupOf.mp (hle (show (⟨k, hKB hk⟩ : ↥B) ∈ L from hk))
  have hM : ∀ D : Subgroup ↥S, D.Characteristic → D ≠ ⊥ →
      normalizer ((D.map S.subtype : Subgroup ↥B) : Set ↥B) ≤ M.subgroupOf B := by
    intro D hDc hD1 x hx
    let eS : ↥S ≃* ↥R := subgroupOfEquivOfLe hRB
    have hD'c := characteristic_map_of_mulEquiv eS hDc
    have hD'1 : D.map eS.toMonoidHom ≠ ⊥ := by
      intro h0
      apply hD1
      rw [eq_bot_iff]
      intro d hd
      have h1 : eS d ∈ D.map eS.toMonoidHom := ⟨d, hd, rfl⟩
      rw [h0, mem_bot] at h1
      rw [mem_bot]
      exact eS.injective (h1.trans (map_one eS).symm)
    have himg : (D.map S.subtype).map B.subtype = (D.map eS.toMonoidHom).map R.subtype := by
      rw [map_map, map_map]
      rfl
    have h1 := coe_mem_normalizer_map hx
    rw [himg] at h1
    exact mem_subgroupOf.mpr (hRchar _ hD'c hD'1 h1)
  have hLS : (L : Set ↥B) * (S : Set ↥B) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨k, hk, r, hr, rfl⟩ := hBkr x
    exact ⟨k, hk, r, hr, rfl⟩
  have hshort := cpu_short_of_setup hchar hS2 hQS hLn hLS hLq hLperf hLM hM hn hFc
    ((centerQuotEquivOfMulEquiv eKL).trans e)
  have h1 := CFSG.QuasithinUnique.Setup.Wreath.IsShort2.map_of_injective B.subtype
    B.subtype_injective hshort
  rwa [hL, subgroupOf_map_subtype, inf_eq_left.mpr hKB] at h1

end CFSG.Quasithin.H13.NQRigid
