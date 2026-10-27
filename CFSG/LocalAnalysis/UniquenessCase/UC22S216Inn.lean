module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.GroupTheory.PermutingProducts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s216_exists_inner_permutes {L B T : Subgroup G}
    (hZ : center (BarInf L) = ⊥)
    (hinn : ∀ σ : MulAut (BarInf L), Odd (orderOf σ) →
      σ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L) (hT : IsPGroup 2 ↥T)
    (hBN : B ≤ normalizer (L : Set G)) (hBT : Permutes B T) (hBab : IsMulCommutative ↥B)
    (hBo : Odd (Nat.card ↥B)) :
    ∃ S Bφ : Subgroup (BarInf L), CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ ∧
      IsMulCommutative ↥Bφ ∧ Odd (Nat.card ↥Bφ) ∧
      (Bφ : Set (BarInf L)) * (S : Set (BarInf L)) = (S : Set (BarInf L)) * (Bφ : Set (BarInf L)) ∧
      ∀ b (hb : b ∈ B), ∃ x ∈ Bφ,
        inducedBarInfAutHom L ⟨b, hBN hb⟩ = MulAut.conj x ∧ orderOf x ∣ orderOf b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := normalizer (L : Set G) with hNdef
  set φ := inducedBarInfAutHom L with hφdef
  set X : Subgroup (MulAut (BarInf L)) :=
    (MulAut.conj : BarInf L →* MulAut (BarInf L)).range with hXdef
  have hinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ center (BarInf L) := by
      rw [mem_center_iff]
      intro w
      have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    rwa [hZ, mem_bot] at hzc
  let eX : BarInf L ≃* ↥X := MonoidHom.ofInjective hinj
  haveI : Finite ↥X := Finite.of_equiv _ eX.toEquiv
  set Bφ : Subgroup (MulAut (BarInf L)) := (B.subgroupOf N).map φ with hBφdef
  set Sφ : Subgroup (MulAut (BarInf L)) := ((T ⊓ N).subgroupOf N).map φ with hSφdef
  have hBX : Bφ ≤ X := by
    rintro _ ⟨⟨b, hbN⟩, hb, rfl⟩
    have hbB : b ∈ B := hb
    have hodd : Odd (orderOf (φ ⟨b, hbN⟩)) := by
      refine Odd.of_dvd_nat (Odd.of_dvd_nat hBo (Subgroup.orderOf_dvd_natCard B hbB)) ?_
      have h := orderOf_map_dvd φ ⟨b, hbN⟩
      rwa [Subgroup.orderOf_mk] at h
    exact hinn _ hodd
  have hperm : (Bφ : Set (MulAut (BarInf L))) * Sφ = Sφ * Bφ := by
    have h1 := CFSG.Quasithin.H23P4.mul_comm_inf_of_le hBT.symm hBN
    exact CFSG.GroupTheory.map_permutes_map φ
      (CFSG.Quasithin.H23P4.mul_comm_subgroupOf hBN inf_le_right h1.symm)
  have hpermX := CFSG.Quasithin.H23P4.mul_comm_subgroupOf hBX inf_le_right
    (CFSG.Quasithin.H23P4.mul_comm_inf_of_le hperm.symm hBX).symm
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf ((Sφ ⊓ X).subgroupOf X) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have hS2 : IsPGroup 2 ↥Sφ :=
        ((hT.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm).map φ
      exact (hS2.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm
    · let f : ↥L →* ↥X := (MulAut.conj : BarInf L →* MulAut (BarInf L)).rangeRestrict.comp
        (QuotientGroup.mk' (CFSG.solvableRadical ↥L))
      have hf : Function.Surjective f :=
        (MonoidHom.rangeRestrict_surjective _).comp (QuotientGroup.mk'_surjective _)
      have hle : ((T ⊓ L).subgroupOf L).map f ≤ (Sφ ⊓ X).subgroupOf X := by
        rintro _ ⟨⟨t, htL⟩, ht, rfl⟩
        have htT : t ∈ T := (mem_inf.mp (show t ∈ T ⊓ L from ht)).1
        rw [mem_subgroupOf]
        refine ⟨⟨⟨t, le_normalizer htL⟩, ?_, uc22s2113_inducedBarInfAutHom_of_mem htL⟩,
          (f ⟨t, htL⟩).2⟩
        show t ∈ T ⊓ N
        exact mem_inf.mpr ⟨htT, le_normalizer htL⟩
      have hidx : ¬ 2 ∣ ((T ⊓ L).subgroupOf L).index :=
        (CFSG.ABGLocalTools.isSylowOf_iff.mp hTL).2.2
      change ¬ 2 ∣ ((Sφ ⊓ X).subgroupOf X).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact fun h2 => hidx
        (h2.trans ((Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd _ hf)))
  have eBX : ↥(Bφ.subgroupOf X) ≃* ↥Bφ := subgroupOfEquivOfLe hBX
  haveI : IsMulCommutative ↥(B.subgroupOf N) := inferInstance
  haveI : IsMulCommutative ↥Bφ := Subgroup.map_isMulCommutative _ _
  have hBo' : Odd (Nat.card ↥(Bφ.subgroupOf X)) := by
    rw [Nat.card_congr eBX.toEquiv]
    refine Odd.of_dvd_nat hBo ?_
    have h := Subgroup.card_map_dvd (B.subgroupOf N) φ
    rwa [Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv] at h
  let e' : ↥X →* BarInf L := eX.symm.toMonoidHom
  have he' : Function.Bijective e' := eX.symm.bijective
  refine ⟨((Sφ ⊓ X).subgroupOf X).map e', (Bφ.subgroupOf X).map e', ⟨le_top, hS.2.1.map e', ?_⟩,
    Subgroup.map_isMulCommutative _ _, ?_, CFSG.GroupTheory.map_permutes_map e' hpermX, ?_⟩
  · change ¬ 2 ∣ (((Sφ ⊓ X).subgroupOf X).map e').relIndex ⊤
    rw [Subgroup.relIndex_top_right, Subgroup.index_map_of_bijective he']
    have h := hS.2.2
    change ¬ 2 ∣ ((Sφ ⊓ X).subgroupOf X).relIndex ⊤ at h
    rwa [Subgroup.relIndex_top_right] at h
  · rwa [Subgroup.card_map_of_injective he'.1]
  · intro b hb
    have hσ : φ ⟨b, hBN hb⟩ ∈ Bφ := ⟨⟨b, hBN hb⟩, hb, rfl⟩
    obtain ⟨y, hy⟩ := hBX hσ
    have hyX : ((eX y : ↥X) : MulAut (BarInf L)) = MulAut.conj y :=
      MonoidHom.ofInjective_apply hinj
    refine ⟨y, ⟨eX y, ?_, eX.symm_apply_apply y⟩, hy.symm, ?_⟩
    · show ((eX y : ↥X) : MulAut (BarInf L)) ∈ Bφ
      rw [hyX, hy]
      exact hσ
    · rw [← orderOf_injective _ hinj y, hy]
      have h := orderOf_map_dvd φ ⟨b, hBN hb⟩
      rwa [Subgroup.orderOf_mk] at h

end CFSG.LocalAnalysis.UniquenessCase.UC22
