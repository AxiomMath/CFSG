module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.RankThree.PartTwo.Sec16.Item16Res9ProofA10

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res9A10

open Equiv Subgroup

private theorem le_alternatingGroup_of_mulEquiv {K : Subgroup (Perm (Fin 10))}
    (e : K ≃* alternatingGroup (Fin 7)) : K ≤ alternatingGroup (Fin 10) := by
  classical
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup K := e.isSimpleGroup
  have hcardK : Nat.card K = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  intro k hk
  rw [Perm.mem_alternatingGroup]
  let f : K →* ℤˣ := Perm.sign.comp K.subtype
  rcases Subgroup.Normal.eq_bot_or_eq_top f.ker with hbot | htop
  · exfalso
    have hinj : Function.Injective f := f.ker_eq_bot_iff.mp hbot
    have hle : Nat.card K ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective f hinj
    have h2 : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_units_int
    rw [hcardK, h2] at hle
    omega
  · have hkker : (⟨k, hk⟩ : K) ∈ f.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    simpa [f] using (MonoidHom.mem_ker.mp hkker)

theorem eq_bot_of_le_normalizer {K T : Subgroup (Perm (Fin 10))}
    (hK : Nonempty (K ≃* alternatingGroup (Fin 7))) (hT : IsPGroup 2 T)
    (hTA : T ≤ alternatingGroup (Fin 10))
    (hKT : K ≤ Subgroup.normalizer (T : Set (Perm (Fin 10)))) : T = ⊥ := by
  classical
  obtain ⟨e⟩ := hK
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup K := e.isSimpleGroup
  let gK : K := e.symm ⟨cSeven, cSeven_mem⟩
  let yK : K := e.symm ⟨cFive, cFive_mem⟩
  have hgK : (gK : Perm (Fin 10)) ∈ K := gK.property
  have hyK : (yK : Perm (Fin 10)) ∈ K := yK.property
  have hg_order : orderOf (gK : Perm (Fin 10)) = 7 := by
    rw [Subgroup.orderOf_coe, ← e.orderOf_eq gK]
    rw [show e gK = ⟨cSeven, cSeven_mem⟩ from e.apply_symm_apply _]
    rw [Subgroup.orderOf_mk, orderOf_cSeven]
  have hy_order : orderOf (yK : Perm (Fin 10)) = 5 := by
    rw [Subgroup.orderOf_coe, ← e.orderOf_eq yK]
    rw [show e yK = ⟨cFive, cFive_mem⟩ from e.apply_symm_apply _]
    rw [Subgroup.orderOf_mk, orderOf_cFive]
  have h2520 : 2520 ∣ Nat.card K := by
    have hcard : Nat.card K = 2520 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    exact hcard ▸ dvd_rfl
  have hVK : T ⊓ K = ⊥ := by
    have hKN : K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup (Perm (Fin 10))) :
        Set (Perm (Fin 10))) :=
      (le_inf hKT Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hNnormal : ((T ⊓ K).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hKN
    haveI := hNnormal
    rcases Subgroup.Normal.eq_bot_or_eq_top ((T ⊓ K).subgroupOf K) with hbot | htop
    · rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.2⟩ : K) ∈ (T ⊓ K).subgroupOf K := hx
      rw [hbot] at hx'
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hx'))
    · exfalso
      have hKleT : K ≤ T := by
        intro x hx
        have hx' : (⟨x, hx⟩ : K) ∈ (T ⊓ K).subgroupOf K := by
          rw [htop]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_inf.mp hx').1
      have hK2 : IsPGroup 2 K := hT.to_le hKleT
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hgne : (⟨(gK : Perm (Fin 10)), hgK⟩ : K) ≠ 1 := by
        intro h
        have h1 : orderOf (⟨(gK : Perm (Fin 10)), hgK⟩ : K) = 1 := by
          rw [h, orderOf_one]
        rw [Subgroup.orderOf_mk, hg_order] at h1
        norm_num at h1
      have h2dvd : 2 ∣ orderOf (⟨(gK : Perm (Fin 10)), hgK⟩ : K) :=
        hK2.dvd_orderOf hgne
      rw [Subgroup.orderOf_mk, hg_order] at h2dvd
      norm_num at h2dvd
  have hC : ∀ N : Subgroup (Perm (Fin 10)), N ≤ K →
      K ≤ Subgroup.normalizer (N : Set (Perm (Fin 10))) →
      (yK : Perm (Fin 10)) ∈ N → ∃ x ∈ N, orderOf x = 7 := by
    intro N hNK hKN hyN
    have hNnormal : (N.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
    haveI := hNnormal
    have hNtop : N.subgroupOf K = ⊤ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (N.subgroupOf K) with hbot | htop
      · exfalso
        have hyN' : (⟨(yK : Perm (Fin 10)), hyK⟩ : K) ∈ N.subgroupOf K := hyN
        rw [hbot] at hyN'
        have hy1 : (⟨(yK : Perm (Fin 10)), hyK⟩ : K) = 1 := Subgroup.mem_bot.mp hyN'
        have hy1' : (yK : Perm (Fin 10)) = 1 := congrArg Subtype.val hy1
        have : orderOf (yK : Perm (Fin 10)) = 1 := by rw [hy1', orderOf_one]
        omega
      · exact htop
    refine ⟨(gK : Perm (Fin 10)), ?_, hg_order⟩
    have hgN' : (⟨(gK : Perm (Fin 10)), hgK⟩ : K) ∈ N.subgroupOf K := by
      rw [hNtop]
      exact Subgroup.mem_top _
    simpa [Subgroup.mem_subgroupOf] using hgN'
  have hy5 : IsPGroup 5 (Subgroup.zpowers (yK : Perm (Fin 10))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy_order, pow_one])
  exact eq_bot_of_normalized hTA (le_alternatingGroup_of_mulEquiv e) hT hKT hVK h2520
    hyK hy5 hC

theorem eq_bot_of_le_normalizer_of_mulEquiv {X : Type*} [Group X]
    (φ : X ≃* alternatingGroup (Fin 10))
    {K T : Subgroup X} (hK : Nonempty (K ≃* alternatingGroup (Fin 7)))
    (hT : IsPGroup 2 T)
    (hKT : K ≤ Subgroup.normalizer (T : Set X)) : T = ⊥ := by
  classical
  let f : X →* Perm (Fin 10) :=
    (Subgroup.subtype (alternatingGroup (Fin 10))).comp
      (φ : X →* alternatingGroup (Fin 10))
  have hf : Function.Injective f := by
    intro x y hxy
    apply φ.injective
    exact Subtype.ext hxy
  let K' : Subgroup (Perm (Fin 10)) := K.map f
  let T' : Subgroup (Perm (Fin 10)) := T.map f
  have hK' : Nonempty (K' ≃* alternatingGroup (Fin 7)) := by
    obtain ⟨e⟩ := hK
    exact ⟨(Subgroup.equivMapOfInjective K f hf).symm.trans e⟩
  have hT' : IsPGroup 2 T' := hT.map f
  have hTA' : T' ≤ alternatingGroup (Fin 10) := by
    intro x hx
    obtain ⟨t, _ht, rfl⟩ := hx
    exact (φ t).property
  have hKT' : K' ≤ Subgroup.normalizer (T' : Set (Perm (Fin 10))) := by
    calc K' = K.map f := rfl
      _ ≤ (Subgroup.normalizer (T : Set X)).map f := Subgroup.map_mono hKT
      _ ≤ Subgroup.normalizer (T.map f : Subgroup (Perm (Fin 10))) :=
        Subgroup.le_normalizer_map f
  have hT'bot : T' = ⊥ := eq_bot_of_le_normalizer hK' hT' hTA' hKT'
  exact (Subgroup.map_eq_bot_iff_of_injective (H := T) hf).mp hT'bot

end CFSG.RankThree.PartTwo.Sec16.Res9A10
