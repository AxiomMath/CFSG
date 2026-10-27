module

public import CFSG.RankThree.PartOne.HNB.Native
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.RankThree.PartOne.HNB

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.Classical

theorem nativeData_of_mulEquiv {M N : Type} [Group M] [Group N] (e : M ≃* N) (h : NativeData N) :
    NativeData M := by
  obtain ⟨f, t, K, Y, hf5, hKf, hKn, hfK, hKs, hKna, hKm, hYK, hYsl, htY, ht2, htc⟩ := h
  set φ : N →* M := e.symm.toMonoidHom with hφ
  have hinj : Function.Injective φ := e.symm.injective
  have eK : K ≃* K.map φ := K.equivMapOfInjective φ hinj
  have eY : Y ≃* Y.map φ := Y.equivMapOfInjective φ hinj
  refine ⟨φ f, φ t, K.map φ, Y.map φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [orderOf_injective φ hinj f]
    exact hf5
  · rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hKf hk)
    rw [← map_mul, ← map_mul, this]
  · refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, hk, hkn⟩ := Subgroup.mem_subgroupOf.mp hn
    have hgC : e (g : M) ∈ Subgroup.centralizer ({f} : Set N) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp g.2
      have h2 : e ((g : M) * e.symm f) = e (e.symm f * (g : M)) := congrArg e h1
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
    have hconj := hKn.conj_mem ⟨k, hKf hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨e (g : M), hgC⟩
    have hconj' := Subgroup.mem_subgroupOf.mp hconj
    rw [Subgroup.mem_subgroupOf]
    refine ⟨e (g : M) * k * (e (g : M))⁻¹, hconj', ?_⟩
    change e.symm (e (g : M) * k * (e (g : M))⁻¹) = (g : M) * (n : M) * (g : M)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    have : e.symm k = (n : M) := hkn
    rw [this]
  · rw [← MonoidHom.map_zpowers, ← Subgroup.map_inf_eq _ _ φ hinj, hfK, Subgroup.map_bot]
  · exact eK.isSimpleGroup_congr.mp hKs
  · obtain ⟨a, b, hab⟩ := hKna
    exact ⟨eK a, eK b, fun h => hab (eK.injective (by rw [map_mul, map_mul, h]))⟩
  · exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv eK.symm hKm
  · exact Subgroup.map_mono hYK
  · obtain ⟨σ⟩ := hYsl
    exact ⟨eY.symm.trans σ⟩
  · exact Subgroup.mem_map_of_mem φ htY
  · rw [orderOf_injective φ hinj t]
    exact ht2
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, htc y hy]

theorem exists_sl2_of_psu35 {G : Type} [Group G] (hB : StatedClassicalModel G .PSU 3 5 1) :
    ∃ Y : Subgroup G, Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  obtain ⟨⟨hp, hf, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hB
  have hU : UnitaryFieldData 5 1 K := ⟨hp, hf, by rw [hK]; norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  set φ : G ≃* unitaryPSU hU 3 := e.trans (unitaryPSUEquiv hU (by norm_num)).symm with hφ
  let Yu : Subgroup (unitaryPSU hU 3) := (coordBlock 5 1 K 0).map (unitaryProj hU 3)
  have hinj := injective_unitaryProj_comp_coordBlock hU 0
  obtain ⟨ψ⟩ := nonempty_coordBlock_mulEquiv hU 0
  have hrange : ((unitaryProj hU 3).comp (coordBlock 5 1 K 0).subtype).range = Yu := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eY : coordBlock 5 1 K 0 ≃* Yu :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hfin := hU.finite
  let _ : Fintype hU.fixedField := Fintype.ofFinite _
  have hcard : Fintype.card hU.fixedField = 5 := by
    rw [← Nat.card_eq_fintype_card, UnitaryFieldData.card_fixedField hU]
    norm_num
  let eF : ZMod 5 ≃+* hU.fixedField := ZMod.ringEquivOfPrime hU.fixedField hp hcard
  refine ⟨Yu.map φ.symm.toMonoidHom, ⟨?_⟩⟩
  exact (Yu.equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective).symm.trans
    (eY.symm.trans (ψ.trans
      (CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2) eF.symm)))

theorem exists_central_involution_sl2 :
    ∃ t0 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), orderOf t0 = 2 ∧
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), A * t0 = t0 * A := by
  have h : ∃ t0 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), t0 ^ 2 = 1 ∧ t0 ≠ 1 ∧
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), A * t0 = t0 * A := by
    decide +kernel
  obtain ⟨t0, h1, h2, h3⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨t0, orderOf_eq_prime h1 h2, h3⟩

end CFSG.RankThree.PartOne.HNB
