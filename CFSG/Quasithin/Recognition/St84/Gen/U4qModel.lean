module

import CFSG.Quasithin.Recognition.GoldschmidtF112RG24
public import CFSG.Quasithin.H13.U4ParOuterO2
public import CFSG.Quasithin.Vol2.Ch9Sec3FactsF112PfA
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13 CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.U4V CFSG.ASVolI
open scoped commutatorElement

namespace U4qModel

variable {m : ℕ} {K : Type} [Field K]

theorem pCoreOf_parP_eq (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m) :
    CFSG.Open.pCoreOf 2 (parP h) = radQ h := by
  have hodd : ¬ 2 ∣ (perfectCore (parP h)).relIndex (parP h) :=
    CFSG.Quasithin.H13.Ch9.F112Pf.not_two_dvd_relIndex
      (isSylowTwoOf_hypUnitriangular h) (hypUnitriangular_le_perfectCore_parP h hm)
  rw [pCoreOf_eq_of_odd (perfectCore_le (parP h))
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore (parP h))) hodd,
    pCoreOf_perfectCore_parP h hm]

theorem pCoreOf_parP2_eq (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m) :
    CFSG.Open.pCoreOf 2 (parP2 h) = radQ2 h := by
  have hodd : ¬ 2 ∣ (perfectCore (parP2 h)).relIndex (parP2 h) :=
    CFSG.Quasithin.H13.Ch9.F112Pf.not_two_dvd_relIndex
      (isSylowTwoOf_hypUnitriangular h) (hypUnitriangular_le_perfectCore_parP2 h hm)
  rw [pCoreOf_eq_of_odd (perfectCore_le (parP2 h))
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore (parP2 h))) hodd,
    pCoreOf_perfectCore_parP2_eq h hm]

noncomputable def quotPerfectCoreParP (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m) :
    oTwoQuot ↥(perfectCore (parP h)) ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField := by
  classical
  let φ : ↥(perfectCore (parP h)) →* Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
    (rhoF h).comp (Subgroup.inclusion (perfectCore_parP_le_parH h))
  have hφs : Function.Surjective φ := by
    intro A
    exact ⟨⟨levHom h A, levHom_range_le_perfectCore h hm ⟨A, rfl⟩⟩, rhoF_levHom h A⟩
  have hker : φ.ker = CFSG.pCore 2 ↥(perfectCore (parP h)) := by
    ext x
    rw [MonoidHom.mem_ker, CFSG.Quasithin.F1.mem_pCore_iff_coe]
    constructor
    · intro hx
      rw [pCoreOf_perfectCore_parP h hm]
      exact CFSG.Quasithin.H13.U4V.mem_radQ_of_rhoF_eq_one h hx
    · intro hx
      rw [pCoreOf_perfectCore_parP h hm] at hx
      have h1 : rho h (x : hypSU h 2 0) = 1 := (chi_rho_of_mem_radQ h hx).2
      apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
      ext i j
      change h.fixedField.subtype ((Matrix.SpecialLinearGroup.coeMonoidHom (φ x)) i j) =
        h.fixedField.subtype ((Matrix.SpecialLinearGroup.coeMonoidHom 1) i j)
      rw [show h.fixedField.subtype ((Matrix.SpecialLinearGroup.coeMonoidHom (φ x)) i j) =
          rho h (x : hypSU h 2 0) i j from
        congrFun (congrFun (map_rhoFMat h ⟨x, perfectCore_parP_le_parH h x.2⟩) i) j, h1]
      simp [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  exact (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)

end U4qModel

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem _root_.CFSG.Quasithin.IsOmega4MinusType.of_mulEquiv {L : Subgroup G} {N : Subgroup H}
    {m : ℕ} (e : ↥L ≃* ↥N) (h : IsOmega4MinusType N m) : IsOmega4MinusType L m := by
  classical
  obtain ⟨F, _, _, hF, α, hαs, hαk, β, hβim, hβk, hβe⟩ := h
  let g : ↥L →* H := N.subtype.comp e.toMonoidHom
  have hg : Function.Injective g := N.subtype_injective.comp e.injective
  have hN : (⊤ : Subgroup ↥L).map g = N := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hL : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hU : blockU N = (blockU (⊤ : Subgroup ↥L)).map g := by
    rw [← hN, CFSG.QuasithinUnique.Setup.Wreath.blockU_map_injective g hg (⊤ : Subgroup ↥L)]
  have hZ : blockZ N = (blockZ (⊤ : Subgroup ↥L)).map g := by
    rw [← hN, CFSG.QuasithinUnique.Setup.Wreath.blockZ_map_injective g hg (⊤ : Subgroup ↥L)]
  have hUL : blockU L = (blockU (⊤ : Subgroup ↥L)).map L.subtype := by
    conv_lhs => rw [← hL]
    exact CFSG.QuasithinUnique.Setup.Wreath.blockU_map_injective L.subtype
      L.subtype_injective (⊤ : Subgroup ↥L)
  have hZL : blockZ L = (blockZ (⊤ : Subgroup ↥L)).map L.subtype := by
    conv_lhs => rw [← hL]
    exact CFSG.QuasithinUnique.Setup.Wreath.blockZ_map_injective L.subtype
      L.subtype_injective (⊤ : Subgroup ↥L)
  have hBL : blockU L ≤ L := by
    rw [blockU, Subgroup.commutator_le]
    intro a ha b hb
    have haL : a ∈ L := pCoreOf_le 2 L ha
    have hbL : b ∈ L := hb
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem haL hbL) (L.inv_mem haL)) (L.inv_mem hbL)
  let eLtop : ↥(blockU L) ≃* ↥(blockU (⊤ : Subgroup ↥L)) :=
    (MulEquiv.subgroupCongr hUL).trans
      (((blockU (⊤ : Subgroup ↥L)).equivMapOfInjective L.subtype
        L.subtype_injective).symm)
  let eU : ↥(blockU L) ≃* ↥(blockU N) :=
    eLtop.trans (((blockU (⊤ : Subgroup ↥L)).equivMapOfInjective g hg).trans
      (MulEquiv.subgroupCongr hU.symm))
  have heU : ∀ u : ↥(blockU L),
      ((eU u : ↥(blockU N)) : H) = g ⟨(u : G), hBL u.2⟩ := by
    intro u
    simp only [eU, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom, eLtop,
      MulEquiv.subgroupCongr_apply, MulEquiv.symm_apply_apply]
    change g (((blockU (⊤ : Subgroup ↥L)).equivMapOfInjective L.subtype
      L.subtype_injective).symm ((MulEquiv.subgroupCongr hUL) u)) = g ⟨(u : G), hBL u.2⟩
    congr 1
    obtain ⟨x, hxmem, hxu⟩ := Subgroup.mem_map.mp (show (u : G) ∈
      (blockU (⊤ : Subgroup ↥L)).map L.subtype from hUL ▸ u.2)
    have hx2 : ((blockU (⊤ : Subgroup ↥L)).equivMapOfInjective L.subtype
        L.subtype_injective) ⟨x, hxmem⟩ = (MulEquiv.subgroupCongr hUL) u := by
      apply Subtype.ext
      exact hxu
    rw [← hx2, MulEquiv.symm_apply_apply]
    exact Subtype.ext hxu
  have hZmem : ∀ u : ↥(blockU L), ((eU u : ↥(blockU N)) : H) ∈ blockZ N ↔
      (u : G) ∈ blockZ L := by
    intro u
    rw [hZ, hZL, heU]
    exact (Subgroup.mem_map_iff_mem hg).trans
      (Subgroup.mem_map_iff_mem L.subtype_injective).symm
  refine ⟨F, inferInstance, inferInstance, hF, α.comp e.toMonoidHom,
    hαs.comp e.surjective, ?_, β.comp eU.toMonoidHom, ?_, ?_, ?_⟩
  · ext x
    change α (e x) = 1 ↔ x ∈ CFSG.pCore 2 ↥L
    constructor
    · intro hx
      have h1 : e x ∈ α.ker := MonoidHom.mem_ker.2 hx
      rw [hαk, ← CFSG.pCore_map_iso 2 e] at h1
      exact (Subgroup.mem_map_iff_mem e.injective).mp h1
    · intro hx
      have h1 : e x ∈ CFSG.pCore 2 ↥N := by
        rw [← CFSG.pCore_map_iso 2 e]
        exact Subgroup.mem_map_of_mem _ hx
      exact MonoidHom.mem_ker.1 (hαk ▸ h1)
  · intro X
    have himg : (∃ u : ↥(blockU L), Multiplicative.toAdd
        ((β.comp eU.toMonoidHom) u) = X) ↔
        (X.map (fun x => x ^ 2 ^ m)) = X.transpose := by
      rw [← hβim X]
      constructor
      · rintro ⟨u, hu⟩
        exact ⟨eU u, hu⟩
      · rintro ⟨u, hu⟩
        refine ⟨eU.symm u, ?_⟩
        show Multiplicative.toAdd (β (eU (eU.symm u))) = X
        rw [MulEquiv.apply_symm_apply]
        exact hu
    exact himg
  · ext u
    change β (eU u) = 1 ↔ u ∈ (blockZ L).subgroupOf (blockU L)
    rw [show β (eU u) = 1 ↔ eU u ∈ β.ker from MonoidHom.mem_ker, hβk,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hZmem u
  · intro ℓ u v huv
    have hrel : ((eU v : ↥(blockU N)) : H) = (e ℓ : H) *
        ((eU u : ↥(blockU N)) : H) * (e ℓ : H)⁻¹ := by
      rw [heU, heU, show ((e ℓ : ↥N) : H) = g ⟨(ℓ : G), ℓ.2⟩ from rfl]
      have h1 : (⟨(v : G), hBL v.2⟩ : ↥L) = ℓ * ⟨(u : G), hBL u.2⟩ * ℓ⁻¹ := by
        apply Subtype.ext
        simpa using huv
      rw [h1, map_mul, map_mul, map_inv]
    have := hβe (e ℓ) (eU u) (eU v) hrel
    simpa [MonoidHom.comp_apply] using this

end Transport

end CFSG.Quasithin.F112R
