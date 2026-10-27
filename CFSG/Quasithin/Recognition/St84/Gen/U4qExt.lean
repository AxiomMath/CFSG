module

import CFSG.Quasithin.H13.U4ParOuterFacts
import CFSG.Quasithin.Recognition.GoldschmidtF112RG24
import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526U4ext
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Recognition.St84.Gen.U4qVFact

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.U4V
open CFSG.Quasithin.H13.U4Ext CFSG.Quasithin.F1 CFSG.Quasithin.B6

variable {G : Type} [Group G] [Finite G]

private theorem isSolvable_quotient_of_index_two {Y : Type} [Group Y] {N : Subgroup Y}
    [N.Normal] (hN : N.index = 2) : Group.IsSolvable (Y ⧸ N) := by
  have hsq : ∀ z : Y ⧸ N, z * z = 1 := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact Subgroup.mul_self_mem_of_index_two hN x
  refine Group.isSolvable_of_comm fun a b => ?_
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq (a * b))).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha, hb]

private theorem isSolvable_inf_of_map_eq {Y : Type} [Group Y] {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) {ψ : hypSU h 2 0 →* Y} (hψ : Function.Injective ψ)
    (hidx : ψ.range.index = 2) {M₁ M₂ : Subgroup Y}
    (hint : (M₁ ⊓ M₂) ⊓ ψ.range = (parP h ⊓ parP2 h).map ψ) :
    Group.IsSolvable ↥(M₁ ⊓ M₂) := by
  classical
  haveI hnorm : ψ.range.Normal := Subgroup.normal_of_index_eq_two hidx
  haveI hpar : Group.IsSolvable ↥(parP h ⊓ parP2 h) := isSolvable_parP_inf_parP2 h
  let X : Subgroup Y := M₁ ⊓ M₂
  haveI hY₀solv : Group.IsSolvable ↥(X ⊓ ψ.range) := by
    have hX : X ⊓ ψ.range = (parP h ⊓ parP2 h).map ψ := hint
    rw [hX]
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective (parP h ⊓ parP2 h) ψ hψ).toMonoidHom)
      (Subgroup.equivMapOfInjective (parP h ⊓ parP2 h) ψ hψ).surjective
  let Nx : Subgroup ↥X := ψ.range.subgroupOf X
  haveI hNsolv : Group.IsSolvable ↥Nx := by
    have hNx : Nx = (X ⊓ ψ.range).subgroupOf X := by
      ext x
      simp only [Nx, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
    rw [hNx]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left : X ⊓ ψ.range ≤ X)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : X ⊓ ψ.range ≤ X)).injective
  haveI hquot : Group.IsSolvable (Y ⧸ ψ.range) :=
    isSolvable_quotient_of_index_two hidx
  have hker : ((QuotientGroup.mk' ψ.range).comp X.subtype).ker = Nx := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Nx, Subgroup.mem_subgroupOf]
    rfl
  exact Group.isSolvable_of_ker_le_range Nx.subtype
    ((QuotientGroup.mk' ψ.range).comp X.subtype)
    (le_of_eq (hker.trans (Subgroup.range_subtype (H := Nx)).symm))

theorem u4q_ident_ext {L1 L2 S : Subgroup G} {f : ℕ} (hF : F112Hyp L1 L2 S) (hf : 2 ≤ f)
    (hA : IsU4ExtTwo f (f112Amalgam L1 L2 S)) :
    Group.IsSolvable ↥(bigB L1 L2 S) ∧
      pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ perfectCore (L1 ⊔ bigB L1 L2 S) ∧
      pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ perfectCore (L2 ⊔ bigB L1 L2 S) ∧
      ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K),
        (Nonempty (↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ≃* ↥(radQ h)) ∧
          Nonempty (↥(perfectCore (L2 ⊔ bigB L1 L2 S)) ≃* ↥(perfectCore (parP2 h)))) ∨
        Nonempty (↥(perfectCore (L2 ⊔ bigB L1 L2 S)) ≃* ↥(perfectCore (parP h))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let V2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  obtain ⟨Y₀, _, Yh, _, ι, hY₀, hι, hidx, Th, Mh₁, Mh₂, hpair, ⟨Φ⟩⟩ := hA
  obtain ⟨K', _, hK', ⟨e⟩⟩ := exists_hypSU_equiv_of_lieModel hY₀
  have hfin : Finite Yh :=
    (exists_embedding (Or.inr ⟨Y₀, inferInstance, ι, hY₀, hι, hidx⟩)).1
  haveI : Finite Yh := hfin
  have hψ₀ : Function.Injective (ι.comp e.toMonoidHom) := hι.comp e.injective
  have hidx₀ : (ι.comp e.toMonoidHom).range.index ≤ 2 := by
    calc (ι.comp e.toMonoidHom).range.index = ι.range.index := by
          rw [CFSG.Quasithin.H13.F431.U42.Am.range_comp_mulEquiv]
      _ ≤ 2 := le_of_eq hidx
  obtain ⟨ψ, hψ, hrange, hU⟩ := exists_adapted hK' hψ₀ hidx₀ hpair.1
  have hidx2 : ψ.range.index = 2 := by
    rw [hrange, CFSG.Quasithin.H13.F431.U42.Am.range_comp_mulEquiv]
    exact hidx
  rw [← hrange] at hidx₀ hU
  haveI hnorm : ψ.range.Normal := Subgroup.normal_of_index_eq_two hidx2
  have hC : Subgroup.centralizer (ψ.range : Set Yh) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨hz2, hzc⟩ := mem_center_of_mem_centralizer_range hK' hψ hidx2 hz
    have hzN : z ∈ Subgroup.normalizer (Th : Set Yh) := Subgroup.center_le_normalizer _ hzc
    have hz₁ : z ∈ Mh₁ := ((hpair.2.2 Mh₁).mpr (Or.inl rfl)).2 hzN
    have hz₂ : z ∈ Mh₂ := ((hpair.2.2 Mh₂).mpr (Or.inr rfl)).2 hzN
    obtain ⟨x, hxz⟩ : ∃ x : ↥(V1 ⊓ V2),
        ((isoφ12 Φ x : ↥(Mh₁ ⊓ Mh₂)) : Yh) = z :=
      ⟨(isoφ12 Φ).symm ⟨z, Subgroup.mem_inf.mpr ⟨hz₁, hz₂⟩⟩,
        by rw [MulEquiv.apply_symm_apply]⟩
    have hx2 : x * x = 1 := (isoφ12 Φ).injective (by
      apply Subtype.ext
      rw [map_mul, map_one, Subgroup.coe_mul, hxz, hz2, OneMemClass.coe_one])
    have hcen := le_centralizer_of_isoφ12_mem_center Φ x (by rw [hxz]; exact hzc)
    have hBle : bigB L1 L2 S ≤ L1 ⊔ L2 ⊔ S :=
      sup_le (sup_le ((borelOf_le L1 S).trans (le_sup_left.trans le_sup_left))
        ((borelOf_le L2 S).trans (le_sup_right.trans le_sup_left))) le_sup_right
    have hV1X : V1 ≤ L1 ⊔ L2 ⊔ S := sup_le (le_sup_left.trans le_sup_left) hBle
    have hBle' : bigB L1 L2 S ≤ V1 ⊔ V2 :=
      (le_sup_right : bigB L1 L2 S ≤ V1).trans le_sup_left
    have hX : L1 ⊔ L2 ⊔ S ≤ V1 ⊔ V2 :=
      sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
        ((le_sup_right : S ≤ bigB L1 L2 S).trans hBle')
    have hmem := mem_pCoreOf_of_le_centralizer (hV1X (Subgroup.mem_inf.mp x.2).1)
      (congrArg Subtype.val hx2) (hX.trans hcen)
    rw [hF.1.o2, Subgroup.mem_bot] at hmem
    rw [← hxz, show x = 1 from Subtype.ext hmem, map_one, OneMemClass.coe_one]
  obtain ⟨y₀, hy₀, -, hact⟩ := exists_frob_elt hK' ψ hψ hidx2 hC
  obtain ⟨i₂, hM₂N, hM₂R⟩ := inf_eq_of_adapted hK' ψ hψ hidx₀ hpair hU
  obtain ⟨i₁, hM₁N, hM₁R⟩ :=
    inf_eq_of_adapted hK' ψ hψ hidx₀ (isYAmalgamPair_swap hpair) hU
  have hii : i₁ ≠ i₂ := by
    intro h
    apply hpair.2.1
    rw [hM₁N, hM₂N, h]
  haveI hquot : Group.IsSolvable (Yh ⧸ ψ.range) := isSolvable_quotient_of_index_two hidx2
  fin_cases i₁
  · fin_cases i₂
    · exact absurd rfl hii
    ·
      have hM₁ : Mh₁ = Subgroup.normalizer
          (((parP hK').map ψ : Subgroup Yh) : Set Yh) := hM₁N
      have hM₁ψ : Mh₁ ⊓ ψ.range = (parP hK').map ψ := hM₁R
      have hM₂ : Mh₂ = Subgroup.normalizer
          (((parP2 hK').map ψ : Subgroup Yh) : Set Yh) := hM₂N
      have hM₂ψ : Mh₂ ⊓ ψ.range = (parP2 hK').map ψ := hM₂R
      obtain ⟨S₀, hS₀, -⟩ := exists_isSylowTwoOf_ge (J := Mh₂ ⊓ Mh₁) (X := ⊥)
        IsPGroup.of_bot bot_le
      obtain ⟨hc₂, hc₁, -⟩ := ext_facts hK' hf hψ hidx2 hC
        (isYAmalgamPair_swap hpair) hU hM₂ hM₂ψ hM₁ hM₁ψ hS₀
      have hO₁ : pCoreOf 2 Mh₁ = (radQ hK').map ψ :=
        pCoreOf_normalizer_parP hK' hact hf hψ hidx2 hy₀ hM₁ hM₁ψ
      have hpc₂ : perfectCore Mh₂ = (perfectCore (parP2 hK')).map ψ :=
        perfectCore_eq_of_inf_range hK' hidx2 hM₂ψ
      have hcore₁ : pCoreOf 2 V1 = pCoreOf 2 (perfectCore V1) :=
        pCoreOf_eq_of_equiv (isoφ1 Φ) hc₁
      have hcore₂ : pCoreOf 2 V2 = pCoreOf 2 (perfectCore V2) :=
        pCoreOf_eq_of_equiv (isoφ2 Φ) hc₂
      have hle₁ : pCoreOf 2 V1 ≤ perfectCore V1 :=
        hcore₁ ▸ CFSG.openPCoreOf_le 2 (perfectCore V1)
      have hle₂ : pCoreOf 2 V2 ≤ perfectCore V2 :=
        hcore₂ ▸ CFSG.openPCoreOf_le 2 (perfectCore V2)
      have hNsplit : (Mh₁ ⊓ Mh₂) ⊓ ψ.range =
          (Mh₁ ⊓ ψ.range) ⊓ (Mh₂ ⊓ ψ.range) := by
        ext z
        simp only [Subgroup.mem_inf]
        tauto
      have hint : (Mh₁ ⊓ Mh₂) ⊓ ψ.range = (parP hK' ⊓ parP2 hK').map ψ := by
        rw [hNsplit, hM₁ψ, hM₂ψ,
          ← Subgroup.map_inf (parP hK') (parP2 hK') ψ hψ]
      haveI hX : Group.IsSolvable ↥(Mh₁ ⊓ Mh₂) :=
        isSolvable_inf_of_map_eq hK' hψ hidx2 hint
      haveI hV : Group.IsSolvable ↥(V1 ⊓ V2) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (isoφ12 Φ).toMonoidHom) (isoφ12 Φ).injective
      have hB : Group.IsSolvable ↥(bigB L1 L2 S) :=
        Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion (le_inf le_sup_right le_sup_right :
            bigB L1 L2 S ≤ V1 ⊓ V2)) (Subgroup.inclusion_injective _)
      have hO₁V : Nonempty (↥(pCoreOf 2 V1) ≃* ↥(radQ hK')) :=
        ⟨(pCoreOfMulEquiv (isoφ1 Φ) 2).trans
          ((MulEquiv.subgroupCongr hO₁).trans
            (Subgroup.equivMapOfInjective (radQ hK') ψ hψ).symm)⟩
      have hpcV2 : Nonempty (↥(perfectCore V2) ≃*
          ↥(perfectCore (parP2 hK'))) := by
        obtain ⟨e₂⟩ := nonempty_perfectCore_mulEquiv (isoφ2 Φ)
        exact ⟨e₂.trans ((MulEquiv.subgroupCongr hpc₂).trans
          (Subgroup.equivMapOfInjective (perfectCore (parP2 hK')) ψ hψ).symm)⟩
      exact ⟨hB, hle₁, hle₂, ⟨K', inferInstance, hK', Or.inl ⟨hO₁V, hpcV2⟩⟩⟩
  · fin_cases i₂
    ·
      have hM₁ : Mh₁ = Subgroup.normalizer
          (((parP2 hK').map ψ : Subgroup Yh) : Set Yh) := hM₁N
      have hM₁ψ : Mh₁ ⊓ ψ.range = (parP2 hK').map ψ := hM₁R
      have hM₂ : Mh₂ = Subgroup.normalizer
          (((parP hK').map ψ : Subgroup Yh) : Set Yh) := hM₂N
      have hM₂ψ : Mh₂ ⊓ ψ.range = (parP hK').map ψ := hM₂R
      obtain ⟨S₀, hS₀, -⟩ := exists_isSylowTwoOf_ge (J := Mh₁ ⊓ Mh₂) (X := ⊥)
        IsPGroup.of_bot bot_le
      obtain ⟨hc₁, hc₂, -⟩ := ext_facts hK' hf hψ hidx2 hC hpair hU
        hM₁ hM₁ψ hM₂ hM₂ψ hS₀
      have hpc₂ : perfectCore Mh₂ = (perfectCore (parP hK')).map ψ :=
        perfectCore_eq_of_inf_range hK' hidx2 hM₂ψ
      have hcore₁ : pCoreOf 2 V1 = pCoreOf 2 (perfectCore V1) :=
        pCoreOf_eq_of_equiv (isoφ1 Φ) hc₁
      have hcore₂ : pCoreOf 2 V2 = pCoreOf 2 (perfectCore V2) :=
        pCoreOf_eq_of_equiv (isoφ2 Φ) hc₂
      have hle₁ : pCoreOf 2 V1 ≤ perfectCore V1 :=
        hcore₁ ▸ CFSG.openPCoreOf_le 2 (perfectCore V1)
      have hle₂ : pCoreOf 2 V2 ≤ perfectCore V2 :=
        hcore₂ ▸ CFSG.openPCoreOf_le 2 (perfectCore V2)
      have hNsplit : (Mh₁ ⊓ Mh₂) ⊓ ψ.range =
          (Mh₁ ⊓ ψ.range) ⊓ (Mh₂ ⊓ ψ.range) := by
        ext z
        simp only [Subgroup.mem_inf]
        tauto
      have hint : (Mh₁ ⊓ Mh₂) ⊓ ψ.range = (parP hK' ⊓ parP2 hK').map ψ := by
        rw [hNsplit, hM₁ψ, hM₂ψ,
          inf_comm ((parP2 hK').map ψ) ((parP hK').map ψ),
          ← Subgroup.map_inf (parP hK') (parP2 hK') ψ hψ]
      haveI hX : Group.IsSolvable ↥(Mh₁ ⊓ Mh₂) :=
        isSolvable_inf_of_map_eq hK' hψ hidx2 hint
      haveI hV : Group.IsSolvable ↥(V1 ⊓ V2) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (isoφ12 Φ).toMonoidHom) (isoφ12 Φ).injective
      have hB : Group.IsSolvable ↥(bigB L1 L2 S) :=
        Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion (le_inf le_sup_right le_sup_right :
            bigB L1 L2 S ≤ V1 ⊓ V2)) (Subgroup.inclusion_injective _)
      have hpcV2 : Nonempty (↥(perfectCore V2) ≃*
          ↥(perfectCore (parP hK'))) := by
        obtain ⟨e₂⟩ := nonempty_perfectCore_mulEquiv (isoφ2 Φ)
        exact ⟨e₂.trans ((MulEquiv.subgroupCongr hpc₂).trans
          (Subgroup.equivMapOfInjective (perfectCore (parP hK')) ψ hψ).symm)⟩
      exact ⟨hB, hle₁, hle₂, ⟨K', inferInstance, hK', Or.inr hpcV2⟩⟩
    · exact absurd rfl hii

end CFSG.Quasithin.F112R
