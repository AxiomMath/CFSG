module

public import CFSG.Monster.Existence.Census.TwoClasses
public import CFSG.Monster.SteinbergMBXFullShortAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.B.TwoA

namespace InvolutionOddCore

variable {G : Type*} [Group G]

theorem pPrimeCore_two_eq_oddCore (G : Type*) [Group G] :
    CFSG.pPrimeCore 2 G = CFSG.oddCore G := by
  unfold CFSG.pPrimeCore CFSG.oddCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem oddCore_eq_bot_of_mulEquiv {H : Type*} [Group H] (e : G ≃* H)
    (h : CFSG.oddCore G = ⊥) : CFSG.oddCore H = ⊥ := by
  rw [CFSG.oddCore, sSup_eq_bot]
  rintro N ⟨hNn, hN⟩
  have hle : N.map e.symm.toMonoidHom ≤ CFSG.oddCore G :=
    le_sSup ⟨hNn.map _ e.symm.surjective,
      (Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective).symm ▸ hN⟩
  rw [h, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective (f := e.symm.toMonoidHom) _ e.symm.injective).1 hle

@[expose] def conjCentralizerEquiv (c s : G) :
    Subgroup.centralizer {s} ≃* Subgroup.centralizer {c * s * c⁻¹} where
  toFun g := ⟨c * g * c⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 g.2
    calc c * g * c⁻¹ * (c * s * c⁻¹) = c * ((g : G) * s) * c⁻¹ := by group
      _ = c * (s * g) * c⁻¹ := by rw [h]
      _ = c * s * c⁻¹ * (c * g * c⁻¹) := by group⟩
  invFun g := ⟨c⁻¹ * g * c, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 g.2
    calc c⁻¹ * g * c * s = c⁻¹ * ((g : G) * (c * s * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * s * c⁻¹) * g) * c := by rw [h]
      _ = s * (c⁻¹ * g * c) := by group⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv g := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by
    change c * ((a : G) * b) * c⁻¹ = c * a * c⁻¹ * (c * b * c⁻¹)
    group)

theorem map_subtype_centralizer {K : Subgroup G} (s : K) :
    (Subgroup.centralizer {s}).map K.subtype = K ⊓ Subgroup.centralizer {(s : G)} := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hh)
  · rintro ⟨hg, hc⟩
    refine ⟨⟨g, hg⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hc)

theorem oddCore_cent_of_isTwoBCentralizer {X : Type} [Group X] [Finite X] {t : X}
    (h : IsTwoBCentralizer t) : CFSG.oddCore (cent t) = ⊥ := by
  obtain ⟨-, -, hcent, -, -, -⟩ := h
  unfold CFSG.inSubgroup at hcent
  refine CFSG.ComponentClassification.BMCase.oddCore_eq_bot_of_selfCentralizing
    (R := CFSG.pCore 2 (cent t)) CFSG.pCore_isPGroup fun g hg => ?_
  have hg' : (g : X) ∈ Subgroup.centralizer
      (((CFSG.pCore 2 (cent t)).map (cent t).subtype : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hg r hr)
  obtain ⟨r, hr, hrg⟩ := hcent hg'
  rwa [show g = r from Subtype.ext hrg.symm]

theorem oddCore_Cfull :
    CFSG.oddCore Cfull = ⊥ := by
  have hZ : Nat.card ZstarF = 2 := by rw [ZstarF, Nat.card_zpowers, orderOf_tStarF]
  have hS : Even (Nat.card Shat) := by
    obtain ⟨-, -, -, m, -, hm⟩ := short_centralizer_generated_quotient_simple
    rw [Shat, ← Nat.card_congr (MonoidHom.ofInjective iotaD_injective).toEquiv, hm]
    exact (Nat.even_pow.2 ⟨even_two, by norm_num⟩).mul_right m
  exact CFSG.ComponentClassification.BMCase.oddCore_eq_bot_of_quotient_monolith hZ hS
    full_short_centralizer_almost_simple.{0}.2.1

theorem oddCore_cent_of_isConj_tGmat
    {t : Gmat} (ht : IsConj tGmat t) :
    CFSG.oddCore (cent t) = ⊥ := by
  have h0 : CFSG.oddCore (cent tGmat) = ⊥ :=
    oddCore_eq_bot_of_mulEquiv
      (((cent tGmat).equivMapOfInjective Gmat.subtype Gmat.subtype_injective).trans
        (MulEquiv.subgroupCongr (map_subtype_centralizer tGmat))).symm oddCore_Cfull
  obtain ⟨c, rfl⟩ := isConj_iff.1 ht
  exact oddCore_eq_bot_of_mulEquiv (conjCentralizerEquiv c tGmat) h0

end InvolutionOddCore

open InvolutionOddCore

theorem native_M_all_involution_centralizers_odd_core_free :
    ∀ t : Gmat, orderOf t = 2 →
      CFSG.pPrimeCore 2 (Subgroup.centralizer {t}) = ⊥ ∧
        CFSG.oddCore (Subgroup.centralizer {t}) = ⊥ := by
  intro t ht
  have h : CFSG.oddCore (Subgroup.centralizer {t}) = ⊥ := by
    rcases Census.generated_group_two_involution_classes t ht with hx | hs
    · exact oddCore_cent_of_isTwoBCentralizer (isTwoBCentralizer_Gmat t hx)
    · exact oddCore_cent_of_isConj_tGmat hs
  exact ⟨(pPrimeCore_two_eq_oddCore _).trans h, h⟩

end CFSG.Monster.Existence
