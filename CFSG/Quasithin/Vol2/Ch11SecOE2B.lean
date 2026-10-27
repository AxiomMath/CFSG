module

public import CFSG.Quasithin.Vol2.Ch11SecOE2A
public import CFSG.Quasithin.H13.NQBlockRadicalR2

public section

namespace CFSG.Quasithin.Vol2.Ch11

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem tmp1_3_3_holds
    : Tmp1_3_3 := by
  intro G _ _ T L p hs hnab hQ hT hL hLq hp hp2 hpF
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hs
  have hTL : T ≤ normalizer (L : Set G) :=
    H13.NQBlock.le_normalizer_of_not_isQuasisimple hs hnab hQ hL hLq
  have hLT2 : pCoreOf 2 (L ⊔ T) ≠ ⊥ := hL.2.2.2
  have hsqtk := (H13.NQCore.qt_positive_two_core_SQTK hnab hQ hLT2).2
  have hSQT : CFSG.IsStronglyQuasithin ↥L := by
    have h := hsqtk.1
    rw [CFSG.SectionRank.isStronglyQuasithin_iff] at h ⊢
    intro q hq hq2
    exact (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt (Subgroup.inclusion le_sup_left)
      (Subgroup.inclusion_injective le_sup_left)).trans (h q hq hq2)
  have hLc : L ∈ cComp (L ⊔ T) := cComp_of_isLocal hL
  have hLself : L ∈ cComp L := cComp_mem_of_le hLc le_rfl le_sup_left
  have hLtop : CFSG.IsCComponent (⊤ : Subgroup ↥L) := by
    have h3 := mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hLself)
    rwa [subgroupOf_self] at h3
  have hpF' : p ∈ (Nat.card (CFSG.fittingSubgroup (↥L ⧸ CFSG.pCore 2 ↥L))).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpF, Nat.card_pos.ne'⟩
  set Q : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := CFSG.pCore p (↥L ⧸ CFSG.pCore 2 ↥L)
  set B : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := closure {a | a ∈ Q ∧ a ^ p = 1}
  set E : Subgroup ↥L := B.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  set Xq : Subgroup ↥L := closure {e | e ∈ E ∧ Odd (orderOf e)}
  obtain ⟨hp5, hXc, hW', -, -, -, ⟨-, φ, -, -, -, -, -⟩, hshape, -⟩ :=
    H13.NQBlock.canonical_prime_witness hSQT hLtop hLq hpF' Q B E Xq rfl rfl rfl rfl
  have hXeq : xiP L p = Xq.map L.subtype := OE2.xiP_eq_map L p
  rw [hXeq]
  set X : Subgroup G := Xq.map L.subtype
  have hXL : X ≤ L := map_subtype_le _
  have hX1 : X = oTwoUpper X := by
    rw [← hXeq, xiP]
    exact (le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun x hx =>
      mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2)).symm
  have hXsub : X.subgroupOf L = Xq := comap_map_eq_self_of_injective L.subtype_injective Xq
  have hXchar : (X.subgroupOf L).Characteristic := hXsub ▸ hXc
  have hTX : T ≤ normalizer (X : Set G) :=
    hTL.trans (H13.NQSetup.normalizer_le_normalizer_of_characteristic hXL hXchar)
  have hO2 : pCoreOf 2 (X ⊔ T) ≠ ⊥ := by
    have h1 : pCoreOf 2 (L ⊔ T) ≤ T :=
      pCoreOf_le_of_quasithinIsSylowTwo hT (le_sup_right.trans le_normalizer)
    have h2 : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (X ⊔ T) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h1.trans le_sup_right)
        ((sup_le_sup_right hXL T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T))
    exact fun h => hLT2 (le_bot_iff.mp (h ▸ h2))
  have hirr : ∀ M : Subgroup ((↥Xq ⧸ CFSG.pCore 2 ↥Xq) ⧸ frattini (↥Xq ⧸ CFSG.pCore 2 ↥Xq)),
      (∀ s : ↥L, (s : G) ∈ T → ∀ w ∈ M, H13.NQBlock.residualAction Xq s w ∈ M) →
        M = ⊥ ∨ M = ⊤ := by
    intro M hM
    have hTJs : IsSylowTwoOf T (normalizer (L : Set G)) :=
      isSylowTwoOf_of_quasithinIsSylowTwo hT hTL
    have hTLs : IsSylowTwoOf (T ⊓ L) L := A4.isSylowTwoOf_inf_normal hTJs le_normalizer le_rfl
    have hTLp : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
      hTLs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTLs.1).symm
    have hTLi : ¬ 2 ∣ ((T ⊓ L).subgroupOf L).index := hTLs.2.2
    set S' : Sylow 2 ↥L := hTLp.toSylow hTLi
    have hS'c : (S' : Subgroup ↥L) = (T ⊓ L).subgroupOf L := IsPGroup.toSylow_coe hTLp hTLi
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hLself)
    have hW := hW'.card_W
    have : IsMulCommutative ((↥Xq ⧸ CFSG.pCore 2 ↥Xq) ⧸ frattini (↥Xq ⧸ CFSG.pCore 2 ↥Xq)) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq hW
    have hWp : ∀ w : (↥Xq ⧸ CFSG.pCore 2 ↥Xq) ⧸ frattini (↥Xq ⧸ CFSG.pCore 2 ↥Xq),
        w ^ p = 1 := by
      intro w
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
      rw [← QuotientGroup.mk_pow, ← hW'.exponent, Monoid.pow_exponent_eq_one,
        QuotientGroup.mk_one]
    refine SteinbergCD.perfect_sylow_two_irreducible_of_card_eq_sq hp5 hWp hW
      (H13.NQBlock.residualAction Xq) hW'.nontrivial S' M ?_
    intro s hs w hw
    rw [hS'c] at hs
    exact hM s (Subgroup.mem_subgroupOf.mp hs).1 w hw
  refine ⟨hX1, hTX, hO2, p, hp, hp2, fun x hx => OE2.pow_mem_pCoreOf hW'.exponent hx, ?_,
    fun Y hY1 hY2 hYT => OE2.eq_or_eq_of_residual Xq hW'.isPGroup hW'.exponent hirr hY1 hY2 hYT⟩
  rw [OE2.relIndex_map]
  have hcard : Nat.card (↥Xq ⧸ CFSG.pCore 2 ↥Xq) = Nat.card B := Nat.card_congr φ.toEquiv
  rcases hshape with ⟨-, -, -, hB2⟩ | ⟨hQB, hQnc, hQ3, -⟩
  · exact Or.inl (hcard.trans hB2)
  · refine Or.inr ⟨by rw [hcard, ← hQB]; exact hQ3, OE2.not_commutator_le fun hc => hQnc ?_⟩
    have hB : IsMulCommutative ↥B := ⟨⟨fun a b => by
      have h := hc.is_comm.comm (φ.symm a) (φ.symm b)
      apply φ.symm.injective
      rw [map_mul, map_mul, h]⟩⟩
    rw [hQB]
    exact hB

end CFSG.Quasithin.Vol2.Ch11
