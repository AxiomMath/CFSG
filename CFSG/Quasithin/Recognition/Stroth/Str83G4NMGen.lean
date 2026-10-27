module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4NM

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree
open CFSG.QuasithinUnique.Setup.X7 CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.ShultStronglyClosedTI.SuzukiLayerKernel
open CFSG.CGT.PushingUpLit.SolKNA
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

theorem str83G4_sectionFacts_of_le_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {U L N : Subgroup G} (hUQ : U ≤ Q1 L1 L2 S)
    (hstep : IsChiefStep (L1 ⊔ S) U L N) :
    L1 ⊔ S ≤ Subgroup.normalizer (L : Set G) ∧
      L1 ⊔ S ≤ Subgroup.normalizer (N : Set G) ∧
      N ≤ Subgroup.normalizer (L : Set G) ∧
      IsElemAbelian 2 (Ch3z.chiefMod L N) ∧
      pCoreOf 2 (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N := by
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hQ1H : Q1 L1 L2 S ≤ L1 ⊔ S := hQ1S.trans le_sup_right
  have hUH : U ≤ L1 ⊔ S := hUQ.trans hQ1H
  have hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  have hU2 : IsPGroup 2 U := (pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le hUQ
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) :=
    CFSG.Quasithin.isElemAbelian_chiefMod hstep hUH hU2
  have hQn : L1 ⊔ S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (sup_left_le_p1 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hNQ : N ≤ Q1 L1 L2 S := hstep.1.1.trans hUQ
  have hcommNQ : ⁅N, Q1 L1 L2 S⁆ ≤ L :=
    F112W.commutator_le_of_isChiefStep (pCoreOf_isPGroup 2 (P1 L1 L2 S)) hQ1H hQn hstep hNQ
  have hO : pCoreOf 2 (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N := by
    rw [str83G4_pCoreOf_sup_left hfr]
    intro q hq
    refine ⟨hQ1H hq, hHL (hQ1H hq), fun n hn => ?_⟩
    have hmem : ⁅n, q⁆ ∈ L := hcommNQ (Subgroup.commutator_mem_commutator hn hq)
    have e : q * n * q⁻¹ * n⁻¹ = ⁅n, q⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact L.inv_mem hmem
  exact ⟨hHL, hHN, hNL, hE, hO⟩

theorem str83G4_sectionRep_ne_one_of_le_q1
    {L1 L2 S : Subgroup G} {a : ℕ} {L N : Subgroup G}
    (hnc : ¬ twoResidual (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N)
    (hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G))
    (hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N)
    (e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a (GaloisField 2 (2 * a + 1))) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    ∃ g, sectionRep hHL hHN hNL hE hO e g ≠ 1 := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  obtain ⟨y, hyR, hyC⟩ := SetLike.not_le_iff_exists.mp hnc
  have hyH : y ∈ L1 ⊔ S := twoResidual_le _ hyR
  obtain ⟨n, hnN, hn⟩ : ∃ n ∈ N, y * n * y⁻¹ * n⁻¹ ∉ L := by
    by_contra hall
    push Not at hall
    exact hyC ⟨hyH, hHL hyH, hall⟩
  refine ⟨e (QuotientGroup.mk ⟨y, hyH⟩), fun h1 => hn ?_⟩
  have hyn : y * n * y⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN hyH) n).mp hnN
  have h2 := LinearMap.congr_fun h1 (Additive.ofMul (Ch3z.chiefIota hNL ⟨n, hnN⟩))
  rw [sectionRep_chiefIota _ _ _ _ _ _ ⟨y, hyH⟩ ⟨n, hnN⟩ hyn, Module.End.one_apply] at h2
  have h3 : Ch3z.chiefIota hNL (⟨y * n * y⁻¹, hyn⟩ * (⟨n, hnN⟩ : ↥N)⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact Additive.ofMul.injective h2
  exact (Ch3z.chiefIota_eq_one_iff hNL _).1 h3

theorem sectionRep_isSzNatural_of_le_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {C : Subgroup G}
    (hC : ∀ s : G, s ∈ C ⊔ Q1 L1 L2 S ↔ s ∈ S ∧ s ^ 2 ∈ Q1 L1 L2 S)
    {U L N : Subgroup G} (hUQ : U ≤ Q1 L1 L2 S)
    (hstep : IsChiefStep (L1 ⊔ S) U L N)
    (hquad : ⁅⁅N, C⁆, C⁆ ≤ L)
    (hnc : ¬ twoResidual (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N)
    (hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G))
    (hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N)
    (e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a (GaloisField 2 (2 * a + 1)))
    (he : (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a (GaloisField 2 (2 * a + 1))) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    IsSzNatural (sectionRep hHL hHN hNL hE hO e) := by
  have hUH : U ≤ L1 ⊔ S := hUQ.trans ((str83G4_q1_le_s hfr).trans le_sup_right)
  exact sectionRep_isSzNatural_of_quadratic_chiefStep hfr hC hUH hquad hstep hHL hHN hNL hE hO e
    he (str83G4_sectionRep_ne_one_of_le_q1 (L2 := L2) hnc hHL hHN hNL hE hO e)

theorem str83G4_isSzNaturalSection_of_quadratic_chiefStep
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {C : Subgroup G}
    (hC : ∀ s : G, s ∈ C ⊔ Q1 L1 L2 S ↔ s ∈ S ∧ s ^ 2 ∈ Q1 L1 L2 S)
    {U L N : Subgroup G} (hUQ : U ≤ Q1 L1 L2 S) (hstep : IsChiefStep (L1 ⊔ S) U L N)
    (hquad : ⁅⁅N, C⁆, C⁆ ≤ L)
    (hnc : ¬ twoResidual (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N) :
    IsSzNaturalSection (L1 ⊔ S) N L a := by
  obtain ⟨hHL, hHN, hNL, hE, hO⟩ := str83G4_sectionFacts_of_le_q1 hfr hUQ hstep
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨e, he⟩ := str83G4_exists_equiv_sylow hK hfr
  have hnat := sectionRep_isSzNatural_of_le_q1 hfr hC hUQ hstep hquad hnc hHL hHN hNL hE hO e he
  exact isSzNaturalSection_of_isSzNatural hHL hHN hNL hE hO e hnat

end CFSG.Quasithin.Stroth

end
