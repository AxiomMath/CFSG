module

public import CFSG.Quasithin.Background.SmithC27RTypeGen
public import CFSG.Quasithin.Background.SmithB51G2DOff
public import CFSG.Quasithin.Background.SmithB42U33
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.EmptyFaithful.Insp9Tr

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

private theorem commutator_le_self' {Γ : Type*} [Group Γ] (H : Subgroup Γ) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)


theorem isPSU_of_equiv_g2Derived {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {X : Type} [Group X] (e : X ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) : IsPSU 3 3 1 X := by
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]
    norm_num
  let e' : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 3 CFSG.Quasithin.G2U.F9) :=
    e.trans ((Insp9.g2DerivedEquivZMod2 K hK).trans
      ((Insp9.g2DerivedEquivZMod2 (GaloisField 2 1) hGF).symm.trans
        CFSG.Quasithin.G11.P3G2.commutatorG2EquivSU))
  obtain ⟨hadm, K', _, _, hKc, ⟨φ⟩⟩ :=
    CFSG.LinearGroups.UnitaryThreeOverNine.classicalModel_statedSU
      (F := CFSG.Quasithin.G2U.F9) CFSG.Quasithin.G2U.card_F9
  exact ⟨hadm, K', inferInstance, inferInstance, hKc, ⟨e'.trans φ⟩⟩

theorem isSimpleGroup_g2Derived {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    IsSimpleGroup ↥⁅quasithinG2 K, quasithinG2 K⁆ :=
  SBc11.isSimpleGroup_of_list (Or.inr (Or.inr (isPSU_of_equiv_g2Derived hK (MulEquiv.refl _))))

theorem b42TypeU33_of_equiv {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {X : Type}
    [Group X] (e : X ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) : B42TypeU33 X := by
  have hP := isPSU_of_equiv_g2Derived hK e
  have hZ : Subgroup.center X = ⊥ := SBc11.center_eq_bot_of_list (Or.inr (Or.inr hP))
  obtain ⟨hadm, K', i1, i2, hKc, ⟨φ⟩⟩ := hP
  exact ⟨hZ, hadm, K', i1, i2, hKc,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans φ⟩⟩

theorem eq_map_g2Derived {Γ : Type*} [Group Γ] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (π : ↥(quasithinG2 F) →* Γ) (hπ : Function.Bijective π)
    {L : Subgroup Γ} (hL : L.Normal) (hperf : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) :
    L = ((⁅quasithinG2 F, quasithinG2 F⁆).subgroupOf (quasithinG2 F)).map π := by
  have : IsSimpleGroup ↥((⁅quasithinG2 F, quasithinG2 F⁆).subgroupOf (quasithinG2 F)) := by
    have := isSimpleGroup_g2Derived hF
    exact (Subgroup.subgroupOfEquivOfLe (commutator_le_self' (quasithinG2 F))).isSimpleGroup
  refine eq_map_of_bijective (D := (⁅quasithinG2 F, quasithinG2 F⁆).subgroupOf (quasithinG2 F))
    π hπ hL hperf hL1 fun a b => ?_
  rw [Subgroup.mem_subgroupOf]
  show (quasithinG2 F).subtype ⁅a, b⁆ ∈ _
  rw [map_commutatorElement]
  exact Subgroup.commutator_mem_commutator a.2 b.2

theorem ne_of_g2NaturalDerived {V : Type} [CommGroup V] [Finite V] (hI : B5.B51IrrInputs)
    (hV : ∀ v : V, v ^ 2 = 1) {G₀ L : Subgroup (MulAut V)} (h : B51Hyp G₀ L)
    (hU : commV L ∈ IrrPlus L ⊤)
    (hG2 : G2NaturalDerived L (commV L) (fixV L ⊓ commV L) 1) : G₀ ≠ L := by
  intro hGL
  obtain ⟨F, iF, fF, hF, π, hπ⟩ := hG2
  have hF2 : Nat.card F = 2 := hF.trans (pow_one 2)
  have : CharP F 2 := FFC.charP_two_of_card_pow hF
  let e := FFC.equivOfRealizes (FFC.zornQ_faithful _ (commutator_le_self' _)) hπ
  have hP : B42TypeU33 ↥L := b42TypeU33_of_equiv hF2 e.symm
  have hcard : Nat.card ↥L = 6048 :=
    SBc11.card_of_isPSU_three_three (isPSU_of_equiv_g2Derived hF2 e.symm)
  have hS : Nat.card (Sec (commV L) (fixV L ⊓ commV L)) = (2 ^ 1) ^ 6 := by
    have h1 := CFSG.Quasithin.G64.RealizesVia.card_eq hπ
    rw [B5.G2D.card_zornQMod, hF2] at h1
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((fixV L ⊓ commV L).subgroupOf (commV L))
    have h3 : Nat.card ↥((fixV L ⊓ commV L).subgroupOf (commV L)) =
        Nat.card ↥(fixV L ⊓ commV L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h3, h1] at h2
    have hpos : 0 < Nat.card ↥(fixV L ⊓ commV L) := Nat.card_pos
    have h4 := Nat.eq_of_mul_eq_mul_right hpos h2
    rw [← h4]
    norm_num
  have hL1 : L ≠ ⊥ := by
    have := FFC.nontrivial_of_isQuasisimple (B5.quasi_L h)
    exact (Subgroup.nontrivial_iff_ne_bot L).1 this
  obtain ⟨A, hA⟩ : ∃ A, IsFFStarOffender G₀ A := by
    by_contra hno
    push Not at hno
    have hJ : ffJ G₀ = ⊥ := iSup₂_eq_bot.2 fun A hA => absurd hA (hno A)
    exact hL1 (hGL.symm.trans (h.2.2.2.2.2.trans hJ))
  obtain ⟨-, hcardA, -, -⟩ := B5.G2D.offender_facts hI.ident hI.b42 hV h hU le_rfl hS
    (Or.inl ⟨rfl, hcard⟩) hA
  have hAL : A ≤ L := hGL ▸ hA.1
  have := B42U33.rank_le_two hP hAL hA.2.2.1 hcardA
  omega

end CFSG.Quasithin.SmithC27
