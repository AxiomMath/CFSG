module

public import CFSG.Quasithin.H13.NQS1312P
public import CFSG.Quasithin.EmptyFaithful.R3c2Types
public import CFSG.Quasithin.EmptyFaithful.SBc17Cases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_oPrimeResidualOf_of_orderOf_three {X : Subgroup G} {x : G} (hx : x ∈ X)
    (h3 : orderOf x = 3) : x ∈ oPrimeResidualOf 3 X :=
  subset_closure ⟨hx, 1, by rw [h3, pow_one]⟩

theorem false_of_exclusion_line (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    {K : Subgroup G} (hK : K ∈ cComp (lineH Φ)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    {S : Type} [Group S] [Finite S] (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* S) (hS : A318Exclusion S) :
    False := by
  have hLV : L ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.1
  obtain ⟨-, -, x, hxL, -, hx3, -, -, hxτ⟩ := exists_e9 hU3 hF hΦLs
  have hxN := mem_lineN_of_tau_k2 (hLV hxL) hxτ
  have hKN : K ∈ cComp (lineN Φ) := cComp_mem_of_subnormal isSubnormal_lineH hK
  have hKeq := eq_oPrimeResidualOf_three_of_exclusion hF318 h36 h38 (isSQTKIn_lineN hH) hKN hq e hS
  have hxK : x ∈ K := hKeq ▸ mem_oPrimeResidualOf_of_orderOf_three hxN hx3
  exact not_mem_lineH_of_tau_k2 (hLV hxL) hxτ (le_of_mem_cComp hK hxK)

omit [Finite G] in
theorem quotPCore_equiv_of_surjective {K : Subgroup G} {X : Type*} [Group X] {α : ↥K →* X}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩

section Entries

variable (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (hKF : KnownFacts15122Types)
  {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
  (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
  {Φ : Additive V ≃ₗ[ZMod 2] W6}
  (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
    (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
  {K : Subgroup G} (hK : K ∈ cComp (lineH Φ)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
  {R M W : Subgroup G}
include hF318 h36 h38 hKF hH hU3 hΦLs hK hq

theorem false_of_c27A7a_line (h : SBc17.C27A7a (lineH Φ) R M K W) : False := by
  obtain ⟨-, ⟨α, hα, hker, -⟩, -⟩ := h
  obtain ⟨e⟩ := quotPCore_equiv_of_surjective hα hker
  exact false_of_exclusion_line hF318 h36 h38 hH hU3 hF hΦLs hK hq e hKF.alt7

theorem false_of_c27A7b_line (h : SBc17.C27A7b (lineH Φ) R M K W) : False := by
  obtain ⟨-, ⟨α, hα, hker, -⟩, -⟩ := h
  obtain ⟨e⟩ := quotPCore_equiv_of_surjective hα hker
  exact false_of_exclusion_line hF318 h36 h38 hH hU3 hF hΦLs hK hq e hKF.alt7

theorem false_of_c27Alt_line {n : ℕ} (hn : n = 6 ∨ n = 7) {α : ↥K →* alternatingGroup (Fin n)}
    (h : IsAltBlockTypeWith K n α) : False := by
  obtain ⟨e⟩ := quotPCore_equiv_of_surjective h.1 h.2.1
  rcases hn with rfl | rfl
  · exact false_of_exclusion_line hF318 h36 h38 hH hU3 hF hΦLs hK hq e hKF.alt6
  · exact false_of_exclusion_line hF318 h36 h38 hH hU3 hF hΦLs hK hq e hKF.alt7

theorem false_of_c27ExcA7_line (h : SBc17.C27ExcA7 (lineH Φ) R M K W) : False := by
  obtain ⟨⟨-, ⟨α, hα, hker⟩, -⟩, -⟩ := h
  obtain ⟨e⟩ := quotPCore_equiv_of_surjective hα hker
  exact false_of_exclusion_line hF318 h36 h38 hH hU3 hF hΦLs hK hq e hKF.alt7

theorem false_of_c27A6Sp4_line (hE : Vol2.Ch11.SecA.FactA318Excl)
    (h : SBc17.C27A6Sp4 (lineH Φ) R M K W) : False := by
  rcases h.1 with h6 | ⟨-, F, _, _, hF4, α, hα, hker, -⟩
  · obtain ⟨e⟩ := quotPCore_equiv_alt_of_isAltBlockType h6
    exact false_of_exclusion_line hF318 h36 h38 hH hU3 hF hΦLs hK hq e hKF.alt6
  · obtain ⟨e⟩ := quotPCore_equiv_of_surjective hα hker
    have hF4' : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hF4]; norm_num
    exact false_of_exclusion_line hF318 h36 h38 hH hU3 hF hΦLs hK hq (MulEquiv.refl _)
      (R3c2.exclusion_sp4 hE hF4' e hq)

theorem false_of_c27G2_line (h : SBc17.C27G2 (lineH Φ) R M K W) : False :=
  false_of_exclusion_line hF318 h36 h38 hH hU3 hF hΦLs hK hq (MulEquiv.refl _)
    (hKF.u33 _ h.1.2.1)

end Entries

end CFSG.Quasithin.H13.U3.NLine
