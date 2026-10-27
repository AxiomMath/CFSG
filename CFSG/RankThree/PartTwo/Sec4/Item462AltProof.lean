module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofSLTwo
public import CFSG.RankThree.PartTwo.Sec4.Item463Proof

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Common

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_eq_three_of_complement {A B D : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hDA : D ≤ A)
    (hBD : B ⊓ D = ⊥) (hBDA : B ⊔ D = A) : Nat.card D = 3 := by
  have hBDc : Nat.card (B ⊔ D : Subgroup G) = Nat.card B * Nat.card D := by
    refine GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B D ?_
      (disjoint_iff.mpr hBD)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxy : ∀ y ∈ B, x * y * x⁻¹ = y := fun y hy => by
      have hc : x * y = y * x := congrArg Subtype.val (hAe.1.1.comm ⟨x, hDA hx⟩ ⟨y, hBA hy⟩)
      rw [hc, mul_inv_cancel_right]
    constructor
    · intro hy
      rw [hxy y hy]
      exact hy
    · intro hy
      have hyA : y ∈ A := by
        have := A.mul_mem (A.mul_mem (A.inv_mem (hDA hx)) (hBA hy)) (hDA hx)
        rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this
      have hc : x * y = y * x := congrArg Subtype.val (hAe.1.1.comm ⟨x, hDA hx⟩ ⟨y, hyA⟩)
      rwa [hc, mul_inv_cancel_right] at hy
  rw [hBDA, h27, hB9] at hBDc
  omega

theorem not_le_thetaQuotCentralizer_of_commutator_eq {L U : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (hUN : U ≤ Subgroup.normalizer (L : Set G))
    (hLU : ⁅L, U⁆ = L) : ¬ U ≤ thetaQuotCentralizer L := by
  intro h
  have h1 : ⁅L, U⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L :=
    (Sec6.commutator_le_theta_iff hUN).mpr h
  rw [hLU] at h1
  have := CFSG.LocalCores.isQuasisimple_nontrivial hL.2.2
  obtain ⟨x, hx⟩ := exists_ne (1 : L ⧸ aschbacherSolvableCore 3 L)
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  apply hx
  obtain ⟨t, ht, htl⟩ := h1 l.2
  have htl' : t = l := Subtype.ext htl
  rw [← htl']
  exact (QuotientGroup.eq_one_iff _).mpr ht

omit [Finite G] in
theorem le_centralizer_of_le {A B : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hBA : B ≤ A) : A ≤ Subgroup.centralizer (B : Set G) := fun x hx =>
  Subgroup.mem_centralizer_iff.mpr fun y hy =>
    congrArg Subtype.val (hAe.1.1.comm ⟨y, hBA hy⟩ ⟨x, hx⟩)

end Common

section Main


theorem step462Alt_core (hKL2 : KLTwoCentralizer) (hKC2 : KChevTwoCentralizer)
    (hKL3 : KSLThreeCentralizerQ) (hKL3K : KSLThreeNoFieldKind)
    {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A) (haZ : a ∈ Subgroup.center G) (ha1 : a ≠ 1)
    {B : Subgroup G} (haB : a ∈ B) (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    {U : Subgroup G} (hU : IsKleinFour U) (hUA : ⁅U, A⁆ = U)
    (hUO : U = inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (B : Set G)))
    {D : Subgroup G} (hDA : D ≤ A) (hBD : B ⊓ D = ⊥) (hBDA : B ⊔ D = A)
    (hND : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G))
    {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hUN : U ≤ Subgroup.normalizer (L : Set G)) (hLU : ⁅L, U⁆ = L)
    (hUs : U ≤ L ⊔ thetaQuotCentralizer L) (h9 : Nat.card (autThetaQuot A L) = 9)
    (halt : Item462Proof.Alt423S A L)
    (h47 : ∀ e ∈ A, orderOf e = 3 → InducesOuterTheta e L → Alt47W L e) :
    (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.J2) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.M12)) ∨
      (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 3)) ∧
        ∃ e ∈ B, InducesOuterTheta e L) := by
  classical
  have hAe := hmax.1
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  obtain ⟨b, hbB, hba, hCB⟩ := Item462Proof.exists_centralizer_eq hB9
    (fun x hx => hAe.2 x (hBA hx)) haB haZ ha3
  have hbA := hBA hbB
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hCA := mem_thetaQuotCentralizer_iff_zpowers hAL h27 haA haZ ha3 h9
  have hbC : b ∉ thetaQuotCentralizer L := fun h => hba ((hCA b hbA).mp h)
  have hβ3 := orderOf_psi_eq_three (hAL hbA) hb3 hbC
  have hU4 : Nat.card U = 4 := @IsKleinFour.card_four _ _ hU
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := by
    rw [← hUA]
    exact Sec6.le_normalizer_commutator_right U A
  have hUθ : U ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) := by
    rw [hUO, hCB]
    exact Item462Proof.inSubgroup_pCore_two_le_theta _
  have hUC := not_le_thetaQuotCentralizer_of_commutator_eq hL hUN hLU
  have hβ := innThetaNoncyclic_of hL (hAL hbA) hb3 hAL hAe.2 hUN hUs hU2 hAU hUA hUC hUθ
  have hD3 := card_eq_three_of_complement hAe h27 hBA hB9 hDA hBD hBDA
  rcases halt with ⟨-, hAut, hx⟩ | ⟨hH, -, hel, h9'⟩ | ⟨hSL2, -⟩ | h8
  · exact (false_of_isZ3PGLThreePi hKL3 hmax h27 haA haZ ha3 haB hbB hba hBA hB9 hDA hBDA hD3
      hND hL hAL hCA hβ3 hβ hAut hx).elim
  · exact (false_of_isHeisCentral hAe h27 haZ ha3 haB hbB hba hBA hB9 hDA hBDA hD3 hND hL hAL hH
      hel h9').elim
  · exact (false_of_isSLThreePiTwo hKL3 hmax h27 haA haZ ha3 haB hbB hba hBA hB9 hDA hBDA hBD
      hND hL hAL hCA hβ3 hβ hSL2).elim
  · obtain ⟨hiso, hout⟩ := case8_462 hKL2 hKC2 hKL3 hKL3K hL hAe hβ3 hβ h47 h8
    exact Or.inr ⟨hiso, b, hbB, (inducesOuterTheta_iff (hAL hbA)).mpr hout⟩

theorem step462Alt_of (hKL2 : KLTwoCentralizer) (hKC2 : KChevTwoCentralizer)
    (hKL3 : KSLThreeCentralizerQ) (hKL3K : KSLThreeNoFieldKind) : Step462Alt := by
  intro G _ _ _ A hmax h27 a haA haZ ha1 B haB hBA hB9 U hU hUA hUO D hDA hBD hBDA hND _ L hL
    hAL hUN hLU hUs h9 halt h47
  exact step462Alt_core hKL2 hKC2 hKL3 hKL3K hmax h27 haA haZ ha1 haB hBA hB9 hU hUA hUO hDA hBD
    hBDA hND hL hAL hUN hLU hUs h9 halt h47

theorem step463Alt_core (h41 : Item4_1LargePrime) (hKL2 : KLTwoCentralizer)
    (hKC2 : KChevTwoCentralizer) (hKL3 : KSLThreeCentralizerQ)
    {G : Type} [Group G] [Finite G] (hS4 : SectionFourHyp G) {A : Subgroup G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A) (haZ : a ∈ Subgroup.center G) (ha1 : a ≠ 1)
    {B : Subgroup G} (haB : a ∈ B) (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    {U : Subgroup G} (hU2 : IsPGroup 2 U) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hUA : ⁅U, A⁆ = U)
    (hUle : U ≤ ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)), A⁆)
    {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hUN : U ≤ Subgroup.normalizer (L : Set G)) (hLU : ⁅L, U⁆ = L)
    (hUs : U ≤ L ⊔ thetaQuotCentralizer L) (h9 : Nat.card (autThetaQuot A L) = 9)
    (halt : Item463Proof.Alt423T A L)
    (h47 : ∀ e ∈ A, orderOf e = 3 → InducesOuterTheta e L → Alt47W L e) : List463 L := by
  classical
  have hAe := hmax.1
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  obtain ⟨b, hbB, hba, hCB⟩ := Item462Proof.exists_centralizer_eq hB9
    (fun x hx => hAe.2 x (hBA hx)) haB haZ ha3
  have hbA := hBA hbB
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hCA := mem_thetaQuotCentralizer_iff_zpowers hAL h27 haA haZ ha3 h9
  have hbC : b ∉ thetaQuotCentralizer L := fun h => hba ((hCA b hbA).mp h)
  have hβ3 := orderOf_psi_eq_three (hAL hbA) hb3 hbC
  have hUθ : U ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) := by
    have hAθ : A ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer (B : Set G)) : Subgroup G) : Set G) := fun x hx =>
      Sec6.le_normalizer_theta _ (le_centralizer_of_le hAe hBA hx)
    rw [← hCB]
    exact hUle.trans (Subgroup.le_normalizer_iff_commutator_le_left.mp hAθ)
  have hUC := not_le_thetaQuotCentralizer_of_commutator_eq hL hUN hLU
  have hβ := innThetaNoncyclic_of hL (hAL hbA) hb3 hAL hAe.2 hUN hUs hU2 hAU hUA hUC hUθ
  rcases halt with ⟨hZ3, -⟩ | ⟨-, -, x, -, -, hxT⟩ | ⟨-, hlist, -, -⟩ | ⟨hSL2, -⟩ | h8
  · exact list463_of_isZ3LThreePi hKL3 h41 hS4 hL hAL hβ3 hβ hZ3
  · exact list463_of_inducesTypeOn hKL3 h41 hS4 hL hβ3 hβ hxT
  · exact list463_of_isHeisCentral hKL3 h41 hS4 hL hβ3 hβ hlist
  · exact list463_of_isSLThreePiTwo hKL3 h41 hS4 hL hAL hAe.2 h27 hβ3 hβ hSL2
  · exact case8_463 hKL2 hKC2 hKL3 hL hAe hβ3 hβ h47 h8

theorem step463Alt_of (h41 : Item4_1LargePrime) (hKL2 : KLTwoCentralizer)
    (hKC2 : KChevTwoCentralizer) (hKL3 : KSLThreeCentralizerQ) : Step463Alt := by
  intro G _ _ hS4 A hmax h27 a haA haZ ha1 _ B haB hBA hB9 U hU2 _ hAU hUA hUle L hL hAL hUN hLU
    hUs h9 halt h47
  exact step463Alt_core h41 hKL2 hKC2 hKL3 hS4 hmax h27 haA haZ ha1 haB hBA hB9 hU2 hAU hUA hUle
    hL hAL hUN hLU hUs h9 halt h47

end Main

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof
