module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res6ProofNoField
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofCases
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofHJL0
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLFree
public import CFSG.RankThree.PartTwo.Sec13.Item137Tools

public section

namespace CFSG.RankThree.PartTwo.Sec12.Proof128

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (lBarA omegaA)


variable {G : Type} [Group G] [Finite G]

theorem not_inducesStdKind_ST (hST : Sec21.Item1134E27ST) (hst : PartTwoStanding G)
    {A : Subgroup G} (hAF : A ∈ partTwoF G) (hAS : A ∈ partTwoS G) (hAT : A ∈ partTwoT G)
    (hFE : partTwoF G = partTwoE G) (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    {K : Subgroup G} (hK : K ∈ lA422 A a) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1) :
    ¬ (KFacts.InducesStdKind K x .field ∨ KFacts.InducesStdKind K x .graphField) := by
  intro hk
  have hsc := hK.2.2.1
  have hsc' := hsc
  rw [Sec13.sectionCentralizer_eq_inf hK.2.1] at hsc'
  have hle : A ⊓ Sec4.thetaQuotCentralizer K ≤ Subgroup.zpowers a := fun y hy => by
    have : y ∈ ((A ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) := hy
    rw [hsc'] at this
    exact this
  have hstar : K ∈ lStarAt A a :=
    ⟨Sec6.mem_lStar_of_inf_le_zpowers hAF.1 haA ha1 hK.1 hK.2.1 hle, hK.1⟩
  have hx := hST G A a K hst hAS hAT h27 haA ha1 hstar hsc
    (Or.inr (Or.inr ⟨not_lTwoEight hst hAF hFE h27 haA ha1 hK hxA hx1 hk,
      not_slThreePiEight hst hAF hFE h27 haA ha1 hK hxA hx1 hk⟩)) hFE.symm x hxA
  rcases hk with hk | hk
  · exact hx.1 hk
  · exact hx.2 hk

theorem hj_of_mem_lA422_free_ST (hNF : KS128NotHJFree) (h423 : Sec4.Item4_23)
    (hST : Sec21.Item1134E27ST) (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves)
    {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hAS : A ∈ partTwoS G) (hAT : A ∈ partTwoT G)
    (hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) (haB : a ∉ Sec4.thetaQuotCentralizer L)
    {K : Subgroup G} (hK : K ∈ lA422 A a) :
    Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2) ∧
      Nonempty (Sec4.autIn K A ≃* Equiv.Perm (Fin 3)) ∧ c ∈ K := by
  have hFE := h.partTwoF_eq
  have hAF : A ∈ partTwoF G := hFE ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have h27 : Nat.card A = 27 := hAE.2.1
  obtain ⟨haA, ha3, -⟩ := Sec13.zpowers_mem_omegaA_iff.mp ha
  have ha1 : a ≠ 1 := ne_one_of_card_zpowers_eq_three ha3
  have hcA := h.mem_A
  have hc1 := h.ne_one
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcB : c ∈ Sec4.thetaQuotCentralizer L := mem_thetaQuotCentralizer_of_central h.mem_L hLc
  have hca : c ∉ Subgroup.zpowers a := by
    intro hc
    apply haB
    have heq : Subgroup.zpowers c = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc)
        (by rw [ha3, Sec13.card_zpowers_of_pow_three (hAe.2 c hcA) hc1])
    have : a ∈ Subgroup.zpowers c := heq ▸ Subgroup.mem_zpowers a
    exact (Subgroup.zpowers_le.mpr hcB) this
  have hW := normalizer_le_of_sec12StdBar_of_list h45 hK2 h hty
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1
  have hT : ∀ σ ∈ Sec4.autIn K A, σ ^ 3 = 1 → σ ∈ transvectionGroup A ⟨c, hcA⟩ :=
    fun σ hσ h3 => mem_transvectionGroup_of_mem_wStar h45 hK2 h hty
      (Sec13.Holds134.autIn_le_wStar K hσ) (k := 1) (by simpa using h3)
  have hcK_of : ∀ x : Sec4.autIn K A, x ≠ 1 → x ^ 3 = 1 → c ∈ K := fun x hx1 hx3 =>
    mem_of_mem_autIn_of_ne_one hAe hK.2.1 hcA x.2
      (hT x x.2 (by simpa using congrArg Subtype.val hx3)) (fun h1 => hx1 (Subtype.ext h1))
  rcases cases423 h423 h.toPartTwoStanding hAF h27 haA ha1 hK with
    ⟨σ, hσ4⟩ | ⟨hPGL, ⟨eZ3⟩, hx⟩ | ⟨h3, h9⟩ | ⟨hSL2, ⟨eZ3⟩⟩ | ⟨hMJ, ⟨eS3⟩⟩ |
      ⟨x, hxA, hx1, hk⟩
  · exact absurd hσ4 (not_orderOf_eq_four hAe h27 haA hcA ha1 hc1 hca hKa hW σ)
  · exfalso
    obtain ⟨y, hy1, hy3⟩ := exists_ne_one_pow_three_of_zmod3 eZ3
    exact (hNF G A c L h hAE hty a ha haB K hK (hcK_of y hy1 hy3)).1 ⟨hPGL, ⟨eZ3⟩, hx⟩
  · exfalso
    have hle : Sec4.autIn K A ≤ transvectionGroup A ⟨c, hcA⟩ := fun σ hσ => hT σ hσ (h3 σ hσ)
    have hfix : ∀ σ ∈ Sec4.autIn K A, σ ⟨a, haA⟩ = ⟨a, haA⟩ := by
      intro σ hσ
      obtain ⟨g, hgN, hgK, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe]
      have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp (hKa hgK)
      rw [hga, mul_inv_cancel_right]
    have := card_le_three_of_le_transvectionGroup hAe h27 haA hcA ha1 hc1 hca hle hfix
    omega
  · exfalso
    obtain ⟨y, hy1, hy3⟩ := exists_ne_one_pow_three_of_zmod3 eZ3
    exact false_of_isSLThreePiTwo hAe h27 haA hcA ha1 hc1 hca hK.1 hK.2.1 (hcK_of y hy1 hy3) hSL2
  · obtain ⟨y, hy1, hy3⟩ := exists_ne_one_pow_three_of_perm3 eS3
    have hcK := hcK_of y hy1 hy3
    rcases hMJ with hM | hJ
    · exact absurd ⟨hM, ⟨eS3⟩⟩ (hNF G A c L h hAE hty a ha haB K hK hcK).2
    · exact ⟨hJ, ⟨eS3⟩, hcK⟩
  · exact absurd hk
      (not_inducesStdKind_ST hST h.toPartTwoStanding hAF hAS hAT hFE h27 haA ha1 hK hxA hx1)

theorem mem_L_of_omega_ST
    (hNF : KS128NotHJFree) (h422 : Sec4.Item4_22) (h423 : Sec4.Item4_23)
    (hST : Sec21.Item1134E27ST) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hK2 : KFacts.KS12NormalizerMoves)
    {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hAS : A ∈ partTwoS G) (hAT : A ∈ partTwoT G)
    (hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) (haB : a ∉ Sec4.thetaQuotCentralizer L) :
    a ∈ L := by
  have hst := h.toPartTwoStanding
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  obtain ⟨K, hK⟩ := exists_mem_lA422 h422 h45 hst hAF hAE.2.1 ha
  obtain ⟨hφ, hS3, hcK⟩ := hj_of_mem_lA422_free_ST hNF h423 hST h45 hK2 h hAE hAS hAT
    hty ha haB hK
  exact (step5 h415 h45 h48 hK2 h hAE hty ha haB hK hφ hS3 hcK).1

end CFSG.RankThree.PartTwo.Sec12.Proof128
