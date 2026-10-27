module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res3ProofCensus
public import CFSG.RankThree.PartTwo.Sec21.Item221Proof228Statements
public import CFSG.RankThree.PartTwo.Sec21.Item221ProofZGen

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def Item212XL45 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ X ∈ lStar A, kOf A φ ≤ X → ∀ a ∈ A, a ≠ 1 →
        X ∈ thetaComponentsAt 3 a → A ⊓ Sec4.thetaQuotCentralizer X = Subgroup.zpowers a →
        inSubgroup (aschbacherSolvableCore 3) X = ⊥ →
        (StatedClassicalModel X .PSL 4 2 1 ∨ StatedClassicalModel X .PSL 5 2 1) →
          Subgroup.normalizer (A : Set G) ≤
            Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G)

open Item228ResProof

section Census

theorem item228OneList_of_censusMono45 (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6)
    (h47 : Sec4.Item4_7W) (h66 : Sec6.Item6_6) (h2130 : Item2130) (h2131 : Item2131One)
    (h222 : Item222) (hKW : KOfWellDefinedAll) (hNF : Item228NoFieldThree)
    (hList : Inspection228ListMono) (hθ : Item228ThetaTrivial) (h212 : Item212XL45) :
    Item228OneList := by
  intro G _ _ A E U c L hpair hA27 hnoT φ hφ X hX hKX m hm0 hme hKm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hpair.standing
  have hG := hst.toTheoremFourHyp
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hAF.2.1 B hB hAB).le⟩
  have hK := hKW G A E U c L hpair
  obtain ⟨a, haA, ha1, hXa⟩ := mem_thetaComponentFamily_iff.mp hX.1
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hXC := Sec6.le_centralizer_of_mem_thetaComponentsAt hXa
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe haA ha1 X hXa
  have hcomA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAc ⟨x, hx⟩ ⟨y, hy⟩)
  have haC : a ∈ Sec4.thetaQuotCentralizer X := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAX haA, fun l hl => ?_⟩
    have hla : l * a = a * l := Subgroup.mem_centralizer_singleton_iff.mp (hXC hl)
    rw [← hla, mul_inv_cancel_right, inv_mul_cancel]
    exact Subgroup.one_mem _
  have hD : A ⊓ Sec4.thetaQuotCentralizer X = Subgroup.zpowers a := by
    have hcyc := h66 G hst A hpair.mem_S X hX
    have hle : Subgroup.zpowers a ≤ A ⊓ Sec4.thetaQuotCentralizer X :=
      Subgroup.zpowers_le.mpr ⟨haA, haC⟩
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
    have hexp : Monoid.exponent (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hAe.2 x x.2.1)
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd (by norm_num) hexp
  have hcard3 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3 := by
    rw [hD, Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  obtain ⟨j, hjK, -, hj⟩ := exists_involution_kOf_wConj_eq h222 hpair hK hφ
  have hφX : φ ∈ starOf A X := by
    rw [← hj]
    exact Item233ZGenProof.wConj_mem_starOf j (hKX hjK)
  have hK0X : kZero A φ ≤ X := kZero_le_of_mem_starOf hAF haA hXa hφX hφ.1.1
  have hU : kOf A φ = kZero A φ ∨ StatedClassicalModel (kZero A φ) .PSU 3 2 2 := by
    by_cases h : StatedClassicalModel (kZero A φ) .PSU 3 2 2
    · exact Or.inr h
    · exact Or.inl (kOf_eq_kZero h)
  have hnorm : ∀ y ∈ X ⊓ Subgroup.centralizer (fixedInG A φ : Set G), ∀ k ∈ kZero A φ,
      y * k * y⁻¹ ∈ kZero A φ := fun y hy k hk =>
    (Subgroup.mem_normalizer_iff.mp (Item233One.centralizer_le_normalizer_kZero A φ hy.2) k).mp hk
  have hdiag : ∀ x ∈ A, Sec4.InducesOuterTheta x X → KFacts.InducesStdKind X x .diagonal := by
    intro x hxA hout
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact KFacts.not_inducesOuterTheta_one X hout
    obtain ⟨hf, hgf⟩ := hNF G A E U c L hpair hA27 φ hφ X hX hKX x hxA
    exact Item223PrintProof.inducesStdKind_diagonal_of h47 hG ha3 ha1 hXa (hcomA x hxA a haA)
      (orderOf_eq_prime (hAe.2 x hxA) hx1) hout hf hgf
  have hmono : ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
      (starOf A X).map (coordGL f) ≤ KFacts.KP14.monomial := by
    obtain ⟨f, hf, -⟩ := h2131 G A E U c L hpair hA27
    exact ⟨f, (Subgroup.map_mono (starOf_le_wStar A X)).trans hf⟩
  have hL := hList G X A (kOf A φ) (kZero A φ) m
    (Item223PrintProof.isList46_of_mem_thetaComponentsAt h46 hG ha3 ha1 hXa) hAmax hA27 hAX
    hcard3 hdiag hmono (fun ρ hρ => hnoT ρ (starOf_le_wStar A X hρ)) φ hφX hφ.1
    (kOf_le_kZero hK hφ) hK0X (kZero_le_centralizer A φ) hnorm hU hKm hm0 hme
  have hθX := hθ G A E U c L hpair hA27 φ hφ X hX hKX m hm0 hme hKm hL
  have eX : X ≃* lBar X := mulEquiv_lBar_of_theta_eq_bot hθX
  rcases hL with h | ⟨hm2, hP⟩ | ⟨-, h45'⟩
  · left
    rcases h with h | h | h | ⟨h4, h⟩ | ⟨h4, h⟩
    · exact Or.inl (h.map eX.trans)
    · exact Or.inr (Or.inl (h.map eX.trans))
    · exact Or.inr (Or.inr (Or.inl (h.map eX.trans)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, h.map eX.trans⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h4, h.map eX.trans⟩)))
  · exact Or.inr ⟨hm2, CFSG.SectionRank.statedClassicalModel_of_mulEquiv eX hP⟩
  ·
    exfalso
    have hX45 : StatedClassicalModel X .PSL 4 2 1 ∨ StatedClassicalModel X .PSL 5 2 1 := by
      rcases h45' with h | h
      · exact Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv eX h)
      · exact Or.inr (CFSG.SectionRank.statedClassicalModel_of_mulEquiv eX h)
    exact false_of_normalizer_le h2130 hpair haA ha1
      (h212 G A E U c L hpair hA27 φ hφ X hX hKX a haA ha1 hXa hD hθX hX45)

end Census

end CFSG.RankThree.PartTwo.Sec21
