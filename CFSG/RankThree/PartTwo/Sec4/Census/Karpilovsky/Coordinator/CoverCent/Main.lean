module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent.Lift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Cover.Reduction
public import CFSG.RankThree.PartTwo.Sec4.Item426RestModels
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Proof
public import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.SolvableKit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open Item426Rest

theorem false_of_alternating_any {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    (hZ : Subgroup.center X ≠ ⊥) {n : ℕ} (e : X ≃* alternatingGroup (Fin n)) : False := by
  rcases Nat.lt_or_ge n 4 with hn | hn
  · have h1 : Nat.card (alternatingGroup (Fin n)) ∣ Nat.card (Equiv.Perm (Fin n)) :=
      Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm,
      Fintype.card_fin] at h1
    have h6 : n.factorial ∣ 2 ^ 1 * 3 ^ 1 := by
      interval_cases n <;> decide
    have hsolv : Group.IsSolvable X :=
      CFSG.AGLEmbeddingD2.Wilson.Census424Rest.isSolvable_of_card_dvd_two_three
        (by rw [Nat.card_congr e.toEquiv]; exact h1.trans h6)
    have : Group.IsPerfect X := hX.1
    have : Nontrivial X := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact hZ (Subsingleton.elim _ _)
    exact (Group.IsPerfect.not_isSolvable (G := X)) hsolv
  · exact hZ (center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot (by simpa using hn)))

theorem false_of_projSp_any {X : Type} [Group X] (hX : IsQuasisimple X)
    (hZ : Subgroup.center X ≠ ⊥) {n : ℕ} {F : Type} [Field F] (e : X ≃* projSp n F) : False :=
  false_of_mulEquiv_quotient_center hX hZ
    ((e.trans (projSpEquivStatedProj n F)).trans
      (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv n F).symm)

theorem false_of_slThreeEps {X : Type} [Group X] (hZ : Subgroup.center X ≠ ⊥)
    (hnsl : ¬ IsSLThreePi X) {p e : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (he : 1 ≤ e)
    (hSL : IsSLThreeEpsAt X (p ^ e)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hq : p ^ e % 3 = 1 ∨ p ^ e % 3 = 2 := by
    have h0 : p ^ e % 3 ≠ 0 := fun h0 => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h0))).symm
    omega
  exact hnsl ⟨_, KFacts.isSLThreePiAt_of_isSLThreeEpsAt he hSL hq hZ⟩


theorem coverCentX_of_rows (hA6 : NoType424At3 (alternatingGroup (Fin 6)))
    (hA7 : NoType424At3 (alternatingGroup (Fin 7)))
    (hM22 : NoType424At3 (Blueprint.NativeSporadic.Carrier .M22))
    (hJ3 : NoType424At3 (Blueprint.NativeSporadic.Carrier .J3))
    (hMcL : NoType424At3 (Blueprint.NativeSporadic.Carrier .McL))
    (hON : NoType424At3 (Blueprint.NativeSporadic.Carrier .ONan))
    (hG2 : ∀ (S : Type) [Group S], Blueprint.ChevalleyExceptionalModel S .G2 3 1 →
      NoType424At3 S)
    (hU43 : NoType424At3 (projSU 4 3 1)) :
    CFSG.AGLEmbeddingD2.Wilson.Census424Cover.CoverCentX := by
  intro X _ _ hlist hX hZ hnsl y hy hy3 P hP hT
  have hrow : ∀ {S : Type} [Group S], (X ⧸ Subgroup.center X ≃* S) → NoType424At3 S → False :=
    fun e hS => false_of_noType424At3 e hS hy hy3 hP hT
  have hcov : ∀ {S : Type} [Group S], Subgroup.center S = ⊥ →
      IsExtOf X S (Multiplicative (ZMod 3)) → NoType424At3 S → False := by
    intro S _ hZS hext hS
    obtain ⟨-, ⟨e⟩⟩ := (isTripleCover_iff_isExtOf hX hZS).mpr hext
    exact hrow e hS
  obtain ⟨hZJ3, hZMcL, hZON⟩ := Item426.center_J3_McL_ON
  have hZA : ∀ {n : ℕ}, 4 ≤ n → Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    fun hn => alternatingGroup.center_eq_bot (by simpa using hn)
  have hZM22 : Subgroup.center Blueprint.NativeSporadic.M22 = ⊥ := by
    have := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact Item426.center_eq_bot_of_isSimpleGroup (by rw [Item426.card_M22]; norm_num)
  rcases hlist with ⟨p, e, _, -, -, ⟨e1⟩⟩ |
      ⟨p, e, _, hp3, he1, -, hSL | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩ |
      ⟨p, _, hp3, hG2' | ⟨⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩⟩ |
      (⟨n, -, ⟨e1⟩⟩ | hA6' | hA7') | (⟨s, hs, ⟨e1⟩⟩ | ⟨s, hs, hext⟩) |
      (hchev | ⟨n, hn, hSL⟩) | (⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩) |
      ((⟨e, he1, -, ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩) | ⟨⟨e1⟩⟩ | ⟨-, hG23 | hU43'⟩)
  ·
    exact false_of_projSL hX hZ e1
  ·
    exact false_of_slThreeEps hZ hnsl Fact.out (by omega) he1 hSL
  · exact false_of_projSL hX hZ e1
  · exact false_of_projSU hX hZ le_rfl he1 e1
  ·
    exact false_of_chevalleyExceptional hX hZ (Or.inl rfl) hG2'
  · exact false_of_projSp_any hX hZ e1
  · exact false_of_projSU hX hZ (by norm_num) le_rfl e1
  · exact false_of_projSL hX hZ e1
  ·
    exact false_of_alternating_any hX hZ e1
  · exact hcov (hZA (by norm_num)) hA6' hA6
  · exact hcov (hZA (by norm_num)) hA7' hA7
  ·
    exact false_of_sporadic46 hX hZ hs e1
  · simp only [sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact hcov hZM22 hext hM22
    · exact hcov hZJ3 hext hJ3
    · exact hcov hZMcL hext hMcL
    · exact hcov hZON hext hON
  ·
    rcases hchev with ⟨n, hn, ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩ |
      ⟨f, hG2' | hD4 | hSz | hF4 | hTits⟩
    · exact false_of_projSL hX hZ e1
    · exact false_of_projSL hX hZ e1
    · exact false_of_projSU hX hZ le_rfl hn e1
    · exact false_of_projSp_any hX hZ e1
    · exact false_of_projSU hX hZ (by norm_num) hn e1
    · exact false_of_chevalleyExceptional hX hZ (Or.inl rfl) hG2'
    · exact false_of_chevalleyExceptional hX hZ (Or.inr rfl) hD4
    · exact false_of_suzuki hX hZ hSz
    · exact false_of_reeTits hX hZ (Or.inl rfl) hF4
    · exact false_of_reeTits hX hZ (Or.inr rfl) hTits
  ·
    exact false_of_slThreeEps hZ hnsl Nat.prime_two (by norm_num) hn hSL
  ·
    exact false_of_projSL hX hZ e1
  · exact false_of_projSp_any hX hZ e1
  · exact false_of_projSU hX hZ (by norm_num) (by norm_num) e1
  ·
    exact false_of_projSL hX hZ e1
  · exact false_of_projSU hX hZ le_rfl he1 e1
  · exact false_of_projSL hX hZ e1
  ·
    exact hrow (MulEquiv.refl _) (hG2 _ hG23)
  · obtain ⟨eU⟩ := hU43'
    exact hrow eU hU43

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent
