module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobDefs
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.LocalAnalysis.StandardType.GGQTwoLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarConnGen
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarData
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarLinData
public import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
public import CFSG.LocalAnalysis.StandardType.ZS.OrthOrderBound

public section
namespace CFSG.StandardType.QTwo
open CFSG.StandardType TauCeti.QuadraticMap
variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W]

theorem qTwoGlobFour_orth_le {A : Subgroup (W ≃ₗ[ZMod 3] W)}
    (Q : QuadraticForm (ZMod 3) W)
    (hcase : (∀ g, g ∈ A ↔ ZS.IsIsom 3 Q g) ∨
      (∃ c : ZMod 3, c ≠ 0 ∧ A = Subgroup.closure (ZS.ClassRefl 3 Q c))) :
    A ≤ orthogonalGroup Q := by
  rcases hcase with hf | ⟨c, _, rfl⟩
  · intro g hg
    exact mem_orthogonalGroup_iff.mpr ((hf g).1 hg)
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    exact mem_orthogonalGroup_iff.mpr hg.2.1

theorem qTwoGlobFour_orth_card [Module.Finite (ZMod 3) W]
    (Q : QuadraticForm (ZMod 3) W) (hQ : (qTwoPolar Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) W = 4) :
    Nat.card (orthogonalGroup Q) = 1152 ∨ Nat.card (orthogonalGroup Q) = 1440 := by
  classical
  by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType Q
  · left
    have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
      (Q := Q) hQ (m := 1) (by simpa using hd) (ε := 1) (Or.inl ⟨rfl, hp⟩)
    norm_num only [Nat.card_zmod, Finset.Icc_self, Finset.prod_singleton] at h
    exact_mod_cast h
  · right
    have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
      (Q := Q) hQ (m := 1) (by simpa using hd) (ε := -1) (Or.inr ⟨rfl, hp⟩)
    norm_num only [Nat.card_zmod, Finset.Icc_self, Finset.prod_singleton] at h
    exact_mod_cast h

theorem qTwoGlobFour_selected_card [Finite W] [Module.Finite (ZMod 3) W]
    {A : Subgroup (W ≃ₗ[ZMod 3] W)}
    (Q : QuadraticForm (ZMod 3) W) (hQ : (qTwoPolar Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) W = 4)
    (hle : A ≤ orthogonalGroup Q)
    {N : ℕ} (hN1 : 6 ≤ N) (hN2 : N ≤ 7)
    (hfac : N.factorial ∣ Nat.card A)
    (hneg : (LinearEquiv.neg (ZMod 3) : W ≃ₗ[ZMod 3] W) ∈ A → False) :
    N = 6 ∧ Nat.card A = 720 := by
  letI : Finite A := Finite.of_injective
    (fun a : A => (⟨a.1, hle a.2⟩ : orthogonalGroup Q))
    (fun _ _ h => Subtype.ext
      (congrArg (fun z : orthogonalGroup Q => (z : W ≃ₗ[ZMod 3] W)) h))
  have ho := qTwoGlobFour_orth_card Q hQ hd
  have hdiv := Subgroup.card_dvd_of_le hle
  have hN : N = 6 := by
    have hcases : N = 6 ∨ N = 7 := by omega
    rcases hcases with h6 | h7
    · exact h6
    · subst N
      have hf := dvd_trans hfac hdiv
      rcases ho with ho | ho <;> rw [ho] at hf <;> norm_num at hf
  subst N
  norm_num only [Nat.factorial] at hfac
  rcases ho with ho | ho
  · have hf := dvd_trans hfac hdiv
    rw [ho] at hf
    norm_num at hf
  · have hleCard : Nat.card A ≤ 1440 := by
      exact Nat.le_of_dvd (by norm_num) (ho ▸ hdiv)
    have hpos : 0 < Nat.card A := Nat.card_pos
    obtain ⟨k, hk⟩ := hfac
    have hkCases : k = 1 ∨ k = 2 := by omega
    rcases hkCases with hk1 | hk2
    · exact ⟨rfl, by omega⟩
    · have heqCard : Nat.card A = Nat.card (orthogonalGroup Q) := by omega
      have heq : A = orthogonalGroup Q :=
        Subgroup.eq_of_le_of_card_ge hle heqCard.ge
      apply False.elim
      apply hneg
      rw [heq]
      apply mem_orthogonalGroup_iff.mpr
      intro v
      exact @QuadraticMap.map_neg (ZMod 3) W (ZMod 3) _ _ _ _
        (inferInstance : Module (ZMod 3) (ZMod 3)) Q v

theorem qTwoGlobFour_orth_five_card [Module.Finite (ZMod 3) W]
    (Q : QuadraticForm (ZMod 3) W) (hQ : (qTwoPolar Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) W = 5) :
    Nat.card (orthogonalGroup Q) = 103680 := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd
    (Q := Q) (by rw [ZMod.ringChar_zmod_n]; decide) hQ (n := 2) (by simpa using hd)
  norm_num only [Nat.card_zmod, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton] at h
  exact_mod_cast h

theorem qTwoGlobFour_five_factorial [Module.Finite (ZMod 3) W]
    {A : Subgroup (W ≃ₗ[ZMod 3] W)}
    (Q : QuadraticForm (ZMod 3) W) (hQ : (qTwoPolar Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) W = 5) (hle : A ≤ orthogonalGroup Q)
    {N : ℕ} (hN : 7 ≤ N) (hfac : N.factorial ∣ Nat.card A) : False := by
  have hdiv := dvd_trans (Nat.factorial_dvd_factorial hN)
    (dvd_trans hfac (Subgroup.card_dvd_of_le hle))
  rw [qTwoGlobFour_orth_five_card Q hQ hd] at hdiv
  norm_num [Nat.factorial] at hdiv

end CFSG.StandardType.QTwo
end
