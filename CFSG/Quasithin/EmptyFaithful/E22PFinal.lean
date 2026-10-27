module

public import CFSG.Quasithin.EmptyFaithful.E22PRes
public import CFSG.Quasithin.EmptyFaithful.E22PL2
public import CFSG.Quasithin.EmptyFaithful.E22PL2Sq
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Families

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB

@[expose] def ResRestGroup (G : Type) [Group G] : Prop :=
  (∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsPSL 2 p 2 (ASInputs.FStar G) ∧
    ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ 2 ∧
      (Nonempty (G ≃* GorensteinWalter.PSL2 K) ∨ Nonempty (G ≃* GorensteinWalter.PGL2 K))) ∨
    ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ (s = true → p % 4 = 3) ∧ (s = false → p % 4 = 1) ∧
      IsPSLEps3 s p 1 (ASInputs.FStar G)

@[expose] def E114OneResRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ → ResRestGroup G → E1.nParam (⊤ : Subgroup G) ≤ 1

theorem e114OneResNoA6_of_rest
    (h : E114OneResRest) : E114OneResNoA6 := by
  intro G _ _ T hSQ hFs hT hFT hty
  rcases hty with h32 | ⟨p, e, hp, hp3, he, hpe8, hP⟩ | ⟨s, p, hp, hp2, h4, h4', hP⟩
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact E22L2.nParam_le_one_of_psl2_prime (p := 7) (Or.inr rfl) le_rfl
      (Vol2Native.statedClassicalModel_psl_two_seven_of_three_two h32)
  · have : Fact p.Prime := ⟨hp⟩
    rcases he with rfl | rfl
    · rw [pow_one] at hpe8
      exact E22L2.nParam_le_one_of_psl2_prime hpe8 (by
        have := hp.two_le
        omega) hP
    · have hp5 : 5 ≤ p := by
        by_contra hlt
        have h4p : p = 4 := by omega
        subst h4p
        norm_num at hp
      by_cases hex : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ 2 ∧
          (Nonempty (G ≃* GorensteinWalter.PSL2 K) ∨ Nonempty (G ≃* GorensteinWalter.PGL2 K))
      · obtain ⟨K, _, _, hK, ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩⟩ := hex
        · rw [E1.Eleven.nParam_top_mulEquiv e]
          exact E22L2.nParam_psl2_sq_le_one hp5 hK
        · have := E22L2.e22pl2pgl_finite K
          rw [E1.Eleven.nParam_top_mulEquiv e]
          exact E22L2.nParam_pgl2_sq_le_one hp5 hK
      · exact h G T hSQ hFs hT hFT (Or.inl ⟨p, hp, hp3, hP, hex⟩)
  · exact h G T hSQ hFs hT hFT (Or.inr ⟨s, p, hp, hp2, h4, h4', hP⟩)

end CFSG.Quasithin.E2.E22N
