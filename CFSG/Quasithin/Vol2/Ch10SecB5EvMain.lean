module

public import CFSG.Quasithin.Vol2.Ch10SecB5EvL2App
public import CFSG.Quasithin.Vol2.Ch10SecB5Main

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem normalizer_T1_le_XOf_even
    (hF : Fact10_2_5Lk2) (h311 : Theorem311Stmt)
    (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) (hA : A = L32.Pa ∨ A = L32.Pb)
    (hcase : (∃ (K₁ : Subgroup G) (s : G), s ∈ T ∧
          K₁ ∈ cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) ∧
          s ∉ Subgroup.normalizer (K₁ : Set G) ∧
          conjClosure (oTwoUpper (preIn Ψ (A.prod A) ⊔ T))
              (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) =
            K₁ ⊔ CFSG.conjugate K₁ s ∧
          ∃ m : ℕ, 0 < m ∧ Even m ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
            Nat.card F = 2 ^ m ∧
            Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        (quasithinIsCComponent
            (conjClosure (oTwoUpper (preIn Ψ (A.prod A) ⊔ T))
              (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)))
            (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) ∧
          ∃ k : ℕ, (k = 4 ∨ k = 5) ∧
            CFSG.Assembly.LowTwoRank.StatedClassicalModel
              (↥(conjClosure (oTwoUpper (preIn Ψ (A.prod A) ⊔ T))
                  (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T))) ⧸
                CFSG.pCore 2 ↥(conjClosure (oTwoUpper (preIn Ψ (A.prod A) ⊔ T))
                  (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T))))
              .PSL k 2 1 ∧
            Nonempty
              (↥(conjClosure (oTwoUpper (preIn Ψ (A.prod A) ⊔ T))
                    (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) ⊔ T) ⧸
                  CFSG.pCore 2 ↥(conjClosure (oTwoUpper (preIn Ψ (A.prod A) ⊔ T))
                    (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) ⊔ T) ≃*
                MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2))))) :
    Subgroup.normalizer (T1 T L : Set G) ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) := by
  rcases hcase with ⟨K₁, s, hs, hK₁, hsn, hK, m, hm, hme, F, _, _, hFc, ⟨e⟩⟩ |
      ⟨-, k, hk, hmod, haut⟩
  · exact normalizer_T1_le_XOf_L2q h311 h hD hA hs hK₁ hsn hK hme hm hFc e
  · exact normalizer_T1_le_XOf_Lk2 hF h hD hk hmod haut

theorem obl10_2_5Even_of
    (hF : Fact10_2_5Lk2) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h311 : Theorem311Stmt) : Obl10_2_5Even := by
  intro G _ _ T L I hyp h3 P hP hTP hcase
  have hinner : T1Inner T L := fun s hs => by
    obtain ⟨x₀, hx₀, hx, -⟩ := inner_of_case3 hyp h3 hs
    exact ⟨x₀, hx₀, hx⟩
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨Ψ, c, hC⟩ := exists_L0Coord h37 h38 hyp h3.1 hinner ht htn
  have h : MaxCtx T L I t Ψ c := ⟨h37, h38, hyp, ht, htn, hC⟩
  rcases maximal_classify h37 h38 hyp ht htn hC hP hTP with rfl | rfl
  · exact normalizer_T1_le_XOf_even hF h311 h parData_a (Or.inl rfl) hcase
  · exact normalizer_T1_le_XOf_even hF h311 h parData_b (Or.inr rfl) hcase

theorem stmt10_2_5_of'
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h3210 : TmpL6_3_2_10_eight) (h1012 : Stmt10_1_2) (h1021 : Stmt10_2_1)
    (h311 : Theorem311Stmt) (h134 : EmptyFaithfulMultiple.Prop134E9He) (hRed : HeReduce)
    (hF : H13.FactAutHeSylow)
    (hFa : FactL33M11) (hFc : FactL4L5) (hgap : Gap10_2_5L2p) (hLk : Fact10_2_5Lk2) :
    Stmt10_2_5 :=
  stmt10_2_5_of h37 h38 h3210 h1012 h1021 h311 h134 hRed hF hFa hFc hgap
    (obl10_2_5Even_of hLk h37 h38 h311)

end CFSG.Quasithin.Vol2.Ch10.SecB
