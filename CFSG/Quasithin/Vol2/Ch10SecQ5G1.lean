module

public import CFSG.Quasithin.Vol2.Ch10SecQ34LM

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

@[expose] def Gap10_2_5L2pE9' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I →
    ∀ P : Subgroup G, IsMaxSubgroupIn (fsuL0 T L ⊔ T) P → T ≤ P →
    ∀ (K₁ : Subgroup G) (s : G), s ∈ T →
      K₁ ∈ cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ P) →
      s ∉ Subgroup.normalizer (K₁ : Set G) →
      conjClosure (oTwoUpper P) (Subgroup.normalizer (T1 T L : Set G) ⊔ P) =
        K₁ ⊔ CFSG.conjugate K₁ s →
      (∃ p : ℕ, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
        Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))) →
      pCoreOf 2 (oTwoUpper P) ≤ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s) →
      Subgroup.normalizer (T1 T L : Set G) ≤ Subgroup.normalizer (oTwoUpper P : Set G)

theorem gap10_2_5L2p_of'
    (hE9' : Gap10_2_5L2pE9')
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h311 : Theorem311Stmt) : Gap10_2_5L2p := by
  intro G _ _ T L I hyp h3 P hP hTP K₁ s hs hK₁ hsn hK hpe
  obtain ⟨p, hp, hp2, ⟨e⟩⟩ := hpe
  by_cases hbad : (p % 8 = 3 ∨ p % 8 = 5) ∧
      pCoreOf 2 (oTwoUpper P) ≤ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s)
  · exact hE9' G T L I hyp h3 P hP hTP K₁ s hs hK₁ hsn hK ⟨p, hp, hbad.1, ⟨e⟩⟩ hbad.2
  have hE9 : p % 8 = 3 ∨ p % 8 = 5 →
      ¬ pCoreOf 2 (oTwoUpper P) ≤ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s) :=
    fun h8 hle => hbad ⟨h8, hle⟩
  have hinner : T1Inner T L := fun s hs => by
    obtain ⟨x₀, hx₀, hx, -⟩ := inner_of_case3 hyp h3 hs
    exact ⟨x₀, hx₀, hx⟩
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨Ψ, c, hC⟩ := exists_L0Coord h37 h38 hyp h3.1 hinner ht htn
  have h : MaxCtx T L I t Ψ c := ⟨h37, h38, hyp, ht, htn, hC⟩
  rcases maximal_classify h37 h38 hyp ht htn hC hP hTP with rfl | rfl
  · exact normalizer_T1_le_XOf_L2p h311 h parData_a (Or.inl rfl) hs hK₁ hsn hK hp hp2 e hE9
  · exact normalizer_T1_le_XOf_L2p h311 h parData_b (Or.inr rfl) hs hK₁ hsn hK hp hp2 e hE9

end CFSG.Quasithin.Vol2.Ch10.SecB
