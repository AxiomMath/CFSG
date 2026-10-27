module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4KPair
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223W21
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4KAct

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S15223P4

namespace K

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem pCoreOf_X_le_S (c : P4Ctx T Mc M H B₀ I X) (hXI : I ≤ Subgroup.normalizer (X : Set G)) :
    pCoreOf 2 X ≤ sOf152 T Mc M B₀ :=
  c.sylow.le_of_normalizes ((pCoreOf_le 2 X).trans c.X_le_I)
    (hXI.trans (normalizer_le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X)

theorem S_le_normalizer_oTwoUpper {Ha Hb V : Subgroup G} (hP : IsHPair H V Ha Hb)
    (hKS : oTwoUpper H ⊔ sOf152 T Mc M B₀ = Ha ⊔ Hb) :
    sOf152 T Mc M B₀ ≤ Subgroup.normalizer (oTwoUpper Hb : Set G) :=
  ((le_sup_right.trans hKS.le).trans (sup_le (hp152_le_normalizer_two hP)
    Subgroup.le_normalizer)).trans (normalizer_le_normalizer_oTwoUpper Hb)

theorem final_aux (c : P4Ctx T Mc M H B₀ I X) (hXI : I ≤ Subgroup.normalizer (X : Set G))
    {Ha Hb V : Subgroup G} (hP : IsHPair H V Ha Hb)
    (hKS : oTwoUpper H ⊔ sOf152 T Mc M B₀ = Ha ⊔ Hb) (hbC : oTwoUpper Hb ≤ Csub H X) :
    ⁅X, oTwoUpper Hb⁆ ≤ pCoreOf 2 X ∧ X ≤ Subgroup.normalizer (oTwoUpper Hb : Set G) := by
  have hKX := K_le_normalizer_X c hXI
  have hnormK0 : pCoreOf 2 (oTwoUpper H) ≤ Subgroup.normalizer (K0 X (oTwoUpper H) : Set G) :=
    fun o ho => mem_normalizer_K0 (hKX (pCoreOf_le 2 _ ho))
      (Subgroup.le_normalizer (pCoreOf_le 2 _ ho))
  have hbK0 : oTwoUpper Hb ≤ K0 X (oTwoUpper H) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyHb, hyodd⟩
    exact mem_of_odd_of_mem_sup (pCoreOf_isPGroup 2 _) hnormK0
      (hbC (mem_oTwoUpper_of_odd hyHb hyodd)) hyodd
  have hcomm : ∀ x ∈ X, ∀ k ∈ oTwoUpper Hb, k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 X :=
    fun x hx k hk => commutator_mem_of_mem_K0 (hbK0 hk) x hx
  refine ⟨?_, ?_⟩
  · rw [Subgroup.commutator_def]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, k, hk, rfl⟩
    have h := (pCoreOf 2 X).inv_mem (hcomm x hx k hk)
    have e : (k * x * k⁻¹ * x⁻¹)⁻¹ = ⁅x, k⁆ := by rw [commutatorElement_def]; group
    rwa [e] at h
  ·
    have hOS : pCoreOf 2 X ≤ Subgroup.normalizer (oTwoUpper Hb : Set G) :=
      (pCoreOf_X_le_S c hXI).trans (S_le_normalizer_oTwoUpper hP hKS)
    have hconj : ∀ x ∈ X, ∀ k ∈ oTwoUpper Hb, x * k * x⁻¹ ∈ oTwoUpper Hb := by
      intro x hx k hk
      change k ∈ Subgroup.closure {y | y ∈ Hb ∧ Odd (orderOf y)} at hk
      induction hk using Subgroup.closure_induction with
      | mem y hy =>
        have hyK : y ∈ oTwoUpper Hb := mem_oTwoUpper_of_odd hy.1 hy.2
        have hxy : x * y * x⁻¹ ∈ oTwoUpper Hb ⊔ pCoreOf 2 X := by
          have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
          have h1 := (pCoreOf 2 X).inv_mem (hcomm x hx y hyK)
          have e2 : (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
          rw [e2] at h1
          rw [e]
          exact (oTwoUpper Hb ⊔ pCoreOf 2 X).mul_mem (Subgroup.mem_sup_right h1)
            (Subgroup.mem_sup_left hyK)
        have hodd : Odd (orderOf (x * y * x⁻¹)) := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
          exact hy.2
        exact mem_of_odd_of_mem_sup (pCoreOf_isPGroup 2 X) hOS hxy hodd
      | one => simp
      | mul a b _ _ iha ihb =>
        have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
        rw [e]
        exact (oTwoUpper Hb).mul_mem iha ihb
      | inv a _ iha =>
        have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
        rw [e]
        exact (oTwoUpper Hb).inv_mem iha
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨hconj x hx k, fun h => ?_⟩
    have := hconj x⁻¹ (X.inv_mem hx) _ h
    simpa [mul_assoc] using this

theorem exists_pair_K2 (c : P4Ctx T Mc M H B₀ I X) (hXI : I ≤ Subgroup.normalizer (X : Set G))
    (hq : IsLnTwoQuot X 3)
    (h21 : ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      Lemma15221ConclW T Mc M H H₁ H₂ B₀ I) :
    (∃ e ∈ oTwoUpper H ⊓ X, orderOf e = 3) ∧
    ¬ IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) ∧
    ∃ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ ∧
      ⁅X, oTwoUpper H₂⁆ ≤ pCoreOf 2 X ∧ X ≤ Subgroup.normalizer (oTwoUpper H₂ : Set G) := by
  obtain ⟨E, hEK, hE, hE9⟩ := c.exists_E9
  obtain ⟨e, heE, heo⟩ := exists_inf_of_E c hXI hq hEK hE hE9
  have hnot := not_isIrredOnSection c hXI hq
  refine ⟨⟨e, ⟨hEK heE.1, heE.2⟩, heo⟩, hnot, ?_⟩
  obtain ⟨H₁, H₂, hP⟩ := c.inputs.hN.pair
  have hKS := ((h21 H₁ H₂ hP).one hnot).1
  rcases exists_oTwoUpper_le c hP hKS (Q_le_Csub H X) (Csub_le H X) (relIndex_Csub c hXI hq)
    (S_le_normalizer_Csub c hXI) with h1 | h2
  · exact ⟨H₂, H₁, isHPair_symm hP, final_aux c hXI (isHPair_symm hP) (by rw [hKS, sup_comm]) h1⟩
  · exact ⟨H₁, H₂, hP, final_aux c hXI hP hKS h2⟩

end K

end S15223P4

end CFSG.Quasithin
