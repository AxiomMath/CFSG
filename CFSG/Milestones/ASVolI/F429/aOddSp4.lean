module

public import CFSG.Milestones.ASVolI.F429.aOddGen
public import CFSG.Milestones.ASVolI.F429.aC7Sp4
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even

public section

namespace CFSG.ASVolI

section Rank

open Matrix CFSG.QuasithinUnique.Lin2.Five

theorem burnsideF429a_tauMat_ne_conj {R : Type*} [CommRing R] [Nontrivial R]
    (A Ai : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) (hA : A * Ai = 1) (t : R)
    (h : tauMat (1 + rootE R) = A * (1 + t • rootE R) * Ai) : False := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hA, Matrix.mul_smul, Matrix.smul_mul] at h
  have h03 := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 1)
  have h12 := congrFun (congrFun h (Sum.inl 1)) (Sum.inr 0)
  have h02 := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 0)
  rw [tauMat_one_add_rootE_ι₀ι₃, Matrix.add_apply, Matrix.smul_apply, conj_rootE_apply] at h03
  rw [tauMat_one_add_rootE_ι₁ι₂, Matrix.add_apply, Matrix.smul_apply, conj_rootE_apply] at h12
  rw [tauMat_one_add_rootE_ι₀ι₂, Matrix.add_apply, Matrix.smul_apply, conj_rootE_apply] at h02
  have e03 : (-1 : R) = t * (A (Sum.inl 0) (Sum.inl 0) * Ai (Sum.inr 0) (Sum.inr 1)) := by
    simpa [Matrix.one_apply] using h03
  have e12 : (1 : R) = t * (A (Sum.inl 1) (Sum.inl 0) * Ai (Sum.inr 0) (Sum.inr 0)) := by
    simpa [Matrix.one_apply] using h12
  have e02 : (0 : R) = t * (A (Sum.inl 0) (Sum.inl 0) * Ai (Sum.inr 0) (Sum.inr 0)) := by
    simpa [Matrix.one_apply] using h02
  have : (-1 : R) = 0 := by
    linear_combination e03 + (t * (A (Sum.inl 0) (Sum.inl 0) * Ai (Sum.inr 0) (Sum.inr 1))) * e12 -
      (t * (A (Sum.inl 1) (Sum.inl 0) * Ai (Sum.inr 0) (Sum.inr 1))) * e02
  exact one_ne_zero (neg_eq_zero.mp this)

end Rank

section SpModel

open Matrix CFSG.Open CFSG.ASVolI.ChF CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Lin2.Five CFSG.ComponentClassification.OuterAutomorphisms

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem burnsideF429a_coe_xl (t : K) :
    (((burnsideF4gSpInv_xl t : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 + t • rootE K := by
  show pairRootMat K (Sum.inl 0) (Sum.inr 0) t = _
  rw [pairRootMat_inl_inr_self]
  rfl

theorem burnsideF429a_fieldSp_xl_one (σ : K ≃+* K) :
    fieldSp 2 K σ (burnsideF4gSpInv_xl 1) = burnsideF4gSpInv_xl 1 := by
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [coe_fieldSp, burnsideF429a_coe_xl, one_smul]
  ext i j
  simp [rootE, Matrix.one_apply, Matrix.single_apply]

theorem burnsideF429a_Sp_tau_not_mem_Xl (A : gsp 2 K) (σ : K ≃+* K) (t : K)
    (h : (conjAut 2 K A * fieldAut 2 K σ * tauAut : MulAut (StatedProj (StatedSp 2 K)))
        (proj 2 K (burnsideF4gSpInv_xl 1)) = proj 2 K (burnsideF4gSpInv_xl t)) : False := by
  rw [MulAut.mul_apply, MulAut.mul_apply, tauAut_proj, fieldAut_proj, conjAut_proj] at h
  have h1 : conjSp 2 K A (fieldSp 2 K σ (tauSp (burnsideF4gSpInv_xl 1))) =
      burnsideF4gSpInv_xl t := (projEquiv K).injective h
  rw [← CFSG.RankThree.PartTwo.KFacts.tauSp_fieldSp, burnsideF429a_fieldSp_xl_one] at h1
  have h2 := congrArg (fun x : StatedSp 2 K =>
    ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h1
  simp only [coe_conjSp, Units.val_mul, coe_tauSp, burnsideF429a_coe_xl, one_smul] at h2
  have hAi : (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 :=
    Units.inv_mul _
  have hT : tauMat (1 + rootE K) = (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (1 + t • rootE K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [← h2]
    calc tauMat (1 + rootE K) =
        ((((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
          tauMat (1 + rootE K) *
          ((((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
          rw [hAi, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  exact burnsideF429a_tauMat_ne_conj _ _ hAi t hT

theorem burnsideF429a_Sp_inner_of_odd {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : Odd f)
    {β : MulAut (StatedProj (StatedSp 2 K))}
    (h₀ : ∀ x, β x ∈ (Q2 K 0).map (proj 2 K) ↔ x ∈ (Q2 K 0).map (proj 2 K))
    {k : ℕ} (hk : β ^ 2 ^ k = 1) :
    β ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range := by
  have hproj : Function.Injective (proj 2 K) := fun a b h => (projEquiv K).injective h
  have hPβ : ((Q2 K 0).map (proj 2 K)).map β.toMonoidHom = (Q2 K 0).map (proj 2 K) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (h₀ y).mpr hy
    · intro hx
      refine ⟨β⁻¹ x, (h₀ _).mp ?_, by simp⟩
      simpa using hx
  have hZ : (ctr (oPPrime 2 ((Q2 K 0).map (proj 2 K)))).map β.toMonoidHom =
      ctr (oPPrime 2 ((Q2 K 0).map (proj 2 K))) := by
    rw [← burnsideF429a_ctr_map (φ := β.toMonoidHom) β.injective,
      ← burnsideF4gU4Inv_oPPrime_map (ψ := β.toMonoidHom) β.injective, hPβ]
  have hZX : ctr (oPPrime 2 ((Q2 K 0).map (proj 2 K))) =
      (burnsideF4gSpInv_Xl K).map (proj 2 K) := by
    rw [burnsideF4gU4Inv_oPPrime_map hproj, burnsideF429a_ctr_map hproj, burnsideF429a_Sp_ctr_L1]
  have hmem : β (proj 2 K (burnsideF4gSpInv_xl 1)) ∈ (burnsideF4gSpInv_Xl K).map (proj 2 K) := by
    rw [← hZX, ← hZ]
    refine ⟨_, ?_, rfl⟩
    rw [hZX]
    exact ⟨_, burnsideF4gSpInv_mem_Xl.2 ⟨1, rfl⟩, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hmem
  obtain ⟨t, rfl⟩ := burnsideF4gSpInv_mem_Xl.1 hy
  obtain ⟨A, σ, ε, hε, hβ⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow β
  have hε0 : ε = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with h | h
    · exact h
    · exfalso
      rw [h, pow_one] at hβ
      rw [hβ] at hyx
      exact burnsideF429a_Sp_tau_not_mem_Xl A σ t hyx.symm
  rw [hε0, pow_zero, mul_one] at hβ
  haveI : (inner (StatedProj (StatedSp 2 K))).Normal := inner_normal _
  have hcA : conjAut 2 K A ∈ inner (StatedProj (StatedSp 2 K)) :=
    CFSG.RankThree.PartTwo.KFacts.conjAut_mem_inner_of_charTwo A
  have hπA : QuotientGroup.mk' (inner (StatedProj (StatedSp 2 K))) (conjAut 2 K A) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hcA
  have hπβ : QuotientGroup.mk' (inner (StatedProj (StatedSp 2 K))) β =
      QuotientGroup.mk' (inner (StatedProj (StatedSp 2 K))) (fieldAut 2 K σ) := by
    rw [hβ, map_mul, hπA, one_mul]
  have h1 : QuotientGroup.mk' (inner (StatedProj (StatedSp 2 K))) (fieldAut 2 K (σ ^ 2 ^ k)) =
      1 := by
    rw [map_pow, map_pow, ← hπβ, ← map_pow, hk, map_one]
  have hσk : σ ^ 2 ^ k = 1 := fieldAut_eq_one_of_mem_inner ((QuotientGroup.eq_one_iff _).mp h1)
  have hσf : σ ^ f = 1 := CFSG.Quasithin.H13.F431.L3.P3.autField_pow_eq_one hf.pos hK σ
  have hσ : σ = 1 := by
    have h1 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hσk
    have h2 : orderOf σ ∣ f := orderOf_dvd_of_pow_eq_one hσf
    have h3 : Nat.Coprime (2 ^ k) f := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hf)
    have h4 : orderOf σ ∣ Nat.gcd (2 ^ k) f := Nat.dvd_gcd h1 h2
    rw [h3.gcd_eq_one] at h4
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  rw [hβ, hσ, map_one, mul_one]
  exact hcA

end SpModel

section Main

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.ASVolI.ChF.ClassicalRoots
  CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem burnsideF429a_two_le_Sp4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : Odd f) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 → r ∈ Gp := by
  intro r hr k hk
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .Sp4) hyp.toHypF_4_4g
  obtain ⟨e, he⟩ := burnsideF4gSpOne_parabolic_eq marking
  have hK : Nat.card marking.field = 2 ^ f := by simpa using marking.field_card
  haveI : CharP marking.field 2 := burnsideF4gSp_charP_of_card hK
  have e0 := he false
  have e1 := he true
  simp only [Bool.false_eq_true, if_false, if_true] at e0 e1
  refine burnsideF429a_mem_of_model₂ hyp.centralizer_trivial e (h1.trans e0) (h2.trans e1) hr
    (fun β hβ₁ _ hβr => ?_)
  exact burnsideF429a_Sp_inner_of_odd hK hf hβ₁ (burnsideF429a_pow_eq_one_of_intertwine _ hβr hk)

end Main

end CFSG.ASVolI
