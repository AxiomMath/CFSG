module

public import CFSG.Quasithin.EmptyFaithful.SBc17MixOne

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem comm_mem_inf_of_normalizes {A B : Subgroup G} (hA : A ≤ Subgroup.normalizer (B : Set G))
    (hB : B ≤ Subgroup.normalizer (A : Set G)) {g b : G} (hg : g ∈ A) (hb : b ∈ B) :
    ⁅g, b⁆ ∈ A ⊓ B := by
  refine ⟨?_, ?_⟩
  · have e : ⁅g, b⁆ = g * (b * g⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact A.mul_mem hg ((Subgroup.mem_normalizer_iff.mp (hB hb) g⁻¹).mp (A.inv_mem hg))
  · exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hA hg) b).mp hb) (B.inv_mem hb)

omit [Finite G] in
theorem comm_mem_sup_of_mul_mem {N₀ O : Subgroup G} {a b g : G} (hab : a * b ∈ N₀)
    (hg : g ∈ Subgroup.normalizer (N₀ : Set G)) (ha : a ∈ Subgroup.normalizer (O : Set G))
    (hc : ⁅g, b⁆ ∈ O) : ⁅g, a⁆ ∈ N₀ ⊔ O := by
  have hc2 : a * ⁅g, b⁆ * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp ha _).mp hc
  have hga : ⁅g, a * b⁆ ∈ N₀ := by
    have h1 : g * (a * b) * g⁻¹ ∈ N₀ := (Subgroup.mem_normalizer_iff.mp hg _).mp hab
    exact N₀.mul_mem h1 (N₀.inv_mem hab)
  have e : ⁅g, a⁆ = ⁅g, a * b⁆ * (a * ⁅g, b⁆ * a⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (N₀ ⊔ O).mul_mem (Subgroup.mem_sup_left hga)
    ((N₀ ⊔ O).inv_mem (Subgroup.mem_sup_right hc2))

omit [Finite G] in
theorem mem_pCoreOf_of_comm_mem_of_equiv {K : Subgroup G}
    (hφ : Nonempty (OTwoQuot K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    {x : G} (hx : x ∈ K) (hc : ∀ g ∈ K, ⁅g, x⁆ ∈ pCoreOf 2 K) : x ∈ pCoreOf 2 K := by
  obtain ⟨φ⟩ := hφ
  let π : ↥K →* OTwoQuot K := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)
  have hcen : π ⟨x, hx⟩ ∈ Subgroup.center (OTwoQuot K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥K) q
    have hmem : π ⁅γ, (⟨x, hx⟩ : ↥K)⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ((SBc16.mem_pCore_iff_coe K _).mpr (hc γ γ.2))
    rw [map_commutatorElement] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  have hz : φ (π ⟨x, hx⟩) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨q, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen q]
  rw [SBc16.center_L216, Subgroup.mem_bot, map_eq_one_iff φ φ.injective] at hz
  exact (SBc16.mem_pCore_iff_coe K _).mp ((QuotientGroup.eq_one_iff _).mp hz)

theorem oTwoUpper_inf_sup_pCoreOf_le {K J : Subgroup G} (hKJ : K ≤ Subgroup.normalizer (J : Set G)) :
    oTwoUpper ((K ⊓ J) ⊔ pCoreOf 2 K) ≤ K ⊓ J := by
  have hON : pCoreOf 2 K ≤ Subgroup.normalizer ((K ⊓ J : Subgroup G) : Set G) := fun o ho =>
    SBc14.mem_normalizer_inf (Subgroup.le_normalizer (pCoreOf_le 2 K ho)) (hKJ (pCoreOf_le 2 K ho))
  exact Der6A.oTwoUpper_le_of_normal_sup le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hON))
    (pCoreOf_isPGroup 2 K) le_sup_right le_rfl

theorem le_of_le_inf_sup_pCoreOf_of_perfect {K J L : Subgroup G}
    (hKJ : K ≤ Subgroup.normalizer (J : Set G)) (hL : oTwoUpper L = L)
    (h : L ≤ (K ⊓ J) ⊔ pCoreOf 2 K) : L ≤ J :=
  calc L = oTwoUpper L := hL.symm
    _ ≤ oTwoUpper ((K ⊓ J) ⊔ pCoreOf 2 K) := oTwoUpper_mono h
    _ ≤ K ⊓ J := oTwoUpper_inf_sup_pCoreOf_le hKJ
    _ ≤ J := inf_le_right

set_option linter.unusedVariables false in
theorem isPGroup_inf_of_not_innerSub_shapeOne (h36 : A36ForSQTK) (S : Setting146 G T M)
    {PQ : Subgroup G} (hp5 : p = 5) (hred : IsRedCE T M H PQ p)
    (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    {K₁ K₂ : Subgroup G} {s : G} (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s)
    (hc₁ : K₁ ∈ cComp (mcOf T)) (hc₂ : K₂ ∈ cComp (mcOf T))
    (hφ : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    {J : Subgroup G} (hX : SQTKGroup ↥(g2_14615 K₂)) (hJc : J ∈ cComp (g2_14615 K₂))
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hK₂N : K₂ ≤ Subgroup.normalizer (J : Set G)) (hK₂c : ⁅J, K₂⁆ ≤ pCoreOf 2 J)
    (hKJ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (J : Set G))
    (hout : ¬ K₁ ⊔ K₂ ≤ innerSub J) :
    IsPGroup 2 ↥((K₁ ⊔ K₂) ⊓ J) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hKG₂ : K₁ ⊔ K₂ ≤ g2_14615 K₂ := by
    have := kz_le_g2_14615 hdec hset
    rwa [hset.kz] at this
  have h₁ : K₁ ≤ Subgroup.normalizer (K₂ : Set G) := fun x hx => hKG₂ (Subgroup.mem_sup_left hx)
  have h₂ : K₂ ≤ Subgroup.normalizer (K₁ : Set G) := fun x hx =>
    SBc16.sup_le_normalizer_of_mem_cComp hc₁ hc₂ (Subgroup.mem_sup_right hx)
  have hnle : ¬ K₁ ≤ K₂ := fun h =>
    SBc13.K₁_ne_K₂ hset (Subgroup.eq_of_le_of_card_ge h (SBc13.card_K₁ hset).symm.le)
  have hKO : K₁ ⊓ K₂ ≤ pCoreOf 2 (K₁ ⊔ K₂) :=
    (inf_le_pCoreOf_of_simple (perfect_of_mem_cComp hc₁) (isSimpleGroup_oTwoQuot_of_equiv hφ) h₁
      hnle).trans (pCoreOf_le_sup_of_normalizes h₂)
  have hφ₂ : Nonempty (OTwoQuot K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
    obtain ⟨φ⟩ := hφ
    rw [hset.conj]
    exact ⟨(SBc16.oTwoQuotConjEquiv s K₁).symm.trans φ⟩
  have hgen₁ : K₁ ≤ Subgroup.closure {x | x ∈ K₁ ∧ orderOf x = 5} :=
    le_closure_five_of_sl2_component le_rfl hc₁ hφ
  obtain ⟨k₁, hk₁K, hk₁5, -⟩ := exists_five_not_mem_of_not_le hgen₁
    (show ¬ K₁ ≤ ⊥ from fun h => ne_bot_of_mem_cComp hc₁ (le_bot_iff.mp h))
  have hz₂ : s * k₁ * s⁻¹ ∈ K₂ := by
    rw [hset.conj]
    exact mul_mem_conjSub hk₁K
  have hz₂5 : orderOf (s * k₁ * s⁻¹) = 5 := by
    have := orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective k₁
    simpa [MulAut.conj_apply, hk₁5] using this
  have hK₂cM : K₂ ≤ cMod J := fun k hk =>
    mem_cMod.mpr ⟨hK₂N hk, fun x hx => hK₂c (Subgroup.commutator_mem_commutator hx hk)⟩
  have h5Z : ∀ z ∈ J, z ∈ cMod J → orderOf z ≠ 5 := fun z hzJ hzc hz5 =>
    SBc13.not_mem_of_commutes hX (h36 _ (SQTKHyp.of_sqtkGroup _ hX)) hJc hJq hz5
      (fun x hx => (mem_cMod.mp hzc).2 x hx) hzJ
  set K := K₁ ⊔ K₂ with hK
  set O := pCoreOf 2 K with hO
  set N₀ := K ⊓ J with hN₀
  set P := N₀ ⊔ O with hP
  have hK₁K : K₁ ≤ K := le_sup_left
  have hK₂K : K₂ ≤ K := le_sup_right
  have hKN₀ : K ≤ Subgroup.normalizer (N₀ : Set G) := fun g hg =>
    SBc14.mem_normalizer_inf (Subgroup.le_normalizer hg) (hKJ hg)
  have hKO' : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 K
  have hKP : K ≤ Subgroup.normalizer (P : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_sup N₀ O ⟨hKN₀ hg, hKO' hg⟩
  have hK₁P : ¬ K₁ ≤ P := by
    intro h
    have hJ₁ : K₁ ≤ J := le_of_le_inf_sup_pCoreOf_of_perfect hKJ (SBc13.oTwoUpper_K₁ hset) h
    exact hout (innerSub_sup_of_le (fun x hx => mem_innerSub_of_mem_J (hJ₁ hx)) hK₂cM)
  have hK₂P : ¬ K₂ ≤ P := by
    intro h
    have hJ₂ : K₂ ≤ J := le_of_le_inf_sup_pCoreOf_of_perfect hKJ hset.perf₂ h
    exact h5Z _ (hJ₂ hz₂) (hK₂cM hz₂) hz₂5
  have hP₁ : K₁ ⊓ P ≤ pCoreOf 2 K₁ :=
    inf_le_pCoreOf_of_simple (perfect_of_mem_cComp hc₁) (isSimpleGroup_oTwoQuot_of_equiv hφ)
      (fun g hg => hKP (hK₁K hg)) hK₁P
  have hP₂ : K₂ ⊓ P ≤ pCoreOf 2 K₂ :=
    inf_le_pCoreOf_of_simple (perfect_of_mem_cComp hc₂) (isSimpleGroup_oTwoQuot_of_equiv hφ₂)
      (fun g hg => hKP (hK₂K hg)) hK₂P
  have hOK₁ : pCoreOf 2 K₁ ≤ O := pCoreOf_le_sup_of_normalizes h₂
  have hOK₂ : pCoreOf 2 K₂ ≤ O := by
    have := pCoreOf_le_sup_of_normalizes h₁
    rwa [sup_comm] at this
  have hNO : N₀ ≤ O := by
    intro x hx
    have hxK : x ∈ K := hx.1
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ h₁
    have hxK' : x ∈ ((K₁ ⊔ K₂ : Subgroup G) : Set G) := hxK
    rw [hmul] at hxK'
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Set.mem_mul.mp hxK'
    have hx₁K : x₁ ∈ K := hK₁K hx₁
    have hxN' : x₂ * x₁ ∈ N₀ := by
      have h1 : x₁⁻¹ * (x₁ * x₂) * x₁⁻¹⁻¹ ∈ N₀ :=
        (Subgroup.mem_normalizer_iff.mp (hKN₀ (K.inv_mem hx₁K)) _).mp hx
      simpa [mul_assoc] using h1
    have hx₁O : x₁ ∈ pCoreOf 2 K₁ := by
      refine mem_pCoreOf_of_comm_mem_of_equiv hφ hx₁ fun g hg => hP₁ ⟨?_, ?_⟩
      · exact K₁.mul_mem (K₁.mul_mem (K₁.mul_mem hg hx₁) (K₁.inv_mem hg)) (K₁.inv_mem hx₁)
      · exact comm_mem_sup_of_mul_mem hx (hKN₀ (hK₁K hg)) (hKO' hx₁K)
          (hKO (comm_mem_inf_of_normalizes h₁ h₂ hg hx₂))
    have hx₂O : x₂ ∈ pCoreOf 2 K₂ := by
      refine mem_pCoreOf_of_comm_mem_of_equiv hφ₂ hx₂ fun g hg => hP₂ ⟨?_, ?_⟩
      · exact K₂.mul_mem (K₂.mul_mem (K₂.mul_mem hg hx₂) (K₂.inv_mem hg)) (K₂.inv_mem hx₂)
      · have hc : ⁅g, x₁⁆ ∈ K₂ ⊓ K₁ := comm_mem_inf_of_normalizes h₂ h₁ hg hx₁
        rw [inf_comm] at hc
        exact comm_mem_sup_of_mul_mem hxN' (hKN₀ (hK₂K hg)) (hKO' (hK₂K hx₂)) (hKO hc)
    exact O.mul_mem (hOK₁ hx₁O) (hOK₂ hx₂O)
  exact (pCoreOf_isPGroup 2 K).to_le hNO

end SBc17

end CFSG.Quasithin
