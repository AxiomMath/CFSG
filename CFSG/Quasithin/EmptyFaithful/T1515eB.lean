module

public import CFSG.Quasithin.EmptyFaithful.T1515eA
public import CFSG.Quasithin.EmptyFaithful.T1515cE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_1_25_one_of_a318 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂)
    (h19 : Lemma15119Used T Mc M Z₁ V₂) (hL : IsL1519 Mc Z₁ L)
    (h22 : Lemma15122Concl T Mc M Z₁ L) (h24 : Lemma15124Concl T Mc M Z₁ V₁ V₂ L) :
    L = oPrimeResidualOf 3 (g1_1516 Z₁) := by
  obtain ⟨S, _, _, ⟨e⟩, hS⟩ := exists_exclusion_model_of_case15122 hK h19.one hL h24.two h22
  have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hC.setting.pCore_g1_ne_bot hC.qtfe hC.mf
  have hH : SQTKGroup ↥(g1_1516 Z₁) :=
    sqtkGroup_of_pCoreOf_ne_bot hC.qtfe.qtke hC.qtfe.simple hC.qtfe.nonabelian hpc
  exact eq_oPrimeResidualOf_three_of_exclusion hF h36 h38 hH hL.comp hL.quasi e hS

omit [Finite G] in
theorem conj_normalizer_centralizer1515e {t y : G} {V₁ V₂ : Subgroup G}
    (hV : conjByElt t V₂ = V₁) (hy : y ∈ Subgroup.normalizer (V₂ : Set G)) :
    t * y * t⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) ∧
      (t * y * t⁻¹ ∈ Subgroup.centralizer (V₁ : Set G) → y ∈ Subgroup.centralizer (V₂ : Set G)) := by
  have hmem : ∀ v : G, v ∈ V₁ ↔ t⁻¹ * v * t ∈ V₂ := fun v => by
    rw [← hV, mem_conjByElt]
  refine ⟨?_, fun hc => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro v
    rw [hmem, hmem, Subgroup.mem_normalizer_iff.mp hy (t⁻¹ * v * t)]
    simp only [mul_assoc, inv_mul_cancel_left, mul_inv_rev, inv_inv]
    group
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hv : t * w * t⁻¹ ∈ V₁ := by
      rw [hmem]
      simpa [mul_assoc] using hw
    have := Subgroup.mem_centralizer_iff.mp hc _ hv
    have h2 := congrArg (fun a : G => t⁻¹ * a * t) this
    simp only [mul_assoc, inv_mul_cancel_left] at h2
    simpa [mul_assoc] using h2

theorem lemma_15_1_25_three_of_a318 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂)
    (h19 : Lemma15119Used T Mc M Z₁ V₂) (hL : IsL1519 Mc Z₁ L)
    (h22 : Lemma15122Concl T Mc M Z₁ L) (h24 : Lemma15124Concl T Mc M Z₁ V₁ V₂ L) :
    ¬ V₁ ≤ Subgroup.centralizer (L : Set G) := by
  intro hV1L
  have hS := hC.setting
  have hsmall := ce15Small_of_four_or_six h24.one
  have h7 := not_seven_of_four_or_six h24.one
  obtain ⟨t, htT, htS⟩ : ∃ t ∈ T, t ∉ s1516 T Z₁ := by
    by_contra hcon
    push Not at hcon
    have h1 := lemma_15_1_25_six hS h24.one
    rw [Subgroup.relIndex_eq_one.mpr (fun x hx => hcon x hx)] at h1
    omega
  have hswap : conjByElt t V₂ = V₁ := hS.swap_small hsmall h7 t htT htS
  obtain ⟨⟨-, -, hcomm, hnorm⟩, -⟩ := hS.y_facts hsmall
  have hV2ne : V₂ ≠ ⊥ := by
    intro h
    apply (h19.seven L hL.comp hL.quasi hL.not_le).2
    rw [h]
    exact Subgroup.commutator_bot_right L
  obtain ⟨y, ⟨hyM, k, hyk⟩, hyC⟩ : ∃ y ∈ {x : G | x ∈ M ⊓ g1_1516 Z₁ ∧ ∃ k : ℕ, orderOf x = 3 ^ k},
      y ∉ Subgroup.centralizer (V₂ : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) ≤ Subgroup.centralizer (V₂ : Set G) :=
      (Subgroup.closure_le _).mpr fun x hx => hcon x hx
    have h1 : ⁅oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁), V₂⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    rw [Subgroup.commutator_comm, hcomm] at h1
    exact hV2ne h1
  have hyY : y ∈ oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) := Subgroup.subset_closure ⟨hyM, k, hyk⟩
  obtain ⟨hxN, hxC⟩ := conj_normalizer_centralizer1515e hswap (hnorm hyY)
  have hx3 : orderOf (t * y * t⁻¹) = 3 ^ k := by
    rw [← hyk]
    exact orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective y
  set H' : Subgroup G := Subgroup.normalizer (V₁ : Set G) with hH'
  have hLC : L ≤ Subgroup.centralizer (V₁ : Set G) := fun l hl =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (hV1L hv) l hl).symm
  have hZ1V1 : Z₁ ≤ V₁ := h24.z1_le
  have hCG : Subgroup.centralizer (V₁ : Set G) ≤ g1_1516 Z₁ :=
    Subgroup.centralizer_le (fun z hz => hZ1V1 hz)
  have hCH : Subgroup.centralizer (V₁ : Set G) ≤ H' := Subgroup.centralizer_le_normalizer _
  have hLcC : L ∈ cComp (Subgroup.centralizer (V₁ : Set G)) := cComp_mem_of_le hL.comp hLC hCG
  have hsub : IsSubnormal (Subgroup.centralizer (V₁ : Set G)) H' :=
    A3.subnormal_of_normal hCH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr
        (normalizer_le_normalizer_centralizer V₁))
  have hLcH : L ∈ cComp H' := cComp_mem_of_subnormal hsub hLcC
  have hV1V : V₁ ≤ V154 T Mc M := (hS.decomp_other h7).1
  have hV1el : IsElemAbelian 2 V₁ :=
    isElemAbelian_mono151 hV1V (hS.V_isElemAbelian hC.qtfe hC.mf)
  have hV1ne : V₁ ≠ ⊥ := fun h => hS.z1_ne (le_bot_iff.mp (h ▸ hZ1V1))
  have hpc : pCoreOf 2 H' ≠ ⊥ := by
    intro h0
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer : V₁ ≤ H') le_rfl (isPGroup_of_isElemAbelian hV1el)
    rw [h0] at this
    exact hV1ne (le_bot_iff.mp this)
  have hH : SQTKGroup ↥H' :=
    sqtkGroup_of_pCoreOf_ne_bot hC.qtfe.qtke hC.qtfe.simple hC.qtfe.nonabelian hpc
  obtain ⟨S, _, _, ⟨e⟩, hSx⟩ := exists_exclusion_model_of_case15122 hK h19.one hL h24.two h22
  have hLeq : L = oPrimeResidualOf 3 H' :=
    eq_oPrimeResidualOf_three_of_exclusion hF h36 h38 hH hLcH hL.quasi e hSx
  have hxL : t * y * t⁻¹ ∈ L := by
    rw [hLeq]
    exact Subgroup.subset_closure ⟨hxN, k, hx3⟩
  refine hyC (hxC ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (hV1L hv) _ hxL).symm

@[expose] def Lemma15125InputFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Lemma15124Concl T Mc M Z₁ V₁ V₂ L → ¬ IsAltBlockType L 7

theorem lemma15125InputRestU_of_five (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (h5 : Lemma15125InputFive) :
    Lemma15125InputRestU := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24
  exact ⟨lemma_15_1_25_one_of_a318 hF h36 h38 hK hC h19 hL h22 h24,
    lemma_15_1_25_three_of_a318 hF h36 h38 hK hC h19 hL h22 h24,
    h5 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24⟩

end CFSG.Quasithin
