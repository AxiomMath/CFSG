module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaRational
public import CFSG.RankThree.PartOne.CTP.SeitzThree
import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlane
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadMinus StatedClassicalModel)

@[expose] def SubfieldPairOmega8mCase (P : ℕ → Prop) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (k : Subfield K) (σ : K ≃+* K) (p f₀ : ℕ) (b c : k)
    (h : OmegaSetup K k σ p f₀ b c), P f₀ →
    ∀ d ∈ (linearConjugationHom (omegaQuad K (b : K) (c : K))).range,
      (fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
        (h.quad_invariant (by norm_num) h.order))).map d.toMonoidHom ≠
        fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
          (h.quad_invariant (by norm_num) h.order)) →
      Subgroup.closure ((fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
          (h.quad_invariant (by norm_num) h.order)) :
          Set (matrixProjectiveDerived (omegaQuad K (b : K) (c : K)))) ∪
        ((fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
          (h.quad_invariant (by norm_num) h.order))).map d.toMonoidHom :
          Set (matrixProjectiveDerived (omegaQuad K (b : K) (c : K))))) = ⊤ ∨
        ¬ p ∣ Nat.card (fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
          (h.quad_invariant (by norm_num) h.order)))

@[expose] def SubfieldPairOmega8m : Prop := SubfieldPairOmega8mCase fun _ => True

section Plane

theorem exists_conj_mem_of_plane_omega {T : Type} [Group T] [Finite T] {f p : ℕ}
    (hM : StatedClassicalModel T .POmegaMinus 4 2 f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (E : Subgroup (MulAut T)) [hE : IsElementaryAbelian p E] (hEc : Nat.card E = p ^ 2) :
    ∃ g : T, g ≠ 1 ∧ MulAut.conj g ∈ E := by
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
  have hnontriv : ∃ x : MulAut T, x ∈ E ∧ x ∈ (MulAut.conj : T →* MulAut T).range ∧ x ≠ 1 := by
    by_cases hin : E ≤ (MulAut.conj : T →* MulAut T).range
    · have hne : E ≠ ⊥ := fun h0 => by
        have := Subgroup.card_eq_one.2 h0
        omega
      obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
      exact ⟨x, x.2, hin x.2, fun h => hx1 (Subtype.ext h)⟩
    · have hpl := orthogonal_noninner_plane_local_core_product_odd_of_subfield
        orthogonal_prime_subfield_core_clause_unconditional T .POmegaMinus 2 f 4 p
        (Or.inr (Or.inr rfl)) hM hp (by omega) (by omega) ⊤ le_top E le_top hE hEc hin
      have hne : (E ⊓ (MulAut.conj : T →* MulAut T).range) ≠ ⊥ := fun h0 => by
        have := Subgroup.card_eq_one.2 h0
        have h1 := hpl.1
        rw [this] at h1
        have := hp.one_lt
        omega
      obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
      exact ⟨x, x.2.1, x.2.2, fun h => hx1 (Subtype.ext h)⟩
  obtain ⟨x, hxE, ⟨g, hg⟩, hx1⟩ := hnontriv
  exact ⟨g, fun h1 => hx1 (by rw [← hg, h1, map_one]), hg ▸ hxE⟩

end Plane

section Main

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {σ : K ≃+* K} {p f₀ : ℕ} {b c : k}

noncomputable def omegaModel (b c : K) :
    StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) ≃*
      matrixProjectiveDerived (omegaQuad K b c) :=
  coordinateMinusWitnessEquiv K (by norm_num) b c (MulEquiv.refl _)

omit [Finite K] in
theorem OmegaSetup.of_orderOf (h : OmegaSetup K k σ p f₀ b c) {σ' : K ≃+* K}
    (hσ' : orderOf σ' = p) (hf : ∀ x, x ∈ k ↔ σ' x = x) : OmegaSetup K k σ' p f₀ b c :=
  ⟨h.prime, h.five_le, h.one_le, h.card_k, h.card_K, hσ', hf, h.irr⟩

theorem omega_statedClassicalModel (h : OmegaSetup K k σ p f₀ b c) :
    StatedClassicalModel (matrixProjectiveDerived (omegaQuad K (b : K) (c : K)))
      .POmegaMinus 4 2 (p * f₀) :=
  ⟨⟨Nat.prime_two, Nat.mul_pos h.prime.pos h.one_le, le_rfl⟩, K, inferInstance, inferInstance,
    h.card_K', b, c, h.irr_K, ⟨(omegaModel (b : K) (c : K)).symm⟩⟩

def omegaStd (h : OmegaSetup K k σ p f₀ b c) :
    Set (MulAut (matrixProjectiveDerived (omegaQuad K (b : K) (c : K)))) :=
  {g | ∃ (σ' : K ≃+* K) (hσ' : orderOf σ' = p),
    g = fieldAutT (omegaQuad K (b : K) (c : K)) σ' (h.quad_invariant (by norm_num) hσ')}

omit [Finite K] in
theorem fixedSubgroup_fieldAutT_eq (h : OmegaSetup K k σ p f₀ b c) {σ₁ σ₂ : K ≃+* K}
    (h₁ : orderOf σ₁ = p) (h₂ : orderOf σ₂ = p) :
    fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ₁
      (h.quad_invariant (by norm_num) h₁)) =
    fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ₂
      (h.quad_invariant (by norm_num) h₂)) := by
  have hf : 1 ≤ f₀ * p := Nat.mul_pos h.one_le h.prime.pos
  have hz : ∀ {τ₁ τ₂ : K ≃+* K}, orderOf τ₁ = p → orderOf τ₂ = p →
      τ₂ ∈ Subgroup.zpowers τ₁ := fun {τ₁ τ₂} g₁ g₂ => by
    have := zpowers_ringEquiv_eq_of_orderOf Nat.prime_two hf h.card_K g₁ g₂
    exact this ▸ Subgroup.mem_zpowers τ₂
  have hmem : ∀ {τ₁ τ₂ : K ≃+* K} (g₁ : orderOf τ₁ = p) (g₂ : orderOf τ₂ = p),
      fieldPair (omegaQuad K (b : K) (c : K)) τ₂ (h.quad_invariant (by norm_num) g₂) ∈
        Subgroup.zpowers (fieldPair (omegaQuad K (b : K) (c : K)) τ₁
          (h.quad_invariant (by norm_num) g₁)) := by
    intro τ₁ τ₂ g₁ g₂
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hz g₁ g₂)
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext ?_⟩
    rw [fieldPair_zpow_val, hm]
    rfl
  exact fixedSubgroup_eq_of_zpowers_eq
    (matrixProjectiveConjugationHom (omegaQuad K (b : K) (c : K)))
    (le_antisymm ((Subgroup.zpowers_le).2 (hmem h₂ h₁)) ((Subgroup.zpowers_le).2 (hmem h₁ h₂)))

omit [Finite K] in
theorem center_eq_bot_of_solvableRadical {N : Type} [Group N] (h : solvableRadical N = ⊥) :
    Subgroup.center N = ⊥ :=
  le_bot_iff.1 (h ▸ le_sSup ⟨inferInstance, inferInstance⟩)

theorem eq_one_of_central_fixed_omega (h : OmegaSetup K k σ p f₀ b c) {σ' : K ≃+* K}
    (hσ' : orderOf σ' = p) {x : matrixProjectiveDerived (omegaQuad K (b : K) (c : K))}
    (hx : x ∈ fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ'
      (h.quad_invariant (by norm_num) hσ')))
    (hc : ∀ y ∈ fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ'
      (h.quad_invariant (by norm_num) hσ')), x * y = y * x) : x = 1 := by
  have : CharP K 2 := h.charP
  have hp5 := h.five_le
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaMinus 4 2 f₀ :=
    ⟨Nat.prime_two, h.one_le, le_rfl⟩
  obtain ⟨-, hconc⟩ :=
    orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional .POmegaMinus
      (Or.inr (Or.inr rfl)) 4 2 f₀ p hadm h.prime h.three_lt h.ne_two (by norm_num) K k h.card_k
      h.card_K σ' hσ' (h.fixed_of_orderOf hσ') b c h.irr
  obtain ⟨-, -, hfixiff, -, -, -, hrad, -, -, -⟩ := hconc
  have hxN := (hfixiff x).1 hx
  have hcen : (⟨x, hxN⟩ : ↥(subfieldFixedGroup k (coordinateQuadMinus 4 k (by norm_num) b c)
      (coordinateQuadMinus 4 K (by norm_num) (b : K) (c : K)))) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y.1 ((hfixiff y.1).2 y.2)).symm
  rw [center_eq_bot_of_solvableRadical hrad, Subgroup.mem_bot] at hcen
  exact congrArg Subtype.val hcen

theorem desc_omega (h : OmegaSetup K k σ p f₀ b c)
    {α : MulAut (matrixProjectiveDerived (omegaQuad K (b : K) (c : K)))}
    (hα : IsOuterOfOrder p α) :
    ∃ d ∈ (linearConjugationHom (omegaQuad K (b : K) (c : K))).range, ∃ f ∈ omegaStd h,
      α = d * f * d⁻¹ := by
  have : Finite (matrixProjectiveDerived (omegaQuad K (b : K) (c : K))) := inferInstance
  obtain ⟨hord, hout⟩ := hα
  have hαp : α ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one α
  have hαinn : α ∉ innerAut (matrixProjectiveDerived (omegaQuad K (b : K) (c : K))) :=
    fun ⟨g, hg⟩ => hout g hg.symm
  obtain ⟨d, hd, σ', hσ', hα'⟩ :=
    exists_conj_fieldAutT h (omegaModel (b : K) (c : K)).symm hαp hαinn
  refine ⟨d, hd, _, ⟨σ', hσ', rfl⟩, ?_⟩
  have hid : coordinateMinusWitnessEquiv K (by norm_num) (b : K) (c : K)
      (omegaModel (b : K) (c : K)).symm = MulEquiv.refl _ := by
    ext x
    simp only [omegaModel, coordinateMinusWitnessEquiv, MulEquiv.refl_apply]
    exact MulEquiv.apply_symm_apply _ x
  rw [hid] at hα'
  have h1 : MulAut.congr (MulEquiv.refl (matrixProjectiveDerived (omegaQuad K (b : K) (c : K))))
      α = α := by
    ext x
    rfl
  rwa [h1] at hα'

theorem fieldAutData_omega (hpair : SubfieldPairOmega8m) (h : OmegaSetup K k σ p f₀ b c) :
    FieldAutData (matrixProjectiveDerived (omegaQuad K (b : K) (c : K))) p := by
  classical
  have : Finite (matrixProjectiveDerived (omegaQuad K (b : K) (c : K))) := inferInstance
  refine fieldAutData_of_standard (p := p)
    (linearConjugationHom (omegaQuad K (b : K) (c : K))).range (omegaStd h) ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_conj_mem_of_plane_omega (omega_statedClassicalModel h) h.prime h.five_le E hEc
  · intro α hα
    exact desc_omega h hα
  · rintro _ ⟨σ₁, h₁, rfl⟩ _ ⟨σ₂, h₂, rfl⟩
    exact fixedSubgroup_fieldAutT_eq h h₁ h₂
  · rintro _ ⟨σ', hσ', rfl⟩ -
    intro x hx hc
    exact eq_one_of_central_fixed_omega h hσ' hx hc
  · rintro _ ⟨σ', hσ', rfl⟩ d hd hne
    exact hpair K k σ' p f₀ b c (h.of_orderOf hσ' (h.fixed_of_orderOf hσ')) trivial d hd hne

end Main

section Index

theorem fieldAutData_twistedD (hpair : SubfieldPairOmega8m) {G : Type} [Group G] [Finite G]
    {f p : ℕ} (hM : StatedClassicalModel G .POmegaMinus 4 2 f) (hp : p.Prime) (hp5 : 5 ≤ p) :
    FieldAutData G p := by
  by_cases hex : ∃ α : MulAut G, IsOuterOfOrder p α
  · obtain ⟨α, hord, hout⟩ := hex
    have hαp : α ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one α
    have hαinn : α ∉ innerAut G := fun ⟨g, hg⟩ => hout g hg.symm
    obtain ⟨f₀, K, _, _, k, σ, b, c, -, hsetup, ⟨ψ⟩⟩ := exists_rational_model hp hp5 hM hαp hαinn
    exact (fieldAutData_omega hpair hsetup).of_mulEquiv ψ hp
  · exact ⟨fun E hE hEc => by
      have := hE
      exact exists_conj_mem_of_plane_omega hM hp hp5 E hEc,
      fun σ hσ => absurd ⟨σ, hσ⟩ hex, fun σ τ hσ _ _ => absurd ⟨σ, hσ⟩ hex⟩

theorem extSeitzAtOuter_twistedD_of_pair (hpair : SubfieldPairOmega8m) {q : TauCeti.PrimePower}
    (hq : q.p = 2) : ExtSeitzAtOuter (.twistedD 4 q) := by
  intro G _ _ _ hnab hiso p hp hp5 hpd E hE hc hout
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hM := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even
    4 q hv hq e0
  rw [hq] at hM
  have hd : FieldAutData G p := fieldAutData_twistedD hpair hM hp hp5
  left
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc hout

end Index

end CFSG.RankThree.PartOne.SEITZ2
