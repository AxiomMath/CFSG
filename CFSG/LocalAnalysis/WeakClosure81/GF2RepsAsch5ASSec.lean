module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3b
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bar
public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecIn
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def ShapeInEAS (j : ℕ) (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (L₀ : Type) [Group L₀] [Finite L₀], IsSimpleGroup L₀ → (∃ a b : L₀, a * b ≠ b * a) → P L₀ →
    ∀ A S : Subgroup (MulAut L₀), AlmostSimpleData L₀ A S → E1.InE j A

theorem inE_top_of_isPGroup_two (j : ℕ) {Q : Type} [Group Q] [Finite Q] (h : IsPGroup 2 Q) :
    E1.InE j (⊤ : Subgroup Q) := by
  intro T hT Ω hΩ
  have hTtop : T = ⊤ := by
    obtain ⟨-, -, hnd⟩ := hT
    obtain ⟨n, hn⟩ := h.index T
    rw [Subgroup.relIndex_top_right, hn] at hnd
    have hn0 : n = 0 := by
      by_contra hn0
      exact hnd (dvd_pow_self 2 hn0)
    rw [hn0, pow_zero] at hn
    exact Subgroup.index_eq_one.mp hn
  subst hTtop
  have hTN : (⊤ : Subgroup Q) ≤ normalizer (E1.weakClosure (⊤ : Subgroup Q) Ω : Set Q) :=
    E1.le_normalizer_weakClosure hΩ
  rw [top_le_iff.mp hTN, top_inf_eq, sup_top_eq]

theorem inE_of_isPGroup_two (j : ℕ) {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (h : IsPGroup 2 ↥H) : E1.InE j H :=
  (E1.inE_subgroupOf j H).mpr (inE_top_of_isPGroup_two j h)

theorem compFactorAutInEAS_of_cfShape {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsPGroup 2 T) {P : ∀ (X : Type) [Group X], Prop} {j : ℕ}
    (hCF : CFShape G P) (hS : ShapeInEAS j P) : CompFactorAutInEAS j T := by
  intro M N hN hNM hNs hMs hsimple
  haveI := hN
  let W := ↥M ⧸ N.subgroupOf M
  haveI : Finite W := inferInstance
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) fun _ _ h => MulEquiv.ext (congrFun h)
  have hP0 : IsPGroup 2 ↥(H13.P31Sec.secP T M N) := by
    refine IsPGroup.map ?_ H13.P31Sec.secActHom
    have hP1 : IsPGroup 2
        ↥(T ⊓ Subgroup.normalizer (M : Set G) ⊓ Subgroup.normalizer (N : Set G)) :=
      hT.to_le fun x hx => hx.1.1
    exact hP1.of_equiv (Subgroup.subgroupOfEquivOfLe H13.P31Sec.le_secB_inf).symm
  by_cases hab : ∀ a b : W, a * b = b * a
  · have hInn : H13.P31Sec.innGroup W = ⊥ := by
      rw [eq_bot_iff]
      rintro α ⟨w, rfl⟩
      refine MulEquiv.ext fun x => ?_
      show w * x * w⁻¹ = x
      rw [hab w x, mul_assoc, mul_inv_cancel, mul_one]
    have hA : RonanE111.innAutInduced T M N = H13.P31Sec.secP T M N := by
      rw [H13.P31Sec.innAutInduced_eq_sup hNM, hInn, bot_sup_eq]
    rw [hA]
    exact inE_of_isPGroup_two j hP0
  · have hnab : ∃ a b : W, a * b ≠ b * a := by
      by_contra h
      exact hab fun a b => by
        by_contra hne
        exact h ⟨a, b, hne⟩
    have hcf : E1.IsCompositionFactor G W :=
      ⟨N, M, inferInstance, hNM, hNs, hMs, hsimple, ⟨MulEquiv.refl W⟩⟩
    have hPW : P W := hCF W hcf hnab
    have hP0A : H13.P31Sec.secP T M N ≤ RonanE111.innAutInduced T M N :=
      H13.P31Sec.secP_le_innAutInduced hNM
    obtain ⟨S, hSylowOf, hP0S⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_isSylowOf_ge_of_isPGroup hP0 hP0A
    have hSylowIn : IsSylowIn 2 S (RonanE111.innAutInduced T M N) :=
      isSylowOf_two_iff_isSylowIn.mp hSylowOf
    have hsd : AlmostSimpleData W (RonanE111.innAutInduced T M N) S := by
      refine ⟨?_, hSylowIn, ?_⟩
      · exact H13.P31Sec.innGroup_le_innAutInduced hNM
      · refine le_antisymm (sup_le (H13.P31Sec.innGroup_le_innAutInduced hNM) hSylowIn.1) ?_
        rw [H13.P31Sec.innAutInduced_eq_sup hNM]
        exact sup_le_sup_left hP0S _
    exact hS W hsimple hnab hPW (RonanE111.innAutInduced T M N) S hsd

theorem inE_of_cfShape {G : Type} [Group G] [Finite G] {T : Subgroup G} {j : ℕ} (hj : 1 ≤ j)
    (hT : IsSylowIn 2 T ⊤) {P : ∀ (X : Type) [Group X], Prop} (hCF : CFShape G P)
    (hS : ShapeInEAS j P) : E1.InE j (⊤ : Subgroup G) :=
  asch4_3E_AS_holds G T j hj hT (compFactorAutInEAS_of_cfShape hT.isPGroup hCF hS)

end CFSG.LocalAnalysis.WeakClosure81

end
