module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenAbstract
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenMatrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open Matrix
open CFSG.RankThree.PartTwo.Sec15.KSL3Two (IsMonomialWith)
open CFSG.LieType.SeitzGeneration (IsCoordBlockOn)

namespace SL3G

section Generic

variable {G : Type} [Group G] {K : Type} [Field K]

@[expose] def ConjProp (ι : G →* GL (Fin 3) K) (Θ : Subgroup (GL (Fin 3) K)) : Prop :=
  ∀ θ ∈ Θ, ∃ β : MulAut G, ∀ g, ι (β g) = θ⁻¹ * ι g * θ

@[expose] def FrameProp (ι : G →* GL (Fin 3) K) (Θ : Subgroup (GL (Fin 3) K)) : Prop :=
  ∀ (T Q : Subgroup (GL (Fin 3) K)) (u : GL (Fin 3) K),
    (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) → (∀ s ∈ T, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q) → u ∈ Q →
    u ∈ ι.range → u ^ 3 = 1 → (∀ c : K, (u : Matrix (Fin 3) (Fin 3) K) ≠ c • 1) →
    ∃ θ ∈ Θ, ∃ ε : Fin 3 → K, IsFrame T Q u θ ε

@[expose] def ClassProp (ι : G →* GL (Fin 3) K) : Prop :=
  ∀ α : MulAut G, α ^ 3 = 1 → ∃ (σ : K ≃+* K) (B : GL (Fin 3) K),
    (σ = 1 ∨ orderOf σ = 3) ∧ ActsAs ι α σ B

@[expose] def BlockProp (ι : G →* GL (Fin 3) K) : Prop :=
  ∀ H : Subgroup G, (∀ a b : Fin 3, a ≠ b → ∀ g : G,
    IsCoordBlockOn a b ((ι g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → g ∈ H) → H = ⊤

@[expose] def FieldProp (ι : G →* GL (Fin 3) K) : Prop :=
  ∀ (α : MulAut G) (T : Subgroup G) (σ : K ≃+* K) (B : GL (Fin 3) K), ModelHyp α T →
    orderOf σ = 3 → ActsAs ι α σ B →
    (∀ s ∈ T, ∃ τ : Fin 3 → Fin 3,
      IsMonomialWith ((ι s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) τ) →
    (∀ x ∈ T ⊓ fixSub α, ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) → False

private theorem actsAs_one_matrix {G : Type} [Group G] {ι : G →* GL (Fin 3) K}
    {α : MulAut G} {B : GL (Fin 3) K} (hact : ActsAs ι α 1 B) :
    (∀ g : G, ((ι (α g) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K) * ((ι g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ∧
    ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (B : Matrix (Fin 3) (Fin 3) K) = 1 ∧
    (B : Matrix (Fin 3) (Fin 3) K) *
        ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
  have hone : ∀ M : Matrix (Fin 3) (Fin 3) K, M.map ⇑(1 : K ≃+* K) = M := fun M => by
    ext i j
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro g
    have := hact g
    rwa [hone] at this
  · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

private theorem core_inner [Finite G] {ι : G →* GL (Fin 3) K} (hι : Function.Injective ι)
    (hblock : BlockProp ι) {α : MulAut G} {T : Subgroup G} (hH : ModelHyp α T) {t : G} (ht : t ∈ T)
    {B : GL (Fin 3) K}
    (hact' : ∀ g : G, ((ι (α g) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K) * ((ι g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hBinv : ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (B : Matrix (Fin 3) (Fin 3) K) = 1)
    (hBinv' : (B : Matrix (Fin 3) (Fin 3) K) *
      ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1)
    {ε : Fin 3 → K} (hu : ((ι (t * (α t)⁻¹) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ε)
    (hε : Function.Injective ε) (hε1 : ∃ j, ε j = 1)
    (hmono : ∀ s ∈ T, ∃ τ : Fin 3 → Fin 3,
      IsMonomialWith ((ι s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) τ) :
    T ⊔ fixSub α = ⊤ := by
  have hcommB : ∀ x ∈ fixSub α, ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (B : Matrix (Fin 3) (Fin 3) K) = (B : Matrix (Fin 3) (Fin 3) K) *
        ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro x hx
    have h1 := hact' x
    rw [mem_fixSub.mp hx] at h1
    calc ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)
        = ((B : Matrix (Fin 3) (Fin 3) K) * ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * (B : Matrix (Fin 3) (Fin 3) K) := by
          rw [← h1]
      _ = (B : Matrix (Fin 3) (Fin 3) K) * ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [Matrix.mul_assoc, hBinv, Matrix.mul_one]
  obtain ⟨hu_mem, -⟩ := commutator_fixed hH ht
  have hBdiag : (B : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    refine TauCeti.isDiag_of_commute_diagonal hε ?_
    show diagonal ε * (B : Matrix (Fin 3) (Fin 3) K) = (B : Matrix (Fin 3) (Fin 3) K) * diagonal ε
    rw [← hu]
    exact hcommB _ hu_mem.2
  have hαt : (ι (α t) : GL (Fin 3) K) = B * ι t * B⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact hact' t
  have hu' : ((ι t * B * (ι t)⁻¹ * B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ε := by
    rw [← hu, map_mul, map_inv, hαt]
    congr 1
    group
  obtain ⟨τ, hτ⟩ := hmono t ht
  have hτ3 := monomial_perm_cube ι hH.pgroup ht hτ
  obtain ⟨hτ1, i, j, hij, hBij⟩ := equal_entries hτ hτ3 hBdiag hu' hε hε1
  have hplane : ∀ g : G, IsCoordBlockOn i j ((ι g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →
      g ∈ T ⊔ fixSub α := by
    intro g hg
    have hcomm := plane_central hBdiag hBij hg
    have hαg : α g = g := by
      apply hι
      apply Units.ext
      rw [hact' g, ← hcomm, Matrix.mul_assoc, hBinv', Matrix.mul_one]
    exact Subgroup.mem_sup_right (mem_fixSub.mpr hαg)
  exact hblock _ (planes_of_cycle ι (T ⊔ fixSub α) (Subgroup.mem_sup_left ht) hτ hτ3 hτ1 hij hplane)

private theorem core_generic [Finite G] {ι : G →* GL (Fin 3) K} (hι : Function.Injective ι)
    (hcls : ClassProp ι) (hblock : BlockProp ι) (hfield : FieldProp ι)
    {α : MulAut G} {T : Subgroup G} (hH : ModelHyp α T) {t : G} (ht : t ∈ T) {ε : Fin 3 → K}
    (hu : ((ι (t * (α t)⁻¹) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ε)
    (hε : Function.Injective ε) (hε1 : ∃ j, ε j = 1)
    (hmono : ∀ s ∈ T, ∃ τ : Fin 3 → Fin 3,
      IsMonomialWith ((ι s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) τ)
    (hdiag : ∀ x ∈ T ⊓ fixSub α, ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    T ⊔ fixSub α = ⊤ := by
  obtain ⟨σ, B, hσ, hact⟩ := hcls α hH.cube
  rcases hσ with rfl | hσ3
  swap
  · exact (hfield α T σ B hH hσ3 hact hmono hdiag).elim
  obtain ⟨hact', hBinv, hBinv'⟩ := actsAs_one_matrix hact
  exact core_inner hι hblock hH ht hact' hBinv hBinv' hu hε hε1 hmono

theorem model_generic [Finite G] {ι : G →* GL (Fin 3) K} (hι : Function.Injective ι)
    {Θ : Subgroup (GL (Fin 3) K)} (hconj : ConjProp ι Θ) (hframe : FrameProp ι Θ)
    (hcls : ClassProp ι) (hblock : BlockProp ι) (hfield : FieldProp ι) : ModelGen G := by
  intro α T hH
  obtain ⟨t, ht, hmv⟩ := hH.moves
  obtain ⟨hu_mem, hu3⟩ := commutator_fixed hH ht
  have hcos := coset_fixed hH.cube hH.stable hH.index
  have hQab : ∀ x ∈ (T ⊓ fixSub α).map ι, ∀ y ∈ (T ⊓ fixSub α).map ι, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hc := hH.abelian.is_comm.comm (⟨x, hx⟩ : ↥(T ⊓ fixSub α)) ⟨y, hy⟩
    have hc' : x * y = y * x := congrArg Subtype.val hc
    rw [← map_mul, ← map_mul, hc']
  have hQn : ∀ s ∈ T.map ι, ∀ x ∈ (T ⊓ fixSub α).map ι, s * x * s⁻¹ ∈ (T ⊓ fixSub α).map ι := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨s * x * s⁻¹, fix_normal hH.stable hcos hH.abelian s hs x hx, by simp⟩
  have hnsc : ∀ c : K, ((ι (t * (α t)⁻¹) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 :=
    fun c hc => hmv (center_of_scalar hι hc)
  obtain ⟨θ, hθΘ, ε, hdiagu, hεinj, hε1, hQdiag, hTmono⟩ :=
    hframe (T.map ι) ((T ⊓ fixSub α).map ι) (ι (t * (α t)⁻¹)) hQab hQn ⟨_, hu_mem, rfl⟩
      ⟨_, rfl⟩ (by rw [← map_pow, hu3, map_one]) hnsc
  obtain ⟨β, hβ⟩ := hconj θ hθΘ
  have hH' := ModelHyp.congr β hH
  have hβα : MulAut.congr β α (β t) = β (α t) := by simp [MulAut.congr_apply]
  have hcore := core_generic hι hcls hblock hfield hH' (t := β t) ⟨t, ht, rfl⟩ (ε := ε)
    (by
      rw [hβα, ← map_inv, ← map_mul, hβ]
      exact hdiagu)
    hεinj hε1
    (by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨τ, hτ⟩ := hTmono (ι s) ⟨s, hs, rfl⟩
      refine ⟨τ, ?_⟩
      show IsMonomialWith ((ι (β s) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) τ
      rw [hβ]
      exact hτ)
    (by
      rintro _ ⟨hxT, hxF⟩
      rw [fixSub_congr] at hxF
      obtain ⟨x, hx, rfl⟩ := hxF
      obtain ⟨y, hy, hyx⟩ := hxT
      have hyx' : y = x := β.injective hyx
      subst hyx'
      show ((ι (β y) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag
      rw [hβ]
      exact hQdiag (ι y) ⟨y, ⟨hy, hx⟩, rfl⟩)
  exact (sup_fixSub_congr β α T).mp hcore

end Generic

end SL3G

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
