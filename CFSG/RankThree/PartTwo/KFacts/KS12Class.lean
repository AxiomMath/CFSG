module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.KFacts.KS18OuterCore

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] def KS12OutSimple : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (Nonempty (S ≃* alternatingGroup (Fin 6)) ∨ Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.M22)) →
    ∀ σ : MulAut S, (∃ k : ℕ, σ ^ 3 ^ k = 1) → ∃ s : S, σ = MulAut.conj s

@[expose] def KS12ClassSL : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Sec4.IsSLThreePi X →
    ∀ T₁ T₂ : Subgroup X, CFSG.Assembly.IsElemAbelian 3 T₁ → Nat.card T₁ = 9 →
      Subgroup.center X ≤ T₁ → CFSG.Assembly.IsElemAbelian 3 T₂ → Nat.card T₂ = 9 →
      Subgroup.center X ≤ T₂ → ∃ x : X, T₂ = T₁.map (MulAut.conj x).toMonoidHom

@[expose] def KS12OutInner : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    (Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.M22) →
    ∀ σ : MulAut X, (∃ k : ℕ, σ ^ 3 ^ k = 1) → ∃ x : X, σ = MulAut.conj x

@[expose] def KS12ClassT : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    (Sec4.IsSLThreePi X ∨ Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.M22) →
    ∀ σ : MulAut X, (∃ k : ℕ, σ ^ 3 ^ k = 1) →
    ∀ T : Subgroup X, CFSG.Assembly.IsElemAbelian 3 T → Nat.card T = 9 →
      Subgroup.center X ≤ T → ∃ x : X, T.map σ.toMonoidHom = T.map (MulAut.conj x).toMonoidHom

theorem exists_conj_of_quotient_center {X S : Type} [Group X] [Group S]
    (hperf : commutator X = ⊤) (e : X ⧸ Subgroup.center X ≃* S)
    (hS : ∀ τ : MulAut S, (∃ k : ℕ, τ ^ 3 ^ k = 1) → ∃ s : S, τ = MulAut.conj s)
    (σ : MulAut X) (hσ : ∃ k : ℕ, σ ^ 3 ^ k = 1) : ∃ x : X, σ = MulAut.conj x := by
  obtain ⟨k, hk⟩ := hσ
  set τ : MulAut S := MulAut.congr e (centerDescend X σ) with hτdef
  have hτ : τ ^ 3 ^ k = 1 := by
    rw [hτdef, ← map_pow, ← map_pow, hk, map_one, map_one]
  obtain ⟨s, hs⟩ := hS τ ⟨k, hτ⟩
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk_surjective (e.symm s)
  refine ⟨x₀, ?_⟩
  have hmk : ∀ l : X, ((σ l : X) : X ⧸ Subgroup.center X) = ((x₀ * l * x₀⁻¹ : X) :
      X ⧸ Subgroup.center X) := by
    intro l
    have h1 : τ (e (l : X ⧸ Subgroup.center X)) = s * e (l : X ⧸ Subgroup.center X) * s⁻¹ := by
      rw [hs, MulAut.conj_apply]
    simp only [hτdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      centerDescend_mk] at h1
    have h2 := congrArg e.symm h1
    rw [MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply,
      ← hx₀] at h2
    rw [h2]
    rfl
  have hψ : ∀ l : X, ((MulAut.conj x₀)⁻¹ * σ) l * l⁻¹ ∈ Subgroup.center X := by
    intro l
    have h1 := hmk l
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv] at h1
    have h2 : ((MulAut.conj x₀)⁻¹ * σ) l * l⁻¹ = x₀⁻¹ * ((σ l) * (x₀ * l * x₀⁻¹)⁻¹) * x₀ := by
      rw [MulAut.mul_apply, MulAut.conj_inv_apply]
      group
    have h3 := Subgroup.mem_center_iff.mp h1 x₀⁻¹
    have h4 : x₀⁻¹ * (σ l * (x₀ * l * x₀⁻¹)⁻¹) * x₀ = σ l * (x₀ * l * x₀⁻¹)⁻¹ := by
      rw [h3, mul_assoc, inv_mul_cancel, mul_one]
    rw [h2, h4]
    exact h1
  have h1 := KS18.eq_of_mul_inv_mem_center hperf _ hψ
  ext l
  have h2 := h1 l
  rw [MulAut.mul_apply, MulAut.conj_inv_apply] at h2
  rw [MulAut.conj_apply]
  calc σ l = x₀ * (x₀⁻¹ * σ l * x₀) * x₀⁻¹ := by group
    _ = x₀ * l * x₀⁻¹ := by rw [h2]

theorem ks12OutInner_of (h : KS12OutSimple) : KS12OutInner := by
  intro X _ _ hq hX σ hσ
  have hperf : commutator X = ⊤ := by
    have h1 := hq.1
    rwa [Group.isPerfect_def] at h1
  rcases hX with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · exact exists_conj_of_quotient_center hperf e
      (h _ (Or.inl ⟨MulEquiv.refl _⟩)) σ hσ
  · exact exists_conj_of_quotient_center hperf e
      (h _ (Or.inr (Or.inl ⟨MulEquiv.refl _⟩))) σ hσ
  · exact exists_conj_of_quotient_center hperf e
      (h _ (Or.inr (Or.inr ⟨MulEquiv.refl _⟩))) σ hσ

theorem ks12ClassT_of (hO : KS12OutInner) (hSL : KS12ClassSL) : KS12ClassT := by
  intro X _ _ hq hX σ hσ T hTe hT9 hZT
  rcases hX with hSLX | hX'
  · have hZ : (Subgroup.center X).map σ.toMonoidHom = Subgroup.center X :=
      Subgroup.map_center_eq σ
    have hTe' : CFSG.Assembly.IsElemAbelian 3 (T.map σ.toMonoidHom) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
      · obtain ⟨_, x', hx', rfl⟩ := x
        obtain ⟨_, y', hy', rfl⟩ := y
        apply Subtype.ext
        change σ x' * σ y' = σ y' * σ x'
        rw [← map_mul, ← map_mul]
        exact congrArg σ (congrArg Subtype.val (hTe.1.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩))
      · rintro _ ⟨x', hx', rfl⟩
        change σ x' ^ 3 = 1
        rw [← map_pow, hTe.2 x' hx', map_one]
    have hT9' : Nat.card (T.map σ.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective σ.injective, hT9]
    have hZT' : Subgroup.center X ≤ T.map σ.toMonoidHom := by
      rw [← hZ]
      exact Subgroup.map_mono hZT
    obtain ⟨x, hx⟩ := hSL X hSLX T (T.map σ.toMonoidHom) hTe hT9 hZT hTe' hT9' hZT'
    exact ⟨x, hx⟩
  · obtain ⟨x, rfl⟩ := hO X hq hX' σ hσ
    exact ⟨x, rfl⟩

end CFSG.RankThree.PartTwo.KFacts
