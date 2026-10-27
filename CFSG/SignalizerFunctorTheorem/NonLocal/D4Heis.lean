module

public import CFSG.SignalizerFunctorTheorem.NonLocal.HeisFam
public import CFSG.SignalizerFunctorTheorem.NonLocal.D4Relations

public noncomputable section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

section D4

variable (K : Type) [Field K] (τ : K →+* K)

@[expose, reducible] def D4P : Unit ⊕ Unit → Type
  | Sum.inl _ => ↥(trialityFixedField K τ)
  | Sum.inr _ => K

instance (s : Unit ⊕ Unit) : AddCommGroup (D4P K τ s) := by
  rcases s with s | s
  · exact inferInstanceAs (AddCommGroup ↥(trialityFixedField K τ))
  · exact inferInstanceAs (AddCommGroup K)

instance (s : Unit ⊕ Unit) [Finite K] : Finite (D4P K τ s) := by
  rcases s with s | s
  · exact inferInstanceAs (Finite ↥(trialityFixedField K τ))
  · exact inferInstanceAs (Finite K)

theorem trialityTrace_neg (hτ : τ ^ 3 = 1) (x : K) :
    trialityTrace K τ hτ (-x) = -trialityTrace K τ hτ x :=
  Subtype.ext (by simp only [coe_trialityTrace, map_neg, Subfield.coe_neg]; ring)

theorem trialityTrace_add (hτ : τ ^ 3 = 1) (x y : K) :
    trialityTrace K τ hτ (x + y) = trialityTrace K τ hτ x + trialityTrace K τ hτ y :=
  Subtype.ext (by simp only [coe_trialityTrace, map_add, Subfield.coe_add]; ring)

theorem trialityTrace_smul (hτ : τ ^ 3 = 1) (c : trialityFixedField K τ) (x : K) :
    trialityTrace K τ hτ ((c : K) * x) = c * trialityTrace K τ hτ x :=
  Subtype.ext (by
    simp only [coe_trialityTrace, map_mul, mem_trialityFixedField.1 c.2, Subfield.coe_mul]
    ring)

end D4

section D4Main


theorem no_small_faithful_action_D4 {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) (hσ : σ.toRingHom ^ 3 = 1) (hK : Nat.card K = 8) {Λ : Type} [Finite Λ]
    (hΛ : Nat.card Λ ≤ 28) :
    ∀ π : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* Equiv.Perm Λ,
      Function.Injective π → False := by
  classical
  set τ := σ.toRingHom with hτ
  intro π hπ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨⟨f₁, -, hf₁⟩, ⟨f₂, -, hf₂⟩, ⟨f₃, -, hf₃⟩, ⟨f₄, -, hf₄⟩, ⟨f₅, -, hf₅⟩,
    ⟨f₆, hf₆inj, hf₆⟩, -⟩ := even_triality_positive_orbit_parametrization K σ hσ
  obtain ⟨-, hc34, hc25, -, -, hc23, hc24, hc26, hc35, hc36, hc45, hc46, hc56, hT, hnd⟩ :=
    even_triality_trace_commutators_nc K τ hσ
  have hle : graphFixedPosUnipotent TwistTag.D4 K τ ≤ graphFixedRootGroup TwistTag.D4 K τ :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  let inc : ↥(graphFixedPosUnipotent TwistTag.D4 K τ) →*
      ↥(graphFixedRootGroup TwistTag.D4 K τ) := Subgroup.inclusion hle
  let emb : ↥(graphFixedRootGroup TwistTag.D4 K τ) →* ↥(adjointGroup TwistTag.D4.tag K) :=
    Subgroup.inclusion ((graphFixedRootGroup_le _ _ _).trans
      (twistedFixedGroup_le_adjointGroup _ _ _))
  have hemb : Function.Injective emb := Subgroup.inclusion_injective _
  let g₂ := inc.comp f₂
  let g₃ := inc.comp f₃
  let g₄ := inc.comp f₄
  let g₅ := inc.comp f₅
  let g₆ := inc.comp f₆
  have e₂ : ∀ b, emb (g₂ (Multiplicative.ofAdd b)) = trialityX₂ K τ b := fun b =>
    Subtype.ext (hf₂ b)
  have e₃ : ∀ s, emb (g₃ (Multiplicative.ofAdd s)) = trialityX₃ K τ s := fun s =>
    Subtype.ext (hf₃ s)
  have e₄ : ∀ t, emb (g₄ (Multiplicative.ofAdd t)) = trialityX₄ K τ t := fun t =>
    Subtype.ext (hf₄ t)
  have e₅ : ∀ b, emb (g₅ (Multiplicative.ofAdd b)) = trialityX₅ K τ b := fun b =>
    Subtype.ext (hf₅ b)
  have e₆ : ∀ b, emb (g₆ (Multiplicative.ofAdd b)) = trialityX₆ K τ b := fun b =>
    Subtype.ext (hf₆ b)
  have transfer : ∀ {u v : ↥(graphFixedRootGroup TwistTag.D4 K τ)},
      Commute (emb u) (emb v) → Commute u v := fun {u v} h => by
    show u * v = v * u
    apply hemb
    simpa only [map_mul] using h.eq
  have R25 : ∀ b e : trialityFixedField K τ,
      ⁅g₂ (Multiplicative.ofAdd b), g₅ (Multiplicative.ofAdd e)⁆ =
        g₆ (Multiplicative.ofAdd (b * e)) := fun b e => hemb (by
    rw [map_commutatorElement, e₂, e₅, e₆]
    exact hc25 b e)
  have R34 : ∀ s t : K, ⁅g₃ (Multiplicative.ofAdd s), g₄ (Multiplicative.ofAdd t)⁆ =
      g₆ (Multiplicative.ofAdd (trialityTrace K τ hσ (s * t))) := fun s t => hemb (by
    rw [map_commutatorElement, e₃, e₄, e₆]
    exact hc34 s t)
  have h2k : (1 : trialityFixedField K τ) + 1 = 0 :=
    Subtype.ext (by
      rw [Subfield.coe_add, Subfield.coe_one, Subfield.coe_zero, one_add_one_eq_two]
      exact CharTwo.two_eq_zero)
  let H : HeisFam ↥(graphFixedRootGroup TwistTag.D4 K τ) (Unit ⊕ Unit) (D4P K τ)
      ↥(trialityFixedField K τ) :=
    { xa := fun s => match s with
        | Sum.inl _ => fun b => g₂ (Multiplicative.ofAdd b)
        | Sum.inr _ => fun t => g₃ (Multiplicative.ofAdd t)
      xb := fun s => match s with
        | Sum.inl _ => fun b => g₅ (Multiplicative.ofAdd b)
        | Sum.inr _ => fun t => g₄ (Multiplicative.ofAdd t)
      z := fun w => g₆ (Multiplicative.ofAdd w)
      e := fun s => match s with
        | Sum.inl _ => fun c d => c * d
        | Sum.inr _ => fun c d => trialityTrace K τ hσ (c * d)
      Rg := ⊤
      z_add := fun w w' => by rw [ofAdd_add, map_mul]
      e_add_left := fun s c c' d => by
        rcases s with s | s
        · show (c + c') * d = c * d + c' * d
          exact add_mul c c' d
        · show trialityTrace K τ hσ ((c + c') * d) =
            trialityTrace K τ hσ (c * d) + trialityTrace K τ hσ (c' * d)
          rw [add_mul, trialityTrace_add]
      e_mem := fun _ _ _ => AddSubgroup.mem_top _
      e_surj := fun s c hc w _ => by
        rcases s with s | s
        · refine ⟨w / c, ?_⟩
          show c * (w / c) = w
          field_simp
        · have hc' : c ≠ 0 := hc
          obtain ⟨t, ht⟩ : ∃ t, trialityTraceForm K τ hσ c t ≠ 0 := by
            by_contra h
            push Not at h
            exact hc' (hnd.1 c h)
          refine ⟨((w / trialityTraceForm K τ hσ c t : trialityFixedField K τ) : K) * t, ?_⟩
          show trialityTrace K τ hσ (c * (((w / trialityTraceForm K τ hσ c t :
            trialityFixedField K τ) : K) * t)) = w
          rw [mul_left_comm, trialityTrace_smul, ← hT c t]
          field_simp
      xa_comm := fun s t c d => by
        rcases s with s | s <;> rcases t with t | t
        · show g₂ (Multiplicative.ofAdd c) * g₂ (Multiplicative.ofAdd d) =
            g₂ (Multiplicative.ofAdd d) * g₂ (Multiplicative.ofAdd c)
          rw [← map_mul g₂, ← map_mul g₂, mul_comm]
        · exact (transfer (by rw [e₂, e₃]; exact hc23 c d)).eq
        · exact (transfer (by rw [e₃, e₂]; exact (hc23 d c).symm)).eq
        · show g₃ (Multiplicative.ofAdd c) * g₃ (Multiplicative.ofAdd d) =
            g₃ (Multiplicative.ofAdd d) * g₃ (Multiplicative.ofAdd c)
          rw [← map_mul g₃, ← map_mul g₃, mul_comm]
      xb_comm := fun s t c d => by
        rcases s with s | s <;> rcases t with t | t
        · show g₅ (Multiplicative.ofAdd c) * g₅ (Multiplicative.ofAdd d) =
            g₅ (Multiplicative.ofAdd d) * g₅ (Multiplicative.ofAdd c)
          rw [← map_mul g₅, ← map_mul g₅, mul_comm]
        · exact (transfer (by rw [e₅, e₄]; exact (hc45 d c).symm)).eq
        · exact (transfer (by rw [e₄, e₅]; exact hc45 c d)).eq
        · show g₄ (Multiplicative.ofAdd c) * g₄ (Multiplicative.ofAdd d) =
            g₄ (Multiplicative.ofAdd d) * g₄ (Multiplicative.ofAdd c)
          rw [← map_mul g₄, ← map_mul g₄, mul_comm]
      z_comm_a := fun w s d => by
        rcases s with s | s
        · exact (transfer (by rw [e₆, e₂]; exact (hc26 d w).symm)).eq
        · exact (transfer (by rw [e₆, e₃]; exact (hc36 d w).symm)).eq
      z_comm_b := fun w s d => by
        rcases s with s | s
        · exact (transfer (by rw [e₆, e₅]; exact (hc56 d w).symm)).eq
        · exact (transfer (by rw [e₆, e₄]; exact (hc46 d w).symm)).eq
      xab_comm := fun s t hst c d => by
        rcases s with s | s <;> rcases t with t | t
        · exact absurd (congrArg Sum.inl (Subsingleton.elim s t)) hst
        · exact (transfer (by rw [e₅, e₃]; exact (hc35 d c).symm)).eq
        · exact (transfer (by rw [e₄, e₂]; exact (hc24 d c).symm)).eq
        · exact absurd (congrArg Sum.inr (Subsingleton.elim s t)) hst
      comm_ss := fun s c d => by
        rcases s with s | s
        · show ⁅(g₅ (Multiplicative.ofAdd c))⁻¹, g₂ (Multiplicative.ofAdd d)⁆ =
            g₆ (Multiplicative.ofAdd (c * d))
          rw [← map_inv, ← ofAdd_neg, ← commutatorElement_inv, R25, ← map_inv, ← ofAdd_neg]
          congr 2
          ring
        · show ⁅(g₄ (Multiplicative.ofAdd c))⁻¹, g₃ (Multiplicative.ofAdd d)⁆ =
            g₆ (Multiplicative.ofAdd (trialityTrace K τ hσ (c * d)))
          rw [← map_inv, ← ofAdd_neg, ← commutatorElement_inv, R34, ← map_inv, ← ofAdd_neg,
            mul_neg, trialityTrace_neg, neg_neg, mul_comm d c] }
  have hz1 : H.z 1 * H.z 1 = 1 := by
    show g₆ (Multiplicative.ofAdd (1 : trialityFixedField K τ)) *
      g₆ (Multiplicative.ofAdd (1 : trialityFixedField K τ)) = 1
    rw [← map_mul, ← ofAdd_add, h2k, ofAdd_zero, map_one]
  have hg₆inj : Function.Injective g₆ := (Subgroup.inclusion_injective hle).comp hf₆inj
  have hz1' : H.z 1 ≠ 1 := by
    intro h
    have h0 : g₆ (Multiplicative.ofAdd (1 : trialityFixedField K τ)) =
        g₆ (Multiplicative.ofAdd (0 : trialityFixedField K τ)) := by
      rw [ofAdd_zero, map_one g₆]
      exact h
    exact one_ne_zero (Multiplicative.ofAdd.injective (hg₆inj h0))
  have hπz : π (H.z 1) ≠ 1 := by
    intro h
    exact hz1' (hπ (h.trans (map_one π).symm))
  have hmain := H.two_mul_card_le_perm π ⟨1, AddSubgroup.mem_top _, hz1, hπz⟩
  have hcard : Nat.card (∀ s, D4P K τ s) = Nat.card (trialityFixedField K τ) * Nat.card K := by
    rw [Nat.card_pi, Fintype.prod_sum_type]
    simp only [Finset.univ_unique, Finset.prod_singleton]
  have hk2 : 2 ≤ Nat.card (trialityFixedField K τ) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  rw [hcard, hK] at hmain
  omega

end D4Main

end CFSG.SignalizerFunctorTheorem.NonLocal
