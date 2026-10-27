module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux11

public section

open CFSG.Open
open scoped Pointwise
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type u} [Group Γ] [Finite Γ]

theorem subset_mul_of_chiefCyclic {p : ℕ} (hp : p.Prime) {A B X : Subgroup Γ}
    (hA : IsElemAbelian p A) (hAX : Admits A X) (hcop : Nat.Coprime p (Nat.card X))
    (hB : B ≤ A) (hH : ChiefCyclic p X) :
    (X : Set Γ) ⊆ (wSub A B X : Set Γ) * (cenIn X (B : Set Γ) : Set Γ) ∧
      (X : Set Γ) ⊆ (cenIn X (B : Set Γ) : Set Γ) * (wSub A B X : Set Γ) := by
  set W := wSub A B X with hW
  set Z := cenIn X (B : Set Γ) with hZ
  have hXnorm : IsNormalIn X (X ⊔ A) := ⟨le_sup_left, sup_le Subgroup.le_normalizer hAX⟩
  have hWX : W ≤ X := wSub_le A B X
  have hZX : Z ≤ X := cenIn_le_left _ _
  have key : ∀ V : Subgroup Γ, IsNormalIn V (X ⊔ A) → V ≤ X →
      ((X : Set Γ) ⊆ (W : Set Γ) * (Z : Set Γ) * (V : Set Γ) ∧
        (X : Set Γ) ⊆ (Z : Set Γ) * (W : Set Γ) * (V : Set Γ)) := by
    intro V
    induction V using WellFoundedGT.induction with
    | _ V ih =>
    intro hVn hVX
    rcases hVX.eq_or_lt with rfl | hVlt
    · exact ⟨fun x hx => ⟨1 * 1, ⟨1, one_mem _, 1, one_mem _, rfl⟩, x, hx, by simp⟩,
        fun x hx => ⟨1 * 1, ⟨1, one_mem _, 1, one_mem _, rfl⟩, x, hx, by simp⟩⟩
    · set 𝒮 : Set (Subgroup Γ) := {K | IsNormalIn K (X ⊔ A) ∧ V < K ∧ K ≤ X} with h𝒮
      obtain ⟨V₁, ⟨hV₁n, hVlt₁, hV₁X⟩, hmin⟩ : ∃ V₁ ∈ 𝒮, ∀ K ∈ 𝒮, ¬ K < V₁ :=
        (wellFounded_lt (α := Subgroup Γ)).has_min 𝒮 ⟨X, hXnorm, hVlt, le_rfl⟩
      have hchief : IsChiefFactorOf (X ⊔ A) V₁ V := by
        refine ⟨hVn, hV₁n, hVlt₁, fun K hK hVK hKV₁ => ?_⟩
        by_cases hKV : K = V
        · exact Or.inl hKV
        · right
          have hVK' : V < K := lt_of_le_of_ne hVK (Ne.symm hKV)
          exact (hKV₁.lt_or_eq).resolve_left fun hlt => hmin K ⟨hK, hVK', hKV₁.trans hV₁X⟩ hlt
      obtain ⟨ih1, ih2⟩ := ih V₁ hVlt₁ hV₁n hV₁X
      obtain ⟨sec1, sec2⟩ := sec_step hp hA hAX hcop hB hV₁X hchief hH
      have hW1 : wSub A B V₁ ≤ W := wSub_mono A B hV₁X
      have hZ1 : cenIn V₁ (B : Set Γ) ≤ Z := cenIn_mono_left hV₁X _
      have hXV₁ : X ≤ Subgroup.normalizer (V₁ : Set Γ) := le_sup_left.trans hV₁n.2
      have hXV : X ≤ Subgroup.normalizer (V : Set Γ) := le_sup_left.trans hVn.2
      constructor
      · intro x hx
        obtain ⟨wz, ⟨w, hw, z, hz, rfl⟩, v₁, hv₁, rfl⟩ := ih1 hx
        have hzX : z ∈ X := hZX hz
        have hvhat : z * v₁ * z⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp (hXV₁ hzX) v₁).mp hv₁
        obtain ⟨w₁z₁, ⟨w₁, hw₁, z₁, hz₁, rfl⟩, v, hv, hvv⟩ := sec1 hvhat
        have hvv' : w₁ * z₁ * v = z * v₁ * z⁻¹ := hvv
        have hvz : z⁻¹ * v * z ∈ V := by
          have := (Subgroup.mem_normalizer_iff.mp (hXV (inv_mem hzX)) v).mp hv
          simpa using this
        refine ⟨(w * w₁) * (z₁ * z), ⟨w * w₁, mul_mem hw (hW1 hw₁), z₁ * z,
          mul_mem (hZ1 hz₁) hz, rfl⟩, z⁻¹ * v * z, hvz, ?_⟩
        calc (w * w₁) * (z₁ * z) * (z⁻¹ * v * z) = w * (w₁ * z₁ * v) * z := by group
          _ = w * (z * v₁ * z⁻¹) * z := by rw [hvv']
          _ = w * z * v₁ := by group
      · intro x hx
        obtain ⟨zw, ⟨z, hz, w, hw, rfl⟩, v₁, hv₁, rfl⟩ := ih2 hx
        have hwX : w ∈ X := hWX hw
        have hvhat : w * v₁ * w⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp (hXV₁ hwX) v₁).mp hv₁
        obtain ⟨z₁w₁, ⟨z₁, hz₁, w₁, hw₁, rfl⟩, v, hv, hvv⟩ := sec2 hvhat
        have hvv' : z₁ * w₁ * v = w * v₁ * w⁻¹ := hvv
        have hvw : w⁻¹ * v * w ∈ V := by
          have := (Subgroup.mem_normalizer_iff.mp (hXV (inv_mem hwX)) v).mp hv
          simpa using this
        refine ⟨(z * z₁) * (w₁ * w), ⟨z * z₁, mul_mem hz (hZ1 hz₁), w₁ * w,
          mul_mem (hW1 hw₁) hw, rfl⟩, w⁻¹ * v * w, hvw, ?_⟩
        calc (z * z₁) * (w₁ * w) * (w⁻¹ * v * w) = z * (z₁ * w₁ * v) * w := by group
          _ = z * (w * v₁ * w⁻¹) * w := by rw [hvv']
          _ = z * w * v₁ := by group
  obtain ⟨k1, k2⟩ := key ⊥ ⟨bot_le, Subgroup.le_normalizer_of_normal⟩ bot_le
  constructor
  · intro x hx
    obtain ⟨wz, hwz, v, hv, rfl⟩ := k1 hx
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hv
    subst hv
    show wz * 1 ∈ _
    rw [mul_one]
    exact hwz
  · intro x hx
    obtain ⟨zw, hzw, v, hv, rfl⟩ := k2 hx
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hv
    subst hv
    show zw * 1 ∈ _
    rw [mul_one]
    exact hzw

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
