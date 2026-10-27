module

public import CFSG.LocalAnalysis.WeakClosure81.Thirteen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

namespace Assumption131

theorem inf_eq_bot_of_mRank_le (h : Assumption131 G Γ VA i) {A B : Subgroup (LGL 2 V)}
    (hA : A ∈ Γ) (hB : B ∈ Γ) (hAr : mRank A ≤ i) (hBr : mRank B ≤ i) (hne : A ≠ B) :
    A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  rintro a ha
  rw [Subgroup.mem_bot]
  by_contra ha1
  have hleA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha.1
  have hleB : Subgroup.zpowers a ≤ B := Subgroup.zpowers_le.mpr ha.2
  have hcA : commSub (Subgroup.zpowers a) ≤ VA A :=
    (commSub_mono _ _ hleA).trans (commSub_le_VA_of_mRank_le h hA hAr)
  have hcB : commSub (Subgroup.zpowers a) ≤ VA B :=
    (commSub_mono _ _ hleB).trans (commSub_le_VA_of_mRank_le h hB hBr)
  have hne0 : commSub (Subgroup.zpowers a) ≠ ⊥ := fun hbot =>
    ha1 (Subgroup.zpowers_eq_bot.mp ((commSub_eq_bot_iff (Subgroup.zpowers a)).mp hbot))
  refine hne0 (le_bot_iff.mp ?_)
  calc commSub (Subgroup.zpowers a) ≤ VA A ⊓ VA B := le_inf hcA hcB
    _ = ⊥ := h.disjoint A hA B hB hne

theorem commSpace_VA_eq_bot_of_le_normalizer (h : Assumption131 G Γ VA i)
    {A B : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hB : B ∈ Γ) (hBr : mRank B ≤ i) (hne : A ≠ B)
    (hnorm : B ≤ Subgroup.normalizer (A : Set (LGL 2 V))) : commSpace B (VA A) = ⊥ := by
  rw [eq_bot_iff]
  refine commSpace_le_iff.2 fun b hb v hv => ?_
  have hstab : b ∈ stabilizerOf G (VA A) := by
    rw [← h.normalizer_eq A hA]
    exact ⟨h.le_G B hB hb, hnorm hb⟩
  have hbv : b v ∈ VA A := by
    have := apply_mem_conjSub (g := b) hv
    rwa [hstab.2] at this
  have h1 : b v - v ∈ VA A := (VA A).sub_mem hbv hv
  have h2 : b v - v ∈ VA B := commSub_le_VA_of_mRank_le h hB hBr (sub_mem_commSub B hb v)
  have h3 : b v - v ∈ VA A ⊓ VA B := ⟨h1, h2⟩
  rwa [h.disjoint A hA B hB hne] at h3

theorem commSpace_VA_eq_bot_of_commute (h : Assumption131 G Γ VA i)
    {A B : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hB : B ∈ Γ) (hBr : mRank B ≤ i) (hne : A ≠ B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : commSpace B (VA A) = ⊥ := by
  refine h.commSpace_VA_eq_bot_of_le_normalizer hA hB hBr hne fun b hb => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have := hcomm a ha b hb
    have e : b * a * b⁻¹ = a := by rw [← this]; group
    rwa [e]
  · intro ha
    have hc := hcomm (b * a * b⁻¹) ha b hb
    have e1 : a = b⁻¹ * ((b * a * b⁻¹) * b) := by group
    rw [hc, ← mul_assoc, inv_mul_cancel, one_mul] at e1
    rw [e1]
    exact ha

theorem stabilizer_le_normalizer (h : Assumption131 G Γ VA i) {A : Subgroup (LGL 2 V)}
    (hA : A ∈ Γ) {v : V} (hv : v ∈ VA A) (hv0 : v ≠ 0) {g : LGL 2 V} (hg : g ∈ G) (hgv : g v = v) :
    g ∈ Subgroup.normalizer (A : Set (LGL 2 V)) := by
  have hAg : cj g A ∈ Γ := h.invariant A hA g hg
  have hvg : v ∈ VA (cj g A) := by
    rw [h.equivariant A hA g hg]
    have := apply_mem_conjSub (g := g) hv
    rwa [hgv] at this
  refine (Subgroup.mem_normalizer_iff_map_conj_eq (H := A) (g := g)).mpr ?_
  by_contra hne
  have hdis := h.disjoint A hA (cj g A) hAg (Ne.symm hne)
  have hboth : v ∈ VA A ⊓ VA (cj g A) := ⟨hv, hvg⟩
  rw [hdis] at hboth
  exact hv0 (by simpa using hboth)

theorem fixSub_le_fixSub_of_conj_mem_coset (h : Assumption131 G Γ VA i)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (hDr : mRank D ≤ i) {Z : Subgroup (LGL 2 V)}
    {y : LGL 2 V} (hy : y ∈ G) (hDy : cj y D ≠ D)
    (hs : ∀ s ∈ D, ∃ z ∈ Z, y * s * y⁻¹ = s * z) : fixSub Z ≤ fixSub D := by
  intro w hw s hs'
  obtain ⟨z, hz, hzs⟩ := hs s hs'
  have hyD : cj y D ∈ Γ := h.invariant D hD y hy
  have hrk : mRank (cj y D) ≤ i := by
    unfold mRank
    rw [card_cj]
    exact hDr
  have hmem : y * s * y⁻¹ ∈ cj y D := Subgroup.mem_map.mpr ⟨s, hs', rfl⟩
  have hA : (y * s * y⁻¹) w - w ∈ VA (cj y D) :=
    commSub_le_VA_of_mRank_le h hyD hrk (sub_mem_commSub (cj y D) hmem w)
  have hB : s w - w ∈ VA D := commSub_le_VA_of_mRank_le h hD hDr (sub_mem_commSub D hs' w)
  have heq : (y * s * y⁻¹) w = s w := by
    rw [hzs]
    show s (z w) = s w
    rw [hw z hz]
  rw [heq] at hA
  have hboth : s w - w ∈ VA D ⊓ VA (cj y D) := ⟨hB, hA⟩
  rw [h.disjoint D hD (cj y D) hyD (Ne.symm hDy)] at hboth
  have h0 : s w - w = 0 := by simpa using hboth
  exact sub_eq_zero.mp h0

theorem false_of_commutator_transfer (h : Assumption131 G Γ VA i)
    {D A' : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (hA' : A' ∈ Γ) (hDr : mRank D ≤ i)
    (hA'r : mRank A' ≤ i) (hVfix : VA A' ≤ fixSub A') {𝒮 : Set (Subgroup (LGL 2 V))}
    (h𝒮 : ∀ X ∈ 𝒮, X ∈ Γ ∧ mRank X ≤ i) {y : LGL 2 V} (hy : y ∈ G) (hDy : cj y D ≠ D)
    (hs : ∀ s ∈ D, ∃ z ∈ Subgroup.closure (⋃ X ∈ 𝒮, (X : Set (LGL 2 V))), y * s * y⁻¹ = s * z)
    (hDnorm : ¬ D ≤ Subgroup.normalizer (A' : Set (LGL 2 V)))
    (h𝒮A' : ∀ X ∈ 𝒮, X = A' ∨ ∀ a ∈ A', ∀ x ∈ X, a * x = x * a) : False := by
  have hfix : VA A' ≤ fixSub (Subgroup.closure (⋃ X ∈ 𝒮, (X : Set (LGL 2 V)))) := by
    intro v hv z hz
    refine Subgroup.closure_induction (p := fun z _ => z v = v) ?_ ?_ ?_ ?_ hz
    · intro x hx
      obtain ⟨X, hXS, hxX⟩ := Set.mem_iUnion₂.mp hx
      by_cases hXA : X = A'
      · subst hXA
        exact hVfix hv x hxX
      · rcases h𝒮A' X hXS with hXA' | hc
        · exact absurd hXA' hXA
        · have hbot := h.commSpace_VA_eq_bot_of_commute hA' (h𝒮 X hXS).1 (h𝒮 X hXS).2
            (Ne.symm hXA) hc
          exact commSpace_eq_bot_iff.mp hbot x hxX v hv
    · rfl
    · intro x y _ _ hx hy
      show x (y v) = v
      rw [hy, hx]
    · intro x _ hx
      show x⁻¹ v = v
      calc x⁻¹ v = x⁻¹ (x v) := by rw [hx]
        _ = v := by simp
  have hD' := h.fixSub_le_fixSub_of_conj_mem_coset hD hDr hy hDy hs
  have hne : commSub A' ≠ ⊥ := commSub_ne_bot_of_mem h hA'
  have hle : commSub A' ≤ VA A' := commSub_le_VA_of_mRank_le h hA' hA'r
  have hVne : VA A' ≠ ⊥ := fun hb => hne (le_bot_iff.mp (hb ▸ hle))
  obtain ⟨v, hvV, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
  apply hDnorm
  intro d hd
  exact h.stabilizer_le_normalizer hA' hvV hv0 (h.le_G D hD hd) (hD' (hfix hvV) d hd)

end Assumption131

end CFSG.LocalAnalysis.WeakClosure81

end
