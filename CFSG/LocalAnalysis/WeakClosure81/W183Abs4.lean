module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

@[expose] def IsTISub (G₀ : Type*) [Group G₀] (A₀ : Subgroup G₀) : Prop :=
  ∀ t ∈ A₀, t ≠ 1 → ∀ g : G₀, g * t = t * g → g ∈ Subgroup.normalizer (A₀ : Set G₀)

@[expose] def CorConfig (G₀ : Type*) [Group G₀] (A₀ : Subgroup G₀) : Prop :=
  ∃ (A' : Subgroup G₀) (S : Set (Subgroup G₀)) (y : G₀),
    (∃ g : G₀, A' = A₀.map (MulAut.conj g).toMonoidHom) ∧
    (∀ X ∈ S, ∃ g : G₀, X = A₀.map (MulAut.conj g).toMonoidHom) ∧
    A₀.map (MulAut.conj y).toMonoidHom ≠ A₀ ∧
    (∀ s ∈ A₀, ∃ z ∈ Subgroup.closure (⋃ X ∈ S, (X : Set G₀)), y * s * y⁻¹ = s * z) ∧
    ¬ A₀ ≤ Subgroup.normalizer (A' : Set G₀) ∧
    (∀ X ∈ S, X = A' ∨ ∀ a ∈ A', ∀ x ∈ X, a * x = x * a)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

namespace Assumption131

theorem centralizer_le_normalizer_of_mRank_le (h : Assumption131 G Γ VA i)
    {A : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hr : mRank A ≤ i) {t : LGL 2 V} (ht : t ∈ A)
    (ht1 : t ≠ 1) {g : LGL 2 V} (hg : g ∈ G) (hgt : g * t = t * g) :
    g ∈ Subgroup.normalizer (A : Set (LGL 2 V)) := by
  have hAg : cj g A ∈ Γ := h.invariant A hA g hg
  have hrg : mRank (cj g A) ≤ i := by
    unfold mRank
    rw [card_cj]
    exact hr
  refine (Subgroup.mem_normalizer_iff_map_conj_eq (H := A) (g := g)).mpr ?_
  by_contra hne
  have hbot := h.inf_eq_bot_of_mRank_le hA hAg hr hrg (Ne.symm hne)
  have hconj : (MulAut.conj g).toMonoidHom t = t := by
    show g * t * g⁻¹ = t
    rw [hgt]
    simp
  have ht' : t ∈ A ⊓ cj g A := ⟨ht, Subgroup.mem_map.mpr ⟨t, ht, hconj⟩⟩
  rw [hbot, Subgroup.mem_bot] at ht'
  exact ht1 ht'

theorem isTISub_of_member (h : Assumption131 G Γ VA i) {G₀ : Type*} [Group G₀]
    (χ : G₀ →* LGL 2 V) (hχ : Function.Injective χ) (hχG : ∀ g, χ g ∈ G)
    {A₀ : Subgroup G₀} (hA : A₀.map χ ∈ Γ) (hr : mRank (A₀.map χ) ≤ i) : IsTISub G₀ A₀ := by
  intro t ht ht1 g hgt
  have hn := h.centralizer_le_normalizer_of_mRank_le hA hr (Subgroup.mem_map_of_mem χ ht)
    (fun h1 => ht1 (hχ (by rw [h1, map_one]))) (hχG g) (by rw [← map_mul, ← map_mul, hgt])
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro x
  have := hn (χ x)
  have hconj : χ g * χ x * (χ g)⁻¹ = χ (g * x * g⁻¹) := by simp [map_mul, map_inv]
  rw [hconj] at this
  exact (Subgroup.mem_map_iff_mem hχ).symm.trans (this.trans (Subgroup.mem_map_iff_mem hχ))

theorem false_of_corConfig (h : Assumption131 G Γ VA i)
    (hVfix : ∀ A ∈ Γ, VA A ≤ fixSub A) {G₀ : Type*} [Group G₀]
    (χ : G₀ →* LGL 2 V) (hχ : Function.Injective χ) (hχG : ∀ g, χ g ∈ G)
    {A₀ : Subgroup G₀} (hA : A₀.map χ ∈ Γ) (hr : mRank (A₀.map χ) ≤ i)
    (hconf : CorConfig G₀ A₀) : False := by
  obtain ⟨A', S, y, ⟨gA, hA'⟩, hS, hy, hs, hn, hSA'⟩ := hconf
  have hmap : ∀ (X : Subgroup G₀) (g : G₀),
      (X.map (MulAut.conj g).toMonoidHom).map χ = cj (χ g) (X.map χ) := by
    intro X g
    unfold cj
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext z
    simp [MulAut.conj_apply]
  have hmem : ∀ g : G₀, (A₀.map (MulAut.conj g).toMonoidHom).map χ ∈ Γ := by
    intro g
    rw [hmap]
    exact h.invariant _ hA (χ g) (hχG g)
  have hrk : ∀ g : G₀, mRank ((A₀.map (MulAut.conj g).toMonoidHom).map χ) ≤ i := by
    intro g
    rw [hmap]
    unfold mRank
    rw [card_cj]
    exact hr
  have hA'Γ : A'.map χ ∈ Γ := hA' ▸ hmem gA
  have hA'r : mRank (A'.map χ) ≤ i := hA' ▸ hrk gA
  have h𝒮 : ∀ X ∈ {Y | ∃ X ∈ S, Y = X.map χ}, X ∈ Γ ∧ mRank X ≤ i := by
    rintro _ ⟨X, hX, rfl⟩
    obtain ⟨g, rfl⟩ := hS X hX
    exact ⟨hmem g, hrk g⟩
  refine h.false_of_commutator_transfer (D := A₀.map χ) (A' := A'.map χ) hA hA'Γ hr hA'r
    (hVfix _ hA'Γ) h𝒮 (y := χ y) (hχG y) ?_ ?_ ?_ ?_
  · intro heq
    rw [← hmap] at heq
    exact hy (Subgroup.map_injective hχ heq)
  · rintro _ ⟨s₀, hs₀, rfl⟩
    obtain ⟨z₀, hz₀, hz⟩ := hs s₀ hs₀
    refine ⟨χ z₀, ?_, by rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, hz]⟩
    have : χ z₀ ∈ (Subgroup.closure (⋃ X ∈ S, (X : Set G₀))).map χ :=
      Subgroup.mem_map_of_mem χ hz₀
    rw [MonoidHom.map_closure] at this
    refine (Subgroup.closure_mono ?_) this
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨X, hX, hwX⟩ := Set.mem_iUnion₂.mp hw
    exact Set.mem_iUnion₂.mpr ⟨X.map χ, ⟨X, hX, rfl⟩, Subgroup.mem_map_of_mem χ hwX⟩
  · intro hle
    apply hn
    intro a ha
    have := hle (Subgroup.mem_map_of_mem χ ha)
    rw [Subgroup.mem_normalizer_iff] at this ⊢
    intro x
    have hx := this (χ x)
    have hconj : χ a * χ x * (χ a)⁻¹ = χ (a * x * a⁻¹) := by simp [map_mul, map_inv]
    rw [hconj] at hx
    exact (Subgroup.mem_map_iff_mem hχ).symm.trans (hx.trans (Subgroup.mem_map_iff_mem hχ))
  · rintro _ ⟨X, hX, rfl⟩
    rcases hSA' X hX with rfl | hc
    · exact Or.inl rfl
    · refine Or.inr ?_
      rintro _ ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul, hc a ha x hx]

theorem false_of_ti_of_finite (h : Assumption131 G Γ VA i)
    (hVfix : ∀ A ∈ Γ, VA A ≤ fixSub A) {G₀ : Type*} [Group G₀]
    (χ : G₀ →* LGL 2 V) (hχ : Function.Injective χ) (hχG : ∀ g, χ g ∈ G)
    {A₀ : Subgroup G₀} (hA : A₀.map χ ∈ Γ) (hr : mRank (A₀.map χ) ≤ i)
    (hfin : IsTISub G₀ A₀ → CorConfig G₀ A₀) : False :=
  h.false_of_corConfig hVfix χ hχ hχG hA hr (hfin (h.isTISub_of_member χ hχ hχG hA hr))

end Assumption131

end CFSG.LocalAnalysis.WeakClosure81

end
