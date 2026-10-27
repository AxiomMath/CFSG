module

public import CFSG.Quasithin.EmptyFaithful.SBc14Pair
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc15

section Defs

variable {G : Type} [Group G]

@[expose] def ParabolicWeak (T X K G₁ : Subgroup G) : Prop :=
  (∀ g ∈ G₁, ∃ k ∈ K, ∃ y ∈ T, g = k * y) ∧
    ∀ k ∈ K, (∀ w ∈ pCoreOf 2 (X ⊔ T ⊓ K), k * w * k⁻¹ ∈ T ⊓ K) → k ∈ X ⊔ T ⊓ K

end Defs

section Generic

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G}
  {t : G}

theorem normalizer_le_of_parabolicWeak (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (h : ParabolicWeak T (oTwoUpper H) (conjClosure (oTwoUpper H) (mcOf T)) (mcOf T)) :
    Subgroup.normalizer ((T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) : Set G) ⊓ mcOf T ≤
      H := by
  set X := oTwoUpper H with hX
  set K := conjClosure X (mcOf T) with hK
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hsup : X ⊔ T = H := C1Pack12.oTwoUpper_sup_eq_of_sylow hsyl
  have hXH : X ≤ H := oTwoUpper_le H
  have hXn : H ≤ Subgroup.normalizer (X : Set G) := le_normalizer_oTwoUpper H
  have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := le_normalizer_conjClosure _ _
  have hXK : X ≤ K := le_conjClosure _ _
  have hUX : T ⊓ K ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans (hTH.trans hXn)
  have hTU : T ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := fun y hy =>
    SBc14.mem_normalizer_inf (Subgroup.le_normalizer hy) (hKn (hHG (hTH hy)))
  have hTJ : T ≤ Subgroup.normalizer ((X ⊔ T ⊓ K : Subgroup G) : Set G) := by
    intro y hy
    apply CosetGeom.mem_normalizer_of_conjSub_eq
    rw [show conjSub y (X ⊔ T ⊓ K) = conjSub y X ⊔ conjSub y (T ⊓ K) from
      Subgroup.map_sup _ _ _, conjSub_eq_of_mem_normalizer (hXn (hTH hy)),
      conjSub_eq_of_mem_normalizer (hTU hy)]
  have hJH : X ⊔ T ⊓ K ≤ H := sup_le hXH (inf_le_left.trans hTH)
  have hJK : X ⊔ T ⊓ K ≤ K := sup_le hXK inf_le_right
  have hWn : H ≤ Subgroup.normalizer (pCoreOf 2 (X ⊔ T ⊓ K) : Set G) := by
    rw [← hsup]
    exact sup_le (le_sup_left.trans (le_normalizer_pCoreOf 2 _))
      (hTJ.trans (normalizer_le_normalizer_pCoreOf 2 _))
  have hWQ : pCoreOf 2 (X ⊔ T ⊓ K) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hJH) hWn (pCoreOf_isPGroup 2 _)
  have hQT : pCoreOf 2 H ≤ T := hsyl.pCoreOf_le
  have hWT₀ : pCoreOf 2 (X ⊔ T ⊓ K) ≤ T ⊓ Subgroup.normalizer (H₁ : Set G) :=
    le_inf (hWQ.trans hQT) (hWQ.trans (hdec.Q₁.trans Subgroup.le_normalizer))
  intro g hg
  obtain ⟨hgN, hgG⟩ := hg
  obtain ⟨k, hk, y, hy, rfl⟩ := h.1 g hgG
  have hyN := hdec.le_normalizer_inf hy
  have hkN : k ∈ Subgroup.normalizer
      ((T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) : Set G) := by
    have := Subgroup.mul_mem _ hgN (Subgroup.inv_mem _ hyN)
    simpa using this
  have hkJ : k ∈ X ⊔ T ⊓ K := by
    refine h.2 k hk fun w hw => ⟨?_, ?_⟩
    · exact ((Subgroup.mem_normalizer_iff.mp hkN w).mp (hWT₀ hw)).1
    · have hwK : w ∈ K := hJK (pCoreOf_le 2 _ hw)
      exact K.mul_mem (K.mul_mem hk hwK) (K.inv_mem hk)
  exact H.mul_mem (hJH hkJ) (hTH hy)

end Generic

section Inputs

@[expose] def Input14616ParabolicTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → p = 3 → Stage14614C2 T H p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t →
        ParabolicWeak T (oTwoUpper H) (conjClosure (oTwoUpper H) (mcOf T)) (mcOf T)

@[expose] def Stage14614C3A {G : Type} [Group G] (T H : Subgroup G) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (K₁ : Subgroup G) (s : G), K₁ ∈ cComp (mcOf T) ∧ s ∈ T ∧
    s ∉ Subgroup.normalizer (K₁ : Set G) ∧
    conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ ∧
    Nonempty (OTwoQuot (mcOf T) ≃* (Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2)))

@[expose] def Stage14614C3B {G : Type} [Group G] (T H : Subgroup G) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (K₁ : Subgroup G) (s : G), K₁ ∈ cComp (mcOf T) ∧ s ∈ T ∧
    s ∉ Subgroup.normalizer (K₁ : Set G) ∧
    conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ ∧
    Nonempty (OTwoQuot (mcOf T) ≃*
      (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≀ᵣ Multiplicative (ZMod 2)))

theorem stage14614C3_iff {G : Type} [Group G] (T H : Subgroup G) (p : ℕ) :
    Stage14614C3 T H p ↔ Stage14614C3A T H p ∨ Stage14614C3B T H p := by
  constructor
  · rintro ⟨hp, K₁, s, h1, h2, h3, h4, h5 | h5⟩
    · exact Or.inl ⟨hp, K₁, s, h1, h2, h3, h4, h5⟩
    · exact Or.inr ⟨hp, K₁, s, h1, h2, h3, h4, h5⟩
  · rintro (⟨hp, K₁, s, h1, h2, h3, h4, h5⟩ | ⟨hp, K₁, s, h1, h2, h3, h4, h5⟩)
    · exact ⟨hp, K₁, s, h1, h2, h3, h4, Or.inl h5⟩
    · exact ⟨hp, K₁, s, h1, h2, h3, h4, Or.inr h5⟩

@[expose] def Input14616ParabolicThreeA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → p = 3 → Stage14614C3A T H p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t →
        ParabolicWeak T (oTwoUpper H) (conjClosure (oTwoUpper H) (mcOf T)) (mcOf T)

@[expose] def Input14616ParabolicThreeB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → p = 3 → Stage14614C3B T H p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t →
        ParabolicWeak T (oTwoUpper H) (conjClosure (oTwoUpper H) (mcOf T)) (mcOf T)

theorem input14616Weak_of_parabolic (h2 : Input14616ParabolicTwo)
    (h3a : Input14616ParabolicThreeA) (h3b : Input14616ParabolicThreeB) : Input14616Weak := by
  intro G _ _ T M S H PQ p hred hp hC H₀ H₁ H₂ t hdec
  have hdecP : IsDecP T M H p H₀ H₁ H₂ t := hdec.toIsDecP hred
  refine normalizer_le_of_parabolicWeak S hred hdecP ?_
  rcases hC with hC | hC
  · exact h2 G T M S H PQ p hred hp hC H₀ H₁ H₂ t hdecP
  · rcases (stage14614C3_iff T H p).mp hC with hC | hC
    · exact h3a G T M S H PQ p hred hp hC H₀ H₁ H₂ t hdecP
    · exact h3b G T M S H PQ p hred hp hC H₀ H₁ H₂ t hdecP

end Inputs

end SBc15

end CFSG.Quasithin
