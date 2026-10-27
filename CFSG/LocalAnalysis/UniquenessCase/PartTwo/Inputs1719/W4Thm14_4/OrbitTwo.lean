module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.OrbitTwoDecide
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Data.A5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin

open CFSG.QuasithinUnique.A5.Delta5 (pact isEven)

theorem exists_orbit_two_of_perm {G : Type*} [Group G] (s : G →* Equiv.Perm (Fin 5))
    (hs2 : ∀ g, s g * s g = 1) (hsc : ∀ g h, s g * s h = s h * s g) (hne : ∃ g, s g ≠ 1) :
    ∃ x : Fin 5 → ZMod 2, isEven x ∧ ∃ g₀ : G, pact (s g₀) x ≠ x ∧
      ∀ g : G, pact (s g) x = x ∨ pact (s g) x = pact (s g₀) x := by
  obtain ⟨g₁, hg₁⟩ := hne
  by_cases hall : ∀ g : G, s g = 1 ∨ s g = s g₁
  · have hex : ∃ x : Fin 5 → ZMod 2, isEven x ∧ pact (s g₁) x ≠ x := by
      by_contra h
      have hf : ∀ x : Fin 5 → ZMod 2, isEven x → pact (s g₁) x = x := by
        intro x hx
        by_contra hpx
        exact h ⟨x, hx, hpx⟩
      exact hg₁ (CFSG.QuasithinUnique.A5.Delta5.pact_faithful (s g₁) hf)
    obtain ⟨x, hxeven, hxmove⟩ := hex
    refine ⟨x, hxeven, g₁, hxmove, fun g => ?_⟩
    rcases hall g with h | h
    · exact Or.inl (by rw [h]; exact CFSG.QuasithinUnique.A5.Delta5.pact_one x)
    · exact Or.inr (by rw [h])
  · have hall' : ∃ g : G, s g ≠ 1 ∧ s g ≠ s g₁ := by
      by_contra h
      apply hall
      intro g
      by_cases h1 : s g = 1
      · exact Or.inl h1
      · exact Or.inr (by
          by_contra h2
          exact h ⟨g, h1, h2⟩)
    obtain ⟨g₂, hg₂1, hg₂2⟩ := hall'
    have hne12 : s g₁ ≠ s g₂ := fun h => hg₂2 h.symm
    obtain ⟨x, hxeven, hx⟩ := perm5_orbit_two (s g₁) (s g₂)
      ⟨hs2 g₁, hs2 g₂, hsc g₁ g₂, hg₁, hg₂1, hne12⟩
    rcases hx with hx | hx | hx
    · refine ⟨x, hxeven, g₁, hx.1, fun g => ?_⟩
      exact hx.2 (s g) (hs2 g) (hsc g g₁) (hsc g g₂)
    · refine ⟨x, hxeven, g₂, hx.1, fun g => ?_⟩
      exact hx.2 (s g) (hs2 g) (hsc g g₁) (hsc g g₂)
    · refine ⟨x, hxeven, g₁ * g₂, ?_, fun g => ?_⟩
      · simpa only [map_mul] using hx.1
      · simpa only [map_mul] using hx.2 (s g) (hs2 g) (hsc g g₁) (hsc g g₂)

theorem not_orbit_two_of_mem_aSet_two {W : Type} [CommGroup W] [Finite W]
    {Y A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 Y) {w : W} {a₀ : MulAut W} (ha₀ : a₀ ∈ A)
    (hmv : a₀ w ≠ w) (horb : ∀ a ∈ A, a w = w ∨ a w = a₀ w) : False := by
  have hA' : A ≤ Y ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧
      ∀ B : Subgroup (MulAut W), B ≤ A → E3.mQuot A B < 2 → fixV B = fixV A := hA
  let B : Subgroup (MulAut W) := A ⊓ MulAction.stabilizer (MulAut W) w
  have hBA : B ≤ A := inf_le_left
  have ha₀B : a₀ ∉ B := by
    intro h
    exact hmv (by
      have h' := (Subgroup.mem_inf.mp h).2
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h')
  have hrel : B.relIndex A = 2 := by
    refine Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr ⟨a₀, ha₀, ha₀B, ?_⟩
    intro b hb
    rcases horb b hb with hbw | hbw
    · exact Or.inr (Subgroup.mem_inf.mpr ⟨hb, by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hbw⟩)
    · refine Or.inl (Subgroup.mem_inf.mpr ⟨A.mul_mem hb ha₀, ?_⟩)
      show (b * a₀) • w = w
      calc (b * a₀) • w = b • (a₀ • w) := mul_smul b a₀ w
        _ = b • (b • w) := by simp only [MulAut.smul_def, ← hbw]
        _ = (b * b) • w := (mul_smul b b w).symm
        _ = b ^ 2 • w := by rw [pow_two]
        _ = (1 : MulAut W) • w := by rw [hA'.2.2.1.2 b hb]
        _ = w := one_smul (MulAut W) w
  have hm : E3.mQuot A B < 2 := by
    show padicValNat 2 (B.relIndex A) < 2
    rw [hrel, padicValNat_base (by norm_num : 1 < 2)]
    norm_num
  have hfix : fixV B = fixV A := hA'.2.2.2 B hBA hm
  have hwB : w ∈ fixV B := mem_fixV.mpr fun b hb => by
    have hb' := (Subgroup.mem_inf.mp hb).2
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hb'
  have hwA : w ∉ fixV A := fun hw => hmv (mem_fixV.mp hw a₀ ha₀)
  rw [hfix] at hwB
  exact hwA hwB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
