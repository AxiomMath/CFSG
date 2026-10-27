module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmall17
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine
public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_vzero_le_four_of_w3Lem914 (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G)
    (h88 : W3Thm88 G) (h126 : R126 D) (h914 : W3Lem914 G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hLperfect : L = CFSG.Quasithin.perfectCore (L ⊔ CFSG.Open.pCoreOf 2 (L ⊔ D.T)))
    (hψ : ∃ (Z : Type) (_ : Group Z) (ψ : ↥(L ⊔ D.T) →* Z), Function.Surjective ψ ∧
      (∀ x : ↥(L ⊔ D.T), ψ x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 (L ⊔ D.T)) ∧
      CFSG.IsComponent ((L.subgroupOf (L ⊔ D.T)).map ψ))
    (hAut : ∃ (A : Type) (_ : Group A)
      (φ : ↥((L ⊔ D.T) ⊓ normalizer (L : Set G)) →* A), Function.Surjective φ ∧
      (∀ x : ↥((L ⊔ D.T) ⊓ normalizer (L : Set G)),
        φ x = 1 ↔ (x : G) ∈ centSection (L ⊔ D.T) L (oTwoThreeIn L)) ∧
      (CFSG.Quasithin.F6.IsPGL2 7 A ∨
        Inputs1719.IsAutOf A (alternatingGroup (Fin 6)) ∨ Inputs1719.IsM10 A ∨
        CFSG.Quasithin.F6.IsPGL2 9 A))
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hU : UniqueMax D.M (L ⊔ D.T)) : Nat.card V₀ ≤ 4 := by
  by_contra h4
  have hV₀p : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup h.pairFacts.elemAbelian₀
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV₀p
  rw [hm] at h4
  have h8 : 8 ≤ Nat.card V₀ := by
    rw [hm]
    have hm3 : 3 ≤ m := by
      by_contra h
      apply h4
      have hm2 : m ≤ 2 := by omega
      calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
        _ = 4 := by norm_num
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  have hne : V₀ ≠ ⊥ := by
    rintro rfl
    simp at h8
  have hW : InCalV D.M V₀ := hyp125_inCalV h hne
  have hTI : IsTI V₀ := hyp125_isTI h hne
  have h9 : Hyp9 V₀ D.T := hyp9_of_hyp125 hTim hcat D h h8
  have hN : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hW
  have h1 : ¬ normalizer (E3.wClos V₀ 1 D.T : Set G) ≤ D.M :=
    twelve_seven_three_one hTim hcat D h66 h88 h.2 hW hTI h8
      (fun z hz hzc hz1 => hyp125_centralizer_le h hne hz hzc hz1)
  have hNM : L ⊔ D.T ≤ D.M := sup_le hL.1.le D.sylowM.le
  have hle : L ⊔ D.T ≤ normalizer (V₀ : Set G) := by
    rw [hN]
    exact hNM
  have hSyl : ∀ P : Subgroup G, IsSylowIn 3 P (L ⊔ D.T) → P ∈ calP V₀ := by
    intro P hP
    have hPM : P ≤ D.M := hP.le.trans hNM
    refine TwelveSixteen.mem_calP D hW hTI Nat.prime_three (by norm_num) hP.isPGroup ?_ ?_
    · intro g hg _
      have hg' : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
      simpa [conjSubgroup] using
        hsp.inf_map_conj_eq_bot Nat.prime_three hPM hP.isPGroup g⁻¹ hg'
    · exact hsp.rankThreeGamma_one_le_of_le Nat.prime_three hP.isPGroup hPM
  rcases h914 V₀ D.T (L ⊔ D.T) L h9 le_sup_right hle (sup_comm ..) hLperfect hψ hAut hSyl with
    h2 | h2
  · exact h1 (hN ▸ h2)
  · exact twelve_seven_one hTim hcat D h86 h126 h.2 hW hTI h8
      (uc22p22u_uniqueMax_mono D (le_inf hNM h2) inf_le_left hU)

theorem card_vzero_le_four_of_permuting_pair (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G)
    (h88 : W3Thm88 G) (h126 : R126 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (h93 : Thm93 V₀ D.T) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X₁ X₂ : Subgroup G}
    (hX₁p : IsPGroup p X₁)
    (hX₁M : ∀ g : G, g ∉ D.M → V₀ ≤ conjSubgroup D.M g → X₁ ⊓ conjSubgroup D.M g = ⊥)
    (hX₁Γ : rankThreeGamma 1 p X₁ ≤ D.M)
    (hX₁T : (X₁ : Set G) * D.T = D.T * X₁)
    (hX₂p : IsPGroup p X₂)
    (hX₂M : ∀ g : G, g ∉ D.M → V₀ ≤ conjSubgroup D.M g → X₂ ⊓ conjSubgroup D.M g = ⊥)
    (hX₂Γ : rankThreeGamma 1 p X₂ ≤ D.M)
    (hX₂T : (X₂ : Set G) * D.T = D.T * X₂)
    (hU : UniqueMax D.M (X₁ ⊔ X₂ ⊔ D.T)) : Nat.card V₀ ≤ 4 := by
  by_contra h4
  have hV₀p : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup h.pairFacts.elemAbelian₀
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV₀p
  rw [hm] at h4
  have h8 : 8 ≤ Nat.card V₀ := by
    rw [hm]
    have hm3 : 3 ≤ m := by
      by_contra h
      apply h4
      have hm2 : m ≤ 2 := by omega
      calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
        _ = 4 := by norm_num
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  have hne : V₀ ≠ ⊥ := by
    rintro rfl
    simp at h8
  have hW : InCalV D.M V₀ := hyp125_inCalV h hne
  have hTI : IsTI V₀ := hyp125_isTI h hne
  have h9 : Hyp9 V₀ D.T := hyp9_of_hyp125 hTim hcat D h h8
  have hN : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hW
  have h1 : ¬ normalizer (E3.wClos V₀ 1 D.T : Set G) ≤ D.M :=
    twelve_seven_three_one hTim hcat D h66 h88 h.2 hW hTI h8
      (fun z hz hzc hz1 => hyp125_centralizer_le h hne hz hzc hz1)
  have h2₁ : X₁ ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) :=
    (twelve_sixteen hTim hcat D h66 h88 h h8 h93 hp hp2 hX₁p hX₁M hX₁Γ hX₁T).2
  have h2₂ : X₂ ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) :=
    (twelve_sixteen hTim hcat D h66 h88 h h8 h93 hp hp2 hX₂p hX₂M hX₂Γ hX₂T).2
  have hX₁M' : X₁ ≤ D.M := (TwelveSixteen.le_rankThreeGamma hp hX₁p).trans hX₁Γ
  have hX₂M' : X₂ ≤ D.M := (TwelveSixteen.le_rankThreeGamma hp hX₂p).trans hX₂Γ
  have hNM : X₁ ⊔ X₂ ⊔ D.T ≤ D.M := sup_le (sup_le hX₁M' hX₂M') D.sylowM.le
  have hNW : X₁ ⊔ X₂ ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) := by
    rw [sup_assoc]
    exact sup_le (le_trans le_sup_left h2₁) h2₂
  exact twelve_seven_one hTim hcat D h86 h126 h.2 hW hTI h8
    (uc22p22u_uniqueMax_mono D (le_inf hNM hNW) inf_le_left hU)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
