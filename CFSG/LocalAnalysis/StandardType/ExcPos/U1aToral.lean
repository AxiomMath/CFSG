module

public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aE6Rank
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHom
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral
public import CFSG.LocalAnalysis.StandardType.GGA6GlueToral
public import CFSG.LocalAnalysis.StandardType.GGSixRCKStepZero
public import CFSG.LocalAnalysis.StandardType.GGLieM6cFinal
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
public import CFSG.LocalAnalysis.StandardType.GGLieBridgePartner
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRest

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.StandardType.ClassicalPosition CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

theorem excU1a_toral
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) {X : Type} [Group X] [Finite X]
    {n f p : ℕ} {ψ : (ggU t n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (h : GGSixPosHyp t n f ψ p G₀ B₁ D J L x) (hf : 1 ≤ f)
    {θ : ↥G₀ →* ModGL (langTag t) GGL} {lam : ↥B₁ →* ModGL (langTag t) GGL}
    (hθker : θ.ker = Subgroup.center ↥G₀) (hθrange : θ.range = ⁅ggFixGp t f, ggFixGp t f⁆)
    (hθι : ∀ (k : (ggU t n f).K) (hk : ψ k ∈ G₀), θ ⟨ψ k, hk⟩ = ggIotaK t n f hf k)
    (hcent : ∀ z ∈ ggFixGp t f, (∀ y, z * θ y = θ y * z) → z = 1)
    (hlam : ∀ b, lam b ∈ ggFixGp t f) (hpart : ∀ b : ↥B₁, GGLiePartner G₀ θ b (lam b))
    (hlam1 : ∀ b : ↥B₁, lam b = 1 ↔ (b : X) ∈ Subgroup.centralizer (G₀ : Set X)) :
    IsToralSubgroup (langTag t) GGL ((D.subgroupOf B₁).map lam) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := h
  let E := (D.subgroupOf B₁).map lam
  have hE_le : E ≤ ggFixGp t f := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
    exact hlam b
  have hE_el : IsElemAbelian p E := by
    have hDel : IsElemAbelian p D := h9.mono h11
    exact (hDel.subgroupOf B₁).map lam
  have hE_card : Nat.card E ≤ p ^ 2 := by
    calc Nat.card E ≤ Nat.card (D.subgroupOf B₁) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd (D.subgroupOf B₁) lam)
      _ = Nat.card D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe h11).toEquiv
      _ = p ^ 2 := h12
  have hExcFive : GGExcFive t := by
    rcases ht with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases CFSG.StandardType.A6Red.a6glue_toral_or_nontoral hExcFive hf h5 h6 hE_le hE_el
    hE_card with hT | ⟨hE6, hp3, _⟩
  · exact hT
  · rcases ht with rfl | rfl | rfl
    ·
      obtain ⟨A, hB1A, hAel, hAN, hAdiag, hAC, hAcent, hArank⟩ := h31 (Or.inl rfl)
      have hlam_inj : Function.Injective lam := by
        rw [injective_iff_map_eq_one]
        intro b hb
        have hbC : (b : X) ∈ Subgroup.centralizer (G₀ : Set X) := (hlam1 b).mp hb
        have hbA : (b : X) ∈ A := hB1A b.2
        have hbot : (b : X) ∈ A ⊓ Subgroup.centralizer (G₀ : Set X) := ⟨hbA, hbC⟩
        rw [hAC] at hbot
        exact Subtype.ext (by simpa using hbot)
      have hadm : StatedLieAdmissible .E6 n 2 f := LieModel.admissible h3
      have hrk : 2 ≤ (ggU .E6 n f).D.rank := by
        rw [ggRank_untw (Or.inr (Or.inl rfl)) n f]
        decide
      have hperfK : commutator (ggU .E6 n f).K = ⊤ := (ggU_perfect_lieModel hadm hrk).1
      have hperfG : commutator ↥G₀ = ⊤ := by
        have hKperf : Group.IsPerfect (ggU .E6 n f).K := Group.isPerfect_def.mpr hperfK
        have hsurj : Function.Surjective (ψ.codRestrict G₀ (fun a => h1 ▸ ⟨a, rfl⟩)) := by
          intro g
          obtain ⟨a, ha⟩ := (show (g : X) ∈ ψ.range from by rw [h1]; exact g.2)
          exact ⟨a, Subtype.ext ha⟩
        haveI : Group.IsPerfect (ggU .E6 n f).K := hKperf
        exact Group.isPerfect_def.mp (Group.IsPerfect.ofSurjective
          (f := ψ.codRestrict G₀ (fun a => h1 ▸ ⟨a, rfl⟩)) hsurj)
      have hpres : GGPresentsG0 G₀ (ggU .E6 n f).D .E6 n f ψ :=
        ⟨⟨hadm, hrk⟩, ⟨h1, h2⟩, hperfG, h3⟩
      have hrange : θ.range ≤ ggFixGp .E6 f := hθrange ▸ Subgroup.commutator_le_self _
      by_cases hfodd : Odd f
      ·
        let E' := (B₁.subgroupOf B₁).map lam
        have hE'_le : E' ≤ ggFixGp .E6 f := by
          intro z hz
          obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
          exact hlam b
        have hE'_el : IsElemAbelian p E' := (h9.subgroupOf B₁).map lam
        have hE'_card : Nat.card E' = Nat.card B₁ := by
          change Nat.card ((B₁.subgroupOf B₁).map lam) = Nat.card B₁
          rw [Subgroup.card_map_of_injective hlam_inj]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_refl B₁)).toEquiv
        have h4' : p ^ 4 ≤ Nat.card E' := by rw [hE'_card]; exact h10
        have hfl : RCKBand.StepZeroRankFloor .E6 f p E' := by
          refine ⟨?_, ?_⟩
          · intro _
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro h
              rcases h with h | h <;> exact absurd h (by decide)
            · intro _ hfe
              exact absurd hfe (Nat.not_even_iff_odd.mpr hfodd)
            · intro h
              exact absurd h (by decide)
            · intro h
              exact absurd h (by decide)
          · intro h
            exact absurd h (by decide)
        have hv : ¬ RCKBand.CaseEightV .E6 f p E' := by
          intro h
          exact absurd h.1 (by decide)
        have h6c : CFSG.StandardType.LieCore.GGLieNonToralRankFour :=
          CFSG.StandardType.LieCore.M6c.ggLieNonToralRankFour_holds
        have hE'_toral : IsToralSubgroup .E6 GGL E' :=
          (RCKBand.ggLieToralStepZeroRCK_of_M6c h6c) .E6 hExcFive f hf p h5 h6
            E' hE'_le hE'_el h4' hfl hv
        have hE_le_E' : E ≤ E' := by
          intro z hz
          obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
          exact Subgroup.mem_map.mpr ⟨b, b.2, rfl⟩
        obtain ⟨g, hg, hgt⟩ := hE'_toral
        exact ⟨g, hg, fun y hy => hgt y (hE_le_E' hy)⟩
      ·
        have hfe : Even f := by
          rcases Nat.even_or_odd f with he | ho
          · exact he
          · exact absurd ho hfodd
        have hpartA : ∀ a ∈ A, ∃ a' ∈ ggFixGp .E6 f, GGLiePartner G₀ θ a a' := by
          intro a ha
          exact ggLiePartner_exists hExcFive hf hpres hrange hθι (hAN ha) (hAdiag a ha)
        obtain ⟨A', hA'_le, hA'_el, hA'_card, hA'_part, -⟩ :=
          ggLieBridge_partner_hom G₀ A (ggFixGp .E6 f) θ hperfG hθker hAN hAel hAC hcent hpartA
        have hEA' : E ≤ A' := by
          intro z hz
          obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
          have hbB1 : (b : X) ∈ B₁ := b.2
          obtain ⟨a, ha, hpa⟩ := hA'_part (b : X) (hB1A hbB1)
          have huniq : lam b = a :=
            GGLiePartner.unique hcent (h7 hbB1) (hlam b) (hA'_le ha) (hpart b) hpa
          rw [huniq]
          exact ha
        have hA'_adj : A' ≤ adjointGroup .E6 GGL := RCKBand.rckSZ_le_adjoint hA'_le
        have hcard5 : 3 ^ ((langTag .E6).rank - 1) ≤ Nat.card A' := by
          rw [hA'_card]
          have hrank := excU1a_e6_twoLocalRank h1 h2 h3 hfe (le_sup_right : G₀ ≤ A ⊔ G₀)
          have hArank' : 3 ^ CFSG.Assembly.LargeEvenTwoLocalRank 3 ↥(A ⊔ G₀) ≤ Nat.card A := by
            simpa only [hp3] using hArank
          calc 3 ^ ((langTag .E6).rank - 1) = 3 ^ 5 := by decide
            _ ≤ 3 ^ CFSG.Assembly.LargeEvenTwoLocalRank 3 ↥(A ⊔ G₀) :=
                Nat.pow_le_pow_right (by norm_num) hrank
            _ ≤ Nat.card A := hArank'
        have hcard5' : p ^ ((langTag .E6).rank - 1) ≤ Nat.card A' := by
          simpa only [hp3] using hcard5
        have hA'_toral : IsToralSubgroup (langTag .E6) GGL A' :=
          RCKBand.rckSZ_bigElem h5 h6
            (by simpa only [hp3, langTag] using ExcFramesHalf.bigElemAbelianToralBar_E6_three)
            hA'_adj hA'_el hcard5'
        obtain ⟨g, hg, hgt⟩ := hA'_toral
        exact ⟨g, hg, fun y hy => hgt y (hEA' hy)⟩
    · exact absurd hE6 (by simp [langTag])
    · exact absurd hE6 (by simp [langTag])

end CFSG.StandardType.LieKnownR2.ExcPos
