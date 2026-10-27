module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniR
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniTor
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Main

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces

private theorem l02qu8_ggInducedAut_mem {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {I : Set (MulAut R)}
    (hact : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ)
    (b : ↥Bs) : ggInducedAut θ (ggGamma L hN b) ∈ I := by
  obtain ⟨φ, hφI, hφ⟩ := hact ((b : G)⁻¹) (Bs.inv_mem b.2)
  have hφ' : LargeEvenInduces θ (fun l l' : ↥L => l' = ggGamma L hN b l) φ := by
    intro l l' hl
    have h2 : (l' : G) = (((b : G)⁻¹))⁻¹ * (l : G) * ((b : G)⁻¹) := by
      rw [hl, ggGamma_coe]
      group
    exact hφ l l' h2
  have hEq : ggInducedAut θ (ggGamma L hN b) = φ := by
    ext r
    obtain ⟨z, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [ggInducedAut_apply]
    exact (hφ' l (ggGamma L hN b l) rfl).symm
  rw [hEq]
  exact hφI

private theorem l02qu8_ggInducedInn_range {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {I : Set (MulAut R)}
    (hact : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ) :
    GGInducedInn (ggGamma L hN).range θ I := by
  intro a ha
  obtain ⟨b, rfl⟩ := ha
  exact l02qu8_ggInducedAut_mem hN θ hact b

private theorem l02qu8_isElemAbelian_range {G : Type} [Group G] {Bs : Subgroup G}
    {p : ℕ} (hE : IsElemAbelian p Bs) {L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    IsElemAbelian p (ggGamma L hN).range := by
  haveI : IsMulCommutative ↥Bs := hE.1
  exact isElemAbelian_range
    (fun a b : ↥Bs => mul_comm' a b)
    (fun a : ↥Bs => Subtype.ext (by simpa using hE.2 a a.2))
    (ggGamma L hN)


theorem q1TorPGU6_config :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
      GGConfig p B Bs x L D J →
      GGMarkingAll (K := ↥L) (fun lab R _ I _ θ =>
        PGU6 p lab → ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
          (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
          ToralUni R ((ggGamma L hN).range.map (ggInducedAut θ))) := by
  intro G _ _ p B Bs x L D J hcfg
  unfold GGMarkingAll
  intro P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  by_cases hPG : PGU6 p lab
  · obtain ⟨htag, hrank, hp, hdvd⟩ := hPG
    subst hp
    unfold LargeEvenRawDatumLegacy at hraw
    rw [htag] at hraw
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hraw
    obtain ⟨hsimple, hnonab, θ, hPθ⟩ := hQ
    refine ⟨hperf, lab, hlab, ?_⟩
    unfold LargeEvenRawDatumLegacy
    rw [htag]
    refine ⟨K, hfield, hfinite, hK, hsimple, hnonab, θ, hPθ, ?_⟩
    intro _ hN hact
    have hGU : GGUnitDvd63Label 3 lab := by
      refine ⟨?_, hrank, rfl⟩
      unfold GGUnitDvdLabel
      rw [htag, hrank]
      exact ⟨rfl, by norm_num, hdvd, by norm_num⟩
    have hsplit : LargeEvenSplit 3 lab := by
      unfold LargeEvenSplit
      rw [htag]
      exact Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by simp, hdvd⟩)
    have hM : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs L := by
      refine ⟨hperf, lab, hlab, ?_⟩
      unfold LargeEvenRawDatumLegacy
      rw [htag]
      refine ⟨K, hfield, hfinite, hK, hsimple, hnonab, θ, ?_⟩
      exact ⟨hGU, hsplit, hN, hact⟩
    have hcard4 : 3 ^ 4 ≤ Nat.card (ggGamma L hN).range :=
      (card_range_ggGamma_unitDvd63 hcfg hM hN).1
    have hInn := l02qu8_ggInducedInn_range hN θ hact
    have hE : IsElemAbelian 3 ((ggGamma L hN).range.map (ggInducedAut θ)) :=
      (l02qu8_isElemAbelian_range hcfg.2.1.2.1 hN).map (ggInducedAut θ)
    have hcardE : 3 ^ 4 ≤ Nat.card ((ggGamma L hN).range.map (ggInducedAut θ)) := by
      rw [Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hperf θ)]
      exact hcard4
    have hexp : (lab.rank + 1) / 3 + 2 = 4 := by rw [hrank]
    have hcard : 3 ^ ((lab.rank + 1) / 3 + 2) ≤
        Nat.card ((ggGamma L hN).range.map (ggInducedAut θ)) := by
      rw [hexp]
      exact hcardE
    have hdq : ¬(lab.rank + 1 = 3 ∧ 2 ^ lab.n = 2) := by rw [hrank]; norm_num
    exact toralUni_of_card (d := lab.rank + 1) (m := lab.n) (p := 3)
      (by rw [hrank]; norm_num) hlab.1 hdq hK (by norm_num) hdvd hE
      (fun a ha => by
        obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
        exact hInn a₀ ha₀)
      hcard
  · refine ⟨hperf, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw
    obtain ⟨hs, hna, θ, hPθ⟩ := hh
    exact ⟨hs, hna, θ, hPθ, fun h => absurd h hPG⟩

theorem q1PGU6_holds : Q1PGU6 :=
  q1On_of_selectedTransfer
    (q1SelectedTransfer_of_toral
      (q1ToralActionTransfer_of_rToral
        (q1RToralTransfer_mono (fun _ _ h => uniOdd_of_pgu6 h) q1RToral_uni))
      q1TorPGU6_config)

end CFSG.StandardType
