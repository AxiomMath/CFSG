module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTSplitLaw
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6SylowUnitary
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTRank
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6FrameDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


private lemma lk0xttplace_exists_subgroup_card_pow_prime
    {X : Type} [Group X] [Finite X] {A D : Subgroup X} {p k : ℕ}
    (hp : p.Prime) (hAel : IsElemAbelian p A) (hDleA : D ≤ A)
    (hDcard : Nat.card D = p ^ 2) (hk2 : 2 ≤ k) (hk : p ^ k ≤ Nat.card A) :
    ∃ Y : Subgroup X, D ≤ Y ∧ Y ≤ A ∧ Nat.card Y = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hApg : IsPGroup p ↥A := IsElemAbelian.isPGroup hAel
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hApg
  have hkm : k ≤ m := by
    rw [hm] at hk
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hk
  have hdvd : Nat.card D ∣ p ^ k := by
    rw [hDcard]
    exact Nat.pow_dvd_pow p hk2
  have hdvdA : p ^ k ∣ Nat.card A := by
    rw [hm]
    exact Nat.pow_dvd_pow p hkm
  obtain ⟨Y, hYcard, hDY, hYA⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hp (n := k) (H := D) (L := A)
      hdvd hdvdA hDleA
  exact ⟨Y, hDY, hYA, hYcard⟩

private lemma lk0xttplace_map_subgroupOf_eq {X : Type} [Group X] {A B : Subgroup X} (hBA : B ≤ A) :
    (B.subgroupOf A).map A.subtype = B := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hBA hx⟩, hx, rfl⟩

theorem twE6_placement (hC : TwE6TTFive) (hD : TwE6TTThreeSplit) (hE : TwE6TTThreeUnitary)
    (hR5 : TwE6RankFive) {X : Type} [Group X] [Finite X] {n f p : ℕ} (hf : 1 ≤ f)
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (hP : GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x)
    (hres : ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1 ∧ ¬ 9 ∣ 2 ^ f + 1)) {A : Subgroup X}
    (hA : TwE6BigGroup n f p ψ G₀ B₁ A) (Θ : ↥A →* ModGL (langTag .twistedE6) GGL)
    (hΘR : ∀ a : ↥A, Θ a ∈ ggFixGp .twistedE6 f) (hΘinj : Function.Injective Θ) :
    (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) ∧ ∃ E : Subgroup (ModGL (langTag .twistedE6) GGL),
      (∀ a : ↥A, (a : X) ∈ D → Θ a ∈ E) ∧ TwE6LawPos p f E := by
  classical
  have hPkeep := hP
  obtain ⟨-, -, -, -, hp, hp2, -, -, hB1el, hB1card, hDB1, hDcard, -⟩ := hP
  have hB1leA : B₁ ≤ A := hA.1
  have hAel : IsElemAbelian p A := hA.2.1
  have hDleA : D ≤ A := hDB1.trans hB1leA
  let E_B1 : Subgroup (ModGL (langTag .twistedE6) GGL) := (B₁.subgroupOf A).map Θ
  have hE_B1_le : E_B1 ≤ ggFixGp .twistedE6 f := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    exact hΘR b
  have hB1subEl : IsElemAbelian p (B₁.subgroupOf A) := IsElemAbelian.subgroupOf hB1el A
  have hE_B1_el : IsElemAbelian p E_B1 := IsElemAbelian.map hB1subEl Θ
  have hB1subCard : Nat.card (B₁.subgroupOf A) = Nat.card B₁ := by
    have h := Subgroup.card_map_of_injective (K := B₁.subgroupOf A) A.subtype_injective
    rw [lk0xttplace_map_subgroupOf_eq hB1leA] at h
    exact h.symm
  have hE_B1_card : Nat.card E_B1 = Nat.card B₁ := by
    rw [Subgroup.card_map_of_injective (K := B₁.subgroupOf A) hΘinj, hB1subCard]
  have hE_B1_contains : ∀ a : ↥A, (a : X) ∈ D → Θ a ∈ E_B1 := by
    intro a ha
    exact Subgroup.mem_map.mpr ⟨a, (Subgroup.mem_subgroupOf).mpr (hDB1 ha), rfl⟩
  by_cases hp3 : p = 3
  · subst p
    have hmod : 3 ∣ 2 ^ f - 1 ∨ 3 ∣ 2 ^ f + 1 := by
      have hmod1 : 2 ^ f % 3 = 1 ∨ 2 ^ f % 3 = 2 := by
        have hlt : 2 ^ f % 3 < 3 := Nat.mod_lt _ (by norm_num)
        have hne : 2 ^ f % 3 ≠ 0 := by
          intro h0
          have hdvd : 3 ∣ 2 ^ f := Nat.dvd_iff_mod_eq_zero.mpr h0
          have h2dvd : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hdvd
          norm_num at h2dvd
        omega
      rcases hmod1 with h1 | h2
      · left
        rw [Nat.dvd_iff_mod_eq_zero]
        have h := Nat.mod_add_div (2 ^ f) 3
        rw [h1] at h
        have hsub : 2 ^ f - 1 = 3 * (2 ^ f / 3) := by omega
        rw [hsub]
        exact Nat.mod_eq_zero_of_dvd (dvd_mul_right 3 (2 ^ f / 3))
      · right
        rw [Nat.dvd_iff_mod_eq_zero]
        have h := Nat.mod_add_div (2 ^ f) 3
        rw [h2] at h
        have hadd : 2 ^ f + 1 = 3 * (2 ^ f / 3 + 1) := by omega
        rw [hadd]
        exact Nat.mod_eq_zero_of_dvd (dvd_mul_right 3 (2 ^ f / 3 + 1))
    refine ⟨hmod, ?_⟩
    rcases hmod with h3m1 | h3p1
    · obtain ⟨Y, hDY, hYB1, hYcard⟩ :=
        lk0xttplace_exists_subgroup_card_pow_prime (p := 3) (k := 4) (A := B₁) (D := D)
          (by norm_num) hB1el hDB1 hDcard (by norm_num) hB1card
      let E : Subgroup (ModGL (langTag .twistedE6) GGL) := (Y.subgroupOf A).map Θ
      have hYleA : Y ≤ A := hYB1.trans hB1leA
      have hYel : IsElemAbelian 3 Y := IsElemAbelian.mono hAel hYleA
      have hYsubEl : IsElemAbelian 3 (Y.subgroupOf A) := IsElemAbelian.subgroupOf hYel A
      have hE_el : IsElemAbelian 3 E := IsElemAbelian.map hYsubEl Θ
      have hE_le : E ≤ ggFixGp .twistedE6 f := by
        intro y hy
        obtain ⟨y', hy', rfl⟩ := hy
        exact hΘR y'
      have hYsubCard : Nat.card (Y.subgroupOf A) = Nat.card Y := by
        have h := Subgroup.card_map_of_injective (K := Y.subgroupOf A) A.subtype_injective
        rw [lk0xttplace_map_subgroupOf_eq hYleA] at h
        exact h.symm
      have hE_card : Nat.card E = 3 ^ 4 := by
        rw [Subgroup.card_map_of_injective (K := Y.subgroupOf A) hΘinj, hYsubCard, hYcard]
      have hcontains : ∀ a : ↥A, (a : X) ∈ D → Θ a ∈ E := by
        intro a ha
        exact Subgroup.mem_map.mpr ⟨a, (Subgroup.mem_subgroupOf).mpr (hDY ha), rfl⟩
      exact ⟨E, hcontains, hD f hf h3m1 E hE_le hE_el hE_card⟩
    · have h9 : 9 ∣ 2 ^ f + 1 := by
        by_contra h
        exact hres ⟨rfl, h3p1, h⟩
      have h35 : 3 ^ 5 ≤ Nat.card A := hR5 X n f ψ G₀ B₁ D J L x hPkeep h9 A hA
      obtain ⟨Y, hDY, hYA, hYcard⟩ :=
        lk0xttplace_exists_subgroup_card_pow_prime (p := 3) (k := 5) (A := A) (D := D)
          (by norm_num) hAel hDleA hDcard (by norm_num) h35
      let E : Subgroup (ModGL (langTag .twistedE6) GGL) := (Y.subgroupOf A).map Θ
      have hYel : IsElemAbelian 3 Y := IsElemAbelian.mono hAel hYA
      have hYsubEl : IsElemAbelian 3 (Y.subgroupOf A) := IsElemAbelian.subgroupOf hYel A
      have hE_el : IsElemAbelian 3 E := IsElemAbelian.map hYsubEl Θ
      have hE_le : E ≤ ggFixGp .twistedE6 f := by
        intro y hy
        obtain ⟨y', hy', rfl⟩ := hy
        exact hΘR y'
      have hYsubCard : Nat.card (Y.subgroupOf A) = Nat.card Y := by
        have h := Subgroup.card_map_of_injective (K := Y.subgroupOf A) A.subtype_injective
        rw [lk0xttplace_map_subgroupOf_eq hYA] at h
        exact h.symm
      have hE_card : Nat.card E = 3 ^ 5 := by
        rw [Subgroup.card_map_of_injective (K := Y.subgroupOf A) hΘinj, hYsubCard, hYcard]
      have hcontains : ∀ a : ↥A, (a : X) ∈ D → Θ a ∈ E := by
        intro a ha
        exact Subgroup.mem_map.mpr ⟨a, (Subgroup.mem_subgroupOf).mpr (hDY ha), rfl⟩
      exact ⟨E, hcontains, hE f hf h9 E hE_le hE_el hE_card⟩
  · have hp5 : 5 ≤ p := by
      have hp2' : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
      have hp3' : 3 < p := by
        have h3 : 3 ≤ p := by omega
        exact lt_of_le_of_ne h3 (Ne.symm hp3)
      have hp4' : p ≠ 4 := by rintro rfl; norm_num at hp
      omega
    by_cases h1 : p ∣ 2 ^ f - 1
    · have hEp : IsPGroup p ↥E_B1 := IsElemAbelian.isPGroup hE_B1_el
      have hLaw : TwE6LawPos p f E_B1 :=
        twE6TTSplit_holds f hf p hp hp5 h1 E_B1 hE_B1_le hEp
      exact ⟨Or.inl h1, ⟨E_B1, hE_B1_contains, hLaw⟩⟩
    · by_cases h2 : p ∣ 2 ^ f + 1
      · by_cases hp5eq : p = 5
        · subst p
          obtain ⟨Y, hDY, hYB1, hYcard⟩ :=
            lk0xttplace_exists_subgroup_card_pow_prime (p := 5) (k := 4) (A := B₁) (D := D)
              (by norm_num) hB1el hDB1 hDcard (by norm_num) hB1card
          let E : Subgroup (ModGL (langTag .twistedE6) GGL) := (Y.subgroupOf A).map Θ
          have hYleA : Y ≤ A := hYB1.trans hB1leA
          have hYel : IsElemAbelian 5 Y := IsElemAbelian.mono hAel hYleA
          have hYsubEl : IsElemAbelian 5 (Y.subgroupOf A) := IsElemAbelian.subgroupOf hYel A
          have hE_el : IsElemAbelian 5 E := IsElemAbelian.map hYsubEl Θ
          have hE_le : E ≤ ggFixGp .twistedE6 f := by
            intro y hy
            obtain ⟨y', hy', rfl⟩ := hy
            exact hΘR y'
          have hYsubCard : Nat.card (Y.subgroupOf A) = Nat.card Y := by
            have h := Subgroup.card_map_of_injective (K := Y.subgroupOf A) A.subtype_injective
            rw [lk0xttplace_map_subgroupOf_eq hYleA] at h
            exact h.symm
          have hE_card : Nat.card E = 5 ^ 4 := by
            rw [Subgroup.card_map_of_injective (K := Y.subgroupOf A) hΘinj, hYsubCard, hYcard]
          have hcontains : ∀ a : ↥A, (a : X) ∈ D → Θ a ∈ E := by
            intro a ha
            exact Subgroup.mem_map.mpr ⟨a, (Subgroup.mem_subgroupOf).mpr (hDY ha), rfl⟩
          exact ⟨Or.inr h2, ⟨E, hcontains, hC f hf h2 E hE_le hE_el hE_card⟩⟩
        · have h7 : 7 ≤ p := by
            have hp5' : 5 < p := lt_of_le_of_ne hp5 (Ne.symm hp5eq)
            have hp6 : p ≠ 6 := by rintro rfl; norm_num at hp
            omega
          have hEp : IsPGroup p ↥E_B1 := IsElemAbelian.isPGroup hE_B1_el
          have hLaw : TwE6LawPos p f E_B1 :=
            twE6_tt_unitary f hf p hp h7 h2 E_B1 hE_B1_le hEp
          exact ⟨Or.inr h2, ⟨E_B1, hE_B1_contains, hLaw⟩⟩
      · exfalso
        have hlt : Nat.card E_B1 < p ^ 4 :=
          twE6TTRank_holds f hf p hp hp5 h1 h2 E_B1 hE_B1_le hE_B1_el
        have hge : p ^ 4 ≤ Nat.card E_B1 := by
          rw [hE_B1_card]
          exact hB1card
        omega

end CFSG.StandardType.LieKnownR2.ExcPos
