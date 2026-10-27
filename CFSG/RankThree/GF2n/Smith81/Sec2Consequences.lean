module

public import CFSG.RankThree.GF2n.Smith81.Sec1Main
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs
public import CFSG.RankThree.GF2n.Smith81.TiFusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Five

variable [Finite G]

theorem smith25_of_117 (h117 : Smith117Statement) {M Q Z B : Subgroup G} (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 3 ≤ n)
    (hno : ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B'))
    (h15c : ∀ B' : Subgroup G, Ctx M Q Z B' →
      CQt Q Z (LB M Q B') = ((B' ⊔ Z : Subgroup G) : Set G)) :
    {V : Subgroup G | ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧ V = A ⊔ Z} =
      {V : Subgroup G | ∃ m ∈ M, V = conjSubgroup m B ⊔ Z} := by
  have H := hc.hyp
  have hfus := h117 G M Q Z B hc n hw hn hno h15c
  have hBc : IsZConjugate Z B := hc.conj
  have hZ1 : ∀ {A : Subgroup G}, IsZConjugate Z A → A ≠ ⊥ := by
    intro A hA h
    have := hA.card_eq
    rw [h, Subgroup.card_bot] at this
    have h4 := H.q4
    omega
  have hnot : ∀ {A : Subgroup G}, IsZConjugate Z A → A ≠ Z → ∀ a ∈ A, a ≠ 1 → a ∉ Z := by
    intro A hA hAZ a haA ha1 haZ
    obtain ⟨g, rfl⟩ := hA
    have := inf_conjSubgroup_eq_bot_of_isTI H.ti hAZ
    have hmem : a ∈ Z ⊓ conjSubgroup g Z := ⟨haZ, haA⟩
    rw [this, Subgroup.mem_bot] at hmem
    exact ha1 hmem
  have hconj : ∀ {A A' : Subgroup G}, IsZConjugate Z A → IsZConjugate Z A' →
      ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A', b ≠ 1 → ∃ g : G, g * a * g⁻¹ = b := by
    intro A A' hA hA' a haA ha1 b hbA' hb1
    obtain ⟨g₁, rfl⟩ := hA
    obtain ⟨g₂, rfl⟩ := hA'
    have ha' : g₁⁻¹ * a * g₁ ∈ Z := mem_conjSubgroup.mp haA
    have hb' : g₂⁻¹ * b * g₂ ∈ Z := mem_conjSubgroup.mp hbA'
    have ha1' : g₁⁻¹ * a * g₁ ≠ 1 := by
      intro h
      apply ha1
      have : a = g₁ * (g₁⁻¹ * a * g₁) * g₁⁻¹ := by group
      rw [this, h]; group
    have hb1' : g₂⁻¹ * b * g₂ ≠ 1 := by
      intro h
      apply hb1
      have : b = g₂ * (g₂⁻¹ * b * g₂) * g₂⁻¹ := by group
      rw [this, h]; group
    obtain ⟨m, -, hm⟩ := Z_isConj H ha' ha1' hb' hb1'
    refine ⟨g₂ * m * g₁⁻¹, ?_⟩
    calc g₂ * m * g₁⁻¹ * a * (g₂ * m * g₁⁻¹)⁻¹
        = g₂ * (m * (g₁⁻¹ * a * g₁) * m⁻¹) * g₂⁻¹ := by group
      _ = b := by rw [hm]; group
  have hQN : ∀ m ∈ M, conjSubgroup m Q = Q := fun m hm =>
    conjSubgroup_eq_self_iff.mpr (H.Q_normal.2 hm)
  have hZN : ∀ m ∈ M, conjSubgroup m Z = Z := fun m hm =>
    conjSubgroup_eq_self_iff.mpr (H.Z_normal.2 hm)
  ext V
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, hAQ, hAZ, rfl⟩
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hZ1 hA)
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hZ1 hBc)
    have haA' : (a : G) ∈ A := a.2
    have hbB' : (b : G) ∈ B := b.2
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨g, hg⟩ := hconj hA hBc a haA' ha1' b hbB' hb1'
    obtain ⟨m, hm, hmab⟩ := hfus a (hAQ haA') (hnot hA hAZ a haA' ha1') b (hc.le hbB')
      (hnot hBc hc.ne b hbB' hb1') g hg
    have hmem : (b : G) ∈ conjSubgroup m A := by
      rw [mem_conjSubgroup, ← hmab]
      simpa [mul_assoc] using haA'
    have heq : conjSubgroup m A = B := (hA.conj m).eq_of_mem H hBc hb1' hmem hbB'
    refine ⟨m⁻¹, Subgroup.inv_mem _ hm, ?_⟩
    have : A = conjSubgroup m⁻¹ B := by
      rw [← heq, ← conjSubgroup_mul]
      simp [conjSubgroup_one]
    rw [this]
  · rintro ⟨m, hm, rfl⟩
    refine ⟨conjSubgroup m B, hBc.conj m, ?_, ?_, rfl⟩
    · calc conjSubgroup m B ≤ conjSubgroup m Q := Subgroup.map_mono hc.le
        _ = Q := hQN m hm
    · intro h
      apply hc.ne
      have := congrArg (conjSubgroup m⁻¹) h
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at this
      rw [this]
      exact hZN m⁻¹ (Subgroup.inv_mem _ hm)

end Five

end CFSG.RankThree.GF2n.Smith81
