module

public import CFSG.Quasithin.EmptyFaithful.A38c10Core
public import CFSG.Quasithin.EmptyFaithful.A38c10Psi
public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.EmptyFaithful.A38c10Fix
public import CFSG.Quasithin.EmptyFaithful.A38c10Mat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open Matrix CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section VMain

variable {V : Type} [CommGroup V]

structure Frame4 (Λ B W Y₁ Y₂ : Subgroup (MulAut V)) : Prop where
  sylow : IsSylowTwoOf B Λ
  BW : B ≤ W
  WL : ∀ w ∈ W, ∀ l ∈ Λ, w * l * w⁻¹ ∈ Λ
  WB : ∀ w ∈ W, ∀ b ∈ B, w * b * w⁻¹ ∈ B
  Y₁L : Y₁ ≤ Λ
  Y₁W : ∀ w ∈ W, ∀ y ∈ Y₁, w * y * w⁻¹ ∈ Y₁
  Y₁c : ∃ a, Nat.card ↥Y₁ = 2 ^ a * 3
  Y₂L : Y₂ ≤ Λ
  Y₂W : ∀ w ∈ W, ∀ y ∈ Y₂, w * y * w⁻¹ ∈ Y₂
  Y₂c : ∃ a, Nat.card ↥Y₂ = 2 ^ a * 3
  nine : 9 ∣ Nat.card ↥(Y₁ ⊔ Y₂)

theorem core4_frame [Finite V] {Λ B W Y₁ Y₂ : Subgroup (MulAut V)} (hF : Frame4 Λ B W Y₁ Y₂)
    (D : BorelIso 4 Λ B) :
    ∃ P₁ P₂ P₃ : Subgroup (MulAut V),
      (B ≤ P₁ ∧ P₁ ≤ Λ ∧ D.cutsOf P₁ = {1}) ∧ (B ≤ P₂ ∧ P₂ ≤ Λ ∧ D.cutsOf P₂ = {2}) ∧
      (B ≤ P₃ ∧ P₃ ≤ Λ ∧ D.cutsOf P₃ = {3}) ∧
      (∀ P : Subgroup (MulAut V), B ≤ P → P ≤ Λ → ∀ w ∈ W, ∀ p ∈ P, w * p * w⁻¹ ∈ P) ∧
      (∀ X : Subgroup (MulAut V), B ≤ X → X ≤ Λ → X ≠ Λ → X ≤ P₁ ∨ X ≤ P₂ ∨ X ≤ P₃) ∧
      Y₁ ⊔ Y₂ ≤ P₂ ∧ P₂ = (Y₁ ⊔ B) ⊔ (Y₂ ⊔ B) ∧
      ((Y₁ ≤ P₁ ∧ ¬ Y₁ ≤ P₃ ∧ Y₂ ≤ P₃ ∧ ¬ Y₂ ≤ P₁) ∨ (Y₁ ≤ P₃ ∧ ¬ Y₁ ≤ P₁ ∧ Y₂ ≤ P₁ ∧ ¬ Y₂ ≤ P₃)) :=
  core4 D hF.sylow hF.BW hF.WL hF.WB hF.Y₁L hF.Y₁W hF.Y₁c hF.Y₂L hF.Y₂W hF.Y₂c hF.nine card_QI_end

theorem fixed_of_cuts_empty [Finite V] {Λ B : Subgroup (MulAut V)} {n : ℕ} (D : BorelIso n Λ B) (hBL : B ≤ Λ)
    {u : V} (huB : ∀ b ∈ B, (b : MulAut V) u = u) (hc : D.cutsOf (Λ ⊓ fixSub u) = ∅) :
    ∀ l ∈ Λ, (l : MulAut V) u = u := by
  have hBX : B ≤ Λ ⊓ fixSub u := fun b hb => ⟨hBL hb, huB b hb⟩
  have heq : Λ ⊓ fixSub u = Λ :=
    D.eq_of_cutsOf_eq hBL hBX inf_le_left hBL le_rfl (by rw [hc, D.cutsOf_L])
  intro l hl
  have : l ∈ Λ ⊓ fixSub u := by rw [heq]; exact hl
  exact this.2

theorem hkey_of_cuts [Finite V] {Λ B W Y₁ Y₂ : Subgroup (MulAut V)} {U : Subgroup V}
    (hF : Frame4 Λ B W Y₁ Y₂) (D : BorelIso 4 Λ B) {C : Set ℕ} (hC : ∀ i ∈ C, i ≠ 2)
    (hcuts : ∀ u ∈ U, (∀ b ∈ B, (b : MulAut V) u = u) → D.cutsOf (Λ ⊓ fixSub u) ⊆ C)
    (hfix : fixV Λ ⊓ U = ⊥) :
    ∀ u' ∈ U, (∀ b ∈ B, (b : MulAut V) u' = u') → (∀ y ∈ Y₁ ⊔ Y₂, (y : MulAut V) u' = u') → u' = 1 := by
  intro u' hu' hB hY
  obtain ⟨P₁, P₂, P₃, -, ⟨hBP₂, hP₂L, hP₂c⟩, -, -, -, -, hP₂eq, -⟩ := core4_frame hF D
  have hBL : B ≤ Λ := hF.sylow.1
  have hBX : B ≤ Λ ⊓ fixSub u' := fun b hb => ⟨hBL hb, hB b hb⟩
  have hY₁X : Y₁ ≤ Λ ⊓ fixSub u' := fun y hy => ⟨hF.Y₁L hy, hY y (Subgroup.mem_sup_left hy)⟩
  have hY₂X : Y₂ ≤ Λ ⊓ fixSub u' := fun y hy => ⟨hF.Y₂L hy, hY y (Subgroup.mem_sup_right hy)⟩
  have hP₂X : P₂ ≤ Λ ⊓ fixSub u' := by
    rw [hP₂eq]
    exact sup_le (sup_le hY₁X hBX) (sup_le hY₂X hBX)
  have hsub : D.cutsOf (Λ ⊓ fixSub u') ⊆ D.cutsOf P₂ := (D.cutsOf_le_iff hBL hBP₂ hP₂L hBX).1 hP₂X
  have hempty : D.cutsOf (Λ ⊓ fixSub u') = ∅ := by
    ext i
    constructor
    · intro hi
      have h1 := hsub hi
      have h2 := hcuts u' hu' hB hi
      rw [hP₂c] at h1
      exact absurd (Set.mem_singleton_iff.1 h1) (hC i h2)
    · intro h
      exact absurd h (Set.notMem_empty i)
  have hall := fixed_of_cuts_empty D hBL hB hempty
  have : u' ∈ fixV Λ ⊓ U := ⟨fun l hl => hall l hl, hu'⟩
  rw [hfix] at this
  exact Subgroup.mem_bot.1 this

theorem model_eq_QI_of_cuts [Finite V] {Λ B : Subgroup (MulAut V)} {n : ℕ} (D : BorelIso n Λ B)
    (hBL : B ≤ Λ) {P : Subgroup (MulAut V)} (hBP : B ≤ P) {k : ℕ} (hPk : D.cutsOf P = {k}) :
    D.model P = QI n {k} := by
  have hUt : Ut n ≤ D.model P := (D.Ut_le_model_iff hBL).2 hBP
  have h1 : D.model P = QI n (cuts (D.model P)) := eq_QI_cuts hUt
  rw [h1]
  show QI n (D.cutsOf P) = _
  rw [hPk]

theorem exists_psi_of_cuts [Finite V] {Λ B : Subgroup (MulAut V)} (D : BorelIso 4 Λ B) (hBL : B ≤ Λ)
    {P : Subgroup (MulAut V)} (hBP : B ≤ P) (hPL : P ≤ Λ) (hPk : D.cutsOf P = {3}) :
    ∃ ψ : ↥P →* SLt 3, Function.Surjective ψ ∧ ∀ x : ↥P, ψ x = 1 → (x : MulAut V) ∈ B := by
  have hmodel : D.model P = QI 4 {3} := model_eq_QI_of_cuts D hBL hBP hPk
  obtain ⟨ψ₀, hψs, hψk⟩ := exists_psi3
  have hmem : ∀ x : ↥P, D.e ⟨(x : MulAut V), hPL x.2⟩ ∈ QI 4 {3} := fun x =>
    hmodel ▸ (D.mem_model ⟨(x : MulAut V), hPL x.2⟩).2 x.2
  let φ : ↥P →* ↥(QI 4 {3}) :=
    ((D.e.toMonoidHom).comp (Subgroup.inclusion hPL)).codRestrict (QI 4 {3}) hmem
  refine ⟨ψ₀.comp φ, ?_, ?_⟩
  · intro t
    obtain ⟨s, hs⟩ := hψs t
    have hsP : (s : SLt 4) ∈ D.model P := by rw [hmodel]; exact s.2
    obtain ⟨y, hy, hys⟩ := hsP
    refine ⟨⟨(y : MulAut V), Subgroup.mem_subgroupOf.1 hy⟩, ?_⟩
    have : φ ⟨(y : MulAut V), Subgroup.mem_subgroupOf.1 hy⟩ = s := Subtype.ext hys
    show ψ₀ (φ _) = t
    rw [this, hs]
  · intro x hx
    have h1 : ((φ x : ↥(QI 4 {3})) : SLt 4) ∈ Ut 4 := hψk (φ x) hx
    have h2 : D.e ⟨(x : MulAut V), hPL x.2⟩ ∈ D.model B := by
      rw [D.model_B]
      exact h1
    exact (D.mem_model _).1 h2

end VMain

end CFSG.Quasithin.A38c10
