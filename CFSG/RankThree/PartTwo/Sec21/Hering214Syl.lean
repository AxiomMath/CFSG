module

public import CFSG.RankThree.PartTwo.Sec21.Hering214Reduce
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)

@[expose] def EInvFourFact (X : Type) [Group X] : Prop :=
  ∀ Ē Ū : Subgroup (MulAut X), BarData X Ē Ū → EInvFour X Ē

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem EInvFourFact.of_mulEquiv (e : X ≃* Y) (h : EInvFourFact Y) : EInvFourFact X := by
  intro Ē Ū hd
  set φ : MulAut X →* MulAut Y := (MulAut.congr e).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  have hdata : BarData Y (Ē.map φ) (Ū.map φ) := by
    refine ⟨CFSG.Open.IsElemAbelian.map hd.elem3 φ, ?_, CFSG.Open.IsElemAbelian.map hd.elem2 φ,
      ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective hφinj, hd.card9]
    · intro h
      exact hd.ne_bot ((Subgroup.map_eq_bot_iff_of_injective Ū hφinj).mp h)
    · rw [Subgroup.card_map_of_injective hφinj]
      exact hd.card_le
    · intro σ' hσ'
      obtain ⟨σ, hσ, rfl⟩ := hσ'
      rw [Subgroup.mem_normalizer_iff]
      intro τ'
      constructor
      · rintro ⟨τ, hτ, rfl⟩
        refine ⟨σ * τ * σ⁻¹, (Subgroup.mem_normalizer_iff.mp (hd.norm hσ) τ).mp hτ, ?_⟩
        simp
      · rintro ⟨τ, hτ, hτ'⟩
        refine ⟨σ⁻¹ * τ * σ, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (hd.norm (Ē.inv_mem hσ)) τ).mp hτ
          simpa using this
        · have h1 : φ σ * τ' * (φ σ)⁻¹ = φ τ := hτ'.symm
          calc φ (σ⁻¹ * τ * σ) = (φ σ)⁻¹ * φ τ * φ σ := by simp [map_mul, map_inv]
            _ = (φ σ)⁻¹ * (φ σ * τ' * (φ σ)⁻¹) * φ σ := by rw [h1]
            _ = τ' := by group
  obtain ⟨W, hW, hW4, hinv, σ', hσ', w, hw, hne⟩ := h _ _ hdata
  refine ⟨W.map e.symm.toMonoidHom, CFSG.Open.IsElemAbelian.map hW _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hW4]
  · intro σ hσ x hx
    obtain ⟨w', hw', rfl⟩ := hx
    refine ⟨φ σ w', hinv _ ⟨σ, hσ, rfl⟩ _ hw', ?_⟩
    simp [hφ, MulAut.congr_apply]
  · obtain ⟨σ, hσ, rfl⟩ := hσ'
    refine ⟨σ, hσ, e.symm w, ⟨w, hw, rfl⟩, fun h => hne ?_⟩
    have h1 := congrArg e h
    simpa [hφ, MulAut.congr_apply] using h1

end Transport

section Sylow

open Pointwise

variable {Y : Type} [Group Y] [Finite Y]

theorem eInvFourFact_of_sylow (hZ : Subgroup.center Y = ⊥)
    (hout : ∀ α : MulAut Y, α ^ 3 = 1 → ∃ y : Y, α = MulAut.conj y)
    (hsyl : ∀ P : Sylow 3 Y, Nat.card P = 9)
    {E₀ : Subgroup Y} (hE₀ : 9 ≤ Nat.card E₀) (hE₀exp : ∀ x ∈ E₀, x ^ 3 = 1)
    {W₀ : Subgroup Y} (hW₀ab : IsElemAbelian 2 W₀) (hW₀4 : Nat.card W₀ = 4)
    (hinv : ∀ e ∈ E₀, ∀ w ∈ W₀, e * w * e⁻¹ ∈ W₀)
    (hmove : ∃ e ∈ E₀, ∃ w ∈ W₀, e * w * e⁻¹ ≠ w) : EInvFourFact Y := by
  intro Ē Ū hd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconjinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    Item211LieProof.conj_injective_of_center_eq_bot hZ
  have hEcube : ∀ α ∈ Ē, α ^ 3 = 1 := fun α hα => hd.elem3.2 α hα
  have hrange : Ē ≤ (MulAut.conj : Y →* MulAut Y).range := by
    intro α hα
    obtain ⟨y, hy⟩ := hout α (hEcube α hα)
    exact ⟨y, hy.symm⟩
  set Et : Subgroup Y := Ē.comap (MulAut.conj : Y →* MulAut Y) with hEt
  have hEtcard : Nat.card Et = 9 := by
    rw [hEt, Item211LieProof.card_comap_conj hZ hrange, hd.card9]
  have hEtexp : ∀ x ∈ Et, x ^ 3 = 1 := by
    intro x hx
    apply hconjinj
    rw [map_pow, map_one]
    exact hEcube _ hx
  have hEtp : IsPGroup 3 Et := fun g => ⟨1, Subtype.ext (by simpa using hEtexp g.1 g.2)⟩
  have hE₀p : IsPGroup 3 E₀ := fun g => ⟨1, Subtype.ext (by simpa using hE₀exp g.1 g.2)⟩
  obtain ⟨P₁, hP₁⟩ := hEtp.exists_le_sylow
  obtain ⟨P₀, hP₀⟩ := hE₀p.exists_le_sylow
  have hEteq : Et = P₁ := Subgroup.eq_of_le_of_card_ge hP₁ (by rw [hsyl P₁, hEtcard])
  have hE₀eq : E₀ = P₀ := Subgroup.eq_of_le_of_card_ge hP₀ (by rw [hsyl P₀]; exact hE₀)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P₀ P₁
  have hmem : ∀ x : Y, x ∈ Et ↔ ∃ e ∈ E₀, x = g * e * g⁻¹ := by
    intro x
    have h1 : (P₁ : Subgroup Y) = MulAut.conj g • (P₀ : Subgroup Y) := by
      rw [← hg]; rfl
    rw [hEteq, h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← hE₀eq]
    constructor
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      simpa [MulAut.smul_def, MulAut.conj_apply] using hx
    · rintro ⟨e, he, rfl⟩
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using he
  set W : Subgroup Y := W₀.map (MulAut.conj g).toMonoidHom with hW
  have hmemW : ∀ x, x ∈ W ↔ ∃ w ∈ W₀, g * w * g⁻¹ = x := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
  refine ⟨W, CFSG.Open.IsElemAbelian.map hW₀ab _, ?_, ?_, ?_⟩
  · rw [hW, Subgroup.card_map_of_injective (show Function.Injective (MulAut.conj g).toMonoidHom from
      (MulAut.conj g).injective), hW₀4]
  · intro α hα x hx
    obtain ⟨w, hw, rfl⟩ := (hmemW x).mp hx
    obtain ⟨y, rfl⟩ := hout α (hEcube α hα)
    obtain ⟨e, he, rfl⟩ := (hmem y).mp (show y ∈ Et from hα)
    refine (hmemW _).mpr ⟨e * w * e⁻¹, hinv e he w hw, ?_⟩
    simp only [MulAut.conj_apply]
    group
  · obtain ⟨e, he, w, hw, hne⟩ := hmove
    have hge : g * e * g⁻¹ ∈ Et := (hmem _).mpr ⟨e, he, rfl⟩
    refine ⟨MulAut.conj (g * e * g⁻¹), hge, g * w * g⁻¹, (hmemW _).mpr ⟨w, hw, rfl⟩,
      fun h => hne ?_⟩
    simp only [MulAut.conj_apply] at h
    have h2 : g * (e * w * e⁻¹) * g⁻¹ = g * w * g⁻¹ := by
      rw [← h]; group
    exact mul_left_cancel (mul_right_cancel h2)

end Sylow

end CFSG.RankThree.PartTwo.Sec21.Hering214
