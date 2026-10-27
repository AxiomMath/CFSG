module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KSpor
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec21.Hering214Lin2

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open CFSG.ComponentClassification.PerfectAutomorphisms

@[expose] def EInvNine (Y : Type) [Group Y] : Prop :=
  ∀ Ē : Subgroup (MulAut Y), IsElemAbelian 3 Ē → Nat.card Ē = 9 → EInvFour Y Ē

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem EInvNine.of_mulEquiv (e : X ≃* Y) (h : EInvNine Y) : EInvNine X := by
  intro Ē hE3 hE9
  set φ : MulAut X →* MulAut Y := (MulAut.congr e).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  obtain ⟨W, hW, hW4, hinv, σ', hσ', w, hw, hne⟩ :=
    h (Ē.map φ) (CFSG.Open.IsElemAbelian.map hE3 φ)
      (by rw [Subgroup.card_map_of_injective hφinj, hE9])
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

theorem eInvNine_of_sylow (hZ : Subgroup.center Y = ⊥)
    (hout : ∀ α : MulAut Y, α ^ 3 = 1 → ∃ y : Y, α = MulAut.conj y)
    (hsyl : ∀ P : Sylow 3 Y, Nat.card P = 9)
    {E₀ : Subgroup Y} (hE₀ : 9 ≤ Nat.card E₀) (hE₀exp : ∀ x ∈ E₀, x ^ 3 = 1)
    {W₀ : Subgroup Y} (hW₀ab : IsElemAbelian 2 W₀) (hW₀4 : Nat.card W₀ = 4)
    (hinv : ∀ e ∈ E₀, ∀ w ∈ W₀, e * w * e⁻¹ ∈ W₀)
    (hmove : ∃ e ∈ E₀, ∃ w ∈ W₀, e * w * e⁻¹ ≠ w) : EInvNine Y := by
  intro Ē hE3 hE9
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconjinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    Item211LieProof.conj_injective_of_center_eq_bot hZ
  have hEcube : ∀ α ∈ Ē, α ^ 3 = 1 := fun α hα => hE3.2 α hα
  have hrange : Ē ≤ (MulAut.conj : Y →* MulAut Y).range := by
    intro α hα
    obtain ⟨y, hy⟩ := hout α (hEcube α hα)
    exact ⟨y, hy.symm⟩
  set Et : Subgroup Y := Ē.comap (MulAut.conj : Y →* MulAut Y) with hEt
  have hEtcard : Nat.card Et = 9 := by
    rw [hEt, Item211LieProof.card_comap_conj hZ hrange, hE9]
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

theorem eInvNine_of_explicit_hout (hZ : Subgroup.center Y = ⊥)
    (hout : ∀ α : MulAut Y, α ^ 3 = 1 → ∃ y : Y, α = MulAut.conj y)
    (hsyl : ∀ P : Sylow 3 Y, Nat.card P = 9)
    {a b u₁ u₂ : Y} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hdist : ∀ i j k l : Fin 3, a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) →
      i = k ∧ j = l)
    (hu₁ : u₁ * u₁ = 1) (hu₂ : u₂ * u₂ = 1) (hu : u₁ * u₂ = u₂ * u₁) (hu₁1 : u₁ ≠ 1)
    (hu₂1 : u₂ ≠ 1) (hu₁₂ : u₁ ≠ u₂) {va₁ va₂ vb₁ vb₂ : Y}
    (hva₁ : Four4 u₁ u₂ va₁) (hva₂ : Four4 u₁ u₂ va₂) (hvb₁ : Four4 u₁ u₂ vb₁)
    (hvb₂ : Four4 u₁ u₂ vb₂) (ha₁ : a * u₁ = va₁ * a) (ha₂ : a * u₂ = va₂ * a)
    (hb₁ : b * u₁ = vb₁ * b) (hb₂ : b * u₂ = vb₂ * b) (hmove : a * u₁ ≠ u₁ * a) :
    EInvNine Y := by
  have hconj : ∀ (g t v : Y), g * t = v * g → g * t * g⁻¹ = v := fun g t v h => by
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have haw : Four4 u₁ u₂ (a * u₁ * a⁻¹) ∧ Four4 u₁ u₂ (a * u₂ * a⁻¹) := by
    rw [hconj a u₁ va₁ ha₁, hconj a u₂ va₂ ha₂]
    exact ⟨hva₁, hva₂⟩
  have hbw : Four4 u₁ u₂ (b * u₁ * b⁻¹) ∧ Four4 u₁ u₂ (b * u₂ * b⁻¹) := by
    rw [hconj b u₁ vb₁ hb₁, hconj b u₂ vb₂ hb₂]
    exact ⟨hvb₁, hvb₂⟩
  have hmove' : a * u₁ * a⁻¹ ≠ u₁ := fun h => hmove (mul_inv_eq_iff_eq_mul.mp h)
  have hab' : a * b = b * a := hab
  set E₀ : Subgroup Y := Subgroup.closure ({a, b} : Set Y) with hE₀
  set W₀ : Subgroup Y := Subgroup.closure ({u₁, u₂} : Set Y) with hW₀
  have hE₀exp : ∀ x ∈ E₀, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := exists_pow_mul_pow_of_mem_closure ha3 hb3 hab hx
    rw [Commute.mul_pow (Commute.pow_pow hab' i j), ← pow_mul, ← pow_mul, mul_comm i 3,
      mul_comm j 3, pow_mul, pow_mul, ha3, hb3, one_pow, one_pow, one_mul]
  have hE₀card : 9 ≤ Nat.card E₀ := by
    let f : Fin 3 × Fin 3 → E₀ := fun p => ⟨a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ),
      Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _
          (Set.mem_singleton _))) _)⟩
    have hf : Function.Injective f := by
      rintro ⟨i, j⟩ ⟨k, l⟩ h
      have h2 : a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) := congrArg Subtype.val h
      obtain ⟨rfl, rfl⟩ := hdist i j k l h2
      rfl
    have := Nat.card_le_card_of_injective f hf
    simpa [Nat.card_prod] using this
  have hmemW : ∀ t : Y, Four4 u₁ u₂ t → t ∈ W₀ := by
    intro t ht
    rcases ht with h | h | h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hmapW : ∀ g : Y, Four4 u₁ u₂ (g * u₁ * g⁻¹) → Four4 u₁ u₂ (g * u₂ * g⁻¹) →
      ∀ w ∈ W₀, g * w * g⁻¹ ∈ W₀ := by
    intro g h1 h2 w hw
    have hle : W₀.map (MulAut.conj g).toMonoidHom ≤ W₀ := by
      rw [hW₀, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with hx | hx
      · rw [hx]
        have := hmemW _ h1
        simpa [MulAut.conj_apply] using this
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        have := hmemW _ h2
        simpa [MulAut.conj_apply] using this
    exact hle ⟨w, hw, rfl⟩
  have hinv : ∀ e ∈ E₀, ∀ w ∈ W₀, e * w * e⁻¹ ∈ W₀ := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · rw [hx]
        exact hmapW a haw.1 haw.2
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hmapW b hbw.1 hbw.2
    | one => intro w hw; simpa using hw
    | mul x y _ _ hx hy =>
      intro w hw
      have := hx _ (hy w hw)
      simpa [mul_assoc] using this
    | inv x _ hx =>
      intro w hw
      let f : W₀ → W₀ := fun v => ⟨x * v * x⁻¹, hx v v.2⟩
      have hfinj : Function.Injective f := by
        intro v v' h
        have h' : x * (v : Y) * x⁻¹ = x * (v' : Y) * x⁻¹ := congrArg Subtype.val h
        exact Subtype.ext (by simpa using h')
      obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hfinj) ⟨w, hw⟩
      have hv' : x * v * x⁻¹ = w := congrArg Subtype.val hv
      have : x⁻¹ * w * (x⁻¹)⁻¹ = v := by
        rw [← hv']; group
      rw [this]
      exact v.2
  have hW₀ab : IsElemAbelian 2 W₀ := isElemAbelian_closure_pair hu₁ hu₂ hu
  have hW₀4 : Nat.card W₀ = 4 := card_closure_pair hu₁ hu₂ hu hu₁1 hu₂1 hu₁₂
  exact eInvNine_of_sylow hZ hout hsyl hE₀card hE₀exp hW₀ab hW₀4 hinv
    ⟨a, Subgroup.subset_closure (Set.mem_insert _ _), u₁,
      Subgroup.subset_closure (Set.mem_insert _ _), hmove'⟩

theorem eInvNine_of_card_bound {N : ℕ} (hZ : Subgroup.center Y = ⊥)
    (hcard : Nat.card (MulAut Y) ≤ 2 * Nat.card Y) (hY : Nat.card Y = N)
    (hN : padicValNat 3 N = 2)
    {a b u₁ u₂ : Y} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hdist : ∀ i j k l : Fin 3, a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) →
      i = k ∧ j = l)
    (hu₁ : u₁ * u₁ = 1) (hu₂ : u₂ * u₂ = 1) (hu : u₁ * u₂ = u₂ * u₁) (hu₁1 : u₁ ≠ 1)
    (hu₂1 : u₂ ≠ 1) (hu₁₂ : u₁ ≠ u₂) {va₁ va₂ vb₁ vb₂ : Y}
    (hva₁ : Four4 u₁ u₂ va₁) (hva₂ : Four4 u₁ u₂ va₂) (hvb₁ : Four4 u₁ u₂ vb₁)
    (hvb₂ : Four4 u₁ u₂ vb₂) (ha₁ : a * u₁ = va₁ * a) (ha₂ : a * u₂ = va₂ * a)
    (hb₁ : b * u₁ = vb₁ * b) (hb₂ : b * u₂ = vb₂ * b) (hmove : a * u₁ ≠ u₁ * a) :
    EInvNine Y :=
  eInvNine_of_explicit_hout hZ (fun α hα => exists_conj_of_pow_three_of_card_le hZ hcard hα)
    (card_sylow_three_of_padicValNat hY hN) ha3 hb3 hab hdist hu₁ hu₂ hu hu₁1 hu₂1 hu₁₂ hva₁
    hva₂ hvb₁ hvb₂ ha₁ ha₂ hb₁ hb₂ hmove

end Sylow

end CFSG.RankThree.PartTwo.Sec21.Hering214
