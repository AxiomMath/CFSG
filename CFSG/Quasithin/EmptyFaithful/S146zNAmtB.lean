module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinDef
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.A6Amt

structure A6Facts {W : Type} [CommGroup W] {L₀ : Type} [Group L₀] (ρ : L₀ →* MulAut W)
    (σ : L₀ ≃* L₀) : Prop where
  inj : Function.Injective ρ
  a1 : ∀ n : MulAut W, (∀ l : L₀, n * ρ l = ρ l * n) → n = 1
  a2 : ∀ l : L₀, l ≠ 1 → l ^ 2 = 1 → A6Rank (ρ l) = 2
  a3 : ∀ n₁ ∈ Subgroup.normalizer (ρ.range : Set (MulAut W)),
    ∀ n₂ ∈ Subgroup.normalizer (ρ.range : Set (MulAut W)),
      n₁ ∉ ρ.range → n₂ ∉ ρ.range → n₁⁻¹ * n₂ ∈ ρ.range
  a4 : ¬ ∃ n : MulAut W, ∀ l : L₀, n * ρ l * n⁻¹ = ρ (σ l)
  a5 : ∀ n ∈ Subgroup.normalizer (ρ.range : Set (MulAut W)),
    ∀ n' ∈ Subgroup.normalizer (ρ.range : Set (MulAut W)),
      n ^ 2 = 1 → n' ^ 2 = 1 → n ∉ ρ.range → n' ∉ ρ.range →
      (∀ l l'' : L₀, n' * ρ l * n'⁻¹ = ρ l'' → n * ρ (σ l) * n⁻¹ = ρ (σ l'')) →
      3 ≤ A6Rank n + A6Rank n'
  a6 : ∀ a b : L₀, a ≠ b → a ≠ 1 → b ≠ 1 → a ^ 2 = 1 → b ^ 2 = 1 → a * b = b * a →
    ¬ (A6QuadPair (ρ a) (ρ b) ∧ A6QuadPair (ρ (σ.symm a)) (ρ (σ.symm b)))

theorem injective_of_irreducible {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hc : Nat.card W = 16) {L₀ : Type} [Group L₀] (e : L₀ ≃* alternatingGroup (Fin 6))
    (ρ : L₀ →* MulAut W)
    (hirr : ∀ S : Subgroup W, (∀ l : L₀, ∀ w ∈ S, ρ l w ∈ S) → S = ⊥ ∨ S = ⊤) :
    Function.Injective ρ := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup L₀ := e.isSimpleGroup
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h0 | h0
  · exact h0
  · exfalso
    have htriv : ∀ l, ρ l = 1 := fun l => by
      have : l ∈ ρ.ker := h0 ▸ Subgroup.mem_top l
      exact this
    have hnt : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨w, hw⟩ := exists_ne (1 : W)
    rcases hirr (Subgroup.zpowers w) (fun l w' hw' => by rw [htriv l]; exact hw') with h1 | h1
    · exact hw (Subgroup.zpowers_eq_bot.mp h1)
    · have h2 : Nat.card (Subgroup.zpowers w) = Nat.card W := by rw [h1, Subgroup.card_top]
      rw [Nat.card_zpowers] at h2
      have h3 : orderOf w ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hW w))
      omega

theorem A6Facts.of_fin (h : A6Fin) {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hc : Nat.card W = 16) {L₀ : Type} [Group L₀] (e : L₀ ≃* alternatingGroup (Fin 6))
    (ρ : L₀ →* MulAut W)
    (hirr : ∀ S : Subgroup W, (∀ l : L₀, ∀ w ∈ S, ρ l w ∈ S) → S = ⊥ ∨ S = ⊤)
    (σ : L₀ ≃* L₀) (hfuse : ∃ x : L₀, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l : L₀, l * x * l⁻¹ ≠ σ x) :
    A6Facts ρ σ := by
  have hinj : Function.Injective ρ := injective_of_irreducible hW hc e ρ hirr
  let eρ : L₀ ≃* ↥ρ.range := MonoidHom.ofInjective hinj
  have heρ : ∀ l, (eρ l : MulAut W) = ρ l := fun l => rfl
  have hiso : Nonempty (↥ρ.range ≃* alternatingGroup (Fin 6)) := ⟨eρ.symm.trans e⟩
  have hirr' : ∀ S : Subgroup W, (∀ l ∈ ρ.range, ∀ w ∈ S, l w ∈ S) → S = ⊥ ∨ S = ⊤ :=
    fun S hS => hirr S fun l w hw => hS (ρ l) ⟨l, rfl⟩ w hw
  obtain ⟨a1, a2, a3, hβ⟩ := h W hW hc ρ.range hiso hirr'
  let β : ↥ρ.range ≃* ↥ρ.range := eρ.symm.trans (σ.trans eρ)
  have hβ1 : ∀ l, β (eρ l) = eρ (σ l) := fun l => by simp [β]
  have hβ2 : ∀ l, β.symm (eρ l) = eρ (σ.symm l) := fun l => by simp [β]
  have hfuse' : A6Fuses β := by
    obtain ⟨x₀, hx3, hx1, hx⟩ := hfuse
    refine ⟨eρ x₀, by rw [← map_pow, hx3, map_one], fun h1 => hx1 (eρ.injective (by rw [h1, map_one])),
      fun l hl => ?_⟩
    obtain ⟨l₀, rfl⟩ := eρ.surjective l
    apply hx l₀
    apply eρ.injective
    rw [hβ1] at hl
    rw [← map_mul, ← map_inv, ← map_mul] at hl
    exact hl
  obtain ⟨a4, a5, a6⟩ := hβ β hfuse'
  refine ⟨hinj, ?_, ?_, a3, ?_, ?_, ?_⟩
  · intro n hn
    exact a1 n fun l hl => by obtain ⟨l₀, rfl⟩ := hl; exact hn l₀
  · intro l h1 h2
    exact a2 (ρ l) ⟨l, rfl⟩ (fun h => h1 (hinj (by rw [h, map_one])))
      (by rw [← map_pow, h2, map_one])
  · rintro ⟨n, hn⟩
    refine a4 ⟨n, fun l => ?_⟩
    obtain ⟨l₀, rfl⟩ := eρ.surjective l
    rw [hβ1]
    exact hn l₀
  · intro n hn n' hn' hn2 hn'2 hnL hn'L hrel
    refine a5 n hn n' hn' hn2 hn'2 hnL hn'L ?_
    intro l l'' hl
    obtain ⟨l₀, rfl⟩ := eρ.surjective l
    obtain ⟨l₁, rfl⟩ := eρ.surjective l''
    rw [hβ1, hβ1]
    exact hrel l₀ l₁ hl
  · intro a b hab ha hb ha2 hb2 hcomm
    have := a6 (eρ a) (eρ b) (fun h => hab (eρ.injective h)) (fun h => ha (eρ.injective (by rw [h, map_one])))
      (fun h => hb (eρ.injective (by rw [h, map_one]))) (by rw [← map_pow, ha2, map_one])
      (by rw [← map_pow, hb2, map_one]) (by rw [← map_mul, ← map_mul, hcomm])
    rw [hβ2, hβ2] at this
    exact this

end CFSG.Quasithin.A6Amt
