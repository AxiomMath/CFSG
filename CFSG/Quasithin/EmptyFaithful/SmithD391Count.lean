module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S153ZE
public import CFSG.Quasithin.EmptyFaithful.S153ZF

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391

open scoped Pointwise

universe u

variable {Γ : Type*} [Group Γ]

theorem smul_mem_of_sup_eq_top {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]
    {A Λ : Subgroup Γ} (hgen : A ⊔ Λ = ⊤) {S : Subgroup Q} (hA : ∀ a ∈ A, ∀ s ∈ S, a • s ∈ S)
    (hΛ : ∀ l ∈ Λ, ∀ s ∈ S, l • s ∈ S) : ∀ g : Γ, ∀ s ∈ S, g • s ∈ S := by
  intro g
  have hg : g ∈ A ⊔ Λ := by rw [hgen]; trivial
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hA x hx
    · exact hΛ x hx
  | inv_mem x hx =>
    rcases hx with hx | hx
    · exact hA x⁻¹ (A.inv_mem hx)
    · exact hΛ x⁻¹ (Λ.inv_mem hx)
  | one => intro s hs; rwa [one_smul]
  | mul x y _ _ hx hy =>
    intro s hs
    rw [mul_smul]
    exact hx _ (hy s hs)

theorem nB_range_eq {P₁ Q : Type*} [CommGroup P₁] [CommGroup Q] [Finite P₁] [Finite Q]
    [MulDistribMulAction Γ P₁] [MulDistribMulAction Γ Q] (A : Subgroup Γ) (φ : P₁ →* Q)
    (hinj : Function.Injective φ) (hA : ∀ a ∈ A, ∀ p, φ (a • p) = a • φ p) :
    nB A φ.range = nB A (⊤ : Subgroup P₁) := by
  unfold nB
  set F := XMod.fixed ↥A (⊤ : Subgroup Q) with hF
  set F₁ := XMod.fixed ↥A (⊤ : Subgroup P₁) with hF₁
  have hrk1 : rk ↥φ.range = rk ↥(⊤ : Subgroup P₁) := by
    unfold rk
    rw [Subgroup.card_top]
    exact congrArg (padicValNat 2) (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm)
  have hmap : φ.range ⊓ F = F₁.map φ := by
    ext y
    constructor
    · rintro ⟨⟨p, rfl⟩, hy⟩
      refine ⟨p, XMod.mem_fixed.2 ⟨trivial, fun a => ?_⟩, rfl⟩
      have h1 := (XMod.mem_fixed.1 hy).2 a
      change (a : Γ) • φ p = φ p at h1
      rw [← hA (a : Γ) a.2 p] at h1
      exact hinj h1
    · rintro ⟨p, hp, rfl⟩
      refine ⟨⟨p, rfl⟩, XMod.mem_fixed.2 ⟨trivial, fun a => ?_⟩⟩
      have h1 := (XMod.mem_fixed.1 hp).2 a
      change (a : Γ) • p = p at h1
      change (a : Γ) • φ p = φ p
      rw [← hA (a : Γ) a.2 p, h1]
  have hrk2 : rk ↥(φ.range ⊓ F) = rk ↥((⊤ : Subgroup P₁) ⊓ F₁) := by
    rw [hmap, top_inf_eq]
    unfold rk
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ φ hinj).toEquiv.symm]
  rw [hrk1, hrk2]

theorem card_quotMod_lt {Q : Type*} [CommGroup Q] [Finite Q] [MulDistribMulAction Γ Q]
    (S : Subgroup Q) (hS : ∀ g : Γ, ∀ s ∈ S, g • s ∈ S) (hne : S ≠ ⊥) :
    Nat.card (QuotMod S hS) < Nat.card Q := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup S
  have h2 : 1 < Nat.card S := by
    refine Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨Nat.card_pos.ne', fun h => hne ?_⟩
    exact Subgroup.card_eq_one.1 h
  have h3 : 0 < Nat.card (Q ⧸ S) := Nat.card_pos
  show Nat.card (Q ⧸ S) < Nat.card Q
  rw [h1]
  nlinarith

theorem count_of_homs {Λ A : Subgroup Γ} (hA : IsPGroup 2 A)
    (hAΛ : ∀ a ∈ A, ∀ l ∈ Λ, a * l * a⁻¹ ∈ Λ) (hgen : A ⊔ Λ = ⊤)
    {P₁ : Type*} [CommGroup P₁] [Finite P₁] [MulDistribMulAction Γ P₁]
    (hirr : ∀ J : Subgroup P₁, (∀ l ∈ Λ, ∀ p ∈ J, l • p ∈ J) → J = ⊥ ∨ J = ⊤) :
    ∀ (n : ℕ) (Q : Type u) [CommGroup Q] [Finite Q] [MulDistribMulAction Γ Q], Nat.card Q = n →
      (∀ q : Q, q ^ 2 = 1) →
      (⊤ : Subgroup Q) ≤ ⨆ (φ : P₁ →* Q) (_ : ∀ l ∈ Λ, ∀ p, φ (l • p) = l • φ p), φ.range →
      ∃ k : ℕ, rk Q = k * rk P₁ ∧ k * nB A (⊤ : Subgroup P₁) ≤ nB A (⊤ : Subgroup Q) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ _ _ hn hQ hgenQ
  by_cases htriv : (⊤ : Subgroup Q) = ⊥
  · refine ⟨0, ?_, by simp⟩
    rw [zero_mul, ← rk_top, htriv, rk_bot]
  obtain ⟨φ₀, hφ₀, hne⟩ : ∃ φ₀ : P₁ →* Q, (∀ l ∈ Λ, ∀ p, φ₀ (l • p) = l • φ₀ p) ∧ φ₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply htriv
    refine le_bot_iff.1 (hgenQ.trans (iSup₂_le fun φ hφ => ?_))
    rw [hcon φ hφ, MonoidHom.range_one]
  obtain ⟨φ, hφne, hφΛ, hφA⟩ := exists_fixed_hom hQ Λ A hA hAΛ φ₀ hφ₀ hne
  have hker : φ.ker = ⊥ := by
    rcases hirr φ.ker (fun l hl p hp => by
        rw [MonoidHom.mem_ker] at hp ⊢
        rw [hφΛ l hl p, hp, smul_one]) with h | h
    · exact h
    · exfalso
      apply hφne
      ext p
      have : p ∈ φ.ker := by rw [h]; trivial
      exact this
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  set S := φ.range with hS
  have hSΓ : ∀ g : Γ, ∀ s ∈ S, g • s ∈ S := by
    refine smul_mem_of_sup_eq_top hgen ?_ ?_
    · rintro a ha _ ⟨p, rfl⟩
      exact ⟨a • p, hφA a ha p⟩
    · rintro l hl _ ⟨p, rfl⟩
      exact ⟨l • p, hφΛ l hl p⟩
  have hSne : S ≠ ⊥ := by
    intro h0
    apply hφne
    ext p
    have : φ p ∈ S := ⟨p, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    exact this
  have hcard : Nat.card (QuotMod S hSΓ) < n := hn ▸ card_quotMod_lt S hSΓ hSne
  have hQ' : ∀ q : QuotMod S hSΓ, q ^ 2 = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotMod.mk_surjective S hSΓ q
    rw [← map_pow, hQ x, map_one]
  have hgen' : (⊤ : Subgroup (QuotMod S hSΓ)) ≤
      ⨆ (ψ : P₁ →* QuotMod S hSΓ) (_ : ∀ l ∈ Λ, ∀ p, ψ (l • p) = l • ψ p), ψ.range := by
    rintro q -
    obtain ⟨x, rfl⟩ := QuotMod.mk_surjective S hSΓ q
    have hx : x ∈ ⨆ (φ : P₁ →* Q) (_ : ∀ l ∈ Λ, ∀ p, φ (l • p) = l • φ p), φ.range :=
      hgenQ trivial
    have hle : (⨆ (φ : P₁ →* Q) (_ : ∀ l ∈ Λ, ∀ p, φ (l • p) = l • φ p), φ.range).map
        (QuotMod.mk S hSΓ) ≤
        ⨆ (ψ : P₁ →* QuotMod S hSΓ) (_ : ∀ l ∈ Λ, ∀ p, ψ (l • p) = l • ψ p), ψ.range := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun ψ => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hψ => ?_
      refine le_trans ?_ (le_iSup₂_of_le ((QuotMod.mk S hSΓ).comp ψ) ?_ le_rfl)
      · rw [MonoidHom.range_comp]
      · intro l hl p
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hψ l hl p]
        rfl
    exact hle (Subgroup.mem_map_of_mem _ hx)
  obtain ⟨k, hk1, hk2⟩ := ih _ hcard (QuotMod S hSΓ) rfl hQ' hgen'
  have hrkS : rk ↥S = rk P₁ := by
    unfold rk
    exact congrArg (padicValNat 2) (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm)
  have hchain := nB_chain A S hSΓ
  have hnS : nB A S = nB A (⊤ : Subgroup P₁) := nB_range_eq A φ hinj hφA
  have hsplit := rk_add_rkIdx S
  have hquot := rk_quotMod_top S hSΓ
  rw [rk_top] at hquot
  refine ⟨k + 1, ?_, ?_⟩
  · rw [← hsplit, hrkS, ← hquot, hk1]
    ring
  · rw [hnS] at hchain
    calc (k + 1) * nB A (⊤ : Subgroup P₁)
        = nB A (⊤ : Subgroup P₁) + k * nB A (⊤ : Subgroup P₁) := by ring
      _ ≤ nB A (⊤ : Subgroup P₁) + nB A (⊤ : Subgroup (QuotMod S hSΓ)) := by omega
      _ ≤ nB A (⊤ : Subgroup Q) := hchain

end CFSG.Quasithin.SmithD391
