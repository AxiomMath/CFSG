module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PGroup
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Solvable
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.SettingAPI

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman.Steps678

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : Subgroup G → Subgroup G}

theorem prime_of_roles {q r : ℕ} (hqr : (q = 2 ∧ r = 3) ∨ (q = 3 ∧ r = 2)) :
    q.Prime ∧ r.Prime ∧ q ≠ r := by
  rcases hqr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨Nat.prime_two, Nat.prime_three, by norm_num⟩
  · exact ⟨Nat.prime_three, Nat.prime_two, by norm_num⟩

theorem le_primeCoreIn_of_normalizerCompletion_le (h : Setting p A θ) {q r : ℕ}
    (hqr : (q = 2 ∧ r = 3) ∨ (q = 3 ∧ r = 2)) {Fq Fr M M' : Subgroup G}
    (hM : solvableSignalizerCompatible p 1 A θ M) (hM' : solvableSignalizerCompatible p 1 A θ M')
    (hFq : Fq ≤ primeCoreIn {q} M) (hFr : Fr ≤ primeCoreIn {r} M)
    (hAq : A ≤ Subgroup.normalizer (Fq : Set G)) (hq0 : Fq ≠ ⊥) (hFqM' : Fq ≤ M')
    (hFrM' : Fr ≤ M') (hθ : signalizerNormalizerCompletion p 1 A θ Fq ≤ M) :
    Fr ≤ primeCoreIn {r} M' := by
  obtain ⟨hq', hr', hqr'⟩ := prime_of_roles hqr
  have hFqcomp : solvableSignalizerCompatible p 1 A θ Fq :=
    compat_of_le hM (hFq.trans (primeCoreIn_le _ M)) hAq
  obtain ⟨-, -, -, hmax⟩ := normalizerCompletion_spec h hq0 hFqcomp
  have hAV : A ≤ Subgroup.normalizer ((M' ⊓ Subgroup.normalizer (Fq : Set G) : Subgroup G) :
      Set G) := normalizer_inf_of_le A _ _ hM'.1.1 (hAq.trans Subgroup.le_normalizer)
  have hVcomp : signalizerCompatible p 1 A θ (M' ⊓ Subgroup.normalizer (Fq : Set G)) :=
    signalizer_compatible_of_le p 1 A θ hM'.1 inf_le_left hAV
  have hVθ : M' ⊓ Subgroup.normalizer (Fq : Set G) ≤ signalizerNormalizerCompletion p 1 A θ Fq :=
    hmax _ hVcomp inf_le_right
  have hVM : M' ⊓ Subgroup.normalizer (Fq : Set G) ≤ M := hVθ.trans hθ
  have hFrC : Fr ≤ Subgroup.centralizer (Fq : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact commute_of_primeCoreIn hq' hr' hqr' M (hFq hx) (hFr hy)
  have hFrV : Fr ≤ M' ⊓ Subgroup.normalizer (Fq : Set G) :=
    le_inf hFrM' (hFrC.trans (Subgroup.centralizer_le_normalizer _))
  have hOrV : primeCoreIn {r} M ⊓ (M' ⊓ Subgroup.normalizer (Fq : Set G)) ≤
      primeCoreIn ({q}ᶜ : Set ℕ) (M' ⊓ Subgroup.normalizer (Fq : Set G)) := by
    refine le_primeCoreIn_compl hq' inf_le_right ?_ ?_
    · exact normalizer_inf_of_le _ _ _
        (le_normalizer_primeCoreIn _ (hVM.trans Subgroup.le_normalizer)) Subgroup.le_normalizer
    · exact coprime_of_isPGroup hr' hq' hqr'
        ((isPGroup_primeCoreIn hr' M).to_le inf_le_left)
  have hFrO : Fr ≤ primeCoreIn ({q}ᶜ : Set ℕ) (M' ⊓ Subgroup.normalizer (Fq : Set G)) :=
    (le_inf hFr hFrV).trans hOrV
  have hFqp : IsPGroup q Fq := (isPGroup_primeCoreIn hq' M).to_le hFq
  have h813 := primeCoreIn_inf_normalizer_le hq' hM'.2 hFqM' hFqp
  have hFrO' : Fr ≤ primeCoreIn ({q}ᶜ : Set ℕ) M' := hFrO.trans h813
  have hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (primeCoreIn ({q}ᶜ : Set ℕ) M') → ℓ = q ∨ ℓ = r := by
    intro ℓ hℓ hd
    exact support_two_three h hM'.1 hqr ℓ hℓ
      (hd.trans (Subgroup.card_dvd_of_le (primeCoreIn_le _ M')))
  have hOp : IsPGroup r (primeCoreIn ({q}ᶜ : Set ℕ) M') :=
    isPGroup_of_coprime_of_support hq' hr' hsupp (coprime_primeCoreIn hq' M')
  exact hFrO'.trans (le_primeCoreIn_pgroup hr' (primeCoreIn_le _ M')
    (le_normalizer_primeCoreIn _ Subgroup.le_normalizer) hOp)

theorem eq_of_normalizerCompletion_le (h : Setting p A θ) {q r : ℕ}
    (hqr : (q = 2 ∧ r = 3) ∨ (q = 3 ∧ r = 2)) {Fq Fr M L : Subgroup G}
    (hM : Maximal (solvableSignalizerCompatible p 1 A θ) M)
    (hL : Maximal (solvableSignalizerCompatible p 1 A θ) L)
    (hFq : Fq ≤ primeCoreIn {q} M) (hFr : Fr ≤ primeCoreIn {r} M)
    (hAq : A ≤ Subgroup.normalizer (Fq : Set G)) (hq0 : Fq ≠ ⊥) (hr0 : Fr ≠ ⊥)
    (IH : ∀ Fq' Fr' M' : Subgroup G, Nat.card Fq * Nat.card Fr < Nat.card Fq' * Nat.card Fr' →
      Maximal (solvableSignalizerCompatible p 1 A θ) M' → Fq' ≤ primeCoreIn {q} M' →
      Fr' ≤ primeCoreIn {r} M' → A ≤ Subgroup.normalizer (Fq' : Set G) →
      A ≤ Subgroup.normalizer (Fr' : Set G) → Fq' ≠ ⊥ → Fr' ≠ ⊥ →
      ∀ L' : Subgroup G, Maximal (solvableSignalizerCompatible p 1 A θ) L' → Fq' ≤ L' →
        Fr' ≤ L' → L' = M')
    (hθL : signalizerNormalizerCompletion p 1 A θ Fq ≤ L) : L = M := by
  obtain ⟨hq', hr', hqr'⟩ := prime_of_roles hqr
  have hFqcomp : solvableSignalizerCompatible p 1 A θ Fq :=
    compat_of_le hM.prop (hFq.trans (primeCoreIn_le _ M)) hAq
  obtain ⟨-, -, -, hmax⟩ := normalizerCompletion_spec h hq0 hFqcomp
  by_cases hEq : Fq = primeCoreIn {q} M
  · have hMN : M ≤ Subgroup.normalizer (Fq : Set G) := by
      rw [hEq]
      exact le_normalizer_primeCoreIn _ Subgroup.le_normalizer
    have hMθ : M ≤ signalizerNormalizerCompletion p 1 A θ Fq := hmax M hM.prop.1 hMN
    exact le_antisymm (hM.2 hL.prop (hMθ.trans hθL)) (hMθ.trans hθL)
  · have hgrow : Fq < primeCoreIn {q} M ⊓ Subgroup.normalizer (Fq : Set G) :=
      lt_inf_normalizer_of_lt hq' (isPGroup_primeCoreIn hq' M) hFq hEq
    have hAOq : A ≤ Subgroup.normalizer (primeCoreIn {q} M : Set G) :=
      le_normalizer_primeCoreIn _ hM.prop.1.1
    have hAOr : A ≤ Subgroup.normalizer (primeCoreIn {r} M : Set G) :=
      le_normalizer_primeCoreIn _ hM.prop.1.1
    have hAt : A ≤ Subgroup.normalizer
        ((primeCoreIn {q} M ⊓ Subgroup.normalizer (Fq : Set G) : Subgroup G) : Set G) :=
      normalizer_inf_of_le A _ _ hAOq (hAq.trans Subgroup.le_normalizer)
    have hcard : Nat.card Fq * Nat.card Fr <
        Nat.card (primeCoreIn {q} M ⊓ Subgroup.normalizer (Fq : Set G) : Subgroup G) *
          Nat.card (primeCoreIn {r} M) := by
      have h1 := subgroup_card_strict_mono hgrow
      have h2 : Nat.card Fr ≤ Nat.card (primeCoreIn {r} M) := Subgroup.card_le_of_le hFr
      have h3 : 0 < Nat.card Fr := Nat.card_pos
      exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1 h3) (Nat.mul_le_mul_left _ h2)
    have hq1 : primeCoreIn {q} M ⊓ Subgroup.normalizer (Fq : Set G) ≠ ⊥ := fun hb =>
      hq0 (le_bot_iff.mp (hb ▸ hgrow.le))
    have hr1 : primeCoreIn {r} M ≠ ⊥ := fun hb => hr0 (le_bot_iff.mp (hb ▸ hFr))
    have hunique := IH (primeCoreIn {q} M ⊓ Subgroup.normalizer (Fq : Set G))
      (primeCoreIn {r} M) M hcard hM inf_le_left le_rfl hAt hAOr hq1 hr1
    refine hunique L hL ?_ ?_
    · refine le_trans ?_ hθL
      refine hmax _ ?_ inf_le_right
      exact signalizer_compatible_of_le p 1 A θ hM.prop.1
        (inf_le_left.trans (primeCoreIn_le _ M)) hAt
    · refine le_trans ?_ hθL
      refine hmax _ ?_ ?_
      · exact signalizer_compatible_of_le p 1 A θ hM.prop.1 (primeCoreIn_le _ M) hAOr
      · intro y hy
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact commute_of_primeCoreIn hq' hr' hqr' M (hFq hx) hy

theorem eq_of_fitting (h : Setting p A θ) {M M' F₂ F₃ : Subgroup G}
    (hM : Maximal (solvableSignalizerCompatible p 1 A θ) M)
    (hM' : Maximal (solvableSignalizerCompatible p 1 A θ) M')
    (h₂ : F₂ ≤ primeCoreIn {2} M) (h₃ : F₃ ≤ primeCoreIn {3} M)
    (hA₂ : A ≤ Subgroup.normalizer (F₂ : Set G)) (hA₃ : A ≤ Subgroup.normalizer (F₃ : Set G))
    (hne₂ : F₂ ≠ ⊥) (hne₃ : F₃ ≠ ⊥) (h₂' : F₂ ≤ M') (h₃' : F₃ ≤ M') : M = M' := by
  by_contra hMM'
  let Bad : Subgroup G → Subgroup G → Prop := fun F₂ F₃ =>
    ∃ M M' : Subgroup G, Maximal (solvableSignalizerCompatible p 1 A θ) M ∧
      Maximal (solvableSignalizerCompatible p 1 A θ) M' ∧ F₂ ≤ primeCoreIn {2} M ∧
      F₃ ≤ primeCoreIn {3} M ∧ A ≤ Subgroup.normalizer (F₂ : Set G) ∧
      A ≤ Subgroup.normalizer (F₃ : Set G) ∧ F₂ ≠ ⊥ ∧ F₃ ≠ ⊥ ∧ F₂ ≤ M' ∧ F₃ ≤ M' ∧ M ≠ M'
  have hbad : Bad F₂ F₃ := ⟨M, M', hM, hM', h₂, h₃, hA₂, hA₃, hne₂, hne₃, h₂', h₃', hMM'⟩
  have : Nonempty {x : Subgroup G × Subgroup G // Bad x.1 x.2} := ⟨⟨(F₂, F₃), hbad⟩⟩
  obtain ⟨⟨⟨G₂, G₃⟩, hGbad⟩, hmaxG⟩ := Finite.exists_max
    (fun x : {x : Subgroup G × Subgroup G // Bad x.1 x.2} => Nat.card x.1.1 * Nat.card x.1.2)
  obtain ⟨N, N', hN, hN', hG₂, hG₃, hAG₂, hAG₃, hG₂0, hG₃0, hG₂N', hG₃N', hNN'⟩ := hGbad
  have IH : ∀ F₂' F₃' M₀ : Subgroup G, Nat.card G₂ * Nat.card G₃ < Nat.card F₂' * Nat.card F₃' →
      Maximal (solvableSignalizerCompatible p 1 A θ) M₀ → F₂' ≤ primeCoreIn {2} M₀ →
      F₃' ≤ primeCoreIn {3} M₀ → A ≤ Subgroup.normalizer (F₂' : Set G) →
      A ≤ Subgroup.normalizer (F₃' : Set G) → F₂' ≠ ⊥ → F₃' ≠ ⊥ →
      ∀ L' : Subgroup G, Maximal (solvableSignalizerCompatible p 1 A θ) L' → F₂' ≤ L' →
        F₃' ≤ L' → L' = M₀ := by
    intro F₂' F₃' M₀ hlt hM₀ h2 h3 hA2 hA3 hn2 hn3 L' hL' hL2 hL3
    by_contra hne
    have hb : Bad F₂' F₃' :=
      ⟨M₀, L', hM₀, hL', h2, h3, hA2, hA3, hn2, hn3, hL2, hL3, fun h => hne h.symm⟩
    exact (not_le.mpr hlt) (hmaxG ⟨(F₂', F₃'), hb⟩)
  have IH' : ∀ F₃' F₂' M₀ : Subgroup G, Nat.card G₃ * Nat.card G₂ < Nat.card F₃' * Nat.card F₂' →
      Maximal (solvableSignalizerCompatible p 1 A θ) M₀ → F₃' ≤ primeCoreIn {3} M₀ →
      F₂' ≤ primeCoreIn {2} M₀ → A ≤ Subgroup.normalizer (F₃' : Set G) →
      A ≤ Subgroup.normalizer (F₂' : Set G) → F₃' ≠ ⊥ → F₂' ≠ ⊥ →
      ∀ L' : Subgroup G, Maximal (solvableSignalizerCompatible p 1 A θ) L' → F₃' ≤ L' →
        F₂' ≤ L' → L' = M₀ := by
    intro F₃' F₂' M₀ hlt hM₀ h3 h2 hA3 hA2 hn3 hn2 L' hL' hL3 hL2
    exact IH F₂' F₃' M₀ (by
      rw [mul_comm (Nat.card G₂) (Nat.card G₃), mul_comm (Nat.card F₂') (Nat.card F₃')]
      exact hlt) hM₀ h2 h3 hA2 hA3 hn2 hn3 L' hL' hL2 hL3
  have hθ₂ : signalizerNormalizerCompletion p 1 A θ G₂ ≤ N := by
    have hG₂comp : solvableSignalizerCompatible p 1 A θ G₂ :=
      compat_of_le hN.prop (hG₂.trans (primeCoreIn_le _ N)) hAG₂
    obtain ⟨hcomp, -, -, -⟩ := normalizerCompletion_spec h hG₂0 hG₂comp
    obtain ⟨L, hL, hLge⟩ := exists_maximal_ge hcomp
    have hLN := eq_of_normalizerCompletion_le h (q := 2) (r := 3) (Or.inl ⟨rfl, rfl⟩) hN hL hG₂
      hG₃ hAG₂ hG₂0 hG₃0 IH hLge
    exact le_of_le_of_eq hLge hLN
  have hθ₃ : signalizerNormalizerCompletion p 1 A θ G₃ ≤ N := by
    have hG₃comp : solvableSignalizerCompatible p 1 A θ G₃ :=
      compat_of_le hN.prop (hG₃.trans (primeCoreIn_le _ N)) hAG₃
    obtain ⟨hcomp, -, -, -⟩ := normalizerCompletion_spec h hG₃0 hG₃comp
    obtain ⟨L, hL, hLge⟩ := exists_maximal_ge hcomp
    have hLN := eq_of_normalizerCompletion_le h (q := 3) (r := 2) (Or.inr ⟨rfl, rfl⟩) hN hL hG₃
      hG₂ hAG₃ hG₃0 hG₂0 IH' hLge
    exact le_of_le_of_eq hLge hLN
  have hG₂N'' : G₂ ≤ primeCoreIn {2} N' :=
    le_primeCoreIn_of_normalizerCompletion_le h (q := 3) (r := 2) (Or.inr ⟨rfl, rfl⟩) hN.prop
      hN'.prop hG₃ hG₂ hAG₃ hG₃0 hG₃N' hG₂N' hθ₃
  have hG₃N'' : G₃ ≤ primeCoreIn {3} N' :=
    le_primeCoreIn_of_normalizerCompletion_le h (q := 2) (r := 3) (Or.inl ⟨rfl, rfl⟩) hN.prop
      hN'.prop hG₂ hG₃ hAG₂ hG₂0 hG₂N' hG₃N' hθ₂
  have hNN'eq := eq_of_normalizerCompletion_le h (q := 2) (r := 3) (Or.inl ⟨rfl, rfl⟩) hN' hN
    hG₂N'' hG₃N'' hAG₂ hG₂0 hG₃0 IH hθ₂
  exact hNN' hNN'eq

end CFSG.SignalizerFunctorTheorem.Glauberman.Steps678
