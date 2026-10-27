module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Fitting
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Seven

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman.Steps678

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : Subgroup G → Subgroup G}

theorem exists_primeCoreIn_eq_bot (h : Setting p A θ) {M : Subgroup G}
    (hM : Maximal (solvableSignalizerCompatible p 1 A θ) M)
    (hCA : signalizerCommonFixed p 1 A θ ≤ M) :
    ∃ q : ℕ, (q = 2 ∨ q = 3) ∧ primeCoreIn ({q}ᶜ : Set ℕ) M = ⊥ := by
  by_contra hne
  have hne' : ∀ q : ℕ, (q = 2 ∨ q = 3) → primeCoreIn ({q}ᶜ : Set ℕ) M ≠ ⊥ :=
    fun q hq hb => hne ⟨q, hq, hb⟩
  have hne3 := hne' 3 (Or.inr rfl)
  have hne2 := hne' 2 (Or.inl rfl)
  have hAM := hM.prop.1.1
  have h32 : primeCoreIn ({3}ᶜ : Set ℕ) M ≤ primeCoreIn {2} M := by
    have hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (primeCoreIn ({3}ᶜ : Set ℕ) M) → ℓ = 3 ∨ ℓ = 2 :=
      fun ℓ hℓ hd => support_two_three h hM.prop.1 (q := 3) (r := 2) (Or.inr ⟨rfl, rfl⟩) ℓ hℓ
        (hd.trans (Subgroup.card_dvd_of_le (primeCoreIn_le _ M)))
    exact le_primeCoreIn_pgroup Nat.prime_two (primeCoreIn_le _ M)
      (le_normalizer_primeCoreIn _ Subgroup.le_normalizer)
      (isPGroup_of_coprime_of_support Nat.prime_three Nat.prime_two hsupp
        (coprime_primeCoreIn Nat.prime_three M))
  have h23 : primeCoreIn ({2}ᶜ : Set ℕ) M ≤ primeCoreIn {3} M := by
    have hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (primeCoreIn ({2}ᶜ : Set ℕ) M) → ℓ = 2 ∨ ℓ = 3 :=
      fun ℓ hℓ hd => support_two_three h hM.prop.1 (q := 2) (r := 3) (Or.inl ⟨rfl, rfl⟩) ℓ hℓ
        (hd.trans (Subgroup.card_dvd_of_le (primeCoreIn_le _ M)))
    exact le_primeCoreIn_pgroup Nat.prime_three (primeCoreIn_le _ M)
      (le_normalizer_primeCoreIn _ Subgroup.le_normalizer)
      (isPGroup_of_coprime_of_support Nat.prime_two Nat.prime_three hsupp
        (coprime_primeCoreIn Nat.prime_two M))
  have hY2 : primeCoreIn {2} M ≠ ⊥ := fun hb => hne3 (le_bot_iff.mp (hb ▸ h32))
  have hY3 : primeCoreIn {3} M ≠ ⊥ := fun hb => hne2 (le_bot_iff.mp (hb ▸ h23))
  obtain ⟨⟨E, hECA, hE3, hE9⟩, -⟩ := h.exists_elemAbelian_nine_eight
  have hEp : IsPGroup 3 E := elementary_abelian_isPGroup 3 E hE3
  have hEM : E ≤ M := hECA.trans hCA
  have hEN : ∀ π : Set ℕ, E ≤ Subgroup.normalizer (primeCoreIn π M : Set G) := fun π =>
    hEM.trans (le_normalizer_primeCoreIn π Subgroup.le_normalizer)
  have hY3E := inf_centralizer_ne_bot Nat.prime_three hEp (isPGroup_primeCoreIn Nat.prime_three M)
    hY3 (hEN {3})
  have hgen := elementary_abelian_centralizer_generation 3 1 Nat.prime_three E
    (primeCoreIn ({3}ᶜ : Set ℕ) M) hE3 (by simp [hE9]) (hEN {3}ᶜ)
    (coprime_primeCoreIn Nat.prime_three M)
  obtain ⟨S, hS, hSne⟩ : ∃ S ∈ signalizerFunctorEk 3 1 E,
      primeCoreIn ({3}ᶜ : Set ℕ) M ⊓ Subgroup.centralizer (S : Set G) ≠ ⊥ := by
    by_contra hcon
    have hall : ∀ S ∈ signalizerFunctorEk 3 1 E,
        primeCoreIn ({3}ᶜ : Set ℕ) M ⊓ Subgroup.centralizer (S : Set G) = ⊥ := by
      intro S hS
      by_contra hb
      exact hcon ⟨S, hS, hb⟩
    apply hne3
    rw [← hgen]
    apply iSup_eq_bot.mpr
    intro S
    apply iSup_eq_bot.mpr
    intro hS
    exact hall S hS
  have hSE : S ≤ E := hS.1
  have hSCA : S ≤ signalizerCommonFixed p 1 A θ := hSE.trans hECA
  have hSp : IsPGroup 3 S := elementary_abelian_isPGroup 3 S (elementary_abelian_of_le 3 hE3 hSE)
  have hS0 : S ≠ ⊥ := by
    intro hbot
    have hcard := hS.2
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hScomp := compat_of_le_commonFixed Nat.prime_three hSp hSCA
  have hAC : A ≤ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) :=
    le_normalizer_centralizer (actor_le_normalizer_of_le_commonFixed hSCA)
  have hAcore : ∀ π : Set ℕ, A ≤ Subgroup.normalizer
      ((primeCoreIn π M ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := fun π =>
    normalizer_inf_of_le A _ _ (le_normalizer_primeCoreIn π hAM) hAC
  have hF3ne : primeCoreIn {3} M ⊓ Subgroup.centralizer (S : Set G) ≠ ⊥ := by
    intro hb
    apply hY3E
    rw [← le_bot_iff, ← hb]
    exact inf_le_inf_left _ (Subgroup.centralizer_le hSE)
  have hF2ne : primeCoreIn {2} M ⊓ Subgroup.centralizer (S : Set G) ≠ ⊥ := by
    intro hb
    apply hSne
    rw [← le_bot_iff, ← hb]
    exact inf_le_inf_right _ h32
  have hcompF : ∀ π : Set ℕ, signalizerCompatible p 1 A θ
      (primeCoreIn π M ⊓ Subgroup.centralizer (S : Set G)) := fun π =>
    signalizer_compatible_of_le p 1 A θ hM.prop.1 (inf_le_left.trans (primeCoreIn_le π M))
      (hAcore π)
  have hDcomp := compat_thetaCentralizer h hS0 hScomp
  obtain ⟨M', hM', hDM'⟩ := exists_maximal_ge hDcomp
  have hFD : ∀ π : Set ℕ, primeCoreIn π M ⊓ Subgroup.centralizer (S : Set G) ≤
      thetaCentralizer p A θ S := fun π =>
    le_thetaCentralizer h hS0 hScomp (hcompF π) inf_le_right
  have hMM' : M = M' := eq_of_fitting h hM hM'
    (F₂ := primeCoreIn {2} M ⊓ Subgroup.centralizer (S : Set G))
    (F₃ := primeCoreIn {3} M ⊓ Subgroup.centralizer (S : Set G)) inf_le_left inf_le_left
    (hAcore {2}) (hAcore {3}) hF2ne hF3ne ((hFD {2}).trans hDM') ((hFD {3}).trans hDM')
  have hDM : thetaCentralizer p A θ S ≤ M := le_of_le_of_eq hDM' hMM'.symm
  have h1 := primeCoreIn_inf_le ({3}ᶜ : Set ℕ) hDM
  have h2 := primeCoreIn_thetaCentralizer_le h (Or.inr rfl : (3 : ℕ) = 2 ∨ (3 : ℕ) = 3) hSp hSCA hS0
  have h3 := hyperplaneMeetJoin_eq_bot h (Or.inr rfl : (3 : ℕ) = 2 ∨ (3 : ℕ) = 3)
  have hCS : primeCoreIn ({3}ᶜ : Set ℕ) M ⊓ Subgroup.centralizer (S : Set G) ≤
      primeCoreIn ({3}ᶜ : Set ℕ) M ⊓ thetaCentralizer p A θ S := by
    exact le_inf inf_le_left (le_thetaCentralizer h hS0 hScomp (hcompF {3}ᶜ) inf_le_right)
  apply hSne
  rw [h3] at h2
  exact le_bot_iff.mp ((hCS.trans h1).trans h2)

end CFSG.SignalizerFunctorTheorem.Glauberman.Steps678
