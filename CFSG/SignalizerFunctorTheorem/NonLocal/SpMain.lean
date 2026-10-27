module

public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.AbelianBound
public import CFSG.SignalizerFunctorTheorem.NonLocal.OrbitBound
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpSiegel
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo

public section

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpComm
  CFSG.SignalizerFunctorTheorem.CatalogBridge
  CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom)

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem two_pow_gt_two_mul (r : ℕ) (hr : 3 ≤ r) : 2 * r < 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    omega

theorem sp_numerics {r f ℓ s m j : ℕ} (hr : 2 ≤ r) (hf : 1 ≤ f) (hℓ : ℓ.Prime)
    (hq : ¬ (r = 2 ∧ ℓ ^ f ≤ 3)) (hs : 2 ≤ s)
    (ha : f * (r * (r + 1) / 2) ≤ m) (ho : ℓ ≤ m)
    (h : m ≤ 2 * r - 1 ∨ (s ^ j ≤ 2 * r ∧ m ≤ 2 * j)) : False := by
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  ·
    have hr2 : r = 2 := by omega
    subst hr2
    have hq' : 4 ≤ ℓ ^ f := by
      by_contra hcon
      exact hq ⟨rfl, by omega⟩
    have hsum : 2 * 3 / 2 = 3 := by norm_num
    rw [hsum] at ha
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · have hf1 : f = 1 := by omega
      subst hf1
      have hℓ4 : 4 ≤ ℓ := by simpa using hq'
      have hℓ5 : 5 ≤ ℓ := by
        rcases Nat.eq_or_lt_of_le hℓ4 with h4 | h4
        · exfalso
          rw [← h4] at hℓ
          norm_num at hℓ
        · omega
      rcases h with h | ⟨hsj, hmj⟩
      · omega
      · have hj : 2 ^ j ≤ 4 := (Nat.pow_le_pow_left hs j).trans (by simpa using hsj)
        have hj2 : j ≤ 2 := by
          by_contra hcon
          have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        omega
    · rcases h with h | ⟨hsj, hmj⟩
      · omega
      · have hj : 2 ^ j ≤ 4 := (Nat.pow_le_pow_left hs j).trans (by simpa using hsj)
        have hj2 : j ≤ 2 := by
          by_contra hcon
          have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        omega
  ·
    have hsr : 2 * r ≤ r * (r + 1) / 2 := by
      have : r * (r + 1) / 2 * 2 = r * (r + 1) := by
        have : 2 ∣ r * (r + 1) := (Nat.even_mul_succ_self r).two_dvd
        omega
      nlinarith
    have hfa : 2 * r ≤ f * (r * (r + 1) / 2) := by
      calc 2 * r ≤ r * (r + 1) / 2 := hsr
        _ = 1 * (r * (r + 1) / 2) := (one_mul _).symm
        _ ≤ f * (r * (r + 1) / 2) := Nat.mul_le_mul_right _ hf
    rcases h with h | ⟨hsj, hmj⟩
    · omega
    · have hj : 2 ^ j ≤ 2 * r := (Nat.pow_le_pow_left hs j).trans hsj
      have hjr : j < r := by
        by_contra hcon
        have h1 : 2 ^ r ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := two_pow_gt_two_mul r hr3
        omega
      omega

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem sp_closing_data (hr : 2 ≤ r) (σ : K ≃+* K) {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hkf : Nat.card (descentField σ) = ℓ ^ f) {s : ℕ} (hs : s.Prime) (hsr : s ≠ ℓ)
    (V : Subgroup (StatedProj (StatedSp r K))) [IsMulCommutative V] (hV0 : V ≠ ⊥)
    (hVexp : ∀ v ∈ V, v ^ s = 1)
    (hVnorm : ∀ g : StatedSp r (descentField σ), ∀ v ∈ V,
      proj r K (subfieldSpHom r (descentField σ) g) * v *
        (proj r K (subfieldSpHom r (descentField σ) g))⁻¹ ∈ V)
    (hfaith : ∀ g : StatedSp r (descentField σ), (∀ v ∈ V,
      proj r K (subfieldSpHom r (descentField σ) g) * v *
        (proj r K (subfieldSpHom r (descentField σ) g))⁻¹ = v) →
      proj r K (subfieldSpHom r (descentField σ) g) = 1)
    (hup : Nat.card V ≤ s ^ (Fintype.card (Fin r ⊕ Fin r) - 1) ∨
      ∃ e : ℕ, e ≤ Fintype.card (Fin r ⊕ Fin r) ∧ e ∣ Nat.card V ∧ Nat.card V ≤ e ^ 2) :
    ∃ m : ℕ, Nat.card V = s ^ m ∧ f * (r * (r + 1) / 2) ≤ m ∧ ℓ ≤ m ∧
      (m ≤ 2 * r - 1 ∨ ∃ j, s ^ j ≤ 2 * r ∧ m ≤ 2 * j) := by
  classical
  have : NeZero r := ⟨by omega⟩
  have hℓ : ℓ.Prime := Fact.out
  have : Fact s.Prime := ⟨hs⟩
  let k : Subfield K := descentField σ
  have hkℓ : CharP k ℓ := (RingHom.charP_iff k.subtype k.subtype.injective ℓ).mpr inferInstance
  have : Finite (StatedProj (StatedSp r K)) :=
    Finite.of_surjective (proj r K) (proj_surjective (r := r) (K := K))
  have hVp : IsPGroup s V := by
    refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
    have h1 : orderOf g ∣ s := orderOf_dvd_of_pow_eq_one (Subtype.ext (hVexp g g.2))
    rcases (Nat.dvd_prime hs).mp h1 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hVp
  refine ⟨m, hm, ?_⟩
  let φ : StatedSp r k →* StatedProj (StatedSp r K) := (proj r K).comp (subfieldSpHom r k)
  have hfaithE : ∀ g ∈ spSiegel r k, (∀ v ∈ V, φ g * v * (φ g)⁻¹ = v) → g = 1 := by
    intro g hg hgV
    have h1 : φ g = 1 := hfaith g hgV
    have h2 : g ∈ spScalars r k := (subfieldProj_eq_one_iff (r := r) σ g).mp h1
    exact eq_one_of_mem_spSiegel_of_mem_spScalars r k hg h2
  have hEexp : ∀ g ∈ spSiegel r k, g ^ ℓ = 1 := fun g hg => pow_eq_one_of_mem_spSiegel r k hg
  have hrℓ : ℓ ≠ s := fun h => hsr h.symm
  have hSiegel : f * (r * (r + 1) / 2) ≤ m := by
    have hEa : Nat.card (spSiegel r k) = ℓ ^ (f * (r * (r + 1) / 2)) := by
      rw [card_spSiegel, hkf, ← pow_mul]
    have := pow_le_card_of_abelian_subgroup φ V hℓ hs hrℓ hVexp hVnorm
      (spSiegel r k) (spSiegel_isMulCommutative r k) hEexp hfaithE hEa hV0
    rw [hm] at this
    exact (Nat.pow_le_pow_iff_right hs.one_lt).mp this
  have hLevi : ℓ ≤ m := by
    have hn1 : ∀ e ∈ spSiegel r k, spLevi r k hr * e * (spLevi r k hr)⁻¹ ∈ spSiegel r k :=
      fun e he => spLevi_conj_mem r k hr he
    have hn2 : ∀ e ∈ spSiegel r k, spLevi r k hr ^ ℓ * e = e * spLevi r k hr ^ ℓ := by
      intro e _
      rw [spLevi_pow r k hr, one_mul, mul_one]
    have := pow_le_card_of_normalizing φ V hℓ hs hrℓ hVexp hVnorm
      (spSiegel r k) (spSiegel_isMulCommutative r k) hEexp (spLevi r k hr) hn1 hn2
      (spLevi_conj_ne r k hr) hfaithE
    rw [hm] at this
    exact (Nat.pow_le_pow_iff_right hs.one_lt).mp this
  have hcardι : Fintype.card (Fin r ⊕ Fin r) = 2 * r := by
    rw [Fintype.card_sum, Fintype.card_fin]
    ring
  have hupm : m ≤ 2 * r - 1 ∨ ∃ j, s ^ j ≤ 2 * r ∧ m ≤ 2 * j := by
    rcases hup with h | ⟨e, he, hdvd, hle⟩
    · left
      rw [hm, hcardι] at h
      exact (Nat.pow_le_pow_iff_right hs.one_lt).mp h
    · right
      rw [hm] at hdvd hle
      obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hs).mp hdvd
      rw [hcardι] at he
      refine ⟨j, he, ?_⟩
      rw [← pow_mul, mul_comm] at hle
      exact (Nat.pow_le_pow_iff_right hs.one_lt).mp hle
  exact ⟨hSiegel, hLevi, hupm⟩

theorem nonLocalized_spSubfield_of_closing (hr : 2 ≤ r) (σ : K ≃+* K)
    (hk2 : ¬ (r = 2 ∧ Nat.card (descentField σ) = 2)) {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hclose : ∀ s : ℕ, s.Prime → s ≠ ℓ → ∀ V : Subgroup (StatedProj (StatedSp r K)), V ≠ ⊥ →
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → (∀ v ∈ V, v ^ s = 1) →
      (∀ g : StatedSp r (descentField σ), ∀ v ∈ V,
        proj r K (subfieldSpHom r (descentField σ) g) * v *
          (proj r K (subfieldSpHom r (descentField σ) g))⁻¹ ∈ V) →
      (∀ g : StatedSp r (descentField σ), (∀ v ∈ V,
        proj r K (subfieldSpHom r (descentField σ) g) * v *
          (proj r K (subfieldSpHom r (descentField σ) g))⁻¹ = v) →
        proj r K (subfieldSpHom r (descentField σ) g) = 1) →
      (Nat.card V ≤ s ^ (Fintype.card (Fin r ⊕ Fin r) - 1) ∨
        ∃ e : ℕ, e ≤ Fintype.card (Fin r ⊕ Fin r) ∧ e ∣ Nat.card V ∧ Nat.card V ≤ e ^ 2) →
      False) :
    NonLocalized (subfieldProj (r := r) σ).range := by
  classical
  have : NeZero r := ⟨by omega⟩
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  let k : Subfield K := descentField σ
  have : Finite k := inferInstance
  let P := spProjData r K
  let φH : StatedSp r k →* StatedSp r K := subfieldSpHom r k
  have hrange : (P.π.comp φH).range = (subfieldProj (r := r) σ).range := rfl
  have hsimple : IsSimpleGroup (P.π.comp φH).range := by
    rw [hrange]
    obtain ⟨hs, -⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj
      (k := k) hr hk2
    rw [← range_subfieldInj]
    exact (MonoidHom.ofInjective (subfieldInj_injective (r := r) σ)).symm.isSimpleGroup
  rw [← hrange]
  refine P.nonLocalized_of_closing φH (fun W hW => sp_irreducible k W hW) hsimple
    (sp_centralizer_eq_one k) ?_
  intro s hs hsr V hV0 hVcomm hVexp hVnorm hfaith hup
  exact hclose s hs hsr V hV0 hVcomm hVexp hVnorm hfaith hup

theorem nonLocalized_spSubfield_generic (hr : 2 ≤ r) (σ : K ≃+* K)
    (hne : ¬ (r = 2 ∧ Nat.card (descentField σ) ≤ 3)) :
    NonLocalized (subfieldProj (r := r) σ).range := by
  classical
  obtain ⟨ℓ, hrK⟩ := CharP.exists K
  have hℓ : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let k : Subfield K := descentField σ
  have : Finite k := inferInstance
  have := Fintype.ofFinite k
  obtain ⟨f', -, hkf'⟩ := FiniteField.card k ℓ
  obtain ⟨f, hkf⟩ : ∃ f : ℕ, Nat.card k = ℓ ^ f :=
    ⟨f', by rw [Nat.card_eq_fintype_card, hkf']⟩
  have hk2 : ¬ (r = 2 ∧ Nat.card (descentField σ) = 2) := fun h => hne ⟨h.1, by omega⟩
  refine nonLocalized_spSubfield_of_closing hr σ hk2 (ℓ := ℓ) ?_
  intro s hs hsr V hV0 hVcomm hVexp hVnorm hfaith hup
  have : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩
  obtain ⟨m, -, hSiegel, hLevi, hupm⟩ :=
    sp_closing_data hr σ hkf hs hsr V hV0 hVexp hVnorm hfaith hup
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      have : Nat.card k = 1 := by rw [hkf, h0, pow_zero]
      have h2 : 1 < Nat.card k := Finite.one_lt_card
      omega
    · exact h0
  have hq : ¬ (r = 2 ∧ ℓ ^ f ≤ 3) := by rwa [← hkf]
  rcases hupm with h | ⟨j, hj1, hj2⟩
  · exact sp_numerics (j := 0) hr hf1 hℓ hq hs.two_le hSiegel hLevi (Or.inl h)
  · exact sp_numerics hr hf1 hℓ hq hs.two_le hSiegel hLevi (Or.inr ⟨hj1, hj2⟩)

theorem nonLocalized_spSubfield_two_three (σ : K ≃+* K) (hk : Nat.card (descentField σ) = 3) :
    NonLocalized (subfieldProj (r := 2) σ).range := by
  classical
  obtain ⟨ℓ, hrK⟩ := CharP.exists K
  have hℓ : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let k : Subfield K := descentField σ
  have : Finite k := inferInstance
  have := Fintype.ofFinite k
  obtain ⟨f', -, hkf'⟩ := FiniteField.card k ℓ
  have hkf : Nat.card k = ℓ ^ (f' : ℕ) := by rw [Nat.card_eq_fintype_card, hkf']
  have hℓ3 : ℓ = 3 ∧ (f' : ℕ) = 1 := by
    have : ℓ ^ (f' : ℕ) = 3 := by rw [← hkf]; exact hk
    exact (Nat.Prime.pow_eq_iff Nat.prime_three).mp this
  have hk2 : ¬ (2 = 2 ∧ Nat.card (descentField σ) = 2) := fun h => by
    have := h.2
    omega
  refine nonLocalized_spSubfield_of_closing (by norm_num) σ hk2 (ℓ := ℓ) ?_
  intro s hs hsr V hV0 hVcomm hVexp hVnorm hfaith hup
  have : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩
  obtain ⟨m, hm, hSiegel, -, hupm⟩ :=
    sp_closing_data (by norm_num) σ hkf hs hsr V hV0 hVexp hVnorm hfaith hup
  have hf1 : (f' : ℕ) = 1 := hℓ3.2
  rw [hf1] at hSiegel
  have hm3 : 3 ≤ m := by simpa using hSiegel
  have hup' : m ≤ 3 ∨ (s = 2 ∧ m ≤ 4) := by
    rcases hupm with h | ⟨j, hj1, hj2⟩
    · left
      simpa using h
    · right
      have hj2' : 2 ≤ j := by omega
      have hs2 : 2 ≤ s := hs.two_le
      have h1 : s ^ 2 ≤ s ^ j := Nat.pow_le_pow_right (by omega) hj2'
      have h2 : s ^ 2 ≤ 4 := h1.trans (by simpa using hj1)
      have hs2' : s = 2 := by nlinarith
      subst hs2'
      have : 2 ^ j ≤ 4 := by simpa using hj1
      have hj3 : j ≤ 2 := by
        by_contra hcon
        have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact ⟨rfl, by omega⟩
  have hs3 : s ≠ 3 := fun h => hsr (h.trans hℓ3.1.symm)
  exact sp_two_three_closing k hk hs hs3 V hVexp hm hVnorm hfaith hm3 hup'

theorem nonLocalized_spSubfield_two_two (σ : K ≃+* K) (hk : Nat.card (descentField σ) = 2) :
    NonLocalized (subfieldProj (r := 2) σ).range := by
  classical
  obtain ⟨ℓ, hrK⟩ := CharP.exists K
  have hℓ : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let k : Subfield K := descentField σ
  have : Finite k := inferInstance
  have := Fintype.ofFinite k
  obtain ⟨f', -, hkf'⟩ := FiniteField.card k ℓ
  have hkf : Nat.card k = ℓ ^ (f' : ℕ) := by rw [Nat.card_eq_fintype_card, hkf']
  have hℓ2 : ℓ = 2 := by
    have : ℓ ^ (f' : ℕ) = 2 := by rw [← hkf]; exact hk
    exact ((Nat.Prime.pow_eq_iff Nat.prime_two).mp this).1
  have : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  let P := spProjData 2 K
  let φH : StatedSp 2 k →* StatedSp 2 K := subfieldSpHom 2 k
  have hrange : (P.π.comp φH).range = (subfieldProj (r := 2) σ).range := rfl
  rw [← hrange]
  refine P.nonLocalized_of_closing_sub φH (fun W hW => sp_irreducible k W hW)
    (commutator (StatedSp 2 k)) (isSimpleGroup_range_commutator_sp_two_two k hk)
    (fun x hx => centralizer_commutator_sp_two_two k hk x hx) ?_
  intro s hs hsr V hV0 hVcomm hVexp hVnorm hfaith hup
  have : Finite (StatedProj (StatedSp 2 K)) :=
    Finite.of_surjective (proj 2 K) (proj_surjective (r := 2) (K := K))
  have : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩
  have : Fact s.Prime := ⟨hs⟩
  have hVp : IsPGroup s V := by
    refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
    have h1 : orderOf g ∣ s := orderOf_dvd_of_pow_eq_one (Subtype.ext (hVexp g g.2))
    rcases (Nat.dvd_prime hs).mp h1 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hVp
  have hs2 : s ≠ 2 := hℓ2 ▸ hsr
  have hs3 : 3 ≤ s := by
    have := hs.two_le
    omega
  have hcard4 : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by
    rw [Fintype.card_sum, Fintype.card_fin]
  have hm3 : m ≤ 3 := by
    rcases hup with h | ⟨e, he, hdvd, hle⟩
    · rw [hm, hcard4] at h
      exact (Nat.pow_le_pow_iff_right hs.one_lt).mp h
    · rw [hm] at hdvd hle
      obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hs).mp hdvd
      rw [hcard4] at he
      have hj1 : j ≤ 1 := by
        by_contra hj
        have : s ^ 2 ≤ s ^ j := Nat.pow_le_pow_right (by omega) (by omega)
        have : 3 ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hs3 2
        omega
      have hmj : m ≤ 2 * j := by
        rw [← pow_mul, mul_comm] at hle
        exact (Nat.pow_le_pow_iff_right hs.one_lt).mp hle
      omega
  exact sp_two_two_closing k hk hs hs2 V hVexp hm hV0 (fun g _ v hv => hVnorm g v hv) hfaith hm3

theorem nonLocalized_spSubfield (hr : 2 ≤ r) (σ : K ≃+* K) :
    NonLocalized (subfieldProj (r := r) σ).range := by
  by_cases hne : r = 2 ∧ Nat.card (descentField σ) ≤ 3
  · obtain ⟨rfl, h3⟩ := hne
    have h2 : 1 < Nat.card (descentField σ) := Finite.one_lt_card
    rcases (by omega : Nat.card (descentField σ) = 2 ∨ Nat.card (descentField σ) = 3) with h | h
    · exact nonLocalized_spSubfield_two_two σ h
    · exact nonLocalized_spSubfield_two_three σ h
  · exact nonLocalized_spSubfield_generic hr σ hne

end CFSG.SignalizerFunctorTheorem.NonLocal
