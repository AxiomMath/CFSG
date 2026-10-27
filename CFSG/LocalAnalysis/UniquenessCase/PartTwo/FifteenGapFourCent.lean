module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
import CFSG.LocalAnalysis.WeakClosure81.FiveSixOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s15GapFour_card_alt_five {X : Type} [Group X] (h : UC22.IsAlt X 5) :
    Nat.card X = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

private theorem s15GapFour_conj_injective {K : Type} [Group K] (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : a ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun f : MulAut K => f g) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    have h' : a * g = g * a := by
      calc a * g = (a * g * a⁻¹) * a := by group
        _ = g * a := by rw [h]
    exact h'.symm
  rw [hZ] at hmem
  exact Subgroup.mem_bot.1 hmem

private theorem s15GapFour_conj_range_normal {K : Type} [Group K] :
    (MulAut.conj : K →* MulAut K).range.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  refine ⟨g k, ?_⟩
  ext x
  simp [MulAut.conj_apply]

private theorem s15GapFour_centralizer_conj {K : Type} [Group K] (hZ : Subgroup.center K = ⊥)
    (φ : MulAut K) (h : ∀ s : K, φ * MulAut.conj s = MulAut.conj s * φ) : φ = 1 := by
  ext s
  have hs : s⁻¹ * φ s ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := φ.surjective y
    have h1 := congrArg (fun f : MulAut K => f x) (h s)
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at h1
    have h2 : φ s * φ x = s * φ x * s⁻¹ * φ s := by
      calc φ s * φ x = (φ s * φ x * (φ s)⁻¹) * φ s := by group
        _ = s * φ x * s⁻¹ * φ s := by rw [h1]
    calc φ x * (s⁻¹ * φ s) = s⁻¹ * (s * φ x * s⁻¹ * φ s) := by group
      _ = s⁻¹ * (φ s * φ x) := by rw [h2]
      _ = (s⁻¹ * φ s) * φ x := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hs
  simpa using hs.symm

theorem s15GapFour_pRank_mulAut_le_one (hAut : RAutRank153) {K : Type} [Group K] [Finite K]
    (hK : s15ListTwo K) (hZ : Subgroup.center K = ⊥) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (⊤ : Subgroup (MulAut K)) ≤ 1 :=
  ((hAut K (MulAut K) (MulAut.conj : K →* MulAut K) (s15GapFour_conj_injective hZ)
    s15GapFour_conj_range_normal (fun h hh => s15GapFour_centralizer_conj hZ h fun s => by
      have := hh s
      simpa using this)).1 hK).1 q hq hq2

theorem s15GapFour_centralizes_of_normalizes (hAut : RAutRank153) {A : Type} [Group A] [Finite A]
    {K : Subgroup A} (hK : s15ListTwo ↥K) (hZ : Subgroup.center ↥K = ⊥)
    {y : A} (hy : y ∈ normalizer (K : Set A)) {q : ℕ} (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card ↥K) (hyq : y ^ q = 1) : y ∈ centralizer (K : Set A) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set φ : MulAut ↥K := K.normalizerMonoidHom ⟨y, hy⟩ with hφ
  have hφq : φ ^ q = 1 := by
    rw [hφ, ← map_pow]
    have h1 : (⟨y, hy⟩ : normalizer (K : Set A)) ^ q = 1 := Subtype.ext (by simpa using hyq)
    rw [h1, map_one]
  by_cases hφ1 : φ = 1
  · have hker : (⟨y, hy⟩ : normalizer (K : Set A)) ∈ K.normalizerMonoidHom.ker :=
      MonoidHom.mem_ker.2 hφ1
    rw [Subgroup.normalizerMonoidHom_ker] at hker
    exact hker
  · exfalso
    have hord : orderOf φ = q := orderOf_eq_prime hφq hφ1
    have hdvd : q ∣ Nat.card (MulAut ↥K) := hord ▸ orderOf_dvd_natCard φ
    have hmain := hAut ↥K (MulAut ↥K) (MulAut.conj : ↥K →* MulAut ↥K)
      (s15GapFour_conj_injective hZ) s15GapFour_conj_range_normal
      (fun h hh => s15GapFour_centralizer_conj hZ h fun s => by
        have := hh s
        simpa using this)
    rcases hK with hL3 | hA5
    · have hc : Nat.card ↥K = 168 := WeakClosure81.card_eq_of_isL3 hL3
      rcases (hmain.1 (Or.inl hL3)).2.1 hL3 q hq hdvd with h | h | h
      all_goals (apply hqK; rw [hc]; subst h; norm_num)
    · have hc : Nat.card ↥K = 60 := s15GapFour_card_alt_five hA5
      rcases (hmain.1 (Or.inr hA5)).2.2 hA5 q hq hdvd with h | h | h
      all_goals (apply hqK; rw [hc]; subst h; norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
