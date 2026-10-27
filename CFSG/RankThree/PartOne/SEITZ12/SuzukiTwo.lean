module

public import CFSG.RankThree.PartOne.SEITZ12.Defs
public import CFSG.LieType.Ree.LargeReeInvolutionFusionCoords

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

@[expose] def zTwo (m : ℕ) (K : Type) [Field K] :
    Subgroup (ModGL F4.tag K) :=
  Subgroup.closure (Set.range fun c : K => sylowB m K 0 c)

section Sigma

variable {m : ℕ} {K : Type} [Field K]

theorem phi4s_sigma_add [CharP K 2] (x y : K) :
    largeReeSigma m (x + y) = largeReeSigma m x + largeReeSigma m y := by
  have e : 2 * 2 ^ m = 2 ^ (m + 1) := by ring
  simp only [largeReeSigma, e]
  exact add_pow_char_pow x y 2 (m + 1)

theorem phi4s_exists_sigma_mul_eq [Finite K] (hK : Nat.card K = 2 ^ (2 * m + 1)) (c : K) :
    ∃ b : K, largeReeSigma m b * b = c := by
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 ^ (2 * m + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨n, hn⟩ : ∃ n, 2 * 2 ^ m = n + 1 :=
    ⟨2 * 2 ^ m - 1, by have := Nat.one_le_two_pow (n := m); omega⟩
  have hsq : n * (n + 1 + 1) + 1 = 2 * Fintype.card K := by
    have h1 : (n + 1) ^ 2 = 2 * 2 ^ (2 * m + 1) := by
      rw [← hn]
      ring
    rw [hq]
    nlinarith [h1]
  have hpos : 1 ≤ Fintype.card K := Fintype.card_pos
  refine ⟨c ^ n, ?_⟩
  rw [largeReeSigma, hn, ← pow_succ, ← pow_mul]
  have hN : n * (n + 1 + 1) = Fintype.card K - 1 + Fintype.card K := by
    generalize n * (n + 1 + 1) = N at hsq ⊢
    omega
  rw [hN]
  by_cases hc : c = 0
  · subst hc
    rw [zero_pow]
    omega
  · rw [pow_add, FiniteField.pow_card_sub_one_eq_one c hc, FiniteField.pow_card, one_mul]

end Sigma

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

omit [Finite K]
  in
theorem phi4s_largeReeCoord_zero_mul (c c' : K) :
    largeReeCoord m K 0 c * largeReeCoord m K 0 c' = largeReeCoord m K 0 (c + c') := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have h2 := F4_two_eq_zero (K := K)
  simp only [largeReeCoord]
  rw [largeReeP_mul h2]
  simp [largeReeSigma_zero, phi4s_sigma_add]

omit [Finite K]
  in
theorem phi4s_sylowB_zero_mul (c c' : K) :
    sylowB m K 0 c * sylowB m K 0 c' = sylowB m K 0 (c + c') := by
  rw [sylowB_eq_largeReeCoord, sylowB_eq_largeReeCoord, sylowB_eq_largeReeCoord]
  exact phi4s_largeReeCoord_zero_mul c c'

omit [Finite K]
  in
theorem phi4s_sylowB_zero_sq (c : K) : sylowB m K 0 c * sylowB m K 0 c = 1 := by
  have h2 := F4_two_eq_zero (K := K)
  rw [phi4s_sylowB_zero_mul, show c + c = 0 by linear_combination c * h2, sylowB_zero_zero]

omit [Finite K]
  in
theorem mem_zTwo_iff (g : ModGL F4.tag K) : g ∈ zTwo m K ↔ ∃ c : K, g = sylowB m K 0 c := by
  constructor
  · intro hg
    change g ∈ Subgroup.closure (Set.range fun c : K => sylowB m K 0 c) at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨c, rfl⟩
    | one => exact ⟨0, sylowB_zero_zero.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := hy
      exact ⟨c + c', phi4s_sylowB_zero_mul c c'⟩
    | inv x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨c, inv_eq_of_mul_eq_one_right (phi4s_sylowB_zero_sq c)⟩
  · rintro ⟨c, rfl⟩
    exact Subgroup.subset_closure ⟨c, rfl⟩

theorem phi4s_sylowB_mul (hK : Nat.card K = 2 ^ (2 * m + 1)) (b c b' c' : K) :
    sylowB m K b c * sylowB m K b' c' =
      sylowB m K (b + b') (c + c' + largeReeSigma m b * b') := by
  rw [sylowB_eq_largeReeCoord, sylowB_eq_largeReeCoord, sylowB_eq_largeReeCoord]
  exact largeReeCoord_mul hK b c b' c'

theorem phi4s_sylowB_sq (hK : Nat.card K = 2 ^ (2 * m + 1)) (b c : K) :
    sylowB m K b c * sylowB m K b c = sylowB m K 0 (largeReeSigma m b * b) := by
  have h2 := F4_two_eq_zero (K := K)
  rw [phi4s_sylowB_mul hK, show b + b = 0 by linear_combination b * h2,
    show c + c + largeReeSigma m b * b = largeReeSigma m b * b by linear_combination c * h2]

theorem phi4s_zTwo_le (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    zTwo m K ≤ F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩ := by
  intro g hg
  obtain ⟨c, rfl⟩ := (mem_zTwo_iff g).1 hg
  exact sylowB_mem_U2 hK 0 c

theorem phi4s_card_zTwo (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Nat.card (zTwo m K) = 2 ^ (2 * m + 1) := by
  let f : K → zTwo m K := fun c => ⟨sylowB m K 0 c, (mem_zTwo_iff _).2 ⟨c, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun c c' h => ?_, fun g => ?_⟩
    · exact (sylowB_injective hK (congrArg Subtype.val h)).2
    · obtain ⟨c, hc⟩ := (mem_zTwo_iff g.1).1 g.2
      exact ⟨c, Subtype.ext hc.symm⟩
  rw [← hK]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem phi4s_card_U₂ (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Nat.card (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) = (2 ^ (2 * m + 1)) ^ 2 := by
  have h := Nat.card_congr ((bijOn_largeReeCoord hK).equiv _)
  rw [Nat.card_univ, Nat.card_prod, hK] at h
  rw [sq, h]
  rfl

theorem suzukiTwo_U₂ (_hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    SuzukiTwo (2 ^ (2 * m + 1)) (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) (zTwo m K) := by
  have hU : ∀ s ∈ F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩, ∃ b c : K, s = sylowB m K b c :=
    fun s hs => by
      obtain ⟨b, c, h⟩ := exists_largeReeCoord_eq hK hs
      exact ⟨b, c, by rw [sylowB_eq_largeReeCoord, h]⟩
  refine ⟨phi4s_zTwo_le hK, phi4s_card_U₂ hK, phi4s_card_zTwo hK, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨b, c, rfl⟩ := hU s hs
    rw [phi4s_sylowB_sq hK]
    exact (mem_zTwo_iff _).2 ⟨_, rfl⟩
  · intro z hz hz1
    obtain ⟨c, rfl⟩ := (mem_zTwo_iff z).1 hz
    obtain ⟨b, hb⟩ := phi4s_exists_sigma_mul_eq (m := m) hK c
    exact ⟨sylowB m K b 0, sylowB_mem_U2 hK b 0, by rw [phi4s_sylowB_sq hK, hb]⟩
  · intro s hs hs1
    obtain ⟨b, c, rfl⟩ := hU s hs
    rw [phi4s_sylowB_sq hK, ← sylowB_zero_zero (m := m) (K := K)] at hs1
    have h0 := (sylowB_injective hK hs1).2
    have hb : b = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact (largeReeSigma_eq_zero_iff b).1 h
      · exact h
    subst hb
    exact (mem_zTwo_iff _).2 ⟨c, rfl⟩
  · intro z hz
    obtain ⟨c, rfl⟩ := (mem_zTwo_iff z).1 hz
    exact phi4s_sylowB_zero_sq c
  · intro z hz s hs
    obtain ⟨c, rfl⟩ := (mem_zTwo_iff z).1 hz
    obtain ⟨b, c', rfl⟩ := hU s hs
    exact sylowB_zero_commute hK c b c'

end CFSG.RankThree.PartOne.SEITZ12
