module

public import CFSG.LocalAnalysis.StandardType.GGKnownInputsNoU6Classical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

private theorem exists_model_of_marking_noJ1 {X : Type*} [Group X] {ℓ : LargeEvenLabel}
    (hc : ℓ.tag = .A ∨ ℓ.tag = .B ∨ ℓ.tag = .C ∨ ℓ.tag = .D)
    (h : LargeEvenMarking X fun lab' _ _ _ _ _ => lab' = ℓ) :
    1 ≤ ℓ.n ∧ ∃ (R : Type) (_ : Group R), Nonempty (X ⧸ Subgroup.center X ≃* R) ∧
      MarkedModel ℓ R := by
  obtain ⟨-, l, hl, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, rfl⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨R, _, I, F, ⟨-, -, θ, -⟩, hM⟩ := largeEvenRawDatum_exists
    (largeEvenLabelAll_markedModel_classical hl hc _ hraw)
  exact ⟨hl.1, R, _, ⟨θ⟩, hM⟩

theorem ordD_four_dvd_card_of_marking {X : Type*} [Group X] {n : ℕ}
    (hmark : LargeEvenMarking X fun lab' _ _ _ _ _ => lab' = ⟨.D, 4, n⟩) :
    1 ≤ n ∧ ordD 4 (2 ^ n) ∣ Nat.card X := by
  obtain ⟨hn, R, _, ⟨θ⟩, hM⟩ := exists_model_of_marking_noJ1
    (ℓ := ⟨.D, 4, n⟩) (Or.inr (Or.inr (Or.inr rfl))) hmark
  have hM' : LieModel R .POmegaPlus 4 2 n := by
    have h43 : ¬ ((4 : ℕ) = 3) := by decide
    simpa only [MarkedModel, markTag, markRank, markChar, markDeg, h43, if_false] using hM
  have hc : Nat.card R = ordD 4 (2 ^ n) :=
    CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hM'
  refine ⟨hn, ?_⟩
  rw [← hc, ← Nat.card_congr θ.toEquiv]
  exact Subgroup.card_quotient_dvd_card _

theorem ordA_two_dvd_card_of_marking {X : Type*} [Group X] {m : ℕ}
    (hmark : LargeEvenMarking X fun lab' _ _ _ _ _ => lab' = ⟨.A, 2, m⟩) :
    1 ≤ m ∧ ordA 2 (2 ^ m) ∣ Nat.card X := by
  obtain ⟨hm, R, _, ⟨θ⟩, hM⟩ := exists_model_of_marking_noJ1
    (ℓ := ⟨.A, 2, m⟩) (Or.inl rfl) hmark
  have hc : Nat.card R = ordA 2 (2 ^ m) :=
    CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide)
      (show LieModel R .PSL (2 + 1) 2 m from hM)
  refine ⟨hm, ?_⟩
  rw [← hc, ← Nat.card_congr θ.toEquiv]
  exact Subgroup.card_quotient_dvd_card _

private theorem card_largeEvenProj_SU_noJ1 {N n : ℕ} (hN : 1 ≤ N) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    1 ≤ n ∧ Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n))) =
      ordTwistedA N (2 ^ n) := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact h
  refine ⟨hn, ?_⟩
  change Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU (N + 1) (2 ^ n) K)) = _
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hn hK (by omega),
    CFSG.Open.ordTwistedA, Nat.add_sub_cancel, Nat.mul_comm (N + 1) N]

theorem ordTwistedA_dvd_card_of_twA_marking {X : Type*} [Group X] {N n : ℕ} (hN : 1 ≤ N)
    (hmark : LargeEvenMarking X fun lab' _ _ _ _ _ => lab' = ⟨.twA, N, n⟩) :
    1 ≤ n ∧ ordTwistedA N (2 ^ n) ∣ Nat.card X := by
  obtain ⟨-, lab', -, hraw⟩ := hmark
  obtain ⟨_, _, _, _, -, -, -, rfl⟩ := largeEvenRawDatum_exists hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K, _, _, hK, -, -, θ, -⟩ := hraw
  obtain ⟨hn, hc⟩ := card_largeEvenProj_SU_noJ1 hN hK
  refine ⟨hn, ?_⟩
  rw [← hc, ← Nat.card_congr θ.toEquiv]
  exact Subgroup.card_quotient_dvd_card _

theorem odd_of_three_dvd_two_pow_add_one_noJ1 {n : ℕ} (h : 3 ∣ 2 ^ n + 1) : Odd n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ho
  · have : 2 ^ (k + k) % 3 = 1 := by
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega
  · exact ho

theorem exists_label_disjunct_marking {X : Type*} [Group X] {S T : LargeEvenLabel → Prop}
    (h : LargeEvenMarking X fun l _ _ _ _ _ => S l ∨ T l) :
    LargeEvenMarking X (fun l _ _ _ _ _ => S l) ∨ LargeEvenMarking X (fun l _ _ _ _ _ => T l) := by
  obtain ⟨hX, l, hl, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, hST⟩ := largeEvenRawDatum_exists hraw
  rcases hST with hS | hT
  · exact Or.inl ⟨hX, l, hl,
      largeEvenRawDatum_mono (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, hS⟩) hraw⟩
  · exact Or.inr ⟨hX, l, hl,
      largeEvenRawDatum_mono (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, hT⟩) hraw⟩

theorem not_dvd_card_of_ne_top_arith {R : Type} [Group R] {N o : ℕ} (hN : 0 < N)
    (hcard : Nat.card R = N) (harith : ¬ o ∣ N ∨ N ≤ o) {J : Subgroup R} (hJ : J ≠ ⊤) :
    ¬ o ∣ Nat.card ↥J := by
  intro hdvd
  haveI : Finite R := Nat.finite_of_card_ne_zero (by omega)
  have hJN : Nat.card ↥J ∣ N := hcard ▸ Subgroup.card_subgroup_dvd_card J
  have hpos : 0 < Nat.card ↥J := Nat.card_pos
  have hidx := Subgroup.card_mul_index J
  rw [hcard] at hidx
  have h1 : J.index ≠ 1 := fun h => hJ (Subgroup.index_eq_one.1 h)
  have h0 : J.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases harith with h | h
  · exact h (hdvd.trans hJN)
  · have h2 := Nat.le_of_dvd hpos hdvd
    have h3 : Nat.card ↥J * 2 ≤ Nat.card ↥J * J.index := Nat.mul_le_mul_left _ (by omega)
    omega

theorem not_largeEvenMarking_D4_of_card {R : Type} [Group R] {N n : ℕ} (hN : 0 < N)
    (hcard : Nat.card R = N) (harith : 1 ≤ n → ¬ ordD 4 (2 ^ n) ∣ N ∨ N ≤ ordD 4 (2 ^ n))
    {J₁ : Subgroup R} (hJ : J₁ ≠ ⊤) :
    ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.D, 4, n⟩) := fun hmark => by
  obtain ⟨hn, hd⟩ := ordD_four_dvd_card_of_marking hmark
  exact not_dvd_card_of_ne_top_arith hN hcard (harith hn) hJ hd

theorem not_largeEvenMarking_A2_of_card {R : Type} [Group R] {N m : ℕ} (hN : 0 < N)
    (hcard : Nat.card R = N) (harith : 1 ≤ m → ¬ ordA 2 (2 ^ m) ∣ N ∨ N ≤ ordA 2 (2 ^ m))
    {J₁ : Subgroup R} (hJ : J₁ ≠ ⊤) :
    ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.A, 2, m⟩) := fun hmark => by
  obtain ⟨hm, hd⟩ := ordA_two_dvd_card_of_marking hmark
  exact not_dvd_card_of_ne_top_arith hN hcard (harith hm) hJ hd

theorem not_largeEvenMarking_twA2_of_card {R : Type} [Group R] {N m : ℕ} (hN : 0 < N)
    (hcard : Nat.card R = N)
    (harith : 1 ≤ m → ¬ ordTwistedA 2 (2 ^ m) ∣ N ∨ N ≤ ordTwistedA 2 (2 ^ m))
    {J₁ : Subgroup R} (hJ : J₁ ≠ ⊤) :
    ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 2, m⟩) := fun hmark => by
  obtain ⟨hm, hd⟩ := ordTwistedA_dvd_card_of_twA_marking (by norm_num) hmark
  exact not_dvd_card_of_ne_top_arith hN hcard (harith hm) hJ hd

theorem largeEvenLabelAll_noJ1_aPair_of_card {lab : LargeEvenLabel} {N : ℕ}
    (hcard : LargeEvenLabelAll lab fun R _ _ _ => Nat.card R = N) (hN : 0 < N)
    (harithA : ∀ n : ℕ, 1 ≤ n → Odd n → lab.n ∣ 3 * n →
      ¬ ordA 2 (2 ^ (3 * n)) ∣ N ∨ N ≤ ordA 2 (2 ^ (3 * n)))
    (harithT : ∀ n : ℕ, 1 ≤ n → Odd n → lab.n ∣ 3 * n →
      ¬ ordTwistedA 2 (2 ^ (3 * n)) ∣ N ∨ N ≤ ordTwistedA 2 (2 ^ (3 * n))) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → 3 ∣ 2 ^ n + 1 →
      lab.n ∣ 3 * n → ¬ LargeEvenMarking ↥J₁
        (fun lab' _ _ _ _ _ => lab' = ⟨.A, 2, 3 * n⟩ ∨ lab' = ⟨.twA, 2, 3 * n⟩) :=
  fun Q hQ => largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq.1, fun _ n hJ h3 hl hmark => by
    rcases exists_label_disjunct_marking hmark with hm | hm
    · exact not_largeEvenMarking_A2_of_card hN hq.2
        (fun h1 => harithA n (by omega) (odd_of_three_dvd_two_pow_add_one_noJ1 h3) hl) hJ hm
    · exact not_largeEvenMarking_twA2_of_card hN hq.2
        (fun h1 => harithT n (by omega) (odd_of_three_dvd_two_pow_add_one_noJ1 h3) hl) hJ hm⟩)
    (hcard Q hQ)

end CFSG.StandardType.SCFourCover

end
