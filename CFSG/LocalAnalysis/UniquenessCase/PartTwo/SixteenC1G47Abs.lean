module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47CaseB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47L3Final
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47OddNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Rank3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16c1_G47_comm_of_card_le_four {Hs : Type} [Group Hs] [Finite Hs] {Xs Vs : Subgroup Hs}
    (hX : IsSL2Prime ↥Xs 5) (hXV : ∀ x ∈ Xs, ∀ v ∈ Vs, x * v * x⁻¹ ∈ Vs)
    (hV4 : Nat.card ↥Vs ≤ 4) : ∀ v ∈ Vs, ∀ x ∈ Xs, v * x = x * v := by
  obtain ⟨hcard, hperf, -⟩ := s16c1_sl2five_facts hX
  haveI : Group.IsPerfect ↥Xs := Group.isPerfect_def.2 (by simpa [commutator_def] using hperf)
  have hnorm : Xs ≤ normalizer (Vs : Set Hs) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hXV x hx h hh, fun hh => ?_⟩
    have := hXV x⁻¹ (Xs.inv_mem hx) _ hh
    simpa [mul_assoc] using this
  intro v hv x hx
  have h := s16c1_G47_perfect_comm (X := Xs) (W := Vs) ‹Group.IsPerfect ↥Xs› hnorm hV4 x hx v hv
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem s16c1_G47_L3_card_le_abs {Hs : Type} [Group Hs] [Finite Hs] {Xs Ys Vs B : Subgroup Hs}
    (hO2 : CFSG.pCore 2 Hs = ⊥) (hY : Ys.Normal) (hXY : Xs ≤ Ys) (hX : IsSL2Prime ↥Xs 5)
    (hL3 : IsL3Five ↥Ys) (hHs : ∀ h : Hs, ∃ y ∈ Ys, ∃ b ∈ B, h = y * b)
    (hVB : ∀ b ∈ B, ∀ v ∈ Vs, b * v * b⁻¹ ∈ Vs) (hV2 : IsPGroup 2 Vs)
    (hV2' : ∀ v ∈ Vs, v * v = 1) (hVX : ∀ v ∈ Vs, ∀ x ∈ Xs, v * x = x * v) :
    Nat.card ↥Vs ≤ 2 :=
  s16c1_G47_L3five_card_le hY hL3 hXY hX hV2' hVX (s16c1_G47_cent_trivial hO2 hY hHs hVB hV2)

theorem s16c1_G47_odd_false {Hs : Type} [Group Hs] [Finite Hs] {Xs Ys Vs B : Subgroup Hs}
    (hO2 : CFSG.pCore 2 Hs = ⊥) (hr3 : CFSG.Open.pRank 3 (⊤ : Subgroup Hs) ≤ 1)
    (hY : Ys.Normal) (hXY : Xs ≤ Ys) (hX : IsSL2Prime ↥Xs 5)
    (hodd : EqTimesOdd Xs Ys) (hHs : ∀ h : Hs, ∃ y ∈ Ys, ∃ b ∈ B, h = y * b)
    (hVB : ∀ b ∈ B, ∀ v ∈ Vs, b * v * b⁻¹ ∈ Vs) (hV2 : IsPGroup 2 Vs)
    (hV2' : ∀ v ∈ Vs, v * v = 1) (hVX : ∀ v ∈ Vs, ∀ x ∈ Xs, v * x = x * v)
    {E : Type} [Group E] (hE : ∀ e : E, e * e = 1) (ρ : Hs →* MulAut E) {a : E} (ha : a ≠ 1)
    (hT : ∀ v ∈ Vs, ∀ e : E, ρ v e = e ∨ ρ v e = e * a)
    (hstab : ∀ r : Hs, ρ r a = a → ∀ v ∈ Vs, r * v * r⁻¹ ∈ Vs)
    (hα : ∃ v ∈ Vs, ρ v ≠ 1) : False := by
  classical
  obtain ⟨N, hNY, hNn, hNodd, hYeq⟩ := hodd
  obtain ⟨N₀, hN₀, hN₀odd, hNN₀, hN₀Y, hXN₀⟩ := s16c1_G47_oddNormal hY hXY hX hNY hNn hNodd
  have hX120 : Nat.card ↥Xs = 120 := (s16c1_sl2five_facts hX).1
  have h3 : ¬ 3 ∣ Nat.card ↥N₀ :=
    s16c1_G47_no_three hXY hN₀Y (Subgroup.Normal.subgroupOf hN₀ Ys) hXN₀
      (by rw [hX120]; norm_num) hr3
  have hVN : ∀ v ∈ Vs, (∀ n ∈ N₀, v * n = n * v) → v = 1 := by
    intro v hv hvN
    have hle : Ys ≤ centralizer ({v} : Set Hs) := by
      refine hYeq.le.trans (sup_le (fun x hx => ?_) (fun n hn => ?_))
      · exact Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff.1 hh]
          exact hVX v hv x hx
      · exact Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff.1 hh]
          exact hvN n (hNN₀ hn)
    exact s16c1_G47_cent_trivial hO2 hY hHs hVB hV2 v hv fun y hy =>
      Subgroup.mem_centralizer_iff.1 (hle hy) v (Set.mem_singleton v)
  exact s16c1_G47_caseB hN₀ hN₀odd hV2' hVN h3 hE ρ ha hT hstab hα

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
