module

public import CFSG.Timmesfeld.Transvection.OddSU3Chord
public import CFSG.Timmesfeld.Transvection.FrameResidue
import CFSG.Timmesfeld.Transvection.OddLocal
import CFSG.Timmesfeld.Transvection.OddSU3Torus
import CFSG.Timmesfeld.Transvection.ShortRootProduct
import CFSG.Timmesfeld.Transvection.RankThreeA2Coords

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.UniquenessCase CFSG.LieType.BorelTits
open CFSG.Timmesfeld.Transvection.Pres

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r} {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem IsFrame.exists_eq_mul_mul_of_mem_map_heis_sup (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsFrame Δ P Q)
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθr : θ.range = residueGroup Δ P Q k)
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k) {i : Fin r} (hik : i ≠ k) {u : H}
    (hu : u ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)) :
    ∃ y ∈ shortRootGroup Δ (P k) (Q k) (Q i) (P i),
      ∃ z ∈ shortRootGroup Δ (P k) (Q k) (P i) (Q i),
        ∃ b ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ, u = y * z * b := by
  haveI := h.finite
  obtain ⟨b, hb, w, hw, hbw⟩ :=
    mem_sup_of_commuting (IsFrame.commuting_map_heis_sup h hML hq hF hFn hcard hθr hθt hθb hik) hu
  have hw' : w ∈ shortRootGroup Δ (Q i) (P i) (P k) (Q k) ⊔
      shortRootGroup Δ (P i) (Q i) (P k) (Q k) ⊔ P k := by
    simpa [shortRootGroup_swap_pairs (Q i) (P i) (P k) (Q k),
      shortRootGroup_swap_pairs (P i) (Q i) (P k) (Q k)] using hw
  obtain ⟨y, hy, z, hz, d, hd, hwd⟩ :=
    (hF.toPairFrame hik).exists_eq_mul_mul_of_mem_sup h.cls h.points
      (hq (P i) (hF.memP i)) hw'
  have hy' : y ∈ shortRootGroup Δ (P k) (Q k) (Q i) (P i) := by
    simpa [shortRootGroup_swap_pairs (Q i) (P i) (P k) (Q k)] using hy
  have hz' : z ∈ shortRootGroup Δ (P k) (Q k) (P i) (Q i) := by
    simpa [shortRootGroup_swap_pairs (P i) (Q i) (P k) (Q k)] using hz
  have hcomm :=
    IsFrame.commuting_map_heis_shortRootGroup h hML hq hF hFn hcard hθr hθt hθb hik
  have hPkB : P k ≤ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ := by
    rw [← hθt]
    exact Subgroup.map_mono (su3Top_le_X (unitaryInvolution_involutive hFn))
  refine ⟨y, hy', z, hz', b * d, Subgroup.mul_mem _ hb (hPkB hd), ?_⟩
  rw [← hbw, hwd]
  have hby : b * y = y * b := (hcomm.1 b hb y hy').eq
  have hbz : b * z = z * b := (hcomm.2 b hb z hz').eq
  calc b * (y * z * d)
      = (b * y) * (z * d) := by group
    _ = (y * b) * (z * d) := by rw [hby]
    _ = y * (b * z) * d := by group
    _ = y * (z * b) * d := by rw [hbz]
    _ = y * (z * (b * d)) := by group
    _ = y * z * (b * d) := by group

theorem IsFrame.conjSub_eq_of_mem_map_heis_sup (hΔ : IsTransvectionClass Δ)
    (hF : IsFrame Δ P Q) (hFn : Nat.card F = (2 ^ n) ^ 2)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k) {i : Fin r} (hik : i ≠ k) {u : H}
    (hu : u ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)) :
    conjSub (P k) u = P k := by
  rw [conjSub_eq_self_iff]
  have hsub : (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k) ≤
      Subgroup.normalizer (P k : Set H) := by
    refine sup_le ?_ (sup_le (sup_le ?_ ?_) ?_)
    · intro b hb
      exact conjSub_eq_self_iff.1
        (conjSub_eq_of_mem_map_heis (unitaryInvolution_involutive hFn) hθt hb)
    · refine ((commuting_iff_le_centralizer (A := P k)
        (B := shortRootGroup Δ (P k) (Q k) (Q i) (P i))).1 ?_).trans
        (Subgroup.centralizer_le_normalizer (P k : Set H))
      intro p hp y hy
      exact (commute_of_mem_lineGroup hΔ (hF.memP k) (hF.memQ i) (hF.commuting_PQ hik.symm)
        hy.1.1 (le_lineGroup (left_mem_lineOf (hF.memP k)) hp)).symm
    · refine ((commuting_iff_le_centralizer (A := P k)
        (B := shortRootGroup Δ (P k) (Q k) (P i) (Q i))).1 ?_).trans
        (Subgroup.centralizer_le_normalizer (P k : Set H))
      intro p hp y hy
      exact (commute_of_mem_lineGroup hΔ (hF.memP k) (hF.memP i) (hF.commuting_PP hik.symm)
        hy.1.1 (le_lineGroup (left_mem_lineOf (hF.memP k)) hp)).symm
    · exact Subgroup.le_normalizer
  exact hsub hu

theorem IsFrame.mem_map_heis_of_mem_sup_of_conjSub_eq (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsFrame Δ P Q)
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθr : θ.range = residueGroup Δ P Q k)
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k) {i : Fin r} (hik : i ≠ k) {u : H}
    (hu : u ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k))
    (huP : conjSub (P i) u = P i) (huQ : conjSub (Q i) u = Q i) :
    u ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ := by
  haveI := h.finite
  obtain ⟨b, hb, w, hw, hbw⟩ :=
    mem_sup_of_commuting (IsFrame.commuting_map_heis_sup h hML hq hF hFn hcard hθr hθt hθb hik) hu
  have hcomm : Commuting ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
      (P i ⊔ Q i) :=
    commuting_map_heis_of_ne (unitaryInvolution_involutive hFn) hθr hik
  have hbP : ∀ p ∈ P i, Commute b⁻¹ p := fun p hp =>
    (hcomm b hb p (Subgroup.mem_sup_left hp)).inv_left
  have hbQ : ∀ q ∈ Q i, Commute b⁻¹ q := fun q hq' =>
    (hcomm b hb q (Subgroup.mem_sup_right hq')).inv_left
  have hw_eq : w = b⁻¹ * u := by rw [← hbw]; group
  have hwP : conjSub (P i) w = P i := by
    rw [hw_eq, conjSub_mul, huP]
    exact conjSub_of_forall_commute hbP
  have hwQ : conjSub (Q i) w = Q i := by
    rw [hw_eq, conjSub_mul, huQ]
    exact conjSub_of_forall_commute hbQ
  have hw' : w ∈ shortRootGroup Δ (Q i) (P i) (P k) (Q k) ⊔
      shortRootGroup Δ (P i) (Q i) (P k) (Q k) ⊔ P k := by
    simpa [shortRootGroup_swap_pairs (Q i) (P i) (P k) (Q k),
      shortRootGroup_swap_pairs (P i) (Q i) (P k) (Q k)] using hw
  have hwPk : w ∈ P k :=
    (hF.toPairFrame hik).mem_of_mem_sup_of_conjSub_eq h.cls h.points
      (hq (P i) (hF.memP i)) hw' hwP hwQ
  have hPkB : P k ≤ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ := by
    rw [← hθt]
    exact Subgroup.map_mono (su3Top_le_X (unitaryInvolution_involutive hFn))
  rw [← hbw]
  exact Subgroup.mul_mem _ hb (hPkB hwPk)

end CFSG.Timmesfeld.Transvection
