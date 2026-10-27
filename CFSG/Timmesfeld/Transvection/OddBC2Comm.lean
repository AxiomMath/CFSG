module

public import CFSG.Timmesfeld.Transvection.OddLocal
public import CFSG.Timmesfeld.Transvection.OddModelHeis
import CFSG.Timmesfeld.Transvection.RankThreeA2Coords

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.UniquenessCase CFSG.LieType.BorelTits
open CFSG.Timmesfeld.Transvection.Pres
open CFSG.LieType.Universal.Unitary.SUExtras (toStd_last_odd)
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r} {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem SURelations.HasFrameImages.commute_map_suHeis_short
    {R : SURelations r (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsFrame Δ P Q) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k)
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k) {i : Fin r} (hik : i ≠ k)
    (u v c : F) :
    Commute (θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v))
        (R.ξ (Sum.inl k) (Sum.inr i) c) ∧
      Commute (θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v))
        (R.ξ (Sum.inl k) (Sum.inl i) c) ∧
      Commute (θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v))
        (R.ξ (Sum.inl i) (Sum.inl k) c) := by
  obtain ⟨h1, h2⟩ :=
    IsFrame.commuting_map_heis_shortRootGroup h hML hq hF hFn hcard hθr hθt hθb hik
  have h3 : toStd 3 (Pi.single (0 : Fin (3 / 2)) 1) = wt (Sum.inl (0 : Fin (3 / 2))) :=
    (toStd_last_odd (k := (0 : Fin (3 / 2))) (n := 3) (by decide) (by decide)).trans
      (weight_crd (m := 3) (Sum.inl (0 : Fin (3 / 2))))
  have hb : θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
      (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v) ∈
      (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ :=
    Subgroup.mem_map_of_mem θ
      (suHeis_mem (unitaryInvolution_involutive hFn)
        (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) h3 u v)
  have hm1 : R.ξ (Sum.inl k) (Sum.inr i) c ∈
      shortRootGroup Δ (P k) (Q k) (Q i) (P i) :=
    (hR.short (Sum.inl k) (Sum.inr i) hik.symm (R.ξ (Sum.inl k) (Sum.inr i) c)).2 ⟨c, rfl⟩
  have hm2 : R.ξ (Sum.inl k) (Sum.inl i) c ∈
      shortRootGroup Δ (P k) (Q k) (P i) (Q i) :=
    (hR.short (Sum.inl k) (Sum.inl i) hik.symm (R.ξ (Sum.inl k) (Sum.inl i) c)).2 ⟨c, rfl⟩
  have hm3 : R.ξ (Sum.inl i) (Sum.inl k) c ∈
      shortRootGroup Δ (P k) (Q k) (P i) (Q i) := by
    rw [← shortRootGroup_swap_pairs (P k) (Q k) (P i) (Q i)]
    exact (hR.short (Sum.inl i) (Sum.inl k) hik (R.ξ (Sum.inl i) (Sum.inl k) c)).2 ⟨c, rfl⟩
  exact ⟨h1 _ hb _ hm1, h2 _ hb _ hm2, h2 _ hb _ hm3⟩

end CFSG.Timmesfeld.Transvection
