module

public import CFSG.LocalAnalysis.StandardType.GGReeB2PairProbe
public import CFSG.LocalAnalysis.StandardType.GGReeB2PairQb
public import CFSG.LocalAnalysis.StandardType.GGReeB2PairFixed
public import CFSG.LocalAnalysis.StandardType.GGReeB2PairLines

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin.B45Sz
open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

private theorem na_inv_fixed_of_ub {K : Type} [Field K] {m : ℕ} {Γ : Type} [Group Γ]
    (k : Type) [Field k] {W : Type} [AddCommGroup W] [Module k W] (ρ : Representation k Γ W)
    (n : Γ) (ψ : suzukiGroup m K →* Γ) (Ub : Subgroup Γ) (w : W)
    (hw : ∀ u ∈ Ub, ρ u w = w) (x : suzukiGroup m K) (hconj : n * ψ x * n⁻¹ ∈ Ub) :
    ρ (ψ x) (ρ n⁻¹ w) = ρ n⁻¹ w := by
  have hbw : ρ (n * ψ x * n⁻¹) w = w := hw _ hconj
  have hbw' : (ρ n * ρ (ψ x) * ρ n⁻¹) w = w := by
    simpa only [map_mul] using hbw
  have hbw'' : ρ n (ρ (ψ x) (ρ n⁻¹ w)) = w := by
    simpa only [Module.End.mul_apply] using hbw'
  have hcancel : ρ n⁻¹ (ρ n (ρ (ψ x) (ρ n⁻¹ w))) = ρ (ψ x) (ρ n⁻¹ w) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hcongr := congrArg (ρ n⁻¹) hbw''
  rwa [hcancel] at hcongr

theorem theoremH {K : Type} [Field K] [CharP K 2] [Fintype K]
    {m : ℕ} {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k] [CharP k 2] [IsAlgClosed k]
    {W : Type} [AddCommGroup W] [Module k W] [Module.Finite k W] [Nontrivial W]
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (hC : CondH m) (𝔇 : SzPairDatum K m Γ)
    (ρ : Representation k Γ W) :
    ∃ v : W, v ≠ 0 ∧ ∀ l : Kˣ, ρ (𝔇.φ₂ (szD K m l)) v = v := by
  classical
  obtain ⟨v, lam, hv, hvU, hvlam⟩ := exists_U_fixed_weight k hK 𝔇 ρ
  have hlamwt : lam ∈ 𝔇.wt k ρ := by
    show weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k lam.1 lam.2) ≠ ⊥
    exact (Submodule.ne_bot_iff _).mpr ⟨v, hvlam, hv⟩
  by_cases hL : OnLines lam.1 lam.2
  · exact lines_fixed k hK 𝔇 ρ hlamwt hL
  · have h1 : lam.1 ≠ 0 := fun h => hL (Or.inl h)
    have h2 : lam.2 ≠ 0 := fun h => hL (Or.inr (Or.inl h))
    have hX₁ : ∀ x ∈ szUp m K, ρ (𝔇.φ₁ x) v = v := fun x hx => hvU _ (𝔇.up₁ x hx)
    have hX₂ : ∀ x ∈ szUp m K, ρ (𝔇.φ₂ x) v = v := fun x hx => hvU _ (𝔇.up₂ x hx)
    obtain ⟨I, J, hI, hJ, hIJ⟩ := hw_probe k hK 𝔇 ρ v hv hX₁ hX₂ lam hvlam h1 h2
    by_cases hadm : Admissible (2 * m + 1) I J
    · obtain ⟨κ, hκmem, hκ'⟩ := hC I J hadm
      obtain ⟨w, hwne, hwUb, hww⟩ := qb_probe k hK 𝔇 ρ v hv hvU lam hvlam h1 I hI κ hκmem
      have hna_mul : ρ 𝔇.na * ρ 𝔇.na⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      have hu_ne : ρ 𝔇.na⁻¹ w ≠ 0 := by
        intro h0
        have hw0 : w = 0 := by
          have hfix : (ρ 𝔇.na * ρ 𝔇.na⁻¹) w = w := by rw [hna_mul, Module.End.one_apply]
          rw [Module.End.mul_apply, h0, map_zero] at hfix
          exact hfix.symm
        exact hwne hw0
      have huX₁ : ∀ x ∈ szUp m K, ρ (𝔇.φ₁ x) (ρ 𝔇.na⁻¹ w) = ρ 𝔇.na⁻¹ w :=
        fun x hx => na_inv_fixed_of_ub k ρ 𝔇.na 𝔇.φ₁ 𝔇.Ub w hwUb x (𝔇.na_up₁ x hx)
      have huX₂ : ∀ x ∈ szUp m K, ρ (𝔇.φ₂ x) (ρ 𝔇.na⁻¹ w) = ρ 𝔇.na⁻¹ w :=
        fun x hx => na_inv_fixed_of_ub k ρ 𝔇.na 𝔇.φ₂ 𝔇.Ub w hwUb x (𝔇.na_up₂ x hx)
      have hna_wt : ρ 𝔇.na⁻¹ w ∈ weightSpace (ρ.comp 𝔇.tau)
          (wchar (K := K) k (sa m (κ, lam.2)).1 (sa m (κ, lam.2)).2) :=
        na_weight (κ := (κ, lam.2)) k hK 𝔇 ρ hww
      have hy : lam.2 ∈ wtSet m J := by rw [← hJ]; exact hw_mem_wtSet m J
      have hκL : ¬ OnLines κ lam.2 := not_onLines_of_admissible m hadm hκmem hy
      have hsaL : ¬ OnLines (sa m (κ, lam.2)).1 (sa m (κ, lam.2)).2 :=
        fun h => hκL ((onLines_sa_iff m κ lam.2).mp h)
      have hs1 : (sa m (κ, lam.2)).1 ≠ 0 := fun h => hsaL (Or.inl h)
      have hs2 : (sa m (κ, lam.2)).2 ≠ 0 := fun h => hsaL (Or.inr (Or.inl h))
      obtain ⟨I', J', hI', hJ', hIJ'⟩ :=
        hw_probe k hK 𝔇 ρ (ρ 𝔇.na⁻¹ w) hu_ne huX₁ huX₂ (sa m (κ, lam.2)) hna_wt hs1 hs2
      have hpair : (hw m I', hw m J') = sa m (κ, hw m J) := by
        rw [hI', hJ', hJ]
      have hnotadm : ¬ Admissible (2 * m + 1) I' J' := hκ' I' J' hpair
      obtain ⟨x', hx', y', hy', hxy'⟩ := exists_onLines_of_not_admissible m hnotadm
      exact lines_fixed k hK 𝔇 ρ (hIJ' x' hx' y' hy') hxy'
    · obtain ⟨x, hx, y, hy, hxy⟩ := exists_onLines_of_not_admissible m hadm
      exact lines_fixed k hK 𝔇 ρ (hIJ x hx y hy) hxy

end CFSG.StandardType.ReeB2Fixed
