module

public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

public section

namespace CFSG.Quasithin

section Avg

universe u

theorem szN11_central_le {Γ : Type} {N : Type u} [Group Γ] [Finite Γ] [CommGroup N]
    (ψ : Γ →* MulAut N) {B : Subgroup Γ} (hB : ¬ 2 ∣ B.index) (hN2 : ∀ n : N, n ^ 2 = 1)
    {W Z : Subgroup N} (hBW : ∀ b ∈ B, ∀ w ∈ W, ψ b w ∈ W)
    (hZ : ∀ g : Γ, ∀ z ∈ Z, ψ g z = z) (hWZ : ∀ n : N, ∃ w ∈ W, ∃ z ∈ Z, n = w * z)
    (hcomm : ∀ {A : Type u} [CommGroup A] (ρ : N →* A), (∀ (g : Γ) (n : N), ρ (ψ g n) = ρ n) →
      ∀ n : N, ρ n = 1) :
    Z ≤ W := by
  classical
  let π : N →* N ⧸ W := QuotientGroup.mk' W
  have hπB : ∀ b ∈ B, ∀ n : N, π (ψ b n) = π n := by
    intro b hb n
    obtain ⟨w, hw, z, hz, rfl⟩ := hWZ n
    have h1 : ψ b (w * z) = ψ b w * z := by rw [map_mul, hZ b z hz]
    have h2 : π (ψ b w) = 1 := (QuotientGroup.eq_one_iff _).mpr (hBW b hb w hw)
    have h3 : π w = 1 := (QuotientGroup.eq_one_iff _).mpr hw
    rw [h1, map_mul, map_mul, h2, h3]
  have : Fintype (Γ ⧸ B) := Fintype.ofFinite _
  let ρ : N →* N ⧸ W := ∏ ω : Γ ⧸ B, π.comp (ψ (ω.out)⁻¹).toMonoidHom
  have hρ : ∀ n : N, ρ n = ∏ ω : Γ ⧸ B, π (ψ (ω.out)⁻¹ n) := by
    intro n
    simp [ρ, MonoidHom.finsetProd_apply]
  have hρinv : ∀ (g : Γ) (n : N), ρ (ψ g n) = ρ n := by
    intro g n
    rw [hρ, hρ]
    have key : ∀ ω : Γ ⧸ B, π (ψ (ω.out)⁻¹ (ψ g n)) = π (ψ (((g⁻¹ • ω : Γ ⧸ B).out)⁻¹) n) := by
      intro ω
      have hb : ((g⁻¹ • ω : Γ ⧸ B).out)⁻¹ * g⁻¹ * ω.out ∈ B :=
        CFSG.GroupTheory.ComplementLifting.out_inv_mul_mem g⁻¹ ω
      have e : (ω.out)⁻¹ * g = (((g⁻¹ • ω : Γ ⧸ B).out)⁻¹ * g⁻¹ * ω.out)⁻¹ * ((g⁻¹ • ω : Γ ⧸ B).out)⁻¹ := by
        group
      have e2 : ψ (ω.out)⁻¹ (ψ g n) = ψ ((ω.out)⁻¹ * g) n := by rw [map_mul]; rfl
      rw [e2, e, map_mul]
      exact hπB _ (B.inv_mem hb) _
    simp only [key]
    exact Fintype.prod_equiv (MulAction.toPerm (g⁻¹ : Γ)) (fun ω => π (ψ (((g⁻¹ • ω : Γ ⧸ B).out)⁻¹) n))
      (fun ω => π (ψ ((ω.out)⁻¹) n)) (fun _ => rfl)
  have hρtriv := hcomm ρ hρinv
  intro z hz
  have h1 : ρ z = π z ^ (Fintype.card (Γ ⧸ B)) := by
    rw [hρ]
    have : ∀ ω : Γ ⧸ B, π (ψ (ω.out)⁻¹ z) = π z := fun ω => by rw [hZ _ z hz]
    simp only [this, Finset.prod_const, Finset.card_univ]
  have h2 : ρ z = 1 := hρtriv z
  have hcard : Fintype.card (Γ ⧸ B) = B.index := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  have hodd : Fintype.card (Γ ⧸ B) % 2 = 1 := by
    rw [hcard]
    omega
  have h3 : π z ^ 2 = 1 := by rw [← map_pow, hN2 z, map_one]
  have h4 : π z ^ (Fintype.card (Γ ⧸ B)) = 1 := h1.symm.trans h2
  have hk : Fintype.card (Γ ⧸ B) = 2 * (Fintype.card (Γ ⧸ B) / 2) + 1 := by omega
  rw [hk, pow_succ, pow_mul, h3, one_pow, one_mul] at h4
  exact (QuotientGroup.eq_one_iff _).mp h4

theorem szN11_decomp {N : Type*} [CommGroup N] (σ : MulAut N) {m : ℕ} (hm : m % 2 = 1)
    (hσ : σ ^ m = 1) (hN2 : ∀ n : N, n ^ 2 = 1) {W : Subgroup N} (hW : ∀ n : N, σ n * n⁻¹ ∈ W) :
    ∀ n : N, ∃ w ∈ W, ∃ c : N, σ c = c ∧ n = w * c := by
  intro n
  let g : ℕ → N := fun i => (σ ^ i) n
  have hg0 : g 0 = n := by simp [g]
  have hgm : g m = n := by simp [g, hσ]
  have hgs : ∀ i, g (i + 1) = σ (g i) := fun i => by simp [g, pow_succ']
  let c : N := ∏ i ∈ Finset.range m, g i
  have hc : σ c = c := by
    have h1 : σ c = ∏ i ∈ Finset.range m, g (i + 1) := by
      simp only [c, map_prod, hgs]
    have h2 : (∏ i ∈ Finset.range m, g (i + 1)) * g 0 = (∏ i ∈ Finset.range m, g i) * g m := by
      rw [← Finset.prod_range_succ', Finset.prod_range_succ]
    rw [hg0, hgm] at h2
    rw [h1]
    exact mul_right_cancel h2
  have hgW : ∀ i, g i * n⁻¹ ∈ W := by
    intro i
    induction i with
    | zero => simp [hg0]
    | succ i ih =>
      have e : g (i + 1) * n⁻¹ = (σ (g i) * (g i)⁻¹) * (g i * n⁻¹) := by
        rw [hgs]; group
      rw [e]
      exact W.mul_mem (hW (g i)) ih
  have hnm : n ^ m = n := by
    have hk : m = 2 * (m / 2) + 1 := by omega
    rw [hk, pow_succ, pow_mul, hN2 n, one_pow, one_mul]
  have hw : n * c⁻¹ ∈ W := by
    have e : n * c⁻¹ = ∏ i ∈ Finset.range m, (n * (g i)⁻¹) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, hnm, Finset.prod_inv_distrib]
    rw [e]
    refine Subgroup.prod_mem _ fun i _ => ?_
    have : n * (g i)⁻¹ = (g i * n⁻¹)⁻¹ := by group
    rw [this]
    exact W.inv_mem (hgW i)
  exact ⟨n * c⁻¹, hw, c, hc, by group⟩

end Avg

end CFSG.Quasithin
