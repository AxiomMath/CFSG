module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre46e
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre42b

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}
variable {θ : ↥(Nor L) →* Perm (Fin 8)}

private theorem ofSix_commute_a8c :
    ∀ (σ : Perm (Fin 6)) (e : Bool),
      ofSix σ e * (a8c * a8d) = (a8c * a8d) * ofSix σ e → ofSix σ e ^ 8 = 1 →
      (ofSix σ e * a8c * (ofSix σ e)⁻¹ * a8c⁻¹) ^ 8 = 1 →
      ofSix σ e * a8c = a8c * ofSix σ e := by
  unfold a8c a8d
  decide +kernel

private theorem ofSix_commute_a8d :
    ∀ (σ : Perm (Fin 6)) (e : Bool),
      ofSix σ e * (a8c * a8d) = (a8c * a8d) * ofSix σ e → ofSix σ e ^ 8 = 1 →
      (ofSix σ e * a8d * (ofSix σ e)⁻¹ * a8d⁻¹) ^ 8 = 1 →
      ofSix σ e * a8d = a8d * ofSix σ e := by
  unfold a8c a8d
  decide +kernel

theorem comm_check_c : ∀ w : Perm (Fin 8), w * (a8c * a8d) = (a8c * a8d) * w → w ^ 8 = 1 →
    (w * a8c * w⁻¹ * a8c⁻¹) ^ 8 = 1 → w * a8c = a8c * w := by
  intro w hw h8 h1
  obtain ⟨σ, e, rfl⟩ :=
    exists_eq_ofSix (maps_pair_of_commute_of_fixed a8c_mul_a8d_apply_eq_self_iff hw)
  exact ofSix_commute_a8c σ e hw h8 h1

theorem comm_check_d : ∀ w : Perm (Fin 8), w * (a8c * a8d) = (a8c * a8d) * w → w ^ 8 = 1 →
    (w * a8d * w⁻¹ * a8d⁻¹) ^ 8 = 1 → w * a8d = a8d * w := by
  intro w hw h8 h1
  obtain ⟨σ, e, rfl⟩ :=
    exists_eq_ofSix (maps_pair_of_commute_of_fixed a8c_mul_a8d_apply_eq_self_iff hw)
  exact ofSix_commute_a8d σ e hw h8 h1

theorem comm_of_theta_comm (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) {β : G} (hβ : β ∈ L) (hβ3 : β ^ 3 = 1) (hθ : ThM L b₁ b₂ θ)
    {e : G} (heN : e ∈ Nor L) (hc : thG L θ e * thG L θ β = thG L θ β * thG L θ e) :
    e * β = β * e := by
  have hβN : β ∈ Nor L := Subgroup.le_normalizer hβ
  set u : G := e * β * e⁻¹ * β⁻¹ with hu
  have huL : u ∈ L := by
    have h1 : e * β * e⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 heN β).1 hβ
    exact mul_mem h1 (inv_mem hβ)
  have huN : u ∈ Nor L := Subgroup.le_normalizer huL
  have hth : thG L θ u = 1 := by
    rw [hu, thG_mul (mul_mem (mul_mem heN hβN) (inv_mem heN)) (inv_mem hβN),
      thG_conj heN hβN, thG_inv hβN, hc]
    group
  have huc : u ∈ CenS L := (hθ.ker u huN).1 hth
  have hu2 := Z_sq hA u huL huc
  have hub : u * β = β * u := (Subgroup.mem_centralizer_iff.1 huc β hβ).symm
  have hu3 : u ^ 3 = 1 := by
    have hconj : (e * β * e⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hβ3]; group
    have e1 : e * β * e⁻¹ = u * β := by rw [hu]; group
    rw [e1, (show Commute u β from hub).mul_pow, hβ3, mul_one] at hconj
    exact hconj
  have hu1 : u = 1 := by
    calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
      _ = 1 := by rw [hu3, hu2]; group
  calc e * β = (e * β * e⁻¹ * β⁻¹) * (β * e) := by group
    _ = β * e := by rw [← hu, hu1, one_mul]

theorem cenS_of_two_elements (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) {e : G} (heb : e ∈ Cen b)
    (he12 : e * (b₁ * b₂) = (b₁ * b₂) * e) {k k₁ k₂ : ℕ} (hk : e ^ 2 ^ k = 1)
    (hk₁ : (e * b₁ * e⁻¹ * b₁⁻¹) ^ 2 ^ k₁ = 1) (hk₂ : (e * b₂ * e⁻¹ * b₂⁻¹) ^ 2 ^ k₂ = 1) :
    e ∈ CenS B := by
  obtain ⟨θ, hθ⟩ := exists_thM hA h
  have heN : e ∈ Nor L := h.hyp.hLN heb
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
  have hb₁N : b₁ ∈ Nor L := Subgroup.le_normalizer hb₁L
  have hb₂N : b₂ ∈ Nor L := Subgroup.le_normalizer hb₂L
  have hg12 : thG L θ e * (a8c * a8d) = (a8c * a8d) * thG L θ e := by
    have := congrArg (thG L θ) he12
    rw [thG_mul heN (mul_mem hb₁N hb₂N), thG_mul hb₁N hb₂N, thG_mul (mul_mem hb₁N hb₂N) heN,
      thG_mul hb₁N hb₂N, hθ.c, hθ.d] at this
    exact this
  have hg8 : thG L θ e ^ 8 = 1 := by
    apply two_pow_perm8 (k := k)
    rw [← thG_pow heN, hk, thG_one]
  have hg₁ : (thG L θ e * a8c * (thG L θ e)⁻¹ * a8c⁻¹) ^ 8 = 1 := by
    apply two_pow_perm8 (k := k₁)
    have hN1 : e * b₁ * e⁻¹ * b₁⁻¹ ∈ Nor L :=
      mul_mem (mul_mem (mul_mem heN hb₁N) (inv_mem heN)) (inv_mem hb₁N)
    rw [← hθ.c, ← thG_inv heN, ← thG_inv hb₁N, ← thG_mul heN hb₁N,
      ← thG_mul (mul_mem heN hb₁N) (inv_mem heN),
      ← thG_mul (mul_mem (mul_mem heN hb₁N) (inv_mem heN)) (inv_mem hb₁N), ← thG_pow hN1, hk₁,
      thG_one]
  have hg₂ : (thG L θ e * a8d * (thG L θ e)⁻¹ * a8d⁻¹) ^ 8 = 1 := by
    apply two_pow_perm8 (k := k₂)
    have hN1 : e * b₂ * e⁻¹ * b₂⁻¹ ∈ Nor L :=
      mul_mem (mul_mem (mul_mem heN hb₂N) (inv_mem heN)) (inv_mem hb₂N)
    rw [← hθ.d, ← thG_inv heN, ← thG_inv hb₂N, ← thG_mul heN hb₂N,
      ← thG_mul (mul_mem heN hb₂N) (inv_mem heN),
      ← thG_mul (mul_mem (mul_mem heN hb₂N) (inv_mem heN)) (inv_mem hb₂N), ← thG_pow hN1, hk₂,
      thG_one]
  have hc₁ := comm_check_c _ hg12 hg8 hg₁
  have hc₂ := comm_check_d _ hg12 hg8 hg₂
  have e1 : e * b₁ = b₁ * e :=
    comm_of_theta_comm hA h hb₁L (pow3_of_mem h (mem_b₁ h)) hθ heN (by rw [hθ.c]; exact hc₁)
  have e2 : e * b₂ = b₂ * e :=
    comm_of_theta_comm hA h hb₂L (pow3_of_mem h (mem_b₂ h)) hθ heN (by rw [hθ.d]; exact hc₂)
  have e0 : e * b = b * e := (Subgroup.mem_centralizer_singleton_iff.1 heb)
  exact cenS_of_gens h e0 e1 e2

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
