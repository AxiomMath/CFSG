module

public import CFSG.Quasithin.Background.F8Basic

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup

variable {G : Type*} [Group G]

theorem le_normalizer_inf_of_sq_not_mem {L Q P D A : Subgroup G}
    (hLQ : L ≤ normalizer (Q : Set G)) (hLD : L ≤ normalizer (D : Set G))
    (hD : D ≤ P ⊓ Q) (hPL : P ≤ L) (hQP : Q ≤ normalizer (P : Set G))
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAP : ∀ a ∈ A, ∀ y ∈ P, a * y = y * a)
    (hPQ : P ⊓ Q ≤ A ⊔ D) {s : G} (hsP : s ∈ P) (hs2 : s ^ 2 ∉ Q)
    (hL : ∀ N : Subgroup G, N ≤ L → L ≤ normalizer (N : Set G) → ¬ N ≤ Q → N ⊔ Q = L) :
    L ≤ normalizer ((P ⊓ Q : Subgroup G) : Set G) := by
  have hsL : s ∈ L := hPL hsP
  have hAD : A ≤ normalizer (D : Set G) := fun a ha =>
    (Subgroup.centralizer_le_normalizer _)
      (Subgroup.mem_centralizer_iff.mpr fun d hd => (hAP a ha d (hD hd).1).symm)
  have hsq : ∀ u ∈ Q, s ^ 2 * u * (s ^ 2)⁻¹ * u⁻¹ ∈ D := by
    intro u hu
    have hkQ : s * u * s⁻¹ * u⁻¹ ∈ Q :=
      mul_mem ((mem_normalizer_iff.mp (hLQ hsL) u).mp hu) (inv_mem hu)
    have hkP : s * u * s⁻¹ * u⁻¹ ∈ P := by
      have h1 : u * s⁻¹ * u⁻¹ ∈ P := (mem_normalizer_iff.mp (hQP hu) _).mp (inv_mem hsP)
      have e : s * u * s⁻¹ * u⁻¹ = s * (u * s⁻¹ * u⁻¹) := by group
      rw [e]
      exact mul_mem hsP h1
    have hk : s * u * s⁻¹ * u⁻¹ ∈ ((A ⊔ D : Subgroup G) : Set G) := hPQ ⟨hkP, hkQ⟩
    rw [coe_mul_of_left_le_normalizer_right A D hAD] at hk
    obtain ⟨a, ha, d, hd, had⟩ := Set.mem_mul.mp hk
    have ha2 : a * a = 1 := by rw [← pow_two]; exact hA2 a ha
    have hdP : s * d * s⁻¹ ∈ D := (mem_normalizer_iff.mp (hLD hsL) d).mp hd
    have hsa : s * a * s⁻¹ = a := by
      rw [← hAP a ha s hsP]
      group
    have hw : s * u * s⁻¹ = a * d * u := by
      rw [had]
      group
    have e1 : s ^ 2 * u * (s ^ 2)⁻¹ * u⁻¹ =
        s * (s * u * s⁻¹ * u⁻¹) * s⁻¹ * (s * u * s⁻¹) * u⁻¹ := by
      rw [pow_two]
      group
    have e2 : s ^ 2 * u * (s ^ 2)⁻¹ * u⁻¹ = s * d * s⁻¹ * d := by
      rw [e1, ← had, hw]
      calc s * (a * d) * s⁻¹ * (a * d * u) * u⁻¹ = (s * a * s⁻¹) * (s * d * s⁻¹) * a * d := by
            group
        _ = a * (s * d * s⁻¹) * a * d := by rw [hsa]
        _ = (s * d * s⁻¹) * a * a * d := by rw [hAP a ha _ (hD hdP).1]
        _ = (s * d * s⁻¹) * (a * a) * d := by group
        _ = s * d * s⁻¹ * d := by rw [ha2]; group
    rw [e2]
    exact mul_mem hdP hd
  have hCL : centralizerMod D L Q ≤ L := centralizerMod_le_left D L Q
  have hLC : L ≤ normalizer ((centralizerMod D L Q : Subgroup G) : Set G) :=
    le_normalizer_centralizerMod hLD le_normalizer hLQ
  have hs2C : s ^ 2 ∈ centralizerMod D L Q :=
    ⟨pow_mem hsL 2, hLD (pow_mem hsL 2), hsq⟩
  have hCQ : centralizerMod D L Q ⊔ Q = L := hL _ hCL hLC fun h => hs2 (h hs2C)
  have hfwd : ∀ c ∈ centralizerMod D L Q, ∀ h ∈ P ⊓ Q, c * h * c⁻¹ ∈ P ⊓ Q := by
    intro c hc h hh
    have e : c * h * c⁻¹ = (c * h * c⁻¹ * h⁻¹) * h := by group
    rw [e]
    exact mul_mem (hD (hc.2.2 h hh.2)) hh
  have hCN : centralizerMod D L Q ≤ normalizer ((P ⊓ Q : Subgroup G) : Set G) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro h
    refine ⟨hfwd c hc h, fun hch => ?_⟩
    have := hfwd c⁻¹ (inv_mem hc) _ hch
    have e : c⁻¹ * (c * h * c⁻¹) * c⁻¹⁻¹ = h := by group
    rwa [e] at this
  have hQN : Q ≤ normalizer ((P ⊓ Q : Subgroup G) : Set G) := fun x hx =>
    inf_normalizer_le_normalizer_inf (mem_inf.mpr ⟨hQP hx, le_normalizer hx⟩)
  rw [← hCQ]
  exact sup_le hCN hQN

end CFSG.Quasithin.Stroth.Rq
