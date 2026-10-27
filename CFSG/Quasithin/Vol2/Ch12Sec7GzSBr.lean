module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSLift
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSAb1

public section

namespace CFSG.Quasithin.H13.I1277

open Certificates.Data.S1277Struct Certificates.Data.S1277Cand Certificates.Data.S1277Bfs

structure KSetting {G : Type} [Group G] (H K Q : Subgroup G) (T : KTab) (κ : G → Nat) : Prop where
  hKH : K ≤ H
  hQK : Q ≤ K
  hQn : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q
  hQ2 : IsPGroup 2 ↥Q
  hQmax : ∀ X : Subgroup G, X ≤ H → (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) → IsPGroup 2 ↥X → X ≤ Q
  hC : ∀ h ∈ H, (∀ x ∈ Q, h * x = x * h) → h ∈ Q
  hodd : ¬ 2 ∣ K.relIndex H
  hne : ¬ H ≤ K
  hκ : KCod K T κ
  hinv : ModelInv T

section Branches

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {T : KTab} {κ : G → Nat}

theorem branch_nf (S : KSetting H K Q T κ) {N : List Nat}
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) (hnf : nfOK T N (phiList T N) = true) : False := by
  unfold nfOK at hnf
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.contains_iff_mem, decide_eq_true_eq] at hnf
  obtain ⟨x, hxK, hxN, hcomm⟩ := hnf
  obtain ⟨k, hk, hkx⟩ := S.hκ.surj x hxK
  subst hkx
  have hxN' : κ k ∉ N := by
    intro h
    have := List.contains_iff_mem.2 h
    rw [hxN] at this
    exact absurd this (by simp)
  have hkQ : k ∉ Q := fun h => hxN' ((hQN _).1 ⟨k, h, rfl⟩)
  have hPl : ∀ y ∈ phiList T N, ∃ r ∈ Phi' Q, κ r = y := by
    intro y hy
    unfold phiList at hy
    rw [mem_sortSet] at hy
    exact Phi'_codes_ge S.hκ S.hinv S.hQK hQN y hy
  have htriv : ∀ y ∈ Q, k * y * k⁻¹ * y⁻¹ ∈ Phi' Q := by
    intro y hy
    have hyK : y ∈ K := S.hQK hy
    obtain ⟨r, hr, hrκ⟩ := hPl _ (hcomm _ ((hQN _).1 ⟨y, hy, rfl⟩))
    have h1 : κ (k * y * k⁻¹ * y⁻¹) = commN T (κ k) (κ y) := S.hκ.comm S.hinv hk hyK
    have hmemK : k * y * k⁻¹ * y⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem hk hyK) (K.inv_mem hk)) (K.inv_mem hyK)
    have : k * y * k⁻¹ * y⁻¹ = r :=
      S.hκ.inj _ hmemK r (S.hQK (Phi'_le Q hr)) (by rw [h1, hrκ])
    rw [this]; exact hr
  exact hkQ (mem_of_trivial_action S.hQmax (S.hQK.trans S.hKH) S.hQn S.hQ2 S.hC (Phi'_le Q)
    (Phi'_normal S.hQn) (Phi'_frattini S.hQ2) (S.hKH hk) htriv)

end Branches

end CFSG.Quasithin.H13.I1277

end
