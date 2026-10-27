module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Weak
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab2Main
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7SysAll

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab2

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

omit [Finite D] in
theorem exists_move_conj {H : Subgroup D} {z t g₀ g g' : D} (hg : g ∈ H) (hg' : g' ∈ H)
    (hz : g * z * g⁻¹ = g₀⁻¹ * t * g₀) (hne : g' * z * g'⁻¹ ≠ z) :
    ∃ k ∈ conjSub g₀ H, k * t * k⁻¹ ≠ t := by
  refine ⟨g₀ * (g * g' * g⁻¹) * g₀⁻¹, ?_, fun hfix => hne ?_⟩
  · rw [mem_conjSub]
    have e : g₀⁻¹ * (g₀ * (g * g' * g⁻¹) * g₀⁻¹) * g₀ = g * g' * g⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hg hg') (H.inv_mem hg)
  · have h1 : (g * g' * g⁻¹) * (g * z * g⁻¹) * (g * g' * g⁻¹)⁻¹ = g * z * g⁻¹ := by
      rw [hz]
      have e : (g * g' * g⁻¹) * (g₀⁻¹ * t * g₀) * (g * g' * g⁻¹)⁻¹ =
          g₀⁻¹ * ((g₀ * (g * g' * g⁻¹) * g₀⁻¹) * t * (g₀ * (g * g' * g⁻¹) * g₀⁻¹)⁻¹) * g₀ := by
        group
      rw [e, hfix]
    have h2 : g * (g' * z * g'⁻¹) * g⁻¹ = g * z * g⁻¹ := by
      calc g * (g' * z * g'⁻¹) * g⁻¹ = (g * g' * g⁻¹) * (g * z * g⁻¹) * (g * g' * g⁻¹)⁻¹ := by
            group
        _ = g * z * g⁻¹ := h1
    exact mul_left_cancel (mul_right_cancel h2)

theorem exists_move_of_mem (h : TwoSys A B z V c V₂) (γ : CosetGeom (A ⊔ B) A B) {t : D}
    (ht : t ∈ Nm A B V V₂ γ) (ht1 : t ≠ 1) : ∃ g ∈ stab γ, g * t * g⁻¹ ≠ t := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  cases hv : vtype γ with
  | false =>
    obtain ⟨g₀, rfl⟩ := exists_smul_eq_γ₀ hv
    rw [Nm_smul hA hB, Nm_γ₀ hA, mem_conjSub] at ht
    have ht1' : (g₀ : D)⁻¹ * t * g₀ ≠ 1 := fun e => ht1 (by
      calc t = (g₀ : D) * ((g₀ : D)⁻¹ * t * g₀) * (g₀ : D)⁻¹ := by group
        _ = 1 := by rw [e]; group)
    obtain ⟨g, hgA, hg⟩ := GoldAmL3.exists_conj_eq_of_mem h.gold h.nat ht ht1'
    obtain ⟨g', hg'A, hg'⟩ := exists_move_of_natural h.nat
    obtain ⟨k, hk, hkt⟩ := exists_move_conj hgA hg'A hg hg'
    refine ⟨k, ?_, hkt⟩
    rw [stab_smul, stab_γ₀ le_sup_left]
    exact hk
  | true =>
    obtain ⟨g₀, rfl⟩ := exists_smul_eq_γ₁ hv
    rw [Nm_smul hA hB, Nm_γ₁ hB, mem_conjSub] at ht
    have ht1' : (g₀ : D)⁻¹ * t * g₀ ≠ 1 := fun e => ht1 (by
      calc t = (g₀ : D) * ((g₀ : D)⁻¹ * t * g₀) * (g₀ : D)⁻¹ := by group
        _ = 1 := by rw [e]; group)
    have hn₂' : IsNaturalAt B (B ⊓ A) c V₂ := by
      have := h.nat₂
      rwa [inf_comm] at this
    obtain ⟨g, hgB, hg⟩ := GoldAmL3.exists_conj_eq_of_mem h.gold.symm hn₂' ht ht1'
    obtain ⟨g', hg'B, hg'⟩ := exists_move_of_natural h.nat₂
    obtain ⟨k, hk, hkt⟩ := exists_move_conj hgB hg'B hg hg'
    refine ⟨k, ?_, hkt⟩
    rw [stab_smul, stab_γ₁ le_sup_right]
    exact hk

theorem fx_moved (h : TwoSys A B z V c V₂) {γ δ : CosetGeom (A ⊔ B) A B}
    (hadj : (graph (A ⊔ B) A B).Adj γ δ) {t : D} (ht : t ∈ Fx V V₂ γ δ) (ht1 : t ≠ 1) {g : D}
    (hg : g ∈ stab γ) (hc : g * t * g⁻¹ = t) : g ∈ stab δ := by
  have hE := goodE0_all h hadj
  set C : Subgroup D := stab γ ⊓ Subgroup.centralizer ({t} : Set D) with hC
  have hEC : stab γ ⊓ stab δ ≤ C := by
    refine le_inf inf_le_left fun u hu => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ((mem_Fx.mp ht).2 u hu).symm
  have hCH : C ≤ stab γ := inf_le_left
  have h1 := Subgroup.relIndex_mul_relIndex (stab γ ⊓ stab δ) C (stab γ) hEC hCH
  rw [hE.rel3] at h1
  have hb : C.relIndex (stab γ) ∣ 3 := ⟨(stab γ ⊓ stab δ).relIndex C, by rw [← h1]; ring⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hb with hb1 | hb3
  · exfalso
    obtain ⟨g', hg'st, hg'⟩ := exists_move_of_mem h γ (mem_Fx.mp ht).1 ht1
    apply hg'
    have hg'C : g' ∈ C := (Subgroup.relIndex_eq_one.mp hb1) hg'st
    have h2 := Subgroup.mem_centralizer_iff.mp hg'C.2 t (Set.mem_singleton _)
    calc g' * t * g'⁻¹ = (t * g') * g'⁻¹ := by rw [← h2]
      _ = t := by group
  · rw [hb3] at h1
    have h3 : (stab γ ⊓ stab δ).relIndex C = 1 := by omega
    have hCT : C ≤ stab γ ⊓ stab δ := Subgroup.relIndex_eq_one.mp h3
    have hgC : g ∈ C := by
      refine ⟨hg, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (mul_eq_of_conj_eq hc).symm
    exact (hCT hgC).2

end GoldAmLab7

end F6

end CFSG.Quasithin
