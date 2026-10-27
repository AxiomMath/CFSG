module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab6Nm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmLab6

variable {D : Type*} [Group D] [Finite D] {H K : Subgroup D} {w' : D} {M' : Subgroup D}

theorem not_pCoreOf_le (h : GoldHyp H K) (hT : Nat.card ↥(H ⊓ K) ≠ 2) :
    ¬ pCoreOf 2 H ≤ pCoreOf 2 K := by
  intro hle
  have hne := h.pCoreOf_ne hT
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 H) (pCoreOf 2 K) (H ⊓ K) hle
    h.pCoreOf_right_le
  rw [h.relIndex_pCoreOf_T_left, h.relIndex_pCoreOf_T_right] at h1
  have h2 : (pCoreOf 2 H).relIndex (pCoreOf 2 K) = 1 := by omega
  exact hne (le_antisymm hle (Subgroup.relIndex_eq_one.mp h2))

theorem inv_mul_mem_pCoreOf (h : GoldHyp H K) {u₁ u₂ : D} (h1 : u₁ ∈ H ⊓ K) (h2 : u₂ ∈ H ⊓ K)
    (n1 : u₁ ∉ pCoreOf 2 H) (n2 : u₂ ∉ pCoreOf 2 H) : u₁⁻¹ * u₂ ∈ pCoreOf 2 H :=
  index_two_inv_mul_mem h.relIndex_pCoreOf_T_left h1 h2 n1 n2

theorem eq_one_or_of_centralizes (h : GoldHyp H K) (hn : IsNaturalAt K (H ⊓ K) w' M') {y : D}
    (hy : y ∈ M') (hc : ∀ t ∈ K ⊓ H, y * t = t * y) : y = 1 ∨ y = w' := by
  obtain ⟨a, ha1, haw, hset⟩ := hn.basis
  have hy' : y ∈ ({1, w', a, w' * a} : Set D) := hset ▸ hy
  have hw : ∀ t ∈ H ⊓ K, t * w' = w' * t := fun t ht =>
    Subgroup.mem_centralizer_iff.mp hn.z_mem.2 t ht
  have key : ∃ t ∈ K ⊓ H, a * t ≠ t * a := by
    by_contra hall
    push Not at hall
    have hT : K ⊓ H ≤ pCoreOf 2 K := by
      intro t ht
      rw [← hn.centralizer_eq]
      refine ⟨ht.1, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have hx' : x ∈ ({1, w', a, w' * a} : Set D) := hset ▸ hx
      have htT : t ∈ H ⊓ K := by rw [inf_comm]; exact ht
      rcases hx' with rfl | rfl | rfl | rfl
      · simp
      · exact (hw t htT).symm
      · exact hall t ht
      · calc w' * a * t = w' * (a * t) := by group
          _ = w' * (t * a) := by rw [hall t ht]
          _ = (w' * t) * a := by group
          _ = (t * w') * a := by rw [hw t htT]
          _ = t * (w' * a) := by group
    have : (pCoreOf 2 K).relIndex (H ⊓ K) = 1 := by
      rw [Subgroup.relIndex_eq_one]
      rwa [inf_comm]
    rw [h.relIndex_pCoreOf_T_right] at this
    omega
  obtain ⟨t, htT, hta⟩ := key
  have htT' : t ∈ H ⊓ K := by rw [inf_comm]; exact htT
  rcases hy' with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd (hc t htT) hta
  · exfalso
    apply hta
    have h1 := hc t htT
    have h2 := hw t htT'
    have : w' * (a * t) = w' * (t * a) := by
      calc w' * (a * t) = w' * a * t := by group
        _ = t * (w' * a) := h1
        _ = (t * w') * a := by group
        _ = (w' * t) * a := by rw [h2]
        _ = w' * (t * a) := by group
    exact mul_left_cancel this

theorem mem_of_centralizes (h : GoldHyp H K) (hn : IsNaturalAt K (H ⊓ K) w' M')
    (hmove : ∃ g ∈ H, g * w' * g⁻¹ ≠ w') {g : D} (hg : g ∈ H) (hc : g * w' * g⁻¹ = w') :
    g ∈ K := by
  set C : Subgroup D := H ⊓ Subgroup.centralizer ({w'} : Set D) with hC
  have hTC : H ⊓ K ≤ C := by
    refine le_inf inf_le_left fun t ht => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (Subgroup.mem_centralizer_iff.mp hn.z_mem.2 t ht).symm
  have hCH : C ≤ H := inf_le_left
  have h1 := Subgroup.relIndex_mul_relIndex (H ⊓ K) C H hTC hCH
  rw [h.relIndex_left] at h1
  have hb : C.relIndex H ∣ 3 := ⟨(H ⊓ K).relIndex C, by rw [← h1]; ring⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hb with hb1 | hb3
  · exfalso
    obtain ⟨g', hg'H, hg'⟩ := hmove
    have hg'C : g' ∈ C := (Subgroup.relIndex_eq_one.mp hb1) hg'H
    apply hg'
    have h2 := Subgroup.mem_centralizer_iff.mp hg'C.2 w' (Set.mem_singleton _)
    calc g' * w' * g'⁻¹ = (w' * g') * g'⁻¹ := by rw [← h2]
      _ = w' := by group
  · rw [hb3] at h1
    have h3 : (H ⊓ K).relIndex C = 1 := by omega
    have hCT : C ≤ H ⊓ K := Subgroup.relIndex_eq_one.mp h3
    have hgC : g ∈ C := by
      refine ⟨hg, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (mul_eq_of_conj_eq hc).symm
    exact (hCT hgC).2

end GoldAmLab6

end F6

end CFSG.Quasithin
