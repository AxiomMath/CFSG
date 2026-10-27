module

public import CFSG.Quasithin.Background.E1Inherit

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b

variable {G : Type*} [Group G]

theorem IsE.mono {i j : ℕ} (hij : i ≤ j) {H T A K : Subgroup G} (h : IsE i H T A K) :
    IsE j H T A K := by
  obtain ⟨h1, h2, h3, h4 | h4⟩ := h
  · exact ⟨h1, h2, h3, Or.inl ⟨h4.1, h4.2.trans (Nat.pow_le_pow_right (by norm_num : 0 < 2) hij)⟩⟩
  · exact ⟨h1, h2, h3, Or.inr ⟨h4.1, h4.2.trans (Nat.pow_le_pow_right (by norm_num : 0 < 2) hij)⟩⟩

theorem IsE.isEAny {i : ℕ} {H T A K : Subgroup G} (h : IsE i H T A K) : IsEAny H T A K :=
  ⟨i, h⟩

theorem eGen_le (i : ℕ) (H T : Subgroup G) (Ω : Set (Subgroup G)) : eGen i H T Ω ≤ H :=
  iSup₂_le fun _ _ => iSup_le fun _ => iSup₂_le fun _ hK => hK.1

theorem eGen_mono {i j : ℕ} (hij : i ≤ j) (H T : Subgroup G) (Ω : Set (Subgroup G)) :
    eGen i H T Ω ≤ eGen j H T Ω := by
  refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
  exact le_iSup₂_of_le A hA (le_iSup_of_le hAT (le_iSup₂_of_le K (IsE.mono hij hK) le_rfl))

theorem eGen_mono_set (i : ℕ) (H T : Subgroup G) {Ω Ω' : Set (Subgroup G)} (h : Ω ⊆ Ω') :
    eGen i H T Ω ≤ eGen i H T Ω' := by
  refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
  exact le_iSup₂_of_le A (h hA) (le_iSup_of_le hAT (le_iSup₂_of_le K hK le_rfl))

theorem InEFor.mono {i j : ℕ} (hij : i ≤ j) {H T : Subgroup G} (h : InEFor i H T) :
    InEFor j H T := fun Ω hΩ =>
  le_antisymm (sup_le (eGen_le j H T Ω) inf_le_left)
    ((h Ω hΩ).symm.le.trans (sup_le_sup_right (eGen_mono hij H T Ω) _))

theorem InE.mono {i j : ℕ} (hij : i ≤ j) {H : Subgroup G} (h : InE i H) : InE j H :=
  fun T hT => InEFor.mono hij (h T hT)

theorem eq_bot_of_isSylowIn_odd [Finite G] {T H : Subgroup G} (hT : IsSylowIn 2 T H)
    (hH : Odd (Nat.card H)) : T = ⊥ := by
  have h2 : IsPGroup 2 T := hT.isPGroup
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h2
  have hdvd : Nat.card T ∣ Nat.card H := Subgroup.card_dvd_of_le hT.le
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hne
    have h2d : 2 ∣ Nat.card H := (dvd_pow_self 2 hne).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hH) (even_iff_two_dvd.mpr h2d)
  rw [hk0, pow_zero] at hk
  exact (Subgroup.card_eq_one).mp hk

theorem inEFor_of_odd [Finite G] {i : ℕ} {H T : Subgroup G} (hT : IsSylowIn 2 T H)
    (hH : Odd (Nat.card H)) : InEFor i H T := by
  intro Ω _
  have hTb : T = ⊥ := eq_bot_of_isSylowIn_odd hT hH
  have hW : weakClosure T Ω = ⊥ := by
    refine le_bot_iff.mp (iSup₂_le fun A _ => iSup_le fun hA => ?_)
    rw [hTb] at hA
    exact hA
  have hN : Subgroup.normalizer ((weakClosure T Ω : Subgroup G) : Set G) = ⊤ := by
    rw [hW]
    exact Subgroup.normalizer_eq_top_iff.mpr inferInstance
  rw [hN, inf_top_eq]
  exact sup_eq_right.mpr (eGen_le i H T Ω)

theorem inE_of_odd [Finite G] {i : ℕ} {H : Subgroup G} (hH : Odd (Nat.card H)) : InE i H :=
  fun _ hT => inEFor_of_odd hT hH

theorem nParam_le_iff [Finite G] {H : Subgroup G} {n : ℕ} (hn : 0 < n) :
    nParam H ≤ n ↔ InE n H := by
  unfold nParam
  by_cases hH : Odd (Nat.card H)
  · simp only [hH, ite_true, zero_le, true_iff]
    exact inE_of_odd hH
  · simp only [hH, ite_false]
    set S : Set ℕ := {i : ℕ | 0 < i ∧ InE i H} with hS
    constructor
    · intro h
      have hne : S.Nonempty := by
        by_contra hne
        rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne] at h
        simp at h
      rw [← ENat.natCast_sInf hne] at h
      have h1 : sInf S ≤ n := by exact_mod_cast h
      have h2 : sInf S ∈ S := Nat.sInf_mem hne
      exact InE.mono h1 h2.2
    · intro h
      exact iInf₂_le n ⟨hn, h⟩

theorem inEFor_of_generated [Finite G] {n : ℕ} {H T : Subgroup G} (hT : IsSylowIn 2 T H)
    {Δ : Set (Subgroup G)} (hΔ : ⨆ D ∈ Δ, D = H) (hTΔ : ∀ D ∈ Δ, T ≤ D)
    (hn : ∀ D ∈ Δ, InEFor n D T) : InEFor n H T := by
  intro Ω hΩ
  refine le_antisymm (sup_le (eGen_le n H T Ω) inf_le_left) ?_
  refine hΔ.ge.trans (iSup₂_le fun D hD => ?_)
  have hDH : D ≤ H := hΔ ▸ le_iSup₂ (f := fun D (_ : D ∈ Δ) => D) D hD
  have hTD : T ≤ D := hTΔ D hD
  have hTD' : IsSylowIn 2 T D := B6.isSylowTwoOf_mono hT hTD hDH
  set ΩD : Set (Subgroup G) := {A | A ∈ Ω ∧ A ≤ D} with hΩD
  have hΩD' : IsInvColl D ΩD := by
    refine ⟨fun A hA => hA.2, fun A hA => hΩ.isElemAbelian A hA.1, fun A hA d hd => ?_⟩
    refine ⟨hΩ.conj A hA.1 d (hDH hd), ?_⟩
    intro x hx
    have hx' := mem_conjSub_iff.mp hx
    have : d⁻¹ * x * d ∈ D := hA.2 hx'
    have hd' : d * (d⁻¹ * x * d) * d⁻¹ ∈ D := D.mul_mem (D.mul_mem hd this) (D.inv_mem hd)
    simpa [mul_assoc] using hd'
  have hWeq : weakClosure T ΩD = weakClosure T Ω := by
    refine le_antisymm (iSup₂_le fun A hA => iSup_le fun hAT => ?_) ?_
    · exact le_iSup₂_of_le A hA.1 (le_iSup_of_le hAT le_rfl)
    · refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
      exact le_iSup₂_of_le A ⟨hA, hAT.trans hTD⟩ (le_iSup_of_le hAT le_rfl)
  have hgen : eGen n D T ΩD ≤ eGen n H T Ω := by
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    have hK' : IsE n H T A K := by
      refine eight_two (H₁ := H) (H₂ := D) hT hAT (hΩ.isElemAbelian A hA.1) hDH
        ((tauOf_le H T A).trans (le_inf le_rfl hTD)) ?_ ?_
      · rw [inf_eq_left.mpr hTD]; exact hTD'
      · rw [inf_eq_left.mpr hTD]; exact hK
    exact le_iSup₂_of_le A hA.1 (le_iSup_of_le hAT (le_iSup₂_of_le K hK' le_rfl))
  have hDD := hn D hD ΩD hΩD'
  rw [hWeq] at hDD
  exact hDD.ge.trans (sup_le_sup hgen (inf_le_inf_right _ hDH))

end E1

end CFSG.Quasithin
