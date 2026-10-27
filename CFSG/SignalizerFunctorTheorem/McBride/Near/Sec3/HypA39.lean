module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxFinal

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

theorem hypA6_of_centralizers_aux
    (n : ℕ) :
    ∀ {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {H A D D₁ D₂ E : Subgroup Γ},
      Nat.card ↥(H ⊔ A) = n → HypA15 p H A D D₁ D₂ → E ≤ A → Nat.card E = p ^ 2 →
      (∀ e ∈ E, e ≠ 1 → HypA6 (H ⊓ Subgroup.centralizer {e}) A D D₁ D₂) →
      (p = 3 → ∀ x ∈ D₁, ∃ k : ℕ, x ^ (5 ^ k) ∈ D₂) → HypA6 H A D D₁ D₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Γ _ _ p H A D D₁ D₂ E hn h hEA hE h6 h5
    by_contra hno
    refine L39.false_of_not_hypA6 ⟨h, hEA, hE, h6, h5, ?_, ?_⟩ hno
    · intro H' hH' hD hadm hne
      have hlt : Nat.card ↥(H' ⊔ A) < n := by
        rw [← hn]
        exact HypAAux.card_lt_of_ne (sup_le_sup_right hH' A) hne
      exact ih _ hlt rfl (h.restrict hH' hD hadm) hEA hE
        (fun e he he1 => (h6 e he he1).mono (inf_le_inf_right _ hH')) h5
    · intro M hMH hM hM0 hMD
      have hHn : H ≤ AChief.nrm M := le_sup_left.trans hM
      have hAn : A ≤ AChief.nrm M := le_sup_right.trans hM
      have hlt : Nat.card ↥(AChief.qimg M H ⊔ AChief.qimg M A) < n := by
        rw [← hn, ← SolQuot.qimg_sup hHn hAn]
        exact HypAAux.card_qimg_lt (hMH.trans le_sup_left) hM hM0
      have hcopM : Nat.Coprime p (Nat.card M) :=
        h.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hMH)
      refine ih _ hlt rfl (h.qimg hMH hM hMD) (SolQuot.qimg_mono hEA) ?_ ?_ ?_
      · rw [HypAAux.card_qimg_eq_of_coprime (hEA.trans hAn) (by
          rw [hE]
          exact (hcopM.symm).pow_right 2), hE]
      · intro e' he' he'1
        obtain ⟨y, hy, rfl⟩ := (AChief.mem_qimg_iff M E e').mp he'
        have hy1 : (y : Γ) ≠ 1 := fun h1 => he'1 (by
          rw [show y = 1 from Subtype.ext h1, map_one])
        have hyA : (y : Γ) ∈ A := hEA hy
        have hDC : D ≤ Subgroup.centralizer {(y : Γ)} := fun x hx =>
          Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp (h.D_le_centralizer hx) y hyA).symm
        have hAC : A ≤ Subgroup.centralizer {(y : Γ)} := fun a ha =>
          Subgroup.mem_centralizer_singleton_iff.mpr
            (commute_of_mem h.a1_elemAbelian.1 ha hyA).eq
        have hcen := HypAAux.qimg_inf_centralizer_singleton (N := M) h.prime h.a1_elemAbelian
          h.a1_admits hAn hHn h.coprime hyA
        have hHadm : Admits (D ⊔ A) H :=
          sup_le (h.D_le.trans Subgroup.le_normalizer) h.a1_admits
        have hadm₀ : Admits (D ⊔ A) (H ⊓ Subgroup.centralizer {(y : Γ)}) :=
          hHadm.inf (admits_centralizer_singleton (sup_le hDC hAC))
        have := HypA6.qimg_of_le h (inf_le_left : H ⊓ Subgroup.centralizer {(y : Γ)} ≤ H)
          (le_inf h.D_le hDC) hadm₀ (h6 y hy hy1) hMH hM hMD
        rwa [hcen] at this
      · intro hp3 x hx
        obtain ⟨y, hy, rfl⟩ := (AChief.mem_qimg_iff M D₁ x).mp hx
        obtain ⟨k, hk⟩ := h5 hp3 y hy
        refine ⟨k, (AChief.mem_qimg_iff M D₂ _).mpr ⟨y ^ (5 ^ k), hk, ?_⟩⟩
        rw [map_pow]

variable {G : Type*} [Group G]

theorem hypA6_of_centralizers
    [Finite G] {p : ℕ} {H A D D₁ D₂ : Subgroup G}
    (h : HypA15 p H A D D₁ D₂) {E : Subgroup G} (hEA : E ≤ A) (hE : Nat.card E = p ^ 2)
    (h6 : ∀ e ∈ E, e ≠ 1 → HypA6 (H ⊓ Subgroup.centralizer {e}) A D D₁ D₂)
    (h5 : p = 3 → ∀ x ∈ D₁, ∃ k : ℕ, x ^ (5 ^ k) ∈ D₂) :
    HypA6 H A D D₁ D₂ :=
  hypA6_of_centralizers_aux _ rfl h hEA hE h6 h5

end CFSG.SignalizerFunctorTheorem.McBride.Near
