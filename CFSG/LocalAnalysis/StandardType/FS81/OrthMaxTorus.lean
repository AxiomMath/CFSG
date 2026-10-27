module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCAbs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute

open QuadraticMap Module CFSG.Open CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
open scoped commutatorElement

theorem fs81_orth_maxElemAb3_eq_torus
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (htype : IsPlusType Q ↔ Even n)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEΩ : E ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hE : IsElemAbelian 3 E)
    (hmax : ∀ E' : Subgroup (V ≃ₗ[ZMod 2] V),
      E' ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      IsElemAbelian 3 E' → E ≤ E' → E' = E) :
    ∃ l : List (V × V), IsFrame Q l ∧ l.length = n ∧ E = torus Q l := by
  have hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hEΩ.trans (Subgroup.commutator_le_self _)
  obtain ⟨l, hl, hEl⟩ := exists_frame_top hQ hEO hE
  have hEq : E = torus Q l :=
    (hmax (torus Q l) (torus_le_commutator hl) (torus_isElemAbelian hl) hEl).symm
  have hno : ¬ ∃ a b : V, a ∈ perpL Q l ∧ b ∈ perpL Q l ∧ MinusPair Q a b := by
    rintro ⟨a, b, ha, hb, hp⟩
    have hperp : ∀ q ∈ l, PairPerp Q (a, b) q := by
      intro q hq
      obtain ⟨h1, h2⟩ := (mem_perpL_iff l a).1 ha q hq
      obtain ⟨h3, h4⟩ := (mem_perpL_iff l b).1 hb q hq
      exact ⟨by rw [polar_comm]; exact h1, by rw [polar_comm]; exact h2,
        by rw [polar_comm]; exact h3, by rw [polar_comm]; exact h4⟩
    have hl' : IsFrame Q ((a, b) :: l) := IsFrame.cons hp hperp hl
    have hEl' : E ≤ torus Q ((a, b) :: l) := by
      rw [hEq]
      exact torus_mono (fun q hq => List.mem_cons_of_mem _ hq)
    have hEqL : torus Q ((a, b) :: l) = E :=
      hmax _ (torus_le_commutator hl') (torus_isElemAbelian hl') hEl'
    have h1 : Nat.card E = 3 ^ l.length := by rw [hEq, card_torus hl]
    have h2 : Nat.card E = 3 ^ (l.length + 1) := by
      rw [← hEqL, card_torus hl', List.length_cons]
    rw [h1] at h2
    exact absurd h2 (ne_of_lt (Nat.pow_lt_pow_right (by norm_num)
      (Nat.lt_succ_self _)))
  have hle2 := hl.finrank_perpL_le hQ hno
  have hPd : finrank (ZMod 2) (perpL Q l) = 2 * n - 2 * l.length := by
    rw [perpL, LinearMap.BilinForm.finrank_orthogonal hQ, hdim, hl.finrank_Wspan]
  have hWle : finrank (ZMod 2) (Wspan l) ≤ finrank (ZMod 2) V := Submodule.finrank_le _
  rw [hl.finrank_Wspan, hdim] at hWle
  have hs : l.length = n ∨ l.length + 1 = n := by omega
  rcases hs with hsn | hsn
  · exact ⟨l, hl, hsn, hEq⟩
  · exfalso
    have hV0 : finrank (ZMod 2) (perpL Q l) = 2 := by rw [hPd]; omega
    have hplus : IsPlusType (Q.comp (perpL Q l).subtype) :=
      isPlusType_of_no_minusPair hV0 hno
    have htypeW : IsPlusType Q ↔ Even l.length := by
      by_cases h0 : l.length = 0
      · obtain rfl : l = [] := List.length_eq_zero_iff.mp h0
        have hperp_top : perpL Q ([] : List (V × V)) = ⊤ := by
          rw [eq_top_iff]
          intro x _
          rw [mem_perpL_iff]
          simp
        have hQplus : IsPlusType Q :=
          (isPlusType_congr (Q := Q.comp (perpL Q ([] : List (V × V))).subtype) (Q' := Q)
            { toLinearEquiv := LinearEquiv.ofTop _ hperp_top, map_app' := fun m => rfl }).1 hplus
        exact ⟨fun _ => ⟨0, rfl⟩, fun _ => hQplus⟩
      · have hd₁ : 1 ≤ l.length := Nat.one_le_iff_ne_zero.2 h0
        have horth : ∀ a ∈ Wspan l, ∀ b ∈ perpL Q l, polar Q a b = 0 := by
          intro a ha b hb
          have h := (LinearMap.BilinForm.mem_orthogonal_iff.1 hb) a ha
          rwa [QuadraticMap.polarBilin_apply_apply] at h
        have hkey := isPlusType_sup_iff (A := Wspan l) (B := perpL Q l) hl.isCompl.1 horth
          (nondeg_Wspan hl) (nondeg_comp_subtype (hl.perpL_nondeg hQ)) (d₁ := l.length)
          (d₂ := 1) hd₁ (le_refl 1) hl.finrank_Wspan (by rw [hV0, mul_one])
        have htop : Wspan l ⊔ perpL Q l = ⊤ := hl.isCompl.sup_eq_top
        have htopType : IsPlusType (Q.comp (Wspan l ⊔ perpL Q l).subtype) ↔ IsPlusType Q :=
          isPlusType_congr (Q := Q.comp (Wspan l ⊔ perpL Q l).subtype) (Q' := Q)
            { toLinearEquiv := LinearEquiv.ofTop _ htop, map_app' := fun m => rfl }
        have hkey2 : (IsPlusType (Q.comp (Wspan l).subtype) ↔
            IsPlusType (Q.comp (perpL Q l).subtype)) ↔
            IsPlusType (Q.comp (Wspan l).subtype) :=
          ⟨fun h => h.2 hplus, fun h => ⟨fun _ => hplus, fun _ => h⟩⟩
        exact ((htopType.symm.trans hkey).trans hkey2).trans (isPlusType_Wspan_iff hl)
    have h1 : Even l.length ↔ Even (l.length + 1) := by
      rw [hsn]
      exact htypeW.symm.trans htype
    rw [Nat.even_add_one] at h1
    by_cases hle : Even l.length
    · exact (h1.1 hle) hle
    · exact hle (h1.2 hle)

end CFSG.StandardType.FrameRoute

end
