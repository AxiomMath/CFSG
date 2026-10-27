module

public import CFSG.Quasithin.Background.P4InspectStmt
public import CFSG.Quasithin.Background.P4InspEndPerm
public import CFSG.Quasithin.Background.P4InspEndAbs
public import CFSG.Quasithin.Background.P4InspEndF4

public section

namespace CFSG.Quasithin.G11

open CFSG.Quasithin.G11.P4InspEnd

theorem inspectSylowEnd : InspectSylowEnd := by
  intro U _ _ _ f M K Q v hd _ hdata P hP
  rcases hdata with ha | ⟨-, -, hL⟩ | hc | hc8
  ·
    obtain ⟨φ, ψ, hψ⟩ := p4inspend_a5_module ha
    refine ⟨?_, ?_, φ, ψ, hψ⟩
    · rw [ψ.finrank_eq, finrank_permCore_five]
    · have hP4 : Nat.card ↥(P : Subgroup ↥K) = 4 := p4inspend_card_sylow_five φ P
      have hQP : ∀ q ∈ Q, ∃ s ∈ (P : Subgroup ↥K), ((s : ↥K) : GLV U) = q :=
        p4inspend_Q_le K Q (P : Subgroup ↥K) φ
          (fun r hr => p4inspend_centralizer_a5 φ ψ hψ r hr)
          (fun q hq k hk => hd.K_norm q (hd.Q_le hq) k hk) hd.Q_comm hd.Q_sq hP
          (by rw [hP4]; norm_num)
      have hbij : Function.Bijective
          (fun s : ↥(P : Subgroup ↥K) => (⟨((s : ↥K) : GLV U), hP s s.2⟩ : ↥Q)) := by
        constructor
        · intro s t hst
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun q : ↥Q => ((q : ↥Q) : GLV U)) hst
        · intro q
          obtain ⟨s, hs, hsq⟩ := hQP q q.2
          exact ⟨⟨s, hs⟩, Subtype.ext hsq⟩
      rw [← Nat.card_eq_of_bijective _ hbij, hP4]
  ·
    exfalso
    obtain ⟨⟨e⟩, ω, hω, hωc⟩ := hL
    obtain ⟨hv0, hvp, hFT⟩ := hd.Q_trans
    let P₁ : Subgroup (GLV U) := (P : Subgroup ↥K).map K.subtype
    have hPQ : P₁ ≤ Q := by
      rintro _ ⟨s, hs, rfl⟩
      exact hP s hs
    have hPsp : P₁ ≤ spSub f := by
      rintro _ ⟨s, hs, rfl⟩
      exact hd.M_le (hd.K_le s.2)
    have hPω : ∀ p ∈ P₁, p * ω = ω * p := by
      rintro _ ⟨s, hs, rfl⟩
      exact hωc s s.2
    have hP3 : 2 < Nat.card ↥P₁ := by
      rw [Subgroup.card_map_of_injective K.subtype_injective, p4inspend_card_sylow_five e P]
      norm_num
    exact p4inspend_f4_false f hd.symp v hv0 hvp Q P₁ hPQ hPsp hFT.1 ω hω hPω hP3
  ·
    exfalso
    obtain ⟨φ, -⟩ := hc
    have : Finite ↥K := Finite.of_equiv _ φ.symm.toEquiv
    obtain ⟨x₀, hx4, hx2⟩ := p4inspend_alt_order4 (n := 6) (Or.inl rfl)
    refine p4inspend_no_order4 P (fun s hs => ?_) (φ.symm x₀) ?_ ?_
    · apply Subtype.ext
      exact hd.Q_sq _ (hP s hs)
    · rw [← map_pow, hx4, map_one]
    · intro h
      apply hx2
      have := congrArg φ h
      rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
  ·
    exfalso
    obtain ⟨φ, -⟩ := hc8
    have : Finite ↥K := Finite.of_equiv _ φ.symm.toEquiv
    obtain ⟨x₀, hx4, hx2⟩ := p4inspend_alt_order4 (n := 8) (Or.inr rfl)
    refine p4inspend_no_order4 P (fun s hs => ?_) (φ.symm x₀) ?_ ?_
    · apply Subtype.ext
      exact hd.Q_sq _ (hP s hs)
    · rw [← map_pow, hx4, map_one]
    · intro h
      apply hx2
      have := congrArg φ h
      rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this

end CFSG.Quasithin.G11
