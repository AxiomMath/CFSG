module

public import CFSG.Quasithin.EmptyFaithful.Insp9Cases3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace Insp9

variable {D : Type} [Group D] [Finite D] {D₁ D₂ J N : Subgroup D}

theorem case12_false (h : Data D₁ D₂ J N) (hs : B56Setting D N) (hsimple : IsSimpleGroup D)
    (hcard : Nat.card D = 95040) (hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ 6) : False := by
  have hN := h.N_eq_top_of_simple hsimple
  have hnc : ∃ a b : D, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative D := ⟨⟨fun a b => hcomm a b⟩⟩
    have hq : (Nat.card D).Prime := hsimple.prime_card
    rw [hcard] at hq
    norm_num at hq
  have hqs := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  have hqsN : CFSG.IsQuasisimple ↥N :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (topEquivOfEq hN).symm hqs
  have hql := hs.ql_of_quasisimple hqsN
  have h8 : ¬ 2 ^ 8 ∣ Nat.card ↥N := by
    rw [Nat.card_congr (topEquivOfEq hN).toEquiv]
    exact fun hd => h.not_two_pow_dvd (k := 6) hT (m := 7) (by norm_num)
      ((Nat.pow_dvd_pow 2 (by norm_num : 7 ≤ 8)).trans hd)
  have hord := b56QL_card_le7 hql h8
  rw [Nat.card_congr (topEquivOfEq hN).toEquiv, hcard] at hord
  revert hord
  decide +kernel

theorem card_extension_E4_Z4 {T : Type*} [Group T] [Finite T]
    (h : F6.IsExtensionOf T (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) : Nat.card T = 2 ^ 6 := by
  rw [h.card_eq, card_E4]
  have : Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) = 16 := by
    rw [Nat.card_prod]
    have : Nat.card (Multiplicative (ZMod 4)) = 4 := by
      rw [Nat.card_eq_fintype_card]; rfl
    rw [this]
  rw [this]
  norm_num

theorem inspCase12 :
    InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseTwelve H₁ H₂ := by
  intro D _ _ D₁ D₂ J N h hs hP
  have key : ∀ H₁ H₂ : Subgroup D, H₁ ⊓ H₂ = D₁ ⊓ D₂ → F6.IsF618CaseTwelve H₁ H₂ →
      InspGoal D N := by
    intro H₁ H₂ hHH hc
    obtain ⟨⟨e⟩, hT, -⟩ := hc
    have hT' : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ 6 := by
      rw [← hHH]
      exact card_extension_E4_Z4 hT
    have hsimple : IsSimpleGroup D :=
      have := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      e.isSimpleGroup
    have hcard : Nat.card D = 95040 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M12
    exact (case12_false h hs hsimple hcard hT').elim
  rcases hP with hP | hP
  · exact key D₁ D₂ rfl hP
  · exact key D₂ D₁ (inf_comm _ _) hP

end Insp9

end CFSG.Quasithin
