module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Model
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Inner
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5UFrame
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UExc

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open

section UE6

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

theorem upper_twE6
    (hR : LangFamilyCompFieldSL) {ψ : (ggU .twistedE6 n f).K →* X}
    (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .twistedE6 f) (hp : p ≠ 3) : Nat.card B ≤ p ^ 4 := by
  have hp' := h.prime
  have hp2 := h.ne_two
  have hf : 1 ≤ f := h.adm.2.1
  obtain ⟨K, instF, instFin, σ, hK, hσ, ⟨θ'⟩⟩ := h.exists_twE6_rootGroup_equiv
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hTor : UToralAt .E6 p (Nat.card B) :=
    utoralAt_of_nonTorsion hp' hp2 (fun _ => hp) (fun h => by cases h) hBpos
  obtain ⟨t', m, f', hlt, hm, -⟩ := hF
  obtain ⟨Ψ, ρ, hΨ, -, hρ, horth, hcard, -⟩ := uframe_main_twE6
    (uFieldInput_of_SL hR (Or.inl rfl)) hf hp' hp2 hK σ hσ θ'
    h.b_norm (h.inner_twE6 (Or.inl hp)) h.b_faithful h.b_elem h.d_le h.d_card
    (h.j_comp.1.trans inf_le_left) (Assembly.isComponentOf_iff_open.1 h.j_comp) h.j_cent
    ⟨t', m, f', hlt, hm⟩ hTor
  have hr := e6_finrank_le_two hΨ hρ horth
  exact hcard.trans (Nat.pow_le_pow_right hp'.pos (by omega))

end UE6

end CFSG.StandardType.TableCRes

end
