module

public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.Quasithin.Background.G11BridgeG6

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section RestrictG6

variable {K : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem hypothesis61_restrict [Finite V] (hI : IsIrr K I) (hq : IsQuotientOfSQTKTauCeti ↥K)
    {a : GLV V} (ha : a ∈ K) (ha2 : a * a = 1) (htr : ∃ c : V, InducesTransvection a I c) :
    Hypothesis61 (restrictRange K I hI.1) (restrictEquiv a I (hI.1.conjSub_eq ha)) := by
  set h : conjSub a I = I := hI.1.conjSub_eq ha with hh
  obtain ⟨c, hc⟩ := htr
  obtain ⟨u, hu, hau⟩ := hc.2
  have hR : LinearMap.range (commMap a I h) ≠ ⊥ := by
    intro hbot
    have : commMap a I h ⟨u, hu⟩ ∈ LinearMap.range (commMap a I h) := ⟨⟨u, hu⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    apply hau
    exact sub_eq_zero.1 (congrArg Subtype.val this)
  have hfr := (inducesTransvection_iff_finrank h).1 ⟨c, hc⟩
  refine ⟨pCoreOf_eq_bot_of_isIrr_top (isIrr_restrictRange_top hI),
    isQuotientOfSQTKTauCeti_restrictRange hI.1 hq, restrictEquiv_mem_restrictRange hI.1 ha, ?_, ?_,
    ?_, ?_⟩
  · intro h1
    apply hau
    have := congrArg (fun e : ↥I ≃ₗ[ZMod 2] ↥I => ((e ⟨u, hu⟩ : ↥I) : V)) h1
    exact this
  · ext i
    show a (a (i : V)) = (i : V)
    have := congrArg (fun e : GLV V => e (i : V)) ha2
    exact this
  · exact hfr.le.trans (by norm_num)
  · set S := ⨆ g ∈ restrictRange K I hI.1, conjSub g (LinearMap.range (commMap a I h)) with hS
    have hinv : Invariant (restrictRange K I hI.1) S := invariant_iSup_conjSub _ _
    have hle : LinearMap.range (commMap a I h) ≤ S := by
      have := le_iSup₂_of_le (f := fun g (_ : g ∈ restrictRange K I hI.1) =>
        conjSub g (LinearMap.range (commMap a I h))) 1 (Subgroup.one_mem _) (conjSub_one _).ge
      exact this
    rcases (isIrr_restrictRange_top hI).eq_bot_or_eq hinv le_top with h0 | h1
    · exfalso
      rw [h0, le_bot_iff] at hle
      exact hR hle
    · exact h1

end RestrictG6

end G11

end CFSG.Quasithin
