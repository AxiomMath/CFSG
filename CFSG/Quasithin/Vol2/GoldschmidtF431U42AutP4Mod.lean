module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2That

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem outer_check : ∀ l ∈ Thl, l ∉ Tl → comp l l = idL →
    (Thl.filter fun m => comp m l == comp l m).length ≤ 32 := by
  decide +kernel

theorem card_cent_le {v : Ah} {vL : PL} (hv : RepL vL (v : P45))
    (h : (Thl.filter fun l => comp l vL == comp vL l).length ≤ 32) :
    Nat.card ↥(That ⊓ Subgroup.centralizer ({v} : Set Ah)) ≤ 32 := by
  classical
  set F := Thl.filter fun l => comp l vL == comp vL l with hF
  have hmem : ∀ g : ↥(That ⊓ Subgroup.centralizer ({v} : Set Ah)),
      permL ((g : Ah) : P45) ∈ F.toFinset := by
    intro g
    rw [List.mem_toFinset, hF, List.mem_filter]
    obtain ⟨hgT, hgC⟩ := g.2
    refine ⟨?_, ?_⟩
    · obtain ⟨l, hl, hrep⟩ := (mem_That_iff _).1 hgT
      rw [permL_eq_of_repL hrep]
      exact hl
    · have hc : (g : Ah) * v = v * g := Subgroup.mem_centralizer_singleton_iff.1 hgC
      have hc' : ((g : Ah) : P45) * (v : P45) = (v : P45) * ((g : Ah) : P45) :=
        congrArg Subtype.val hc
      have h1 := repL_mul (repL_permL ((g : Ah) : P45)) hv
      have h2 := repL_mul hv (repL_permL ((g : Ah) : P45))
      rw [← hc'] at h2
      simp only [beq_iff_eq]
      exact repL_unique h1 h2
  have hinj : Function.Injective fun g : ↥(That ⊓ Subgroup.centralizer ({v} : Set Ah)) =>
      (⟨permL ((g : Ah) : P45), hmem g⟩ : ↥F.toFinset) := by
    intro g₁ g₂ hg
    have h1 : permL ((g₁ : Ah) : P45) = permL ((g₂ : Ah) : P45) := congrArg Subtype.val hg
    have h2 : ((g₁ : Ah) : P45) = ((g₂ : Ah) : P45) :=
      eq_of_repL (repL_permL _) (h1 ▸ repL_permL _)
    exact Subtype.ext (Subtype.ext h2)
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h3 : Nat.card ↥F.toFinset = F.toFinset.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [h3] at h1
  exact h1.trans ((List.toFinset_card_le F).trans h)

end CFSG.Quasithin.H13.F431.U42Aut
