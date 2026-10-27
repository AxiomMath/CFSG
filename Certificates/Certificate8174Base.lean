
module

public import CFSG.RankThree.PartTwo.Toolkit.M12LocalGroups
import Certificates.Data.Kernel.M12Loc

@[expose] public section

namespace Certificates

open CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.KC.M12Loc Subgroup
open scoped commutatorElement

theorem card_of_tables8174 {K : Subgroup G12} {T : List (List ℕ)}
    (hT : ∀ g : G12, tbl g.1 ∈ T ↔ g ∈ K) (hs : ∀ t ∈ T, ∃ g : G12, tbl g.1 = t)
    (hnd : T.Nodup) : Nat.card K = T.length := by
  let f : K → {t // t ∈ T} := fun g => ⟨tbl g.1.1, (hT _).2 g.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun g h he => Subtype.ext (eq_iff_tbl.2 (congrArg Subtype.val he)), fun t => ?_⟩
    obtain ⟨g, hg⟩ := hs _ t.2
    exact ⟨⟨g, (hT g).1 (by rw [hg]; exact t.2)⟩, Subtype.ext hg⟩
  rw [Nat.card_eq_of_bijective f hf, ← Nat.card_congr (List.Nodup.getEquiv _ hnd),
    Nat.card_eq_fintype_card, Fintype.card_fin]

end Certificates
