module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.Quasithin.H13.KG14726

open Equiv Equiv.Perm Subgroup

theorem card_mulAut_alternatingGroup {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (MulAut (alternatingGroup (Fin n))) = n.factorial := by
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  rw [← Nat.card_congr (Equiv.ofBijective _ hb), Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end CFSG.Quasithin.H13.KG14726

end
