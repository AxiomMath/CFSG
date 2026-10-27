module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriKegel
public import CFSG.LieType.D4Small.NormalForm

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.LieType.D4Small

theorem NF.isNormalForm {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
    {D : D4Datum G K} {X : Type*} [AddCommGroup X] [Module K X] {ρ : Representation K G X}
    {j : ℕ} {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X}
    (h : NF D ρ j C b) : D.IsNormalForm ρ C j b where
  mem a ha := ⟨h.ne_zero a ha, h.mem_wtSpace a ha⟩
  span_eq := h.span_eq
  act := h.root

theorem nfIso_holds : NFIsoStatement := by
  intro G _ K _ _ _ D X X' _ _ _ _ ρ ρ' j C b b' hb hb'
  obtain ⟨e, -, he⟩ := hb.isNormalForm.exists_equiv hb'.isNormalForm
  exact ⟨e, he⟩

end CFSG.RankThree.GF2n.Stroth80.Tri
