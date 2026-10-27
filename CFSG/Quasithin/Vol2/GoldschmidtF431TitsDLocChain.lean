module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDLocV
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Gen

public section

namespace CFSG.Quasithin.H13.F431.TitsD

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.RuType
  CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru CFSG.Sporadic.Schreier.Tits CFSG.RuF45
  CFSG.TwoF4Lie CFSG.TwoF4Loc CFSG.TitsLoc CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false


theorem hne_of_col_D {b' : ↥titsD} (hb : ∃ q ∈ Col0, b'.1 q ≠ q) :
    ∀ h ∈ titsHD, h * tD * h⁻¹ ≠ b' := by
  intro h hh heq
  have hmem : ιD h ∈ twoF4M1 :=
    (mem_twoF4M1_iff _).2 (fix_zero_of_mem_titsH (Subgroup.mem_subgroupOf.1 hh))
  refine hne_of_col (b' := ιD b') hb (ιD h) hmem ?_
  have := congrArg ιD heq
  simpa [map_mul, map_inv, ιD_tD] using this

theorem pairChainD {a b : Equiv.Perm (Fin 1755) × Equiv.Perm (Fin 1755)}
    (h : Relation.ReflTransGen Certificates.c4182Pair a b) :
    ∀ x y x' y' : ↥titsD, x.1 = a.1 → y.1 = a.2 → x'.1 = b.1 → y'.1 = b.2 →
      Relation.ReflTransGen (PairLink titsSD titsHD titsND) (x, y) (x', y') := by
  induction h with
  | refl =>
    intro x y x' y' hx hy hx' hy'
    have e1 : x = x' := Subtype.ext (hx.trans hx'.symm)
    have e2 : y = y' := Subtype.ext (hy.trans hy'.symm)
    rw [e1, e2]
  | tail _ hbc ih =>
    intro x y x' y' hx hy hx' hy'
    obtain ⟨s1, s2, s1', s2', g, hgD, hg, e1, e2⟩ := hbc
    refine (ih x y ⟨_, s1.1⟩ ⟨_, s2.1⟩ hx hy rfl rfl).tail ⟨mem_titsSD s1, mem_titsSD s2,
      mem_titsSD (by rw [hx']; exact s1'), mem_titsSD (by rw [hy']; exact s2'), ⟨g, hgD⟩, ?_,
      Subtype.ext (hx'.trans e1), Subtype.ext (hy'.trans e2)⟩
    rcases hg with h | h
    · exact Or.inl (Subgroup.mem_subgroupOf.2 (mem_titsH_of hgD h))
    · exact Or.inr (Subgroup.mem_subgroupOf.2 (mem_titsN_of hgD h))

end CFSG.Quasithin.H13.F431.TitsD
