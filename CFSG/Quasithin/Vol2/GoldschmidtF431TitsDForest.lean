module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDSpec

public section

namespace CFSG.Quasithin.H13.F431.TitsD

open CFSG.Quasithin CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.RuType
  CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru CFSG.Sporadic.Schreier.Tits CFSG.RuF45
  CFSG.TwoF4Lie CFSG.TwoF4Loc CFSG.TitsLoc CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false


theorem invStepD_of_step {x y : Equiv.Perm (Fin 1755)} (h : Certificates.c4182Step x y)
    (hx : x ∈ titsD) (hy : y ∈ titsD) : InvStep titsSD titsHD titsND ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨hxS, hyS, g, hgD, hg, e⟩ := h
  refine ⟨mem_titsSD hxS, mem_titsSD hyS, ⟨g, hgD⟩, ?_, Subtype.ext e⟩
  rcases hg with h | h
  · exact Or.inl (Subgroup.mem_subgroupOf.2 (mem_titsH_of hgD h))
  · exact Or.inr (Subgroup.mem_subgroupOf.2 (mem_titsN_of hgD h))

theorem chainD_of_steps {a b : Equiv.Perm (Fin 1755)}
    (h : Relation.ReflTransGen Certificates.c4182Step a b) (ha : a ∈ titsD) :
    ∀ hb : b ∈ titsD,
      Relation.ReflTransGen (InvStep titsSD titsHD titsND) ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl => exact fun _ => Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    intro hc
    exact (ih hbc.1.1).tail (invStepD_of_step hbc _ hc)

theorem inv_chain_D : ∀ i ∈ titsSD, orderOf i = 2 →
    Relation.ReflTransGen (InvStep titsSD titsHD titsND) zD i ∨
      Relation.ReflTransGen (InvStep titsSD titsHD titsND) tD i := by
  obtain ⟨-, -, hch, -⟩ := Certificates.certificate4182
  intro i hi ho
  have h2 : i * i = 1 := by
    rw [← pow_two]
    exact ho ▸ pow_orderOf_eq_one i
  have h1 : i ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ho
    omega
  have htD : tD = ⟨Certificates.c4180T, by rw [← tEl_eq]; exact tD.2⟩ := Subtype.ext tEl_eq
  rcases hch i.1 (S_of_mem_titsS (Subgroup.mem_subgroupOf.1 hi)) (congrArg Subtype.val h2)
      (fun h => h1 (Subtype.ext h)) with h | h
  · exact Or.inl (chainD_of_steps h zD.2 i.2)
  · rw [htD]
    exact Or.inr (chainD_of_steps h _ i.2)

end CFSG.Quasithin.H13.F431.TitsD
