module

public import CFSG.Quasithin.H13.GoldschmidtC137SQU33Card
public import CFSG.Quasithin.H13.GoldschmidtC137SQU3Inv
public import CFSG.Quasithin.H13.GoldschmidtC137SQMain

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

open CFSG.Blueprint CFSG.SectionRank

@[expose] def Simple168Catalog : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], Nat.card S = 168 → Catalog S

theorem u33KGroup_of_simple168 (h168 : Simple168Catalog) : U33KGroup := by
  intro Y _ _ h
  obtain ⟨hs, hcard⟩ := simple_card_of_lieModel_psu_three_three h
  have hnc := u3_no_comm_of_lieModel h
  refine isKGroupCat_of_simple (lieModel_catalog Y .PSU 3 3 1 h) fun H hH N _ hs' hnab => ?_
  exact h168 (H ⧸ N) (card_section_u33 hcard hnc hH N hs' hnab)

theorem c137SQTKSupply_of_simple168 (h168 : Simple168Catalog) : C137SQTKSupply :=
  c137SQTKSupply_of_u33 (u33KGroup_of_simple168 h168)

end CFSG.Quasithin.H13.U3.GC137.SQ
