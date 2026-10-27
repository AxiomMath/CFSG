module

public import CFSG.Quasithin.Recognition.St84.Sec68E
public import CFSG.Quasithin.Recognition.St84.Sec4Main
public import CFSG.Quasithin.Recognition.St84.TransportL34
public import CFSG.Quasithin.Recognition.St84.TransportSp44
public import CFSG.Quasithin.Recognition.St84.TransportG24
public import CFSG.Quasithin.Recognition.St84.G24Ident
public import CFSG.Quasithin.Recognition.F112IdentW

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ

theorem idA5A5W_of_g24Ident
    (hident : ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), F112HypW L1 L2 S →
      VA5 L1 → VA5 L2 → G24LocalData L1 L2 S →
        IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsG2Over 2)) : IdA5A5W := by
  intro G _ _ L1 L2 S hF h1 h2
  have hH := f112_hyp30 hF h1 h2
  have hc := f112_charTwoStab hF h1 h2
  have hn := f112_nOf_eq_two hF h1 h2
  obtain ⟨s, X, hs, hX, hcase⟩ := sec7_A5A5 hH hc hn
  rcases hcase with ⟨hodd, h5⟩ | ⟨hs4, -⟩
  · rcases Nat.even_or_odd (Nat.card X.GT) with hGT | hGT
    · exact (sec6_false hc X (Or.inl (hn _).ge) hs hodd h5 hX hGT).elim
    · obtain ⟨X₀, hX0, hX1⟩ := f112_exists_setup_baseEdge hF h1 h2
      rcases sec4_A5A5_all hc X hn hs hodd h5 hX hGT X₀ with ⟨-, d⟩ | ⟨-, d⟩
      · exact Or.inr (Or.inl (f112_sp4_of_treeSp44Data hF h1 h2 hX0 hX1 d))
      · exact Or.inr (Or.inr (f112_g24_of_treeG24Data hF h1 h2 hX0 hX1
          (fun hF' h1' h2' hd => hident G _ _ _ hF' h1' h2' hd) d))
  · exact Or.inl (f112_psl3_of_even_singularity hF h1 h2 hs (by rw [hs4]; decide))

theorem idA5A5W_holds :
    IdA5A5W :=
  idA5A5W_of_g24Ident g24Ident

theorem idA5A5_holds :
    IdA5A5 :=
  idA5A5W_holds.idA5A5

end CFSG.Quasithin.F112R.St84
