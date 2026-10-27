module

public import CFSG.Quasithin.EmptyFaithful.S152WBase
public import CFSG.GH74.Generic.S45.LSporHe

public section

namespace CFSG.Quasithin.S152W

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.GH74.Uniqueness.Bender CFSG.GH74.Generic.S45
  CFSG.ComponentClassification.OuterAutomorphisms

theorem he_cent_values
    {S : Type} [Group S] (e : S ≃* NativeSporadic.He)
    (hZ : Subgroup.center S = ⊥) (t : S) (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set S)) = 161280 ∨
      Nat.card (Subgroup.centralizer ({t} : Set S)) = 21504 ∨
        Nat.card (Subgroup.centralizer ({t} : Set S)) = 15120 := by
  obtain ⟨h2, h1⟩ := conj_involution hZ ht
  have h := he_fixed_card e (MulAut.conj t) h2 h1
  have hc : Nat.card ↥(autFixed (MulAut.conj t)) =
      Nat.card (Subgroup.centralizer ({t} : Set S)) := by
    rw [← card_fixed_conj]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  rwa [hc] at h

theorem atlasClauses_He
    {S : Type} [Group S] (e : S ≃* NativeSporadic.He) :
    AtlasClauses S := by
  obtain ⟨hfin, -, hsimple⟩ := CFSG.Sporadic.He.fam_he_simplicity
  have : Finite S := Finite.of_equiv _ e.symm.toEquiv
  have : IsSimpleGroup S := @MulEquiv.isSimpleGroup S _ NativeSporadic.He _ hsimple e
  have hcard : Nat.card S = 4030387200 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.He.card_He
  have hZ : Subgroup.center S = ⊥ :=
    center_eq_bot_of_simple_not_prime (by rw [hcard]; norm_num)
  have h2part : (Nat.card S).factorization 2 = 10 :=
    factorization_two_of_eq (b := 3935925) (by rw [hcard]; norm_num) (by norm_num)
  have hout : Nat.card (Outer S) ≤ 2 := outer_card_le_of_equiv AT_He_Schreier.1 e
  refine atlasClauses_of_data hout [161280, 21504, 15120] ?_ ?_
  · intro t ht
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using he_cent_values e hZ t ht
  · intro c hc h9
    rw [h2part]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> revert h9 <;> decide

end CFSG.Quasithin.S152W
