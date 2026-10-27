module

public import CFSG.Quasithin.EmptyFaithful.S151XA
public import CFSG.Quasithin.Background.FLcNat
public import CFSG.Quasithin.Background.FLcAutMat

public section

namespace CFSG.Quasithin

theorem input15129FlagLocal_holds : Input15129FlagLocal := by
  intro G _ _ L S UL hnat hSL hSU _ hSyl
  obtain ⟨n, hn, hsec⟩ := hnat
  obtain ⟨α, β, -, hαs, -, hβs, hβk, hrel⟩ := FLc.isNaturalSection_data hsec
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> omega
  obtain ⟨W, hWU, hWc, hWN, hWm, hWu⟩ :=
    FLc.flagLocal_core hn1 α β hαs hβi hβs hrel hSL hSU hSyl
  exact ⟨n, W, hn, ⟨FLc.card_eq_of_bijective hβi hβs,
    fun k _ hkn => ⟨hWU k, hWc k hkn.le, hWN k hkn.le, fun _ => hWm k⟩⟩,
    fun k _ hkn X hXU hSX hXc => hWu k hkn.le X hXU hSX hXc⟩

end CFSG.Quasithin
