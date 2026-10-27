module

public import CFSG.Quasithin.Background.C124Interface
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.C124BlkTransfer

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem card_fourSpace : Nat.card (Multiplicative (Fin 4 → ZMod 2)) = 2 ^ 4 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
  simp

theorem spec4cA7Four_holds : Spec4cA7Four := by
  intro G _ _ X T V L R m hV hE hC hB
  have hL : L ≤ Subgroup.normalizer (V : Set G) := (le_of_mem_cComp hE.comp).trans hE.red.2.1
  obtain ⟨-, ⟨α8, π, hπ⟩, ⟨e⟩⟩ := hC
  have hinj : Function.Injective π := by
    let π' : ↥(alternatingGroup (Fin 7)) →* ↥(autI hV L) := π
    have h1 : Function.Surjective π' := hπ.1
    exact (Function.Surjective.bijective_of_nat_card_le h1 (Nat.card_congr e.toEquiv).ge).1
  let eπ : ↥(alternatingGroup (Fin 7)) ≃* ↥(autI hV L) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  obtain ⟨β, hβs, hβk, -⟩ := exists_blockHomOfEquiv hV hL hB.VL_le hB.U_eq (FFModel.a7Four α8) π hπ
    (natQuotEquiv (FFModel.a7Four α8) rfl rfl)
  refine ⟨hB.short, ⟨eπ.symm.toMonoidHom.comp (starHom hV L hL), ?_, ?_⟩, ?_⟩
  · exact eπ.symm.surjective.comp (starHom_surjective hV hL)
  · rw [MonoidHom.ker_comp_of_injective _ eπ.symm.toMonoidHom eπ.symm.injective]
    exact ker_starHom_eq_pCore hV hL hB.ker
  · rw [← hβk, Subgroup.index_ker, MonoidHom.range_eq_top.2 hβs, Subgroup.card_top]
    exact card_fourSpace

end CFSG.Quasithin.C124
