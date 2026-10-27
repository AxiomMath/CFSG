module

public import CFSG.Quasithin.Background.C124Interface
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.C124BlkTransfer

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem spec4cL2_holds : Spec4cL2 := by
  intro G _ _ X T V L R m hV hE hC hB
  have hL : L ≤ Subgroup.normalizer (V : Set G) := (le_of_mem_cComp hE.comp).trans hE.red.2.1
  obtain ⟨-, F, hF, hFin, hcard, π, hπ, hinj⟩ := hC
  let eπ : StatedSL 2 F ≃* ↥(autI hV L) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  let e₂ := specialLinearGroupEquivStatedSL 2 F
  let α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e₂.symm.toMonoidHom.comp (eπ.symm.toMonoidHom.comp (starHom hV L hL))
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_blockHomOfEquiv hV hL hB.VL_le hB.U_eq
    (FFModel.nat (StatedSL 2 F)) π hπ (natQuotEquiv (FFModel.nat (StatedSL 2 F)) rfl rfl)
  let _ : Fintype F := Fintype.ofFinite F
  refine ⟨F, hF, inferInstance, ?_, α, ?_, ?_, β, hβs, hβk, ?_⟩
  · rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  · exact e₂.symm.surjective.comp (eπ.symm.surjective.comp (starHom_surjective hV hL))
  · rw [MonoidHom.ker_comp_of_injective _ e₂.symm.toMonoidHom e₂.symm.injective,
      MonoidHom.ker_comp_of_injective _ eπ.symm.toMonoidHom eπ.symm.injective]
    exact ker_starHom_eq_pCore hV hL hB.ker
  · intro ℓ u v hv
    set γ : StatedSL 2 F := eπ.symm (starHom hV L hL ℓ) with hγ
    have hπγ : π γ = starHom hV L hL ℓ := eπ.apply_symm_apply _
    have h1 := hβe ℓ γ hπγ u v ⟨(β u : Multiplicative (Fin 2 → F)), trivial⟩ trivial hv rfl
    have h2 : ((α ℓ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((γ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      have := specialLinearGroupEquivStatedSL_coe 2 F (α ℓ)
      rw [← this]
      simp [α, e₂, hγ]
    rw [h2]
    exact congrArg Multiplicative.toAdd h1

end CFSG.Quasithin.C124
