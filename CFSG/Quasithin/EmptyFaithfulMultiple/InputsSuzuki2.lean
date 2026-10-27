module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs4
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Wreath
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationFinal
public import CFSG.Quasithin.Background.C1PackC129Case
public import CFSG.Quasithin.EmptyFaithful.S14113Case

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def wreathPointEquiv : Fin 4 × Multiplicative (ZMod 2) ≃ Fin 8 :=
  (Equiv.prodComm _ _).trans ((Equiv.prodCongr Multiplicative.toAdd (Equiv.refl _)).trans
    (finProdFinEquiv (m := 2) (n := 4)))

theorem wreathPointEquiv_block (p q : Fin 4 × Multiplicative (ZMod 2)) :
    (wreathPointEquiv p).val / 4 = (wreathPointEquiv q).val / 4 ↔ p.2 = q.2 := by
  revert p q
  decide

@[expose] noncomputable def wreathToPerm :
    Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2) →* Equiv.Perm (Fin 8) :=
  wreathPointEquiv.permCongrHom.toMonoidHom.comp
    (RegularWreathProduct.toPerm (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2)) (Fin 4))

theorem wreathToPerm_injective : Function.Injective wreathToPerm :=
  (wreathPointEquiv.permCongrHom.comp_injective _).mpr
    (RegularWreathProduct.toPermInj (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2)) (Fin 4))

theorem wreathToPerm_apply (w : Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2)) (i : Fin 8) :
    wreathToPerm w i = wreathPointEquiv (w • wreathPointEquiv.symm i) := rfl

theorem wreathToPerm_mem (w : Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2)) :
    wreathToPerm w ∈ wreathSFourTwo := by
  intro i j
  rw [wreathToPerm_apply, wreathToPerm_apply, wreathPointEquiv_block]
  conv_lhs => rw [← wreathPointEquiv.apply_symm_apply i, ← wreathPointEquiv.apply_symm_apply j]
  rw [wreathPointEquiv_block, RegularWreathProduct.smul_def, RegularWreathProduct.smul_def]
  simp

theorem card_wreathRegular :
    Nat.card (Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2)) = 1152 := by
  rw [RegularWreathProduct.card, Nat.card_perm]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem range_wreathToPerm : wreathToPerm.range = wreathSFourTwo := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨w, rfl⟩
    exact wreathToPerm_mem w
  · rw [← Nat.card_congr (MonoidHom.ofInjective wreathToPerm_injective).toEquiv,
      card_wreathRegular]
    exact L1547.card_wreathSFourTwo_le

noncomputable def wreathSFourTwoEquiv :
    Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2) ≃* wreathSFourTwo :=
  (MonoidHom.ofInjective wreathToPerm_injective).trans (MulEquiv.subgroupCongr range_wreathToPerm)

theorem input1391_holds
    : Input1391 := by
  intro G _ _ T hs hnab hq hT M hM
  exact ⟨fun e => CFSG.Quasithin.A10.theorem1391 G T hs hnab hq hT M hM.1 hM.2
    ⟨e.trans wreathSFourTwoEquiv.symm⟩⟩

theorem isSQTKIn_of_isSQTKCat {A : Type} [Group A] [Finite A] {H : Subgroup A}
    (h : CFSG.SectionRank.IsSQTKCat ↥H) : IsSQTKIn H :=
  ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mp h.1, h.2⟩

theorem o2FOf_eq_oTwoFIn {A : Type} [Group A] (H : Subgroup A) : O2FOf H = oTwoFIn H :=
  (oTwoFIn_eq_map_O2F H).symm

theorem inputC226_holds : InputC226 := by
  intro A _ _ H R MH hsq hR hMH hcgs hsyl hF _
  rw [o2FOf_eq_oTwoFIn] at hF ⊢
  have hyp : HypC23 H R MH := ⟨isSQTKIn_of_isSQTKCat hsq, hR, hMH, hcgs, hsyl⟩
  obtain ⟨r, L, hL, hprod⟩ := c2_6_two_thompson_solv hyp hF
  refine ⟨r, L, fun i => ⟨isBlock2_of_oTwoFIn (hL i).1, (hL i).2.1, (hL i).2.2.1⟩, ?_⟩
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_right (iSup_le fun i => (hL i).1.2.1))
  obtain ⟨m, hm, y, hy, rfl⟩ := hprod x hx
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hm) (Subgroup.list_prod_mem _ fun z hz => ?_)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem i (hy i))

end CFSG.Quasithin.EmptyFaithfulMultiple
