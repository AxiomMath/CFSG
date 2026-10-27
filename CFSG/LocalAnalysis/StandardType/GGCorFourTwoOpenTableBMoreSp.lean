module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestSC
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoRestTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord Multiplicative

namespace CorFourTwoMore

section Signed

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggTorusIrredSC_of_signedEltSC (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusSignedEltSC p R) :
    CorFourTwoOpen.GGTorusIrredSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
  have := Fact.mk hp
  obtain ⟨k, Θ, hk, hW, hS, hP, -⟩ :=
    exists_signedModelSC hp hp2 hI hZ hcp h hψ hker hperf hA hAI h3 hsc
  obtain ⟨Ws, hWs1, hWs4⟩ :=
    ggTorusSchurSC_of_signedEltSC hp hp2 hI hZ hcp h L' ψ hψ hker hperf A hA hAI h3 hsc
  refine ⟨Ws ∪ {n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))}, ?_, ?_, ?_, ?_⟩
  · rintro n (hn | hn)
    · exact hWs1 n hn
    · exact hW n hn
  · intro A' hA'A hinv
    set F : Subgroup (Fin k → Multiplicative (ZMod p)) :=
      (A'.subgroupOf A).comap Θ.toMonoidHom with hF
    have hmemF : ∀ f, f ∈ F ↔ ((Θ f : ↥A) : MulAut L') ∈ A' := fun f => Iff.rfl
    have hstab : ∀ α : MulAut (Fin k → Multiplicative (ZMod p)),
        (∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
          ggConjAut A hn = MulAut.congr Θ α) → ∀ f ∈ F, α f ∈ F := by
      rintro α ⟨n, hn, hnα⟩ f hf
      rw [hmemF, ← coe_conj_of_ggConjAut_eq Θ hnα]
      exact hinv n (Or.inr hn) _ ((hmemF f).mp hf)
    rcases NbrSp.eq_bot_or_eq_top_of_signed hp hp2 F (fun i f hf => hstab _ (hS i) f hf)
        (fun σ f hf => hstab _ (hP σ) f hf) with hbot | htop
    · left
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨f, hf⟩ := Θ.surjective ⟨a, hA'A ha⟩
      have hfF : f ∈ F := by
        rw [hmemF, hf]
        exact ha
      rw [hbot, Subgroup.mem_bot] at hfF
      rw [hfF, map_one] at hf
      rw [Subgroup.mem_bot]
      exact (congrArg Subtype.val hf).symm
    · right
      refine le_antisymm hA'A fun a ha => ?_
      obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
      have hfF : f ∈ F := htop ▸ Subgroup.mem_top f
      rw [hmemF, hf] at hfF
      exact hfF
  · set i₀ : Fin k := ⟨0, by omega⟩ with hi₀
    obtain ⟨n, hn, hnα⟩ := hS i₀
    refine ⟨n, Or.inr hn, Θ (Pi.mulSingle i₀ (ofAdd 1)), (Θ _).2, fun heq => ?_⟩
    rw [coe_conj_of_ggConjAut_eq Θ hnα, sgnAut_mulSingle_self] at heq
    have h1 := congrFun (Θ.injective (Subtype.ext heq)) i₀
    rw [Pi.inv_apply, Pi.mulSingle_eq_same] at h1
    have h2 : (1 : ZMod p) = -1 := by
      have h3 := congrArg toAdd h1
      rw [toAdd_inv, toAdd_ofAdd] at h3
      exact h3.symm
    exact one_ne_zero (coord_eq_zero_of_eq_neg hp hp2 h2)
  · intro f hfA hfmul hfW
    exact hWs4 f hfA hfmul fun m hm a ha => hfW m (Or.inl hm) a ha

end Signed

end CorFourTwoMore

open CorFourTwoMore

section Labels


theorem recipeSymplectic_torusIrredSC {l n p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    (hn : 1 ≤ n) (hl : 2 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ CorFourTwoOpen.GGTorusIrredSC p R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have : NeZero l := ⟨by omega⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  have hpK : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  obtain ⟨hT, hcp⟩ := ggSpNonsplitTorusInput_holds K l p hl hp hpK
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    ggTorusIrredSC_of_signedEltSC hp hp2 TableBSymp.sp_I_subset_inn
      TableBSymp.center_spProj_eq_bot hcp hT⟩

theorem largeEvenLabelAll_torusIrredSC_spNonsplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGSpNonsplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => CorFourTwoOpen.GGTorusIrredSC p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    exact recipeSymplectic_torusIrredSC hp hpn hn hlab.2.1 hQ

theorem ggTableBIrredInputOn_spNonsplit : GGTableBIrredInputOn GGSpNonsplitLabel :=
  CorFourTwoOpen.ggTableBIrredInputOn_of_labelsSC fun _ _ hp hlab h =>
    largeEvenLabelAll_torusIrredSC_spNonsplit hp hlab h

end Labels

theorem GGSpTwoThreeLabel.spNonsplit {p : ℕ} {lab : LargeEvenLabel}
    (h : GGSpTwoThreeLabel p lab) : GGSpNonsplitLabel p lab := by
  obtain ⟨rfl, hn, ht⟩ := h
  refine ⟨ht, ?_⟩
  rw [hn]
  norm_num

section TwoThree


theorem ggTableBIrredInputOn_spTwoThree : GGTableBIrredInputOn GGSpTwoThreeLabel :=
  ggTableBIrredInputOn_spNonsplit.mono fun _ _ h => h.spNonsplit

theorem ggTableBCxInputOn_spTwoThree : GGTableBCxInputOn GGSpTwoThreeLabel :=
  ggTableBCxInputOn_of_irred ggBstarInnerDiagLInputOn_spTwoThree ggTableBIrredInputOn_spTwoThree

theorem ggTableBModuleInputOn_spTwoThree : GGTableBModuleInputOn GGSpTwoThreeLabel :=
  ggTableBModuleInputOn_of_irred ggBstarInnerDiagLInputOn_spTwoThree
    ggTableBIrredInputOn_spTwoThree

theorem ggTableBActionInputOn_spTwoThree : GGTableBActionInputOn GGSpTwoThreeLabel :=
  ggTableBActionInputOn_of_irred ggBstarInnerDiagLInputOn_spTwoThree
    ggTableBIrredInputOn_spTwoThree

end TwoThree

end CFSG.StandardType

end
