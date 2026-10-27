module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestCore
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord Multiplicative

namespace NbrInnerRest

section Signed

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggTorusNbrSC_of_signedEltSC (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusSignedEltSC p R) : GGTorusNbrSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
  obtain ⟨k, Θ, -, hW, hS, hP, -⟩ :=
    exists_signedModelSC hp hp2 hI hZ hcp h hψ hker hperf hA hAI h3 hsc
  refine ⟨{n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))}, fun n hn => hW n hn,
    forall_comm_of_irred hp hA h3 fun A' hA'A hinv => ?_⟩
  set F : Subgroup (Fin k → Multiplicative (ZMod p)) :=
    (A'.subgroupOf A).comap Θ.toMonoidHom with hF
  have hmemF : ∀ f, f ∈ F ↔ ((Θ f : ↥A) : MulAut L') ∈ A' := fun f => Iff.rfl
  have hstab : ∀ α : MulAut (Fin k → Multiplicative (ZMod p)),
      (∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ α) → ∀ f ∈ F, α f ∈ F := by
    rintro α ⟨n, hn, hnα⟩ f hf
    rw [hmemF, ← coe_conj_of_ggConjAut_eq Θ hnα]
    exact hinv n hn _ ((hmemF f).mp hf)
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

end Signed

end NbrInnerRest

open NbrInnerRest

section Labels


theorem largeEvenLabelAll_torusNbrSC_unitary {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitaryCoprimeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusNbrSC p R I :=
  (largeEvenLabelAll_torusIrredSC_unitary hp hlab h).mono fun _ _ _ _ hT =>
    ggTorusNbrSC_of_ggTorusIrredSC hp hT

theorem ggTableBNbrInnerInputOn_unitary : GGTableBNbrInnerInputOn GGUnitaryCoprimeLabel :=
  ggTableBNbrInnerInputOn_of_labelsSC fun _ _ hp hlab h =>
    largeEvenLabelAll_torusNbrSC_unitary hp hlab h

theorem recipeSymplectic_torusNbrSC {l n p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    (hn : 1 ≤ n) (hl : 2 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧ GGTorusNbrSC p R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have : NeZero l := ⟨by omega⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  have hpK : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  obtain ⟨hT, hcp⟩ := ggSpNonsplitTorusInput_holds K l p hl hp hpK
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    ggTorusNbrSC_of_signedEltSC hp hp2 TableBSymp.sp_I_subset_inn
      TableBSymp.center_spProj_eq_bot hcp hT⟩

theorem largeEvenLabelAll_torusNbrSC_spNonsplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGSpNonsplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusNbrSC p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    exact recipeSymplectic_torusNbrSC hp hpn hn hlab.2.1 hQ

theorem ggTableBNbrInnerInputOn_spNonsplit : GGTableBNbrInnerInputOn GGSpNonsplitLabel :=
  ggTableBNbrInnerInputOn_of_labelsSC fun _ _ hp hlab h =>
    largeEvenLabelAll_torusNbrSC_spNonsplit hp hlab h

end Labels

end CFSG.StandardType

end
