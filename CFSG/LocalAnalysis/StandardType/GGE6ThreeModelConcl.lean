module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelDefs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelNbr
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAct
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTv
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLModPSL
public import CFSG.LocalAnalysis.StandardType.GGTableBLinIrredDef
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTv
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Nbr
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63ActCore
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActMain

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section PerExtension

variable {L' : Type} [Group L'] [Finite L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
  {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}

theorem GGE6ThreeData.moduleConcl (h : GGE6ThreeData Z A Φ T w) :
    ∃ (H : Subgroup (MulAut L')) (W : Set L'), H ≤ A ∧ H ≠ ⊥ ∧ Nat.card A ≤ 3 * Nat.card H ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        ∀ x ∈ H, MulAut.conj n * x * (MulAut.conj n)⁻¹ ∈ H) ∧
      (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
      ∀ A' : Subgroup (MulAut L'), A' ≤ A → A' ≠ ⊥ →
        (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → H ≤ A' :=
  ⟨heartOf Φ, (Subgroup.closure (Set.range w) : Set L'), heartOf_le, h.heart_ne_bot,
    h.card_le_three_mul_card_heart, fun n hn => h.heart_conj_mem hn,
    fun n hn => h.closure_weyl hn, fun A' hA' hne hinv =>
      h.heart_le_of_invariant hA' hne fun i a ha =>
        hinv (w i) (Subgroup.subset_closure ⟨i, rfl⟩) a ha⟩

theorem GGE6ThreeData.actConcl (h : GGE6ThreeData Z A Φ T w) (hodd : Odd (Nat.card Z)) :
    U63TB.ActConcl 3 A :=
  ⟨heartOf Φ, (Subgroup.closure (Set.range w) : Set L'), heartOf_le, h.heart_ne_bot,
    fun n hn => h.heart_conj_mem hn, fun n hn => h.closure_weyl hn,
    fun A' hA' hne hinv => h.heart_le_of_invariant hA' hne fun i a ha =>
      hinv (w i) (Subgroup.subset_closure ⟨i, rfl⟩) a ha,
    fun a ha hfix => h.eq_one_of_forall_conj_eq ha fun i =>
      hfix (w i) (Subgroup.subset_closure ⟨i, rfl⟩),
    fun n hn a ha => h.comm_mem_heart hn ha,
    fun n hn => h.normalizer_clause hodd hn,
    fun n hn => h.mem_closure_involutions hodd hn,
    fun f hf1 hf2 hf3 => h.exists_power_map f hf1 hf2 hf3⟩

end PerExtension

section PerLabel

variable {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggTorusNbrSCrK_of_model
    (hM : GGE6ThreeModelSCr R I) : U63TB.GGTorusNbrSCrK 3 5 R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ hsc
  obtain ⟨Φ, T, w, hd⟩ := (hM L' ψ hψ hker hperf A hA hAI hr hsc).exists_data
  exact hd.nbrConcl

theorem ggTableBModuleSCr_of_model (hM : GGE6ThreeModelSCr R I) : GGTableBModuleSCr 3 5 R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ hsc
  obtain ⟨Φ, T, w, hd⟩ := (hM L' ψ hψ hker hperf A hA hAI hr hsc).exists_data
  exact hd.moduleConcl

theorem ggNoTransvectionSCr_of_model
    (hM : GGE6ThreeModelSCr R I) : GGNoTransvectionSCr 3 5 R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ hsc α _
  obtain ⟨Φ, T, w, hd⟩ := (hM L' ψ hψ hker hperf A hA hAI hr hsc).exists_data
  exact hd.not_isTransvection α

theorem ggTableBActionSCr_of_model (hM : GGE6ThreeModelSCr R I)
    (hodd : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Odd (Nat.card ψ.ker)) :
    GGTableBActionSCr 3 5 R I := by
  refine ⟨by norm_num, fun L' _ _ ψ hψ hker hperf A hA hAI hr _ hsc => ?_⟩
  obtain ⟨Φ, T, w, hd⟩ := (hM L' ψ hψ hker hperf A hA hAI hr hsc).exists_data
  exact hd.actConcl (hodd L' ψ hψ hker hperf)

end PerLabel

end CFSG.StandardType
