module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6Pat
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusHolds
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaTwE6ThreeAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlusAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlusAux2
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaTwE6
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggNEE_torusE6Pat_of_weyl {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
    (hsc : GGTorusSelfCent p A) (Φ : A ≃* Multiplicative (Fin τ.rank → ZMod p))
    (w : Fin τ.rank → L') (hw : ∀ i, GGTorusWeylElt p A (w i))
    (hact : ∀ i (a b : A), (b : MulAut L') = MulAut.conj (w i) * a * (MulAut.conj (w i))⁻¹ →
      Multiplicative.toAdd (Φ b) =
        TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a))) :
    GGTorusE6Pat p A := by
  have hsym : ∀ i j : Fin τ.rank, τ.cartan i j = τ.cartan j i := by
    rcases hτ with rfl | rfl | rfl
    · intro i j
      fin_cases i <;> fin_cases j <;> decide
    · intro i j
      fin_cases i <;> fin_cases j <;> decide
    · intro i j
      fin_cases i <;> fin_cases j <;> decide
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hN : ∀ i, MulAut.conj (w i) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun i => conj_mem_normalizer_of_torusWeylElt hsc (hw i)
  let ρ : Fin τ.rank → MulAut ↥A := fun i => ggConjAut A (hN i)
  have hρ : ∀ i (a : A), Multiplicative.toAdd (Φ (ρ i a)) =
      TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a)) :=
    fun i a => hact i a (ρ i a) (ggConjAut_apply A (hN i) a)
  have hρsq : ∀ i, ρ i ^ 2 = 1 := fun i => by
    refine MulEquiv.ext fun a => ?_
    apply Φ.injective
    apply Multiplicative.toAdd.injective
    rw [pow_two, MulAut.mul_apply, hρ, hρ, torusAct_simple_involutive, MulAut.one_apply]
  have hρfix : ∀ i, Nat.card {a : A // ρ i a = a} * p = Nat.card A := fun i => by
    have hcardA : Nat.card A = p ^ τ.rank := by
      rw [Nat.card_congr Φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
    have hcardFix : Nat.card {a : A // ρ i a = a} = Nat.card
        {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p (simple τ i) x = x} := by
      refine Nat.card_congr (Equiv.subtypeEquiv (Φ.toEquiv.trans Multiplicative.toAdd) ?_)
      intro a
      change ρ i a = a ↔ TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a)) =
        Multiplicative.toAdd (Φ a)
      rw [← hρ]
      constructor
      · intro hh; rw [hh]
      · intro hh; exact Φ.injective (Multiplicative.toAdd.injective hh)
    rw [hcardFix, card_fix_torusAct_simple τ hp2 i, hcardA]
  have hρmem : ∀ i, ρ i ∈ ggTorusReflSet p A := fun i =>
    ⟨w i, hN i, hw i, rfl, hρsq i, hρfix i⟩
  have e6Pat_of_nodes : ∀ (i0 i1 i2 i3 j1 j2 : Fin τ.rank),
      τ.cartan i0 i1 = -1 → τ.cartan i0 i2 = -1 → τ.cartan i0 i3 = -1 →
      τ.cartan i1 i2 = 0 → τ.cartan i1 i3 = 0 → τ.cartan i2 i3 = 0 →
      τ.cartan j1 i1 = -1 → τ.cartan j1 i2 = 0 → τ.cartan j1 i3 = 0 →
      τ.cartan j2 i2 = -1 → τ.cartan j2 i3 = 0 →
      GGTorusE6Pat p A := by
    rintro i0 i1 i2 i3 j1 j2 hA01 hA02 hA03 hA12 hA13 hA23 hAb11 hAb12 hAb13 hAb22 hAb23
    have hrev : ∀ {i j : Fin τ.rank} {a : ℤ}, τ.cartan i j = a → τ.cartan j i = a := by
      intro i j a h
      rwa [hsym i j] at h
    have hne : ∀ {i j : Fin τ.rank}, τ.cartan i j ≠ 2 → i ≠ j := by
      intro i j h rfl
      exact h (Tag.cartan_self τ i)
    have h01 : i0 ≠ i1 := hne (by rw [hA01]; norm_num)
    have h02 : i0 ≠ i2 := hne (by rw [hA02]; norm_num)
    have h03 : i0 ≠ i3 := hne (by rw [hA03]; norm_num)
    have h12 : i1 ≠ i2 := hne (by rw [hA12]; norm_num)
    have h13 : i1 ≠ i3 := hne (by rw [hA13]; norm_num)
    have h23 : i2 ≠ i3 := hne (by rw [hA23]; norm_num)
    have hb11 : j1 ≠ i1 := hne (by rw [hAb11]; norm_num)
    have hb12 : j1 ≠ i2 := hne (by rw [hAb12]; norm_num)
    have hb13 : j1 ≠ i3 := hne (by rw [hAb13]; norm_num)
    have hb22 : j2 ≠ i2 := hne (by rw [hAb22]; norm_num)
    have hb23 : j2 ≠ i3 := hne (by rw [hAb23]; norm_num)
    have hM01 : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) i0 i1 = 3 :=
      ggNEE_coxeterMatrix_eq_three_of_cartan h01 hA01 (hrev hA01)
    have hM02 : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) i0 i2 = 3 :=
      ggNEE_coxeterMatrix_eq_three_of_cartan h02 hA02 (hrev hA02)
    have hM03 : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) i0 i3 = 3 :=
      ggNEE_coxeterMatrix_eq_three_of_cartan h03 hA03 (hrev hA03)
    have hM12 : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) i1 i2 = 2 :=
      ggNEE_coxeterMatrix_eq_two_of_cartan h12 hA12 (hrev hA12)
    have hM13 : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) i1 i3 = 2 :=
      ggNEE_coxeterMatrix_eq_two_of_cartan h13 hA13 (hrev hA13)
    have hM23 : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) i2 i3 = 2 :=
      ggNEE_coxeterMatrix_eq_two_of_cartan h23 hA23 (hrev hA23)
    have hMb11 : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) j1 i1 = 3 :=
      ggNEE_coxeterMatrix_eq_three_of_cartan hb11 hAb11 (hrev hAb11)
    have hMb12 : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) j1 i2 = 2 :=
      ggNEE_coxeterMatrix_eq_two_of_cartan hb12 hAb12 (hrev hAb12)
    have hMb13 : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) j1 i3 = 2 :=
      ggNEE_coxeterMatrix_eq_two_of_cartan hb13 hAb13 (hrev hAb13)
    have hMb22 : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) j2 i2 = 3 :=
      ggNEE_coxeterMatrix_eq_three_of_cartan hb22 hAb22 (hrev hAb22)
    have hMb23 : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) j2 i3 = 2 :=
      ggNEE_coxeterMatrix_eq_two_of_cartan hb23 hAb23 (hrev hAb23)
    have hpow : ∀ {i j : Fin τ.rank} {n : ℕ},
        (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) i j = n →
        (simple τ i * simple τ j) ^ n = 1 := by
      intro i j n hM
      have h := (coxeterSystem τ).simple_mul_simple_pow i j
      rwa [hM] at h
    refine ⟨ρ i0, hρmem i0, ρ i1, hρmem i1, ρ i2, hρmem i2, ρ i3, hρmem i3,
      ρ j1, hρmem j1, ρ j2, hρmem j2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact orderOf_eq_prime (p := 3) (ggNEE_pair_pow_eq_one hρ (hpow hM01))
        (ggNEE_pair_ne_one_of_torusAct_ne hρ
          (ggNEE_torusAct_simple_mul_single_adj_ne τ h01 hA01))
    · exact orderOf_eq_prime (p := 3) (ggNEE_pair_pow_eq_one hρ (hpow hM02))
        (ggNEE_pair_ne_one_of_torusAct_ne hρ
          (ggNEE_torusAct_simple_mul_single_adj_ne τ h02 hA02))
    · exact orderOf_eq_prime (p := 3) (ggNEE_pair_pow_eq_one hρ (hpow hM03))
        (ggNEE_pair_ne_one_of_torusAct_ne hρ
          (ggNEE_torusAct_simple_mul_single_adj_ne τ h03 hA03))
    · exact orderOf_eq_prime (p := 2) (ggNEE_pair_pow_eq_one hρ (hpow hM12))
        (ggNEE_pair_ne_one_of_torusAct_ne hρ
          (ggNEE_torusAct_simple_mul_single_orth_ne τ hp2 (hrev hA12)))
    · exact orderOf_eq_prime (p := 2) (ggNEE_pair_pow_eq_one hρ (hpow hM13))
        (ggNEE_pair_ne_one_of_torusAct_ne hρ
          (ggNEE_torusAct_simple_mul_single_orth_ne τ hp2 (hrev hA13)))
    · exact orderOf_eq_prime (p := 2) (ggNEE_pair_pow_eq_one hρ (hpow hM23))
        (ggNEE_pair_ne_one_of_torusAct_ne hρ
          (ggNEE_torusAct_simple_mul_single_orth_ne τ hp2 (hrev hA23)))
    · exact orderOf_eq_prime (p := 3) (ggNEE_pair_pow_eq_one hρ (hpow hMb11))
        (ggNEE_pair_ne_one_of_torusAct_ne hρ
          (ggNEE_torusAct_simple_mul_single_adj_ne τ hb11 hAb11))
    · exact orderOf_eq_prime (p := 2) (ggNEE_pair_pow_eq_one hρ (hpow hMb12))
        (ggNEE_pair_ne_one_of_torusAct_ne hρ
          (ggNEE_torusAct_simple_mul_single_orth_ne τ hp2 (hrev hAb12)))
    · exact orderOf_eq_prime (p := 2) (ggNEE_pair_pow_eq_one hρ (hpow hMb13))
        (ggNEE_pair_ne_one_of_torusAct_ne hρ
          (ggNEE_torusAct_simple_mul_single_orth_ne τ hp2 (hrev hAb13)))
    · exact orderOf_eq_prime (p := 3) (ggNEE_pair_pow_eq_one hρ (hpow hMb22))
        (ggNEE_pair_ne_one_of_torusAct_ne hρ
          (ggNEE_torusAct_simple_mul_single_adj_ne τ hb22 hAb22))
    · exact orderOf_eq_prime (p := 2) (ggNEE_pair_pow_eq_one hρ (hpow hMb23))
        (ggNEE_pair_ne_one_of_torusAct_ne hρ
          (ggNEE_torusAct_simple_mul_single_orth_ne τ hp2 (hrev hAb23)))
  rcases hτ with rfl | rfl | rfl
  · refine e6Pat_of_nodes ⟨3, by decide⟩ ⟨2, by decide⟩ ⟨4, by decide⟩ ⟨1, by decide⟩
      ⟨0, by decide⟩ ⟨5, by decide⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals decide
  · refine e6Pat_of_nodes ⟨3, by decide⟩ ⟨2, by decide⟩ ⟨4, by decide⟩ ⟨1, by decide⟩
      ⟨0, by decide⟩ ⟨5, by decide⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals decide
  · refine e6Pat_of_nodes ⟨3, by decide⟩ ⟨2, by decide⟩ ⟨4, by decide⟩ ⟨1, by decide⟩
      ⟨0, by decide⟩ ⟨5, by decide⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals decide

theorem ggTorusE6Pat_of_excPlusModel
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : GGExcPlusWeylModelSCr τ p r R I) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup p r R I L' ψ A → GGTorusE6Pat p A := by
  intro L' _ _ ψ A hA
  have hsc : GGTorusSelfCent p A := hA.2.2.2.2.2.2.2
  obtain ⟨Φ, w, hw, hact, -⟩ := h L' ψ A hA
  exact ggNEE_torusE6Pat_of_weyl (Or.inr hτ) hp hp2 hsc Φ w hw hact

theorem ggRowE6Pat_EE7
    : GGRowE6Pat ggRowP_EE7 := by
  intro p hp hp2 lab _ hS
  obtain ⟨htag, hpn⟩ := hS
  refine (largeEvenLabelAll_and
    (largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inl htag, hpn⟩)
    (ggNEE_largeEvenLabelAll_model_excPlus hp hp2 (Or.inl htag) hpn)).mono
      fun _ _ _ _ h =>
        ⟨_, h.1, ggTorusE6Pat_of_excPlusModel (Or.inl (by simp [ggNEE_tagOf, htag])) hp hp2 h.2⟩

theorem ggRowE6Pat_EE8
    : GGRowE6Pat ggRowP_EE8 := by
  intro p hp hp2 lab _ hS
  obtain ⟨htag, hpn⟩ := hS
  refine (largeEvenLabelAll_and
    (largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inr (Or.inl htag), hpn⟩)
    (ggNEE_largeEvenLabelAll_model_excPlus hp hp2 (Or.inr htag) hpn)).mono
      fun _ _ _ _ h =>
        ⟨_, h.1, ggTorusE6Pat_of_excPlusModel (Or.inr (by simp [ggNEE_tagOf, htag])) hp hp2 h.2⟩

theorem ggTorusE6Pat_of_twE6Model {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : TwE6TB.GGTorusModelSCr p r R I) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup p r R I L' ψ A → GGTorusE6Pat p A := by
  intro L' _ _ ψ A hA
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  obtain ⟨Φ, w, hw, hact⟩ := h L' ψ hψ hker hperf A hAe hAI hr h3 hsc
  refine ggNEE_torusE6Pat_of_weyl (τ := .E6) (Or.inl rfl) hp hp2 hsc Φ w hw ?_
  intro i a b hb
  have hb' : b = Φ.symm (Multiplicative.ofAdd
      (TwE6TB.reflE6 p i (Multiplicative.toAdd (Φ a)))) :=
    Subtype.ext (hb.trans (hact i a))
  have h1 : Φ b = Multiplicative.ofAdd (TwE6TB.reflE6 p i (Multiplicative.toAdd (Φ a))) := by
    rw [hb']
    exact MulEquiv.apply_symm_apply Φ _
  exact (congrArg Multiplicative.toAdd h1).trans (ggNET_reflE6_eq_torusAct i _)

theorem ggRowE6Pat_ETwE6_ge5
    : GGRowE6Pat fun p lab => ggRowP_ETwE6 p lab ∧ 5 ≤ p := by
  intro p hp hp2 lab hlab hS
  obtain ⟨hrow, hp5⟩ := hS
  haveI : Fact p.Prime := ⟨hp⟩
  refine TwE6Delta.labelAll hrow.1 fun K _ _ hK => ⟨5, ?_, ?_⟩
  · have hl := ggTorusLift_twE6Add_holds hlab.1 hK hp hrow.2
    rwa [TwE6Delta.liftRank_of_ne (by omega)] at hl
  · exact ggTorusE6Pat_of_twE6Model hp hp2
      (ggTwE6TorusModelInput_holds K lab.n p hlab.1 hK hp hrow.2 hp5)

theorem ggNE3_cube_02 : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s 0 (ggNE3_s 2 z))^[3]) y = y := by
  decide +kernel

theorem ggNE3_cube_54 : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s 5 (ggNE3_s 4 z))^[3]) y = y := by
  decide +kernel

theorem ggNE3_sq_21 : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s 2 (ggNE3_s 1 z))^[2]) y = y := by
  decide +kernel

theorem ggNE3_sq_41 : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s 4 (ggNE3_s 1 z))^[2]) y = y := by
  decide +kernel

theorem ggNE3_sq_04 : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s 0 (ggNE3_s 4 z))^[2]) y = y := by
  decide +kernel

theorem ggNE3_sq_01 : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s 0 (ggNE3_s 1 z))^[2]) y = y := by
  decide +kernel

theorem ggNE3_sq_51 : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s 5 (ggNE3_s 1 z))^[2]) y = y := by
  decide +kernel

theorem ggNE3_move_02 :
    ∃ x : E6Dep.Vec6, dotProduct E6Dep.ZL.kappa x = 0 ∧ ggNE3_s 0 (ggNE3_s 2 x) ≠ x := by
  decide +kernel

theorem ggNE3_move_54 :
    ∃ x : E6Dep.Vec6, dotProduct E6Dep.ZL.kappa x = 0 ∧ ggNE3_s 5 (ggNE3_s 4 x) ≠ x := by
  decide +kernel

theorem ggNE3_move_21 :
    ∃ x : E6Dep.Vec6, dotProduct E6Dep.ZL.kappa x = 0 ∧ ggNE3_s 2 (ggNE3_s 1 x) ≠ x := by
  decide +kernel

theorem ggNE3_move_41 :
    ∃ x : E6Dep.Vec6, dotProduct E6Dep.ZL.kappa x = 0 ∧ ggNE3_s 4 (ggNE3_s 1 x) ≠ x := by
  decide +kernel

theorem ggNE3_move_04 :
    ∃ x : E6Dep.Vec6, dotProduct E6Dep.ZL.kappa x = 0 ∧ ggNE3_s 0 (ggNE3_s 4 x) ≠ x := by
  decide +kernel

theorem ggNE3_move_01 :
    ∃ x : E6Dep.Vec6, dotProduct E6Dep.ZL.kappa x = 0 ∧ ggNE3_s 0 (ggNE3_s 1 x) ≠ x := by
  decide +kernel

theorem ggNE3_move_51 :
    ∃ x : E6Dep.Vec6, dotProduct E6Dep.ZL.kappa x = 0 ∧ ggNE3_s 5 (ggNE3_s 1 x) ≠ x := by
  decide +kernel

theorem ggTorusE6Pat_of_e6ThreeModel {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGE6ThreeModelSCr R I) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup 3 5 R I L' ψ A → GGTorusE6Pat 3 A := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, h5, -, hsc⟩ := hA
  obtain ⟨Φ, T, w, hd⟩ := (h L' ψ hψ hker hperf A hAe hAI h5 hsc).exists_data
  obtain ⟨x32, hx32, hn32⟩ := ggNE3_move_32
  obtain ⟨x34, hx34, hn34⟩ := ggNE3_move_34
  obtain ⟨x31, hx31, hn31⟩ := ggNE3_move_31
  obtain ⟨x24, hx24, hn24⟩ := ggNE3_move_24
  obtain ⟨x21, hx21, hn21⟩ := ggNE3_move_21
  obtain ⟨x41, hx41, hn41⟩ := ggNE3_move_41
  obtain ⟨x02, hx02, hn02⟩ := ggNE3_move_02
  obtain ⟨x04, hx04, hn04⟩ := ggNE3_move_04
  obtain ⟨x01, hx01, hn01⟩ := ggNE3_move_01
  obtain ⟨x54, hx54, hn54⟩ := ggNE3_move_54
  obtain ⟨x51, hx51, hn51⟩ := ggNE3_move_51
  refine ⟨hd.conjAut (3 : Fin 6), hd.conjAut_mem_ggTorusReflSet (3 : Fin 6),
    hd.conjAut (2 : Fin 6), hd.conjAut_mem_ggTorusReflSet (2 : Fin 6),
    hd.conjAut (4 : Fin 6), hd.conjAut_mem_ggTorusReflSet (4 : Fin 6),
    hd.conjAut (1 : Fin 6), hd.conjAut_mem_ggTorusReflSet (1 : Fin 6),
    hd.conjAut (0 : Fin 6), hd.conjAut_mem_ggTorusReflSet (0 : Fin 6),
    hd.conjAut (5 : Fin 6), hd.conjAut_mem_ggTorusReflSet (5 : Fin 6),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact orderOf_eq_prime (p := 3) (ggNE3_pair_pow_eq_one hd 3 2 3 ggNE3_cube_32)
      (ggNE3_pair_ne_one hd 3 2 x32 hx32 hn32)
  · exact orderOf_eq_prime (p := 3) (ggNE3_pair_pow_eq_one hd 3 4 3 ggNE3_cube_34)
      (ggNE3_pair_ne_one hd 3 4 x34 hx34 hn34)
  · exact orderOf_eq_prime (p := 3) (ggNE3_pair_pow_eq_one hd 3 1 3 ggNE3_cube_31)
      (ggNE3_pair_ne_one hd 3 1 x31 hx31 hn31)
  · exact orderOf_eq_prime (p := 2) (ggNE3_pair_pow_eq_one hd 2 4 2 ggNE3_sq_24)
      (ggNE3_pair_ne_one hd 2 4 x24 hx24 hn24)
  · exact orderOf_eq_prime (p := 2) (ggNE3_pair_pow_eq_one hd 2 1 2 ggNE3_sq_21)
      (ggNE3_pair_ne_one hd 2 1 x21 hx21 hn21)
  · exact orderOf_eq_prime (p := 2) (ggNE3_pair_pow_eq_one hd 4 1 2 ggNE3_sq_41)
      (ggNE3_pair_ne_one hd 4 1 x41 hx41 hn41)
  · exact orderOf_eq_prime (p := 3) (ggNE3_pair_pow_eq_one hd 0 2 3 ggNE3_cube_02)
      (ggNE3_pair_ne_one hd 0 2 x02 hx02 hn02)
  · exact orderOf_eq_prime (p := 2) (ggNE3_pair_pow_eq_one hd 0 4 2 ggNE3_sq_04)
      (ggNE3_pair_ne_one hd 0 4 x04 hx04 hn04)
  · exact orderOf_eq_prime (p := 2) (ggNE3_pair_pow_eq_one hd 0 1 2 ggNE3_sq_01)
      (ggNE3_pair_ne_one hd 0 1 x01 hx01 hn01)
  · exact orderOf_eq_prime (p := 3) (ggNE3_pair_pow_eq_one hd 5 4 3 ggNE3_cube_54)
      (ggNE3_pair_ne_one hd 5 4 x54 hx54 hn54)
  · exact orderOf_eq_prime (p := 2) (ggNE3_pair_pow_eq_one hd 5 1 2 ggNE3_sq_51)
      (ggNE3_pair_ne_one hd 5 1 x51 hx51 hn51)

theorem ggRowE6PatAt_ETwE6_three
    : GGRowE6PatAt (fun p lab => ggRowP_ETwE6 p lab ∧ p = 3) 5 := by
  intro p hp hp2 lab hlab hS
  obtain ⟨hrow, rfl⟩ := hS
  refine TwE6Delta.labelAll hrow.1 fun K _ _ hK => ?_
  exact ggTorusE6Pat_of_e6ThreeModel (E6ThreeModel.e6ThreeModel_holds.2 K lab.n hlab.1 hK hrow.2)

end CFSG.StandardType

end
