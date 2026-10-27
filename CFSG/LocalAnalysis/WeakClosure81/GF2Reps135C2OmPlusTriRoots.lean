module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusTriPinned

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.ClassicalInvolution.G2D4Models.Twin
open scoped MatrixGroups

section Roots

variable {F : Type} [Field F] {ρ : spinGroup (Spin.quadPlus 4 F) ≃* spinGroup (Spin.quadPlus 4 F)}

theorem tv_zero_one_eq_upperSL2 (c : F) : (tv 0 1 c : SL(2, F)) = Spin.upperSL2 c := by
  apply Subtype.ext
  rw [tv_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.single_apply,
      Spin.upperSL2]

theorem tv_one_zero_eq_lowerSL2 (c : F) : (tv 1 0 c : SL(2, F)) = Spin.lowerSL2 c := by
  apply Subtype.ext
  rw [tv_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.single_apply,
      Spin.lowerSL2]

theorem comp_rankOneD_of_pinned (hρ : IsTrialityPinned ρ) (k : Fin 4) :
    ρ.toMonoidHom.comp (Spin.rankOneD F (by norm_num) k) =
      Spin.rankOneD F (by norm_num) (triPerm k) := by
  refine MonoidHom.ext fun g => ?_
  have hg : g ∈ Subgroup.closure ({g | ∃ c : F, g = tv 0 1 c} ∪ {g | ∃ c : F, g = tv 1 0 c} :
      Set SL(2, F)) := by
    rw [closure_tv_two]
    trivial
  refine MonoidHom.eqOn_closure (f := ρ.toMonoidHom.comp (Spin.rankOneD F (by norm_num) k))
    (g := Spin.rankOneD F (by norm_num) (triPerm k)) ?_ hg
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · show ρ (Spin.rankOneD F _ k (tv 0 1 c)) = Spin.rankOneD F _ (triPerm k) (tv 0 1 c)
    rw [tv_zero_one_eq_upperSL2, ← Steinberg.SpinPlus.x_single, ← Steinberg.SpinPlus.x_single]
    exact (hρ k c).1
  · show ρ (Spin.rankOneD F _ k (tv 1 0 c)) = Spin.rankOneD F _ (triPerm k) (tv 1 0 c)
    rw [tv_one_zero_eq_lowerSL2, ← Steinberg.SpinPlus.x_neg_single,
      ← Steinberg.SpinPlus.x_neg_single]
    exact (hρ k c).2

theorem map_weylD_of_pinned (hρ : IsTrialityPinned ρ) (k : Fin 4) :
    ρ (Spin.weylD F (by norm_num) k) = Spin.weylD F (by norm_num) (triPerm k) := by
  rw [Spin.weylD_eq_rankOneD, Spin.weylD_eq_rankOneD]
  exact congrArg (fun f => f (Spin.weylSL2 1)) (comp_rankOneD_of_pinned hρ k)

theorem map_torusD_of_pinned (hρ : IsTrialityPinned ρ) (k : Fin 4) (a : Fˣ) :
    ρ (Spin.torusD F (by norm_num) k a) = Spin.torusD F (by norm_num) (triPerm k) a := by
  rw [Spin.torusD_apply, Spin.torusD_apply]
  exact congrArg (fun f => f (Spin.diagSL2 a)) (comp_rankOneD_of_pinned hρ k)

theorem map_plusRootGroup_single_of_pinned (hρ : IsTrialityPinned ρ) (k : Fin 4) :
    (Spin.plusRootGroup 4 F (by norm_num) (Pi.single k 1)).map ρ.toMonoidHom =
      Spin.plusRootGroup 4 F (by norm_num) (Pi.single (triPerm k) 1) := by
  have hpar := Steinberg.SpinPlus.isParametrization (n := 4) (K := F) (by norm_num)
  have hk := fun k : Fin 4 => (hpar _ (ClassicalInvolution.Balance.single_mem_roots
    (Spin.plusDatum 4 F (by norm_num)) k)).1
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨c, rfl⟩ := (hk k g).1 hg
    exact (hk (triPerm k) _).2 ⟨c, (hρ k c).1.symm⟩
  · intro hy
    obtain ⟨c, rfl⟩ := (hk (triPerm k) y).1 hy
    exact ⟨_, (hk k _).2 ⟨c, rfl⟩, (hρ k c).1⟩

end Roots

section Weyl


theorem reflection_comp_triEquiv (i : Fin 4) (v : Fin 4 → ℤ) :
    reflection (Spin.cartanD 4) (triPerm i) (v ∘ ⇑triEquiv.symm) =
      reflection (Spin.cartanD 4) i v ∘ ⇑triEquiv.symm := by
  have hsum : ∑ k, Spin.cartanD 4 (triPerm i) k * v (triEquiv.symm k) =
      ∑ k, Spin.cartanD 4 i k * v k := by
    rw [← Equiv.sum_comp triEquiv]
    refine Finset.sum_congr rfl fun k => ?_
    intro _
    rw [show triEquiv.symm (triEquiv k) = k from triEquiv.symm_apply_apply k]
    exact congrArg (· * v k) (cartanD_triPerm i k)
  ext j
  simp only [reflection_apply, Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  have hj : (Pi.single (triPerm i) (1 : ℤ) : Fin 4 → ℤ) j =
      (Pi.single i 1 : Fin 4 → ℤ) (triEquiv.symm j) := by
    rw [Pi.single_apply, Pi.single_apply]
    exact if_congr (Equiv.symm_apply_eq triEquiv).symm rfl rfl
  rw [hj]

theorem weylAction_wordProd_comp_triEquiv (ω : List (Fin 4)) (v : Fin 4 → ℤ) :
    weylAction (Spin.isFiniteType_cartanD 4)
        ((coxeterMatrix (Spin.isFiniteType_cartanD 4)).toCoxeterSystem.wordProd
          (ω.map triPerm)) (v ∘ ⇑triEquiv.symm) =
      weylAction (Spin.isFiniteType_cartanD 4)
        ((coxeterMatrix (Spin.isFiniteType_cartanD 4)).toCoxeterSystem.wordProd ω) v ∘
          ⇑triEquiv.symm := by
  induction ω with
  | nil => simp
  | cons s ω ih =>
    rw [List.map_cons, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
      weylAction_mul_apply, weylAction_mul_apply, ih, weylAction_simple, weylAction_simple,
      reflection_comp_triEquiv]

end Weyl

section AllRoots

open CFSG.LieType.Steinberg

variable {F : Type} [Field F] {ρ : spinGroup (Spin.quadPlus 4 F) ≃* spinGroup (Spin.quadPlus 4 F)}

theorem map_plusRootGroup_of_pinned (hρ : IsTrialityPinned ρ) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ roots (Spin.isFiniteType_cartanD 4) ∅) :
    γ ∘ ⇑triEquiv.symm ∈ roots (Spin.isFiniteType_cartanD 4) ∅ ∧
      (Spin.plusRootGroup 4 F (by norm_num) γ).map ρ.toMonoidHom =
        Spin.plusRootGroup 4 F (by norm_num) (γ ∘ ⇑triEquiv.symm) := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hct := Spin.plusDatum_isCTGroupDatum hn3 (Spin.plusDatum_iSup_eq_top 4 F hn3)
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  swap
  · exact absurd hi (Set.notMem_empty i)
  obtain ⟨ω, -, rfl⟩ :=
    (coxeterMatrix (Spin.isFiniteType_cartanD 4)).toCoxeterSystem.exists_isReduced w
  have hid : (Pi.single i (1 : ℤ) : Fin 4 → ℤ) ∘ ⇑triEquiv.symm = Pi.single (triPerm i) 1 := by
    ext j
    simp only [Function.comp_apply, Pi.single_apply]
    exact if_congr (Equiv.symm_apply_eq triEquiv) rfl rfl
  have e := weylAction_wordProd_comp_triEquiv ω (Pi.single i 1)
  rw [hid] at e
  refine ⟨by rw [← e]; exact Or.inl ⟨_, _, rfl⟩, ?_⟩
  have hsa := ClassicalInvolution.Balance.single_mem_roots (Spin.plusDatum 4 F hn3)
  have hρN : ∀ ω : List (Fin 4), ρ (ω.map (Spin.weylD F hn3)).prod =
      ((ω.map triPerm).map (Spin.weylD F hn3)).prod := by
    intro ω
    induction ω with
    | nil => simp
    | cons s ω ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, ih, map_weylD_of_pinned hρ]
  have h1 : (Spin.plusRootGroup 4 F hn3 (Pi.single i 1)).map
      (MulAut.conj (ω.map (Spin.weylD F hn3)).prod).toMonoidHom =
      Spin.plusRootGroup 4 F hn3 (weylAction (Spin.isFiniteType_cartanD 4)
        ((coxeterMatrix (Spin.isFiniteType_cartanD 4)).toCoxeterSystem.wordProd ω)
          (Pi.single i 1)) :=
    actsAs_list_prod (D := Spin.plusDatum 4 F hn3) hct ω _ (hsa i)
  have h2 : (Spin.plusRootGroup 4 F hn3 (Pi.single (triPerm i) 1)).map
      (MulAut.conj ((ω.map triPerm).map (Spin.weylD F hn3)).prod).toMonoidHom =
      Spin.plusRootGroup 4 F hn3 (weylAction (Spin.isFiniteType_cartanD 4)
        ((coxeterMatrix (Spin.isFiniteType_cartanD 4)).toCoxeterSystem.wordProd
          (ω.map triPerm)) (Pi.single (triPerm i) 1)) :=
    actsAs_list_prod (D := Spin.plusDatum 4 F hn3) hct (ω.map triPerm) _ (hsa (triPerm i))
  have hcomp : ρ.toMonoidHom.comp (MulAut.conj (ω.map (Spin.weylD F hn3)).prod).toMonoidHom =
      (MulAut.conj ((ω.map triPerm).map (Spin.weylD F hn3)).prod).toMonoidHom.comp
        ρ.toMonoidHom := by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, hρN ω]
  calc (Spin.plusRootGroup 4 F hn3 (weylAction (Spin.isFiniteType_cartanD 4)
        ((coxeterMatrix (Spin.isFiniteType_cartanD 4)).toCoxeterSystem.wordProd ω)
          (Pi.single i 1))).map ρ.toMonoidHom
      = ((Spin.plusRootGroup 4 F hn3 (Pi.single i 1)).map
          (MulAut.conj (ω.map (Spin.weylD F hn3)).prod).toMonoidHom).map ρ.toMonoidHom := by
        rw [h1]
    _ = (Spin.plusRootGroup 4 F hn3 (Pi.single i 1)).map
          (ρ.toMonoidHom.comp (MulAut.conj (ω.map (Spin.weylD F hn3)).prod).toMonoidHom) :=
        Subgroup.map_map _ _ _
    _ = ((Spin.plusRootGroup 4 F hn3 (Pi.single i 1)).map ρ.toMonoidHom).map
          (MulAut.conj ((ω.map triPerm).map (Spin.weylD F hn3)).prod).toMonoidHom := by
        rw [hcomp, ← Subgroup.map_map]
    _ = (Spin.plusRootGroup 4 F hn3 (Pi.single (triPerm i) 1)).map
          (MulAut.conj ((ω.map triPerm).map (Spin.weylD F hn3)).prod).toMonoidHom := by
        rw [map_plusRootGroup_single_of_pinned hρ i]
    _ = _ := by rw [h2, e]

end AllRoots

end CFSG.LocalAnalysis.WeakClosure81
