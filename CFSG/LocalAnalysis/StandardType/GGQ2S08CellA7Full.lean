module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNSum
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertA8Full
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellsFull

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}

theorem ggQ2s08_cell_of_test_given (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) {B D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) (M : GGQ2LDatum 3 Bs L x) {n : ℕ}
    (κ : M.V ≃ₗ[ZMod 3] Vn n) {x₀ : Vn n} (hκx : κ M.xV = x₀)
    {W : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} (hW : (ggAutomizer L Bs).map (ggQ2CellLin M κ) = W)
    (Pg : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n) → Subgroup (Vn n ≃ₗ[ZMod 3] Vn n) → Prop)
    (hPg : Pg ((ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ))
      ((ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs).map
        (ggQ2CellLin M κ)))
    (htest : ∀ A Mg : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n), TestHyp W x₀ A Mg → Pg A Mg →
      ∀ r ∈ Mg, IsRefl r → ¬ FixesLine x₀ r →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine x₀ t → t ∈ Mg)
    (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ) (hRefl : GGIsReflection 3 φ) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  classical
  have hΓ : GGQ2GammaX 3 B Bs x L D J := hΓi hS rfl hI1 hCav
  have hAJ : ggAutomizer J Bs ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hCav
    exact absurd (Nat.le_of_dvd one_pos hCav) (by norm_num)
  have hH := ggQ2Cell_hyp hLB hP hS hΓ hAJ M κ hκx hW
  by_cases hline : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs)
  · refine hΓ g hInd.1 ?_
    have h1 := hInd.2 ⟨x, M.hx⟩
    rw [← h1]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hline
    rw [← hm]
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simp⟩
  obtain ⟨ρ, hρM, hρR, hρx⟩ := ggQ2_exists_movesLine_refl_M hTBN hS hI1
  have hmoves : ∀ ψ : MulAut ↥Bs, ψ ⟨x, M.hx⟩ ∉ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) →
      ¬ FixesLine x₀ (ggQ2CellLin M κ ψ) := fun ψ hψ h =>
    hψ (ggQ2Cell_mem_zpowers_of_fixesLine M κ hκx h)
  have hφA : φ ∈ ggAutomizer ⊤ Bs :=
    mem_ggAutomizer_iff.mpr ⟨g, Subgroup.mem_top _, hInd.1, hInd.2⟩
  obtain ⟨φ', hφ'M, hφ'⟩ := htest _ _ hH hPg _ ⟨ρ, hρM, rfl⟩ (ggQ2Cell_isRefl M κ hρR)
    (hmoves ρ (ggQ2Cell_not_mem_zpowers_of_movesLine M.hx hρx)) _ ⟨φ, hφA, rfl⟩
    (ggQ2Cell_isRefl M κ hRefl) (hmoves φ hline)
  obtain rfl := ggQ2CellLin_injective M κ hφ'
  exact ggQ2Cell_normalizes_of_mem hΓ M.hx hInd hφ'M

omit [Finite G] in
theorem ggQ2s08_roFrame_of_coords (M : GGQ2LDatum 3 Bs L x) {N : ℕ}
    (κ : M.V ≃ₗ[ZMod 3] Vn N) (hκx : κ M.xV = oneN N)
    (hW : (ggAutomizer L Bs).map (ggQ2CellLin M κ) ≤ permGroup N) (F : Fin N → Vn N)
    (hli : LinearIndependent (ZMod 3) F) (hsp : Submodule.span (ZMod 3) (Set.range F) = ⊤)
    (hsum : ∑ i, F i = oneN N) (hperm : ∀ σ i, permN σ (F i) = F (σ i)) :
    GGQ2S08ROFrame M (fun i => κ.symm (F i)) := by
  refine ⟨hli.map' κ.symm.toLinearMap κ.symm.ker, ?_, ?_, fun a ha => ?_⟩
  · change Submodule.span (ZMod 3) (Set.range (⇑κ.symm.toLinearMap ∘ F)) = ⊤
    rw [Set.range_comp, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]
  · rw [← map_sum κ.symm, hsum, ← hκx, LinearEquiv.symm_apply_apply]
  · obtain ⟨σ, hσ⟩ := hW ⟨a, ha, rfl⟩
    refine ⟨σ, fun i => ?_⟩
    have h := ggQ2CellLin_apply M κ a (F i)
    rw [← hσ] at h
    change permN σ (F i) = _ at h
    rw [hperm] at h
    exact ((LinearEquiv.symm_apply_eq κ).mpr h).symm

theorem closure_aFullS_le_permGroup (N : ℕ) :
    Subgroup.closure (Set.range (aFullS N)) ≤ permGroup N := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  refine ⟨Equiv.swap (aIdx N k) (aIdxSucc N k), ?_⟩
  change permN _ = _
  rw [permN, Equiv.symm_swap]
  rfl

theorem a8fS_eq : a8fS = aFullS 8 := by
  funext k
  refine LinearEquiv.toLinearMap_injective ((Pi.basisFun (ZMod 3) (Fin 8)).ext fun j => ?_)
  rw [Pi.basisFun_apply]
  revert k j
  decide +kernel

theorem permGroup_le_closure_aFullS_eight :
    permGroup 8 ≤ Subgroup.closure (Set.range (aFullS 8)) :=
  a8fS_eq ▸ permGroup_le_of_gens a8fS a8fGens (fun _ => rfl) (by norm_num) a8f_adj

theorem ggQ2s08_a7_pair
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRig : GGLabelRigidInput) {B D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel}
    (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = 7 ∧ GGLabQTwo 3 labL)
    (hWeyl : GGQ2LabelWeyl labL M.coxeter) (κ : M.V ≃ₗ[ZMod 3] Vn 8) (hκx : κ M.xV = oneN 8)
    (hW : (ggAutomizer L Bs).map (ggQ2CellLin M κ) = Subgroup.closure (Set.range (aFullS 8)))
    (F : Fin 8 → Vn 8) (hli : LinearIndependent (ZMod 3) F)
    (hsp : Submodule.span (ZMod 3) (Set.range F) = ⊤) (hsum : ∑ i, F i = oneN 8)
    (hpermF : ∀ σ i, permN σ (F i) = F (σ i)) {r t : Vn 8 ≃ₗ[ZMod 3] Vn 8}
    (hr : r (F 6) = -F 7 ∧ r (F 7) = -F 6 ∧ ∀ k, k ≠ 6 → k ≠ 7 → r (F k) = F k)
    (ht : ∃ ε : Fin 8 → ZMod 3, (∀ i, ε i ≠ 0) ∧ ∀ i, t (F i) = ε i • F i)
    (hrM : r ∈ (ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs).map
      (ggQ2CellLin M κ))
    (htA : t ∈ (ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ)) :
    t ∈ (ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs).map
      (ggQ2CellLin M κ) := by
  classical
  have hLN : L ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    le_trans le_sup_left Subgroup.le_normalizer
  set f : Fin (7 + 1) → M.V := fun i => κ.symm (F i) with hf
  have hFrame : GGQ2S08ROFrame M f :=
    ggQ2s08_roFrame_of_coords M κ hκx (hW ▸ closure_aFullS_le_permGroup 8) F hli hsp hsum hpermF
  have hlin : ∀ (φ : MulAut ↥Bs) (T : Vn 8 ≃ₗ[ZMod 3] Vn 8), ggQ2CellLin M κ φ = T →
      ∀ v, ggLin (p := 3) M.model φ (κ.symm v) = κ.symm (T v) := by
    intro φ T hT v
    rw [← hT, ggQ2CellLin_apply, LinearEquiv.symm_apply_apply]
  have hperm : ∀ σ : Equiv.Perm (Fin (7 + 1)), ∃ φ ∈ ggAutomizer
      (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs,
        ∀ i, ggLin (p := 3) M.model φ (f i) = f (σ i) := by
    intro σ
    have hmem : permN σ ∈ (ggAutomizer L Bs).map (ggQ2CellLin M κ) :=
      hW ▸ permGroup_le_closure_aFullS_eight ⟨σ, rfl⟩
    obtain ⟨φ, hφ, hφσ⟩ := hmem
    exact ⟨φ, ggAutomizer_mono Bs hLN hφ, fun i => by rw [hf, hlin φ _ hφσ, hpermF]⟩
  obtain ⟨φs, hφs, hφsr⟩ := hrM
  have hs : ∃ φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs,
      ggLin (p := 3) M.model φ (f 6) = -f 7 ∧ ggLin (p := 3) M.model φ (f 7) = -f 6 ∧
        ∀ k, k ≠ 6 → k ≠ 7 → ggLin (p := 3) M.model φ (f k) = f k := by
    refine ⟨φs, hφs, ?_, ?_, fun k hk6 hk7 => ?_⟩
    · rw [hf, hlin φs r hφsr, hr.1]
      exact κ.symm.map_neg (F 7)
    · rw [hf, hlin φs r hφsr, hr.2.1]
      exact κ.symm.map_neg (F 6)
    · rw [hf, hlin φs r hφsr, hr.2.2 k hk6 hk7]
  obtain ⟨ψ, hψ, hψt⟩ := htA
  obtain ⟨ε, hε, htε⟩ := ht
  have hmono : GGQ2S08Mono f (ggLin (p := 3) M.model ψ) :=
    ⟨1, ε, hε, fun i => by rw [hf, hlin ψ t hψt, htε, map_smul, Equiv.Perm.one_apply]⟩
  have hψM := ggQ2s08_roN_of_sum hLB hP hRig hS hCav M (by norm_num) (by decide)
    hMark hLab hWeyl f hFrame hperm (by decide) hs hψ hmono
  exact ⟨ψ, hψM, hψt⟩

theorem a8f_basisFun_eq :
    ⇑(Pi.basisFun (ZMod 3) (Fin 8)) = fun i : Fin 8 => (Pi.single i 1 : Vn 8) :=
  funext fun i => Pi.basisFun_apply _ _ i

@[expose] def a8fFrame' (i : Fin 8) : Vn 8 := oneN 8 - Pi.single i 1

theorem a8fFrame'_span : Submodule.span (ZMod 3) (Set.range a8fFrame') = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun (ZMod 3) (Fin 8)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  have h : ∀ i : Fin 8, (Pi.single i 1 : Vn 8) = ∑ k, a8fFrame' k - a8fFrame' i := by
    decide +kernel
  rw [h i]
  exact Submodule.sub_mem _ (Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨k, rfl⟩)
    (Submodule.subset_span ⟨i, rfl⟩)

theorem a8fFrame'_linearIndependent : LinearIndependent (ZMod 3) a8fFrame' :=
  linearIndependent_of_top_le_span_of_card_eq_finrank a8fFrame'_span.ge (by simp)

theorem ggQ2s08_cell_twA7
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRig : GGLabelRigidInput) (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) :
    GGQ2S08Cell .twA 7 .full := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hShape labL hMark htag hrank hq hWeyl g φ hInd hRefl
  have hW' : ∃ e : Fin 7 ≃ M.Λ, M.coxeter = (CoxeterMatrix.A 7).reindex e := by
    have key : ∀ m : ℕ, m = 7 → (∃ e : Fin m ≃ M.Λ, M.coxeter = (CoxeterMatrix.A m).reindex e) →
        ∃ e : Fin 7 ≃ M.Λ, M.coxeter = (CoxeterMatrix.A 7).reindex e := by
      rintro m rfl h
      exact h
    exact key _ hrank (by simpa only [GGQ2LabelWeyl, htag] using hWeyl)
  obtain ⟨e, he⟩ := hW'
  obtain ⟨κ, hκx, hκs⟩ := ggQ2_fullCoords_A8 M hShape.2.2.1 e (ggQ2_cartan_A e he M.isCartan)
  have hW := ggQ2Cell_map_automizer_L M κ e (aFullS 8) hκs
  refine ggQ2s08_cell_of_test_given hLB hP hΓi hTBN hS hI1 hCav M κ hκx hW
    (fun A Mg => ∀ i j, (i, j) ∈ a8fGiven →
      ∀ (hi : (letAt a8fReps i).2 ⬝ᵥ (letAt a8fReps i).1 = 2)
        (hj : (letAt a8fReps j).2 ⬝ᵥ (letAt a8fReps j).1 = 2),
      refl (letAt a8fReps i).1 (letAt a8fReps i).2 hi ∈ Mg →
      refl (letAt a8fReps j).1 (letAt a8fReps j).2 hj ∈ A →
      refl (letAt a8fReps j).1 (letAt a8fReps j).2 hj ∈ Mg) ?_
    (fun A Mg hT hPg => a8f_test A Mg (by rw [a8fS_eq]; exact hT) hPg) g φ hInd hRefl
  intro i j hij hi hj hrM htA
  simp only [a8fGiven, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hij
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ggQ2s08_a7_pair hLB hP hRig hS hCav M hMark ⟨htag, hrank, hq⟩ hWeyl κ hκx hW
      (fun i => Pi.single i 1) ?_ ?_ ?_ (fun σ i => permN_single σ i) ?_ ?_ hrM htA
    · rw [← a8f_basisFun_eq]
      exact (Pi.basisFun (ZMod 3) (Fin 8)).linearIndependent
    · rw [← a8f_basisFun_eq]
      exact (Pi.basisFun (ZMod 3) (Fin 8)).span_eq
    · decide +kernel
    · simp only [refl_apply]
      refine ⟨by decide +kernel, by decide +kernel, ?_⟩
      decide +kernel
    · refine ⟨![1, 1, 1, 1, 1, 1, 1, 2], by decide +kernel, ?_⟩
      simp only [refl_apply]
      decide +kernel
  · refine ggQ2s08_a7_pair hLB hP hRig hS hCav M hMark ⟨htag, hrank, hq⟩ hWeyl κ hκx hW
      a8fFrame' a8fFrame'_linearIndependent a8fFrame'_span ?_ ?_ ?_ ?_ hrM htA
    · decide +kernel
    · intro σ i
      rw [a8fFrame', a8fFrame', map_sub, permN_oneN, permN_single]
      rfl
    · simp only [refl_apply]
      refine ⟨by decide +kernel, by decide +kernel, ?_⟩
      decide +kernel
    · refine ⟨![2, 1, 1, 1, 1, 1, 1, 1], by decide +kernel, ?_⟩
      simp only [refl_apply]
      decide +kernel

end CFSG.StandardType

end
