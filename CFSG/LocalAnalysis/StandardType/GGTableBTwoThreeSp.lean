module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThree
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticLift
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeB2der
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeEndNode
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB TypeA TwoThree TableBSymp
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace TwoThree

section Sp

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem mem_range_conj_sp (hK : Nat.card K = 2) (hm : 3 ≤ m)
    (α : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) :
    α ∈ Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →* _) := by
  have : NeZero m := ⟨by omega⟩
  obtain ⟨-, hgen⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.automorphism_generation (K := K) hm
  obtain ⟨A, σ, hα⟩ := hgen α
  have hσ : σ = 1 := by
    ext x
    rcases eq_zero_or_eq_one_of_card hK x with rfl | rfl
    · simp
    · simp
  have hin := CFSG.SeitzReduction.SymplecticPilot.spLinearAutGroup_le_inner (K := K) (r := m)
    (Subgroup.subset_closure ⟨A, rfl⟩)
  rw [hα, hσ, map_one, mul_one]
  exact hin

theorem card_sq_le_sp (hK : Nat.card K = 2) [NeZero m]
    {A : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))} (hA : IsElemAbelian 3 A) :
    Nat.card A ^ 2 ≤ 3 ^ (2 * m) := by
  set A' : Subgroup (GL (Fin m ⊕ Fin m) K) :=
    (A.map (spProjEquivSp (K := K) (m := m)).toMonoidHom).map (LargeEvenSpGroup K m).subtype
  have hA' : IsElemAbelian 3 A' := TableB.isElemAbelian_map (TableB.isElemAbelian_map hA _) _
  have hcard : Nat.card A' = Nat.card A := by
    rw [← Nat.card_congr ((A.map (spProjEquivSp (K := K) (m := m)).toMonoidHom).equivMapOfInjective
      _ (LargeEvenSpGroup K m).subtype_injective).toEquiv,
      ← Nat.card_congr (A.equivMapOfInjective _
        (spProjEquivSp (K := K) (m := m)).injective).toEquiv]
  set e := (Matrix.GeneralLinearGroup.toLin : GL (Fin m ⊕ Fin m) K ≃* _) with he
  set Y : Subgroup (Module.End K (Fin m ⊕ Fin m → K))ˣ := A'.map e.toMonoidHom with hY
  have hcardY : Nat.card Y = Nat.card A' :=
    (Nat.card_congr (A'.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
    rintro _ ⟨B, hB, rfl⟩ _ ⟨C, hC, rfl⟩
    change e B * e C = e C * e B
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hA' hB hC]
  have hexp : ∀ x ∈ Y, x ^ 3 = 1 := by
    rintro _ ⟨B, hB, rfl⟩
    change e B ^ 3 = 1
    rw [← map_pow, hA'.2 B hB, map_one]
  have h := card_sq_le_top hK Y hcomm hexp
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, hcardY, hcard,
    ← two_mul] at h

theorem ggBstarBound_sp_two (hK : Nat.card K = 2) (hm : 3 ≤ m) :
    GGBstarBound 3 (m - 1) (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  intro Eb Eh _ _ hr _ _ hEh hcard
  exfalso
  have : NeZero m := ⟨by omega⟩
  obtain ⟨A, hA, hAc⟩ := exists_of_subset_inn (center_spProj_eq_bot (K := K) (m := m))
    (fun φ _ => mem_range_conj_sp hK hm φ) hEh
  have h1 := card_le_pow_half hA (card_sq_le_sp hK hA)
  rw [hAc, show 2 * m / 2 = m by omega] at h1
  have h4 : 3 ^ (m + 1) ≤ Nat.card Eh :=
    calc 3 ^ (m + 1) = 3 ^ 2 * 3 ^ (m - 1) := by rw [← pow_add]; congr 1; omega
      _ ≤ 3 ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ hr
      _ ≤ Nat.card Eh := hcard
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (h4.trans h1)
  omega

end Sp

section Torus

open CFSG.LieType.SteinbergBR.EvenSp

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}

@[expose] noncomputable def planeSp (hK : Nat.card K = 2) :
    (Fin (k + 1) → GL (Fin 2) K) →* LargeEvenSpGroup K (k + 1) :=
  planeHom.codRestrict _ fun g => Subgroup.subset_closure
    (planeMat_symplectic _ fun j => det_eq_one_of_card hK (g j))

@[expose] noncomputable def planeProj (hK : Nat.card K = 2) :
    (Fin (k + 1) → GL (Fin 2) K) →* LargeEvenProj (LargeEvenSpGroup K (k + 1)) :=
  (LargeEvenProjMk _).comp (planeSp hK)

omit [CharP K 2] in
theorem planeProj_injective (hK : Nat.card K = 2) :
    Function.Injective (planeProj (k := k) hK) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : planeSp hK g ∈ (LargeEvenScalars (Fin (k + 1) ⊕ Fin (k + 1)) K).subgroupOf
      (LargeEvenSpGroup K (k + 1)) := (QuotientGroup.eq_one_iff _).mp hg
  rw [largeEvenScalars_eq_bot hK, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at h1
  apply planeHom_injective
  rw [map_one]
  exact congrArg Subtype.val h1

@[expose] noncomputable def tPow : Multiplicative (ZMod 3) →* GL (Fin 2) K :=
  zmodPowHom (tGL_pow_three (K := K))

omit [Finite K] in
theorem tPow_injective : Function.Injective (tPow (K := K)) := by
  have : NeZero (3 : ℕ) := ⟨by norm_num⟩
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [tPow, zmodPowHom_apply] at ha
  have h3 := orderOf_dvd_of_pow_eq_one ha
  rw [orderOf_tGL] at h3
  have hlt := ZMod.val_lt (Multiplicative.toAdd a)
  have h0 : (Multiplicative.toAdd a).val = 0 := by
    rcases h3 with ⟨c, hc⟩
    omega
  rw [ZMod.val_eq_zero] at h0
  exact h0

@[expose] noncomputable def extTorus :
    (Fin k → Multiplicative (ZMod 3)) →* (Fin (k + 1) → GL (Fin 2) K) where
  toFun f j := if h : (j : ℕ) < k then tPow (f ⟨j, h⟩) else 1
  map_one' := by
    funext j
    by_cases h : (j : ℕ) < k <;> simp [h]
  map_mul' f g := by
    funext j
    by_cases h : (j : ℕ) < k <;> simp [h]

omit [Finite K] in
theorem extTorus_injective : Function.Injective (extTorus (K := K) (k := k)) := by
  rw [injective_iff_map_eq_one]
  intro f hf
  funext i
  have h1 := congrFun hf i.castSucc
  simp only [extTorus, MonoidHom.coe_mk, OneHom.coe_mk, Fin.val_castSucc, i.2, dite_true,
    Pi.one_apply] at h1
  have h2 : tPow (K := K) (f i) = 1 := by simpa using h1
  exact tPow_injective (K := K) (by rw [h2, Pi.one_apply, map_one])

@[expose] def swapGL : GL (Fin 2) K :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp, by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp⟩

@[expose] def unipGL : GL (Fin 2) K :=
  ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [CharTwo.add_self_eq_zero], by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [CharTwo.add_self_eq_zero]⟩

omit [Finite K] in
theorem swapGL_conj_tGL : swapGL (K := K) * tGL * swapGL⁻¹ = tGL⁻¹ := by
  apply Units.ext
  change !![(0 : K), 1; 1, 0] * !![0, 1; 1, 1] * !![0, 1; 1, 0] = !![1, 1; 1, 0]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

omit [Finite K] in
theorem unipGL_sq : unipGL (K := K) ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, sq]
  change !![(1 : K), 1; 0, 1] * !![1, 1; 0, 1] = 1
  rw [Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [CharTwo.add_self_eq_zero]

omit [Finite K] in
theorem unipGL_ne_one : unipGL (K := K) ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp [unipGL] at this

omit [Finite K] in
theorem tPow_ofAdd_one : tPow (K := K) (Multiplicative.ofAdd 1) = tGL := by
  have : NeZero (3 : ℕ) := ⟨by norm_num⟩
  rw [tPow, zmodPowHom_apply, toAdd_ofAdd, ZMod.val_one, pow_one]

omit [Finite K] in
theorem extTorus_mulSingle (i : Fin k) :
    extTorus (K := K) (Pi.mulSingle i (Multiplicative.ofAdd 1)) = Pi.mulSingle i.castSucc tGL := by
  funext j
  by_cases h : (j : ℕ) < k
  · simp only [extTorus, MonoidHom.coe_mk, OneHom.coe_mk, h, dite_true]
    by_cases hji : (⟨j, h⟩ : Fin k) = i
    · have hj : j = i.castSucc := by
        apply Fin.ext
        rw [Fin.val_castSucc]
        have := congrArg Fin.val hji
        simpa using this
      rw [hji, Pi.mulSingle_eq_same, hj, Pi.mulSingle_eq_same, tPow_ofAdd_one]
    · have hj : j ≠ i.castSucc := fun hj => hji (Fin.ext (by
        show (j : ℕ) = i
        rw [hj, Fin.val_castSucc]))
      rw [Pi.mulSingle_eq_of_ne hji, map_one, Pi.mulSingle_eq_of_ne hj]
  · have hj : j ≠ i.castSucc := fun hj => h (by rw [hj, Fin.val_castSucc]; exact i.2)
    simp only [extTorus, MonoidHom.coe_mk, OneHom.coe_mk, h, dite_false]
    rw [Pi.mulSingle_eq_of_ne hj]

omit [Finite K] in
theorem extTorus_commute_last (f : Fin k → Multiplicative (ZMod 3)) :
    Commute (extTorus (K := K) f)
      (Pi.mulSingle (Fin.last k) (unipGL (K := K)) : Fin (k + 1) → GL (Fin 2) K) := by
  funext j
  show extTorus f j * (Pi.mulSingle (Fin.last k) (unipGL (K := K)) :
      Fin (k + 1) → GL (Fin 2) K) j =
    (Pi.mulSingle (Fin.last k) (unipGL (K := K)) : Fin (k + 1) → GL (Fin 2) K) j * extTorus f j
  by_cases hj : j = Fin.last k
  · subst hj
    have h : ¬ ((Fin.last k : Fin (k + 1)) : ℕ) < k := by simp
    simp only [extTorus, MonoidHom.coe_mk, OneHom.coe_mk, h, dite_false, one_mul, mul_one]
  · rw [Pi.mulSingle_eq_of_ne hj, one_mul, mul_one]

theorem ggTorusLift_sp_two (hK : Nat.card K = 2) :
    GGTorusLift 3 k (LargeEvenProj (LargeEvenSpGroup K (k + 1))) := by
  set τ := (planeProj (k := k) hK).comp (extTorus (K := K)) with hτ
  have hτi : Function.Injective τ := (planeProj_injective hK).comp extTorus_injective
  have hbasis : ∀ i, torusBasis τ i = planeProj hK (Pi.mulSingle i.castSucc tGL) := fun i => by
    rw [torusBasis, hτ, MonoidHom.comp_apply, extTorus_mulSingle]
  set u₀ := planeProj hK (Pi.mulSingle (Fin.last k) (unipGL (K := K))) with hu₀
  have hu₀1 : u₀ ≠ 1 := by
    intro h
    apply unipGL_ne_one (K := K)
    have h1 := planeProj_injective hK (h.trans (map_one _).symm)
    have := congrFun h1 (Fin.last k)
    simpa using this
  have hu₀2 : u₀ ^ 2 ^ 1 = 1 := by
    rw [pow_one, hu₀, ← map_pow, ← Pi.mulSingle_pow, unipGL_sq, Pi.mulSingle_one, map_one]
  refine ggTorusLift_of_torus Nat.prime_three (by norm_num) τ hτi ?_ (U := Subgroup.zpowers u₀)
    ?_ (isPGroup_two_zpowers hu₀2) ?_
  · intro i j
    refine ⟨planeProj hK (Pi.mulSingle i.castSucc (swapGL (K := K))), ?_, fun hji => ?_⟩
    · rw [hbasis, ← map_inv, ← map_mul, ← map_mul, ← Pi.mulSingle_inv, ← Pi.mulSingle_mul,
        ← Pi.mulSingle_mul, swapGL_conj_tGL, Pi.mulSingle_inv, map_inv]
    · have hne : j.castSucc ≠ i.castSucc := fun h => hji (Fin.castSucc_injective _ h)
      have hc : (Pi.mulSingle i.castSucc (swapGL (K := K)) : Fin (k + 1) → GL (Fin 2) K) *
          Pi.mulSingle j.castSucc tGL =
          Pi.mulSingle j.castSucc tGL * Pi.mulSingle i.castSucc swapGL := by
        funext x
        simp only [Pi.mul_apply]
        by_cases hx : x = i.castSucc
        · subst hx
          rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hne), mul_one, one_mul]
        · rw [Pi.mulSingle_eq_of_ne hx, one_mul, mul_one]
      rw [hbasis, ← map_inv, ← map_mul, ← map_mul, hc, mul_inv_cancel_right]
  · intro hbot
    apply hu₀1
    have : u₀ ∈ (⊥ : Subgroup _) := hbot ▸ Subgroup.mem_zpowers u₀
    exact Subgroup.mem_bot.mp this
  · intro d u hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hc : Commute (τ d) u₀ := by
      rw [hτ, MonoidHom.comp_apply, hu₀]
      exact (extTorus_commute_last d).map _
    rw [(hc.zpow_right n).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers u₀ n

end Torus

end TwoThree

theorem recipeSymplectic_tableB_three {m N : ℕ} (hm : 3 ≤ m) (hN : N = 2) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic m N false Q) :
    LargeEvenRecipeSymplectic m N false fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift 3 r R ∧ GGBstarBound 3 r R I := by
  subst hN
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine ⟨k, ggTorusLift_sp_two hK, ?_⟩
  have h := ggBstarBound_sp_two (K := K) hK hm
  rwa [Nat.add_sub_cancel] at h

@[expose] def GGSpTwoThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 3 ∧ lab.n = 1 ∧ (lab.tag = .B ∨ lab.tag = .C)

theorem GGSpTwoThreeLabel.pilot {p : ℕ} {lab : LargeEvenLabel} (h : GGSpTwoThreeLabel p lab) :
    GGOutdiagPilotLabel lab := by
  rcases h.2.2 with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem largeEvenLabelAll_spTwoThree {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGSpTwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, hn, ht⟩ := h
  dsimp only at hn ht
  subst hn
  intro Q hQ
  rcases ht with rfl | rfl
  · have hl : 3 ≤ l := by
      have h1 := hlab.2
      dsimp only at h1
      omega
    exact recipeSymplectic_tableB_three hl (by norm_num) hQ
  · have hl : 3 ≤ l := by
      have h1 := hlab.2
      dsimp only at h1
      omega
    exact recipeSymplectic_tableB_three hl (by norm_num) hQ

theorem ggBstarInputOn_spTwoThree : GGBstarInputOn GGSpTwoThreeLabel :=
  ggBstarInputOn_of_labels (fun _ _ h => h.pilot) fun _ _ _ hlab h =>
    largeEvenLabelAll_spTwoThree hlab h

end CFSG.StandardType
