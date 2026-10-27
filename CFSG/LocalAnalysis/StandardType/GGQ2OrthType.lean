module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthPlaneForm
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.GroupTheory.WeirSylow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private noncomputable def splitFinEquiv (a s δ : ℕ) :
    Fin ((a + s) + δ) ≃ Fin a ⊕ Fin (s + δ) :=
  (finCongr (Nat.add_assoc a s δ)).trans finSumFinEquiv.symm

private noncomputable def splitCoordEquiv (a s δ : ℕ) :
    (Fin ((a + s) + δ) ⊕ Fin ((a + s) + δ)) ≃
      (Fin a ⊕ Fin a) ⊕ (Fin (s + δ) ⊕ Fin (s + δ)) :=
  (Equiv.sumCongr (splitFinEquiv a s δ) (splitFinEquiv a s δ)).trans
    (Equiv.sumSumSumComm (Fin a) (Fin (s + δ)) (Fin a) (Fin (s + δ)))

private noncomputable def splitCoord (a s δ : ℕ) :
    (Fin ((a + s) + δ) ⊕ Fin ((a + s) + δ) → K) ≃ₗ[K]
      ((Fin a ⊕ Fin a → K) × (Fin (s + δ) ⊕ Fin (s + δ) → K)) :=
  (LinearEquiv.funCongrLeft K K (splitCoordEquiv a s δ).symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin a ⊕ Fin a) (Fin (s + δ) ⊕ Fin (s + δ)) K K)

omit [Finite K] [CharP K 2] in
private theorem splitCoord_fst_inl (a s δ : ℕ)
    (v : Fin ((a + s) + δ) ⊕ Fin ((a + s) + δ) → K) (i : Fin a) :
    (splitCoord (K := K) a s δ v).1 (Sum.inl i) =
      v (Sum.inl (Fin.castAdd δ (Fin.castAdd s i))) := by
  simp only [splitCoord, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
    LinearEquiv.sumArrowLequivProdArrow_apply_fst, splitCoordEquiv,
    Equiv.sumSumSumComm, splitFinEquiv]
  congr 2

omit [Finite K] [CharP K 2] in
private theorem splitCoord_fst_inr (a s δ : ℕ)
    (v : Fin ((a + s) + δ) ⊕ Fin ((a + s) + δ) → K) (i : Fin a) :
    (splitCoord (K := K) a s δ v).1 (Sum.inr i) =
      v (Sum.inr (Fin.castAdd δ (Fin.castAdd s i))) := by
  simp only [splitCoord, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
    LinearEquiv.sumArrowLequivProdArrow_apply_fst, splitCoordEquiv,
    Equiv.sumSumSumComm, splitFinEquiv]
  congr 2

omit [Finite K] [CharP K 2] in
private theorem splitCoord_snd_inl (a s δ : ℕ)
    (v : Fin ((a + s) + δ) ⊕ Fin ((a + s) + δ) → K) (j : Fin (s + δ)) :
    (splitCoord (K := K) a s δ v).2 (Sum.inl j) =
      v (Sum.inl (Fin.cast (Nat.add_assoc a s δ).symm (Fin.natAdd a j))) := by
  simp [splitCoord, splitCoordEquiv, splitFinEquiv, LinearEquiv.funCongrLeft,
    LinearEquiv.sumArrowLequivProdArrow]

omit [Finite K] [CharP K 2] in
private theorem splitCoord_snd_inr (a s δ : ℕ)
    (v : Fin ((a + s) + δ) ⊕ Fin ((a + s) + δ) → K) (j : Fin (s + δ)) :
    (splitCoord (K := K) a s δ v).2 (Sum.inr j) =
      v (Sum.inr (Fin.cast (Nat.add_assoc a s δ).symm (Fin.natAdd a j))) := by
  simp [splitCoord, splitCoordEquiv, splitFinEquiv, LinearEquiv.funCongrLeft,
    LinearEquiv.sumArrowLequivProdArrow]

private theorem splitSum {M : Type*} [AddCommMonoid M] (a s δ : ℕ)
    (f : Fin ((a + s) + δ) → M) :
    (∑ i : Fin ((a + s) + δ), f i) =
      (∑ i : Fin a, f (Fin.castAdd δ (Fin.castAdd s i))) +
      (∑ i : Fin (s + δ), f (Fin.cast (Nat.add_assoc a s δ).symm (Fin.natAdd a i))) := by
  classical
  let g : Fin (a + (s + δ)) → M := fun k => f (Fin.cast (Nat.add_assoc a s δ).symm k)
  have h1 : (∑ i : Fin ((a + s) + δ), f i) = ∑ k : Fin (a + (s + δ)), g k := by
    refine Fintype.sum_equiv (finCongr (Nat.add_assoc a s δ)) f g ?_
    intro i
    simp [g]
  rw [h1, Fin.sum_univ_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g]
    rw [show Fin.cast (Nat.add_assoc a s δ).symm (Fin.castAdd (s + δ) i) =
        Fin.castAdd δ (Fin.castAdd s i) from Fin.ext rfl]
  · refine Finset.sum_congr rfl fun i _ => rfl

private noncomputable def splitPlaneForm (a s : ℕ) (δ : Fin 2) :
    (planeQForm K (a + s) δ).IsometryEquiv
      ((planeQForm K a 0).prod (planeQForm K s δ)) where
  toLinearEquiv := splitCoord a s δ.val
  map_app' v := by
    change planeQForm K a 0 (splitCoord (K := K) a s δ.val v).1 +
      planeQForm K s δ (splitCoord (K := K) a s δ.val v).2 = planeQForm K (a + s) δ v
    rw [coe_planeQForm, coe_planeQForm, coe_planeQForm]
    simp only [planeQ, Fin.val_zero, Nat.add_zero]
    simp only [splitCoord_fst_inl, splitCoord_fst_inr, splitCoord_snd_inl, splitCoord_snd_inr]
    rw [splitSum a s δ.val]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [if_pos x.isLt, if_pos (by rw [Fin.val_castAdd, Fin.val_castAdd]; omega)]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Fin.val_cast, Fin.val_natAdd]
      by_cases h : (x : ℕ) < s
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]

omit [Finite K] [CharP K 2] in
private theorem isPlusType_zero (δ : Fin 2) : IsPlusType (planeQForm K 0 δ) := by
  fin_cases δ
  · simp only [Fin.val_mk, Nat.add_zero]
    exact isPlusType_of_subsingleton _
  · change IsPlusType (planeQForm K 0 (1 : Fin 2))
    let e : (planeQForm K 0 1).IsometryEquiv
        (CFSG.LieType.Universal.Spin.quadPlus 1 K) :=
      { toLinearEquiv := LinearEquiv.refl K _
        map_app' := fun v => by
          change CFSG.LieType.Universal.Spin.quadPlus 1 K v = planeQForm K 0 1 v
          rw [coe_planeQForm, CFSG.LieType.Universal.Spin.quadPlus_apply]
          simp [planeQ] }
    exact IsPlusType.of_isometryEquiv e.symm (isPlusType_quadPlus K 1)

omit [Finite K] in
private theorem isPlusType_two : IsPlusType (planeQForm K 2 0) := by
  let e0 : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1
  let e1 : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 1) 1
  let f0 : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inr 0) 1
  let f1 : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inr 1) 1
  let u : Fin 2 ⊕ Fin 2 → K := e0 + e1
  let v : Fin 2 ⊕ Fin 2 → K := e0 + f0 + f1
  have hu : planeQForm K 2 0 u = 0 := by
    rw [coe_planeQForm]
    simp [planeQ, Fin.sum_univ_two, u, e0, e1, CharTwo.add_self_eq_zero]
  have hv : planeQForm K 2 0 v = 0 := by
    rw [coe_planeQForm]
    simp [planeQ, Fin.sum_univ_two, v, e0, f0, f1, CharTwo.add_self_eq_zero]
  have hQ : planeQForm K 2 0 (u + v) = 0 := by
    rw [coe_planeQForm]
    simp [planeQ, Fin.sum_univ_two, u, v, e0, e1, f0, f1, CharTwo.add_self_eq_zero]
  have huv : QuadraticMap.polar (planeQForm K 2 0) u v = 0 := by
    have h := QuadraticMap.map_add (planeQForm K 2 0) u v
    rw [hu, hv] at h
    simp only [zero_add] at h
    exact h.symm.trans hQ
  have hli : LinearIndependent K ![u, v] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrFun hab (Sum.inr 0)
    have h2 := congrFun hab (Sum.inl 1)
    simp [u, v, e0, e1, f0, f1] at h1 h2
    exact ⟨h2, h1⟩
  refine ⟨Submodule.span K (Set.range ![u, v]), ?_, ?_⟩
  · have hspan : Module.finrank K (Submodule.span K (Set.range ![u, v])) = 2 := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    simp only [hspan, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin,
      Fin.val_zero, Nat.add_zero]
  · have hS : ∀ x ∈ Set.range ![u, v], planeQForm K 2 0 x = 0 := by
      rintro x ⟨k, rfl⟩
      fin_cases k
      · exact hu
      · exact hv
    have hvu : QuadraticMap.polar (planeQForm K 2 0) v u = 0 := by
      rw [QuadraticMap.polar_comm]
      exact huv
    have hB : ∀ x ∈ Set.range ![u, v], ∀ y ∈ Set.range ![u, v],
        QuadraticMap.polar (planeQForm K 2 0) x y = 0 := by
      rintro x ⟨k, rfl⟩ y ⟨l, rfl⟩
      fin_cases k <;> fin_cases l
      · rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
      · exact huv
      · exact hvu
      · rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
    exact fun x hx => CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span hS hB hx

omit [Finite K] in
private theorem isPlusType_even (s : ℕ) (δ : Fin 2) (hs : Even s) :
    IsPlusType (planeQForm K s δ) := by
  obtain ⟨k, rfl⟩ := hs
  rw [show k + k = 2 * k from by omega]
  induction k with
  | zero => simpa using isPlusType_zero (K := K) δ
  | succ k ih =>
    have hsplit := splitPlaneForm (K := K) 2 (2 * k) δ
    rw [show 2 * (k + 1) = 2 + 2 * k from by omega]
    exact (isPlusType_congr hsplit).2 (IsPlusType.prod isPlusType_two ih)

private noncomputable def onePlaneIso :
    (planeQForm K 1 0).IsometryEquiv (binForm (1 : K) 1) where
  toLinearEquiv :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin 1) K K).trans
      ((LinearEquiv.funUnique (Fin 1) K K).prodCongr (LinearEquiv.funUnique (Fin 1) K K))
  map_app' := fun v => by
    rw [coe_planeQForm, binForm_apply]
    simp [planeQ, LinearEquiv.sumArrowLequivProdArrow_apply_fst,
      LinearEquiv.sumArrowLequivProdArrow_apply_snd, LinearEquiv.funUnique_apply]
    ring

private theorem isometry_even (s : ℕ) (δ : Fin 2) (hs : Even s) :
    Nonempty ((planeQForm K s δ).IsometryEquiv
      (CFSG.LieType.Universal.Spin.quadPlus (s + δ.val) K)) := by
  let _ : Fintype K := Fintype.ofFinite K
  have hnd := nondegenerate_planeQForm (K := K) (t := s) (δ := δ)
  have hdim : Module.finrank K (Fin (s + δ.val) ⊕ Fin (s + δ.val) → K) =
      2 * (s + δ.val) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  exact nonempty_isometry_quadPlus hnd hdim (isPlusType_even s δ hs)

private theorem isometry_odd (s : ℕ) (δ : Fin 2) (hs : Odd s) :
    Nonempty ((planeQForm K s δ).IsometryEquiv
      (CFSG.LieType.Universal.Spin.quadMinus (s + δ.val) K 1 1)) := by
  obtain ⟨k, rfl⟩ := hs
  have hsplit := splitPlaneForm (K := K) 1 (2 * k) δ
  obtain ⟨eEven⟩ := isometry_even (K := K) (2 * k) δ (even_two_mul k)
  have hmain : Nonempty ((planeQForm K (1 + 2 * k) δ).IsometryEquiv
      ((CFSG.LieType.Universal.Spin.quadPlus (2 * k + δ.val) K).prod
        (binForm (1 : K) 1))) := by
    refine ⟨hsplit.trans ((onePlaneIso.prod eEven).trans ?_)⟩
    exact QuadraticMap.IsometryEquiv.prodComm _ _
  rw [show 2 * k + 1 = 1 + 2 * k from by omega]
  obtain ⟨e⟩ := hmain
  refine ⟨e.trans ?_⟩
  rw [show 1 + 2 * k + δ.val = (2 * k + δ.val) + 1 from by omega]
  simpa using (quadMinusIsometry (2 * k + δ.val + 1) (1 : K) (1 : K)).symm

theorem nonempty_isometryEquiv_planeQForm_quadPlus (s : ℕ) (δ : Fin 2) (hs : Even s) :
    Nonempty ((planeQForm K s δ).IsometryEquiv
      (CFSG.LieType.Universal.Spin.quadPlus (s + δ.val) K)) :=
  isometry_even s δ hs

theorem nonempty_isometryEquiv_planeQForm_quadMinus (s : ℕ) (δ : Fin 2) (hs : Odd s) :
    Nonempty ((planeQForm K s δ).IsometryEquiv
      (CFSG.LieType.Universal.Spin.quadMinus (s + δ.val) K 1 1)) :=
  isometry_odd s δ hs

end CFSG.StandardType.GGQ2Frame.OrthBlocks
