module

public import CFSG.Sporadic.Co1Patterson.TwistNativeType
public import CFSG.Sporadic.Co1Patterson.TwistModel
public import CFSG.LargeExtraspecial.S4CEOmegaSpin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.LargeExtraspecial CFSG.LieType.Universal.Spin
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalGroups.Orthogonal (eichler)
open CFSG.LocalAnalysis.ComponentInitial (orthElementaryGroup)

@[expose] def HasCols (f : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (m : List ℕ) : Prop :=
  ∀ k, k < 8 → f (bv (2 ^ k)) = bv (m.getD k 0)

theorem HasCols.apply {f : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)} {m : List ℕ}
    (h : HasCols f m) (v : ℕ) : f (bv v) = bv (colsApply m v) :=
  apply_bv_of_cols f m h v

theorem HasCols.comp {f g : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)} {m n : List ℕ}
    (hf : HasCols f m) (hg : HasCols g n) : HasCols (f ∘ₗ g) (colsMul m n) := fun k hk => by
  have e : (colsMul m n).getD k 0 = colsApply m (n.getD k 0) := by
    rw [colsMul, List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_map, List.getElem_range]
  rw [LinearMap.comp_apply, hg k hk, hf.apply, e]

theorem hasCols_id : HasCols LinearMap.id idCols := fun k hk => by
  rw [idCols, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

theorem HasCols.ext {f g : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)} {m : List ℕ}
    (hf : HasCols f m) (hg : HasCols g m) : f = g :=
  linearMap_ext_bv fun k hk => by rw [hf k hk, hg k hk]

theorem finrank_plus : Module.finrank (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) = 8 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

theorem L₀_map_plusCoords :
    L₀.map (Bridge.conjLinearEquiv plusCoords).toMonoidHom =
      CFSG.Open.timmesfeldOmega (quadPlus 4 (ZMod 2)) :=
  Bridge.omega_map plusCoords fun v => quadPlus_plusCoords v

theorem timmesfeldOmega_quadPlus :
    CFSG.Open.timmesfeldOmega (quadPlus 4 (ZMod 2)) =
      orthElementaryGroup (quadPlus 4 (ZMod 2)) := by
  rw [s12_timmesfeldOmega_eq _ (nondegenerate_polarBilin_quadPlus 4 (ZMod 2)),
    S4.omegaGroup_eq_elementaryGroup (nondegenerate_polarBilin_quadPlus 4 (ZMod 2))
      (by rw [finrank_plus]; norm_num)
      (CFSG.ClassicalGroups.Orthogonal.plusPair_orth (K := ZMod 2) (n := 4) (i := 0) (j := 1)
        (by decide))]
  rfl

@[expose] noncomputable def elemEquiv : L₀ ≃* orthElementaryGroup (quadPlus 4 (ZMod 2)) :=
  (L₀.equivMapOfInjective _ (Bridge.conjLinearEquiv plusCoords).injective).trans
    (MulEquiv.subgroupCongr (L₀_map_plusCoords.trans timmesfeldOmega_quadPlus))

theorem coe_elemEquiv (l : L₀) (w : Fin 4 ⊕ Fin 4 → ZMod 2) :
    ((elemEquiv l : orthElementaryGroup (quadPlus 4 (ZMod 2))) :
      (Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] _) w =
      plusCoords ((l : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (plusCoords.symm w)) :=
  rfl

theorem map_foldl_mul {G G' : Type*} [Monoid G] [Monoid G'] (f : G →* G') (l : List ℕ)
    (x : ℕ → G) (g : G) :
    f (l.foldl (fun b i => b * x i) g) = l.foldl (fun b i => b * f (x i)) (f g) := by
  induction l generalizing g with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons, ih, map_mul]

theorem rhoPow_lt (k : ℕ) {j : ℕ} (hj : j < 8) : rhoPow k j < 8 := by
  induction k with
  | zero => exact hj
  | succ k ih => exact rhoPerm_lt ih

theorem rhoPow_liftLetter {k j : ℕ} (hk : k < 3) (hj : j < 8) : rhoPow k (liftLetter k j) = j := by
  interval_cases k <;> interval_cases j <;> rfl

theorem liftLetter_lt {k j : ℕ} (hj : j < 8) : liftLetter k j < 8 := rhoPow_lt _ hj

theorem wordPerm_append (l l' : List ℕ) : wordPerm (l ++ l') = wordPerm l * wordPerm l' := by
  rw [wordPerm, List.map_append, List.prod_append]
  rfl


@[expose] noncomputable def iotaC : L₀ ≃* omegaT :=
  elemEquiv.trans ((elementaryOmega1Equiv card_zmod_two).trans omegaRestrictEquiv.symm)

@[expose] noncomputable def eichL (j : ℕ) : L₀ := elemEquiv.symm (eichGen (ZMod 2) j)

theorem hasCols_eichL {j : ℕ} (hj : j < 8) :
    HasCols ((eichL j : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (eichCols j) :=
  fun k hk => by
  have e : ∀ x : ℕ, ((eichL j : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (bv x) =
      bv (eichNat (pair0 j).1 (pair0 j).2 x) := fun x => by
    have h1 := coe_elemEquiv (eichL j) (vecK (ZMod 2) x)
    rw [eichL, MulEquiv.apply_symm_apply] at h1
    have h2 := congrArg plusCoords.symm h1
    rw [LinearEquiv.symm_apply_apply] at h2
    rw [bv, eichL, ← h2]
    obtain ⟨hq, hb, -, -⟩ := pair0_ok hj
    exact congrArg plusCoords.symm (eichler_vecK card_zmod_two hq hb x)
  rw [LinearEquiv.coe_coe, e, eichCols, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp [pair0]

theorem iotaC_eichL {j : ℕ} (hj : j < 8) : iotaC (eichL j) = ⟨gen j, gen_mem_omegaT hj⟩ := by
  rw [iotaC, MulEquiv.trans_apply, MulEquiv.trans_apply, eichL, MulEquiv.apply_symm_apply,
    MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [omegaRestrictEquiv_apply, omegaRes_gen hj]
  exact act0_eichGen card_zmod_two hj

theorem hasCols_mul {l l' : L₀} {m n : List ℕ}
    (h : HasCols ((l : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) m)
    (h' : HasCols ((l' : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) n) :
    HasCols ((l * l' : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (colsMul m n) :=
  HasCols.comp h h'

theorem hasCols_one : HasCols ((1 : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) idCols :=
  hasCols_id

@[expose] noncomputable def eichWord (w : List ℕ) : L₀ := w.foldl (fun acc j => acc * eichL j) 1

theorem hasCols_eichWord (w : List ℕ) (hw : ∀ j ∈ w, j < 8) :
    HasCols ((eichWord w : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (wordCols w) := by
  have key : ∀ (l : L₀) (m : List ℕ), HasCols ((l : L₀) :
      (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) m →
      HasCols ((w.foldl (fun acc j => acc * eichL j) l : L₀) :
        (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))
        (w.foldl (fun acc j => colsMul acc (eichCols j)) m) := by
    induction w with
    | nil => exact fun _ _ h => h
    | cons j w ih =>
      intro l m h
      exact ih (fun i hi => hw i (List.mem_cons_of_mem _ hi)) _ _
        (hasCols_mul h (hasCols_eichL (hw j List.mem_cons_self)))
  exact key 1 idCols hasCols_one

theorem trialityAut_pow_gen (k : ℕ) {i : ℕ} (hi : i < 8) :
    (trialityAut ^ k) ⟨gen i, gen_mem_omegaT hi⟩ =
      ⟨gen (rhoPow k i), gen_mem_omegaT (rhoPow_lt k hi)⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih]
    apply Subtype.ext
    rw [trialityAut_apply, Cover.coe_triality, conj_gen_rho (rhoPow_lt k hi)]
    rfl

theorem omegaRestrictEquiv_symm_gen1 {i : ℕ} (hi : i < 8) :
    omegaRestrictEquiv.symm ⟨gen1 i, (omega1T_eq ▸ subset_closure ⟨i, hi, rfl⟩ :
      gen1 i ∈ omega1T)⟩ = ⟨gen i, gen_mem_omegaT hi⟩ := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [omegaRestrictEquiv_apply, omegaRes_gen hi]

@[expose] noncomputable def omLiftW (i : ℕ) : wPlus :=
  if h : i < 8 then ⟨omLift i, omLift_mem h⟩ else 1

@[expose] noncomputable def liftWord (k : ℕ) (w : List ℕ) : wPlus :=
  w.foldl (fun acc j => acc * omLiftW (liftLetter k j)) 1

theorem pOnto_omLiftW {i : ℕ} (hi : i < 8) :
    pOnto (omLiftW i) = ⟨gen1 i, (omega1T_eq ▸ subset_closure ⟨i, hi, rfl⟩ :
      gen1 i ∈ omega1T)⟩ := by
  rw [omLiftW, dite_eq_left hi]
  exact Subtype.ext (pPlus_omLift hi)

theorem wPlusMap_omLiftW (k : Fin 3) {j : ℕ} (hj : j < 8) :
    wPlusMap iotaC k (omLiftW (liftLetter k j)) = eichL j := by
  rw [wPlusMap_apply, pOnto_omLiftW (liftLetter_lt hj), omegaRestrictEquiv_symm_gen1
    (liftLetter_lt hj), trialityAut_pow_gen _ (liftLetter_lt hj), MulEquiv.symm_apply_eq,
    iotaC_eichL hj]
  exact Subtype.ext (congrArg gen (rhoPow_liftLetter k.2 hj))

theorem wPlusMap_liftWord (k : Fin 3) (w : List ℕ) (hw : ∀ j ∈ w, j < 8) :
    wPlusMap iotaC k (liftWord k w) = eichWord w := by
  rw [liftWord, map_foldl_mul, map_one, eichWord]
  exact List.foldl_ext _ _ _ fun b j hj => by rw [wPlusMap_omLiftW k (hw j hj)]

theorem coe_liftWord (k : ℕ) (w : List ℕ) (hw : ∀ j ∈ w, j < 8) :
    ((liftWord k w : wPlus) : Equiv.Perm (Fin 240)) =
      wordPerm (w.flatMap fun j => omWords.getD (liftLetter k j) []) := by
  have key : ∀ (acc : wPlus) (L : List ℕ), (acc : Equiv.Perm (Fin 240)) = wordPerm L →
      ((w.foldl (fun acc j => acc * omLiftW (liftLetter k j)) acc : wPlus) :
        Equiv.Perm (Fin 240)) =
          wordPerm (L ++ w.flatMap fun j => omWords.getD (liftLetter k j) []) := by
    induction w with
    | nil => intro acc L h; simpa using h
    | cons j w ih =>
      intro acc L h
      rw [List.foldl_cons, List.flatMap_cons, ← List.append_assoc]
      refine ih (fun i hi => hw i (List.mem_cons_of_mem _ hi)) _ _ ?_
      rw [Subgroup.coe_mul, h, wordPerm_append, omLiftW, dite_eq_left (liftLetter_lt
        (hw j List.mem_cons_self))]
      rfl
  have h := key 1 [] rfl
  rwa [List.nil_append] at h

end CFSG.Sporadic.Co1Patterson.TwistNative
