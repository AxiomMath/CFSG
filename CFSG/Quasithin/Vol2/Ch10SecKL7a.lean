module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

abbrev SL32 : Type := ↥(StatedSL 3 (ZMod 2))

abbrev M3 : Type := Multiplicative (Fin 3 → ZMod 2)

abbrev mat (γ : SL32) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ((γ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))

@[expose] def act (γ : SL32) : M3 →* M3 where
  toFun x := natAct (StatedSL 3 (ZMod 2)) γ x
  map_one' := by simp [natAct]
  map_mul' x y := by simp [natAct, Matrix.mulVec_add]

theorem act_apply (γ : SL32) (x : M3) :
    act γ x = Multiplicative.ofAdd (mat γ *ᵥ Multiplicative.toAdd x) := rfl

theorem mat_mul (γ δ : SL32) : mat (γ * δ) = mat γ * mat δ := rfl

theorem mat_one : mat 1 = 1 := rfl

theorem act_mul (γ δ : SL32) (x : M3) : act (γ * δ) x = act γ (act δ x) := by
  simp [act_apply, mat_mul, Matrix.mulVec_mulVec]

theorem act_one' (x : M3) : act 1 x = x := by
  simp [act_apply, mat_one]

theorem act_inv_act (γ : SL32) (x : M3) : act γ⁻¹ (act γ x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one']

theorem act_injective (γ : SL32) : Function.Injective (act γ) := fun x y h => by
  rw [← act_inv_act γ x, h, act_inv_act]

theorem mem_statedSL (g : GL (Fin 3) (ZMod 2)) : g ∈ StatedSL 3 (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSL_zmod_two g

@[expose] noncomputable def mkSL (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : A.det ≠ 0) : SL32 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A h, mem_statedSL _⟩

theorem mat_mkSL (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : A.det ≠ 0) : mat (mkSL A h) = A :=
  rfl

theorem ext_mat {γ δ : SL32} (h : mat γ = mat δ) : γ = δ :=
  Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => congrFun (congrFun h i) j)

theorem eq_one_of_act (γ : SL32) (h : ∀ x : M3, act γ x = x) : γ = 1 := by
  apply ext_mat
  ext i j
  have hj := congrArg Multiplicative.toAdd (h (Multiplicative.ofAdd (Pi.single j 1)))
  simp only [act_apply, toAdd_ofAdd, Matrix.mulVec_single_one] at hj
  have hij := congrFun hj i
  rw [Matrix.col_apply] at hij
  rw [hij, mat_one, Matrix.one_apply, Pi.single_apply]

theorem iterate_two_of_index_two {V : Type*} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (f : V →* V)
    (hf : Function.Injective f) (H : Subgroup V) (hH : ∀ v, v ∈ H ↔ f v = v) (h2 : H.index = 2)
    (v : V) : f (f v) = v := by
  by_cases hv : v ∈ H
  · rw [(hH v).1 hv, (hH v).1 hv]
  · have hfv : f v ∉ H := fun hfv => hv ((hH v).2 (hf ((hH (f v)).1 hfv)))
    have hmem : f v * v⁻¹ ∈ H := by
      rw [Subgroup.mul_mem_iff_of_index_two h2, inv_mem_iff]
      exact iff_of_false hfv hv
    have hfix := (hH _).1 hmem
    have hsq := hV (f v * v⁻¹)
    calc f (f v) = f (f v * v⁻¹ * v) := by rw [inv_mul_cancel_right]
      _ = f (f v * v⁻¹) * f v := by rw [map_mul]
      _ = (f v * v⁻¹) * (f v * v⁻¹) * v := by rw [hfix]; group
      _ = v := by rw [← sq, hsq, one_mul]

@[expose] def fixM (γ : SL32) : Subgroup M3 := (act γ).eqLocus (MonoidHom.id M3)

theorem mem_fixM {γ : SL32} {x : M3} : x ∈ fixM γ ↔ act γ x = x := Iff.rfl

theorem sq_M3 (x : M3) : x ^ 2 = 1 := by
  rw [← ofAdd_toAdd x, ← ofAdd_nsmul, two_nsmul, CharTwo.add_self_eq_zero, ofAdd_zero]

theorem sq_eq_one_of_index_two (γ : SL32) (h : (fixM γ).index = 2) : γ ^ 2 = 1 := by
  apply eq_one_of_act
  intro x
  rw [pow_two, act_mul]
  exact iterate_two_of_index_two sq_M3 (act γ) (act_injective γ) (fixM γ) (fun _ => Iff.rfl) h x

theorem eq_one_of_fixM_eq_top (γ : SL32) (h : fixM γ = ⊤) : γ = 1 :=
  eq_one_of_act γ fun x => (h ▸ Subgroup.mem_top x : x ∈ fixM γ)

@[expose] def tP : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def tQ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

@[expose] def tR : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 0; 1, 0, 1]

theorem det_tP : tP.det ≠ 0 := by rw [Matrix.det_fin_three]; decide

theorem det_tQ : tQ.det ≠ 0 := by rw [Matrix.det_fin_three]; decide

theorem det_tR : tR.det ≠ 0 := by rw [Matrix.det_fin_three]; decide

theorem tP_mul_tQ_ne : tP * tQ ≠ tQ * tP := by decide

theorem fix_tPQR : ∀ v : Fin 3 → ZMod 2, tP *ᵥ v = v → tQ *ᵥ v = v → tR *ᵥ v = v → v = 0 := by
  decide

theorem eq_one_of_forall_act (x : M3) (h : ∀ γ : SL32, act γ x = x) : x = 1 := by
  have hP := congrArg Multiplicative.toAdd (h (mkSL tP det_tP))
  have hQ := congrArg Multiplicative.toAdd (h (mkSL tQ det_tQ))
  have hR := congrArg Multiplicative.toAdd (h (mkSL tR det_tR))
  simp only [act_apply, mat_mkSL, toAdd_ofAdd] at hP hQ hR
  rw [← ofAdd_toAdd x, fix_tPQR _ hP hQ hR, ofAdd_zero]

@[expose] def compl (y : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  if y 0 = 1 then !![y 0, 0, 0; y 1, 1, 0; y 2, 0, 1]
  else if y 1 = 1 then !![y 0, 1, 0; y 1, 0, 0; y 2, 0, 1]
  else !![y 0, 1, 0; y 1, 0, 1; y 2, 0, 0]

theorem compl_spec : ∀ y : Fin 3 → ZMod 2, y ≠ 0 →
    (compl y 0 0 * compl y 1 1 * compl y 2 2 - compl y 0 0 * compl y 1 2 * compl y 2 1 -
      compl y 0 1 * compl y 1 0 * compl y 2 2 + compl y 0 1 * compl y 1 2 * compl y 2 0 +
      compl y 0 2 * compl y 1 0 * compl y 2 1 - compl y 0 2 * compl y 1 1 * compl y 2 0) ≠ 0 ∧
    compl y *ᵥ Pi.single 0 1 = y := by
  decide

theorem det_compl {y : Fin 3 → ZMod 2} (hy : y ≠ 0) : (compl y).det ≠ 0 := by
  rw [Matrix.det_fin_three]
  exact (compl_spec y hy).1

theorem exists_act_e₀ (x : M3) (hx : x ≠ 1) :
    ∃ γ : SL32, act γ (Multiplicative.ofAdd (Pi.single 0 1)) = x := by
  have hx' : Multiplicative.toAdd x ≠ 0 := fun h => hx (by rw [← ofAdd_toAdd x, h, ofAdd_zero])
  refine ⟨mkSL (compl (Multiplicative.toAdd x)) (det_compl hx'), ?_⟩
  rw [act_apply, mat_mkSL, toAdd_ofAdd, (compl_spec _ hx').2, ofAdd_toAdd]

theorem exists_act_eq (x y : M3) (hx : x ≠ 1) (hy : y ≠ 1) : ∃ γ : SL32, act γ x = y := by
  obtain ⟨a, ha⟩ := exists_act_e₀ x hx
  obtain ⟨b, hb⟩ := exists_act_e₀ y hy
  refine ⟨b * a⁻¹, ?_⟩
  rw [act_mul, ← ha, act_inv_act, hb]

theorem invariant_eq_bot_or_top (U : Subgroup M3) (hU : ∀ γ : SL32, ∀ u ∈ U, act γ u ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  · right
    obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h
    refine eq_top_iff.2 fun y _ => ?_
    rcases eq_or_ne y 1 with rfl | hy
    · exact U.one_mem
    · obtain ⟨γ, hγ⟩ := exists_act_eq (u : M3) y (fun h1 => hu1 (Subtype.ext h1)) hy
      exact hγ ▸ hU γ u u.2

theorem statedSL_eq_top : StatedSL 3 (ZMod 2) = ⊤ :=
  eq_top_iff.2 fun g _ => mem_statedSL g

theorem card_SL32 : Nat.card SL32 = 168 := by
  rw [Nat.card_congr ((MulEquiv.subgroupCongr statedSL_eq_top).trans Subgroup.topEquiv).toEquiv,
    Matrix.card_GL_field, ZMod.card]
  decide

theorem isSimpleGroup_SL32 : IsSimpleGroup SL32 := by
  have := CFSG.QuasithinUnique.Bridge.isSimple_sl_zmod2 3 le_rfl
  exact (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm.isSimpleGroup

theorem eq_one_of_commute_all (γ : SL32) (h : ∀ δ : SL32, γ * δ = δ * γ) : γ = 1 := by
  have := isSimpleGroup_SL32
  have hc : γ ∈ Subgroup.center SL32 := Subgroup.mem_center_iff.2 fun δ => (h δ).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center SL32) with h0 | h0
  · rw [h0] at hc
    exact hc
  · exfalso
    have hPQ := Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top (mkSL tP det_tP)) (mkSL tQ det_tQ)
    apply tP_mul_tQ_ne
    have := congrArg mat hPQ
    rwa [mat_mul, mat_mul, mat_mkSL, mat_mkSL, eq_comm] at this

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
