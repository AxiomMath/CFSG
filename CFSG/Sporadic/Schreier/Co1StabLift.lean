module

public import CFSG.Sporadic.Schreier.Co1QuotCheck
public import CFSG.Sporadic.Schreier.Co1Lift
public import CFSG.Sporadic.SuzOddCore.LiftedValid
public import CFSG.Sporadic.Co2

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD toVecD_xor toVecD_injective rowsMatrix)
open CFSG.Sporadic.SmallF2.Native Matrix CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2
  CFSG.Certificates

@[expose] noncomputable def quotRep (k : ℕ) : Vec24 := toVecD 24 Data.liftReps.toArray[k]!

@[expose] noncomputable def quotPerm0 : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 Data.quotAct0.toArray

@[expose] noncomputable def quotPerm1 : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 Data.quotAct1.toArray

@[expose] noncomputable def stabG0 : stabH := ⟨stabH0, stabH0_mem⟩

@[expose] noncomputable def stabG1 : stabH := ⟨stabH1, stabH1_mem⟩

@[expose] noncomputable def stabU :
    Vector stabH co2Q.originalCount :=
  ⟨#[stabG0, stabG1], by rw [co2Q_originalCount]; rfl⟩

@[expose] noncomputable def stabW : GL24 := stabH0⁻¹ * stabH1 * stabH1 * stabH0 * stabH1 * stabH0⁻¹

theorem quot_facts : Data.quotAct0.toArray = co2OrigArrs[0]! ∧
    Data.quotAct1.toArray = co2OrigArrs[1]! ∧ Native.hRows0 = Data.subRows0.toArray ∧
    Native.hRows1 = Data.subRows1.toArray := by
  have h := quot_check
  simp only [Native.quotCheck, Native.quotCheckOf, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem quotFixed_eq : toVecD 24 Data.quotFixed = stabVecOf 0 := rfl

theorem quotRep_eq {k : ℕ} (hk : k < 2300) : quotRep k = clsV k := (clsV_lt hk).symm

theorem clsHom_stabG0 :
    clsHom stabG0 = co2Gen 0 := clsHom_gen0

theorem clsHom_stabG1 :
    clsHom stabG1 = co2Gen 1 := clsHom_gen1

theorem stabU_get (j : Fin co2Q.originalCount) :
    stabU.get j = if (j : ℕ) = 0 then stabG0 else stabG1 := by
  have hj : (j : ℕ) < 2 := lt_of_lt_of_eq j.2 co2Q_originalCount
  rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 by omega) with h | h
  · simp only [h, ↓reduceIte]
    show #[stabG0, stabG1][(j : ℕ)] = stabG0
    simp only [h]
    rfl
  · simp only [h, one_ne_zero, ↓reduceIte]
    show #[stabG0, stabG1][(j : ℕ)] = stabG1
    simp only [h]
    rfl

theorem clsHom_stabU
    (j : Fin co2Q.originalCount) : clsHom (stabU.get j) = co2Q.original.get j := by
  have hj : (j : ℕ) < 2 := lt_of_lt_of_eq j.2 co2Q_originalCount
  rw [co2Q_original_get, stabU_get]
  rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 by omega) with h | h
  · simp only [h, ↓reduceIte]
    exact clsHom_stabG0
  · simp only [h, one_ne_zero, ↓reduceIte]
    exact clsHom_stabG1

theorem clsHom_injective :
    Function.Injective clsHom := fun g g' h =>
  stabPermEquiv.injective (Subtype.ext (show (stabPermEquiv g : Equiv.Perm (Fin 2300)) =
    stabPermEquiv g' by rw [stabPermEquiv_apply, stabPermEquiv_apply]; exact h))

theorem stab_mem_lifted
    {g : GL24} (hg' : g ∈ Subgroup.closure ({stabH0, stabH1} : Set GL24)) :
    ∀ hg : g ∈ stabH, (⟨g, hg⟩ : stabH) ∈ co2Q.liftedOriginalSubgroup stabU := by
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    intro hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [stab_mk_eq hg stabH0_mem hx]
      exact Subgroup.subset_closure (show stabG0 ∈ stabU.toList from List.mem_cons_self ..)
    · rw [stab_mk_eq hg stabH1_mem hx]
      exact Subgroup.subset_closure
        (show stabG1 ∈ stabU.toList from List.mem_cons_of_mem _ (List.mem_cons_self ..))
  | one =>
    intro hg
    exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    intro hg
    have hx' : x ∈ stabH := hx
    have hy' : y ∈ stabH := hy
    rw [show (⟨x * y, hg⟩ : stabH) = ⟨x, hx'⟩ * ⟨y, hy'⟩ from rfl]
    exact Subgroup.mul_mem _ (ihx hx') (ihy hy')
  | inv x hx ih =>
    intro hg
    have hx' : x ∈ stabH := hx
    rw [show (⟨x⁻¹, hg⟩ : stabH) = (⟨x, hx'⟩ : stabH)⁻¹ from rfl]
    exact Subgroup.inv_mem _ (ih hx')

theorem liftedOriginalSubgroup_stabU :
    co2Q.liftedOriginalSubgroup stabU = ⊤ :=
  eq_top_iff.mpr fun g _ => stab_mem_lifted g.2 g.2

theorem validLiftedSchreier_stab :
    ValidLiftedSchreier co2Q clsHom stabU :=
  CFSG.Sporadic.SuzOddCore.validLiftedSchreier_of_injOn co2Q_valid.1 clsHom_stabU
    fun _ _ hx => clsHom_injective (hx.trans (map_one clsHom).symm)

theorem stabPermEquiv_symm
    (j : Fin co2Q.originalCount) (hj : co2Q.original.get j ∈ co2P) :
    stabPermEquiv.symm ⟨co2Q.original.get j, hj⟩ = stabU.get j := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [stabPermEquiv_apply, clsHom_stabU]

theorem isSimpleGroup_stabH :
    IsSimpleGroup stabH :=
  @MulEquiv.isSimpleGroup (↥stabH) (Subgroup.toGroup stabH) Blueprint.NativeSporadic.Co2
    Units.instGroup CFSG.Sporadic.Co2.isSimpleGroup_Co2 stabCo2Equiv

@[expose] noncomputable def stabWS : stabH :=
  stabG0⁻¹ * stabG1 * stabG1 * stabG0 * stabG1 * stabG0⁻¹

@[expose] noncomputable def stabTS : stabH := stabG0 * stabWS⁻¹ * stabG1 * stabWS

theorem coe_stabG0 : (stabG0 : GL24) = stabH0 := by
  rw [show stabG0 = ⟨stabH0, stabH0_mem⟩ from rfl]

theorem coe_stabG1 : (stabG1 : GL24) = stabH1 := by
  rw [show stabG1 = ⟨stabH1, stabH1_mem⟩ from rfl]

theorem coe_stabTS : (stabTS : GL24) = stabH0 * stabW⁻¹ * stabH1 * stabW := by
  rw [stabTS, stabWS, stabW]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_stabG0, coe_stabG1]

theorem orderOf_stabT :
    orderOf (stabH0 * stabW⁻¹ * stabH1 * stabW) = 23 := by
  have hw : clsHom stabWS = co2W := by
    rw [co2W_eq, stabWS]
    simp only [map_mul, map_inv, clsHom_stabG0, clsHom_stabG1]
  have himg : clsHom stabTS = co2cGen 0 * co2cGen 1 := by
    rw [co2cGen_zero, co2cGen_one, stabTS]
    simp only [map_mul, map_inv, clsHom_stabG0, clsHom_stabG1, hw, mul_assoc]
  rw [← coe_stabTS, Subgroup.orderOf_coe, ← orderOf_injective clsHom clsHom_injective stabTS,
    himg, orderOf_co2cGen_mul]

theorem fam_co1_stabilizer_lift :
    stabH ≤ GA ∧
    ((stabH0 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = rowsMatrix 24 Data.subRows0.toArray ∧
      (stabH1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = rowsMatrix 24 Data.subRows1.toArray) ∧
    Data.quotFixed = Data.stabVecs.getD 0 0 ∧
    (∀ h ∈ stabH, ((h : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ toVecD 24 Data.quotFixed =
      toVecD 24 Data.quotFixed) ∧
    (∀ j k, j < 2300 → k < 2300 →
      (quotRep j = quotRep k ∨ quotRep j = toVecD 24 Data.quotFixed + quotRep k) → j = k) ∧
    (∀ (g : stabH) (k : Fin 2300),
      ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ quotRep k = quotRep (clsHom g k) ∨
        ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ quotRep k =
          toVecD 24 Data.quotFixed + quotRep (clsHom g k)) ∧
    (∀ j : Fin co2Q.originalCount, clsHom (stabU.get j) = co2Q.original.get j) ∧
    (quotPerm0 = co2Gen 0 ∧ quotPerm1 = co2Gen 1 ∧
      ∀ j : Fin co2Q.originalCount, co2Q.original.get j = co2Gen j) ∧
    ValidLiftedSchreier co2Q clsHom stabU ∧ co2Q.liftedOriginalSubgroup stabU = ⊤ ∧
    co2Q.originalSubgroup = co2P ∧
    (∃ e : stabH ≃* co2P, (∀ g : stabH, (e g : Equiv.Perm (Fin 2300)) = clsHom g) ∧
      ∀ (j : Fin co2Q.originalCount) (hj : co2Q.original.get j ∈ co2P),
        e.symm ⟨co2Q.original.get j, hj⟩ = stabU.get j) ∧
    Nonempty (stabH ≃* Blueprint.NativeSporadic.Co2) ∧ Nontrivial stabH ∧ IsSimpleGroup stabH ∧
    Nat.card stabH = 42305421312000 ∧
    orderOf (stabH0 * stabW⁻¹ * stabH1 * stabW) = 23 := by
  obtain ⟨hq0, hq1, hr0, hr1⟩ := quot_facts
  have hsimple := isSimpleGroup_stabH
  refine ⟨stabH_le_GA, ⟨?_, ?_⟩, rfl, fun h hh => stabH_fix_z hh, fun j k hj hk h => ?_,
    fun g k => ?_, clsHom_stabU, ⟨?_, ?_, co2Q_original_get⟩, validLiftedSchreier_stab,
    liftedOriginalSubgroup_stabU, co2Q_originalSubgroup, ⟨stabPermEquiv, stabPermEquiv_apply,
      stabPermEquiv_symm⟩, ⟨stabCo2Equiv⟩, inferInstance, hsimple, card_stabH, orderOf_stabT⟩
  · rw [← hr0]
    exact stabH0_rep.symm
  · rw [← hr1]
    exact stabH1_rep.symm
  · rw [quotRep_eq hj, quotRep_eq hk, quotFixed_eq, ← clsV_add hk] at h
    rcases h with h | h
    · exact clsV_inj (by omega) (by omega) h
    · have := clsV_inj (by omega) (by omega) h
      omega
  · have h := clsAct_spec g k
    rw [quotRep_eq k.2, quotRep_eq (clsHom g k).2, quotFixed_eq, ← clsV_add (clsHom g k).2]
    exact h
  · rw [quotPerm0, hq0]
    rfl
  · rw [quotPerm1, hq1]
    rfl

end CFSG.Sporadic.Co1Schreier
