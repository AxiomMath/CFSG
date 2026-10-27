module

public import CFSG.Timmesfeld.Transvection.PresSUModel
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUEmbed
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
public import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.Timmesfeld.Transvection.Pres

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
  CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement BigOperators

variable (r : ℕ)

private theorem two_mul_div_two (r : ℕ) : 2 * r / 2 = r := Nat.mul_div_right r (by norm_num)

private theorem two_mul_add_one_div_two (r : ℕ) : (2 * r + 1) / 2 = r := by
  rw [Nat.mul_add_div (by norm_num) r 1, Nat.div_eq_of_lt (by norm_num : 1 < 2), add_zero]

@[expose] def skipMid : Fin (2 * r) → Fin (2 * r + 1) := Fin.succAbove ⟨r, by omega⟩

theorem skipMid_injective : Function.Injective (skipMid r) :=
  Fin.succAbove_right_injective

theorem skipMid_rev (i : Fin (2 * r)) : skipMid r (Fin.rev i) = Fin.rev (skipMid r i) := by
  have hp : (⟨r, by omega⟩ : Fin (2 * r + 1)).rev = ⟨r, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_mk]
    omega
  have h := Fin.succAbove_rev_left (⟨r, by omega⟩ : Fin (2 * r + 1)) (Fin.rev i)
  rwa [hp, Fin.rev_rev] at h

theorem midIdx_odd : midIdx (2 * r + 1) (Nat.not_even_two_mul_add_one r) =
    ⟨r, Nat.lt_add_one_iff.mpr (Nat.le_mul_of_pos_left r Nat.two_pos)⟩ := by
  apply Fin.ext
  simp only [midIdx]
  omega

theorem skipMid_ne_midIdx (i : Fin (2 * r)) :
    skipMid r i ≠ midIdx (2 * r + 1) (Nat.not_even_two_mul_add_one r) := by
  rw [midIdx_odd]
  exact Fin.succAbove_ne _ i

theorem exists_skipMid_eq {j : Fin (2 * r + 1)} (hj : j ≠ Fin.rev j) : ∃ i, skipMid r i = j := by
  have hne : j ≠ (⟨r, by omega⟩ : Fin (2 * r + 1)) := by
    intro h
    apply hj
    rw [h]
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_mk]
    omega
  obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hne
  exact ⟨i, by rwa [skipMid]⟩

@[expose] def finCastOdd : Fin (2 * r / 2) ≃ Fin ((2 * r + 1) / 2) := finCongr (by omega)

@[expose] def sCast : Fin (2 * r / 2) ⊕ Fin (2 * r / 2) ≃
    Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2) :=
  Equiv.sumCongr (finCastOdd r) (finCastOdd r)

private theorem finCastOdd_val (a : Fin (2 * r / 2)) : (finCastOdd r a).val = a.val := rfl

private theorem finCastOdd_symm_val (a : Fin ((2 * r + 1) / 2)) :
    ((finCastOdd r).symm a).val = a.val := rfl

private theorem skipMid_lowIdx (a : Fin (2 * r / 2)) :
    skipMid r (lowIdx a) = lowIdx (finCastOdd r a) := by
  rw [skipMid, Fin.succAbove_of_castSucc_lt]
  · apply Fin.ext
    simp only [Fin.val_castSucc, val_lowIdx, lowIdx, finCastOdd_val]
  · simp only [Fin.lt_def, Fin.val_castSucc, val_lowIdx]
    have hd := two_mul_div_two r
    have := a.isLt
    omega

theorem skipMid_crd (a : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) :
    skipMid r (crd a) = crd (sCast r a) := by
  rcases a with a | a
  · rw [crd_inl, sCast, Equiv.sumCongr_apply, Sum.map_inl, crd_inl]
    exact skipMid_lowIdx r a
  · rw [crd_inr, sCast, Equiv.sumCongr_apply, Sum.map_inr, crd_inr, skipMid_rev]
    exact congrArg Fin.rev (skipMid_lowIdx r a)

theorem sCast_swap (a : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) :
    sCast r (Sum.swap a) = Sum.swap (sCast r a) := by
  rcases a with a | a <;> rfl

theorem idx_sCast (a : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) :
    idx (sCast r a) = finCastOdd r (idx a) := by
  rcases a with a | a <;> rfl

theorem idx_sCast_ne {a b : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)} (h : idx a ≠ idx b) :
    idx (sCast r a) ≠ idx (sCast r b) := by
  rw [idx_sCast, idx_sCast]
  exact fun e => h ((finCastOdd r).injective e)

theorem weight_skipMid (i : Fin (2 * r)) :
    weight (2 * r + 1) (skipMid r i) = weight (2 * r) i ∘ (finCastOdd r).symm := by
  funext a
  rw [Function.comp_apply, weight_apply', weight_apply', skipMid, Fin.val_succAbove,
    finCastOdd_symm_val]
  simp only [Fin.val_mk]
  have hd := two_mul_add_one_div_two r
  split_ifs <;> omega

@[expose] def rootCast (γ : Fin (2 * r / 2) → ℤ) : Fin ((2 * r + 1) / 2) → ℤ :=
  fun a => (if a.val + 1 = r then 2 else 1) * γ ((finCastOdd r).symm a)

private theorem symplectic_toStd_two_mul (v : Fin (2 * r / 2) → ℤ)
    (a : Fin (2 * r / 2)) :
    CFSG.LieType.Universal.Symplectic.toStd (2 * r / 2) v a =
      (if a.val + 1 = r then 2 else 1) * v a -
        (if h : 0 < a.val then
          v ⟨a.val - 1, by have hd := two_mul_div_two r; have := a.isLt; omega⟩ else 0) := by
  unfold CFSG.LieType.Universal.Symplectic.toStd
  by_cases h : a.val + 1 = 2 * r / 2
  · have h' : a.val + 1 = r := by
      have hd := two_mul_div_two r
      omega
    rw [if_pos h, if_pos h']
  · have h' : ¬ a.val + 1 = r := by
      intro hh
      apply h
      omega
    rw [if_neg h, if_neg h']

theorem toStd_rootCast (γ : Fin (2 * r / 2) → ℤ) :
    toStd (2 * r + 1) (rootCast r γ) = toStd (2 * r) γ ∘ (finCastOdd r).symm := by
  funext a
  have hodd : ¬ Even (2 * r + 1) := Nat.not_even_two_mul_add_one r
  have heven : Even (2 * r) := even_two_mul r
  have hbval : ((finCastOdd r).symm a).val = a.val := finCastOdd_symm_val r a
  have hb1 : a.val - 1 < 2 * r / 2 := by
    have hd := two_mul_div_two r
    have := a.isLt
    omega
  have hb2 : a.val - 1 < (2 * r + 1) / 2 := by
    have hd := two_mul_add_one_div_two r
    have := a.isLt
    omega
  unfold CFSG.LieType.Universal.Unitary.toStd rootCast
  rw [if_neg hodd, if_pos heven]
  simp only [Function.comp_apply, symplectic_toStd_two_mul, hbval]
  by_cases h0 : 0 < a.val
  · rw [dif_pos h0, dif_pos h0]
    rw [if_neg (by omega : ¬ (a.val - 1) + 1 = r), one_mul]
    congr 1
  · simp only [dif_neg h0]

private def rootCastInv (γ : Fin ((2 * r + 1) / 2) → ℤ) : Fin (2 * r / 2) → ℤ :=
  fun b => if b.val + 1 = r then γ (finCastOdd r b) / 2 else γ (finCastOdd r b)

private theorem rootCast_rootCastInv (hr : 1 ≤ r) {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (h : Even (γ ⟨r - 1, by omega⟩)) : rootCast r (rootCastInv r γ) = γ := by
  funext a
  have hbval : ((finCastOdd r).symm a).val = a.val := finCastOdd_symm_val r a
  simp only [rootCast, rootCastInv]
  by_cases ha : a.val + 1 = r
  · rw [if_pos ha, if_pos (by rw [hbval]; exact ha)]
    have ha' : a = ⟨r - 1, by
        have hd := two_mul_add_one_div_two r
        omega⟩ := by
      apply Fin.ext
      show a.val = r - 1
      omega
    have hEven : Even (γ a) := by
      rw [ha']
      exact h
    rw [Equiv.apply_symm_apply, Int.two_mul_ediv_two_of_even hEven]
  · rw [if_neg ha, if_neg (by rw [hbval]; exact ha), one_mul, Equiv.apply_symm_apply]

theorem exists_rootCast_eq (hr : 1 ≤ r) {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (h : Even (γ ⟨r - 1, Nat.lt_of_lt_of_le (Nat.sub_one_lt_of_lt hr)
      (Nat.le_div_iff_mul_le Nat.two_pos |>.mpr (Nat.le_succ_of_le (Nat.mul_comm r 2).le))⟩)) :
    ∃ γ', rootCast r γ' = γ :=
  ⟨rootCastInv r γ, rootCast_rootCastInv r hr h⟩

theorem rootCast_unitaryLongRoot (hr : 2 ≤ r) :
    rootCast r (unitaryLongRoot (2 * r)
        (Nat.le_mul_of_pos_right 2 (Nat.lt_of_lt_of_le Nat.two_pos hr))) =
      unitaryLongRoot (2 * r + 1)
        (Nat.le_trans (Nat.le_mul_of_pos_right 2 (Nat.lt_of_lt_of_le Nat.two_pos hr))
          (Nat.le_add_right (2 * r) 1)) := by
  funext a
  have h2 : (2 * r) % 2 = 0 := by omega
  have h3 : ¬ (2 * r + 1) % 2 = 0 := by omega
  have hb1 : r - 1 < 2 * r / 2 := by rw [two_mul_div_two]; omega
  have hb2 : r - 1 < (2 * r + 1) / 2 := by rw [two_mul_add_one_div_two]; omega
  have e1 : (⟨2 * r / 2 - 1, by omega⟩ : Fin (2 * r / 2)) = ⟨r - 1, hb1⟩ := by
    apply Fin.ext
    show 2 * r / 2 - 1 = r - 1
    rw [two_mul_div_two]
  have e2 : (⟨(2 * r + 1) / 2 - 1, by omega⟩ : Fin ((2 * r + 1) / 2)) =
      ⟨r - 1, hb2⟩ := by
    apply Fin.ext
    show (2 * r + 1) / 2 - 1 = r - 1
    rw [two_mul_add_one_div_two]
  rw [unitaryLongRoot, unitaryLongRoot, if_pos h2, if_neg h3, e1, e2, one_smul]
  have hbval : ((finCastOdd r).symm a).val = a.val := finCastOdd_symm_val r a
  have hlast : finCastOdd r (⟨r - 1, hb1⟩ : Fin (2 * r / 2)) = ⟨r - 1, hb2⟩ := by
    apply Fin.ext
    rw [finCastOdd_val]
  have hiff : ((finCastOdd r).symm a = (⟨r - 1, hb1⟩ : Fin (2 * r / 2))) ↔
      a = (⟨r - 1, hb2⟩ : Fin ((2 * r + 1) / 2)) := by
    rw [Equiv.symm_apply_eq, hlast]
  have hcond : (a = (⟨r - 1, hb2⟩ : Fin ((2 * r + 1) / 2))) ↔ a.val + 1 = r := by
    constructor
    · intro h
      rw [h]
      simp only [Fin.val_mk]
      omega
    · intro h
      apply Fin.ext
      show a.val = r - 1
      omega
  simp only [rootCast, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul, hiff,
    show (a = (⟨r - 1, hb2⟩ : Fin ((2 * r + 1) / 2))) = (a.val + 1 = r) from
      propext hcond]
  by_cases h : a.val + 1 = r <;> simp [h]


section OddEmb

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

@[expose] noncomputable def oddEmb (σ : F ≃+* F) (r : ℕ) :
    SU σ (2 * r) →* SU σ (2 * r + 1) :=
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.suEmbed σ (skipMid_injective r)
    (skipMid_rev r)

theorem oddEmb_injective : Function.Injective (oddEmb σ r) := by
  rw [show oddEmb σ r = suEmbed σ (skipMid_injective r) (skipMid_rev r) from rfl]
  exact suEmbed_injective σ (skipMid_injective r) (skipMid_rev r)

private theorem mat_oddEmb (g : SU σ (2 * r)) :
    mat σ (2 * r + 1) (oddEmb σ r g) =
      CFSG.AGLEmbedding.LeviBlock.extendMat (skipMid_injective r) (mat σ (2 * r) g) := by
  rw [show oddEmb σ r = suEmbed σ (skipMid_injective r) (skipMid_rev r) from rfl]
  exact mat_suEmbed σ (skipMid_injective r) (skipMid_rev r) g

theorem mat_oddEmb_apply_mid (g : SU σ (2 * r)) {i : Fin (2 * r + 1)}
    (hi : i ≠ midIdx (2 * r + 1) (Nat.not_even_two_mul_add_one r)) :
    mat σ (2 * r + 1) (oddEmb σ r g) i
      (midIdx (2 * r + 1) (Nat.not_even_two_mul_add_one r)) = 0 := by
  rw [mat_oddEmb]
  have hmid : midIdx (2 * r + 1) (Nat.not_even_two_mul_add_one r) ∉ Set.range (skipMid r) := by
    rintro ⟨j, hj⟩
    exact skipMid_ne_midIdx r j hj
  rw [CFSG.AGLEmbedding.LeviBlock.extendMat_apply_of_not_mem (skipMid_injective r)
    (mat σ (2 * r) g) (Or.inr hmid)]
  exact Matrix.one_apply_ne hi

private theorem rootHom_congr {n : ℕ} {i j i' j' : Fin n} {hij : i ≠ j} {hi : i ≠ Fin.rev i}
    {hj : j ≠ Fin.rev j} {hij' : i' ≠ j'} {hi' : i' ≠ Fin.rev i'} {hj' : j' ≠ Fin.rev j'}
    (h1 : i = i') (h2 : j = j') (c : Multiplicative F) :
    rootHom σ hσ hij hi hj c = rootHom σ hσ hij' hi' hj' c := by
  subst h1
  subst h2
  apply mat_injective
  rfl

private theorem longRootHom_congr {n : ℕ} {i i' : Fin n} {hi : i ≠ Fin.rev i}
    {hi' : i' ≠ Fin.rev i'} (h : i = i') (c : Multiplicative (traceZero σ)) :
    longRootHom σ hi c = longRootHom σ hi' c := by
  subst h
  apply mat_injective
  rfl

theorem oddEmb_suElt (a b : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) (c : F) :
    oddEmb σ r (suElt σ hσ a b c) = suElt σ hσ (sCast r a) (sCast r b) c := by
  by_cases h : idx a = idx b
  · rw [suElt, dite_eq_right (fun hne => hne h), suElt,
      dite_eq_right (fun hne => hne (by rw [idx_sCast, idx_sCast, h])), map_one]
  · rw [suElt, dite_eq_left h, suElt, dite_eq_left (idx_sCast_ne r h)]
    apply mat_injective
    rw [mat_oddEmb, mat_apply, coe_rootHom, mat_apply, coe_rootHom]
    rw [← sCast_swap r b, ← skipMid_crd r (Sum.swap b), ← skipMid_crd r a]
    rw [extendMat_rootMatrix (skipMid_injective r) (skipMid_rev r)]

theorem oddEmb_suLong (a : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) (c : F) :
    oddEmb σ r (suLong σ a c) = suLong σ (sCast r a) c := by
  by_cases h : c + σ c = 0
  · rw [suLong, dite_eq_left h, suLong, dite_eq_left h]
    apply mat_injective
    rw [mat_oddEmb, mat_apply, coe_longRootHom, mat_apply, coe_longRootHom]
    rw [← skipMid_crd r a]
    rw [extendMat_longRootMatrix (skipMid_injective r) (skipMid_rev r)]
  · rw [suLong, dite_eq_right h, suLong, dite_eq_right h, map_one]

private theorem oddEmb_shortWeyl (k : Fin (2 * r / 2)) (hk : k.val + 1 < 2 * r / 2)
    (hk' : (finCastOdd r k).val + 1 < (2 * r + 1) / 2) :
    oddEmb σ r (shortWeyl σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev k k)
      (lowIdx_ne_rev _ _) 1) =
    shortWeyl σ hσ (lowIdx_ne_succ hk') (lowIdx_ne_rev (finCastOdd r k) (finCastOdd r k))
      (lowIdx_ne_rev _ _) 1 := by
  have h1 : skipMid r (lowIdx k) = lowIdx (finCastOdd r k) := skipMid_lowIdx r k
  have h2 : skipMid r (lowIdx ⟨k.val + 1, hk⟩) =
      lowIdx ⟨(finCastOdd r k).val + 1, hk'⟩ := by
    rw [skipMid_lowIdx]
    congr 1
  rw [shortWeyl_def, shortWeyl_def, map_mul, map_mul]
  simp only [show oddEmb σ r = suEmbed σ (skipMid_injective r) (skipMid_rev r) from rfl,
    suEmbed_rootHom]
  congr 1
  · congr 1
    · exact rootHom_congr (hσ := hσ) h1 h2 _
    · exact rootHom_congr (hσ := hσ) h2 h1 _
  · exact rootHom_congr (hσ := hσ) h1 h2 _

private theorem oddEmb_longWeyl (k : Fin (2 * r / 2)) (ζ : traceZero σ) :
    oddEmb σ r (longWeyl σ (lowIdx_ne_rev k k) ζ) =
      longWeyl σ (lowIdx_ne_rev (finCastOdd r k) (finCastOdd r k)) ζ := by
  have h1 : skipMid r (lowIdx k) = lowIdx (finCastOdd r k) := skipMid_lowIdx r k
  have h2 : skipMid r (Fin.rev (lowIdx k)) = Fin.rev (lowIdx (finCastOdd r k)) := by
    rw [skipMid_rev, h1]
  simp only [longWeyl_def, map_mul]
  simp only [show oddEmb σ r = suEmbed σ (skipMid_injective r) (skipMid_rev r) from rfl,
    suEmbed_longRootHom]
  congr 1
  · congr 1
    · exact longRootHom_congr h1 _
    · exact longRootHom_congr h2 _
  · exact longRootHom_congr h1 _

theorem oddEmb_levelWeyl (ζ : traceZero σ) (k : Fin (2 * r / 2)) :
    oddEmb σ r (levelWeyl hσ ζ k) = levelWeyl hσ ζ (finCastOdd r k) := by
  have hv : (finCastOdd r k).val = k.val := finCastOdd_val r k
  unfold levelWeyl
  by_cases hk : k.val + 1 < 2 * r / 2
  · have hk' : (finCastOdd r k).val + 1 < (2 * r + 1) / 2 := by
      have hd1 := two_mul_div_two r
      have hd2 := two_mul_add_one_div_two r
      omega
    rw [dif_pos hk, dif_pos hk']
    exact oddEmb_shortWeyl (r := r) (hσ := hσ) (k := k) hk hk'
  · have hk' : ¬ (finCastOdd r k).val + 1 < (2 * r + 1) / 2 := by
      have hd1 := two_mul_div_two r
      have hd2 := two_mul_add_one_div_two r
      omega
    rw [dif_neg hk, dif_neg hk']
    exact oddEmb_longWeyl (r := r) (k := k) ζ

end OddEmb

section RootGroups

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

private theorem weight_sub_eq_of_skipMid {i j : Fin (2 * r)} {γ : Fin (2 * r / 2) → ℤ}
    (h : weight (2 * r + 1) (skipMid r i) - weight (2 * r + 1) (skipMid r j) =
      toStd (2 * r + 1) (rootCast r γ)) :
    weight (2 * r) i - weight (2 * r) j = toStd (2 * r) γ := by
  funext a
  have h' := congrFun h (finCastOdd r a)
  simp only [Pi.sub_apply, weight_skipMid, Function.comp_apply, toStd_rootCast,
    Equiv.symm_apply_apply] at h'
  exact h'

private theorem weight_eq_of_skipMid {i : Fin (2 * r)} {γ : Fin (2 * r / 2) → ℤ}
    (h : weight (2 * r + 1) (skipMid r i) = toStd (2 * r + 1) (rootCast r γ)) :
    weight (2 * r) i = toStd (2 * r) γ := by
  funext a
  have h' := congrFun h (finCastOdd r a)
  simp only [weight_skipMid, Function.comp_apply, toStd_rootCast, Equiv.symm_apply_apply] at h'
  exact h'

private theorem two_smul_weight_eq_of_skipMid {i : Fin (2 * r)} {γ : Fin (2 * r / 2) → ℤ}
    (h : 2 • weight (2 * r + 1) (skipMid r i) = toStd (2 * r + 1) (rootCast r γ)) :
    2 • weight (2 * r) i = toStd (2 * r) γ := by
  funext a
  have h' := congrFun h (finCastOdd r a)
  simp only [Pi.smul_apply, weight_skipMid, Function.comp_apply, toStd_rootCast,
    Equiv.symm_apply_apply] at h'
  exact h'

private theorem weight_sub_eq_skipMid {i j : Fin (2 * r)} {γ : Fin (2 * r / 2) → ℤ}
    (h : weight (2 * r) i - weight (2 * r) j = toStd (2 * r) γ) :
    weight (2 * r + 1) (skipMid r i) - weight (2 * r + 1) (skipMid r j) =
      toStd (2 * r + 1) (rootCast r γ) := by
  funext a
  rw [weight_skipMid, weight_skipMid, Pi.sub_apply, Function.comp_apply, Function.comp_apply,
    toStd_rootCast, Function.comp_apply]
  exact congrFun h ((finCastOdd r).symm a)

private theorem weight_eq_skipMid {i : Fin (2 * r)} {γ : Fin (2 * r / 2) → ℤ}
    (h : weight (2 * r) i = toStd (2 * r) γ) :
    weight (2 * r + 1) (skipMid r i) = toStd (2 * r + 1) (rootCast r γ) := by
  funext a
  rw [weight_skipMid, toStd_rootCast, Function.comp_apply]
  exact congrFun h ((finCastOdd r).symm a)

private theorem two_smul_weight_eq_skipMid {i : Fin (2 * r)} {γ : Fin (2 * r / 2) → ℤ}
    (h : 2 • weight (2 * r) i = toStd (2 * r) γ) :
    2 • weight (2 * r + 1) (skipMid r i) = toStd (2 * r + 1) (rootCast r γ) := by
  funext a
  rw [Pi.smul_apply, weight_skipMid, toStd_rootCast, Function.comp_apply]
  exact congrFun h ((finCastOdd r).symm a)

private theorem oddEmb_rootHom {i j : Fin (2 * r)} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (c : Multiplicative F) :
    oddEmb σ r (rootHom σ hσ hij hi hj c) =
      rootHom σ hσ ((skipMid_injective r).ne hij)
        (ne_rev_of_embed (skipMid_injective r) (skipMid_rev r) hi)
        (ne_rev_of_embed (skipMid_injective r) (skipMid_rev r) hj) c := by
  apply mat_injective
  rw [mat_oddEmb, mat_apply, coe_rootHom, mat_apply, coe_rootHom]
  rw [extendMat_rootMatrix (skipMid_injective r) (skipMid_rev r)]

private theorem oddEmb_longRootHom {i : Fin (2 * r)} (hi : i ≠ Fin.rev i)
    (c : Multiplicative (traceZero σ)) :
    oddEmb σ r (longRootHom σ hi c) =
      longRootHom σ (ne_rev_of_embed (skipMid_injective r) (skipMid_rev r) hi) c := by
  apply mat_injective
  rw [mat_oddEmb, mat_apply, coe_longRootHom, mat_apply, coe_longRootHom]
  rw [extendMat_longRootMatrix (skipMid_injective r) (skipMid_rev r)]

private theorem coordSum_wt_inl {k : ℕ} (i : Fin k) : ∑ c, wt (Sum.inl i) c = 1 := by
  simp [wt, Pi.single_apply]

private theorem coordSum_wt_inr {k : ℕ} (i : Fin k) : ∑ c, wt (Sum.inr i) c = -1 := by
  simp [wt, Pi.single_apply]

private theorem sum_toStd_odd (m : ℕ) (v : Fin ((2 * m + 1) / 2) → ℤ) :
    ∑ a : Fin ((2 * m + 1) / 2), toStd (2 * m + 1) v a =
      if h : 0 < (2 * m + 1) / 2 then v ⟨(2 * m + 1) / 2 - 1, by omega⟩ else 0 := by
  let N := (2 * m + 1) / 2
  let f : ℕ → ℤ := fun i => if h : i < N then toStd (2 * m + 1) v ⟨i, h⟩ else 0
  let u : ℕ → ℤ := fun i => if h : i < N then v ⟨i, h⟩ else 0
  let g : ℕ → ℤ := fun i => if i = 0 then 0 else u (i - 1)
  have hf : ∀ a : Fin N, f ↑a = toStd (2 * m + 1) v a := by
    intro a
    simp [f, a.isLt]
  have hterm : ∀ i ∈ Finset.range N, f i = g (i + 1) - g i := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hi0 : i = 0
    · subst hi0
      simp only [f, u, g, hi, if_true, Nat.succ_ne_zero, ↓reduceIte, Fin.val_mk]
      rw [toStd, if_neg (Nat.not_even_two_mul_add_one m)]
      simp
    · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
      have hlt : i - 1 < N := by omega
      simp only [f, u, g, hi, hi0, hlt, if_true, if_false, Nat.succ_ne_zero, ↓reduceIte,
        Fin.val_mk, Nat.add_sub_cancel]
      rw [toStd, if_neg (Nat.not_even_two_mul_add_one m)]
      rw [dif_pos (by simpa using hpos)]
      simp
      rw [dif_pos hpos]
  have hsum : ∑ a : Fin N, toStd (2 * m + 1) v a =
      ∑ i ∈ Finset.range N, (g (i + 1) - g i) := by
    rw [show (∑ a : Fin N, toStd (2 * m + 1) v a) = ∑ a : Fin N, f ↑a from
      Finset.sum_congr rfl (fun a _ => (hf a).symm)]
    rw [Fin.sum_univ_eq_sum_range f N]
    exact Finset.sum_congr rfl hterm
  rw [hsum, Finset.sum_range_sub]
  by_cases hN0 : N = 0
  · rw [dif_neg (by omega), hN0]
    simp
  · rw [dif_pos (by omega)]
    have hlt : N - 1 < N := by omega
    simp [f, g, u, hN0, hlt, N]

private theorem coordSum_toStd_even (r : ℕ) (v : Fin (2 * r / 2) → ℤ) :
    ∑ a, toStd (2 * r) v a = if h : 0 < r then 2 * v ⟨r - 1, by omega⟩ else 0 := by
  have h : ∑ a : Fin (2 * r / 2), toStd (2 * r) v a =
      ∑ b : Fin ((2 * r + 1) / 2), toStd (2 * r + 1) (rootCast r v) b := by
    rw [← Equiv.sum_comp (finCastOdd r)
      (fun b : Fin ((2 * r + 1) / 2) => toStd (2 * r + 1) (rootCast r v) b)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [toStd_rootCast, Function.comp_apply, Equiv.symm_apply_apply]
  rw [h, sum_toStd_odd r]
  by_cases hr : 0 < r
  · rw [dif_pos (by omega), dif_pos hr]
    have hlast : (⟨(2 * r + 1) / 2 - 1, by omega⟩ : Fin ((2 * r + 1) / 2)).val + 1 = r := by
      have hd := two_mul_add_one_div_two r
      simp only [Fin.val_mk]
      omega
    rw [rootCast, if_pos hlast]
    apply congrArg (fun z => 2 * z)
    apply congrArg v
    apply Fin.ext
    rw [finCastOdd_symm_val]
    have hd := two_mul_add_one_div_two r
    simp only [Fin.val_mk]
    omega
  · rw [dif_neg (by omega), dif_neg hr]

private theorem map_rootGroup_oddEmb_le (γ : Fin (2 * r / 2) → ℤ) :
    (CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r) γ).map (oddEmb σ r) ≤
      CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r + 1) (rootCast r γ) := by
  rw [Subgroup.map_le_iff_le_comap]
  unfold CFSG.LieType.Universal.Unitary.rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
    rintro x ⟨c, rfl⟩
    rw [Subgroup.mem_comap, oddEmb_rootHom]
    exact rootHom_mem hσ ((skipMid_injective r).ne hij)
      (ne_rev_of_embed (skipMid_injective r) (skipMid_rev r) hi)
      (ne_rev_of_embed (skipMid_injective r) (skipMid_rev r) hj)
      (by rw [← skipMid_rev]; exact (skipMid_injective r).ne hji)
      (weight_sub_eq_skipMid r hw) c
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    rintro x ⟨c, rfl⟩
    rw [Subgroup.mem_comap, oddEmb_longRootHom]
    exact longRootHom_mem hσ _
      (two_smul_weight_eq_skipMid r hw) c
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    intro x hx
    rw [Subgroup.mem_comap]
    refine heisenberg_le hσ (ne_rev_of_embed (skipMid_injective r) (skipMid_rev r) hi)
      ((skipMid_injective r).ne hik) (by rw [← skipMid_rev, hk])
      (weight_eq_skipMid r hw) ?_
    exact suEmbed_mem_heisenbergSubgroup hσ (skipMid_injective r) (skipMid_rev r) hi hik hk hx

private theorem oddEmb_rootHom' {i j : Fin (2 * r)} (hij : skipMid r i ≠ skipMid r j)
    (hi : skipMid r i ≠ Fin.rev (skipMid r i))
    (hj : skipMid r j ≠ Fin.rev (skipMid r j)) (c : Multiplicative F) :
    oddEmb σ r (rootHom σ hσ (fun h : i = j => hij (by rw [h]))
      (fun h : i = Fin.rev i => hi (by conv_lhs => rw [h]; rw [skipMid_rev]))
      (fun h : j = Fin.rev j => hj (by conv_lhs => rw [h]; rw [skipMid_rev])) c) =
      rootHom σ hσ hij hi hj c := by
  apply mat_injective
  rw [mat_oddEmb, mat_apply, coe_rootHom, mat_apply, coe_rootHom]
  rw [extendMat_rootMatrix (skipMid_injective r) (skipMid_rev r)]

private theorem oddEmb_longRootHom' {i : Fin (2 * r)}
    (hi : skipMid r i ≠ Fin.rev (skipMid r i)) (c : Multiplicative (traceZero σ)) :
    oddEmb σ r (longRootHom σ
      (fun h : i = Fin.rev i => hi (by conv_lhs => rw [h]; rw [skipMid_rev])) c) =
      longRootHom σ hi c := by
  apply mat_injective
  rw [mat_oddEmb, mat_apply, coe_longRootHom, mat_apply, coe_longRootHom]
  rw [extendMat_longRootMatrix (skipMid_injective r) (skipMid_rev r)]

private theorem coordSum_weight_odd {i : Fin (2 * r + 1)} (hi : i ≠ Fin.rev i) :
    ∑ c, weight (2 * r + 1) i c = 1 ∨ ∑ c, weight (2 * r + 1) i c = -1 := by
  obtain ⟨a, rfl | rfl⟩ := exists_lowIdx hi
  · exact Or.inl (by rw [show lowIdx a = crd (Sum.inl a) from rfl, weight_crd,
      coordSum_wt_inl a])
  · exact Or.inr (by rw [show Fin.rev (lowIdx a) = crd (Sum.inr a) from rfl, weight_crd,
      coordSum_wt_inr a])

private theorem even_coordSum_toStd (r : ℕ) (v : Fin (2 * r / 2) → ℤ) :
    Even (∑ a, toStd (2 * r) v a) := by
  rcases r with _ | m
  · simp
  · rw [coordSum_toStd_even (m + 1) v]
    rw [dif_pos (by omega : 0 < m + 1)]
    exact even_two_mul _

private theorem heisenberg_component_empty {γ : Fin (2 * r / 2) → ℤ} {i : Fin (2 * r + 1)}
    (hi : i ≠ Fin.rev i)
    (hw : weight (2 * r + 1) i = toStd (2 * r + 1) (rootCast r γ)) : False := by
  obtain ⟨i', rfl⟩ := exists_skipMid_eq r hi
  have hi' : i' ≠ Fin.rev i' := fun h => hi (by conv_lhs => rw [h]; rw [skipMid_rev])
  have hw' : weight (2 * r) i' = toStd (2 * r) γ := weight_eq_of_skipMid r hw
  have hweight : ∑ c : Fin ((2 * r + 1) / 2), weight (2 * r + 1) (skipMid r i') c =
      ∑ a : Fin (2 * r / 2), weight (2 * r) i' a := by
    rw [← Equiv.sum_comp (finCastOdd r)
      (fun c : Fin ((2 * r + 1) / 2) => weight (2 * r + 1) (skipMid r i') c)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [weight_skipMid, Function.comp_apply, Equiv.symm_apply_apply]
  have hsum : ∑ c : Fin ((2 * r + 1) / 2), weight (2 * r + 1) (skipMid r i') c =
      ∑ a : Fin (2 * r / 2), toStd (2 * r) γ a := by
    rw [hweight, hw']
  rcases coordSum_weight_odd (r := r) hi with h | h
  · rw [h] at hsum
    have he := even_coordSum_toStd r γ
    rw [← hsum] at he
    norm_num at he
  · rw [h] at hsum
    have he := even_coordSum_toStd r γ
    rw [← hsum] at he
    norm_num at he

private theorem map_rootGroup_oddEmb_ge (γ : Fin (2 * r / 2) → ℤ) :
    CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r + 1) (rootCast r γ) ≤
      (CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r) γ).map (oddEmb σ r) := by
  unfold CFSG.LieType.Universal.Unitary.rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
    obtain ⟨i', rfl⟩ := exists_skipMid_eq r hi
    obtain ⟨j', rfl⟩ := exists_skipMid_eq r hj
    rintro x ⟨c, rfl⟩
    rw [← oddEmb_rootHom' (r := r) hσ hij hi hj c]
    refine Subgroup.mem_map_of_mem _ (rootHom_mem hσ (fun h : i' = j' => hij (by rw [h]))
      (fun h : i' = Fin.rev i' => hi (by conv_lhs => rw [h]; rw [skipMid_rev]))
      (fun h : j' = Fin.rev j' => hj (by conv_lhs => rw [h]; rw [skipMid_rev]))
      (fun h : j' = Fin.rev i' => hji (by conv_lhs => rw [h]; rw [skipMid_rev]))
      (weight_sub_eq_of_skipMid r hw) c)
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    obtain ⟨i', rfl⟩ := exists_skipMid_eq r hi
    rintro x ⟨c, rfl⟩
    rw [← oddEmb_longRootHom' (r := r) hi c]
    exact Subgroup.mem_map_of_mem _ (longRootHom_mem hσ _
      (two_smul_weight_eq_of_skipMid r hw) c)
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    exfalso
    exact heisenberg_component_empty r hi hw

theorem map_rootGroup_oddEmb (γ : Fin (2 * r / 2) → ℤ) :
    (CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r) γ).map (oddEmb σ r) =
      CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r + 1) (rootCast r γ) :=
  le_antisymm (map_rootGroup_oddEmb_le r hσ γ) (map_rootGroup_oddEmb_ge r hσ γ)

theorem rootGroup_le_range_oddEmb (hr : 1 ≤ r) {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (h : Even (γ ⟨r - 1, Nat.lt_of_lt_of_le (Nat.sub_one_lt_of_lt hr)
      (Nat.le_div_iff_mul_le Nat.two_pos |>.mpr (Nat.le_succ_of_le (Nat.mul_comm r 2).le))⟩)) :
    CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r + 1) γ ≤
      (oddEmb σ r).range := by
  obtain ⟨γ', rfl⟩ := exists_rootCast_eq r hr h
  rw [← map_rootGroup_oddEmb (r := r) hσ γ']
  exact Subgroup.map_le_range _ _

end RootGroups

section SU3

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem lastIdxOdd_injective' {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) :
    Function.Injective (lastIdxOdd k hn) := by
  have hk : k.val < n / 2 := k.isLt
  have hnodd : n = 2 * (n / 2) + 1 := by
    rw [Nat.not_even_iff_odd] at hn
    obtain ⟨r, hr⟩ := hn
    omega
  have hpm : lowIdx k ≠ midIdx n hn := by
    intro h
    have h' := congrArg Fin.val h
    simp only [val_lowIdx, midIdx] at h'
    omega
  have hp'm : Fin.rev (lowIdx k) ≠ midIdx n hn := by
    intro h
    have h' : n - (k.val + 1) = n / 2 := by
      have := congrArg Fin.val h
      simpa only [Fin.val_rev, val_lowIdx, midIdx] using this
    omega
  have hpp : lowIdx k ≠ Fin.rev (lowIdx k) := lowIdx_ne_rev k k
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd h hpm
  · exact absurd h hpp
  · exact absurd h.symm hpm
  · rfl
  · exact absurd h.symm hp'm
  · exact absurd h.symm hpp
  · exact absurd h hp'm
  · rfl

@[expose] noncomputable def su3Emb (σ : F ≃+* F) {n : ℕ} (hn : ¬ Even n)
    (k : Fin (n / 2)) : SU σ 3 →* SU σ n :=
  suEmbed σ (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn)

private theorem mat_su3Emb {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) (A : SU σ 3) :
    mat σ n (su3Emb σ hn k A) =
      CFSG.AGLEmbedding.LeviBlock.extendMat (lastIdxOdd_injective' hn k)
        (mat σ 3 A) := by
  rw [show su3Emb σ hn k = suEmbed σ (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn) from rfl]
  exact mat_suEmbed σ (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn) A

variable (hσ : ∀ c, σ (σ c) = c)

theorem su3Emb_suLong_inl {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) (c : F) :
    su3Emb σ hn k (suLong σ (Sum.inl (0 : Fin (3 / 2))) c) =
      suLong σ (Sum.inl k) c := by
  by_cases h : c + σ c = 0
  · rw [suLong, dite_eq_left h, suLong, dite_eq_left h]
    apply mat_injective
    rw [mat_su3Emb, mat_apply, coe_longRootHom, mat_apply, coe_longRootHom]
    rw [extendMat_longRootMatrix (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn)]
    rfl
  · rw [suLong, dite_eq_right h, suLong, dite_eq_right h, map_one]

theorem su3Emb_suLong_inr {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) (c : F) :
    su3Emb σ hn k (suLong σ (Sum.inr (0 : Fin (3 / 2))) c) =
      suLong σ (Sum.inr k) c := by
  by_cases h : c + σ c = 0
  · rw [suLong, dite_eq_left h, suLong, dite_eq_left h]
    apply mat_injective
    rw [mat_su3Emb, mat_apply, coe_longRootHom, mat_apply, coe_longRootHom]
    rw [extendMat_longRootMatrix (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn)]
    rfl
  · rw [suLong, dite_eq_right h, suLong, dite_eq_right h, map_one]

theorem su3Emb_levelWeyl {n : ℕ} (hn : ¬ Even n) {k : Fin (n / 2)}
    (hk : ¬ k.val + 1 < n / 2) (ζ : traceZero σ) :
    su3Emb σ hn k (levelWeyl hσ ζ (0 : Fin (3 / 2))) = levelWeyl hσ ζ k := by
  have h0 : ¬ (0 : Fin (3 / 2)).val + 1 < 3 / 2 := by decide
  unfold levelWeyl
  rw [dif_neg h0, dif_neg hk]
  simp only [longWeyl_def, map_mul]
  simp only [show su3Emb σ hn k = suEmbed σ (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn)
    from rfl, suEmbed_longRootHom]
  rfl

theorem eq_extendMat_of_isBlkOn {F : Type*} [Field F] {r n : ℕ} {e : Fin r → Fin n}
    (he : Function.Injective e) {B : Matrix (Fin r) (Fin r) F} {M : Matrix (Fin n) (Fin n) F}
    (hM : IsBlkOn e M) (hB : M.submatrix e e = B) :
    M = CFSG.AGLEmbedding.LeviBlock.extendMat he B := by
  ext a b
  by_cases ha : a ∈ Set.range e <;> by_cases hb : b ∈ Set.range e
  · obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    rw [CFSG.AGLEmbedding.LeviBlock.extendMat_apply_map, ← hB, Matrix.submatrix_apply]
  · rw [CFSG.AGLEmbedding.LeviBlock.extendMat_apply_of_not_mem he B (Or.inr hb),
      hM a b (Or.inr hb)]
  · rw [CFSG.AGLEmbedding.LeviBlock.extendMat_apply_of_not_mem he B (Or.inl ha),
      hM a b (Or.inl ha)]
  · rw [CFSG.AGLEmbedding.LeviBlock.extendMat_apply_of_not_mem he B (Or.inl ha),
      hM a b (Or.inl ha)]

theorem su3Emb_eq_rankOneLastOddEquiv_symm {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} (hn : ¬ Even n)
    {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) (A : SU (unitaryInvolution F p f) 3) :
    su3Emb (unitaryInvolution F p f) hn k A =
      ((rankOneLastOddEquiv hF hn hk).symm A : SU (unitaryInvolution F p f) n) := by
  apply mat_injective
  rw [mat_su3Emb]
  have hg : ((rankOneLastOddEquiv hF hn hk).symm A : SU (unitaryInvolution F p f) n) ∈
      CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F p f)
          (unitaryInvolution_involutive hF) n) k :=
    ((rankOneLastOddEquiv hF hn hk).symm A).2
  have hblk := isBlkOn_lastIdxOdd hn hk hg
  have hblock : (mat (unitaryInvolution F p f) n
      ((rankOneLastOddEquiv hF hn hk).symm A)).submatrix (lastIdxOdd k hn) (lastIdxOdd k hn) =
      mat (unitaryInvolution F p f) 3 A := by
    rw [show lastIdxOdd k hn = ![lowIdx k, midIdx n hn, Fin.rev (lowIdx k)] from rfl]
    rw [← toBlock3_eq_submatrix (lowIdx k) (midIdx n hn) (Fin.rev (lowIdx k))]
    exact toBlock3_mat_rankOneLastOddEquiv_symm A
  have h := eq_extendMat_of_isBlkOn (lastIdxOdd_injective' hn k) hblk hblock
  rw [h]

theorem range_su3Emb_last {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} (hn : ¬ Even n)
    {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) :
    (su3Emb (unitaryInvolution F p f) hn k).range =
      CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F p f)
          (unitaryInvolution_involutive hF) n) k := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨A, rfl⟩
    rw [su3Emb_eq_rankOneLastOddEquiv_symm hF hn hk A]
    exact ((rankOneLastOddEquiv hF hn hk).symm A).2
  · intro x hx
    refine ⟨(rankOneLastOddEquiv hF hn hk) ⟨x, hx⟩, ?_⟩
    rw [su3Emb_eq_rankOneLastOddEquiv_symm hF hn hk]
    simp

end SU3

end CFSG.Timmesfeld.Transvection.Pres
