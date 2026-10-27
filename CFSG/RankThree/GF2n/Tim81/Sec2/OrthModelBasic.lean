module

public import CFSG.Quasithin.Background.SmithB45L2Row
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Rank

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7

variable {F : Type} [Field F] [CharP F 2]

theorem one_le_of_card [Fintype F] {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l)) : 1 ≤ l := by
  by_contra h
  have h0 : l = 0 := by omega
  subst h0
  simp only [mul_zero, pow_zero] at hF
  have := Fintype.one_lt_card (α := F)
  omega

@[expose] def frobFixField (l : ℕ) (F : Type) [Field F] [CharP F 2] : Subfield F where
  carrier := {x | x ^ 2 ^ l = x}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [add_pow_char_pow, hx, hy]
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [mul_pow, hx, hy]
  neg_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [neg_pow, hx]
    rcases Nat.even_or_odd (2 ^ l) with h | h
    · rw [h.neg_one_pow, one_mul, CharTwo.neg_eq]
    · rw [h.neg_one_pow]
      ring
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [inv_pow, hx]

theorem mem_frobFixField {l : ℕ} {x : F} :
    x ∈ frobFixField l F ↔ x ^ 2 ^ l = x := Iff.rfl

theorem card_frobFixField [Fintype F] {l : ℕ}
    (hF : Fintype.card F = 2 ^ (2 * l)) :
    Nat.card (frobFixField l F) = 2 ^ l := by
  have hl : 1 ≤ l := one_le_of_card hF
  have e : ↥(frobFixField l F) ≃ {x : F // x ^ 2 ^ l = x} :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (card_frob_fixed (F := F) hl hF)

theorem exists_mul_sig_eq [Fintype F] {l : ℕ}
    (hF : Fintype.card F = 2 ^ (2 * l))
    {b : F} (hb : b ^ 2 ^ l = b) (hb0 : b ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ c * c ^ 2 ^ l = b := by
  have hl : 1 ≤ l := one_le_of_card hF
  let K : Subfield F := frobFixField l F
  have hbK : b ∈ K := hb
  have hKcard : Nat.card K = 2 ^ l := card_frobFixField hF
  have hFcard : Nat.card F = 2 ^ (2 * l) := by
    rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨u, hu⟩ := FiniteField.unitsMap_norm_surjective (K := K) (K' := F)
    (Units.mk0 (⟨b, hbK⟩ : K) (by intro h; exact hb0 (congrArg Subtype.val h)))
  have hnorm : (Algebra.norm K (u : F) : F) = b := by
    have h := congrArg (fun y : Kˣ => ((y : K) : F)) hu
    simpa using h
  refine ⟨(u : F), u.ne_zero, ?_⟩
  have h1 := FiniteField.algebraMap_norm_eq_pow (K := K) (K' := F) (x := u)
  have halg : algebraMap K F (Algebra.norm K (u : F)) = (Algebra.norm K (u : F) : F) := rfl
  rw [halg, hnorm] at h1
  have hexp : (Nat.card F - 1) / (Nat.card K - 1) = 2 ^ l + 1 := by
    rw [hFcard, hKcard]
    have h1 : 1 ≤ 2 ^ l := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (2 * l) := Nat.one_le_two_pow
    have hfac : 2 ^ (2 * l) - 1 = (2 ^ l - 1) * (2 ^ l + 1) := by
      apply Nat.cast_injective (R := ℤ)
      push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
      ring
    rw [hfac, Nat.mul_div_cancel_left _ (by
      have h2le : 2 ≤ 2 ^ l := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
      omega)]
  rw [hexp, pow_succ] at h1
  rw [mul_comm, ← h1]

theorem exists_add_sig_eq [Fintype F] {l : ℕ}
    (hF : Fintype.card F = 2 ^ (2 * l))
    {a : F} (ha : a ^ 2 ^ l = a) :
    ∃ t : F, t ^ 2 ^ l + t = a := by
  have hl : 1 ≤ l := one_le_of_card hF
  obtain ⟨t₀, ht₀⟩ := CFSG.Quasithin.JonesParshall.exists_sig_ne (F := F) hF (by omega : 0 < l)
  have hL0 : t₀ ^ 2 ^ l + t₀ ≠ 0 := by
    intro h
    apply ht₀
    have h' : t₀ ^ 2 ^ l = -t₀ := (add_eq_zero_iff_eq_neg).mp h
    rw [CharTwo.neg_eq] at h'
    simpa [sig_apply] using h'
  have hfix : (t₀ ^ 2 ^ l + t₀) ^ 2 ^ l = t₀ ^ 2 ^ l + t₀ := by
    rw [add_pow_char_pow]
    have hσ : (t₀ ^ 2 ^ l) ^ 2 ^ l = t₀ := by
      rw [← pow_mul, ← pow_add, ← two_mul, ← hF, FiniteField.pow_card]
    rw [hσ]
    ring
  set c := a / (t₀ ^ 2 ^ l + t₀) with hcdef
  have hc : c ^ 2 ^ l = c := by
    rw [hcdef, div_pow, ha, hfix]
  refine ⟨c * t₀, ?_⟩
  rw [mul_pow, hc]
  have hca : c * (t₀ ^ 2 ^ l + t₀) = a := by
    rw [hcdef]
    field_simp
  linear_combination hca

variable [Fintype F] [Algebra (ZMod 2) F]

@[expose] noncomputable def hermRep (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) :
    Representation (ZMod 2) (SL(2, F)) ↥(hermA l F) where
  toFun g := AddMonoidHom.toZModLinearMap 2 (hermAct l (sig_sig hF) g)
  map_one' := by
    ext x i j
    change ((hermAct l (sig_sig hF) (1 : SL(2, F)) x : ↥(hermA l F)) :
      Matrix (Fin 2) (Fin 2) F) i j = _
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x i j
    change ((hermAct l (sig_sig hF) (g * h) x : ↥(hermA l F)) :
      Matrix (Fin 2) (Fin 2) F) i j =
      ((hermAct l (sig_sig hF) g (hermAct l (sig_sig hF) h x) : ↥(hermA l F)) :
        Matrix (Fin 2) (Fin 2) F) i j
    rw [map_mul]
    rfl

theorem hermRep_apply (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) (g : SL(2, F))
    (X : ↥(hermA l F)) :
    hermRep l hF g X = hermAct l (sig_sig hF) g X := rfl

abbrev upperSylow : Subgroup (SL(2, F)) :=
  (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.upperUnipotent (F := F)).range

theorem rootSub_top_eq_stabilizer :
    rootSub (⊤ : AddSubgroup F) =
      MulAction.stabilizer (SL(2, F)) (Pi.single 0 1 : Fin 2 → F) := by
  ext g
  rw [mem_rootSub, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨t, -, rfl⟩
    change Matrix.mulVec ((uMat t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
      (Pi.single 0 1 : Fin 2 → F) = Pi.single 0 1
    rw [uMat_coe, Matrix.mulVec_single_one]
    ext i
    fin_cases i <;> simp
  · intro hg
    change Matrix.mulVec ((g : Matrix (Fin 2) (Fin 2) F)) (Pi.single 0 1 : Fin 2 → F) =
      Pi.single 0 1 at hg
    rw [Matrix.mulVec_single_one] at hg
    have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by simpa using congrFun hg 0
    have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simpa using congrFun hg 1
    have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      have hd := g.2
      simp only [Matrix.det_fin_two, h00, h10, one_mul, mul_zero, sub_zero] at hd
      exact hd
    refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 1, AddSubgroup.mem_top _, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uMat_coe, h00, h10, h11]

theorem upperSylow_eq_rootSub_top :
    upperSylow = rootSub (⊤ : AddSubgroup F) := by
  rw [rootSub_top_eq_stabilizer]
  exact Subgroup.ext fun g =>
    (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.sl2_fixes_first_iff g).symm.trans
      MulAction.mem_stabilizer_iff

theorem mem_upperSylow_iff {g : SL(2, F)} : g ∈ upperSylow ↔ ∃ t : F, g = uMat t := by
  rw [upperSylow_eq_rootSub_top, mem_rootSub]
  exact exists_congr fun t => and_iff_right (AddSubgroup.mem_top t)

@[expose] def wMat : SL(2, F) :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

theorem frobPow_wMat (l : ℕ) :
    CFSG.Quasithin.frobPow l ((wMat : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.Quasithin.frobPow, wMat]

theorem hermAct_wMat (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) (X : ↥(hermA l F)) :
    ((hermAct l (sig_sig hF) wMat X : ↥(hermA l F)) : Matrix (Fin 2) (Fin 2) F) =
      !![(X : Matrix (Fin 2) (Fin 2) F) 1 1, (X : Matrix (Fin 2) (Fin 2) F) 1 0;
        (X : Matrix (Fin 2) (Fin 2) F) 0 1, (X : Matrix (Fin 2) (Fin 2) F) 0 0] := by
  rw [hermAct_coe, frobPow_wMat, wMat]
  ext i j
  rw [triple_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem hermAct_uMat_sub (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) (t : F)
    (X : ↥(hermA l F)) :
    ((hermAct l (sig_sig hF) (uMat t) X - X : ↥(hermA l F)) : Matrix (Fin 2) (Fin 2) F) =
      !![t ^ 2 ^ l * (X : Matrix (Fin 2) (Fin 2) F) 0 1 +
            t * (X : Matrix (Fin 2) (Fin 2) F) 1 0 +
              t * t ^ 2 ^ l * (X : Matrix (Fin 2) (Fin 2) F) 1 1,
          t * (X : Matrix (Fin 2) (Fin 2) F) 1 1;
        t ^ 2 ^ l * (X : Matrix (Fin 2) (Fin 2) F) 1 1, 0] := by
  ext i j
  change ((hermAct l (sig_sig hF) (uMat t) X : ↥(hermA l F)) : Matrix (Fin 2) (Fin 2) F) i j -
      (X : Matrix (Fin 2) (Fin 2) F) i j = _
  fin_cases i <;> fin_cases j
  · simp [hermAct_uMat_00, sig_apply]; ring
  · simp [hermAct_uMat_01]
  · simp [hermAct_uMat_00, hermAct_uMat_01, hermAct_uMat_11, sig_apply, hermA_10,
      add_pow_char_pow, mul_pow]
    left
    simpa [sig_apply] using hermA_11 (a := l) X
  · simp [hermAct_uMat_11]

theorem eq_zero_of_hermAct_uMat_fixed (l : ℕ)
    (hF : Fintype.card F = 2 ^ (2 * l))
    (X : ↥(hermA l F)) (hfix : ∀ t : F, hermAct l (sig_sig hF) (uMat t) X = X) :
    (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 ∧
      (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
  have hl : 1 ≤ l := one_le_of_card hF
  have h11 : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    have h := congrArg (fun Y : ↥(hermA l F) => (Y : Matrix (Fin 2) (Fin 2) F) 0 1) (hfix 1)
    rw [hermAct_uMat_01] at h
    linear_combination h
  have hmul : ∀ t : F, t ^ 2 ^ l * (X : Matrix (Fin 2) (Fin 2) F) 0 1 +
      t * (X : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    intro t
    have h := congrArg (fun Y : ↥(hermA l F) => (Y : Matrix (Fin 2) (Fin 2) F) 0 0) (hfix t)
    rw [hermAct_uMat_00, h11, sig_apply] at h
    have h' : (X : Matrix (Fin 2) (Fin 2) F) 0 0 +
        (t ^ 2 ^ l * (X : Matrix (Fin 2) (Fin 2) F) 0 1 +
          t * (X : Matrix (Fin 2) (Fin 2) F) 1 0) =
        (X : Matrix (Fin 2) (Fin 2) F) 0 0 + 0 := by
      simpa [add_assoc] using h
    exact add_left_cancel h'
  have h10 : (X : Matrix (Fin 2) (Fin 2) F) 1 0 =
      ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l := hermA_10 (a := l) X
  have hA : (X : Matrix (Fin 2) (Fin 2) F) 0 1 +
      ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l = 0 := by
    have h := hmul 1
    rw [one_pow, one_mul, h10] at h
    simpa using h
  obtain ⟨t₀, ht₀⟩ := CFSG.Quasithin.JonesParshall.exists_sig_ne (F := F) hF (by omega : 0 < l)
  have hB : t₀ ^ 2 ^ l * (X : Matrix (Fin 2) (Fin 2) F) 0 1 +
      t₀ * ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l = 0 := by
    have h := hmul t₀
    rwa [h10] at h
  refine ⟨h11, ?_⟩
  by_contra hne
  have hkey : (t₀ ^ 2 ^ l - t₀) * (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    linear_combination hB - t₀ * hA
  have hzero : t₀ ^ 2 ^ l - t₀ = 0 := (mul_eq_zero.mp hkey).resolve_right hne
  have hfinal : t₀ ^ 2 ^ l = t₀ := sub_eq_zero.mp hzero
  exact ht₀ (by simpa [sig_apply] using hfinal)

theorem mem_fixedSub_upperSylow (l : ℕ)
    (hF : Fintype.card F = 2 ^ (2 * l))
    {X : ↥(hermA l F)} :
    X ∈ fixedSub (hermRep l hF) upperSylow ↔
      (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 ∧
        (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
  constructor
  · intro hX
    refine eq_zero_of_hermAct_uMat_fixed l hF X fun t => ?_
    have h := (mem_fixedSub.mp hX) (uMat t) (mem_upperSylow_iff.mpr ⟨t, rfl⟩)
    rwa [hermRep_apply] at h
  · rintro ⟨h11, h01⟩
    refine mem_fixedSub.mpr ?_
    rintro g hg
    obtain ⟨t, rfl⟩ := mem_upperSylow_iff.mp hg
    rw [hermRep_apply]
    exact hermAct_uMat_fixed_E11 hF t X h11 h01

theorem fixedSub_upperSylow (l : ℕ)
    (hF : Fintype.card F = 2 ^ (2 * l)) :
    fixedSub (hermRep l hF) upperSylow =
      AddSubgroup.toZModSubmodule (n := 2) (herm1101 l F) := by
  ext X
  rw [mem_fixedSub_upperSylow l hF, AddSubgroup.mem_toZModSubmodule]
  rfl

theorem commSub_le_herm11 (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) :
    commSub (hermRep l hF) upperSylow ≤
      AddSubgroup.toZModSubmodule (n := 2) (herm11 l F) := by
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨Y, rfl⟩
  obtain ⟨t, rfl⟩ := mem_upperSylow_iff.mp hg
  rw [LinearMap.sub_apply, Module.End.one_apply, hermRep_apply]
  change ((hermAct l (sig_sig hF) (uMat t) Y - Y : ↥(hermA l F)) :
    Matrix (Fin 2) (Fin 2) F) 1 1 = 0
  rw [AddSubgroup.coe_sub, Matrix.sub_apply, hermAct_uMat_11, sub_self]

end CFSG.RankThree.GF2n.Tim81.Sec2
