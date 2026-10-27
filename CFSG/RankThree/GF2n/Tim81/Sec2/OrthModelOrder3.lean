module

public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelAbstract
public import CFSG.CGT.Timmesfeld75.L2Sylow

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.CGT.Timmesfeld75
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
  {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l))
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) SL(2, F) W}

theorem mem_fixedSub_zpowers_uMat_iff_K0 (t : F) (ht : t ≠ 0)
    (X : ↥(hermA l F)) :
    X ∈ fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t)) ↔
      (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 ∧
        ∃ c : F, c ^ 2 ^ l = c ∧ (X : Matrix (Fin 2) (Fin 2) F) 0 1 = t * c := by
  rw [mem_fixedSub_zpowers]
  constructor
  · intro hfix
    have h01 : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
      have h := congrArg (fun Y : ↥(hermA l F) => (Y : Matrix (Fin 2) (Fin 2) F) 0 1) hfix
      rw [hermRep_apply, hermAct_uMat_01] at h
      have h' : t * (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp h').resolve_left ht
    have hcond : t ^ 2 ^ l * (X : Matrix (Fin 2) (Fin 2) F) 0 1 +
        t * (X : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have h := congrArg (fun Y : ↥(hermA l F) => (Y : Matrix (Fin 2) (Fin 2) F) 0 0) hfix
      rw [hermRep_apply, hermAct_uMat_00, h01, sig_apply] at h
      have h' : t ^ 2 ^ l * (X : Matrix (Fin 2) (Fin 2) F) 0 1 +
          t * (X : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
        linear_combination h
      exact h'
    refine ⟨h01, ⟨(X : Matrix (Fin 2) (Fin 2) F) 0 1 / t, ?_, ?_⟩⟩
    · have hb : (X : Matrix (Fin 2) (Fin 2) F) 0 1 ^ 2 ^ l =
          (X : Matrix (Fin 2) (Fin 2) F) 1 0 := (hermA_10 (a := l) X).symm
      rw [div_pow, hb]
      rw [div_eq_div_iff (pow_ne_zero _ ht) ht]
      have hsum : t ^ 2 ^ l * (X : Matrix (Fin 2) (Fin 2) F) 0 1 =
          t * (X : Matrix (Fin 2) (Fin 2) F) 1 0 := by
        have h := (add_eq_zero_iff_eq_neg.mp hcond)
        rwa [CharTwo.neg_eq] at h
      rw [mul_comm ((X : Matrix (Fin 2) (Fin 2) F) 1 0) t,
        mul_comm ((X : Matrix (Fin 2) (Fin 2) F) 0 1) (t ^ 2 ^ l), hsum]
    · field_simp
  · rintro ⟨h11, c, hc, h01⟩
    rw [hermRep_apply]
    refine hermA_ext ?_ ?_ ?_
    · rw [hermAct_uMat_00, h11, sig_apply]
      have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      have h10 : (X : Matrix (Fin 2) (Fin 2) F) 1 0 = (t * c) ^ 2 ^ l := by
        rw [hermA_10, h01, sig_apply]
      have hcond : t ^ 2 ^ l * (X : Matrix (Fin 2) (Fin 2) F) 0 1 +
          t * (X : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
        rw [h01, h10, mul_pow, hc]
        ring_nf
        simp [h2]
      linear_combination hcond
    · rw [hermAct_uMat_01, h11]
      simp
    · rw [hermAct_uMat_11]



private theorem uMat_eq_utriElt (t : F) : uMat t = utriElt t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat_coe, utriElt_apply_00, utriElt_apply_01, utriElt_apply_10,
      utriElt_apply_11]

theorem upperSylow_eq_utri : upperSylow (F := F) = utri F := by
  ext g
  rw [mem_upperSylow_iff, mem_utri_iff]
  exact exists_congr fun t => by rw [uMat_eq_utriElt]

private theorem wMat_eq_wElt : (wMat (F := F) : SL(2, F)) = wElt := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, wElt_apply_00, wElt_apply_01, wElt_apply_10, wElt_apply_11,
      CharTwo.neg_eq]

private theorem wMat_mul_self : (wMat (F := F)) * wMat = 1 := by
  apply Subtype.ext
  change (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; 1, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem conj_wMat_upperSylow :
    upperSylow.map (MulAut.conj (wMat (F := F))).toMonoidHom = ltri F := by
  rw [upperSylow_eq_utri, wMat_eq_wElt]
  exact conjSubgroup_wElt_utri

private theorem mem_fixedSub_ltri_iff (X : ↥(hermA l F)) :
    X ∈ fixedSub (hermRep l hF) (ltri F) ↔
      (X : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧
        (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
  conv_lhs => rw [← conj_wMat_upperSylow (F := F), fixedSub_map_conj]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    rw [fixedSub_upperSylow] at hY
    obtain ⟨h11, h01⟩ := hY
    rw [hermRep_apply, hermAct_wMat (hF := hF)]
    constructor
    · simpa using h11
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [hermA_10, h01, map_zero]
  · rintro ⟨h00, h01⟩
    refine ⟨hermRep l hF wMat X, ?_, ?_⟩
    · change (hermRep l hF wMat X) ∈ fixedSub (hermRep l hF) upperSylow
      rw [mem_fixedSub_upperSylow, hermRep_apply, hermAct_wMat (hF := hF)]
      constructor
      · simpa using h00
      · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
        rw [hermA_10, h01, map_zero]
    · rw [← Module.End.mul_apply, ← map_mul, wMat_mul_self, map_one,
        Module.End.one_apply]

private theorem hermAct_uMat_sub_hermDiag11 (t a : F) (ha : a ^ 2 ^ l = a) :
    ((hermAct l (sig_sig hF) (uMat t) (hermDiag11 l hF a ha) -
        hermDiag11 l hF a ha : ↥(hermA l F)) : Matrix (Fin 2) (Fin 2) F) =
      !![t ^ 2 ^ l * t * a, t * a; t ^ 2 ^ l * a, 0] := by
  rw [hermAct_uMat_sub l hF t (hermDiag11 l hF a ha), hermDiag11_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, hermAct_uMat_00, hermAct_uMat_01,
      hermAct_uMat_11, hermDiag11_coe, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.zero_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] <;>
    ring

private theorem hermDiag11_mem_fixedSub_ltri (a : F) (ha : a ^ 2 ^ l = a) :
    hermDiag11 l hF a ha ∈ fixedSub (hermRep l hF) (ltri F) := by
  rw [mem_fixedSub_ltri_iff, hermDiag11_coe]
  exact ⟨rfl, rfl⟩

private theorem card_fixedSub_zpowers_uMat (t : F) (ht : t ≠ 0) :
    Nat.card ↥(fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t))) = 2 ^ (2 * l) := by
  have e : ↥(fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t))) ≃
      ↥(frobFixField l F) × ↥(frobFixField l F) :=
    { toFun := fun X =>
        (⟨(X : Matrix (Fin 2) (Fin 2) F) 0 0, mem_frobFixField.mpr (by
            rw [← sig_apply]
            exact hermA_00 (a := l) X.1)⟩,
          ⟨(X : Matrix (Fin 2) (Fin 2) F) 0 1 / t, by
            obtain ⟨-, c, hc, h01⟩ :=
              (mem_fixedSub_zpowers_uMat_iff_K0 (hF := hF) t ht X).mp X.2
            have hc' : (X : Matrix (Fin 2) (Fin 2) F) 0 1 / t = c := by
              rw [h01]
              field_simp
            rw [hc']
            exact mem_frobFixField.mpr hc⟩)
      invFun := fun p =>
        ⟨hermMk hF (p.1 : F) (show (p.1 : F) ^ 2 ^ l = (p.1 : F) from p.1.2) (t * p.2) 0
            (by simp), by
          refine (mem_fixedSub_zpowers_uMat_iff_K0 (hF := hF) t ht _).mpr ?_
          refine ⟨by rw [hermMk_coe]; simp, p.2, p.2.2, ?_⟩
          rw [hermMk_coe]; simp⟩
      left_inv := fun X => by
        apply Subtype.ext
        apply hermA_ext
        · rw [hermMk_coe]; simp
        · rw [hermMk_coe]
          simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
          field_simp
        · obtain ⟨h11, -⟩ :=
            (mem_fixedSub_zpowers_uMat_iff_K0 (hF := hF) t ht X).mp X.2
          rw [hermMk_coe]; simp [h11]
      right_inv := fun p => by
        apply Prod.ext
        · apply Subtype.ext
          dsimp only
          rw [hermMk_coe]; simp
        · apply Subtype.ext
          dsimp only
          rw [hermMk_coe]
          simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
          field_simp }
  rw [Nat.card_congr e, Nat.card_prod, card_frobFixField (hF := hF)]
  rw [← pow_add]
  congr 1
  ring



private theorem hermRep_uMat_sub_hermDiag11 (t a : F) (ha : a ^ 2 ^ l = a) :
    (((hermRep l hF (uMat t) - 1) (hermDiag11 l hF a ha) : ↥(hermA l F)) :
        Matrix (Fin 2) (Fin 2) F) =
      !![t ^ 2 ^ l * t * a, t * a; t ^ 2 ^ l * a, 0] := by
  rw [LinearMap.sub_apply, Module.End.one_apply, hermRep_apply]
  exact hermAct_uMat_sub_hermDiag11 (hF := hF) t a ha

private theorem exists_eq_hermDiag_add_sub_of_mem_fixedSub_zpowers_uMat (t : F) (ht : t ≠ 0)
    {X : ↥(hermA l F)}
    (hX : X ∈ fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t))) :
    ∃ (a c : F) (ha : a ^ 2 ^ l = a) (hc : c ^ 2 ^ l = c),
      X = hermDiag l hF a ha +
        (hermRep l hF (uMat t) - 1) (hermDiag11 l hF c hc) := by
  obtain ⟨h11, c, hc, h01⟩ :=
    (mem_fixedSub_zpowers_uMat_iff_K0 (hF := hF) t ht X).mp hX
  let a0 : F := (X : Matrix (Fin 2) (Fin 2) F) 0 0 - c * (t ^ 2 ^ l * t)
  have ha0 : a0 ^ 2 ^ l = a0 := by
    dsimp [a0]
    rw [sub_pow_char_pow, mul_pow, hc]
    have h0 : ((X : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 ^ l =
        (X : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      rw [← sig_apply]
      exact hermA_00 (a := l) X
    have hnorm : (t ^ 2 ^ l * t) ^ 2 ^ l = t ^ 2 ^ l * t := by
      rw [mul_comm (t ^ 2 ^ l) t]
      exact mul_pow_fix hF t
    rw [h0, hnorm]
  refine ⟨a0, c, ha0, hc, ?_⟩
  refine hermA_ext ?_ ?_ ?_
  · rw [AddSubgroup.coe_add, Matrix.add_apply, hermDiag_coe,
      hermRep_uMat_sub_hermDiag11]
    dsimp [a0]
    ring
  · rw [AddSubgroup.coe_add, Matrix.add_apply, hermDiag_coe,
      hermRep_uMat_sub_hermDiag11, h01]
    simp
  · rw [AddSubgroup.coe_add, Matrix.add_apply, hermDiag_coe,
      hermRep_uMat_sub_hermDiag11, h11]
    simp

private theorem sub_mem_fixedSub_zpowers_uMat_and_commSub (t : F) (ht : t ≠ 0)
    {W : ↥(hermA l F)} (hW : W ∈ fixedSub (hermRep l hF) (ltri F)) :
    ((hermRep l hF (uMat t) - 1) W) ∈
        fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t)) ∧
      ((hermRep l hF (uMat t) - 1) W) ∈ commSub (hermRep l hF) upperSylow := by
  have hW' := (mem_fixedSub_ltri_iff (hF := hF) W).mp hW
  have hWdiag : W = hermDiag11 l hF ((W : Matrix (Fin 2) (Fin 2) F) 1 1)
      (hermA_11 (a := l) W) := by
    refine hermA_ext ?_ ?_ ?_
    · change (W : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (!![0, 0; 0, (W : Matrix (Fin 2) (Fin 2) F) 1 1] :
          Matrix (Fin 2) (Fin 2) F) 0 0
      rw [hW'.1]; simp
    · change (W : Matrix (Fin 2) (Fin 2) F) 0 1 =
        (!![0, 0; 0, (W : Matrix (Fin 2) (Fin 2) F) 1 1] :
          Matrix (Fin 2) (Fin 2) F) 0 1
      rw [hW'.2]; simp
    · change (W : Matrix (Fin 2) (Fin 2) F) 1 1 =
        (!![0, 0; 0, (W : Matrix (Fin 2) (Fin 2) F) 1 1] :
          Matrix (Fin 2) (Fin 2) F) 1 1
      simp
  have hact := hermRep_uMat_sub_hermDiag11 (hF := hF) t
    ((W : Matrix (Fin 2) (Fin 2) F) 1 1) (hermA_11 (a := l) W)
  refine ⟨?_, ?_⟩
  · rw [hWdiag]
    refine (mem_fixedSub_zpowers_uMat_iff_K0 (hF := hF) t ht _).mpr ⟨?_, ?_⟩
    · rw [hact]; simp
    · exact ⟨(W : Matrix (Fin 2) (Fin 2) F) 1 1, hermA_11 (a := l) W, by rw [hact]; simp⟩
  · exact range_le_commSub (mem_upperSylow_iff.mpr ⟨t, rfl⟩) ⟨W, rfl⟩

private theorem fixedSub_zpowers_uMat_inf_commSub_upperSylow (t : F) (ht : t ≠ 0) :
    fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t)) ⊓
        commSub (hermRep l hF) upperSylow =
      fixedSub (hermRep l hF) upperSylow ⊔
        (fixedSub (hermRep l hF) (ltri F)).map (hermRep l hF (uMat t) - 1) := by
  refine le_antisymm ?_ ?_
  · rintro X ⟨hXfix, -⟩
    obtain ⟨a, c, ha, hc, rfl⟩ :=
      exists_eq_hermDiag_add_sub_of_mem_fixedSub_zpowers_uMat (hF := hF) t ht hXfix
    refine Submodule.add_mem_sup ?_ ?_
    · rw [fixedSub_upperSylow]
      exact hermDiag_mem_herm1101 (hF := hF) a ha
    · exact ⟨hermDiag11 l hF c hc, hermDiag11_mem_fixedSub_ltri (hF := hF) c hc, rfl⟩
  · intro X hX
    rcases Submodule.mem_sup.1 hX with ⟨Y, hY, Z, hZ, rfl⟩
    have hYfix : Y ∈ fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t)) := by
      rw [fixedSub_upperSylow] at hY
      obtain ⟨hY11, hY01⟩ := hY
      exact (mem_fixedSub_zpowers_uMat_iff_K0 (hF := hF) t ht Y).mpr
        ⟨hY11, 0, by simp, by rw [hY01]; simp⟩
    have hYcomm : Y ∈ commSub (hermRep l hF) upperSylow := by
      rw [commSub_upperSylow]
      rw [fixedSub_upperSylow] at hY
      exact hY.1
    obtain ⟨W, hW, rfl⟩ := hZ
    obtain ⟨hZfix, hZcomm⟩ := sub_mem_fixedSub_zpowers_uMat_and_commSub (hF := hF) t ht hW
    exact ⟨(fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t))).add_mem hYfix hZfix,
      (commSub (hermRep l hF) upperSylow).add_mem hYcomm hZcomm⟩



include hF in
private theorem card_compl_lt_two_pow (t : F)
    (H : AddSubgroup F) (hS0 : {s : F | ¬ ∃ c : F, c ^ 2 ^ l = c ∧ s = t * c} ⊆ H) :
    Nat.card {x : F // x ∉ H} < 2 ^ l := by
  classical
  have hex : ∀ x : {x : F // x ∉ H}, ∃ c : F, c ^ 2 ^ l = c ∧ x.1 = t * c := by
    intro x
    by_contra h
    exact x.2 (hS0 h)
  let f : {x : F // x ∉ H} → {c : F // c ^ 2 ^ l = c} := fun x =>
    ⟨Classical.choose (hex x), (Classical.choose_spec (hex x)).1⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hval : (f x).1 = (f y).1 := congrArg Subtype.val hxy
    calc x.1 = t * (f x).1 := (Classical.choose_spec (hex x)).2
      _ = t * (f y).1 := by rw [hval]
      _ = y.1 := (Classical.choose_spec (hex y)).2.symm
  have hnotsurj : ¬ Function.Surjective f := by
    intro hsurj
    obtain ⟨x, hx0⟩ := hsurj ⟨0, by simp⟩
    have hxval : x.1 = t * (f x).1 := (Classical.choose_spec (hex x)).2
    have hfx : (f x).1 = 0 := by rw [hx0]
    have hxzero : x.1 = 0 := by rw [hxval, hfx, mul_zero]
    exact x.2 (by rw [hxzero]; exact H.zero_mem)
  have hlt : Fintype.card {x : F // x ∉ H} < Fintype.card {c : F // c ^ 2 ^ l = c} :=
    Fintype.card_lt_of_injective_not_surjective f hf_inj hnotsurj
  have hK0card : Fintype.card {c : F // c ^ 2 ^ l = c} = 2 ^ l := by
    change Fintype.card ↥(frobFixField l F) = 2 ^ l
    rw [← Nat.card_eq_fintype_card]
    exact card_frobFixField (hF := hF)
  simpa [Nat.card_eq_fintype_card, hK0card] using hlt

include hF in
private theorem closure_compl_mul_frobFixField_eq_top (t : F) :
    AddSubgroup.closure {s : F | ¬ ∃ c : F, c ^ 2 ^ l = c ∧ s = t * c} = ⊤ := by
  classical
  let S0 : Set F := {s : F | ¬ ∃ c : F, c ^ 2 ^ l = c ∧ s = t * c}
  let H : AddSubgroup F := AddSubgroup.closure S0
  have hS0 : S0 ⊆ H := AddSubgroup.subset_closure
  by_contra htop
  have hproper : H ≠ ⊤ := htop
  have hindex_ne : H.index ≠ 1 := fun h => hproper (AddSubgroup.index_eq_one.mp h)
  have hindex_pos : 0 < H.index := Nat.pos_of_ne_zero AddSubgroup.index_ne_zero_of_finite
  have hindex_ge : 2 ≤ H.index := by omega
  have hcardmul := AddSubgroup.card_mul_index H
  have h2H : 2 * Nat.card H ≤ Nat.card F := by
    rw [← hcardmul]
    calc 2 * Nat.card H = Nat.card H * 2 := by ring
      _ ≤ Nat.card H * H.index := Nat.mul_le_mul_left _ hindex_ge
  have hcardH : Nat.card H ≤ Nat.card F / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    linarith
  have hcomp_eq : Nat.card {x : F // x ∉ H} = Nat.card F - Nat.card H := by
    have h1 : Nat.card {x : F // x ∉ H} = Nat.card (Hᶜ : Set F) := rfl
    rw [h1, Nat.card_coe_set_eq, Set.ncard_compl, ← Nat.card_coe_set_eq]
    rfl
  have hcomp_ge : Nat.card F / 2 ≤ Nat.card {x : F // x ∉ H} := by
    rw [hcomp_eq]
    omega
  have hcomp_lt : Nat.card {x : F // x ∉ H} < 2 ^ l :=
    card_compl_lt_two_pow (hF := hF) t H hS0
  have hpow : 2 ^ l ≤ Nat.card F / 2 := by
    have hF : Nat.card F = 2 ^ (2 * l) := by
      rw [Nat.card_eq_fintype_card, hF]
    rw [hF]
    have hl : 1 ≤ l := by
      by_contra h
      have h0 : l = 0 := by omega
      subst h0
      simp only [mul_zero, pow_zero] at hF
      have hc : 1 < Nat.card F := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      omega
    have hdiv : 2 ^ (2 * l) / 2 = 2 ^ (2 * l - 1) := by
      conv_lhs => rw [show 2 * l = (2 * l - 1) + 1 by omega, pow_succ]
      rw [Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    rw [hdiv]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega



private theorem fixedSub_upperSylow_le_fixedSub_zpowers_uMat (t : F) :
    fixedSub (hermRep l hF) upperSylow ≤
      fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t)) := by
  intro X hX
  rw [mem_fixedSub] at hX ⊢
  intro y hy
  apply hX
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact Subgroup.zpow_mem _ (mem_upperSylow_iff.mpr ⟨t, rfl⟩) n

private theorem fixedSub_zpowers_uMat_inf_fixedSub_zpowers_uMat_eq (t s : F) (ht : t ≠ 0)
    (hst : s ∉ {x : F | ∃ c : F, c ^ 2 ^ l = c ∧ x = t * c}) :
    fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t)) ⊓
        fixedSub (hermRep l hF) (Subgroup.zpowers (uMat s)) =
      fixedSub (hermRep l hF) upperSylow := by
  have hs : s ≠ 0 := by
    intro h0
    apply hst
    exact ⟨0, by simp, by rw [h0, mul_zero]⟩
  refine le_antisymm ?_ ?_
  · rintro X ⟨hXt, hXs⟩
    obtain ⟨h11, c, hc, h01⟩ :=
      (mem_fixedSub_zpowers_uMat_iff_K0 (hF := hF) t ht X).mp hXt
    obtain ⟨-, d, hd, h02⟩ :=
      (mem_fixedSub_zpowers_uMat_iff_K0 (hF := hF) s hs X).mp hXs
    have hb0 : (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      by_contra hbne
      have hc0 : c ≠ 0 := by
        intro hc0
        exact hbne (by rw [h01, hc0, mul_zero])
      have hd0 : d ≠ 0 := by
        intro hd0
        exact hbne (by rw [h02, hd0, mul_zero])
      have hmul : t * c = s * d := by rw [← h01, h02]
      have hcdK : c / d ∈ frobFixField l F :=
        (frobFixField l F).div_mem (mem_frobFixField.mpr hc) (mem_frobFixField.mpr hd)
      refine hst ⟨c / d, mem_frobFixField.mp hcdK, ?_⟩
      apply (mul_right_injective₀ hd0)
      field_simp [hd0]
      simpa [mul_comm] using hmul.symm
    rw [mem_fixedSub_upperSylow]
    exact ⟨h11, hb0⟩
  · intro X hX
    exact ⟨fixedSub_upperSylow_le_fixedSub_zpowers_uMat (hF := hF) t hX,
      fixedSub_upperSylow_le_fixedSub_zpowers_uMat (hF := hF) s hX⟩



include hF in
private theorem closure_uMat_compl_eq_upperSylow (t : F) :
    Subgroup.closure {z : SL(2, F) | ∃ s : F,
      (¬ ∃ c : F, c ^ 2 ^ l = c ∧ s = t * c) ∧ z = uMat s} = upperSylow := by
  let S0 : Set F := {s : F | ¬ ∃ c : F, c ^ 2 ^ l = c ∧ s = t * c}
  let K : Subgroup (SL(2, F)) := Subgroup.closure {z : SL(2, F) | ∃ s ∈ S0, z = uMat s}
  have hgen : AddSubgroup.closure S0 = ⊤ :=
    closure_compl_mul_frobFixField_eq_top (hF := hF) t
  have hKupper : K ≤ upperSylow := by
    change Subgroup.closure {z : SL(2, F) | ∃ s ∈ S0, z = uMat s} ≤ upperSylow
    rw [Subgroup.closure_le]
    rintro z ⟨s, -, rfl⟩
    exact mem_upperSylow_iff.mpr ⟨s, rfl⟩
  have hupperK : upperSylow ≤ K := by
    intro g hg
    obtain ⟨s, rfl⟩ := mem_upperSylow_iff.mp hg
    have hs : s ∈ AddSubgroup.closure S0 := by rw [hgen]; exact AddSubgroup.mem_top s
    clear hg
    induction hs using AddSubgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure ⟨x, hx, rfl⟩
    | zero => simpa [uMat_zero] using K.one_mem
    | add x y hx hy ihx ihy =>
        rw [← uMat_mul]
        exact K.mul_mem ihx ihy
    | neg x hx ih => simpa [CharTwo.neg_eq] using ih
  exact le_antisymm hKupper hupperK

private theorem upperSylow_eq_closure_fixedSub_zpowers (t : F) (ht : t ≠ 0) :
    upperSylow = Subgroup.closure {z : SL(2, F) | z ∈ upperSylow ∧
      fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t)) ⊓
          fixedSub (hermRep l hF) (Subgroup.zpowers z) =
        fixedSub (hermRep l hF) upperSylow} := by
  let S0 : Set F := {s : F | ¬ ∃ c : F, c ^ 2 ^ l = c ∧ s = t * c}
  have hgood_upper : ∀ z ∈ {z : SL(2, F) | z ∈ upperSylow ∧
      fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t)) ⊓
          fixedSub (hermRep l hF) (Subgroup.zpowers z) =
        fixedSub (hermRep l hF) upperSylow}, z ∈ upperSylow := by
    intro z hz
    exact hz.1
  have huMat_good : ∀ s ∈ S0, uMat s ∈ {z : SL(2, F) | z ∈ upperSylow ∧
      fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t)) ⊓
          fixedSub (hermRep l hF) (Subgroup.zpowers z) =
        fixedSub (hermRep l hF) upperSylow} := by
    intro s hs
    refine ⟨mem_upperSylow_iff.mpr ⟨s, rfl⟩, ?_⟩
    exact fixedSub_zpowers_uMat_inf_fixedSub_zpowers_uMat_eq (hF := hF) t s ht hs
  have hKgood : Subgroup.closure {z : SL(2, F) | ∃ s ∈ S0, z = uMat s} ≤
      Subgroup.closure {z : SL(2, F) | z ∈ upperSylow ∧
        fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t)) ⊓
            fixedSub (hermRep l hF) (Subgroup.zpowers z) =
          fixedSub (hermRep l hF) upperSylow} := by
    rw [Subgroup.closure_le]
    rintro z ⟨s, hs, rfl⟩
    exact Subgroup.subset_closure (huMat_good s hs)
  have hKupper : Subgroup.closure {z : SL(2, F) | ∃ s ∈ S0, z = uMat s} = upperSylow := by
    simpa [S0] using closure_uMat_compl_eq_upperSylow (hF := hF) t
  refine le_antisymm ?_ ?_
  · exact hKupper.symm.trans_le hKgood
  · rw [Subgroup.closure_le]
    intro z hz
    exact hgood_upper z hz



include hF in
private theorem exists_conj_map_eq_upperSylow_ltri
    (B B' : Subgroup (SL(2, F))) (hB2 : ∀ a ∈ B, a * a = 1)
    (hB : Nat.card B = 2 ^ (2 * l)) (hB'2 : ∀ a ∈ B', a * a = 1)
    (hB' : Nat.card B' = 2 ^ (2 * l)) (hne : B ≠ B') :
    ∃ c : SL(2, F), B.map (MulAut.conj c).toMonoidHom = upperSylow ∧
      B'.map (MulAut.conj c).toMonoidHom = ltri F := by
  have hBeq : Nat.card B = Nat.card F := by
    rw [hB, Nat.card_eq_fintype_card, hF]
  have hB'eq : Nat.card B' = Nat.card F := by
    rw [hB', Nat.card_eq_fintype_card, hF]
  obtain ⟨a, ha⟩ := eq_conj_rootGroup B hB2 hBeq
  obtain ⟨b, hb⟩ := eq_conj_rootGroup B' hB'2 hB'eq
  have hBconj : B = upperSylow.map (MulAut.conj a).toMonoidHom := by
    ext g
    rw [ha g]
    constructor
    · intro h
      exact ⟨a⁻¹ * g * a, h, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨s, hs, rfl⟩
      change a⁻¹ * (a * s * a⁻¹) * a ∈ upperSylow
      simpa [mul_assoc] using hs
  have hB'conj : B' = upperSylow.map (MulAut.conj b).toMonoidHom := by
    ext g
    rw [hb g]
    constructor
    · intro h
      exact ⟨b⁻¹ * g * b, h, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨s, hs, rfl⟩
      change b⁻¹ * (b * s * b⁻¹) * b ∈ upperSylow
      simpa [mul_assoc] using hs
  have hneconj : CFSG.CGT.Timmesfeld75.conjSubgroup a (utri F) ≠
      CFSG.CGT.Timmesfeld75.conjSubgroup b (utri F) := by
    intro h
    apply hne
    rw [hBconj, hB'conj]
    rw [← upperSylow_eq_utri] at h
    exact h
  obtain ⟨c, hc1, hc2⟩ := CFSG.CGT.Timmesfeld75.exists_conj_pair_normal_form hneconj
  refine ⟨c, ?_, ?_⟩
  · rw [hBconj]
    change CFSG.CGT.Timmesfeld75.conjSubgroup c
      (CFSG.CGT.Timmesfeld75.conjSubgroup a upperSylow) = upperSylow
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup, upperSylow_eq_utri]
    exact hc1
  · rw [hB'conj]
    change CFSG.CGT.Timmesfeld75.conjSubgroup c
      (CFSG.CGT.Timmesfeld75.conjSubgroup b upperSylow) = ltri F
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup, upperSylow_eq_utri]
    exact hc2

private theorem fixedSub_zpowers_inf_commSub_eq_sup_map_model
    (B B' : Subgroup (SL(2, F))) (hB2 : ∀ a ∈ B, a * a = 1)
    (hB : Nat.card B = 2 ^ (2 * l)) (hB'2 : ∀ a ∈ B', a * a = 1)
    (hB' : Nat.card B' = 2 ^ (2 * l)) (hne : B ≠ B') {x : SL(2, F)} (hx : x ∈ B)
    (hx1 : x ≠ 1) :
    fixedSub (hermRep l hF) (Subgroup.zpowers x) ⊓ commSub (hermRep l hF) B =
      fixedSub (hermRep l hF) B ⊔
        (fixedSub (hermRep l hF) B').map (hermRep l hF x - 1) := by
  obtain ⟨c, hBc, hB'c⟩ :=
    exists_conj_map_eq_upperSylow_ltri (hF := hF) B B' hB2 hB hB'2 hB' hne
  let xc : SL(2, F) := c * x * c⁻¹
  have hxcmem : xc ∈ upperSylow := by
    have h := CFSG.CGT.Timmesfeld75.conj_mem_conjSubgroup c hx
    rw [show CFSG.CGT.Timmesfeld75.conjSubgroup c B =
      B.map (MulAut.conj c).toMonoidHom from rfl, hBc] at h
    exact h
  have hxc1 : xc ≠ 1 := by
    intro h
    apply hx1
    have := congrArg (fun y => c⁻¹ * y * c) h
    simpa [xc, mul_assoc] using this
  obtain ⟨t, ht_eq⟩ := mem_upperSylow_iff.mp hxcmem
  have ht : t ≠ 0 := by
    intro h0
    apply hxc1
    rw [ht_eq, h0, uMat_zero]
  have hmodel := fixedSub_zpowers_uMat_inf_commSub_upperSylow (hF := hF) t ht
  have hinj : Function.Injective (hermRep l hF c : ↥(hermA l F) → ↥(hermA l F)) := by
    intro u v h
    have := congrArg (hermRep l hF c⁻¹) h
    simpa using this
  have hzp : (Subgroup.zpowers x).map (MulAut.conj c).toMonoidHom =
      Subgroup.zpowers xc := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hLmap : (fixedSub (hermRep l hF) (Subgroup.zpowers x) ⊓
        commSub (hermRep l hF) B).map (hermRep l hF c) =
      fixedSub (hermRep l hF) (Subgroup.zpowers xc) ⊓
        commSub (hermRep l hF) upperSylow := by
    rw [Submodule.map_inf _ hinj, ← fixedSub_map_conj (ρ := hermRep l hF) c
      (Subgroup.zpowers x), ← commSub_map_conj (ρ := hermRep l hF) c B, hzp, hBc]
  have hRmap : (fixedSub (hermRep l hF) B ⊔
        (fixedSub (hermRep l hF) B').map (hermRep l hF x - 1)).map (hermRep l hF c) =
      fixedSub (hermRep l hF) upperSylow ⊔
        (fixedSub (hermRep l hF) (ltri F)).map (hermRep l hF xc - 1) := by
    rw [Submodule.map_sup, ← fixedSub_map_conj (ρ := hermRep l hF) c B, hBc,
      map_sub_image_conj (ρ := hermRep l hF) c x
        (fixedSub (hermRep l hF) B'),
      ← fixedSub_map_conj (ρ := hermRep l hF) c B', hB'c]
  rw [← ht_eq] at hmodel
  have hmap : (fixedSub (hermRep l hF) (Subgroup.zpowers x) ⊓
        commSub (hermRep l hF) B).map (hermRep l hF c) =
      (fixedSub (hermRep l hF) B ⊔
        (fixedSub (hermRep l hF) B').map (hermRep l hF x - 1)).map (hermRep l hF c) := by
    rw [hLmap, hRmap, hmodel]
  exact Submodule.map_injective_of_injective hinj hmap



private theorem card_fixedSub_zpowers_model (B : Subgroup (SL(2, F)))
    (hB2 : ∀ a ∈ B, a * a = 1) (hB : Nat.card B = 2 ^ (2 * l))
    {x : SL(2, F)} (hx : x ∈ B) (hx1 : x ≠ 1) :
    Nat.card ↥(fixedSub (hermRep l hF) (Subgroup.zpowers x)) = 2 ^ (2 * l) := by
  have hBeq : Nat.card B = Nat.card F := by
    rw [hB, Nat.card_eq_fintype_card, hF]
  obtain ⟨a, ha⟩ := eq_conj_rootGroup B hB2 hBeq
  let xa : SL(2, F) := a⁻¹ * x * a
  have hxamem : xa ∈ upperSylow := by
    simpa [xa] using (ha x).1 hx
  have hxa1 : xa ≠ 1 := by
    intro h
    apply hx1
    have := congrArg (fun y => a * y * a⁻¹) h
    simpa [xa, mul_assoc] using this
  obtain ⟨t, ht_eq⟩ := mem_upperSylow_iff.mp hxamem
  have ht : t ≠ 0 := by
    intro h0
    apply hxa1
    rw [ht_eq, h0, uMat_zero]
  have hzp : (Subgroup.zpowers x).map (MulAut.conj a⁻¹).toMonoidHom =
      Subgroup.zpowers xa := by
    simpa [xa] using MonoidHom.map_zpowers (MulAut.conj a⁻¹).toMonoidHom x
  have hfixmap : (fixedSub (hermRep l hF) (Subgroup.zpowers x)).map
        (hermRep l hF a⁻¹) = fixedSub (hermRep l hF) (Subgroup.zpowers xa) := by
    rw [← fixedSub_map_conj (ρ := hermRep l hF) a⁻¹ (Subgroup.zpowers x), hzp]
  have hinj : Function.Injective (hermRep l hF a⁻¹ : ↥(hermA l F) → ↥(hermA l F)) := by
    intro u v h
    have := congrArg (hermRep l hF a) h
    simpa using this
  calc Nat.card ↥(fixedSub (hermRep l hF) (Subgroup.zpowers x))
      = Nat.card ↥((fixedSub (hermRep l hF) (Subgroup.zpowers x)).map
          (hermRep l hF a⁻¹)) := by
        exact Nat.card_congr (Submodule.equivMapOfInjective
          (hermRep l hF a⁻¹) hinj (fixedSub (hermRep l hF) (Subgroup.zpowers x)))
    _ = Nat.card ↥(fixedSub (hermRep l hF) (Subgroup.zpowers xa)) := by rw [hfixmap]
    _ = Nat.card ↥(fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t))) := by rw [← ht_eq]
    _ = 2 ^ (2 * l) := card_fixedSub_zpowers_uMat (hF := hF) t ht

private theorem map_sub_image_fieldAut {j : ℕ} {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    (A' : Subgroup SL(2, F)) (x : SL(2, F)) :
    ((fixedSub ρ A').map (ρ x - 1)).map (β.toAddMonoidHom.toZModLinearMap 2) =
      (fixedSub (hermRep l hF) (A'.map (fieldAut F j))).map
        (hermRep l hF (fieldAut F j x) - 1) := by
  ext w
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨β v, (fixedSub_fieldAut_mem (hF := hF) hβ A' v).mp hv, ?_⟩
    have hfwd : β ((ρ x - 1) v) =
        (hermRep l hF (fieldAut F j x) - 1) (β v) := by
      change β ((ρ x) v - v) = (hermAct l (sig_sig hF) (fieldAut F j x) - 1) (β v)
      rw [map_sub, hβ x v]
      rfl
    exact hfwd.symm
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(ρ x - 1) (β.symm u), ⟨β.symm u,
      (fixedSub_fieldAut_mem (hF := hF) hβ A' (β.symm u)).mpr (by simpa using hu), rfl⟩, ?_⟩
    have hfwd : β ((ρ x - 1) (β.symm u)) =
        (hermRep l hF (fieldAut F j x) - 1) u := by
      change β ((ρ x) (β.symm u) - β.symm u) =
        (hermAct l (sig_sig hF) (fieldAut F j x) - 1) u
      rw [map_sub, hβ x (β.symm u), β.apply_symm_apply]
      rfl
    exact hfwd

private theorem map_fixedSub_eq_fieldAut {j : ℕ} {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    (U : Subgroup SL(2, F)) :
    (fixedSub ρ U).map (β.toAddMonoidHom.toZModLinearMap 2) =
      fixedSub (hermRep l hF) (U.map (fieldAut F j)) := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (fixedSub_fieldAut_mem (hF := hF) hβ U v).mp hv
  · intro hu
    exact ⟨β.symm u, (fixedSub_fieldAut_mem (hF := hF) hβ U (β.symm u)).mpr
      (by simpa using hu), by simp⟩

private theorem map_commSub_eq_fieldAut {j : ℕ}
    {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    (A : Subgroup SL(2, F)) :
    (commSub ρ A).map (β.toAddMonoidHom.toZModLinearMap 2) =
      commSub (hermRep l hF) (A.map (fieldAut F j)) := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (commSub_fieldAut_mem (hF := hF) hβ A v).mp hv
  · intro hu
    exact ⟨β.symm u,
      (commSub_fieldAut_mem (hF := hF) hβ A (β.symm u)).mpr
        (by simpa using hu), by simp⟩

include hF in
theorem IsOrthModule.fixedSub_zpowers_inf_commSub_eq_sup_map (horth : IsOrthModule hF ρ)
    (A A' : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card A = 2 ^ (2 * l)) (hA'2 : ∀ a ∈ A', a * a = 1)
    (hA' : Nat.card A' = 2 ^ (2 * l)) (hne : A ≠ A') {x : SL(2, F)} (hx : x ∈ A)
    (hx1 : x ≠ 1) :
    fixedSub ρ (Subgroup.zpowers x) ⊓ commSub ρ A =
      fixedSub ρ A ⊔ (fixedSub ρ A').map (ρ x - 1) := by
  have horth0 := horth
  obtain ⟨j, β, hβ⟩ := horth
  let f : W →ₗ[ZMod 2] ↥(hermA l F) := β.toAddMonoidHom.toZModLinearMap 2
  have hf_inj : Function.Injective f := fun u v h => β.injective (by simpa [f] using h)
  have hs := fieldAut_image_sylow A hA2 hA j
  have hs' := fieldAut_image_sylow A' hA'2 hA' j
  let B : Subgroup (SL(2, F)) := A.map (fieldAut F j)
  let B' : Subgroup (SL(2, F)) := A'.map (fieldAut F j)
  let xB : SL(2, F) := fieldAut F j x
  have hB2 : ∀ a ∈ B, a * a = 1 := hs.1
  have hB : Nat.card B = 2 ^ (2 * l) := hs.2
  have hB'2 : ∀ a ∈ B', a * a = 1 := hs'.1
  have hB' : Nat.card B' = 2 ^ (2 * l) := hs'.2
  have hBne : B ≠ B' := by
    intro h
    apply hne
    have hinj := (fieldAutEquiv (F := F) j).injective
    have hmap : A.map (fieldAutEquiv j).toMonoidHom = A'.map (fieldAutEquiv j).toMonoidHom := h
    exact Subgroup.map_injective hinj hmap
  have hxB : xB ∈ B := Subgroup.mem_map_of_mem _ hx
  have hxB1 : xB ≠ 1 := by
    intro h
    apply hx1
    change fieldAut F j x = 1 at h
    have h' : (fieldAutEquiv (F := F) j) x = (fieldAutEquiv (F := F) j) 1 := by
      simpa [fieldAutEquiv_apply] using h
    exact (fieldAutEquiv (F := F) j).injective h'
  have hmodel := fixedSub_zpowers_inf_commSub_eq_sup_map_model (hF := hF)
    B B' hB2 hB hB'2 hB' hBne hxB hxB1
  have hzp : (Subgroup.zpowers x).map (fieldAut F j) = Subgroup.zpowers xB := by
    simpa [xB] using MonoidHom.map_zpowers (fieldAut F j) x
  have hfix : (fixedSub ρ (Subgroup.zpowers x)).map f =
      fixedSub (hermRep l hF) (Subgroup.zpowers xB) := by
    rw [map_fixedSub_eq_fieldAut (hF := hF) hβ (Subgroup.zpowers x), hzp]
  have hcomm : (commSub ρ A).map f = commSub (hermRep l hF) B := by
    rw [map_commSub_eq_fieldAut (hF := hF) hβ A]
  have hfixA : (fixedSub ρ A).map f = fixedSub (hermRep l hF) B := by
    rw [map_fixedSub_eq_fieldAut (hF := hF) hβ A]
  have himage := map_sub_image_fieldAut (hF := hF) hβ A' x
  have hleft : (fixedSub ρ (Subgroup.zpowers x) ⊓ commSub ρ A).map f =
      fixedSub (hermRep l hF) (Subgroup.zpowers xB) ⊓ commSub (hermRep l hF) B := by
    rw [Submodule.map_inf _ hf_inj, hfix, hcomm]
  have hright : (fixedSub ρ A ⊔ (fixedSub ρ A').map (ρ x - 1)).map f =
      fixedSub (hermRep l hF) B ⊔
        (fixedSub (hermRep l hF) B').map (hermRep l hF xB - 1) := by
    rw [Submodule.map_sup, hfixA, himage]
  have hmap : (fixedSub ρ (Subgroup.zpowers x) ⊓ commSub ρ A).map f =
      (fixedSub ρ A ⊔ (fixedSub ρ A').map (ρ x - 1)).map f := by
    rw [hleft, hright, hmodel]
  exact Submodule.map_injective_of_injective hf_inj hmap

include hF in
theorem IsOrthModule.card_fixedSub_zpowers (horth : IsOrthModule hF ρ)
    (A : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card A = 2 ^ (2 * l)) {x : SL(2, F)} (hx : x ∈ A) (hx1 : x ≠ 1) :
    Nat.card ↥(fixedSub ρ (Subgroup.zpowers x)) = 2 ^ (2 * l) := by
  obtain ⟨j, β, hβ⟩ := horth
  have hs := fieldAut_image_sylow A hA2 hA j
  let B : Subgroup (SL(2, F)) := A.map (fieldAut F j)
  let xB : SL(2, F) := fieldAut F j x
  have hB2 : ∀ a ∈ B, a * a = 1 := hs.1
  have hB : Nat.card B = 2 ^ (2 * l) := hs.2
  have hxB : xB ∈ B := Subgroup.mem_map_of_mem _ hx
  have hxB1 : xB ≠ 1 := by
    intro h
    apply hx1
    change fieldAut F j x = 1 at h
    have h' : (fieldAutEquiv (F := F) j) x = (fieldAutEquiv (F := F) j) 1 := by
      simpa [fieldAutEquiv_apply] using h
    exact (fieldAutEquiv (F := F) j).injective h'
  have hzp : (Subgroup.zpowers x).map (fieldAut F j) = Subgroup.zpowers xB := by
    simpa [xB] using MonoidHom.map_zpowers (fieldAut F j) x
  have hcard : Nat.card ↥(fixedSub ρ (Subgroup.zpowers x)) =
      Nat.card ↥(fixedSub (hermRep l hF) (Subgroup.zpowers xB)) := by
    refine Nat.card_congr (Equiv.subtypeEquiv β.toEquiv ?_)
    intro v
    change v ∈ fixedSub ρ (Subgroup.zpowers x) ↔
      β v ∈ fixedSub (hermRep l hF) (Subgroup.zpowers xB)
    rw [← hzp]
    exact fixedSub_fieldAut_mem (hF := hF) hβ (Subgroup.zpowers x) v
  rw [hcard]
  exact card_fixedSub_zpowers_model (hF := hF) B hB2 hB hxB hxB1



private theorem map_closure_good_eq_upperSylow (B : Subgroup (SL(2, F))) {c : SL(2, F)}
    (hBc : B.map (MulAut.conj c).toMonoidHom = upperSylow) {x : SL(2, F)} {t : F}
    (ht : t ≠ 0) (hxc : c * x * c⁻¹ = uMat t) :
    Subgroup.map (MulAut.conj c).toMonoidHom
        (Subgroup.closure {z : SL(2, F) | z ∈ B ∧
          fixedSub (hermRep l hF) (Subgroup.zpowers x) ⊓
              fixedSub (hermRep l hF) (Subgroup.zpowers z) =
            fixedSub (hermRep l hF) B}) = upperSylow := by
  let xc : SL(2, F) := c * x * c⁻¹
  have hxc' : xc = uMat t := by simpa [xc] using hxc
  have hzp_x : (Subgroup.zpowers x).map (MulAut.conj c).toMonoidHom =
      Subgroup.zpowers xc := by
    simpa [xc] using MonoidHom.map_zpowers (MulAut.conj c).toMonoidHom x
  let goodB : Set (SL(2, F)) := {z : SL(2, F) | z ∈ B ∧
    fixedSub (hermRep l hF) (Subgroup.zpowers x) ⊓
        fixedSub (hermRep l hF) (Subgroup.zpowers z) =
      fixedSub (hermRep l hF) B}
  let goodS : Set (SL(2, F)) := {z : SL(2, F) | z ∈ upperSylow ∧
    fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t)) ⊓
        fixedSub (hermRep l hF) (Subgroup.zpowers z) =
      fixedSub (hermRep l hF) upperSylow}
  have hgood : goodS = (MulAut.conj c) '' goodB := by
    ext z
    constructor
    · intro hz
      have hzS : z ∈ upperSylow := hz.1
      have hzS' : z ∈ B.map (MulAut.conj c).toMonoidHom := by rwa [hBc]
      obtain ⟨w, hwB, hwz⟩ := Subgroup.mem_map.mp hzS'
      have hwx : w = c⁻¹ * z * c := by
        rw [← hwz]
        simp [MulAut.conj_apply, mul_assoc]
      have hzp_w : (Subgroup.zpowers w).map (MulAut.conj c).toMonoidHom =
          Subgroup.zpowers z := by
        rw [hwx]
        simpa [MulAut.conj_apply, mul_assoc] using
          (MonoidHom.map_zpowers (MulAut.conj c).toMonoidHom (c⁻¹ * z * c))
      have hcond := fixedSub_inf_eq_map_conj_iff (ρ := hermRep l hF) c
        (Subgroup.zpowers x) (Subgroup.zpowers w) B
      rw [hzp_x, hzp_w, hBc, hxc'] at hcond
      refine ⟨w, ⟨hwB, ?_⟩, hwz⟩
      exact hcond.mpr hz.2
    · rintro ⟨w, hw, rfl⟩
      have hzS : c * w * c⁻¹ ∈ upperSylow := by
        have h := hw.1
        have hm := Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom h
        rwa [hBc] at hm
      have hzp_w : (Subgroup.zpowers w).map (MulAut.conj c).toMonoidHom =
          Subgroup.zpowers (c * w * c⁻¹) := by
        simpa [MulAut.conj_apply] using
          MonoidHom.map_zpowers (MulAut.conj c).toMonoidHom w
      have hcond := fixedSub_inf_eq_map_conj_iff (ρ := hermRep l hF) c
        (Subgroup.zpowers x) (Subgroup.zpowers w) B
      rw [hzp_x, hzp_w, hBc, hxc'] at hcond
      rw [show (MulAut.conj c) w = c * w * c⁻¹ from rfl]
      exact ⟨hzS, hcond.mp hw.2⟩
  calc Subgroup.map (MulAut.conj c).toMonoidHom (Subgroup.closure goodB)
      = Subgroup.closure ((MulAut.conj c) '' goodB) := MonoidHom.map_closure _ _
    _ = Subgroup.closure goodS := by rw [← hgood]
    _ = upperSylow := (upperSylow_eq_closure_fixedSub_zpowers (hF := hF) t ht).symm

private theorem eq_closure_fixedSub_zpowers_model
    (B B' : Subgroup (SL(2, F))) (hB2 : ∀ a ∈ B, a * a = 1)
    (hB : Nat.card B = 2 ^ (2 * l)) (hB'2 : ∀ a ∈ B', a * a = 1)
    (hB' : Nat.card B' = 2 ^ (2 * l)) (hne : B ≠ B') {x : SL(2, F)} (hx : x ∈ B)
    (hx1 : x ≠ 1) :
    B = Subgroup.closure {z : SL(2, F) | z ∈ B ∧
      fixedSub (hermRep l hF) (Subgroup.zpowers x) ⊓
          fixedSub (hermRep l hF) (Subgroup.zpowers z) =
        fixedSub (hermRep l hF) B} := by
  obtain ⟨c, hBc, -⟩ :=
    exists_conj_map_eq_upperSylow_ltri (hF := hF) B B' hB2 hB hB'2 hB' hne
  have hxcmem : c * x * c⁻¹ ∈ upperSylow := by
    have h := CFSG.CGT.Timmesfeld75.conj_mem_conjSubgroup c hx
    rw [show CFSG.CGT.Timmesfeld75.conjSubgroup c B =
      B.map (MulAut.conj c).toMonoidHom from rfl, hBc] at h
    exact h
  have hxc1 : c * x * c⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have := congrArg (fun y => c⁻¹ * y * c) h
    simpa [mul_assoc] using this
  obtain ⟨t, ht_eq⟩ := mem_upperSylow_iff.mp hxcmem
  have ht : t ≠ 0 := by
    intro h0
    apply hxc1
    rw [ht_eq, h0, uMat_zero]
  have hmapEq := map_closure_good_eq_upperSylow (hF := hF) B hBc ht ht_eq
  have hfinal := Subgroup.map_injective (MulAut.conj c).injective
    (hmapEq.trans hBc.symm)
  exact hfinal.symm



private theorem fixedSub_inf_eq_fieldAut_iff {j : ℕ} {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    (U V' W : Subgroup SL(2, F)) :
    (fixedSub ρ U ⊓ fixedSub ρ V' = fixedSub ρ W) ↔
      (fixedSub (hermRep l hF) (U.map (fieldAut F j)) ⊓
          fixedSub (hermRep l hF) (V'.map (fieldAut F j)) =
        fixedSub (hermRep l hF) (W.map (fieldAut F j))) := by
  constructor
  · intro h
    refine le_antisymm ?_ ?_
    · intro y hy
      have hyU : β.symm y ∈ fixedSub ρ U :=
        (fixedSub_fieldAut_mem (hF := hF) hβ U (β.symm y)).mpr (by
          rw [β.apply_symm_apply]; exact hy.1)
      have hyV : β.symm y ∈ fixedSub ρ V' :=
        (fixedSub_fieldAut_mem (hF := hF) hβ V' (β.symm y)).mpr (by
          rw [β.apply_symm_apply]; exact hy.2)
      have hyW : β.symm y ∈ fixedSub ρ W := by
        rw [← h]
        exact ⟨hyU, hyV⟩
      rw [← β.apply_symm_apply y]
      exact (fixedSub_fieldAut_mem (hF := hF) hβ W (β.symm y)).mp hyW
    · intro y hy
      have hyW : β.symm y ∈ fixedSub ρ W :=
        (fixedSub_fieldAut_mem (hF := hF) hβ W (β.symm y)).mpr (by
          rw [β.apply_symm_apply]; exact hy)
      have hyP : β.symm y ∈ fixedSub ρ U ⊓ fixedSub ρ V' := by
        rwa [← h] at hyW
      have hyU : β.symm y ∈ fixedSub ρ U := hyP.1
      have hyV : β.symm y ∈ fixedSub ρ V' := hyP.2
      rw [← β.apply_symm_apply y]
      exact ⟨(fixedSub_fieldAut_mem (hF := hF) hβ U (β.symm y)).mp hyU,
        (fixedSub_fieldAut_mem (hF := hF) hβ V' (β.symm y)).mp hyV⟩
  · intro h
    refine le_antisymm ?_ ?_
    · intro u hu
      have huU : β u ∈ fixedSub (hermRep l hF) (U.map (fieldAut F j)) :=
        (fixedSub_fieldAut_mem (hF := hF) hβ U u).mp hu.1
      have huV : β u ∈ fixedSub (hermRep l hF) (V'.map (fieldAut F j)) :=
        (fixedSub_fieldAut_mem (hF := hF) hβ V' u).mp hu.2
      have huW : β u ∈ fixedSub (hermRep l hF) (W.map (fieldAut F j)) := by
        rw [← h]; exact ⟨huU, huV⟩
      exact (fixedSub_fieldAut_mem (hF := hF) hβ W u).mpr huW
    · intro w hw
      have hwW : β w ∈ fixedSub (hermRep l hF) (W.map (fieldAut F j)) :=
        (fixedSub_fieldAut_mem (hF := hF) hβ W w).mp hw
      have hwU : β w ∈ fixedSub (hermRep l hF) (U.map (fieldAut F j)) := by
        rw [← h] at hwW
        exact hwW.1
      have hwV : β w ∈ fixedSub (hermRep l hF) (V'.map (fieldAut F j)) := by
        rw [← h] at hwW
        exact hwW.2
      exact ⟨(fixedSub_fieldAut_mem (hF := hF) hβ U w).mpr hwU,
        (fixedSub_fieldAut_mem (hF := hF) hβ V' w).mpr hwV⟩

private theorem image_goodB_eq_goodA {j : ℕ} {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    (A : Subgroup SL(2, F)) {x : SL(2, F)} :
    ((fieldAutEquiv j).symm : SL(2, F) → SL(2, F)) ''
        {z : SL(2, F) | z ∈ A.map (fieldAut F j) ∧
          fixedSub (hermRep l hF) (Subgroup.zpowers (fieldAut F j x)) ⊓
              fixedSub (hermRep l hF) (Subgroup.zpowers z) =
            fixedSub (hermRep l hF) (A.map (fieldAut F j))} =
      {z : SL(2, F) | z ∈ A ∧
        fixedSub ρ (Subgroup.zpowers x) ⊓ fixedSub ρ (Subgroup.zpowers z) =
          fixedSub ρ A} := by
  ext z
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hzA : (fieldAutEquiv j).symm b ∈ A := by
      have hm : b ∈ A.map (fieldAutEquiv j).toMonoidHom := hb.1
      exact Subgroup.mem_map.mp hm |>.elim fun a ha => by
        have : (fieldAutEquiv j).symm b = a := by
          apply (fieldAutEquiv j).injective
          simpa using ha.2.symm
        rw [this]
        exact ha.1
    have hzp_b : (Subgroup.zpowers ((fieldAutEquiv j).symm b)).map (fieldAut F j) =
        Subgroup.zpowers b := by
      change (Subgroup.zpowers ((fieldAutEquiv j).symm b)).map
        (fieldAutEquiv (F := F) j).toMonoidHom = Subgroup.zpowers b
      rw [MonoidHom.map_zpowers]
      congr 1
      exact (fieldAutEquiv (F := F) j).apply_symm_apply b
    have hcond := fixedSub_inf_eq_fieldAut_iff (hF := hF) hβ
      (Subgroup.zpowers x) (Subgroup.zpowers ((fieldAutEquiv j).symm b)) A
    rw [show (Subgroup.zpowers x).map (fieldAut F j) =
        Subgroup.zpowers (fieldAut F j x) from MonoidHom.map_zpowers (fieldAut F j) x,
      hzp_b] at hcond
    exact ⟨hzA, hcond.mpr hb.2⟩
  · intro hz
    refine ⟨fieldAutEquiv j z, ⟨?_, ?_⟩, by simp⟩
    · exact Subgroup.mem_map_of_mem (fieldAutEquiv j).toMonoidHom hz.1
    · have hzp_z : (Subgroup.zpowers z).map (fieldAut F j) =
          Subgroup.zpowers (fieldAutEquiv j z) := by
        rw [MonoidHom.map_zpowers]
        rfl
      have hcond := fixedSub_inf_eq_fieldAut_iff (hF := hF) hβ
        (Subgroup.zpowers x) (Subgroup.zpowers z) A
      rw [show (Subgroup.zpowers x).map (fieldAut F j) =
          Subgroup.zpowers (fieldAut F j x) from MonoidHom.map_zpowers (fieldAut F j) x,
        hzp_z] at hcond
      exact hcond.mp hz.2

include hF in
theorem IsOrthModule.eq_closure_fixedSub_zpowers (horth : IsOrthModule hF ρ)
    (A A' : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card A = 2 ^ (2 * l)) (hA'2 : ∀ a ∈ A', a * a = 1)
    (hA' : Nat.card A' = 2 ^ (2 * l)) (hne : A ≠ A') {x : SL(2, F)} (hx : x ∈ A)
    (hx1 : x ≠ 1) :
    A = Subgroup.closure {z : SL(2, F) | z ∈ A ∧
      fixedSub ρ (Subgroup.zpowers x) ⊓ fixedSub ρ (Subgroup.zpowers z) =
        fixedSub ρ A} := by
  obtain ⟨j, β, hβ⟩ := horth
  let ψ : SL(2, F) ≃* SL(2, F) := fieldAutEquiv j
  let B : Subgroup (SL(2, F)) := A.map (fieldAut F j)
  let B' : Subgroup (SL(2, F)) := A'.map (fieldAut F j)
  let xB : SL(2, F) := fieldAut F j x
  have hs := fieldAut_image_sylow A hA2 hA j
  have hs' := fieldAut_image_sylow A' hA'2 hA' j
  have hB2 : ∀ a ∈ B, a * a = 1 := hs.1
  have hB : Nat.card B = 2 ^ (2 * l) := hs.2
  have hB'2 : ∀ a ∈ B', a * a = 1 := hs'.1
  have hB' : Nat.card B' = 2 ^ (2 * l) := hs'.2
  have hBne : B ≠ B' := by
    intro h
    apply hne
    have hinj := (fieldAutEquiv (F := F) j).injective
    have hmap : A.map (fieldAutEquiv (F := F) j).toMonoidHom =
        A'.map (fieldAutEquiv (F := F) j).toMonoidHom := h
    exact Subgroup.map_injective hinj hmap
  have hxB : xB ∈ B := Subgroup.mem_map_of_mem _ hx
  have hxB1 : xB ≠ 1 := by
    intro h
    apply hx1
    have h' : (fieldAutEquiv (F := F) j) x = (fieldAutEquiv (F := F) j) 1 := by
      simpa [xB, fieldAutEquiv_apply] using h
    exact (fieldAutEquiv (F := F) j).injective h'
  have hmodel := eq_closure_fixedSub_zpowers_model (hF := hF)
    B B' hB2 hB hB'2 hB' hBne hxB hxB1
  let goodB : Set (SL(2, F)) := {z : SL(2, F) | z ∈ B ∧
    fixedSub (hermRep l hF) (Subgroup.zpowers xB) ⊓
        fixedSub (hermRep l hF) (Subgroup.zpowers z) =
      fixedSub (hermRep l hF) B}
  let goodA : Set (SL(2, F)) := {z : SL(2, F) | z ∈ A ∧
    fixedSub ρ (Subgroup.zpowers x) ⊓ fixedSub ρ (Subgroup.zpowers z) =
      fixedSub ρ A}
  have hcomp : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id (SL(2, F)) := by
    ext a
    simp
  have hAeq : A = B.map ψ.symm.toMonoidHom := by
    rw [← show A.map ψ.toMonoidHom = B from rfl, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hgood := image_goodB_eq_goodA (hF := hF) hβ A (x := x)
  have hmapclosure : Subgroup.map ψ.symm.toMonoidHom (Subgroup.closure goodB) =
      Subgroup.closure goodA := by
    rw [MonoidHom.map_closure]
    simpa [MulEquiv.coe_toMonoidHom, goodB, goodA, B, xB] using congrArg Subgroup.closure hgood
  exact hAeq.trans (hmodel ▸ hmapclosure)

end CFSG.RankThree.GF2n.Tim81.Sec2

end
