module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartOne.CTP.StdSub
public import CFSG.RankThree.PartOne.KF.U4Model

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryCoord
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.Classical (subfieldGL coe_subfieldGL)

section Dg

variable {F : Type} [Field F]

@[expose] def dgVec (a b : Fin 3) (u : Fˣ) : Fin 3 → Fˣ :=
  fun i => if i = a then u else if i = b then u⁻¹ else 1

theorem dgVec_mul (a b : Fin 3) (u v : Fˣ) :
    dgVec a b (u * v) = dgVec a b u * dgVec a b v := by
  funext i
  simp only [dgVec, Pi.mul_apply]
  split_ifs <;> simp [mul_comm]

theorem dgVec_one (a b : Fin 3) : dgVec a b (1 : Fˣ) = 1 := by
  funext i
  simp only [dgVec, Pi.one_apply]
  split_ifs <;> simp

theorem dgVec_pow (a b : Fin 3) (u : Fˣ) (k : ℕ) : dgVec a b (u ^ k) = dgVec a b u ^ k := by
  induction k with
  | zero => simp [dgVec_one]
  | succ k ih => rw [pow_succ, dgVec_mul, ih, pow_succ]

theorem dgVec_inv (a b : Fin 3) (u : Fˣ) : dgVec a b u⁻¹ = (dgVec a b u)⁻¹ := by
  funext i
  simp only [dgVec, Pi.inv_apply]
  split_ifs <;> simp

@[expose] def dg3 (a b : Fin 3) (u : Fˣ) : GL (Fin 3) F := diagU (dgVec a b u)

theorem dg3_mul (a b : Fin 3) (u v : Fˣ) :
    dg3 a b (u * v) = (dg3 a b u : GL (Fin 3) F) * dg3 a b v := by
  unfold dg3
  rw [dgVec_mul, diagU_mul]

theorem dg3_pow (a b : Fin 3) (u : Fˣ) (k : ℕ) :
    dg3 a b (u ^ k) = (dg3 a b u : GL (Fin 3) F) ^ k := by
  unfold dg3
  rw [dgVec_pow, diagU_pow]

theorem dg3_inv (a b : Fin 3) (u : Fˣ) : dg3 a b u⁻¹ = (dg3 a b u : GL (Fin 3) F)⁻¹ := by
  unfold dg3
  rw [dgVec_inv]
  apply mul_eq_one_iff_eq_inv.mp
  rw [diagU_mul, inv_mul_cancel, diagU_one]

theorem dg3_injective (a b : Fin 3) : Function.Injective (dg3 a b : Fˣ → GL (Fin 3) F) := by
  intro u v h
  have := congrFun (diagU_injective h) a
  simpa [dgVec] using this

@[expose] def dg3Hom (a b : Fin 3) : Fˣ →* GL (Fin 3) F :=
  MonoidHom.mk' (dg3 a b) (dg3_mul a b)

theorem orderOf_dg3 (a b : Fin 3) (u : Fˣ) : orderOf (dg3 a b u : GL (Fin 3) F) = orderOf u :=
  orderOf_injective (dg3Hom a b) (dg3_injective a b) u

end Dg

section Emb

variable {F : Type} [Field F] {a b : Fin 3}

@[expose] noncomputable def emb (hab : a ≠ b) : GL (Fin 2) F →* GL (Fin 3) F :=
  Units.map (coordEmbedHom F a b hab)

theorem coe_emb (hab : a ≠ b) (X : GL (Fin 2) F) :
    ((emb hab X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      coordEmbed F a b (X : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem emb_injective (hab : a ≠ b) : Function.Injective (emb hab : GL (Fin 2) F →* GL (Fin 3) F) :=
  fun _ _ h => Units.ext (coordEmbed_injective hab
    (congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h))

theorem mem_blk_iff_emb {f : ℕ} (h : UnitaryFieldData 2 f F) (hab : a ≠ b) {g : GL (Fin 3) F} :
    g ∈ blk h hab ↔ ∃ X : GL (Fin 2) F, X ∈ gramSU h (idGram F 2) ∧ g = emb hab X := by
  rw [mem_blk_iff hab]
  constructor
  · rintro ⟨X, hX, hg⟩
    exact ⟨X, hX, Units.ext hg⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X, hX, rfl⟩

theorem dg3_eq_emb (hab : a ≠ b) (u : Fˣ) : (dg3 a b u : GL (Fin 3) F) = emb hab (diag2 u) := by
  apply Units.ext
  rw [coe_emb]
  have h2 : ((diag2 u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      diagonal ![(u : F), ((u⁻¹ : Fˣ) : F)] := rfl
  rw [h2, coordEmbed_diagonal a b hab]
  unfold dg3
  rw [diagU_val]
  congr 1
  funext i
  simp only [dgVec]
  split_ifs <;> rfl

theorem swap2_mul_diag2 (u : Fˣ) :
    (swap2 : GL (Fin 2) F) * diag2 u * (swap2 : GL (Fin 2) F)⁻¹ = diag2 u⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have h1 : (((swap2 : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, -1; 1, 0] := rfl
  have h2 : ((swap2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl
  have h3 : ((diag2 u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(u : F), 0; 0, ((u⁻¹ : Fˣ) : F)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diag2]
  have h4 : ((diag2 u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((u⁻¹ : Fˣ) : F), 0; 0, (u : F)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diag2]
  rw [h1, h2, h3, h4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[expose] noncomputable def sw3 (hab : a ≠ b) : GL (Fin 3) F := emb hab swap2

theorem sw3_dg3 (hab : a ≠ b) (u : Fˣ) :
    sw3 hab * (dg3 a b u : GL (Fin 3) F) * (sw3 hab)⁻¹ = dg3 a b u⁻¹ := by
  unfold sw3
  rw [dg3_eq_emb hab, dg3_eq_emb hab, ← map_inv, ← map_mul, ← map_mul, swap2_mul_diag2]

theorem swap2_ne_one : (swap2 : GL (Fin 2) F) ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [swap2] at this

theorem swap2_mul_self [CharP F 2] : (swap2 : GL (Fin 2) F) * swap2 = 1 := by
  apply Units.ext
  rw [Units.val_mul]
  have h2 : ((swap2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl
  rw [h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

theorem orderOf_sw3 [CharP F 2] (hab : a ≠ b) : orderOf (sw3 hab : GL (Fin 3) F) = 2 := by
  have h1 : (sw3 hab : GL (Fin 3) F) ^ 2 = 1 := by
    unfold sw3
    rw [pow_two, ← map_mul, swap2_mul_self, map_one]
  have h2 : (sw3 hab : GL (Fin 3) F) ≠ 1 := fun h => swap2_ne_one (emb_injective hab (by
    rw [map_one]; exact h))
  exact orderOf_eq_prime h1 h2

theorem sw3_mem_blk {f : ℕ} (h : UnitaryFieldData 2 f F) (hab : a ≠ b) :
    (sw3 hab : GL (Fin 3) F) ∈ blk h hab :=
  (mem_blk_iff_emb h hab).mpr ⟨swap2, swap2_mem h, rfl⟩

theorem dg3_mem_blk {f : ℕ} (h : UnitaryFieldData 2 f F) (hab : a ≠ b) {u : Fˣ}
    (hu : h.norm (u : F) = 1) : (dg3 a b u : GL (Fin 3) F) ∈ blk h hab :=
  (mem_blk_iff_emb h hab).mpr ⟨diag2 u, diag2_mem h u hu, dg3_eq_emb hab u⟩

theorem eq_one_of_commute_swap_diag [CharP F 2] {Y : GL (Fin 2) F}
    (hdet : (Y : Matrix (Fin 2) (Fin 2) F).det = 1) {ζ : Fˣ} (hζ : ζ ≠ ζ⁻¹)
    (h1 : Y * swap2 = swap2 * Y) (h2 : Y * diag2 ζ = diag2 ζ * Y) : Y = 1 := by
  have e1 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h1
  have e2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h2
  simp only [Units.val_mul] at e1 e2
  have hne : (ζ : F) - ((ζ⁻¹ : Fˣ) : F) ≠ 0 := sub_ne_zero.mpr (fun h => hζ (Units.ext h))
  have s : ((swap2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl
  have d : ((diag2 ζ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(ζ : F), 0; 0, ((ζ⁻¹ : Fˣ) : F)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diag2]
  rw [s] at e1
  rw [d] at e2
  have a01 := congrFun (congrFun e2 0) 1
  have a10 := congrFun (congrFun e2 1) 0
  have b00 := congrFun (congrFun e1 0) 0
  have b01 := congrFun (congrFun e1 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at a01 a10 b00 b01
  have hne' : (ζ : F)⁻¹ - (ζ : F) ≠ 0 := by
    rw [Units.val_inv_eq_inv_val] at hne
    intro h
    apply hne
    linear_combination -h
  have y01 : (Y : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have : (Y : Matrix (Fin 2) (Fin 2) F) 0 1 * ((ζ : F)⁻¹ - (ζ : F)) = 0 := by
      linear_combination a01
    exact (mul_eq_zero.mp this).resolve_right hne'
  have y10 : (Y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rw [← b00, y01, neg_zero]
  have hd : (Y : Matrix (Fin 2) (Fin 2) F) 0 0 * (Y : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    rw [Matrix.det_fin_two, y01, y10] at hdet
    linear_combination hdet
  have h2' : (2 : F) = 0 := by
    have := CharP.cast_eq_zero F 2
    simpa using this
  have hp : (Y : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [← b01] at hd
    have : ((Y : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) *
        ((Y : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) = 0 := by
      linear_combination hd + (1 - (Y : Matrix (Fin 2) (Fin 2) F) 0 0) * h2'
    have := mul_self_eq_zero.mp this
    linear_combination this
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hp, y01, y10, ← b01]

theorem coordEmbed_third {a b e' : Fin 3} (hae : e' ≠ a) (hbe : e' ≠ b)
    (X : Matrix (Fin 2) (Fin 2) F) : coordEmbed F a b X e' e' = 1 := by
  simp [coordEmbed, coordIncl, coordProj, Matrix.mul_apply, Fin.sum_univ_two, hae, hbe]

end Emb

section Sub

variable {e : ℕ} {F : Type} [Field F] (K₀ : Subfield F) {a b : Fin 3}

theorem prod_dgVec (hab : a ≠ b) (u : Fˣ) : ∏ i, dgVec a b u i = 1 := by
  fin_cases a <;> fin_cases b <;> simp_all [dgVec, Fin.prod_univ_three]

theorem subfieldGL_dg3 (u₀ : K₀ˣ) :
    subfieldGL K₀ 3 (dg3 a b u₀) = dg3 a b (Units.map K₀.subtype.toMonoidHom u₀) := by
  unfold dg3
  rw [subfieldGL_diagU]
  congr 1
  funext i
  simp only [dgVec]
  split_ifs <;> simp

theorem subfieldGL_emb (hab : a ≠ b) (X : GL (Fin 2) K₀) :
    subfieldGL K₀ 3 (emb hab X) = emb hab (subfieldGL K₀ 2 X) := by
  apply Units.ext
  rw [coe_subfieldGL, coe_emb, coe_emb, coe_subfieldGL]
  exact coordEmbed_map_ringHom K₀.subtype a b _

theorem subfieldGL_swap2 : subfieldGL K₀ 2 (swap2 : GL (Fin 2) K₀) = swap2 := by
  apply Units.ext
  rw [coe_subfieldGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2]

theorem subfieldGL_sw3 (hab : a ≠ b) : subfieldGL K₀ 3 (sw3 hab : GL (Fin 3) K₀) = sw3 hab := by
  unfold sw3
  rw [subfieldGL_emb, subfieldGL_swap2]

theorem sw3_mem_Jst (h₀ : UnitaryFieldData 2 e K₀) (hab : a ≠ b) :
    (sw3 hab : GL (Fin 3) F) ∈ Jst K₀ h₀ hab :=
  ⟨sw3 hab, sw3_mem_blk h₀ hab, subfieldGL_sw3 K₀ hab⟩

theorem dg3_mem_Jst (h₀ : UnitaryFieldData 2 e K₀) (hab : a ≠ b) {u₀ : K₀ˣ}
    (hu : h₀.norm (u₀ : K₀) = 1) :
    (dg3 a b (Units.map K₀.subtype.toMonoidHom u₀) : GL (Fin 3) F) ∈ Jst K₀ h₀ hab :=
  ⟨dg3 a b u₀, dg3_mem_blk h₀ hab hu, subfieldGL_dg3 K₀ u₀⟩

theorem dg3_mem_Bst (hab : a ≠ b) {u₀ : K₀ˣ} (hu : u₀ ^ 5 = 1) :
    (dg3 a b (Units.map K₀.subtype.toMonoidHom u₀) : GL (Fin 3) F) ∈ Bst K₀ := by
  refine (mem_Bst_iff K₀).mpr ⟨dgVec a b u₀, ?_, prod_dgVec hab u₀, ?_⟩
  · intro i
    simp only [dgVec]
    split_ifs <;> simp [inv_pow, hu]
  · unfold dg3
    congr 1
    funext i
    simp only [dgVec]
    split_ifs <;> simp

end Sub

section Torus5

variable {f e : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData 2 f F) (K₀ : Subfield F)
  (h₀ : UnitaryFieldData 2 e K₀) (hbar : ∀ c : K₀, (h₀.bar c : F) = hF.bar c) {a b : Fin 3}

theorem prod_three {d : Fin 3 → Fˣ} {e' : Fin 3} (hab : a ≠ b) (hae : a ≠ e') (hbe : b ≠ e') :
    ∏ i, d i = d a * d b * d e' := by
  have hcard : ({a, b, e'} : Finset (Fin 3)).card = Fintype.card (Fin 3) := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hae]), Finset.card_pair hbe]
    simp
  have huniv : ({a, b, e'} : Finset (Fin 3)) = Finset.univ := Finset.eq_univ_of_card _ hcard
  rw [← huniv, Finset.prod_insert (by simp [hab, hae]), Finset.prod_pair hbe, mul_assoc]

theorem norm_eq_one_of_pow_five (h5 : 5 ∣ 2 ^ e + 1) {x : K₀} (hx : x ^ 5 = 1) :
    h₀.norm x = 1 := by
  obtain ⟨k, hk⟩ := h5
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ']
  rw [show 2 ^ e + 1 = 5 * k from hk, pow_mul, hx, one_pow]

include h₀ in
theorem exists_mem_K₀ (h5 : 5 ∣ 2 ^ e + 1) {ζ : Fˣ} (hζ : ζ ^ 5 = 1) :
    ∃ ζ₀ : K₀ˣ, Units.map K₀.subtype.toMonoidHom ζ₀ = ζ ∧ ζ₀ ^ 5 = 1 := by
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot h₀ Nat.prime_five h5
  have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
  let z₀ : K₀ˣ := Units.mk0 z hz0
  have hzF : IsPrimitiveRoot (z : F) 5 :=
    hz.map_of_injective (f := K₀.subtype) Subtype.val_injective
  have hζF : (ζ : F) ^ 5 = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hζ
    simpa using this
  obtain ⟨i, -, hi⟩ := hzF.eq_pow_of_pow_eq_one hζF
  refine ⟨z₀ ^ i, Units.ext ?_, ?_⟩
  · simp [z₀, hi]
  · apply Units.ext
    simp only [z₀, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]

include hF hbar in
theorem Bst_inf_Jst_eq (h5 : 5 ∣ 2 ^ e + 1) (hab : a ≠ b) {ζ : Fˣ} (hζ : orderOf ζ = 5) :
    Bst K₀ ⊓ Jst K₀ h₀ hab = Subgroup.zpowers (dg3 a b ζ : GL (Fin 3) F) := by
  have hζ5 : ζ ^ 5 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  obtain ⟨ζ₀, hζ₀, hζ₀5⟩ := exists_mem_K₀ K₀ h₀ h5 hζ5
  obtain ⟨e', hea, heb⟩ := CFSG.RankThree.Classical.exists_fin_ne_ne (by norm_num : 3 ≤ 3) a b
  apply le_antisymm
  · rintro y ⟨hyB, hyJ⟩
    obtain ⟨d₀, hd5, hprod, rfl⟩ := (mem_Bst_iff K₀).mp hyB
    have hyblk := map_blk_subfield_le hF K₀ h₀ hbar hab hyJ
    obtain ⟨Y, -, hyY⟩ := (mem_blk_iff hab).mp hyblk
    have hent := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M e' e') hyY
    simp only [diagU_val, Matrix.diagonal_apply_eq] at hent
    rw [coordEmbed_third hea heb] at hent
    have hde : d₀ e' = 1 := by
      apply Units.ext
      apply Subtype.val_injective
      simpa using hent
    have hdb : d₀ b = (d₀ a)⁻¹ := by
      have h3 := prod_three (d := d₀) hab hea.symm heb.symm
      rw [hprod, hde, mul_one] at h3
      exact eq_inv_of_mul_eq_one_right h3.symm
    have hord : orderOf ζ₀ = 5 := by
      rw [← hζ, ← hζ₀]
      exact (orderOf_injective (Units.map K₀.subtype.toMonoidHom : K₀ˣ →* Fˣ)
        (Units.map_injective Subtype.val_injective) ζ₀).symm
    have hprim : IsPrimitiveRoot (ζ₀ : K₀) 5 :=
      IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hord)
    have hda : ((d₀ a : K₀ˣ) : K₀) ^ 5 = 1 := by
      have := congrArg (fun u : K₀ˣ => (u : K₀)) (hd5 a)
      simpa using this
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hda
    have hdai : d₀ a = ζ₀ ^ i := Units.ext (by simpa using hi.symm)
    have hy : diagU (fun j => Units.map K₀.subtype.toMonoidHom (d₀ j)) =
        dg3 a b (ζ ^ i) := by
      unfold dg3
      congr 1
      funext j
      rcases fin_three_cases a b e' j hab hea.symm heb.symm with h | h | h
      · subst h
        simp [dgVec, hdai, ← hζ₀]
      · subst h
        simp [dgVec, hab.symm, hdb, hdai, ← hζ₀]
      · subst h
        simp [dgVec, hea, heb, hde]
    rw [hy, dg3_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i
  · refine Subgroup.zpowers_le.mpr ⟨?_, ?_⟩
    · rw [← hζ₀]
      exact dg3_mem_Bst K₀ hab hζ₀5
    · rw [← hζ₀]
      exact dg3_mem_Jst K₀ h₀ hab (norm_eq_one_of_pow_five K₀ h₀ h5 (by
        have := congrArg (fun u : K₀ˣ => (u : K₀)) hζ₀5
        simpa using this))

end Torus5

end CFSG.RankThree.PartOne.CTP
