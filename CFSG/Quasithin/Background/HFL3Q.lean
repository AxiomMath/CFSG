module

public import CFSG.Quasithin.Background.HFL3Out

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag SU3
  Tri

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem uni3_inv_entries {x : SpecialLinearGroup (Fin 3) K} (hx : x ∈ unitriangular 3 K) :
    ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 =
        -(x : Matrix (Fin 3) (Fin 3) K) 0 1 ∧
      ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 =
        -(x : Matrix (Fin 3) (Fin 3) K) 1 2 := by
  have hxi : x⁻¹ ∈ unitriangular 3 K := inv_mem hx
  have h1 := uni3_mul_01 hxi hx
  have h2 := uni3_mul_12 hxi hx
  rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne (by decide)] at h1 h2
  constructor
  · linear_combination -h1
  · linear_combination -h2

@[expose] def Q1 (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {x | x ∈ unitriangular 3 K ∧ (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' {x y} (hx : x ∈ unitriangular 3 K ∧ (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0)
      (hy : y ∈ unitriangular 3 K ∧ (y : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) :=
    ⟨mul_mem hx.1 hy.1, by rw [uni3_mul_12 hx.1 hy.1, hx.2, hy.2, add_zero]⟩
  inv_mem' {x} (hx : x ∈ unitriangular 3 K ∧ (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) :=
    ⟨inv_mem hx.1, by rw [(uni3_inv_entries hx.1).2, hx.2, neg_zero]⟩

@[expose] def Q2 (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {x | x ∈ unitriangular 3 K ∧ (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' {x y} (hx : x ∈ unitriangular 3 K ∧ (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
      (hy : y ∈ unitriangular 3 K ∧ (y : Matrix (Fin 3) (Fin 3) K) 0 1 = 0) :=
    ⟨mul_mem hx.1 hy.1, by rw [uni3_mul_01 hx.1 hy.1, hx.2, hy.2, add_zero]⟩
  inv_mem' {x} (hx : x ∈ unitriangular 3 K ∧ (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0) :=
    ⟨inv_mem hx.1, by rw [(uni3_inv_entries hx.1).1, hx.2, neg_zero]⟩

omit [Finite K] [CharP K 2] in
theorem mem_Q2 {x : SpecialLinearGroup (Fin 3) K} :
    x ∈ Q2 K ↔ x ∈ unitriangular 3 K ∧ (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := Iff.rfl

omit [CharP K 2] in
theorem card_Q1_le : Nat.card (Q1 K) ≤ Nat.card K ^ 2 := by
  let f : ↥(Q1 K) → K × K := fun x =>
    ((x : Matrix (Fin 3) (Fin 3) K) 0 1, (x : Matrix (Fin 3) (Fin 3) K) 0 2)
  have hf : Function.Injective f := fun x y h => Subtype.ext (uni3_ext x.2.1 y.2.1
    (congrArg Prod.fst h) (congrArg Prod.snd h) (x.2.2.trans y.2.2.symm))
  calc Nat.card (Q1 K) ≤ Nat.card (K × K) := Nat.card_le_card_of_injective f hf
    _ = Nat.card K ^ 2 := by rw [Nat.card_prod, sq]

omit [CharP K 2] in
theorem card_Q2_le : Nat.card (Q2 K) ≤ Nat.card K ^ 2 := by
  let f : ↥(Q2 K) → K × K := fun x =>
    ((x : Matrix (Fin 3) (Fin 3) K) 0 2, (x : Matrix (Fin 3) (Fin 3) K) 1 2)
  have hf : Function.Injective f := fun x y h => Subtype.ext (uni3_ext x.2.1 y.2.1
    (x.2.2.trans y.2.2.symm) (congrArg Prod.fst h) (congrArg Prod.snd h))
  calc Nat.card (Q2 K) ≤ Nat.card (K × K) := Nat.card_le_card_of_injective f hf
    _ = Nat.card K ^ 2 := by rw [Nat.card_prod, sq]

omit [Finite K] [CharP K 2] in
theorem transvection_mem_Q1 {j : Fin 3} (hj : (0 : Fin 3) ≠ j) (a : K) :
    SpecialLinearGroup.transvection hj a ∈ Q1 K := by
  refine ⟨mem_unitriangular.2 ⟨fun i k hik => ?_, fun i => ?_⟩, ?_⟩ <;>
    rw [Matrix.SpecialLinearGroup.transvection_coe] <;> fin_cases j
  · exact absurd rfl hj
  · fin_cases i <;> fin_cases k <;> simp_all [Matrix.transvection, Matrix.single_apply]
  · fin_cases i <;> fin_cases k <;> simp_all [Matrix.transvection, Matrix.single_apply]
  · exact absurd rfl hj
  · fin_cases i <;> simp [Matrix.transvection, Matrix.single_apply]
  · fin_cases i <;> simp [Matrix.transvection, Matrix.single_apply]
  · exact absurd rfl hj
  · simp [Matrix.transvection, Matrix.single_apply]
  · simp [Matrix.transvection, Matrix.single_apply]

theorem card_fixV_Q1_le (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card ↥(fixV ((Q1 K).map (rho hK))) ≤ 2 ^ n := by
  have hfix : ∀ X ∈ fixV ((Q1 K).map (rho hK)), ∀ i j : Fin 3, ¬ (i = 0 ∧ j = 0) →
      mat X i j = 0 := by
    intro X hX
    refine eq_zero_of_fix hn hK (fun a => ?_) (fun a => ?_)
    · rw [← rho_transvection]
      exact hX _ ⟨_, transvection_mem_Q1 (by decide) a, rfl⟩
    · rw [← rho_transvection]
      exact hX _ ⟨_, transvection_mem_Q1 (by decide) a, rfl⟩
  let f : ↥(fixV ((Q1 K).map (rho hK))) → {b : K // bar n b = b} := fun X =>
    ⟨mat (X : HMod n K) 0 0, herm_apply _ 0 0⟩
  have hf : Function.Injective f := by
    intro X Y h
    have h00 : mat (X : HMod n K) 0 0 = mat (Y : HMod n K) 0 0 := congrArg Subtype.val h
    apply Subtype.ext
    apply mat_injective
    ext i j
    by_cases hij : i = 0 ∧ j = 0
    · rw [hij.1, hij.2]
      exact h00
    · rw [hfix _ X.2 i j hij, hfix _ Y.2 i j hij]
  calc Nat.card ↥(fixV ((Q1 K).map (rho hK))) ≤ Nat.card {b : K // bar n b = b} :=
        Nat.card_le_card_of_injective f hf
    _ = 2 ^ n := card_fixed hn hK

@[expose] def blkW (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] : Subgroup (HMod n K) where
  carrier := {X | mat X 0 2 = 0 ∧ mat X 1 2 = 0 ∧ mat X 2 2 = 0}
  one_mem' := ⟨by simp [mat_one], by simp [mat_one], by simp [mat_one]⟩
  mul_mem' {X Y} (hX : mat X 0 2 = 0 ∧ mat X 1 2 = 0 ∧ mat X 2 2 = 0)
      (hY : mat Y 0 2 = 0 ∧ mat Y 1 2 = 0 ∧ mat Y 2 2 = 0) :=
    ⟨by simp [mat_mul, hX.1, hY.1], by simp [mat_mul, hX.2.1, hY.2.1],
      by simp [mat_mul, hX.2.2, hY.2.2]⟩
  inv_mem' {X} (hX : mat X 0 2 = 0 ∧ mat X 1 2 = 0 ∧ mat X 2 2 = 0) :=
    ⟨by simp [mat_inv, hX.1], by simp [mat_inv, hX.2.1], by simp [mat_inv, hX.2.2]⟩

theorem mem_blkW {X : HMod n K} :
    X ∈ blkW n K ↔ mat X 0 2 = 0 ∧ mat X 1 2 = 0 ∧ mat X 2 2 = 0 := Iff.rfl

theorem card_blkW (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card (blkW n K) = Nat.card K ^ 2 := by
  classical
  let Fq := {b : K // bar n b = b}
  let mk : Fq × Fq × K → HMod n K := fun p =>
    mkH !![p.1.1, p.2.2, 0; bar n p.2.2, p.2.1.1, 0; 0, 0, 0] (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [conjM, p.1.2, p.2.1.2, bar_bar hK])
  let e : ↥(blkW n K) ≃ Fq × Fq × K :=
    { toFun := fun X => (⟨mat (X : HMod n K) 0 0, herm_apply _ 0 0⟩,
        ⟨mat (X : HMod n K) 1 1, herm_apply _ 1 1⟩, mat (X : HMod n K) 0 1)
      invFun := fun p => ⟨mk p, by
        refine ⟨?_, ?_, ?_⟩ <;> simp [mk, mat_mkH]⟩
      left_inv := fun X => by
        obtain ⟨h02, h12, h22⟩ := X.2
        apply Subtype.ext
        apply mat_injective
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mk, mat_mkH, h02, h12, h22]
        · exact herm_apply _ 1 0
        · rw [← herm_apply _ 2 0, h02, map_zero]
        · rw [← herm_apply _ 2 1, h12, map_zero]
      right_inv := fun p => by
        simp [mk, mat_mkH] }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, card_fixed hn hK, hK]
  ring

theorem blkW_le_fixV {x : SpecialLinearGroup (Fin 3) K} (hx : x ∈ Q2 K)
    (hK : Nat.card K = (2 ^ n) ^ 2) {X : HMod n K} (hX : X ∈ blkW n K) : rho hK x X = X := by
  obtain ⟨x00, x11, x22, x10, x20, x21⟩ := uni3_entries hx.1
  have x01 := hx.2
  obtain ⟨h02, h12, h22⟩ := hX
  have h20 : mat X 2 0 = 0 := by rw [← herm_apply, h02, map_zero]
  have h21 : mat X 2 1 = 0 := by rw [← herm_apply, h12, map_zero]
  apply mat_injective
  rw [mat_rho]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tw, Matrix.mul_apply, Fin.sum_univ_three, conjM, x00, x11, x22, x10, x20, x21, x01, h02,
      h12, h22, h20, h21]

theorem eq_one_of_rho_uni3 (hK : Nat.card K = (2 ^ n) ^ 2) {x : SpecialLinearGroup (Fin 3) K}
    (hx : x ∈ unitriangular 3 K) (h : rho hK x = 1) : x = 1 := by
  obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK (B := SpecialLinearGroup.toGL x) h
  have hd' : (x : Matrix (Fin 3) (Fin 3) K) = d • 1 := hd
  have h00 : d = 1 := by
    have := congrFun (congrFun hd' 0) 0
    rw [(uni3_entries hx).1] at this
    simpa using this.symm
  apply Subtype.ext
  rw [hd', h00, one_smul, Matrix.SpecialLinearGroup.coe_one]

theorem eq_Q_of_le_uni3 {P : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hPU : P ≤ unitriangular 3 K) (hc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hs : ∀ x ∈ P, x * x = 1) (hcard : Nat.card K ^ 2 ≤ Nat.card P) : P = Q1 K ∨ P = Q2 K := by
  rcases uni3_cases hPU hc hs with h12 | h01
  · left
    have hle : P ≤ Q1 K := fun x hx => ⟨hPU hx, h12 x hx⟩
    exact Subgroup.eq_of_le_of_card_ge hle (card_Q1_le.trans hcard)
  · right
    have hle : P ≤ Q2 K := fun x hx => ⟨hPU hx, h01 x hx⟩
    exact Subgroup.eq_of_le_of_card_ge hle (card_Q2_le.trans hcard)

theorem eq_rhoQ2_of_le (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {B : Subgroup (MulAut (HMod n K))} (hBU : B ≤ (unitriangular 3 K).map (rho hK))
    (hBe : IsElemAbelian2 B) (hcard : Nat.card K ^ 2 ≤ Nat.card B)
    (hfix : 2 ^ n < Nat.card (fixV B)) : B = (Q2 K).map (rho hK) := by
  let P := B.comap (rho hK) ⊓ unitriangular 3 K
  have hinj : ∀ x ∈ P, rho hK x = 1 → x = 1 := fun x hx h => eq_one_of_rho_uni3 hK hx.2 h
  have hPB : P.map (rho hK) = B := by
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.1
    · intro hb
      obtain ⟨x, hxU, rfl⟩ := hBU hb
      exact ⟨x, ⟨hb, hxU⟩, rfl⟩
  have hc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have h1 : rho hK (x * y * (y * x)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hBe.1 _ hx.1 _ hy.1, mul_inv_cancel]
    exact mul_inv_eq_one.1 (hinj _ (P.mul_mem (P.mul_mem hx hy) (P.inv_mem (P.mul_mem hy hx)))
      h1)
  have hs : ∀ x ∈ P, x * x = 1 := by
    intro x hx
    refine hinj _ (P.mul_mem hx hx) ?_
    rw [map_mul, ← sq]
    exact hBe.2 _ hx.1
  have hcP : Nat.card K ^ 2 ≤ Nat.card P := by
    rw [← card_map_rho_of_inj hK hinj, hPB]
    exact hcard
  rcases eq_Q_of_le_uni3 (inf_le_right : P ≤ unitriangular 3 K) hc hs hcP with h | h
  · exfalso
    have h' : P = Q1 K := h
    rw [← hPB, h'] at hfix
    exact absurd (card_fixV_Q1_le hn hK) (not_le.2 hfix)
  · have h' : P = Q2 K := h
    rw [← hPB, h']

theorem conj_eq_congrHom {W : Type*} [CommGroup W] (c : MulAut W) :
    (MulAut.conj c).toMonoidHom = congrHom c := by
  ext x w
  rfl

theorem card_fixV_map_conj {W : Type*} [CommGroup W] (c : MulAut W) (A : Subgroup (MulAut W)) :
    Nat.card (fixV (A.map (MulAut.conj c).toMonoidHom)) = Nat.card (fixV A) := by
  rw [conj_eq_congrHom, fixV_map_congrHom]
  exact Subgroup.card_map_of_injective c.injective

theorem eq_of_le_isPGroup (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {T : Subgroup (MulAut (HMod n K))} (hT : T ≤ img hK) (hT2 : IsPGroup 2 T)
    {B₁ B₂ : Subgroup (MulAut (HMod n K))} (h₁ : B₁ ≤ T) (h₂ : B₂ ≤ T)
    (he₁ : IsElemAbelian2 B₁) (he₂ : IsElemAbelian2 B₂) (hc₁ : Nat.card K ^ 2 ≤ Nat.card B₁)
    (hc₂ : Nat.card K ^ 2 ≤ Nat.card B₂) (hf₁ : 2 ^ n < Nat.card (fixV B₁))
    (hf₂ : 2 ^ n < Nat.card (fixV B₂)) : B₁ = B₂ := by
  obtain ⟨g, P, hPU, -, -, hPmap⟩ := exists_conj_uni3 hK (hT.trans (img_le_linImg hK)) hT2
  set c := MulAut.conj (rho hK g) with hcdef
  have hTU : T.map c.toMonoidHom ≤ (unitriangular 3 K).map (rho hK) := by
    rw [← hPmap]
    exact Subgroup.map_mono hPU
  have key : ∀ B : Subgroup (MulAut (HMod n K)), B ≤ T → IsElemAbelian2 B →
      Nat.card K ^ 2 ≤ Nat.card B → 2 ^ n < Nat.card (fixV B) →
        B.map c.toMonoidHom = (Q2 K).map (rho hK) := by
    intro B hBT hBe hcB hfB
    refine eq_rhoQ2_of_le hn hK ((Subgroup.map_mono hBT).trans hTU) ?_ ?_ ?_
    · rw [conj_eq_congrHom]
      exact (isElemAbelian2_map_congrHom _).2 hBe
    · rw [Subgroup.card_map_of_injective c.injective]
      exact hcB
    · rw [card_fixV_map_conj]
      exact hfB
  have h := (key B₁ h₁ he₁ hc₁ hf₁).trans (key B₂ h₂ he₂ hc₂ hf₂).symm
  exact Subgroup.map_injective c.injective h

theorem exists_conj_eq_Q2 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (HMod n K))} (hA : A ≤ norm hK) (hAe : IsElemAbelian2 A)
    (hcard : Nat.card K ^ 2 ≤ Nat.card A) (hfix : 2 ^ n < Nat.card (fixV A)) :
    ∃ g : SpecialLinearGroup (Fin 3) K,
      A.map (MulAut.conj (rho hK g)).toMonoidHom = (Q2 K).map (rho hK) := by
  have hAL : A ≤ img hK := by
    refine le_img_of_card hn hK hA hAe (lt_of_lt_of_le ?_ hcard)
    rw [hK, ← pow_mul, ← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hA2 : IsPGroup 2 A := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hAe.2 x x.2)⟩
  obtain ⟨g, P, hPU, -, -, hPmap⟩ := exists_conj_uni3 hK (hAL.trans (img_le_linImg hK)) hA2
  refine ⟨g, eq_rhoQ2_of_le hn hK ?_ ?_ ?_ ?_⟩
  · rw [← hPmap]
    exact Subgroup.map_mono hPU
  · rw [conj_eq_congrHom]
    exact (isElemAbelian2_map_congrHom _).2 hAe
  · rw [Subgroup.card_map_of_injective (MulAut.conj (rho hK g)).injective]
    exact hcard
  · rw [card_fixV_map_conj]
    exact hfix

theorem le_normalizer_of_le (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {S A : Subgroup (MulAut (HMod n K))} (hS : S ≤ norm hK) (hS2 : IsPGroup 2 S) (hAS : A ≤ S)
    (hAe : IsElemAbelian2 A) (hcard : Nat.card K ^ 2 ≤ Nat.card A)
    (hfix : 2 ^ n < Nat.card (fixV A)) : S ≤ Subgroup.normalizer (A : Set (MulAut (HMod n K))) := by
  have hAL : A ≤ img hK := by
    refine le_img_of_card hn hK (hAS.trans hS) hAe (lt_of_lt_of_le ?_ hcard)
    rw [hK, ← pow_mul, ← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  intro x hx
  set c := MulAut.conj x with hc
  set A' := A.map c.toMonoidHom with hA'
  have hA'S : A' ≤ S := by
    rintro _ ⟨a, ha, rfl⟩
    exact S.mul_mem (S.mul_mem hx (hAS ha)) (S.inv_mem hx)
  have hA'L : A' ≤ img hK := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hS hx) a).mp (hAL ha)
  have hT2 : IsPGroup 2 ↥(S ⊓ img hK) := hS2.to_le inf_le_left
  have heq : A = A' := eq_of_le_isPGroup hn hK (inf_le_right : S ⊓ img hK ≤ img hK) hT2
    (le_inf hAS hAL) (le_inf hA'S hA'L) hAe
    (by rw [hA', conj_eq_congrHom]; exact (isElemAbelian2_map_congrHom _).2 hAe) hcard
    (by rw [Subgroup.card_map_of_injective c.injective]; exact hcard) hfix
    (by rw [card_fixV_map_conj]; exact hfix)
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have : x * a * x⁻¹ ∈ A' := ⟨a, ha, rfl⟩
    rwa [← heq] at this
  · intro ha
    have h1 : x * a * x⁻¹ ∈ A' := by rwa [← heq]
    obtain ⟨b, hb, hbe⟩ := h1
    have : b = a := by
      have := hbe
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      exact mul_left_cancel (mul_right_cancel this)
    rwa [← this]

end CFSG.Quasithin.H.L3Nine
