module

public import CFSG.Quasithin.H13.U4ParSp
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ASVolI

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.QuasithinUnique.Setup.X7a

section SpBlocks

variable {F : Type} [Field F]

abbrev burnsideF4m_spM (A : StatedSp 2 F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)

theorem burnsideF4m_mem_flag_two (v : Fin 2 ⊕ Fin 2 → F) :
    v ∈ flag 2 F 2 ↔ ∀ j, v (Sum.inr j) = 0 := by
  rw [mem_flag_of_le (by norm_num), mem_isoFlag]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun j hj => ?_⟩
    have := j.2
    omega

theorem burnsideF4m_spQ1_bl {A : StatedSp 2 F} (hA : A ∈ Q2 F 1) (i j : Fin 2) :
    burnsideF4m_spM A (Sum.inr i) (Sum.inl j) = 0 := by
  have hmem : (Pi.single (Sum.inl j) (1 : F) : Fin 2 ⊕ Fin 2 → F) ∈ flag 2 F 2 := by
    rw [burnsideF4m_mem_flag_two]
    intro k
    simp
  have hA' : A ∈ stabilizer 2 F (flag 2 F 2) := hA
  rw [mem_stabilizer] at hA'
  have himg : burnsideF4m_spM A *ᵥ Pi.single (Sum.inl j) 1 ∈ flag 2 F 2 := by
    rw [← hA']
    exact ⟨_, hmem, rfl⟩
  rw [burnsideF4m_mem_flag_two, mulVec_single_one] at himg
  exact himg i

theorem burnsideF4m_spQ1_of_bl {A : StatedSp 2 F}
    (h1 : ∀ i j, burnsideF4m_spM A (Sum.inr i) (Sum.inl j) = 0)
    (h2 : ∀ i j, burnsideF4m_spM A⁻¹ (Sum.inr i) (Sum.inl j) = 0) : A ∈ Q2 F 1 := by
  have key : ∀ (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F),
      (∀ i j, M (Sum.inr i) (Sum.inl j) = 0) → ∀ v ∈ flag 2 F 2, M *ᵥ v ∈ flag 2 F 2 := by
    intro M hM v hv
    rw [burnsideF4m_mem_flag_two] at hv ⊢
    intro i
    rw [mulVec, dotProduct, Fintype.sum_sum_type]
    simp [hM, hv]
  exact mem_stabilizer_of_mulVec_mem (key _ h1) (key _ h2)

@[expose] def burnsideF4m_spTL (A : StatedSp 2 F) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i j => burnsideF4m_spM A (Sum.inl i) (Sum.inl j)

theorem burnsideF4m_spTL_mul (A : StatedSp 2 F) {B : StatedSp 2 F} (hB : B ∈ Q2 F 1) :
    burnsideF4m_spTL (A * B) = burnsideF4m_spTL A * burnsideF4m_spTL B := by
  ext i j
  have hbl := burnsideF4m_spQ1_bl hB
  simp only [burnsideF4m_spM] at hbl
  simp only [burnsideF4m_spTL, burnsideF4m_spM, Matrix.of_apply, Matrix.mul_apply,
    Subgroup.coe_mul, Units.val_mul, Fintype.sum_sum_type, hbl, mul_zero, Finset.sum_const_zero,
    add_zero]

theorem burnsideF4m_spTL_one : burnsideF4m_spTL (1 : StatedSp 2 F) = 1 := by
  ext i j
  simp [burnsideF4m_spTL, burnsideF4m_spM, Matrix.one_apply]

theorem burnsideF4m_spTL_inv_mul {A : StatedSp 2 F} (hA : A ∈ Q2 F 1) :
    burnsideF4m_spTL A⁻¹ * burnsideF4m_spTL A = 1 := by
  rw [← burnsideF4m_spTL_mul _ hA, inv_mul_cancel, burnsideF4m_spTL_one]

theorem burnsideF4m_spTL_pow {A : StatedSp 2 F} (hA : A ∈ Q2 F 1) (n : ℕ) :
    burnsideF4m_spTL (A ^ n) = burnsideF4m_spTL A ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, burnsideF4m_spTL_one]
  | succ n ih => rw [pow_succ, pow_succ, burnsideF4m_spTL_mul _ hA, ih]

@[expose] def burnsideF4m_spU1 (F : Type) [Field F] : Subgroup (StatedSp 2 F) where
  carrier := {A | A ∈ Q2 F 1 ∧ burnsideF4m_spTL A = 1}
  one_mem' := ⟨(Q2 F 1).one_mem, burnsideF4m_spTL_one⟩
  mul_mem' := by
    rintro A B ⟨hA, hA1⟩ ⟨hB, hB1⟩
    exact ⟨(Q2 F 1).mul_mem hA hB, by rw [burnsideF4m_spTL_mul _ hB, hA1, hB1, one_mul]⟩
  inv_mem' := by
    rintro A ⟨hA, hA1⟩
    refine ⟨(Q2 F 1).inv_mem hA, ?_⟩
    have := burnsideF4m_spTL_inv_mul hA
    rwa [hA1, mul_one] at this

theorem burnsideF4m_spU1_normal :
    Q2 F 1 ≤ Subgroup.normalizer ((burnsideF4m_spU1 F : Subgroup (StatedSp 2 F)) :
      Set (StatedSp 2 F)) := by
  have hconj : ∀ B ∈ Q2 F 1, ∀ A ∈ burnsideF4m_spU1 F, B * A * B⁻¹ ∈ burnsideF4m_spU1 F := by
    rintro B hB A ⟨hA, hA1⟩
    refine ⟨(Q2 F 1).mul_mem ((Q2 F 1).mul_mem hB hA) ((Q2 F 1).inv_mem hB), ?_⟩
    rw [burnsideF4m_spTL_mul _ ((Q2 F 1).inv_mem hB), burnsideF4m_spTL_mul _ hA, hA1, mul_one,
      ← burnsideF4m_spTL_mul _ ((Q2 F 1).inv_mem hB), mul_inv_cancel, burnsideF4m_spTL_one]
  intro B hB
  rw [Subgroup.mem_normalizer_iff]
  intro A
  refine ⟨hconj B hB A, fun h => ?_⟩
  have := hconj B⁻¹ ((Q2 F 1).inv_mem hB) _ h
  simpa [mul_assoc] using this

theorem burnsideF4m_spU1_entries {A : StatedSp 2 F} (hA : A ∈ burnsideF4m_spU1 F) (i j : Fin 2) :
    burnsideF4m_spM A (Sum.inl i) (Sum.inl j) = (if i = j then 1 else 0) ∧
      burnsideF4m_spM A (Sum.inr i) (Sum.inl j) = 0 := by
  refine ⟨?_, burnsideF4m_spQ1_bl hA.1 i j⟩
  have := congrFun (congrFun hA.2 i) j
  simpa [burnsideF4m_spTL, Matrix.one_apply] using this

theorem burnsideF4m_spU1_ff {A : StatedSp 2 F} (hA : A ∈ burnsideF4m_spU1 F) (i j : Fin 2) :
    burnsideF4m_spM A (Sum.inr i) (Sum.inr j) = if i = j then 1 else 0 := by
  have hs := congrFun (congrFun (CFSG.Quasithin.H13.U4Par.symp_of_mem_statedSp A.2)
    (Sum.inl i)) (Sum.inr j)
  have he := burnsideF4m_spU1_entries hA
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
    CFSG.Quasithin.H13.U4Par.spJ, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply,
    Matrix.neg_apply, mul_zero, zero_mul, add_zero, zero_add, Fin.sum_univ_two] at hs
  simp only [(he _ _).1, (he _ _).2] at hs
  fin_cases i <;> fin_cases j <;> simpa using hs

theorem burnsideF4m_spU1_sq [CharP F 2] {A : StatedSp 2 F} (hA : A ∈ burnsideF4m_spU1 F) :
    A * A = 1 := by
  have he := burnsideF4m_spU1_entries hA
  have hf := burnsideF4m_spU1_ff hA
  refine Subtype.ext (Units.ext ?_)
  ext a b
  rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [Fin.sum_univ_two, (he _ _).1, (he _ _).2, hf, Subgroup.coe_one, Units.val_one,
      Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false] <;>
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

theorem burnsideF4m_spU1_isPGroup [CharP F 2] : IsPGroup 2 (burnsideF4m_spU1 F) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, pow_two]
  exact burnsideF4m_spU1_sq g.2

theorem burnsideF4m_spU1_le_Q0 : burnsideF4m_spU1 F ≤ Q2 F 0 := by
  intro A hA
  have hcol : ∀ (B : StatedSp 2 F), B ∈ burnsideF4m_spU1 F → ∀ b, b ≠ Sum.inl 0 →
      burnsideF4m_spM B b (Sum.inl 0) = 0 := by
    intro B hB b hb
    have he := burnsideF4m_spU1_entries hB
    rcases b with i | i
    · have hi : i ≠ 0 := fun h => hb (by rw [h])
      rw [(he i 0).1, if_neg hi]
    · exact (he i 0).2
  exact CFSG.Quasithin.H13.U4Par.mem_Q2_zero_of_col (hcol A hA)
    (hcol A⁻¹ ((burnsideF4m_spU1 F).inv_mem hA))

end SpBlocks

section SpTwo

variable {F : Type} [Field F]

noncomputable def burnsideF4m_zmod2Equiv (hF : Nat.card F = 2) : ZMod 2 ≃+* F :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  letI : Fintype F := Fintype.ofFinite F
  letI : CharP F 2 := charP_of_card_eq_prime (p := 2) (by rw [Fintype.card_eq_nat_card, hF])
  RingEquiv.ofBijective (ZMod.castHom (dvd_refl 2) F)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨(ZMod.castHom (dvd_refl 2) F).injective, by
        rw [ZMod.card, Fintype.card_eq_nat_card, hF]⟩)

@[expose] def burnsideF4m_r2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]

theorem burnsideF4m_gl2_pow_six :
    ∀ τ : Matrix (Fin 2) (Fin 2) (ZMod 2), τ.det ≠ 0 → τ ^ 6 = 1 := by
  decide

theorem burnsideF4m_gl2_inv_prod :
    ∀ τ : Matrix (Fin 2) (Fin 2) (ZMod 2), τ * τ = 1 → τ ≠ 1 →
      (τ * (burnsideF4m_r2 * τ * (burnsideF4m_r2 * burnsideF4m_r2))) ^ 3 = 1 ∧
        τ * (burnsideF4m_r2 * τ * (burnsideF4m_r2 * burnsideF4m_r2)) ≠ 1 := by
  decide

@[expose] def burnsideF4m_J2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks 0 1 (-1) 0

theorem burnsideF4m_spJ_map (hF : Nat.card F = 2) :
    (burnsideF4m_zmod2Equiv hF).toRingHom.mapMatrix burnsideF4m_J2 =
      CFSG.Quasithin.H13.U4Par.spJ F := by
  have hneg : ∀ x : ZMod 2, (burnsideF4m_zmod2Equiv hF) (-x) = -(burnsideF4m_zmod2Equiv hF) x :=
    fun x => map_neg _ x
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · simp [burnsideF4m_J2, CFSG.Quasithin.H13.U4Par.spJ]
  · simp only [burnsideF4m_J2, CFSG.Quasithin.H13.U4Par.spJ, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.fromBlocks_apply₁₂, Matrix.one_apply]
    split_ifs <;> simp
  · simp only [burnsideF4m_J2, CFSG.Quasithin.H13.U4Par.spJ, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.one_apply]
    split_ifs
    · rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hneg, map_one]
    · rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hneg, map_zero]
  · simp [burnsideF4m_J2, CFSG.Quasithin.H13.U4Par.spJ]

@[expose] noncomputable def burnsideF4m_spElt (hF : Nat.card F = 2)
    (X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) (hXY : X * Y = 1) (hYX : Y * X = 1)
    (hX : Xᵀ * burnsideF4m_J2 * X = burnsideF4m_J2) : StatedSp 2 F :=
  ⟨⟨(burnsideF4m_zmod2Equiv hF).toRingHom.mapMatrix X,
      (burnsideF4m_zmod2Equiv hF).toRingHom.mapMatrix Y,
      by rw [← map_mul, hXY, map_one], by rw [← map_mul, hYX, map_one]⟩, by
    apply Subgroup.subset_closure
    change ((burnsideF4m_zmod2Equiv hF).toRingHom.mapMatrix X)ᵀ *
        CFSG.Quasithin.H13.U4Par.spJ F * (burnsideF4m_zmod2Equiv hF).toRingHom.mapMatrix X =
      CFSG.Quasithin.H13.U4Par.spJ F
    rw [← burnsideF4m_spJ_map hF]
    have ht : ((burnsideF4m_zmod2Equiv hF).toRingHom.mapMatrix X)ᵀ =
        (burnsideF4m_zmod2Equiv hF).toRingHom.mapMatrix Xᵀ := by
      simp only [RingHom.mapMatrix_apply, Matrix.transpose_map]
    rw [ht, ← map_mul, ← map_mul, hX]⟩

theorem burnsideF4m_spM_spElt (hF : Nat.card F = 2)
    (X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) (hXY : X * Y = 1) (hYX : Y * X = 1)
    (hX : Xᵀ * burnsideF4m_J2 * X = burnsideF4m_J2) :
    burnsideF4m_spM (burnsideF4m_spElt hF X Y hXY hYX hX : StatedSp 2 F) =
      (burnsideF4m_zmod2Equiv hF).toRingHom.mapMatrix X := rfl

@[expose] def burnsideF4m_spT1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks !![0, 1; 1, 1] 0 0 !![1, 1; 1, 0]

@[expose] def burnsideF4m_spT2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks !![1, 1; 1, 0] !![1, 0; 0, 1] 0 !![0, 1; 1, 1]

@[expose] def burnsideF4m_spX : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks !![1, 0; 0, 0] !![0, 0; 0, 1] !![0, 0; 0, 1] !![1, 0; 0, 0]

theorem burnsideF4m_sp_witness_facts :
    burnsideF4m_spT1 * (burnsideF4m_spT1 * burnsideF4m_spT1) = 1 ∧
      burnsideF4m_spT1 * burnsideF4m_spT1 * burnsideF4m_spT1 = 1 ∧
      burnsideF4m_spT2 * (burnsideF4m_spT2 * burnsideF4m_spT2) = 1 ∧
      burnsideF4m_spT2 * burnsideF4m_spT2 * burnsideF4m_spT2 = 1 ∧
      burnsideF4m_spX * burnsideF4m_spX = 1 ∧
      burnsideF4m_spT1ᵀ * burnsideF4m_J2 * burnsideF4m_spT1 = burnsideF4m_J2 ∧
      burnsideF4m_spT2ᵀ * burnsideF4m_J2 * burnsideF4m_spT2 = burnsideF4m_J2 ∧
      burnsideF4m_spXᵀ * burnsideF4m_J2 * burnsideF4m_spX = burnsideF4m_J2 ∧
      (∀ i j, (burnsideF4m_spT1 * burnsideF4m_spT2) (Sum.inl i) (Sum.inl j) =
        if i = j then 1 else 0) ∧
      (∀ i j, burnsideF4m_spT1 (Sum.inr i) (Sum.inl j) = 0) ∧
      (∀ i j, (burnsideF4m_spT1 * burnsideF4m_spT1) (Sum.inr i) (Sum.inl j) = 0) ∧
      (∀ i j, burnsideF4m_spT2 (Sum.inr i) (Sum.inl j) = 0) ∧
      (∀ i j, (burnsideF4m_spT2 * burnsideF4m_spT2) (Sum.inr i) (Sum.inl j) = 0) ∧
      (∀ b, b ≠ Sum.inl 0 → burnsideF4m_spX b (Sum.inl 0) = 0) ∧
      Matrix.of (fun i j => burnsideF4m_spT1 (Sum.inl i) (Sum.inl j)) = burnsideF4m_r2 ∧
      Matrix.of (fun i j => (burnsideF4m_spT1 * burnsideF4m_spT1) (Sum.inl i) (Sum.inl j)) =
        burnsideF4m_r2 * burnsideF4m_r2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem burnsideF4m_sp_w_facts :
    let v := burnsideF4m_spT1 * burnsideF4m_spT2
    let w := v * (burnsideF4m_spX * v * burnsideF4m_spX)
    w ≠ 1 ∧ w * w * w = 1 := by
  decide

theorem burnsideF4m_spM_spElt_inv (hF : Nat.card F = 2)
    (X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) (hXY : X * Y = 1) (hYX : Y * X = 1)
    (hX : Xᵀ * burnsideF4m_J2 * X = burnsideF4m_J2) :
    burnsideF4m_spM (burnsideF4m_spElt hF X Y hXY hYX hX : StatedSp 2 F)⁻¹ =
      (burnsideF4m_zmod2Equiv hF).toRingHom.mapMatrix Y := rfl

theorem burnsideF4m_spTL_spElt (hF : Nat.card F = 2) (A : StatedSp 2 F)
    (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))
    (hA : burnsideF4m_spM A = (burnsideF4m_zmod2Equiv hF).toRingHom.mapMatrix X) :
    burnsideF4m_spTL A = (burnsideF4m_zmod2Equiv hF).toRingHom.mapMatrix
      (Matrix.of fun i j => X (Sum.inl i) (Sum.inl j)) := by
  ext i j
  simp only [burnsideF4m_spTL, Matrix.of_apply, hA, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem burnsideF4m_sp_pow_three (hF : Nat.card F = 2) (A : StatedSp 2 F)
    (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))
    (hA : burnsideF4m_spM A = (burnsideF4m_zmod2Equiv hF).toRingHom.mapMatrix X)
    (hX : X * X * X = 1) : A ^ 3 = 1 := by
  refine Subtype.ext (Units.ext ?_)
  change burnsideF4m_spM (A ^ 3) = burnsideF4m_spM 1
  simp only [burnsideF4m_spM, pow_succ, pow_zero, one_mul, Subgroup.coe_mul, Units.val_mul,
    Subgroup.coe_one, Units.val_one]
  simp only [burnsideF4m_spM] at hA
  rw [hA, ← map_mul, ← map_mul, hX, map_one]

theorem burnsideF4m_sp_pCore_le_U1 (hF : Nat.card F = 2) :
    pCoreOf 2 (Q2 F 1) ≤ burnsideF4m_spU1 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  set e := burnsideF4m_zmod2Equiv hF with he
  set E : Matrix (Fin 2) (Fin 2) (ZMod 2) ≃+* Matrix (Fin 2) (Fin 2) F := e.mapMatrix with hE
  have hEe : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 2), E M = e.toRingHom.mapMatrix M := fun M => rfl
  obtain ⟨f1, f2, -, -, -, f6, -, -, -, f10, f11, -, -, -, f15, f16⟩ :=
    burnsideF4m_sp_witness_facts
  set R : StatedSp 2 F := burnsideF4m_spElt hF burnsideF4m_spT1
    (burnsideF4m_spT1 * burnsideF4m_spT1) f1 f2 f6 with hR
  have hRQ : R ∈ Q2 F 1 := by
    refine burnsideF4m_spQ1_of_bl (fun i j => ?_) (fun i j => ?_)
    · rw [hR, burnsideF4m_spM_spElt, RingHom.mapMatrix_apply, Matrix.map_apply, f10, map_zero]
    · rw [hR, burnsideF4m_spM_spElt_inv, RingHom.mapMatrix_apply, Matrix.map_apply, f11,
        map_zero]
  have hρR : burnsideF4m_spTL R = E burnsideF4m_r2 := by
    rw [burnsideF4m_spTL_spElt hF R _ (burnsideF4m_spM_spElt hF _ _ f1 f2 f6), f15, hEe]
  have hρRi : burnsideF4m_spTL R⁻¹ = E (burnsideF4m_r2 * burnsideF4m_r2) := by
    rw [burnsideF4m_spTL_spElt hF R⁻¹ _ (burnsideF4m_spM_spElt_inv hF _ _ f1 f2 f6), f16, hEe]
  have hinv2 : ∀ (A : StatedSp 2 F), A ∈ Q2 F 1 → ∀ k : ℕ, A ^ 2 ^ k = 1 →
      E.symm (burnsideF4m_spTL A) * E.symm (burnsideF4m_spTL A) = 1 := by
    intro A hA k hk
    set τ := E.symm (burnsideF4m_spTL A) with hτ
    have hτk : τ ^ 2 ^ k = 1 := by
      rw [hτ, ← map_pow, ← burnsideF4m_spTL_pow hA, hk, burnsideF4m_spTL_one, map_one]
    have hdet : τ.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hτk
      rw [Matrix.det_pow, h0, zero_pow (pow_ne_zero _ two_ne_zero), Matrix.det_one] at this
      exact zero_ne_one this
    have h1 : orderOf τ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hτk
    have h2 : orderOf τ ∣ 6 := orderOf_dvd_of_pow_eq_one (burnsideF4m_gl2_pow_six τ hdet)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hj1 : j ≤ 1 := by
      by_contra hj2
      rw [hj] at h2
      have h4 : 2 ^ 2 ∣ 6 := (Nat.pow_dvd_pow 2 (by omega : 2 ≤ j)).trans h2
      norm_num at h4
    have h3 : orderOf τ ∣ 2 := by
      rw [hj]
      exact (Nat.pow_dvd_pow 2 hj1).trans (by norm_num)
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  intro v hv
  have hvQ : v ∈ Q2 F 1 := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hv
  refine ⟨hvQ, ?_⟩
  by_contra hne
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Q2 F 1) ⟨v, hv⟩
  have hk' : v ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hRv : R * v * R⁻¹ ∈ pCoreOf 2 (Q2 F 1) := by
    have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Q2 F 1) hRQ
    exact (Subgroup.mem_normalizer_iff.mp hN v).mp hv
  set w := v * (R * v * R⁻¹) with hw
  have hwP : w ∈ pCoreOf 2 (Q2 F 1) := Subgroup.mul_mem _ hv hRv
  have hwQ : w ∈ Q2 F 1 := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hwP
  obtain ⟨k', hk2⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Q2 F 1) ⟨w, hwP⟩
  have hk2' : w ^ 2 ^ k' = 1 := by simpa using congrArg Subtype.val hk2
  set τ := E.symm (burnsideF4m_spTL v) with hτ
  have hτ2 := hinv2 v hvQ k hk'
  have hτ1 : τ ≠ 1 := by
    intro h1
    apply hne
    have := congrArg E h1
    rwa [hτ, RingEquiv.apply_symm_apply, map_one] at this
  obtain ⟨hw3, hw1⟩ := burnsideF4m_gl2_inv_prod τ hτ2 hτ1
  have hρw : E.symm (burnsideF4m_spTL w) =
      τ * (burnsideF4m_r2 * τ * (burnsideF4m_r2 * burnsideF4m_r2)) := by
    have hRvQ : R * v ∈ Q2 F 1 := (Q2 F 1).mul_mem hRQ hvQ
    rw [hw, burnsideF4m_spTL_mul _ ((Q2 F 1).mul_mem hRvQ ((Q2 F 1).inv_mem hRQ)),
      burnsideF4m_spTL_mul _ ((Q2 F 1).inv_mem hRQ), burnsideF4m_spTL_mul _ hvQ, hρR, hρRi]
    apply E.injective
    simp only [RingEquiv.apply_symm_apply, map_mul, hτ]
  have hw2 := hinv2 w hwQ k' hk2'
  rw [hρw] at hw2
  apply hw1
  have h3 : (τ * (burnsideF4m_r2 * τ * (burnsideF4m_r2 * burnsideF4m_r2))) ^ 2 = 1 := by
    rw [pow_two]
    exact hw2
  have h6 := orderOf_dvd_of_pow_eq_one h3
  have h7 := orderOf_dvd_of_pow_eq_one hw3
  have h8 : orderOf (τ * (burnsideF4m_r2 * τ * (burnsideF4m_r2 * burnsideF4m_r2))) = 1 :=
    Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 2 3) h6 h7
  exact orderOf_eq_one_iff.mp h8

theorem burnsideF4m_sp2_V (hF : Nat.card F = 2) :
    pCoreOf 2 (oTwoRes (Q2 F 1)) ≤ Q2 F 0 ∧
      ¬ pCoreOf 2 (oTwoRes (Q2 F 1)) ≤ pCoreOf 2 (Q2 F 0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime (p := 2) (by rw [Fintype.card_eq_nat_card, hF])
  set e := burnsideF4m_zmod2Equiv hF with he
  have hle1 : pCoreOf 2 (oTwoRes (Q2 F 1)) ≤ pCoreOf 2 (Q2 F 1) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (oTwoRes_le _))
      ((le_normalizer_oTwoRes _).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  refine ⟨hle1.trans ((burnsideF4m_sp_pCore_le_U1 hF).trans burnsideF4m_spU1_le_Q0), ?_⟩
  intro hle
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, -, -⟩ :=
    burnsideF4m_sp_witness_facts
  obtain ⟨hw1, hw3⟩ := burnsideF4m_sp_w_facts
  set t₁ : StatedSp 2 F := burnsideF4m_spElt hF burnsideF4m_spT1
    (burnsideF4m_spT1 * burnsideF4m_spT1) f1 f2 f6 with ht₁
  set t₂ : StatedSp 2 F := burnsideF4m_spElt hF burnsideF4m_spT2
    (burnsideF4m_spT2 * burnsideF4m_spT2) f3 f4 f7 with ht₂
  set x : StatedSp 2 F := burnsideF4m_spElt hF burnsideF4m_spX burnsideF4m_spX f5 f5 f8 with hx
  have hm : ∀ (X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) (a b : Fin 2 ⊕ Fin 2),
      X a b = 0 → e.toRingHom.mapMatrix X a b = 0 := by
    intro X Y a b h0
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, h0, map_zero]
  have ht₁Q : t₁ ∈ Q2 F 1 :=
    burnsideF4m_spQ1_of_bl (fun i j => hm _ 0 _ _ (f10 i j)) (fun i j => hm _ 0 _ _ (f11 i j))
  have ht₂Q : t₂ ∈ Q2 F 1 :=
    burnsideF4m_spQ1_of_bl (fun i j => hm _ 0 _ _ (f12 i j)) (fun i j => hm _ 0 _ _ (f13 i j))
  have hxQ : x ∈ Q2 F 0 :=
    CFSG.Quasithin.H13.U4Par.mem_Q2_zero_of_col (fun b hb => hm _ 0 _ _ (f14 b hb))
      (fun b hb => hm _ 0 _ _ (f14 b hb))
  have ht₁3 : t₁ ^ 3 = 1 := burnsideF4m_sp_pow_three hF t₁ _ rfl f2
  have ht₂3 : t₂ ^ 3 = 1 := burnsideF4m_sp_pow_three hF t₂ _ rfl f4
  set v := t₁ * t₂ with hv
  have hvR : v ∈ oTwoRes (Q2 F 1) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure ⟨ht₁Q, 3, by decide, ht₁3⟩)
      (Subgroup.subset_closure ⟨ht₂Q, 3, by decide, ht₂3⟩)
  have hvM : burnsideF4m_spM v = e.toRingHom.mapMatrix (burnsideF4m_spT1 * burnsideF4m_spT2) := by
    simp only [hv, burnsideF4m_spM, Subgroup.coe_mul, Units.val_mul]
    rw [map_mul]
    rfl
  have hvU : v ∈ burnsideF4m_spU1 F := by
    refine ⟨(Q2 F 1).mul_mem ht₁Q ht₂Q, ?_⟩
    rw [burnsideF4m_spTL_spElt hF v _ hvM]
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, f9 i j, Matrix.one_apply]
    split_ifs <;> simp
  have hUV : burnsideF4m_spU1 F ⊓ oTwoRes (Q2 F 1) ≤ pCoreOf 2 (oTwoRes (Q2 F 1)) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      (burnsideF4m_spU1_isPGroup.to_le inf_le_left)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hgQ : g ∈ Q2 F 1 := oTwoRes_le _ hg
    have hN := Subgroup.mem_normalizer_iff.mp (burnsideF4m_spU1_normal hgQ) y
    have hN' := Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes (Q2 F 1) hgQ) y
    exact ⟨fun ⟨h1, h2⟩ => ⟨hN.mp h1, hN'.mp h2⟩, fun ⟨h1, h2⟩ => ⟨hN.mpr h1, hN'.mpr h2⟩⟩
  have hvP : v ∈ pCoreOf 2 (Q2 F 0) := hle (hUV ⟨hvU, hvR⟩)
  have hxv : x * v * x⁻¹ ∈ pCoreOf 2 (Q2 F 0) := by
    have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Q2 F 0) hxQ
    exact (Subgroup.mem_normalizer_iff.mp hN v).mp hvP
  set w := v * (x * v * x⁻¹) with hw
  have hwP : w ∈ pCoreOf 2 (Q2 F 0) := Subgroup.mul_mem _ hvP hxv
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Q2 F 0) ⟨w, hwP⟩
  have hk' : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hwM : burnsideF4m_spM w = e.toRingHom.mapMatrix
      (burnsideF4m_spT1 * burnsideF4m_spT2 *
        (burnsideF4m_spX * (burnsideF4m_spT1 * burnsideF4m_spT2) * burnsideF4m_spX)) := by
    have hxi : burnsideF4m_spM x⁻¹ = e.toRingHom.mapMatrix burnsideF4m_spX := rfl
    have hxm : burnsideF4m_spM x = e.toRingHom.mapMatrix burnsideF4m_spX := rfl
    simp only [hw, burnsideF4m_spM, Subgroup.coe_mul, Units.val_mul] at hvM hxi hxm ⊢
    rw [hvM, hxi, hxm]
    simp only [map_mul]
  have hw3' : w ^ 3 = 1 := burnsideF4m_sp_pow_three hF w _ hwM hw3
  have hord : orderOf w = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
      (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hw3')
  rw [orderOf_eq_one_iff] at hord
  apply hw1
  have := congrArg burnsideF4m_spM hord
  rw [hwM] at this
  apply (RingHom.mapMatrix e.toRingHom).injective
  · rw [this, map_one]
    rfl

end SpTwo

end CFSG.ASVolI
