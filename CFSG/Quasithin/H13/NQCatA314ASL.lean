module

public import CFSG.Fischer.F4
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open Matrix CFSG.Fischer CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

theorem f4_ext {x y : F4} (h : x.code = y.code) : x = y := by
  cases x
  cases y
  simp_all

theorem f4_eq_one_of_sq {r : F4} (hr : r ^ 2 = 1) : r = 1 := by
  have h : (r - 1) ^ 2 = 0 := by
    rw [sub_sq, hr]
    have h2 : (2 : F4) = 0 := F4.two_eq_zero
    linear_combination (1 - r) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)

theorem card_sl2F4 : Nat.card (SpecialLinearGroup (Fin 2) F4) = 60 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_two, F4.card]

theorem center_sl2F4 : Subgroup.center (SpecialLinearGroup (Fin 2) F4) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, f4_eq_one_of_sq hr, map_one]
  rfl

@[expose] noncomputable def sl2F4EquivPSL :
    SpecialLinearGroup (Fin 2) F4 ≃* ProjectiveSpecialLinearGroup (Fin 2) F4 :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq center_sl2F4.symm)

theorem isSimpleGroup_sl2F4 : IsSimpleGroup (SpecialLinearGroup (Fin 2) F4) := by
  have : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) F4) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_eq_fintype_card, F4.card])
  exact sl2F4EquivPSL.isSimpleGroup

theorem nonabelian_of_simple_card {S : Type} [Group S] [IsSimpleGroup S]
    (h : ¬ (Nat.card S).Prime) : ∃ a b : S, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative S := ⟨⟨hcon⟩⟩
  exact h (Group.is_simple_iff_prime_card.mp inferInstance)

theorem nonabelian_sl2F4 : ∃ a b : SpecialLinearGroup (Fin 2) F4, a * b ≠ b * a := by
  have := isSimpleGroup_sl2F4
  exact nonabelian_of_simple_card (by rw [card_sl2F4]; norm_num)

theorem commutator_sl2F4 : commutator (SpecialLinearGroup (Fin 2) F4) = ⊤ := by
  have hs := isSimpleGroup_sl2F4
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs
    (commutator (SpecialLinearGroup (Fin 2) F4)) inferInstance with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := nonabelian_sl2F4
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator (SpecialLinearGroup (Fin 2) F4) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · exact h

theorem exists_sl2F4_col (v : Fin 2 → F4) (hv : v ≠ 0) :
    ∃ A : SpecialLinearGroup (Fin 2) F4,
      (A : Matrix (Fin 2) (Fin 2) F4).mulVec ![1, 0] = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], ?_⟩, ?_⟩
    · rw [det_fin_two_of]
      field_simp
      ring
    · ext i
      fin_cases i <;> simp [h0, mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], ?_⟩, ?_⟩
    · rw [det_fin_two_of]
      field_simp
      ring
    · ext i
      fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl2F4_mulVec_eq {v w : Fin 2 → F4} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ A : SpecialLinearGroup (Fin 2) F4, (A : Matrix (Fin 2) (Fin 2) F4).mulVec v = w := by
  obtain ⟨B, hB⟩ := exists_sl2F4_col v hv
  obtain ⟨C, hC⟩ := exists_sl2F4_col w hw
  refine ⟨C * B⁻¹, ?_⟩
  rw [← hB, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right, hC]

theorem sl3F4_mul_apply (a b : SpecialLinearGroup (Fin 3) F4) (i j : Fin 3) :
    ((a * b : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) i j =
      ∑ k, (a : Matrix (Fin 3) (Fin 3) F4) i k * (b : Matrix (Fin 3) (Fin 3) F4) k j :=
  rfl

theorem sl3F4_inv_eq (a : SpecialLinearGroup (Fin 3) F4) :
    ((a⁻¹ : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      adjugate (a : Matrix (Fin 3) (Fin 3) F4) :=
  Matrix.SpecialLinearGroup.coe_inv a

@[expose] def K4 : Subgroup (SpecialLinearGroup (Fin 3) F4) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) F4) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) F4) 2 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F4) 2 2 = 1}
  mul_mem' {a b} ha hb := by
    obtain ⟨a1, a2, a3⟩ := ha
    obtain ⟨b1, b2, b3⟩ := hb
    refine ⟨?_, ?_, ?_⟩ <;> rw [sl3F4_mul_apply, Fin.sum_univ_three] <;>
      simp [a1, a2, a3, b1, b2, b3]
  one_mem' := ⟨by simp, by simp, by simp⟩
  inv_mem' {a} ha := by
    obtain ⟨a1, a2, a3⟩ := ha
    have hdet : (a : Matrix (Fin 3) (Fin 3) F4).det = 1 := a.2
    rw [Matrix.det_fin_three, a1, a2, a3] at hdet
    refine ⟨?_, ?_, ?_⟩ <;> rw [sl3F4_inv_eq] <;> simp [adjugate_fin_three, a1, a2]
    linear_combination hdet

@[expose] def Tr4 : Subgroup (SpecialLinearGroup (Fin 3) F4) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) F4) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) F4) 2 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F4) 2 2 = 1 ∧
    (g : Matrix (Fin 3) (Fin 3) F4) 0 0 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) F4) 0 1 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) F4) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F4) 1 1 = 1}
  mul_mem' {a b} ha hb := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ha
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hb
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [sl3F4_mul_apply, Fin.sum_univ_three] <;>
      simp [a1, a2, a3, a4, a5, a6, a7, b1, b2, b3, b4, b5, b6, b7]
  one_mem' := ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  inv_mem' {a} ha := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ha
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [sl3F4_inv_eq] <;>
      simp [adjugate_fin_three, a1, a2, a3, a4, a5, a6, a7]

theorem Tr4_le_K4 : Tr4 ≤ K4 := fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

@[expose] def tau4 (v : Fin 2 → F4) : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![1, 0, v 0; 0, 1, v 1; 0, 0, 1], by rw [Matrix.det_fin_three]; simp⟩

theorem tau4_mem (v : Fin 2 → F4) : tau4 v ∈ Tr4 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tau4_mul (v w : Fin 2 → F4) : tau4 v * tau4 w = tau4 (v + w) := by
  ext i j
  rw [sl3F4_mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [tau4, add_comm]

theorem eq_tau4 {g : SpecialLinearGroup (Fin 3) F4} (hg : g ∈ Tr4) :
    g = tau4 ![(g : Matrix (Fin 3) (Fin 3) F4) 0 2, (g : Matrix (Fin 3) (Fin 3) F4) 1 2] := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hg
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tau4, a1, a2, a3, a4, a5, a6, a7]

theorem tau4_injective : Function.Injective tau4 := by
  intro v w h
  have h0 := congrArg (fun g : SpecialLinearGroup (Fin 3) F4 =>
    (g : Matrix (Fin 3) (Fin 3) F4) 0 2) h
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) F4 =>
    (g : Matrix (Fin 3) (Fin 3) F4) 1 2) h
  simp only [tau4] at h0 h1
  ext i
  fin_cases i
  · exact h0
  · exact h1

@[expose] def blk4 (g : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 2) (Fin 2) F4 :=
  !![(g : Matrix (Fin 3) (Fin 3) F4) 0 0, (g : Matrix (Fin 3) (Fin 3) F4) 0 1;
    (g : Matrix (Fin 3) (Fin 3) F4) 1 0, (g : Matrix (Fin 3) (Fin 3) F4) 1 1]

theorem det_blk4 {g : SpecialLinearGroup (Fin 3) F4} (hg : g ∈ K4) : (blk4 g).det = 1 := by
  obtain ⟨a1, a2, a3⟩ := hg
  have hdet : (g : Matrix (Fin 3) (Fin 3) F4).det = 1 := g.2
  rw [Matrix.det_fin_three, a1, a2, a3] at hdet
  rw [blk4, det_fin_two_of]
  linear_combination hdet

theorem blk4_mul {a b : SpecialLinearGroup (Fin 3) F4} (hb : b ∈ K4) :
    blk4 (a * b) = blk4 a * blk4 b := by
  obtain ⟨b1, b2, -⟩ := hb
  ext i j
  rw [blk4, blk4, blk4, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [sl3F4_mul_apply, Fin.sum_univ_three, b1, b2]

@[expose] noncomputable def alpha4 : ↥K4 →* SpecialLinearGroup (Fin 2) F4 where
  toFun g := ⟨blk4 g, det_blk4 g.2⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk4]
  map_mul' a b := by
    ext i j
    show blk4 ((a : SpecialLinearGroup (Fin 3) F4) * b) i j = (blk4 a * blk4 b) i j
    rw [blk4_mul b.2]

theorem coe_alpha4 (g : ↥K4) :
    ((alpha4 g : SpecialLinearGroup (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4) = blk4 g :=
  rfl

@[expose] def emb4 (A : SpecialLinearGroup (Fin 2) F4) : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) F4) 0 0, (A : Matrix (Fin 2) (Fin 2) F4) 0 1, 0;
      (A : Matrix (Fin 2) (Fin 2) F4) 1 0, (A : Matrix (Fin 2) (Fin 2) F4) 1 1, 0; 0, 0, 1], by
    have h : (A : Matrix (Fin 2) (Fin 2) F4).det = 1 := A.2
    rw [Matrix.det_fin_three]
    rw [Matrix.det_fin_two] at h
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, head_cons, tail_cons, head_fin_const]
    linear_combination h⟩

theorem emb4_mem (A : SpecialLinearGroup (Fin 2) F4) : emb4 A ∈ K4 := ⟨rfl, rfl, rfl⟩

theorem alpha4_emb4 (A : SpecialLinearGroup (Fin 2) F4) : alpha4 ⟨emb4 A, emb4_mem A⟩ = A := by
  ext i j
  rw [coe_alpha4]
  fin_cases i <;> fin_cases j <;> rfl

theorem alpha4_surjective : Function.Surjective alpha4 :=
  fun A => ⟨⟨emb4 A, emb4_mem A⟩, alpha4_emb4 A⟩

theorem ker_alpha4 : alpha4.ker = Tr4.subgroupOf K4 := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨g1, g2, g3⟩ := g.2
  constructor
  · intro h
    have h1 := congrArg (fun A : SpecialLinearGroup (Fin 2) F4 =>
      (A : Matrix (Fin 2) (Fin 2) F4)) h
    simp only [coe_alpha4, Matrix.SpecialLinearGroup.coe_one] at h1
    have e00 := congrFun (congrFun h1 0) 0
    have e01 := congrFun (congrFun h1 0) 1
    have e10 := congrFun (congrFun h1 1) 0
    have e11 := congrFun (congrFun h1 1) 1
    simp [blk4] at e00 e01 e10 e11
    exact ⟨g1, g2, g3, e00, e01, e10, e11⟩
  · rintro ⟨-, -, -, h4, h5, h6, h7⟩
    ext i j
    rw [coe_alpha4]
    fin_cases i <;> fin_cases j <;> simp [blk4, h4, h5, h6, h7]

theorem conj_tau4 {g : SpecialLinearGroup (Fin 3) F4} (hg : g ∈ K4) (v : Fin 2 → F4) :
    g * tau4 v * g⁻¹ = tau4 ((blk4 g).mulVec v) := by
  obtain ⟨g1, g2, g3⟩ := hg
  have h : g * tau4 v = tau4 ((blk4 g).mulVec v) * g := by
    ext i j
    rw [sl3F4_mul_apply, sl3F4_mul_apply, Fin.sum_univ_three, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;>
      simp [tau4, blk4, g1, g2, g3, mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  rw [h, mul_inv_cancel_right]

theorem tau4_zero : tau4 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem add_self_vec (v : Fin 2 → F4) : v + v = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (v i)

theorem tau4_mul_self (v : Fin 2 → F4) : tau4 v * tau4 v = 1 := by
  rw [tau4_mul, add_self_vec, tau4_zero]

theorem mem_Tr4_iff {g : SpecialLinearGroup (Fin 3) F4} : g ∈ Tr4 ↔ ∃ v, g = tau4 v :=
  ⟨fun h => ⟨_, eq_tau4 h⟩, by rintro ⟨v, rfl⟩; exact tau4_mem v⟩

theorem conj_mem_Tr4 {g t : SpecialLinearGroup (Fin 3) F4} (hg : g ∈ K4) (ht : t ∈ Tr4) :
    g * t * g⁻¹ ∈ Tr4 := by
  obtain ⟨v, rfl⟩ := mem_Tr4_iff.mp ht
  rw [conj_tau4 hg]
  exact tau4_mem _

theorem normal_Tr4 : (Tr4.subgroupOf K4).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_Tr4 g.2 hn⟩

theorem isPGroup_Tr4 : IsPGroup 2 (Tr4.subgroupOf K4) := by
  intro x
  refine ⟨1, ?_⟩
  obtain ⟨v, hv⟩ := mem_Tr4_iff.mp (Subgroup.mem_subgroupOf.mp x.2)
  apply Subtype.ext
  apply Subtype.ext
  rw [pow_one, sq]
  show ((x : ↥K4) : SpecialLinearGroup (Fin 3) F4) * (x : ↥K4) = 1
  rw [hv, tau4_mul_self]

theorem pCore_K4 : CFSG.pCore 2 ↥K4 = Tr4.subgroupOf K4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hs := isSimpleGroup_sl2F4
    set P := CFSG.pCore 2 ↥K4 with hP
    have hPn : P.Normal := CFSG.pCore_normal
    have hPp : IsPGroup 2 P := CFSG.pCore_isPGroup
    have hPm : (P.map alpha4).Normal := hPn.map alpha4 alpha4_surjective
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (P.map alpha4) hPm with h | h
    · rw [Subgroup.map_eq_bot_iff, ker_alpha4] at h
      exact h
    · exfalso
      have h2 : IsPGroup 2 (⊤ : Subgroup (SpecialLinearGroup (Fin 2) F4)) := h ▸ hPp.map alpha4
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
      rw [Subgroup.card_top, card_sl2F4] at hn
      have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 60)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  · exact le_sSup ⟨normal_Tr4, isPGroup_Tr4⟩

theorem blockQ_K4 : blockQ K4 = Tr4 := by
  show (Open.pCore 2 ↥K4).map K4.subtype = Tr4
  rw [pCore_K4, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr Tr4_le_K4]

theorem omega_cube : F4.ω * (F4.ω * F4.ω) = 1 := f4_ext (by decide)

@[expose] def d4 : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![F4.ω, 0, 0; 0, F4.ω * F4.ω, 0; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simp [omega_cube]⟩

theorem d4_mem : d4 ∈ K4 := ⟨rfl, rfl, rfl⟩

theorem comm_tau4_d4 (v : Fin 2 → F4) :
    ⁅tau4 ![F4.ω * v 0, F4.ω * F4.ω * v 1], d4⁆ = tau4 v := by
  have e1 : (1 + F4.ω) * F4.ω = 1 := f4_ext (by decide)
  have e2 : (1 + F4.ω * F4.ω) * (F4.ω * F4.ω) = 1 := f4_ext (by decide)
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc d4,
    show (tau4 ![F4.ω * v 0, F4.ω * F4.ω * v 1])⁻¹ = tau4 ![F4.ω * v 0, F4.ω * F4.ω * v 1] from
      inv_eq_of_mul_eq_one_right (tau4_mul_self _),
    conj_tau4 d4_mem, tau4_mul]
  congr 1
  ext i
  fin_cases i
  · simp [d4, blk4]
    linear_combination (v 0) * e1
  · simp [d4, blk4]
    linear_combination (v 1) * e2

theorem blockU_K4 : blockU K4 = Tr4 := by
  show ⁅blockQ K4, K4⁆ = Tr4
  rw [blockQ_K4]
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro t ht g hg
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact Tr4.mul_mem ht (by simpa [mul_assoc] using conj_mem_Tr4 hg (Tr4.inv_mem ht))
  · intro t ht
    obtain ⟨v, rfl⟩ := mem_Tr4_iff.mp ht
    rw [← comm_tau4_d4 v]
    exact Subgroup.commutator_mem_commutator (tau4_mem _) d4_mem

theorem fix_zero {c a : F4} (hc : c + 1 ≠ 0) (h : c * a = a) : a = 0 := by
  have e : (c + 1) * a = 0 := by
    rw [add_mul, h, one_mul]
    exact CharTwo.add_self_eq_zero a
  exact (mul_eq_zero.mp e).resolve_left hc

theorem blockZ_K4 : blockZ K4 = ⊥ := by
  show blockU K4 ⊓ Subgroup.centralizer (K4 : Set (SpecialLinearGroup (Fin 3) F4)) = ⊥
  rw [blockU_K4, eq_bot_iff]
  rintro t ⟨ht, hc⟩
  obtain ⟨v, rfl⟩ := mem_Tr4_iff.mp ht
  have h1 : d4 * tau4 v * d4⁻¹ = tau4 v := by
    rw [Subgroup.mem_centralizer_iff.mp hc d4 d4_mem, mul_inv_cancel_right]
  rw [conj_tau4 d4_mem] at h1
  have h2 := tau4_injective h1
  have e0 := congrFun h2 0
  have e1 := congrFun h2 1
  simp [d4, blk4, mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  have v0 : v 0 = 0 :=
    fix_zero (fun h0 => absurd (congrArg F4.code h0) (by decide)) e0
  have v1 : v 1 = 0 :=
    fix_zero (fun h0 => absurd (congrArg F4.code h0) (by decide)) e1
  rw [Subgroup.mem_bot, show v = 0 by ext i; fin_cases i <;> simp [v0, v1], tau4_zero]

theorem emb4_mul (A B : SpecialLinearGroup (Fin 2) F4) : emb4 (A * B) = emb4 A * emb4 B := by
  ext i j
  rw [sl3F4_mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [emb4, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def emb4Hom : SpecialLinearGroup (Fin 2) F4 →* SpecialLinearGroup (Fin 3) F4 where
  toFun := emb4
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' := emb4_mul

theorem blk4_emb4 (A : SpecialLinearGroup (Fin 2) F4) :
    blk4 (emb4 A) = (A : Matrix (Fin 2) (Fin 2) F4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem mul_emb4_inv_mem (g : ↥K4) :
    (g : SpecialLinearGroup (Fin 3) F4) * (emb4 (alpha4 g))⁻¹ ∈ Tr4 := by
  have h1 : alpha4 (g * (⟨emb4 (alpha4 g), emb4_mem _⟩ : ↥K4)⁻¹) = 1 := by
    rw [map_mul, map_inv, alpha4_emb4, mul_inv_cancel]
  have h2 := ker_alpha4 ▸ (MonoidHom.mem_ker.mpr h1)
  exact Subgroup.mem_subgroupOf.mp h2

theorem commutator_K4 : ⁅K4, K4⁆ = K4 := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact K4.mul_mem (K4.mul_mem (K4.mul_mem hx hy) (K4.inv_mem hx)) (K4.inv_mem hy)
  · intro g hg
    have hT : Tr4 ≤ ⁅K4, K4⁆ := by
      rw [← blockU_K4]
      exact Subgroup.commutator_mono (blockQ_K4 ▸ Tr4_le_K4) le_rfl
    have hE : emb4Hom.range ≤ ⁅K4, K4⁆ := by
      have hr : emb4Hom.range ≤ K4 := by
        rintro _ ⟨A, rfl⟩
        exact emb4_mem A
      have h1 : emb4Hom.range = ⁅emb4Hom.range, emb4Hom.range⁆ := by
        rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
          commutator_sl2F4]
      rw [h1]
      exact Subgroup.commutator_mono hr hr
    have e : g = (g * (emb4 (alpha4 ⟨g, hg⟩))⁻¹) * emb4 (alpha4 ⟨g, hg⟩) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hT (mul_emb4_inv_mem ⟨g, hg⟩)) (hE ⟨_, rfl⟩)

theorem commutator_top_K4 : commutator ↥K4 = ⊤ := by
  apply Subgroup.map_injective K4.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    commutator_K4]

theorem tau4_comm (v w : Fin 2 → F4) : tau4 v * tau4 w = tau4 w * tau4 v := by
  rw [tau4_mul, tau4_mul, add_comm]

theorem charTwo_K4 : CharTwo K4 := by
  show K4 ⊓ Subgroup.centralizer (pCoreOf 2 K4 : Set (SpecialLinearGroup (Fin 3) F4)) ≤
    pCoreOf 2 K4
  rw [show pCoreOf 2 K4 = Tr4 from blockQ_K4]
  rintro g ⟨hg, hc⟩
  have hfix : ∀ v, (blk4 g).mulVec v = v := by
    intro v
    apply tau4_injective
    rw [← conj_tau4 hg, (Subgroup.mem_centralizer_iff.mp hc (tau4 v) (tau4_mem v)).symm,
      mul_inv_cancel_right]
  have h1 : alpha4 ⟨g, hg⟩ = 1 := by
    have e0 := hfix ![1, 0]
    have e1 := hfix ![0, 1]
    have e00 := congrFun e0 0
    have e10 := congrFun e0 1
    have e01 := congrFun e1 0
    have e11 := congrFun e1 1
    simp [blk4, mulVec, dotProduct, Fin.sum_univ_two] at e00 e10 e01 e11
    ext i j
    rw [coe_alpha4, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [blk4, e00, e10, e01, e11]
  have h2 := ker_alpha4 ▸ (MonoidHom.mem_ker.mpr h1)
  exact Subgroup.mem_subgroupOf.mp h2

theorem Tr4_ne_bot : Tr4 ≠ ⊥ := by
  intro h
  have h1 : tau4 ![1, 0] ∈ (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F4)) := h ▸ tau4_mem _
  rw [Subgroup.mem_bot, ← tau4_zero] at h1
  have := congrFun (tau4_injective h1) 0
  exact absurd this (by simp)

theorem irreducible_K4 {W : Subgroup (SpecialLinearGroup (Fin 3) F4)} (hWU : W ≤ Tr4)
    (hN : K4 ≤ Subgroup.normalizer (W : Set (SpecialLinearGroup (Fin 3) F4))) :
    W = ⊥ ∨ W = Tr4 := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  apply le_antisymm hWU
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  obtain ⟨v, hv⟩ := mem_Tr4_iff.mp (hWU t.2)
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact ht1 (Subtype.ext (by rw [hv, tau4_zero]; rfl))
  intro s hs
  obtain ⟨u, rfl⟩ := mem_Tr4_iff.mp hs
  by_cases hu : u = 0
  · rw [hu, tau4_zero]
    exact W.one_mem
  obtain ⟨A, hA⟩ := exists_sl2F4_mulVec_eq hv0 hu
  have h1 := (Subgroup.mem_normalizer_iff.mp (hN (emb4_mem A))
    (t : SpecialLinearGroup (Fin 3) F4)).mp t.2
  rw [hv, conj_tau4 (emb4_mem A), blk4_emb4, hA] at h1
  exact h1

theorem isShort2_K4 : IsShort2 K4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, charTwo_K4, ?_, Or.inl ?_, ?_⟩
  · intro N _ hN
    by_contra hne
    have hQ : Nontrivial (↥K4 ⧸ N) := by
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      apply hne
      rw [eq_top_iff]
      intro g _
      exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
    have hnil : Group.IsNilpotent (↥K4 ⧸ N) := hN.isNilpotent
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥K4 ⧸ N)
    apply hlt.ne
    have h := Subgroup.map_commutator (⊤ : Subgroup ↥K4) (⊤ : Subgroup ↥K4)
      (QuotientGroup.mk' N)
    have h2 : ⁅(⊤ : Subgroup ↥K4), ⊤⁆ = ⊤ := commutator_top_K4
    rw [h2, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h
    exact h.symm
  · rw [blockU_K4, blockQ_K4]
    refine ⟨fun t ht => ⟨ht, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩, ?_⟩
    · obtain ⟨v, rfl⟩ := mem_Tr4_iff.mp ht
      obtain ⟨w, rfl⟩ := mem_Tr4_iff.mp hs
      exact tau4_comm w v
    · intro x hx
      obtain ⟨v, rfl⟩ := mem_Tr4_iff.mp hx
      rw [sq, tau4_mul_self]
  ·
    have := isSimpleGroup_sl2F4
    have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup nonabelian_sl2F4).1
    let f : SpecialLinearGroup (Fin 2) F4 →* ↥K4 ⧸ CFSG.pCore 2 ↥K4 :=
      (QuotientGroup.mk' _).comp (emb4Hom.codRestrict K4 emb4_mem)
    refine CFSG.LocalCores.isQuasisimple_of_surjective hq f ?_ ?_
    · intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ q
      refine ⟨alpha4 g, ?_⟩
      show (QuotientGroup.mk' (CFSG.pCore 2 ↥K4)) (⟨emb4 (alpha4 g), emb4_mem _⟩ : ↥K4) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥K4) g
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, pCore_K4,
        Subgroup.mem_subgroupOf]
      have h1 := conj_mem_Tr4 (K4.inv_mem (emb4_mem (alpha4 g))) (mul_emb4_inv_mem g)
      have e : (emb4 (alpha4 g))⁻¹ * ((g : SpecialLinearGroup (Fin 3) F4) *
          (emb4 (alpha4 g))⁻¹) * (emb4 (alpha4 g))⁻¹⁻¹ =
          (emb4 (alpha4 g))⁻¹ * (g : SpecialLinearGroup (Fin 3) F4) := by group
      rw [e] at h1
      exact h1
    · intro A hA
      rw [MonoidHom.mem_ker] at hA
      have h1 : (⟨emb4 A, emb4_mem A⟩ : ↥K4) ∈ CFSG.pCore 2 ↥K4 :=
        (QuotientGroup.eq_one_iff _).mp hA
      rw [pCore_K4, Subgroup.mem_subgroupOf] at h1
      have h2 : alpha4 ⟨emb4 A, emb4_mem A⟩ = 1 := by
        rw [MonoidHom.mem_ker.mp (ker_alpha4 ▸ Subgroup.mem_subgroupOf.mpr h1)]
      rw [alpha4_emb4] at h2
      rw [h2]
      exact Subgroup.one_mem _
  · rw [blockZ_K4, blockU_K4]
    refine ⟨bot_lt_iff_ne_bot.mpr Tr4_ne_bot, fun W _ hWU hN => ?_⟩
    exact irreducible_K4 hWU hN

theorem isLin2Type_K4 : IsLin2Type K4 2 := by
  have hU := blockU_K4
  have hmem : ∀ u : ↥(blockU K4), (u : SpecialLinearGroup (Fin 3) F4) ∈ Tr4 :=
    fun u => hU ▸ u.2
  let β : ↥(blockU K4) →* Multiplicative (Fin 2 → F4) :=
    { toFun := fun u => Multiplicative.ofAdd ![(u : Matrix (Fin 3) (Fin 3) F4) 0 2,
        (u : Matrix (Fin 3) (Fin 3) F4) 1 2]
      map_one' := by
        apply Multiplicative.toAdd.injective
        ext i
        fin_cases i <;> rfl
      map_mul' := fun u v => by
        obtain ⟨a, ha⟩ := mem_Tr4_iff.mp (hmem u)
        obtain ⟨b, hb⟩ := mem_Tr4_iff.mp (hmem v)
        have huv : ((u * v : ↥(blockU K4)) : SpecialLinearGroup (Fin 3) F4) = tau4 (a + b) := by
          rw [Subgroup.coe_mul, ha, hb, tau4_mul]
        apply Multiplicative.toAdd.injective
        ext i
        fin_cases i
        · show ((u * v : ↥(blockU K4)) : Matrix (Fin 3) (Fin 3) F4) 0 2 =
            (u : Matrix (Fin 3) (Fin 3) F4) 0 2 + (v : Matrix (Fin 3) (Fin 3) F4) 0 2
          rw [huv, ha, hb]
          rfl
        · show ((u * v : ↥(blockU K4)) : Matrix (Fin 3) (Fin 3) F4) 1 2 =
            (u : Matrix (Fin 3) (Fin 3) F4) 1 2 + (v : Matrix (Fin 3) (Fin 3) F4) 1 2
          rw [huv, ha, hb]
          rfl }
  have hβ : ∀ u : ↥(blockU K4), (u : SpecialLinearGroup (Fin 3) F4) =
      tau4 (Multiplicative.toAdd (β u)) := fun u => eq_tau4 (hmem u)
  refine ⟨F4, inferInstance, inferInstance, by rw [F4.card]; norm_num, alpha4, alpha4_surjective,
    by rw [ker_alpha4, pCore_K4], β, ?_, ?_, ?_⟩
  · intro w
    refine ⟨⟨tau4 (Multiplicative.toAdd w), hU ▸ tau4_mem _⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> rfl
  · rw [blockZ_K4, Subgroup.bot_subgroupOf]
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro h
      apply Subtype.ext
      rw [hβ u, h, toAdd_one, tau4_zero]
      rfl
    · rintro rfl
      exact map_one β
  · intro ℓ u v huv
    rw [hβ u, hβ v, Subgroup.coe_inv, conj_tau4 ℓ.2] at huv
    rw [coe_alpha4]
    exact tau4_injective huv

end CFSG.Quasithin.H13.NQCat.A314D
