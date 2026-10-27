module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofCover

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Five

namespace U43Q8

open CFSG.RankThree.PartTwo.Sec4.Item434RemU43 CFSG.LieType.Multipliers.U43 Matrix
open CFSG.RankThree.PartTwo.Sec6.Res611Res4.U43 (rtProdL rtProd_eq toMat_conj_eq)

@[expose] def q8Codes : List (List ℕ) :=
  [[3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 8, 8, 0, 0, 4, 8],
    [3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 7, 5, 0, 0, 7, 7],
    [3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3],
    [3, 0, 0, 0, 0, 0, 5, 8, 0, 8, 6, 2, 0, 5, 1, 6],
    [3, 0, 0, 0, 0, 0, 8, 7, 0, 5, 6, 2, 0, 4, 1, 6],
    [3, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0],
    [3, 0, 0, 0, 0, 0, 4, 5, 0, 7, 6, 2, 0, 8, 1, 6],
    [3, 0, 0, 0, 0, 0, 7, 4, 0, 4, 6, 2, 0, 7, 1, 6]]

@[expose] def u1Code : List ℕ := [3, 0, 0, 0, 0, 4, 6, 1, 0, 3, 4, 3, 0, 1, 6, 4]

@[expose] def u2Code : List ℕ := [4, 0, 6, 2, 0, 3, 0, 0, 3, 0, 4, 6, 2, 0, 3, 4]

@[expose] def q0Code : List ℕ := [3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 8, 8, 0, 0, 4, 8]

theorem rtProdL_u1 : rtProdL 41 = u1Code := by decide +kernel

theorem rtProdL_u2 : rtProdL 49 = u2Code := by decide +kernel

theorem q8_mul : ∀ a ∈ q8Codes, ∀ b ∈ q8Codes, mul4 a b ∈ q8Codes := by decide +kernel

theorem q8_one : one4 ∈ q8Codes := by decide +kernel

theorem q8_pow4 : ∀ a ∈ q8Codes, mul4 (mul4 (mul4 a a) a) a = one4 := by decide +kernel

theorem q8_conj_u1 : ∀ a ∈ q8Codes, mul4 (mul4 u1Code a) (adj4 u1Code) ∈ q8Codes ∧
    mul4 (mul4 (mul4 u1Code a) (adj4 u1Code)) u1Code = mul4 u1Code a := by decide +kernel

theorem q8_conj_u2 : ∀ a ∈ q8Codes, mul4 a u2Code = mul4 u2Code a := by decide +kernel

theorem q0_mem : q0Code ∈ q8Codes := by decide +kernel

theorem det_q0 : (dec4 q0Code).det = 1 := by decide +kernel

theorem unitary_q0 : ((dec4 q0Code).map (· ^ 3))ᵀ * dec4 q0Code = 1 := by decide +kernel

theorem q0_adj : mul4 q0Code (adj4 q0Code) = one4 := by decide +kernel

theorem u2_not_pow : u2Code ≠ one4 ∧ u2Code ≠ u1Code ∧ u2Code ≠ mul4 u1Code u1Code := by
  decide +kernel

theorem u_ne_one : u1Code ≠ one4 ∧ u2Code ≠ one4 := by decide +kernel

theorem u_canon : canon4 u1Code = true ∧ canon4 u2Code = true := by decide +kernel

theorem comm_code_vals :
    (mul4 (mul4 (mul4 u1Code q0Code) (adj4 u1Code)) (adj4 q0Code)).getD 0 0 = 3 ∧
      (mul4 (mul4 (mul4 u1Code q0Code) (adj4 u1Code)) (adj4 q0Code)).getD 5 0 = 0 := by
  decide +kernel

@[expose] noncomputable def q8Sub : Subgroup SUg where
  carrier := {g | ∃ c ∈ q8Codes, toMat g = dec4 c}
  one_mem' := ⟨one4, q8_one, by rw [map_one, dec4_one4]⟩
  mul_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨c', hc', hb⟩
    exact ⟨mul4 c c', q8_mul c hc c' hc', by rw [map_mul, ha, hb, dec4_mul4]⟩
  inv_mem' := by
    rintro a ⟨c, hc, ha⟩
    have h4 : a ^ 4 = 1 := by
      apply toMat_injective
      rw [map_pow, ha, map_one, pow_succ, pow_succ, pow_succ, pow_one, ← dec4_mul4,
        ← dec4_mul4, ← dec4_mul4, q8_pow4 c hc, dec4_one4]
    have hinv : a⁻¹ = a ^ 3 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h4)
    refine ⟨mul4 (mul4 c c) c, q8_mul _ (q8_mul c hc c hc) c hc, ?_⟩
    rw [hinv, map_pow, ha, pow_succ, pow_succ, pow_one, ← dec4_mul4, ← dec4_mul4]

theorem pow_four_of_mem_q8Sub {a : SUg} (ha : a ∈ q8Sub) : a ^ 4 = 1 := by
  obtain ⟨c, hc, ha⟩ := ha
  apply toMat_injective
  rw [map_pow, ha, map_one, pow_succ, pow_succ, pow_succ, pow_one, ← dec4_mul4,
    ← dec4_mul4, ← dec4_mul4, q8_pow4 c hc, dec4_one4]

theorem isPGroup_q8Sub : IsPGroup 2 q8Sub := fun g =>
  ⟨2, Subtype.ext (by simpa using pow_four_of_mem_q8Sub g.2)⟩

@[expose] noncomputable def q0 : SUg := suOfMat (dec4 q0Code) det_q0 unitary_q0

theorem toMat_q0 : toMat q0 = dec4 q0Code := coe_suOfMat _ det_q0 unitary_q0

theorem q0_mem_q8Sub : q0 ∈ q8Sub := ⟨q0Code, q0_mem, toMat_q0⟩

theorem toMat_q0_inv : toMat q0⁻¹ = dec4 (adj4 q0Code) := by
  have h1 : toMat q0 * dec4 (adj4 q0Code) = 1 := by
    rw [toMat_q0, ← dec4_mul4, q0_adj, dec4_one4]
  calc toMat q0⁻¹ = toMat q0⁻¹ * (toMat q0 * dec4 (adj4 q0Code)) := by rw [h1, mul_one]
    _ = toMat (q0⁻¹ * q0) * dec4 (adj4 q0Code) := by rw [map_mul, mul_assoc]
    _ = dec4 (adj4 q0Code) := by rw [inv_mul_cancel, map_one, one_mul]

@[expose] noncomputable def u1 : SUg := prodX 41

@[expose] noncomputable def u2 : SUg := prodX 49

theorem toMat_u1 : toMat u1 = dec4 u1Code := by
  rw [u1, toMat_prodX uSylCheck_true (uClassCheck_parts uClassCheck_true).1, rtProd_eq,
    rtProdL_u1]

theorem toMat_u2 : toMat u2 = dec4 u2Code := by
  rw [u2, toMat_prodX uSylCheck_true (uClassCheck_parts uClassCheck_true).1, rtProd_eq,
    rtProdL_u2]

theorem u1_mem_normalizer : u1 ∈ Subgroup.normalizer (q8Sub : Set SUg) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨c, hc, hn⟩ := hn
  exact ⟨_, (q8_conj_u1 c hc).1, toMat_conj_eq toMat_u1 hn (q8_conj_u1 c hc).2⟩

theorem u2_mem_normalizer : u2 ∈ Subgroup.normalizer (q8Sub : Set SUg) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨c, hc, hn⟩ := hn
  exact ⟨c, hc, toMat_conj_eq toMat_u2 hn (q8_conj_u2 c hc)⟩

@[expose] noncomputable def e9Sub : Subgroup SUg := Subgroup.zpowers u1 ⊔ Subgroup.zpowers u2

theorem e9Sub_le_rtS : e9Sub ≤ rtS :=
  sup_le (Subgroup.zpowers_le.mpr (prodX_mem 41)) (Subgroup.zpowers_le.mpr (prodX_mem 49))

theorem card_e9Sub : Nat.card e9Sub = 9 := by
  have hsyl := uSylCheck_true
  have hrt := (uClassCheck_parts uClassCheck_true).1
  have hRe := rtS_isElemAbelian hsyl hrt
  have hne : ∀ {g : SUg} {c : List ℕ}, toMat g = dec4 c → canon4 c = true → c ≠ one4 →
      g ≠ 1 := by
    intro g c hgc hc hc1 h
    apply hc1
    refine dec4_injective hc canon4_one4 ?_
    rw [← hgc, h, map_one, dec4_one4]
  have hu1 : orderOf u1 = 3 :=
    orderOf_eq_prime (hRe.2 _ (prodX_mem 41)) (hne toMat_u1 u_canon.1 u_ne_one.1)
  have hu2 : orderOf u2 = 3 :=
    orderOf_eq_prime (hRe.2 _ (prodX_mem 49)) (hne toMat_u2 u_canon.2 u_ne_one.2)
  have hcomm : ∀ a ∈ Subgroup.zpowers u1, ∀ b ∈ Subgroup.zpowers u2, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hRe.1.is_comm.comm
      ⟨a, (Subgroup.zpowers_le.mpr (prodX_mem 41)) ha⟩
      ⟨b, (Subgroup.zpowers_le.mpr (prodX_mem 49)) hb⟩)
  have hnot : u2 ∉ Subgroup.zpowers u1 := by
    intro h
    rw [← mem_powers_iff_mem_zpowers] at h
    obtain ⟨n, hn⟩ := h
    have hn : u1 ^ n = u2 := hn
    rw [← pow_mod_orderOf, hu1] at hn
    have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hmat : toMat (u1 ^ (n % 3)) = dec4 u2Code := by rw [hn, toMat_u2]
    interval_cases h : n % 3
    · rw [pow_zero, map_one, ← dec4_one4] at hmat
      exact u2_not_pow.1 (dec4_injective u_canon.2 canon4_one4 hmat.symm)
    · rw [pow_one, toMat_u1] at hmat
      exact u2_not_pow.2.1 (dec4_injective u_canon.2 u_canon.1 hmat.symm)
    · rw [pow_two, map_mul, toMat_u1, ← dec4_mul4] at hmat
      exact u2_not_pow.2.2 (dec4_injective u_canon.2 (canon4_mul4 _ _) hmat.symm)
  rw [e9Sub, card_sup_zpowers_eq_three_mul hu2 hnot hcomm, Nat.card_zpowers, hu1]

theorem e81_data_UX : ∃ P E₀ T₀ : Subgroup UX, CFSG.Assembly.IsElemAbelian 3 P ∧
    Nat.card P = 3 ^ 4 ∧ E₀ ≤ P ∧ Nat.card E₀ = 9 ∧ IsPGroup 2 T₀ ∧
    E₀ ≤ Subgroup.normalizer (T₀ : Set UX) ∧ ¬ T₀ ≤ Subgroup.centralizer (E₀ : Set UX) := by
  have hsyl := uSylCheck_true
  have hrt := (uClassCheck_parts uClassCheck_true).1
  obtain ⟨d₀, -⟩ : ∃ d₀ : Sec6.Res611Res4.U43.Data, True :=
    ⟨Sec6.Res611Res4.U43.data hsyl hrt, trivial⟩
  have hRrt : rtS = d₀.R := d₀.eq_R_of_le hsyl (rtS_le_sylS hsyl hrt)
    (fun x hx y hy => congrArg Subtype.val
      ((rtS_isElemAbelian hsyl hrt).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) (card_rtS hsyl hrt)
  refine ⟨rtS.map piU, e9Sub.map piU, q8Sub.map piU,
    Sec6.Res611Res4.isElemAbelian_map piU (rtS_isElemAbelian hsyl hrt), ?_,
    Subgroup.map_mono e9Sub_le_rtS, ?_, isPGroup_q8Sub.map piU, ?_, ?_⟩
  · rw [card_map_piU_of_le hsyl (rtS_le_sylS hsyl hrt), hRrt, d₀.card_R]
    norm_num
  · rw [card_map_piU_of_le hsyl (e9Sub_le_rtS.trans (rtS_le_sylS hsyl hrt)), card_e9Sub]
  · exact (Subgroup.map_mono (sup_le (Subgroup.zpowers_le.mpr u1_mem_normalizer)
      (Subgroup.zpowers_le.mpr u2_mem_normalizer))).trans (Subgroup.le_normalizer_map piU)
  · intro hle
    have hc := Subgroup.mem_centralizer_iff.mp (hle ⟨q0, q0_mem_q8Sub, rfl⟩) (piU u1)
      ⟨u1, Subgroup.mem_sup_left (Subgroup.mem_zpowers u1), rfl⟩
    have h1 : piU (u1 * q0 * u1⁻¹ * q0⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    obtain ⟨c, hcs⟩ := piU_eq_one_iff.mp h1
    have hk : toMat (u1 * q0 * u1⁻¹ * q0⁻¹) =
        dec4 (mul4 (mul4 (mul4 u1Code q0Code) (adj4 u1Code)) (adj4 q0Code)) := by
      rw [map_mul, toMat_conj_eq toMat_u1 toMat_q0 (q8_conj_u1 q0Code q0_mem).2,
        toMat_q0_inv, ← dec4_mul4]
    have hsc : toMat (u1 * q0 * u1⁻¹ * q0⁻¹) = Matrix.scalar (Fin 4) (c : F9) := by
      rw [toMat_apply, ← hcs]
      rfl
    rw [hk] at hsc
    have h00 := congrFun (congrFun hsc 0) 0
    have h11 := congrFun (congrFun hsc 1) 1
    simp only [dec4, Matrix.of_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00 h11
    rw [show (4 * ((0 : Fin 4) : ℕ) + ((0 : Fin 4) : ℕ)) = 0 by rfl, comm_code_vals.1] at h00
    rw [show (4 * ((1 : Fin 4) : ℕ) + ((1 : Fin 4) : ℕ)) = 5 by rfl, comm_code_vals.2] at h11
    have : uncodeF 3 = uncodeF 0 := h00.trans h11.symm
    exact absurd this (by decide)

end U43Q8

open U43Q8 in
theorem k417E81U43_holds :
    K417E81U43 := by
  obtain ⟨P, E₀, T₀, hP, hP81, hEP, hE9, hT₀, hET, hTE⟩ := e81_data_UX
  exact ⟨_, _, _, e81_data_map Item434RemU43.projSUEquivUX.symm.toMonoidHom
    Item434RemU43.projSUEquivUX.symm.injective hP hP81 hEP hE9 hT₀ hET hTE⟩

end CFSG.RankThree.PartTwo.Sec4.Res417Five
