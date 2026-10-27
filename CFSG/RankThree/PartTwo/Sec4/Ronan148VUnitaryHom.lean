module

public import CFSG.RankThree.PartTwo.KFacts.K71InnerSU3
import CFSG.RankThree.PartTwo.Sec4.Ronan148VSL2
import CFSG.RankThree.PartTwo.Sec4.Item417ResProofTwo
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.Assembly.LowTwoRank
open CFSG.RankThree.SubgroupLists (leviSU3 blockGL3 coe_blockGL3)
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K]

theorem exists_scalar_of_unitaryProj_eq_one (h : UnitaryFieldData 2 f K) {g : unitarySU 2 f K 3}
    (hg : unitaryProj h 3 g = 1) : ∃ c : Kˣ, h.norm (c : K) = 1 ∧ c ^ 3 = 1 ∧
      (g : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := by
  rw [← MonoidHom.mem_ker, ker_unitaryProj] at hg
  exact hg

theorem unitaryProj_eq_one_of_scalar (h : UnitaryFieldData 2 f K) {g : unitarySU 2 f K 3}
    (hg : (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K) : unitaryProj h 3 g = 1 := by
  rw [← MonoidHom.mem_ker, ker_unitaryProj, unitaryScalars_eq h (by norm_num)]
  exact Subgroup.mem_subgroupOf.mpr hg

@[expose] noncomputable def swap02 : GL (Fin 3) K :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_swap02 :
    ((swap02 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] :=
  rfl

theorem swap02_inv : (swap02 : GL (Fin 3) K)⁻¹ = swap02 := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, coe_swap02, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem swap02_mem_unitaryIsom3 (h : UnitaryFieldData 2 f K) :
    (swap02 : GL (Fin 3) K) ∈ unitaryIsom3 h := by
  have hP : ((swap02 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar =
      ((swap02 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    rw [Matrix.map_apply, coe_swap02]
    fin_cases i <;> fin_cases j <;> simp
  rw [mem_unitaryIsom3, hP, coe_swap02]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_diag_of_homology_unitary (hf : Odd f) (h : UnitaryFieldData 2 f K)
    {Z T : unitarySU 2 f K 3} (hz3 : unitaryProj h 3 Z ^ 3 = 1) (hz1 : unitaryProj h 3 Z ≠ 1)
    (ht2 : unitaryProj h 3 T ^ 2 = 1) (ht1 : unitaryProj h 3 T ≠ 1)
    (hzt : unitaryProj h 3 Z * unitaryProj h 3 T = unitaryProj h 3 T * unitaryProj h 3 Z) :
    ∃ (A : unitaryIsom3 h) (l m : K), l ≠ m ∧
      (((A : GL (Fin 3) K)⁻¹ * (Z : GL (Fin 3) K) * A : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m] := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.finite
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hf1 : 1 ≤ f := h.one_le
  have hK : PiField false 2 f K := ⟨Nat.prime_two, hf1, h.card_eq_sq⟩
  have hq : ModThree false (2 ^ f) := two_pow_mod_three_of_odd hf
  obtain ⟨τ, hτ3, hτ1⟩ := exists_tau hK hq
  have hZH : (Z : GL (Fin 3) K) ∈ glPi false 3 (2 ^ f) K :=
    (mem_glPi_false h).mpr ((mem_unitarySU_iff h).mp Z.2).2
  have hZZ : (Z : GL (Fin 3) K) ∉ zPi false 3 (2 ^ f) K := by
    intro hz
    obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi hK hq hτ3 hτ1 hz
    exact hz1 (unitaryProj_eq_one_of_scalar h ⟨ξ, hξ⟩)
  have hZ3 : (Z : GL (Fin 3) K) ^ 3 ∈ zPi false 3 (2 ^ f) K := by
    obtain ⟨c, hcN, -, hc⟩ := exists_scalar_of_unitaryProj_eq_one h
      (show unitaryProj h 3 (Z ^ 3) = 1 by rw [map_pow]; exact hz3)
    rw [Subgroup.coe_pow] at hc
    rw [hc]
    refine scalar_mem_zPi hK hq hτ3 hτ1 ?_
    rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
    change (c : K) ^ (2 ^ f + 1) = 1
    rw [← h.norm_eq_pow, hcN]
  rcases type123_exhaust hK hq hZH hZZ hZ3 with h1 | ⟨e, he3, he1, ζ, hζ, g, hg, hD⟩ | h3
  · exfalso
    refine Res417Two.false_of_commute_mod_scalars hK hq h2 (Or.inl h1) (s := T) ?_ ?_ ?_
    · obtain ⟨c, -, -, hc⟩ := exists_scalar_of_unitaryProj_eq_one h
        (show unitaryProj h 3 (T * T) = 1 by rw [map_mul, ← pow_two]; exact ht2)
      exact ⟨c, by rw [← hc, Subgroup.coe_mul]⟩
    · exact fun hT => ht1 (unitaryProj_eq_one_of_scalar h hT)
    · obtain ⟨c, -, -, hc⟩ := exists_scalar_of_unitaryProj_eq_one h
        (show unitaryProj h 3 (Z * T * Z⁻¹ * T⁻¹) = 1 by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hzt]; group)
      exact ⟨c, by rw [← hc]; simp⟩
  swap
  · exfalso
    refine Res417Two.false_of_commute_mod_scalars hK hq h2 (Or.inr h3) (s := T) ?_ ?_ ?_
    · obtain ⟨c, -, -, hc⟩ := exists_scalar_of_unitaryProj_eq_one h
        (show unitaryProj h 3 (T * T) = 1 by rw [map_mul, ← pow_two]; exact ht2)
      exact ⟨c, by rw [← hc, Subgroup.coe_mul]⟩
    · exact fun hT => ht1 (unitaryProj_eq_one_of_scalar h hT)
    · obtain ⟨c, -, -, hc⟩ := exists_scalar_of_unitaryProj_eq_one h
        (show unitaryProj h 3 (Z * T * Z⁻¹ * T⁻¹) = 1 by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hzt]; group)
      exact ⟨c, by rw [← hc]; simp⟩
  obtain ⟨ξ, -, rfl⟩ := exists_scalar_of_mem_zPi hK hq hτ3 hτ1 hζ
  have hgU : g ∈ unitaryIsom3 h := by
    rw [mem_unitaryIsom3]
    exact (mem_glPi_false h).mp hg
  refine ⟨⟨g * swap02, mul_mem hgU (swap02_mem_unitaryIsom3 h)⟩, (ξ⁻¹ : Kˣ), (e * ξ⁻¹ : Kˣ),
    ?_, ?_⟩
  · intro hlm
    apply he1
    have := congrArg (fun x : K => x * ξ) hlm
    simp only [Units.val_mul, Units.val_inv_eq_inv_val] at this
    apply Units.ext
    field_simp at this
    rw [Units.val_one]
    exact this.symm
  · set X : GL (Fin 3) K := g * swap02 with hX
    set ζ : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) ξ with hζdef
    have h1 : X⁻¹ * ((Z : GL (Fin 3) K) * ζ) * X = swap02 * diagE e * swap02 := by
      rw [show X⁻¹ * ((Z : GL (Fin 3) K) * ζ) * X =
          swap02⁻¹ * (g⁻¹ * ((Z : GL (Fin 3) K) * ζ) * g) * swap02 by rw [hX]; group, hD,
        swap02_inv]
    have h2 : X⁻¹ * ((Z : GL (Fin 3) K) * ζ) * X = X⁻¹ * (Z : GL (Fin 3) K) * X * ζ := by
      have hc := (commute_scalar ξ X).eq
      calc X⁻¹ * ((Z : GL (Fin 3) K) * ζ) * X = X⁻¹ * (Z : GL (Fin 3) K) * (ζ * X) := by group
        _ = X⁻¹ * (Z : GL (Fin 3) K) * (X * ζ) := by rw [hc]
        _ = X⁻¹ * (Z : GL (Fin 3) K) * X * ζ := by group
    have e1 : X⁻¹ * (Z : GL (Fin 3) K) * X = swap02 * diagE e * swap02 * ζ⁻¹ := by
      rw [← h1, h2, mul_inv_cancel_right]
    rw [e1, hζdef, Units.val_mul, Units.val_mul, Units.val_mul, coe_swap02, coe_diagE,
      ← map_inv, GeneralLinearGroup.coe_scalar, scalar_apply]
    ext i j
    simp only [Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_three, Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;> simp [Units.val_inv_eq_inv_val]

theorem psuConj_unitaryProj (h : UnitaryFieldData 2 f K) (g w : unitarySU 2 f K 3) :
    psuConj h ⟨g, unitarySU_le_unitaryIsom3 (h := h) g.2⟩ (unitaryProj h 3 w) =
      unitaryProj h 3 g * unitaryProj h 3 w * (unitaryProj h 3 g)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  change psuConj h _ (w : unitaryPSU h 3) = ((g * w * g⁻¹ : unitarySU 2 f K 3) : unitaryPSU h 3)
  rw [psuConj_mk]
  congr 1

theorem exists_lift_of_commute (h : UnitaryFieldData 2 f K) {t : unitarySU 2 f K 3} {l m : K}
    (ht : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m])
    {w : unitaryPSU h 3} (hw : w * unitaryProj h 3 t = unitaryProj h 3 t * w) :
    ∃ v : unitarySU 2 f K 3, v ∈ suCentralizer (2 ^ f) (t : GL (Fin 3) K) ∧
      unitaryProj h 3 v = w := by
  have hfix : psuConj h ⟨t, unitarySU_le_unitaryIsom3 (h := h) t.2⟩ w = w := by
    obtain ⟨w', rfl⟩ := unitaryProj_surjective h 3 w
    rw [psuConj_unitaryProj, ← hw, mul_inv_cancel_right]
  obtain ⟨v, hv, hvw⟩ :=
    (mem_map_suCentralizer_iff h (A := ⟨t, unitarySU_le_unitaryIsom3 (h := h) t.2⟩) ht w).mpr hfix
  exact ⟨v, hv, hvw⟩

theorem commutator_mem_leviSU3 (h : UnitaryFieldData 2 f K) {t : unitarySU 2 f K 3} {l m : K}
    (hlm : l ≠ m) (ht : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m])
    {a b : unitarySU 2 f K 3} (ha : a ∈ suCentralizer (2 ^ f) (t : GL (Fin 3) K))
    (hb : b ∈ suCentralizer (2 ^ f) (t : GL (Fin 3) K)) :
    ⁅a, b⁆ ∈ leviSU3 (K := K) (2 ^ f) := by
  have hab : ⁅a, b⁆ ∈ suCentralizer (2 ^ f) (t : GL (Fin 3) K) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  refine mem_leviSU3_of_corner_eq_one h hlm ht hab ?_
  have h1 := map_commutatorElement (suCornerHom hlm ht) ⟨a, ha⟩ ⟨b, hb⟩
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm (suCornerHom hlm ht ⟨a, ha⟩)
    (suCornerHom hlm ht ⟨b, hb⟩))] at h1
  have h2 := congrArg Units.val h1
  rw [coe_suCornerHom, Units.val_one] at h2
  exact h2

theorem exists_su2_conj (h : UnitaryFieldData 2 f K) {t : unitarySU 2 f K 3} {l m : K}
    (hlm : l ≠ m) (ht : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m])
    {x : unitarySU 2 f K 3} (hx : x ∈ suCentralizer (2 ^ f) (t : GL (Fin 3) K))
    (hx3 : unitaryProj h 3 x ^ 3 = 1) :
    ∃ s : StatedSU 2 (2 ^ f) K, s ^ 3 = 1 ∧ ∀ S : StatedSU 2 (2 ^ f) K,
      (x : GL (Fin 3) K) * blockGL3 (S : GL (Fin 2) K) * (x : GL (Fin 3) K)⁻¹ =
        blockGL3 ((s * S * s⁻¹ : StatedSU 2 (2 ^ f) K) : GL (Fin 2) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.finite
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨h02, h12, h20, h21⟩ := entries_eq_zero_of_mem_suCentralizer hlm ht hx
  have ha0 := corner_ne_zero hlm ht hx
  have hdet := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU x.2
  have hu := ((mem_unitarySU_iff h).mp x.2).2
  set X : Matrix (Fin 3) (Fin 3) K := ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hXdef
  set a := X 2 2 with hadef
  rw [det_eq_of_entries_eq_zero ⟨h02, h12, h20, h21⟩] at hdet
  set B₀ : Matrix (Fin 2) (Fin 2) K := !![X 0 0, X 0 1; X 1 0, X 1 1] with hB₀
  have hB₀det : B₀.det * a = 1 := by
    rw [hB₀, Matrix.det_fin_two_of]
    exact hdet
  have hd0 : B₀.det ≠ 0 := left_ne_zero_of_mul_eq_one hB₀det
  set B : GL (Fin 2) K := GeneralLinearGroup.mkOfDetNeZero B₀ hd0 with hBdef
  have hBcoe : (B : Matrix (Fin 2) (Fin 2) K) = B₀ := rfl
  have e := fun i j => congrFun (congrFun hu i) j
  have hq0 : (0 : K) ^ 2 ^ f = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  have hBu : (B₀.map h.bar)ᵀ * B₀ = 1 := by
    ext i j
    have hij := e (Fin.castSucc i) (Fin.castSucc j)
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h.bar_apply, h20, h21, hq0,
        hB₀] at hij ⊢ <;> linear_combination hij
  have haN : h.norm a = 1 := by
    have h22 := e 2 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, h.bar_apply, h02, h12, hq0] at h22
    rw [UnitaryFieldData.norm, h.bar_apply, mul_comm]
    exact h22
  have hdN : h.norm B₀.det = 1 := by
    have h1 : h.norm (B₀.det * a) = 1 := by rw [hB₀det, UnitaryFieldData.norm, map_one, one_mul]
    rw [norm_mul_eq h, haN, mul_one] at h1
    exact h1
  have hdq : B₀.det ^ (2 ^ f + 1) = 1 := by rw [← h.norm_eq_pow, hdN]
  have hf1 : 1 ≤ f := h.one_le
  set ζ : K := B₀.det ^ (2 ^ (f - 1) + 1) with hζdef
  have hζ2 : ζ * ζ = B₀.det := by
    have h3 : 2 ^ f = 2 * 2 ^ (f - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hf1]
    rw [hζdef, ← pow_add]
    have h4 : 2 ^ (f - 1) + 1 + (2 ^ (f - 1) + 1) = (2 ^ f + 1) + 1 := by omega
    rw [h4, pow_succ, hdq, one_mul]
  have hζ0 : ζ ≠ 0 := fun h0 => hd0 (by rw [← hζ2, h0, mul_zero])
  have hζN : h.norm ζ = 1 := by
    rw [hζdef]
    have : ∀ (c : K) (n : ℕ), h.norm (c ^ n) = h.norm c ^ n := by
      intro c n
      induction n with
      | zero => simp [UnitaryFieldData.norm]
      | succ n ih => rw [pow_succ, norm_mul_eq h, ih, pow_succ]
    rw [this, hdN, one_pow]
  set ζu : Kˣ := Units.mk0 ζ hζ0 with hζu
  set s₀ : GL (Fin 2) K := B * GeneralLinearGroup.scalar (Fin 2) ζu⁻¹ with hs₀
  have hs₀coe : (s₀ : Matrix (Fin 2) (Fin 2) K) = ζ⁻¹ • B₀ := by
    rw [hs₀, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, hBcoe,
      ← smul_one_eq_diagonal, mul_smul_comm, mul_one, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hs₀mem : s₀ ∈ StatedSU 2 (2 ^ f) K := by
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · rw [hs₀coe, Matrix.det_smul, Fintype.card_fin, ← hζ2]
      field_simp
    · change ((s₀ : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f))ᵀ *
        (s₀ : Matrix (Fin 2) (Fin 2) K) = 1
      have hmap : ((s₀ : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f)) =
          (ζ⁻¹) ^ 2 ^ f • B₀.map h.bar := by
        rw [hs₀coe]
        ext i j
        simp [h.bar_apply, mul_pow]
      rw [hmap, hs₀coe, transpose_smul, smul_mul_smul_comm, hBu]
      have : (ζ⁻¹) ^ 2 ^ f * ζ⁻¹ = (h.norm ζ)⁻¹ := by
        rw [UnitaryFieldData.norm, h.bar_apply, mul_inv, mul_comm, inv_pow]
      rw [this, hζN, inv_one, one_smul]
  set s : StatedSU 2 (2 ^ f) K := ⟨s₀, hs₀mem⟩ with hsdef
  have ha0' : a ≠ 0 := ha0
  set D : GL (Fin 3) K := GeneralLinearGroup.mkOfDetNeZero (diagonal ![1, 1, a]) (by
    rw [det_diagonal, Fin.prod_univ_three]
    simpa using ha0') with hDdef
  have hDcoe : (D : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, 1, a] := rfl
  have hxBD : (x : GL (Fin 3) K) = blockGL3 B * D := by
    apply Units.ext
    rw [Units.val_mul, coe_blockGL3, hBcoe, hDcoe]
    change X = _
    ext i j
    rw [Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.RankThree.SubgroupLists.leviMat, hB₀, h02, h12, h20, h21, hadef]
  have hDcomm : ∀ C : GL (Fin 2) K, D * blockGL3 C = blockGL3 C * D := by
    intro C
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_blockGL3]
    rw [hDcoe]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [CFSG.RankThree.SubgroupLists.leviMat]
  have hconj : ∀ C : GL (Fin 2) K,
      (x : GL (Fin 3) K) * blockGL3 C * (x : GL (Fin 3) K)⁻¹ = blockGL3 (B * C * B⁻¹) := by
    intro C
    rw [hxBD, map_mul, map_mul, map_inv]
    calc blockGL3 B * D * blockGL3 C * (blockGL3 B * D)⁻¹
        = blockGL3 B * (D * blockGL3 C) * D⁻¹ * (blockGL3 B)⁻¹ := by group
      _ = blockGL3 B * blockGL3 C * (blockGL3 B)⁻¹ := by rw [hDcomm]; group
  have hBs : ∀ C : GL (Fin 2) K, B * C * B⁻¹ = s₀ * C * s₀⁻¹ := by
    intro C
    have hc := (commute_scalar ζu⁻¹ C).eq
    rw [hs₀, _root_.mul_inv_rev]
    calc B * C * B⁻¹ = B * (C * GeneralLinearGroup.scalar (Fin 2) ζu⁻¹ *
          (GeneralLinearGroup.scalar (Fin 2) ζu⁻¹)⁻¹) * B⁻¹ := by group
      _ = B * GeneralLinearGroup.scalar (Fin 2) ζu⁻¹ * C *
          ((GeneralLinearGroup.scalar (Fin 2) ζu⁻¹)⁻¹ * B⁻¹) := by rw [hc]; group
  refine ⟨s, ?_, fun S => ?_⟩
  ·
    obtain ⟨c, -, -, hc⟩ := exists_scalar_of_unitaryProj_eq_one h
      (show unitaryProj h 3 (x ^ 3) = 1 by rw [map_pow]; exact hx3)
    rw [Subgroup.coe_pow, hxBD] at hc
    have hcomm' : Commute (blockGL3 B) D := (hDcomm B).symm
    rw [hcomm'.mul_pow, ← map_pow] at hc
    have hB3 : (B ^ 3 : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) c := by
      apply Units.ext
      have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_blockGL3,
        GeneralLinearGroup.coe_scalar] at h1
      have hD3 : ((D : Matrix (Fin 3) (Fin 3) K)) ^ 3 = diagonal ![1, 1, a ^ 3] := by
        rw [hDcoe, diagonal_pow]
        congr 1
        funext i
        fin_cases i <;> simp
      rw [hD3] at h1
      ext i j
      have hij := congrFun (congrFun h1 (Fin.castSucc i)) (Fin.castSucc j)
      rw [Matrix.mul_diagonal] at hij
      rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar]
      fin_cases i <;> fin_cases j <;>
        simpa [CFSG.RankThree.SubgroupLists.leviMat, scalar_apply, Matrix.diagonal_apply] using hij
    have hs3 : (s₀ ^ 3 : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) (c * ζu⁻¹ ^ 3) := by
      have hc' : Commute B (GeneralLinearGroup.scalar (Fin 2) ζu⁻¹) := commute_scalar _ _
      rw [hs₀, hc'.mul_pow, hB3, ← map_pow, ← map_mul]
    have hdet3 := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU (s ^ 3).2
    change ((s₀ ^ 3 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 at hdet3
    rw [hs3, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Fin.prod_univ_two] at hdet3
    have hlam : ((c * ζu⁻¹ ^ 3 : Kˣ) : K) = 1 := by
      have h5 : (((c * ζu⁻¹ ^ 3 : Kˣ) : K) + 1) ^ 2 = 0 := by
        linear_combination hdet3 + (((c * ζu⁻¹ ^ 3 : Kˣ) : K) + 1) * h2
      have h6 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5
      linear_combination h6 - h2
    apply Subtype.ext
    change (s₀ ^ 3 : GL (Fin 2) K) = 1
    rw [hs3]
    have : c * ζu⁻¹ ^ 3 = 1 := Units.ext (by rw [hlam, Units.val_one])
    rw [this, map_one]
  · rw [hconj, hBs]
    rfl

theorem exists_levi_of_homology_unitary (hf : Odd f)
    (h : UnitaryFieldData 2 f K) {z t : unitaryPSU h 3} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (hzt : z * t = t * z) :
    ∃ L : Subgroup (unitaryPSU h 3),
      (∀ a b : unitaryPSU h 3, a * z = z * a → b * z = z * b → ⁅a, b⁆ ∈ L) ∧
      ∀ x : unitaryPSU h 3, x * z = z * x → x ^ 3 = 1 → ∀ R : Subgroup (unitaryPSU h 3),
        R ≤ L → ¬ 3 ∣ Nat.card R → x ∈ Subgroup.normalizer (R : Set (unitaryPSU h 3)) →
        ∀ r ∈ R, r * x = x * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.finite
  have : CharP K 2 := h.charP
  obtain ⟨Z, rfl⟩ := unitaryProj_surjective h 3 z
  obtain ⟨T, rfl⟩ := unitaryProj_surjective h 3 t
  obtain ⟨A, l, m, hlm, hA⟩ := exists_diag_of_homology_unitary hf h hz3 hz1 ht2 ht1 hzt
  have htmem : (A : GL (Fin 3) K)⁻¹ * Z * A ∈ unitarySU 2 f K 3 := by
    have := conj_mem_unitarySU (h := h) (inv_mem A.2) Z.2
    rwa [inv_inv] at this
  set tS : unitarySU 2 f K 3 := ⟨_, htmem⟩ with htS
  have htS' : ((tS : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m] := hA
  set ψ : MulAut (unitaryPSU h 3) := psuConj h A with hψ
  have hψt : ψ (unitaryProj h 3 tS) = unitaryProj h 3 Z := by
    change psuConj h A (tS : unitaryPSU h 3) = (Z : unitaryPSU h 3)
    rw [psuConj_mk]
    congr 1
    apply Subtype.ext
    rw [coe_suConj]
    change (A : GL (Fin 3) K) * ((A : GL (Fin 3) K)⁻¹ * Z * A) * (A : GL (Fin 3) K)⁻¹ = Z
    group
  have hlift : ∀ w : unitaryPSU h 3, w * unitaryProj h 3 Z = unitaryProj h 3 Z * w →
      ∃ v : unitarySU 2 f K 3, v ∈ suCentralizer (2 ^ f) (tS : GL (Fin 3) K) ∧
        ψ (unitaryProj h 3 v) = w := by
    intro w hw
    have hw' : ψ⁻¹ w * unitaryProj h 3 tS = unitaryProj h 3 tS * ψ⁻¹ w := by
      apply ψ.injective
      rw [map_mul, map_mul, MulAut.apply_inv_self, hψt, hw]
    obtain ⟨v, hv, hvw⟩ := exists_lift_of_commute h htS' hw'
    exact ⟨v, hv, by rw [hvw, MulAut.apply_inv_self]⟩
  set L : Subgroup (unitaryPSU h 3) :=
    ((leviSU3 (K := K) (2 ^ f)).map (unitaryProj h 3)).map ψ.toMonoidHom with hL
  refine ⟨L, fun a b ha hb => ?_, fun x hx hx3 R hRL hR3 hxR => ?_⟩
  · obtain ⟨a', ha', rfl⟩ := hlift a ha
    obtain ⟨b', hb', rfl⟩ := hlift b hb
    rw [← map_commutatorElement, ← map_commutatorElement]
    exact ⟨_, ⟨_, commutator_mem_leviSU3 h hlm htS' ha' hb', rfl⟩, rfl⟩
  obtain ⟨x', hx', rfl⟩ := hlift x hx
  have hx'3 : unitaryProj h 3 x' ^ 3 = 1 := by
    apply ψ.injective
    rw [map_pow, hx3, map_one]
  obtain ⟨s, hs3, hsconj⟩ := exists_su2_conj h hlm htS' hx' hx'3
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  set emb : StatedSU 2 (2 ^ f) K →* unitarySU 2 f K 3 :=
    (blockGL3.comp (StatedSU 2 (2 ^ f) K).subtype).codRestrict (unitarySU 2 f K 3) fun S =>
      CFSG.RankThree.SubgroupLists.map_blockGL3_statedSU_le hq1 ⟨S, S.2, rfl⟩ with hemb
  set Λ : StatedSU 2 (2 ^ f) K →* unitaryPSU h 3 :=
    ψ.toMonoidHom.comp ((unitaryProj h 3).comp emb) with hΛ
  have hΛapp : ∀ S, Λ S = ψ (unitaryProj h 3 (emb S)) := fun S => rfl
  have hΛinj : Function.Injective Λ := by
    rw [injective_iff_map_eq_one]
    intro S hS
    have h1 : unitaryProj h 3 (emb S) = 1 := ψ.injective (hS.trans (map_one ψ).symm)
    obtain ⟨c, -, -, hc⟩ := exists_scalar_of_unitaryProj_eq_one h h1
    have h2 : blockGL3 (S : GL (Fin 2) K) ∈ StatedScalars (Fin 3) K := ⟨c, hc.symm⟩
    exact Subtype.ext (CFSG.RankThree.SubgroupLists.blockGL3_eq_one_of_scalar h2)
  have hLΛ : L ≤ Λ.range := by
    rintro _ ⟨_, ⟨y, ⟨S, hS, hSy⟩, rfl⟩, rfl⟩
    refine ⟨⟨S, hS⟩, ?_⟩
    have hy : emb ⟨S, hS⟩ = y := Subtype.ext hSy
    rw [hΛapp, hy]
    rfl
  have hΛconj : ∀ S, Λ (s * S * s⁻¹) =
      ψ (unitaryProj h 3 x') * Λ S * (ψ (unitaryProj h 3 x'))⁻¹ := by
    intro S
    have h1 : emb (s * S * s⁻¹) = x' * emb S * x'⁻¹ := Subtype.ext (hsconj S).symm
    rw [hΛapp, hΛapp, h1, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  set R' := R.comap Λ with hR'
  have hcardR' : Nat.card R' = Nat.card R := by
    have h1 : Nat.card (R'.map Λ) = Nat.card R' := Subgroup.card_map_of_injective hΛinj
    rw [Subgroup.map_comap_eq_self (hRL.trans hLΛ)] at h1
    exact h1.symm
  have hsR' : s ∈ Subgroup.normalizer (R' : Set (StatedSU 2 (2 ^ f) K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro S
    change Λ S ∈ R ↔ Λ (s * S * s⁻¹) ∈ R
    rw [hΛconj]
    exact Subgroup.mem_normalizer_iff.mp hxR (Λ S)
  obtain ⟨ι⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two (r := 2) (f := f)
    h.card_eq_sq
  set R'' := R'.comap ι.toMonoidHom with hR''
  have hcardR'' : Nat.card R'' = Nat.card R' := by
    rw [hR'', Subgroup.comap_equiv_eq_map_symm', Subgroup.card_map_of_injective ι.symm.injective]
  have hs''3 : (ι.symm s) ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
  have hsR'' : ι.symm s ∈ Subgroup.normalizer (R'' : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro S
    change ι S ∈ R' ↔ ι (ι.symm s * S * (ι.symm s)⁻¹) ∈ R'
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_normalizer_iff.mp hsR' (ι S)
  have hcomm := commute_of_mem_normalizer hf
    (CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq) hs''3
    (by rw [hcardR'', hcardR']; exact hR3) hsR''
  intro r hr
  obtain ⟨S, rfl⟩ := hLΛ (hRL hr)
  have hS'' : ι.symm S ∈ R'' := by
    change ι (ι.symm S) ∈ R'
    rw [MulEquiv.apply_symm_apply]
    exact hr
  have h1 := hcomm _ hS''
  have h2 : S * s = s * S := by
    have := congrArg ι h1
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  have h3 : s * S * s⁻¹ = S := by rw [← h2, mul_inv_cancel_right]
  have h4 := hΛconj S
  rw [h3] at h4
  calc Λ S * ψ (unitaryProj h 3 x') =
      ψ (unitaryProj h 3 x') * Λ S * (ψ (unitaryProj h 3 x'))⁻¹ * ψ (unitaryProj h 3 x') := by
        rw [← h4]
    _ = ψ (unitaryProj h 3 x') * Λ S := by group

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
