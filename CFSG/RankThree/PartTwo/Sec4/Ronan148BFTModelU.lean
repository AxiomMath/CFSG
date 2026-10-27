module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BFTTorusU
public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {f : ℕ} {F : Type} [Field F] {hU : UnitaryFieldData 2 f F}

theorem exists_lift_pow_eq_one {x : unitaryPSU hU 3} (hx : Nat.Coprime 3 (orderOf x)) :
    ∃ y : unitarySU 2 f F 3, unitaryProj hU 3 y = x ∧ y ^ orderOf x = 1 := by
  obtain ⟨y₀, rfl⟩ := unitaryProj_surjective hU 3 x
  set m := orderOf (unitaryProj hU 3 y₀) with hm
  have hpm : unitaryProj hU 3 (y₀ ^ m) = 1 := by rw [map_pow]; exact pow_orderOf_eq_one _
  obtain ⟨c, -, hc3, hc⟩ := Ronan148V.exists_scalar_of_unitaryProj_eq_one hU hpm
  have h3m : y₀ ^ (m * 3) = 1 := by
    apply Subtype.ext
    rw [pow_mul, Subgroup.coe_pow, hc, Subgroup.coe_one, ← map_pow, hc3, map_one]
  have := hU.finite
  have hm0 : 0 < m := orderOf_pos_iff.mpr (isOfFinOrder_of_finite _)
  by_cases hm1 : m = 1
  · refine ⟨y₀ ^ 3, ?_, ?_⟩
    · have hx1 : unitaryProj hU 3 y₀ = 1 := by rw [← orderOf_eq_one_iff, ← hm, hm1]
      rw [map_pow, hx1, one_pow]
    · rw [hm1, one_mul] at h3m
      rw [hm1, pow_one]
      exact h3m
  · obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hx (by omega)
    refine ⟨y₀ ^ (3 * a), ?_, ?_⟩
    · rw [map_pow, ← pow_mod_orderOf, ← hm, ha, pow_one]
    · rw [← pow_mul, show 3 * a * m = m * 3 * a by ring, pow_mul, h3m, one_pow]

theorem commute_of_unitaryProj_commute {y w : unitarySU 2 f F 3} {m : ℕ} (hm : Nat.Coprime 3 m)
    (hym : y ^ m = 1)
    (h : unitaryProj hU 3 y * unitaryProj hU 3 w = unitaryProj hU 3 w * unitaryProj hU 3 y) :
    y * w = w * y := by
  obtain ⟨μ, hμ⟩ := exists_scalar_of_unitaryProj_eq (hU := hU) (A := y) (B := w * y * w⁻¹)
    (by rw [map_mul, map_mul, map_inv, ← h, mul_inv_cancel_right])
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hμ
  have hμ3 : μ ^ 3 = 1 := pow_three_eq_one_of_conj_eq_scalar_mul hμ
  have hym' : (y : GL (Fin 3) F) ^ m = 1 := by rw [← Subgroup.coe_pow, hym, Subgroup.coe_one]
  have hμm : μ ^ m = 1 := by
    have e1 : ((w : GL (Fin 3) F) * y * (w : GL (Fin 3) F)⁻¹) ^ m = 1 := by
      rw [conj_pow, hym', mul_one, mul_inv_cancel]
    rw [hμ, ((commute_scalar μ (y : GL (Fin 3) F)).symm).mul_pow, hym', mul_one, ← map_pow] at e1
    have e2 := congrArg (fun g : GL (Fin 3) F => ((g : Matrix (Fin 3) (Fin 3) F) 0 0)) e1
    simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, Units.val_one,
      Matrix.one_apply_eq] at e2
    exact Units.ext e2
  have hμ1 : μ = 1 := by
    have h1 := pow_gcd_eq_one.mpr ⟨hμ3, hμm⟩
    rwa [Nat.Coprime.gcd_eq_one hm, pow_one] at h1
  rw [hμ1, map_one, one_mul] at hμ
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  calc (y : GL (Fin 3) F) * w = (w * y * (w : GL (Fin 3) F)⁻¹) * w := by rw [hμ]
    _ = w * y := by group

theorem exists_eq_scalar_mul_cycThree_pow_diagTau {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {M : GL (Fin 3) F} {ζ₁ ζ₂ : Fˣ}
    (h1 : M * diagTau hτ * M⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ₁ * diagTau hτ)
    (h2 : M * cycThree * M⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ₂ * cycThree) :
    ∃ (k j : ℕ) (μ : Fˣ),
      M = GeneralLinearGroup.scalar (Fin 3) μ * (cycThree ^ k * diagTau hτ ^ j) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  obtain ⟨k, -, -, a, b, e, rfl⟩ := Ronan148V.exists_cycThree_pow_mul_of_conj hτ hτ1 h1
  have hD : diagUnits a b e * cycThree * (diagUnits a b e)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ζ₂ * cycThree := by
    have hck : cycThree ^ k * cycThree = cycThree * (cycThree ^ k : GL (Fin 3) F) := by
      rw [← pow_succ, ← pow_succ']
    have hsc : ∀ (u : Fˣ) (A : GL (Fin 3) F),
        A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
      fun u A => (commute_scalar u A).eq
    calc diagUnits a b e * cycThree * (diagUnits a b e)⁻¹
        = (cycThree ^ k)⁻¹ * ((cycThree ^ k * diagUnits a b e) * cycThree *
            (cycThree ^ k * diagUnits a b e)⁻¹) * cycThree ^ k := by group
      _ = (cycThree ^ k)⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ζ₂ * cycThree) * cycThree ^ k := by
          rw [h2]
      _ = ((cycThree ^ k)⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ₂) *
            (cycThree * cycThree ^ k) := by
          group
      _ = (GeneralLinearGroup.scalar (Fin 3) ζ₂ * (cycThree ^ k)⁻¹) *
            (cycThree ^ k * cycThree) := by
          rw [hsc ζ₂ (cycThree ^ k)⁻¹, ← hck]
      _ = GeneralLinearGroup.scalar (Fin 3) ζ₂ * cycThree := by group
  have hD' : diagUnits a b e = GeneralLinearGroup.scalar (Fin 3) ζ₂ * diagUnits e a b := by
    rw [← cycThree_conj_diagUnits a b e]
    calc diagUnits a b e = (diagUnits a b e * cycThree * (diagUnits a b e)⁻¹) * diagUnits a b e *
          cycThree⁻¹ := by group
      _ = GeneralLinearGroup.scalar (Fin 3) ζ₂ * cycThree * diagUnits a b e * cycThree⁻¹ := by
          rw [hD]
      _ = GeneralLinearGroup.scalar (Fin 3) ζ₂ * (cycThree * diagUnits a b e * cycThree⁻¹) := by
          group
  have hent := fun i => congrFun (congrFun (congrArg (fun g : GL (Fin 3) F =>
    (g : Matrix (Fin 3) (Fin 3) F)) hD') i) i
  have e0 := hent 0
  have e1 := hent 1
  have e2 := hent 2
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_mul,
    coe_diagUnits, diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
  have he0 : (e : F) ≠ 0 := e.ne_zero
  have hζ3 : (ζ₂ : F) ^ 3 = 1 := by
    have : (e : F) = (ζ₂ : F) ^ 3 * e := by
      calc (e : F) = ζ₂ * b := e2
        _ = ζ₂ * (ζ₂ * a) := by rw [e1]
        _ = ζ₂ * (ζ₂ * (ζ₂ * e)) := by rw [e0]
        _ = (ζ₂ : F) ^ 3 * e := by ring
    exact mul_right_cancel₀ he0 (this.symm.trans (one_mul _).symm)
  have hDe : diagUnits a b e = GeneralLinearGroup.scalar (Fin 3) e *
      diagUnits ζ₂ (ζ₂ ^ 2) 1 := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, coe_diagUnits, coe_diagUnits,
      diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [e0, e1, pow_two] <;> ring
  have hτu : Units.mk0 τ hτ0 ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ, Units.val_one])
  obtain ⟨j, hj⟩ : ∃ j : ℕ, diagUnits ζ₂ (ζ₂ ^ 2) 1 = diagTau hτ ^ j := by
    rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hζ3 with h | h | h
    · refine ⟨0, ?_⟩
      have hζ : ζ₂ = 1 := Units.ext h
      rw [hζ, one_pow, pow_zero, diagUnits_one]
    · refine ⟨1, ?_⟩
      have hζ : ζ₂ = Units.mk0 τ hτ0 := Units.ext h
      rw [hζ, pow_one, diagTau_eq_diagUnits hτ hτ0]
    · refine ⟨2, ?_⟩
      have hζ : ζ₂ = Units.mk0 τ hτ0 ^ 2 := Units.ext (by rw [h, Units.val_pow_eq_pow_val,
        Units.val_mk0])
      rw [hζ, diagTau_eq_diagUnits hτ hτ0, pow_two (diagUnits _ _ _), diagUnits_mul,
        mul_one, ← pow_two, ← pow_two, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_add, hτu,
        one_mul, pow_one]
  refine ⟨k, j, e, ?_⟩
  rw [hDe, hj]
  have hsc := (commute_scalar e (cycThree ^ k : GL (Fin 3) F)).eq
  calc cycThree ^ k * (GeneralLinearGroup.scalar (Fin 3) e * diagTau hτ ^ j)
      = (cycThree ^ k * GeneralLinearGroup.scalar (Fin 3) e) * diagTau hτ ^ j := by group
    _ = GeneralLinearGroup.scalar (Fin 3) e * (cycThree ^ k * diagTau hτ ^ j) := by
        rw [hsc]; group

@[expose] noncomputable def swap12 : GL (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_swap12 :
    ((swap12 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] :=
  rfl

theorem swap12_mul_self : (swap12 : GL (Fin 3) F) * swap12 = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_swap12, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem swap12_mul_diagE (e : Fˣ) : (swap12 : GL (Fin 3) F) * diagE e = diagE e * swap12 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_swap12, coe_diagE]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem swap12_mem_unitarySU (hU : UnitaryFieldData 2 f F) :
    (swap12 : GL (Fin 3) F) ∈ unitarySU 2 f F 3 := by
  have : CharP F 2 := hU.charP
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [mem_unitarySU_iff hU]
  have hP : ((swap12 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map hU.bar =
      ((swap12 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    ext i j
    rw [Matrix.map_apply, coe_swap12]
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨?_, ?_⟩
  · rw [coe_swap12, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    linear_combination -h2
  · rw [hP, coe_swap12]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem two_pow_mod_three_of_odd_ftU {m : ℕ} (hm : Odd m) : 2 ^ m % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem exists_frame_of_odd (hf : Odd f) {z : unitaryPSU hU 3} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hodd : ¬ 2 ∣ Nat.card (Subgroup.centralizer ({z} : Set (unitaryPSU hU 3)))) :
    ∃ (τ : F) (hτ : τ ^ 3 = 1) (_hτ1 : τ ≠ 1) (zh : unitarySU 2 f F 3) (g : GL (Fin 3) F),
      unitaryProj hU 3 zh = z ∧ g ∈ unitaryIsom3 hU ∧
        g⁻¹ * (zh : GL (Fin 3) F) * g = diagTau hτ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hU.finite
  have hK : PiField false 2 f F := ⟨Nat.prime_two, hU.one_le, hU.card_eq_sq⟩
  have hq : ModThree false (2 ^ f) := two_pow_mod_three_of_odd_ftU hf
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := exists_tau hK hq
  obtain ⟨zh₀, rfl⟩ := unitaryProj_surjective hU 3 z
  have hZH : (zh₀ : GL (Fin 3) F) ∈ glPi false 3 (2 ^ f) F :=
    (mem_glPi_false hU).mpr ((mem_unitarySU_iff hU).mp zh₀.2).2
  have hZZ : (zh₀ : GL (Fin 3) F) ∉ zPi false 3 (2 ^ f) F := by
    intro hz
    obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi hK hq hτ₀ hτ₀1 hz
    exact hz1 (Ronan148V.unitaryProj_eq_one_of_scalar hU ⟨ξ, hξ⟩)
  have hZ3 : (zh₀ : GL (Fin 3) F) ^ 3 ∈ zPi false 3 (2 ^ f) F := by
    obtain ⟨c, hcN, -, hc⟩ := Ronan148V.exists_scalar_of_unitaryProj_eq_one hU
      (show unitaryProj hU 3 (zh₀ ^ 3) = 1 by rw [map_pow]; exact hz3)
    rw [Subgroup.coe_pow] at hc
    rw [hc]
    refine scalar_mem_zPi hK hq hτ₀ hτ₀1 ?_
    rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
    change (c : F) ^ (2 ^ f + 1) = 1
    rw [← hU.norm_eq_pow, hcN]
  rcases type123_exhaust hK hq hZH hZZ hZ3 with
    ⟨τ, hτ, hτ1, z₁, hz₁, g, hg, hD⟩ | ⟨e, -, he1, ζ, hζ, g, hg, hD⟩ | h3
  ·
    obtain ⟨ξ, hξ, rfl⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz₁
    have hξN : hU.norm (ξ : F) = 1 := by
      rw [hU.norm_eq_pow]
      have h := congrArg Units.val ((mem_rootsOfUnity _ _).mp hξ)
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h
      exact h
    have hξ3 : ξ ^ 3 = 1 := by
      have hd := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F).det) hD
      simp only [Units.val_mul, Matrix.det_mul, det_scalar_three] at hd
      have hdz := ((mem_unitarySU_iff hU).mp zh₀.2).1
      have hgg : ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det *
          (g : Matrix (Fin 3) (Fin 3) F).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
      have hdd : ((diagTau hτ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
        rw [coe_diagTau_eq_diagonal, det_diagonal, Fin.prod_univ_three]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, mul_one]
        linear_combination hτ
      rw [hdz, one_mul, hdd] at hd
      have h1 : (ξ : F) ^ 3 = 1 := by linear_combination hd - (ξ : F) ^ 3 * hgg
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
    have hsc : GeneralLinearGroup.scalar (Fin 3) ξ ∈ unitarySU 2 f F 3 :=
      scalar_mem_unitarySU hU (by norm_num) hξN hξ3
    refine ⟨τ, hτ, hτ1, zh₀ * ⟨_, hsc⟩, g, ?_, (mem_glPi_false hU).mp hg, ?_⟩
    · rw [map_mul, Ronan148V.unitaryProj_eq_one_of_scalar hU (g := ⟨_, hsc⟩) ⟨ξ, rfl⟩, mul_one]
    · rw [Subgroup.coe_mul]
      exact hD
  ·
    exfalso
    obtain ⟨ξ', -, rfl⟩ := exists_scalar_of_mem_zPi hK hq hτ₀ hτ₀1 hζ
    have hgU : g ∈ unitaryIsom3 hU := (mem_glPi_false hU).mp hg
    set t : unitarySU 2 f F 3 := ⟨_, conj_mem_unitarySU hgU (swap12_mem_unitarySU hU)⟩
      with ht
    have hzD : (zh₀ : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) ξ' =
        g * diagE e * g⁻¹ := by
      rw [← hD]; group
    have htz : t * zh₀ = zh₀ * t := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      have hsc := (commute_scalar ξ' (zh₀ : GL (Fin 3) F)).eq
      have hsc' := (commute_scalar ξ' (t : GL (Fin 3) F)).eq
      have key : (t : GL (Fin 3) F) * (zh₀ * GeneralLinearGroup.scalar (Fin 3) ξ') =
          (zh₀ * GeneralLinearGroup.scalar (Fin 3) ξ') * t := by
        rw [hzD]
        change g * swap12 * g⁻¹ * (g * diagE e * g⁻¹) = g * diagE e * g⁻¹ * (g * swap12 * g⁻¹)
        calc g * swap12 * g⁻¹ * (g * diagE e * g⁻¹) = g * (swap12 * diagE e) * g⁻¹ := by group
          _ = g * (diagE e * swap12) * g⁻¹ := by rw [swap12_mul_diagE]
          _ = g * diagE e * g⁻¹ * (g * swap12 * g⁻¹) := by group
      calc (t : GL (Fin 3) F) * zh₀ =
          ((t : GL (Fin 3) F) * (zh₀ * GeneralLinearGroup.scalar (Fin 3) ξ')) *
            (GeneralLinearGroup.scalar (Fin 3) ξ')⁻¹ := by group
        _ = ((zh₀ * GeneralLinearGroup.scalar (Fin 3) ξ') * t) *
            (GeneralLinearGroup.scalar (Fin 3) ξ')⁻¹ := by rw [key]
        _ = zh₀ * (t * GeneralLinearGroup.scalar (Fin 3) ξ') *
            (GeneralLinearGroup.scalar (Fin 3) ξ')⁻¹ := by rw [hsc']; group
        _ = zh₀ * t := by group
    have ht2 : unitaryProj hU 3 t ^ 2 = 1 := by
      rw [← map_pow]
      have : t ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
        change g * swap12 * g⁻¹ * (g * swap12 * g⁻¹) = 1
        calc g * swap12 * g⁻¹ * (g * swap12 * g⁻¹) = g * (swap12 * swap12) * g⁻¹ := by group
          _ = 1 := by rw [swap12_mul_self]; group
      rw [this, map_one]
    have ht1 : unitaryProj hU 3 t ≠ 1 := by
      intro h1
      obtain ⟨c, -, -, hc⟩ := Ronan148V.exists_scalar_of_unitaryProj_eq_one hU h1
      have hsw : (swap12 : GL (Fin 3) F) = GeneralLinearGroup.scalar (Fin 3) c := by
        have : (swap12 : GL (Fin 3) F) = g⁻¹ * (t : GL (Fin 3) F) * g := by
          change swap12 = g⁻¹ * (g * swap12 * g⁻¹) * g
          group
        rw [this, hc, (commute_scalar c g⁻¹).eq]
        group
      have e12 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 1 2) hsw
      simp [coe_swap12, GeneralLinearGroup.coe_scalar] at e12
    have hmem : unitaryProj hU 3 t ∈ Subgroup.centralizer ({unitaryProj hU 3 zh₀} :
        Set (unitaryPSU hU 3)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, htz]
    apply hodd
    have hord : orderOf (unitaryProj hU 3 t) = 2 := orderOf_eq_prime ht2 ht1
    have h2 := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hord] at h2
    exact h2
  ·
    exact absurd ⟨zh₀, zh₀.2, fun m _ => rfl⟩ (not_inner_of_type3 hK hq hZH h3)

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
