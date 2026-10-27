module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentConfig
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentQ8Frame
import CFSG.CharacterTheory.Semidihedral.QuaternionAutomorphismLifting
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

theorem not_three_dvd_card_closure_of_quaternion {G : Type*} [Group G] {i j : G}
    (hi4 : i ^ 4 = 1) (hj2 : j ^ 2 = i ^ 2) (hij : i * j = j * i⁻¹) :
    ¬ 3 ∣ Nat.card (Subgroup.closure ({i, j} : Set G)) := by
  set c := CFSG.Semidihedral.QuaternionAutomorphismLifting.coordinatePowerHom 4 i hi4 with hc
  have hcn : ∀ n : ℕ, c (Multiplicative.ofAdd (n : ZMod 4)) = i ^ n := fun n =>
    CFSG.Semidihedral.QuaternionAutomorphismLifting.coordinatePowerHom_natCast 4 i hi4 n
  set φ := CFSG.TwoRankLowerBound.Helpers.quaternionNormalFormHom 2 c j
    (by rw [hcn 2, hj2]) (fun r => by
      have := CFSG.Semidihedral.QuaternionAutomorphismLifting.power_passes_outside i j hij r.val
      change i ^ r.val * j = j * (i ^ r.val)⁻¹ at this
      have hr : c (Multiplicative.ofAdd r) = i ^ r.val := by
        rw [← hcn r.val, ZMod.natCast_zmod_val]
      rw [hr]
      exact this) with hφ
  have hφa : φ (QuaternionGroup.a 1) = i := by
    change c (Multiplicative.ofAdd (1 : ZMod 4)) = i
    rw [show (1 : ZMod 4) = ((1 : ℕ) : ZMod 4) by norm_num, hcn 1, pow_one]
  have hφx : φ (QuaternionGroup.xa 0) = j := by
    change j * c (Multiplicative.ofAdd (0 : ZMod 4)) = j
    rw [show Multiplicative.ofAdd (0 : ZMod 4) = 1 from rfl, map_one, mul_one]
  have hle : Subgroup.closure ({i, j} : Set G) ≤ φ.range := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ⟨_, hφa⟩
    · exact ⟨_, hφx⟩
  have hdvd : Nat.card (Subgroup.closure ({i, j} : Set G)) ∣ 8 := by
    have h1 := Subgroup.card_dvd_of_le hle
    have h2 := Subgroup.card_range_dvd φ
    rw [Nat.card_eq_fintype_card (α := QuaternionGroup 2), QuaternionGroup.card] at h2
    exact dvd_trans h1 h2
  intro h3
  have := dvd_trans h3 hdvd
  norm_num at this

theorem quaternion_relations {G : Type*} [Group G] {i t z : G} (hz : ∀ g, g * z = z * g)
    (hz2 : z * z = 1) (hi : i * i = z) (ht3 : t ^ 3 = 1)
    (hk : i * (t * i * t⁻¹) = t * (t * i * t⁻¹) * t⁻¹) :
    i ^ 4 = 1 ∧ (t * i * t⁻¹) ^ 2 = i ^ 2 ∧ i * (t * i * t⁻¹) = (t * i * t⁻¹) * i⁻¹ := by
  obtain ⟨j, hj⟩ : ∃ j, j = t * i * t⁻¹ := ⟨_, rfl⟩
  rw [← hj] at hk ⊢
  have hjj : j * j = z := by
    calc j * j = t * (i * i) * t⁻¹ := by rw [hj]; group
      _ = z := by rw [hi, mul_assoc, ← hz, mul_inv_cancel_left]
  have ht3' : t * t * t = 1 := by rw [← ht3, pow_succ, pow_two]
  refine ⟨?_, ?_, ?_⟩
  · rw [show i ^ 4 = i ^ 2 * i ^ 2 by rw [← pow_add], pow_two, hi, hz2]
  · rw [pow_two, pow_two, hjj, hi]
  ·
    have h1 : j * (i * j) = i := by
      calc j * (i * j) = j * (t * j * t⁻¹) := by rw [hk]
        _ = t * (i * j) * t⁻¹ := by rw [hj]; group
        _ = t * (t * j * t⁻¹) * t⁻¹ := by rw [hk]
        _ = (t * t * t) * i * (t * t * t)⁻¹ := by rw [hj]; group
        _ = i := by rw [ht3', one_mul, inv_one, mul_one]
    have hjinv : j⁻¹ = z * j := by
      rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hz j, mul_assoc, hjj, hz2]
    have hiinv : i⁻¹ = z * i := by
      rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hz i, mul_assoc, hi, hz2]
    calc i * j = j⁻¹ * (j * (i * j)) := by group
      _ = j⁻¹ * i := by rw [h1]
      _ = z * j * i := by rw [hjinv]
      _ = j * (z * i) := by rw [← hz j]; group
      _ = j * i⁻¹ := by rw [hiinv]

variable {K : Type} [Field K] {p f : ℕ}

theorem diagOne_mul (s t : Kˣ) : diagOne s * diagOne t = (diagOne (s * t) : GL (Fin 2) K) := by
  apply Units.ext
  rw [Units.val_mul, coe_diagOne, coe_diagOne, coe_diagOne, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diagOne_one : diagOne (1 : Kˣ) = (1 : GL (Fin 2) K) := by
  apply Units.ext
  rw [coe_diagOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagOne_pow (t : Kˣ) (n : ℕ) : diagOne t ^ n = (diagOne (t ^ n) : GL (Fin 2) K) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, diagOne_one]
  | succ n ih => rw [pow_succ, ih, diagOne_mul, ← pow_succ]

theorem diagUnits_conj_blockHom (a b c : Kˣ) (B : GL (Fin 2) K) :
    diagUnits a b c * blockHom B * (diagUnits a b c)⁻¹ =
      blockHom (diagOne (c * b⁻¹) * B * (diagOne (c * b⁻¹))⁻¹) := by
  have hdet : GeneralLinearGroup.det (diagOne (c * b⁻¹) * B * (diagOne (c * b⁻¹))⁻¹) =
      GeneralLinearGroup.det B := by
    rw [map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det (diagOne _)), mul_assoc,
      mul_inv_cancel, mul_one]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_blockHom, coe_blockHom, hdet,
    Sec12.KS128Move.diagUnits_inv, coe_diagUnits, coe_diagUnits]
  have hinv : (((diagOne (c * b⁻¹))⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      diagonal ![1, (((c * b⁻¹)⁻¹ : Kˣ) : K)] := rfl
  simp only [Units.val_mul, coe_diagOne, hinv]
  have hb : (b : K) ≠ 0 := b.ne_zero
  have hc : (c : K) ≠ 0 := c.ne_zero
  have ha : (a : K) ≠ 0 := a.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, diagonal,
      Matrix.mul_diagonal, Matrix.diagonal_mul] <;> field_simp

theorem eq_pow_of_pow_three {τ r : Kˣ} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hr : r ^ 3 = 1) :
    ∃ m : ℕ, m < 3 ∧ r = τ ^ m := by
  have hτ' : (τ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hτ, Units.val_one]
  have hr' : (r : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hr, Units.val_one]
  have hsum : (τ : K) ^ 2 + τ + 1 = 0 := by
    have : ((τ : K) - 1) * ((τ : K) ^ 2 + τ + 1) = 0 := by linear_combination hτ'
    exact (mul_eq_zero.mp this).resolve_left
      (sub_ne_zero.mpr fun h => hτ1 (Units.ext (by rw [Units.val_one]; exact h)))
  have hfac : ((r : K) - 1) * ((r : K) - τ) * ((r : K) - τ ^ 2) = 0 := by
    linear_combination hr' + (-(r : K) ^ 2 + r) * hsum + ((r : K) - 1) * hτ'
  rcases mul_eq_zero.mp hfac with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · exact ⟨0, by norm_num, Units.ext (by simpa using sub_eq_zero.mp h1)⟩
    · exact ⟨1, by norm_num, Units.ext (by simpa using sub_eq_zero.mp h2)⟩
  · exact ⟨2, by norm_num, Units.ext (by simpa using sub_eq_zero.mp h3)⟩

theorem eq_of_mk_blockHom_conj {g B : GL (Fin 2) K}
    (h : pmk (blockHom (g * B * g⁻¹)) = pmk (blockHom B)) : g * B * g⁻¹ = B := by
  have hdet : GeneralLinearGroup.det (g * B * g⁻¹) = GeneralLinearGroup.det B := by
    rw [map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det g), mul_assoc,
      mul_inv_cancel, mul_one]
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h00 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hu
  simp only [Units.val_mul, coe_blockHom, hdet, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.mul_diagonal] at h00
  have hu1 : u = 1 := by
    apply Units.ext
    simp only [blockMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h00
    rw [Units.val_one]
    exact (mul_eq_left₀ (Units.ne_zero _)).mp h00
  rw [hu1, map_one, mul_one] at hu
  exact blockHom_injective hu

variable {ι : Type*}

theorem CentConfig.false_of_quaternion (hK : PiField false p f K)
    (hq : ModThree false (p ^ f)) (hq2 : 2 < p ^ f) (hp2 : p ≠ 2)
    {α : ι → MulAut (projImage (slPi false 3 (p ^ f) K))}
    {e₀ : projImage (slPi false 3 (p ^ f) K)} (hc : CentConfig false p f K α e₀) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ))
    (hdiag : ∀ x, ∃ y ∈ glPi false 3 (p ^ f) K, (∃ a b c : Kˣ, y = diagUnits a b c) ∧
      ∀ m, (α x m : ProjGenLinGroup (Fin 3) K) = pmk y * m * (pmk y)⁻¹) : False := by
  have hU := hK.unitary
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set τu := Units.mk0 τ hτ0 with hτu
  have hτu3 : τu ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0, hτ,
    Units.val_one])
  have hτu1 : τu ≠ 1 := fun h => hτ1 (by
    have := congrArg Units.val h
    rwa [hτu, Units.val_mk0, Units.val_one] at this)
  obtain ⟨i₀, hi₀, hii, hk, hne⟩ := exists_quaternion_frame hU hq hp2 hτu3 hτu1
  set t := diagOne τu with ht
  have htG : t ∈ glPi false 2 (p ^ f) K := diagOne_mem_glPi hU hq hτu3
  have ht3 : t ^ 3 = 1 := by rw [ht, diagOne_pow, hτu3, diagOne_one]
  have hconjG : ∀ (m : ℕ) {B : GL (Fin 2) K}, B ∈ glPi false 2 (p ^ f) K →
      t ^ m * B * (t ^ m)⁻¹ ∈ glPi false 2 (p ^ f) K := fun m B hB =>
    mul_mem (mul_mem (pow_mem htG m) hB) (inv_mem (pow_mem htG m))
  obtain ⟨hi4, hj2, hij⟩ := quaternion_relations (z := (-1 : GL (Fin 2) K))
    (fun g => by rw [mul_neg_one, neg_one_mul]) (by rw [neg_one_mul, neg_neg]) hii ht3 hk
  set j₀ := t * i₀ * t⁻¹ with hj₀
  have hj₀G : j₀ ∈ glPi false 2 (p ^ f) K := by simpa using hconjG 1 hi₀
  set ψ : glPi false 2 (p ^ f) K →* projImage (slPi false 3 (p ^ f) K) :=
    (projOf (slPi false 3 (p ^ f) K)).comp ((blockHom.comp (glPi false 2 (p ^ f) K).subtype).codRestrict
      (slPi false 3 (p ^ f) K) fun B => blockHom_mem_slPi hK B.2) with hψ
  have hψc : ∀ B : glPi false 2 (p ^ f) K,
      (ψ B : ProjGenLinGroup (Fin 3) K) = pmk (blockHom (B : GL (Fin 2) K)) := fun B => rfl
  set I := ψ ⟨i₀, hi₀⟩ with hI
  set J := ψ ⟨j₀, hj₀G⟩ with hJ
  have hIJ : I * J = ψ ⟨t * j₀ * t⁻¹, by simpa using hconjG 1 hj₀G⟩ := by
    rw [hI, hJ, ← map_mul]
    congr 1
    exact Subtype.ext (by simp only [Subgroup.coe_mul]; exact hk)
  have hV3 : ¬ 3 ∣ Nat.card (Subgroup.closure ({I, J} : Set (projImage (slPi false 3 (p ^ f) K)))) := by
    refine not_three_dvd_card_closure_of_quaternion ?_ ?_ ?_
    · rw [hI, ← map_pow]
      rw [show (⟨i₀, hi₀⟩ : glPi false 2 (p ^ f) K) ^ 4 = 1 from
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hi4), map_one]
    · rw [hI, hJ, ← map_pow, ← map_pow]
      congr 1
      exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_pow]; exact hj2)
    · rw [hI, hJ, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; exact hij)
  have hact : ∀ x, ∃ m : ℕ, m < 3 ∧ ∀ (B : GL (Fin 2) K) (hB : B ∈ glPi false 2 (p ^ f) K),
      α x (ψ ⟨B, hB⟩) = ψ ⟨t ^ m * B * (t ^ m)⁻¹, hconjG m hB⟩ := by
    intro x
    obtain ⟨y, -, ⟨a, b, c, rfl⟩, hyx⟩ := hdiag x
    obtain ⟨l, hl⟩ := pow_three_mem_scalars hK hq hq2 (hc.pow_three x) hyx
    rw [Sec12.KS128Move.diagUnits_pow, Sec12.KS128Move.scalar_eq_diagUnits,
      Sec12.KS128Move.diagUnits_eq_iff] at hl
    have hcb : (c * b⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, ← hl.2.2, hl.2.1, mul_inv_cancel]
    obtain ⟨m, hm, hmc⟩ := eq_pow_of_pow_three hτu3 hτu1 hcb
    refine ⟨m, hm, fun B hB => Subtype.ext ?_⟩
    rw [hyx, hψc, hψc, ← map_inv, ← map_mul, ← map_mul, diagUnits_conj_blockHom, hmc,
      ← diagOne_pow]
  have hk₀ : t * (t * j₀ * t⁻¹) * t⁻¹ = i₀ := by
    rw [hj₀]
    calc t * (t * (t * i₀ * t⁻¹) * t⁻¹) * t⁻¹ = t ^ 3 * i₀ * (t ^ 3)⁻¹ := by
          rw [pow_succ, pow_two]
          group
      _ = i₀ := by rw [ht3, one_mul, inv_one, mul_one]
  have hmemI : ∀ m < 3, ψ ⟨t ^ m * i₀ * (t ^ m)⁻¹, hconjG m hi₀⟩ ∈
      Subgroup.closure ({I, J} : Set (projImage (slPi false 3 (p ^ f) K))) := by
    intro m hm
    interval_cases m
    · have h0 : ψ ⟨t ^ 0 * i₀ * (t ^ 0)⁻¹, hconjG 0 hi₀⟩ = I := by
        rw [hI]
        congr 1
        exact Subtype.ext (by simp)
      rw [h0]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · have h1 : ψ ⟨t ^ 1 * i₀ * (t ^ 1)⁻¹, hconjG 1 hi₀⟩ = J := by
        rw [hJ]
        congr 1
        exact Subtype.ext (by simp [hj₀])
      rw [h1]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · have h2 : ψ ⟨t ^ 2 * i₀ * (t ^ 2)⁻¹, hconjG 2 hi₀⟩ = I * J := by
        rw [hIJ]
        congr 1
        exact Subtype.ext (by simp only [hj₀, pow_two]; group)
      rw [h2]
      exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hmemJ : ∀ m < 3, ψ ⟨t ^ m * j₀ * (t ^ m)⁻¹, hconjG m hj₀G⟩ ∈
      Subgroup.closure ({I, J} : Set (projImage (slPi false 3 (p ^ f) K))) := by
    intro m hm
    interval_cases m
    · have h0 : ψ ⟨t ^ 0 * j₀ * (t ^ 0)⁻¹, hconjG 0 hj₀G⟩ = J := by
        rw [hJ]
        congr 1
        exact Subtype.ext (by simp)
      rw [h0]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · have h1 : ψ ⟨t ^ 1 * j₀ * (t ^ 1)⁻¹, hconjG 1 hj₀G⟩ = I * J := by
        rw [hIJ]
        congr 1
        exact Subtype.ext (by simp)
      rw [h1]
      exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    · have h2 : ψ ⟨t ^ 2 * j₀ * (t ^ 2)⁻¹, hconjG 2 hj₀G⟩ = I := by
        rw [hI]
        congr 1
        apply Subtype.ext
        change t ^ 2 * j₀ * (t ^ 2)⁻¹ = i₀
        rw [← hk₀, pow_two]
        group
      rw [h2]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hinv : ∀ x, ∀ w ∈ Subgroup.closure ({I, J} : Set (projImage (slPi false 3 (p ^ f) K))),
      α x w ∈ Subgroup.closure ({I, J} : Set (projImage (slPi false 3 (p ^ f) K))) := by
    intro x w hw
    obtain ⟨m, hm, hx⟩ := hact x
    have hle : Subgroup.closure ({I, J} : Set (projImage (slPi false 3 (p ^ f) K))) ≤
        (Subgroup.closure ({I, J} : Set (projImage (slPi false 3 (p ^ f) K)))).comap
          (α x).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl) <;>
        simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
      · rw [hI, hx]
        exact hmemI m hm
      · rw [hJ, hx]
        exact hmemJ m hm
    exact hle hw
  obtain ⟨x₀, hx₀⟩ := hc.conj_e
  have hfix := congrArg Subtype.val
    (hc.hV _ hV3 hinv x₀ I (Subgroup.subset_closure (Set.mem_insert _ _)))
  rw [hx₀, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, he₀, hI,
    hψc, ← map_inv, ← map_mul, ← map_mul, diagTau_eq_diagUnits hτ hτ0,
    diagUnits_conj_blockHom] at hfix
  have hτinv : (1 : Kˣ) * (Units.mk0 τ hτ0 ^ 2)⁻¹ = τu := by
    rw [one_mul, ← hτu, inv_eq_iff_mul_eq_one, ← pow_succ, hτu3]
  rw [hτinv] at hfix
  exact hne (eq_of_mk_blockHom_conj hfix)

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
