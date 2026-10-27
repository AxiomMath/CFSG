module

public import CFSG.RankThree.SubgroupLists2.OmegaThree
public import CFSG.RankThree.PartOne.LIT.OrthogonalTransport
public import CFSG.RankThree.PartOne.LIT.CongruenceSplit

public section

namespace CFSG.RankThree.PartOne.KFBloom

open Matrix CFSG.RankThree.SubgroupLists CFSG.RankThree.PartOne.LIT
open scoped MatrixGroups

section Adjoint

variable {K : Type*} [Field K]

@[expose] def adMat (a b c d : K) : Matrix (Fin 3) (Fin 3) K :=
  !![a ^ 2, -2 * a * b, -b ^ 2; -a * c, a * d + b * c, b * d; -c ^ 2, 2 * c * d, d ^ 2]

theorem adMat_mul (a b c d a' b' c' d' : K) :
    adMat a b c d * adMat a' b' c' d' =
      adMat (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem adMat_one : adMat (1 : K) 0 0 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adMat]

theorem adMat_orth (a b c d : K) (h : a * d - b * c = 1) :
    (adMat a b c d)ᵀ * !![0, 0, 1; 0, 2, 0; 1, 0, 0] * adMat a b c d =
      !![0, 0, 1; 0, 2, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    first | ring1 | linear_combination (a * d - b * c + 1) * h |
      linear_combination 2 * (a * d - b * c + 1) * h

theorem det_adMat (a b c d : K) (h : a * d - b * c = 1) : (adMat a b c d).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [adMat]
  linear_combination ((a * d - b * c) ^ 2 + (a * d - b * c) + 1) * h

@[expose] def adMatHom : SL(2, K) →* Matrix (Fin 3) (Fin 3) K where
  toFun g := adMat (g 0 0) (g 0 1) (g 1 0) (g 1 1)
  map_one' := by simpa using adMat_one
  map_mul' g g' := by
    rw [adMat_mul]
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def adGL : SL(2, K) →* GL (Fin 3) K := (adMatHom (K := K)).toHomUnits

theorem coe_adGL (g : SL(2, K)) :
    ((adGL g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      adMat (g 0 0) (g 0 1) (g 1 0) (g 1 1) := rfl

theorem det_sl2 (g : SL(2, K)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := g.2
  rwa [Matrix.det_fin_two] at this

@[expose] def negOne : SL(2, K) := ⟨-1, by rw [Matrix.det_neg]; simp⟩

theorem sl2_eq_of_entries {g h : SL(2, K)} (h00 : g 0 0 = h 0 0) (h01 : g 0 1 = h 0 1)
    (h10 : g 1 0 = h 1 0) (h11 : g 1 1 = h 1 1) : g = h := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem ker_adGL_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ((adGL (K := ZMod p)).ker : Set SL(2, ZMod p)) = {1, negOne} := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have hm := congrArg (fun x : GL (Fin 3) (ZMod p) => (x : Matrix (Fin 3) (Fin 3) (ZMod p))) h
    simp only [coe_adGL, Units.val_one] at hm
    have e00 := congrFun (congrFun hm 0) 0
    have e02 := congrFun (congrFun hm 0) 2
    have e20 := congrFun (congrFun hm 2) 0
    have e22 := congrFun (congrFun hm 2) 2
    simp [adMat] at e00 e02 e20 e22
    have hdet := det_sl2 g
    rw [e02, e20] at hdet
    have had : g 0 0 * g 1 1 = 1 := by linear_combination hdet
    rcases e00 with ha | ha <;> rcases e22 with hd | hd
    · left
      exact sl2_eq_of_entries (by simp [ha]) (by simp [e02]) (by simp [e20]) (by simp [hd])
    · exfalso
      rw [ha, hd] at had
      apply h2
      linear_combination -had
    · exfalso
      rw [ha, hd] at had
      apply h2
      linear_combination -had
    · right
      exact sl2_eq_of_entries (by simp [negOne, ha]) (by simp [negOne, e02]; ring)
        (by simp [negOne, e20]; ring) (by simp [negOne, hd])
  · rintro (rfl | rfl)
    · exact map_one _
    · apply Units.ext
      rw [coe_adGL]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [negOne, adMat] <;> ring

end Adjoint

theorem adGL_mem_soGL {p : ℕ} [Fact p.Prime] (g : SL(2, ZMod p)) :
    adGL g ∈ soGL (splitForm p) := by
  rw [mem_soGL, coe_adGL]
  exact ⟨adMat_orth _ _ _ _ (det_sl2 g), det_adMat _ _ _ _ (det_sl2 g)⟩

theorem commutator_mem_of_index_eq_two' {G : Type*} [Group G] {H : Subgroup G}
    (hH : H.index = 2) (a b : G) : a * b * a⁻¹ * b⁻¹ ∈ H := by
  have h := fun x y : G => Subgroup.mul_mem_iff_of_index_two hH (a := x) (b := y)
  rw [h, h, h, inv_mem_iff, inv_mem_iff]
  tauto

theorem card_sl2_zmod (p : ℕ) [hp : Fact p.Prime] :
    Nat.card SL(2, ZMod p) = p * (p ^ 2 - 1) := by
  have hq : 1 < p := hp.out.one_lt
  have := Fintype.ofFinite (ZMod p)
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    ZMod.card, show p ^ 2 - p = p * (p - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem isPerfect_sl2_zmod {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    Group.IsPerfect SL(2, ZMod p) := by
  have hpr : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  refine ⟨Matrix.SL2.commutator_eq_top (a := (2 : ZMod p)) ?_ ?_⟩
  · intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp this)
  · intro h
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      have : (2 : ZMod p) ^ 2 = 1 := h
      push_cast
      linear_combination this
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_three).mp h3
    omega

theorem splitForm_transpose_eq (p : ℕ) : (splitForm p)ᵀ = splitForm p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [splitForm]

theorem splitForm_det_ne_zero_of_ne_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (splitForm p).det ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  rw [Matrix.det_fin_three]
  simp [splitForm]
  intro h
  first | exact h2 h | exact h2 (by linear_combination -h)

theorem omegaGL_splitForm_eq_range {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    omegaGL (splitForm p) = (adGL (K := ZMod p)).range := by
  have hpr : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hSL := card_sl2_zmod p
  have hcard : Nat.card (soGL (splitForm p)) = p * (p ^ 2 - 1) :=
    card_soGL_three hp2 (splitForm_transpose_eq p) (splitForm_det_ne_zero_of_ne_two hp2)
  set R := (adGL (K := ZMod p)).range with hR
  have hRle : R ≤ soGL (splitForm p) := by
    rintro _ ⟨g, rfl⟩
    exact adGL_mem_soGL g
  have hker : Nat.card (adGL (K := ZMod p)).ker = 2 := by
    have h1 : Nat.card (adGL (K := ZMod p)).ker =
        Set.ncard ((adGL (K := ZMod p)).ker : Set SL(2, ZMod p)) := Nat.card_coe_set_eq _
    have hne : (1 : SL(2, ZMod p)) ≠ negOne := by
      intro h
      have h2 := congrArg (fun g : SL(2, ZMod p) => (g 0 0)) h
      simp only [negOne, Matrix.SpecialLinearGroup.coe_one] at h2
      have h3 : (2 : ZMod p) = 0 := by
        simp at h2
        linear_combination h2
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp this)
    rw [h1, ker_adGL_eq hp2, Set.ncard_pair hne]
  have hRcard : Nat.card R * 2 = p * (p ^ 2 - 1) := by
    have h1 := (adGL (K := ZMod p)).ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (adGL (K := ZMod p))).toEquiv,
      hker, hSL] at h1
    exact h1.symm
  have hidx : (R.subgroupOf (soGL (splitForm p))).index = 2 := by
    have h := Subgroup.card_mul_index (R.subgroupOf (soGL (splitForm p)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv, hcard] at h
    have hpos : 0 < Nat.card R := Nat.card_pos
    have : Nat.card R * (R.subgroupOf (soGL (splitForm p))).index = Nat.card R * 2 := by
      rw [h, hRcard]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have : Group.IsPerfect SL(2, ZMod p) := isPerfect_sl2_zmod hp
  have hRperf : Group.IsPerfect R := Group.IsPerfect.range (adGL (K := ZMod p))
  apply le_antisymm
  · rw [omegaGL, Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    have h := commutator_mem_of_index_eq_two' hidx ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    rw [Subgroup.mem_subgroupOf] at h
    rw [commutatorElement_def]
    simpa using h
  · rw [← Subgroup.commutator_eq_self (H := R)]
    exact Subgroup.commutator_mono hRle hRle

theorem omegaGL_isPerfect {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (M : Matrix (Fin 3) (Fin 3) (ZMod p)) (hM : Mᵀ = M) (hdet : M.det ≠ 0) :
    Group.IsPerfect (omegaGL M) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨g, c, hc, hg⟩ := exists_congr_splitForm hp2 M hM hdet
  have h1 := omegaGL_congr g M
  rw [hg, omegaGL_smul _ hc, omegaGL_splitForm_eq_range hp] at h1
  have h2 : omegaGL M = (adGL (K := ZMod p)).range.map (MulAut.conj g : GL (Fin 3) (ZMod p) →*
      GL (Fin 3) (ZMod p)) := by
    rw [h1, Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective]
  have : Group.IsPerfect SL(2, ZMod p) := isPerfect_sl2_zmod hp
  have : Group.IsPerfect (adGL (K := ZMod p)).range := Group.IsPerfect.range _
  rw [h2]
  exact Group.IsPerfect.map _

end CFSG.RankThree.PartOne.KFBloom
