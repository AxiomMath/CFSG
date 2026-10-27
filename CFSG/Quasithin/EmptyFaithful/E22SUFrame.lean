module

public import CFSG.Quasithin.EmptyFaithful.E22SULift
public import CFSG.Quasithin.EmptyFaithful.E22SFrame

public section

namespace CFSG.Quasithin.E22S

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.SubgroupLists CFSG.Assembly.LowTwoRank CFSG.Open

variable {K : Type} [Field K] {p f : ℕ}

@[expose] def IsDiagU (g x : GL (Fin 3) K) : Prop :=
  ((g * x * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag

@[expose] def dgU (g x : GL (Fin 3) K) (i : Fin 3) : K :=
  ((g * x * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i

theorem conjU_eq_diagonal {g x : GL (Fin 3) K} (h : IsDiagU g x) :
    ((g * x * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal (dgU g x) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hij]
    exact h hij

theorem exists_unitary_frame (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {A : Subgroup (StatedProj (unitarySU p f K 3))} (hA : IsElemAbelian 2 A) :
    ∃ g : GL (Fin 3) K, g ∈ primeFormUnitary hU (idGram K 3) ∧
      ∀ x ∈ invLiftsU A hA, IsDiagU g (x : GL (Fin 3) K) := by
  have hpq : 2 ∣ p ^ f + 1 := by
    have hodd : Odd p := hU.prime.odd_of_ne_two hp2
    exact even_iff_two_dvd.mp ((hodd.pow (n := f)).add_one)
  set G : Subgroup ↥(primeFormUnitary hU (idGram K 3)) :=
    (invLiftsU A hA).map (Subgroup.inclusion (unitarySU_le_primeFormUnitary hU)) with hG
  have hGmem : ∀ y ∈ G, ∃ x ∈ invLiftsU A hA,
      Subgroup.inclusion (unitarySU_le_primeFormUnitary hU) x = y := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, hx, hxy⟩
  have hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := hGmem x hx
    obtain ⟨y₀, hy₀, rfl⟩ := hGmem y hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact commute_of_proj_commute_two_U hx₀.2 (by
      have := hA.1.is_comm.comm ⟨(x₀ : StatedProj (unitarySU p f K 3)), hx₀.1⟩
        ⟨(y₀ : StatedProj (unitarySU p f K 3)), hy₀.1⟩
      exact congrArg Subtype.val this)
  have hpow : ∀ x ∈ G, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hGmem x hx
    rw [← map_pow, hx₀.2, map_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag hU Nat.prime_two hpq G hcomm hpow
  refine ⟨(P : GL (Fin 3) K)⁻¹, (inv_mem P.2), fun x hx => ?_⟩
  have := hP _ (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  simpa [IsDiagU] using this

theorem dgU_mul {g x y : GL (Fin 3) K} (hx : IsDiagU g x) (hy : IsDiagU g y) (i : Fin 3) :
    dgU g (x * y) i = dgU g x i * dgU g y i := by
  have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
  have h1 := conjU_eq_diagonal hx
  have h2 := conjU_eq_diagonal hy
  unfold dgU
  rw [e, Units.val_mul, h1, h2, Matrix.diagonal_mul_diagonal]
  simp only [Matrix.diagonal_apply_eq]

theorem dgU_one (g : GL (Fin 3) K) (i : Fin 3) : dgU g 1 i = 1 := by
  unfold dgU
  simp

theorem dgU_sq {g x : GL (Fin 3) K} (hx : IsDiagU g x) (hx2 : x ^ 2 = 1) (i : Fin 3) :
    dgU g x i * dgU g x i = 1 := by
  rw [← dgU_mul hx hx, ← pow_two, hx2, dgU_one]

theorem dgU_prod {g x : GL (Fin 3) K} (hx : IsDiagU g x)
    (hdet : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1) : ∏ i, dgU g x i = 1 := by
  have h : ((g * x * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [conjU_eq_diagonal hx, Matrix.det_diagonal] at h
  exact h

theorem dgU_inj {g x y : GL (Fin 3) K} (hx : IsDiagU g x) (hy : IsDiagU g y)
    (h : ∀ i, dgU g x i = dgU g y i) : x = y := by
  have : g * x * g⁻¹ = g * y * g⁻¹ := by
    apply Units.ext
    rw [conjU_eq_diagonal hx, conjU_eq_diagonal hy]
    congr 1
    exact funext h
  simpa using this


theorem card_elemAbelian_le_four (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {A : Subgroup (StatedProj (unitarySU p f K 3))} (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 4 := by
  have : Finite K := hU.finite
  obtain ⟨g, -, hg⟩ := exists_unitary_frame hU hp2 hA
  have hsq : ∀ x : invLiftsU A hA, dgU g (x : GL (Fin 3) K) 0 * dgU g (x : GL (Fin 3) K) 0 = 1 ∧
      dgU g (x : GL (Fin 3) K) 1 * dgU g (x : GL (Fin 3) K) 1 = 1 := fun x =>
    ⟨dgU_sq (hg x x.2) (by simpa using congrArg Subtype.val x.2.2) 0,
      dgU_sq (hg x x.2) (by simpa using congrArg Subtype.val x.2.2) 1⟩
  let φ : invLiftsU A hA → {e : K // e = 1 ∨ e = -1} × {e : K // e = 1 ∨ e = -1} := fun x =>
    (⟨dgU g (x : GL (Fin 3) K) 0, mul_self_eq_one_iff.mp (hsq x).1⟩,
      ⟨dgU g (x : GL (Fin 3) K) 1, mul_self_eq_one_iff.mp (hsq x).2⟩)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h0 : dgU g (x : GL (Fin 3) K) 0 = dgU g (y : GL (Fin 3) K) 0 :=
      congrArg Subtype.val (congrArg Prod.fst hxy)
    have h1 : dgU g (x : GL (Fin 3) K) 1 = dgU g (y : GL (Fin 3) K) 1 :=
      congrArg Subtype.val (congrArg Prod.snd hxy)
    have hxd : ∀ z : invLiftsU A hA, dgU g (z : GL (Fin 3) K) 2 =
        dgU g (z : GL (Fin 3) K) 0 * dgU g (z : GL (Fin 3) K) 1 := by
      intro z
      have hp := dgU_prod (hg z z.2)
        (CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU z.1.2)
      rw [Fin.prod_univ_three] at hp
      have h0 := (hsq z).1
      have h1 := (hsq z).2
      calc dgU g (z : GL (Fin 3) K) 2
          = (dgU g (z : GL (Fin 3) K) 0 * dgU g (z : GL (Fin 3) K) 0) *
            (dgU g (z : GL (Fin 3) K) 1 * dgU g (z : GL (Fin 3) K) 1) *
            dgU g (z : GL (Fin 3) K) 2 := by rw [h0, h1]; ring
        _ = (dgU g (z : GL (Fin 3) K) 0 * dgU g (z : GL (Fin 3) K) 1) *
            (dgU g (z : GL (Fin 3) K) 0 * dgU g (z : GL (Fin 3) K) 1 *
              dgU g (z : GL (Fin 3) K) 2) := by ring
        _ = dgU g (z : GL (Fin 3) K) 0 * dgU g (z : GL (Fin 3) K) 1 := by rw [hp, mul_one]
    apply Subtype.ext
    apply Subtype.ext
    apply dgU_inj (hg x x.2) (hg y y.2)
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · show dgU g (x : GL (Fin 3) K) 2 = dgU g (y : GL (Fin 3) K) 2
      rw [hxd x, hxd y, h0, h1]
  have h1 := Nat.card_le_card_of_injective φ hφ
  have h2 := card_le_card_invLiftsU hA
  have h3 : Nat.card ({e : K // e = 1 ∨ e = -1} × {e : K // e = 1 ∨ e = -1}) ≤ 4 := by
    rw [Nat.card_prod]
    have := card_sign_le_two (K := K)
    nlinarith [this, Nat.zero_le (Nat.card {e : K // e = 1 ∨ e = -1})]
  omega


theorem two_ne_zero_of_unitaryFieldData (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    (2 : K) ≠ 0 := by
  have : CharP K p := hU.charP
  have : Fact p.Prime := ⟨hU.prime⟩
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hU.prime Nat.prime_two).mp h')

theorem exists_sign_neg_oneU (hU : UnitaryFieldData p f K)
    {A : Subgroup (StatedProj (unitarySU p f K 3))} (hA : IsElemAbelian 2 A)
    (hA4 : 4 ≤ Nat.card A) {g : GL (Fin 3) K}
    (hg : ∀ x ∈ invLiftsU A hA, IsDiagU g (x : GL (Fin 3) K)) {i j : Fin 3} (hij : i ≠ j) :
    ∃ x ∈ invLiftsU A hA, dgU g (x : GL (Fin 3) K) i * dgU g (x : GL (Fin 3) K) j = -1 := by
  have : Finite K := hU.finite
  by_contra hcon
  push Not at hcon
  have hsqx : ∀ x ∈ invLiftsU A hA, ∀ l : Fin 3,
      dgU g (x : GL (Fin 3) K) l * dgU g (x : GL (Fin 3) K) l = 1 := fun x hx l =>
    dgU_sq (hg x hx) (by simpa using congrArg Subtype.val hx.2) l
  have hone : ∀ x ∈ invLiftsU A hA,
      dgU g (x : GL (Fin 3) K) i * dgU g (x : GL (Fin 3) K) j = 1 := by
    intro x hx
    have h2 : (dgU g (x : GL (Fin 3) K) i * dgU g (x : GL (Fin 3) K) j) *
        (dgU g (x : GL (Fin 3) K) i * dgU g (x : GL (Fin 3) K) j) = 1 := by
      calc (dgU g (x : GL (Fin 3) K) i * dgU g (x : GL (Fin 3) K) j) *
          (dgU g (x : GL (Fin 3) K) i * dgU g (x : GL (Fin 3) K) j)
          = (dgU g (x : GL (Fin 3) K) i * dgU g (x : GL (Fin 3) K) i) *
            (dgU g (x : GL (Fin 3) K) j * dgU g (x : GL (Fin 3) K) j) := by ring
        _ = 1 := by rw [hsqx x hx i, hsqx x hx j, one_mul]
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · exact absurd h (hcon x hx)
  let φ : invLiftsU A hA → {e : K // e = 1 ∨ e = -1} := fun x =>
    ⟨dgU g (x : GL (Fin 3) K) i, mul_self_eq_one_iff.mp (hsqx x x.2 i)⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have hxy' : dgU g (x : GL (Fin 3) K) i = dgU g (y : GL (Fin 3) K) i := congrArg Subtype.val hxy
    apply Subtype.ext
    apply Subtype.ext
    refine dgU_inj (hg x x.2) (hg y y.2) fun l => ?_
    have := sign_vectors_eq (dgU g (x : GL (Fin 3) K)) (dgU g (y : GL (Fin 3) K))
      (hsqx x x.2) (hsqx y y.2)
      (dgU_prod (hg x x.2) (CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU x.1.2))
      (dgU_prod (hg y y.2) (CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU y.1.2))
      hij (hone x x.2) (hone y y.2) hxy'
    exact congrFun this l
  have h1 := Nat.card_le_card_of_injective φ hφ
  have h2 := card_le_card_invLiftsU hA
  have h3 : Nat.card {e : K // e = 1 ∨ e = -1} ≤ 2 := card_sign_le_two
  omega

theorem isDiagU_of_commute (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {A : Subgroup (StatedProj (unitarySU p f K 3))} (hA : IsElemAbelian 2 A)
    (hA4 : 4 ≤ Nat.card A) {g : GL (Fin 3) K}
    (hg : ∀ x ∈ invLiftsU A hA, IsDiagU g (x : GL (Fin 3) K)) {h : GL (Fin 3) K}
    (hh : ∀ x ∈ invLiftsU A hA, h * (x : GL (Fin 3) K) = (x : GL (Fin 3) K) * h) :
    IsDiagU g h := by
  intro i j hij
  obtain ⟨x, hx, hxij⟩ := exists_sign_neg_oneU hU hA hA4 hg hij
  have hK2 := two_ne_zero_of_unitaryFieldData hU hp2
  have hcomm : (g * h * g⁻¹) * (g * (x : GL (Fin 3) K) * g⁻¹) =
      (g * (x : GL (Fin 3) K) * g⁻¹) * (g * h * g⁻¹) := by
    calc (g * h * g⁻¹) * (g * (x : GL (Fin 3) K) * g⁻¹)
        = g * (h * (x : GL (Fin 3) K)) * g⁻¹ := by group
      _ = g * ((x : GL (Fin 3) K) * h) * g⁻¹ := by rw [hh x hx]
      _ = (g * (x : GL (Fin 3) K) * g⁻¹) * (g * h * g⁻¹) := by group
  have hM0 : ((g * h * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((g * (x : GL (Fin 3) K) * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g * (x : GL (Fin 3) K) * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((g * h * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul, ← Units.val_mul, hcomm]
  rw [conjU_eq_diagonal (hg x hx)] at hM0
  have hM := congrFun (congrFun hM0 i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hM
  have hsq : ∀ l, dgU g (x : GL (Fin 3) K) l * dgU g (x : GL (Fin 3) K) l = 1 := fun l =>
    dgU_sq (hg x hx) (by simpa using congrArg Subtype.val hx.2) l
  have hdne : dgU g (x : GL (Fin 3) K) j - dgU g (x : GL (Fin 3) K) i ≠ 0 := by
    intro h0
    have hji : dgU g (x : GL (Fin 3) K) j = dgU g (x : GL (Fin 3) K) i := sub_eq_zero.mp h0
    have h1 := hsq i
    rw [hji] at hxij
    rw [hxij] at h1
    apply hK2
    have : (-1 : K) = 1 := h1
    linear_combination -this
  have : ((g * h * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j *
      (dgU g (x : GL (Fin 3) K) j - dgU g (x : GL (Fin 3) K) i) = 0 := by
    linear_combination hM
  exact (mul_eq_zero.mp this).resolve_right hdne

end CFSG.Quasithin.E22S
