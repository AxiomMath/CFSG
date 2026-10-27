module

public import CFSG.Open.LocalVocabulary
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open Matrix CFSG.Open

structure CubeRoot (K : Type) [Field K] where
  ω : Kˣ
  pow_three : ω ^ 3 = 1
  ne_one : ω ≠ 1

namespace CubeRoot

variable {K : Type} [Field K] (ζ : CubeRoot K)

@[expose] def pow (x : ZMod 3) : Kˣ := ζ.ω ^ x.val

theorem pow_add (x y : ZMod 3) : ζ.pow (x + y) = ζ.pow x * ζ.pow y := by
  unfold pow
  rw [← _root_.pow_add, ZMod.val_add]
  exact (_root_.pow_eq_pow_mod _ ζ.pow_three).symm

theorem pow_zero : ζ.pow 0 = 1 := by simp [pow]

theorem exists_of_dvd [Finite K] (h : 3 ∣ Nat.card K - 1) : Nonempty (CubeRoot K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨⟨ω, ?_, ?_⟩⟩
  · rw [← hω]
    exact pow_orderOf_eq_one ω
  · intro h1
    rw [h1, orderOf_one] at hω
    exact absurd hω (by norm_num)

end CubeRoot

section Standard

variable {K : Type} [Field K]

@[expose] def diagUnit (u : Fin 4 → Kˣ) : GL (Fin 4) K :=
  ⟨Matrix.diagonal fun i => (u i : K), Matrix.diagonal fun i => ((u i)⁻¹ : Kˣ),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩

theorem diagUnit_mul (u v : Fin 4 → Kˣ) : diagUnit (u * v) = diagUnit u * diagUnit v := by
  apply Units.ext
  simp [diagUnit, Matrix.diagonal_mul_diagonal]

theorem diagUnit_one : diagUnit (1 : Fin 4 → Kˣ) = 1 := by
  apply Units.ext
  simp [diagUnit]

theorem card_D₀_diagUnit_injective :
    Function.Injective (diagUnit : (Fin 4 → Kˣ) → GL (Fin 4) K) := by
  intro u v h
  funext i
  apply Units.ext
  have := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) i i) h
  simpa [diagUnit] using this

theorem card_D₀_diagUnit_eq_one_iff (u : Fin 4 → Kˣ) : diagUnit u = 1 ↔ u = 1 :=
  ⟨fun h => card_D₀_diagUnit_injective (h.trans diagUnit_one.symm),
    fun h => by rw [h, diagUnit_one]⟩

theorem mem_D₀_of_diag_diagUnit_pow (u : Fin 4 → Kˣ) (n : ℕ) :
    diagUnit (u ^ n) = diagUnit u ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, diagUnit_one]
  | succ n ih => rw [pow_succ, pow_succ, diagUnit_mul, ih]

@[expose] def stdDiagHom (ζ : CubeRoot K) : Multiplicative (Fin 4 → ZMod 3) →* GL (Fin 4) K where
  toFun v := diagUnit fun i => ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j)
  map_one' := by
    rw [← diagUnit_one]
    congr 1
    funext i
    simp [CubeRoot.pow_zero]
  map_mul' v w := by
    rw [← diagUnit_mul]
    congr 1
    funext i
    simp only [toAdd_mul, Pi.add_apply, Pi.mul_apply, Finset.sum_add_distrib]
    rw [← CubeRoot.pow_add]
    congr 1
    ring

@[expose] def D₀ (ζ : CubeRoot K) : Subgroup (GL (Fin 4) K) := (stdDiagHom ζ).range

@[expose] def d₁ (ζ : CubeRoot K) : GL (Fin 4) K :=
  stdDiagHom ζ (Multiplicative.ofAdd ![1, 1, -1, -1])

@[expose] def d₂ (ζ : CubeRoot K) : GL (Fin 4) K :=
  stdDiagHom ζ (Multiplicative.ofAdd ![1, -1, 0, 0])

@[expose] def d₃ (ζ : CubeRoot K) : GL (Fin 4) K :=
  stdDiagHom ζ (Multiplicative.ofAdd ![1, 1, 1, 0])

theorem stdDiagHom_const (ζ : CubeRoot K) (t : ZMod 3) :
    stdDiagHom ζ (Multiplicative.ofAdd fun _ => t) = 1 := by
  have h : ∀ t : ZMod 3, t - 4 * t = 0 := by decide
  rw [← diagUnit_one]
  show diagUnit _ = diagUnit _
  congr 1
  funext i
  simp [h t, CubeRoot.pow_zero]

theorem stdDiagHom_pow_three (ζ : CubeRoot K) (v : Multiplicative (Fin 4 → ZMod 3)) :
    stdDiagHom ζ v ^ 3 = 1 := by
  rw [← map_pow]
  have : v ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [toAdd_pow]
    decide +revert
  rw [this, map_one]

namespace CubeRoot

theorem card_D₀_pow_eq_one_iff (ζ : CubeRoot K) (x : ZMod 3) : ζ.pow x = 1 ↔ x = 0 := by
  have horder : orderOf ζ.ω = 3 := orderOf_eq_prime ζ.pow_three ζ.ne_one
  rw [CubeRoot.pow, ← orderOf_dvd_iff_pow_eq_one, horder]
  exact ⟨fun h => ZMod.val_eq_zero x |>.mp (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt x)),
    fun h => by subst h; simp⟩

end CubeRoot

theorem card_D₀_stdDiagHom_eq_one_iff (ζ : CubeRoot K)
    (v : Multiplicative (Fin 4 → ZMod 3)) :
    stdDiagHom ζ v = 1 ↔ ∀ i, Multiplicative.toAdd v i = ∑ j, Multiplicative.toAdd v j := by
  rw [show stdDiagHom ζ v =
      diagUnit (fun i => ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j))
      from rfl, card_D₀_diagUnit_eq_one_iff]
  simp only [funext_iff, Pi.one_apply, CubeRoot.card_D₀_pow_eq_one_iff, sub_eq_zero]

theorem det_stdDiagHom_sum (v : Fin 4 → ZMod 3) : (∑ i, (v i - ∑ j, v j)) = 0 := by
  have h : (∑ i, (v i - ∑ j, v j)) = (∑ i, v i) - (∑ i, (∑ j, v j)) :=
    Finset.sum_sub_distrib v (fun _ => ∑ j, v j)
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h4 : ∀ t : ZMod 3, t - 4 * t = 0 := by decide
  exact h4 _

namespace CubeRoot

theorem det_stdDiagHom_prod_pow (ζ : CubeRoot K) {ι : Type*} (s : Finset ι) (x : ι → ZMod 3) :
    ∏ i ∈ s, ζ.pow (x i) = ζ.pow (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [CubeRoot.pow_zero]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, CubeRoot.pow_add]

end CubeRoot

theorem det_stdDiagHom (ζ : CubeRoot K) (v : Multiplicative (Fin 4 → ZMod 3)) :
    ((stdDiagHom ζ v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [show ((stdDiagHom ζ v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun i =>
        (ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j) : K)) from rfl,
    Matrix.det_diagonal]
  rw [show (∏ i, (ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j) : K)) =
      ((∏ i, ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j) : Kˣ) : K)
      from (map_prod (Units.coeHom K)
        (fun i => ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j))
        Finset.univ).symm]
  rw [CubeRoot.det_stdDiagHom_prod_pow,
    det_stdDiagHom_sum, CubeRoot.pow_zero, Units.val_one]

theorem D₀_pow_three (ζ : CubeRoot K) {g : GL (Fin 4) K} (hg : g ∈ D₀ ζ) : g ^ 3 = 1 := by
  obtain ⟨v, rfl⟩ := hg
  exact stdDiagHom_pow_three ζ v

@[expose] def stdDiagHomH (ζ : CubeRoot K) {H : Subgroup (GL (Fin 4) K)} (h : D₀ ζ ≤ H) :
    Multiplicative (Fin 4 → ZMod 3) →* H :=
  (stdDiagHom ζ).codRestrict H fun v => h ⟨v, rfl⟩

@[expose] def stdPt (ζ : CubeRoot K) {H : Subgroup (GL (Fin 4) K)} (h : D₀ ζ ≤ H)
    (w : Fin 4 → ZMod 3) : H :=
  stdDiagHomH ζ h (Multiplicative.ofAdd w)

end Standard

section Torus

variable {K : Type} [Field K]

theorem monomial_of_normalizes_apply (ζ : CubeRoot K)
    (v : Multiplicative (Fin 4 → ZMod 3)) (i : Fin 4) :
    ((stdDiagHom ζ v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i =
      (ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j) : K) := by
  change Matrix.diagonal (fun i => (ζ.pow (Multiplicative.toAdd v i -
    ∑ j, Multiplicative.toAdd v j) : K)) i i =
    (ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j) : K)
  rw [Matrix.diagonal_apply_eq]

theorem monomial_of_normalizes_single (ζ : CubeRoot K) (i k : Fin 4) :
    ((stdDiagHom ζ (Multiplicative.ofAdd (Pi.single i 1)) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) k k = if k = i then (1 : K) else (ζ.pow (-1) : K) := by
  rw [monomial_of_normalizes_apply, toAdd_ofAdd]
  have hsum : ∑ j : Fin 4, (Pi.single i (1 : ZMod 3)) j = 1 := by
    rw [Finset.sum_eq_single i]
    · exact Pi.single_eq_same i 1
    · intro j _ hj; exact Pi.single_eq_of_ne hj 1
    · intro hi; exact absurd (Finset.mem_univ i) hi
  by_cases hki : k = i
  · subst hki
    rw [Pi.single_eq_same, hsum, sub_self, CubeRoot.pow_zero, if_pos rfl]
    rfl
  · rw [Pi.single_eq_of_ne hki, hsum, if_neg hki, zero_sub]
    rfl

theorem monomial_of_normalizes_pow_neg_one_ne_one (ζ : CubeRoot K) :
    (ζ.pow (-1) : K) ≠ 1 := by
  intro h
  have h2 : ζ.ω ^ 2 = 1 := by
    have hv : ((-1 : ZMod 3).val) = 2 := by decide
    simp only [CubeRoot.pow, hv] at h
    exact Units.ext h
  apply ζ.ne_one
  have h3 : ζ.ω ^ 2 * ζ.ω = 1 := by
    rw [← pow_succ, show (2 : ℕ) + 1 = 3 from rfl, ζ.pow_three]
  rw [h2, one_mul] at h3
  exact h3

theorem monomial_of_normalizes_diag (ζ : CubeRoot K) {g : GL (Fin 4) K} (hg : g ∈ D₀ ζ) :
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag := by
  obtain ⟨v, rfl⟩ := hg
  exact Matrix.isDiag_diagonal _

theorem monomial_of_normalizes_distinct (ζ : CubeRoot K) {i j : Fin 4} (hij : i ≠ j) :
    ∃ g ∈ D₀ ζ, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i ≠
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) j j := by
  refine ⟨stdDiagHom ζ (Multiplicative.ofAdd (Pi.single i 1)), ⟨_, rfl⟩, ?_⟩
  rw [monomial_of_normalizes_single ζ i i, monomial_of_normalizes_single ζ i j, if_pos rfl,
    if_neg hij.symm]
  intro h
  exact monomial_of_normalizes_pow_neg_one_ne_one ζ h.symm

theorem monomial_of_normalizes_eq_of_diag {x y : GL (Fin 4) K}
    (hx : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag)
    (hy : ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag)
    (h : ∀ m, ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) m m =
      ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) m m) : x = y := by
  apply Units.ext
  rw [← hx.diagonal_diag, ← hy.diagonal_diag]
  congr 1
  exact funext h

theorem monomial_of_normalizes (ζ : CubeRoot K) {g : GL (Fin 4) K}
    (hg : g ∈ Subgroup.normalizer ((D₀ ζ : Subgroup (GL (Fin 4) K)) : Set (GL (Fin 4) K))) :
    ∃ ρ : Equiv.Perm (Fin 4), ∀ v : Multiplicative (Fin 4 → ZMod 3),
      g * stdDiagHom ζ v * g⁻¹ =
        stdDiagHom ζ (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (ρ i)) := by
  have hw : ∀ x ∈ D₀ ζ, g * x * g⁻¹ ∈ D₀ ζ :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hinv : ∀ x ∈ D₀ ζ, g⁻¹ * x * g ∈ D₀ ζ := by
    intro x hx
    have hginv : g⁻¹ ∈ Subgroup.normalizer
        ((D₀ ζ : Subgroup (GL (Fin 4) K)) : Set (GL (Fin 4) K)) := Subgroup.inv_mem _ hg
    simpa using (Subgroup.mem_normalizer_iff.mp hginv x).mp hx
  obtain ⟨σ, -, -, hσ⟩ := CFSG.RankThree.PartOne.KFU.exists_perm_of_normalizes (n := 4)
    (D₀ ζ) (fun x hx => monomial_of_normalizes_diag ζ hx)
    (fun i j hij => monomial_of_normalizes_distinct ζ hij) (w := g) hw hinv
  refine ⟨σ.symm, fun v => ?_⟩
  refine monomial_of_normalizes_eq_of_diag (monomial_of_normalizes_diag ζ (hw _ ⟨v, rfl⟩))
    (monomial_of_normalizes_diag ζ ⟨_, rfl⟩) (fun m => ?_)
  have hdiag := hσ (stdDiagHom ζ v) ⟨v, rfl⟩ (σ.symm m)
  simp only [Equiv.apply_symm_apply] at hdiag
  have hdiag' : ((g * stdDiagHom ζ v * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) m m =
      ((stdDiagHom ζ v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) (σ.symm m) (σ.symm m) := by
    show CFSG.RankThree.PartOne.KFU.ent (g * stdDiagHom ζ v * g⁻¹) m m =
      CFSG.RankThree.PartOne.KFU.ent (stdDiagHom ζ v) (σ.symm m) (σ.symm m)
    exact hdiag
  rw [hdiag', monomial_of_normalizes_apply ζ v (σ.symm m),
    monomial_of_normalizes_apply ζ
      (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ.symm i)) m,
    toAdd_ofAdd]
  rw [Equiv.sum_comp σ.symm (Multiplicative.toAdd v)]

theorem centralizer_D₀_comm_diag (ζ : CubeRoot K) {H : Subgroup (GL (Fin 4) K)}
    (hD : D₀ ζ ≤ H)
    {x : H} (hx : x ∈ Subgroup.centralizer (((D₀ ζ).subgroupOf H : Subgroup H) : Set H)) :
    ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag := by
  intro i l hil
  let D : GL (Fin 4) K := stdDiagHom ζ (Multiplicative.ofAdd (Pi.single i 1))
  have hDmem : D ∈ D₀ ζ := ⟨Multiplicative.ofAdd (Pi.single i 1), rfl⟩
  have hHmem : (⟨D, hD hDmem⟩ : H) ∈ ((D₀ ζ).subgroupOf H : Subgroup H) := by
    rw [Subgroup.mem_subgroupOf]; exact hDmem
  have hh := (Subgroup.mem_centralizer_iff.mp hx) ⟨D, hD hDmem⟩ hHmem
  have hmat : (D : Matrix (Fin 4) (Fin 4) K) *
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (D : Matrix (Fin 4) (Fin 4) K) := by
    have := congrArg (fun y : H => ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hh
    simpa [Subgroup.coe_mul, Units.val_mul] using this
  have hentry := congrFun (congrFun hmat i) l
  have hDdiag : (D : Matrix (Fin 4) (Fin 4) K).IsDiag := monomial_of_normalizes_diag ζ hDmem
  rw [← hDdiag.diagonal_diag, Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
  have hti : (D : Matrix (Fin 4) (Fin 4) K).diag i = 1 := by
    have h := monomial_of_normalizes_single ζ i i
    rw [if_pos rfl] at h
    simpa using h
  have htl : (D : Matrix (Fin 4) (Fin 4) K).diag l = (ζ.pow (-1) : K) := by
    have h := monomial_of_normalizes_single ζ i l
    rw [if_neg hil.symm] at h
    simpa using h
  rw [hti, htl, one_mul] at hentry
  by_contra hne
  have h1 : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i l * (1 : K) =
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i l * (ζ.pow (-1) : K) := by
    rw [mul_one]
    exact hentry
  exact monomial_of_normalizes_pow_neg_one_ne_one ζ (mul_left_cancel₀ hne h1).symm

theorem centralizer_D₀_comm (ζ : CubeRoot K) {H : Subgroup (GL (Fin 4) K)} (hD : D₀ ζ ≤ H) :
    IsMulCommutative ↥(Subgroup.centralizer (((D₀ ζ).subgroupOf H : Subgroup H) : Set H)) := by
  refine IsMulCommutative.of_comm fun a b => ?_
  apply Subtype.ext
  apply Subtype.ext
  show (a : GL (Fin 4) K) * (b : GL (Fin 4) K) = (b : GL (Fin 4) K) * (a : GL (Fin 4) K)
  have ha : ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag :=
    centralizer_D₀_comm_diag ζ hD a.2
  have hb : ((b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag :=
    centralizer_D₀_comm_diag ζ hD b.2
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← ha.diagonal_diag, ← hb.diagonal_diag,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  exact funext fun k => mul_comm _ _

variable [Finite K]

def card_D₀_ker_equiv (ζ : CubeRoot K) : (stdDiagHom ζ).ker ≃ ZMod 3 where
  toFun v := Multiplicative.toAdd v.1 0
  invFun t := ⟨Multiplicative.ofAdd (fun _ => t), by
    rw [MonoidHom.mem_ker]
    exact stdDiagHom_const ζ t⟩
  left_inv v := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    have hv := (card_D₀_stdDiagHom_eq_one_iff ζ v.1).mp (MonoidHom.mem_ker.mp v.2)
    show Multiplicative.toAdd v.1 0 = Multiplicative.toAdd v.1 i
    rw [hv i, hv 0]
  right_inv t := rfl

theorem card_D₀_ker (ζ : CubeRoot K) : Nat.card (stdDiagHom ζ).ker = 3 := by
  rw [Nat.card_congr (card_D₀_ker_equiv ζ), Nat.card_zmod]

theorem card_D₀ (ζ : CubeRoot K) : Nat.card (D₀ ζ) = 27 := by
  have h := Subgroup.card_ker_mul_card_range (stdDiagHom ζ)
  have h81 : Nat.card (Multiplicative (Fin 4 → ZMod 3)) = 81 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  rw [card_D₀_ker ζ, h81] at h
  change Nat.card (stdDiagHom ζ).range = 27
  omega

theorem mem_D₀_of_diag_exists_diagUnit {g : GL (Fin 4) K}
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag) :
    ∃ u : Fin 4 → Kˣ, diagUnit u = g := by
  classical
  have hdet : IsUnit ((g : Matrix (Fin 4) (Fin 4) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have hne : ∀ i, (g : Matrix (Fin 4) (Fin 4) K) i i ≠ 0 := by
    intro i h0
    have hzero : (g : Matrix (Fin 4) (Fin 4) K).det = 0 := by
      rw [← hg.diagonal_diag, Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using h0)
    rw [hzero] at hdet
    exact not_isUnit_zero hdet
  refine ⟨fun i => Units.mk0 _ (hne i), ?_⟩
  apply Units.ext
  simp only [diagUnit, Units.val_mk0]
  exact hg.diagonal_diag

theorem mem_D₀_of_diag_exists_pow (ζ : CubeRoot K) {w : Kˣ} (hw : w ^ 3 = 1) :
    ∃ a : ZMod 3, ζ.pow a = w := by
  have hω3 : (ζ.ω : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ζ.pow_three, Units.val_one]
  have hωne : (ζ.ω : K) ≠ 1 := fun h => ζ.ne_one (Units.ext h)
  have hsum : 1 + (ζ.ω : K) + (ζ.ω : K) ^ 2 = 0 := by
    have h : ((ζ.ω : K) - 1) * (1 + (ζ.ω : K) + (ζ.ω : K) ^ 2) = 0 := by
      have h' : ((ζ.ω : K) - 1) * (1 + (ζ.ω : K) + (ζ.ω : K) ^ 2) =
          (ζ.ω : K) ^ 3 - 1 := by ring
      rw [h', hω3]; ring
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hωne)
  have hwK : (w : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hw, Units.val_one]
  have hfac : ((w : K) - 1) * ((w : K) - (ζ.ω : K)) * ((w : K) - (ζ.ω : K) ^ 2) = 0 := by
    have hω2 : (ζ.ω : K) ^ 2 = -(1 + (ζ.ω : K)) := by linear_combination hsum
    rw [hω2]
    have h' : ((w : K) - 1) * ((w : K) - (ζ.ω : K)) * ((w : K) - -(1 + (ζ.ω : K))) =
        (w : K) ^ 3 - 1 := by
      linear_combination -((w : K) - 1) * hsum
    rw [h', hwK]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h | h
    · refine ⟨0, ?_⟩
      rw [CubeRoot.pow_zero]
      exact (Units.ext (sub_eq_zero.mp h)).symm
    · refine ⟨1, ?_⟩
      show ζ.ω ^ (1 : ZMod 3).val = w
      rw [show (1 : ZMod 3).val = 1 from by decide, pow_one]
      exact (Units.ext (sub_eq_zero.mp h)).symm
  · refine ⟨2, ?_⟩
    show ζ.ω ^ (2 : ZMod 3).val = w
    rw [show (2 : ZMod 3).val = 2 from by decide]
    exact (Units.ext (sub_eq_zero.mp h)).symm

theorem mem_D₀_of_diag (ζ : CubeRoot K) {g : GL (Fin 4) K}
    (hd : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag) (h3 : g ^ 3 = 1)
    (hdet : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1) : g ∈ D₀ ζ := by
  obtain ⟨u, hu⟩ := mem_D₀_of_diag_exists_diagUnit hd
  have hu3 : u ^ 3 = 1 := by
    apply card_D₀_diagUnit_injective
    rw [mem_D₀_of_diag_diagUnit_pow, hu, h3, diagUnit_one]
  have hu3' : ∀ i, u i ^ 3 = 1 := fun i => by
    have := congrFun hu3 i
    simpa using this
  choose a ha using fun i => mem_D₀_of_diag_exists_pow ζ (hu3' i)
  have hdetprod : ∏ i, u i = 1 := by
    apply Units.ext
    rw [Units.val_one]
    rw [show ((∏ i, u i : Kˣ) : K) = ∏ i, ((u i : Kˣ) : K)
      from map_prod (Units.coeHom K) u Finset.univ]
    have hdiag : (∏ i, (u i : K)) =
        ((diagUnit u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det := by
      rw [show ((diagUnit u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          Matrix.diagonal (fun i => (u i : K)) from rfl, Matrix.det_diagonal]
    rw [hdiag, hu, hdet]
  have hsum0 : ∑ i, a i = 0 := by
    have hprod : ∏ i, ζ.pow (a i) = 1 :=
      (Finset.prod_congr rfl fun i _ => ha i).trans hdetprod
    rw [CubeRoot.det_stdDiagHom_prod_pow] at hprod
    exact (CubeRoot.card_D₀_pow_eq_one_iff ζ _).mp hprod
  change g ∈ (stdDiagHom ζ).range
  refine ⟨Multiplicative.ofAdd a, ?_⟩
  change diagUnit (fun i => ζ.pow (a i - ∑ j, a j)) = g
  rw [show (fun i => ζ.pow (a i - ∑ j, a j)) = fun i => ζ.pow (a i) from by
    funext i
    rw [hsum0]
    exact congrArg ζ.pow (sub_zero (a i))]
  rw [show diagUnit (fun i => ζ.pow (a i)) = diagUnit u from by
    congr 1; funext i; exact ha i]
  exact hu

end Torus

structure TwoQuot {H Y : Type} [Group H] [Group Y] (π : H →* Y) : Prop where
  surj : Function.Surjective π
  central : π.ker ≤ Subgroup.center H
  two : IsPGroup 2 π.ker

section Facts

variable {K : Type} [Field K] [Finite K] (H : Subgroup (GL (Fin 4) K)) (ζ : CubeRoot K) (r : ℕ)

@[expose] def ConjFact : Prop :=
  D₀ ζ ≤ H ∧ ∀ A : Subgroup H, IsElemAbelian 3 A → Nat.card A = 27 →
    ∃ g : H, A.map (MulAut.conj g).toMonoidHom = (D₀ ζ).subgroupOf H

@[expose] def CentFact : Prop :=
  (∀ d : H, (d : GL (Fin 4) K) = d₁ ζ →
    (Nat.card (Subgroup.centralizer ({d} : Set H))).factorization r = 2 ∧
    pRank r (Subgroup.centralizer ({d} : Set H)) = 2) ∧
  (∀ d : H, (d : GL (Fin 4) K) = d₂ ζ →
    (Nat.card (Subgroup.centralizer ({d} : Set H))).factorization r = 1) ∧
  (∀ d : H, (d : GL (Fin 4) K) = d₃ ζ →
    (Nat.card (Subgroup.centralizer ({d} : Set H))).factorization r = 3 ∧
    pRank r (Subgroup.centralizer ({d} : Set H)) = 2) ∧
  (∀ d : H, (d : GL (Fin 4) K) = d₂ ζ →
    (Nat.card (Subgroup.centralizer (((D₀ ζ).subgroupOf H : Subgroup H) : Set H))).factorization
        3 = (Nat.card (Subgroup.centralizer ({d} : Set H))).factorization 3)

@[expose] def Sub8Fact : Prop :=
  ∀ d : H, (d : GL (Fin 4) K) = d₁ ζ →
    ∃ K₁ : Subgroup H, K₁ ≤ Subgroup.centralizer ({d} : Set H) ∧ ⁅K₁, K₁⁆ = K₁ ∧
      ¬ IsSolvable K₁ ∧ Nat.card K₁ = (r * (r ^ 2 - 1)) ^ 2 ∧
      Nat.card ↥(K₁ ⊓ (StatedScalars (Fin 4) K).subgroupOf H) = 2 ∧
      ∀ N : Subgroup H, N ≤ K₁ → (N.subgroupOf K₁).Normal →
        K₁ ⊓ (StatedScalars (Fin 4) K).subgroupOf H ≤ N → Odd (Nat.card N / 2) →
          N ≤ (StatedScalars (Fin 4) K).subgroupOf H

@[expose] def Sub9Fact : Prop :=
  ∀ d : H, (d : GL (Fin 4) K) = d₃ ζ →
    ∃ K₃ : Subgroup H, K₃ ≤ Subgroup.centralizer ({d} : Set H) ∧ ¬ IsSolvable K₃ ∧
      K₃ ⊓ (StatedScalars (Fin 4) K).subgroupOf H = ⊥ ∧
      ∀ N : Subgroup H, N ≤ K₃ → (N.subgroupOf K₃).Normal → Odd (Nat.card N) →
        N ≤ Subgroup.centralizer (K₃ : Set H)

end Facts

theorem orbit_four : ∀ w : Fin 4 → ZMod 3, ∑ i, w i = 0 → w ≠ 0 →
    (Finset.univ.image fun σ : Equiv.Perm (Fin 4) => w ∘ σ).card ≤ 4 →
    ∃ ε : ZMod 3, ε ≠ 0 ∧ ∃ j : Fin 4, w = fun i => if i = j then 0 else ε := by
  decide +kernel

theorem point_classes : ∀ u : Fin 4 → ZMod 3, (¬ ∃ t : ZMod 3, u = fun _ => t) →
    ∃ (ε : ZMod 3) (σ : Equiv.Perm (Fin 4)) (t : ZMod 3),
      ε ≠ 0 ∧ ((∀ i, u i = ε * ![1, 1, -1, -1] (σ i) + t) ∨
        (∀ i, u i = ε * ![1, -1, 0, 0] (σ i) + t) ∨ (∀ i, u i = ε * ![1, 1, 1, 0] (σ i) + t)) := by
  decide +kernel

theorem weights_of_invariant_eq {ε ε' : ZMod 3} (hε : ε ≠ 0) (hε' : ε' ≠ 0) {k k' : Fin 4}
    (h : (fun i => if i = k then 0 else ε) = fun i => if i = k' then 0 else ε') :
    ε = ε' ∧ k = k' := by
  have hk : k = k' := by
    by_contra hne
    have h1 := congr_fun h k
    rw [if_pos rfl, if_neg hne] at h1
    exact hε' h1.symm
  subst hk
  refine ⟨?_, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, i ≠ k := Fintype.exists_ne_of_one_lt_card (by norm_num) k
  have h1 := congr_fun h i
  rwa [if_neg hi, if_neg hi] at h1

theorem weights_of_invariant_orbit_card (ξ : Fin 4 → Fin 4 → ZMod 3)
    (hinv : ∀ (σ : Equiv.Perm (Fin 4)) (j : Fin 4), ∃ j', ∀ i, ξ j (σ i) = ξ j' i) (j : Fin 4) :
    (Finset.univ.image fun σ : Equiv.Perm (Fin 4) => ξ j ∘ σ).card ≤ 4 := by
  calc (Finset.univ.image fun σ : Equiv.Perm (Fin 4) => ξ j ∘ σ).card
      ≤ (Finset.univ.image ξ).card := Finset.card_le_card fun x hx => by
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
        obtain ⟨σ, rfl⟩ := hx
        obtain ⟨j', hj'⟩ := hinv σ j
        exact ⟨j', (funext hj').symm⟩
    _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
    _ = 4 := by simp

theorem weights_of_invariant_range {ξ : Fin 4 → Fin 4 → ZMod 3}
    (hinv : ∀ (σ : Equiv.Perm (Fin 4)) (j : Fin 4), ∃ j', ∀ i, ξ j (σ i) = ξ j' i)
    {j₀ : Fin 4} {ε : ZMod 3} {k : Fin 4}
    (hk : ξ j₀ = fun i => if i = k then 0 else ε) :
    ∀ m : Fin 4, (fun i => if i = m then 0 else ε) ∈ Finset.univ.image ξ := by
  intro m
  set σ : Equiv.Perm (Fin 4) := Equiv.swap m k with hσ
  obtain ⟨j', hj'⟩ := hinv σ j₀
  refine Finset.mem_image.mpr ⟨j', Finset.mem_univ _, ?_⟩
  funext i
  rw [← hj' i, hk]
  have hσs : σ.symm k = m := by
    rw [hσ, Equiv.symm_swap]
    exact Equiv.swap_apply_right m k
  have hiff : σ i = k ↔ i = m := by
    rw [Equiv.apply_eq_iff_eq_symm_apply, hσs]
  exact if_congr hiff rfl rfl

theorem weights_of_invariant_image {ξ : Fin 4 → Fin 4 → ZMod 3}
    {ε : ZMod 3} (hε : ε ≠ 0)
    (hrange : ∀ m : Fin 4, (fun i => if i = m then 0 else ε) ∈ Finset.univ.image ξ) :
    Finset.univ.image ξ =
      Finset.univ.image (fun m : Fin 4 => (fun i => if i = m then 0 else ε)) := by
  have hcard : (Finset.univ.image fun m : Fin 4 =>
      (fun i => if i = m then 0 else ε)).card = 4 := by
    rw [Finset.card_image_of_injective Finset.univ
      fun _ _ h => (weights_of_invariant_eq hε hε h).2]
    simp
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨m, hm⟩ := hx
    rw [← hm]
    exact hrange m
  · rw [hcard]
    calc (Finset.univ.image ξ).card ≤ (Finset.univ : Finset (Fin 4)).card :=
          Finset.card_image_le
      _ = 4 := by simp

theorem weights_of_invariant (ξ : Fin 4 → Fin 4 → ZMod 3)
    (hsum : ∀ j, ∑ i, ξ j i = 0) (hne : ∀ j, ξ j ≠ 0) (hinj : Function.Injective ξ)
    (hinv : ∀ (σ : Equiv.Perm (Fin 4)) (j : Fin 4), ∃ j', ∀ i, ξ j (σ i) = ξ j' i) :
    ∃ (ε : ZMod 3) (τ : Equiv.Perm (Fin 4)), ε ≠ 0 ∧ ∀ j i, ξ j i = if i = τ j then 0 else ε := by
  classical
  have hrepr : ∀ j, ∃ (ε : ZMod 3) (k : Fin 4), ε ≠ 0 ∧
      ξ j = fun i => if i = k then 0 else ε := by
    intro j
    obtain ⟨ε, hε, k, hk⟩ := orbit_four (ξ j) (hsum j) (hne j)
      (weights_of_invariant_orbit_card ξ hinv j)
    exact ⟨ε, k, hε, hk⟩
  choose ε k hε hk using hrepr
  obtain ⟨j₀⟩ := (inferInstance : Nonempty (Fin 4))
  have hset_eq : Finset.univ.image ξ =
      Finset.univ.image (fun m : Fin 4 => (fun i => if i = m then 0 else ε j₀)) :=
    weights_of_invariant_image (hε j₀) (weights_of_invariant_range hinv (hk j₀))
  have hmem : ∀ j, ∃ m : Fin 4, ξ j = fun i => if i = m then 0 else ε j₀ := by
    intro j
    have : ξ j ∈ Finset.univ.image (fun m : Fin 4 => (fun i => if i = m then 0 else ε j₀)) := by
      rw [← hset_eq]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    obtain ⟨m, hm⟩ := Finset.mem_image.mp this
    exact ⟨m, hm.2.symm⟩
  have hεeq : ∀ j, ε j = ε j₀ := by
    intro j
    obtain ⟨m, hm⟩ := hmem j
    exact (weights_of_invariant_eq (hε j) (hε j₀) ((hk j).symm.trans hm)).1
  have hkinj : Function.Injective k := by
    intro j₁ j₂ hk12
    apply hinj
    rw [hk j₁, hk j₂, hk12, hεeq j₁, hεeq j₂]
  let τ : Equiv.Perm (Fin 4) :=
    Equiv.ofBijective k ⟨hkinj, Finite.injective_iff_surjective.mp hkinj⟩
  exact ⟨ε j₀, τ, hε j₀, fun j i => by rw [hk j, hεeq j]; rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
