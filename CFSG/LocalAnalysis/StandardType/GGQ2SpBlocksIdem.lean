module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpStatements
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsDiag
import CFSG.LocalAnalysis.StandardType.GGTorCPlane

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K]

theorem coe_tau (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (u : PlaneRaw.V m) :
    (((tau ζ m u : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      WitSpNs.planeMat fun j =>
        ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) :=
  TorC.coe_spPlaneTorus m ζ fun i => Multiplicative.ofAdd (u i)

theorem planeMat_add {m : ℕ} (M M' : Fin m → Matrix (Fin 2) (Fin 2) K) :
    WitSpNs.planeMat M + WitSpNs.planeMat M' = WitSpNs.planeMat (M + M') := by
  ext a b
  simp only [Matrix.add_apply, WitSpNs.planeMat_apply, Pi.add_apply]
  split_ifs <;> simp

theorem planeIdem_eq_planeMat (m : ℕ) (S : Finset (Fin m)) :
    (planeIdem m S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      WitSpNs.planeMat fun j => if j ∈ S then 1 else 0 := by
  ext a b
  rw [WitSpNs.planeMat_apply, planeIdem, Matrix.diagonal_apply]
  rcases a with i | i <;> rcases b with j | j <;> by_cases hij : i = j <;>
    by_cases hj : j ∈ S <;> simp [hij, hj, Matrix.one_apply]

theorem planeIdem_inter (m : ℕ) (S T : Finset (Fin m)) :
    (planeIdem m (S ∩ T) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      planeIdem m S * planeIdem m T := by
  simp only [planeIdem, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  by_cases hS : Sum.elim id id x ∈ S <;> by_cases hT : Sum.elim id id x ∈ T <;> simp [hS, hT]

theorem planeIdem_univ (m : ℕ) :
    (planeIdem m Finset.univ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 := by
  simp [planeIdem]

theorem planeIdem_compl (m : ℕ) (S : Finset (Fin m)) :
    (planeIdem m Sᶜ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 - planeIdem m S := by
  simp only [planeIdem]
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  congr 1
  funext x
  by_cases hS : Sum.elim id id x ∈ S <;> simp [hS]

theorem neg_eq_self_of_charTwo [CharP K 2] {ι : Type} [Fintype ι] (X : Matrix ι ι K) :
    -X = X := by
  ext i j
  simp [CharTwo.neg_eq]

theorem add_self_eq_zero_of_charTwo [CharP K 2] {ι : Type} [Fintype ι] (X : Matrix ι ι K) :
    X + X = 0 := by
  ext i j
  simp [CharTwo.add_self_eq_zero]

theorem eq_zero_or_eq_one [Finite K] (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hx : x ^ 2 = x := by
    have := FiniteField.pow_card x
    rwa [Fintype.card_eq_nat_card, hK] at this
  have hx' : x * (x - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, hx, sub_self]
  rcases mul_eq_zero.mp hx' with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h0)

theorem mul_self_add_self_eq_one [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {h : SpecialLinearGroup (Fin 2) K} (h3 : h ^ 3 = 1) (h1 : h ≠ 1) :
    (h : Matrix (Fin 2) (Fin 2) K) * h + h = 1 := by
  set A : Matrix (Fin 2) (Fin 2) K := ↑h with hA_def
  have hdet : A.det = 1 := h.2
  have hCH : A * A = A.trace • A - 1 := by
    have hc := Matrix.aeval_self_charpoly A
    rw [Matrix.charpoly_fin_two, hdet] at hc
    simp only [map_add, map_sub, map_mul, Polynomial.aeval_X_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, map_one, Algebra.algebraMap_eq_smul_one] at hc
    rw [smul_mul_assoc, one_mul, pow_two] at hc
    rw [eq_sub_iff_add_eq]
    calc A * A + 1 = (A * A - A.trace • A + 1) + A.trace • A := by abel
      _ = A.trace • A := by rw [hc, zero_add]
  have h01 := eq_zero_or_eq_one hK
  have hA3 : A * (A * A) = 1 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h3
    simpa [pow_succ, pow_two, Matrix.mul_assoc] using this
  rcases h01 A.trace with ht | ht
  · exfalso
    apply h1
    have hsq : A * A = 1 := by
      rw [hCH, ht, zero_smul, zero_sub, neg_eq_self_of_charTwo]
    have : A = 1 := by rw [← hA3, hsq, Matrix.mul_one]
    exact Subtype.ext this
  · rw [hCH, ht, one_smul]
    calc A - 1 + A = (A + A) - 1 := by abel
      _ = 1 := by rw [add_self_eq_zero_of_charTwo, zero_sub, neg_eq_self_of_charTwo]

theorem zeta_mul_self_add [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    (k : ZMod 3) :
    ((ζ (Multiplicative.ofAdd k) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (ζ (Multiplicative.ofAdd k) : SpecialLinearGroup (Fin 2) K) +
      (ζ (Multiplicative.ofAdd k) : SpecialLinearGroup (Fin 2) K) = if k = 0 then 0 else 1 := by
  split_ifs with hk
  · subst hk
    rw [ofAdd_zero, map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul,
      add_self_eq_zero_of_charTwo]
  · apply mul_self_add_self_eq_one hK
    · rw [← map_pow, ← ofAdd_nsmul]
      have h3 : (3 : ℕ) • k = 0 := by revert k; decide
      rw [h3, ofAdd_zero, map_one]
    · intro h
      apply hk
      have := hζ (h.trans (map_one ζ).symm)
      simpa using this

theorem tau_mul_self_add [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (u : PlaneRaw.V m) :
    (((tau ζ m u : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        (((tau ζ m u : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) +
      (((tau ζ m u : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      planeIdem m (Finset.univ.filter fun j => u j ≠ 0) := by
  rw [coe_tau, WitSpNs.planeMat_mul, planeMat_add, planeIdem_eq_planeMat]
  congr 1
  funext j
  rw [Pi.add_apply, zeta_mul_self_add hK hζ]
  by_cases hj : u j = 0 <;> simp [hj]

theorem planeIdem_iInter_mem {m : ℕ} {ι : Type} [Fintype ι]
    (A : Subalgebra K (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) (W : ι → Finset (Fin m))
    (hW : ∀ i, planeIdem m (W i) ∈ A) :
    planeIdem m (Finset.univ.filter fun j => ∀ i, j ∈ W i) ∈ A := by
  classical
  have key : ∀ s : Finset ι,
      planeIdem m (Finset.univ.filter fun j => ∀ i ∈ s, j ∈ W i) ∈ A := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [planeIdem_univ]
    | insert a s ha ih =>
      have hs : (Finset.univ.filter fun j => ∀ i ∈ insert a s, j ∈ W i) =
          W a ∩ Finset.univ.filter fun j => ∀ i ∈ s, j ∈ W i := by
        ext j
        simp [Finset.mem_insert, forall_eq_or_imp]
      rw [hs, planeIdem_inter]
      exact A.mul_mem (hW a) ih
  simpa using key Finset.univ

theorem planeIdem_mem_adjoin [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (U : Submodule (ZMod 3) (PlaneRaw.V m)) {c : PlaneRaw.Code m}
    (hc : PlaneRaw.occurs U c) :
    planeIdem m c.support ∈ Algebra.adjoin K (Units.val '' torusSet ζ m U) := by
  classical
  set A := Algebra.adjoin K (Units.val '' torusSet ζ m U) with hA
  have : Fintype ↥U := Fintype.ofFinite _
  have hT : ∀ u : ↥U,
      planeIdem m (Finset.univ.filter fun j => (u : PlaneRaw.V m) j ≠ 0) ∈ A := by
    intro u
    have hg : (((tau ζ m (u : PlaneRaw.V m) : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) ∈ A :=
      Algebra.subset_adjoin ⟨_, ⟨u, u.2, rfl⟩, rfl⟩
    rw [← tau_mul_self_add hK hζ]
    exact A.add_mem (A.mul_mem hg hg) hg
  have hTc : ∀ u : ↥U,
      planeIdem m (Finset.univ.filter fun j => (u : PlaneRaw.V m) j ≠ 0)ᶜ ∈ A := by
    intro u
    rw [planeIdem_compl]
    exact A.sub_mem A.one_mem (hT u)
  cases c with
  | zero S =>
    have hS : S = Finset.univ.filter fun j =>
        ∀ u : ↥U, j ∈ (Finset.univ.filter fun j => (u : PlaneRaw.V m) j ≠ 0)ᶜ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, not_not]
      exact hc j
    change planeIdem m S ∈ A
    rw [hS]
    exact planeIdem_iInter_mem A _ hTc
  | extension e =>
    obtain ⟨-, χ, hχ, hsupp, hout⟩ := hc
    have happ : ∀ (i : Fin m) (u : ↥U), PlaneRaw.evalRestr U i u = (u : PlaneRaw.V m) i :=
      fun _ _ => rfl
    let W : ↥U → Finset (Fin m) := fun u =>
      if χ u ≠ 0 then Finset.univ.filter fun j => (u : PlaneRaw.V m) j ≠ 0
      else (Finset.univ.filter fun j => (u : PlaneRaw.V m) j ≠ 0)ᶜ
    have hW : ∀ u, planeIdem m (W u) ∈ A := by
      intro u
      simp only [W]
      split_ifs
      exacts [hT u, hTc u]
    have heq : PlaneRaw.Code.extSupport e = Finset.univ.filter fun j => ∀ u, j ∈ W u := by
      ext j
      simp only [PlaneRaw.Code.extSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hej u
        have hj : (u : PlaneRaw.V m) j = e j * χ u := by
          rw [← happ, hsupp j hej, LinearMap.smul_apply, smul_eq_mul]
        simp only [W]
        split_ifs with hu
        · simp [hj, hej, hu]
        · simp only [not_not] at hu
          simp [hj, hu]
      · intro hall
        by_contra hej
        obtain ⟨hne1, hne2⟩ := hout j hej
        obtain ⟨u₁, hu₁⟩ : ∃ u, χ u ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hχ (LinearMap.ext hcon)
        set u₀ : ↥U := (χ u₁)⁻¹ • u₁ with hu₀
        have hχ₀ : χ u₀ = 1 := by
          rw [hu₀, map_smul, smul_eq_mul, inv_mul_cancel₀ hu₁]
        have hmem : ∀ u : ↥U, (χ u ≠ 0 → (u : PlaneRaw.V m) j ≠ 0) ∧
            (χ u = 0 → (u : PlaneRaw.V m) j = 0) := by
          intro u
          have h := hall u
          simp only [W] at h
          split_ifs at h with hu
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
            exact ⟨fun _ => h, fun h0 => absurd h0 hu⟩
          · simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
              not_not] at h
            exact ⟨fun h0 => absurd (not_not.mp hu) h0, fun _ => h⟩
        set a := (u₀ : PlaneRaw.V m) j with ha
        have ha0 : a ≠ 0 := (hmem u₀).1 (by rw [hχ₀]; exact one_ne_zero)
        have hψ : PlaneRaw.evalRestr U j = a • χ := by
          ext u
          rw [happ, LinearMap.smul_apply, smul_eq_mul]
          have hv := (hmem (u - χ u • u₀)).2 (by rw [map_sub, map_smul, hχ₀, smul_eq_mul,
            mul_one, sub_self])
          rw [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply,
            smul_eq_mul, sub_eq_zero] at hv
          rw [hv, ha, mul_comm]
        have h12 : ∀ b : ZMod 3, b ≠ 0 → b = 1 ∨ b = -1 := by decide
        rcases h12 a ha0 with h1 | h1
        · exact hne1 (by rw [hψ, h1, one_smul])
        · exact hne2 (by rw [hψ, h1]; ext u; simp)
    change planeIdem m (PlaneRaw.Code.extSupport e) ∈ A
    rw [heq]
    exact planeIdem_iInter_mem A W hW

theorem commute_of_mem_adjoin {m : ℕ} {S : Set (GL (Fin m ⊕ Fin m) K)}
    {g : GL (Fin m ⊕ Fin m) K} (hg : g ∈ Subgroup.centralizer S)
    {a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K} (ha : a ∈ Algebra.adjoin K (Units.val '' S)) :
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * a =
      a * (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
  refine Algebra.adjoin_induction (p := fun x _ =>
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * x =
      x * (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp hg s hs
    rw [← Units.val_mul, ← Units.val_mul, h]
  · intro r
    exact (Algebra.commutes r _).symm
  · intro x y _ _ hx hy
    rw [Matrix.mul_add, Matrix.add_mul, hx, hy]
  · intro x y _ _ hx hy
    rw [← Matrix.mul_assoc, hx, Matrix.mul_assoc, hy, Matrix.mul_assoc]

theorem commute_planeIdem_of_mem_centralizer [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (U : Submodule (ZMod 3) (PlaneRaw.V m)) {c : PlaneRaw.Code m}
    (hc : PlaneRaw.occurs U c) {g : GL (Fin m ⊕ Fin m) K}
    (hg : g ∈ Subgroup.centralizer (torusSet ζ m U)) :
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * planeIdem m c.support =
      planeIdem m c.support * (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :=
  commute_of_mem_adjoin hg (planeIdem_mem_adjoin hK hζ U hc)

theorem evalRestr_apply' {m : ℕ} (U : Submodule (ZMod 3) (PlaneRaw.V m)) (i : Fin m) (u : ↥U) :
    PlaneRaw.evalRestr U i u = (u : PlaneRaw.V m) i :=
  rfl

theorem planeMat_smul {m : ℕ} (r : K) (M : Fin m → Matrix (Fin 2) (Fin 2) K) :
    r • WitSpNs.planeMat M = WitSpNs.planeMat fun j => r • M j := by
  ext a b
  simp only [Matrix.smul_apply, WitSpNs.planeMat_apply]
  split_ifs <;> simp

theorem zeta_one_mul_self [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ) :
    ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) =
      1 + (ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) := by
  have h := zeta_mul_self_add hK hζ 1
  rw [if_neg (show (1 : ZMod 3) ≠ 0 by decide)] at h
  rw [← h, add_assoc, add_self_eq_zero_of_charTwo, add_zero]

theorem coe_zeta_eq [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    (k : ZMod 3) :
    ((ζ (Multiplicative.ofAdd k) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (if k = 1 then 0 else 1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) +
        (if k = 0 then 0 else 1 : K) •
          ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by revert k; decide
  rcases hk with rfl | rfl | rfl
  · rw [if_neg (show (0 : ZMod 3) ≠ 1 by decide), if_pos rfl, ofAdd_zero, map_one,
      Matrix.SpecialLinearGroup.coe_one, one_smul, zero_smul, add_zero]
  · rw [if_pos rfl, if_neg (show (1 : ZMod 3) ≠ 0 by decide), zero_smul, one_smul, zero_add]
  · rw [if_neg (show (2 : ZMod 3) ≠ 1 by decide), if_neg (show (2 : ZMod 3) ≠ 0 by decide),
      one_smul, one_smul, show (2 : ZMod 3) = 1 + 1 by decide, ofAdd_add, map_mul,
      Matrix.SpecialLinearGroup.coe_mul, zeta_one_mul_self hK hζ]

theorem zeta_coeff_neg [CharP K 2] (k : ZMod 3) :
    ((if -k = 1 then 0 else 1 : K) = (if k = 1 then 0 else 1) + (if k = 0 then 0 else 1)) ∧
      ((if -k = 0 then 0 else 1 : K) = if k = 0 then 0 else 1) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by revert k; decide
  rcases hk with rfl | rfl | rfl <;> simp +decide [CharTwo.add_self_eq_zero]

theorem blk_mul {Z : Matrix (Fin 2) (Fin 2) K} (hZ : Z * Z = 1 + Z) (α β α' β' : K) :
    (α • (1 : Matrix (Fin 2) (Fin 2) K) + β • Z) * (α' • 1 + β' • Z) =
      (α * α' + β * β') • 1 + (α * β' + β * α' + β * β') • Z := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hZ]
  module

theorem blk_inj [Finite K] [CharP K 2] (hK : Nat.card K = 2) {Z : Matrix (Fin 2) (Fin 2) K}
    (hZ : Z * Z = 1 + Z) {α β α' β' : K}
    (h : α • (1 : Matrix (Fin 2) (Fin 2) K) + β • Z = α' • 1 + β' • Z) : α = α' ∧ β = β' := by
  have hβ : β = β' := by
    by_contra hne
    have hd : β - β' ≠ 0 := sub_ne_zero.mpr hne
    have h2 : (β - β') • Z = (α' - α) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, add_comm (β • Z)]
      exact h
    have hZc : Z = ((β - β')⁻¹ * (α' - α)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd, one_smul]
    set c := (β - β')⁻¹ * (α' - α)
    rw [hZc, smul_mul_smul_comm, mul_one] at hZ
    have h00 := congrFun (congrFun hZ 0) 0
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one] at h00
    rcases eq_zero_or_eq_one hK c with hc | hc
    · rw [hc, mul_zero, add_zero] at h00
      exact zero_ne_one h00
    · rw [hc, mul_one, CharTwo.add_self_eq_zero] at h00
      exact one_ne_zero h00
  subst hβ
  refine ⟨?_, rfl⟩
  have h1 := congrArg (· - β • Z) h
  simp only [add_sub_cancel_right] at h1
  have h00 := congrFun (congrFun h1 0) 0
  simpa using h00

theorem exists_blocks_of_mem_adjoin [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (U : Submodule (ZMod 3) (PlaneRaw.V m))
    {a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (ha : a ∈ Algebra.adjoin K (Units.val '' torusSet ζ m U)) :
    ∃ α β : Fin m → K, a = WitSpNs.planeMat (fun j => α j • (1 : Matrix (Fin 2) (Fin 2) K) +
        β j • ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) ∧
      ∀ i j, (PlaneRaw.evalRestr U i = PlaneRaw.evalRestr U j → α i = α j ∧ β i = β j) ∧
        (PlaneRaw.evalRestr U i = -PlaneRaw.evalRestr U j → α i = α j + β j ∧ β i = β j) := by
  have hZ := zeta_one_mul_self hK hζ
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, ⟨u, hu, rfl⟩, rfl⟩ := hx
    refine ⟨fun j => if u j = 1 then 0 else 1, fun j => if u j = 0 then 0 else 1, ?_,
      fun i j => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [coe_tau]
      congr 1
      funext j
      exact coe_zeta_eq hK hζ (u j)
    · have hij := congrArg (fun f => f ⟨u, hu⟩) h
      simp only [evalRestr_apply'] at hij
      simp only [hij, and_self]
    · have hij := congrArg (fun f => f ⟨u, hu⟩) h
      simp only [LinearMap.neg_apply, evalRestr_apply'] at hij
      simp only [hij]
      exact zeta_coeff_neg (u j)
  | algebraMap r =>
    refine ⟨fun _ => r, fun _ => 0, ?_, fun i j => ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨?_, rfl⟩⟩⟩
    · rw [Algebra.algebraMap_eq_smul_one, ← WitSpNs.planeMat_one, planeMat_smul]
      simp only [zero_smul, add_zero]
    · rw [add_zero]
  | add x y _ _ hx hy =>
    obtain ⟨α, β, rfl, hαβ⟩ := hx
    obtain ⟨α', β', rfl, hαβ'⟩ := hy
    refine ⟨α + α', β + β', ?_, fun i j => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [planeMat_add]
      congr 1
      funext j
      simp only [Pi.add_apply, add_smul]
      abel
    · obtain ⟨h1, h2⟩ := (hαβ i j).1 h
      obtain ⟨h1', h2'⟩ := (hαβ' i j).1 h
      simp only [Pi.add_apply, h1, h2, h1', h2', and_self]
    · obtain ⟨h1, h2⟩ := (hαβ i j).2 h
      obtain ⟨h1', h2'⟩ := (hαβ' i j).2 h
      refine ⟨?_, by simp only [Pi.add_apply, h2, h2']⟩
      simp only [Pi.add_apply]
      rw [h1, h1']
      ring
  | mul x y _ _ hx hy =>
    obtain ⟨α, β, rfl, hαβ⟩ := hx
    obtain ⟨α', β', rfl, hαβ'⟩ := hy
    refine ⟨fun j => α j * α' j + β j * β' j, fun j => α j * β' j + β j * α' j + β j * β' j, ?_,
      fun i j => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [WitSpNs.planeMat_mul]
      congr 1
      funext j
      exact blk_mul hZ _ _ _ _
    · obtain ⟨h1, h2⟩ := (hαβ i j).1 h
      obtain ⟨h1', h2'⟩ := (hαβ' i j).1 h
      simp only [h1, h2, h1', h2', and_self]
    · obtain ⟨h1, h2⟩ := (hαβ i j).2 h
      obtain ⟨h1', h2'⟩ := (hαβ' i j).2 h
      simp only [h1, h2, h1', h2']
      exact ⟨by ring, by linear_combination (β j * β' j) * h2K⟩

theorem exists_planeIdem_of_isIdempotentElem [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (U : Submodule (ZMod 3) (PlaneRaw.V m))
    {e : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (he : e ∈ Algebra.adjoin K (Units.val '' torusSet ζ m U)) (hidem : IsIdempotentElem e) :
    ∃ T : Finset (Fin m), e = planeIdem m T ∧ ∀ i j,
      (PlaneRaw.evalRestr U i = PlaneRaw.evalRestr U j ∨
        PlaneRaw.evalRestr U i = -PlaneRaw.evalRestr U j) → j ∈ T → i ∈ T := by
  classical
  obtain ⟨α, β, rfl, hαβ⟩ := exists_blocks_of_mem_adjoin hK hζ U he
  have hZ := zeta_one_mul_self hK hζ
  have hsq : ∀ x : K, x * x = x := fun x => by
    rcases eq_zero_or_eq_one hK x with h | h <;> simp [h]
  have hblk : ∀ j, β j = 0 ∧ (α j = 0 ∨ α j = 1) := by
    intro j
    have h1 := hidem.eq
    rw [WitSpNs.planeMat_mul] at h1
    have h2 := congrFun (WitSpNs.planeMat_injective h1) j
    simp only [blk_mul hZ] at h2
    have h3 := (blk_inj hK hZ h2).1
    rw [hsq, hsq] at h3
    exact ⟨by simpa using h3, eq_zero_or_eq_one hK _⟩
  refine ⟨Finset.univ.filter fun j => α j = 1, ?_, fun i j hij hj => ?_⟩
  · rw [planeIdem_eq_planeMat]
    congr 1
    funext j
    rw [(hblk j).1, zero_smul, add_zero]
    rcases (hblk j).2 with h | h <;> simp [h]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rcases hij with h | h
    · rw [((hαβ i j).1 h).1, hj]
    · rw [((hαβ i j).2 h).1, (hblk j).1, add_zero, hj]

theorem symJ_mul_self (m : ℕ) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      fromBlocks 0 1 (-1) 0 = -1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem formAdj_planeIdem (m : ℕ) (S : Finset (Fin m)) :
    formAdj (RingHom.id K) (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      (planeIdem m S) = planeIdem m S := by
  have hinv : (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)⁻¹ =
      -fromBlocks 0 1 (-1) 0 :=
    Matrix.inv_eq_left_inv (by rw [neg_mul, symJ_mul_self, neg_neg])
  have hcomm : (planeIdem m S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      fromBlocks 0 1 (-1) 0 = fromBlocks 0 1 (-1) 0 * planeIdem m S := by
    ext a b
    simp only [planeIdem, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rcases a with i | i <;> rcases b with j | j <;> by_cases hij : i = j <;>
      simp [hij] <;> rfl
  have hmap : (planeIdem m S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map (RingHom.id K) =
      planeIdem m S := by
    ext a b
    rfl
  have htr : (planeIdem m S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)ᵀ = planeIdem m S :=
    Matrix.diagonal_transpose _
  rw [formAdj, hinv, hmap, htr, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, neg_mul,
    symJ_mul_self, neg_neg, Matrix.one_mul]

theorem isIdempotentElem_planeIdem (m : ℕ) (S : Finset (Fin m)) :
    IsIdempotentElem (planeIdem m S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
  rw [IsIdempotentElem, ← planeIdem_inter, Finset.inter_self]

theorem planeIdem_inl (m : ℕ) (S : Finset (Fin m)) (j : Fin m) :
    (planeIdem m S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inl j) (Sum.inl j) =
      if j ∈ S then 1 else 0 := by
  rw [planeIdem, Matrix.diagonal_apply_eq]
  rfl

theorem planeIdem_empty (m : ℕ) :
    (planeIdem m ∅ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 0 := by
  simp [planeIdem]

theorem planeIdem_ne_zero {m : ℕ} {S : Finset (Fin m)} (hS : S.Nonempty) :
    (planeIdem m S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) ≠ 0 := by
  obtain ⟨j, hj⟩ := hS
  intro h
  have h1 := planeIdem_inl (K := K) m S j
  rw [h, if_pos hj] at h1
  exact zero_ne_one h1

theorem evalRestr_eq_or_eq_neg_of_mem_support {m : ℕ} (U : Submodule (ZMod 3) (PlaneRaw.V m))
    {c : PlaneRaw.Code m} (hc : PlaneRaw.occurs U c) {i j : Fin m} (hi : i ∈ c.support)
    (hj : j ∈ c.support) :
    PlaneRaw.evalRestr U i = PlaneRaw.evalRestr U j ∨
      PlaneRaw.evalRestr U i = -PlaneRaw.evalRestr U j := by
  cases c with
  | zero S =>
    left
    ext u
    rw [evalRestr_apply', evalRestr_apply', (hc i).1 hi u, (hc j).1 hj u]
  | extension e =>
    obtain ⟨-, χ, -, hsupp, -⟩ := hc
    have hei : e i ≠ 0 := by
      simpa [PlaneRaw.Code.support, PlaneRaw.Code.extSupport] using hi
    have hej : e j ≠ 0 := by
      simpa [PlaneRaw.Code.support, PlaneRaw.Code.extSupport] using hj
    rw [hsupp i hei, hsupp j hej]
    have h12 : ∀ b : ZMod 3, b ≠ 0 → b = 1 ∨ b = -1 := by decide
    rcases h12 _ hei with h | h <;> rcases h12 _ hej with h' | h' <;> rw [h, h']
    · exact Or.inl rfl
    · right
      ext u
      simp
    · right
      ext u
      simp
    · exact Or.inl rfl

theorem exists_code_support_eq {m : ℕ} (U : Submodule (ZMod 3) (PlaneRaw.V m)) (i : Fin m) :
    ∃ c : PlaneRaw.Code m, PlaneRaw.occurs U c ∧ ∀ j, j ∈ c.support ↔
      (PlaneRaw.evalRestr U j = PlaneRaw.evalRestr U i ∨
        PlaneRaw.evalRestr U j = -PlaneRaw.evalRestr U i) := by
  classical
  by_cases h0 : PlaneRaw.evalRestr U i = 0
  · refine ⟨.zero (Finset.univ.filter fun j => PlaneRaw.evalRestr U j = 0), fun j => ?_,
      fun j => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h u
        rw [← evalRestr_apply', h, LinearMap.zero_apply]
      · intro h
        ext u
        rw [evalRestr_apply', h u, LinearMap.zero_apply]
    · simp only [PlaneRaw.Code.support, Finset.mem_filter, Finset.mem_univ, true_and, h0,
        neg_zero, or_self]
  · let e : PlaneRaw.V m := fun j =>
      if PlaneRaw.evalRestr U j = PlaneRaw.evalRestr U i then 1
      else if PlaneRaw.evalRestr U j = -PlaneRaw.evalRestr U i then -1 else 0
    refine ⟨.extension e, ⟨fun he => ?_, PlaneRaw.evalRestr U i, h0, fun j hej => ?_,
      fun j hej => ?_⟩, fun j => ?_⟩
    · have h1 := congrFun he i
      simp only [e, if_pos rfl, Pi.zero_apply] at h1
      exact one_ne_zero h1
    · simp only [e] at hej ⊢
      split_ifs at hej ⊢ with h1 h2
      · rw [h1, one_smul]
      · rw [h2]
        ext u
        simp
      · exact (hej rfl).elim
    · simp only [e] at hej
      split_ifs at hej with h1 h2
      · exact (one_ne_zero hej).elim
      · exact (neg_ne_zero.mpr one_ne_zero hej).elim
      · exact ⟨h1, h2⟩
    · simp only [PlaneRaw.Code.support, PlaneRaw.Code.extSupport, Finset.mem_filter,
        Finset.mem_univ, true_and, e]
      split_ifs with h1 h2
      · simp [h1]
      · simp [h2]
      · simp [h1, h2]

theorem spExistsCodeOfIsPrimAdjIdemIn_holds : SpExistsCodeOfIsPrimAdjIdemIn := by
  intro K _ _ _ ζ m hK hζ U ε hε
  obtain ⟨hεA, hidem, hε0, -, hmin⟩ := hε
  obtain ⟨T, rfl, hT⟩ := exists_planeIdem_of_isIdempotentElem hK hζ U hεA hidem
  obtain ⟨i, hi⟩ : T.Nonempty := by
    rcases T.eq_empty_or_nonempty with h | h
    · exact (hε0 (by rw [h, planeIdem_empty])).elim
    · exact h
  obtain ⟨c, hc, hsupp⟩ := exists_code_support_eq U i
  have hci : i ∈ c.support := (hsupp i).2 (Or.inl rfl)
  have hsub : c.support ⊆ T := fun j hj => hT j i ((hsupp j).1 hj) hi
  have hmul : (planeIdem m c.support : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      planeIdem m T = planeIdem m c.support := by
    rw [← planeIdem_inter, Finset.inter_eq_left.mpr hsub]
  rcases hmin _ (planeIdem_mem_adjoin hK hζ U hc) (isIdempotentElem_planeIdem m _)
      (formAdj_planeIdem m _) hmul with h | h
  · exact (planeIdem_ne_zero ⟨i, hci⟩ h).elim
  · exact ⟨c, hc, ⟨i, hci⟩, h.symm⟩

end CFSG.StandardType.GGQ2Frame.SpBlocks

end
