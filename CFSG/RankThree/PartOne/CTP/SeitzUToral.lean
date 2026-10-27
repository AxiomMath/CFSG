module

public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KFU

section Generic

theorem not_isCyclic_of_exponent_card {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ x : G, x ^ p = 1) (hcard : Nat.card G = p ^ 2) : ¬ IsCyclic G := by
  intro hc
  obtain ⟨g, hg⟩ := hc.exists_generator
  have h1 : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hexp g)
  rw [h1, hcard] at h2
  have h3 := Nat.le_of_dvd hp.pos h2
  nlinarith [hp.two_le]

theorem exists_ne_one_hom_eq {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ x : G, x ^ p = 1) (hcard : Nat.card G = p ^ 2) {F : Type*} [Field F]
    (χ ψ : G →* F) : ∃ x : G, x ≠ 1 ∧ ψ x ≠ 0 ∧ χ x = ψ x := by
  by_contra hcon
  push Not at hcon
  let r : G →* F :=
    { toFun := fun x => χ x * (ψ x)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by simp only [map_mul, mul_inv]; ring }
  have hr : ∀ x : G, x ≠ 1 → r x ≠ 1 := by
    intro x hx hrx
    have h1 : χ x * (ψ x)⁻¹ = 1 := hrx
    have hψ : ψ x ≠ 0 := by
      intro h0
      rw [h0, _root_.inv_zero, mul_zero] at h1
      exact zero_ne_one h1
    exact hcon x hx hψ (by field_simp at h1; exact h1)
  have hinj : Function.Injective r := by
    intro x y hxy
    have h1 : r (x * y⁻¹) = 1 := by
      have hy : r y * r y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [map_mul, hxy, hy]
    by_contra hne
    exact hr _ (fun h => hne (mul_inv_eq_one.mp h)) h1
  exact not_isCyclic_of_exponent_card hp hexp hcard (isCyclic_of_injective_ringHom r hinj)

end Generic

section Diag

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

theorem mul_apply_diag_of_isDiag {A B : Matrix ι ι F} (hA : A.IsDiag) (i : ι) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rw [hA hj.symm, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end Diag

section Block

variable {F : Type*} [Field F]

theorem blockMat_mul_diagonal_comm {m i : ℕ} (h : i + 2 ≤ m)
    (v : Fin m → F) (hv : ∀ c, v c ≠ 0) (a b : Fin m) (ha : a.val = i) (hb : b.val = i + 1)
    (hvv : v a = v b) (A : Matrix (Fin 2) (Fin 2) F) :
    blockMat m i A * Matrix.diagonal v = Matrix.diagonal v * blockMat m i A := by
  have key := diagonal_mul_blockMat_mul_diagonal (k := 2) h v (fun c => (v c)⁻¹)
    (fun c => mul_inv_cancel₀ (hv c)) A
  have hfun : (fun x : Fin 2 => v (blockIdx i h x)) = fun _ => v a := by
    funext x
    fin_cases x
    · exact congrArg v (Fin.ext (by simp [blockIdx_val, ha]))
    · exact (congrArg v (Fin.ext (by simp [blockIdx_val, hb]))).trans hvv.symm
  have hfun' : (fun x : Fin 2 => (v (blockIdx i h x))⁻¹) = fun _ => (v a)⁻¹ := by
    funext x
    rw [congrFun hfun x]
  rw [hfun, hfun', ← Matrix.smul_one_eq_diagonal, ← Matrix.smul_one_eq_diagonal,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ (hv a), one_smul] at key
  have hinv : Matrix.diagonal (fun c => (v c)⁻¹) * Matrix.diagonal v = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext fun c => inv_mul_cancel₀ (hv c))
  calc blockMat m i A * Matrix.diagonal v
      = (Matrix.diagonal v * blockMat m i A * Matrix.diagonal fun c => (v c)⁻¹) *
          Matrix.diagonal v := by rw [key]
    _ = Matrix.diagonal v * blockMat m i A := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]

end Block

section Toral

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem closure_centralizers_unitarySU_of_dvd_add_one
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1)
    (hq : ℓ ^ f ≠ 2) (E : Subgroup (unitarySU ℓ f K (n + 1)))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {g : unitarySU ℓ f K (n + 1) | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hle : unitarySU ℓ f K (n + 1) ≤ primeFormUnitary h (idGram K (n + 1)) :=
    unitarySU_le_primeFormUnitary h
  let G : Subgroup (primeFormUnitary h (idGram K (n + 1))) := E.map (Subgroup.inclusion hle)
  have hGcomm : ∀ u ∈ G, ∀ v ∈ G, u * v = v * u := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hGexp : ∀ u ∈ G, u ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h hp hpq G hGcomm hGexp
  let Pg : GL (Fin (n + 1)) K := (P : GL (Fin (n + 1)) K)
  let Dg : E → GL (Fin (n + 1)) K := fun x =>
    Pg⁻¹ * (((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)) * Pg
  have hdiag : ∀ x : E,
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K).IsDiag :=
    fun x => hP (Subgroup.inclusion hle x) ⟨x, x.2, rfl⟩
  have hDmul : ∀ x y : E, Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin (n + 1) → E →* K := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiag x) c }
  have hnz : ∀ (x : E) (c : Fin (n + 1)),
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c ≠ 0 := by
    intro x c
    have h1 : (((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
        (((Dg x)⁻¹ : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiag x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hexpE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hcommblock : ∀ i : Fin n, ∃ x : E, x ≠ 1 ∧ ∀ A : Matrix (Fin 2) (Fin 2) K,
      blockMat (n + 1) i A * ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
          blockMat (n + 1) i A := by
    intro i
    obtain ⟨x, hx1, -, hxeq⟩ := exists_ne_one_hom_eq hp hexpE hcard (χ i.castSucc) (χ i.succ)
    refine ⟨x, hx1, fun A => ?_⟩
    have hD : ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        Matrix.diagonal (fun c => ((Dg x : GL (Fin (n + 1)) K) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c) := ((hdiag x).diagonal_diag).symm
    rw [hD]
    exact blockMat_mul_diagonal_comm (by omega) _ (hnz x) i.castSucc i.succ (by simp) (by simp)
      hxeq A
  let φ := conjSU h P
  set S := Subgroup.closure {g : unitarySU ℓ f K (n + 1) | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g}
    with hS
  have hblock : ∀ (i : Fin n) (y : unitarySU ℓ f K (n + 1))
      (A : Matrix (Fin 2) (Fin 2) K),
      (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) = blockMat (n + 1) i A → φ y ∈ S := by
    intro i y A hA
    obtain ⟨x, hx1, hxc⟩ := hcommblock i
    refine Subgroup.subset_closure ⟨(x : unitarySU ℓ f K (n + 1)), x.2,
      fun h1 => hx1 (Subtype.ext h1), ?_⟩
    apply Subtype.ext
    have hYD : ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x =
        Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) := by
      apply Units.ext
      simp only [Units.val_mul]
      rw [hA]
      exact hxc A
    have hxeq : ((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) = Pg * Dg x * Pg⁻¹ := by
      simp [Dg, mul_assoc]
    show Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
        ((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) =
      ((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) *
        (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹)
    rw [hxeq]
    calc Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
          (Pg * Dg x * Pg⁻¹)
        = Pg * (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x) * Pg⁻¹ := by group
      _ = Pg * (Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)) * Pg⁻¹ := by
        rw [hYD]
      _ = Pg * Dg x * Pg⁻¹ *
          (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹) := by group
  let ε : Su K ℓ f (n + 1) ≃* unitarySU ℓ f K (n + 1) :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq (n + 1))
  let ι : Fin n → (Su K ℓ f 2 →* unitarySU ℓ f K (n + 1)) := fun i =>
    ε.toMonoidHom.comp (blockEmb2 K ℓ f n i)
  have hgen : ⨆ i : Fin n, (ι i).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := ℓ) (f := f) h.card_eq_sq hq n
    have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
    simpa [ι, MonoidHom.range_comp] using h2
  have hle' : (⨆ i : Fin n, (ι i).range).map φ.toMonoidHom ≤ S := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hblock i _ ((a : Su K ℓ f 2) : GL (Fin 2) K) rfl
  rw [hgen, Subgroup.map_top_of_surjective _ φ.surjective] at hle'
  exact top_unique hle'

end Toral

end CFSG.RankThree.PartOne.CTP
